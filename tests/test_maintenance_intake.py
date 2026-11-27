import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import maintenance_intake as m


class MaintenanceTests(unittest.TestCase):
    def test_dashboard_and_bot_activity_do_not_loop(self):
        event = {'sender': {'type': 'User', 'login': 'reader'}, 'issue': {'number': 13},
                 'action': 'created', 'comment': {'user': {'type': 'User'}}}
        self.assertTrue(m.qualifies('issue_comment', event, 99))
        self.assertFalse(m.qualifies('issue_comment', event, 13))
        event['comment']['user']['type'] = 'Bot'
        self.assertFalse(m.qualifies('issue_comment', event, 99))
        self.assertFalse(m.qualifies('issues', {'action': 'opened'}, 99))

    def test_producer_scope_and_no_self_trigger(self):
        run = {'name': 'Publish textbook', 'conclusion': 'success',
               'head_branch': 'curriculum-v1.2', 'head_repository': {'full_name': m.REPO}}
        self.assertTrue(m.qualifies('workflow_run', {'workflow_run': run}, 99))
        for key, value in [('name', 'Continuous issue and PR triage'), ('conclusion', 'failure'),
                           ('head_branch', 'untrusted'), ('head_repository', {'full_name': 'other/repo'})]:
            self.assertFalse(m.qualifies('workflow_run', {'workflow_run': run | {key: value}}, 99))

    def test_snapshot_excludes_dashboard_and_detects_comment_and_ci_changes(self):
        issue = {'number': 13, 'title': 'Correction', 'body': 'Original', 'state': 'open'}
        pr = {'number': 24, 'title': 'Proposal', 'body': 'Diff', 'state': 'open',
              'head': {'sha': 'abc'}, 'base': {'ref': 'curriculum-v1.2'}, 'draft': False}
        status = {'context': 'book', 'state': 'pending'}
        comments = []
        def paginated(path):
            if path.endswith('issues?state=open'):
                return [issue, {'number': 99}, {'number': 24, 'pull_request': {}}]
            if path.endswith('pulls?state=open'):
                return [pr]
            return comments if '/issues/13/comments' in path else []
        def api(path):
            if path.endswith('/status'):
                return {'statuses': [status]}
            if '/check-runs?' in path:
                return {'check_runs': []}
            return []
        with patch.object(m, 'pages', side_effect=paginated), patch.object(m, 'api', side_effect=api):
            before, refs = m.snapshot(99)
            self.assertEqual([r['number'] for r in refs], [13, 24])
            issue['updated_at'] = 'new timestamp only'
            self.assertEqual(before, m.snapshot(99)[0])
            comments.append({'id': 1, 'body': 'Additional evidence'})
            after_comment = m.snapshot(99)[0]
            self.assertNotEqual(before, after_comment)
            status['state'] = 'success'
            self.assertNotEqual(after_comment, m.snapshot(99)[0])

    def test_identical_queue_and_closed_dashboard_skip_ai(self):
        key = 'a' * 64
        board = {'title': m.DASHBOARD_TITLE, 'state': 'open',
                 'body': '<!-- maintenance-snapshot: ' + key + ' -->'}
        with tempfile.TemporaryDirectory() as tmp:
            output = str(Path(tmp) / 'output')
            env = {'MAINTENANCE_ISSUE': '99', 'GITHUB_EVENT_NAME': 'workflow_dispatch',
                   'GITHUB_EVENT_PATH': '', 'GITHUB_OUTPUT': output}
            with patch.dict(os.environ, env), patch.object(m, 'api', return_value=board), \
                    patch.object(m, 'snapshot', return_value=(key, [])) as read:
                m.main()
                self.assertIn('run=false', Path(output).read_text())
                board['state'] = 'closed'
                m.main()
                self.assertEqual(read.call_count, 1)

    def test_ignored_event_never_reads_repository(self):
        with tempfile.TemporaryDirectory() as tmp:
            event_path, out = Path(tmp) / 'event', Path(tmp) / 'out'
            event_path.write_text(json.dumps({'sender': {'type': 'Bot'}, 'action': 'edited'}))
            env = {'MAINTENANCE_ISSUE': '99', 'GITHUB_EVENT_NAME': 'issues',
                   'GITHUB_EVENT_PATH': str(event_path), 'GITHUB_OUTPUT': str(out)}
            with patch.dict(os.environ, env), patch.object(m, 'api') as api:
                m.main()
                api.assert_not_called()


if __name__ == '__main__':
    unittest.main()
