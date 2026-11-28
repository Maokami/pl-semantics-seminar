import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import maintenance_status as status
import feedback_actions as actions


class MaintenanceStatusTests(unittest.TestCase):
    def test_dashboard_and_own_run_do_not_trigger_a_loop(self):
        self.assertFalse(status.qualifies('issue_comment', {'issue': {'number': 27}}))
        self.assertTrue(status.qualifies('issues', {'issue': {'number': 13}}))
        run = {'name': 'Refresh repository status', 'head_repository': {'full_name': status.REPO}}
        self.assertFalse(status.qualifies('workflow_run', {'workflow_run': run}))
        run['name'] = 'Publish textbook'
        self.assertTrue(status.qualifies('workflow_run', {'workflow_run': run}))
        run['head_repository']['full_name'] = 'outsider/fork'
        self.assertFalse(status.qualifies('workflow_run', {'workflow_run': run}))

    def test_snapshot_identifies_merged_links_without_claiming_resolution(self):
        issue = {'number': 13, 'title': '<script>@user | [link]</script>', 'labels': []}
        def pages(path):
            if path.endswith('issues?state=open'):
                return [issue, {'number': 27}, {'number': 90, 'pull_request': {}}]
            if path.endswith('/timeline'):
                return [{'source': {'issue': {'number': 24, 'repository_url': f'https://api.github.com/repos/{status.REPO}',
                                             'pull_request': {'merged_at': 'today'}}}}]
            return []
        def api(path):
            if '/runs?' in path:
                return {'workflow_runs': [{'id': 10, 'name': 'Review', 'status': 'completed', 'conclusion': 'success'}]}
            if '/jobs?' in path:
                return {'jobs': [{'name': 'agent', 'status': 'completed', 'conclusion': 'skipped'}]}
            return []
        with patch.object(status, 'pages', side_effect=pages), patch.object(status, 'api', side_effect=api):
            data = status.snapshot()
        self.assertEqual(data['issues'][0]['merged_prs'], [24])
        text = status.render(data, 'now')
        self.assertIn('요청 전체 해결·게시 여부 확인 후 닫기', text)
        self.assertIn('AI agent `skipped`', text)
        self.assertNotIn('<script>', text)
        self.assertNotIn('@user', text)

    def test_identical_snapshot_is_not_posted_again(self):
        data = {'issues': [], 'prs': [], 'recent_merged': [], 'runs': []}
        comment = {'id': 5, 'user': {'login': 'github-actions[bot]'}, 'body': status.render(data, 'old')}
        with patch.dict(status.os.environ, {'GITHUB_EVENT_PATH': '', 'GITHUB_EVENT_NAME': 'workflow_dispatch'}), \
                patch.object(status, 'api', return_value={'title': status.DASHBOARD_TITLE, 'state': 'open'}) as api, \
                patch.object(status, 'pages', return_value=[comment]), patch.object(status, 'snapshot', return_value=data), \
                patch.object(status.subprocess, 'run') as write:
            status.main()
            self.assertEqual(api.call_count, 1)
            write.assert_not_called()

    def test_closure_requires_opt_in_change_and_respects_reopening(self):
        pr = {'merged_at': '2026-11-28T00:00:00Z'}
        issue = {'state': 'open', 'labels': [{'name': actions.CLOSE_LABEL}]}
        with patch.object(actions, 'api', return_value=issue) as read, \
                patch.object(actions, 'pages', return_value=[]) as events, \
                patch.object(actions.subprocess, 'run') as write:
            for records in ([], [{'disposition': 'no-change'}], [{'disposition': 'needs-discussion'}],
                            [{'disposition': 'change'}, {'disposition': 'needs-discussion'}]):
                actions.close_published_issue(pr, '13', records)
            read.assert_not_called()
            actions.close_published_issue({}, '13', [{'disposition': 'change'}])
            read.assert_not_called()
            issue['labels'] = []
            actions.close_published_issue(pr, '13', [{'disposition': 'change'}])
            events.assert_not_called()
            issue['labels'] = [{'name': actions.CLOSE_LABEL}]
            events.return_value = [{'event': 'reopened', 'created_at': '2026-11-28T00:01:00Z'}]
            actions.close_published_issue(pr, '13', [{'disposition': 'change'}])
            write.assert_not_called()
            events.return_value = []
            actions.close_published_issue(pr, '13', [{'disposition': 'change'}])
            self.assertEqual(json.loads(write.call_args.kwargs['input']), {'state': 'closed', 'state_reason': 'completed'})
            issue['state'] = 'closed'
            actions.close_published_issue(pr, '13', [{'disposition': 'change'}])
            self.assertEqual(write.call_count, 1)


if __name__ == '__main__':
    unittest.main()
