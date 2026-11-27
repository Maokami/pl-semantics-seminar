import json
import sys
from pathlib import Path
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import reader_feedback as f
import feedback_actions as actions


class FeedbackEventTests(unittest.TestCase):
    def issue(self, action='opened'):
        return {'action': action, 'sender': {'login': 'reader', 'type': 'User'},
                'issue': {'state': 'open', 'labels': [{'name': 'textbook feedback'}]},
                'comment': {'user': {'login': 'reader', 'type': 'User'}}}

    def decision(self):
        return {'workflow_run': {'name': 'Reader feedback checks and decisions',
                'path': '.github/workflows/reader-feedback-followup.yml',
                'event': 'pull_request_target', 'conclusion': 'success',
                'repository': {'full_name': f.REPO}, 'head_repository': {'full_name': f.REPO},
                'head_sha': 'a' * 40}}

    def test_issue_lifecycle_and_feedback_label_only(self):
        for action in ('opened', 'reopened'):
            self.assertTrue(f.event_qualifies('issues', self.issue(action)))
        e = self.issue('labeled')
        e['label'] = {'name': 'textbook feedback'}
        self.assertTrue(f.event_qualifies('issues', e))
        e['label']['name'] = 'unrelated'
        self.assertFalse(f.event_qualifies('issues', e))
        e = self.issue('edited')
        e['changes'] = {'body': {'from': 'old'}}
        self.assertTrue(f.event_qualifies('issues', e))
        e['changes'] = {'milestone': {}}
        self.assertFalse(f.event_qualifies('issues', e))

    def test_unrelated_closed_and_pr_issues_are_ignored(self):
        for change in ({'labels': []}, {'state': 'closed'}, {'pull_request': {}}):
            e = self.issue('created')
            e['issue'].update(change)
            self.assertFalse(f.event_qualifies('issue_comment', e))

    def test_comments_and_replies_include_edits_and_deletions(self):
        for action in ('created', 'edited', 'deleted'):
            e = self.issue(action)
            self.assertTrue(f.event_qualifies('issue_comment', e))
            e['discussion'] = {'title': 'Session 01 · Arithmetic Expressions', 'state': 'open'}
            e['comment']['reply_to_id'] = 123
            self.assertTrue(f.event_qualifies('discussion_comment', e))
        e['discussion']['title'] = 'Unrelated discussion'
        self.assertFalse(f.event_qualifies('discussion_comment', e))

    def test_bot_sender_and_bot_notifications_never_trigger(self):
        e = self.issue('created')
        e['sender'] = {'login': 'github-actions[bot]', 'type': 'Bot'}
        self.assertFalse(f.event_qualifies('issue_comment', e))
        e['sender'] = {'login': 'maintainer', 'type': 'User'}
        e['comment']['user'] = {'login': 'github-actions[bot]', 'type': 'Bot'}
        self.assertFalse(f.event_qualifies('issue_comment', e))

    def test_discussion_body_and_title_edits(self):
        e = self.issue('edited')
        e['discussion'] = {'title': '[Session 02] Question'}
        for key in ('body', 'title'):
            e['changes'] = {key: {'from': 'old'}}
            self.assertTrue(f.event_qualifies('discussion', e))

    def test_decision_wakeup_cannot_form_a_workflow_loop(self):
        pr = {'user': {'login': 'github-actions[bot]'}, 'labels': [{'name': f.LABEL}],
              'state': 'closed', 'base': {'ref': 'curriculum-v1.2'},
              'head': {'repo': {'full_name': f.REPO}}}
        self.assertTrue(actions.decision_releases_queue('pull_request_target', {'action': 'closed'}, pr))
        for name in ('workflow_run', 'workflow_dispatch'):
            self.assertFalse(actions.decision_releases_queue(name, {'action': 'closed'}, pr))
        for action in ('synchronize', 'reopened'):
            self.assertFalse(actions.decision_releases_queue('pull_request_target', {'action': action}, pr))
        self.assertFalse(f.event_qualifies('workflow_run', self.decision()))

    def test_decision_wakeup_requires_same_repo_closed_bot_proposal(self):
        pr = {'user': {'login': 'github-actions[bot]'}, 'labels': [{'name': f.LABEL}],
              'state': 'closed', 'base': {'ref': 'curriculum-v1.2'},
              'head': {'repo': {'full_name': f.REPO}}}
        for change in ({'state': 'open'}, {'user': {'login': 'reader'}},
                       {'head': {'repo': {'full_name': 'other/fork'}}}, {'base': {'ref': 'other'}}):
            bad = dict(pr, **change)
            self.assertFalse(actions.decision_releases_queue('pull_request_target', {'action': 'closed'}, bad))

    def test_irrelevant_event_exits_before_any_api_or_ai(self):
        with patch.dict(f.os.environ, {'GITHUB_EVENT_NAME': 'issue_comment', 'GITHUB_EVENT_PATH': 'event.json', 'GITHUB_OUTPUT': ''}), \
             patch.object(f.Path, 'read_text', return_value=json.dumps({'sender': {'type': 'Bot'}})), \
             patch.object(f, 'pages') as pages, patch.object(f, 'collect') as collect, patch('builtins.print') as output:
            f.main()
            pages.assert_not_called()
            collect.assert_not_called()
            self.assertFalse(json.loads(output.call_args.args[0])['run'])

    def test_relevant_event_batches_then_collects_latest_snapshot(self):
        with patch.dict(f.os.environ, {'GITHUB_EVENT_NAME': 'issues', 'GITHUB_EVENT_PATH': 'event.json',
                                     'GITHUB_OUTPUT': '', 'SMOKE_TEST': 'false', 'HAS_KEY': 'true',
                                     'FEEDBACK_DEBOUNCE_SECONDS': '60'}), \
             patch.object(f.Path, 'read_text', return_value=json.dumps(self.issue())), \
             patch.object(f, 'pages', return_value=[]), patch.object(f, 'blocked_proposals', return_value=[]), \
             patch.object(f.time, 'sleep') as sleep, patch.object(f, 'collect', return_value=[{'key': 'latest'}]) as collect, \
             patch('builtins.print') as output:
            f.main()
            sleep.assert_called_once_with(60)
            collect.assert_called_once()
            self.assertTrue(json.loads(output.call_args.args[0])['run'])

    def test_duplicate_builds_and_automatic_failure_retries_are_avoided(self):
        self.assertTrue(actions.needs_book_check(None))
        self.assertFalse(actions.needs_book_check({'state': 'success'}))
        self.assertFalse(actions.needs_book_check({'state': 'failure'}))
        self.assertTrue(actions.needs_book_check({'state': 'failure'}, retry=True))
        status = {'state': 'pending', 'target_url': f'https://github.com/{f.REPO}/actions/runs/123'}
        with patch.object(actions, 'api', return_value={'status': 'in_progress'}):
            self.assertFalse(actions.needs_book_check(status, retry=True))
        with patch.object(actions, 'api', return_value={'status': 'completed'}):
            self.assertTrue(actions.needs_book_check(status))


if __name__ == '__main__':
    unittest.main()
