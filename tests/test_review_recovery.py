from datetime import datetime, timezone
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import feedback_actions as actions
import reader_feedback as reader
import review_capacity as capacity


class RecoveryTests(unittest.TestCase):
    def test_missing_key_and_manual_mode_never_probe_or_buy_capacity(self):
        now = datetime.now(timezone.utc)
        with patch.object(capacity, 'api') as api:
            self.assertTrue(capacity.hold_reason('reader-feedback', {}, now))
            self.assertTrue(capacity.hold_reason('reader-feedback', {'HAS_KEY': 'true', 'TEXTBOOK_AI_MODE': 'manual'}, now))
            api.assert_not_called()

    def test_failure_holds_automatic_retries_and_human_dispatch_can_resume(self):
        now = datetime.now(timezone.utc)
        env = {'HAS_KEY': 'true', 'GITHUB_SHA': 'a' * 40, 'GITHUB_EVENT_NAME': 'workflow_dispatch'}
        with patch.object(capacity, 'api', return_value={'workflow_runs': [{'html_url': 'run-1'}]}) as api:
            self.assertIn('run-1', capacity.hold_reason('reader-feedback', env | {'GITHUB_ACTOR': 'github-actions[bot]'}, now))
            self.assertIn('head_sha=' + env['GITHUB_SHA'], api.call_args.args[0])
            self.assertIsNone(capacity.hold_reason('reader-feedback', env | {'GITHUB_ACTOR': 'maintainer'}, now))
            self.assertEqual(api.call_count, 1)

    def test_same_record_for_human_and_agent(self):
        pr = {'user': {'login': 'editor'}, 'labels': [{'name': reader.LABEL}], 'author_association': 'COLLABORATOR',
              'head': {'repo': {'full_name': reader.REPO}}, 'body': '<!-- reader-feedback: ' + 'f'*64 + ' -->'}
        with patch.object(reader, 'proposal_records', return_value=[{'key': 'f'*64}]):
            self.assertEqual(reader.pending([{'key': 'f'*64}], [pr]), [])
        fork = pr | {'head': {'repo': {'full_name': 'reader/fork'}}}
        self.assertFalse(reader.trusted_proposal(fork))
        self.assertTrue(reader.trusted_proposal(fork | {'merged_at': 'today'}))

    def test_no_change_is_distinct_from_published_manuscript(self):
        pr = {'number': 42, 'html_url': 'pr-42', 'merged_at': 'today'}
        for disposition in ('needs-discussion', 'no-change'):
            self.assertNotIn('교재에 반영되었습니다', actions.notification(pr, True, {'disposition': disposition}, 'a'*40))
        body = actions.notification(pr, True, {'disposition': 'change', 'target': 'chapter-01/#ch01-s4'}, 'b'*40)
        self.assertIn('chapter-01/#ch01-s4', body)
        self.assertIn('/commit/'+'b'*40, body)
        self.assertNotIn('Merge', body)

    def test_graphql_bot_comment_is_updated_in_place(self):
        pr = {'number': 24, 'html_url': 'pr-24', 'state': 'open', 'user': {'login': 'github-actions[bot]'}, 'body': '<!-- reader-source: discussion:1 -->'}
        old = {'id': 'comment', 'author': {'login': 'github-actions', '__typename': 'Bot'}, 'body': '<!-- reader-proposal: 24 -->'}
        thread = {'id': 'thread', 'comments': {'nodes': [old], 'pageInfo': {'hasNextPage': False}}}
        with patch.object(actions, 'proposal_records', return_value=[]), patch.object(actions, 'graphql',
                side_effect=[{'repository': {'discussion': thread}}, {}]) as graphql:
            actions.notify(pr)
            self.assertIn('updateDiscussionComment', graphql.call_args.args[0])
            self.assertEqual(graphql.call_args.args[1]['id'], 'comment')
