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

    def test_actions_api_failure_falls_back_without_model_activation(self):
        env = {'HAS_KEY': 'true', 'GITHUB_SHA': 'a'*40}
        with patch.object(capacity, 'api', side_effect=capacity.subprocess.CalledProcessError(1, 'gh')):
            self.assertIn('unavailable', capacity.hold_reason('reader-feedback', env, datetime.now(timezone.utc)))

    def test_manual_summary_preserves_input_after_api_outage(self):
        item = {'kind': 'issue', 'number': 12, 'url': 'issue-12', 'key': 'a'*64}
        with patch.object(capacity, 'collect', return_value=[item]):
            self.assertIn('[issue #12](issue-12)', capacity.manual_queue('reader-feedback'))
        with patch.object(capacity, 'collect', side_effect=capacity.subprocess.CalledProcessError(1, 'gh')):
            self.assertIn('Open corrections on GitHub', capacity.manual_queue('reader-feedback'))

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
        with patch.object(actions, 'proposal_records', return_value=[]), patch.object(actions, 'discussion_comments',
                return_value=[old]), patch.object(actions, 'graphql') as graphql:
            actions.notify(pr)
            self.assertIn('updateDiscussionComment', graphql.call_args.args[0])
            self.assertEqual(graphql.call_args.args[1]['id'], 'comment')

    def test_approved_comment_gets_a_reply_on_the_original_thread(self):
        source = 'https://github.com/' + reader.REPO + '/discussions/1#discussioncomment-123'
        with patch.object(actions, 'discussion_comments', return_value=[{'id': 'root', 'url': source}]), \
                patch.object(actions, 'api', return_value={'node_id': 'thread'}), patch.object(actions, 'graphql') as graphql:
            actions.notify_discussion('1', source, 'marker', 'decision')
            self.assertEqual(graphql.call_args.args[1], {'id': 'thread', 'parent': 'root', 'body': 'decision'})
