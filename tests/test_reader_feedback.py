import sys
from pathlib import Path
import unittest
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import reader_feedback as f
import feedback_actions as actions


class IntakeTests(unittest.TestCase):
    def item(self):
        return {'number': 1, 'title': 'Session 01', 'body': 'Question', 'html_url': 'https://github.com/Maokami/pl-semantics-seminar/discussions/1'}

    def test_bot_reply_does_not_requeue_and_human_edit_does(self):
        item = self.item()
        comment = {'id': 1, 'body': 'Why?', 'user': {'login': 'reader', 'type': 'User'}}
        before = f.snapshot('discussion', item, [comment])
        bot = {'id': 2, 'body': 'Proposal ready', 'user': {'login': 'github-actions[bot]', 'type': 'Bot'}}
        self.assertEqual(before, f.snapshot('discussion', item, [comment, bot]))
        comment['body'] = 'Why? Here is a counterexample.'
        self.assertNotEqual(before['key'], f.snapshot('discussion', item, [comment])['key'])

    def test_closed_proposals_deduplicate_but_forged_markers_do_not(self):
        item = f.snapshot('issue', self.item(), [])
        pr = {'body': '<!-- reader-feedback: ' + item['key'] + ' -->', 'state': 'closed',
              'user': {'login': 'reader'}, 'labels': [{'name': f.LABEL}]}
        self.assertEqual(f.pending([item], [pr]), [item])
        pr['user']['login'] = 'github-actions[bot]'
        self.assertEqual(f.pending([item], [pr]), [])

    def test_paginated_rest(self):
        with patch.object(f, 'api', side_effect=[list(range(100)), [101]]) as call:
            self.assertEqual(len(f.pages('repos/a/b/issues?state=open')), 101)
            self.assertIn('&per_page=100&page=2', call.call_args.args[0])

    def test_only_trusted_workflow_fallback_issues_block(self):
        issue = {'html_url': 'https://example.com/17',
                 'user': {'login': 'github-actions[bot]'},
                 'labels': [{'name': f.LABEL}],
                 'body': '<!-- gh-aw-workflow-id: reader-feedback -->'}
        forged = dict(issue, user={'login': 'reader'})
        pr = dict(issue, pull_request={})
        unrelated = dict(issue, body='Other workflow')
        with patch.object(f, 'pages', return_value=[issue, forged, pr, unrelated]):
            self.assertEqual(f.blocked_proposals(), [issue])

    def test_blocked_intake_does_not_collect_or_run_ai(self):
        with patch.dict(f.os.environ, {'SMOKE_TEST': 'false', 'GITHUB_OUTPUT': ''}), \
                patch.object(f, 'blocked_proposals', return_value=[{'html_url': 'https://example.com/17'}]), \
                patch.object(f, 'collect') as collect, \
                patch.object(f, 'pages', return_value=[]), patch('builtins.print') as output:
            f.main()
            collect.assert_not_called()
            self.assertFalse(f.json.loads(output.call_args_list[0].args[0])['run'])

    def test_graphql_paginates_replies_and_root_comments(self):
        def conn(nodes, more=False, cursor=None):
            return {'nodes': nodes, 'pageInfo': {'hasNextPage': more, 'endCursor': cursor}}
        first = {'id': 'root1', 'body': 'question', 'author': {'login': 'reader'},
                 'replies': conn([{'id': 'reply1', 'body': 'first'}], True, 'r1')}
        responses = [
            {'data': {'repository': {'discussion': {'comments': conn([first], True, 'c1')}}}},
            {'data': {'node': {'replies': conn([{'id': 'reply2', 'body': 'later'}])}}},
            {'data': {'repository': {'discussion': {'comments': conn([])}}}},
        ]
        with patch.object(f, 'api', side_effect=responses) as call:
            posts = f.discussion_comments(1)
        self.assertEqual([p['id'] for p in posts], ['root1', 'reply1', 'reply2'])
        self.assertEqual(call.call_args_list[1].args[1]['variables']['cursor'], 'r1')
        self.assertEqual(call.call_args_list[2].args[1]['variables']['cursor'], 'c1')

    def test_graphql_errors_fail_closed(self):
        with patch.object(f, 'api', return_value={'errors': [{'message': 'rate limit'}]}):
            with self.assertRaises(RuntimeError):
                f.discussion_comments(1)

    def test_graphql_bot_identity_is_excluded(self):
        self.assertFalse(f.human({'author': {'login': 'robot', '__typename': 'Bot'}}))

    def test_source_markers_are_restricted_and_unique(self):
        self.assertEqual(actions.sources({'body': '<!-- reader-source: issue:42 -->\n<!-- reader-source: issue:42 -->\n<!-- reader-source: other:4 -->'}), [('issue', '42')])

    def test_publication_is_not_claimed_on_merge(self):
        pr = {'number': 5, 'state': 'closed', 'merged_at': 'date', 'html_url': 'https://example.com/5'}
        self.assertNotIn('게시가 완료', actions.notification(pr))
        self.assertIn('게시가 완료', actions.notification(pr, published=True))

    def test_review_records_recover_omitted_markers_for_dedup_and_notification(self):
        item = f.snapshot('issue', self.item(), [])
        pr = {'number': 24, 'body': 'No machine-readable markers',
              'user': {'login': 'github-actions[bot]'}, 'labels': [{'name': f.LABEL}]}
        changed = {'filename': f'feedback/reviews/{item["key"]}.json', 'status': 'added', 'sha': 'blob-sha'}
        record = {'key': item['key'], 'source_url': f'https://github.com/{f.REPO}/issues/13'}
        blob = {'encoding': 'base64', 'size': 300,
                'content': f.base64.b64encode(f.json.dumps(record).encode()).decode()}
        with patch.object(f, 'pages', return_value=[changed]), patch.object(f, 'api', return_value=blob):
            self.assertEqual(f.pending([item], [pr]), [])
            self.assertEqual(actions.sources(pr), [('issue', '13')])
            record['source_url'] = 'https://github.com/someone/else/issues/13'
            blob['content'] = f.base64.b64encode(f.json.dumps(record).encode()).decode()
            with self.assertRaises(ValueError):
                f.proposal_records(pr)
            record['source_url'] = f'https://github.com/{f.REPO}/issues/13'
            record['key'] = '0' * 64
            blob['content'] = f.base64.b64encode(f.json.dumps(record).encode()).decode()
            with self.assertRaises(ValueError):
                f.proposal_records(pr)

    def test_smoke_record_is_not_a_reader_source(self):
        pr = {'number': 21, 'user': {'login': 'github-actions[bot]'}, 'labels': [{'name': f.LABEL}]}
        with patch.object(f, 'pages', return_value=[{'filename': 'feedback/reviews/smoke-123.json', 'status': 'added'}]), \
                patch.object(f, 'api') as api:
            self.assertEqual(f.proposal_records(pr), [])
            api.assert_not_called()


if __name__ == '__main__':
    unittest.main()
