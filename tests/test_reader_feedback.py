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

    def test_source_markers_are_restricted_and_unique(self):
        self.assertEqual(actions.sources({'body': '<!-- reader-source: issue:42 -->\n<!-- reader-source: issue:42 -->\n<!-- reader-source: other:4 -->'}), [('issue', '42')])

    def test_publication_is_not_claimed_on_merge(self):
        pr = {'number': 5, 'state': 'closed', 'merged_at': 'date', 'html_url': 'https://example.com/5'}
        self.assertNotIn('게시가 완료', actions.notification(pr))
        self.assertIn('게시가 완료', actions.notification(pr, published=True))


if __name__ == '__main__':
    unittest.main()
