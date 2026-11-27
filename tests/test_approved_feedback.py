import sys
from pathlib import Path
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from approved_feedback import submission_body
import publish_approved_feedback as publisher
import reader_feedback as reader


def posted(body=None, login='github-actions', kind='Bot'):
    return {'id': 'comment', 'url': 'https://github.com/Maokami/pl-semantics-seminar/discussions/1#discussioncomment-123',
            'body': submission_body() if body is None else body,
            'author': {'login': login, '__typename': kind}}


class ApprovedFeedbackTests(unittest.TestCase):
    def test_only_exact_approved_bot_text_in_target_discussion_is_admitted(self):
        self.assertTrue(reader.reader_post(posted(), 'discussion', 1))
        self.assertFalse(reader.reader_post(posted(), 'discussion', 2))
        self.assertFalse(reader.reader_post(posted(), 'issue', 1))
        self.assertFalse(reader.reader_post(posted(login='other[bot]'), 'discussion', 1))
        self.assertFalse(reader.reader_post(posted(body=submission_body() + '\nchanged'), 'discussion', 1))
        self.assertFalse(reader.reader_post(posted(body='Review completed'), 'discussion', 1))

    def test_approved_submission_changes_snapshot_but_bot_notifications_do_not(self):
        thread = {'number': 1, 'title': 'Session 01', 'body': '', 'html_url': 'url'}
        initial = reader.snapshot('discussion', thread, [])
        self.assertNotEqual(initial['key'], reader.snapshot('discussion', thread, [posted()])['key'])
        self.assertEqual(initial['key'], reader.snapshot('discussion', thread, [posted(body='Notification')])['key'])

    def test_publisher_paginates_and_does_not_duplicate_existing_comment(self):
        meta = {'node_id': publisher.DISCUSSION_ID, 'title': 'Session 01 · Arithmetic Expressions', 'state': 'open'}
        first = {'data': {'node': {'comments': {'nodes': [], 'pageInfo': {'hasNextPage': True, 'endCursor': 'next'}}}}}
        second = {'data': {'node': {'comments': {'nodes': [posted()], 'pageInfo': {'hasNextPage': False}}}}}
        with patch.object(publisher, 'api', side_effect=[meta, first, second]) as api:
            url, created = publisher.publish()
            self.assertFalse(created)
            self.assertEqual(url, posted()['url'])
            self.assertEqual(api.call_count, 3)
            self.assertEqual(api.call_args.args[1]['variables']['cursor'], 'next')

    def test_publisher_posts_the_exact_approved_text(self):
        meta = {'node_id': publisher.DISCUSSION_ID, 'title': 'Session 01', 'state': 'open'}
        empty = {'data': {'node': {'comments': {'nodes': [], 'pageInfo': {'hasNextPage': False}}}}}
        result = {'data': {'addDiscussionComment': {'comment': posted()}}}
        with patch.object(publisher, 'api', side_effect=[meta, empty, result]) as api:
            url, created = publisher.publish()
            self.assertTrue(created)
            self.assertEqual(api.call_args.args[1]['variables']['body'], submission_body())

    def test_publisher_refuses_wrong_or_locked_target(self):
        for changes in ({'node_id': 'different'}, {'locked': True}, {'state': 'closed'}):
            meta = {'node_id': publisher.DISCUSSION_ID, 'title': 'Session 01', 'state': 'open'} | changes
            with patch.object(publisher, 'api', return_value=meta) as api:
                with self.assertRaises(ValueError):
                    publisher.publish()
                self.assertEqual(api.call_count, 1)

    def test_graphql_errors_cannot_look_like_publication_success(self):
        with patch.object(publisher, 'api', return_value={'errors': [{'message': 'Forbidden'}]}):
            with self.assertRaises(RuntimeError):
                publisher.graphql('mutation', {})


if __name__ == '__main__':
    unittest.main()
