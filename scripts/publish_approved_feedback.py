"""Publish one fixed approved text to Discussion #1; safe to repeat."""
import os
from approved_feedback import approved_post, submission_body
from reader_feedback import api, REPO

TARGET_REPO = 'Maokami/pl-semantics-seminar'
DISCUSSION_ID = 'D_kwDOV5jDy84Arggz'


def graphql(query, variables):
    result = api('graphql', {'query': query, 'variables': variables})
    if result.get('errors'):
        raise RuntimeError(result['errors'])
    return result['data']


def publish():
    if REPO != TARGET_REPO:
        raise ValueError('This publisher is restricted to the original repository')
    discussion = api(f'repos/{REPO}/discussions/1')
    if discussion['node_id'] != DISCUSSION_ID or not discussion['title'].startswith('Session 01'):
        raise ValueError('Discussion identity does not match the approved destination')
    if discussion.get('locked') or discussion.get('state', 'open') != 'open':
        raise ValueError('The target discussion is not open for comments')
    cursor = None
    while True:
        data = graphql('''query($id:ID!,$cursor:String){node(id:$id){... on Discussion{
            comments(first:100,after:$cursor){nodes{id url body author{login __typename}}
            pageInfo{hasNextPage endCursor}}}}}''', {'id': DISCUSSION_ID, 'cursor': cursor})
        comments = data['node']['comments']
        for comment in comments['nodes']:
            if approved_post(comment):
                return comment['url'], False
        if not comments['pageInfo']['hasNextPage']:
            break
        cursor = comments['pageInfo']['endCursor']
    data = graphql('''mutation($id:ID!,$body:String!){addDiscussionComment(
        input:{discussionId:$id,body:$body}){comment{id url body author{login __typename}}}}''',
        {'id': DISCUSSION_ID, 'body': submission_body()})
    comment = data['addDiscussionComment']['comment']
    if not approved_post(comment):
        raise RuntimeError('Posted comment does not match approved content and bot identity')
    return comment['url'], True


def main():
    url, created = publish()
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write(f'comment_url={url}\ncreated={str(created).lower()}\n')
    with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as out:
        out.write(f'Approved Chapter 1 feedback: {url}\n\nNew comment: {created}\n')
    print(url)


if __name__ == '__main__':
    main()
