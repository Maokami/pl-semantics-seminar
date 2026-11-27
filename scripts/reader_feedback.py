"""Deterministic, paginated intake for the human-reviewed textbook workflow.

Reader text is data, never executable code. Only trusted automation PR markers
suppress a revision; closing a proposal records a decision without deleting input.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

REPO = os.environ.get('GITHUB_REPOSITORY', 'Maokami/pl-semantics-seminar')
MARKER = re.compile(r'<!-- reader-feedback: ([a-f0-9]{64}) -->')
SOURCE = re.compile(r'<!-- reader-source: (issue|discussion):(\d+) -->')
LABEL = 'reader proposal'


def api(path, payload=None):
    cmd = ['gh', 'api', path]
    if payload is not None:
        cmd += ['--method', 'POST', '--input', '-']
    result = subprocess.run(cmd, input=json.dumps(payload) if payload is not None else None,
                            text=True, capture_output=True, check=True)
    return json.loads(result.stdout) if result.stdout.strip() else None


def pages(path):
    sep = '&' if '?' in path else '?'
    result = []
    for page in range(1, 10001):
        batch = api(f'{path}{sep}per_page=100&page={page}')
        result.extend(batch)
        if len(batch) < 100:
            return result
    raise RuntimeError('Pagination limit exceeded; refusing an incomplete intake')


def human(post):
    user = post.get('user') or post.get('author') or {}
    return user.get('type', user.get('__typename')) != 'Bot' and not user.get('login', '').endswith('[bot]')


def snapshot(kind, item, comments):
    # Do not hash updated_at: automation labels, status changes and notifications
    # must not cause the exact same reader text to be reviewed repeatedly.
    posts = [{'id': p['id'], 'body': p.get('body') or ''} for p in comments if human(p)]
    data = {'kind': kind, 'number': item['number'], 'title': item['title'],
            'body': item.get('body') or '', 'comments': sorted(posts, key=lambda p: str(p['id']))}
    key = hashlib.sha256(json.dumps(data, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    return {'key': key, 'kind': kind, 'number': item['number'],
            'url': item['html_url'], 'title': item['title']}


def trusted_proposal(pr):
    return pr.get('user', {}).get('login') == 'github-actions[bot]' and any(
        label['name'] == LABEL for label in pr.get('labels', []))


def pending(candidates, proposals):
    seen = {key for pr in proposals if trusted_proposal(pr)
            for key in MARKER.findall(pr.get('body') or '')}
    return [item for item in candidates if item['key'] not in seen]


def discussion_comments(number):
    # GraphQL pagination includes replies to older comments, not just root posts.
    query = '''query($o:String!,$r:String!,$n:Int!,$cursor:String){repository(owner:$o,name:$r){discussion(number:$n){comments(first:100,after:$cursor){nodes{id body author{login __typename} replies(first:100){nodes{id body author{login __typename}} pageInfo{hasNextPage endCursor}}} pageInfo{hasNextPage endCursor}}}}}'''
    owner, name = REPO.split('/')
    result, cursor = [], None
    while True:
        data = api('graphql', {'query': query, 'variables': {'o': owner, 'r': name, 'n': number, 'cursor': cursor}})
        if data.get('errors'):
            raise RuntimeError(data['errors'])
        connection = data['data']['repository']['discussion']['comments']
        for comment in connection['nodes']:
            result.append(comment)
            replies = comment['replies']
            result.extend(replies['nodes'])
            while replies['pageInfo']['hasNextPage']:
                q = '''query($id:ID!,$cursor:String){node(id:$id){... on DiscussionComment{replies(first:100,after:$cursor){nodes{id body author{login __typename}} pageInfo{hasNextPage endCursor}}}}}'''
                data = api('graphql', {'query': q, 'variables': {'id': comment['id'], 'cursor': replies['pageInfo']['endCursor']}})
                if data.get('errors'):
                    raise RuntimeError(data['errors'])
                replies = data['data']['node']['replies']
                result.extend(replies['nodes'])
        if not connection['pageInfo']['hasNextPage']:
            return result
        cursor = connection['pageInfo']['endCursor']


def collect():
    candidates = []
    for issue in pages(f'repos/{REPO}/issues?state=open&labels=textbook%20feedback'):
        if 'pull_request' not in issue:
            candidates.append(snapshot('issue', issue, pages(f'repos/{REPO}/issues/{issue["number"]}/comments')))
    for thread in pages(f'repos/{REPO}/discussions'):
        if thread.get('state', 'open') != 'open' or not re.search(r'\bSession\s+\d{1,2}\b', thread['title']):
            continue
        comments = discussion_comments(thread['number'])
        # Empty pre-created General chapter threads are navigation, not feedback.
        if thread.get('category', {}).get('slug') == 'general' and not any(human(p) for p in comments):
            continue
        candidates.append(snapshot('discussion', thread, comments))
    proposals = pages(f'repos/{REPO}/pulls?state=all&sort=created&direction=desc')
    return pending(candidates, proposals)


def main():
    smoke = os.environ.get('SMOKE_TEST') == 'true'
    items = [] if smoke else collect()
    # One outstanding proposal keeps review load bounded; input is picked up later.
    proposals = pages(f'repos/{REPO}/pulls?state=open')
    outstanding = any(trusted_proposal(pr) for pr in proposals)
    items = [] if outstanding and not smoke else items[:3]
    run = smoke or bool(items)
    if run and os.environ.get('HAS_KEY') == 'false':
        raise RuntimeError('ANTHROPIC_API_KEY is required when feedback is ready')
    values = {'run': str(run).lower(), 'items': json.dumps(items, ensure_ascii=False), 'smoke': str(smoke).lower()}
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
            for key, value in values.items():
                out.write(f'{key}={value}\n')
    print(json.dumps({'run': run, 'selected': items, 'outstanding_proposal': outstanding}, ensure_ascii=False))


if __name__ == '__main__':
    main()
