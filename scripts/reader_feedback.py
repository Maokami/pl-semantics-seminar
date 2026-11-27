"""Deterministic, paginated intake for the human-reviewed textbook workflow.

Reader text is data, never executable code. Only trusted automation PR records
suppress a revision; closing a proposal records a decision without deleting input.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

REPO = os.environ.get('GITHUB_REPOSITORY', 'Maokami/pl-semantics-seminar')
MARKER = re.compile(r'<!-- reader-feedback: ([a-f0-9]{64}) -->')
SOURCE = re.compile(r'<!-- reader-source: (issue|discussion):(\d+) -->')
LABEL = 'reader proposal'


def event_qualifies(name, event):
    """Select wake-ups, not instructions. Human text is fetched later as data."""
    if name in ('schedule', 'workflow_dispatch'):
        return True
    sender = event.get('sender', {})
    if sender.get('type') != 'User' or not human({'user': sender}):
        return False
    action = event.get('action')
    if name in ('issues', 'issue_comment'):
        issue = event.get('issue', {})
        if ('pull_request' in issue or issue.get('state') != 'open'
                or not any(label.get('name') == 'textbook feedback' for label in issue.get('labels', []))):
            return False
        if name == 'issues':
            if action == 'labeled':
                return event.get('label', {}).get('name') == 'textbook feedback'
            return action in ('opened', 'reopened') or (action == 'edited' and bool({'title', 'body'} & event.get('changes', {}).keys()))
    elif name in ('discussion', 'discussion_comment'):
        discussion = event.get('discussion', {})
        if discussion.get('state', 'open') != 'open' or not re.search(r'\bSession\s+\d{1,2}\b', discussion.get('title', '')):
            return False
        if name == 'discussion':
            return action in ('created', 'category_changed') or (action == 'edited' and bool({'title', 'body'} & event.get('changes', {}).keys()))
    else:
        return False
    return action in ('created', 'edited', 'deleted') and human(event.get('comment', {}))


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


def blocked_proposals():
    # gh-aw 1.2.2 creates a review issue on PR permission failure even when
    # fallback-as-issue is false. Do not spend money recreating that proposal.
    return [issue for issue in pages(f'repos/{REPO}/issues?state=open&labels=reader%20proposal')
            if 'pull_request' not in issue and trusted_proposal(issue)
            and '<!-- gh-aw-workflow-id: reader-feedback -->' in (issue.get('body') or '')]


def proposal_records(pr):
    """Read bounded JSON blobs as data; never check out or execute PR content."""
    if not trusted_proposal(pr):
        return []
    records = []
    for changed in pages(f'repos/{REPO}/pulls/{pr["number"]}/files'):
        match = re.fullmatch(r'feedback/reviews/([a-f0-9]{64})\.json', changed['filename'])
        if not match or changed['status'] == 'removed':
            continue
        if len(records) >= 8:
            raise ValueError('Too many review records')
        blob = api(f'repos/{REPO}/git/blobs/{changed["sha"]}')
        if blob.get('encoding') != 'base64' or blob['size'] > 262144:
            raise ValueError('Invalid review record encoding or size')
        record = json.loads(base64.b64decode(blob['content']))
        if not isinstance(record, dict) or record.get('key') != match[1]:
            raise ValueError('Review record key does not match its path')
        source = re.fullmatch(r'https://github\.com/' + re.escape(REPO)
                              + r'/(issues|discussions)/([1-9][0-9]*)', record.get('source_url', ''))
        if not source:
            raise ValueError('Review source must be an issue/discussion in this repository')
        records.append({'key': match[1], 'kind': {'issues': 'issue', 'discussions': 'discussion'}[source[1]],
                        'number': source[2]})
    return records


def pending(candidates, proposals):
    seen = set()
    for pr in proposals:
        if trusted_proposal(pr):
            keys = MARKER.findall(pr.get('body') or '')
            seen.update(keys or [record['key'] for record in proposal_records(pr)])
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
    event_name = os.environ.get('GITHUB_EVENT_NAME', 'workflow_dispatch')
    event_path = os.environ.get('GITHUB_EVENT_PATH')
    event = json.loads(Path(event_path).read_text()) if event_path else {}
    eligible = event_qualifies(event_name, event)
    smoke = os.environ.get('SMOKE_TEST') == 'true'
    # One outstanding proposal keeps review load bounded; input is picked up later.
    proposals = pages(f'repos/{REPO}/pulls?state=open') if eligible else []
    outstanding = any(trusted_proposal(pr) for pr in proposals)
    blocked = [] if not eligible or smoke or outstanding else blocked_proposals()
    items = []
    if eligible and not smoke and not outstanding and not blocked:
        if event_name not in ('schedule', 'workflow_dispatch'):
            # Workflow-level concurrency serializes intake through publication.
            # One active run + the latest pending run coalesce bursts; never
            # cancel an active agent or safe-output write because of a comment.
            time.sleep(min(120, max(0, int(os.environ.get('FEEDBACK_DEBOUNCE_SECONDS', '0')))))
        items = collect()[:3]
    run = eligible and (smoke or bool(items))
    if run and os.environ.get('HAS_KEY') == 'false':
        raise RuntimeError('ANTHROPIC_API_KEY is required when feedback is ready')
    values = {'run': str(run).lower(), 'items': json.dumps(items, ensure_ascii=False), 'smoke': str(smoke).lower()}
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
            for key, value in values.items():
                out.write(f'{key}={value}\n')
    print(json.dumps({'run': run, 'selected': items, 'outstanding_proposal': outstanding,
                      'event': event_name, 'eligible_event': eligible,
                      'blocked_proposal_issues': [i['html_url'] for i in blocked]}, ensure_ascii=False))
    if blocked:
        print('::warning::PR creation is blocked. Resolve and close the linked fallback issue before resuming normal AI reviews.')


if __name__ == '__main__':
    main()
