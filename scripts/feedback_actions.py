"""Trusted-base automation: proposal notifications and checks, never executes PR code."""
import json
import os
import base64
import re
import subprocess
from reader_feedback import api, pages, trusted_proposal, blocked_proposals, proposal_records, discussion_comments, SOURCE, REPO

CONTEXT = 'Textbook verification'
CLOSE_LABEL = 'close after publication'


def close_published_issue(pr, number, records):
    """Opt-in completion, only after the caller verified a successful deployment."""
    if not pr.get('merged_at') or not records or any(r.get('disposition') != 'change' for r in records):
        return
    issue = api(f'repos/{REPO}/issues/{number}')
    if (issue.get('state') != 'open' or 'pull_request' in issue
            or CLOSE_LABEL not in {label['name'] for label in issue.get('labels', [])}):
        return
    # A maintainer reopening an issue after this merge overrides this old decision.
    events = pages(f'repos/{REPO}/issues/{number}/events')
    if any(e.get('event') == 'reopened' and e.get('created_at', '') >= pr['merged_at'] for e in events):
        return
    subprocess.run(['gh', 'api', f'repos/{REPO}/issues/{number}', '--method', 'PATCH', '--input', '-'],
                   input=json.dumps({'state': 'closed', 'state_reason': 'completed'}),
                   text=True, check=True, capture_output=True)


def decision_releases_queue(event_name, event, pr):
    return (event_name == 'pull_request_target' and event.get('action') == 'closed'
            and trusted_proposal(pr) and pr.get('state') == 'closed'
            and pr.get('base', {}).get('ref') == 'curriculum-v1.2'
            and (pr.get('head', {}).get('repo') or {}).get('full_name') == REPO)


def needs_book_check(existing, *, retry=False):
    if not existing:
        return True
    if existing['state'] == 'success':
        return False
    if existing['state'] == 'pending':
        match = re.fullmatch(r'https://github\.com/' + re.escape(REPO)
                             + r'/actions/runs/([0-9]+)', existing.get('target_url') or '')
        if match:
            run = api(f'repos/{REPO}/actions/runs/{match[1]}')
            if run['status'] != 'completed':
                return False
        return True  # Recover a stale pending status after interruption.
    return retry  # Reader activity must not repeatedly rebuild a failing SHA.


def sources(pr, records=None):
    if records is None:
        records = proposal_records(pr)
    result = {(r['kind'], r['number']) for r in records}
    if pr.get('user', {}).get('login') == 'github-actions[bot]':
        result.update(SOURCE.findall(pr.get('body') or ''))
    return sorted(result)


def notification(pr, published=False, record=None, revision=None):
    record = record or {}
    disposition = record.get('disposition')
    if pr.get('merged_at') and disposition == 'no-change':
        state = '검토 완료 · 현재 원고를 유지합니다.'
    elif pr.get('merged_at') and disposition == 'needs-discussion':
        state = '검토 완료 · 원래 글에서 추가 논의를 기다립니다.'
    elif published:
        state = '교재에 반영되었습니다. GitHub Pages 게시가 완료되었습니다.'
    elif pr.get('merged_at'):
        state = '관리자가 승인했습니다. 교재 게시를 기다립니다.'
    elif pr['state'] == 'closed':
        state = '변경안이 닫혔습니다. 결정 사유는 PR의 대화에서 확인할 수 있습니다.'
    else:
        state = '변경안이 관리자 검토를 기다리고 있습니다.'
    lines = [f'<!-- reader-proposal: {pr["number"]} -->', state, pr['html_url']]
    if published and revision:
        lines.append(f'게시 리비전 [{revision[:7]}](https://github.com/{REPO}/commit/{revision})')
        target = record.get('target') or ''
        if re.fullmatch(r'chapter-(?:0[1-9]|[12][0-9]|3[0-8])/#ch[0-9]{2}[-a-z0-9]*', target):
            lines.append('[교재 문단 보기](https://maokami.github.io/pl-semantics-seminar/' + target + ')')
        if disposition == 'change':
            lines.append('Issue에 `close after publication` 라벨이 있으면 게시 확인 후 완료로 닫습니다. '
                         '추가 문제가 있으면 Reopen하고 댓글을 남겨 주세요. 같은 PR로 다시 닫지 않습니다.')
    return '\n\n'.join(lines)


def graphql(query, variables):
    result = api('graphql', {'query': query, 'variables': variables})
    if result.get('errors'):
        raise RuntimeError(result['errors'])
    return result['data']


def notify(pr, published=False, revision=None):
    marker = f'<!-- reader-proposal: {pr["number"]} -->'
    records = proposal_records(pr)
    by_source, deployed_records = {}, []
    for record in records:
        if published:
            # Read the record from the deployed commit, including later anchor repairs.
            path = f'feedback/reviews/{record["key"]}.json'
            result = api(f'repos/{REPO}/contents/{path}?ref={revision}')
            deployed = json.loads(base64.b64decode(result['content']))
            record = record | {k: deployed.get(k) for k in ('target', 'disposition')}
        by_source[record['kind'], record['number']] = record
        deployed_records.append(record)
    for kind, number in sources(pr, records):
        body = notification(pr, published, by_source.get((kind, number)), revision)
        if kind == 'issue':
            comments = pages(f'repos/{REPO}/issues/{number}/comments')
            existing = next((c for c in comments if c.get('user', {}).get('login') == 'github-actions[bot]' and marker in c['body']), None)
            if existing:
                if existing['body'] != body:
                    # gh api supports explicit PATCH through method override.
                    subprocess.run(['gh', 'api', f'repos/{REPO}/issues/comments/{existing["id"]}', '--method', 'PATCH', '--input', '-'], input=json.dumps({'body': body}), text=True, check=True, capture_output=True)
            else:
                api(f'repos/{REPO}/issues/{number}/comments', {'body': body})
            if published:
                close_published_issue(pr, number, [r for r in deployed_records
                                                 if r['kind'] == 'issue' and r['number'] == number])
        else:
            record = by_source.get((kind, number), {})
            notify_discussion(number, record.get('url', ''), marker, body)


def notify_discussion(number, source_url, marker, body):
    posts = discussion_comments(int(number))
    parent = None
    if '#discussioncomment-' in source_url:
        original = next((post for post in posts if post.get('url') == source_url), None)
        if original is None:
            raise ValueError('Original discussion comment no longer exists: ' + source_url)
        parent = original.get('parent_id') or original['id']
    for post in posts:
        author = post.get('author') or {}
        if (post.get('parent_id') == parent and author.get('__typename') == 'Bot'
                and author.get('login') in ('github-actions', 'github-actions[bot]')
                and marker in post['body']):
            if post['body'] != body:
                graphql('mutation($id:ID!,$body:String!){updateDiscussionComment(input:{commentId:$id,body:$body}){comment{id}}}',
                        {'id': post['id'], 'body': body})
            return
    discussion = api(f'repos/{REPO}/discussions/{number}')
    graphql('mutation($id:ID!,$parent:ID,$body:String!){addDiscussionComment(input:{discussionId:$id,replyToId:$parent,body:$body}){comment{id}}}',
            {'id': discussion['node_id'], 'parent': parent, 'body': body})



def main():
    event = json.load(open(os.environ['GITHUB_EVENT_PATH']))
    event_name = os.environ['GITHUB_EVENT_NAME']
    if event.get('workflow_run', {}).get('name') == 'Continuous reader feedback':
        blocked = blocked_proposals()
        if blocked:
            raise RuntimeError('PR creation did not complete; resolve and close fallback issues: '
                               + ', '.join(i['html_url'] for i in blocked))
    is_publish = event.get('workflow_run', {}).get('name') == 'Publish textbook'
    if event_name == 'pull_request_target':
        proposals = [api(f'repos/{REPO}/pulls/{event["number"]}')]
    else:
        proposals = pages(f'repos/{REPO}/pulls?state={"closed" if is_publish else "open"}')
    selected = []
    wake_queue = False
    for pr in proposals:
        if not trusted_proposal(pr) or pr['base']['ref'] != 'curriculum-v1.2':
            continue
        if is_publish:
            run = event['workflow_run']
            if not pr.get('merged_at') or run.get('head_branch') != 'curriculum-v1.2' or run.get('event') not in ('push', 'workflow_dispatch'):
                continue
            comparison = api(f'repos/{REPO}/compare/{pr["merge_commit_sha"]}...{run["head_sha"]}')
            if comparison['status'] not in ('ahead', 'identical'):
                continue
            notify(pr, published=True, revision=run['head_sha'])
            continue
        notify(pr)
        wake_queue = wake_queue or decision_releases_queue(event_name, event, pr)
        if pr.get('user', {}).get('login') != 'github-actions[bot]' or pr['state'] != 'open' or (pr['head'].get('repo') or {}).get('full_name') != REPO:
            continue
        statuses = api(f'repos/{REPO}/commits/{pr["head"]["sha"]}/status')['statuses']
        existing = next((s for s in statuses if s['context'] == CONTEXT), None)
        retry = event_name == 'workflow_dispatch' or (event_name == 'pull_request_target' and event.get('action') == 'reopened')
        if not needs_book_check(existing, retry=retry):
            continue
        selected.append({'number': pr['number'], 'sha': pr['head']['sha']})
        api(f'repos/{REPO}/statuses/{pr["head"]["sha"]}', {'state': 'pending', 'context': CONTEXT,
            'description': 'Building the proposed textbook revision',
            'target_url': f'https://github.com/{REPO}/actions/runs/{os.environ["GITHUB_RUN_ID"]}'})
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write('matrix=' + json.dumps({'include': selected}) + '\n')
        out.write('has_prs=' + str(bool(selected)).lower() + '\n')
        out.write('wake_queue=' + str(wake_queue).lower() + '\n')


if __name__ == '__main__':
    main()
