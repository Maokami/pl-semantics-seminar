"""Trusted-base automation: proposal notifications and checks, never executes PR code."""
import json
import os
import sys
import re
from reader_feedback import api, pages, trusted_proposal, blocked_proposals, proposal_records, SOURCE, REPO

CONTEXT = 'Reader feedback / book'


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


def sources(pr):
    markers = SOURCE.findall(pr.get('body') or '')
    return sorted(set(markers or [(r['kind'], r['number']) for r in proposal_records(pr)]))


def notification(pr, published=False):
    if published:
        state = '교재에 반영되었습니다. GitHub Pages 게시가 완료되었습니다.'
    elif pr.get('merged_at'):
        state = '관리자가 승인했습니다. 교재 빌드·게시 결과는 아래 변경안에서 확인할 수 있습니다.'
    elif pr['state'] == 'closed':
        state = '관리자가 이 변경안을 반영하지 않기로 했습니다. 거부 사유나 후속 논의는 변경안의 댓글에서 확인해 주세요.'
    else:
        state = 'AI가 검토한 변경안이 관리자 승인을 기다리고 있습니다. 아직 교재에 반영되지 않았습니다.'
    return (f'<!-- reader-proposal: {pr["number"]} -->\n{state}\n\n'
            f'검토·결정 기록: {pr["html_url"]}\n\n'
            '관리자: 검사 통과 후 **Merge**로 승인하거나, 사유를 작성하고 '
            '**Comment and close pull request**로 거부할 수 있습니다.\n\n'
            '교재: https://maokami.github.io/pl-semantics-seminar/')


def graphql(query, variables):
    result = api('graphql', {'query': query, 'variables': variables})
    if result.get('errors'):
        raise RuntimeError(result['errors'])
    return result['data']


def notify(pr, published=False):
    marker = f'<!-- reader-proposal: {pr["number"]} -->'
    body = notification(pr, published)
    for kind, number in sources(pr):
        if kind == 'issue':
            comments = pages(f'repos/{REPO}/issues/{number}/comments')
            existing = next((c for c in comments if c.get('user', {}).get('login') == 'github-actions[bot]' and marker in c['body']), None)
            if existing:
                if existing['body'] != body:
                    # gh api supports explicit PATCH through method override.
                    from subprocess import run
                    run(['gh', 'api', f'repos/{REPO}/issues/comments/{existing["id"]}', '--method', 'PATCH', '--input', '-'], input=json.dumps({'body': body}), text=True, check=True, capture_output=True)
            else:
                api(f'repos/{REPO}/issues/{number}/comments', {'body': body})
        else:
            owner, name = REPO.split('/')
            cursor, existing, discussion_id = None, None, None
            while True:
                data = graphql('''query($o:String!,$r:String!,$n:Int!,$c:String){repository(owner:$o,name:$r){discussion(number:$n){id comments(first:100,after:$c){nodes{id body author{login}} pageInfo{hasNextPage endCursor}}}}}''', {'o': owner, 'r': name, 'n': int(number), 'c': cursor})['repository']['discussion']
                discussion_id = data['id']
                for c in data['comments']['nodes']:
                    if (c.get('author') or {}).get('login') == 'github-actions[bot]' and marker in c['body']:
                        existing = c
                info = data['comments']['pageInfo']
                if not info['hasNextPage']:
                    break
                cursor = info['endCursor']
            if existing:
                if existing['body'] != body:
                    graphql('mutation($id:ID!,$body:String!){updateDiscussionComment(input:{commentId:$id,body:$body}){comment{id}}}', {'id': existing['id'], 'body': body})
            else:
                graphql('mutation($id:ID!,$body:String!){addDiscussionComment(input:{discussionId:$id,body:$body}){comment{id}}}', {'id': discussion_id, 'body': body})


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
        if not trusted_proposal(pr) or pr['base']['ref'] != 'curriculum-v1.2' or pr['head']['repo']['full_name'] != REPO:
            continue
        if is_publish:
            run = event['workflow_run']
            if not pr.get('merged_at') or run.get('head_branch') != 'curriculum-v1.2' or run.get('event') not in ('push', 'workflow_dispatch'):
                continue
            comparison = api(f'repos/{REPO}/compare/{pr["merge_commit_sha"]}...{run["head_sha"]}')
            if comparison['status'] not in ('ahead', 'identical'):
                continue
            notify(pr, published=True)
            continue
        notify(pr)
        wake_queue = wake_queue or decision_releases_queue(event_name, event, pr)
        if pr['state'] != 'open':
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
