"""Read-only queue snapshot; never execute or check out a pull request."""
import hashlib
import json
import os
from pathlib import Path
import re
import time

from reader_feedback import api, pages, human, REPO

DASHBOARD_TITLE = '[Maintenance] Issue·PR 정리 현황'
MARKER = re.compile(r'<!-- maintenance-snapshot: ([a-f0-9]{64}) -->')
PRODUCERS = {'Reader feedback checks and decisions', 'Publish textbook'}


def qualifies(name, event, dashboard):
    if name in ('schedule', 'workflow_dispatch'):
        return True
    if name == 'workflow_run':
        run = event.get('workflow_run', {})
        return (run.get('name') in PRODUCERS and run.get('conclusion') == 'success'
                and run.get('head_branch') == 'curriculum-v1.2'
                and (run.get('head_repository') or {}).get('full_name') == REPO)
    if event.get('sender', {}).get('type') != 'User' or not human({'user': event.get('sender', {})}):
        return False
    issue = event.get('issue', {})
    if issue.get('number') == dashboard:
        return False
    if name == 'issues':
        return event.get('action') in ('opened', 'edited', 'reopened', 'closed', 'labeled', 'unlabeled')
    if name == 'issue_comment':
        return event.get('action') in ('created', 'edited', 'deleted') and human(event.get('comment', {}))
    return False


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def summarize(item):
    return {k: item.get(k) for k in ('number', 'title', 'body', 'state', 'html_url', 'closed_at', 'merged_at')} | {
        'labels': sorted(label['name'] for label in item.get('labels', []))}


def snapshot(dashboard):
    items = []
    for issue in pages(f'repos/{REPO}/issues?state=open'):
        if issue['number'] == dashboard or 'pull_request' in issue:
            continue
        row = summarize(issue)
        row['kind'] = 'issue'
        row['comments'] = [{k: c.get(k) for k in ('id', 'body')} for c in
                           pages(f'repos/{REPO}/issues/{issue["number"]}/comments')]
        items.append(row)
    for pr in pages(f'repos/{REPO}/pulls?state=open'):
        row = summarize(pr)
        row.update(kind='pr', sha=pr['head']['sha'], draft=pr['draft'], base=pr['base']['ref'])
        row['comments'] = [{k: c.get(k) for k in ('id', 'body')} for c in
                           pages(f'repos/{REPO}/issues/{pr["number"]}/comments')]
        row['reviews'] = [{k: r.get(k) for k in ('id', 'body', 'state', 'commit_id')} for r in
                          pages(f'repos/{REPO}/pulls/{pr["number"]}/reviews')]
        row['review_comments'] = [{k: c.get(k) for k in ('id', 'body', 'commit_id')} for c in
                                  pages(f'repos/{REPO}/pulls/{pr["number"]}/comments')]
        # Include exact-head CI changes in deduplication, without timestamps that
        # would cause an otherwise unchanged queue to spend another AI budget.
        statuses = api(f'repos/{REPO}/commits/{pr["head"]["sha"]}/status')['statuses']
        row['statuses'] = [{k: s.get(k) for k in ('context', 'state', 'target_url')} for s in statuses]
        checks, page = [], 1
        while True:
            batch = api(f'repos/{REPO}/commits/{pr["head"]["sha"]}/check-runs?per_page=100&page={page}')['check_runs']
            checks.extend({k: c.get(k) for k in ('id', 'name', 'status', 'conclusion', 'html_url')} for c in batch)
            if len(batch) < 100:
                break
            page += 1
        row['checks'] = checks
        items.append(row)
    # Bounded context, explicitly described as such to the agent. Older linked
    # PRs remain available through read tools when a source calls for them.
    closed = api(f'repos/{REPO}/pulls?state=closed&sort=updated&direction=desc&per_page=20')
    recent = [summarize(pr) | {'sha': pr['head']['sha']} for pr in closed]
    data = {'open': sorted(items, key=lambda r: r['number']), 'recent_closed_prs': recent}
    refs = [{k: r[k] for k in ('kind', 'number', 'html_url')} for r in data['open']]
    return digest(data), refs


def main():
    dashboard = int(os.environ['MAINTENANCE_ISSUE'])
    event_path = os.environ.get('GITHUB_EVENT_PATH')
    event = json.loads(Path(event_path).read_text()) if event_path else {}
    name = os.environ.get('GITHUB_EVENT_NAME', 'workflow_dispatch')
    run, key, refs = False, '', []
    eligible = qualifies(name, event, dashboard)
    if eligible:
        if name not in ('schedule', 'workflow_dispatch'):
            time.sleep(min(120, max(0, int(os.environ.get('MAINTENANCE_DEBOUNCE_SECONDS', '0')))))
        board = api(f'repos/{REPO}/issues/{dashboard}')
        if board['title'] != DASHBOARD_TITLE or 'pull_request' in board:
            raise ValueError('Maintenance dashboard identity does not match')
        if board['state'] == 'open':
            key, refs = snapshot(dashboard)
            run = key not in MARKER.findall(board.get('body') or '')
    if run and os.environ.get('HAS_KEY') == 'false':
        raise RuntimeError('ANTHROPIC_API_KEY is required')
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write(f'run={str(run).lower()}\nkey={key}\n')
        out.write('items=' + json.dumps(refs) + '\n')
    print(json.dumps({'run': run, 'eligible_event': eligible, 'dashboard': dashboard, 'items': refs}))


if __name__ == '__main__':
    main()
