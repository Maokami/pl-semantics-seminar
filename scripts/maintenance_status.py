"""Maintain one factual dashboard comment without an AI key or PR checkout."""
from datetime import datetime, timezone
import html
import json
import os
from pathlib import Path
import subprocess

from maintenance_intake import DASHBOARD_TITLE, digest
from reader_feedback import api, pages, REPO

DASHBOARD = 27
MARKER = '<!-- maintenance-live-status -->'
WORKFLOWS = ('reader-feedback.lock.yml', 'maintenance-triage.lock.yml')
PRODUCERS = {'Publish textbook', 'Reader feedback checks and decisions',
             'Feedback automation tests', 'Continuous reader feedback', 'Continuous issue and PR triage'}


def qualifies(name, event):
    if name in ('schedule', 'workflow_dispatch'):
        return True
    if name == 'workflow_run':
        run = event.get('workflow_run', {})
        return (run.get('name') in PRODUCERS
                and (run.get('head_repository') or {}).get('full_name') == REPO)
    if name in ('issues', 'issue_comment'):
        return event.get('issue', {}).get('number') != DASHBOARD
    return name == 'pull_request_target'


def cell(value):
    # Reader titles are display data, never Markdown links, mentions or HTML.
    return html.escape(str(value)).replace('\n', ' ').replace('\r', ' ').replace('|', '&#124;').replace('@', '&#64;').replace('[', '&#91;').replace(']', '&#93;').replace('`', '&#96;')


def snapshot():
    issues, prs = [], []
    for item in pages(f'repos/{REPO}/issues?state=open'):
        if item['number'] == DASHBOARD or 'pull_request' in item:
            continue
        linked = {}
        for event in pages(f'repos/{REPO}/issues/{item["number"]}/timeline'):
            source = (event.get('source') or {}).get('issue') or {}
            pr = source.get('pull_request') or {}
            # Use API-provided merge evidence, never infer resolution from mentions.
            if pr.get('merged_at') and source.get('repository_url') == f'https://api.github.com/repos/{REPO}':
                linked[source['number']] = source['number']
        issues.append({'number': item['number'], 'title': item['title'], 'merged_prs': sorted(linked),
                       'close_after_publication': any(l['name'] == 'close after publication' for l in item['labels'])})
    for pr in pages(f'repos/{REPO}/pulls?state=open'):
        prs.append({'number': pr['number'], 'title': pr['title'], 'draft': pr['draft'], 'sha': pr['head']['sha']})
    recent = api(f'repos/{REPO}/pulls?state=closed&sort=updated&direction=desc&per_page=10')
    merged = [{'number': p['number'], 'title': p['title'], 'merged_at': p['merged_at']}
              for p in recent if p.get('merged_at')]
    runs = []
    for workflow in WORKFLOWS:
        latest = api(f'repos/{REPO}/actions/workflows/{workflow}/runs?branch=curriculum-v1.2&per_page=1')['workflow_runs']
        if not latest:
            continue
        run = latest[0]
        jobs = api(f'repos/{REPO}/actions/runs/{run["id"]}/jobs?per_page=100')['jobs']
        agent = next((j for j in jobs if j['name'] == 'agent'), None)
        runs.append({'id': run['id'], 'name': run['name'], 'status': run['status'], 'conclusion': run['conclusion'],
                     'agent': (agent.get('conclusion') or agent['status']) if agent else 'not-created'})
    return {'issues': sorted(issues, key=lambda i: i['number']),
            'prs': sorted(prs, key=lambda p: p['number']), 'recent_merged': merged, 'runs': runs}


def render(data, now):
    link = f'https://github.com/{REPO}'
    lines = [MARKER, '<!-- maintenance-live-snapshot: ' + digest(data) + ' -->',
             '## 자동 현황 · AI 없이 갱신', f'마지막 상태 변경 확인: {now} (UTC)',
             'GitHub API로 집계한 현재 상태입니다. 본문의 AI 권고는 그 검토 시점의 기록이며, 이 댓글과 시점이 다를 수 있습니다.',
             f'열린 Issue **{len(data["issues"])}개** (#27 제외), 열린 PR **{len(data["prs"])}개**.',
             '| 열린 항목 | 현재 확인된 상태 |', '| --- | --- |']
    for item in data['issues']:
        state = '열림'
        if item['number'] == 6:
            state = 'gh-aw 관리 진단 기록 · 유지'
        if item['merged_prs']:
            refs = ', '.join(f'[#{n}]({link}/pull/{n})' for n in item['merged_prs'])
            state += f' · 연결 PR 병합됨: {refs}. 요청 전체 해결·게시 여부 확인 후 닫기'
        if item['close_after_publication']:
            state += ' · 승인된 교재 수정 게시 후 자동 종료 허용'
        lines.append(f'| [#{item["number"]}]({link}/issues/{item["number"]}) {cell(item["title"])} | {state} |')
    for pr in data['prs']:
        state = '초안' if pr['draft'] else '검토 대기'
        lines.append(f'| [PR #{pr["number"]}]({link}/pull/{pr["number"]}) {cell(pr["title"])} | {state} · `{pr["sha"][:7]}` · [검사]({link}/pull/{pr["number"]}/checks) |')
    if not data['issues'] and not data['prs']:
        lines.append('| 없음 | 열린 항목 없음 |')
    lines += ['', '### 최근 병합', '최근 갱신된 닫힌 PR 10개 중 병합된 항목입니다. 병합만으로 게시 완료를 뜻하지 않습니다.']
    lines += [f'- [PR #{p["number"]}]({link}/pull/{p["number"]}) {cell(p["title"])} · {p["merged_at"]}' for p in data['recent_merged']]
    lines += ['', '### 자동 검토 실행 상태', '아래는 각 워크플로의 최신 실행입니다. `skipped`/`not-created`는 AI 검토 완료가 아닙니다.']
    lines += [f'- [{cell(r["name"])}]({link}/actions/runs/{r["id"]}): 실행 `{r["conclusion"] or r["status"]}`, AI agent `{r["agent"]}`.' for r in data['runs']]
    lines += ['', f'[수동 검토·서비스 복구 안내]({link}/blob/curriculum-v1.2/docs/review-recovery.ko.md)',
              '이 집계는 Issue를 닫거나 PR을 병합하지 않습니다. 관리자 판단·사유는 원래 글의 댓글에 남겨 주세요.']
    return '\n\n'.join(lines[:6]) + '\n\n' + '\n'.join(lines[6:]) + '\n'


def main():
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text()) if os.environ.get('GITHUB_EVENT_PATH') else {}
    if not qualifies(os.environ.get('GITHUB_EVENT_NAME', 'workflow_dispatch'), event):
        return
    board = api(f'repos/{REPO}/issues/{DASHBOARD}')
    if board['title'] != DASHBOARD_TITLE or 'pull_request' in board:
        raise ValueError('Maintenance dashboard identity does not match')
    if board['state'] != 'open':
        return
    comments = pages(f'repos/{REPO}/issues/{DASHBOARD}/comments')
    existing = next((c for c in comments if c.get('user', {}).get('login') == 'github-actions[bot]'
                     and c.get('body', '').startswith(MARKER)), None)
    data = snapshot()
    marker = '<!-- maintenance-live-snapshot: ' + digest(data) + ' -->'
    if existing and marker in existing['body']:
        print('No state change; preserving the existing factual snapshot')
        return
    body = render(data, datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M'))
    if existing:
        subprocess.run(['gh', 'api', f'repos/{REPO}/issues/comments/{existing["id"]}', '--method', 'PATCH', '--input', '-'],
                       input=json.dumps({'body': body}), text=True, capture_output=True, check=True)
    else:
        api(f'repos/{REPO}/issues/{DASHBOARD}/comments', {'body': body})
    print('Updated factual maintenance status')


if __name__ == '__main__':
    main()
