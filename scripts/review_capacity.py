"""Choose automated or manual review before starting a metered agent."""
from datetime import datetime, timedelta, timezone
import os
import subprocess
from pathlib import Path
from urllib.parse import urlencode

from reader_feedback import REPO, api

GUIDE = f'https://github.com/{REPO}/blob/curriculum-v1.2/docs/review-recovery.ko.md'


def hold_reason(workflow, env, now):
    mode = env.get('TEXTBOOK_AI_MODE', '') or 'auto'
    if mode != 'auto':
        return f'TEXTBOOK_AI_MODE={mode}. Use the manual review queue.'
    if env.get('HAS_KEY') != 'true':
        return 'No Claude API credential is configured.'
    if env.get('GITHUB_EVENT_NAME') == 'workflow_dispatch' and not env.get('GITHUB_ACTOR', '').endswith('[bot]'):
        return None
    # A skipped/noop success must not mask a failed model run. Bound retries on
    # the same workflow and revision. A maintainer can explicitly retry earlier.
    since = (now - timedelta(hours=24)).isoformat(timespec='seconds')
    query = urlencode({'head_sha': env['GITHUB_SHA'], 'status': 'failure',
                       'created': '>=' + since, 'per_page': 1})
    try:
        runs = api(f'repos/{REPO}/actions/workflows/{workflow}.lock.yml/runs?{query}')['workflow_runs']
    except subprocess.CalledProcessError:
        return 'Actions run history is unavailable. Check GitHub status, API rate limits and actions:read access.'
    if runs:
        return f'This workflow failed on this revision during the past 24 hours ({runs[0]["html_url"]}).'
    return None


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('workflow', choices=['reader-feedback', 'reader-correction', 'maintenance-triage', 'seminar-brief'])
    reason = hold_reason(parser.parse_args().workflow, os.environ, datetime.now(timezone.utc))
    with Path(os.environ['GITHUB_OUTPUT']).open('a') as out:
        print('ready=' + str(reason is None).lower(), file=out)
    if reason:
        with Path(os.environ['GITHUB_STEP_SUMMARY']).open('a') as summary:
            print(f'**Manual review available** · {reason}\n\n'
                  f'[Open the queue and recovery options]({GUIDE}). Feedback remains on GitHub.', file=summary)


if __name__ == '__main__':
    main()
