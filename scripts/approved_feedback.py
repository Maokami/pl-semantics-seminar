"""Recognize only the exact maintainer-approved Chapter 1 submission."""
import hashlib
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[1] / 'feedback/submissions/chapter01-review.ko.md'


def submission_body():
    text = SOURCE.read_text().strip()
    if not text:
        raise ValueError('Approved feedback must not be empty')
    key = hashlib.sha256(text.encode()).hexdigest()
    return ('_관리자 요청으로 승인된 원고를 자동 게시했습니다. 아래 내용은 교재 개정 제안이며, '
            '반영은 별도 PR 검토 후 결정합니다._\n\n' + text
            + '\n\n<!-- approved-reader-feedback: chapter01:' + key + ' -->')


def approved_post(post):
    user = post.get('user') or post.get('author') or {}
    return (user.get('type', user.get('__typename')) == 'Bot'
            and user.get('login') in ('github-actions', 'github-actions[bot]')
            and post.get('body') == submission_body())
