"""Render accepted feedback records alongside their passages in this edition."""
import html
import json
from pathlib import Path
import re

DIRECTORY = Path(__file__).resolve().parents[1] / 'feedback/reviews'
REPO = 'https://github.com/Maokami/pl-semantics-seminar'
TARGET = re.compile(r'chapter-(0[1-9]|[12][0-9]|3[0-8])/#(ch[0-9]{2}(?:-[a-z0-9]+)*)')
SOURCE = re.compile(re.escape(REPO) + r'/(issues|discussions)/([1-9][0-9]*)(?:#discussioncomment-[0-9]+)?')
LABELS = {'change': 'Published correction', 'no-change': 'Reviewed · no change', 'needs-discussion': 'Further discussion'}


def chapter_reviews(page, number):
    rows = []
    for path in sorted(DIRECTORY.glob('*.json')):
        record = json.loads(path.read_text())
        if record.get('smoke_test'):
            continue
        source = SOURCE.fullmatch(record['source_url'])
        target = TARGET.fullmatch(record['target'])
        if not source or not target or not target[2].startswith('ch' + target[1]) or path.stem != record['key']:
            raise ValueError(f'Invalid feedback record {path}')
        if int(target[1]) != number:
            continue
        anchor = target[2]
        if f'id="{anchor}"' not in page:
            raise ValueError(f'{path.name}: missing target {anchor}')
        for old in record.get('previous_anchors', []):
            if not re.fullmatch(f'ch{number:02}-[a-z0-9-]+', old) or f'id="{old}"' in page:
                raise ValueError(f'Invalid or duplicate passage alias {old}')
            # Put the historical target inside the same paragraph (also works without JS).
            page = re.sub(r'(<(?:p|pre) id="' + anchor + r'"[^>]*>)',
                          rf'\1<span id="{old}" data-current-passage="{anchor}"></span>', page, count=1)
            if f'id="{old}"' not in page:
                raise ValueError(f'Passage alias requires an addressable paragraph: {anchor}')
        label = LABELS[record['disposition']]
        rows.append(f'<li data-review-source="{source[1]}/{source[2]}">{label} · '
                    f'<a href="{html.escape(record["source_url"], quote=True)}">Feedback #{source[2]}</a> · '
                    f'<a href="{record["target"]}">View passage</a></li>')
    listing = '<ul class="published-reviews">' + ''.join(rows) + '</ul>' if rows else ''
    return page, listing
