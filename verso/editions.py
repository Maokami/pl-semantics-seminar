"""Apply seminar order to the navigation of the rendered Verso editions."""
import html
import re
from pathlib import Path

from seminar import chapter_slug, study_groups

ROOT = Path(__file__).resolve().parent
EN_UNITS = [
    'Execution Rules and Structural Induction', 'Denotational and Axiomatic Semantics',
    'Lambda Calculus and Function Types', 'Type Inference and Polymorphism',
    'Domain Theory and PCF', 'State, Control and Concurrency',
    'Compiler Correctness and Static Analysis',
]


def units(ko=False):
    groups = study_groups()
    for i, group in enumerate(groups[:1] if ko else groups):
        rows = group['sessions']
        weeks = {}
        for row in rows:
            for span in row['read']:
                n = int(span.split('.')[0])
                if row['week'] not in weeks.setdefault(n, []):
                    weeks[n].append(row['week'])
        yield rows[0]['week'], rows[-1]['week'], group['title'], EN_UNITS[i], weeks


def titles(ko):
    folder = ROOT / ('PLBook/Ko' if ko else 'PLBook')
    return {int(p.stem[2:]): re.search(r'^#doc \(Manual\) "([^"]+)"', p.read_text(), re.M)[1]
            for p in folder.glob('Ch*.lean')}


def chapter_link(n):
    return f'{chapter_slug(n)}/index.html'


def reader_buttons(page, current, order, names):
    position = order.index(current) if current is not None else -1
    buttons = []
    for rel, offset in [('prev', -1), ('next', 1)]:
        j = position + offset
        if 0 <= j < len(order):
            n = order[j]
            where = f'<span class="where">{n}. {html.escape(names[n])}</span>'
            arrow = '<span class="arrow">←</span>' if offset < 0 else '<span class="arrow">→</span>'
            body = arrow + where if offset < 0 else where + arrow
            buttons.append(f'<a class="local-button active" rel="{rel}" href="{chapter_link(n)}">{body}</a>')
    return re.sub(r'<nav class="prev-next-buttons">.*?</nav>',
                  lambda _: '<nav class="prev-next-buttons">' + ''.join(buttons) + '</nav>',
                  page, flags=re.S)

def course_nav(groups, names, ko, current, sidebar):
    blocks = []
    for first, last, title, english, chapters in groups:
        label = f'{first}–{last}회 · {title}' if ko else english
        rows = []
        for n, weeks in chapters.items():
            if ko:
                meeting = '·'.join(map(str, weeks)) + '회'
            else:
                meeting = ('Session ' if len(weeks) == 1 else 'Sessions ') + '–'.join(map(str, weeks))
            active = ' aria-current="page"' if current == n else ''
            rows.append(f'<li><a{active} href="{chapter_link(n)}"><span class="meeting-no">{meeting}</span>'
                        f' <span>{n}. {html.escape(names[n])}</span></a></li>')
        listing = '<ul>' + ''.join(rows) + '</ul>'
        if sidebar:
            opened = ' open' if current in chapters or (current is None and first == 1) else ''
            blocks.append(f'<details{opened}><summary>{label}</summary>{listing}</details>')
        else:
            blocks.append(f'<section><h3>{label}</h3>{listing}</section>')
    return '<div class="course-toc">' + ''.join(blocks) + '</div>'


def update_pages(site, ko=False):
    groups = list(units(ko))
    names = titles(ko)
    order = [n for *_, chapters in groups for n in chapters]
    by_slug = {chapter_slug(n): n for n in order}
    for p in [site/'index.html', *site.glob('*/index.html')]:
        if p.parent.parent == site and p.parent.name == 'ko':
            continue
        s = p.read_text()
        if 'split-toc book' not in s:
            continue
        ch = by_slug.get(p.parent.name)
        guide = '../seminar/index.html' if ko else 'seminar/index.html'
        guide_label = '이전 판 42회 읽기 일정' if ko else 'Reading schedule (Korean)'
        more = f'<a class="guide-link" href="{guide}">{guide_label}</a>'
        if ko:
            more += '<a class="guide-link" href="imp-card/index.html">IMP 언어 카드</a>'
            more += '<a class="guide-link" href="glossary/index.html">1–3회 용어집</a>'
            langlink = '../' + (chapter_link(ch) if ch else 'index.html')
            more += f'<a class="guide-link" href="{langlink}">English edition</a>'
        # Verso uses a heading div for some releases, so anchor on this book's first table.
        pattern = r'(<div class="split-toc book">(?:(?!<table>).)*?)<table>.*?</table>'
        s, k = re.subn(pattern, lambda m: m[1]+more+course_nav(groups,names,ko,ch,True),s,count=1,flags=re.S)
        if k != 1: raise ValueError(f'Book navigation missing in {p}')
        if p == site/'index.html':
            s, k = re.subn(r'<ol class="section-toc">.*?</ol>',lambda m: course_nav(groups,names,ko,ch,False),s,count=1,flags=re.S)
            if k != 1: raise ValueError(f'Root navigation missing in {p}')
        if ch or p == site/'index.html':
            s = reader_buttons(s, ch, order, names)
        s=s.replace('<html>', '<html lang="ko">' if ko else '<html lang="en">',1)
        if ko:
            s=s.replace('<html lang="en"','<html lang="ko"').replace('>Table of Contents<','>차례<')
            s=re.sub(r'(<h2>\s*)Contents(</h2>)',r'\1차례\2',s)
        p.write_text(s)
