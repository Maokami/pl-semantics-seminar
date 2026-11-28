"""Apply seminar order to the navigation of the rendered Verso editions."""
import html
import re
import subprocess
from review_index import chapter_reviews
from study import chapter_tools
from passages import address_passages
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PARTS = (
    (1, 21, "IMP", "Part 1 · IMP"),
    (22, 32, "함수와 타입", "Part 2 · Functions and Types"),
    (33, 38, "논리 관계와 PCF", "Part 3 · Logical Relations and PCF"),
)
REFERENCES = (
    ("imp-card", "IMP language card"),
    ("machine-card", "Stack machine card"),
    ("lambda-card", "Lambda language card"),
    ("glossary", "Glossary"),
)


def units(ko=False):
    parts = [(1, 7, "실행 규칙과 구조적 귀납", "")] if ko else PARTS
    for first, last, korean, english in parts:
        yield first, last, korean, english, range(first, last + 1)


@lru_cache(maxsize=None)
def chapter_slug(n, ko=False):
    folder = ROOT / ("PLBook/Ko" if ko else "PLBook")
    source = (folder / f"Ch{n:02}.lean").read_text()
    return re.search(r'^file := "([^"]+)"$', source, re.M)[1]


def titles():
    folder = ROOT / "PLBook"
    return {int(p.stem[2:]): re.search(r'^#doc \(Manual\) "([^"]+)"', p.read_text(), re.M)[1]
            for p in folder.glob('Ch*.lean')}


def chapter_link(n, ko=False):
    return f'{chapter_slug(n, ko)}/index.html'


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

def course_nav(groups, names, current, sidebar):
    blocks = []
    for first, _, _, label, chapters in groups:
        rows = []
        for n in chapters:
            meeting = f'Session {n}'
            active = ' aria-current="page"' if current == n else ''
            rows.append(f'<li><a{active} href="{chapter_link(n)}"><span class="meeting-no">{meeting}</span>'
                        f' · {html.escape(names[n])}</a></li>')
        listing = '<ul>' + ''.join(rows) + '</ul>'
        if sidebar:
            opened = ' open' if current in chapters or (current is None and first == 1) else ''
            blocks.append(f'<details{opened}><summary>{label}</summary>{listing}</details>')
        else:
            blocks.append(f'<section><h3>{label}</h3>{listing}</section>')
    return '<div class="course-toc">' + ''.join(blocks) + '</div>'


def update_pages(site):
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    groups = list(units())
    names = titles()
    order = [n for *_, chapters in groups for n in chapters]
    by_slug = {chapter_slug(n): n for n in order}
    for p in [site/'index.html', *site.glob('*/index.html')]:
        s = p.read_text()
        if 'split-toc book' not in s:
            continue
        ch = by_slug.get(p.parent.name)
        tag = f'ch{ch:02}' if ch else p.parent.name
        if ch or any(tag == slug for slug, _ in REFERENCES):
            # Verso links to the part tag but leaves its own page heading untagged.
            s = re.sub(r'(<section>\s*)<h1>', rf'\1<h1 id="{tag}">', s, count=1)
        more = ''.join(f'<a class="guide-link" href="{slug}/index.html">{label}</a>'
                       for slug, label in REFERENCES)
        # Verso uses a heading div for some releases, so anchor on this book's first table.
        pattern = r'(<div class="split-toc book">(?:(?!<table>).)*?)<table>.*?</table>'
        s, k = re.subn(pattern, lambda m: m[1]+more+course_nav(groups,names,ch,True),s,count=1,flags=re.S)
        if k != 1: raise ValueError(f'Book navigation missing in {p}')
        if p == site/'index.html':
            s, k = re.subn(r'<ol class="section-toc">.*?</ol>',lambda m: course_nav(groups,names,ch,False),s,count=1,flags=re.S)
            if k != 1: raise ValueError(f'Root navigation missing in {p}')
        if ch or p == site/'index.html':
            s = reader_buttons(s, ch, order, names)
        if ch:
            s = address_passages(s)
            chapter_url = f'chapter-{ch:02}/'
            s, reviews = chapter_reviews(s, ch)
            tools = chapter_tools(ch, names[ch], revision, s, reviews)
            s = s.replace('<strong>Board case.</strong>',
                          f'<strong><a href="{chapter_url}#board-exercise">Board case.</a></strong>', 1)
            sources = re.search(r'<h2 id="([^"]+)">(?:(?!</h2>).)*Sources and Formalization', s, re.S)
            if sources:
                s = s.replace('<strong>In this session.</strong>', '<strong>In this session.</strong> '
                              + f'<a href="{chapter_url}#{sources[1]}">Sources and proof status</a>', 1)
            before, nav, after = s.rpartition('<nav class="prev-next-buttons">')
            if not nav:
                raise ValueError(f'Chapter navigation missing in {p}')
            s = before + tools + nav + after
        p.write_text(s.replace('<html>', '<html lang="en">', 1))
