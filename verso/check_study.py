"""Check that published study links match the rendered session."""
from pathlib import Path
from html.parser import HTMLParser

ROOT = Path(__file__).resolve().parent / "site/html-multi"


class Chapter(HTMLParser):
    def __init__(self):
        super().__init__()
        self.passages = []
        self.panels = []
        self.links = []
        self.scripts = []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if "data-passage" in a:
            self.passages.append(a["id"])
        if tag == "aside" and "data-session" in a:
            self.panels.append(a)
        if tag == "script":
            self.scripts.append(a.get("src"))
        if tag == "a" and "href" in a:
            self.links.append(a["href"])


for i in range(1, 39):
    chapter = Chapter()
    page = (ROOT / f"chapter-{i:02}/index.html").read_text()
    chapter.feed(page)
    assert len(chapter.passages) == len(set(chapter.passages)) >= 10, i
    assert all(anchor.startswith(f"ch{i:02}") for anchor in chapter.passages), i
    assert page.count('class="passage-picker"') == 1
    assert page.count('id="chapter-discussion"') == 1 and '<details class="comments">' not in page
    assert page.index('class="chapter-questions"') < page.index('id="chapter-discussion"'), i
    assert page.count('class="giscus"') == page.count('class="question-feed"') == 1
    assert "docs/reader-guide.ko.md" in page
    if i == 1:
        assert 'ch01-s1-p-definition-1-2' in chapter.passages
    assert len(chapter.panels) == 1 and chapter.panels[0]["data-session"] == f"{i:02}"
    assert any("pl-semantics-seminar/issues/new?" in link for link in chapter.links)
    assert chapter.scripts.count("static/composer.js") == 1
    assert chapter.scripts.index("static/study-math.js") < chapter.scripts.index("static/composer.js")
    assert ("static/workbook.js" in chapter.scripts) == (i <= 3)
    for section_name in ("Exercises", "Reading for the Seminar", "Solutions and Further Reading", "Sources and Formalization"):
        assert section_name in page, (i, section_name)
    assert page.count('id="study-together"') == 1
    assert page.index('id="study-together"') < page.rindex('<nav class="prev-next-buttons">')
    for action in ("question", "correction"):
        assert page.count(f'data-compose="{action}"') == 1
    revision = chapter.panels[0]["data-revision"]
    assert any(link.endswith(f"/blob/{revision}/verso/PLBook/Ch{i:02}.lean") for link in chapter.links)
    assert page.count('class="correction-feed"') == 1
    assert 'Maintainer review queue' in page and 'Chapter review decisions' in page
    assert 'docs/feedback-maintenance.ko.md' in page
    assert page.count('class="board"') == 1
    assert (f'Exercises/Session{i:02}.lean' in page) == (i <= 3)
    assert ('class="lean-lab"' in page) == (i <= 3)
    assert ('<summary>Show proof outline</summary>' in page) == (i > 3)
    thread = chapter.panels[0]["data-thread"]
    if thread:
        assert any(link.endswith("/discussions/" + thread) for link in chapter.links)
for asset in ("study.js", "study-math.js", "composer.js", "composer.css", "workbook.js"):
    assert (ROOT / "static" / asset).is_file(), asset
print("38 chapters checked, including the three Lean exercises and discussion threads.")
