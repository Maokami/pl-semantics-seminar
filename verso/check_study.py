"""Check that published study links match the rendered session."""
from pathlib import Path
from html.parser import HTMLParser

ROOT = Path(__file__).resolve().parent / "site/html-multi"


class Chapter(HTMLParser):
    def __init__(self):
        super().__init__()
        self.panels = []
        self.links = []
        self.scripts = []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
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
    assert len(chapter.panels) == 1 and chapter.panels[0]["data-session"] == f"{i:02}"
    assert any("pl-semantics-seminar/issues/new?" in link for link in chapter.links)
    assert ("study-pilot" in chapter.panels[0]["class"].split()) == (i <= 3)
    assert ("static/composer.js" in chapter.scripts) == (i <= 3)
    assert ("static/workbook.js" in chapter.scripts) == (i <= 3)
    for section_name in ("Exercises", "Reading for the Seminar", "Solutions and Further Reading", "Sources and Formalization"):
        assert section_name in page, (i, section_name)
    if i <= 3:
        assert page.count('id="study-together"') == 1
        assert page.index('id="study-together"') < page.rindex('<nav class="prev-next-buttons">')
        for action in ("question", "correction"):
            assert page.count(f'data-compose="{action}"') == 1
        revision = chapter.panels[0]["data-revision"]
        assert any(link.endswith(f"/blob/{revision}/verso/PLBook/Ch{i:02}.lean") for link in chapter.links)
        assert any(link.endswith(f"Exercises/Session{i:02}.lean") for link in chapter.links)
        assert any(link.endswith("/discussions/" + chapter.panels[0]["data-thread"]) for link in chapter.links)
for asset in ("study.js", "composer.js", "composer.css", "workbook.js"):
    assert (ROOT / "static" / asset).is_file(), asset
print("38 chapters checked, including the three Lean exercises and discussion threads.")
