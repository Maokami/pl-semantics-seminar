"""Check that published study links match the rendered session."""
from pathlib import Path
from html.parser import HTMLParser

ROOT = Path(__file__).resolve().parent / "site/html-multi"


class Chapter(HTMLParser):
    def __init__(self):
        super().__init__()
        self.panels = []
        self.links = []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "aside" and "data-session" in a:
            self.panels.append(a)
        if tag == "a" and "href" in a:
            self.links.append(a["href"])


for i in range(1, 39):
    chapter = Chapter()
    chapter.feed((ROOT / f"chapter-{i:02}/index.html").read_text())
    assert len(chapter.panels) == 1 and chapter.panels[0]["data-session"] == f"{i:02}"
    assert any("pl-semantics-seminar/issues/new?" in link for link in chapter.links)
    if i <= 3:
        assert any(link.endswith(f"Exercises/Session{i:02}.lean") for link in chapter.links)
        assert any(link.endswith("/discussions/" + chapter.panels[0]["data-thread"]) for link in chapter.links)
assert (ROOT / "static/study.js").is_file()
print("38 chapters checked, including the three Lean exercises and discussion threads.")
