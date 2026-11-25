"""Generate the English and Korean Verso manuals and their seminar navigation."""
import argparse
from pathlib import Path
import shutil
import subprocess

from check_translation import check_pilot_terms
from editions import update_pages
from seminar import render_guide

ROOT = Path(__file__).resolve().parent
SITE = ROOT / "site/html-multi"


def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def build(ko):
    if ko:
        check_pilot_terms()
    render_guide()
    chapter_dir = ROOT / ("PLBook/Ko" if ko else "PLBook")
    modules = [("PLBook.Ko." if ko else "PLBook.") + p.stem for p in sorted(chapter_dir.glob("Ch*.lean"))]
    for i in range(0,len(modules),3):
        run("lake","build",*["+"+m for m in modules[i:i+3]])
    run("lake","build","+PLBook.Korean" if ko else "+PLBook")
    out = ROOT / ("site-ko" if ko else "site")
    run("lake","env","lean","--run","MainKo.lean" if ko else "Main.lean","--output",str(out))
    stage = out/"html-multi"
    if ko:
        (stage/"static").mkdir(exist_ok=True)
        for name in ("reader.css","reader.js","marked.min.js"):
            shutil.copy2(ROOT/"static"/name, stage/"static"/name)
    external = "https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js"
    for page in [stage/'index.html', *stage.glob('*/index.html')]:
        if page.parent == stage/'ko': continue
        markup = page.read_text()
        if external in markup:
            start = markup.index('<script src="' + external)
            end = markup.index("</script>", start)
            page.write_text(markup[:start] + '<script src="static/marked.min.js">' + markup[end:])
    update_pages(stage,ko)
    if ko:
        shutil.copytree(stage,SITE/"ko",dirs_exist_ok=True)
    else:
        (SITE/"print").mkdir(exist_ok=True)
        shutil.copy2(ROOT.parent/"curriculum.pdf", SITE/"print/syllabus-ko.pdf")


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument('--edition',choices=['en','ko','both'],default='both')
    edition=parser.parse_args().edition
    if edition!='ko': build(False)
    if edition!='en': build(True)
