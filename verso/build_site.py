"""Build the English textbook and its navigation in site/html-multi."""
import argparse
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

from editions import update_pages

ROOT = Path(__file__).resolve().parent


def build():
    site = ROOT / "site"
    site.mkdir(exist_ok=True)
    subprocess.run(["lake", "build", "+PLBook"], cwd=ROOT, check=True)
    with TemporaryDirectory(dir=site) as work:
        out = Path(work)
        subprocess.run(["lake", "env", "lean", "--run", "Main.lean", "--output", str(out)],
                       cwd=ROOT, check=True)
        stage = out / "html-multi"
        for page in [stage / "index.html", *stage.glob("*/index.html")]:
            text = page.read_text()
            external = "https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js"
            if external in text:
                page.write_text(re.sub(r'<script src="' + re.escape(external) + r'"[^>]*>',
                                       '<script src="static/marked.min.js">', text))
        update_pages(stage)
        destination = site / "html-multi"
        if destination.exists():
            destination.rename(out / "previous")
        stage.rename(destination)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edition", choices=["en"], default="en")
    parser.parse_args()
    build()
