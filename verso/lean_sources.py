"""Publish the checked Lean modules and the two in-chapter proof blocks as readable HTML."""
from html import escape, unescape
from pathlib import Path
import re
import shutil

BOOK = Path(__file__).resolve().parent / "PLBook"
DECLARATION = re.compile(
    r"^(?:@\[[^\]]+\] )*(?:(?:private|noncomputable|protected) )*"
    r"(?:inductive|structure|theorem|lemma|abbrev|def)\s+([\w']+)"
)
# Constructors referenced by name on the IMP card.
CONSTRUCTOR = re.compile(r"^  \| (cexec_\w+)\s*:")


def document(title, content):
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width">
<title>{escape(title)} · Lean sources</title><link rel="stylesheet" href="source.css"></head>
<body><nav><a href="../index.html">Programming Languages</a> · <a href="index.html">Lean sources</a></nav>
<main><h1>{escape(title)}</h1>{content}</main></body></html>
"""


def write_lean_sources(site):
    out = site / "lean"
    out.mkdir()
    imp = BOOK / "IMP"
    modules = {p.stem: p.read_text() for p in sorted(imp.glob("*.lean"))}
    for block in re.findall(r"^```lean\n(.*?)^```$", (BOOK / "Ch33.lean").read_text(), re.M | re.S):
        namespace = re.search(r"^namespace (\w+)$", block, re.M)[1]
        modules[namespace] = block
    (out / "source.css").write_text("""
body {max-width:80rem; margin:auto; padding:1.5rem; font:1rem/1.55 system-ui,sans-serif; color:#192631}
a {color:#1d567c} nav {margin-bottom:2rem} h1 {font-size:1.6rem}
pre {background:#f5f7f8; padding:1rem; overflow-x:auto; tab-size:2; font:0.95rem/1.55 ui-monospace,monospace}
code span:target {background:#fff1ac; outline:2px solid #c18b17; scroll-margin-top:3rem}
""".lstrip())
    shutil.copyfile(imp / "LICENSE.md", out / "LICENSE.txt")
    entries = []
    targets = {"lean/index.html"}
    for name, source in modules.items():
        url = f"lean/{name}.html"
        targets.add(url)
        lines = []
        for line in source.splitlines():
            declaration = DECLARATION.match(line) or CONSTRUCTOR.match(line)
            if declaration:
                targets.add(f"{url}#{declaration[1]}")
                anchor = escape(declaration[1], quote=True)
                lines.append(f'<span id="{anchor}">{escape(line)}</span>')
            else:
                lines.append(escape(line))
        listing = "<pre><code>" + "\n".join(lines) + "\n</code></pre>"
        if name == "Language":
            listing += '<p><a href="LICENSE.txt">License for the adapted IMP definitions</a></p>'
        title = f"PLBook.IMP.{name}" if (imp / f"{name}.lean").exists() else f"Session 33 · {name}"
        (out / f"{name}.html").write_text(document(title, listing))
        entries.append(f'<li><a href="{name}.html">{escape(title)}</a></li>')
    (out / "index.html").write_text(document("Lean sources", "<ul>" + "".join(entries) + "</ul>"))

    for page in site.glob("*/index.html"):
        for link in re.findall(r'href="(lean/[^"]+)"', page.read_text()):
            if unescape(link) not in targets:
                raise ValueError(f"{page.relative_to(site)} links to a missing Lean declaration: {link}")
