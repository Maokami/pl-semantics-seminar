# /// script
# requires-python = ">=3.11"
# dependencies = ["playwright==1.65.2", "pypdf==7.1.1"]
# ///
"""Generate chapter handouts and a bookmarked volume from the rendered Verso manual.

Usage: uv run print_book.py [path/to/html-multi] [--chrome PATH]
Requires an installed Chrome or Chromium and the complete rendered manual.
"""
import argparse
import contextlib
import html
import io
import os
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
from threading import Thread
from urllib.parse import urlparse

from playwright.sync_api import sync_playwright
from pypdf import PdfReader, PdfWriter

from editions import units

ROOT = Path(__file__).resolve().parent
TITLE = "Programming Languages"
CSS = """
@page {
  size: A4; margin: 18mm 21mm 19mm;
  @bottom-left {content: 'Programming Languages'; font: 8pt Arial, sans-serif; color: #475569;}
  @bottom-right {content: counter(page); font: 9pt Arial, sans-serif; color: #253650;}
}
html, body {padding:0!important; margin:0!important; height:auto!important;
  display:block!important; position:static!important; overflow:visible!important;
  min-width:0!important; background:white!important;}
body {width:168mm!important; max-width:168mm!important; color:#18202b;
  font: 11pt/1.49 Georgia, 'Times New Roman', serif!important;}
.print-chapter, .print-front {margin:0; padding:0; width:100%; max-width:none;
  display:block; position:static;}
.print-chapter + .print-chapter, .print-front + .print-chapter,
.print-front + .print-front {break-before:page;}
.print-chapter section {margin:0; padding:0; max-width:none;}
.print-chapter p, .print-front p {font:inherit; margin:0 0 8pt; orphans:3; widows:3;
  text-indent:0!important; color:inherit;}
.print-chapter h1, .print-chapter h2, .print-chapter h3, .print-front h1, .print-front h2 {
  display:block; font-family:Georgia, 'Times New Roman', serif; text-wrap:balance;
  break-after:avoid-page; color:#142c3d; line-height:1.17; border:0;
  padding:0; margin:15pt 0 7pt;}
.print-chapter h1, .print-front h1 {font-size:26pt; margin:0 0 13pt;}
.print-chapter h2, .print-front h2 {font-size:17pt;}
.print-chapter h3 {font-size:13pt;}
.print-chapter .chapter-no, .print-front .chapter-no {
  font:700 10pt/1.1 Arial,sans-serif; color:#435d6e; margin:0 0 7pt;
  break-after:avoid-page;}
.print-chapter pre, .print-chapter code.hl.lean.block, .print-chapter pre code {
  white-space:pre-wrap!important; overflow-wrap:anywhere!important;
  tab-size:3; max-width:100%!important; height:auto!important; overflow:visible!important;}
.print-chapter pre, .print-chapter code.hl.lean.block {
  display:block; box-sizing:border-box; background:#f1f4f6!important;
  padding:6pt 8pt!important; margin:5pt 0 9pt!important; border:0!important;
  box-decoration-break:clone; border-left:2pt solid #8596a0!important;}
.print-chapter pre code.hl.lean.block {margin:0!important; padding:0!important;
  border:0!important;}
.print-chapter code:not(.math), .print-chapter pre {
  font-family:'Menlo','DejaVu Sans Mono',monospace!important;
  font-size:8.7pt; line-height:1.44; overflow-wrap:anywhere;}
.print-chapter code:not(.math) {white-space:normal;}
.print-chapter pre code:not(.math) {white-space:pre-wrap;}
.print-chapter .tactic::after, .print-chapter .tactic label::after {content:none!important;}
.print-chapter .hl .tactic, .print-chapter .hl .tactic > * {display:inline;}
.print-chapter .tactic-state, .print-chapter input, .print-chapter .permalink-widget,
.print-chapter button, .print-chapter .split-toc, .print-chapter .section-toc,
.print-chapter nav {display:none!important;}
.print-chapter code.math {font:inherit; background:transparent!important;
  padding:0!important; border:0!important; color:inherit;}
.print-chapter code.math.display {display:block; width:100%; overflow:visible!important;
  margin:8pt 0; text-align:center; break-inside:avoid-page;}
.print-chapter .katex-display {margin:0!important; overflow:visible!important;}
.print-chapter .katex-display > .katex {display:inline-block;}
.print-chapter .katex {font-size:1.03em;}
.print-chapter ul, .print-chapter ol {padding-left:22pt; margin:4pt 0 8pt;}
.print-chapter li {margin:0 0 3pt;}
.print-chapter table {border-collapse:collapse; width:100%; font-size:.94em;}
.print-chapter table td, .print-chapter table th {padding:3pt 5pt; vertical-align:top;}
.print-chapter tr, .print-chapter figure, .print-chapter h1, .print-chapter h2 {break-inside:avoid;}
.print-chapter a, .print-front a {color:#27475a; text-decoration:underline;
  text-decoration-thickness:.4pt; overflow-wrap:anywhere;}
.print-chapter a:not([href]) {color:inherit; text-decoration:none;}
.schedule {font:10pt/1.46 "Apple SD Gothic Neo",sans-serif; word-break:keep-all;}
.schedule h1 {font:700 21pt "Apple SD Gothic Neo",sans-serif; margin:0 0 10pt;}
.schedule .meeting {border-top:.5pt solid #becbd0; padding:5pt 0 4pt; break-inside:avoid;}
.schedule h3 {font:700 12pt "Apple SD Gothic Neo",sans-serif; margin:1pt 0 3pt;}
.schedule .meeting p {margin:0 0 2pt;}
.schedule .reading {font-size:9pt; color:#435d6e;}
.print-front .contents {list-style:none; margin:12pt 0 0; padding:0;}
.print-front .contents li {margin:0; padding:3pt 0; border-bottom:.4pt solid #d3dadc;}
.print-front .contents a {display:flex; gap:9pt; text-decoration:none; color:inherit;}
.print-front .contents .chapter-index {min-width:15pt; color:#466373;}
.print-front .contents .folio {margin-left:auto; color:#466373;}
"""
EXTRACT = """
([n, ko]) => {
 const original = document.querySelector('main section');
 if (!original) throw Error('Missing chapter body');
 const body = original.cloneNode(true);
 body.querySelectorAll('.permalink-widget,.tactic-state,.tactic-toggle,.split-toc,.section-toc,button,input,nav,script').forEach(el => el.remove());
 for (const link of body.querySelectorAll('a[href^="print/"]')) {
   const paragraph = link.closest('p');
   if (paragraph && !paragraph.textContent.includes('Sources')) paragraph.remove();
 }
 const heading = body.querySelector('h1');
 if (!heading) throw Error('Missing chapter heading');
 const title = heading.textContent.trim().replace(/^\\d+\\.\\s*/, '');
 heading.textContent = title;
 body.querySelectorAll('h2,h3').forEach(h => {
   // Verso numbering precedes a second editorial section number in some manuals.
   const lead = h.firstChild;
   if (lead && lead.nodeType === Node.TEXT_NODE) {
     lead.textContent = lead.textContent.replace(/^(\\s*)(\\d+(?:\\.\\d+)+)\\.\\s+\\2(?=\\s)/, '$1$2');
   }
 });
 const label = document.createElement('p');
 label.className = 'chapter-no'; label.textContent = ko ? '제' + n + '장' : 'Chapter ' + n;
 heading.before(label);
 const article = document.createElement('article'); article.className = 'print-chapter';
 article.id = 'print-ch-' + n;
 article.append(body);
 for (const a of article.querySelectorAll('a[href]')) {
   const url = new URL(a.getAttribute('href'), document.baseURI);
   if (url.origin === location.origin) {
     // Local proof navigation is an interactive feature; external source links remain usable.
     a.removeAttribute('href');
   } else {a.href = url.href;}
 }
 document.body.replaceChildren(article);
 return title;
}
"""
FIT = """
async () => {
 await document.fonts.ready;
 for (const math of document.querySelectorAll('.math.display .katex-display > .katex')) {
   const container = math.closest('.math.display');
   const ratio = container.clientWidth / math.getBoundingClientRect().width;
   if (ratio < .99) math.style.fontSize = (Math.min(1,ratio)*.98) + 'em';
 }
 await document.fonts.ready;
}
"""


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self, format, *args):
        pass


@contextlib.contextmanager
def serve(site):
    handler = partial(QuietHandler, directory=site)
    with ThreadingHTTPServer(("127.0.0.1", 0), handler) as server:
        Thread(target=server.serve_forever, daemon=True).start()
        try:
            yield f"http://127.0.0.1:{server.server_port}"
        finally:
            server.shutdown()


def chrome_path(override):
    candidates = (override, os.environ.get("CHROME_BIN"),
                  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
                  shutil.which("google-chrome"), shutil.which("chromium"),
                  shutil.which("chromium-browser"))
    for path in candidates:
        if path and Path(path).is_file():
            return path
    raise SystemExit("Install Chrome or provide its executable with --chrome.")


def print_current(page):
    return page.pdf(prefer_css_page_size=True, print_background=True, tagged=False)


def contents(chapters, groups, ko):
    entries = {n: (title, start) for n, title, start in chapters}
    pages = [groups] if ko else [groups[:3],groups[3:]]
    result = []
    for i, subset in enumerate(pages):
        heading = "차례" if ko else ("Contents" if i == 0 else "Contents, continued")
        sections = [f'<section class="print-front"><h1>{heading}</h1>']
        for first, last, korean, english, numbers in subset:
            title = f"{first}–{last}회 · {korean}" if ko else f"Sessions {first}–{last} · {english}"
            sections.append(f'<h3>{html.escape(title)}</h3><ol class="contents">')
            for n in numbers:
                name, start = entries[n]
                sections.append(f'<li><a href="#print-ch-{n}"><span class="chapter-index">{n:02}</span>'
                                f'{html.escape(name)}<span class="folio">{start}</span></a></li>')
            sections.append('</ol>')
        result.append("".join(sections) + "</section>")
    return "".join(result)


def generate(site, chrome, ko=False):
    groups = list(units(ko))
    numbers = [n for *_, chapter_weeks in groups for n in chapter_weeks]
    filename = "pl-study-ko.pdf" if ko else "pl-study.pdf"
    book_title = "프로그래밍 언어 이론" if ko else TITLE
    expected = [site / f"chapter-{i:02}/index.html" for i in numbers]
    if missing := [str(f) for f in expected if not f.is_file()]:
        raise SystemExit(f"Generate the complete Verso site first. Missing {missing[0]}")
    with TemporaryDirectory(dir=site, prefix=".print-") as scratch, serve(site) as base, sync_playwright() as api:
        directory = Path(scratch)
        browser = api.chromium.launch(executable_path=chrome, args=["--disable-dev-shm-usage"])
        page = browser.new_page(viewport={"width": 900, "height": 1100})
        # Local KaTeX and Verso styles are sufficient. Block requests to remote CDNs.
        page.route("**/*", lambda route: route.continue_() if urlparse(route.request.url).netloc
                   == urlparse(base).netloc else route.abort())
        page.emulate_media(media="print")
        page.goto(base + "/", wait_until="load")
        paragraphs = page.locator("main .titlepage > p")
        intro_parts = [p.inner_text() for p in paragraphs.all() if not p.locator("a").count()]
        if not ko: intro_parts = intro_parts[:2]
        if len(intro_parts) < 2:
            raise ValueError("Expected the two introduction paragraphs on the book title page.")
        intro = "".join(f'<p>{html.escape(" ".join(p.split()))}</p>' for p in intro_parts)
        subtitle = '한국어판 · 1–7회' if ko else 'English edition · Sessions 1–42'
        cover = (f'<section class="print-front"><p class="chapter-no">{subtitle}</p>'
                 f'<h1>{book_title}</h1>{intro}</section>')
        css = CSS + ('@page {@bottom-left {content:"프로그래밍 언어 이론"}}' if ko else '')
        css += '.print-front .contents {margin:3pt 0}.print-front .contents li {padding:1.8pt 0}.print-front h3 {margin:9pt 0 3pt}'

        chapters, articles = [], []
        next_page = 3 if ko else 4  # cover and one or two contents pages
        for number in numbers:
            page.goto(f"{base}/chapter-{number:02}/", wait_until="load")
            title = page.evaluate(EXTRACT, [number, ko])
            page.add_style_tag(content=css)
            page.evaluate(FIT)
            errors = page.locator(".katex-error").all_text_contents()
            if errors:
                raise ValueError(f"Unrendered math in chapter {number}: {errors[:3]}")
            pdf = print_current(page)
            pages = len(PdfReader(io.BytesIO(pdf)).pages)
            chapters.append((number, title, next_page))
            next_page += pages
            (directory / f"chapter-{number:02}.pdf").write_bytes(pdf)
            articles.append(page.locator(".print-chapter").evaluate("el => el.outerHTML"))
            print(f"{number:02} {title}: {pages} pages", flush=True)
        # Use the already typeset chapter bodies and the same local KaTeX styles.
        page.evaluate("""(body) => {
          document.querySelectorAll('link[rel=stylesheet]').forEach(el => {el.href = el.href;});
          document.querySelector('base')?.remove();
          document.title = 'Programming Languages';
          document.body.innerHTML = body;
        }""", cover + contents(chapters, groups, ko) + "".join(articles))
        page.evaluate("document.fonts.ready")
        pdf = print_current(page)
        reader = PdfReader(io.BytesIO(pdf))
        if len(reader.pages) != next_page - 1:
            raise ValueError(f"Expected {next_page-1} combined pages, rendered {len(reader.pages)}. Check front matter and section breaks.")
        for number, title, start in chapters:
            dest = reader.named_destinations.get(f"/print-ch-{number}")
            if dest is None or reader.get_destination_page_number(dest) != start - 1:
                raise ValueError(f"Chapter {number} did not begin on its contents page {start}.")
        writer = PdfWriter(clone_from=reader)
        writer.add_metadata({"/Title": book_title, "/Author": "PL Study Group"})
        entries = {n: (title, page_no) for n, title, page_no in chapters}
        for first, last, korean, english, weeks in groups:
            part = korean if ko else english
            parent = writer.add_outline_item(part,entries[next(iter(weeks))][1]-1)
            for n in weeks:
                title, page_no = entries[n]
                writer.add_outline_item(f"{n}. {title}", page_no-1, parent=parent)
        with (directory / filename).open("wb") as stream:
            writer.write(stream)
        destination = site / "print"
        destination.mkdir(exist_ok=True)
        for pdf_file in directory.glob("*.pdf"):
            pdf_file.replace(destination / pdf_file.name)
        print(f"{len(reader.pages)} total pages; {destination / filename}")
        browser.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path, default=ROOT / "site/html-multi", nargs="?")
    parser.add_argument("--chrome")
    parser.add_argument("--edition", choices=["en","ko","both"], default="both")
    args = parser.parse_args()
    if args.edition != "ko": generate(args.site.resolve(), chrome_path(args.chrome))
    if args.edition != "en": generate(args.site.resolve() / "ko", chrome_path(args.chrome), True)
