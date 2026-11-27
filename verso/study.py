"""Add chapter discussions to the rendered textbook."""
import html
import json
import re
from pathlib import Path
from urllib.parse import urlencode

ROOT = Path(__file__).resolve().parent
THREADS = json.loads((ROOT / "static/study-threads.json").read_text())
LAB_REVISION = "75e26a2974b0b802b4fd2b439cc790b4e14a26e0"
LAB_REPO = "https://github.com/Maokami/pl-semantics-labs"
REPO = "https://github.com/Maokami/pl-semantics-seminar"
# Each prompt exposes one premise at a time for use at the board.
PROOFS = {
    1: ("Derive the value of x + 4 when σ(x) = 3.",
        "Use the addition rule. What evidence does each operand need?",
        "Lookup gives σ ⊢ x ⇓ 3. The literal rule gives σ ⊢ 4 ⇓ 4.",
        "The addition rule yields σ ⊢ x + 4 ⇓ 7."),
    2: ("Derive x := 1; y := x + 3 from the all-zero state σ.",
        "Choose the state between the two commands.",
        "The first assignment yields μ = σ[x ↦ 1]. The second reads μ(x), so it yields τ = μ[y ↦ 4].",
        "Sequencing joins the two premises at μ to derive σ ⊢ (x := 1; y := x + 3) ⇓ τ."),
    3: ("Two runs of c; d start at σ and finish at τ and υ. Show τ = υ.",
        "Invert the second sequence derivation. Name the two intermediate states μ and ν.",
        "Apply the first induction hypothesis to the two runs of c from σ. It gives μ = ν.",
        "Substitute this equality. Both runs of d now start at the same state, so the second induction hypothesis gives τ = υ."),
}


def board_exercise(number, page):
    if number in PROOFS:
        question, *steps = PROOFS[number]
        hints = zip(("Hint", "Premises", "Conclusion"), steps)
    else:
        # Reuse the edited session card, including Verso's links and math markup.
        card = page.partition('<strong>In this session.</strong>')[2].partition('</ul>')[0]
        def card_item(label):
            match = re.search(r'<strong>' + re.escape(label) + r'</strong>\s*(.*?)</p>', card, re.S)
            if not match:
                raise ValueError(f"Session {number} is missing its {label} card entry")
            return match[1]
        question = card_item("Board case.")
        hints = [("Show proof outline", card_item("Proof outline."))]
    details = "".join(f'<details><summary>{label}</summary><p>{step}</p></details>' for label, step in hints)
    return f'<details class="board"><summary>Reconstruct the proof</summary><p>{question}</p>{details}</details>'


def chapter_tools(number, title, revision, page):
    tag = f"Session {number:02}"
    thread = THREADS.get(str(number))
    discussion = f"{REPO}/discussions/{thread}" if thread else f"{REPO}/discussions?{urlencode({'discussions_q': tag})}"
    ask = REPO + "/discussions/new?" + urlencode({"category": "q-a", "title": f"[{tag}] "})
    unanswered = REPO + "/discussions?" + urlencode({"discussions_q": f'category:"Q&A" is:unanswered "{tag}"'})
    issue_body = f"Chapter: {title}\nRevision: {revision}\n\nCurrent text or section:\n\nSuggested change and reason:\n"
    issue = REPO + "/issues/new?" + urlencode({"title": f"[{tag}] ", "template": "correction.md", "body": issue_body})
    node = lambda url: html.escape(url, quote=True)
    picker = '<p class="passage-help">Select text in the chapter to share it. <button type="button" class="passage-picker">Choose a passage</button> · <a href="https://github.com/Maokami/pl-semantics-seminar/blob/curriculum-v1.2/docs/reader-guide.ko.md" lang="ko">스터디 이용 안내</a></p>'
    questions = f"{REPO}/discussions?" + urlencode({"discussions_q": f'category:"Q&A" "{tag}"'})
    discussion_tools = f"""<div class="chapter-questions"><div class="questions-heading"><h3>Questions from readers</h3><button type="button" class="refresh-questions" aria-label="Refresh chapter questions" hidden>Refresh</button></div>
<div class="question-feed" aria-live="polite"></div>
<div class="study-actions"><a data-compose="question" href="{node(ask)}">Ask a question</a><a href="{node(questions)}">All chapter questions ↗</a></div></div>
<div class="comments" id="chapter-discussion" tabindex="-1">
<h3>Chapter discussion</h3>
<p class="discussion-help">Reply in English or Korean using your GitHub account. <a href="{node(discussion)}">View on GitHub ↗</a></p>
<div class="giscus"></div></div>"""
    prompt = board_exercise(number, page)
    lab = workbook_script = ""
    if number <= 3:
        workbook_script = '<script defer src="static/workbook.js"></script>'
        lab = f"""<div class="lean-lab" data-session="{number:02}" data-revision="{LAB_REVISION}">
<h3>Lean workbook</h3><p class="lab-instruction"></p>
<div class="lab-actions"><button class="lab-start" type="button" hidden>Open Lean editor</button>
<a href="https://codespaces.new/Maokami/pl-semantics-labs?quickstart=1">Open project workspace ↗</a></div>
<p class="lab-path"><a href="{LAB_REPO}/blob/{LAB_REVISION}/Exercises/Session{number:02}.lean"><code>Exercises/Session{number:02}.lean</code></a></p>
<p role="status" class="lab-status"></p></div>"""
    source = f"{REPO}/blob/{revision}/verso/PLBook/Ch{number:02}.lean"
    history = f"{REPO}/commits/{revision}/verso/PLBook/Ch{number:02}.lean"
    proposals = f"{REPO}/pulls?" + urlencode({"q": f'is:pr label:"reader proposal" "[Session {number:02}]"'})
    queue = f"{REPO}/pulls?" + urlencode({"q": 'is:pr is:open label:"reader proposal"'})
    corrections = f"{REPO}/issues?" + urlencode({"q": f'is:issue label:"textbook feedback" "[{tag}]"'})
    return f"""<aside class="study" lang="en" data-session="{number:02}" data-thread="{thread or ''}" data-revision="{revision}" aria-label="Study together">
<div class="study-head"><h2 id="study-together" tabindex="-1">Study together</h2></div>
{picker}
{discussion_tools}
<div class="meeting-tools" aria-label="Seminar preparation">{prompt}{lab}
<details class="presenter"><summary>Prepare to present<small>Readings and meeting agenda</small></summary><div class="study-links"></div><p><a href="{node(unanswered)}">Unanswered questions</a> · <a href="{REPO}/issues?q=is%3Aopen+label%3A%22seminar+agenda%22">Meeting briefs</a></p></details></div>
<details class="saved" hidden><summary>Saved passages</summary><div></div></details>
<section class="feedback-progress" aria-label="Correction review status">
<h3>Corrections and review</h3>
<p>New or changed reader feedback triggers review. Pending proposals wait for a maintainer’s decision; a daily check catches missed feedback. Proposed edits need approval before publication.</p>
<div class="correction-feed" aria-live="polite"></div>
<p><a href="{node(proposals)}">Chapter review decisions</a> · <a href="{node(corrections)}">All chapter corrections</a></p>
<details><summary>How review works</summary><p>Suggest a correction with its section and reason. AI compares it with the current manuscript and prepares a proposal. The maintainer checks the changes and build result, then merges or closes the proposal. The original discussion links to the decision; a merged change appears after a successful textbook build.</p>
<p><a href="{node(queue)}">Maintainer review queue</a> · <a href="{REPO}/blob/curriculum-v1.2/docs/feedback-maintenance.ko.md" lang="ko">승인·거부 안내</a></p></details>
</section>
<footer><div><a data-compose="correction" href="{node(issue)}">Suggest a correction</a> · <a href="{node(corrections)}">Track corrections</a></div>
<div>Manuscript <a class="source-revision" href="{node(source)}">{revision[:7]}</a> · <a href="{node(history)}">Chapter history</a></div></footer>
</aside><link rel="stylesheet" href="static/composer.css"><script defer src="static/study-math.js"></script><script defer src="static/composer.js"></script>{workbook_script}<script defer src="static/study.js"></script>"""
