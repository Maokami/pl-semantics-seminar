"""Add chapter discussions to the rendered textbook."""
import html
import json
from pathlib import Path
from urllib.parse import urlencode

ROOT = Path(__file__).resolve().parent
THREADS = json.loads((ROOT / "static/study-threads.json").read_text())
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


def chapter_tools(number, title, revision):
    tag = f"Session {number:02}"
    thread = THREADS.get(str(number))
    discussion = f"{REPO}/discussions/{thread}" if thread else f"{REPO}/discussions?{urlencode({'discussions_q': tag})}"
    ask = f"{REPO}/discussions/new?{urlencode({'category': 'q-a', 'title': f'[{tag}] '})}"
    unanswered = f"{REPO}/discussions?{urlencode({'discussions_q': f'category:Q&A is:unanswered "{tag}"'})}"
    issue = f"{REPO}/issues/new?{urlencode({'title': f'[{tag}] ', 'labels': 'textbook feedback', 'body': f'Chapter: {title}\nRevision: {revision}\n\nCurrent text or section:\n\nSuggested change and reason:\n'})}"
    node = lambda url: html.escape(url, quote=True)
    prompt = ""
    if number in PROOFS:
        q, *steps = PROOFS[number]
        prompt = '<details class="board"><summary>Reconstruct the proof</summary><p>' + q + '</p>'
        for label, step in zip(("Hint", "Premises", "Conclusion"), steps):
            prompt += f'<details><summary>{label}</summary><p>{step}</p></details>'
        prompt += f'<p><a href="https://github.com/Maokami/pl-semantics-labs/blob/main/Exercises/Session{number:02}.lean">Try the Lean exercise</a></p></details>'
    return f"""<aside class="study" data-session="{number:02}" data-thread="{thread or ''}" data-revision="{revision}" aria-label="Study group">
<h2>Study group</h2>
<p><a href="{node(discussion)}">Chapter discussion</a> · <a href="{node(ask)}">Ask a question</a> · <a href="{node(issue)}">Suggest a correction</a></p>
{prompt}
<details class="presenter"><summary>Prepare to present</summary><div class="study-links"></div>
<p><a href="{node(discussion)}">Read the chapter thread</a> · <a href="{node(unanswered)}">Unanswered questions</a> · <a href="{REPO}/issues?q=is%3Aissue+is%3Aopen+%22%5BSession+{number:02}%5D%22">Open chapter issues</a> · <a href="{REPO}/issues?q=is%3Aopen+label%3A%22seminar+agenda%22">Meeting briefs</a></p></details>
<details class="saved"><summary>My reading notes</summary><div></div></details>
<details class="comments"><summary>Discuss this chapter</summary><div class="giscus"></div></details>
<small><a href="{REPO}/commits/{revision}/verso/PLBook/Ch{number:02}.lean">Chapter history</a> · <a href="{REPO}/issues?q=is%3Aclosed+label%3A%22textbook+feedback%22+%22%5BSession+{number:02}%5D%22">Resolved feedback</a></small>
</aside><script defer src="static/study.js"></script>"""
