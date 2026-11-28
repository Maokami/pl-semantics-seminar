# 프로그래밍 언어 이론 스터디

영어 교재는 정규 32회와 조건부 6회로 구성한다. 1부(1–21회)는 IMP의 의미론, 컴파일러 정확성과 정적 분석을 다룬다. 2부(22–32회)는 함수와 타입, 3부(33–38회)는 논리 관계와 PCF를 다룬다. [확정 커리큘럼과 회차별 원전](docs/curriculum.ko.md)

각 장의 첫 페이지에서 대표 정리, 출처, 칠판에서 전개할 증명 경우를 찾을 수 있다. 세 언어 카드에는 정의와 규칙을, 영어–한국어 용어집에는 토론에 쓸 대응어와 처음 정의한 절을 모았다. [교재 원고](verso/PLBook.lean) · [용어집](verso/PLBook/Glossary.lean)

[공개 교재](https://maokami.github.io/pl-semantics-seminar/) · [스터디원 이용 안내](docs/reader-guide.ko.md)

공개판은 영어 38장입니다. 한국어 1–7장 초안은 [원고 폴더](verso/PLBook/Ko)에 있습니다. [질문하기](https://github.com/Maokami/pl-semantics-seminar/discussions/categories/q-a) · [정정 제안](https://github.com/Maokami/pl-semantics-seminar/issues/new?template=correction.md) · [직접 PR로 고치기](docs/feedback-maintenance.ko.md#사람이-직접-고치는-경우)

Actions나 Claude 사용량에 도달하면 [수동 검토·결제·재개 안내](docs/review-recovery.ko.md)를 이용하세요.

## 빌드

```sh
cd verso
python3 build_site.py
python3 -m http.server 8042 --bind 127.0.0.1 --directory site/html-multi
```

로컬 브라우저에서 [교재 첫 화면](http://127.0.0.1:8042/)을 연다. 버전과 개별 장 검사 방법은 [Verso 빌드 안내](verso/README.md)에 있다.

## Reading with the seminar

Open **Exercises → Reconstruct the proof** to try the chapter’s board case.
Sessions 1–3 also include a **Lean workbook**. The editor loads the matching learner sheet and
its IMP definitions from one pinned workbook revision into Lean 4.35.0. Use
the editor's download option to keep a proof. Choose **Open project workspace** for
multi-file development, repository tests and later labs with additional dependencies.
Only self-contained exercises with a tested playground project get an inline editor.

Open **Reading for the Seminar** for the session agenda, outstanding questions
and meeting briefs. Solutions and source notes have separate disclosures. Direct
section links open the referenced material, and printing includes the chapter text.

Use **Study together** in any chapter to read existing questions or start one.
Selecting a passage attaches the quote and section to a question or correction;
the correction also records the manuscript revision. Comments may be in Korean
or English. Saved passages are private to the current browser on each host.

[Textbook on GitHub Pages](https://maokami.github.io/pl-semantics-seminar/) ·
[Reader discussions](https://github.com/Maokami/pl-semantics-seminar/discussions)

The Pages workflow rebuilds the English edition when book sources change on
`curriculum-v1.2`. GitHub Pages is the maintained textbook site; the existing
Sites copy is left unchanged and its automatic synchronization is disabled.
To resolve a correction, review the proposed manuscript PR and merge it after
checks pass, or comment with the reason and close the PR. Automation links the
decision and publication status back to the original reader discussion or issue.

### Presenter briefs and editing

**Seminar reading brief** checks for new feedback on Thursday at 09:13 KST.
Maintainers can also run it for a chosen session before a meeting. It reads the
chapter source, groups open questions and suggests up to three topics in Korean.
Actionable results become issues labeled `seminar agenda`. Configure the Actions
secret `ANTHROPIC_API_KEY` for this repository. The primary Claude session has
a ten-minute workflow timeout, a ten-turn limit and a USD 0.50 CLI budget.

**Reader correction review** is a manual, read-only Claude Haiku workflow for an
open issue labeled `textbook feedback`. It stages one suggested response for a
maintainer and skips unrelated issues before model inference. It uses the same
repository secret and USD 0.50 CLI budget as the reading brief. The companion
workbook audits changed labs on the first and sixteenth of each month.

For an optional Copilot second opinion, use the official Copilot CLI locally
with `--model auto`. Its availability is independent of the scheduled workflows.

### Continuous reader feedback

Repository housekeeping is summarized in the [Issue/PR maintenance dashboard](https://github.com/Maokami/pl-semantics-seminar/issues/27).
The separate continuous triage workflow recommends next actions and closure/duplicate candidates;
it does not close issues or merge PRs. See the [maintenance guide](docs/maintenance-triage.ko.md).

Labeled corrections trigger manuscript review after a short batching
delay. Closing or merging a proposal checks the waiting queue. Daily review at
09:37 KST remains as a fallback. Bot notifications do not trigger review. The AI
prepares a bounded manuscript PR for the maintainer; it never merges its own work.
Approve with **Merge** after the **Textbook verification** check, or leave a reason
and use **Comment and close pull request**. Source threads link to the decision,
and publication is reported only after a successful GitHub Pages deployment.
[Review queue](https://github.com/Maokami/pl-semantics-seminar/pulls?q=is%3Apr+is%3Aopen+label%3A%22reader+proposal%22)
· [관리자 운영 안내](docs/feedback-maintenance.ko.md)
