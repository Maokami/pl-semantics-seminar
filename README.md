# 프로그래밍 언어 이론 스터디

영어 교재는 정규 32회와 조건부 6회로 구성한다. 1부(1–21회)는 IMP의 의미론, 컴파일러 정확성과 정적 분석을 다룬다. 2부(22–32회)는 함수와 타입, 3부(33–38회)는 논리 관계와 PCF를 다룬다. [확정 커리큘럼과 회차별 원전](docs/curriculum.ko.md)

각 장의 첫 페이지에서 대표 정리, 출처, 칠판에서 전개할 증명 경우를 찾을 수 있다. 세 언어 카드에는 정의와 규칙을, 영어–한국어 용어집에는 토론에 쓸 대응어와 처음 정의한 절을 모았다. [교재 원고](verso/PLBook.lean) · [용어집](verso/PLBook/Glossary.lean)

[공개 교재](https://maokami.github.io/pl-semantics-seminar/) · [스터디원 이용 안내](docs/reader-guide.ko.md)

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

[Textbook on Sites](https://pl-semantics-textbook.moonlitwhale2.chatgpt.site/) ·
[GitHub Pages mirror](https://maokami.github.io/pl-semantics-seminar/) ·
[Reader discussions](https://github.com/Maokami/pl-semantics-seminar/discussions)

The Pages workflow rebuilds the English edition when book sources change on
`curriculum-v1.2`. The Sites edition uses the same static output. Both sites use
the same GitHub discussion identifiers. To resolve a correction, review the
proposed change in a manuscript PR, then reply with the published chapter and
commit. Use the issue's close reason to distinguish an applied correction from
a declined proposal.

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
