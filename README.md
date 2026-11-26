# 프로그래밍 언어 이론 스터디

영어 교재는 정규 32회와 조건부 6회로 구성한다. 1부(1–21회)는 IMP의 의미론, 컴파일러 정확성과 정적 분석을 다룬다. 2부(22–32회)는 함수와 타입, 3부(33–38회)는 논리 관계와 PCF를 다룬다. [확정 커리큘럼과 회차별 원전](docs/curriculum.ko.md)

각 장의 첫 페이지에서 대표 정리, 출처, 칠판에서 전개할 증명 경우를 찾을 수 있다. 세 언어 카드에는 정의와 규칙을, 영어–한국어 용어집에는 토론에 쓸 대응어와 처음 정의한 절을 모았다. [교재 원고](verso/PLBook.lean) · [용어집](verso/PLBook/Glossary.lean)

## 빌드

```sh
cd verso
python3 build_site.py
python3 -m http.server 8042 --bind 127.0.0.1 --directory site/html-multi
```

로컬 브라우저에서 [교재 첫 화면](http://127.0.0.1:8042/)을 연다. 버전과 개별 장 검사 방법은 [Verso 빌드 안내](verso/README.md)에 있다.

## Reading with the seminar

In Sessions 1–3, choose **질문 쓰기** or **수정 제안** at the chapter heading, or select a passage first to quote it. Write in the book, then review and post on GitHub. The current tab keeps your draft when you close the form. Choose **의견·답글 쓰기** to join the chapter conversation on the page.

Read the same chapter before the meeting. Use **Chapter discussion** for a shared
conversation or **Ask a question** to open a Q&A thread whose answer can be marked.
Select a passage and choose **Suggest a correction** to include the quote, section
and source revision in a public GitHub issue. Korean and English are both welcome.
**Save for rereading** keeps a note in the current browser on the current host.
The presenter can open **Prepare to present** for readings, unanswered questions
and meeting briefs. Sessions 1–3 include proof prompts and Lean exercises.

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

**Copilot feedback check** is a manually dispatched second opinion on an open
issue labeled `textbook feedback`. Its suggested reply is staged in the run
report for a maintainer. Set the repository secret `COPILOT_GITHUB_TOKEN` to
a personal fine-grained token with the account permission **Copilot Requests:
Read**. The workflow uses automatic model selection and a five-AI-credit cap.
