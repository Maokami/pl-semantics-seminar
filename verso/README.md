# Programming Languages

[영어판 42회](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/index.html) · [한국어판 1–7회](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/ko/index.html) · [모임별 읽을 절과 원전](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/seminar/index.html) · [장별 분량 검토](chapter-review.ko.md)

한국어판은 1–7장 전체를 수록한다. 웹 차례와 인쇄본은 모임 순서를 따르고, 장·절·정리 번호는 두 언어에서 같다.

[영문 PDF](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/print/pl-study.pdf) · [한국어 PDF](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/ko/print/pl-study-ko.pdf) · [한국어 강의계획서](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/print/syllabus-ko.pdf)

## 원고

영문 본문은 PLBook/ChNN.lean, 번역은 PLBook/Ko/ChNN.lean에 있다. PLBook/Korean.lean의 용어 해설을 따르고, 번역에서 수식·Lean 코드·절 태그를 보존한다. sessions.json은 회차, 읽기 범위, 원전 및 문제를 지정한다. 운영 자료는 수학 본문과 별도로 구성한다.

파일명 ChNN.lean의 NN은 차례에 표시되는 장 번호다. 원고의 `file`과 `tag`는 장별 웹 주소·PDF 링크·절 책갈피를 식별한다. 장을 재배치할 때도 이미 공유한 링크가 같은 내용을 열 수 있도록 이 식별자를 유지한다.

## 수식 표기

식의 큰걸음 평가는 `σ ⊢ e ⇓ n`, 명령의 큰걸음 실행은 `σ ⊢ c ⇓ σ′`로 쓴다. 상태를 인자로 받는 평가 함수는 `eval(e,σ)`다. §1.4–1.5에서 판단을 정의하고 함수와의 대응을 증명한다. 작은걸음은 `⟨c,σ⟩ → ⟨c′,σ′⟩`, 영 번 이상의 전이는 `→*`, 정확히 n번의 전이는 `→ⁿ`로 쓴다. 닫힌 항의 평가에는 `t ⇓ v`를 쓴다. 환경이나 저장소를 추가하는 언어는 판단을 정의할 때 그 구성 요소를 명시한다.

타입 판단은 `Γ ⊢ t : A`다(§18.1). 호어 논리에서 `⊢_H {P} c {Q}`는 증명 체계에서의 유도 가능성을, `⊨ {P} c {Q}`는 모든 종료 실행에 대한 부분 정확성을 뜻한다(§11.1). 원전의 다른 규약은 해당 절에서 대조하고 Lean 식별자는 원전의 철자를 따른다.

## 빌드

Lean과 Verso 버전은 lean-toolchain과 lake-manifest.json에 고정되어 있다. Typst, Python 3, uv, Chrome 또는 Chromium을 사용한다.

```sh
typst compile ../curriculum.typ ../curriculum.pdf
python3 build_site.py
uv run print_book.py
python3 -m http.server 8042 --bind 127.0.0.1 --directory site/html-multi
```

build_site.py는 두 Verso 책을 생성하고 회차표로 탐색 순서를 정한다. print_book.py는 이 HTML에서 수식과 Lean 코드를 조판한 뒤 pypdf로 실제 장 시작 쪽과 책갈피를 연결한다. 두 스크립트 모두 --edition en 또는 --edition ko를 받는다. 한 장만 검사하려면 lake build +PLBook.Ch18 또는 lake build +PLBook.Ko.Ch03을 사용한다.
