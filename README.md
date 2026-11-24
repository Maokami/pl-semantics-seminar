# 프로그래밍 언어 이론 스터디

운영적·표시적·공리적 의미론, 타입 이론, 영역 이론, 컴파일러 정확성과 정적 분석을 공부하는 42회 스터디 교재다. 영어판은 42장 전체를, 한국어판은 1–7회에 읽는 1·2·3·25·4·5·6장을 수록한다.

[영어판](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/) · [한국어판](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/ko/) · [42회 읽기 일정](https://pl-semantics-seminar.moonlitwhale2.chatgpt.site/seminar/)

## 원고와 빌드 코드

| 작업 | 파일 |
|---|---|
| 영어 본문과 Lean 예제 편집 | [verso/PLBook](verso/PLBook) 아래의 Ch01.lean–Ch42.lean |
| 한국어 본문과 Lean 예제 편집 | [verso/PLBook/Ko](verso/PLBook/Ko) |
| 회차별 읽을 절, 원전, 발표 문제 변경 | [verso/sessions.json](verso/sessions.json) |
| Verso 사이트와 언어별 차례 생성 | [build_site.py](verso/build_site.py), [editions.py](verso/editions.py), [seminar.py](verso/seminar.py) |
| 장별 PDF와 책갈피가 있는 합본 생성 | [print_book.py](verso/print_book.py) |
| 한국어 강의계획서 조판 | [curriculum.typ](curriculum.typ), [style.typ](style.typ) |

각 장은 본문·수식·Lean 코드 블록을 함께 담은 Verso 문서다. [1장](verso/PLBook/Ch01.lean)은 산술식의 평가 함수와 귀납적 평가 관계를 정의한 뒤 두 정의의 대응을 증명한다. [25장](verso/PLBook/Ch25.lean)은 식 트리의 fold를 정의하고 유일성을 증명한다. Lean은 빌드할 때 코드 블록의 정의와 증명을 검사한다. 본문에 산문으로 전개한 증명도 있다.

## 빌드

Lean과 Lake는 elan으로 실행한다. Lean과 Verso 버전은 [lean-toolchain](verso/lean-toolchain)과 [lake-manifest.json](verso/lake-manifest.json)에 고정했다. 전체 출력에는 Python 3.11 이상, uv, Typst, Chrome 또는 Chromium이 필요하다. 현재 인쇄본의 한국어 글꼴은 macOS의 Apple SD Gothic Neo다.

저장소 루트에서 다음 명령을 실행한다.

```sh
typst compile curriculum.typ curriculum.pdf
cd verso
python3 check_translation.py
python3 build_site.py
uv run print_book.py
python3 -m http.server 8042 --bind 127.0.0.1 --directory site/html-multi
```

브라우저에서 <http://127.0.0.1:8042/>를 열면 영어판, `/ko/`를 열면 한국어판이 나온다. 합본 PDF는 웹 출력 폴더의 `print/pl-study.pdf`와 `ko/print/pl-study-ko.pdf`에 생성된다. 강의계획서 PDF는 `print/syllabus-ko.pdf`에 복사된다.

한 장만 수정했을 때는 `verso/`에서 `lake build +PLBook.Ch01`로 그 장의 본문과 Lean 예제를 검사할 수 있다. 한국어판 1장은 `lake build +PLBook.Ko.Ch01`로 검사한다. 두 언어판의 수식·코드·원전 링크 대조에는 `python3 check_translation.py`를 쓴다.
