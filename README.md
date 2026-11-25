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
