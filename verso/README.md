# Programming Languages

[교재 첫 화면](site/html-multi/index.html) · [회차별 주제와 원전](../docs/curriculum.ko.md)

영어 장 원고는 `PLBook/Ch01.lean`부터 `PLBook/Ch38.lean`까지다. [루트 문서](PLBook.lean)가 장과 부록의 순서를 정한다. 절 태그 `chNN-sK`는 `chapter-NN/index.html` 안에서 해당 절을 가리킨다.

| 원고 | 내용 |
|---|---|
| [IMP Language Card](PLBook/LanguageCard.lean) | 산술식, 상태, 명령의 실행과 전이, 증명 출처 |
| [Stack Machine Card](PLBook/MachineCard.lean) | 명령어, 기계 구성, 코드 배치와 컴파일 |
| [Lambda Language Card](PLBook/LambdaCard.lean) | 바인딩, 평가, 타입 판단과 안전성 표 |
| [Glossary](PLBook/Glossary.lean) | 검사 표시의 의미, 부별 용어, 한국어 대응어와 정의 위치 |

## 빌드

Lean과 Verso 버전은 [lean-toolchain](lean-toolchain)과 [lake-manifest.json](lake-manifest.json)에 고정했다. 이 디렉터리에서 다음 명령을 실행한다.

```sh
lake build +PLBook.Ch03
python3 build_site.py --edition en
```

첫 명령은 3회 원고와 그 원고가 가져오는 Lean 증명을 검사한다. 두 번째 명령은 전체 영어 책을 생성하고 첫 화면과 사이드바에 회차별 차례를 붙인다. 출력은 `site/html-multi/index.html`이다. 한국어 초안은 [PLBook/Ko](PLBook/Ko)에 보관한다.
