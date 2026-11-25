import VersoManual

open Verso.Genre Manual

#doc (Manual) "1–3회 용어집" =>
%%%
tag := "pilot-glossary"
file := "glossary"
number := false
%%%

각 항목에는 한국어 표제어와 영어 이름, 처음 쓰는 회차, 정의 위치, 뜻, 금지 변형을 차례로 적었다. 시범 장에서는 상태를 $`\sigma`, 중간 상태를 $`\mu,\nu`, 종료 상태를 $`\tau`로 쓴다.

* *변수 이름(variable name)* · 1회 · [A.1](imp-card/index.html#imp-a1) · 문자열 하나로 식별하는 변수의 이름. · 금지 변형 `변수명칭`

* *산술식(arithmetic expression)* · 1회 · [A.1](imp-card/index.html#imp-a1) · 정수·변수 또는 두 식의 합이나 차로 만든 식. · 금지 변형 `산술 표현식`

* *생성자(constructor)* · 1회 · [A.1](imp-card/index.html#imp-a1) · 구문의 한 형태를 만드는 연산. · 금지 변형 `구성자`

* *상태(state)* · 1회 · [A.2](imp-card/index.html#imp-a2) · 각 변수 이름에 정수를 하나씩 주는 함수. · 금지 변형 없음

* *상태 갱신(state update)* · 1회 · [A.2](imp-card/index.html#imp-a2) · 한 이름에서의 값만 지정한 값으로 바꾼 상태. · 금지 변형 `상태 업데이트`

* *평가 함수(evaluation function)* · 1회 · [A.3](imp-card/index.html#imp-a3) · 산술식과 상태를 받아 정수를 주는 함수. · 금지 변형 없음

* *구조적 재귀(structural recursion)* · 1회 · [A.3](imp-card/index.html#imp-a3) · 직접 부분식의 결과로 식 전체의 값을 정의하는 방법. · 금지 변형 `구조 재귀`

* *구조적 귀납법(structural induction)* · 1회 · [A.3](imp-card/index.html#imp-a3) · 각 생성자에 대해 직접 부분식에서 성립하는 명제가 전체 식에서도 성립함을 보이는 방법. · 금지 변형 `구조 귀납법`

* *판단(judgment)* · 1회 · [A.3](imp-card/index.html#imp-a3) · 규칙을 통해 성립 여부를 기술하는 주장. · 금지 변형 `판정식`

* *추론 규칙(inference rule)* · 1회 · [A.3](imp-card/index.html#imp-a3) · 주어진 전제에서 어떤 결론을 얻는지 정한 규칙. · 금지 변형 `추리 규칙`

* *평가 판단(evaluation judgment)* · 1회 · [A.3](imp-card/index.html#imp-a3) · 주어진 상태에서 산술식의 값이 정수 n이라는 판단. · 금지 변형 없음

* *유도(derivation)* · 1회 · [A.3](imp-card/index.html#imp-a3) · 규칙의 전제마다 그 유도를 붙여 결론을 정당화한 유한한 나무. · 금지 변형 `도출 트리`

* *역전(inversion)* · 1회 · [A.3](imp-card/index.html#imp-a3) · 결론에서 가능한 마지막 규칙을 찾아 그 전제를 복원하는 추론. · 금지 변형 `반전 추론`

* *조건식(Boolean expression)* · 2회 · [A.4](imp-card/index.html#imp-a4) · 참 또는 거짓으로 평가되는 식. · 금지 변형 `불리언 식`

* *명령(command)* · 2회 · [A.4](imp-card/index.html#imp-a4) · 상태를 입력으로 받아 실행하는 IMP 구문. · 금지 변형 `명령문`

* *가드(guard)* · 2회 · [A.5](imp-card/index.html#imp-a5) · 분기 선택이나 반복 여부를 정하는 조건식. · 금지 변형 `가드식`

* *큰걸음 의미론(big-step semantics)* · 2회 · [A.5](imp-card/index.html#imp-a5) · 한 판단으로 명령의 시작 상태와 종료 상태를 연결하는 의미론. · 금지 변형 `큰 걸음 의미론`

* *실행 판단(execution judgment)* · 2회 · [A.5](imp-card/index.html#imp-a5) · 명령이 주어진 상태에서 실행되어 특정 상태로 종료한다는 판단. · 금지 변형 없음

* *순차 합성(sequencing)* · 2회 · [A.5](imp-card/index.html#imp-a5) · 첫째 명령의 종료 상태에서 둘째 명령을 실행하는 명령. · 금지 변형 `순차 구성`

* *결정성(determinacy)* · 3회 · [§3.2](chapter-03/index.html#ch03-s2) · 같은 명령과 초기 상태의 종료 결과가 많아야 하나인 성질. · 금지 변형 `결정적 성질`

* *유도에 대한 귀납법(induction on derivations)* · 3회 · [§3.2](chapter-03/index.html#ch03-s2) · 직접 전제의 유도에서 얻은 귀납가정으로 결론의 유도에 관한 명제를 보이는 방법. · 금지 변형 `유도 귀납법`

* *귀납가정(induction hypothesis)* · 3회 · [§3.2](chapter-03/index.html#ch03-s2) · 귀납 단계에서 작은 대상에 대해 이미 성립한다고 놓고 사용하는 명제. · 금지 변형 `귀납 가설`, `귀납가설`, `귀납 가정`
