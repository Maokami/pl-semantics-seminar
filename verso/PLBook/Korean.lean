import PLBook.Ko.Ch01
import PLBook.Ko.Ch02
import PLBook.Ko.Ch03
import PLBook.Ko.Ch25
import PLBook.Ko.Ch04
import PLBook.Ko.Ch05
import PLBook.Ko.Ch06

open Verso.Genre Manual

#doc (Manual) "프로그래밍 언어 이론" =>
%%%
authors := ["PL 스터디"]
tag := "pl-study-ko"
%%%

이 책은 실행 규칙과 구조적 귀납을 공부하는 1–7회 교재다. 산술식의 값을 계산하는 함수에서 출발해 실행을 유도하는 규칙을 세우고, 같은 명령의 두 가지 운영적 의미론이 종료 결과에 관해 일치함을 증명한다.

4회에는 25장의 초기 대수를 읽는다. 장·절·정리 번호는 영문판과 같으며, 차례는 모임 순서를 따른다. 각 장에는 정의와 증명, Lean 예제, 연습문제와 풀이가 있다.

[판단 표기](chapter-01/index.html#ch01-s4) · [한국어판 PDF](print/pl-study-ko.pdf) · [English edition](../index.html) · [42회 강의계획서](../seminar/index.html)

*용어와 표기.* 상태(state)는 변수 이름을 정수에 대응시키는 함수다. 구성(configuration)은 실행 중인 명령과 현재 상태의 쌍이다. 환경(environment)은 이름에 값을 대응시키는 것으로, 이 단원에서는 명령이 갱신하는 상태와 구별한다. 유도(derivation)는 추론 규칙을 적용한 기록이며 유도 트리(derivation tree)로 나타낸다.

큰걸음 의미론(big-step semantics)은 종료한 명령과 그 시작·종료 상태를 한 판단으로 연결한다. 작은걸음 의미론(small-step semantics)은 한 구성에서 다음 구성으로 가는 전이(transition)를 정의한다. 결정성(determinacy)은 같은 입력에 서로 다른 결과가 나올 수 없다는 성질이다. 발산(divergence)은 실행이 무한히 이어지는 경우다.

구조적 귀납법(structural induction)은 구문의 생성자를 따라 증명한다. 유도에 대한 귀납법(induction on derivations)은 마지막 규칙과 그 전제의 유도를 따라 증명한다. 초기 대수(initial algebra)의 보편 성질은 생성자에 해석을 지정하면 그 해석을 보존하는 준동형(homomorphism)이 유일하게 정해진다는 것이다.

판단(judgment)은 규칙으로 뒷받침할 주장의 형식이고 유도는 그 주장을 얻는 증거다. 역전(inversion)은 주어진 결론을 만들 수 있는 마지막 규칙을 조사해 전제를 복원하는 추론이다. 접기(fold)는 구문 트리의 각 생성자를 주어진 연산으로 해석하는 함수다. 실행이 막힌 구성(stuck configuration)은 정상 종료 구성과 다르며 다음 전이도 없다. 반면 발산하는 실행에는 무한한 전이열이 있다.

{include 1 PLBook.Ko.Ch01}

{include 1 PLBook.Ko.Ch02}

{include 1 PLBook.Ko.Ch03}

{include 1 PLBook.Ko.Ch25}

{include 1 PLBook.Ko.Ch04}

{include 1 PLBook.Ko.Ch05}

{include 1 PLBook.Ko.Ch06}
