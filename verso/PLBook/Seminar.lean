import VersoManual

open Verso.Genre Manual

#doc (Manual) "세미나 · 42회 읽기 일정" =>
%%%
tag := "seminar"
file := "seminar"
shortTitle := "Reading schedule (Korean)"
number := false
%%%

모임 전에는 ‘함께 읽을 절’을 읽고 예제의 계산을 종이에 써 봅니다. 담당자는 ‘담당자 자료’에서 해당 규칙이나 정리를 찾아 아래 과제에 필요한 식이나 유도 트리를 준비합니다. 예를 들어 3회에는 같은 순차 명령을 실행한 두 트리를 나란히 그리고, 두 중간 상태가 같아지는 곳에 귀납가정을 표시합니다.

모임은 60분입니다. 처음 10분에는 예제와 기호를 확인하고, 30분 동안 칠판에서 문제를 함께 풀고, 마지막 20분에는 다른 참가자가 핵심 단계를 다시 설명합니다. 7회와 13회에는 혼자 완성한 증명과 독서·발표 준비에 각각 걸린 시간을 확인합니다.

TAPL은 Benjamin Pierce의 _Types and Programming Languages_입니다. TAPL과 Reynolds의 목차 링크는 소장본에서 읽을 절을 찾는 데 씁니다. S1·S2·S4는 한국어 발표 자료입니다.

1–13회는 Winskel의 IMP를 따라 실행·표시·명세를 연결합니다. 작은걸음은 Concrete Semantics, 고정점은 Reynolds, 전체 정확성 실습은 Hitchhiker’s Guide를 참고합니다. 14–26회에는 TAPL의 타입 이론과 Pfenning의 표현 독립성을, 27–31회에는 Cambridge 강의 노트의 PCF를, 32–36회에는 Reynolds와 Leroy의 효과·제어·동시성을 읽고, 37–42회의 분석과 컴파일은 Leroy 강좌를 중심으로 읽습니다.

[한국어판 · 1–7회](ko/index.html) · [영문 교재 PDF](print/pl-study.pdf) · [한국어 강의계획서 PDF](print/syllabus-ko.pdf)

* [1–7회 · 실행 규칙과 구조적 귀납](seminar/index.html#week-01)
* [8–13회 · 표시적 의미론과 공리적 의미론](seminar/index.html#week-08)
* [14–20회 · 람다 계산과 함수 타입](seminar/index.html#week-14)
* [21–26회 · 타입 추론과 다형성](seminar/index.html#week-21)
* [27–31회 · 영역 이론과 PCF](seminar/index.html#week-27)
* [32–36회 · 상태·제어·동시성](seminar/index.html#week-32)
* [37–42회 · 컴파일러 정확성과 정적 분석](seminar/index.html#week-37)

# 1회 · 산술식의 평가
%%%
tag := "week-01"
number := false
%%%

*함께 읽을 절*　[§1.1–1.2](chapter-01/index.html#ch01-s1), [§1.4–1.5](chapter-01/index.html#ch01-s4)

덧셈의 경우에 평가 유도에서 함수값을, 함수값에서 평가 유도를 얻는다. 각 방향에서 무엇에 대해 귀납하는가? 변수 규칙을 지우면 어느 방향이 깨지는지 보인다.

*담당자 자료*　[Winskel §§2.1–2.2, 산술식 평가](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)

# 2회 · 명령의 big-step 의미론
%%%
tag := "week-02"
number := false
%%%

*함께 읽을 절*　[§2.1–2.3](chapter-02/index.html#ch02-s1)

순차 합성 규칙을 역전해 중간 상태의 존재를 얻고, 두 전제에서 전체 유도를 복원한다. x := x + 1; y := x에서 둘째 대입을 처음 상태로 시작하면 왜 틀리는지 설명한다. 마지막에 §2.4의 루프 탈출 규칙을 확인한다.

*담당자 자료*　[Winskel §2.4, 순차 합성 규칙](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)

# 3회 · 실행 규칙의 역전과 결정성
%%%
tag := "week-03"
number := false
%%%

*함께 읽을 절*　[§3.1–3.3](chapter-03/index.html#ch03-s1)

첫 실행 유도에 대해 귀납한다. 둘째 유도와 최종 상태를 일반화한 귀납가정을 쓰고, 순차 합성의 두 중간 상태가 같다는 사실을 얻은 뒤 마지막 상태를 비교한다. 같은 방법으로 참인 가드의 반복 규칙을 검토한다.

*담당자 자료*　[대응 원전 · Concrete Semantics §7.2.5, 보조정리 7.9](https://concrete-semantics.org/concrete-semantics.pdf)

# 4회 · 초기 대수와 구조적 재귀
%%%
tag := "week-04"
number := false
%%%

*함께 읽을 절*　[§4.1–4.3](chapter-04/index.html#ch04-s1)

임의의 식 대수에서 접기를 구성하고 구조적 귀납으로 유일성을 증명한다. 두 대수 사이의 준동형을 접기 뒤에 합성하면 도착 대수의 접기가 된다는 것을 유일성으로 도출한다.

*담당자 자료*　[S1 「Exp는 initial algebra다」](static/slides/s1/index.html#/15)

# 5회 · 한 단계 전이와 무한 실행
%%%
tag := "week-05"
number := false
%%%

*함께 읽을 절*　[§5.1–5.3](chapter-05/index.html#ch05-s1)

while true do skip의 무한 전이열을 구성한다. 그런 다음 abort를 추가해 다음 단계가 없는 유한 실행을 만든다. 두 실행 모두 정상 종료 유도가 없는데 무엇이 다른가?

*담당자 자료*　[Concrete Semantics §7.3, 한 단계 전이](https://concrete-semantics.org/concrete-semantics.pdf)

# 6회 · 두 운영적 의미론의 대응
%%%
tag := "week-06"
number := false
%%%

*함께 읽을 절*　[§6.1–6.3](chapter-06/index.html#ch06-s1)

순차 합성의 두 경로 길이가 m과 n일 때 전체 길이가 m+1+n임을 보인다. 역방향은 보조정리 6.3을 써서 마지막 skip 유도에서 출발해 한 전이씩 거슬러 복원한다.

*담당자 자료*　[Concrete Semantics §7.3.1, 종료 실행의 대응](https://concrete-semantics.org/concrete-semantics.pdf)

# 7회 · 프로그램 동치와 루프 펼침
%%%
tag := "week-07"
number := false
%%%

*함께 읽을 절*　[§7.1–7.3](chapter-06-legacy/index.html#ch06-legacy-s1)

루프 펼침 동치를 순차 문맥 안에서 사용한다. out := y를 뒤에 붙여 각 변수의 최종값을 검사하는 실험들로 전체 최종 상태 동치를 복원할 때 결정성이 왜 필요한지 증명한다.

*담당자 자료*　[Concrete Semantics §7.2.4, 명령 동치](https://concrete-semantics.org/concrete-semantics.pdf)

# 8회 · 상태 변환과 비종료
%%%
tag := "week-08"
number := false
%%%

*함께 읽을 절*　[§8.1–8.3](chapter-07/index.html#ch07-s1)

첫 명령의 결과가 정상 상태일 때와 ⊥일 때를 나눠 순차 합성을 정의하고, 세 명령을 어느 쪽부터 묶어도 결과가 같음을 보인다.

*담당자 자료*　[Reynolds §2.2, 순차 명령의 표시 의미 (목차)](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# 9회 · 루프의 유한 근사와 최소 고정점
%%%
tag := "week-09"
number := false
%%%

*함께 읽을 절*　[§9.1–9.3](chapter-08/index.html#ch08-s1)

몸체를 정확히 k번 실행하는 입력에서 결과가 처음 나타나는 근사 단계를 구한다. 연속성이 근사열의 상한을 고정점으로 만드는 자리를 찾는다.

*담당자 자료*　[Reynolds §2.4, 최소 고정점 정리 (목차)](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

*심화*　[S2 · 순서·근사·최소 고정점](static/slides/s2/index.html#/13)

# 10회 · 실행과 표시 의미의 대응
%%%
tag := "week-10"
number := false
%%%

*함께 읽을 절*　[§10.1–10.3](chapter-09/index.html#ch09-s1)

순차 합성의 중간 상태를 미리 찾는다. 모임에서는 while의 종료 유도에서 유한 근사 단계를 구하고, 반대로 단계 번호에 대한 귀납으로 종료 유도를 복원한다.

*담당자 자료*　[Winskel §5.3, 두 의미론의 동치](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)

# 11회 · Hoare 삼중항과 대입
%%%
tag := "week-11"
number := false
%%%

*함께 읽을 절*　[§11.1–11.3](chapter-10/index.html#ch10-s1)

x := x + 1 뒤에 x = 5를 보장하려면 처음에 무엇이 참이어야 하는지 구하고, 상태 갱신을 사용해 대입 규칙을 정당화한다.

*담당자 자료*　[Winskel §6.4, 대입의 부분 정확성 규칙](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)

# 12회 · 루프 불변식
%%%
tag := "week-12"
number := false
%%%

*함께 읽을 절*　[§12.1–12.3](chapter-11/index.html#ch11-s1)

합계를 구하는 루프에서 시작·몸체·탈출 시점에 각각 무엇을 보여야 하는지 적고, 한 번 더 더해도 불변식이 유지됨을 보인다. 건전성과 상대적 완전성의 질문을 각각 한 문장으로 쓴다.

*담당자 자료*　[Winskel §§6.4–6.5, while 규칙과 건전성](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)

# 13회 · 전체 정확성과 종료
%%%
tag := "week-13"
number := false
%%%

*함께 읽을 절*　[§13.1–13.3](chapter-12/index.html#ch12-s1)

두 카운터의 합을 자연수 변량으로 택한다. 몸체가 끝나고 변량이 감소한다는 두 전제를 사용해 루프의 종료를 증명한다.

*담당자 자료*　[Hitchhiker’s Guide §10.8, 전체 정확성](https://raw.githubusercontent.com/lean-forward/logical_verification_2026/460f6be0846eefc3d9441e4e48d75753fcfe1709/hitchhikers_guide_2026_desktop.pdf)

# 14회 · 바인딩과 포획 회피 치환
%%%
tag := "week-14"
number := false
%%%

*함께 읽을 절*　[§14.1–14.3](chapter-13/index.html#ch13-s1)

(λy. x)에 y를 x 대신 대입한다. 바인더를 먼저 새 이름으로 바꾼 결과와 그대로 바꾼 결과의 자유 변수를 비교한다. 이 예를 이용해 치환 뒤 자유 변수에 관한 보조정리의 추상화 경우를 증명한다.

*담당자 자료*　[TAPL §5.3, 치환 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 15회 · 값 호출과 이름 호출
%%%
tag := "week-15"
number := false
%%%

*함께 읽을 절*　[§15.1–15.3](chapter-14/index.html#ch14-s1)

쓰이지 않는 인자에 발산하는 항을 전달한다. 두 전략의 첫 전이를 적고 어느 쪽이 함수의 결과에 도달하는지 설명한다. §15.3에서 인자를 두 번 쓰면 어느 계산을 반복하는지 추적한다.

*담당자 자료*　[TAPL §5.1, 평가 전략 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 16회 · 환경과 클로저
%%%
tag := "week-16"
number := false
%%%

*함께 읽을 절*　[§16.1–16.3](chapter-15/index.html#ch15-s1)

함수가 정의된 뒤 같은 이름의 변수가 다시 바인딩된 예를 평가한다. 함수 본문의 자유 변수가 어느 환경에서 조회되는지 표시한다. 호출 시점의 환경으로 바꾸면 같은 항의 결과가 어떻게 달라지는지 확인한다.

*담당자 자료*　[Reynolds §11.2 평가 규칙, §§11.6–11.7 환경과 바인딩 (목차)](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# 17회 · Bool·Nat의 타입 안전성
%%%
tag := "week-17"
number := false
%%%

*함께 읽을 절*　[§17.1–17.3](chapter-16/index.html#ch16-s1)

닫힌 Bool 타입 값이 true나 false임을 보인다. 이 사실을 조건식의 가드에 적용해 값이 아닌 조건식이 진행함을 증명한다.

*담당자 자료*　[TAPL §8.3, 진행과 보존 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 18회 · 약화와 타입이 있는 치환
%%%
tag := "week-18"
number := false
%%%

*함께 읽을 절*　[§18.1–18.4](chapter-17/index.html#ch17-s1)

열린 인자를 람다 본문에 치환한다. 바인더를 지난 문맥에서 인자의 타입 유도가 필요한 지점을 적고 약화를 적용한다.

*담당자 자료*　[TAPL §9.3, 치환 보조정리 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 19회 · 함수 적용의 진행과 보존
%%%
tag := "week-19"
number := false
%%%

*함께 읽을 절*　[§19.1–19.3](chapter-18/index.html#ch18-s1)

β-축약 전의 타입 유도에서 함수 몸체와 인자의 타입을 복원한다. 치환 보조정리를 적용해 축약 후 항의 타입을 얻는다. 타입 보존만으로 평가가 끝난다고 결론 내릴 수 있는지도 따져 본다.

*담당자 자료*　[TAPL §9.3, 보존 정리의 β-축약 경우 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 20회 · 곱·지수 대상과 함수 적용
%%%
tag := "week-20"
number := false
%%%

*함께 읽을 절*　[§20.1–20.3](chapter-26/index.html#ch26-s1)

문맥을 곱으로 표현하고 짝짓기와 평가 사상으로 함수 적용을 해석한다. β-축약 전후 사상이 같음을 지수 대상의 등식에서 유도한다.

*담당자 자료*　[Crole §2.8, pp. 67–72, 지수 대상의 보편 성질 (출판사 서지)](https://www.cambridge.org/core/books/categories-for-types/258841251C62FED1DACD20884E59E61C)

# 21회 · 타입 검사와 타입 추론
%%%
tag := "week-21"
number := false
%%%

*함께 읽을 절*　[§21.1–21.2](chapter-19/index.html#ch19-s1), [§22.1–22.2](chapter-20/index.html#ch20-s1)

주석이 있는 (λx:Nat. x) 0의 타입을 검사한다. 주석을 지운 같은 항에서 타입 방정식을 만들고 단일화해 두 결과를 비교한다. 계산을 마친 뒤 §22.3의 풀이와 대조한다. 마지막으로 0에 대한 적용을 지우면 어떤 타입 변수가 자유롭게 남는지 설명한다.

*담당자 자료*　[TAPL §10.3 타입 검사, §§22.3–22.4 제약과 단일화 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 22회 · let 다형성
%%%
tag := "week-22"
number := false
%%%

*함께 읽을 절*　[§23.1–23.3](chapter-21/index.html#ch21-s1)

같은 let 바인딩의 항등함수를 숫자와 불 값에 적용한다. 두 사용처가 선택한 타입과 바깥 문맥 때문에 일반화할 수 없는 변수를 구분한다.

*담당자 자료*　[TAPL §22.7, let 다형성 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 23회 · 구조적 서브타이핑
%%%
tag := "week-23"
number := false
%%%

*함께 읽을 절*　[§24.1–24.3](chapter-22/index.html#ch22-s1)

필드가 두 개인 레코드를 하나만 요구하는 함수에 넘기는 타입 유도를 그린다. 함수 인자의 서브타입 방향이 반대인 이유를 설명한다.

*담당자 자료*　[TAPL §15.2, 서브타이핑 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 24회 · System F와 전칭 타입
%%%
tag := "week-24"
number := false
%%%

*함께 읽을 절*　[§25.1–25.3](chapter-23/index.html#ch23-s1)

다형적 항등함수에서 먼저 타입 인자로 Nat을, 다음에는 값 인자로 0을 전달한다. 두 치환 직후의 항과 타입을 적는다. 22회 let 예의 두 사용처에 숨었던 타입 인자를 명시한다.

*담당자 자료*　[TAPL §23.3, System F (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 25회 · 존재 타입과 표현 은닉
%%%
tag := "week-25"
number := false
%%%

*함께 읽을 절*　[§26.1–26.3](chapter-24/index.html#ch24-s1)

카운터 패키지를 새 타입 이름으로 열고 연산을 호출한다. 클라이언트의 결과 타입에 그 이름이 남으면 안 되는 이유를 보인다. 두 카운터의 초기값이 관련되고 next와 read가 그 관계를 보존하는지 확인한다.

*담당자 자료*　[TAPL §24.1, 존재 타입 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 26회 · 관계적 매개변수성과 표현 독립성
%%%
tag := "week-26"
number := false
%%%

*함께 읽을 절*　[§26.4](chapter-24/index.html#ch24-client-relation)

추상 타입 X를 두 방식으로 해석한다. 변수·추상화·적용에 대한 귀납으로 기본 정리를 증명하고, 두 카운터에서 모든 단순 타입 클라이언트의 Nat 관찰값이 같음을 도출한다.

*담당자 자료*　[Pfenning, Representation Independence §1, 표현 관계의 선택](https://www.cs.cmu.edu/~fp/courses/15814-f25/lectures/16-independence.pdf)

# 27회 · 함수 영역과 Scott 귀납법
%%%
tag := "week-27"
number := false
%%%

*함께 읽을 절*　[§27.1–27.3](chapter-27/index.html#ch27-s1)

함수 근사의 점별 상한을 계산하고, 정의된 출력이 모두 0이라는 성질을 Scott 귀납법으로 증명한다. 각 근사에 남아 있던 미정의 입력이 극한에서는 모두 사라질 수 있는 이유를 설명한다.

*담당자 자료*　[Cambridge 강의 노트 §4, 고정점 귀납법](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

*심화*　[S2 · 순서·근사·최소 고정점](static/slides/s2/index.html#/13)

# 28회 · PCF에서 재귀 함수 평가
%%%
tag := "week-28"
number := false
%%%

*함께 읽을 절*　[§28.1–28.3](chapter-28/index.html#ch28-s1)

재귀 함수 K를 입력 1에서 펼쳐 평가한다. 같은 결과가 함수의 유한 근사 중 어느 단계에서 처음 나오는지 계산한다. 먼저 fix (λx : Nat. x)가 값을 내지 못하는 이유를 19회의 보존 정리와 함께 설명한다.

*담당자 자료*　[Cambridge 강의 노트 §5.2, PCF 평가 규칙](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

# 29회 · 논리 관계의 기본 성질
%%%
tag := "week-29"
number := false
%%%

*함께 읽을 절*　[§29.1–29.2](chapter-29/index.html#ch29-s1)

열린 항 f x에서 함수 쌍과 인자 쌍이 각각 관련된다고 쓴다. 함수 타입의 관계 정의에 인자 쌍을 넣어 적용 결과도 관련됨을 유도한다.

*담당자 자료*　[Cambridge 강의 노트 정의 27과 정리 30, pp. 56–58](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

# 30회 · 기초 타입의 계산적 적절성
%%%
tag := "week-30"
number := false
%%%

*함께 읽을 절*　[§29.2–29.3](chapter-29/index.html#ch29-s2)

재귀항을 고정하고 각 유한 근사가 그 항과 관련됨을 보인다. 27회의 상한 조건을 적용한 뒤, 빈 환경과 빈 치환을 넣어 닫힌 자연수 항의 계산적 적절성을 도출한다.

*담당자 자료*　[Cambridge 강의 노트 보조정리 33·35, 정리 30–31](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

# 31회 · 문맥 동치와 완전 추상화
%%%
tag := "week-31"
number := false
%%%

*함께 읽을 절*　[§30.1–30.3](chapter-30/index.html#ch30-s1)

두 순차 PCF 함수를 구별하는 모델의 인자로 병렬 논리합을 사용한다. 프로그램 문맥이 그 인자를 공급할 수 없는 이유를 원전의 비정의 가능성 결과로 설명한다.

*담당자 자료*　[Cambridge 강의 노트 §8.1, 정리 40–41](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

# 32회 · 참조와 저장소 타입
%%%
tag := "week-32"
number := false
%%%

*함께 읽을 절*　[§31.1–31.3](chapter-31/index.html#ch31-s1)

참조 셀을 하나 할당한다. 저장소 타입을 확장한 뒤 새 셀의 값뿐 아니라 기존 셀의 타입도 유지됨을 보인다. 같은 셀을 Nat과 Bool에서 각각 쓴다고 가정해 타입 안전성이 깨지는 반례를 추적한다.

*담당자 자료*　[TAPL §§13.5, 22.7, 저장소 타입과 값 제한 (목차)](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# 33회 · 실패와 예외 처리
%%%
tag := "week-33"
number := false
%%%

*함께 읽을 절*　[§32.1–32.3](chapter-32/index.html#ch32-s1)

대입 직후 예외를 발생시킨다. 예외 발생 시점의 상태를 처리기에 넘기는 규칙과 보호 구역 진입 상태를 넘기는 규칙의 결과를 비교한다.

*담당자 자료*　[Reynolds §5.1, 실패 결과 (목차)](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

*심화*　[S4 · 실패와 Kleisli 확장](static/slides/s4/index.html#/18)

# 34회 · 연속과 CPS
%%%
tag := "week-34"
number := false
%%%

*함께 읽을 절*　[§33.1–33.3](chapter-34/index.html#ch34-s1)

덧셈의 왼쪽 결과를 받은 뒤 실행할 함수를 쓴다. 두 피연산자의 귀납가정으로 CPS 계산이 직접 평가값을 연속에 넘긴 결과와 같음을 보인다.

*담당자 자료*　[Leroy, Control Structures §6.5, CPS 변환](https://xavierleroy.org/control-structures/book/main009.html)

# 35회 · 출력 접두부와 may·must 종료
%%%
tag := "week-35"
number := false
%%%

*함께 읽을 절*　[§34.1–34.3](chapter-33/index.html#ch33-s1), [§35.1–35.3](chapter-35/index.html#ch35-s1)

7을 출력하고 종료하는 명령과, 출력 뒤 종료 또는 발산을 선택하는 명령을 비교한다. 유한 출력 접두부와 may 종료는 같지만 must 종료가 다름을 보인다. §34.3의 연속성 예제는 사전에 읽는다.

*담당자 자료*　[Reynolds §§5.2–5.3 중간 출력, §7.1 선택 규칙 (목차)](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# 36회 · 인터리빙과 원자성
%%%
tag := "week-36"
number := false
%%%

*함께 읽을 절*　[§36.1–36.3](chapter-36/index.html#ch36-s1)

두 스레드가 각각 한 번 증가시키는데 결과는 한 번만 증가하는 스케줄을 그린다. 읽기와 쓰기를 하나의 원자적 단계로 묶으면 그 경로가 사라지는 이유를 설명한다.

*담당자 자료*　[Reynolds §8.2, 임계 영역 (목차)](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# 37회 · 식의 스택 기계 컴파일
%%%
tag := "week-37"
number := false
%%%

*함께 읽을 절*　[§37.1–37.3](chapter-37/index.html#ch37-s1)

덧셈의 왼쪽 코드를 실행한 직후의 주소와 스택을 적는다. 그 스택에서 오른쪽 코드의 귀납가정을 사용해 기존 스택 꼬리가 보존됨을 보인다.

*담당자 자료*　[Leroy, Compil.lean의 compile\_aexp\_correct](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean#L347-L404)

# 38회 · 명령 컴파일의 시뮬레이션
%%%
tag := "week-38"
number := false
%%%

*함께 읽을 절*　[§38.1–38.3](chapter-38/index.html#ch38-s1)

소스에서 skip 뒤의 명령으로 넘어갈 때 기계가 0단계를 실행하는 경우를 그린다. 이때 감소하는 척도를 계산해 무한히 많은 소스 단계가 모두 사라질 수 없음을 보인다. 심화 문제 4에서는 한 단계 전이로 무한 경로의 존재를 보이는 공귀납 원리를 증명한다.

*담당자 자료*　[Leroy, Compil.lean의 simulation\_step 중 순차 명령 경우](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean#L905-L923)

# 39회 · 추상 상태와 분석의 건전성
%%%
tag := "week-39"
number := false
%%%

*함께 읽을 절*　[§39.1–39.3](chapter-39/index.html#ch39-s1)

두 분기의 상수 정보를 합쳐 공통 사실만 남긴다. 실제로 어느 분기로 실행되더라도 최종 상태가 남은 사실을 만족한다는 것을 보인다. 구체적 전이의 결과 집합이 추상 결과의 구체화에 포함됨을 식으로 쓴다.

*담당자 자료*　[Leroy, Constprop.lean의 Cexec\_sound 중 조건문 경우](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Constprop.lean#L431-L482)

# 40회 · 상수 전파의 정확성
%%%
tag := "week-40"
number := false
%%%

*함께 읽을 절*　[§40.1–40.3](chapter-40/index.html#ch40-s1)

두 분기가 모두 x에 4를 쓰는 예에서 뒤의 x 읽기를 4로 바꾼다. 앞부분의 최종 상태와 분석 결과를 이용해 전체 종료 결과가 같음을 증명한다.

*담당자 자료*　[Leroy, Constprop.lean의 cp\_com\_correct\_terminating](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Constprop.lean#L548-L607)

# 41회 · 생존 변수와 루프 고정점
%%%
tag := "week-41"
number := false
%%%

*함께 읽을 절*　[§41.1–41.3](chapter-41/index.html#ch41-s1)

출구에서 필요한 변수부터 루프 머리의 집합을 거꾸로 계산한다. 반복 횟수가 소진될 때 반환하는 상한도 안전한 이유를 포함 관계로 확인한다.

*담당자 자료*　[Leroy, Deadcode.lean의 live\_while\_charact](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Deadcode.lean#L68-L126)

# 42회 · 죽은 대입 제거의 정확성
%%%
tag := "week-42"
number := false
%%%

*함께 읽을 절*　[§42.1–42.3](chapter-42/index.html#ch42-s1)

관찰하지 않는 변수에 대한 대입을 지운다. 두 초기 상태가 필요한 입력에서 일치하면 종료 뒤 관찰할 변수의 값도 같음을 보인다.

*담당자 자료*　[Leroy, Deadcode.lean의 dce\_correct\_terminating](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Deadcode.lean#L127-L218)

# 심화 읽기
%%%
tag := "further-reading"
number := false
%%%

19회 뒤에는 TAPL §12.1에서 재귀 없는 단순 타입 람다 계산의 정규화를 증명할 수 있다. 28회에는 일반 재귀를 추가하여 어느 결론이 달라지는지 확인한다. 31회 뒤 재귀 타입을 연구할 때는 TAPL 20–21장의 타입 규칙과 Winskel 12–13장의 의미 모델을 대조한다.

39–41회의 분석을 확장하려면 Concrete Semantics §§13.3–13.5에서 수집 의미론과 일반 추상 해석기를, §13.9에서 넓히기(widening)와 좁히기(narrowing)를 읽는다. 동시성을 더 공부할 때는 Reynolds 9장의 통신 프로세스, 타입과 모듈을 더 공부할 때는 Reynolds 18장의 모듈 명세가 출발점이다.
