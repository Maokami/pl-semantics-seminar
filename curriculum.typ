#import "style.typ": *
#show: document-layout.with("PL 스터디 · 강의계획서")

#let leroy-source(file, lines, body) = link(
  "https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/" + file + ".lean#" + lines,
  body,
)

#cover(
  [프로그래밍 언어 이론],
  [42회 강의계획서],
  [작은 언어의 실행과 수학적 의미를 정의하고, 둘의 대응을 증명한다. 이어 타입 안전성과 컴파일러의 의미 보존을 다룬다.],
)

== IMP의 세 가지 의미론

IMP는 대입·순차 합성·조건문·반복문을 갖춘 작은 명령형 언어다. 명령을 $c$, 변수에 값을 배정한 상태들의 집합을 $Sigma$로 쓴다. 

#perspective([운영적 의미론 (operational semantics)], [$sigma ⊢ e ⇓ n$은 상태 $sigma$에서 식 $e$의 값이 정수 $n$이라는 판단이다. $sigma ⊢ c ⇓ sigma'$은 같은 상태에서 명령 $c$가 종료해 상태 $sigma'$을 남긴다는 판단이다. 한 단계 전이는 구성(configuration) 사이에 $arrow$로 표시한다.])
#perspective([표시적 의미론 (denotational semantics)], [명령을 함수 $Sigma arrow Sigma_bot$ 또는 상태 사이의 관계로 합성적으로 해석한다. $Sigma_bot$의 $bot$은 비종료를 나타낸다. 반복의 의미는 최소 고정점으로 정한다.])
#perspective([공리적 의미론 (axiomatic semantics)], [Hoare triple의 유도 규칙을 정의한다. 부분 정확성의 건전성을 실행 판단에 대해 증명하고, 종료를 요구하는 전체 정확성을 따로 정의한다.])

== 모임 준비

강의계획서에서 ‘함께 읽을 절’을 찾아 예제의 계산을 종이에 써 본다. 담당자는 지정된 원전의 규칙이나 정리를 한 번 확인하고 칠판에 쓸 식이나 유도 트리를 준비한다. 3회라면 같은 순차 명령을 실행한 두 트리를 나란히 놓고 첫 명령의 최종 상태가 같아지는 줄에 귀납가정을 표시한다.

60분 동안 예제와 기호를 확인하고(10분), 문제를 함께 풀고(30분), 다른 참가자가 핵심 단계를 다시 설명한다(20분). 7회와 13회에는 혼자 완성한 증명과 독서·발표 준비에 각각 걸린 시간을 확인한다.

== 학습 순서

21회에는 21장과 22장을 함께 읽고, 28–29회에는 29장의 논리 관계와 계산적 적절성을 두 모임에 걸쳐 공부한다.

#let groups = json("verso/sessions.json")
#for g in groups {
  let rows = g.sessions
  par([#(rows.first().week)–#(rows.last().week)회　#g.title])
}

#for g in groups {
  pagebreak()
  let rows = g.sessions
  section-top(str(rows.first().week) + "–" + str(rows.last().week) + "회", g.title)
  for r in rows {
    let section-label = r.read.map(s => "§" + s).join(", ")
    let details = [
      #small([함께 읽을 절　#section-label]) \
      #r.task \
      #small([담당자 자료　#context if r.url.starts-with("https:") {
        link(r.url, r.source)
      } else if target() == "html" {
        link("verso/site/html-multi/" + r.url, r.source)
      } else { r.source }])
      #if "extra" in r {
        linebreak()
        small([심화　#context if target() == "html" {
          link("verso/site/html-multi/" + r.extra.at(1), r.extra.at(0))
        } else { r.extra.at(0) }])
      }
    ]
    context if target() == "html" {
      html.elem("h3", [#(r.week)회 · #r.title])
      par(details)
    } else {
      block(width: 100%, breakable: false, above: 7pt, below: 7pt)[
        #line(length: 100%, stroke: 0.45pt + rule)
        #grid(columns: (32pt, 1fr), gutter: 6pt,
          text(fill: accent, weight: "bold", [#(r.week)회]),
          [*#r.title* \ #details])
      ]
    }
  }
}

#pagebreak()
#section-top("자료 안내", [교재와 Lean 실습])

== 단원별 원전

#source("R", [John C. Reynolds, Theories of Programming Languages], "https://assets.cambridge.org/97805211/06979/toc/9780521106979_toc.pdf", [언어 기능의 추가가 표시적 의미, 명세와 관찰을 어떻게 바꾸는지 공부한다.])
#source("W", [Glynn Winskel, The Formal Semantics of Programming Languages], "https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf", [운영·표시·공리적 모델과 귀납 증명에 공통 뼈대를 제공한다.])
#source("T", [Benjamin C. Pierce, Types and Programming Languages], "https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf", [산술식의 안전성부터 타입 검사·추론·다형성·모듈까지 학습 순서를 제공한다.])
#source("H", [The Hitchhiker’s Guide to Logical Verification, 2026], "https://raw.githubusercontent.com/lean-forward/logical_verification_2026/460f6be0846eefc3d9441e4e48d75753fcfe1709/hitchhikers_guide_2026_desktop.pdf", [9-11장의 세 의미론을 Lean으로 읽고, 공식 실습 저장소의 파일을 사용한다.])
#source("CS", [Nipkow and Klein, Concrete Semantics], "https://concrete-semantics.org/", [IMP, 명령 동치, 컴파일러, 프로그램 분석과 추상 해석을 비교하는 Isabelle/HOL 교재다.])

== 연결해서 읽을 자료

#source("범주", [Roy Crole, Categories for Types], "https://www.cambridge.org/core/books/categories-for-types/258841251C62FED1DACD20884E59E61C", [곱, 함수 타입과 범주적 해석에 사용한다.])
#source("PCF", [Cambridge Denotational Semantics], "https://www.cl.cam.ac.uk/teaching/2526/DenotSem/materials.html", [함수 영역, PCF, adequacy, full abstraction의 강의 노트와 연습문제.])
#source("효과", [Xavier Leroy, Control Structures for Programming Languages], "https://xavierleroy.org/control-structures/book/index.html", [2026년 7월 13일 공개 원고의 6장 CPS와 10장 effect handlers를 읽는다.])
#source("실습", [Hitchhiker’s Guide Lean 저장소], "https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709", [460f6be의 2026판 데모와 연습. Lean 4.24.0 실습 환경.])
#source("실습", [Theories of Programming Languages in Lean], "https://maokami.github.io/tpl-in-lean/", [한국어 해설과 연습. Reynolds의 구문·고정점·Hoare logic을 읽을 때 쓴다.])

#small[R과 T 링크는 출판사 또는 저자의 목차다. Winskel 링크는 책 본문이며, Crole 링크는 출판사 서지다. 정수 IMP의 공통 실습 환경은 Leroy 포트로 두고, H와 기존 Reynolds 실습 환경은 해당 과제를 진행할 때 사용한다.]

#pagebreak()
#section-top("자료 안내", [Leroy 강좌를 사용하는 범위])

#source("원전", [EUTypes 2019, Proving the Correctness of a Compiler], "https://xavierleroy.org/courses/EUTypes-2019/", [IMP, 컴파일, 상수 전파, 생존 변수 분석과 dead-code elimination, 고정점의 Coq 원강좌.])
#source("Lean", [LeroyCompilerVerificationCourse], "https://github.com/leanprover/LeroyCompilerVerificationCourse/tree/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01", [검토한 리비전은 a2730e7. Lean 4.23.0-rc2와 batteries를 쓰며, 코드에 완성된 증명이 들어 있다.])
#source("이론", [Collège de France, Mechanized Semantics], "https://xavierleroy.org/CdF/2019-2020/", [5강의 일반적인 추상 해석과 Coq 구현을 읽는다. Lean 실습의 구체적 분석은 EUTypes 포트의 상수 전파를 쓴다.])

== 마지막 단원에서 읽을 계약

#perspective([표현식 컴파일], [#leroy-source("Compil", "L351-L353", mono("compile_aexp_correct"))는 해당 PC에 컴파일된 코드가 놓인 조건에서, 평가 결과가 기존 스택 위에 추가되고 저장소가 같은 target 실행을 보인다.])
#perspective([명령 컴파일], [#leroy-source("Compil", "L988-L991", mono("compile_program_correct_terminating_2"))와 #leroy-source("Compil", "L1044-L1047", mono("compile_program_correct_diverging"))는 continuation 기반 source의 종료와 발산에서 각각 대응하는 target 동작을 도출한다.])
#perspective([Dead-code elimination], [#leroy-source("Deadcode", "L208-L211", mono("dce_correct_terminating"))은 원래 실행이 종료하고 입력이 필요한 변수에 대해 일치하면, 최적화 결과도 종료하며 출구의 관찰 변수에서 원래 결과와 일치함을 보인다.])
#perspective([Constant propagation], [#leroy-source("Constprop", "L602-L604", mono("cp_com_correct_terminating"))에는 초기 구체 상태가 추상 상태와 맞는다는 전제가 있다. 원래 명령의 종료 실행을 최적화 명령의 같은 결과로 옮긴다.])
#perspective([고정점 계산], [이 변환 정리는 #leroy-source("Constprop", "L381-L412", [연료가 소진되면 Top을 반환하는 계산])을 쓴다. #leroy-source("Fixpoints", "L313-L347", mono("fixpoint_join"))은 별도로 제시되는 종료 보장 구성이다. 생존 변수 분석은 #leroy-source("Deadcode", "L70-L85", [변수 집합에 대한 자체 계산])을 쓴다.])

#small[이 리비전의 분석 정의에는 #mono("noncomputable")인 부분이 있어, 분석 예는 손으로 계산하고 Lean에서는 정의와 증명을 읽는다. #leroy-source("Deadcode", "L25", [Deadcode의 집합 합집합 보조 성질])은 #mono("union_characterisation") 공리로 선언되어 있다. 계약과 전제는 소스 선언 기준이며, 실습 환경은 각 저장소의 toolchain을 따른다.]

== 확장 회차 후보

배열과 이진 탐색(R 4장), call-by-need(R §14.6), 재귀 타입과 unfolding(T 20-21장), 재귀 영역 방정식(R §5.5, W 12-13장), effect handlers(Leroy 10장), 메시지 전달과 교착(R 9장). 각각 본 과정의 관련 단원 뒤에 붙일 수 있다.

#pagebreak()
#section-top("용어 해설 · IMP", [실행, 의미, 명세])

*구문과 상태.* 추상 구문은 식과 명령을 생성자로 이루어진 트리로 나타낸다. IMP는 변수 대입, 순차 실행, 조건문, 반복문을 갖춘 작은 명령형 언어다. 정수 IMP의 상태는 각 변수 이름에 정수를 대응시키는 함수다. #mono("skip")은 상태를 그대로 두고 끝난다. 구조적 재귀는 자식 트리에서 계산한 값으로 부모의 값을 정의한다. 구조적 귀납은 자식에 성립한다고 가정해 부모에서도 성립함을 보이는 증명법이다.

*실행 판단과 전이.* Big-step 판단은 명령·초기 상태·최종 상태 사이의 종료 관계다. Small-step 전이는 한 구성(남은 명령과 현재 상태)에서 다음 구성으로 진행하는 한 단계다. 유도는 규칙의 전제와 결론으로 이루어진 유한한 증명 트리다. 유도 귀납은 자식 유도들의 귀납 가설을 사용한다. 역전은 결론의 형태에서 가능한 마지막 규칙과 전제를 복원한다. 결정성은 같은 입력에서 결과가 둘이면 둘이 같다는 성질이다. 여기서 명령 동치는 모든 초기 상태에서 가능한 최종 상태 집합이 같다는 뜻이다.

*표시적 의미와 순서.* Denotation은 구문에 할당한 수학적 대상이다. 합성성이란 복합 구문의 의미가 생성자와 부분 구문의 의미만으로 정해진다는 성질이다. 정보 순서에서 $a ⊑ b$는 $b$가 $a$를 더 구체화한다는 뜻이다. $Sigma_bot$은 $Sigma$에 최소 원소 $bot$을 추가한 집합이다. 상한(supremum)은 모든 원소 이상의 값들 가운데 가장 작은 값이다. 함수의 점별 순서는 모든 입력에서 출력들이 순서 관계를 만족하는지로 정한다.

*고정점.* $F(w)=w$이면 $w$는 $F$의 고정점이다. 최소 고정점은 모든 고정점 이하인 고정점이다. 최소 원소와 모든 증가 수열의 상한을 갖는 순서 집합에서, 단조이고 그 상한을 보존하는 함수는 $bot,F(bot),F(F(bot)),dots$의 상한을 최소 고정점으로 갖는다(Kleene). 모든 부분집합의 상한과 하한이 있는 완비 격자에서는 단조성만으로 최소 고정점이 존재한다(Knaster–Tarski).

*명세.* 단언은 상태에 관한 술어다. Hoare 삼중항 #{mono("{P} c {Q}")}의 부분 정확성은 $P$인 상태에서 $c$가 종료할 때마다 최종 상태가 $Q$임을 뜻한다. 전체 정확성은 종료까지 요구한다. 규칙의 건전성은 참인 전제에서 참인 결론을 얻는 성질이다. 대입의 전조건은 갱신 함수로 사후조건을 만족하는 상태 집합의 역상을 취해 얻는다. 가드는 반복 여부를 정하는 조건식이고 불변식은 매 반복 진입 시 보존할 단언이다. 변량은 가드가 참일 때 몸체 실행마다 엄격히 감소하는 자연숫값이다.

#pagebreak()
#section-top("용어 해설 · 함수와 모델", [타입, 귀납, 의미 모델])

*바인딩과 함수.* 람다 항은 변수, 함수 추상화 $λ x.t$, 함수 적용으로 구성한다. $λ x$는 몸체 $t$ 안의 해당 $x$ 출현을 묶는다. 자유 변수는 바인더에 묶이지 않은 출현의 이름이다. α-renaming은 결합 관계를 보존하는 이름 변경이다. β-축약은 적용 $(λ x.t) u$에서 자유 변수의 포획을 피하며 $u$를 $x$에 치환한다. Call-by-value는 인자를 값으로 평가한 뒤 적용하고 call-by-name은 인자를 먼저 치환한다. 환경은 이름과 그 의미를 대응시킨다. 클로저는 함수 코드와 정의 시점의 환경을 저장해 어휘적 유효 범위(lexical scope)를 구현한다.

*타입 안전성.* STLC는 함수 타입을 갖는 단순 타입 람다 계산이다. 타입 문맥은 자유 변수에 타입을 배정한다. 타입 판단은 주어진 문맥에서 항이 특정 타입을 갖는다는 주장이다. Canonical forms 보조정리는 타입별로 값이 취할 수 있는 구문 형태를 정한다. Progress는 닫힌 항이 잘 타입되면 값이거나 다음 단계가 있다는 성질이다. Preservation은 한 단계 실행 뒤에도 타입이 보존된다는 성질이다.

*타입 검사와 추론.* 검사는 항이 주어진 타입을 갖는지 판정한다. 추론은 타입을 구한다. 단일화(unification)는 타입 식 사이의 등식을 만족시키는 타입 변수 치환을 구하는 절차다. Let-다형성은 계산한 타입의 변수 일부를 일반화하고 사용처마다 새 타입으로 구체화한다. 구조적 서브타이핑은 타입 구조로 대체 가능성을 판정한다. 레코드의 너비 규칙은 필요한 필드를 모두 가진 레코드에 필드가 더 있어도 허용한다. System F는 타입에 대한 추상화와 적용을 항에 명시한다. 존재 타입은 어떤 구현 타입과 그 타입을 사용하는 값을 묶고, 외부에서는 인터페이스에 주어진 연산을 사용하게 한다.

*범주적 해석.* 범주는 대상과 대상 사이의 사상, 각 대상의 항등사상과 결합법칙·항등법칙을 만족하는 합성으로 주어진다. 구문 생성자에 대응하는 연산들을 갖춘 대수들 사이에서 준동형은 모든 생성자 연산을 보존하는 함수다. 시작 대수(initial algebra)에서는 각 대수로 유일한 준동형이 존재한다. 유한 구문 트리에서 그 준동형이 fold다. 곱으로 가는 사상은 두 사상의 쌍(pairing)으로 유일하게 정해진다. 지수 객체 $B^A$는 각 $X$에 대해 $X times A arrow B$와 $X arrow B^A$ 사이의 자연스러운 일대일 대응으로 함수 타입을 해석한다. 적용 사상(evaluation)은 함수와 인자를 결과로 보낸다.

*모델과 관찰.* PCF는 기저 타입, 함수 타입, 재귀를 갖는 계산 언어다. 여기서 적합성(adequacy)은 닫힌 자연수 항의 표시가 수 $n$이면 그 항이 $n$으로 평가된다는 방향을 포함한다. 문맥 동치는 결과를 관찰할 수 있는 모든 닫는 프로그램 문맥에 두 항을 넣었을 때 관찰이 같다는 뜻이다. 완전 추상성(full abstraction)은 문맥 동치와 모델에서의 의미 동치가 정확히 일치한다는 성질이다. 고정점 귀납에서는 최소 원소에서 성립하고 증가 근사열의 상한에서 보존되는 성질이 한 번의 펼침에도 보존됨을 증명한다.

#pagebreak()
#section-top("용어 해설 · 응용", [효과, 컴파일, 분석])

*참조와 제어.* 저장소(store)는 위치에 값을 배정한다. 저장소 타입(store typing)은 위치에 그곳에 저장할 값의 타입을 배정한다. 서로 다른 참조가 같은 위치를 가리키면 한쪽을 통한 쓰기가 다른 쪽을 통한 읽기에 영향을 준다. 실패는 정상 결과 없이 실행을 중단한다. 예외는 예외 처리기가 가로챌 수 있는 제어 이동을 일으킨다. Trace는 실행에서 관찰한 사건들의 순서열이다. Continuation은 현재 결과를 받은 뒤 남은 계산이다. CPS(continuation-passing style)는 그 계산을 함수 인자로 명시한다.

*비결정성과 동시성.* 한 구성에 가능한 후속 구성이 여러 개면 전이는 비결정적이다. May 종료는 종료하는 실행이 하나 이상 있다는 뜻이고 must 종료는 모든 최대 실행이 종료한다는 뜻이다. 최대 실행은 무한 실행 또는 더 진행할 수 없는 유한 실행이다. Guarded command에서는 조건이 참인 가지들 가운데 하나를 택한다. Interleaving은 각 스레드 내부 순서를 지키면서 여러 스레드의 단계를 섞는 실행이다. 원자적 동작은 다른 스레드가 내부 단계 사이에 끼어들 수 없는 단위다.

*컴파일과 시뮬레이션.* Source와 target은 각각 변환 전후의 언어다. 스택은 가장 나중에 넣은 값을 먼저 꺼내는 저장 구조다. PC(program counter)는 다음 명령의 위치다. 순방향 시뮬레이션은 관련된 두 상태에서 source의 한 단계에 대응하는 target 실행을 찾아 그 결과가 다시 관련됨을 보인다. 대응하는 target 단계가 0개일 수 있으면, 발산 보존 증명에는 그런 정지가 무한히 반복되지 않는다는 별도 근거가 필요하다.

*분석과 최적화.* 생존 변수 분석(liveness)은 특정 지점의 변수 값이 이후 관찰에 필요할 수 있는지 보수적으로 계산한다. 죽은 대입 제거(DCE)는 이후 관찰에 영향을 주지 않는 대입을 지운다. 루프에서 $F(L) subset.eq L$은 집합 $L$이 한 번의 역방향 전파에 대해 필요한 변수를 모두 포함한다는 조건이다. 분석의 연료는 반복 계산을 제한하는 자연수 횟수다.

*추상 해석.* 추상 상태는 가능한 구체 상태들의 집합을 표현한다. 구체화 함수 $gamma$가 추상 상태 $a$에 그 집합 $gamma(a)$를 대응시킨다. 전이의 건전성은 $gamma(a)$에서 출발한 모든 구체 후속 상태가 추상 전이 결과의 구체화에 속한다는 성질이다. 합류(join)는 두 추상 상태의 최소 상한이다. Top은 모든 구체 상태를 허용한다. 상수 전파는 한 지점에 도달하는 모든 실행에서 변수가 같은 상숫값을 가질 때 그 사실을 후속 식의 단순화에 쓴다.
