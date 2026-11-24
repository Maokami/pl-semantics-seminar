import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "전이와 무한 실행" =>
%%%
tag := "ch04"
file := "chapter-04"
%%%

[한국어판 PDF](print/pl-study-ko.pdf) · [5회 읽기 일정](../seminar/index.html#week-05) · [영어 본문](../chapter-04/index.html)

디버거로 순차 합성의 첫 대입과 둘째 대입 사이에서 실행을 멈출 수 있다. 그 순간의 상태와 아직 실행할 명령을 한 쌍으로 묶은 것이 *구성(configuration)*이다. 전이 시스템(transition system)은 각 구성에서 다음에 어느 구성으로 옮겨갈 수 있는지를 기술한다. 따라서 최종 상태가 없는 계산도 기술할 수 있다.

*읽을 문헌.* 한 단계 실행은 Nipkow와 Klein의 _Concrete Semantics_ §7.3, 전이에 대한 추론 규칙은 John C. Reynolds의 _Theories of Programming Languages_ §6.2를 참고하라. 여기서 무엇을 한 단계로 셀 것인지는 Xavier Leroy의 컴파일러 검증 강좌를 Lean으로 옮긴 자료의 축약 관계 `red`을 따른다. 이 책에서 다루는 IMP의 큰걸음 의미론(big-step semantics)과 작은걸음 의미론(small-step semantics)은 모두 산술식이나 조건식의 값이 필요할 때 그 식을 끝까지 평가한다. 모임에서는 인접한 모든 구성 쌍을 전이 규칙으로 정당화할 수 있는 무한 수열을 구성한다. [Concrete Semantics 본문](https://concrete-semantics.org/concrete-semantics.pdf) · [Reynolds 6장](https://www.cs.cmu.edu/~jcr/tpl-toc.html) · [Leroy의 IMP 축약 의미론](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean)

# 한 단계 전이 관계
%%%
tag := "ch04-s1"
%%%

명령 $`c`와 상태 $`s`에서 한 단계를 실행하여 남은 명령 $`d`와 상태 $`t`를 얻는다는 것을 $`\left\langle {c,s} \right\rangle\rightarrow\left\langle {d,t} \right\rangle`로 쓴다. 남은 명령(residual command)은 앞으로 수행할 계산을 나타낸다. 구문과 상태 연산은 2장과 같다. 앞에서처럼 $`B\left( {b,s} \right)`는 주어진 상태에서 조건식이 참이라는 뜻이다. `if b then c else d`는 $`I`로, `while b do c`는 $`W`로 줄여 쓴다.

*정의 5.1.* 다음 규칙들이 한 단계 전이 관계를 생성한다. 빈 명령(skip)에서 출발하는 규칙은 없다.

$$`\begin{matrix} \left\langle {x \mathrel{:=} e,s} \right\rangle & {\rightarrow\left\langle {\operatorname{skip},s\left\lbrack {x\mapsto\operatorname{eval}\left( {e,s} \right)} \right\rbrack} \right\rangle} \\ \left\langle {\operatorname{skip}\text{;}\ d,s} \right\rangle & {\rightarrow\left\langle {d,s} \right\rangle} \end{matrix}`

$$`\frac{\left\langle {c,s} \right\rangle\rightarrow\left\langle {c',t} \right\rangle}{\left\langle {c\ \text{;}\ d,s} \right\rangle\rightarrow\left\langle {c'\ \text{;}\ d,t} \right\rangle}`

$$`\begin{matrix} {B\left( {b,s} \right)} & {\Longrightarrow\left\langle {I,s} \right\rangle\rightarrow\left\langle {c,s} \right\rangle} \\ {\neg B\left( {b,s} \right)} & {\Longrightarrow\left\langle {I,s} \right\rangle\rightarrow\left\langle {d,s} \right\rangle} \\ {B\left( {b,s} \right)} & {\Longrightarrow\left\langle {W,s} \right\rangle\rightarrow\left\langle {c\ \text{;}\ W,s} \right\rangle} \\ {\neg B\left( {b,s} \right)} & {\Longrightarrow\left\langle {W,s} \right\rangle\rightarrow\left\langle {\operatorname{skip},s} \right\rangle} \end{matrix}`

세 번째 규칙은 왼쪽 명령의 한 단계를 순차 합성 전체의 한 단계로 올린다. 왼쪽에 할 일이 남았을 때 오른쪽 명령을 임의로 실행할 수 있는 규칙은 없다. 반복 조건이 참인 규칙은 다음 조건 검사 앞에 반복문 본문을 한 벌 놓는다. 어떤 교재에서는 먼저 조건의 참·거짓에 관계없이 반복문을 한 단계에 조건문으로 펼친다. 이 선택에 따라 실행 경로의 길이가 달라지므로 단계 수를 세는 증명에서는 한 규약을 일관되게 써야 한다.

다음에 실행할 위치는 남은 명령의 구문에서 찾는다. `(a; b); d`에서는 왼쪽 자식 `a; b`를 살펴본다. `a`가 한 단계 진행할 수 있으면 그 전이를 안쪽 순차 합성으로 한 번 올리고 다시 바깥 순차 합성으로 올린다. 이 두 번의 규칙 적용이 유도하는 것은 전체 명령의 전이 *한 단계*이다. `a`가 빈 명령이면 안쪽 순차 합성에서 이를 제거할 수 있고, 바깥 합성은 그 전이를 한 번 올린다. 두 경우 모두 맨 오른쪽 명령을 조사할 필요가 없다. 따라서 실행한 단계 수가 정확히 하나여도 그 전이를 *정당화하는* 규칙 적용은 여러 번일 수 있다.

같은 분석으로 이 문법에서 다음 구성의 유일성도 보일 수 있다. 명령에 대해 귀납하자. 대입에는 정해진 결과가 하나 있고, 조건문과 반복문에서는 조건식의 불 값이 사용할 규칙을 결정한다. 순차 합성의 왼쪽이 빈 명령이면 거기서 한 단계를 진행할 수 없으므로 전이를 올리는 규칙은 적용할 수 없다. 왼쪽이 다른 명령이면 빈 명령을 제거하는 규칙은 적용할 수 없으며, 귀납가정에 따라 올릴 전이가 존재할 때 그 결과가 유일하다. 여기에 아래의 진행 성질을 결합하면 최종 구성을 제외한 모든 구성에는 다음 구성이 정확히 하나 있다. 뒤에서는 이 사실로 ‘종료하지 않는다’와 ‘무한 경로가 있다’의 관계를 밝힌다.

# 유한 경로와 종료
%%%
tag := "ch04-s2"
%%%

두 구성 $`p,q`에 대하여 $`p`에서 시작해 $`q`에서 끝나는 $`n + 1`개의 구성으로 이루어진 열이 있고 이웃한 두 항마다 한 단계 전이가 성립할 때 $`p\rightarrow^{n}q`라 쓴다. 자연수 $`n`은 간선의 수를 센다. 그런 $`n`이 존재하면 $`p\rightarrow^{*}q`라 쓴다. 길이 0의 경로를 허용하므로 이 관계는 반사적이다. 경로를 이으면 길이는 두 길이의 합이 되며, 이로부터 추이성이 따른다. $`\left\langle {c,s} \right\rangle`에서 시작하여 결과 $`t`로 종료한다는 것은 $`\left\langle {c,s} \right\rangle\rightarrow^{*}\left\langle {\operatorname{skip},t} \right\rangle`를 뜻한다.

*예 5.2.* $`x \neq y`라 하고, `x := 2`를 $`a`로, `y := x`를 $`d`로 줄여 쓰자. $`u = s\left\lbrack {x\mapsto 2} \right\rbrack`, $`t = u\left\lbrack {y\mapsto 2} \right\rbrack`라 놓으면 전체 경로는 다음과 같다.

$$`\left\langle {a\ \text{;}\ d,s} \right\rangle\rightarrow\left\langle {\operatorname{skip}\text{;}\ d,u} \right\rangle\rightarrow\left\langle {d,u} \right\rangle\rightarrow\left\langle {\operatorname{skip},t} \right\rangle.`

가운데 전이에서는 남은 명령의 구문만 달라지고 상태는 그대로이다. $`\left\langle {d,u} \right\rangle`까지만 표시한 유한 접두 경로에서는 아직 둘째 대입을 실행하지 않았다.

*보조정리 5.3 (명령의 진행, progress).* 임의의 명령과 상태에 대하여 명령이 빈 명령이거나 해당 구성이 한 단계 진행할 수 있다. 명령에 대한 구조적 귀납법으로 증명한다. 대입은 첫 규칙으로 한 단계를 진행한다. 조건문과 반복문에서는 조건식 평가가 모든 상태에서 정의되므로 규칙 하나를 택할 수 있다. 순차 합성에서는 주어진 상태와 왼쪽 명령에 귀납가정을 적용한다. 빈 명령이면 제거하고, 그 밖에는 귀납가정에서 얻은 전이를 올린다. 이로써 모든 경우를 다루었다.

더 이상 전이할 수 없는 구성을 기약 구성(irreducible configuration)이라 한다. 남은 명령이 빈 명령이 아닌데도 기약이면 실행이 *막혔다(stuck)*고 한다. 보조정리 5.3에 따라 이 문법에서는 실행이 막히지 않는다. 정수 나눗셈처럼 값이 부분적으로만 정의되는 식을 추가하려면 0으로 나누는 경우를 어떻게 처리할지 정하고 진행 성질을 다시 증명해야 한다.

자주 쓰이는 두 종류의 폐포(closure)를 구분하자. 0단계를 허용하면 빈 명령은 다음 구성이 없어도 모든 상태에서 종료한다. 적어도 한 단계를 요구하면 길이 0인 실행은 제외된다. 한편 전이 시스템에 순환이 있으면 길이가 양수인 경로도 시작점으로 돌아올 수 있다. 따라서 양 끝점이 서로 다른지만 확인해서는 주어진 경로가 어느 폐포의 조건을 만족하는지 판별할 수 없다. 경로의 길이나 적어도 첫 간선의 유무를 알아야 한다.

경로를 잇는 예로, 첫 경로에서는 조건이 참인 조건문이 한 단계 만에 참 분기로 옮겨가고 둘째 경로에서는 그 분기가 세 단계 만에 빈 명령에 이른다고 하자. 첫 경로의 끝에서 남은 명령과 상태가 둘째 경로의 시작에서 남은 명령과 상태에 각각 일치해야 두 경로를 이을 수 있다. 경계에서 중복되는 구성 하나를 제거하면 구성 다섯 개와 간선 네 개가 남는다. 이렇게 얻은 경로를 두 번째 간선 직후에서 나누어도 된다. 새 경계는 여러 대입을 합성한 명령의 *중간*에 놓일 수도 있다. 경로를 나누는 위치는 선택할 수 있지만 큰걸음 유도의 분해는 그 유도에 마지막으로 적용한 규칙에 따른다.

# 무한 경로
%%%
tag := "ch04-s3"
%%%

$`p`에서 시작하는 무한 실행은 자연수에서 구성으로 가는 함수 $`q`로서 $`q(0) = p`이고 모든 $`i`에 대해 $`q(i)\rightarrow q\left( {i + 1} \right)`인 것이다. 발산(divergence)의 증거로 그런 함수를 하나 구성하면 충분하다. $`W =` `while true do skip`이라 하고 임의의 상태 $`s`를 고정하자. $`A = \left\langle {W,s} \right\rangle`, $`C = \left\langle {\operatorname{skip}\text{;}\ W,s} \right\rangle`라 놓는다. 조건이 참인 반복 규칙으로 $`A\rightarrow C`을 얻고 빈 명령을 제거하는 규칙으로 $`C\rightarrow A`를 얻는다. $`q\left( {2i} \right) = A`, $`q\left( {2i + 1} \right) = C`로 둔다. 모든 자연수 인덱스가 짝수이거나 홀수이므로, 위의 두 전이로 필요한 모든 간선이 확인된다.

구성이 한 번도 반복되지 않는 무한 실행도 있다. `while true do x := x + 1`에서 $`x = 0`인 초기 상태로 시작하면 반복문의 머리로 돌아올 때마다 $`x`의 값이 커진다. 발산이란 무한 수열 전체에 걸쳐 매번 다음 구성으로 전이할 수 있다는 뜻이다. 같은 구성으로 돌아오는 경로를 반복하는 것은 이 성질을 보일 수 있는 한 가지 방법이다.

결정적인 IMP에서는 두 관찰을 더 긴밀하게 연결할 수 있다. 어떤 구성에서 빈 명령에 이르는 유한 경로가 없다고 하자. 현재 명령이 빈 명령이라면 길이 0의 경로가 있으므로 현재 명령은 빈 명령일 수 없다. 진행 성질에 의해 다음 구성이 있다. 그 다음 구성에서 빈 명령에 이르는 유한 경로가 있다면 지금 택한 간선을 앞에 붙여 처음 구성에서 빈 명령에 이르는 유한 경로를 얻는다. 따라서 다음 구성에서도 빈 명령에 이르는 유한 경로가 없다. 이 논증을 반복하면 각 자연수 인덱스에서의 구성이 정해진다. 다음 구성은 유일하므로 이 무한 수열을 정하는 데 별도의 선택이 필요하지 않다.

반대로 같은 구성에서 무한 실행과 빈 명령에 이르는 유한 경로가 모두 시작한다고 하자. 유한 경로의 길이에 대해 귀납하면 끝점에 이르기까지 두 실행의 각 구성이 일치한다. 시작점이 같고 결정성에 의해 다음 구성도 같기 때문이다. 그러면 무한 실행은 그 다음 인덱스에서 빈 명령으로부터 한 단계 전이해야 하는데, 그런 규칙이 없다. 이 논증에는 결정성이 쓰였다. 비결정적 언어에서는 같은 입력에 대해 무한 실행과 종료 실행이 함께 존재할 수 있다. 35장에서 바로 이 차이를 다룬다.

무한 경로는 첫 번째 인덱스에서도 다음 구성을 가져야 한다. 아래의 짧은 정리는 정상 종료인지 실행이 막힌 것인지에 관계없이 *모든* 기약 구성 `p`에서 무한 경로가 불가능함을 보인다. Lean의 `Nat → C`는 구성의 수열을 나타내는 타입이며, `step`은 이웃한 두 항이 만족해야 할 전이 관계이다.

```lean
example {C : Type} (step : C → C → Prop) (p : C)
    (terminal : ∀ q, ¬ step p q) :
    ¬ ∃ path : Nat → C, path 0 = p ∧ ∀ n, step (path n) (path (n+1)) := by
  rintro ⟨path, start, edges⟩
  have first := edges 0
  rw [start] at first
  exact terminal _ first
```

# 연습문제
%%%
tag := "ch04-s4"
number := false
%%%

*5.1.* `if true then skip else x := 1`가 종료하기까지 몇 단계가 필요한가? 이 장의 종료 정의를 사용해 빈 명령의 경우와 비교하라.

*5.2.* $`\left\langle {\operatorname{skip},s} \right\rangle`에서 출발하는 양의 길이의 경로는 존재하지 않음을 보여라. 별표로 표시한 관계가 이 구성과 자기 자신 사이에는 성립하는지 판단하라.

*5.3.* 매번 값을 1씩 증가시키는 반복문에서 시점 $`3i`, $`3i + 1`, $`3i + 2`의 구성을 써서 무한 실행을 구성하라.

*심화 문제.* 전이 규칙이 없는 명령 `abort`를 추가하고 정상 종료로 인정하는 명령은 여전히 빈 명령뿐이라고 하자. `(x := 1); abort`에서 시작하는 극대 유한 경로를 하나 제시하라. 이 장의 어느 보조정리가 성립하지 않는가? 빈 명령에 도달할 수 없다는 이유로 실행이 무한하다고 결론지을 수 있는가?

# 세미나 과제
%%%
tag := "ch04-s5"
number := false
%%%

*정의 확인 · 10분.* §5.2의 세 단계 경로에 명령, 상태, 한 단계 전이를 나타내는 화살표를 각각 표시한다.

*공동 증명 · 30분.* §5.3의 무한 실행을 구성한다. 이 실행을 나타내는 함수의 정의역을 밝히고, 짝수와 홀수 인덱스에서 출발하는 모든 간선을 각각 정당화한다.

*증명 검토 · 20분.* 값을 1씩 증가시키는 반복문에도 같은 구성 방법을 적용해 본다. 언어를 확장했을 때 실행이 막힌 항과 무한 실행이 서로 다른 현상인 이유를 진행 성질과 관련지어 설명한다.

*진행자를 위한 힌트.* 반복 조건이 참인 규칙을 한 번 적용하면 남은 명령은 순차 합성이다. 다음 규칙을 고르기 전에 맨 왼쪽 명령을 확인한다.

# 풀이와 참고 문헌
%%%
tag := "ch04-s6"
number := false
%%%

*5.1.* 조건문은 한 단계 만에 $`\left\langle {\operatorname{skip},s} \right\rangle`에 이르며, 빈 명령은 길이 0의 경로로 이미 종료한다. 두 경우 모두 최종 상태는 $`s`이다.

*5.2.* 길이가 양수인 경로에는 첫 간선이 있어야 한다. 정의 5.1의 어느 규칙도 빈 명령에서 출발하는 전이를 결론으로 갖지 않는다. 간선이 없는 경로로 반사성은 여전히 성립한다.

*5.3.* $`s_{i}(x) = i`로 $`s_{i}`를 정의하고 다른 변수들에서는 초기 상태와 같은 값을 주자. 본문을 $`a`, 반복문을 $`W`라 쓰면 세 구성은 차례로 $`\left\langle {W,s_{i}} \right\rangle`, $`\left\langle {a\ \text{;}\ W,s_{i}} \right\rangle`, $`\left\langle {\operatorname{skip}\text{;}\ W,s_{i + 1}} \right\rangle`이다. 빈 명령을 제거하면 $`\left\langle {W,s_{i + 1}} \right\rangle`로 돌아온다. 이 세 간선이 모든 인덱스에서의 전이를 정당화한다.

원전의 정의에서는 `star`(유한한 단계에 해당하는 반사적·추이적 폐포)와 `infseq`(무한 전이열)을 비교해 보라. 본문의 반복 예에서는 주기적인 함수를 직접 정의해 무한 실행을 제시했다. [Leroy의 Sequences 모듈](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean)

*심화 문제.* 임의의 초기 상태 `s`에서 첫 간선은 대입의 전이를 순차 합성으로 올려 `⟨skip; abort, s[x ↦ 1]⟩`에 이른다. 다음 간선은 맨 앞의 빈 명령을 제거해 `⟨abort, s[x ↦ 1]⟩`에 이른다. 여기서 더 붙일 수 있는 간선이 없으므로 이 경로는 극대(maximal)이다. 끝점의 상태가 잘 정의되지만 남은 명령은 정상 종료로 지정한 명령과 다르다. 극대 유한 경로의 마지막 상태만 기록한다면 이런 실행까지 정상 종료로 잘못 판정하게 된다.

`⟨abort,s⟩`는 빈 명령도 아니고 전이할 수도 없으므로 이 구성에서 이미 진행 보조정리가 성립하지 않는다. 앞에서 살펴본 시작 구성에서의 첫 두 간선은 강제되고 세 번째 간선은 존재할 수 없으므로, 거기에서 시작하는 무한 실행은 없다. 따라서 확장한 전이 시스템에서는 빈 명령에 도달하지 못해도 유한 단계 후 실행이 막힐 수 있다. 다른 설계로는 abort를 예외 종료로 지정할 수 있다. 이때는 정상 종료와 예외 종료를 각각 정의하고 이에 맞게 진행 성질도 다시 서술해야 한다.
