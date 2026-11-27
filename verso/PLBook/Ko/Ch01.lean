import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "산술식" =>
%%%
tag := "ch01"
file := "chapter-01"
%%%

[한국어판 PDF](print/pl-study-ko.pdf) · [영어 본문](../chapter-01/index.html) · [1회 일정](../seminar/index.html#week-01)

식 $`x + 4`에서 $`x`의 값이 $`3`이면 결과는 $`7`이고, $`x`의 값이 $`8`이면 결과는 $`12`이다. 두 계산에서 식의 구문 트리(syntax tree)는 같다. 각 변수 이름에 정수를 하나씩 대응시킨 것을 *상태*(state)라고 한다. 트리의 값을 구하는 한 방법은 잎에서 시작해 뿌리까지 계산하는 것이다. 다른 방법은 어떤 정수가 그 식의 값이라고 판단할 수 있는 규칙을 주는 것이다. 이 장에서는 그 규칙으로 정당화할 수 있는 값이 계산으로 얻는 값과 정확히 일치함을 증명한다.

*읽을 자료.* 이 장에서는 §§1.1–1.2와 §§1.4–1.5를 함께 읽는다. Glynn Winskel의 _The Formal Semantics of Programming Languages_ 중 [§§2.1–2.2, 11–16쪽](https://web.cecs.pdx.edu/~apt/cs558/winskel2.1-5.pdf)에서 구문, 상태, 실행 규칙을 살펴보고, [§3.2 명제 3.3, 30쪽](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)에서 값의 유일성을 직접 증명하는 방법을 읽는다. §1.3은 개별 학습 범위이며, §1.6은 11장에서 대입 명령을 다룰 때 다시 읽는다.

# 추상 구문과 상태
%%%
tag := "ch01-s1"
%%%

*정의 1.1 (산술식).* 정수 집합을 $`\mathbb{Z}`로 쓰고 변수 이름의 집합 $`V`를 고정한다. 산술식의 집합 $`E`는 다음 문법으로 만드는 유한 트리들의 집합이다. 여기서 $`n \in {\mathbb{Z}}`이고 $`x \in V`이다.

$$`e ::= \operatorname{lit}(n)\,\ \mid \ \,\operatorname{var}(x)\,\ \mid \ \,\operatorname{add}\left( {e_{1},e_{2}} \right)`

$`::=`의 오른쪽에는 가능한 구문 형태를 세로줄로 구분하여 나열한다. 각 형태에 해당하는 트리를 만드는 연산을 *생성자*(constructor)라 한다. 잎 $`\operatorname{lit}(n)`에는 정수 리터럴(식에 표기한 정수 상수)이, 잎 $`\operatorname{var}(x)`에는 변수 이름이 들어 있다. 생성자 $`\operatorname{add}`는 두 트리 $`e_{1}`과 $`e_{2}`를 차례로 자식으로 삼아 새 뿌리를 만든다. 모든 식은 맨 바깥 생성자가 하나로 정해진다. 덧셈이면 왼쪽 부분식과 오른쪽 부분식도 각각 유일하다. 예를 들어 $`x + 4`는 $`\operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(4)} \right)`의 구체적 표기이다.

*구조적 귀납법(structural induction).* $`P`를 식의 성질이라 하자. $`E`의 모든 식이 $`P`를 만족함을 보이려면 다음 세 가지로 충분하다. 모든 $`n \in {\mathbb{Z}}`에 대해 $`P\left( {\operatorname{lit}(n)} \right)`를, 모든 $`x \in V`에 대해 $`P\left( {\operatorname{var}(x)} \right)`을 증명한다. 그리고 임의의 $`e_{1},e_{2} \in E`에 대해 $`P\left( e_{1} \right)`와 $`P\left( e_{2} \right)`을 가정하여 $`P\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)} \right)`을 보인다. 이는 트리 높이에 대한 귀납법으로 정당화된다. 리터럴과 변수의 높이는 0이고, 덧셈의 높이는 두 자식의 높이 중 큰 값에 1을 더한 값이다.

*정의 1.2 (상태).* 상태란 각 변수에 정확히 하나의 정수를 대응시키는 함수이다. 이러한 함수 전체의 집합을 $`\Sigma = \left( {V\rightarrow{\mathbb{Z}}} \right)`, 상태 $`\sigma`에서 변수 $`x`가 갖는 값을 $`\sigma(x)`로 쓴다. 이 장에서는 변수 이름이 곧 상태에서 읽어야 할 좌표를 정한다.

예를 들어 상태 $`\sigma`가 $`x`에는 $`3`을, 나머지 이름에는 모두 $`0`을 대응시킨다고 하자. 기호 $`x`는 $`V`의 원소이고 트리 $`\operatorname{var}(x)`는 $`E`의 원소이다. $`\sigma(x) = 3`라고 쓸 때의 그 정숫값은 $`\mathbb{Z}`의 원소이다. 이 셋 중 선택한 상태에 따라 달라지는 것은 마지막 값뿐이다.

*TAPL과 비교.* Pierce는 §§3.2–3.3에서 불리언 항과 자연수 항을 귀납적으로 정의한다. 조건식에 대한 증명에서는 세 직접 부분항마다 귀납가정을 하나씩 얻는다. 여기서는 두 인자를 취하는 덧셈을 쓰므로 덧셈의 귀납 단계에는 가정이 둘이다. 새 문법의 귀납 원리를 쓰려면 각 생성자의 인자 중 어떤 것이 다시 같은 문법의 항인지 살펴보면 된다.

트리에서 꺼낼 수 있는 정보는 생성자가 정한다. 덧셈이 뿌리인 식을 받으면 그 왼쪽과 오른쪽 자식을 볼 수 있다. 뿌리가 정수 리터럴이면 거기에 적힌 정수를 읽을 수 있다. 이 정보는 상태에 영향을 받지 않는다. 어떤 경우에 상태 조회가 필요하더라도 식의 형태에 따른 정의는 먼저 뿌리의 생성자를 확인하는 데서 시작한다.

Lean에서 두 입력인 식과 상태를 다음과 같이 표현한다. 변수 이름으로 문자열을 쓴다. 상태는 주어진 식에 나타나지 않는 이름까지 포함하여 모든 문자열에 값을 준다. 귀납적 자료형을 선언하면 생성자의 재귀적 필드마다 귀납가정을 사용할 수 있다. 리터럴의 정수와 변수의 이름도 필드이지만, 이 둘의 타입은 식 자체의 타입과 다르다.

```lean
inductive ArithmeticTree where
  | lit (n : Int)
  | var (x : String)
  | add (left right : ArithmeticTree)

abbrev IntegerStore := String → Int
```

따라서 `x + x`의 트리에는 이름이 같은 두 변수가 서로 다른 위치에 한 번씩 나타난다. 평가 함수는 재귀적으로 두 자식을 모두 방문한다. 한편 트리에 나타나는 변수 이름을 집합으로 모으면 같은 이름은 한 번만 센다.

# 평가
%%%
tag := "ch01-s2"
%%%

*정의 1.3 (평가).* 함수 $`\operatorname{eval}:E \times \Sigma\rightarrow{\mathbb{Z}}`은 식과 상태의 순서쌍을 받아 정수를 돌려준다. 각 생성자에 등식 하나를 주고 자식에 대해서만 재귀 호출하는 *구조적 재귀*(structural recursion)로 정의한다.

$$`\begin{matrix} {\operatorname{eval}\left( {\operatorname{lit}(n),\sigma} \right)} & {= n} \\ {\operatorname{eval}\left( {\operatorname{var}(x),\sigma} \right)} & {= \sigma(x)} \\ {\operatorname{eval}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right),\sigma} \right)} & {= \operatorname{eval}\left( {e_{1},\sigma} \right) + \operatorname{eval}\left( {e_{2},\sigma} \right)} \end{matrix}`

마지막 등식의 왼쪽에서 $`\operatorname{add}`는 식을 만들고 오른쪽에서 $`+`는 두 정수를 더한다. 두 재귀 호출에는 같은 상태를 전달한다. 상태 하나를 고정하면 처음 두 등식이 높이 0에서의 값을 결정한다. 마지막 등식은 더 낮은 두 트리의 값으로 덧셈의 값을 결정한다. 따라서 이 등식을 만족하고 모든 입력에서 정의되는 함수가 유일하게 존재한다.

*예 1.1.* $`\sigma(x) = 3`이면 다음과 같이 계산한다.

$$`\begin{matrix} {\operatorname{eval}\left( {\operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(4)} \right),\sigma} \right)} & {= \operatorname{eval}\left( {\operatorname{var}(x),\sigma} \right) + \operatorname{eval}\left( {\operatorname{lit}(4),\sigma} \right)} \\ & {= 3 + 4 = 7.} \end{matrix}`

*Concrete Semantics의 평가 함수.* [_Concrete Semantics_, §§3.1.1–3.1.2, 27–29쪽](https://concrete-semantics.org/)에서 Nipkow와 Klein은 세 생성자를 각각 `N`, `V`, `Plus`로 쓴다. 함수 `aval`은 먼저 트리를 받고 이어서 상태를 받는다. 예를 들어 `aval (Plus (V x) (N 4)) s`는 예 1.1의 트리를 상태 `s`에서 평가하며, 결과는 `s x + 4`이다. 상태를 바꾸면 변수 조회의 결과만 달라진다. §1.5에서는 이 방식으로 정의한 함수와 Winskel의 규칙을 비교한다. [Isabelle의 AExp 이론과 aval의 정의](https://isabelle.in.tum.de/library/HOL/HOL-IMP/AExp.html)

*합성적 해석(compositional interpretation).* Reynolds는 §§1.1–1.2에서 술어논리의 생성자를 부분식의 의미에 작용하는 연산으로 해석한다. 이 산술 언어에서 변수를 포함할 수 있는 식의 의미는 상태에서 정수로 가는 함수이다. $`D(e)(\sigma) = \operatorname{eval}\left( {e,\sigma} \right)`로 쓴다. 정수 리터럴의 의미는 언제나 $`n`을 돌려주는 상수 함수이고, 변수의 의미는 그 이름에 해당하는 값을 조회하는 함수이다. 덧셈을 해석하려면 그러한 두 함수 $`f,g:\Sigma\rightarrow{\mathbb{Z}}`를 점별로 더한다. 이 합은 $`\sigma`를 $`f(\sigma) + g(\sigma)`에 대응시키는 함수이다. 따라서 다음 등식이 성립한다.

$$`D\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)} \right)(\sigma) = D\left( e_{1} \right)(\sigma) + D\left( e_{2} \right)(\sigma).`

이는 바로 평가 함수의 세 번째 정의식이다. 부분식의 의미인 두 함수 $`D\left( e_{1} \right)`와 $`D\left( e_{2} \right)`만 알면 덧셈 전체를 해석할 수 있다는 점에서 합성적이다.

예를 들어 $`\operatorname{var}(x)`와 $`\operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(0)} \right)`는 구문 트리가 다르지만 의미가 같다. 임의의 상태 $`\sigma`에서 두 번째 식을 평가하면 정의식에 의해 $`\sigma(x) + 0 = \sigma(x)`이다. 두 의미가 같으려면 모든 상태에서 값이 같아야 한다. 한 상태에서만 계산 결과를 비교하면 다른 상태에서 어떻게 될지 알 수 없다.

식 하나를 고정하고 상태를 바꿔 보자. 리터럴이 정하는 함수는 상수 함수이고, 변수가 정하는 함수는 해당 좌표를 읽는 사영이다. 덧셈이 정하는 함수는 두 함수의 점별 합이다. 예를 들어 어느 상태에서 `x`와 `y`의 값이 각각 3과 5라면 `x + y`와 `y + x`의 값은 모두 8이다. 두 함수가 같음을 보이려면 3과 5 대신 임의의 상태가 주는 정수를 택하고 정수 덧셈의 교환법칙을 적용한다. 구문 트리 두 개는 여전히 왼쪽 자식의 이름으로 구별할 수 있다.

```lean
def arithmeticValue (s : IntegerStore) : ArithmeticTree → Int
  | .lit n => n
  | .var x => s x
  | .add a b => arithmeticValue s a + arithmeticValue s b

example (s : IntegerStore) (a b : ArithmeticTree) :
    arithmeticValue s (.add a b) = arithmeticValue s (.add b a) :=
  Int.add_comm _ _
```

이 증명에서는 양변에 평가의 정의식을 한 번씩 쓴다. 자식의 내부 구조가 아무리 복잡해도 각 자식의 결과는 정수이므로, 두 결과에 곧바로 덧셈의 교환법칙을 적용할 수 있다. 자식에 대한 귀납법은 필요하지 않다.

# 자유 변수와 일치 보조정리
%%%
tag := "ch01-s3"
%%%

*정의 1.4 (자유 변수).* 함수 $`\operatorname{FV}:E\rightarrow\mathcal{P}(V)`는 각 식에 변수 이름의 집합을 대응시킨다. $`\mathcal{P}(V)`는 $`V`의 모든 부분집합의 집합, $`\varnothing`는 공집합, $`\cup`는 합집합을 뜻한다. 다음과 같이 정의한다.

$$`\begin{matrix} {\operatorname{FV}\left( {\operatorname{lit}(n)} \right)} & {= \varnothing} \\ {\operatorname{FV}\left( {\operatorname{var}(x)} \right)} & {= \left\{ x \right\}} \\ {\operatorname{FV}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)} \right)} & {= \operatorname{FV}\left( e_{1} \right) \cup \operatorname{FV}\left( e_{2} \right).} \end{matrix}`

변수의 *출현*(occurrence)이란 그 이름이 적힌 잎 하나를 가리킨다. *바인더*(binder)는 항의 일정한 부분인 *유효 범위*(scope)에 국소적인 이름을 도입한다. 한 출현이 그것을 둘러싼 어떤 바인더에도 묶이지 않을 때 그 출현은 *자유롭다*(free)고 한다. 이 문법에는 바인더가 없으므로 모든 변수 출현이 자유롭다. 같은 이름이 두 번 나타나도 자유 변수 집합에는 원소 하나만 들어간다. $`S \subseteq V`일 때 $`\sigma \rvert_{S}:S\rightarrow{\mathbb{Z}}`는 함수 $`\sigma`의 정의역을 $`S`로 제한한 것이다. 따라서 $`\sigma \rvert_{S} = \tau\rvert_{S}`일 필요충분조건은 모든 $`x \in S`에서 $`\sigma(x) = \tau(x)`이라는 것이다.

*보조정리 1.1 (일치, coincidence).* 임의의 $`e \in E`와 $`\sigma,\tau \in \Sigma`에 대하여 다음이 성립한다.

$$`\sigma \rvert_{\operatorname{FV}{(e)}} = \tau \rvert_{\operatorname{FV}{(e)}}\quad\Longrightarrow\quad\operatorname{eval}\left( {e,\sigma} \right) = \operatorname{eval}\left( {e,\tau} \right).`

*증명.* $`e`에 대한 구조적 귀납법을 쓴다. 각 식에서 증명할 명제는 모든 상태 쌍에 대한 것이다. $`\operatorname{FV}(e)`에서 일치하는 임의의 상태 $`\sigma`와 $`\tau`를 고정하자.

$`e = \operatorname{lit}(n)`이면 두 평가 결과는 모두 $`n`이다. $`e = \operatorname{var}(x)`이면 $`\operatorname{FV}(e) = \left\{ x \right\}`이므로 $`\sigma(x) = \tau(x)`에서 원하는 등식을 얻는다.

$`e = \operatorname{add}\left( {e_{1},e_{2}} \right)`이면 두 상태가 $`\operatorname{FV}\left( e_{1} \right) \cup \operatorname{FV}\left( e_{2} \right)`에서 일치하므로 두 집합 각각에서도 일치한다. 귀납가정에 의해 $`i = 1,2`에 대해 $`\operatorname{eval}\left( {e_{i},\sigma} \right) = \operatorname{eval}\left( {e_{i},\tau} \right)`이다. 따라서 다음을 얻는다.

$$`\begin{matrix} {\operatorname{eval}\left( {e,\sigma} \right)} & {= \operatorname{eval}\left( {e_{1},\sigma} \right) + \operatorname{eval}\left( {e_{2},\sigma} \right)} \\ & {= \operatorname{eval}\left( {e_{1},\tau} \right) + \operatorname{eval}\left( {e_{2},\tau} \right)} \\ & {= \operatorname{eval}\left( {e,\tau} \right).} \end{matrix}`

*따름정리 1.2 (상태 갱신).* $`\sigma \in \Sigma`, $`x \in V`, $`n \in {\mathbb{Z}}`에 대하여 $`\sigma\left\lbrack {x\mapsto n} \right\rbrack`를 다음과 같이 정의한다. $`x`에서는 값이 $`n`이고 나머지 변수에서는 $`\sigma`와 일치한다. 그러면 $`x \notin \operatorname{FV}(e)`인 모든 $`e \in E`에 대하여 다음이 성립한다.

$$`\operatorname{eval}\left( {e,\sigma\left\lbrack {x\mapsto n} \right\rbrack} \right) = \operatorname{eval}\left( {e,\sigma} \right).`

*증명.* 이 갱신은 $`\operatorname{FV}(e)`에 속하는 모든 변수의 값을 보존한다. 보조정리 1.1을 적용한다. $`\square`

자유 변수 집합이 공집합인 식을 *닫힌 식*(closed expression)이라고 한다. 임의의 두 상태는 공집합에서 일치하므로 보조정리 1.1에 의해 닫힌 식은 모든 상태에서 같은 값을 갖는다.

*Lean 정리의 해석.* Leroy 강좌의 Lean 4 판에서 `free_in_aexp x a`는 이름 $`x`가 식 $`a`에 자유롭게 나타난다는 명제이다. `aeval_free`의 가정은 그와 같은 모든 $`x`에 대해 두 상태의 값이 같다는 것이다. $`a = \operatorname{add}\left( {\operatorname{var}(x),\operatorname{var}(x)} \right)`로 택하면 평가식에는 $`x`의 조회가 두 번 나오지만 두 상태가 만족해야 할 조건은 하나다. 이 강좌의 식에는 뺄셈도 있어, 증명에 뺄셈의 경우가 하나 더 있다. [Leroy 강좌 Imp.lean의 자유 변수와 일치 보조정리](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L52-L60)

일치 보조정리는 역이 성립하지 않는다. `x + y`에서 두 변숫값을 차례로 `(1,4)`와 `(2,3)`으로 주는 두 상태를 생각하자. 두 상태에서 식의 값은 모두 5이지만 어느 좌표의 값도 같지 않다. 주어진 두 상태에서 평가값이 같다는 사실로부터 각 자유 변수의 값이 같다는 결론을 낼 수는 없다. 보조정리가 보장하는 것은 충분한 입력 좌표들에서 값이 같으면 결과도 같다는 것이다.

같은 정리를 다음처럼 이용할 수 있다. 식에 나타나는 유한 개의 이름에만 값을 배정하고 그 밖의 이름에 대한 정보는 버린다. 이 변수 할당을 모든 이름으로 확장하는 두 가지 방법을 택해도 평가값은 같다. 두 확장을 일치 보조정리의 상태로 취하면 모든 자유 변수에서 같은 할당을 확장했으므로 가정이 성립한다. 따라서 완전한 상태를 입력으로 받는 평가 함수를 사용하여 제한된 할당만으로도 평가값을 정의할 수 있다. 예를 들어 빠진 이름에는 모두 0을 주어 확장해도 된다. 다른 기본값을 택해도 결과는 같다. 실행 규칙이 상태 전체를 쓰더라도 뒤에서 배울 데이터 흐름 분석이 변수 이름의 집합만으로 추론할 수 있는 근거가 여기에 있다.

# 평가 판단
%%%
tag := "ch01-s4"
%%%

정의 1.3은 값을 계산한다. 같은 평가를 상태, 식, 정수의 세 성분 사이의 관계로 규정할 수도 있다. 상태 $`\sigma`에서 식 $`e`가 값 $`n`으로 평가된다는 *판단*(judgment)을 $`\sigma \vdash e \Downarrow n`로 쓴다. 여기서 $`\Downarrow`는 평가 전체를 한 번에 나타낸다. 이런 관계로 주어진 의미론을 *큰걸음 의미론*(big-step semantics)이라고 한다.

*판단을 읽는 법.* 기호 $`\vdash`(턴스타일)의 왼쪽에는 판단에 주어진 상태를, 오른쪽에는 평가할 식이나 실행할 명령을 쓴다. $`\sigma \vdash e \Downarrow n`에서 결과는 정수이고, $`\sigma \vdash c \Downarrow \sigma'`에서 결과는 최종 상태이다. 두 판단 모두 계산이 종료됨을 뜻한다. 작은걸음 $`\langle c,\sigma\rangle \rightarrow \langle c',\sigma'\rangle`는 한 구성에서 다음 구성으로 가는 전이 한 번을 나타낸다. 구성은 명령과 현재 상태의 순서쌍이다. $`\rightarrow^{*}`의 별표는 전이를 유한 번 이을 수 있다는 뜻이며, 전이가 0번인 경우도 포함한다. 식의 평가 판단과 함수 $`\operatorname{eval}(e,\sigma)`의 값이 일치한다는 것은 정리 1.3에서 증명한다.

*정의 1.5 (평가 관계).* 평가 관계는 $`\Sigma \times E \times {\mathbb{Z}}`의 부분집합 중 다음 추론 규칙(inference rule)에 대해 닫힌 가장 작은 집합이다. 집합이 한 규칙에 대해 *닫혀 있다*는 것은 선 위의 전제들을 모두 포함할 때마다 선 아래의 결론도 포함한다는 뜻이다. 전제가 없는 규칙을 공리(axiom)라 한다. $`a,b,n`은 정수를 나타낸다.

$$`\frac{}{\sigma \vdash \operatorname{lit}(n) \Downarrow n}\quad\frac{}{\sigma \vdash \operatorname{var}(x) \Downarrow \sigma(x)}`

$$`\frac{\sigma \vdash e_{1} \Downarrow a\quad \sigma \vdash e_{2} \Downarrow b}{\sigma \vdash \operatorname{add}\left( {e_{1},e_{2}} \right) \Downarrow a + b}`

‘가장 작다’는 포함 관계를 기준으로 한다. 상태·식·정수로 이루어진 순서삼중항이 이 관계에 속할 필요충분조건은 그 판단의 유한한 *유도*(derivation)가 존재하는 것이다. 유도는 각 노드에 한 규칙의 결론이 있고 그 자식들이 전제를 제공하는 트리이다. 실제로 유한한 유도를 갖는 판단들은 새 뿌리를 붙일 수 있으므로 규칙에 대해 닫혀 있다. 한편 규칙에 대해 닫힌 모든 관계는 그러한 판단을 전부 포함한다. 이는 잎에서 뿌리로 올라가는 귀납법으로 보일 수 있다.

*예 1.2.* $`\sigma(x) = 3`인 상태 $`\sigma`를 택한다. 다음 트리의 두 잎은 덧셈 규칙의 두 전제를 정당화한다.

$$`\dfrac{\dfrac{\vphantom{\sigma}}{\sigma \vdash \operatorname{var}(x) \Downarrow 3}\qquad\dfrac{\vphantom{\sigma}}{\sigma \vdash \operatorname{lit}(4) \Downarrow 4}}{\sigma \vdash \operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(4)} \right) \Downarrow 7}`

거꾸로 같은 덧셈이 $`n`으로 평가되었다고 하자. 결론의 맨 바깥 생성자가 덧셈인 규칙은 덧셈 규칙뿐이다. 그 두 전제의 결과는 각각 $`3`과 $`4`여야 하므로 $`n = 7`이다. 이처럼 결론에서 가능한 마지막 규칙과 그 전제를 복원하는 추론을 *역전*(inversion)이라 한다.

규칙에 대해 닫혀 있다는 조건만으로는 불필요한 판단도 허용된다. 예를 들어 가능한 모든 순서삼중항의 집합은 위 규칙에 대해 닫혀 있다. 여기에는 $`\sigma \vdash \operatorname{lit}(4) \Downarrow 9`도 속한다. 그러나 이를 결론으로 갖는 유한한 유도는 없다. 마지막 규칙은 리터럴 공리여야 하는데, 이 공리가 해당 잎에 주는 값은 $`4`이기 때문이다. 닫힌 관계 가운데 가장 작은 것을 취해야 역전이 정당화된다.

*원전의 표기.* Winskel은 $`\langle a,\sigma\rangle \rightarrow n`(§2.2, 13쪽)과 $`\langle c,\sigma\rangle \rightarrow \sigma'`(§2.4, 19쪽)으로 각각 식과 명령의 계산 전체를 나타낸다. 이 책에서는 같은 두 판단에 아래쪽 이중 화살표를 쓴다. 덧셈 규칙에서 Winskel은 두 전제의 결과를 더해 결론의 값을 얻는다는 조건을 따로 적고, 정의 1.5는 그 합을 결론에 직접 적는다. [Winskel, §§2.2, 2.4](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf#page=34)

_PLFA_의 BigStep 장에서는 $`\gamma \vdash M \Downarrow V`로 람다 항의 평가를 나타낸다. 여기서 $`\gamma`는 변수에 클로저(항과 그 자유 변수의 값을 찾을 환경의 쌍)를 연결하는 환경이다. 이 장의 명령형 언어에서는 턴스타일 왼쪽 자리에 정수 변수의 현재 상태를 둔다. [PLFA, BigStep](https://plfa.github.io/BigStep/#big-step-evaluation)

다음 Lean 선언은 상태를 매개변수로 고정하여 귀납적 명제족을 정의한다. 식과 결과 정수는 이 명제족의 지표(index)이다. 각 생성자의 타입은 그것이 결론으로 내놓을 수 있는 판단을 정확히 정한다. 특히 덧셈 생성자의 결론에는 전제의 두 결과를 더한 값이 들어 있다. 다른 표기로 주어진 정수를 결과로 쓰려면 그 정수가 이 합과 같다는 증거가 더 필요하다.

```lean
inductive ArithmeticDerives (s : IntegerStore) : ArithmeticTree → Int → Prop where
  | lit (n : Int) : ArithmeticDerives s (.lit n) n
  | var (x : String) : ArithmeticDerives s (.var x) (s x)
  | add {a b : ArithmeticTree} {m n : Int} :
      ArithmeticDerives s a m → ArithmeticDerives s b n →
      ArithmeticDerives s (.add a b) (m + n)
```

임의의 상태에서 `x + 4`의 유도를 만들려면 변수 규칙에 `x`를, 리터럴 규칙에 4를 넣는다. 두 규칙의 결론이 결과 쪽 덧셈의 두 인자를 정한다. 유도를 역전할 때는 반대쪽에서 출발한다. 결론의 식 지표가 덧셈이면 두 잎 생성자 중 어느 것도 이 지표를 만들 수 없다. 남은 생성자를 살펴보면 구체적인 두 정수와 그 값을 산출하는 유도들이 나온다. 이 증인들은 주어진 유도에서 얻으므로 따로 이들을 찾아내는 알고리즘을 선택할 필요가 없다.

# 평가 함수와 관계의 대응 및 결정성
%%%
tag := "ch01-s5"
%%%

$`e`와 $`\sigma`를 고정하면 정의 1.3은 정수 하나를 준다. 정의 1.5로는 어떤 값이 규칙으로 정당화되는지를 기술한다. 각 후보 $`n`에 대하여 유한한 유도가 있거나 없다. 다음 정리에 따르면 유도할 수 있는 결과의 집합은 계산한 정수 하나만을 원소로 갖는다.

*정리 1.3 (대응).* 모든 $`e \in E`, $`\sigma \in \Sigma`, $`n \in {\mathbb{Z}}`에 대하여 다음이 성립한다.

$$`\sigma \vdash e \Downarrow n\quad\Longleftrightarrow\quad\operatorname{eval}\left( {e,\sigma} \right) = n.`

*증명 (유도에서 계산값으로).* 주어진 유도에 대한 귀납법을 쓴다. 그러면 바로 아래 전제들에서 성립하는 명제를 가정하여 결론에 필요한 명제를 증명할 수 있다. 리터럴과 변수의 경우 결론은 각각 정의 1.3의 등식과 일치한다. 덧셈의 두 전제의 결과가 $`a`와 $`b`이면 결론의 결과는 $`a + b`이다. 두 귀납가정으로 $`\operatorname{eval}\left( {e_{1},\sigma} \right) = a`, $`\operatorname{eval}\left( {e_{2},\sigma} \right) = b`를 얻는다. 덧셈의 정의식에 대입하면 계산값도 $`a + b`이다.

*증명 (계산값에서 유도로).* 상태 $`\sigma`를 고정한다. $`e`에 대한 구조적 귀납법으로 결과가 $`\operatorname{eval}\left( {e,\sigma} \right)`인 유도를 구성한다. 리터럴에는 리터럴 공리를, 변수에는 변수 공리를 쓴다. 덧셈의 경우 두 귀납가정이 전제의 유도를 하나씩 제공한다. 뿌리에 덧셈 규칙을 붙이면 결과는 $`\operatorname{eval}\left( {e_{1},\sigma} \right) + \operatorname{eval}\left( {e_{2},\sigma} \right)`이고, 이는 $`\operatorname{eval}\left( {e,\sigma} \right)`와 같다. $`\operatorname{eval}\left( {e,\sigma} \right) = n`이라면 이것이 바로 원하는 유도이다. $`\square`

*따름정리 1.4.* 평가에는 *전체성*(totality)과 *결정성*(determinacy)이 있다. 즉 모든 식과 상태에는 적어도 하나의 결과가 있으며, 같은 식과 상태에는 많아야 하나의 결과가 있다.

*증명.* $`\operatorname{eval}\left( {e,\sigma} \right)`에 대한 유도를 구성하면 존재성을 얻는다. 같은 입력에 대한 두 유도의 결과가 $`n`과 $`m`이면 정리 1.3에서 $`n = \operatorname{eval}\left( {e,\sigma} \right) = m`를 얻는다. $`\square`

순방향 증명은 평가했다는 증거를 이미 가지고 시작하여 마지막 규칙을 살펴본다. 역방향 증명은 구문에서 출발하여 그 증거를 구성한다. 이 언어의 덧셈 규칙은 자식 하나당 전제가 정확히 하나이다. 반면 반복문에서는 전제에 같은 명령이 새 상태로 다시 나타날 수 있다. 그 명령의 구문은 그대로여도 전제의 유도는 전체 유도보다 작다.

*결정성의 직접 증명.* Winskel은 §3.2 명제 3.3에서 식에 대한 구조적 귀납법으로 규칙에서 직접 유일성을 증명한다. 이 문법의 덧셈 경우를 보자. $`e = \operatorname{add}\left( {e_{1},e_{2}} \right)`를 고정하고 같은 상태에서 두 유도의 결과가 $`r`과 $`s`라고 하자. 마지막 규칙을 각각 역전하면 자식들의 값 $`a,b`와 $`a',b'`를 얻고 $`r = a + b`, $`s = a' + b'`이다. $`e_{1}`의 두 평가에 귀납가정을 적용하면 $`a = a'`이고, $`e_{2}`에 대한 가정에서 $`b = b'`이다. 따라서 $`r = s`이다. 공리의 경우에는 결과가 리터럴 자체의 값이나 상태에서 그 이름에 저장된 값으로 강제된다. 이 증명은 평가 함수를 정의하기 전에도 유일성을 보장한다. 존재성은 별도의 명제이며, 여기서는 정리 1.3의 역방향에서 얻었다.

순방향에서는 전체 유도가 증명의 입력이다. 덧셈 경우 Lean은 자식의 계산값과 유도 결과를 연결하는 등식을 하나씩 준다. 이 등식들로 두 계산값의 합을 고쳐 쓰면 덧셈 규칙의 결론에 있는 값이 된다. 역방향에서는 트리를 입력으로 받으므로 자식에 대한 귀납가정은 각각 판단을 뒷받침하는 유도를 제공해야 한다. 덧셈 생성자는 바로 그 두 유도를 받는다.

```lean
theorem arithmeticSound (s : IntegerStore) {e : ArithmeticTree} {n : Int}
    (d : ArithmeticDerives s e n) : arithmeticValue s e = n := by
  induction d with
  | lit n => rfl
  | var x => rfl
  | add h₁ h₂ ih₁ ih₂ => simp only [arithmeticValue, ih₁, ih₂]

theorem arithmeticComplete (s : IntegerStore) (e : ArithmeticTree) :
    ArithmeticDerives s e (arithmeticValue s e) := by
  induction e with
  | lit n => exact .lit n
  | var x => exact .var x
  | add a b ih₁ ih₂ => exact .add ih₁ ih₂

example (s : IntegerStore) (e : ArithmeticTree) (n : Int) :
    ArithmeticDerives s e n ↔ arithmeticValue s e = n := by
  constructor
  · exact arithmeticSound s
  · intro h
    rw [← h]
    exact arithmeticComplete s e
```

마지막에 등식으로 고쳐 쓰는 단계를 살펴보자. 구문에 대한 귀납법이 구성한 유도의 결과는 *계산으로 얻은 정수*이다. 정리의 명제는 *임의의 후보 정수*에 대한 것이다. 가정한 등식으로 그 후보를 유도의 결과 지표와 동일시할 수 있다. 역방향에서 계산값과 목표 판단이 연결되는 지점이다.

# 치환
%%%
tag := "ch01-s6"
%%%

*정의 1.6 (치환, substitution).* $`e,t \in E`, $`x \in V`에 대하여 $`e` 안에 나타나는 $`x`를 모두 $`t`로 바꾸어 얻은 트리를 $`e\left\lbrack {t/x} \right\rbrack`로 쓴다. 모든 출현을 동시에 바꾼다. 새로 끼워 넣은 트리 안의 변수는 그대로 둔다.

$$`\begin{matrix} {\operatorname{lit}(n)\left\lbrack {t/x} \right\rbrack} & {= \operatorname{lit}(n)} \\ {\operatorname{var}(y)\left\lbrack {t/x} \right\rbrack} & {= \left\{ \begin{matrix} {t\ } & {\text{if}\ y = x} \\ {\operatorname{var}(y)\ } & {\text{if}\ y \neq x} \end{matrix} \right.} \\ {\operatorname{add}\left( {e_{1},e_{2}} \right)\left\lbrack {t/x} \right\rbrack} & {= \operatorname{add}\left( {e_{1}\left\lbrack {t/x} \right\rbrack,e_{2}\left\lbrack {t/x} \right\rbrack} \right).} \end{matrix}`

*예 1.3.* $`x + x`에서 $`x`를 $`x + 1`로 치환한다. 결과는 $`\left( {x + 1} \right) + \left( {x + 1} \right)`이다. $`\sigma(x) = 2`라면 그 값은 $`6`이다. 원래 식 $`x + x`을 갱신된 상태 $`\sigma\left\lbrack {x\mapsto 3} \right\rbrack`에서 평가해도 값이 같다. 이때 $`x`에 새로 줄 값은 원래 상태에서 계산한다.

*정리 1.5 (치환 보조정리).* 임의의 $`e,t \in E`, $`x \in V`, $`\sigma \in \Sigma`에 대하여 다음이 성립한다.

$$`\operatorname{eval}\left( {e\left\lbrack {t/x} \right\rbrack,\sigma} \right) = \operatorname{eval}\left( {e,\sigma\left\lbrack {x\mapsto\operatorname{eval}\left( {t,\sigma} \right)} \right\rbrack} \right).`

*증명.* $`u = \operatorname{eval}\left( {t,\sigma} \right)`, $`\tau = \sigma\left\lbrack {x\mapsto u} \right\rbrack`로 놓고 $`e`에 대한 구조적 귀납법을 쓴다. 리터럴에서는 양변이 그 정수를 준다. $`y = x`일 때 $`\operatorname{var}(y)`의 경우 왼쪽은 새로 끼워 넣은 트리를 평가해 $`u`을 얻고, 오른쪽은 갱신된 값 $`\tau(x) = u`를 읽는다. $`y \neq x`이면 원래 잎이 그대로 남으며 $`\tau(y) = \sigma(y)`이다. 덧셈의 경우 치환과 평가의 정의에 의해 다음을 얻는다.

$$`\begin{matrix} {\operatorname{eval}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)\left\lbrack {t/x} \right\rbrack,\sigma} \right)} & {= \operatorname{eval}\left( {e_{1}\left\lbrack {t/x} \right\rbrack,\sigma} \right) + \operatorname{eval}\left( {e_{2}\left\lbrack {t/x} \right\rbrack,\sigma} \right)} \\ & {= \operatorname{eval}\left( {e_{1},\tau} \right) + \operatorname{eval}\left( {e_{2},\tau} \right)} \\ & {= \operatorname{eval}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right),\tau} \right).} \end{matrix}`

가운데 등식에는 두 귀납가정을 썼다. $`\square`

명령형 언어에서 $`x`에 값을 대입하면 뒤에 오는 식들이 평가될 상태가 달라진다. 치환 보조정리는 대입의 오른쪽 식을 치환해 넣음으로써 뒤에 오는 식들의 값을 *원래 상태에서* 계산하는 방법을 준다.

*바인더 아래의 치환.* Reynolds §1.4에서는 바인더가 있는 언어를 다룬다. 예를 들어 $`P`가 두 정수에 대한 술어이고 $`x \neq y`일 때 논리식 $`\forall y,P\left( {x,y} \right)`를 생각하자. $`x`에 자유 변수 $`y`를 치환하면 끼워 넣은 변수는 여전히 바깥 상태에 따라 값이 결정되어야 한다. 기호만 그대로 바꾸어 $`\forall y,P\left( {y,y} \right)`을 얻으면 양화사가 그 변수를 포획한다. 새 이름 $`z`를 택해 묶인 변수의 이름부터 바꾸고 치환하면 $`\forall z,P\left( {y,z} \right)`을 얻는다. 이 장의 산술식은 어느 생성자도 이름을 묶지 않으므로 정의 1.6에서는 세 경우만으로 충분하다.

치환을 차례로 적용하면 두 대입이 서로 어떻게 의존하는지 볼 수 있다. 서로 다른 두 이름으로 된 식 `x + y`의 값을 명령 `x := y; y := 1`가 끝난 뒤 관찰하자. 처음에 `x = 9`, `y = 4`이면 마지막 식의 값은 5이다. 이를 처음 상태의 식으로 나타내려면 *나중* 대입부터 없앤다. 관찰할 식에서 `y`를 1로 바꾸면 `x + 1`이다. 이제 앞선 대입을 없애기 위해 `x`를 `y`로 바꾸면 `y + 1`이다. 실제로 초기 상태에서 이 식의 값은 5이다.

프로그램에 적힌 순서대로 두 번 치환하면 먼저 `y + y`, 그다음 `1 + 1`를 얻는다. `y`의 예전 값을 읽어야 한다는 정보가 사라진다. 명령은 실행 순서대로 상태를 갱신하지만, 마지막 상태에 관한 관찰을 처음 상태의 관찰로 옮길 때에는 갱신을 역순으로 거슬러 올라간다. 각 단계가 치환 보조정리의 적용 한 번에 해당한다. 여러 대입 앞쪽으로 사후조건을 옮길 때에도 진릿값에 대해 같은 계산을 하게 된다.

# 연습문제
%%%
tag := "ch01-s7"
number := false
%%%

*1.1 (평가).* $`x,y,z`는 서로 다른 이름이고 $`e = \operatorname{add}\left( {\operatorname{var}(x),\operatorname{add}\left( {\operatorname{lit}(4),\operatorname{var}(z)} \right)} \right)`이라 하자. $`\sigma(x) = 2`, $`\sigma(y) = 9`, $`\sigma(z) = 5`일 때 정의식으로 $`\operatorname{eval}\left( {e,\sigma} \right)`과 $`\operatorname{FV}(e)`를 계산하라. 따름정리 1.2를 이용하여 $`\operatorname{eval}\left( {e,\sigma\left\lbrack {y\mapsto - 1} \right\rbrack} \right)`의 값을 구하라.

*1.2 (일치).* $`x \neq y`이고 $`e = \operatorname{add}\left( {\operatorname{var}(x),\operatorname{var}(y)} \right)`이라 하자.

1. $`x`의 값은 같지만 $`e`의 평가값은 다른 두 상태를 제시하라.
2. $`x`에서도 $`y`에서도 값이 다르지만 $`e`의 값은 같은 두 상태를 제시하라. 보조정리 1.1의 역을 쓰고 이 예가 그 반례인 까닭을 설명하라.

*1.3 (변수의 출현 횟수).* 자연수 집합을 $`{\mathbb{N}} = \left\{ {0,1,2,\ldots} \right\}`로 쓴다. 각 $`x \in V`에 대하여 $`m_{x}:E\rightarrow{\mathbb{N}}`를 구조적 재귀로 정의하되, $`m_{x}(e)`가 $`e`에 나타난 $`x`의 출현 횟수가 되게 하라. 다음 등식이 모든 $`e \in E`, $`\sigma \in \Sigma`, $`k \in {\mathbb{Z}}`에 대해 성립함을 구조적 귀납법으로 증명하라.

$$`\operatorname{eval}\left( {e,\sigma\left\lbrack {x\mapsto\sigma(x) + k} \right\rbrack} \right) = \operatorname{eval}\left( {e,\sigma} \right) + k \cdot m_{x}(e).`

두 상태가 $`S`에서 일치하면 $`e`의 평가값이 같을 때, $`S \subseteq V`를 $`e`에 *충분한 집합*이라고 하자. 보조정리 1.1과 방금 얻은 등식의 $`k = 1`인 경우를 이용해 $`\operatorname{FV}(e)`가 포함 관계에서 가장 작은 충분한 집합임을 보여라.

*1.4 (유도).* 정수의 부호를 반대로 바꾸는 식 $`\operatorname{neg}(e)`를 문법에 추가하라. 정의 1.3에 등식 하나를, 정의 1.5에 규칙 하나를 추가하라. 정리 1.3의 양방향에 대해 새로 생긴 경우를 증명하고 각 증명에서 귀납가정이 주는 것을 정확히 쓰라.

*1.5 (치환).* 서로 다른 이름 $`x`와 $`y`에 대해 $`e = x + y`, $`t = y + 1`라 하자. $`\sigma(x) = 4`, $`\sigma(y) = 2`인 상태에서 $`e\left\lbrack {t/x} \right\rbrack`와 $`e\left\lbrack {x/y} \right\rbrack`의 값을 비교하라. 각 치환에 대해 원래 트리를 그대로 평가하여 같은 결과를 얻으려면 상태를 한 번 어떻게 갱신해야 하는지 쓰라.

*심화 문제.* 산술 언어에 정수의 뺄셈을 추가하라. 어떤 변수 하나의 값만 다른 두 상태에서 한 식의 평가값이 달라질 수 있으면 그 변수는 이 식에 *본질적*이라고 하자. 자유 변수 집합에 속한다는 것이 본질적인 변수의 필요충분조건인가? 확장된 언어에서 본질적인 변수를 정확히 판정하는 절차를 제시하고 양방향을 정당화하라.

# 세미나 활동지
%%%
tag := "ch01-s8"
number := false
%%%

*준비.* 지정된 절을 읽은 뒤 약 30분 동안 칠판 한 면을 쓸 분량으로 준비한다. §1.4의 덧셈 규칙, §1.2의 덧셈 정의식, 정리 1.3을 적는다. 책의 증명을 가리고 아래의 두 구성을 연습한다. 참가자는 정리와 두 정의를 펼쳐 두면 된다.

*0–10분 · 예제.* $`\sigma(x) = 3`이라 하자. 한 사람은 $`x + 4`를 계산하고 다른 사람은 두 공리와 이들을 전제로 쓰는 규칙을 그려 결과를 정당화한다. 숫자 $`7`은 유도의 어디에서 나타나는가? 예 1.2의 유도 트리와 비교한다.

*10–40분 · 대응.* 칠판을 두 열로 나누고 양쪽에 모두 $`s = \operatorname{add}\left( {e_{1},e_{2}} \right)`을 쓴다. 각 열의 위에는 주어진 정보, 아래에는 목표를 쓰고 참가자가 중간 단계를 채울 자리를 남긴다.

1. *$`\sigma \vdash s \Downarrow n`의 유도가 주어진 경우.* 마지막 규칙을 복원하고 두 전제의 결과를 $`a`와 $`b`로 표시한다. 규칙 자체로 $`n`에 관해 무엇을 알 수 있는가? 두 전제에 귀납가정을 적용하면 각각 무슨 등식을 얻는가? 세 등식을 결합하여 $`\operatorname{eval}\left( {s,\sigma} \right)`를 계산한다.
2. *구문 트리 $`s`가 주어진 경우.* 목표는 $`\sigma \vdash s \Downarrow \operatorname{eval}\left( {s,\sigma} \right)`의 유도를 만드는 것이다. 구조적 귀납법으로 얻는 두 자식의 판단을 결과값까지 써라. 덧셈 규칙으로 두 유도를 묶고 뿌리의 결과가 목표와 일치하는지 확인한다.

*40–60분 · 두 방향의 검토.* 정의 1.5에 다음 두 수정을 각각 독립적으로 적용한다. 매번 평가 함수와 다른 규칙은 그대로 두고 달라진 규칙들이 생성하는 가장 작은 관계를 취한다.

1. 변수 공리를 삭제한다. 유도할 수 있는 값이 평가 함수의 결과와 다를 수 있는가? 모든 식에 여전히 유도가 존재하는가? $`\operatorname{var}(x)`로 확인하라.
2. 변수 공리를 복원하고, 어느 상태에서나 $`\operatorname{lit}(0)`을 $`1`로 평가할 수 있다는 공리를 추가한다. 계산한 모든 결과를 여전히 유도할 수 있는가? 모든 유도가 계산한 값을 주는가? $`\operatorname{lit}(0)`으로 확인하라.

*진행자 참고.* 모든 입력의 유도가 존재한다고 가정하는 참가자가 있다면 왼쪽 열의 출발점을 짚어 준다. 거기서는 유도 하나가 이미 주어져 있다. 오른쪽 열에서는 “목표 트리의 뿌리에 실제로 어떤 규칙을 놓을 수 있는가?”라고 묻는다. 그러면 참가자가 귀납 단계의 나머지 부분을 직접 구성할 수 있다.

# 풀이
%%%
tag := "ch01-s9"
number := false
%%%

*세미나 활동지.* 변수 공리를 없애면 원래 유도 중 일부만 남는다. 따라서 남은 모든 유도는 원래 규칙에 대한 정리 1.3의 순방향에 의해 평가 함수의 값을 준다. 그러나 $`\operatorname{eval}\left( {\operatorname{var}(x),\sigma} \right) = \sigma(x)`임에도 $`\operatorname{var}(x)`에 관한 판단을 결론으로 만드는 규칙이 남아 있지 않다. 따라서 역방향은 성립하지 않는다.

공리를 추가하면 원래 유도가 모두 보존되므로 역방향은 여전히 성립한다. 추가한 공리로 $`\sigma \vdash \operatorname{lit}(0) \Downarrow 1`을 유도할 수 있지만 $`\operatorname{eval}\left( {\operatorname{lit}(0),\sigma} \right) = 0`이다. 따라서 순방향은 깨진다. 같은 트리와 상태에 원래의 리터럴 공리를 적용하면 다른 결과도 얻는다.

*1.1.* 평가의 정의식으로 $`\operatorname{eval}\left( {e,\sigma} \right) = 2 + \left( {4 + 5} \right) = 11`을 얻는다. 자유 변수의 정의식으로는 $`\operatorname{FV}(e) = \left\{ x \right\} \cup \left( {\varnothing \cup \left\{ z \right\}} \right) = \left\{ {x,z} \right\}`를 얻는다. $`y \notin \operatorname{FV}(e)`이므로 따름정리 1.2에 의해 $`\operatorname{eval}\left( {e,\sigma\left\lbrack {y\mapsto - 1} \right\rbrack} \right) = 11`이다.

*1.2.* 좌표를 $`\left( {x,y} \right)` 순으로 쓰고 나머지 이름의 값은 모두 0으로 둔다. 상태 $`\left( {1,2} \right)`와 $`\left( {1,3} \right)`은 $`x`에서 일치하지만 식의 값은 각각 $`3`과 $`4`이다. 반면 상태 $`\left( {1,2} \right)`과 $`\left( {2,1} \right)`은 두 자유 변수에서 모두 값이 다르지만 평가값은 둘 다 $`3`이다. 따라서 두 상태에서 결과가 같다는 사실로 자유 변수에서의 일치를 보장할 수 없다.

*1.3.* 리터럴의 출현 횟수는 0이다. 변수 잎에서는 이름이 $`x`이면 1, 아니면 0이다. 덧셈에서는 두 자식의 횟수를 더한다. 리터럴에서 평가값의 변화량은 0이다. 변수 잎에서는 이름이 $`x`일 때에만 갱신으로 인해 그 값에 $`k`를 더하게 된다. 덧셈의 두 자식에서 값의 변화량은 귀납가정에 의해 각각 $`k \cdot m_{x}\left( e_{1} \right)`, $`k \cdot m_{x}\left( e_{2} \right)`이다. 두 변화량의 합이 $`k \cdot m_{x}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)} \right)`이다.

보조정리 1.1에 따르면 $`\operatorname{FV}(e)`는 충분한 집합이다. 충분한 집합 $`S`가 어떤 $`x \in \operatorname{FV}(e)`를 포함하지 않는다고 가정하자. $`x`의 출현 횟수는 양수이다. 임의의 상태에서 $`x`의 값만 1 증가시키면 두 상태는 $`S`에서 일치하지만, 방금 증명한 등식에 의해 평가값이 달라진다. 충분성에 모순이다. 따라서 모든 충분한 집합 $`S`에 대하여 $`\operatorname{FV}(e) \subseteq S`이다.

*1.4.* 등식은 $`\operatorname{eval}\left( {\operatorname{neg}(e),\sigma} \right) = - \operatorname{eval}\left( {e,\sigma} \right)`이고, 새 규칙은 다음과 같다.

$$`\frac{\sigma \vdash e \Downarrow a}{\sigma \vdash \operatorname{neg}(e) \Downarrow - a}.`

이 규칙으로 끝나는 유도가 주어지면 전제에 대한 귀납가정으로 $`\operatorname{eval}\left( {e,\sigma} \right) = a`을 얻는다. 새 등식을 적용하면 결론이 따른다. 역방향에서는 구조적 귀납법으로 자식에 대해 $`\operatorname{eval}\left( {e,\sigma} \right)`를 결과로 갖는 유도를 얻는다. 새 규칙을 한 번 적용하여 목표 유도를 만든다.

*1.5.* 첫 치환의 결과는 $`\left( {y + 1} \right) + y`이고 그 값은 $`\left( {2 + 1} \right) + 2 = 5`이다. 원래 식 $`x + y`을 상태 $`\sigma\left\lbrack {x\mapsto 3} \right\rbrack`에서 평가해도 값이 같다. 둘째 치환의 결과는 $`x + x`이고 값은 $`4 + 4 = 8`이다. 이에 대응하는 갱신 상태는 $`\sigma\left\lbrack {y\mapsto 4} \right\rbrack`이다. 두 경우 모두 갱신할 좌표에 쓸 값은 원래 상태에서 계산한다.

*심화 문제.* `x − x`에는 변수 `x`가 두 번 나타나지만 식의 값은 모든 상태에서 0이다. 어느 이름이 값에 영향을 주는지 판정하려면 각 이름에 정수 계수를 대응시킨다. 리터럴에서 계수는 0이다. 변수 잎에서는 이름이 일치하면 1이고 아니면 0이다. 덧셈 노드에서는 두 자식의 계수를 더하고, 뺄셈 노드에서는 왼쪽 계수에서 오른쪽 계수를 뺀다.

이름 하나를 고정하고 그 밖의 이름에서는 일치하는 두 상태를 택하자. 그 이름에서 두 번째 상태의 값에서 첫 번째 상태의 값을 뺀 차이를 `d`라 하자. 구조적 귀납법으로 더 강한 명제를 얻는다. 두 번째 평가값에서 첫 번째 평가값을 뺀 차이는 계수와 `d`의 곱이다. 같은 이름의 잎에서는 차이가 정확히 `d`이고, 뺄셈 노드에서는 두 귀납가정으로 `a*d − b*d = (a−b)*d`를 얻는다. 리터럴, 다른 이름의 잎, 덧셈의 경우는 평가의 정의식에서 곧바로 따른다. 계수가 0이면 차이도 항상 0이다. 계수가 0이 아니면 임의의 상태에서 그 좌표 하나만 1 증가시킨다. 두 평가값의 차이는 0이 아닌 그 계수와 같다. 이 계산을 통해 확장된 언어에서도 자유 변수에서의 일치 보조정리가 여전히 성립하는 이유를 알 수 있다.

# 참고문헌과 읽기 안내
%%%
tag := "ch01-s10"
number := false
%%%

*공동 증명을 위한 필독 자료.*

Glynn Winskel, [_The Formal Semantics of Programming Languages: An Introduction_](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf) (MIT Press, 1993). 2장의 [§§2.1–2.2, 11–16쪽](https://web.cecs.pdx.edu/~apt/cs558/winskel2.1-5.pdf)에서 식의 형성 규칙, 상태의 정의, 수·위치·덧셈의 평가 규칙을 읽는다. 원전에는 뺄셈과 곱셈 규칙도 있다. 여기서는 생성자를 세 개로 한정하고 변수 이름을 상태의 정의역으로 택했다. 3장의 [§3.2 명제 3.3, 30쪽](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)에서는 덧셈에 대한 두 유도를 따라간다. 명제 3.3은 결정성을 증명하며, 같은 쪽의 연습문제 3.4는 존재성을 묻는다. 이 장의 정리 1.3은 규칙과 함수의 대응으로 두 사실을 모두 증명한다.

*주제별 보충 자료.*

Tobias Nipkow와 Gerwin Klein, [_Concrete Semantics with Isabelle/HOL_](https://concrete-semantics.org/), 3장 §§3.1.1–3.1.2, 27–29쪽. §1.2의 계산과 비교하려면 산술식의 자료형부터 `aval`의 정의식까지 읽는다. 저자들은 변수 이름으로 문자열을 쓴다. 여기서 $`V`는 임의의 집합이다. [Isabelle 이론과 평가 예제](https://isabelle.in.tum.de/library/HOL/HOL-IMP/AExp.html)

John C. Reynolds, [_Theories of Programming Languages_](https://www.cs.cmu.edu/~jcr/tpl-toc.html) (Cambridge University Press, 1998), 1장 §§1.1–1.2, 1–11쪽, §1.4, 15쪽부터. 이 장의 §§1.2, 1.6에 대응하는 선택 읽기이다. 생성자의 해석을 어떻게 지정하는지 살펴보고, 바인더가 있는 식에서는 치환 뒤 어느 변수 출현이 자유로운 채로 남는지 확인한다.

Benjamin C. Pierce, [_Types and Programming Languages_](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf) (MIT Press, 2002), 3장 §§3.2–3.3, 26–31쪽. 이 장의 §1.1에 대응하는 선택 읽기이다. Pierce의 문법에서 귀납법의 각 경우를 이끌어 내고, 정의 1.1에서도 이를 반복해 보자.

Xavier Leroy의 _Compiler Verification_ 강좌, Wojciech Różowski의 Lean 4 이식판. [Imp.lean, §1.1](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L14-L60). 이 장의 §1.3에 대응하는 선택 읽기이다. `aeval_free`의 가정과 보조정리 1.1에서 $`\operatorname{FV}(e)` 위의 일치 조건을 비교하라. `aeval_free`는 뺄셈을 포함하는 정수식에 대해서도 일치 보조정리를 증명한다.
