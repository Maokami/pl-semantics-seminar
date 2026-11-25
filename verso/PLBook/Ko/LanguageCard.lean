import VersoManual

open Verso.Genre Manual

#doc (Manual) "IMP 언어 카드" =>
%%%
tag := "imp-card"
file := "imp-card"
number := false
%%%

3회의 선수 범위는 A.1–A.5이다. A.6은 같은 언어를 한 걸음씩 실행하는 5–6회의 표기를 정한다. 문자 $`x,y`는 변수 이름, $`e`는 산술식, $`b`는 조건식, $`c,d`는 명령, $`\sigma,\mu,\tau`는 상태다. [3회 결정성](chapter-03/index.html) · [용어집](glossary/index.html)

# A.1 산술식의 구문 · 1회
%%%
tag := "imp-a1"
number := false
%%%

변수 이름(variable name)은 문자열이다. 산술식(arithmetic expression)은 다음 네 생성자(constructor)로 만든 유한한 나무다. $`n`은 음수를 포함한 임의의 정수다. 각 세로줄은 다른 생성자를 구분한다.

$$`e ::= n \mid x \mid (e_1+e_2) \mid (e_1-e_2)`

# A.2 상태와 갱신 · 1회
%%%
tag := "imp-a2"
number := false
%%%

상태(state)는 모든 변수 이름에 정수를 하나씩 주는 함수 $`\sigma:\mathrm{Name}\to\mathbb Z`다. $`\Sigma`는 이런 함수들의 집합이다. 상태 갱신(state update) $`\sigma[x\mapsto n]`은 $`x`에서 $`n`을 주고 다른 모든 이름 $`y`에서는 $`\sigma(y)`를 주는 함수다. 두 상태의 등식은 모든 이름에서 값이 같음을 뜻한다.

# A.3 평가 함수와 평가 판단 · 1회
%%%
tag := "imp-a3"
number := false
%%%

평가 함수(evaluation function) $`\mathrm{eval}(e,\sigma)`는 정수를 돌려준다. 구문을 만든 방식에 따라 더 작은 부분식에 같은 정의를 적용하는 방법을 구조적 재귀(structural recursion)라 한다.

$$`\begin{aligned}
\mathrm{eval}(n,\sigma)&=n & \mathrm{eval}(x,\sigma)&=\sigma(x)\\
\mathrm{eval}(e_1+e_2,\sigma)&=\mathrm{eval}(e_1,\sigma)+\mathrm{eval}(e_2,\sigma)\\
\mathrm{eval}(e_1-e_2,\sigma)&=\mathrm{eval}(e_1,\sigma)-\mathrm{eval}(e_2,\sigma)
\end{aligned}`

*평가 판단(evaluation judgment) \[자체\].* $`\sigma\vdash e\Downarrow n`은 아래 규칙들로 유한하게 유도할 수 있다는 뜻이다. 추론 규칙(inference rule)은 가로줄 위의 전제들이 성립하면 아래의 결론을 쓸 수 있다는 약속이다. 전제가 없는 규칙은 바로 쓸 수 있다. 규칙들을 이렇게 이어 만든 나무를 유도(derivation)라고 한다.

$$`\frac{}{\sigma\vdash n\Downarrow n}\qquad
\frac{}{\sigma\vdash x\Downarrow\sigma(x)}`

$$`\frac{\sigma\vdash e_1\Downarrow m\quad\sigma\vdash e_2\Downarrow n}
{\sigma\vdash e_1+e_2\Downarrow m+n}\qquad
\frac{\sigma\vdash e_1\Downarrow m\quad\sigma\vdash e_2\Downarrow n}
{\sigma\vdash e_1-e_2\Downarrow m-n}`

결론에서 가능한 마지막 규칙을 찾아 전제를 복원하는 추론을 역전(inversion)이라 한다. 식 자체에 관한 명제를 증명할 때 각 생성자마다 직접 부분식에 대해 성립한다고 가정하고 전체 식에 대해 보이는 방법은 구조적 귀납법(structural induction)이다.

함수와 판단은 같은 값을 기술한다. 이 대응은 1회의 정리다. 3회의 대입 규칙은 위의 평가 함수를 직접 사용한다.

# A.4 조건식과 명령 · 2회
%%%
tag := "imp-a4"
number := false
%%%

조건식(Boolean expression)의 문법과 명령(command)의 문법은 다음과 같다.

$$`b ::= \mathsf{true}\mid\mathsf{false}\mid e_1=e_2\mid e_1\le e_2\mid\neg b\mid b_1\land b_2`

조건식의 값 $`B(b,\sigma)`는 두 불 값 중 하나다. 참과 거짓은 각각 자기 자신으로 평가한다. 두 비교는 피연산자의 정수 값을 비교하고, 부정은 값을 뒤집으며, 논리곱은 두 값이 모두 참일 때 참을 준다. $`a<b`는 $`\neg(b\le a)`, $`p\lor q`는 $`\neg(\neg p\land\neg q)`의 약자다. $`a\ne b`는 $`\neg(a=b)`를 뜻한다.

$$`c ::= \mathsf{skip}\mid x:=e\mid (c_1;c_2)\mid
\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\mid
\mathsf{while}\ b\ \mathsf{do}\ c`

# A.5 명령의 큰걸음 실행 · 2회
%%%
tag := "imp-a5"
number := false
%%%

큰걸음 의미론(big-step semantics)의 실행 판단(execution judgment) $`\sigma\vdash c\Downarrow\tau`는 아래 여섯 규칙으로 얻는 유한한 유도가 있다는 뜻이다. 순차 합성(sequencing)의 두 전제는 중간 상태 $`\mu`를 공유한다.

$$`\frac{}{\sigma\vdash\mathsf{skip}\Downarrow\sigma}\qquad
\frac{}{\sigma\vdash x:=e\Downarrow\sigma[x\mapsto\mathrm{eval}(e,\sigma)]}`

$$`\frac{\sigma\vdash c_1\Downarrow\mu\quad\mu\vdash c_2\Downarrow\tau}
{\sigma\vdash(c_1;c_2)\Downarrow\tau}`

조건문의 가드(guard)는 분기를 정하는 조건식이다. $`\mathrm{sel}(b,\sigma,c,d)`는 $`B(b,\sigma)`가 참이면 $`c`, 거짓이면 $`d`를 가리키는 수학적 약자다. 조건문 규칙의 전제는 선택된 명령의 실행 하나다.

$$`\frac{\sigma\vdash\mathrm{sel}(b,\sigma,c,d)\Downarrow\tau}
{\sigma\vdash\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d\Downarrow\tau}`

$`W=\mathsf{while}\ b\ \mathsf{do}\ c`라 쓰면 반복문에는 두 규칙이 있다. 오른쪽 규칙은 몸체가 끝난 상태에서 가드를 다시 검사한다.

$$`\frac{B(b,\sigma)=\mathsf{false}}{\sigma\vdash W\Downarrow\sigma}\qquad
\frac{B(b,\sigma)=\mathsf{true}\quad \sigma\vdash c\Downarrow\mu\quad\mu\vdash W\Downarrow\tau}
{\sigma\vdash W\Downarrow\tau}`

# A.6 전이와 경로 · 5–6회
%%%
tag := "imp-a6"
number := false
%%%

구성(configuration) $`\langle c,\sigma\rangle`은 남은 명령과 현재 상태의 쌍이다. 작은걸음 의미론(small-step semantics)의 화살표 $`p\to q`는 한 번의 전이다. 대입은 값을 써 넣고 빈 명령이 된다. 순차 합성에서 왼쪽이 빈 명령이면 오른쪽으로 옮긴다. 왼쪽이 한 걸음 가면 순차 합성 안에서 그 걸음을 밟으며 상태도 함께 바뀐다. 조건문은 선택된 분기로 간다. 반복문은 가드가 거짓이면 빈 명령으로, 참이면 몸체와 같은 반복문의 순차 합성으로 간다. 대입과 순차 합성 내부의 전이를 제외한 이 규칙들은 상태를 그대로 둔다. 빈 명령 자체에는 전이가 없다.

$`p\to^*q`는 영 번 이상의 유한 경로다. $`p\to^*p`는 항상 성립하고, $`p\to r`와 $`r\to^*q`로부터 $`p\to^*q`를 얻는다. $`p\to^n q`는 정확히 $`n`걸음인 경로를 따로 세는 교재 표기다. 무한 경로는 $`f(0)=p`이고 모든 자연수 $`i`에 대해 $`f(i)\to f(i+1)`인 함수 $`f`로 보일 수 있다. 원전의 공귀납 정의는 “다음 한 걸음이 있고 그 뒤로도 계속할 수 있다”를 만족하는 가장 큰 술어다.

# 원전과 기호 대조
%%%
tag := "imp-sources"
number := false
%%%

Leroy 강좌 Lean 포트의 고정 리비전 `a2730e7`에서 정의를 대조했다. A.1–A.5의 원전은 식 평가 함수와 명령 실행 관계를 제공한다. A.3의 식 평가 판단은 같은 문법에 대해 교재가 정한 관계다. [IMP 원전](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean) · [경로 원전](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean)

* A.1–A.2. 이름·상태는 `ident`·`store`, 갱신은 `update x n s`다.
* A.3–A.4. $`\mathrm{eval}(e,\sigma)`와 $`B(b,\sigma)`는 `aeval s e`와 `beval s b`다.
* A.5. $`\sigma\vdash c\Downarrow\tau`는 `cexec s c t`다. 조건문 생성자는 `cexec_ifthenelse` 하나다.
* A.6. 한 걸음은 `red`, 유한 경로는 `star`, 무한 경로의 두 표현은 `infseq_with_function`과 `infseq`다.
* 3회 정리 3.2의 검사 선언은 `PLBook.IMP.deterministic`이다. 조건문 따름정리는 같은 이름공간의 `ifTrue`와 `ifFalse`다. 세 선언에서 사용하는 공리는 명제 외연성(`propext`) 하나다.
