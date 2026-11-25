import VersoManual
import PLBook.IMP.Determinacy

open Verso.Genre Manual

#doc (Manual) "종료 실행의 결정성" =>
%%%
tag := "ch03"
file := "chapter-03"
%%%

*3회 · 회차 카드*　읽을 절 §3.1–3.3 · 담당 ＿＿＿＿ · 준비 시간 ＿＿＿＿시간

* *쓰는 정의.* [IMP 언어 카드 A.1–A.5](imp-card/index.html). 상태와 갱신, 식의 평가 함수, 명령의 큰걸음 실행 규칙 여섯 개를 사용한다.
* *새 용어(3).* 결정성(determinacy), 유도에 대한 귀납법(induction on derivations), 귀납가정(induction hypothesis). [용어집](glossary/index.html)
* *정리 3.2 \[자체\] \[검사됨\].* 모든 명령 $`c`와 상태 $`\sigma,\tau,\tau'`에 대해, $`\sigma\vdash c\Downarrow\tau`이고 $`\sigma\vdash c\Downarrow\tau'`이면 $`\tau=\tau'`이다.
* *출처.* \[원전\] 실행 관계는 Leroy 강좌의 IMP 큰걸음 의미론을 따른다. \[대응\] Nipkow와 Klein의 _Concrete Semantics_ 보조정리 7.9는 그 책의 IMP 규칙에서 같은 유일성을 증명한다. 이 장의 정리는 언어 카드 A.5의 관계 위에서 증명했다. [원전 대조와 검사 기록](imp-card/index.html#imp-sources) · [Concrete Semantics §7.2.5, 보조정리 7.9](https://concrete-semantics.org/concrete-semantics.pdf)
* *칠판에서 끝낼 경우.* 순차 합성의 두 유도에서 최종 상태의 등식까지.
* *증명의 뼈대.* 두 유도의 중간 상태를 각각 $`\mu,\nu`라 쓰고, 첫째 명령의 귀납가정으로 $`\mu=\nu`를 얻는다. 이 등식으로 둘째 유도의 시작 상태를 바꾼 뒤 둘째 명령의 귀납가정을 쓴다.
* *앞 회차와 달라진 점.* 2회에는 한 실행의 전제를 복원했다. 이번에는 같은 입력을 가진 두 실행을 비교한다.
* *재설명 질문.* 첫째 명령에 귀납가정을 쓸 때 비교할 결과는 어느 상태인가? 반복문의 남은 실행에 귀납가정을 쓸 수 있는 이유는 무엇인가?

# 3.1 실행 규칙의 역전
%%%
tag := "ch03-s1"
number := false
%%%

서로 다른 변수 `x`와 `y`에 대해 `x := x − 1; y := x`를 실행하자. 상태(state) $`\sigma`에서 $`\sigma(x)=4`라면 첫 대입 뒤의 상태는 $`\mu=\sigma[x\mapsto3]`이다. 둘째 대입은 이 상태에서 `x`를 읽으므로 최종 상태는 $`\mu[y\mapsto3]`이다. 다른 사람이 중간 상태에 $`\nu`라는 이름을 붙여도 대입 규칙을 쓰면 $`\nu=\sigma[x\mapsto3]`을 얻는다. 첫째 명령이 여러 번 도는 반복문이어도 두 중간 상태가 같다고 말할 수 있을까?

역전(inversion)은 주어진 유도(derivation)의 결론을 만든 마지막 규칙을 찾아 그 전제를 꺼내는 추론이다. 예컨대 $`\sigma\vdash(c;d)\Downarrow\tau`라는 유한한 유도가 있으면, 뿌리는 반드시 순차 합성(sequencing) 규칙이다. 따라서 *어떤* 상태 $`\mu`에 대해 $`\sigma\vdash c\Downarrow\mu`와 $`\mu\vdash d\Downarrow\tau`인 유도가 있다. 역전만으로는 다른 유도에서 꺼낸 중간 상태가 이 $`\mu`와 같다고 말할 수 없다.

*조건문 규칙의 두 따름정리 \[검사됨\].* 조건문에는 실행 규칙 하나가 있다. 가드(guard)의 값 $`B(b,\sigma)`가 고른 분기의 유도를 전제로 삼는다. 그 값이 참이면 선택된 명령은 $`c`이므로 왼쪽 추론을 얻는다. 거짓이면 $`d`이므로 오른쪽 추론을 얻는다. 아래에서 $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`이다.

$$`\frac{B(b,\sigma)=\mathsf{true}\qquad\sigma\vdash c\Downarrow\tau}{\sigma\vdash I\Downarrow\tau}
\qquad
\frac{B(b,\sigma)=\mathsf{false}\qquad\sigma\vdash d\Downarrow\tau}{\sigma\vdash I\Downarrow\tau}`

# 3.2 결정성 정리의 증명
%%%
tag := "ch03-s2"
number := false
%%%

*정리 3.2 (종료 실행의 결정성) \[자체\] \[검사됨\].* 같은 명령을 같은 상태에서 실행한 두 유한한 유도의 최종 상태는 같다.

첫 유도 $`D`를 고정한다. 그 결론이 $`\sigma\vdash c\Downarrow\tau`일 때 증명할 명제를 다음과 같이 잡는다.

$$`P(D)\;:\quad\forall u\in\Sigma,\quad(\sigma\vdash c\Downarrow u)\ \Longrightarrow\ \tau=u.`

유도에 대한 귀납법은 마지막 규칙의 각 실행 전제에 대해 그 전제의 유도에서 명제가 성립한다고 가정할 수 있게 한다. 이때 쓰는 명제가 귀납가정이다. 비교할 상태 $`u`를 전칭 양화사 안에 둔 덕분에, 각 귀납가정을 적용할 때마다 그 유도에 맞는 결과를 고를 수 있다.

*빈 명령과 대입.* 빈 명령의 두 유도를 역전하면 어느 쪽의 결과도 $`\sigma`다. 대입에서는 같은 식이 같은 상태에서 같은 정수로 평가되므로 두 유도의 결론에 적힌 상태가 모두 $`\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`다.

*순차 합성.* $`D`에서 얻는 전제를 윗줄에, 비교할 유도를 역전하여 얻은 전제를 아랫줄에 적자.

$$`\begin{array}{c|cc}
 & c & d\\ \hline
 D & \sigma\vdash c\Downarrow\mu & \mu\vdash d\Downarrow\tau\\
 D' & \sigma\vdash c\Downarrow\nu & \nu\vdash d\Downarrow u
\end{array}`

첫째 귀납가정은 모든 $`v`에 대해 $`\sigma\vdash c\Downarrow v`이면 $`\mu=v`라고 말한다. 여기에 $`v=\nu`와 아랫줄의 왼쪽 유도를 넣으면 $`\mu=\nu`다. 따라서 아랫줄의 오른쪽 유도는 $`\mu\vdash d\Downarrow u`라는 전제를 준다. 둘째 귀납가정에 이 전제를 넣으면 $`\tau=u`다. 이 등식이 두 순차 합성의 결과를 비교하려던 결론이다.

*조건문.* 두 유도를 역전하면 모두 $`B(b,\sigma)`가 고른 분기의 유도가 나온다. 두 입력이 같으므로 분기도 같다. 첫 유도에 속한 그 분기의 귀납가정을 둘째 유도의 전제에 적용한다.

*반복문.* $`W=\mathsf{while}\ b\ \mathsf{do}\ c`라 하자. 가드가 거짓이면 두 유도 모두 즉시 끝나며 결과는 $`\sigma`다. 가드가 참이면 둘째 유도도 몸체를 실행해야 한다. 첫 유도의 몸체는 $`\mu`에서, 둘째 유도의 몸체는 $`\nu`에서 끝난다고 하자. 몸체의 귀납가정으로 $`\mu=\nu`를 얻는다. 이제 $`\mu`에서 시작하는 나머지 두 반복 실행에 둘째 귀납가정을 적용하여 최종 상태의 등식을 얻는다. 남은 반복문의 *구문*은 원래와 같지만, 그 *유도*는 첫 유도의 뿌리 아래에 있으므로 더 작다. 이로써 여섯 규칙을 모두 다루었다.

# 3.3 유일성과 종료
%%%
tag := "ch03-s3"
number := false
%%%

명령과 초기 상태를 고정하면 종료 결과는 많아야 하나다. 예를 들어 `while true do skip`에는 유한한 실행 유도가 없다. 있다면 마지막 규칙의 전제에 똑같은 반복문의 더 작은 유도가 있어야 하고, 유한한 나무 안에서 이를 끝없이 되풀이할 수는 없다. 결정성 정리가 종료까지 보장한다면 이 명령이 반례가 된다.

*연습 1.* 순차 합성의 증명에서 두 귀납가정의 비교 대상을 처음부터 최종 상태 $`u`로 고정해 보자. 위 표의 어느 칸에 첫째 귀납가정을 쓸 수 없게 되는가?

*연습 2.* 명령 `choose c d`를 추가하고 같은 상태에서 어느 분기의 결과든 허용한다. 두 분기 각각의 실행이 결정적인데도 전체 명령의 결정성이 깨지는 예를 구성하라.

*풀이.* 1. 아랫줄 왼쪽의 결과는 $`\nu`다. 첫째 귀납가정의 전제가 $`\sigma\vdash c\Downarrow u`로 고정되면 그 칸의 유도를 넣을 수 없다. 2. 두 분기를 `x := 0`과 `x := 1`로 잡으면 어느 초기 상태에서도 서로 다른 결과가 나온다. §3.1의 조건문에서는 같은 가드 값이 두 유도에 같은 분기를 지정했다. 선택 명령에는 그 전제가 없다.
