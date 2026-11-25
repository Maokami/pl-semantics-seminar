import VersoManual

open Verso.Genre Manual

#doc (Manual) "Compiling Boolean Expressions and Branches" =>
%%%
tag := "ch15"
file := "chapter-15"
%%%

* *Definitions.* Expressions, stores and $`\mathrm{eval}` ([IMP language card A.1–A.3](imp-card/index.html#imp-a1)). Boolean expressions and their values $`B(b,s)` ([A.4](imp-card/index.html#imp-a4)). Structural induction ([Session 1, §1.1](chapter-01/index.html#ch01-s1)). Instructions, code, code at a position $`\mathrm{at}(C,\mathit{pc},K)` with its three facts, stacks, machine configurations, transitions, finite paths and joining, and the compilers $`\mathrm{cexp}` and $`\mathrm{cbexp}` ([Stack machine card B.1–B.7](machine-card/index.html#machine-b1)). The loop layout ([B.8](machine-card/index.html#machine-b8)). Compiled expressions on the machine ([Session 14, Corollary 14.4](chapter-14/index.html#ch14-s3)). A variable quantified inside the induction property ([Session 3, §3.2](chapter-03/index.html#ch03-s2)).
* *New terms.* Branch instruction and branch distance, conditional branch instruction, compilation with two distances, contract of compiled Boolean expressions. [Glossary and label key](glossary/index.html)
* *Theorem 15.2 (Compiled Boolean expressions meet the contract).* For every code $`C`, store $`s`, stack $`S`, Boolean expression $`b`, integers $`d_1,d_0` and position $`\mathit{pc}`, let $`K=\mathrm{cbexp}(b,d_1,d_0)`. If $`\mathrm{at}(C,\mathit{pc},K)`, then $`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|K|+\mathrm{sel}(B(b,s),d_1,d_0),S,s\rangle`. Here $`\mathrm{sel}(\beta,d_1,d_0)` is $`d_1` if $`\beta=\mathsf{true}` and $`d_0` if $`\beta=\mathsf{false}`.
* *Source.* The instructions, the transitions and the compiler $`\mathrm{cbexp}` are those of Leroy’s course, as recorded in the stack machine card. Theorem 15.2 is the correctness theorem for compiled Boolean expressions in that course. Nipkow and Klein prove the same contract for their compiler. It takes one offset and a flag instead of two distances, runs the code on its own from position $`0`, and requires the offset to be nonnegative. [Source and Lean names](machine-card/index.html#machine-sources) · [Concrete Semantics, §8.3, p. 101](https://concrete-semantics.org/concrete-semantics.pdf#page=111)
* *Board case.* Conjunction. Split the block at the end of the code for $`b_1`. Apply the hypothesis for $`b_1` with the distances $`0` and $`|K_2|+d_0`. A false $`b_1` already reaches the false exit. A true $`b_1` reaches the start of $`K_2`, where the hypothesis for $`b_2` applies. Six steps.
* *Proof outline.* Fix $`C`, $`s` and $`S`. Use structural induction on $`b` with $`P(b)\coloneqq\forall d_1,d_0,\mathit{pc},\ \mathrm{at}(C,\mathit{pc},\mathrm{cbexp}(b,d_1,d_0))\Rightarrow C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|\mathrm{cbexp}(b,d_1,d_0)|+\mathrm{sel}(B(b,s),d_1,d_0),S,s\rangle`. The distances and the position are quantified inside $`P(b)`, as the final store was in Session 3: negation uses the hypothesis with the distances exchanged, and conjunction uses it with new distances for $`b_1` and a new position for $`b_2`. Constants take at most one branch. Comparisons use Corollary 14.4 twice and no hypothesis.
* *From Session 14.* Expression code ends at its own end with one new value on the stack. Code for a Boolean expression pushes nothing and has two possible ends, chosen by $`B(b,s)`. It contains branches, so the list execution of Session 14 does not apply, and the proof works with positions throughout. Session 16 places this code at the head of every loop and conditional. In a loop, a true guard continues into the body, and a false guard continues past the body and the backward branch.

Session 16 compiles the loop $`\mathsf{while}\ x\le1\ \mathsf{do}\ x:=x+1` as in [B.8](machine-card/index.html#machine-b8). Placed at position $`0`, the test $`[\mathsf{load}(x),\mathsf{push}(1),\mathsf{ble}(0,5)]` occupies positions 0–2, the body $`[\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus},\mathsf{setvar}(x)]` occupies positions 3–6, and $`\mathsf{branch}(-8)` sits at position 7. Run it from a store with $`s(x)=1` and the empty stack. The first two instructions of the test leave $`[1,1]` on the stack. Since $`1\le1`, the instruction $`\mathsf{ble}(0,5)` pops both integers and continues at $`2+1+0=3`, the start of the body. The body sets $`x` to $`2`, and the branch at 7 continues at $`7+1-8=0`. Now the first two instructions leave $`[1,2]`. Since $`2\le1` is false, it continues at $`2+1+5=8`, just past the loop. Each time the test ended with the stack and the store it started with. The proof in Session 16 needs this from the code of every guard, however many branches that code contains. A true guard must end at the end of the test, a false guard five instructions further, and neither may change the stack or the store. This session states that requirement as a contract and proves that the compiler meets it.

# Branches and compiled Boolean expressions
%%%
tag := "ch15-s1"
%%%

The instruction $`\mathsf{branch}(d)` is a *branch instruction*. Its rule in [B.4](machine-card/index.html#machine-b4) moves the program counter from $`\mathit{pc}` to $`\mathit{pc}+1+d` and changes nothing else. The integer $`d` is its *branch distance*. The distance is relative: it counts instructions from the instruction after the branch, not from the start of the code. So $`\mathsf{branch}(0)` continues with the next instruction and $`\mathsf{branch}(2)` skips two. Relative distances let the compiler build a block before it knows where the block will be placed. Placed at position $`20` instead of $`0`, the loop above has the same instructions, and its $`\mathsf{branch}(-8)` at position $`27` continues at $`27+1-8=20`, again the start of the test.

The instructions $`\mathsf{beq}(d_1,d_0)` and $`\mathsf{ble}(d_1,d_0)` are *conditional branch instructions*. Each pops two integers, $`n_2` from the top and $`n_1` below it. Then $`\mathsf{beq}` tests $`n_1=n_2` and $`\mathsf{ble}` tests $`n_1\le n_2`. If the test holds, the instruction branches with distance $`d_1`. If it fails, it branches with distance $`d_0`. Neither pushes a result. In the second test of the opening run, $`\mathsf{ble}(0,5)` at position 2 found $`[1,2]`, so $`n_2=1` and $`n_1=2`. The test $`2\le1` failed, and the distance was $`5`.

The compiler for Boolean expressions ([B.7](machine-card/index.html#machine-b7)) takes two distances as arguments:

$$`\begin{aligned}
\mathrm{cbexp}(\mathsf{true},d_1,d_0)&=[\,]\ \text{ if } d_1=0,\quad\text{otherwise } [\mathsf{branch}(d_1)]\\
\mathrm{cbexp}(\mathsf{false},d_1,d_0)&=[\,]\ \text{ if } d_0=0,\quad\text{otherwise } [\mathsf{branch}(d_0)]\\
\mathrm{cbexp}(e_1=e_2,d_1,d_0)&=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{beq}(d_1,d_0)]\\
\mathrm{cbexp}(e_1\le e_2,d_1,d_0)&=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{ble}(d_1,d_0)]\\
\mathrm{cbexp}(\neg b,d_1,d_0)&=\mathrm{cbexp}(b,d_0,d_1)\\
\mathrm{cbexp}(b_1\land b_2,d_1,d_0)&=\mathrm{cbexp}(b_1,0,|K_2|+d_0)\mathbin{+\!\!+}K_2\quad\text{where } K_2=\mathrm{cbexp}(b_2,d_1,d_0).
\end{aligned}`

This is *compilation with two distances*. The caller chooses $`d_1` and $`d_0`. Both are measured from the end of the block, the position just after its last instruction. The code never puts a truth value on the stack. The value of $`b` decides only where the code ends. A constant needs at most one branch, and none for a distance $`0`. A comparison computes both operands with $`\mathrm{cexp}` and then executes one conditional branch instruction. Negation emits no instruction. It exchanges the distances. In a conjunction the code $`K_2` for $`b_2` is built first, because the code for $`b_1` needs its length. A true $`b_1` continues into $`K_2`. A false $`b_1` skips $`K_2` and then $`d_0` further instructions, so $`b_2` is not evaluated.

Now take the guard $`b=(x\le1)\land\neg(y=0)` with the body of the opening loop. That body has four instructions, so Session 16 compiles the test with the distances $`0` and $`4+1=5` (B.8). Compute $`\mathrm{cbexp}(b,0,5)` from the second operand outward:

$$`\begin{aligned}
K_2&=\mathrm{cbexp}(\neg(y=0),0,5)=\mathrm{cbexp}(y=0,5,0)=[\mathsf{load}(y),\mathsf{push}(0),\mathsf{beq}(5,0)],\\
K_1&=\mathrm{cbexp}(x\le1,0,|K_2|+5)=\mathrm{cbexp}(x\le1,0,8)=[\mathsf{load}(x),\mathsf{push}(1),\mathsf{ble}(0,8)].
\end{aligned}`

The block $`K=K_1\mathbin{+\!\!+}K_2` has six instructions. Place it at position $`0`. Then $`K_1` occupies positions 0–2, $`K_2` occupies positions 3–5, and the block ends at $`6`. It should continue at $`6+0=6`, the start of the body, when $`b` is true, and at $`6+5=11`, past the loop, when $`b` is false. Start each run with the empty stack.

* $`s(x)=4,\ s(y)=7`. The stacks are $`[4]` and $`[1,4]`. At position 2, $`4\le1` fails, so $`\mathsf{ble}(0,8)` continues at $`2+1+8=11`. Positions 3–5 are never reached. Here $`B(b,s)=\mathsf{false}`.
* $`s(x)=0,\ s(y)=7`. The stacks are $`[0]` and $`[1,0]`. At position 2, $`0\le1` holds, so the machine continues at $`3`. The stacks are $`[7]` and $`[0,7]`. At position 5, $`7=0` fails, so $`\mathsf{beq}(5,0)` continues at $`5+1+0=6`. Here $`B(b,s)=\mathsf{true}`.
* $`s(x)=0,\ s(y)=0`. The run is as before up to position 5. There $`0=0` holds, and $`\mathsf{beq}(5,0)` continues at $`5+1+5=11`. Here $`B(b,s)=\mathsf{false}`.

Every run ends with the empty stack and the store it started with. The position $`11` is reached from two different instructions.

# The contract
%%%
tag := "ch15-s2"
%%%

In the example each run ends at $`6+0` or at $`6+5`, and the value of the guard selects the summand. We name this selection.

*Definition 15.1 (Contract of compiled Boolean expressions).* For a Boolean $`\beta` and integers $`d_1,d_0`, write $`\mathrm{sel}(\beta,d_1,d_0)` for $`d_1` if $`\beta=\mathsf{true}` and for $`d_0` if $`\beta=\mathsf{false}`. Let $`K` be code, $`b` a Boolean expression and $`d_1,d_0` integers. The code $`K` *meets the contract* for $`b,d_1,d_0` if for every code $`C`, store $`s`, stack $`S` and position $`\mathit{pc}` with $`\mathrm{at}(C,\mathit{pc},K)`,

$$`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|K|+\mathrm{sel}(B(b,s),d_1,d_0),\,S,\,s\rangle.`

The positions $`\mathit{pc}+|K|+d_1` and $`\mathit{pc}+|K|+d_0` are the *true exit* and the *false exit* of the block.

The contract has four parts. The run ends at one of two positions. The value $`B(b,s)` decides which. The stack is $`S` again. The store is $`s` again. In the example, $`\mathrm{sel}(B(b,s),0,5)` is $`0` when $`s(x)\le1` and $`s(y)\ne0`, and $`5` otherwise.

*Theorem 15.2 (Compiled Boolean expressions meet the contract).* For every code $`C`, store $`s`, stack $`S`, Boolean expression $`b`, integers $`d_1,d_0` and position $`\mathit{pc}`, let $`K=\mathrm{cbexp}(b,d_1,d_0)`. If $`\mathrm{at}(C,\mathit{pc},K)`, then

$$`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|K|+\mathrm{sel}(B(b,s),d_1,d_0),\,S,\,s\rangle.`

In words, $`\mathrm{cbexp}(b,d_1,d_0)` meets the contract for $`b,d_1,d_0`. Session 16 applies the theorem with the distances $`0` and $`|K'|+1`, where $`K'` is the code of the loop body or of the first branch of a conditional.

The theorem says that the machine passes through the exit configuration. It does not say that every instruction of the block runs: in the first run above, positions 3–5 were skipped. Nor does it say what happens at the exit. That depends on the instruction found there, which belongs to the code around the block.

# Proof by structural induction
%%%
tag := "ch15-s3"
%%%

*Proof of Theorem 15.2.* Fix $`C`, $`s` and $`S`. We prove $`P(b)` for every Boolean expression $`b` by structural induction on $`b`, with one case for each of the six forms of A.4. The induction property is

$$`P(b)\ \coloneqq\ \forall d_1,d_0,\mathit{pc},\quad\mathrm{at}(C,\mathit{pc},\mathrm{cbexp}(b,d_1,d_0))\ \Longrightarrow\ C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|\mathrm{cbexp}(b,d_1,d_0)|+\mathrm{sel}(B(b,s),d_1,d_0),\,S,\,s\rangle.`

Only $`\neg b_1` and $`b_1\land b_2` have Boolean expressions as children, so only these two cases have induction hypotheses. The children of a comparison are arithmetic expressions, and for them Session 14 has done the work.

The distances and the position are quantified inside $`P(b)`. In [Session 3, §3.2](chapter-03/index.html#ch03-s2) the final store was quantified inside the induction property, because the hypothesis for the first premise was applied at a different store. Here the hypotheses are applied at different distances and positions. Take the conjunction $`b` of §15.1, compiled with the distances $`0` and $`5`. Its hypothesis for $`x\le1` must describe $`K_1=\mathrm{cbexp}(x\le1,0,8)`, and its hypothesis for $`\neg(y=0)` must describe a block that starts at position $`3`, not $`0`. With $`d_1,d_0,\mathit{pc}` fixed before the induction, the hypothesis for $`x\le1` would describe $`\mathrm{cbexp}(x\le1,0,5)`, a block that does not occur in $`C`. The code $`C`, the store $`s` and the stack $`S` may stay fixed, because every hypothesis is used with the same three. Code for a Boolean expression changes neither the stack nor the store.

*Constants.* Suppose $`b=\mathsf{true}`. Then $`\mathrm{sel}(B(b,s),d_1,d_0)=d_1`. If $`d_1=0`, the block is empty, and the path with zero transitions ends at $`\mathit{pc}+0+0`. Otherwise the block is $`[\mathsf{branch}(d_1)]`. By B.2, fact 1, $`C(\mathit{pc})=\mathsf{branch}(d_1)`, and the branch rule gives one transition to $`\langle\mathit{pc}+1+d_1,S,s\rangle`. A single transition is a path (B.5). The block has length $`1`, so this is the required configuration. The case $`b=\mathsf{false}` is the same with $`d_0`.

*Comparison (warm-up).* Suppose $`b=(e_1\le e_2)`, so the block is $`K=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{ble}(d_1,d_0)]`. Write $`\ell_1=|\mathrm{cexp}(e_1)|`, $`\ell_2=|\mathrm{cexp}(e_2)|`, $`n_1=\mathrm{eval}(e_1,s)` and $`n_2=\mathrm{eval}(e_2,s)`. Then $`|K|=\ell_1+\ell_2+1`. Assume $`\mathrm{at}(C,\mathit{pc},K)`. The steps use [Session 14, Corollary 14.4](chapter-14/index.html#ch14-s3) twice.

1. By B.2, fact 2 applied twice, $`\mathrm{at}(C,\mathit{pc},\mathrm{cexp}(e_1))`, $`\mathrm{at}(C,\mathit{pc}+\ell_1,\mathrm{cexp}(e_2))` and $`\mathrm{at}(C,\mathit{pc}+\ell_1+\ell_2,[\mathsf{ble}(d_1,d_0)])`. By fact 1, $`C(\mathit{pc}+\ell_1+\ell_2)=\mathsf{ble}(d_1,d_0)`.
2. Corollary 14.4 for $`e_1` at $`\mathit{pc}` with the stack $`S` gives $`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+\ell_1,n_1::S,s\rangle`.
3. Corollary 14.4 for $`e_2` at $`\mathit{pc}+\ell_1` with the stack $`n_1::S` gives $`C\vdash\langle\mathit{pc}+\ell_1,n_1::S,s\rangle\to^*\langle\mathit{pc}+\ell_1+\ell_2,n_2::n_1::S,s\rangle`.
4. The rule for $`\mathsf{ble}` (B.4) pops $`n_2` and $`n_1` and moves to $`\langle\mathit{pc}+\ell_1+\ell_2+1+\delta,S,s\rangle`, where $`\delta` is $`d_1` if $`n_1\le n_2` and $`d_0` otherwise. By A.4, $`n_1\le n_2` holds exactly when $`B(b,s)=\mathsf{true}`. So $`\delta=\mathrm{sel}(B(b,s),d_1,d_0)`, and the new position is $`\mathit{pc}+|K|+\mathrm{sel}(B(b,s),d_1,d_0)`.
5. Join the paths of steps 2–4 (B.5).

The equality case is the same with $`\mathsf{beq}` and $`n_1=n_2`. Step 3 applies Corollary 14.4 on the stack $`n_1::S`, not on the stack the block started with. This is why Session 14 proved it for every stack. No induction hypothesis was used.

*Negation.* Suppose $`b=\neg b_1`. The block is $`K=\mathrm{cbexp}(\neg b_1,d_1,d_0)=\mathrm{cbexp}(b_1,d_0,d_1)`. Assume $`\mathrm{at}(C,\mathit{pc},K)`. Apply $`P(b_1)` with the distances $`d_0,d_1`, in this order, and the position $`\mathit{pc}`. It gives a path to $`\langle\mathit{pc}+|K|+\mathrm{sel}(B(b_1,s),d_0,d_1),S,s\rangle`. If $`B(b_1,s)=\mathsf{true}`, then $`B(b,s)=\mathsf{false}` by A.4, and both $`\mathrm{sel}(B(b_1,s),d_0,d_1)` and $`\mathrm{sel}(B(b,s),d_1,d_0)` equal $`d_0`. If $`B(b_1,s)=\mathsf{false}`, both equal $`d_1`. So the path ends at the required configuration.

*Conjunction (board case).* Suppose $`b=b_1\land b_2`. Fix $`d_1,d_0,\mathit{pc}` and write

$$`K_2=\mathrm{cbexp}(b_2,d_1,d_0),\qquad K_1=\mathrm{cbexp}(b_1,0,|K_2|+d_0),\qquad K=K_1\mathbin{+\!\!+}K_2.`

By B.7, $`K=\mathrm{cbexp}(b,d_1,d_0)`, and $`|K|=|K_1|+|K_2|` by B.2. The induction hypotheses are as follows. We name the bound distances $`d_1',d_0'` and the bound position $`\mathit{pc}'` to keep them apart from those of the case.

$$`\begin{aligned}
P(b_1):\quad&\forall d_1',d_0',\mathit{pc}',\ \ \mathrm{at}(C,\mathit{pc}',\mathrm{cbexp}(b_1,d_1',d_0'))\Longrightarrow{}\\
&\qquad C\vdash\langle\mathit{pc}',S,s\rangle\to^*\langle\mathit{pc}'+|\mathrm{cbexp}(b_1,d_1',d_0')|+\mathrm{sel}(B(b_1,s),d_1',d_0'),\,S,\,s\rangle,\\
P(b_2):\quad&\forall d_1',d_0',\mathit{pc}',\ \ \mathrm{at}(C,\mathit{pc}',\mathrm{cbexp}(b_2,d_1',d_0'))\Longrightarrow{}\\
&\qquad C\vdash\langle\mathit{pc}',S,s\rangle\to^*\langle\mathit{pc}'+|\mathrm{cbexp}(b_2,d_1',d_0')|+\mathrm{sel}(B(b_2,s),d_1',d_0'),\,S,\,s\rangle.
\end{aligned}`

1. Assume $`\mathrm{at}(C,\mathit{pc},K_1\mathbin{+\!\!+}K_2)`. We must show $`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|K_1|+|K_2|+\mathrm{sel}(B(b,s),d_1,d_0),S,s\rangle`. By B.2, fact 2, $`\mathrm{at}(C,\mathit{pc},K_1)` and $`\mathrm{at}(C,\mathit{pc}+|K_1|,K_2)`.
2. Apply $`P(b_1)` with $`d_1'=0`, $`d_0'=|K_2|+d_0` and $`\mathit{pc}'=\mathit{pc}`. Its block is $`K_1`, which is at $`\mathit{pc}` by step 1. This gives $`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|K_1|+\mathrm{sel}(B(b_1,s),0,|K_2|+d_0),S,s\rangle`.
3. Suppose $`B(b_1,s)=\mathsf{false}`. The selected distance in step 2 is $`|K_2|+d_0`, so the path ends at $`\mathit{pc}+|K_1|+|K_2|+d_0`. By A.4, $`B(b,s)=\mathsf{false}`, so $`\mathrm{sel}(B(b,s),d_1,d_0)=d_0`. The path of step 2 is the required one. The block $`K_2` was skipped, and $`P(b_2)` is not needed.
4. Suppose $`B(b_1,s)=\mathsf{true}`. The selected distance in step 2 is $`0`, so the path ends at $`\langle\mathit{pc}+|K_1|,S,s\rangle`, the start of $`K_2`.
5. Apply $`P(b_2)` with $`d_1'=d_1`, $`d_0'=d_0` and $`\mathit{pc}'=\mathit{pc}+|K_1|`. Its block is $`K_2`, which is at $`\mathit{pc}+|K_1|` by step 1. This gives $`C\vdash\langle\mathit{pc}+|K_1|,S,s\rangle\to^*\langle\mathit{pc}+|K_1|+|K_2|+\mathrm{sel}(B(b_2,s),d_1,d_0),S,s\rangle`.
6. By A.4, $`B(b,s)=B(b_2,s)` when $`B(b_1,s)=\mathsf{true}`. So the path of step 5 ends at the required configuration. Join the paths of steps 2 and 5 (B.5).

Step 2 uses the hypothesis for $`b_1` at the distances $`0` and $`|K_2|+d_0`. Step 5 uses the hypothesis for $`b_2` at the position $`\mathit{pc}+|K_1|`. Neither matches the $`d_1,d_0,\mathit{pc}` of the case. Step 3 also shows why the compiler adds $`|K_2|` to the false distance of $`b_1`: the false exit of $`K_1` is $`(\mathit{pc}+|K_1|)+(|K_2|+d_0)=\mathit{pc}+|K|+d_0`, the false exit of $`K`.

This proves $`P(b)` for every Boolean expression $`b`. Theorem 15.2 is $`P(b)` at the given $`d_1,d_0,\mathit{pc}`. $`\square`

# Exercises
%%%
tag := "ch15-s4"
number := false
%%%

*15.1.* The guard $`x=0\lor y=0` abbreviates $`\neg(\neg(x=0)\land\neg(y=0))` (A.4). Compute $`\mathrm{cbexp}` of it with the distances $`0` and $`4`. Place the code at position $`0` and run it from stores with $`(s(x),s(y))` equal to $`(0,5)`, $`(3,0)` and $`(3,5)`. Which conditional branch instruction decides each run, and which exit does it reach?

*15.2.* Compute $`\mathrm{cbexp}(\mathsf{false}\land\mathsf{true},3,0)`. Which instruction never runs, whatever the store? Does this contradict Theorem 15.2?

*15.3.* Suppose the induction property fixed $`d_1` and $`d_0` before the induction and quantified only $`\mathit{pc}`. Which cases of the proof fail? For each, name the block the hypothesis describes and the block that occurs in $`C`.

*Further problem.* Add a Boolean expression $`b_1\lor b_2` with $`B(b_1\lor b_2,s)=\mathsf{true}` exactly when $`B(b_1,s)=\mathsf{true}` or $`B(b_2,s)=\mathsf{true}`. Compile it by $`\mathrm{cbexp}(b_1\lor b_2,d_1,d_0)=\mathrm{cbexp}(b_1,|K_2|+d_1,0)\mathbin{+\!\!+}K_2` with $`K_2=\mathrm{cbexp}(b_2,d_1,d_0)`. Prove the new case of Theorem 15.2 in the style of the board case. Compare the code for $`x=0\lor y=0` with the code of Exercise 15.1.

# Reading for the Seminar
%%%
tag := "ch15-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the rules for $`\mathsf{branch}` and $`\mathsf{ble}` (B.4). Draw the loop layout of the opening and mark the two exits of the test. Compute $`\mathrm{cbexp}((x\le1)\land\neg(y=0),0,5)` and run it from a store with $`s(x)=0` and $`s(y)=7`.

*Joint proof · 30 minutes.* Write $`P(b)` with its three quantifiers. Do the comparison case as a warm-up: two uses of Corollary 14.4 and one conditional branch instruction. Then write $`P(b_1)` and $`P(b_2)` and the six steps of the board case.

*Proof review · 20 minutes.* Do the constant and negation cases. Use Exercise 15.3 to find which quantifier each case needs. Run Exercise 15.2 and say what the theorem does not promise.

*Facilitator’s hint.* In step 2 of the board case, ask with which distances the code for $`b_1` was compiled. In step 5, ask at which position the code for $`b_2` starts.

# Solutions and Further Reading
%%%
tag := "ch15-s6"
number := false
%%%

*15.1.* The negation exchanges the distances, so the code is $`\mathrm{cbexp}(\neg(x=0)\land\neg(y=0),4,0)`. Then $`K_2=\mathrm{cbexp}(\neg(y=0),4,0)=\mathrm{cbexp}(y=0,0,4)=[\mathsf{load}(y),\mathsf{push}(0),\mathsf{beq}(0,4)]` and $`K_1=\mathrm{cbexp}(\neg(x=0),0,3)=\mathrm{cbexp}(x=0,3,0)=[\mathsf{load}(x),\mathsf{push}(0),\mathsf{beq}(3,0)]`. At position $`0` the block ends at $`6`. The true exit is $`6` and the false exit is $`10`. For $`(0,5)` the $`\mathsf{beq}` at position 2 finds $`0=0` and continues at $`2+1+3=6`. For $`(3,0)` it fails and continues at $`3`, and the $`\mathsf{beq}` at position 5 finds $`0=0` and continues at $`5+1+0=6`. For $`(3,5)` both tests fail, and the $`\mathsf{beq}` at position 5 continues at $`5+1+4=10`. The first two runs reach the true exit and the third the false exit.

*15.2.* Here $`K_2=\mathrm{cbexp}(\mathsf{true},3,0)=[\mathsf{branch}(3)]` and $`K_1=\mathrm{cbexp}(\mathsf{false},0,1+0)=[\mathsf{branch}(1)]`. The block is $`[\mathsf{branch}(1),\mathsf{branch}(3)]`. From $`\mathit{pc}`, the first branch continues at $`\mathit{pc}+2=\mathit{pc}+|K|+0`, the false exit, as required since $`B(\mathsf{false}\land\mathsf{true},s)=\mathsf{false}`. The $`\mathsf{branch}(3)` at $`\mathit{pc}+1` never runs. The theorem promises only the exit reached, so this unreachable instruction does not contradict it. Nipkow and Klein observe the same effect in their Example 8.7.

*15.3.* Constants and comparisons use no hypothesis, so they still go through. In the negation case the hypothesis describes $`\mathrm{cbexp}(b_1,d_1,d_0)`, but $`C` contains $`\mathrm{cbexp}(b_1,d_0,d_1)`. In the conjunction case the hypothesis for $`b_1` describes $`\mathrm{cbexp}(b_1,d_1,d_0)`, but $`C` contains $`K_1=\mathrm{cbexp}(b_1,0,|K_2|+d_0)`. The hypothesis for $`b_2` has the right distances, and its position is still quantified, so step 5 survives. If the position were fixed as well, step 5 would also fail, because $`K_2` starts at $`\mathit{pc}+|K_1|`.

*Further problem.* By B.2, fact 2, $`K_1=\mathrm{cbexp}(b_1,|K_2|+d_1,0)` is at $`\mathit{pc}` and $`K_2` at $`\mathit{pc}+|K_1|`. Apply $`P(b_1)` with the distances $`|K_2|+d_1` and $`0` at $`\mathit{pc}`. If $`B(b_1,s)=\mathsf{true}`, the path ends at $`\mathit{pc}+|K_1|+|K_2|+d_1`, the true exit, and $`B(b_1\lor b_2,s)=\mathsf{true}`. If $`B(b_1,s)=\mathsf{false}`, it ends at $`\mathit{pc}+|K_1|`. Apply $`P(b_2)` with $`d_1,d_0` at $`\mathit{pc}+|K_1|`, note $`B(b_1\lor b_2,s)=B(b_2,s)`, and join the two paths. For $`x=0\lor y=0` with the distances $`0` and $`4`, the new equation gives $`\mathrm{cbexp}(y=0,0,4)` as $`K_2` and $`\mathrm{cbexp}(x=0,3,0)` as $`K_1`. This is exactly the code of Exercise 15.1.

*Further reading · Sources.* Nipkow and Klein, _Concrete Semantics_, §8.3, compile a Boolean expression with one offset $`n` and a flag $`f`. Their code jumps $`n` instructions past its end when the value of the expression equals $`f`, and otherwise ends at its end. The distances $`0` and $`n` of this book correspond to their flag false. Their Lemma 8.8 runs the code on its own from position $`0` and requires $`0\le n`. They place code in a larger program with a separate composition lemma (Lemma 8.5). They motivate the scheme with the same loop layout (Fig. 8.1), and their Lemma 8.13 bounds the possible exits of the code. Leroy’s _Compiler Verification_ course remarks that the code could instead push $`1` or $`0` and let the conditional and the loop compare that value with $`0`. The course calls the branching code simpler and more efficient: it never computes the value as an integer, and it leaves the stack unchanged. The code also skips the second operand of a conjunction whose first operand is false (§15.1). [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf#page=110) · [Source and Lean names](machine-card/index.html#machine-sources)

# Sources and Formalization
%%%
tag := "ch15-notes"
number := false
%%%

* *Definition 15.1.* Formulated in this book.
* *Theorem 15.2.* Corresponds to CS Lemma 8.8. Externally checked: the statement matches a declaration of Leroy’s course ([machine-card references](machine-card/index.html#machine-sources)).
