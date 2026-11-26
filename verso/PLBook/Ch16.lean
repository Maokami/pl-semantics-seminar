import VersoManual

open Verso.Genre Manual

#doc (Manual) "Compiling Commands" =>
%%%
tag := "ch16"
file := "chapter-16"
%%%

Compile $`x:=0;\ \mathsf{while}\ x\le1\ \mathsf{do}\ x:=x+1` and run the code from any state. The code of the loop starts at position 2. The machine passes position 2 three times, with $`x` equal to $`0`, $`1` and $`2`. Each pass begins a run of the loop code that ends at position 10, the end of the program, and each later run is the final part of the earlier ones. To prove that the run from the first pass is correct, we need the same claim for the run from the second pass. That claim is about the code of the whole loop, from the same position, in a different state. It is not a claim about the body. The derivation of the loop execution contains a matching premise: the last premise of the loop iteration rule is an execution of the same loop. This session proves, by induction on that derivation, that the code of every terminating command changes the state as the command does.

*In this session.*

* *Definitions.* Commands, the six execution rules and the height of an execution derivation ([IMP language card A.4–A.5](imp-card/index.html#imp-a4)). Induction on execution derivations by height ([Session 3, §3.1](chapter-03/index.html#ch03-s1)). A variable quantified inside the induction property ([Session 3, §3.2](chapter-03/index.html#ch03-s2)). Code, code at a position $`\mathrm{at}(C,\mathit{pc},K)` with its three facts, machine configurations, transitions, finite paths and joining, and the compilers $`\mathrm{cexp}`, $`\mathrm{cbexp}` and $`\mathrm{ccom}` ([Stack machine card B.1–B.8](machine-card/index.html#machine-b1)). Whole programs and their three behaviours ([B.9](machine-card/index.html#machine-b9)). Compiled expressions on the machine ([Session 14, Corollary 14.4](chapter-14/index.html#ch14-s3)). The selection $`\mathrm{sel}` and the contract of compiled Boolean expressions ([Session 15, Definition 15.1 and Theorem 15.2](chapter-15/index.html#ch15-s2)).
* *New terms.* Test, backward branch, layout of a compiled command, contract of compiled commands. [Glossary](glossary/index.html)
* *Theorem 16.2 (Compiled commands meet the contract).* For every command $`c` and states $`\sigma,\sigma'`, if $`\sigma\vdash c\Downarrow\sigma'`, then for every code $`C`, position $`\mathit{pc}` and stack $`S` with $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))`, $`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|\mathrm{ccom}(c)|,S,\sigma'\rangle`.
* *Board case.* Loop iteration with a true guard. The test reaches the start of the body. The hypothesis for the body reaches the backward branch, and the branch returns to the start of the loop code. There the hypothesis for the rest of the loop applies, at the same position and in the state left by the body. Seven steps.
* *Proof outline.* Induction on the derivation $`D:\sigma\vdash c\Downarrow\sigma'` with $`P(D)\coloneqq\forall C,\mathit{pc},S,\ \mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))\Rightarrow C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|\mathrm{ccom}(c)|,S,\sigma'\rangle`. Each case splits the block with B.2 and joins paths: Corollary 14.4 for an assignment, Theorem 15.2 for every guard, one transition for each branch instruction, and the induction hypotheses for the parts. The position is quantified inside $`P(D)` because the hypotheses are applied at the start of each part.
* *From Session 15.* Session 15 proved, by structural induction on the Boolean expression, that its code ends at the true exit or at the false exit. Here that code heads every conditional and loop, with the distances $`0` and $`|K_1|+1`, where $`K_1` is the code of the first branch of a conditional or of the body of a loop. The induction is now on derivations. The code of a loop runs again from its own start, and only the derivation of a loop execution has a premise about the same loop.

# Compiled commands and their layout
%%%
tag := "ch16-s1"
%%%

The compiler for commands ([B.8](machine-card/index.html#machine-b8)) has one clause for each of the five forms of A.4:

$$`\begin{aligned}
\mathrm{ccom}(\mathsf{skip})&=[\,]\\
\mathrm{ccom}(x:=e)&=\mathrm{cexp}(e)\mathbin{+\!\!+}[\mathsf{setvar}(x)]\\
\mathrm{ccom}(c_1;c_2)&=\mathrm{ccom}(c_1)\mathbin{+\!\!+}\mathrm{ccom}(c_2)\\
\mathrm{ccom}(\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2)&=\mathrm{cbexp}(b,0,|K_1|+1)\mathbin{+\!\!+}K_1\mathbin{+\!\!+}[\mathsf{branch}(|K_2|)]\mathbin{+\!\!+}K_2\\
\mathrm{ccom}(\mathsf{while}\ b\ \mathsf{do}\ c)&=K_b\mathbin{+\!\!+}K_c\mathbin{+\!\!+}[\mathsf{branch}(-(|K_b|+|K_c|+1))]
\end{aligned}`

In the conditional, $`K_1=\mathrm{ccom}(c_1)` and $`K_2=\mathrm{ccom}(c_2)`. In the loop, $`K_c=\mathrm{ccom}(c)` and $`K_b=\mathrm{cbexp}(b,0,|K_c|+1)`. In the examples and proof below, the loop body is named $`c_1`, so its code is $`K_1`. Skip emits nothing. An assignment computes the value of $`e` on the stack and $`\mathsf{setvar}(x)` pops it into $`x`. A sequence places the two blocks one after the other. A conditional and a loop start with the code of their guard, the *test*. A branch instruction with a negative distance is a *backward branch*. The loop ends with one.

Session 15 proved that the test meets a contract ([Definition 15.1 and Theorem 15.2](chapter-15/index.html#ch15-s2)). If $`K=\mathrm{cbexp}(b,d_1,d_0)` and $`\mathrm{at}(C,\mathit{pc},K)`, then for every stack $`S` and state $`\sigma`

$$`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|K|+\mathrm{sel}(B(b,\sigma),d_1,d_0),\,S,\,\sigma\rangle,`

where $`\mathrm{sel}(\beta,d_1,d_0)` is $`d_1` if $`\beta=\mathsf{true}` and $`d_0` if $`\beta=\mathsf{false}`. The command compiler always takes $`d_1=0` and $`d_0=|K_1|+1`. A true guard ends at the end of the test. A false guard skips the next $`|K_1|+1` instructions: the code $`K_1` and the one branch instruction after it.

The *layout* of a compiled command lists where each part of its code starts, relative to the position $`\mathit{pc}` of the block. For a loop $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1` placed at $`\mathit{pc}`:

$$`\begin{aligned}
&\mathit{pc} &&\text{start of the test } K_b\\
&\mathit{pc}+|K_b| &&\text{start of the body } K_1\text{, the true exit of } K_b\\
&\mathit{pc}+|K_b|+|K_1| &&\mathsf{branch}(-(|K_b|+|K_1|+1))\\
&\mathit{pc}+|K_b|+|K_1|+1 &&\text{end of the block, the false exit of } K_b.
\end{aligned}`

The test ends at $`\mathit{pc}+|K_b|`. Its true exit $`\mathit{pc}+|K_b|+0` is the start of the body. Its false exit $`\mathit{pc}+|K_b|+(|K_1|+1)` is the end of the block. The backward branch sits at $`\mathit{pc}+|K_b|+|K_1|`. By its rule in [B.4](machine-card/index.html#machine-b4) it continues at

$$`(\mathit{pc}+|K_b|+|K_1|)+1-(|K_b|+|K_1|+1)=\mathit{pc},`

the start of the test. For a conditional at $`\mathit{pc}` write $`K_t=\mathrm{cbexp}(b,0,|K_1|+1)` for its test. Then $`K_1` starts at $`\mathit{pc}+|K_t|`, the instruction $`\mathsf{branch}(|K_2|)` sits at $`\mathit{pc}+|K_t|+|K_1|`, and $`K_2` starts at $`\mathit{pc}+|K_t|+|K_1|+1`. The false exit of the test is the start of $`K_2`. The branch after $`K_1` continues at $`(\mathit{pc}+|K_t|+|K_1|)+1+|K_2|`, the end of the block.

Now take $`c=(x:=0;W)` with $`W=\mathsf{while}\ x\le1\ \mathsf{do}\ x:=x+1`. The body code is $`K_1=[\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus},\mathsf{setvar}(x)]`. The test is $`K_b=\mathrm{cbexp}(x\le1,0,5)=[\mathsf{load}(x),\mathsf{push}(1),\mathsf{ble}(0,5)]`. So $`\mathrm{ccom}(W)` has $`3+4+1=8` instructions and ends with $`\mathsf{branch}(-8)`. In $`\mathrm{ccom}(c)` the code $`[\mathsf{push}(0),\mathsf{setvar}(x)]` of $`x:=0` occupies positions 0–1. The loop code starts at $`\mathit{pc}=2`: the test occupies 2–4, the body 5–8, the backward branch sits at 9, and the block ends at 10. The $`\mathsf{ble}(0,5)` at position 4 continues at $`4+1+0=5` or at $`4+1+5=10`. The branch at 9 continues at $`9+1-8=2`.

# The contract of compiled commands
%%%
tag := "ch16-s2"
%%%

Run the code $`C=\mathrm{ccom}(c)` of the example from a stack $`S` and a state $`\sigma`. Write $`\sigma_0=\sigma[x\mapsto0]`, $`\sigma_1=\sigma[x\mapsto1]` and $`\sigma_2=\sigma[x\mapsto2]`. The run splits into eight paths of $`C`, one after the other. Each line omits the prefix $`C\vdash` of [B.4](machine-card/index.html#machine-b4):

$$`\begin{aligned}
&\text{(1)}\quad\langle0,S,\sigma\rangle\to^*\langle2,S,\sigma_0\rangle &&\text{code of } x:=0\\
&\text{(2)}\quad\langle2,S,\sigma_0\rangle\to^*\langle5,S,\sigma_0\rangle &&\text{test: } 0\le1 \text{ holds}\\
&\text{(3)}\quad\langle5,S,\sigma_0\rangle\to^*\langle9,S,\sigma_1\rangle &&\text{body}\\
&\text{(4)}\quad\langle9,S,\sigma_1\rangle\to\langle2,S,\sigma_1\rangle &&\mathsf{branch}(-8)\\
&\text{(5)}\quad\langle2,S,\sigma_1\rangle\to^*\langle5,S,\sigma_1\rangle &&\text{test: } 1\le1 \text{ holds}\\
&\text{(6)}\quad\langle5,S,\sigma_1\rangle\to^*\langle9,S,\sigma_2\rangle &&\text{body}\\
&\text{(7)}\quad\langle9,S,\sigma_2\rangle\to\langle2,S,\sigma_2\rangle &&\mathsf{branch}(-8)\\
&\text{(8)}\quad\langle2,S,\sigma_2\rangle\to^*\langle10,S,\sigma_2\rangle &&\text{test: } 2\le1 \text{ fails}
\end{aligned}`

Inside a path the test and the body push integers above $`S` and pop them again. At the end of every path the stack is $`S`.

The derivation of $`\sigma\vdash c\Downarrow\sigma_2` has the same nesting. Its root uses the sequence rule with the premises $`\sigma\vdash x:=0\Downarrow\sigma_0` and $`E_0:\sigma_0\vdash W\Downarrow\sigma_2`. The derivation $`E_0` uses the loop iteration rule with the premises $`\sigma_0\vdash x:=x+1\Downarrow\sigma_1` and $`E_1:\sigma_1\vdash W\Downarrow\sigma_2`. The derivation $`E_1` uses it again, with $`\sigma_1\vdash x:=x+1\Downarrow\sigma_2` and $`E_2:\sigma_2\vdash W\Downarrow\sigma_2`. The derivation $`E_2` uses the loop exit rule. Each derivation matches a part of the run. The premise $`\sigma\vdash x:=0\Downarrow\sigma_0` matches path (1). $`E_0` matches paths (2)–(8), $`E_1` matches (5)–(8), and $`E_2` matches (8). The three loop derivations concern the same command $`W`. Their parts of the run start at the same position $`2` in different states, and all end at position $`10`.

*Definition 16.1 (Contract of compiled commands).* Let $`K` be code and $`c` a command. The code $`K` *meets the contract* for $`c` if for all states $`\sigma,\sigma'` with $`\sigma\vdash c\Downarrow\sigma'`, and for every code $`C`, position $`\mathit{pc}` and stack $`S` with $`\mathrm{at}(C,\mathit{pc},K)`,

$$`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|K|,\,S,\,\sigma'\rangle.`

The contract has four parts. The run starts at the first position of $`K` and reaches the position just after its last instruction. The state changes from $`\sigma` to $`\sigma'`, as in the execution of $`c`. The stack is $`S` again. The code around $`K` is arbitrary, so $`K` may be placed anywhere in any program. In the example, $`\mathrm{ccom}(W)` is at position $`2`, and paths (2)–(8) go from $`\langle2,S,\sigma_0\rangle` to $`\langle2+8,S,\sigma_2\rangle`.

*Theorem 16.2 (Compiled commands meet the contract).* For every command $`c` and states $`\sigma,\sigma'`, if $`\sigma\vdash c\Downarrow\sigma'`, then for every code $`C`, position $`\mathit{pc}` and stack $`S` with $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))`,

$$`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|\mathrm{ccom}(c)|,\,S,\,\sigma'\rangle.`

In words, $`\mathrm{ccom}(c)` meets the contract for $`c`. The quantifiers over $`C`, $`\mathit{pc}` and $`S` come after the hypothesis $`\sigma\vdash c\Downarrow\sigma'`. In an induction on the derivation of that hypothesis, they therefore belong to the induction property.

# Proof by induction on derivations
%%%
tag := "ch16-s3"
%%%

Why induct on the derivation? Consider $`E_0` in the example. Its part of the run, paths (2)–(8), contains paths (5)–(8): a run of the code of $`W` from $`\langle2,S,\sigma_1\rangle`. Structural induction on the command gives, for $`W`, a hypothesis about its body $`x:=x+1` only. That hypothesis covers the body paths (3) and (6), but not the run (5)–(8) of the whole loop. Induction on the length of the machine path is not available either, because that path is what the theorem must construct. The derivation $`E_0` has the premise $`E_1:\sigma_1\vdash W\Downarrow\sigma_2`, which is about $`W` itself, and $`E_1` has smaller height than $`E_0` (A.5). Induction on derivations ([Session 3, §3.1](chapter-03/index.html#ch03-s1)) therefore supplies a hypothesis for $`E_1`, and this hypothesis covers paths (5)–(8).

*Proof of Theorem 16.2.* We prove $`P(D)` for every execution derivation $`D` by induction on $`D`. For $`D:\sigma\vdash c\Downarrow\sigma'`, read $`\sigma,c,\sigma'` from the conclusion of $`D`. The induction property is

$$`P(D)\ \coloneqq\ \forall C,\mathit{pc},S,\quad\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))\ \Longrightarrow\ C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|\mathrm{ccom}(c)|,\,S,\,\sigma'\rangle.`

The position is quantified inside $`P(D)`, as the final state was in [Session 3, §3.2](chapter-03/index.html#ch03-s2). The proof applies the hypotheses at the start of each part of a block: the code of $`c_2` in a sequence starts at $`\mathit{pc}+|K_1|`, not at $`\mathit{pc}`. The code $`C` and the stack $`S` are also inside $`P(D)`, as in the statement of Theorem 16.2. Every hypothesis is in fact applied with the $`C` and the $`S` of its case, because the code of a command starts and ends with the stack it is given. So $`C` and $`S` could be fixed before the induction, as the code and the stack were in Session 15 (Exercise 16.2).

*Skip and assignment.* If $`D` ends with the skip rule, then $`c=\mathsf{skip}` and $`\sigma'=\sigma`. The block is empty, and the path with zero transitions ends at $`\langle\mathit{pc}+0,S,\sigma'\rangle`. If $`D` ends with the assignment rule, then $`c` is $`x:=e` and $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. Assume $`\mathrm{at}(C,\mathit{pc},\mathrm{cexp}(e)\mathbin{+\!\!+}[\mathsf{setvar}(x)])` and write $`\ell=|\mathrm{cexp}(e)|`. By B.2, fact 2, $`\mathrm{cexp}(e)` is at $`\mathit{pc}`, and by facts 2 and 1, $`C(\mathit{pc}+\ell)=\mathsf{setvar}(x)`. Corollary 14.4 gives $`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+\ell,\mathrm{eval}(e,\sigma)::S,\sigma\rangle`. The rule for $`\mathsf{setvar}` (B.4) adds one transition to $`\langle\mathit{pc}+\ell+1,S,\sigma'\rangle`. Join the two paths (B.5). No hypothesis is used.

*Sequence (warm-up).* Suppose $`D` ends with the sequence rule. Then $`c=c_1;c_2`, and for some state $`\sigma_1` the premises of $`D` are $`D_1:\sigma\vdash c_1\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash c_2\Downarrow\sigma'`. Fix $`C,\mathit{pc},S` and assume $`\mathrm{at}(C,\mathit{pc},K_1\mathbin{+\!\!+}K_2)`.

1. By B.2, fact 2, $`\mathrm{at}(C,\mathit{pc},K_1)` and $`\mathrm{at}(C,\mathit{pc}+|K_1|,K_2)`.
2. $`P(D_1)` at $`C,\mathit{pc},S` gives $`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|K_1|,S,\sigma_1\rangle`.
3. $`P(D_2)` at $`C,\mathit{pc}+|K_1|,S` gives $`C\vdash\langle\mathit{pc}+|K_1|,S,\sigma_1\rangle\to^*\langle\mathit{pc}+|K_1|+|K_2|,S,\sigma'\rangle`.
4. Join the two paths (B.5). Since $`|\mathrm{ccom}(c)|=|K_1|+|K_2|` (B.2), this is the required path.

*Conditional.* Suppose $`D` ends with the conditional rule. Then $`c=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`, and its premise is $`D_1:\sigma\vdash k\Downarrow\sigma'`, where $`k` is $`c_1` if $`B(b,\sigma)=\mathsf{true}` and $`c_2` otherwise (A.5). Assume $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))`. By B.2, fact 2, the parts are at the positions of the layout in §16.1, and $`C(\mathit{pc}+|K_t|+|K_1|)=\mathsf{branch}(|K_2|)` by fact 1. Theorem 15.2 at $`\mathit{pc}` gives a path to $`\langle\mathit{pc}+|K_t|+\mathrm{sel}(B(b,\sigma),0,|K_1|+1),S,\sigma\rangle`. If $`B(b,\sigma)=\mathsf{true}`, this is the start of $`K_1`, and $`k=c_1`. Then $`P(D_1)` at $`\mathit{pc}+|K_t|` reaches $`\langle\mathit{pc}+|K_t|+|K_1|,S,\sigma'\rangle`, and the branch rule moves to $`\langle\mathit{pc}+|K_t|+|K_1|+1+|K_2|,S,\sigma'\rangle`, the end of the block. If $`B(b,\sigma)=\mathsf{false}`, the path ends at $`\mathit{pc}+|K_t|+|K_1|+1`, the start of $`K_2`, and $`k=c_2`. Then $`P(D_1)` at that position reaches the end of the block with the state $`\sigma'`. In both cases join the paths.

*Loop exit.* Suppose $`D` ends with the loop exit rule. Then $`c=W=\mathsf{while}\ b\ \mathsf{do}\ c_1`, $`B(b,\sigma)=\mathsf{false}` and $`\sigma'=\sigma`. Assume $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(W))`. By B.2, fact 2, $`K_b` is at $`\mathit{pc}`. Theorem 15.2 with $`\mathrm{sel}(\mathsf{false},0,|K_1|+1)=|K_1|+1` gives $`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|K_b|+|K_1|+1,S,\sigma\rangle`, which is $`\langle\mathit{pc}+|\mathrm{ccom}(W)|,S,\sigma'\rangle`. No hypothesis is used.

*Loop iteration (board case).* Suppose $`D` ends with the loop iteration rule. Then $`c=W=\mathsf{while}\ b\ \mathsf{do}\ c_1` (we write $`c_1` for the body because $`c` names the whole command), and $`D` gives $`B(b,\sigma)=\mathsf{true}`, $`D_1:\sigma\vdash c_1\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash W\Downarrow\sigma'` for some state $`\sigma_1`. Write

$$`K_1=\mathrm{ccom}(c_1),\qquad K_b=\mathrm{cbexp}(b,0,|K_1|+1),\qquad d=-(|K_b|+|K_1|+1).`

By B.8, $`\mathrm{ccom}(W)=K_b\mathbin{+\!\!+}K_1\mathbin{+\!\!+}[\mathsf{branch}(d)]`, and $`|\mathrm{ccom}(W)|=|K_b|+|K_1|+1` by B.2. The induction hypotheses are as follows. We name the bound variables $`C',\mathit{pc}',S'` to keep them apart from those of the case.

$$`\begin{aligned}
P(D_1):\quad&\forall C',\mathit{pc}',S',\ \ \mathrm{at}(C',\mathit{pc}',K_1)\Longrightarrow C'\vdash\langle\mathit{pc}',S',\sigma\rangle\to^*\langle\mathit{pc}'+|K_1|,\,S',\,\sigma_1\rangle,\\
P(D_2):\quad&\forall C',\mathit{pc}',S',\ \ \mathrm{at}(C',\mathit{pc}',\mathrm{ccom}(W))\Longrightarrow C'\vdash\langle\mathit{pc}',S',\sigma_1\rangle\to^*\langle\mathit{pc}'+|\mathrm{ccom}(W)|,\,S',\,\sigma'\rangle.
\end{aligned}`

1. Fix $`C,\mathit{pc},S` and assume $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(W))`. We must show $`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|K_b|+|K_1|+1,S,\sigma'\rangle`.
2. By B.2, fact 2 applied twice, $`\mathrm{at}(C,\mathit{pc},K_b)`, $`\mathrm{at}(C,\mathit{pc}+|K_b|,K_1)` and $`\mathrm{at}(C,\mathit{pc}+|K_b|+|K_1|,[\mathsf{branch}(d)])`. By fact 1, $`C(\mathit{pc}+|K_b|+|K_1|)=\mathsf{branch}(d)`.
3. Apply Theorem 15.2 to $`K_b` at $`\mathit{pc}` with the stack $`S` and the state $`\sigma`. Since $`B(b,\sigma)=\mathsf{true}`, $`\mathrm{sel}(B(b,\sigma),0,|K_1|+1)=0`. This gives $`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|K_b|,S,\sigma\rangle`, which ends at the start of the body.
4. Apply $`P(D_1)` with $`C'=C`, $`\mathit{pc}'=\mathit{pc}+|K_b|` and $`S'=S`. Its premise holds by step 2. This gives $`C\vdash\langle\mathit{pc}+|K_b|,S,\sigma\rangle\to^*\langle\mathit{pc}+|K_b|+|K_1|,S,\sigma_1\rangle`.
5. By step 2 and the branch rule (B.4), $`C\vdash\langle\mathit{pc}+|K_b|+|K_1|,S,\sigma_1\rangle\to\langle\mathit{pc}+|K_b|+|K_1|+1+d,S,\sigma_1\rangle`. The target is the start of the loop code: $`(\mathit{pc}+|K_b|+|K_1|)+1-(|K_b|+|K_1|+1)=\mathit{pc}`. So the transition ends at $`\langle\mathit{pc},S,\sigma_1\rangle`. A single transition is a path (B.5).
6. Apply $`P(D_2)` with $`C'=C`, $`\mathit{pc}'=\mathit{pc}` and $`S'=S`. Its premise $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(W))` is the assumption of step 1. This gives $`C\vdash\langle\mathit{pc},S,\sigma_1\rangle\to^*\langle\mathit{pc}+|\mathrm{ccom}(W)|,S,\sigma'\rangle`, and $`\mathit{pc}+|\mathrm{ccom}(W)|=\mathit{pc}+|K_b|+|K_1|+1`.
7. Join the paths of steps 3–6 (B.5). The result goes from $`\langle\mathit{pc},S,\sigma\rangle` to $`\langle\mathit{pc}+|K_b|+|K_1|+1,S,\sigma'\rangle`, as required in step 1.

Step 6 applies a hypothesis about the loop $`W` itself. $`D_2` is an immediate execution subderivation of $`D`, so its height is smaller (A.5), and $`P(D_2)` is an induction hypothesis. Structural induction on $`c` would offer no such hypothesis. Step 4 applies $`P(D_1)` at the position $`\mathit{pc}+|K_b|`, not at $`\mathit{pc}`. Step 5 is where the layout enters: the equation sends the machine back to the position where step 6 needs the code of $`W`. In the example take $`D=E_0` and $`\mathit{pc}=2`. Steps 3, 4 and 5 are paths (2), (3) and (4), with the intermediate state $`\sigma_1` of the example. Step 6 applies $`P(E_1)` and obtains paths (5)–(8).

This proves $`P(D)` for every derivation $`D`. Theorem 16.2 is $`P(D)` for the given derivation at the given $`C,\mathit{pc},S`. $`\square`

# What the theorem does not say
%%%
tag := "ch16-s4"
%%%

A whole program $`c` is compiled to $`\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]` and started in $`\langle0,[\,],\sigma\rangle` ([B.9](machine-card/index.html#machine-b9)).

*Corollary 16.3 (Whole programs).* For every command $`c` and states $`\sigma,\sigma'`, if $`\sigma\vdash c\Downarrow\sigma'`, then the machine running $`\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]` terminates from $`\sigma` with final state $`\sigma'`.

*Proof.* Let $`C=\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]`. Then $`\mathrm{at}(C,0,C)` holds with two empty lists around $`C`. By B.2, fact 2, $`\mathrm{at}(C,0,\mathrm{ccom}(c))` and $`\mathrm{at}(C,|\mathrm{ccom}(c)|,[\mathsf{halt}])`, and by fact 1, $`C(|\mathrm{ccom}(c)|)=\mathsf{halt}`. Theorem 16.2 with $`\mathit{pc}=0` and $`S=[\,]` gives $`C\vdash\langle0,[\,],\sigma\rangle\to^*\langle|\mathrm{ccom}(c)|,[\,],\sigma'\rangle`. This is termination with final state $`\sigma'` in the sense of B.9. $`\square`

The hypothesis $`\sigma\vdash c\Downarrow\sigma'` restricts Theorem 16.2 and Corollary 16.3 to source programs that terminate. B.9 lists three behaviours of the machine. Corollary 16.3 says that a terminating source program yields the first one, with the same final state. The theorem says nothing in the following situations.

The direction matters when comparing this result with refinement ([§7.1](chapter-07/index.html#ch07-s1)). Here the given evidence is a terminating source execution. The conclusion supplies a path through compiled code, with the prescribed exit position, stack and state. To establish that every target behavior is allowed by the source, one would have to start with a target behavior.

*Diverging source programs.* If $`c` has no terminating execution from $`\sigma`, there is no derivation to start from, and the theorem promises nothing. Take $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`. It has no terminating execution ([Session 2, §2.4](chapter-02/index.html#ch02-s4)) and an infinite path from every state ([Session 5, Example 5.5](chapter-05/index.html#ch05-s3)). Its body code is empty and $`\mathrm{cbexp}(\mathsf{true},0,1)=[\,]`, so the loop compiles to $`[\mathsf{branch}(-1)]`. In the whole program $`[\mathsf{branch}(-1),\mathsf{halt}]` the branch at position $`0` continues at $`0+1-1=0`. The machine diverges, as the source program does. No result of this session proves that this happens for every diverging program. That needs a different method, which follows the source program step by step (Further Reading).

*Failing source programs.* A source program fails when it reaches a configuration other than skip that has no transition. IMP has no such program: by [Session 5, Lemma 5.3](chapter-05/index.html#ch05-s2), every configuration other than skip has a transition. In a language with a failing operation, such as division by zero, a failing run has no derivation either. The theorem would then say nothing about the compiled code of a failing program. That code could go wrong (B.9) or end with any state.

*The converse.* The theorem turns a source execution into a machine run. It does not turn a machine run into a source execution. Nipkow and Klein prove that converse for their compiler as Lemma 8.18. [Session 21](chapter-21/index.html) collects the premises of this theorem with those of the other correctness theorems of Part 1.

# Exercises
%%%
tag := "ch16-s5"
number := false
%%%

*16.1.* Compile $`\mathsf{if}\ x=0\ \mathsf{then}\ y:=1\ \mathsf{else}\ y:=2` and place the code at position $`3` of a larger program. Give the start of each part, the end of the block, and the target of each branch instruction. Run the code from states with $`\sigma(x)=0` and $`\sigma(x)=5`. In each run, at which position does the conditional case apply its induction hypothesis?

*16.2.* Suppose the induction property fixed the position before the induction: $`P_{\mathit{pc}}(D)\coloneqq\forall C,S,\ \mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))\Rightarrow C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|\mathrm{ccom}(c)|,S,\sigma'\rangle`. Which cases of the proof fail, and at which position does each need its hypothesis? Which step of the board case still goes through? What fails if $`C` and $`S` are fixed instead and the position stays quantified?

*16.3.* Suppose the compiler ended every loop with $`\mathsf{branch}(-(|K_b|+|K_1|))`. Compile $`x:=0;\ \mathsf{while}\ x\le1\ \mathsf{do}\ x:=x+1` with this change and run it from the stack $`[7]`. Where does the run end, and with which stack and which value of $`x`? What happens from the empty stack? Which step of the board case fails?

*Further problem.* Add a command $`\mathsf{if}\ b\ \mathsf{then}\ c_1` with two rules: if $`B(b,\sigma)=\mathsf{true}` and $`\sigma\vdash c_1\Downarrow\sigma'`, then $`\sigma\vdash\mathsf{if}\ b\ \mathsf{then}\ c_1\Downarrow\sigma'`; if $`B(b,\sigma)=\mathsf{false}`, then $`\sigma\vdash\mathsf{if}\ b\ \mathsf{then}\ c_1\Downarrow\sigma`. Compile it to $`\mathrm{cbexp}(b,0,|K_1|)\mathbin{+\!\!+}K_1` with $`K_1=\mathrm{ccom}(c_1)`. Draw its layout and prove the two new cases of Theorem 16.2. Why does this code need no branch instruction of its own?

# Reading for the Seminar
%%%
tag := "ch16-s6"
number := false
%%%

*Definitions · 10 minutes.* Write the five clauses of $`\mathrm{ccom}`. Compile $`x:=0;\ \mathsf{while}\ x\le1\ \mathsf{do}\ x:=x+1`, mark the layout of the loop, and compute the targets of $`\mathsf{ble}(0,5)` and $`\mathsf{branch}(-8)`.

*Joint proof · 30 minutes.* Write $`P(D)` with its three quantifiers. Do the sequence case as a warm-up. Then write $`P(D_1)` and $`P(D_2)` for the loop iteration rule and the seven steps of the board case. Check step 5 on the example.

*Proof review · 20 minutes.* Do the conditional and loop exit cases. Use Exercise 16.2 to find which quantifier each case needs. Compile $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}` and say what Theorem 16.2 says about it.

*Facilitator’s hint.* In step 5, ask where the backward branch lands. In step 6, ask which derivation the hypothesis is about, and why it is smaller than $`D` although its command is the same.

# Solutions and Further Reading
%%%
tag := "ch16-s7"
number := false
%%%

*16.1.* Here $`K_1=[\mathsf{push}(1),\mathsf{setvar}(y)]`, $`K_2=[\mathsf{push}(2),\mathsf{setvar}(y)]` and $`K_t=\mathrm{cbexp}(x=0,0,3)=[\mathsf{load}(x),\mathsf{push}(0),\mathsf{beq}(0,3)]`. At position $`3` the test occupies 3–5, $`K_1` occupies 6–7, $`\mathsf{branch}(2)` sits at 8, $`K_2` occupies 9–10, and the block ends at 11. The $`\mathsf{beq}(0,3)` at 5 continues at $`5+1+0=6` or at $`5+1+3=9`. The branch at 8 continues at $`8+1+2=11`. With $`\sigma(x)=0` the test reaches 6, the code of $`y:=1` reaches 8 with $`y=1`, and the branch reaches 11. The hypothesis is applied at position 6, to the premise $`\sigma\vdash y:=1\Downarrow\sigma[y\mapsto1]`. With $`\sigma(x)=5` the test reaches 9, and the code of $`y:=2` reaches 11 with $`y=2`. The hypothesis is applied at position 9.

*16.2.* Skip, assignment and loop exit use no hypothesis and still go through. The sequence case needs the hypothesis for $`c_2` at $`\mathit{pc}+|K_1|`. The conditional case needs it at $`\mathit{pc}+|K_t|` or at $`\mathit{pc}+|K_t|+|K_1|+1`. The board case needs $`P(D_1)` at $`\mathit{pc}+|K_b|` in step 4, so step 4 fails. Step 6 still goes through, because the backward branch returns to $`\mathit{pc}` itself. If $`C` and $`S` are fixed instead, nothing fails: every hypothesis is applied with the code and the stack of its case.

*16.3.* The branch at position 9 is now $`\mathsf{branch}(-7)` and continues at $`9+1-7=3`, one instruction after the start of the test. The first iteration runs as before and reaches position 9 with $`x=1` and the stack $`[7]`. The branch moves to 3, where $`\mathsf{push}(1)` gives $`[1,7]`. The $`\mathsf{ble}(0,5)` at 4 pops $`n_2=1` and $`n_1=7`. Since $`7\le1` fails, it continues at $`4+1+5=10` with the empty stack. The run ends at the end of the code with $`x=1`, whereas the source program ends with $`x=2`, and the stack $`[7]` is lost. From the empty stack the $`\mathsf{ble}` at 4 finds only one integer, so that configuration has no transition. In the whole program it goes wrong (B.9). In the board case the equation of step 5 becomes $`(\mathit{pc}+|K_b|+|K_1|)+1-(|K_b|+|K_1|)=\mathit{pc}+1`. The code of $`W` is not at $`\mathit{pc}+1`, so step 6 cannot apply $`P(D_2)`.

*Further problem.* At $`\mathit{pc}` the test $`K_t=\mathrm{cbexp}(b,0,|K_1|)` starts at $`\mathit{pc}`, $`K_1` at $`\mathit{pc}+|K_t|`, and the block ends at $`\mathit{pc}+|K_t|+|K_1|`. The false exit of the test is the end of the block. If $`B(b,\sigma)=\mathsf{true}`, Theorem 15.2 reaches $`\langle\mathit{pc}+|K_t|,S,\sigma\rangle`, the hypothesis for the premise $`\sigma\vdash c_1\Downarrow\sigma'` at $`\mathit{pc}+|K_t|` reaches $`\langle\mathit{pc}+|K_t|+|K_1|,S,\sigma'\rangle`, and the two paths are joined. If $`B(b,\sigma)=\mathsf{false}`, Theorem 15.2 reaches $`\langle\mathit{pc}+|K_t|+|K_1|,S,\sigma\rangle` directly, and $`\sigma'=\sigma`. The two-armed conditional needs $`\mathsf{branch}(|K_2|)` to skip $`K_2` after $`K_1`. Here nothing follows $`K_1` inside the block, so the end of $`K_1` is already the end of the block.

*Further reading · Diverging programs.* The last part of the compiler chapter of Leroy’s _Compiler Verification_ course proves that the code of a diverging program diverges. A big-step derivation cannot describe a run that does not end, so the course uses a small-step semantics. Its configurations hold the command in focus, a continuation that records the pending work, and a state. The course proves that each source step is matched by a finite path of machine transitions, and that a source step matched by an empty path decreases a natural-number measure of the source configuration. For example, the step that moves the focus to the first command of a sequence, and records the second command in the continuation, runs no instruction. The measure cannot decrease forever, so an infinite source run yields an infinite machine run. The same simulation also gives the terminating case for whole programs, stated with this small-step semantics instead of the big-step one. [Leroy’s course, compiler chapter](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean)

*Further reading · Sources.* Nipkow and Klein, _Concrete Semantics_, §8.4, prove Lemma 8.9 by rule induction on the big-step semantics. Their code runs on its own from position $`0`, and Lemma 8.5 composes such runs. They prove the converse, Lemma 8.18, by structural induction on the command, with a nested induction on the length of the machine run in the loop case, and combine both directions in Theorem 8.19. They remark that for a deterministic language such as IMP the converse reduces to preserving termination. Our machine is deterministic too: each configuration has at most one transition (B.4). So when $`\sigma\vdash c\Downarrow\sigma'`, the run of Corollary 16.3 is the only run from $`\langle0,[\,],\sigma\rangle`, and the compiled program can neither diverge nor go wrong from $`\sigma`. This uses a fact about the machine, not Theorem 16.2 alone. [Concrete Semantics, §8.4](https://concrete-semantics.org/concrete-semantics.pdf#page=112) · [Source and Lean names](machine-card/index.html#machine-sources)

# Sources and Formalization
%%%
tag := "ch16-notes"
number := false
%%%

The compiler $`\mathrm{ccom}` is that of Leroy’s course, as recorded in the stack machine card. Theorem 16.2 is the correctness theorem for compiled commands, terminating case, in that course. Nipkow and Klein prove the same statement for their compiler. They run the compiled code on its own from position $`0` and place it in a larger program with a separate composition lemma. [Source and Lean names](machine-card/index.html#machine-sources) · [Concrete Semantics, §8.4, p. 103](https://concrete-semantics.org/concrete-semantics.pdf#page=113)

* *Definition 16.1.* Formulated in this book.
* *Theorem 16.2.* Corresponds to CS Lemma 8.9. Externally checked: the statement matches a declaration of Leroy’s course ([`compile_com_correct_terminating`](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean#L475) · [machine-card references](machine-card/index.html#machine-sources)).
* *Corollary 16.3.* Formulated in this book. Paper proof only ([§16.4](chapter-16/index.html#ch16-s4)).
