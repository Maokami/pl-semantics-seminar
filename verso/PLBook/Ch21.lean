import VersoManual

open Verso.Genre Manual

#doc (Manual) "What the Theorems of Part 1 Say" =>
%%%
tag := "ch21"
file := "chapter-21"
%%%

Run `y := x + 1; x := 0` from a state with $`x=4`. Four theorems of Part 1 speak about this run. Session 6 gives it a path of transitions that ends at skip. Session 10 gives it a meaning that is a state. Session 16 runs its compiled code to the end of the block. Session 20 deletes its second assignment and keeps the final value of $`y`. Quoted in one line, each says that two things agree. Each compares a different part of the result, and each needs premises that are easy to drop. This session writes the premises back and runs the program through all four theorems.

*In this session.*

* *Definitions.* Execution rules and transitions ([A.5–A.6](imp-card/index.html#imp-a5)). Observation ([Session 7, §7.1](chapter-07/index.html#ch07-s1)). Outcomes, strict extension and the meanings $`f_c` ([Session 8, Definitions 8.1–8.4](chapter-08/index.html#ch08-s1); [Session 9, Definition 9.4](chapter-09/index.html#ch09-s2)). Code at a position, machine configurations, $`\mathrm{ccom}` and whole programs ([B.2–B.9](machine-card/index.html#machine-b2)). Abstract states and $`\gamma` ([Session 17, §17.1](chapter-17/index.html#ch17-s1)) and constant propagation $`\mathrm{cp}` ([Session 18, §18.2](chapter-18/index.html#ch18-s2)). The liveness transfer $`\mathrm{live}(c,L)` ([Session 19, Definitions 19.2–19.3](chapter-19/index.html#ch19-s1)), agreement $`\sigma|_X=\sigma''|_X` ([Session 1, §1.3](chapter-01/index.html#ch01-s3)) and $`\mathrm{elim}(c,L)` ([Session 20, §20.1](chapter-20/index.html#ch20-s1)). Progress ([Session 5, Lemma 5.3](chapter-05/index.html#ch05-s2)).
* *New terms.* None. [Glossary](glossary/index.html)
* *Theorems.* No new theorem. §21.1 restates [Session 6, Theorem 6.2](chapter-06/index.html#ch06-s2), [Session 10, Theorem 10.2](chapter-10/index.html#ch10-s1), [Session 16, Theorem 16.2](chapter-16/index.html#ch16-s2) and [Session 20, Theorem 20.2](chapter-20/index.html#ch20-s2) with every premise, and names the observation each one preserves or equates.
* *Board case.* Fill the row of Theorem 20.2 for $`c=(y:=x+1;\ x:=0)` and the observed set $`\{y\}`: compute the live sets and $`\mathrm{elim}(c,\{y\})`, check both premises, run the transformed command, and name what the conclusion compares and what it leaves out. Seven steps (§21.2).
* *Proof outline.* No induction. Each theorem is applied in three moves: instantiate its quantifiers, check its premises, read off its conclusion. The runs of the example are computed with the rules of A.5, A.6 and B.4.
* *From Session 20.* Session 20 proved that removing dead assignments keeps the final values of the observed names. That is the last correctness theorem of Part 1. Here it is set beside the theorems of Sessions 6, 10 and 16.

# Terminating executions and Hoare soundness
%%%
tag := "ch21-s1"
%%%

[Session 7, §7.1](chapter-07/index.html#ch07-s1) calls what a notion of equivalence compares about a run its *observation*. Program equivalence (Definition 7.1) observes the whole final state. We use the word in the same sense for each theorem below. Four results below describe the run of the example in §21.2. Hoare soundness gives a fifth kind of statement about that program, with a proof of a triple as its premise.

*Theorem 6.2 (Equivalence of terminating executions), restated.* For every command $`c` and states $`\sigma,\sigma'`, $`\sigma\vdash c\Downarrow\sigma'` if and only if $`\langle c,\sigma\rangle\to^*\langle\mathsf{skip},\sigma'\rangle`.

*Theorem 10.2 (Correspondence), restated.* For every command $`c` and states $`\sigma,\sigma'\in\Sigma`, $`\sigma\vdash c\Downarrow\sigma'` if and only if $`f_c(\sigma)=\sigma'`.

[Hoare soundness (Theorem 12.3)](chapter-12/index.html#ch12-s3) begins with a different kind of evidence. For any assertions $`P,Q` and command $`c`, a derivation of $`\vdash_{\mathrm H}\{P\}\,c\,\{Q\}` implies $`\models\{P\}\,c\,\{Q\}`. Take any initial state satisfying $`P` and any terminating execution from it. Soundness guarantees that its final state satisfies $`Q`. A single execution can refute a triple by violating its postcondition. Even a successful execution supplies no derivation of a triple about all initial states.

*Theorem 16.2 (Compiled commands meet the contract), restated.* For every command $`c` and states $`\sigma,\sigma'`, if $`\sigma\vdash c\Downarrow\sigma'`, then for every code $`C`, position $`\mathit{pc}` and stack $`S` with $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))`, $`C\vdash\langle\mathit{pc},S,\sigma\rangle\to^*\langle\mathit{pc}+|\mathrm{ccom}(c)|,S,\sigma'\rangle`.

*Theorem 20.2 (Correctness of dead-assignment elimination), restated.* For every command $`c`, finite set of names $`L` and states $`\sigma,\sigma',\sigma''`: if $`\sigma\vdash c\Downarrow\sigma'` and $`\sigma|_{\mathrm{live}(c,L)}=\sigma''|_{\mathrm{live}(c,L)}`, then some state $`\sigma'''` satisfies $`\sigma''\vdash\mathrm{elim}(c,L)\Downarrow\sigma'''` and $`\sigma'|_L=\sigma'''|_L`.

*Observations.* Theorem 6.2 equates final states: the state at the root of a derivation is the state beside skip at the end of a path. Theorem 10.2 equates the final state with the normal result of the meaning, that is, the outcome $`f_c(\sigma)` when it is a state. Theorem 16.2 preserves the final state and observes two more things: the run of the code reaches the position just after the block, and the stack there is the $`S` it started with. Theorem 20.2 preserves only the final values of the names in $`L`.

*Premises.* Theorems 6.2 and 10.2 are biconditionals. Either side can serve as the premise for the other. Two choices in Theorem 10.2 matter for that reading. The final $`\sigma'` is a state, never $`\bot`. The meaning $`f_W` of a loop is the least fixed point of its unfolding operator (Session 9, Definition 9.4 and Theorem 9.5); with another fixed point the direction from meanings to derivations fails ([Session 10, §10.4](chapter-10/index.html#ch10-s4)). Session 10, Corollary 10.3 adds that $`f_c(\sigma)=\bot` exactly when no state $`\sigma'` satisfies $`\sigma\vdash c\Downarrow\sigma'`. Theorem 16.2 needs a terminating source execution and the code at $`\mathit{pc}`. [Session 16, Corollary 16.3](chapter-16/index.html#ch16-s4) takes $`C=\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]`, $`\mathit{pc}=0` and $`S=[\,]`: the whole program terminates with final state $`\sigma'` (B.9). Theorem 20.2 needs a terminating run of the original command and agreement of the two initial states on the live set. Its external check assumes one axiom about finite sets ([Session 20, §20.2](chapter-20/index.html#ch20-s2)), which the paper proof does not need.

The table adds [Session 18, Theorem 18.4](chapter-18/index.html#ch18-s3): if $`\sigma\in\gamma(A)` and $`\sigma\vdash c\Downarrow\sigma'`, then $`\sigma\vdash\mathrm{cp}(A,c)\Downarrow\sigma'`. Theorems 16.2, 18.4 and 20.2 share the premise $`\sigma\vdash c\Downarrow\sigma'`.

:::table +header
*
  * Theorem
  * Premises
  * Observed
  * Not said
*
  * Theorem 6.2
  * For each command, input state and candidate final state, either form of terminating execution supplies the premise for the other.
  * The final state, at the root of a derivation and beside skip at the end of a path.
  * The length of the path or the height of the derivation. Intermediate configurations. An infinite path when no derivation exists.
*
  * Theorem 10.2
  * For each input and final state, either a terminating derivation or the corresponding denotational equality. Loop meanings use the least fixed point.
  * The outcome $`f_c(\sigma)` when it is a state.
  * Intermediate states and numbers of steps. By Corollary 10.3, $`f_c(\sigma)=\bot` says only that no terminating execution exists.
*
  * [Theorem 12.3](chapter-12/index.html#ch12-s3)
  * A Hoare derivation of $`\{P\}\,c\,\{Q\}`.
  * Every terminating execution from a state satisfying $`P` ends in one satisfying $`Q`.
  * Termination from those states. Derivability from validity.
*
  * Theorem 16.2
  * $`\sigma\vdash c\Downarrow\sigma'`. $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))`.
  * The configuration $`\langle\mathit{pc}+|\mathrm{ccom}(c)|,S,\sigma'\rangle`: end position, same stack, final state.
  * Nonterminating source programs. Failing source programs. A source run from a machine run. Configurations inside the block.
*
  * Theorem 18.4
  * $`\sigma\in\gamma(A)`. $`\sigma\vdash c\Downarrow\sigma'`.
  * The whole final state of $`\mathrm{cp}(A,c)` from $`\sigma`.
  * Nonterminating source programs. Failing source programs. States outside $`\gamma(A)`. A run of $`c` from a run of $`\mathrm{cp}(A,c)`.
*
  * Theorem 20.2
  * $`\sigma\vdash c\Downarrow\sigma'`. $`\sigma|_{\mathrm{live}(c,L)}=\sigma''|_{\mathrm{live}(c,L)}`.
  * The final values of the names in $`L`.
  * Names outside $`L`. Nonterminating source programs. Failing source programs. A run of $`c` from a run of $`\mathrm{elim}(c,L)`.
:::

# One program through four theorems
%%%
tag := "ch21-s2"
%%%

Let $`x,y` be distinct names, let $`c=(y:=x+1;\ x:=0)`, and let $`\sigma` be a state with $`\sigma(x)=4`. Put $`\sigma_1=\sigma[y\mapsto5]` and $`\sigma'=\sigma_1[x\mapsto0]`. The assignment rule gives $`\sigma\vdash y:=x+1\Downarrow\sigma_1` and $`\sigma_1\vdash x:=0\Downarrow\sigma'`. The sequence rule joins them into a derivation $`D:\sigma\vdash c\Downarrow\sigma'` of height one.

*Theorem 6.2.* $`D` gives the left side. The rules of A.6 (the lifted assignment, discarding skip, the assignment) give the right side, $`\langle c,\sigma\rangle\to\langle\mathsf{skip};x:=0,\ \sigma_1\rangle\to\langle x:=0,\ \sigma_1\rangle\to\langle\mathsf{skip},\sigma'\rangle`. The path has three edges, and $`D` has height one. The theorem compares only the final state $`\sigma'`.

*Theorem 10.2.* Definitions 8.3 and 8.4 give $`f_c(\sigma)=f_{x:=0}^\dagger(f_{y:=x+1}(\sigma))=f_{x:=0}^\dagger(\sigma_1)=f_{x:=0}(\sigma_1)=\sigma'`. The operational semantics gives a derivation or a path for this run. The denotational semantics gives a function on initial states. At $`\sigma` that function returns the very state $`\sigma'` reached by the run.

In the axiomatic semantics we can use the rules of Hoare logic to prove a guarantee for the same command, $`\{x=4\}\ c\ \{y=5\}`. The first assignment establishes $`y=5` from $`x=4`. The second changes only $`x`, so $`y=5` still holds. The sequence rule joins these two facts. By [Hoare soundness](chapter-12/index.html#ch12-s3), the conclusion covers every terminating run from a state with $`x=4`, whatever the initial value of $`y`. The triple leaves the final value of $`x` unspecified.

*Theorem 16.2.* By B.6 and B.8, $`\mathrm{ccom}(c)=[\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus},\mathsf{setvar}(y),\mathsf{push}(0),\mathsf{setvar}(x)]` has six instructions. Take $`C=\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]`, $`\mathit{pc}=0` and $`S=[\,]`. The rules of B.4 give $`C\vdash\langle0,[\,],\sigma\rangle\to\langle1,[4],\sigma\rangle\to\langle2,[1,4],\sigma\rangle\to\langle3,[5],\sigma\rangle\to\langle4,[\,],\sigma_1\rangle\to\langle5,[0],\sigma_1\rangle\to\langle6,[\,],\sigma'\rangle`, and $`C(6)=\mathsf{halt}`. The theorem predicts only the last configuration: position $`0+6`, stack $`[\,]`, state $`\sigma'`. The stacks $`[4]`, $`[1,4]`, $`[5]` and $`[0]` inside the run are not observed. Placed at any position $`\mathit{pc}` of any code and started with any stack $`S`, the same block goes from $`\langle\mathit{pc},S,\sigma\rangle` to $`\langle\mathit{pc}+6,S,\sigma'\rangle`.

*Theorem 20.2 (board case).* We must fill the row of Theorem 20.2 for $`c` and $`L=\{y\}`.

1. Compute the live sets from the end (Definition 19.2). Since $`x\notin\{y\}`, $`\mathrm{live}(x:=0,\{y\})=\{y\}`. Since $`y\in\{y\}`, $`\mathrm{live}(y:=x+1,\{y\})=(\{y\}\smallsetminus\{y\})\cup\mathrm{FV}(x+1)=\{x\}`. The sequence clause gives $`\mathrm{live}(c,\{y\})=\mathrm{live}(y:=x+1,\mathrm{live}(x:=0,\{y\}))=\{x\}`.
2. Definition 20.1 gives $`\mathrm{elim}(c,\{y\})=\mathrm{elim}(y:=x+1,\{y\});\ \mathrm{elim}(x:=0,\{y\})=(y:=x+1;\ \mathsf{skip})`. The assignment $`x:=0` is dead.
3. First premise: $`D` derives $`\sigma\vdash c\Downarrow\sigma'`.
4. Second premise: take $`\sigma''` with $`\sigma''(x)=4` and $`\sigma''(y)=100`. Then $`\sigma|_{\{x\}}=\sigma''|_{\{x\}}`. The premise asks nothing about $`y`.
5. Conclusion: the theorem gives a state $`\sigma'''` with $`\sigma''\vdash\mathrm{elim}(c,\{y\})\Downarrow\sigma'''` and $`\sigma'|_{\{y\}}=\sigma'''|_{\{y\}}`. The assignment, skip and sequence rules give $`\sigma'''=\sigma''[y\mapsto5]`, and indeed $`\sigma'(y)=5=\sigma'''(y)`.
6. What it leaves out: $`\sigma'(x)=0` and $`\sigma'''(x)=\sigma''(x)=4`, so the final states differ at $`x`. With $`\sigma''=\sigma` they still differ at $`x`, since then $`\sigma'''=\sigma_1\neq\sigma'`. The theorem cannot conclude $`\sigma'''=\sigma'`.
7. The row: the premises are $`\sigma\vdash c\Downarrow\sigma'` and $`\sigma(x)=\sigma''(x)`. The observation is the final value of $`y`. Not said: the final value of $`x`.

One run, four observations. Theorems 6.2 and 10.2 observe the final state $`\sigma'`. Theorem 16.2 observes $`\sigma'` with the end position and the unchanged stack. Theorem 20.2 observes only $`\sigma'(y)`. Theorem 18.4 observes the whole final state, as Definition 7.1 does. With $`A=\{x\mapsto4\}` we have $`\sigma\in\gamma(A)` and $`\mathrm{cp}(A,c)=(y:=5;\ x:=0)`, and the theorem gives $`\sigma\vdash(y:=5;\ x:=0)\Downarrow\sigma'`.

# What the theorems do not say
%%%
tag := "ch21-s3"
%%%

*Nonterminating source programs.* Let $`W=\mathsf{while\ true\ do\ skip}`. It has no terminating execution ([Session 2, §2.4](chapter-02/index.html#ch02-s4)). Theorems 16.2, 18.4 and 20.2 start from a derivation $`\sigma\vdash c\Downarrow\sigma'`, so for $`W` they say nothing about $`\mathrm{ccom}(W)`, $`\mathrm{cp}(A,W)` or $`\mathrm{elim}(W,L)`. The code $`\mathrm{ccom}(W)=[\mathsf{branch}(-1)]` does run forever ([Session 16, §16.4](chapter-16/index.html#ch16-s4)), but that is a computation for one program, not a consequence of Theorem 16.2. Theorems 6.2 and 10.2 are equivalences, so they do say something: no path from $`\langle W,\sigma\rangle` reaches skip, and $`f_W(\sigma)=\bot` by Corollary 10.3. Neither builds the infinite path of [Session 5, Example 5.5](chapter-05/index.html#ch05-s3) by itself (Further problem).

*Failing source programs.* A run fails when it reaches a configuration other than skip with no transition. By Session 5, Lemma 5.3, IMP has no failing run, so for the language of Part 1 the question does not arise. Add an operation that can fail, such as division by zero. A failing run has no derivation, and Theorems 16.2, 18.4 and 20.2 again say nothing about it. The target may then behave differently. Deleting a dead assignment whose expression fails turns a failing run into a terminating one ([Session 20, Solution 20.4](chapter-20/index.html#ch20-s6)). The compiled code of a failing program may go wrong or end with any state (Session 16, §16.4).

*The converse.* Theorems 16.2, 18.4 and 20.2 turn a run of the source into a run of the target. None of them turns a run of the target into a run of the source.

# Exercises
%%%
tag := "ch21-s4"
number := false
%%%

*21.1.* Let $`d=(z:=x;\ \mathsf{if}\ x\le0\ \mathsf{then}\ y:=1\ \mathsf{else}\ y:=2)` and let $`\sigma(x)=3`, with $`0` at every other name. Fill the four rows for $`d`: the path of Theorem 6.2 and its length; $`f_d(\sigma)`; $`\mathrm{ccom}(d)` and the final configuration that Theorem 16.2 gives at $`\mathit{pc}=0` and $`S=[\,]`; and, for $`L=\{y\}`, $`\mathrm{live}(d,L)`, $`\mathrm{elim}(d,L)` and the name at which the final states of $`d` and $`\mathrm{elim}(d,L)` from $`\sigma` differ.

*21.2.* Drop one premise and show that the conclusion fails, using $`c` and $`\sigma` of §21.2. (a) Theorem 20.2 with $`L=\{y\}` and a state $`\sigma''` with $`\sigma''(x)=0`. (b) Theorem 16.2 with $`C=\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]` started at $`\langle1,[\,],\sigma\rangle`. (c) Theorem 16.2 without $`\sigma\vdash c\Downarrow\sigma'`, for $`W=\mathsf{while\ true\ do\ skip}` and any state $`\sigma'`.

*Further problem.* Suppose no state $`\sigma'` satisfies $`\sigma\vdash c\Downarrow\sigma'`. Use Theorem 6.2 and Session 5, Lemma 5.3 to construct an infinite path from $`\langle c,\sigma\rangle` (A.6). Which direction of Theorem 6.2 do you use?

# Reading for the Seminar
%%%
tag := "ch21-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the four restated theorems in a column. Underline each premise and circle the observation in each conclusion.

*Joint proof · 30 minutes.* The presenter fills the row of Theorem 20.2 for $`c` in seven steps. Three participants compute the runs of §21.2 for Theorems 6.2, 10.2 and 16.2 and fill those rows.

*Proof review · 20 minutes.* Do Exercise 21.2. Then take $`\mathsf{while\ true\ do\ skip}` and say, row by row, what each theorem of the table gives.

*Facilitator’s hint.* Ask two questions of every theorem: what must be checked before it applies, and which part of the final configuration it compares.

# Solutions and Further Reading
%%%
tag := "ch21-s6"
number := false
%%%

*21.1.* Write $`I` for the conditional, $`\sigma_1=\sigma[z\mapsto3]` and $`\sigma_3=\sigma_1[y\mapsto2]`. The guard is false at $`\sigma_1`. The path is $`\langle d,\sigma\rangle\to\langle\mathsf{skip};I,\sigma_1\rangle\to\langle I,\sigma_1\rangle\to\langle y:=2,\sigma_1\rangle\to\langle\mathsf{skip},\sigma_3\rangle`, four edges. The meaning is $`f_d(\sigma)=f_I^\dagger(\sigma_1)=f_I(\sigma_1)=f_{y:=2}(\sigma_1)=\sigma_3`. The code is $`[\mathsf{load}(x),\mathsf{setvar}(z),\mathsf{load}(x),\mathsf{push}(0),\mathsf{ble}(0,3),\mathsf{push}(1),\mathsf{setvar}(y),\mathsf{branch}(2),\mathsf{push}(2),\mathsf{setvar}(y)]`, ten instructions. The $`\mathsf{ble}` at 4 pops $`0` and $`3`, and since $`3\le0` fails it continues at $`4+1+3=8`. Theorem 16.2 gives $`C\vdash\langle0,[\,],\sigma\rangle\to^*\langle10,[\,],\sigma_3\rangle` for every code $`C` with $`\mathrm{at}(C,0,\mathrm{ccom}(d))`. For $`L=\{y\}`, $`\mathrm{live}(I,L)=\mathrm{FV}(x\le0)\cup\varnothing\cup\varnothing=\{x\}`, and $`z\notin\{x\}`, so $`\mathrm{live}(d,L)=\{x\}` and $`\mathrm{elim}(d,L)=(\mathsf{skip};\ I)`. From $`\sigma` it ends in $`\sigma[y\mapsto2]`, with $`0` at $`z`, whereas $`\sigma_3(z)=3`. The final states agree at $`y` and differ at $`z`.

*21.2.* (a) $`\mathrm{elim}(c,\{y\})` runs from $`\sigma''` to $`\sigma'''=\sigma''[y\mapsto1]`, and $`\sigma'''(y)=1\neq5=\sigma'(y)`. By Session 3, Theorem 3.2, $`\sigma'''` is the only final state, so no state satisfies the conclusion. The premise $`\sigma|_{\{x\}}=\sigma''|_{\{x\}}` fails. (b) $`C(1)=\mathsf{push}(1)` gives $`\langle2,[1],\sigma\rangle`. There $`\mathsf{plus}` finds one integer, so the run stops at position 2, which holds no $`\mathsf{halt}`, and never reaches $`1+6=7`. The premise $`\mathrm{at}(C,1,\mathrm{ccom}(c))` fails, because $`\mathrm{ccom}(c)` starts with $`\mathsf{load}(x)`. (c) $`\mathrm{ccom}(W)=[\mathsf{branch}(-1)]`. At $`\mathit{pc}` the branch continues at $`\mathit{pc}+1-1=\mathit{pc}`. Each configuration has at most one transition (B.4), so every path from $`\langle\mathit{pc},S,\sigma\rangle` stays at $`\mathit{pc}` and never reaches $`\mathit{pc}+1`.

*Further problem.* Every configuration $`p` with $`\langle c,\sigma\rangle\to^*p` has a successor. Otherwise Lemma 5.3 gives $`p=\langle\mathsf{skip},\sigma'\rangle` for some $`\sigma'`, and the direction from paths to derivations of Theorem 6.2 gives $`\sigma\vdash c\Downarrow\sigma'`, which was excluded. Put $`f(0)=\langle c,\sigma\rangle` and let $`f(i+1)` be a successor of $`f(i)`. By induction on $`i`, each $`f(i)` is reached from $`\langle c,\sigma\rangle` by a finite path, so the successor exists.

*Further reading.* Nipkow and Klein prove the converse of their compiler theorem as Lemma 8.18 (p. 110) and combine both directions in Theorem 8.19 (p. 111). For their dead-code elimination they prove the converse as Lemma 10.20 (p. 170), and Corollary 10.21 (p. 171) observes every name and obtains equivalence in the sense of Session 7. The compiler chapter of Xavier Leroy’s _Compiler Verification_ course proves that the code of a diverging program diverges. It uses a small-step semantics with continuations and a measure on source configurations that decreases at every source step matched by no machine transition (Session 16, Further Reading). [Concrete Semantics, §8.4](https://concrete-semantics.org/concrete-semantics.pdf#page=120) · [Concrete Semantics, §10.3](https://concrete-semantics.org/concrete-semantics.pdf#page=180) · [Leroy’s course, compiler chapter](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean)

*Further reading · Special lecture S4.* The organizer’s special lecture [S4 (failure and composition)](static/slides/s4/index.html) adds a failing outcome to the state transformers of Session 8 and proves the laws of sequencing for it. These are the failing runs set aside in §21.3.

# Sources and Formalization
%%%
tag := "ch21-notes"
number := false
%%%

No new source. Each theorem keeps the source given in its session. Further Reading cites the converse directions proved by Nipkow and Klein, _Concrete Semantics_, Lemma 8.18 (p. 110) and Lemma 10.20 (p. 170). [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf#page=120)

* *Theorem 6.2.* Restated from Session 6; see [its notes](chapter-06/index.html#ch06-notes).
* *Theorem 10.2.* Restated from Session 10; see [its notes](chapter-10/index.html#ch10-notes).
* *Theorem 16.2.* Restated from Session 16; see [its notes](chapter-16/index.html#ch16-notes).
* *Theorem 20.2.* Restated from Session 20; see [its notes](chapter-20/index.html#ch20-notes).
