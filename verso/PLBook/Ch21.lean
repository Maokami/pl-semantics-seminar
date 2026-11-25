import VersoManual

open Verso.Genre Manual

#doc (Manual) "What the Theorems of Part 1 Say" =>
%%%
tag := "ch21"
file := "chapter-21"
%%%

* *Definitions.* Execution rules and transitions ([A.5–A.6](imp-card/index.html#imp-a5)). Observation ([Session 7, §7.1](chapter-07/index.html#ch07-s1)). Outcomes, strict extension and the meanings $`f_c` ([Session 8, Definitions 8.1–8.4](chapter-08/index.html#ch08-s1); [Session 9, Definition 9.4](chapter-09/index.html#ch09-s2)). Code at a position, machine configurations, $`\mathrm{ccom}` and whole programs ([B.2–B.9](machine-card/index.html#machine-b2)). Abstract stores and $`\gamma` ([Session 17, §17.1](chapter-17/index.html#ch17-s1)) and constant propagation $`\mathrm{cp}` ([Session 18, §18.2](chapter-18/index.html#ch18-s2)). The liveness transfer $`\mathrm{live}(c,L)` ([Session 19, Definitions 19.2–19.3](chapter-19/index.html#ch19-s1)), agreement $`s|_X=u|_X` and $`\mathrm{elim}(c,L)` ([Session 20, §20.1](chapter-20/index.html#ch20-s1)). Progress ([Session 5, Lemma 5.3](chapter-05/index.html#ch05-s2)).
* *New terms.* None. [Glossary and label key](glossary/index.html)
* *Theorems.* No new theorem. §21.1 restates [Session 6, Theorem 6.2](chapter-06/index.html#ch06-s2), [Session 10, Theorem 10.2](chapter-10/index.html#ch10-s1), [Session 16, Theorem 16.2](chapter-16/index.html#ch16-s2) and [Session 20, Theorem 20.2](chapter-20/index.html#ch20-s2) with every premise, and names the observation each one preserves or equates.
* *Source.* No new source. Each theorem keeps the source given in its session. Further Reading cites the converse directions proved by Nipkow and Klein, _Concrete Semantics_, Lemma 8.18 (p. 110) and Lemma 10.20 (p. 170). [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf#page=120)
* *Board case.* Fill the row of Theorem 20.2 for $`c=(y:=x+1;\ x:=0)` and the observed set $`\{y\}`: compute the live sets and $`\mathrm{elim}(c,\{y\})`, check both premises, run the transformed command, and name what the conclusion compares and what it leaves out. Seven steps (§21.2).
* *Proof outline.* No induction. Each theorem is applied in three moves: instantiate its quantifiers, check its premises, read off its conclusion. The runs of the example are computed with the rules of A.5, A.6 and B.4.
* *From Session 20.* Session 20 proved that removing dead assignments keeps the final values of the observed names. That is the last correctness theorem of Part 1. Here it is set beside the theorems of Sessions 6, 10 and 16.

Run `y := x + 1; x := 0` from a store with $`x=4`. Four theorems of Part 1 speak about this run. Session 6 gives it a path of transitions that ends at skip. Session 10 gives it a meaning that is a store. Session 16 runs its compiled code to the end of the block. Session 20 deletes its second assignment and keeps the final value of $`y`. Quoted in one line, each says that two things agree. Each compares a different part of the result, and each needs premises that are easy to drop. This session writes the premises back and runs the program through all four theorems.

# Four theorems and their premises
%%%
tag := "ch21-s1"
%%%

[Session 7, §7.1](chapter-07/index.html#ch07-s1) calls what a notion of equivalence compares about a run its *observation*. Program equivalence (Definition 7.1) observes the whole final store. We use the word in the same sense for each theorem below. The four theorems are restated with all their quantifiers. Two paragraphs then name their observations and their premises.

*Theorem 6.2 (Equivalence of terminating evaluations), restated \[Checked\].* For every command $`c` and stores $`s,t`, $`s\vdash c\Downarrow t` if and only if $`\langle c,s\rangle\to^*\langle\mathsf{skip},t\rangle`.

*Theorem 10.2 (Correspondence), restated \[This book\] \[Checked\].* For every command $`c` and stores $`s,t\in\Sigma`, $`s\vdash c\Downarrow t` if and only if $`f_c(s)=t`.

*Theorem 16.2 (Compiled commands meet the contract), restated \[Externally checked: Leroy course, [machine-card references](machine-card/index.html#machine-sources)\].* For every command $`c` and stores $`s,t`, if $`s\vdash c\Downarrow t`, then for every code $`C`, position $`\mathit{pc}` and stack $`S` with $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))`, $`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|\mathrm{ccom}(c)|,S,t\rangle`.

*Theorem 20.2 (Correctness of dead-assignment elimination), restated \[Externally checked: Leroy course, [IMP card references](imp-card/index.html#imp-sources)\].* For every command $`c`, finite set of names $`L` and stores $`s,t,u`: if $`s\vdash c\Downarrow t` and $`s|_{\mathrm{live}(c,L)}=u|_{\mathrm{live}(c,L)}`, then some store $`v` satisfies $`u\vdash\mathrm{elim}(c,L)\Downarrow v` and $`t|_L=v|_L`.

*Observations.* Theorem 6.2 equates final stores: the store at the root of a derivation is the store beside skip at the end of a path. Theorem 10.2 equates the final store with the normal result of the meaning, that is, the outcome $`f_c(s)` when it is a store. Theorem 16.2 preserves the final store and observes two more things: the run of the code reaches the position just after the block, and the stack there is the $`S` it started with. Theorem 20.2 preserves only the final values of the names in $`L`.

*Premises.* Theorem 6.2 has none besides its quantifiers. Theorem 10.2 hides two in its notation. The final $`t` is a store, never $`\bot`. The meaning $`f_W` of a loop is the least fixed point of its unfolding operator (Session 9, Definition 9.4 and Theorem 9.5); with another fixed point the direction from meanings to derivations fails ([Session 10, §10.4](chapter-10/index.html#ch10-s4)). Session 10, Corollary 10.3 adds that $`f_c(s)=\bot` exactly when no store $`t` satisfies $`s\vdash c\Downarrow t`. Theorem 16.2 needs a terminating source execution and the code at $`\mathit{pc}`. [Session 16, Corollary 16.3](chapter-16/index.html#ch16-s4) takes $`C=\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]`, $`\mathit{pc}=0` and $`S=[\,]`: the whole program terminates with final store $`t` (B.9). Theorem 20.2 needs a terminating run of the original command and agreement of the two initial stores on the live set. Its external check assumes one axiom about finite sets ([Session 20, §20.2](chapter-20/index.html#ch20-s2)), which the paper proof does not need.

The table adds [Session 18, Theorem 18.4](chapter-18/index.html#ch18-s3): if $`s\in\gamma(A)` and $`s\vdash c\Downarrow t`, then $`s\vdash\mathrm{cp}(A,c)\Downarrow t`. Theorems 16.2, 18.4 and 20.2 share the premise $`s\vdash c\Downarrow t`.

:::table +header
*
  * Theorem
  * Premises
  * Observed
  * Not said
*
  * Theorem 6.2
  * The quantifiers only.
  * The final store, at the root of a derivation and beside skip at the end of a path.
  * The length of the path or the height of the derivation. Intermediate configurations. An infinite path when no derivation exists.
*
  * Theorem 10.2
  * $`t` is a store. $`f_W` is the least fixed point.
  * The outcome $`f_c(s)` when it is a store.
  * Intermediate stores and numbers of steps. By Corollary 10.3, $`f_c(s)=\bot` says only that no terminating execution exists.
*
  * Theorem 16.2
  * $`s\vdash c\Downarrow t`. $`\mathrm{at}(C,\mathit{pc},\mathrm{ccom}(c))`.
  * The configuration $`\langle\mathit{pc}+|\mathrm{ccom}(c)|,S,t\rangle`: end position, same stack, final store.
  * Nonterminating source programs. Failing source programs. A source run from a machine run. Configurations inside the block.
*
  * Theorem 18.4
  * $`s\in\gamma(A)`. $`s\vdash c\Downarrow t`.
  * The whole final store of $`\mathrm{cp}(A,c)` from $`s`.
  * Nonterminating source programs. Failing source programs. Stores outside $`\gamma(A)`. A run of $`c` from a run of $`\mathrm{cp}(A,c)`.
*
  * Theorem 20.2
  * $`s\vdash c\Downarrow t`. $`s|_{\mathrm{live}(c,L)}=u|_{\mathrm{live}(c,L)}`.
  * The final values of the names in $`L`.
  * Names outside $`L`. Nonterminating source programs. Failing source programs. A run of $`c` from a run of $`\mathrm{elim}(c,L)`.
:::

# One program through four theorems
%%%
tag := "ch21-s2"
%%%

Let $`x,y` be distinct names, let $`c=(y:=x+1;\ x:=0)`, and let $`s` be a store with $`s(x)=4`. Put $`s_1=s[y\mapsto5]` and $`t=s_1[x\mapsto0]`. The assignment rule gives $`s\vdash y:=x+1\Downarrow s_1` and $`s_1\vdash x:=0\Downarrow t`. The sequence rule joins them into a derivation $`D:s\vdash c\Downarrow t` of height one.

*Theorem 6.2.* $`D` gives the left side. The rules of A.6 (the lifted assignment, discarding skip, the assignment) give the right side, $`\langle c,s\rangle\to\langle\mathsf{skip};x:=0,\ s_1\rangle\to\langle x:=0,\ s_1\rangle\to\langle\mathsf{skip},t\rangle`. The path has three edges, and $`D` has height one. The theorem compares only the final store $`t`.

*Theorem 10.2.* Definitions 8.3 and 8.4 give $`f_c(s)=f_{x:=0}^\dagger(f_{y:=x+1}(s))=f_{x:=0}^\dagger(s_1)=f_{x:=0}(s_1)=t`. The outcome is the store $`t`, as the theorem requires.

*Theorem 16.2.* By B.6 and B.8, $`\mathrm{ccom}(c)=[\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus},\mathsf{setvar}(y),\mathsf{push}(0),\mathsf{setvar}(x)]` has six instructions. Take $`C=\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]`, $`\mathit{pc}=0` and $`S=[\,]`. The rules of B.4 give $`C\vdash\langle0,[\,],s\rangle\to\langle1,[4],s\rangle\to\langle2,[1,4],s\rangle\to\langle3,[5],s\rangle\to\langle4,[\,],s_1\rangle\to\langle5,[0],s_1\rangle\to\langle6,[\,],t\rangle`, and $`C(6)=\mathsf{halt}`. The theorem predicts only the last configuration: position $`0+6`, stack $`[\,]`, store $`t`. The stacks $`[4]`, $`[1,4]`, $`[5]` and $`[0]` inside the run are not observed. Placed at any position $`\mathit{pc}` of any code and started with any stack $`S`, the same block goes from $`\langle\mathit{pc},S,s\rangle` to $`\langle\mathit{pc}+6,S,t\rangle`.

*Theorem 20.2 (board case).* We must fill the row of Theorem 20.2 for $`c` and $`L=\{y\}`.

1. Compute the live sets from the end (Definition 19.2). Since $`x\notin\{y\}`, $`\mathrm{live}(x:=0,\{y\})=\{y\}`. Since $`y\in\{y\}`, $`\mathrm{live}(y:=x+1,\{y\})=(\{y\}\smallsetminus\{y\})\cup\mathrm{FV}(x+1)=\{x\}`. The sequence clause gives $`\mathrm{live}(c,\{y\})=\mathrm{live}(y:=x+1,\mathrm{live}(x:=0,\{y\}))=\{x\}`.
2. Definition 20.1 gives $`\mathrm{elim}(c,\{y\})=\mathrm{elim}(y:=x+1,\{y\});\ \mathrm{elim}(x:=0,\{y\})=(y:=x+1;\ \mathsf{skip})`. The assignment $`x:=0` is dead.
3. First premise: $`D` derives $`s\vdash c\Downarrow t`.
4. Second premise: take $`u` with $`u(x)=4` and $`u(y)=100`. Then $`s|_{\{x\}}=u|_{\{x\}}`. The premise asks nothing about $`y`.
5. Conclusion: the theorem gives a store $`v` with $`u\vdash\mathrm{elim}(c,\{y\})\Downarrow v` and $`t|_{\{y\}}=v|_{\{y\}}`. The assignment, skip and sequence rules give $`v=u[y\mapsto5]`, and indeed $`t(y)=5=v(y)`.
6. What it leaves out: $`t(x)=0` and $`v(x)=u(x)=4`, so the final stores differ at $`x`. With $`u=s` they still differ at $`x`, since then $`v=s_1\neq t`. The theorem cannot conclude $`v=t`.
7. The row: the premises are $`s\vdash c\Downarrow t` and $`s(x)=u(x)`. The observation is the final value of $`y`. Not said: the final value of $`x`.

One run, four observations. Theorems 6.2 and 10.2 observe the final store $`t`. Theorem 16.2 observes $`t` with the end position and the unchanged stack. Theorem 20.2 observes only $`t(y)`. Theorem 18.4 observes the whole final store, as Definition 7.1 does. With $`A=\{x\mapsto4\}` we have $`s\in\gamma(A)` and $`\mathrm{cp}(A,c)=(y:=5;\ x:=0)`, and the theorem gives $`s\vdash(y:=5;\ x:=0)\Downarrow t`.

# What the theorems do not say
%%%
tag := "ch21-s3"
%%%

*Nonterminating source programs.* Let $`W=\mathsf{while\ true\ do\ skip}`. It has no terminating execution ([Session 2, §2.4](chapter-02/index.html#ch02-s4)). Theorems 16.2, 18.4 and 20.2 start from a derivation $`s\vdash c\Downarrow t`, so for $`W` they say nothing about $`\mathrm{ccom}(W)`, $`\mathrm{cp}(A,W)` or $`\mathrm{elim}(W,L)`. The code $`\mathrm{ccom}(W)=[\mathsf{branch}(-1)]` does run forever ([Session 16, §16.4](chapter-16/index.html#ch16-s4)), but that is a computation for one program, not a consequence of Theorem 16.2. Theorems 6.2 and 10.2 are equivalences, so they do say something: no path from $`\langle W,s\rangle` reaches skip, and $`f_W(s)=\bot` by Corollary 10.3. Neither builds the infinite path of [Session 5, Example 5.5](chapter-05/index.html#ch05-s3) by itself (Further problem).

*Failing source programs.* A run fails when it reaches a configuration other than skip with no transition. By Session 5, Lemma 5.3, IMP has no failing run, so for the language of Part 1 the question does not arise. Add an operation that can fail, such as division by zero. A failing run has no derivation, and Theorems 16.2, 18.4 and 20.2 again say nothing about it. The target may then behave differently. Deleting a dead assignment whose expression fails turns a failing run into a terminating one ([Session 20, Solution 20.4](chapter-20/index.html#ch20-s6)). The compiled code of a failing program may go wrong or end with any store (Session 16, §16.4).

*The converse.* Theorems 16.2, 18.4 and 20.2 turn a run of the source into a run of the target. None of them turns a run of the target into a run of the source.

# Exercises
%%%
tag := "ch21-s4"
number := false
%%%

*21.1.* Let $`d=(z:=x;\ \mathsf{if}\ x\le0\ \mathsf{then}\ y:=1\ \mathsf{else}\ y:=2)` and let $`s(x)=3`, with $`0` at every other name. Fill the four rows for $`d`: the path of Theorem 6.2 and its length; $`f_d(s)`; $`\mathrm{ccom}(d)` and the final configuration that Theorem 16.2 gives at $`\mathit{pc}=0` and $`S=[\,]`; and, for $`L=\{y\}`, $`\mathrm{live}(d,L)`, $`\mathrm{elim}(d,L)` and the name at which the final stores of $`d` and $`\mathrm{elim}(d,L)` from $`s` differ.

*21.2.* Drop one premise and show that the conclusion fails, using $`c` and $`s` of §21.2. (a) Theorem 20.2 with $`L=\{y\}` and a store $`u` with $`u(x)=0`. (b) Theorem 16.2 with $`C=\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]` started at $`\langle1,[\,],s\rangle`. (c) Theorem 16.2 without $`s\vdash c\Downarrow t`, for $`W=\mathsf{while\ true\ do\ skip}` and any store $`t`.

*Further problem.* Suppose no store $`t` satisfies $`s\vdash c\Downarrow t`. Use Theorem 6.2 and Session 5, Lemma 5.3 to construct an infinite path from $`\langle c,s\rangle` (A.6). Which direction of Theorem 6.2 do you use?

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

*21.1.* Write $`I` for the conditional, $`s_1=s[z\mapsto3]` and $`t'=s_1[y\mapsto2]`. The guard is false at $`s_1`. The path is $`\langle d,s\rangle\to\langle\mathsf{skip};I,s_1\rangle\to\langle I,s_1\rangle\to\langle y:=2,s_1\rangle\to\langle\mathsf{skip},t'\rangle`, four edges. The meaning is $`f_d(s)=f_I^\dagger(s_1)=f_I(s_1)=f_{y:=2}(s_1)=t'`. The code is $`[\mathsf{load}(x),\mathsf{setvar}(z),\mathsf{load}(x),\mathsf{push}(0),\mathsf{ble}(0,3),\mathsf{push}(1),\mathsf{setvar}(y),\mathsf{branch}(2),\mathsf{push}(2),\mathsf{setvar}(y)]`, ten instructions. The $`\mathsf{ble}` at 4 pops $`0` and $`3`, and since $`3\le0` fails it continues at $`4+1+3=8`. Theorem 16.2 gives $`C\vdash\langle0,[\,],s\rangle\to^*\langle10,[\,],t'\rangle` for every code $`C` with $`\mathrm{at}(C,0,\mathrm{ccom}(d))`. For $`L=\{y\}`, $`\mathrm{live}(I,L)=\mathrm{FV}(x\le0)\cup\varnothing\cup\varnothing=\{x\}`, and $`z\notin\{x\}`, so $`\mathrm{live}(d,L)=\{x\}` and $`\mathrm{elim}(d,L)=(\mathsf{skip};\ I)`. From $`s` it ends in $`s[y\mapsto2]`, with $`0` at $`z`, whereas $`t'(z)=3`. The final stores agree at $`y` and differ at $`z`.

*21.2.* (a) $`\mathrm{elim}(c,\{y\})` runs from $`u` to $`v=u[y\mapsto1]`, and $`v(y)=1\neq5=t(y)`. By Session 3, Theorem 3.2, $`v` is the only final store, so no store satisfies the conclusion. The premise $`s|_{\{x\}}=u|_{\{x\}}` fails. (b) $`C(1)=\mathsf{push}(1)` gives $`\langle2,[1],s\rangle`. There $`\mathsf{plus}` finds one integer, so the run stops at position 2, which holds no $`\mathsf{halt}`, and never reaches $`1+6=7`. The premise $`\mathrm{at}(C,1,\mathrm{ccom}(c))` fails, because $`\mathrm{ccom}(c)` starts with $`\mathsf{load}(x)`. (c) $`\mathrm{ccom}(W)=[\mathsf{branch}(-1)]`. At $`\mathit{pc}` the branch continues at $`\mathit{pc}+1-1=\mathit{pc}`. Each configuration has at most one transition (B.4), so every path from $`\langle\mathit{pc},S,s\rangle` stays at $`\mathit{pc}` and never reaches $`\mathit{pc}+1`.

*Further problem.* Every configuration $`p` with $`\langle c,s\rangle\to^*p` has a successor. Otherwise Lemma 5.3 gives $`p=\langle\mathsf{skip},t\rangle` for some $`t`, and the direction from paths to derivations of Theorem 6.2 gives $`s\vdash c\Downarrow t`, which was excluded. Put $`f(0)=\langle c,s\rangle` and let $`f(i+1)` be a successor of $`f(i)`. By induction on $`i`, each $`f(i)` is reached from $`\langle c,s\rangle` by a finite path, so the successor exists.

*Further reading.* Nipkow and Klein prove the converse of their compiler theorem as Lemma 8.18 (p. 110) and combine both directions in Theorem 8.19 (p. 111). For their dead-code elimination they prove the converse as Lemma 10.20 (p. 170), and Corollary 10.21 (p. 171) observes every name and obtains equivalence in the sense of Session 7. The compiler chapter of Xavier Leroy’s _Compiler Verification_ course proves that the code of a diverging program diverges. It uses a small-step semantics with continuations and a measure on source configurations that decreases at every source step matched by no machine transition (Session 16, Further Reading). [Concrete Semantics, §8.4](https://concrete-semantics.org/concrete-semantics.pdf#page=120) · [Concrete Semantics, §10.3](https://concrete-semantics.org/concrete-semantics.pdf#page=180) · [Leroy’s course, compiler chapter](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean)
