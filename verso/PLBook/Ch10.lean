import VersoManual
import PLBook.IMP.Correspondence

open Verso.Genre Manual

#doc (Manual) "Correspondence of Command Semantics" =>
%%%
tag := "ch10"
file := "chapter-10"
%%%

Take $`\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1` and a state with $`x=0`. The rules of Session 2 derive a final state with $`x=2`. The meaning computed in Session 9 returns the same state, first at stage 3. This session connects the operational and denotational semantics of IMP. Given an initial state $`\sigma`, the meaning of a command returns a final state $`\sigma'` exactly when the execution rules derive a run from $`\sigma` to $`\sigma'`. The intermediate state in sequencing is where they meet. For a loop the bridge is the number of finite unfoldings needed by an execution.

*In this session.*

* *Definitions.* The execution rules ([Session 2, Definition 2.1](chapter-02/index.html#ch02-s2); [A.5](imp-card/index.html#imp-a5)). Partial function and graph ([Session 3, §3.3](chapter-03/index.html#ch03-s3)). The set $`\mathrm{Exec}(c)` of initial–final state pairs ([Session 7, Definition 7.1](chapter-07/index.html#ch07-s1)). Outcomes $`\Sigma_\bot`, state transformers, strict extension $`h^\dagger` and the meanings $`f_c` ([Session 8, Definitions 8.1–8.4](chapter-08/index.html#ch08-s1)). The information order and increasing sequences of outcomes ([Session 8, Definition 8.7 and Lemma 8.10](chapter-08/index.html#ch08-s4)). The unfolding operator $`F`, the approximations $`w_n` and the loop meaning $`f_W` ([Session 9, Definitions 9.1 and 9.4](chapter-09/index.html#ch09-s1)), the increasing approximations ([Session 9, Lemma 9.3](chapter-09/index.html#ch09-s2)), and the least fixed-point theorem ([Session 9, Theorem 9.5](chapter-09/index.html#ch09-s3)).
* *New terms.* Relational composition, nested induction. [Glossary](glossary/index.html)
* *Theorem 10.2 (Correspondence).* For every command $`c` and states $`\sigma,\sigma'`, $`\sigma\vdash c\Downarrow\sigma'` if and only if $`f_c(\sigma)=\sigma'`.
* *Board case.* From a derivation to a meaning, loop iteration. Apply one induction hypothesis to the body and one to the loop from the intermediate state $`\sigma_1`, and join them with the fixed-point equation of Session 9, Theorem 9.5(a).
* *Proof outline.* From derivations to meanings: induction on the derivation $`D:\sigma\vdash c\Downarrow\sigma'` with $`P(D)\coloneqq f_c(\sigma)=\sigma'`. From meanings to derivations: structural induction on $`c` with $`Q(c)\coloneqq\forall\sigma,\sigma'\in\Sigma,\ f_c(\sigma)=\sigma'\Rightarrow\sigma\vdash c\Downarrow\sigma'`. In the loop case a nested induction on the stage $`n` proves $`Q_W(n)\coloneqq\forall\sigma,\sigma'\in\Sigma,\ w_n(\sigma)=\sigma'\Rightarrow\sigma\vdash W\Downarrow\sigma'`.
* *From Session 9.* Session 9 defined the loop meaning $`f_W` as the least upper bound of the approximations $`w_n` and proved that it is the least fixed point of $`F`. The direction from derivations to meanings uses only the fixed-point equation $`f_W=F(f_W)`. The other direction uses the approximations themselves, and this is where leastness matters.

# Two accounts of one loop
%%%
tag := "ch10-s1"
%%%

Write $`W=\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1`. Let $`\sigma(x)=0`, and put $`\sigma_1=\sigma[x\mapsto1]` and $`\sigma'=\sigma_1[x\mapsto2]`. By [A.4](imp-card/index.html#imp-a4) the guard $`x<2` abbreviates $`\neg(2\le x)`. It is true in $`\sigma` and $`\sigma_1` and false in $`\sigma'`. Reading upwards from the root, the derivation $`D` of $`\sigma\vdash W\Downarrow\sigma'` contains three loop judgments.

1. $`\sigma\vdash W\Downarrow\sigma'` by the loop iteration rule, with body premise $`\sigma\vdash x:=x+1\Downarrow\sigma_1`.
2. $`\sigma_1\vdash W\Downarrow\sigma'` by the loop iteration rule, with body premise $`\sigma_1\vdash x:=x+1\Downarrow\sigma'`.
3. $`\sigma'\vdash W\Downarrow\sigma'` by the loop exit rule.

Session 9 computes the meaning of the same loop through the approximations of Definition 9.1. The approximation $`w_0` gives $`\bot` at every state, $`w_{n+1}=F(w_n)`, and $`n` is the stage of $`w_n`. At the three states of the run,

$$`w_1(\sigma')=\sigma',\qquad w_2(\sigma_1)=w_1(\sigma')=\sigma',\qquad w_3(\sigma)=w_2(\sigma_1)=\sigma'.`

Hence $`f_W(\sigma)=\sigma'`, as in the table of Session 9, §9.1. The exit at $`\sigma'` matches the first stage at which $`\sigma'` returns. Each iteration rule matches one more stage.

A state transformer $`g:\Sigma\to\Sigma_\bot` carries the same information as the partial function on states that is undefined at $`\sigma` exactly when $`g(\sigma)=\bot` ([Session 8, §8.1](chapter-08/index.html#ch08-s1)). Its graph, in the sense of Session 3, is therefore

$$`\mathrm{graph}(g)=\{(\sigma,\sigma')\in\Sigma\times\Sigma\mid g(\sigma)=\sigma'\}.`

For a command $`c`, [Session 7, Definition 7.1](chapter-07/index.html#ch07-s1) writes $`\mathrm{Exec}(c)=\{(\sigma,\sigma')\mid\sigma\vdash c\Downarrow\sigma'\}` for its set of initial–final state pairs. In the example the pairs $`(\sigma,\sigma')`, $`(\sigma_1,\sigma')` and $`(\sigma',\sigma')` belong to both $`\mathrm{graph}(f_W)` and $`\mathrm{Exec}(W)`.

Both directions of the main theorem use one calculation with strict extension. Let $`x\ne y`, let $`c_1` be $`x:=1` and let $`c_2` be $`y:=x+1`. Definition 8.4 gives $`f_{c_1;c_2}(\sigma)=f_{c_2}^\dagger(f_{c_1}(\sigma))`. Here $`f_{c_1}(\sigma)=\sigma[x\mapsto1]=\sigma_1` is a state. Strict extension passes $`\sigma_1` to $`f_{c_2}`, and the result is $`\sigma_1[y\mapsto2]`. If the prefix were $`\mathsf{while\ true\ do\ skip}`, its meaning would give $`\bot` at every state (§10.4). The strict extension would return $`\bot`, and no state would lie in the middle.

*Lemma 10.1 (Intermediate state).* For state transformers $`g,h` and states $`\sigma,\sigma'`,

$$`h^\dagger(g(\sigma))=\sigma'\quad\Longleftrightarrow\quad\exists\sigma_1\in\Sigma,\ \ g(\sigma)=\sigma_1\ \land\ h(\sigma_1)=\sigma'.`

*Proof.* Split on the outcome $`g(\sigma)`. If $`g(\sigma)=\bot`, the left side reads $`\bot=\sigma'`, which is false because $`\bot` is not a state. The right side is false because $`g(\sigma)` is not a state. If $`g(\sigma)=\sigma''` for a state $`\sigma''`, the left side reads $`h(\sigma'')=\sigma'`. Then the right side holds with $`\sigma_1=\sigma''`. Conversely, any witness satisfies $`\sigma_1=g(\sigma)=\sigma''`, so $`h(\sigma'')=\sigma'`. $`\square`

In terms of graphs, $`(\sigma,\sigma')\in\mathrm{graph}(h^\dagger\circ g)` exactly when some state $`\sigma_1` has $`(\sigma,\sigma_1)\in\mathrm{graph}(g)` and $`(\sigma_1,\sigma')\in\mathrm{graph}(h)`. The set of pairs joined in this way is the *relational composition* of the two graphs. A relation can in general offer several intermediate states. Here the only candidate is the outcome $`g(\sigma)`, because the first computation is represented by a function.

*Theorem 10.2 (Correspondence).* For every command $`c` and states $`\sigma,\sigma'\in\Sigma`,

$$`\sigma\vdash c\Downarrow\sigma'\quad\Longleftrightarrow\quad f_c(\sigma)=\sigma'.`

Here $`\sigma'` is a state, never $`\bot`. Equivalently, $`\mathrm{graph}(f_c)=\mathrm{Exec}(c)`. The two directions are proved separately, by different inductions.

* *From derivations to meanings* (§10.2). Assume a derivation $`D` of $`\sigma\vdash c\Downarrow\sigma'`. Conclude $`f_c(\sigma)=\sigma'`. The proof is by induction on $`D`.
* *From meanings to derivations* (§10.3). Assume $`f_c(\sigma)=\sigma'`. Construct a derivation of $`\sigma\vdash c\Downarrow\sigma'`. The proof is by structural induction on $`c`, with a nested induction on the stage in the loop case.

# From derivations to meanings
%%%
tag := "ch10-s2"
%%%

We prove $`P(D)` for every derivation $`D:\sigma\vdash c\Downarrow\sigma'` by induction on $`D`, as in Session 3. The induction property is

$$`P(D)\quad\coloneqq\quad f_c(\sigma)=\sigma'.`

Read $`\sigma,c,\sigma'` from the conclusion of $`D`. Nothing is quantified inside $`P(D)`. Each premise fixes its own states, and each hypothesis is used at exactly those states.

For a loop $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`, Definition 9.1 builds the unfolding operator $`F` from the guard $`b` and the body meaning $`f_{c_1}`. For a state transformer $`h`,

$$`\begin{aligned}
F(h)(\sigma)&=h^\dagger(f_{c_1}(\sigma)) && \text{if } B(b,\sigma)=\mathsf{true},\\
F(h)(\sigma)&=\sigma && \text{if } B(b,\sigma)=\mathsf{false}.
\end{aligned}`

Theorem 9.5(a) states that the loop meaning is a fixed point:

$$`f_W=F(f_W).`

This direction uses only this equation.

*Skip and assignment.* $`D` is an axiom. Its conclusion is $`\sigma\vdash\mathsf{skip}\Downarrow\sigma` or $`\sigma\vdash x:=e\Downarrow\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. Definition 8.4 assigns the same state as the meaning at $`\sigma`.

*Sequence.* Suppose $`c=c_1;c_2`. The premises of $`D` are $`D_1:\sigma\vdash c_1\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash c_2\Downarrow\sigma'`. The induction hypotheses are $`P(D_1):f_{c_1}(\sigma)=\sigma_1` and $`P(D_2):f_{c_2}(\sigma_1)=\sigma'`. Lemma 10.1, read from right to left with the witness $`\sigma_1`, gives $`f_{c_2}^\dagger(f_{c_1}(\sigma))=\sigma'`. By Definition 8.4 the left side is $`f_{c_1;c_2}(\sigma)`.

*Conditional.* For $`I=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`, let $`k` be the command selected by $`B(b,\sigma)`. The premise of $`D` is $`D_1:\sigma\vdash k\Downarrow\sigma'`, with $`P(D_1):f_k(\sigma)=\sigma'`. Definition 8.4 gives $`f_I(\sigma)=f_k(\sigma)`, so $`f_I(\sigma)=\sigma'`.

*Loop exit.* If $`D` ends by the loop exit rule, then $`B(b,\sigma)=\mathsf{false}` and $`\sigma'=\sigma`. The fixed-point equation gives $`f_W(\sigma)=F(f_W)(\sigma)=\sigma`.

*Loop iteration (board case).* Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`. We must show $`f_W(\sigma)=\sigma'`. Suppose $`D` ends with the loop iteration rule. Its side condition is $`B(b,\sigma)=\mathsf{true}`. Its premises are $`D_1:\sigma\vdash c_1\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash W\Downarrow\sigma'`. The induction hypotheses are

$$`\begin{aligned}
P(D_1)&:\quad f_{c_1}(\sigma)=\sigma_1,\\
P(D_2)&:\quad f_W(\sigma_1)=\sigma'.
\end{aligned}`

1. By the fixed-point equation (Theorem 9.5(a)), $`f_W(\sigma)=F(f_W)(\sigma)`.
2. The side condition gives $`B(b,\sigma)=\mathsf{true}`. So the true-guard clause of $`F` applies: $`F(f_W)(\sigma)=f_W^\dagger(f_{c_1}(\sigma))`.
3. Rewrite the body outcome with $`P(D_1)`, that is, $`f_{c_1}(\sigma)=\sigma_1`. Hence $`f_W^\dagger(f_{c_1}(\sigma))=f_W^\dagger(\sigma_1)`.
4. Since $`\sigma_1` is a state, the strict extension applies $`f_W` to it: $`f_W^\dagger(\sigma_1)=f_W(\sigma_1)`.
5. Rewrite the loop outcome at $`\sigma_1` with $`P(D_2)`, that is, $`f_W(\sigma_1)=\sigma'`.
6. Chain steps 1–5: $`f_W(\sigma)=F(f_W)(\sigma)=f_W^\dagger(\sigma_1)=f_W(\sigma_1)=\sigma'`.

Steps 3–5 are Lemma 10.1 read from right to left with the witness $`\sigma_1`. The derivation $`D_2` concerns the very same command $`W`. Induction on command syntax would supply no hypothesis for it. Induction on derivations does, because $`D_2` is a proper subderivation of $`D`. This proves $`P(D)` for every derivation $`D`.

# From meanings to derivations
%%%
tag := "ch10-s3"
%%%

Now assume $`f_c(\sigma)=\sigma'` for a state $`\sigma'`. We must construct a derivation of $`\sigma\vdash c\Downarrow\sigma'`. There is no derivation to induct on yet. We use structural induction on $`c` with the induction property

$$`Q(c)\quad\coloneqq\quad\forall\sigma,\sigma'\in\Sigma,\ \ f_c(\sigma)=\sigma'\ \Longrightarrow\ \sigma\vdash c\Downarrow\sigma'.`

The states are quantified inside $`Q(c)`. In the sequence case the hypothesis for the second command is needed at the intermediate state, not at $`\sigma`.

*Skip and assignment.* Since $`f_{\mathsf{skip}}(\sigma)=\sigma`, we have $`\sigma'=\sigma`, and the skip rule applies. For $`x:=e`, we have $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`, and the assignment rule applies.

*Sequence.* Suppose $`c=c_1;c_2`. The induction hypotheses are

$$`\begin{aligned}
Q(c_1)&:\quad\forall\sigma,\sigma'\in\Sigma,\ f_{c_1}(\sigma)=\sigma'\Rightarrow\sigma\vdash c_1\Downarrow\sigma',\\
Q(c_2)&:\quad\forall\sigma,\sigma'\in\Sigma,\ f_{c_2}(\sigma)=\sigma'\Rightarrow\sigma\vdash c_2\Downarrow\sigma'.
\end{aligned}`

1. By Definition 8.4, the assumption reads $`f_{c_2}^\dagger(f_{c_1}(\sigma))=\sigma'`.
2. Lemma 10.1, read from left to right, gives a state $`\sigma_1` with $`f_{c_1}(\sigma)=\sigma_1` and $`f_{c_2}(\sigma_1)=\sigma'`.
3. Apply $`Q(c_1)` to the pair $`(\sigma,\sigma_1)`. This gives $`\sigma\vdash c_1\Downarrow\sigma_1`.
4. Apply $`Q(c_2)` to the pair $`(\sigma_1,\sigma')`. This gives $`\sigma_1\vdash c_2\Downarrow\sigma'`.
5. The sequence rule joins the two derivations into $`\sigma\vdash c_1;c_2\Downarrow\sigma'`.

*Conditional.* The selected command $`k` is $`c_1` or $`c_2`, an immediate part of $`I`. From $`f_I(\sigma)=f_k(\sigma)=\sigma'`, apply $`Q(k)` to $`(\sigma,\sigma')` to obtain $`\sigma\vdash k\Downarrow\sigma'`. The conditional rule gives $`\sigma\vdash I\Downarrow\sigma'`.

*Loop.* Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`. The structural induction hypothesis $`Q(c_1)` gives the correspondence for the body on all states. It supplies no hypothesis for the loop itself. We therefore carry out a second induction, on the stage of the approximations, inside this case. An induction carried out inside one case of another induction, with the outer hypotheses still available, is a *nested induction*.

First reduce to a finite stage. The outcomes $`w_0(\sigma)\sqsubseteq w_1(\sigma)\sqsubseteq\cdots` increase (Lemma 9.3), and $`f_W(\sigma)` is their least upper bound (Definition 9.4). By Lemma 8.10 such a sequence either stays at $`\bot` or reaches a state and stays there. Since $`f_W(\sigma)=\sigma'`, some stage $`n` has $`w_n(\sigma)=\sigma'`.

Next prove $`Q_W(n)` for every natural number $`n` by induction on $`n`, where

$$`Q_W(n)\quad\coloneqq\quad\forall\sigma,\sigma'\in\Sigma,\ \ w_n(\sigma)=\sigma'\ \Longrightarrow\ \sigma\vdash W\Downarrow\sigma'.`

*Stage zero.* $`w_0(\sigma)=\bot`, which is never a state. There is nothing to prove.

*Successor stage.* Assume $`Q_W(n)` and $`w_{n+1}(\sigma)=\sigma'`. By definition $`w_{n+1}(\sigma)=F(w_n)(\sigma)`.

* If $`B(b,\sigma)=\mathsf{false}`, then $`F(w_n)(\sigma)=\sigma`, so $`\sigma'=\sigma`. The loop exit rule gives $`\sigma\vdash W\Downarrow\sigma`.
* If $`B(b,\sigma)=\mathsf{true}`, then $`w_n^\dagger(f_{c_1}(\sigma))=\sigma'`. Lemma 10.1 gives a state $`\sigma_1` with $`f_{c_1}(\sigma)=\sigma_1` and $`w_n(\sigma_1)=\sigma'`. Apply $`Q(c_1)` to $`(\sigma,\sigma_1)` to obtain $`\sigma\vdash c_1\Downarrow\sigma_1`. Apply $`Q_W(n)` to $`(\sigma_1,\sigma')` to obtain $`\sigma_1\vdash W\Downarrow\sigma'`. The loop iteration rule gives $`\sigma\vdash W\Downarrow\sigma'`.

Finally apply $`Q_W(n)`, for the stage $`n` found first, to the pair $`(\sigma,\sigma')`. The body hypothesis comes from a smaller command. The loop hypothesis comes from a smaller stage. Each direction constructs the witness that its target definition demands. This completes the proof of Theorem 10.2. $`\square`

# Scope of the theorem
%%%
tag := "ch10-s4"
%%%

Consider $`\mathsf{while\ true\ do\ skip}`. [Session 2, §2.4](chapter-02/index.html#ch02-s4) proved that it has no terminating derivation. Its meaning gives $`\bot` at every state: by induction on the stage, $`w_{n+1}(\sigma)=w_n^\dagger(\sigma)=w_n(\sigma)=\bot`. Theorem 10.2 speaks only about states $`\sigma'`. There is no inference rule whose conclusion says that the final state is $`\bot`. To reach $`\bot` we quantify over states and rule them all out. This works because $`\Sigma_\bot` has exactly one element besides the states.

*Corollary 10.3 (Graph of the meaning).* For every command $`c`, $`\mathrm{graph}(f_c)=\mathrm{Exec}(c)`. Moreover, for every state $`\sigma`, $`f_c(\sigma)=\bot` if and only if no state $`\sigma'` satisfies $`\sigma\vdash c\Downarrow\sigma'`.

*Proof.* The first claim is Theorem 10.2 applied to each pair $`(\sigma,\sigma')`. For the second, $`f_c(\sigma)` is either $`\bot` or a state. If $`f_c(\sigma)=\sigma'` for a state $`\sigma'`, Theorem 10.2 gives $`\sigma\vdash c\Downarrow\sigma'`. Conversely, if $`\sigma\vdash c\Downarrow\sigma'`, then Theorem 10.2 gives $`f_c(\sigma)=\sigma'`, which is not $`\bot`. $`\square`

This is the operational–denotational correspondence for IMP. From an execution tree one obtains the denoted outcome. From a denoted state one constructs an execution tree. The graph records only the input and the terminating result. The intermediate configurations visited on the way to that result belong to the small-step account.

Session 3 used determinacy to read $`\mathrm{Exec}(c)` as the graph of a partial function: defined at $`\sigma` when some $`\sigma'` has $`\sigma\vdash c\Downarrow\sigma'`, with that unique $`\sigma'` as output. Corollary 10.3 identifies this partial function. It is the one represented by $`f_c`. Theorem 10.2 itself does not use determinacy. It even reproves it (Exercise 10.3).

*Which direction needs leastness.* Let $`W=\mathsf{while}\ 0<x\ \mathsf{do\ skip}`. [Session 9, §9.3](chapter-09/index.html#ch09-s3) showed that the identity $`\mathrm{id}` on states is a fixed point of its unfolding operator, while the least fixed point $`f_W` gives $`\bot` wherever $`0<x`. Suppose we had chosen $`\mathrm{id}` as the meaning of $`W`. The proof in §10.2 used only the fixed-point equation, so the direction from derivations to meanings would still hold. The other direction would fail. At a state with $`\sigma(x)=1` the identity returns $`\sigma`, but $`\sigma\vdash W\Downarrow\sigma` has no derivation. The least-height argument of Session 2, §2.4 applies unchanged, because the body skip leaves the guard true. The approximations used in §10.3 exclude such a result.

# Exercises
%%%
tag := "ch10-s5"
number := false
%%%

*10.1.* In the loop iteration case of §10.2, replace step 1 by an argument that uses only the approximations. From $`P(D_2)`, find a stage $`n` with $`w_n(\sigma_1)=\sigma'` and show $`w_{n+1}(\sigma)=\sigma'`. Which property of the information order then gives $`f_W(\sigma)=\sigma'`?

*10.2.* For the loop of §10.1 and the state $`\sigma` with $`\sigma(x)=0`, run the proof of §10.3 starting from $`w_3(\sigma)=\sigma'`. At each stage, name the pair of states at which $`Q_W` is applied and the derivation it returns.

*10.3.* Derive Session 3, Theorem 3.2 from Theorem 10.2. Then add the command `choose c or d` of Session 3, Exercise 3.2. Show that no state transformer, taken as the meaning of `choose x := 0 or x := 1`, can satisfy Theorem 10.2.

*Further problem.* Characterize the commands $`c` whose set $`\mathrm{Exec}(c)` is included in the diagonal $`\{(\sigma,\sigma)\mid\sigma\in\Sigma\}`. Use Theorem 10.2 to describe the meaning of $`c;d` for an arbitrary $`d`. Give an example showing why this inclusion alone does not justify deleting $`c`.

# Reading for the Seminar
%%%
tag := "ch10-s6"
number := false
%%%

*Definitions · 10 minutes.* Put the loop of §10.1 on the board: its three loop judgments and the outcomes $`w_1(\sigma')`, $`w_2(\sigma_1)`, $`w_3(\sigma)`. Write $`P(D)`, $`Q(c)` and $`Q_W(n)`, and mark what each induction runs over.

*Joint proof · 30 minutes.* The presenter proves the loop iteration case of §10.2. A second participant then proves the sequence case of §10.3 with Lemma 10.1, applying $`Q(c_2)` at the intermediate state.

*Proof review · 20 minutes.* Run the nested induction of §10.3 on the example (Exercise 10.2). Ask which direction fails if the identity is taken as the meaning of $`\mathsf{while}\ 0<x\ \mathsf{do\ skip}`.

*Facilitator’s hint.* Name the body result before naming the loop result. The body result comes from a smaller command. The loop result comes from a smaller derivation in §10.2 and from a smaller stage in §10.3.

# Solutions and Further Reading
%%%
tag := "ch10-s7"
number := false
%%%

*10.1.* $`P(D_2)` gives $`f_W(\sigma_1)=\sigma'`. The outcomes $`w_n(\sigma_1)` increase (Lemma 9.3) and their least upper bound is the state $`\sigma'` (Definition 9.4). By Lemma 8.10 some stage $`n` has $`w_n(\sigma_1)=\sigma'`. Since $`B(b,\sigma)=\mathsf{true}` and $`P(D_1)` gives $`f_{c_1}(\sigma)=\sigma_1`, we get $`w_{n+1}(\sigma)=F(w_n)(\sigma)=w_n^\dagger(\sigma_1)=w_n(\sigma_1)=\sigma'`. Finally $`w_{n+1}\sqsubseteq f_W`, and in the information order a state lies below only itself. Hence $`f_W(\sigma)=\sigma'`.

*10.2.* Start with $`Q_W(3)` at $`(\sigma,\sigma')`. The guard is true at $`\sigma` and the body gives $`\sigma_1`, so $`w_2(\sigma_1)=\sigma'`. The body hypothesis gives $`\sigma\vdash x:=x+1\Downarrow\sigma_1`, and $`Q_W(2)` is applied at $`(\sigma_1,\sigma')`. The guard is true at $`\sigma_1` and the body gives $`\sigma'`, so $`w_1(\sigma')=\sigma'`. The body hypothesis gives $`\sigma_1\vdash x:=x+1\Downarrow\sigma'`, and $`Q_W(1)` is applied at $`(\sigma',\sigma')`. The guard is false at $`\sigma'`, so the loop exit rule gives $`\sigma'\vdash W\Downarrow\sigma'`. Two loop iteration rules rebuild the derivation of §10.1. Stage zero is never reached. Here each stage exceeds the height of its loop judgment by one. A body containing its own loop would break this match, because the body derivation adds height but no stage.

*10.3.* If $`\sigma\vdash c\Downarrow\sigma'` and $`\sigma\vdash c\Downarrow\sigma''`, the direction from derivations to meanings gives $`f_c(\sigma)=\sigma'` and $`f_c(\sigma)=\sigma''`. Hence $`\sigma'=\sigma''`. For the choice command, both $`\sigma[x\mapsto0]` and $`\sigma[x\mapsto1]` are results from every $`\sigma`. A state transformer satisfying Theorem 10.2 would have to return both, and they differ at $`x`. A meaning for this command would have to give a set of outcomes rather than one outcome.

*Further problem.* Inclusion in the diagonal means that every terminating execution of $`c` leaves the initial state unchanged. By Corollary 10.3, $`f_c` gives either $`\bot` or its input at every state. Write $`A` for the set of states at which it returns. By Lemma 10.1 the intermediate state of $`c;d` from $`\sigma\in A` is $`\sigma` itself. So $`f_{c;d}(\sigma)=f_d(\sigma)` for $`\sigma\in A` and $`f_{c;d}(\sigma)=\bot` otherwise. For an example, let $`c` be $`\mathsf{while}\ 0<x\ \mathsf{do\ skip}` and let $`d` be skip. At a state with positive $`x` the prefix, and hence the sequence, has no terminating result. Deleting the prefix gives skip, which returns the input. To justify removal for every suffix and every input, take skip as the suffix. This shows that $`f_c` must be the identity on all states.

*Further reading · Meanings as relations.* Winskel (§§5.2–5.3) and Nipkow and Klein (_Concrete Semantics_, §11.1) define the meaning of a command directly as a set of pairs of states. Sequencing is relational composition, and a loop is the least fixed point of a monotone operator on relations. Nipkow and Klein obtain that fixed point from the Knaster–Tarski theorem. Winskel’s Theorem 5.7 and CS Theorem 11.6 identify the relation with the execution relation. Lemma 10.1 is the step that matches their sequencing clause: the graph of a strict composite is the relational composition of the two graphs. Nipkow and Klein prove the two directions separately, by rule induction (CS Lemma 11.4) and by structural induction (CS Lemma 11.5). Their loop case avoids approximations. The set of initial–final state pairs of the loop is closed under the loop operator, and the least fixed point lies inside every such closed relation. _The Hitchhiker’s Guide to Logical Verification_, §§11.2–11.7, develops relational meanings in Lean. [Concrete Semantics, §11.1](https://concrete-semantics.org/concrete-semantics.pdf#page=190) · [Hitchhiker’s Guide](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

*Further reading · Transferring a law.* [Session 7, Theorem 7.3](chapter-07/index.html#ch07-s2) proved that a loop $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1` and its one-step unfolding $`U=\mathsf{if}\ b\ \mathsf{then}\ (c_1;W)\ \mathsf{else\ skip}` satisfy $`\mathrm{Exec}(W)=\mathrm{Exec}(U)`. Corollary 10.3 determines each meaning from its set $`\mathrm{Exec}(c)`: $`f_c(\sigma)` is the unique $`\sigma'` with $`\sigma\vdash c\Downarrow\sigma'` if one exists, and $`\bot` otherwise. Hence $`f_W=f_U`. In general, $`c\equiv d` in the sense of Definition 7.1 if and only if $`f_c=f_d`. Nipkow and Klein state this for their relational meaning as CS Corollary 11.7.

*Further reading · An execution function with fuel.* Leroy’s course defines an execution function that takes a natural-number bound, called fuel, and gives no result when the fuel runs out. Every recursive call consumes fuel, not only the loop unfoldings counted by the stage. The course proves the function sound for the execution relation by induction on the fuel. It proves completeness by induction on the derivation, with a bound beyond which every larger fuel gives the same result. These are the two directions of Theorem 10.2 for a different function. [Leroy, IMP execution with fuel](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L206-L287)

# Sources and Formalization
%%%
tag := "ch10-notes"
number := false
%%%

The execution rules follow Leroy’s IMP (A.5). The meanings $`f_c` follow Reynolds, _Theories of Programming Languages_, §§2.2–2.4, as presented in Sessions 8–9. The proof structure follows Winskel, _The Formal Semantics of Programming Languages_, §5.3. Winskel and, in _Concrete Semantics_, Nipkow and Klein prove the corresponding theorem for a meaning defined directly as a relation between states. [Winskel, §5.3](https://doi.org/10.7551/mitpress/3054.001.0001) · [Concrete Semantics, §11.1.1, p. 183](https://concrete-semantics.org/concrete-semantics.pdf#page=193)

* *Lemma 10.1.* Formulated in this book. Checked in Lean ([`intermediateStore`](lean/Denotation.html#intermediateStore) · [IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 10.2.* Formulated in this book. Corresponds to Winskel Theorem 5.7 and CS Theorem 11.6. Checked in Lean ([`executionIffDenotation`](lean/Correspondence.html#executionIffDenotation) · [IMP card references](imp-card/index.html#imp-sources)).
* *Corollary 10.3.* Formulated in this book. Checked in Lean ([`graphAndDivergence`](lean/Correspondence.html#graphAndDivergence) · [IMP card references](imp-card/index.html#imp-sources)).
