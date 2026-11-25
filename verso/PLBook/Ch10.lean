import VersoManual
import PLBook.IMP.Correspondence

open Verso.Genre Manual

#doc (Manual) "Correspondence of Command Semantics" =>
%%%
tag := "ch10"
file := "chapter-10"
%%%

* *Definitions.* The execution rules ([Session 2, Definition 2.1](chapter-02/index.html#ch02-s2); [A.5](imp-card/index.html#imp-a5)). Partial function and graph ([Session 3, §3.3](chapter-03/index.html#ch03-s3)). The set $`\mathrm{Exec}(c)` of initial–final store pairs ([Session 7, Definition 7.1](chapter-07/index.html#ch07-s1)). Outcomes $`\Sigma_\bot`, state transformers, strict extension $`h^\dagger` and the meanings $`f_c` ([Session 8, Definitions 8.1–8.4](chapter-08/index.html#ch08-s1)). The information order and increasing sequences of outcomes ([Session 8, Definition 8.7 and Lemma 8.10](chapter-08/index.html#ch08-s4)). The unfolding operator $`F`, the approximations $`w_n` and the loop meaning $`f_W` ([Session 9, Definitions 9.1 and 9.4](chapter-09/index.html#ch09-s1)), and the least fixed-point theorem ([Session 9, Theorem 9.5](chapter-09/index.html#ch09-s3)).
* *New terms.* Relational composition, nested induction. [Glossary and label key](glossary/index.html)
* *Theorem 10.2 \[This book\] \[Checked\].* For every command $`c` and stores $`s,t`, $`s\vdash c\Downarrow t` if and only if $`f_c(s)=t`.
* *Source.* The execution rules follow Leroy’s IMP (A.5). The meanings $`f_c` follow Reynolds, _Theories of Programming Languages_, §§2.2–2.4, as presented in Sessions 8–9. The proof structure follows Winskel, _The Formal Semantics of Programming Languages_, §5.3. \[Corresponding: Winskel Theorem 5.7; CS Theorem 11.6\] Winskel and, in _Concrete Semantics_, Nipkow and Klein prove the corresponding theorem for a meaning defined directly as a relation between stores. [Winskel, §5.3](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf) · [Concrete Semantics, §11.1.1, p. 183](https://concrete-semantics.org/concrete-semantics.pdf#page=193)
* *Board case.* From a derivation to a meaning, loop iteration. Apply one induction hypothesis to the body and one to the loop from the intermediate store $`m`, and join them with the fixed-point equation of Session 9, Theorem 9.5(a).
* *Proof outline.* From derivations to meanings: induction on the derivation $`D:s\vdash c\Downarrow t` with $`P(D)\coloneqq f_c(s)=t`. From meanings to derivations: structural induction on $`c` with $`Q(c)\coloneqq\forall s,t\in\Sigma,\ f_c(s)=t\Rightarrow s\vdash c\Downarrow t`. In the loop case a nested induction on the stage $`n` proves $`Q_W(n)\coloneqq\forall s,t\in\Sigma,\ w_n(s)=t\Rightarrow s\vdash W\Downarrow t`.
* *From Session 9.* Session 9 defined the loop meaning $`f_W` as the least upper bound of the approximations $`w_n` and proved that it is the least fixed point of $`F`. The direction from derivations to meanings uses only the fixed-point equation $`f_W=F(f_W)`. The other direction uses the approximations themselves, and this is where leastness matters.

Take $`\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1` and a store with $`x=0`. The rules of Session 2 derive a final store with $`x=2`. The meaning computed in Session 9 returns the same store, first at stage 3. This session proves that the two accounts agree for every command and every pair of stores. The intermediate store in sequential composition is where they meet. For a loop the bridge is the number of finite unfoldings needed by an execution.

# Two accounts of one loop
%%%
tag := "ch10-s1"
%%%

Write $`W=\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1`. Let $`s(x)=0`, and put $`m=s[x\mapsto1]` and $`t=m[x\mapsto2]`. By [A.4](imp-card/index.html#imp-a4) the guard $`x<2` abbreviates $`\neg(2\le x)`. It is true in $`s` and $`m` and false in $`t`. Reading upwards from the root, the derivation $`D` of $`s\vdash W\Downarrow t` contains three loop judgments.

1. $`s\vdash W\Downarrow t` by the loop iteration rule, with body premise $`s\vdash x:=x+1\Downarrow m`.
2. $`m\vdash W\Downarrow t` by the loop iteration rule, with body premise $`m\vdash x:=x+1\Downarrow t`.
3. $`t\vdash W\Downarrow t` by the loop exit rule.

Session 9 computes the meaning of the same loop through the approximations of Definition 9.1. The approximation $`w_0` gives $`\bot` at every store, $`w_{n+1}=F(w_n)`, and $`n` is the stage of $`w_n`. At the three stores of the run,

$$`w_1(t)=t,\qquad w_2(m)=w_1(t)=t,\qquad w_3(s)=w_2(m)=t.`

Hence $`f_W(s)=t`, as in the table of Session 9, §9.1. The exit at $`t` matches the first stage at which $`t` returns. Each iteration rule matches one more stage.

A state transformer $`g:\Sigma\to\Sigma_\bot` carries the same information as the partial function on stores that is undefined at $`s` exactly when $`g(s)=\bot` ([Session 8, §8.1](chapter-08/index.html#ch08-s1)). Its graph, in the sense of Session 3, is therefore

$$`\mathrm{graph}(g)=\{(s,t)\in\Sigma\times\Sigma\mid g(s)=t\}.`

For a command $`c`, [Session 7, Definition 7.1](chapter-07/index.html#ch07-s1) writes $`\mathrm{Exec}(c)=\{(s,t)\mid s\vdash c\Downarrow t\}` for its set of initial–final store pairs. Call it the execution relation of $`c`. In the example the pairs $`(s,t)`, $`(m,t)` and $`(t,t)` belong to both $`\mathrm{graph}(f_W)` and $`\mathrm{Exec}(W)`.

Both directions of the main theorem use one calculation with strict extension. Let $`x\ne y`, let $`c_1` be $`x:=1` and let $`c_2` be $`y:=x+1`. Definition 8.4 gives $`f_{c_1;c_2}(s)=f_{c_2}^\dagger(f_{c_1}(s))`. Here $`f_{c_1}(s)=s[x\mapsto1]=m` is a store. Strict extension passes $`m` to $`f_{c_2}`, and the result is $`m[y\mapsto2]`. If the prefix were $`\mathsf{while\ true\ do\ skip}`, its meaning would give $`\bot` at every store (§10.4). The strict extension would return $`\bot`, and no store would lie in the middle.

*Lemma 10.1 (Intermediate store) \[This book\] \[Checked\].* For state transformers $`g,h` and stores $`s,t`,

$$`h^\dagger(g(s))=t\quad\Longleftrightarrow\quad\exists m\in\Sigma,\ \ g(s)=m\ \land\ h(m)=t.`

*Proof.* Split on the outcome $`g(s)`. If $`g(s)=\bot`, the left side reads $`\bot=t`, which is false because $`\bot` is not a store. The right side is false because $`g(s)` is not a store. If $`g(s)=u` for a store $`u`, the left side reads $`h(u)=t`. Then the right side holds with $`m=u`. Conversely, any witness satisfies $`m=g(s)=u`, so $`h(u)=t`. $`\square`

In terms of graphs, $`(s,t)\in\mathrm{graph}(h^\dagger\circ g)` exactly when some store $`m` has $`(s,m)\in\mathrm{graph}(g)` and $`(m,t)\in\mathrm{graph}(h)`. The set of pairs joined in this way is the *relational composition* of the two graphs. A relation can in general offer several intermediate stores. Here the only candidate is the outcome $`g(s)`, because the first computation is represented by a function.

*Theorem 10.2 (Correspondence) \[This book\] \[Checked\].* For every command $`c` and stores $`s,t\in\Sigma`,

$$`s\vdash c\Downarrow t\quad\Longleftrightarrow\quad f_c(s)=t.`

Here $`t` is a store, never $`\bot`. Equivalently, $`\mathrm{graph}(f_c)=\mathrm{Exec}(c)`. The two directions are proved separately, by different inductions.

* *From derivations to meanings* (§10.2). Assume a derivation $`D` of $`s\vdash c\Downarrow t`. Conclude $`f_c(s)=t`. The proof is by induction on $`D`.
* *From meanings to derivations* (§10.3). Assume $`f_c(s)=t`. Construct a derivation of $`s\vdash c\Downarrow t`. The proof is by structural induction on $`c`, with a nested induction on the stage in the loop case.

# From derivations to meanings
%%%
tag := "ch10-s2"
%%%

We prove $`P(D)` for every derivation $`D:s\vdash c\Downarrow t` by induction on $`D`, as in Session 3. The induction property is

$$`P(D)\quad\coloneqq\quad f_c(s)=t.`

Read $`s,c,t` from the conclusion of $`D`. Nothing is quantified inside $`P(D)`. Each premise fixes its own stores, and each hypothesis is used at exactly those stores.

For a loop $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`, Definition 9.1 builds the unfolding operator $`F` from the guard $`b` and the body meaning $`f_{c_1}`. For a state transformer $`h`,

$$`\begin{aligned}
F(h)(s)&=h^\dagger(f_{c_1}(s)) && \text{if } B(b,s)=\mathsf{true},\\
F(h)(s)&=s && \text{if } B(b,s)=\mathsf{false}.
\end{aligned}`

Theorem 9.5(a) states that the loop meaning is a fixed point:

$$`f_W=F(f_W).`

This direction uses only this equation.

*Skip and assignment.* $`D` is an axiom. Its conclusion is $`s\vdash\mathsf{skip}\Downarrow s` or $`s\vdash x:=e\Downarrow s[x\mapsto\mathrm{eval}(e,s)]`. Definition 8.4 assigns the same store as the meaning at $`s`.

*Sequence.* Suppose $`c=c_1;c_2`. The premises of $`D` are $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash c_2\Downarrow t`. The induction hypotheses are $`P(D_1):f_{c_1}(s)=m` and $`P(D_2):f_{c_2}(m)=t`. Lemma 10.1, read from right to left with the witness $`m`, gives $`f_{c_2}^\dagger(f_{c_1}(s))=t`. By Definition 8.4 the left side is $`f_{c_1;c_2}(s)`.

*Conditional.* For $`I=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`, let $`k` be the command selected by $`B(b,s)`. The premise of $`D` is $`D_1:s\vdash k\Downarrow t`, with $`P(D_1):f_k(s)=t`. Definition 8.4 gives $`f_I(s)=f_k(s)`, so $`f_I(s)=t`.

*Loop exit.* If $`D` ends by the loop exit rule, then $`B(b,s)=\mathsf{false}` and $`t=s`. The fixed-point equation gives $`f_W(s)=F(f_W)(s)=s`.

*Loop iteration (board case).* Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`. We must show $`f_W(s)=t`. Suppose $`D` ends with the loop iteration rule. Its side condition is $`B(b,s)=\mathsf{true}`. Its premises are $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash W\Downarrow t`. The induction hypotheses are

$$`\begin{aligned}
P(D_1)&:\quad f_{c_1}(s)=m,\\
P(D_2)&:\quad f_W(m)=t.
\end{aligned}`

1. By the fixed-point equation (Theorem 9.5(a)), $`f_W(s)=F(f_W)(s)`.
2. The side condition gives $`B(b,s)=\mathsf{true}`. So the true-guard clause of $`F` applies: $`F(f_W)(s)=f_W^\dagger(f_{c_1}(s))`.
3. Rewrite the body outcome with $`P(D_1)`, that is, $`f_{c_1}(s)=m`. Hence $`f_W^\dagger(f_{c_1}(s))=f_W^\dagger(m)`.
4. Since $`m` is a store, the strict extension applies $`f_W` to it: $`f_W^\dagger(m)=f_W(m)`.
5. Rewrite the loop outcome at $`m` with $`P(D_2)`, that is, $`f_W(m)=t`.
6. Chain steps 1–5: $`f_W(s)=F(f_W)(s)=f_W^\dagger(m)=f_W(m)=t`.

Steps 3–5 are Lemma 10.1 read from right to left with the witness $`m`. The derivation $`D_2` concerns the very same command $`W`. Induction on command syntax would supply no hypothesis for it. Induction on derivations does, because $`D_2` is a proper subderivation of $`D`. This proves $`P(D)` for every derivation $`D`.

# From meanings to derivations
%%%
tag := "ch10-s3"
%%%

Now assume $`f_c(s)=t` for a store $`t`. We must construct a derivation of $`s\vdash c\Downarrow t`. There is no derivation to induct on yet. We use structural induction on $`c` with the induction property

$$`Q(c)\quad\coloneqq\quad\forall s,t\in\Sigma,\ \ f_c(s)=t\ \Longrightarrow\ s\vdash c\Downarrow t.`

The stores are quantified inside $`Q(c)`. In the sequence case the hypothesis for the second command is needed at the intermediate store, not at $`s`.

*Skip and assignment.* Since $`f_{\mathsf{skip}}(s)=s`, we have $`t=s`, and the skip axiom applies. For $`x:=e`, we have $`t=s[x\mapsto\mathrm{eval}(e,s)]`, and the assignment axiom applies.

*Sequence.* Suppose $`c=c_1;c_2`. The induction hypotheses are

$$`\begin{aligned}
Q(c_1)&:\quad\forall s,t\in\Sigma,\ f_{c_1}(s)=t\Rightarrow s\vdash c_1\Downarrow t,\\
Q(c_2)&:\quad\forall s,t\in\Sigma,\ f_{c_2}(s)=t\Rightarrow s\vdash c_2\Downarrow t.
\end{aligned}`

1. By Definition 8.4, the assumption reads $`f_{c_2}^\dagger(f_{c_1}(s))=t`.
2. Lemma 10.1, read from left to right, gives a store $`m` with $`f_{c_1}(s)=m` and $`f_{c_2}(m)=t`.
3. Apply $`Q(c_1)` to the pair $`(s,m)`. This gives $`s\vdash c_1\Downarrow m`.
4. Apply $`Q(c_2)` to the pair $`(m,t)`. This gives $`m\vdash c_2\Downarrow t`.
5. The sequence rule joins the two derivations into $`s\vdash c_1;c_2\Downarrow t`.

*Conditional.* The selected command $`k` is $`c_1` or $`c_2`, an immediate part of $`I`. From $`f_I(s)=f_k(s)=t`, apply $`Q(k)` to $`(s,t)` to obtain $`s\vdash k\Downarrow t`. The conditional rule gives $`s\vdash I\Downarrow t`.

*Loop.* Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`. The structural induction hypothesis $`Q(c_1)` gives the correspondence for the body on all stores. It supplies no hypothesis for the loop itself. We therefore carry out a second induction, on the stage of the approximations, inside this case. An induction carried out inside one case of another induction, with the outer hypotheses still available, is a *nested induction*.

First reduce to a finite stage. The outcomes $`w_0(s)\sqsubseteq w_1(s)\sqsubseteq\cdots` increase (Lemma 9.3), and $`f_W(s)` is their least upper bound (Definition 9.4). By Lemma 8.10 such a sequence either stays at $`\bot` or reaches a store and stays there. Since $`f_W(s)=t`, some stage $`n` has $`w_n(s)=t`.

Next prove $`Q_W(n)` for every natural number $`n` by induction on $`n`, where

$$`Q_W(n)\quad\coloneqq\quad\forall s,t\in\Sigma,\ \ w_n(s)=t\ \Longrightarrow\ s\vdash W\Downarrow t.`

*Stage zero.* $`w_0(s)=\bot`, which is never a store. There is nothing to prove.

*Successor stage.* Assume $`Q_W(n)` and $`w_{n+1}(s)=t`. By definition $`w_{n+1}(s)=F(w_n)(s)`.

* If $`B(b,s)=\mathsf{false}`, then $`F(w_n)(s)=s`, so $`t=s`. The loop exit rule gives $`s\vdash W\Downarrow s`.
* If $`B(b,s)=\mathsf{true}`, then $`w_n^\dagger(f_{c_1}(s))=t`. Lemma 10.1 gives a store $`m` with $`f_{c_1}(s)=m` and $`w_n(m)=t`. Apply $`Q(c_1)` to $`(s,m)` to obtain $`s\vdash c_1\Downarrow m`. Apply $`Q_W(n)` to $`(m,t)` to obtain $`m\vdash W\Downarrow t`. The loop iteration rule gives $`s\vdash W\Downarrow t`.

Finally apply $`Q_W(n)`, for the stage $`n` found first, to the pair $`(s,t)`. The body hypothesis comes from a smaller command. The loop hypothesis comes from a smaller stage. Each direction constructs the witness that its target definition demands. This completes the proof of Theorem 10.2. $`\square`

# Scope of the theorem
%%%
tag := "ch10-s4"
%%%

Consider $`\mathsf{while\ true\ do\ skip}`. [Session 2, §2.4](chapter-02/index.html#ch02-s4) proved that it has no terminating derivation. Its meaning gives $`\bot` at every store: by induction on the stage, $`w_{n+1}(s)=w_n^\dagger(s)=w_n(s)=\bot`. Theorem 10.2 speaks only about stores $`t`. There is no inference rule whose conclusion says that the final store is $`\bot`. To reach $`\bot` we quantify over stores and rule them all out. This works because $`\Sigma_\bot` has exactly one element besides the stores.

*Corollary 10.3 (Graph of the meaning) \[This book\] \[Checked\].* For every command $`c`, $`\mathrm{graph}(f_c)=\mathrm{Exec}(c)`. Moreover, for every store $`s`, $`f_c(s)=\bot` if and only if no store $`t` satisfies $`s\vdash c\Downarrow t`.

*Proof.* The first claim is Theorem 10.2 applied to each pair $`(s,t)`. For the second, $`f_c(s)` is either $`\bot` or a store. If $`f_c(s)=t` for a store $`t`, Theorem 10.2 gives $`s\vdash c\Downarrow t`. Conversely, if $`s\vdash c\Downarrow t`, then Theorem 10.2 gives $`f_c(s)=t`, which is not $`\bot`. $`\square`

Session 3 used determinacy to read $`\mathrm{Exec}(c)` as the graph of a partial function: defined at $`s` when some $`t` has $`s\vdash c\Downarrow t`, with that unique $`t` as output. Corollary 10.3 identifies this partial function. It is the one represented by $`f_c`. Theorem 10.2 itself does not use determinacy. It even reproves it (Exercise 10.3).

*Which direction needs leastness.* Let $`W=\mathsf{while}\ 0<x\ \mathsf{do\ skip}`. [Session 9, §9.3](chapter-09/index.html#ch09-s3) showed that the identity $`\mathrm{id}` on stores is a fixed point of its unfolding operator, while the least fixed point $`f_W` gives $`\bot` wherever $`0<x`. Suppose we had chosen $`\mathrm{id}` as the meaning of $`W`. The proof in §10.2 used only the fixed-point equation, so the direction from derivations to meanings would still hold. The other direction would fail. At a store with $`s(x)=1` the identity returns $`s`, but $`s\vdash W\Downarrow s` has no derivation. The least-height argument of Session 2, §2.4 applies unchanged, because the body skip leaves the guard true. The approximations used in §10.3 exclude such a result.

# Exercises
%%%
tag := "ch10-s5"
number := false
%%%

*10.1.* In the loop iteration case of §10.2, replace step 1 by an argument that uses only the approximations. From $`P(D_2)`, find a stage $`n` with $`w_n(m)=t` and show $`w_{n+1}(s)=t`. Which property of the information order then gives $`f_W(s)=t`?

*10.2.* For the loop of §10.1 and the store $`s` with $`s(x)=0`, run the proof of §10.3 starting from $`w_3(s)=t`. At each stage, name the pair of stores at which $`Q_W` is applied and the derivation it returns.

*10.3.* Derive Session 3, Theorem 3.2 from Theorem 10.2. Then add the command `choose c or d` of Session 3, Exercise 3.2. Show that no state transformer, taken as the meaning of `choose x := 0 or x := 1`, can satisfy Theorem 10.2.

*Further problem.* Characterize the commands $`c` whose execution relation is included in the diagonal $`\{(s,s)\mid s\in\Sigma\}`. Use Theorem 10.2 to describe the meaning of $`c;d` for an arbitrary $`d`. Give an example showing why this inclusion alone does not justify deleting $`c`.

# Reading for the Seminar
%%%
tag := "ch10-s6"
number := false
%%%

*Definitions · 10 minutes.* Put the loop of §10.1 on the board: its three loop judgments and the outcomes $`w_1(t)`, $`w_2(m)`, $`w_3(s)`. Write $`P(D)`, $`Q(c)` and $`Q_W(n)`, and mark what each induction runs over.

*Joint proof · 30 minutes.* The presenter proves the loop iteration case of §10.2. A second participant then proves the sequence case of §10.3 with Lemma 10.1, applying $`Q(c_2)` at the intermediate store.

*Proof review · 20 minutes.* Run the nested induction of §10.3 on the example (Exercise 10.2). Ask which direction fails if the identity is taken as the meaning of $`\mathsf{while}\ 0<x\ \mathsf{do\ skip}`.

*Facilitator’s hint.* Name the body result before naming the loop result. The body result comes from a smaller command. The loop result comes from a smaller derivation in §10.2 and from a smaller stage in §10.3.

# Solutions and Further Reading
%%%
tag := "ch10-s7"
number := false
%%%

*10.1.* $`P(D_2)` gives $`f_W(m)=t`. The outcomes $`w_n(m)` increase (Lemma 9.3) and their least upper bound is the store $`t` (Definition 9.4). By Lemma 8.10 some stage $`n` has $`w_n(m)=t`. Since $`B(b,s)=\mathsf{true}` and $`P(D_1)` gives $`f_{c_1}(s)=m`, we get $`w_{n+1}(s)=F(w_n)(s)=w_n^\dagger(m)=w_n(m)=t`. Finally $`w_{n+1}\sqsubseteq f_W`, and in the information order a store lies below only itself. Hence $`f_W(s)=t`.

*10.2.* Start with $`Q_W(3)` at $`(s,t)`. The guard is true at $`s` and the body gives $`m`, so $`w_2(m)=t`. The body hypothesis gives $`s\vdash x:=x+1\Downarrow m`, and $`Q_W(2)` is applied at $`(m,t)`. The guard is true at $`m` and the body gives $`t`, so $`w_1(t)=t`. The body hypothesis gives $`m\vdash x:=x+1\Downarrow t`, and $`Q_W(1)` is applied at $`(t,t)`. The guard is false at $`t`, so the loop exit rule gives $`t\vdash W\Downarrow t`. Two loop iteration rules rebuild the derivation of §10.1. Stage zero is never reached. Here each stage exceeds the height of its loop judgment by one. A body containing its own loop would break this match, because the body derivation adds height but no stage.

*10.3.* If $`s\vdash c\Downarrow t` and $`s\vdash c\Downarrow u`, the direction from derivations to meanings gives $`f_c(s)=t` and $`f_c(s)=u`. Hence $`t=u`. For the choice command, both $`s[x\mapsto0]` and $`s[x\mapsto1]` are results from every $`s`. A state transformer satisfying Theorem 10.2 would have to return both, and they differ at $`x`. A meaning for this command would have to give a set of outcomes rather than one outcome.

*Further problem.* Inclusion in the diagonal means that every terminating execution of $`c` leaves the initial store unchanged. By Corollary 10.3, $`f_c` gives either $`\bot` or its input at every store. Write $`A` for the set of stores at which it returns. By Lemma 10.1 the intermediate store of $`c;d` from $`s\in A` is $`s` itself. So $`f_{c;d}(s)=f_d(s)` for $`s\in A` and $`f_{c;d}(s)=\bot` otherwise. For an example, let $`c` be $`\mathsf{while}\ 0<x\ \mathsf{do\ skip}` and let $`d` be skip. At a store with positive $`x` the prefix, and hence the sequence, has no terminating result. Deleting the prefix gives skip, which returns the input. To justify removal for every suffix and every input, take skip as the suffix. This shows that $`f_c` must be the identity on all stores.

*Further reading · Meanings as relations.* Winskel (§§5.2–5.3) and Nipkow and Klein (_Concrete Semantics_, §11.1) define the meaning of a command directly as a set of pairs of stores. Sequencing is relational composition, and a loop is the least fixed point of a monotone operator on relations. Nipkow and Klein obtain that fixed point from the Knaster–Tarski theorem. Winskel’s Theorem 5.7 and CS Theorem 11.6 identify the relation with the execution relation. Lemma 10.1 is the step that matches their sequencing clause: the graph of a strict composite is the relational composition of the two graphs. Nipkow and Klein prove the two directions separately, by rule induction (CS Lemma 11.4) and by structural induction (CS Lemma 11.5). Their loop case avoids approximations. The execution relation of the loop is closed under the loop operator, and the least fixed point lies inside every such closed relation. _The Hitchhiker’s Guide to Logical Verification_, §§11.2–11.7, develops relational meanings in Lean. [Concrete Semantics, §11.1](https://concrete-semantics.org/concrete-semantics.pdf#page=190) · [Hitchhiker’s Guide](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

*Further reading · Transferring a law.* [Session 7, Theorem 7.3](chapter-07/index.html#ch07-s2) proved that a loop $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1` and its one-step unfolding $`U=\mathsf{if}\ b\ \mathsf{then}\ (c_1;W)\ \mathsf{else\ skip}` satisfy $`\mathrm{Exec}(W)=\mathrm{Exec}(U)`. Corollary 10.3 determines each meaning from its execution relation: $`f_c(s)` is the unique $`t` with $`s\vdash c\Downarrow t` if one exists, and $`\bot` otherwise. Hence $`f_W=f_U`. In general, $`c\equiv d` in the sense of Definition 7.1 if and only if $`f_c=f_d`. Nipkow and Klein state this for their relational meaning as CS Corollary 11.7.

*Further reading · An execution function with fuel.* Leroy’s course defines an execution function that takes a natural-number bound, called fuel, and gives no result when the fuel runs out. Every recursive call consumes fuel, not only the loop unfoldings counted by the stage. The course proves the function sound for the execution relation by induction on the fuel. It proves completeness by induction on the derivation, with a bound beyond which every larger fuel gives the same result. These are the two directions of Theorem 10.2 for a different function. [Leroy, IMP execution with fuel](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L206-L237)
