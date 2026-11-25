import VersoManual

open Verso.Genre Manual

#doc (Manual) "Type Safety for Booleans and Numbers" =>
%%%
tag := "ch24"
file := "chapter-24"
%%%

The closed term $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` cannot step. Its guard $`0` is a value, but E-IfTrue and E-IfFalse need the guard $`\mathsf{true}` or $`\mathsf{false}`, and E-If needs a step of the guard. The term is not a value either, so evaluation stops without an answer. The term $`\mathsf{if}\ \mathsf{iszero}\ 0\ \mathsf{then}\ \mathsf{succ}\ 0\ \mathsf{else}\ 0` reaches the value $`\mathsf{succ}\ 0` in two steps. The first term has no type, and the second has type Nat. This session proves that a term with a type never reaches a term like the first.

*In this session.*

* *Definitions.* Terms, values, numeric values $`nv`, the evaluation rules, the types Bool and Nat and the typing rules ([C.2](lambda-card/index.html#lambda-c2)). The typing judgment $`\vdash t:T` ([Lambda card, Judgments](lambda-card/index.html)). One step $`t\to t'`, computation and congruence rules, normal forms and $`t\to^*t'` ([C.1](lambda-card/index.html#lambda-c1), Session 23). Inference rules and derivations ([A.3](imp-card/index.html#imp-a3)). Inversion and induction on derivations ([Session 1, §§1.4–1.5](chapter-01/index.html#ch01-s4)). The general statements and the form of the safety table ([C.8](lambda-card/index.html#lambda-c8)).
* *New terms.* Stuck term, well-typed term, canonical form, preservation, type safety. [Glossary](glossary/index.html)
* *Lemma 24.2 (Canonical forms), Theorem 24.3 (Progress) and Theorem 24.4 (Preservation).* (Canonical forms) For every value $`v`: if $`\vdash v:\mathsf{Bool}` then $`v=\mathsf{true}` or $`v=\mathsf{false}`; if $`\vdash v:\mathsf{Nat}` then $`v` is a numeric value. (Progress) For every term $`t` and type $`T`: if $`\vdash t:T`, then $`t` is a value or there is a term $`t'` with $`t\to t'`. (Preservation) For all terms $`t,t'` and every type $`T`: if $`\vdash t:T` and $`t\to t'`, then $`\vdash t':T`.
* *Board case.* Progress, case T-If. Apply the induction hypothesis to the guard. A step of the guard lifts to the conditional by E-If. A guard that is a value has type Bool, so Lemma 24.2 makes it true or false, and E-IfTrue or E-IfFalse applies.
* *Proof outline.* Canonical forms: list the forms of value and exclude the wrong ones with the inversion Lemma 24.1. Progress: induction on the typing derivation $`D` of $`\vdash t:T` with $`P(D)\coloneqq t\ \text{is a value}\ \lor\ \exists t',\ t\to t'`. Preservation: induction on the evaluation derivation $`E` of $`t\to t'` with $`Q(E)\coloneqq\forall T,\ (\vdash t:T)\Rightarrow(\vdash t':T)`. Each preservation case inverts the typing of $`t` and builds a typing of $`t'`.
* *From Session 23.* Session 23 followed evaluation that never ends, as for $`\Omega`. Here evaluation can also end without an answer. In the untyped terms of C.1 every value is an abstraction, so an application of a value to a value is always a redex. Session 24 starts the typed language with two kinds of value, Booleans and numeric values. A value of the wrong kind can block every rule, so a closed term can now be stuck. The typing rules exclude such terms before evaluation starts. The language has no variables until C.3.

# Values, steps and stuck terms
%%%
tag := "ch24-s1"
%%%

By [C.2](lambda-card/index.html#lambda-c2), the values are $`\mathsf{true}`, $`\mathsf{false}` and the numeric values $`nv::=0\mid\mathsf{succ}\ nv`. Each evaluation rule is an inference rule as in [A.3](imp-card/index.html#imp-a3), so $`t\to t'` holds exactly when it has a derivation. We call such a derivation an _evaluation derivation_. Every term of C.2 is closed, because the language has no variables.

Consider $`\mathsf{pred}\ (\mathsf{succ}\ (\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0))`. E-PredSucc does not apply yet. It needs $`\mathsf{pred}\ (\mathsf{succ}\ nv_1)`, and the argument of succ is a conditional, not a numeric value. The conditional steps by E-IfTrue. E-Succ lifts this step over succ, and E-Pred lifts the result over pred:

$$`\dfrac{\dfrac{\dfrac{}{\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0\to 0}\;\textsf{E-IfTrue}}{\mathsf{succ}\ (\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0)\to\mathsf{succ}\ 0}\;\textsf{E-Succ}}{\mathsf{pred}\ (\mathsf{succ}\ (\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0))\to\mathsf{pred}\ (\mathsf{succ}\ 0)}\;\textsf{E-Pred}`

This is one step, and its derivation has three rules. The next step is $`\mathsf{pred}\ (\mathsf{succ}\ 0)\to 0` by E-PredSucc with $`nv_1=0`. Its derivation has one rule. The size of the derivation of one step and the number of steps measure different things. Progress and preservation concern one step. Safety concerns any number of steps.

Now consider $`\mathsf{pred}\ (\mathsf{succ}\ \mathsf{false})`. The syntax still has pred directly above succ, yet no rule applies.

1. E-PredZero needs the argument $`0`.
2. E-PredSucc needs $`\mathsf{succ}\ nv_1`, and $`\mathsf{false}` is not a numeric value.
3. E-Pred needs a step $`\mathsf{succ}\ \mathsf{false}\to t_1'`. The only rule whose conclusion starts with succ is E-Succ, and it needs a step from $`\mathsf{false}`. No rule has a conclusion that starts with $`\mathsf{false}`.

So the term is a normal form. It is not a value, because no value starts with pred. A closed term that is a normal form but not a value is *stuck* (C.2; compare stuck IMP configurations in [Session 5, §5.2](chapter-05/index.html#ch05-s2)). The opening term $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` is stuck by the same kind of check. In both terms a value of one kind sits where every rule expects a value of the other kind.

# Typing, inversion and canonical forms
%%%
tag := "ch24-s2"
%%%

This session uses the typing rules of C.2 with the empty context and writes $`\vdash t:T`. A term $`t` is *well typed* if $`\vdash t:T` for some type $`T`. The opening term that reaches $`\mathsf{succ}\ 0` has the following typing derivation.

$$`\dfrac{\dfrac{\dfrac{}{\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}}{\vdash\mathsf{iszero}\ 0:\mathsf{Bool}}\;\textsf{T-IsZero}\qquad\dfrac{\dfrac{}{\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}}{\vdash\mathsf{succ}\ 0:\mathsf{Nat}}\;\textsf{T-Succ}\qquad\dfrac{}{\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}}{\vdash\mathsf{if}\ \mathsf{iszero}\ 0\ \mathsf{then}\ \mathsf{succ}\ 0\ \mathsf{else}\ 0:\mathsf{Nat}}\;\textsf{T-If}`

The stuck term $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` has no type. A derivation would have to end with T-If, the only typing rule whose conclusion is a conditional. Its first premise would be $`\vdash 0:\mathsf{Bool}`. But T-Zero is the only rule whose conclusion types $`0`, and it gives Nat. In the same way $`\mathsf{pred}\ (\mathsf{succ}\ \mathsf{false})` has no type, since T-Succ would need $`\vdash\mathsf{false}:\mathsf{Nat}`. The next lemma records this reasoning once for every form of term.

*Lemma 24.1 (Inversion of typing).* For every type $`T` and all terms $`t_1,t_2,t_3`:

* (a) If $`\vdash\mathsf{true}:T` or $`\vdash\mathsf{false}:T`, then $`T=\mathsf{Bool}`.
* (b) If $`\vdash\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3:T`, then $`\vdash t_1:\mathsf{Bool}`, $`\vdash t_2:T` and $`\vdash t_3:T`.
* (c) If $`\vdash 0:T`, then $`T=\mathsf{Nat}`.
* (d) If $`\vdash\mathsf{succ}\ t_1:T` or $`\vdash\mathsf{pred}\ t_1:T`, then $`T=\mathsf{Nat}` and $`\vdash t_1:\mathsf{Nat}`.
* (e) If $`\vdash\mathsf{iszero}\ t_1:T`, then $`T=\mathsf{Bool}` and $`\vdash t_1:\mathsf{Nat}`.

*Proof.* For each form of term, exactly one typing rule of C.2 has a conclusion of that form. By inversion ([Session 1, §1.4](chapter-01/index.html#ch01-s4)), a derivation of the hypothesis ends with that rule. Its conclusion fixes $`T`, and its premises are the remaining claims. $`\square`

Compare three guards. The term $`\mathsf{iszero}\ (\mathsf{pred}\ 0)` has type Bool but is not a value. A conditional with this guard steps inside the guard, by E-If. The term $`\mathsf{succ}\ 0` is a value but has type Nat, and no rule selects a branch with it. The term $`\mathsf{true}` is a value and has type Bool, and E-IfTrue applies. Only the two facts together, being a value and having type Bool, give the shape that a computation rule needs. The *canonical forms* of a type are the shapes that a value of that type can have. The next lemma lists them for Bool and Nat.

*Lemma 24.2 (Canonical forms).* Let $`v` be a value.

* (a) If $`\vdash v:\mathsf{Bool}`, then $`v=\mathsf{true}` or $`v=\mathsf{false}`.
* (b) If $`\vdash v:\mathsf{Nat}`, then $`v` is a numeric value.

*Proof.* By the grammar of values in C.2, $`v` is $`\mathsf{true}`, $`\mathsf{false}`, $`0`, or $`\mathsf{succ}\ nv_1` for a numeric value $`nv_1`. (a) If $`v=0`, Lemma 24.1(c) gives $`\mathsf{Bool}=\mathsf{Nat}`. If $`v=\mathsf{succ}\ nv_1`, Lemma 24.1(d) gives $`\mathsf{Bool}=\mathsf{Nat}`. Both are impossible, so $`v` is $`\mathsf{true}` or $`\mathsf{false}`. (b) If $`v` is $`\mathsf{true}` or $`\mathsf{false}`, Lemma 24.1(a) gives $`\mathsf{Nat}=\mathsf{Bool}`, which is impossible. So $`v` is $`0` or $`\mathsf{succ}\ nv_1`, a numeric value. $`\square`

The hypothesis that $`v` is a value cannot be dropped: $`\vdash\mathsf{iszero}\ 0:\mathsf{Bool}`, and $`\mathsf{iszero}\ 0` is neither $`\mathsf{true}` nor $`\mathsf{false}`.

# Progress and preservation
%%%
tag := "ch24-s3"
%%%

Take $`t=\mathsf{if}\ \mathsf{iszero}\ 0\ \mathsf{then}\ \mathsf{succ}\ 0\ \mathsf{else}\ 0` with $`\vdash t:\mathsf{Nat}`. Its guard $`\mathsf{iszero}\ 0` steps to $`\mathsf{true}` by E-IszeroZero, and E-If lifts that step to $`t`. After the step the guard is $`\mathsf{true}`, a value of type Bool, and E-IfTrue applies. The proof of progress follows this pattern: ask the guard first. [Session 5](chapter-05/index.html#ch05-s2) used the word progress for IMP configurations. Here it is a property of well-typed terms.

*Theorem 24.3 (Progress).* For every term $`t` and type $`T`: if $`\vdash t:T`, then $`t` is a value or there is a term $`t'` with $`t\to t'`.

We prove $`P(D)` for every typing derivation $`D` by induction on $`D` ([Session 1, §1.5](chapter-01/index.html#ch01-s5)). For $`D:\ \vdash t:T` the induction property is

$$`P(D)\coloneqq t\ \text{is a value}\ \lor\ \exists t',\ t\to t'.`

The board case uses four rules of C.2, written here with the empty context.

$$`\frac{\vdash t_1:\mathsf{Bool}\quad\vdash t_2:T\quad\vdash t_3:T}{\vdash\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3:T}\;\textsf{T-If}\qquad\frac{t_1\to t_1'}{\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\to\mathsf{if}\ t_1'\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3}\;\textsf{E-If}`

$$`\frac{}{\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\to t_2}\;\textsf{E-IfTrue}\qquad\frac{}{\mathsf{if}\ \mathsf{false}\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\to t_3}\;\textsf{E-IfFalse}`

*Case T-If (board case).* Suppose $`D` ends with T-If. Then $`t=\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3`, and the premises of $`D` are $`D_1:\ \vdash t_1:\mathsf{Bool}`, $`D_2:\ \vdash t_2:T` and $`D_3:\ \vdash t_3:T`. The induction hypothesis for the guard is

$$`P(D_1):\quad t_1\ \text{is a value}\ \lor\ \exists t_1',\ t_1\to t_1'.`

1. We must show that $`t` is a value or that $`t\to t'` for some $`t'`. No value of C.2 is a conditional, so we must find $`t'`.
2. Apply $`P(D_1)`. It gives two cases, treated in step 3 and in steps 4–5.
3. Suppose $`t_1\to t_1'`. E-If, with this step as its premise, gives $`t\to\mathsf{if}\ t_1'\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3`.
4. Suppose $`t_1` is a value. The premise $`D_1` gives $`\vdash t_1:\mathsf{Bool}`. Lemma 24.2(a), applied to the value $`t_1`, gives $`t_1=\mathsf{true}` or $`t_1=\mathsf{false}`.
5. If $`t_1=\mathsf{true}`, E-IfTrue gives $`t\to t_2`. If $`t_1=\mathsf{false}`, E-IfFalse gives $`t\to t_3`.

In every case $`t` steps. Step 4 is the only place where the conclusion $`\vdash t_1:\mathsf{Bool}` of $`D_1` is used; step 2 uses $`D_1` only through its induction hypothesis. The hypotheses $`P(D_2)` and $`P(D_3)` are not used: a branch need not be a value, and need not step, for the conditional to step.

*Other cases.* T-True, T-False and T-Zero: $`t` is $`\mathsf{true}`, $`\mathsf{false}` or $`0`, a value. T-Succ: $`t=\mathsf{succ}\ t_1` with $`D_1:\ \vdash t_1:\mathsf{Nat}`. If $`t_1\to t_1'`, E-Succ gives $`t\to\mathsf{succ}\ t_1'`. If $`t_1` is a value, Lemma 24.2(b) makes it a numeric value $`nv_1`. Then $`t=\mathsf{succ}\ nv_1` is a numeric value, so $`t` is a value. T-Pred: $`t=\mathsf{pred}\ t_1` with $`D_1:\ \vdash t_1:\mathsf{Nat}`. If $`t_1\to t_1'`, E-Pred applies. If $`t_1` is a value, Lemma 24.2(b) gives $`t_1=0` or $`t_1=\mathsf{succ}\ nv_1`, and E-PredZero or E-PredSucc applies. T-IsZero: as for T-Pred, with E-IsZero, E-IszeroZero and E-IszeroSucc. This proves $`P(D)` for every $`D`. $`\square`

Preservation follows one step and keeps the type. The term $`t` above steps to $`t'=\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ \mathsf{succ}\ 0\ \mathsf{else}\ 0` by E-If above E-IszeroZero. Lemma 24.1(b) inverts $`\vdash t:\mathsf{Nat}` into $`\vdash\mathsf{iszero}\ 0:\mathsf{Bool}`, $`\vdash\mathsf{succ}\ 0:\mathsf{Nat}` and $`\vdash 0:\mathsf{Nat}`. The guard step keeps the type Bool, since $`\vdash\mathsf{true}:\mathsf{Bool}` by T-True. T-If builds $`\vdash t':\mathsf{Nat}` from the new guard typing and the two old branch typings. The next step, by E-IfTrue, gives $`\mathsf{succ}\ 0`, and its typing is already a premise. For the first step the proof applies T-If again to build a new derivation. For the second it reuses a premise.

*Theorem 24.4 (Preservation).* For all terms $`t,t'` and every type $`T`: if $`\vdash t:T` and $`t\to t'`, then $`\vdash t':T`.

We prove $`Q(E)` for every evaluation derivation $`E` by induction on $`E`. For $`E:t\to t'` the induction property is

$$`Q(E)\coloneqq\forall T,\ (\vdash t:T)\Rightarrow(\vdash t':T).`

The type is quantified inside $`Q(E)`, as the final state was in [Session 3, §3.2](chapter-03/index.html#ch03-s2). The induction hypothesis is then available at the type of the subterm that steps, which may differ from $`T`. In the case E-IsZero below, $`T=\mathsf{Bool}` and the subterm has type Nat.

*E-If.* Here $`t=\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3` and $`t'=\mathsf{if}\ t_1'\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3`. The premise of $`E` is $`E_1:t_1\to t_1'`, with $`Q(E_1):\forall S,\ (\vdash t_1:S)\Rightarrow(\vdash t_1':S)`. Let $`\vdash t:T`. Lemma 24.1(b) gives $`\vdash t_1:\mathsf{Bool}`, $`\vdash t_2:T` and $`\vdash t_3:T`. $`Q(E_1)` at $`S=\mathsf{Bool}` gives $`\vdash t_1':\mathsf{Bool}`. T-If gives $`\vdash t':T`.

*E-Succ, E-Pred, E-IsZero.* Here $`t` is $`\mathsf{succ}\ t_1`, $`\mathsf{pred}\ t_1` or $`\mathsf{iszero}\ t_1`, and the premise of $`E` is $`E_1:t_1\to t_1'`. Let $`\vdash t:T`. Lemma 24.1(d) or (e) gives $`\vdash t_1:\mathsf{Nat}` and the value of $`T`. $`Q(E_1)` at $`\mathsf{Nat}` gives $`\vdash t_1':\mathsf{Nat}`, and T-Succ, T-Pred or T-IsZero gives $`\vdash t':T`.

*E-IfTrue, E-IfFalse.* Here $`t=\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3` and $`t'=t_2`, or the guard is $`\mathsf{false}` and $`t'=t_3`. Let $`\vdash t:T`. Lemma 24.1(b) gives $`\vdash t_2:T` and $`\vdash t_3:T`.

*E-PredZero, E-PredSucc.* Let $`\vdash t:T`. Lemma 24.1(d) gives $`T=\mathsf{Nat}`. For $`\mathsf{pred}\ 0\to 0`, T-Zero gives $`\vdash 0:\mathsf{Nat}`. For $`\mathsf{pred}\ (\mathsf{succ}\ nv_1)\to nv_1`, Lemma 24.1(d) also gives $`\vdash\mathsf{succ}\ nv_1:\mathsf{Nat}`, and applied once more it gives $`\vdash nv_1:\mathsf{Nat}`.

*E-IszeroZero, E-IszeroSucc.* Let $`\vdash t:T`. Lemma 24.1(e) gives $`T=\mathsf{Bool}`. The result $`\mathsf{true}` or $`\mathsf{false}` has type Bool by T-True or T-False.

This proves $`Q(E)` for every $`E`. Apply it at the given $`T`. $`\square`

Progress inducts on the typing derivation, because it starts from a typing and must produce a step. Preservation inducts on the evaluation derivation, because it starts from a step.

# Safety and the safety table
%%%
tag := "ch24-s4"
%%%

On the path $`t\to\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ \mathsf{succ}\ 0\ \mathsf{else}\ 0\to\mathsf{succ}\ 0` every term has type Nat, and only the last is a value. *Type safety* says that this always happens: a well-typed term never reaches a stuck term. [C.8](lambda-card/index.html#lambda-c8) states it, before Session 30, as follows. If $`\vdash t:T` and $`t\to^*t'`, then $`t'` is a value or $`t'\to t''` for some term $`t''`.

For the proof, fix $`T` and show $`\vdash t':T` by induction on the path $`\pi:t\to^*t'` ([A.6](imp-card/index.html#imp-a6)), with $`R(\pi)\coloneqq(\vdash t:T)\Rightarrow(\vdash t':T)`. A path of zero steps has $`t'=t`. A path with first step $`t\to r` and tail $`\pi':r\to^*t'` gives $`\vdash r:T` by Theorem 24.4, and then $`R(\pi')` gives $`\vdash t':T`. Theorem 24.3 applied to $`\vdash t':T` finishes the proof. Progress alone does not suffice. It speaks about a typed term, and only preservation makes the next term typed again.

*The safety table.* Sessions 24–31 record their safety proofs in one table, C.8. The table has one row per group of constructs. A row names the session that adds it and has three entries. The canonical-forms entry has one statement per type of the row. The progress entry has one case per typing rule, as in the proof of Theorem 24.3, and names the evaluation rules that supply the step. The preservation entry has one case per evaluation rule, as in the proof of Theorem 24.4, and names each lemma used besides inversion and the induction hypothesis. This session writes the first row.

*Row 1 · Booleans and natural numbers · Session 24.*

* *Canonical forms.* If $`v` is a value and $`\vdash v:\mathsf{Bool}`, then $`v=\mathsf{true}` or $`v=\mathsf{false}`. If $`v` is a value and $`\vdash v:\mathsf{Nat}`, then $`v` is a numeric value $`nv`.
* *Progress.* T-True, T-False, T-Zero: the term is a value. T-Succ: $`\mathsf{succ}\ t_1` is a value or steps by E-Succ. T-If: steps by E-If, E-IfTrue or E-IfFalse. T-Pred: steps by E-Pred, E-PredZero or E-PredSucc. T-IsZero: steps by E-IsZero, E-IszeroZero or E-IszeroSucc.
* *Preservation.* E-IfTrue, E-IfFalse, E-PredZero, E-PredSucc, E-IszeroZero, E-IszeroSucc: no lemma. E-If, E-Succ, E-Pred, E-IsZero: premise.

In the preservation entry, “no lemma” means that the case uses only inversion of typing (here Lemma 24.1) and a typing rule. “Premise” means that the case applies the induction hypothesis to the evaluation premise and rebuilds the typing with the same rule. From Session 30 every preservation entry also names a store typing, and C.8 lists Row 1 in that form.

Later sessions add rows: functions and Unit (Session 26), products and sums (Session 27), let (Session 29), references (Session 30), and universal and existential types (Session 31, statements only). A new row can add forms of value. Each earlier canonical-forms statement then gains a case. For example, from Session 26 an abstraction is a value, and the proof of Lemma 24.2(a) must also show that no abstraction has type Bool. C.8 states preservation for every typing context $`\Gamma` ([C.3](lambda-card/index.html#lambda-c3)). The rules of C.2 do not inspect $`\Gamma`, so the proof of Theorem 24.4 works for every $`\Gamma` without change.

# Exercises
%%%
tag := "ch24-s5"
number := false
%%%

*24.1.* Reduce $`\mathsf{if}\ \mathsf{iszero}\ (\mathsf{pred}\ (\mathsf{succ}\ 0))\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0` to a value. For each step, list the rules of its derivation and give the type of the term reached.

*24.2.* Give a conditional that has no type but steps to a numeric value. Name the typing premise that fails. Does the example contradict Theorem 24.3 or Theorem 24.4?

*24.3.* Remove the premise $`\vdash t_1:\mathsf{Bool}` from T-If and keep every other rule. (a) Give a type for $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}`. (b) Which theorem fails? At which numbered step does the board case break? (c) Does Theorem 24.4 still hold?

*24.4.* Write the E-If case of Theorem 24.4 as numbered steps, in the style of the board case. Write $`Q(E_1)` as a formula and name the type at which you apply it.

*Further problem.* Keep the rules of C.2 and add the rule $`\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\to\mathsf{true}`. Give a well-typed term for which preservation fails. Does progress still hold? Is one-step evaluation still deterministic, in the sense of [Session 23, Theorem 23.1](chapter-23/index.html#ch23-s2): at most one $`t'` with $`t\to t'` for each $`t`?

# Reading for the Seminar
%%%
tag := "ch24-s6"
number := false
%%%

*Definitions · 10 minutes.* Classify $`\mathsf{true}`, $`\mathsf{iszero}\ (\mathsf{pred}\ 0)` and $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` as a value, a term that steps, or a stuck term. Draw the typing derivation of the opening example.

*Joint proof · 30 minutes.* Prove Lemma 24.2(a) from the list of values. Then present the T-If case of progress in five steps, marking the step where Lemma 24.2 applies.

*Proof review · 20 minutes.* Do Exercise 24.3 and locate the broken step. Contrast it with Exercise 24.2, where a branch that evaluation discards is ill typed. Write Row 1 of the safety table on the board.

*Facilitator’s hint.* The induction hypothesis for the guard is a disjunction. Only its value branch permits the use of canonical forms.

# Solutions and Further Reading
%%%
tag := "ch24-s7"
number := false
%%%

*24.1.* There are three steps.

1. $`\mathsf{pred}\ (\mathsf{succ}\ 0)\to 0` by E-PredSucc, lifted by E-IsZero and then E-If. The term reached is $`\mathsf{if}\ \mathsf{iszero}\ 0\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0`.
2. $`\mathsf{iszero}\ 0\to\mathsf{true}` by E-IszeroZero, lifted by E-If. The term reached is $`\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0`.
3. E-IfTrue gives $`0`.

Every term on the path has type Nat, and every guard on it has type Bool.

*24.2.* $`\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{false}\to 0` by E-IfTrue. T-If needs both branches at one type, but by Lemma 24.1 the term $`0` has only type Nat and $`\mathsf{false}` only type Bool. Neither theorem is contradicted, since both assume $`\vdash t:T`. The example shows that the typing rules reject some terms that evaluate to a value.

*24.3.* (a) T-True, T-False and the reduced T-If give $`\vdash\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}:\mathsf{Bool}`. (b) Progress fails, because this well-typed term is stuck. The board case breaks at step 2. The hypothesis $`P(D_1)` belongs to the premise $`D_1:\ \vdash t_1:\mathsf{Bool}`, which no longer exists, so nothing says that the guard is a value or steps. Step 4 breaks as well: even when the guard is a value, as $`0` is here, Lemma 24.2(a) needs $`\vdash t_1:\mathsf{Bool}`. (c) Yes. In the case E-If, T-If is rebuilt from $`\vdash t_2:T` and $`\vdash t_3:T` alone, and the new guard needs no type. The other cases do not use the removed premise.

*24.4.* Suppose $`E` ends with E-If.

1. Then $`t=\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3`, $`t'=\mathsf{if}\ t_1'\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3`, and the premise is $`E_1:t_1\to t_1'` with $`Q(E_1):\forall S,\ (\vdash t_1:S)\Rightarrow(\vdash t_1':S)`.
2. Fix $`T` and assume $`\vdash t:T`. We must show $`\vdash t':T`.
3. Lemma 24.1(b) gives $`\vdash t_1:\mathsf{Bool}`, $`\vdash t_2:T` and $`\vdash t_3:T`.
4. Apply $`Q(E_1)` at $`S=\mathsf{Bool}` to $`\vdash t_1:\mathsf{Bool}`. This gives $`\vdash t_1':\mathsf{Bool}`.
5. T-If, applied to $`\vdash t_1':\mathsf{Bool}`, $`\vdash t_2:T` and $`\vdash t_3:T`, gives $`\vdash t':T`.

*Further problem.* Take $`t=\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0`. T-If gives $`\vdash t:\mathsf{Nat}`. The new rule gives $`t\to\mathsf{true}`, and $`\mathsf{true}` has only type Bool by Lemma 24.1(a). Preservation requires every step from a well-typed term to keep its type, so this one step refutes it. E-IfTrue still gives $`t\to 0`. Since $`0\neq\mathsf{true}`, the term has two different successors, and one-step evaluation is no longer deterministic. Progress still holds. The proof of Theorem 24.3 uses only rules of C.2, and all of them are still present. Progress asks for some step, not for a unique step or a typed result.

*Further reading · Two inductions.* TAPL §8.3 proves preservation by induction on the typing derivation. Induction on the evaluation derivation, used here, works as well. This chapter uses it because the preservation entries of the safety table have one case per evaluation rule.

*Further reading · Uniqueness of types.* Every term of C.2 has at most one type. The proof is by structural induction on the term, using Lemma 24.1 at each form; TAPL §8.2 gives it. Theorems 24.3–24.4 do not use it. It fails for the unannotated terms of [C.5](lambda-card/index.html#lambda-c5), where $`\vdash\lambda x.x:\mathsf{Nat}\to\mathsf{Nat}` and $`\vdash\lambda x.x:X\to X`.

# Sources and Formalization
%%%
tag := "ch24-notes"
number := false
%%%

Pierce, _Types and Programming Languages_ (TAPL). The terms, values and evaluation rules of C.2 are those of §§3.2 and 3.5, and the types and typing rules are those of §§8.1–8.2. TAPL writes the typing judgment of this language without a context. With the empty context the rules are the same. [Source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

* *Lemma 24.1.* Source: TAPL §8.2. Paper proof only ([§24.2](chapter-24/index.html#ch24-s2)).
* *Lemma 24.2.* Source: TAPL §8.3. Paper proof only ([§24.2](chapter-24/index.html#ch24-s2)).
* *Theorem 24.3.* Source: TAPL §8.3. Paper proof only ([§24.3](chapter-24/index.html#ch24-s3)).
* *Theorem 24.4.* Source: TAPL §8.3. Paper proof only ([§24.3](chapter-24/index.html#ch24-s3)).
