import VersoManual

open Verso.Genre Manual

#doc (Manual) "Progress and Preservation for Functions" =>
%%%
tag := "ch26"
file := "chapter-26"
%%%

* *Definitions.* The typed language of Session 26: the terms, values, evaluation rules and typing rules of the [Lambda language card C.2–C.3](lambda-card/index.html#lambda-c2). Closed terms, alpha-equivalence, substitution $`[x\mapsto s]t`, normal forms and $`\to^*` ([C.1](lambda-card/index.html#lambda-c1)). Stuck terms ([C.2](lambda-card/index.html#lambda-c2)). Typing contexts and $`\mathrm{dom}(\Gamma)` ([C.3](lambda-card/index.html#lambda-c3)). The counted path $`t\to^n t'`, read as in [A.6](imp-card/index.html#imp-a6). The safety statements, the form of the safety table and its Row 1 ([C.8](lambda-card/index.html#lambda-c8), Session 24). The substitution lemma ([Session 25](chapter-25/index.html)). Inversion and induction on derivations ([Session 1, §1.4](chapter-01/index.html#ch01-s4); [Session 3, §3.1](chapter-03/index.html#ch03-s1)).
* *New terms.* Domain and codomain of a function type. [Glossary and label key](glossary/index.html)
* *Theorem 26.3 \[Paper proof only: §§26.2–26.3\].* (a) Progress: for every term $`t` and type $`T`, if $`\vdash t:T`, then $`t` is a value or there is a term $`t'` with $`t\to t'`. (b) Preservation: for every context $`\Gamma`, terms $`t,t'` and type $`T`, if $`\Gamma\vdash t:T` and $`t\to t'`, then $`\Gamma\vdash t':T`.
* *Source.* Benjamin C. Pierce, _Types and Programming Languages_ (TAPL), §9.3. Pierce proves inversion, canonical forms, progress and preservation for functions with Booleans. Our typed language also has the natural numbers, whose cases are those of TAPL §8.3 and Session 24, and Unit (TAPL §11.2), whose cases are immediate. [Table of contents.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)
* *Board case.* Preservation for a step by E-AppAbs. Invert T-App and then T-Abs, identify the argument type with the parameter type, and apply the substitution lemma of Session 25 to the body and the argument.
* *Proof outline.* Progress: induction on the typing derivation $`D:\Gamma\vdash t:T` with $`P(D)\coloneqq(\Gamma=\varnothing)\Rightarrow\bigl(t\text{ is a value}\vee\exists t',\ t\to t'\bigr)`. The T-App case uses canonical forms (Lemma 26.2). Preservation: induction on the evaluation derivation $`E:t\to t'` with $`Q(E)\coloneqq\forall\Gamma\,\forall T,\ (\Gamma\vdash t:T)\Rightarrow(\Gamma\vdash t':T)`. The congruence cases apply the induction hypothesis at the function type or at its domain. The computation case E-AppAbs uses the substitution lemma.
* *From Session 25.* Session 25 proved that substituting a term of type $`S` for a variable of type $`S` keeps the type. Here that lemma types the result of E-AppAbs. Session 24 proved progress and preservation for Booleans and natural numbers in the empty context. Here the language has functions and Unit, and preservation holds in every context.

Let $`\mathit{inc}=\lambda z{:}\mathsf{Nat}.\mathsf{succ}\ z`. The term $`(\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.f)\ \mathit{inc}\ (\mathsf{pred}\ (\mathsf{succ}\ 0))` has type Nat. It takes three steps and ends at the value $`\mathsf{succ}\ 0`. Every term on the way has type Nat. This session proves that this is no accident: a closed well-typed term is a value or takes a step, and a step keeps the type. The last of the three steps is the delicate one. An application disappears, and the body of $`\mathit{inc}` appears with the argument in place of the parameter. The type of the new term is rebuilt by the substitution lemma of Session 25.

# Functions in the typed language
%%%
tag := "ch26-s1"
%%%

The typed language of this session consists of the Booleans and natural numbers of [C.2](lambda-card/index.html#lambda-c2) and the functions and Unit of [C.3](lambda-card/index.html#lambda-c3). Its values are $`\mathsf{true}`, $`\mathsf{false}`, the numeric values $`nv`, the abstractions $`\lambda x{:}T.t` and $`\mathsf{unit}`. The typing rules for the new forms are

$$`\frac{x{:}T\in\Gamma}{\Gamma\vdash x:T}\;\textsf{T-Var}\qquad\frac{\Gamma,x{:}T_1\vdash t_2:T_2}{\Gamma\vdash\lambda x{:}T_1.t_2:T_1\to T_2}\;\textsf{T-Abs}\qquad\frac{\Gamma\vdash t_1:T_{11}\to T_{12}\quad\Gamma\vdash t_2:T_{11}}{\Gamma\vdash t_1\,t_2:T_{12}}\;\textsf{T-App}\qquad\frac{}{\Gamma\vdash\mathsf{unit}:\mathsf{Unit}}\;\textsf{T-Unit}`

and the evaluation rules for application are

$$`\frac{t_1\to t_1'}{t_1\,t_2\to t_1'\,t_2}\;\textsf{E-App1}\qquad\frac{t_2\to t_2'}{v_1\,t_2\to v_1\,t_2'}\;\textsf{E-App2}\qquad\frac{}{(\lambda x{:}T_{11}.t_{12})\,v_2\to[x\mapsto v_2]t_{12}}\;\textsf{E-AppAbs}`

The operand is evaluated only after the operator is a value. A redex is contracted only when its operand is a value. No rule steps inside an abstraction, but T-Abs types its body.

Write $`t_0` for the opening term. By the rules for parentheses of the card it is $`((\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.f)\ \mathit{inc})\ (\mathsf{pred}\ (\mathsf{succ}\ 0))`. Its three steps are as follows.

1. $`t_0\to\mathit{inc}\ (\mathsf{pred}\ (\mathsf{succ}\ 0))` by E-App1. The premise $`(\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.f)\ \mathit{inc}\to[f\mapsto\mathit{inc}]f=\mathit{inc}` is an instance of E-AppAbs, since $`\mathit{inc}` is a value.
2. $`\mathit{inc}\ (\mathsf{pred}\ (\mathsf{succ}\ 0))\to\mathit{inc}\ 0` by E-App2, since the operator $`\mathit{inc}` is a value. The premise $`\mathsf{pred}\ (\mathsf{succ}\ 0)\to 0` is an instance of E-PredSucc.
3. $`\mathit{inc}\ 0\to[z\mapsto 0](\mathsf{succ}\ z)=\mathsf{succ}\ 0` by E-AppAbs.

Each of the four terms has type Nat in the empty context. Compare the typing derivations before and after step 3:

$$`\dfrac{\dfrac{\dfrac{\dfrac{z{:}\mathsf{Nat}\in z{:}\mathsf{Nat}}{z{:}\mathsf{Nat}\vdash z:\mathsf{Nat}}\;\textsf{T-Var}}{z{:}\mathsf{Nat}\vdash\mathsf{succ}\ z:\mathsf{Nat}}\;\textsf{T-Succ}}{\vdash\mathit{inc}:\mathsf{Nat}\to\mathsf{Nat}}\;\textsf{T-Abs}\qquad\dfrac{}{\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}}{\vdash\mathit{inc}\ 0:\mathsf{Nat}}\;\textsf{T-App}\qquad\qquad\dfrac{\dfrac{}{\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}}{\vdash\mathsf{succ}\ 0:\mathsf{Nat}}\;\textsf{T-Succ}`

The right derivation is not a subderivation of the left one. It is the body derivation $`z{:}\mathsf{Nat}\vdash\mathsf{succ}\ z:\mathsf{Nat}` with $`z` replaced by $`0`, the binding $`z{:}\mathsf{Nat}` removed, and the T-Var leaf replaced by the derivation of $`\vdash 0:\mathsf{Nat}`. The substitution lemma performs this rebuilding for every body and every argument.

A proof about all typed terms cannot look at one particular derivation. It reads the premises off the conclusion by inversion. Below the left derivation, the term $`\mathit{inc}\ 0` is an application, so the last rule must be T-App. Its premises give $`\mathit{inc}` a function type and $`0` the matching argument type. The abstraction $`\mathit{inc}` is typed by T-Abs, whose premise types the body under $`z{:}\mathsf{Nat}`.

*Lemma 26.1 (Inversion for functions) \[Paper proof only: proof in this section\].* For every context $`\Gamma` and type $`T`:

1. If $`\Gamma\vdash x:T`, then $`x{:}T\in\Gamma`.
2. If $`\Gamma\vdash\lambda x{:}T_1.t_2:T` and $`x\notin\mathrm{dom}(\Gamma)`, then $`T=T_1\to T_2` for some type $`T_2` with $`\Gamma,x{:}T_1\vdash t_2:T_2`.
3. If $`\Gamma\vdash t_1\,t_2:T`, then there is a type $`U` with $`\Gamma\vdash t_1:U\to T` and $`\Gamma\vdash t_2:U`.
4. If $`\Gamma\vdash\mathsf{unit}:T`, then $`T=\mathsf{Unit}`.

*Proof.* Each of the four term forms is the conclusion form of exactly one typing rule of C.2–C.3: T-Var, T-Abs, T-App and T-Unit respectively. So a derivation of the judgment ends with that rule, and each claim reads off its premises and its conclusion. In (3), $`U` is the type $`T_{11}` of that instance of T-App. In (2), the convention of C.3 renames the parameter when necessary, so we may assume $`x\notin\mathrm{dom}(\Gamma)`. $`\square`

For a function type $`T_1\to T_2`, call $`T_1` its *domain* and $`T_2` its *codomain*. Types are syntax trees. So $`T_1\to T_2=S_1\to S_2` holds only when $`T_1=S_1` and $`T_2=S_2`, and a function type is never Bool, Nat or Unit.

# Canonical forms and progress
%%%
tag := "ch26-s2"
%%%

The closed term $`(\mathsf{succ}\ 0)\ 0` is stuck. E-App1 and E-App2 do not apply, because both subterms are values and values do not step. E-AppAbs does not apply, because the operator is not an abstraction. The term has no type: by Lemma 26.1(3) its operator would need a type $`U\to T`, but the only rule for $`\mathsf{succ}` gives Nat. Progress must exclude terms like this one. Its application case needs to know that a value of a function type is an abstraction.

*Lemma 26.2 (Canonical forms) \[Paper proof only: proof in this section\].* Let $`v` be a value.

1. If $`\vdash v:T_1\to T_2`, then $`v=\lambda x{:}T_1.t_2` for some $`x` and $`t_2`.
2. If $`\vdash v:\mathsf{Unit}`, then $`v=\mathsf{unit}`.
3. If $`\vdash v:\mathsf{Bool}`, then $`v=\mathsf{true}` or $`v=\mathsf{false}`. If $`\vdash v:\mathsf{Nat}`, then $`v` is a numeric value.

*Proof.* A value is $`\mathsf{true}`, $`\mathsf{false}`, a numeric value, an abstraction or $`\mathsf{unit}`. A derivation for one of these forms ends with T-True, T-False, T-Zero or T-Succ, T-Abs, or T-Unit, respectively. Their conclusions give the type Bool, Bool, Nat, a function type and Unit. These types are distinct. So a value of type $`T_1\to T_2` is an abstraction $`\lambda x{:}T_1'.t_2`, and by Lemma 26.1(2) its type is $`T_1'\to T_2'` for some $`T_2'`. Comparing domains gives $`T_1'=T_1`. A value of type Unit is $`\mathsf{unit}`. Part 3 is the canonical forms statement of Session 24. Its proof now also excludes an abstraction and $`\mathsf{unit}`, whose types are a function type and Unit. $`\square`

*Theorem 26.3 (Progress and preservation) \[Paper proof only: §§26.2–26.3\].*

* (a) Progress. For every term $`t` and type $`T`: if $`\vdash t:T`, then $`t` is a value or there is a term $`t'` with $`t\to t'`.
* (b) Preservation. For every context $`\Gamma`, terms $`t,t'` and type $`T`: if $`\Gamma\vdash t:T` and $`t\to t'`, then $`\Gamma\vdash t':T`.

*Proof of (a).* We prove $`P(D)` for every typing derivation $`D:\Gamma\vdash t:T` by induction on $`D`, where

$$`P(D)\coloneqq(\Gamma=\varnothing)\Rightarrow\bigl(t\text{ is a value}\ \vee\ \exists t',\ t\to t'\bigr).`

Statement (a) is $`P(D)` for a derivation $`D` of $`\vdash t:T`. The context is not fixed in the induction, because the premise of T-Abs has the context $`\Gamma,x{:}T_1`.

*T-Var.* Then $`t=x` and $`x{:}T\in\Gamma`. The empty context has no binding, so $`\Gamma\neq\varnothing`. The premise of $`P(D)` is false, and $`P(D)` holds.

*T-Abs and T-Unit.* The term is a value. The hypothesis for the body of an abstraction is not needed, and its context is not empty.

*T-App.* Then $`t=t_1\,t_2` and $`T=T_{12}`, with premises $`D_1:\Gamma\vdash t_1:T_{11}\to T_{12}` and $`D_2:\Gamma\vdash t_2:T_{11}`. The induction hypotheses are

$$`\begin{aligned}
P(D_1)&:\quad(\Gamma=\varnothing)\Rightarrow\bigl(t_1\text{ is a value}\ \vee\ \exists t_1',\ t_1\to t_1'\bigr),\\
P(D_2)&:\quad(\Gamma=\varnothing)\Rightarrow\bigl(t_2\text{ is a value}\ \vee\ \exists t_2',\ t_2\to t_2'\bigr).
\end{aligned}`

Assume $`\Gamma=\varnothing`. Both premises have the context $`\Gamma`, so both hypotheses apply.

1. If $`t_1\to t_1'` for some $`t_1'`, then $`t_1\,t_2\to t_1'\,t_2` by E-App1.
2. Otherwise $`t_1` is a value by $`P(D_1)`. If $`t_2\to t_2'` for some $`t_2'`, then $`t_1\,t_2\to t_1\,t_2'` by E-App2.
3. Otherwise $`t_2` is a value by $`P(D_2)`. Lemma 26.2(1) applied to $`D_1` gives $`t_1=\lambda x{:}T_{11}.t_{12}` for some $`x` and $`t_{12}`. Then $`t_1\,t_2\to[x\mapsto t_2]t_{12}` by E-AppAbs.

*Rules of C.2.* These are the progress cases of Row 1 ([C.8](lambda-card/index.html#lambda-c8)), proved in Session 24. The guard of a conditional and the argument of $`\mathsf{succ}`, $`\mathsf{pred}` and $`\mathsf{iszero}` are typed in the same context $`\Gamma`, so their hypotheses apply. The canonical forms they use are Lemma 26.2(3). $`\square`

Only the T-Var case needs the assumption $`\Gamma=\varnothing` to reach its conclusion. The other cases pass it on to premises with the same context, and the T-App case also uses it to apply Lemma 26.2, which is stated for the empty context. The assumption cannot be dropped. We have $`x{:}\mathsf{Nat}\to\mathsf{Nat}\vdash x\ 0:\mathsf{Nat}` by T-App, and $`x\ 0` is neither a value nor able to step. In its T-App case, the hypothesis for the operator $`x` has a false premise, so it does not say that $`x` is a value or steps.

# Preservation
%%%
tag := "ch26-s3"
%%%

*Proof of Theorem 26.3(b).* We prove $`Q(E)` for every evaluation derivation $`E:t\to t'` by induction on $`E`, where

$$`Q(E)\coloneqq\forall\Gamma\,\forall T,\ (\Gamma\vdash t:T)\Rightarrow(\Gamma\vdash t':T).`

Read $`t` and $`t'` from the conclusion of $`E`. Both $`\Gamma` and $`T` are quantified inside $`Q(E)`. The congruence cases apply the hypothesis at a type other than $`T`.

The computation case uses the substitution lemma of [Session 25](chapter-25/index.html). For every context $`\Gamma`, variable $`x\notin\mathrm{dom}(\Gamma)`, terms $`u,s` and types $`S,T`:

$$`\text{if}\quad\Gamma,x{:}S\vdash u:T\quad\text{and}\quad\Gamma\vdash s:S,\quad\text{then}\quad\Gamma\vdash[x\mapsto s]u:T.`

*E-AppAbs (board case).* Suppose $`E` ends with E-AppAbs. Then $`t=(\lambda x{:}T_{11}.t_{12})\,v_2` and $`t'=[x\mapsto v_2]t_{12}`. The rule has no evaluation premise, so there is no induction hypothesis. Fix $`\Gamma` and $`T` and assume

$$`D:\quad\Gamma\vdash(\lambda x{:}T_{11}.t_{12})\,v_2:T.`

Rename the parameter $`x` if necessary so that $`x\notin\mathrm{dom}(\Gamma)`. Up to alpha-equivalence this changes neither $`t` nor $`t'`. We must show $`\Gamma\vdash[x\mapsto v_2]t_{12}:T`.

1. Apply Lemma 26.1(3) to $`D`. There is a type $`U` with (i) $`\Gamma\vdash\lambda x{:}T_{11}.t_{12}:U\to T` and (ii) $`\Gamma\vdash v_2:U`.
2. Apply Lemma 26.1(2) to (i). There is a type $`T_{12}` with $`U\to T=T_{11}\to T_{12}` and (iii) $`\Gamma,x{:}T_{11}\vdash t_{12}:T_{12}`.
3. Compare the domains and the codomains in $`U\to T=T_{11}\to T_{12}`. This gives $`U=T_{11}` and $`T=T_{12}`. So (ii) is $`\Gamma\vdash v_2:T_{11}`, and (iii) is $`\Gamma,x{:}T_{11}\vdash t_{12}:T`.
4. Apply the substitution lemma with $`S\coloneqq T_{11}`, $`u\coloneqq t_{12}` and $`s\coloneqq v_2`. Its premises are (iii) and (ii) in the form of step 3. Its conclusion is $`\Gamma\vdash[x\mapsto v_2]t_{12}:T`, the goal.

Inversion types only the body $`t_{12}`, and only under the extra binding $`x{:}T_{11}`. The type of the result comes from the substitution lemma, not from a subderivation of $`D`. Step 4 does not use that $`v_2` is a value. E-AppAbs demands a value to fix when a redex is contracted. The substitution lemma accepts any term of the right type.

In step 3 of §26.1, the case reads $`\Gamma=\varnothing`, $`T_{11}=\mathsf{Nat}`, $`t_{12}=\mathsf{succ}\ z` and $`v_2=0`. Step 2 gives $`T_{12}=\mathsf{Nat}` and $`z{:}\mathsf{Nat}\vdash\mathsf{succ}\ z:\mathsf{Nat}`, and step 4 gives $`\vdash\mathsf{succ}\ 0:\mathsf{Nat}`.

The result of E-AppAbs may be larger than the redex and may contain a new redex. Take

$$`(\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\lambda y{:}\mathsf{Nat}.f\ y)\ \mathit{inc}\to\lambda y{:}\mathsf{Nat}.\mathit{inc}\ y.`

Here $`T_{11}=\mathsf{Nat}\to\mathsf{Nat}`, $`t_{12}=\lambda y{:}\mathsf{Nat}.f\ y` and $`v_2=\mathit{inc}`. Steps 2 and 3 give $`f{:}\mathsf{Nat}\to\mathsf{Nat}\vdash\lambda y{:}\mathsf{Nat}.f\ y:\mathsf{Nat}\to\mathsf{Nat}` and $`T=\mathsf{Nat}\to\mathsf{Nat}`. Step 4 gives $`\vdash\lambda y{:}\mathsf{Nat}.\mathit{inc}\ y:\mathsf{Nat}\to\mathsf{Nat}`. The result is a value. Its body contains the redex $`\mathit{inc}\ y`, which is contracted only after the function is applied. Inside the proof of the substitution lemma, the step under the binder $`y` uses weakening to type $`\mathit{inc}` in the context $`y{:}\mathsf{Nat}` (Session 25).

*E-App1.* Suppose $`E` ends with E-App1. Then $`t=t_1\,t_2` and $`t'=t_1'\,t_2`, and the premise is $`E_1:t_1\to t_1'` with

$$`Q(E_1):\quad\forall\Gamma'\,\forall S,\ (\Gamma'\vdash t_1:S)\Rightarrow(\Gamma'\vdash t_1':S).`

Fix $`\Gamma` and $`T` and assume $`\Gamma\vdash t_1\,t_2:T`. Lemma 26.1(3) gives a type $`U` with $`\Gamma\vdash t_1:U\to T` and $`\Gamma\vdash t_2:U`. Apply $`Q(E_1)` with $`\Gamma'\coloneqq\Gamma` and $`S\coloneqq U\to T`. This gives $`\Gamma\vdash t_1':U\to T`. T-App gives $`\Gamma\vdash t_1'\,t_2:T`.

*E-App2.* As for E-App1, with the hypothesis applied at the domain $`U` (Exercise 26.2).

*Rules of C.2.* These are the preservation cases of Row 1 ([C.8](lambda-card/index.html#lambda-c8)), proved in Session 24. No typing rule of C.2 inspects the context, so the arbitrary $`\Gamma` is carried through unchanged. $`\square`

# Safety and the safety table
%%%
tag := "ch26-s4"
%%%

The run of $`t_0` in §26.1 never met a stuck term. Theorem 26.3 says that no run of a closed well-typed term does.

*Corollary 26.4 (Safety) \[This book\] \[Paper proof only: proof in this section\].* For all terms $`t,t'` and every type $`T`: if $`\vdash t:T` and $`t\to^*t'`, then $`\vdash t':T`, and $`t'` is a value or there is a term $`t''` with $`t'\to t''`.

*Proof.* Fix $`T`. By induction on the natural number $`n` we prove

$$`R(n)\coloneqq\forall t\,\forall t',\ \bigl(\vdash t:T\ \wedge\ t\to^n t'\bigr)\Rightarrow\ \vdash t':T.`

$`R(0)` holds because $`t\to^0 t'` means $`t'=t`. Assume $`R(n)`, and let $`t\to t_1` and $`t_1\to^n t'`. Theorem 26.3(b) with $`\Gamma=\varnothing` gives $`\vdash t_1:T`, and $`R(n)` gives $`\vdash t':T`. So $`R(n+1)` holds. Finally, $`t\to^*t'` means $`t\to^n t'` for some $`n`, and Theorem 26.3(a) applied to $`\vdash t':T` gives the last claim. $`\square`

The proof uses only the two parts of Theorem 26.3. Each later row of the safety table therefore needs only its own cases of progress and preservation.

The cases proved in this session form Row 2 of the safety table. In the form of [C.8](lambda-card/index.html#lambda-c8), without stores, the row reads as follows.

*Row 2 · Functions and Unit · Session 26.*

* *Canonical forms.* If $`v` is a value and $`\vdash v:T_1\to T_2`, then $`v=\lambda x{:}T_1.t_2` for some $`x` and $`t_2`. If $`v` is a value and $`\vdash v:\mathsf{Unit}`, then $`v=\mathsf{unit}`.
* *Progress.* T-Var: no derivation of $`\vdash x:T` exists. T-Abs, T-Unit: the term is a value. T-App: steps by E-App1, E-App2 or E-AppAbs.
* *Preservation.* E-AppAbs: uses the substitution lemma of Session 25. E-App1, E-App2: premise.

“Premise” means that the case follows from the induction hypothesis for the evaluation premise, with Lemma 26.1(3) and T-App. Adding Row 2 changes Row 1 in two places. Its canonical forms for Bool and Nat must now exclude the new values $`\lambda x{:}T_1.t_2` and $`\mathsf{unit}`, as in the proof of Lemma 26.2. Its preservation cases are now read in an arbitrary context $`\Gamma`.

# Exercises
%%%
tag := "ch26-s5"
number := false
%%%

*26.1.* Derive $`\vdash(\lambda f{:}\mathsf{Unit}\to\mathsf{Unit}.f\ \mathsf{unit})\ (\lambda z{:}\mathsf{Unit}.z):\mathsf{Unit}`. Derive its two steps, name the rule of each, and give the type of each term.

*26.2.* Write the E-App2 case of preservation in the style of the E-App1 case. At which type is the induction hypothesis applied? Is it used that the operator $`v_1` is a value?

*26.3.* Show $`x{:}\mathsf{Nat}\vdash(\lambda y{:}\mathsf{Nat}.y)\ (\mathsf{succ}\ x):\mathsf{Nat}`, and show that this term is neither a value nor able to step. Which case of the proof of Theorem 26.3(a) would fail if $`P(D)` did not assume $`\Gamma=\varnothing`?

*26.4.* Add a constant $`\mathsf{bad}` that is a value, with $`\Gamma\vdash\mathsf{bad}:\mathsf{Nat}\to\mathsf{Nat}` for every $`\Gamma` and no evaluation rule. Which statement of this session becomes false? Give a closed well-typed stuck term.

*Further problem.* Add a constant $`\mathsf{loop}` that is not a value, with $`\Gamma\vdash\mathsf{loop}:\mathsf{Unit}` for every $`\Gamma` and the rule $`\mathsf{loop}\to\mathsf{loop}`. Check progress and preservation. Give a closed well-typed application whose evaluation never reaches a value.

# Reading for the Seminar
%%%
tag := "ch26-s6"
number := false
%%%

*Definitions · 10 minutes.* Write T-Abs, T-App, E-AppAbs and the substitution lemma of Session 25. Draw the two derivations of §26.1, for $`\mathit{inc}\ 0` and for $`\mathsf{succ}\ 0`.

*Joint proof · 30 minutes.* Start from a typing of the redex $`(\lambda x{:}T_{11}.t_{12})\,v_2` at an unknown type $`T`. Invert twice, identify $`U` with $`T_{11}` and $`T_{12}` with $`T`, and instantiate the substitution lemma explicitly. Check the case on the example whose result is an abstraction.

*Proof review · 20 minutes.* Prove the T-App case of progress. Then add the constant of Exercise 26.4 and show which line of that case fails.

*Facilitator’s hint.* Ask which result provides a typing for the substituted body. Inversion types only the original body, under the extra binding $`x{:}T_{11}`.

# Solutions and Further Reading
%%%
tag := "ch26-s7"
number := false
%%%

*26.1.* T-Var and T-Unit give $`f{:}\mathsf{Unit}\to\mathsf{Unit}\vdash f\ \mathsf{unit}:\mathsf{Unit}` by T-App, and T-Abs gives the operator the type $`(\mathsf{Unit}\to\mathsf{Unit})\to\mathsf{Unit}`. T-Var and T-Abs give $`\vdash\lambda z{:}\mathsf{Unit}.z:\mathsf{Unit}\to\mathsf{Unit}`. T-App gives the whole term the type Unit. The first step is by E-AppAbs, to $`(\lambda z{:}\mathsf{Unit}.z)\ \mathsf{unit}`, of type Unit. The second step is by E-AppAbs, to $`\mathsf{unit}`, of type Unit. This value is $`\mathsf{unit}`, as Lemma 26.2(2) requires.

*26.2.* Here $`t=v_1\,t_2`, $`t'=v_1\,t_2'`, and the premise is $`E_2:t_2\to t_2'` with $`Q(E_2):\forall\Gamma'\,\forall S,\ (\Gamma'\vdash t_2:S)\Rightarrow(\Gamma'\vdash t_2':S)`. Fix $`\Gamma` and $`T` and assume $`\Gamma\vdash v_1\,t_2:T`. Lemma 26.1(3) gives $`U` with $`\Gamma\vdash v_1:U\to T` and $`\Gamma\vdash t_2:U`. Apply $`Q(E_2)` with $`\Gamma'\coloneqq\Gamma` and $`S\coloneqq U`, the domain. This gives $`\Gamma\vdash t_2':U`, and T-App gives $`\Gamma\vdash v_1\,t_2':T`. The fact that $`v_1` is a value is not used.

*26.3.* In the context $`x{:}\mathsf{Nat}`, T-Var and T-Abs give $`\lambda y{:}\mathsf{Nat}.y` the type $`\mathsf{Nat}\to\mathsf{Nat}`, and T-Var and T-Succ give $`\mathsf{succ}\ x` the type Nat. T-App gives Nat. The term is an application, so it is not a value. E-App1 needs a step of the operator, which is a value. E-App2 needs a step of $`\mathsf{succ}\ x`, which needs a step of $`x` by E-Succ, and no rule steps a variable. E-AppAbs needs the operand to be a value, and $`\mathsf{succ}\ x` is not a numeric value. Without the assumption $`\Gamma=\varnothing`, the T-Var case would have to show that $`x` is a value or steps, and it is neither. In this term that case is reached through T-App, step 2, and then T-Succ.

*26.4.* Lemma 26.2(1) becomes false: $`\mathsf{bad}` is a value of type $`\mathsf{Nat}\to\mathsf{Nat}` that is not an abstraction. Step 3 of the T-App case of progress fails with it. The term $`\mathsf{bad}\ 0` has type Nat, is not a value, and cannot step: both subterms are values, and its operator is not an abstraction. Preservation is unaffected, because no evaluation rule was added.

*Further problem.* Preservation gains the case $`\mathsf{loop}\to\mathsf{loop}`. The only typing rule for $`\mathsf{loop}` gives Unit, and the target is the same term, so the typing is reused. The congruence cases are unchanged. In the substitution lemma the constant is a new case with no variables, so substitution leaves it unchanged. Progress gains the case of the new typing rule, which supplies the step $`\mathsf{loop}\to\mathsf{loop}`. The constant is not a value, so canonical forms are unchanged. Take $`(\lambda u{:}\mathsf{Unit}.\mathsf{unit})\ \mathsf{loop}`, of type Unit. Its operand is not a value, so E-AppAbs does not apply. Its only step is by E-App2 and returns the same term. By induction on $`n`, every $`t'` with $`(\lambda u{:}\mathsf{Unit}.\mathsf{unit})\ \mathsf{loop}\to^n t'` is that term, which is not a value. Progress and preservation therefore hold for a language with a nonterminating term. They do not say that evaluation terminates.

*Typing inspects code that evaluation never reaches.* The term $`(\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.0)\ (\lambda z{:}\mathsf{Nat}.z\ 0)` steps to $`0` by E-AppAbs and never gets stuck. It has no type. The operand needs $`z{:}\mathsf{Nat}\vdash z\ 0:T` for some $`T`, and Lemma 26.1(3) would require $`z` to have a function type, but T-Var gives Nat. With the operand $`\lambda z{:}\mathsf{Nat}.z` instead, the term has type Nat. Both terms take the same single step, and only the second is covered by Theorem 26.3. A well-typed closed term never reaches a stuck term. One run that does not get stuck is no evidence of a type.

*Closed instances of open terms.* Progress could also be stated for closed instances of open typed terms. The term $`x\ 0` with $`x{:}\mathsf{Nat}\to\mathsf{Nat}` cannot step, but its instance $`[x\mapsto\mathit{inc}](x\ 0)=\mathit{inc}\ 0` can. Such a statement needs, for each free variable, a closed value of its type to substitute.

*Normalization.* In the typed language of this session every closed well-typed term evaluates to a value. This is a separate theorem, proved by a different method (TAPL §12.1). Progress and preservation do not bound the number of steps, as the Further problem shows. TAPL §11.11 adds a typed fixed-point operator, which keeps safety and loses termination.

TAPL §9.3 proves the theorems of this session for functions with Booleans. TAPL §11.2 adds Unit. [Table of contents.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)
