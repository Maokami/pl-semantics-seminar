import VersoManual

open Verso.Genre Manual

#doc (Manual) "Products and Sums" =>
%%%
tag := "ch27"
file := "chapter-27"
%%%

* *Definitions.* The typed language of Session 27: the terms, values, evaluation rules and typing rules of [C.2–C.4](lambda-card/index.html#lambda-c4). Closed terms, alpha-equivalence, free variables, substitution $`[x\mapsto s]t`, normal forms and $`\to^*` ([C.1](lambda-card/index.html#lambda-c1)). Stuck terms ([C.2](lambda-card/index.html#lambda-c2)). Typing contexts and $`\mathrm{dom}(\Gamma)` ([C.3](lambda-card/index.html#lambda-c3)). The safety statements, the form of the safety table and Rows 1–2 ([C.8](lambda-card/index.html#lambda-c8)). Lemmas 25.1–25.4 and the substitution lemma, Theorem 25.5 ([Session 25](chapter-25/index.html)). Inversion, canonical forms, progress and preservation, and safety for functions: Lemmas 26.1–26.2, Theorem 26.3 and Corollary 26.4 ([Session 26](chapter-26/index.html)). Induction on derivations and on height ([Session 1, §1.5](chapter-01/index.html#ch01-s5); [Session 3, §3.1](chapter-03/index.html#ch03-s1)).
* *New terms.* Product type, sum type, summand, case term, Curry–Howard correspondence. [Glossary and label key](glossary/index.html)
* *Theorem 27.3 (Progress and preservation for products and sums).* For the typed language of Session 27: (a) Progress: for every term $`t` and type $`T`, if $`\vdash t:T`, then $`t` is a value or there is a term $`t'` with $`t\to t'`. (b) Preservation: for every context $`\Gamma`, terms $`t,t'` and type $`T`, if $`\Gamma\vdash t:T` and $`t\to t'`, then $`\Gamma\vdash t':T`.
* *Source.* Benjamin C. Pierce, _Types and Programming Languages_ (TAPL). The rules for pairs are those of §11.6. The rules for sums are those of §11.9, in the form with type annotations. TAPL proves progress and preservation for functions with Booleans in §9.3. Theorem 27.3 has the same form for a language with products and sums. §9.4 presents the Curry–Howard correspondence, the subject of §27.5. [Source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)
* *Board case.* Preservation for a step by E-CaseInl. Invert T-Case and then T-Inl, compare the left summands, and apply the substitution lemma to the left branch and the injected value.
* *Proof outline.* Progress: induction on the typing derivation $`D:\Gamma\vdash t:T` with $`P(D)\coloneqq(\Gamma=\varnothing)\Rightarrow\bigl(t\text{ is a value}\vee\exists t',\ t\to t'\bigr)`, as in Session 26. The cases T-Proj1, T-Proj2 and T-Case use the canonical forms of Lemma 27.2. Preservation: induction on the evaluation derivation $`E:t\to t'` with $`Q(E)\coloneqq\forall\Gamma\,\forall T,\ (\Gamma\vdash t:T)\Rightarrow(\Gamma\vdash t':T)`. The congruence cases apply the induction hypothesis at a component of a product, at a summand of a sum, at a product type or at a sum type. E-PairBeta1 and E-PairBeta2 use inversion only. E-CaseInl and E-CaseInr use the substitution lemma, extended to the new rules in Lemma 27.4.
* *From Session 26.* Session 26 proved progress and preservation for functions and Unit. Here the typed language gains two type constructors, the product $`T_1\times T_2` and the sum $`T_1+T_2`, and six term forms. Each form adds cases to the proofs of Session 26 and entries to a new row of the safety table. The case term binds variables, as an abstraction does, so the lemmas of Session 25 gain a binder case.

Let $`\mathit{main}=(\mathsf{case}\ (\mathsf{inl}\ (\mathsf{pred}\ (\mathsf{succ}\ 0))\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool})\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow\{x,\mathsf{iszero}\ x\}\mid\mathsf{inr}\ y\Rightarrow\{0,y\}).2`. The injection tags a number as the left alternative of the type $`\mathsf{Nat}+\mathsf{Bool}`. The case term reads the tag, selects the left branch, and builds a pair. The projection $`.2` takes the second component of the pair. The term has type Bool and reaches the value $`\mathsf{true}` in four steps. Now take $`(\lambda z{:}\mathsf{Nat}.z).2` and $`\mathsf{case}\ \{0,0\}\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow x\mid\mathsf{inr}\ y\Rightarrow y`. Neither is a value, and neither can step: a projection needs a pair, and a case term needs an injection. This session proves that a closed well-typed term never reaches such a term. The proof adds cases to the proofs of Session 26. The delicate step is the one that selects a branch. It replaces the bound variable of the branch by the injected value, and the substitution lemma rebuilds the type.

# Pairs and sums in the typed language
%%%
tag := "ch27-s1"
%%%

The typed language of this session consists of the forms of C.2, C.3 and [C.4](lambda-card/index.html#lambda-c4). C.4 adds two type constructors. The *product type* $`T_1\times T_2` is the type of a *pair* $`\{t_1,t_2\}` whose first component has type $`T_1` and whose second component has type $`T_2`. The *projections* $`t.1` and $`t.2` select the first and the second component of a pair. The *sum type* $`T_1+T_2` holds a term of type $`T_1` or of type $`T_2`, with a tag that says which. The tagged term is an *injection*, $`\mathsf{inl}\ t\ \mathsf{as}\ T_1+T_2` or $`\mathsf{inr}\ t\ \mathsf{as}\ T_1+T_2`. In $`T_1+T_2` we call $`T_1` the *left summand* and $`T_2` the *right summand*. The *case term* $`\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2` reads the tag of $`t_0` and continues with the left *branch* $`t_1` or the right branch $`t_2`. The variable $`x_1` is bound in $`t_1`, and $`x_2` is bound in $`t_2`. The typing rules are

$$`\frac{\Gamma\vdash t_1:T_1\quad\Gamma\vdash t_2:T_2}{\Gamma\vdash\{t_1,t_2\}:T_1\times T_2}\;\textsf{T-Pair}\qquad\frac{\Gamma\vdash t_1:T_{11}\times T_{12}}{\Gamma\vdash t_1.1:T_{11}}\;\textsf{T-Proj1}\qquad\frac{\Gamma\vdash t_1:T_{11}\times T_{12}}{\Gamma\vdash t_1.2:T_{12}}\;\textsf{T-Proj2}`

$$`\frac{\Gamma\vdash t_1:T_1}{\Gamma\vdash\mathsf{inl}\ t_1\ \mathsf{as}\ T_1+T_2:T_1+T_2}\;\textsf{T-Inl}\qquad\frac{\Gamma\vdash t_1:T_2}{\Gamma\vdash\mathsf{inr}\ t_1\ \mathsf{as}\ T_1+T_2:T_1+T_2}\;\textsf{T-Inr}`

$$`\frac{\Gamma\vdash t_0:T_1+T_2\quad\Gamma,x_1{:}T_1\vdash t_1:T\quad\Gamma,x_2{:}T_2\vdash t_2:T}{\Gamma\vdash\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2:T}\;\textsf{T-Case}`

and the computation rules are

$$`\frac{}{\{v_1,v_2\}.1\to v_1}\;\textsf{E-PairBeta1}\qquad\frac{}{\{v_1,v_2\}.2\to v_2}\;\textsf{E-PairBeta2}`

$$`\frac{}{\mathsf{case}\ (\mathsf{inl}\ v_0\ \mathsf{as}\ T_0)\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2\to[x_1\mapsto v_0]t_1}\;\textsf{E-CaseInl}`

$$`\frac{}{\mathsf{case}\ (\mathsf{inr}\ v_0\ \mathsf{as}\ T_0)\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2\to[x_2\mapsto v_0]t_2}\;\textsf{E-CaseInr}`

The congruence rules E-Pair1, E-Pair2, E-Proj1, E-Proj2, E-Inl, E-Inr and E-Case of C.4 each step one immediate subterm: the components of a pair from left to right, the argument of a projection or of an injection, and the first part $`t_0` of a case term. No rule steps inside a branch. The annotation of an injection names the whole sum type. By T-Inl, $`\mathsf{inl}\ 0\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool}` has type $`\mathsf{Nat}+\mathsf{Bool}`. The term $`0` alone does not determine the right summand. The evaluation rules ignore the annotation.

The case term is a binder. Its free variables and substitution follow C.1 and C.3:

$$`\mathrm{FV}(\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2)=\mathrm{FV}(t_0)\cup(\mathrm{FV}(t_1)\setminus\{x_1\})\cup(\mathrm{FV}(t_2)\setminus\{x_2\})`

$$`[x\mapsto s](\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2)=\mathsf{case}\ [x\mapsto s]t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow[x\mapsto s]t_1\mid\mathsf{inr}\ x_2\Rightarrow[x\mapsto s]t_2`

The second equation requires $`x_1\neq x`, $`x_2\neq x` and $`x_1,x_2\notin\mathrm{FV}(s)`. Otherwise the bound variable that violates the condition is renamed first, as in C.1. The other new forms bind no variable. An annotation is a type and contains no term variable, so substitution leaves it unchanged.

Let $`\mathit{pick}` be the case term reached after the first step of $`\mathit{main}`:

$$`\mathit{pick}=\mathsf{case}\ (\mathsf{inl}\ 0\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool})\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow\{x,\mathsf{iszero}\ x\}\mid\mathsf{inr}\ y\Rightarrow\{0,y\}.`

The four steps of $`\mathit{main}` are as follows.

1. $`\mathit{main}\to\mathit{pick}.2`. The step $`\mathsf{pred}\ (\mathsf{succ}\ 0)\to 0` is an instance of E-PredSucc. E-Inl lifts it into the injection, E-Case into the case term, and E-Proj2 into the projection.
2. $`\mathit{pick}.2\to\{0,\mathsf{iszero}\ 0\}.2` by E-Proj2. Its premise $`\mathit{pick}\to[x\mapsto 0]\{x,\mathsf{iszero}\ x\}=\{0,\mathsf{iszero}\ 0\}` is an instance of E-CaseInl, since $`0` is a value.
3. $`\{0,\mathsf{iszero}\ 0\}.2\to\{0,\mathsf{true}\}.2` by E-Proj2 above E-Pair2 above E-IszeroZero. E-Pair2 applies because the first component $`0` is a value.
4. $`\{0,\mathsf{true}\}.2\to\mathsf{true}` by E-PairBeta2.

Each of the five terms has type Bool in the empty context. The subterm $`\mathit{pick}` has type $`\mathsf{Nat}\times\mathsf{Bool}`, by a derivation that ends with T-Case:

$$`\dfrac{\dfrac{\dfrac{}{\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}}{\vdash\mathsf{inl}\ 0\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool}:\mathsf{Nat}+\mathsf{Bool}}\;\textsf{T-Inl}\qquad x{:}\mathsf{Nat}\vdash\{x,\mathsf{iszero}\ x\}:\mathsf{Nat}\times\mathsf{Bool}\qquad y{:}\mathsf{Bool}\vdash\{0,y\}:\mathsf{Nat}\times\mathsf{Bool}}{\vdash\mathit{pick}:\mathsf{Nat}\times\mathsf{Bool}}\;\textsf{T-Case}`

The second premise follows by T-Pair from T-Var and T-IsZero, and the third by T-Pair from T-Zero and T-Var. The right branch $`\{0,y\}` is typed although step 2 discards it.

A proof about all typed terms reads the premises off the conclusion by inversion, as in Session 26. Below the derivation above, $`\mathit{pick}` is a case term, so the last rule must be T-Case. Its first premise gives the injection a sum type. The conclusion of T-Inl writes the annotation and the type with the same $`T_1+T_2`, so the annotation $`\mathsf{Nat}+\mathsf{Bool}` is that sum type.

*Lemma 27.1 (Inversion for products and sums).* For every context $`\Gamma`, type $`T` and terms $`t_0,t_1,t_2`:

* (a) If $`\Gamma\vdash\{t_1,t_2\}:T`, then $`T=T_1\times T_2` for some types $`T_1,T_2` with $`\Gamma\vdash t_1:T_1` and $`\Gamma\vdash t_2:T_2`.
* (b) If $`\Gamma\vdash t_1.1:T`, then $`\Gamma\vdash t_1:T\times U` for some type $`U`. If $`\Gamma\vdash t_1.2:T`, then $`\Gamma\vdash t_1:U\times T` for some type $`U`.
* (c) If $`\Gamma\vdash\mathsf{inl}\ t_1\ \mathsf{as}\ U:T`, then $`U=T`, and $`T=T_1+T_2` for some types $`T_1,T_2` with $`\Gamma\vdash t_1:T_1`. If $`\Gamma\vdash\mathsf{inr}\ t_1\ \mathsf{as}\ U:T`, then $`U=T`, and $`T=T_1+T_2` for some types $`T_1,T_2` with $`\Gamma\vdash t_1:T_2`.
* (d) If $`\Gamma\vdash\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2:T` and $`x_1,x_2\notin\mathrm{dom}(\Gamma)`, then there are types $`T_1,T_2` with $`\Gamma\vdash t_0:T_1+T_2`, $`\Gamma,x_1{:}T_1\vdash t_1:T` and $`\Gamma,x_2{:}T_2\vdash t_2:T`.

*Proof.* Each of the six term forms is the conclusion form of exactly one typing rule: T-Pair, T-Proj1, T-Proj2, T-Inl, T-Inr and T-Case respectively. So a derivation of the judgment ends with that rule, and each claim reads off its premises and its conclusion. In (d), the convention of C.3 renames the bound variables when necessary, so we may assume $`x_1,x_2\notin\mathrm{dom}(\Gamma)`. $`\square`

The rules of C.4 conclude only the new forms, so [Session 26, Lemma 26.1](chapter-26/index.html#ch26-s1) still holds for the typed language of this session. Types are syntax trees. So $`T_1\times T_2=S_1\times S_2` holds only when $`T_1=S_1` and $`T_2=S_2`, and $`T_1+T_2=S_1+S_2` holds only when the left summands are equal and the right summands are equal. A product type is never a sum type, and neither is Bool, Nat, Unit or a function type.

# Canonical forms and progress
%%%
tag := "ch27-s2"
%%%

The closed term $`(\lambda z{:}\mathsf{Nat}.z).2` is stuck. E-PairBeta2 needs a pair of values, and E-Proj2 needs a step of the abstraction, which is a value. The term has no type: by Lemma 27.1(b) the abstraction would need a product type, but by Lemma 26.1(b) its type is a function type. The closed term $`\mathsf{case}\ \{0,0\}\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow x\mid\mathsf{inr}\ y\Rightarrow y` is stuck in the same way. E-CaseInl and E-CaseInr need an injection, and E-Case needs a step of the pair, which is a value. By Lemma 27.1(d) the pair would need a sum type, but by Lemma 27.1(a) its type is a product type. Progress must exclude these terms. Its new cases need to know that a value of a product type is a pair and that a value of a sum type is an injection.

*Lemma 27.2 (Canonical forms for products and sums).* Let $`v` be a value.

* (a) If $`\vdash v:T_1\times T_2`, then $`v=\{v_1,v_2\}` for values $`v_1,v_2`.
* (b) If $`\vdash v:T_1+T_2`, then $`v=\mathsf{inl}\ v_1\ \mathsf{as}\ T_1+T_2` for a value $`v_1`, or $`v=\mathsf{inr}\ v_2\ \mathsf{as}\ T_1+T_2` for a value $`v_2`.
* (c) [Session 26, Lemma 26.2](chapter-26/index.html#ch26-s2) holds for the typed language of this session.

*Proof.* A value is $`\mathsf{true}`, $`\mathsf{false}`, a numeric value, an abstraction, $`\mathsf{unit}`, a pair of values, or an injection of a value. A derivation for one of these forms ends with T-True, T-False, T-Zero or T-Succ, T-Abs, T-Unit, T-Pair, or T-Inl or T-Inr, respectively. Their conclusions give the type Bool, Bool, Nat, a function type, Unit, a product type and a sum type. A product type and a sum type differ from each other and from the other types. (a) So a value of type $`T_1\times T_2` is a pair. By the grammar of values its components are values. (b) A value of type $`T_1+T_2` is $`\mathsf{inl}\ v_1\ \mathsf{as}\ U` or $`\mathsf{inr}\ v_2\ \mathsf{as}\ U`, where $`v_1` or $`v_2` is a value by the grammar. Lemma 27.1(c) gives $`U=T_1+T_2`. (c) The proof of Lemma 26.2 now also excludes pairs and injections, whose types are product and sum types. $`\square`

The hypothesis that $`v` is a value cannot be dropped: $`\vdash\mathit{pick}:\mathsf{Nat}\times\mathsf{Bool}`, and $`\mathit{pick}` is not a pair.

*Theorem 27.3 (Progress and preservation for products and sums).* The following hold for the typed language of Session 27.

* (a) Progress. For every term $`t` and type $`T`: if $`\vdash t:T`, then $`t` is a value or there is a term $`t'` with $`t\to t'`.
* (b) Preservation. For every context $`\Gamma`, terms $`t,t'` and type $`T`: if $`\Gamma\vdash t:T` and $`t\to t'`, then $`\Gamma\vdash t':T`.

*Proof of (a).* We prove $`P(D)` for every typing derivation $`D:\Gamma\vdash t:T` by induction on $`D`, with the property of Session 26:

$$`P(D)\coloneqq(\Gamma=\varnothing)\Rightarrow\bigl(t\text{ is a value}\ \vee\ \exists t',\ t\to t'\bigr).`

The cases of the rules of C.2 and C.3 are those of the proof of [Theorem 26.3(a)](chapter-26/index.html#ch26-s2). Their canonical forms now come from Lemma 27.2(c).

*T-Case.* Suppose $`D` ends with T-Case. Then $`t=\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2`, and the first premise is $`D_0:\Gamma\vdash t_0:T_1+T_2`. Its induction hypothesis is

$$`P(D_0):\quad(\Gamma=\varnothing)\Rightarrow\bigl(t_0\text{ is a value}\ \vee\ \exists t_0',\ t_0\to t_0'\bigr).`

Assume $`\Gamma=\varnothing`. No value is a case term, so we must find a step.

1. If $`t_0\to t_0'` for some $`t_0'`, then E-Case gives $`t\to\mathsf{case}\ t_0'\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2`.
2. Otherwise $`t_0` is a value by $`P(D_0)`. Lemma 27.2(b) applied to $`D_0` gives $`t_0=\mathsf{inl}\ v_1\ \mathsf{as}\ T_1+T_2` for a value $`v_1`, or $`t_0=\mathsf{inr}\ v_2\ \mathsf{as}\ T_1+T_2` for a value $`v_2`.
3. In the first case E-CaseInl gives $`t\to[x_1\mapsto v_1]t_1`. In the second case E-CaseInr gives $`t\to[x_2\mapsto v_2]t_2`.

The premises for the branches have the contexts $`\Gamma,x_1{:}T_1` and $`\Gamma,x_2{:}T_2`, which are not empty. Their hypotheses are not used.

*T-Proj1, T-Proj2.* Suppose $`D` ends with T-Proj1. Then $`t=t_1.1` and $`T=T_{11}`, with premise $`D_1:\Gamma\vdash t_1:T_{11}\times T_{12}`. Assume $`\Gamma=\varnothing`. If $`t_1\to t_1'`, then E-Proj1 gives $`t\to t_1'.1`. Otherwise $`t_1` is a value by $`P(D_1)`, Lemma 27.2(a) gives $`t_1=\{v_1,v_2\}`, and E-PairBeta1 gives $`t\to v_1`. T-Proj2 is the same with E-Proj2 and E-PairBeta2.

*T-Pair.* Then $`t=\{t_1,t_2\}`, with premises $`D_1:\Gamma\vdash t_1:T_1` and $`D_2:\Gamma\vdash t_2:T_2`. Assume $`\Gamma=\varnothing`. If $`t_1` steps, E-Pair1 applies. Otherwise $`t_1` is a value by $`P(D_1)`, and if $`t_2` steps, E-Pair2 applies. Otherwise $`t_2` is a value by $`P(D_2)`, and $`\{t_1,t_2\}` is a value.

*T-Inl, T-Inr.* For T-Inl, $`t=\mathsf{inl}\ t_1\ \mathsf{as}\ T_1+T_2` with premise $`D_1:\Gamma\vdash t_1:T_1`. Assume $`\Gamma=\varnothing`. If $`t_1` steps, E-Inl applies. Otherwise $`t_1` is a value by $`P(D_1)`, and so is $`t`. T-Inr is the same with E-Inr. $`\square`

# Preservation
%%%
tag := "ch27-s3"
%%%

Step 2 of §27.1 replaces $`x` by $`0` in the left branch. Compare the derivation of the left branch, from the second premise of the T-Case node, with the derivation of the result:

$$`\dfrac{\dfrac{x{:}\mathsf{Nat}\in x{:}\mathsf{Nat}}{x{:}\mathsf{Nat}\vdash x:\mathsf{Nat}}\;\textsf{T-Var}\qquad\dfrac{\dfrac{x{:}\mathsf{Nat}\in x{:}\mathsf{Nat}}{x{:}\mathsf{Nat}\vdash x:\mathsf{Nat}}\;\textsf{T-Var}}{x{:}\mathsf{Nat}\vdash\mathsf{iszero}\ x:\mathsf{Bool}}\;\textsf{T-IsZero}}{x{:}\mathsf{Nat}\vdash\{x,\mathsf{iszero}\ x\}:\mathsf{Nat}\times\mathsf{Bool}}\;\textsf{T-Pair}\qquad\qquad\dfrac{\dfrac{}{\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}\qquad\dfrac{\dfrac{}{\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}}{\vdash\mathsf{iszero}\ 0:\mathsf{Bool}}\;\textsf{T-IsZero}}{\vdash\{0,\mathsf{iszero}\ 0\}:\mathsf{Nat}\times\mathsf{Bool}}\;\textsf{T-Pair}`

The right derivation is the left one with each T-Var leaf for $`x` replaced by the derivation of $`\vdash 0:\mathsf{Nat}`, and with the binding $`x{:}\mathsf{Nat}` removed from every context. Session 25 proved that this rebuilding works for the rules of C.2 and C.3. The rules of C.4 need it too.

*Lemma 27.4 (Typing lemmas for products and sums).* Permutation ([Lemma 25.2](chapter-25/index.html#ch25-s2)), weakening ([Lemma 25.4](chapter-25/index.html#ch25-s2)) and the substitution lemma ([Theorem 25.5](chapter-25/index.html#ch25-s3)) hold for the typed language of Session 27. In particular, for every context $`\Gamma`, variable $`x`, terms $`s,u` and types $`S,T`:

$$`\text{if}\quad\Gamma,x{:}S\vdash u:T\quad\text{and}\quad\Gamma\vdash s:S,\quad\text{then}\quad\Gamma\vdash[x\mapsto s]u:T.`

*Proof.* Theorem 25.5 uses Lemmas 25.1, 25.2 and 25.4, and Lemma 25.4 uses Lemma 25.3. Each is proved by induction on a derivation or on its height, with one case per typing rule. We add the cases of the rules of C.4. The old cases do not change.

*T-Pair, T-Proj1, T-Proj2, T-Inl and T-Inr.* These forms bind no variable, and every premise has the context of the conclusion. Each proof treats them as it treats T-App: apply the induction hypothesis to each premise and use the same rule.

*T-Case.* Its first premise has the context of the conclusion and is treated in the same way. The premises for the branches extend the context by $`x_1{:}T_1` and by $`x_2{:}T_2`. Each of them is treated as the premise of T-Abs, with $`x_1` or $`x_2` in the role of the parameter $`y`. Lemma 25.3 gains the same statement for a derivation that ends with T-Case. Its proof renames $`x_1` in the premise for $`t_1` and $`x_2` in the premise for $`t_2`, each to a variable outside $`V` that occurs nowhere in the derivation. As in Lemma 25.3, no binder inside a renamed premise binds the renamed variable: the context of the premise already binds it, and T-Abs and T-Case extend a context only by a variable that it does not bind. In Lemma 25.4, first rename both bound variables away from the new variable by this statement. In Theorem 25.5, steps 1–5 of the abstraction case apply to each branch. The contexts of the branch premises are formed, so $`x_1,x_2\notin\mathrm{dom}(\Gamma)\cup\{x\}`. Lemma 25.1 gives $`x_1,x_2\notin\mathrm{FV}(s)`, so the substitution equation for the case term of §27.1 applies without renaming. Permutation, weakening and the induction hypotheses give $`\Gamma,x_1{:}T_1\vdash[x\mapsto s]t_1:T` and $`\Gamma,x_2{:}T_2\vdash[x\mapsto s]t_2:T`. With $`\Gamma\vdash[x\mapsto s]t_0:T_1+T_2`, T-Case closes the case. $`\square`

*Proof of Theorem 27.3(b).* We prove $`Q(E)` for every evaluation derivation $`E:t\to t'` by induction on $`E`, where

$$`Q(E)\coloneqq\forall\Gamma\,\forall T,\ (\Gamma\vdash t:T)\Rightarrow(\Gamma\vdash t':T).`

In each congruence case the premise is $`E_i:t_i\to t_i'` for the immediate subterm $`t_i` that steps, with

$$`Q(E_i):\quad\forall\Gamma'\,\forall S,\ (\Gamma'\vdash t_i:S)\Rightarrow(\Gamma'\vdash t_i':S).`

*E-CaseInl (board case).* Suppose $`E` ends with E-CaseInl. Then

$$`t=\mathsf{case}\ (\mathsf{inl}\ v_0\ \mathsf{as}\ T_0)\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2\qquad\text{and}\qquad t'=[x_1\mapsto v_0]t_1.`

The rule has no evaluation premise, so there is no induction hypothesis. Fix $`\Gamma` and $`T` and assume $`D:\Gamma\vdash t:T`. Rename the bound variables $`x_1` and $`x_2` if necessary so that $`x_1,x_2\notin\mathrm{dom}(\Gamma)`. Up to alpha-equivalence this changes neither $`t` nor $`t'`. We must show $`\Gamma\vdash[x_1\mapsto v_0]t_1:T`.

1. Apply Lemma 27.1(d) to $`D`. There are types $`T_1,T_2` with (i) $`\Gamma\vdash\mathsf{inl}\ v_0\ \mathsf{as}\ T_0:T_1+T_2`, (ii) $`\Gamma,x_1{:}T_1\vdash t_1:T` and (iii) $`\Gamma,x_2{:}T_2\vdash t_2:T`.
2. Apply Lemma 27.1(c) to (i). The annotation is the type, $`T_0=T_1+T_2`, and there are types $`U_1,U_2` with $`T_1+T_2=U_1+U_2` and (iv) $`\Gamma\vdash v_0:U_1`.
3. Compare the left summands in $`T_1+T_2=U_1+U_2`. This gives $`U_1=T_1`, so (iv) is $`\Gamma\vdash v_0:T_1`.
4. Apply Lemma 27.4 with $`x\coloneqq x_1`, $`S\coloneqq T_1`, $`u\coloneqq t_1` and $`s\coloneqq v_0`. Its premises are (ii) and (iv) in the form of step 3. Its conclusion is $`\Gamma\vdash[x_1\mapsto v_0]t_1:T`, the goal.

The type $`T` of the result is read directly from premise (ii) of T-Case. What must be matched is the type of the injected value. Steps 2 and 3 obtain it from T-Inl and identify it with the type of $`x_1`. E-CaseInl ignores the annotation $`T_0`, but typing fixes it. Premise (iii), for the discarded right branch, is not used. Step 4 does not use that $`v_0` is a value.

In step 2 of §27.1, the case reads $`\Gamma=\varnothing`, $`T_0=\mathsf{Nat}+\mathsf{Bool}`, $`v_0=0`, $`x_1=x`, $`t_1=\{x,\mathsf{iszero}\ x\}`, $`x_2=y`, $`t_2=\{0,y\}` and $`T=\mathsf{Nat}\times\mathsf{Bool}`. Step 1 gives $`T_1=\mathsf{Nat}` and $`T_2=\mathsf{Bool}`, step 3 gives $`\vdash 0:\mathsf{Nat}`, and step 4 gives the right derivation displayed above.

*E-CaseInr.* As for E-CaseInl, with the second part of Lemma 27.1(c), the right summands, and premise (iii) (Exercise 27.2).

*E-PairBeta1, E-PairBeta2.* For E-PairBeta1, $`t=\{v_1,v_2\}.1` and $`t'=v_1`. Assume $`\Gamma\vdash t:T`. Lemma 27.1(b) gives a type $`U` with $`\Gamma\vdash\{v_1,v_2\}:T\times U`. Lemma 27.1(a) gives $`T\times U=T_1\times T_2` with $`\Gamma\vdash v_1:T_1`. Comparing first components gives $`T_1=T`, so $`\Gamma\vdash v_1:T`. E-PairBeta2 is the same with second components.

*E-Proj1, E-Proj2.* For E-Proj1, $`t=t_1.1` and $`t'=t_1'.1`. Assume $`\Gamma\vdash t:T`. Lemma 27.1(b) gives $`U` with $`\Gamma\vdash t_1:T\times U`. $`Q(E_1)` with $`\Gamma'\coloneqq\Gamma` and $`S\coloneqq T\times U` gives $`\Gamma\vdash t_1':T\times U`, and T-Proj1 gives $`\Gamma\vdash t':T`. E-Proj2 is the same at $`U\times T`.

*E-Pair1, E-Pair2.* Lemma 27.1(a) gives $`T=T_1\times T_2` with $`\Gamma\vdash t_1:T_1` and $`\Gamma\vdash t_2:T_2`. Apply $`Q(E_1)` at $`S\coloneqq T_1` for E-Pair1, or $`Q(E_2)` at $`S\coloneqq T_2` for E-Pair2, and use T-Pair.

*E-Inl, E-Inr.* For E-Inl, $`t=\mathsf{inl}\ t_1\ \mathsf{as}\ U` and $`t'=\mathsf{inl}\ t_1'\ \mathsf{as}\ U`. Lemma 27.1(c) gives $`U=T=T_1+T_2` with $`\Gamma\vdash t_1:T_1`. $`Q(E_1)` at $`T_1` gives $`\Gamma\vdash t_1':T_1`, and T-Inl gives $`\Gamma\vdash\mathsf{inl}\ t_1'\ \mathsf{as}\ T_1+T_2:T_1+T_2`, which is $`\Gamma\vdash t':T`. E-Inr is the same with $`T_2`.

*E-Case.* Rename the bound variables as in the board case. Lemma 27.1(d) gives $`\Gamma\vdash t_0:T_1+T_2` and the two branch typings. $`Q(E_0)` at $`T_1+T_2` gives $`\Gamma\vdash t_0':T_1+T_2`, and T-Case gives $`\Gamma\vdash t':T`.

*Rules of C.2 and C.3.* These are the cases of the proof of [Theorem 26.3(b)](chapter-26/index.html#ch26-s3). In the case E-AppAbs the substitution lemma is now Lemma 27.4, because the body and the argument may contain the new forms. $`\square`

# The safety table
%%%
tag := "ch27-s4"
%%%

The run of $`\mathit{main}` in §27.1 never met a stuck term. The proof of [Session 26, Corollary 26.4](chapter-26/index.html#ch26-s4) uses only the two parts of Theorem 26.3. With Theorem 27.3 in their place, the same induction on the number of steps proves safety for the typed language of this session: if $`\vdash t:T` and $`t\to^*t'`, then $`\vdash t':T`, and $`t'` is a value or takes a step.

The cases proved in this session form Row 3 of the safety table. In the form of [C.8](lambda-card/index.html#lambda-c8), without stores, the row reads as follows.

*Row 3 · Products and sums · Session 27.*

* *Canonical forms.* If $`v` is a value and $`\vdash v:T_1\times T_2`, then $`v=\{v_1,v_2\}` for values $`v_1,v_2`. If $`v` is a value and $`\vdash v:T_1+T_2`, then $`v=\mathsf{inl}\ v_1\ \mathsf{as}\ T_1+T_2` for a value $`v_1`, or $`v=\mathsf{inr}\ v_2\ \mathsf{as}\ T_1+T_2` for a value $`v_2`.
* *Progress.* T-Pair: $`\{t_1,t_2\}` is a value or steps by E-Pair1 or E-Pair2. T-Proj1: steps by E-Proj1 or E-PairBeta1. T-Proj2: steps by E-Proj2 or E-PairBeta2. T-Inl, T-Inr: the term is a value or steps by E-Inl, respectively E-Inr. T-Case: steps by E-Case, E-CaseInl or E-CaseInr.
* *Preservation.* E-PairBeta1, E-PairBeta2: no lemma. E-CaseInl, E-CaseInr: uses the substitution lemma (Lemma 27.4). E-Pair1, E-Pair2, E-Proj1, E-Proj2, E-Inl, E-Inr, E-Case: premise.

“No lemma” and “premise” are read as in Sessions 24 and 26. Adding Row 3 changes the earlier rows in two places. The canonical-forms entries of Rows 1 and 2 must now exclude pairs and injections, as in the proof of Lemma 27.2(c). The E-AppAbs entry of Row 2 uses the substitution lemma for the larger language, Lemma 27.4.

# Types as propositions
%%%
tag := "ch27-s5"
%%%

For any types $`T` and $`S`, let

$$`\mathit{swap}=\lambda z{:}T+S.\ \mathsf{case}\ z\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow\mathsf{inr}\ x\ \mathsf{as}\ S+T\mid\mathsf{inr}\ y\Rightarrow\mathsf{inl}\ y\ \mathsf{as}\ S+T.`

Read the sum type $`T+S` as the proposition “$`T` or $`S`”. The derivation of $`\vdash\mathit{swap}:T+S\to S+T` then reads as an argument.

1. T-Var gives $`z{:}T+S\vdash z:T+S`. Read: assume $`T` or $`S`.
2. T-Var and T-Inr give $`z{:}T+S,x{:}T\vdash\mathsf{inr}\ x\ \mathsf{as}\ S+T:S+T`. Read: in the case $`T`, conclude $`S` or $`T`.
3. T-Var and T-Inl give $`z{:}T+S,y{:}S\vdash\mathsf{inl}\ y\ \mathsf{as}\ S+T:S+T`. Read: in the case $`S`, conclude $`S` or $`T`.
4. T-Case, applied to the judgments of steps 1–3, types the case term at $`S+T` in the context $`z{:}T+S`. Read: $`S` or $`T` holds in both cases.
5. T-Abs gives $`\vdash\mathit{swap}:T+S\to S+T`. Read: $`T` or $`S` implies $`S` or $`T`, with no assumption left.

In general, read the function type $`T_1\to T_2` as the implication “$`T_1` implies $`T_2`”, the product type $`T_1\times T_2` as the conjunction “$`T_1` and $`T_2`”, and the sum type $`T_1+T_2` as the disjunction “$`T_1` or $`T_2`”. Read a typing context as a list of assumptions. Erase the terms from T-Var, T-Abs, T-App, T-Pair, T-Proj1, T-Proj2, T-Inl, T-Inr and T-Case. They become the rules of propositional logic for assumptions, implication, conjunction and disjunction. For example, T-App becomes “from $`T_{11}` implies $`T_{12}`, and $`T_{11}`, conclude $`T_{12}`”, and T-Case becomes proof by cases. A derivation of $`\Gamma\vdash t:T` becomes a proof of $`T` from the assumptions in $`\Gamma`, and the term $`t` records that proof. This reading is the *Curry–Howard correspondence* (TAPL §9.4).

Evaluation has a reading too. The computation rules for functions, pairs and sums each remove a rule that builds a value directly followed by a rule that uses it: E-AppAbs removes T-Abs followed by T-App, E-PairBeta1 and E-PairBeta2 remove T-Pair followed by a projection, and E-CaseInl and E-CaseInr remove an injection followed by T-Case. Preservation says that the proof after the step proves the same proposition. In the board case of §27.3, step 4 puts the proof of the left alternative in place of the assumption $`x_1{:}T_1`.

The correspondence concerns terms without constants. The term $`\lambda z{:}\mathsf{Nat}.\mathsf{true}` has type $`\mathsf{Nat}\to\mathsf{Bool}`, but “Nat implies Bool” is not a law of logic when Nat and Bool are read as arbitrary propositions. In $`\mathit{swap}`, by contrast, $`T` and $`S` are arbitrary types. The typed language has no type without values, so it has no proposition “false” and no negation.

# Exercises
%%%
tag := "ch27-s6"
number := false
%%%

*27.1.* Reduce $`\mathsf{case}\ (\mathsf{inr}\ (\mathsf{iszero}\ 0)\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool})\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow x\mid\mathsf{inr}\ y\Rightarrow\mathsf{if}\ y\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0` to a value. For each step, list the rules of its derivation and give the type of the term reached.

*27.2.* Write the E-CaseInr case of preservation in four numbered steps, in the style of the board case. Which premise of T-Case is not used?

*27.3.* Replace T-Case by a rule without the premise for the right branch: from $`\Gamma\vdash t_0:T_1+T_2` and $`\Gamma,x_1{:}T_1\vdash t_1:T`, conclude $`\Gamma\vdash\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2:T`. (a) Give a closed term that is well typed under the new rule and reaches a stuck term. (b) Which part of Theorem 27.3 fails, and at which step of which case? (c) Does the other part still hold?

*27.4.* For any types $`T` and $`S`, give a closed term of type $`T\times S\to S\times T`. Read its derivation as an argument, as for $`\mathit{swap}` in §27.5.

*Further problem.* Make every pair $`\{t_1,t_2\}` a value, delete E-Pair1 and E-Pair2, and replace E-PairBeta1 and E-PairBeta2 by $`\{t_1,t_2\}.1\to t_1` and $`\{t_1,t_2\}.2\to t_2` for all terms $`t_1,t_2`. Restate Row 3 for this language. Do progress and preservation still hold? Compare the runs of $`\{0,\mathsf{pred}\ 0\}.1` in both languages.

# Reading for the Seminar
%%%
tag := "ch27-s7"
number := false
%%%

*Definitions · 10 minutes.* Write T-Inl, T-Case, E-CaseInl and Lemma 27.4. Follow the four steps of $`\mathit{main}` in §27.1 and give the type of each term. Draw the T-Case derivation of $`\mathit{pick}`.

*Joint proof · 30 minutes.* Start from a typing of the redex $`\mathsf{case}\ (\mathsf{inl}\ v_0\ \mathsf{as}\ T_0)\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2` at an unknown type $`T`. Invert T-Case and then T-Inl, compare the left summands, and instantiate Lemma 27.4 explicitly. Check the case on step 2 of $`\mathit{main}`. Then do Exercise 27.2.

*Proof review · 20 minutes.* Prove the T-Case case of progress. Do Exercise 27.3 and locate the broken step. Write Row 3 on the board. In the last five minutes, read $`\mathit{swap}` of §27.5 as an argument by cases.

*Facilitator’s hint.* Ask two questions. Where does the type of the result come from? From premise (ii) of T-Case. Where does the type of $`v_0` come from? From T-Inl, through the annotation, which evaluation ignores.

# Solutions and Further Reading
%%%
tag := "ch27-s8"
number := false
%%%

*27.1.* There are three steps.

1. $`\mathsf{iszero}\ 0\to\mathsf{true}` by E-IszeroZero, lifted by E-Inr and then E-Case. The term reached is $`\mathsf{case}\ (\mathsf{inr}\ \mathsf{true}\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool})\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow x\mid\mathsf{inr}\ y\Rightarrow\mathsf{if}\ y\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0`.
2. E-CaseInr gives $`[y\mapsto\mathsf{true}](\mathsf{if}\ y\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0)=\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0`.
3. E-IfTrue gives $`0`.

Every term has type Nat. The first is typed by T-Case from $`\vdash\mathsf{inr}\ (\mathsf{iszero}\ 0)\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool}:\mathsf{Nat}+\mathsf{Bool}` (T-Inr above T-IsZero above T-Zero), $`x{:}\mathsf{Nat}\vdash x:\mathsf{Nat}` and $`y{:}\mathsf{Bool}\vdash\mathsf{if}\ y\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{succ}\ 0:\mathsf{Nat}`.

*27.2.* Suppose $`E` ends with E-CaseInr. Then $`t=\mathsf{case}\ (\mathsf{inr}\ v_0\ \mathsf{as}\ T_0)\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2` and $`t'=[x_2\mapsto v_0]t_2`. Fix $`\Gamma` and $`T`, assume $`D:\Gamma\vdash t:T`, and rename so that $`x_1,x_2\notin\mathrm{dom}(\Gamma)`. We must show $`\Gamma\vdash[x_2\mapsto v_0]t_2:T`.

1. Lemma 27.1(d) applied to $`D` gives $`T_1,T_2` with (i) $`\Gamma\vdash\mathsf{inr}\ v_0\ \mathsf{as}\ T_0:T_1+T_2`, (ii) $`\Gamma,x_1{:}T_1\vdash t_1:T` and (iii) $`\Gamma,x_2{:}T_2\vdash t_2:T`.
2. The second part of Lemma 27.1(c) applied to (i) gives $`T_0=T_1+T_2`, and types $`U_1,U_2` with $`T_1+T_2=U_1+U_2` and (iv) $`\Gamma\vdash v_0:U_2`.
3. Comparing the right summands gives $`U_2=T_2`, so (iv) is $`\Gamma\vdash v_0:T_2`.
4. Lemma 27.4 with $`x\coloneqq x_2`, $`S\coloneqq T_2`, $`u\coloneqq t_2` and $`s\coloneqq v_0`, applied to (iii) and (iv), gives $`\Gamma\vdash[x_2\mapsto v_0]t_2:T`.

Premise (ii), for the left branch, is not used.

*27.3.* (a) Take $`\mathsf{case}\ (\mathsf{inr}\ \mathsf{true}\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool})\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow x\mid\mathsf{inr}\ y\Rightarrow\mathsf{succ}\ y`. T-Inr types the injection at $`\mathsf{Nat}+\mathsf{Bool}`, and T-Var gives $`x{:}\mathsf{Nat}\vdash x:\mathsf{Nat}`, so the new rule gives the type Nat. E-CaseInr gives $`\mathsf{succ}\ \mathsf{true}`, which is stuck (C.2). (b) Preservation fails, in the case E-CaseInr. Step 1 of Exercise 27.2 no longer yields premise (iii), so step 4 has no typing of the branch $`t_2` to substitute into. Indeed $`\mathsf{succ}\ \mathsf{true}` has no type. (c) Progress still holds. Its T-Case case uses only the first premise.

*27.4.* Take $`\lambda z{:}T\times S.\{z.2,z.1\}`. T-Var gives $`z{:}T\times S\vdash z:T\times S`. Read: assume $`T` and $`S`. T-Proj2 and T-Proj1 give $`z.2:S` and $`z.1:T` in that context. Read: so $`S`, and so $`T`. T-Pair gives $`\{z.2,z.1\}:S\times T`. Read: so $`S` and $`T`. T-Abs gives $`\vdash\lambda z{:}T\times S.\{z.2,z.1\}:T\times S\to S\times T`. Read: $`T` and $`S` implies $`S` and $`T`.

*Further problem.* The canonical form of a product type is now $`\{t_1,t_2\}` for terms $`t_1,t_2`. Progress: T-Pair gives a value. T-Proj1 steps by E-Proj1 or by the new first projection rule, T-Proj2 likewise. The other entries are unchanged. Preservation: the new projection rules use no lemma, since Lemma 27.1(b) and then 27.1(a) give $`\Gamma\vdash t_1:T` directly. E-Proj1 and E-Proj2 use the premise. Both properties still hold. The eager language takes two steps, $`\{0,\mathsf{pred}\ 0\}.1\to\{0,0\}.1\to 0`, by E-Proj1 above E-Pair2 above E-PredZero, and then E-PairBeta1. The new language takes one step to $`0` and never evaluates $`\mathsf{pred}\ 0`. Progress and preservation constrain how each rule relates to typing. They do not fix an evaluation order.

*Further reading · Annotations and uniqueness of types.* TAPL §11.9 first presents sums without annotations, with a rule that types $`\mathsf{inl}\ t_1` at $`T_1+T_2` for every $`T_2`. Then $`\mathsf{inl}\ 0` has type $`\mathsf{Nat}+\mathsf{Bool}` and also $`\mathsf{Nat}+\mathsf{Unit}`. Progress and preservation still hold, with the same proofs. The annotation restores the uniqueness of types of Session 24's further reading, so a type checker can compute the type from the term. The inference form of [C.5](lambda-card/index.html#lambda-c5) omits sums for this reason.

*Further reading · More on the Curry–Howard correspondence.* The propositions that have a proof in the sense of §27.5 are those of intuitionistic propositional logic with implication, conjunction and disjunction. Some classical laws are missing. For example, Peirce’s law, “if ($`T` implies $`S`) implies $`T`, then $`T`”, holds in every truth table but has no such proof when $`T` and $`S` are arbitrary propositions. TAPL §9.4 presents the correspondence. Philip Wadler’s “Propositions as Types” (_Communications of the ACM_ 58(12), 2015) tells its history.

TAPL §11.6 defines pairs, §11.9 defines sums, and §9.3 proves the safety theorems for functions. [Table of contents.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Sources and Formalization
%%%
tag := "ch27-notes"
number := false
%%%

* *Lemma 27.1.* Corresponds to TAPL §9.3. Paper proof only ([§27.1](chapter-27/index.html#ch27-s1)).
* *Lemma 27.2.* Corresponds to TAPL §9.3. Paper proof only ([§27.2](chapter-27/index.html#ch27-s2)).
* *Theorem 27.3.* Corresponds to TAPL §9.3. Paper proof only ([§27.2](chapter-27/index.html#ch27-s2)–[§27.3](chapter-27/index.html#ch27-s3)).
* *Lemma 27.4.* Corresponds to TAPL §9.3. Paper proof only ([§27.3](chapter-27/index.html#ch27-s3)).
