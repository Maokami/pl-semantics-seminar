import VersoManual

open Verso.Genre Manual

#doc (Manual) "Computational Adequacy: the Statement and the Approximation Relation" =>
%%%
tag := "ch36"
file := "chapter-36"
%%%

* *Definitions.* PCF types, closed terms, values, the typing judgment $`\vdash t:T`, the evaluation judgment $`t\Downarrow v` with its call-by-name application rule and its fixed-point rule, the domains $`\llbracket T\rrbracket ` and the meaning $`\llbracket t\rrbracket ` of a closed term ([Session 35](chapter-35/index.html)). Increasing sequences $`d_0\sqsubseteq d_1\sqsubseteq\cdots`, least upper bounds $`\bigsqcup_j d_j`, flat domains, the pointwise order on continuous functions and admissible sets ([Session 34](chapter-34/index.html)).
* *New terms.* Computational adequacy, ground type, formal approximation relation, closure under evaluation. [Glossary and label key](glossary/index.html)
* *Lemma 36.4 \[Paper proof only: §36.3\].* For every type $`T` and every closed term $`t` with $`\vdash t:T`: (a) $`\bot\lhd_T t`; (b) for every increasing sequence $`d_0\sqsubseteq d_1\sqsubseteq\cdots` in $`\llbracket T\rrbracket `, if $`d_j\lhd_T t` for every $`j`, then $`\bigsqcup_j d_j\lhd_T t`. With Lemma 36.5 it is one of the two tools for Theorem 36.2 (adequacy), which Session 37 proves.
* *Source.* Cambridge _Denotational Semantics_ lecture notes, 2025–26 edition. Definition 36.3 is their Definition 27, Lemma 36.4 their Lemma 33, Lemma 36.5 their Lemma 35, and Theorem 36.2 their Theorem 31. [Notes.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)
* *Board case.* Lemma 36.4(b) in the case Nat and in the case of an arrow type $`T\to S`.
* *Proof outline.* Induction on the type $`T` with $`Q(T)\coloneqq\forall t,\ \forall(d_j)_j,\ (\forall j,\ d_j\lhd_T t)\Rightarrow\bigsqcup_j d_j\lhd_T t`, where $`t` ranges over closed terms of type $`T` and $`(d_j)_j` over increasing sequences in $`\llbracket T\rrbracket `. At $`\mathsf{Nat}` a number in the limit already occurs at a finite stage. At $`T\to S` fix a related argument pair $`(d,u)` and apply $`Q(S)` to the term $`t\,u`, which is the same at every stage.
* *From Session 35.* Session 35 computed $`\llbracket K\,\overline{1}\rrbracket =0` from an increasing sequence of approximations and built a derivation of $`K\,\overline{1}\Downarrow\overline{0}` by hand. This session asks when the first calculation guarantees the second, for every closed term of type $`\mathsf{Nat}` or $`\mathsf{Bool}`.

Session 35 computed the meaning of the term $`K\,\overline{1}` without evaluating it and obtained the number 0. Separately, it found an evaluation of $`K\,\overline{1}` to the numeral $`\overline{0}`. Was that evaluation guaranteed once the meaning was known? This session states the guarantee, called computational adequacy, and builds the tool for its proof: a relation between semantic elements and closed terms, defined by induction on types. Session 37 proves the theorem.

# Soundness and adequacy
%%%
tag := "ch36-s1"
%%%

Recall the countdown program of Session 35:

$$`G=\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\ \lambda x{:}\mathsf{Nat}.\ \mathsf{if}\ \mathsf{iszero}\ x\ \mathsf{then}\ 0\ \mathsf{else}\ f\,(\mathsf{pred}\ x),\qquad K=\mathsf{fix}\ G.`

Write $`\overline{n}` for the numeral with $`n` successors: $`\overline{0}=0` and $`\overline{n+1}=\mathsf{succ}\ \overline{n}`. The values of type $`\mathsf{Nat}` are exactly the numerals, a numeral evaluates only to itself, and $`\llbracket \overline{n}\rrbracket =n`. Session 35 computed $`\llbracket K\rrbracket ` as the least upper bound of the increasing sequence $`g_0\sqsubseteq g_1\sqsubseteq\cdots` in $`\llbracket \mathsf{Nat}\to\mathsf{Nat}\rrbracket ` given by $`g_0=\bot` and $`g_{j+1}=\llbracket G\rrbracket (g_j)`. At a number $`k`, $`g_j(k)=0` if $`k<j` and $`g_j(k)=\bot` if $`k\ge j`; at $`\bot`, $`g_j(\bot)=\bot`. Hence $`\llbracket K\,\overline{1}\rrbracket =\llbracket K\rrbracket (1)=0`. Session 35 also gave a derivation of $`K\,\overline{1}\Downarrow\overline{0}`.

The two results agree. In one direction the agreement holds for every closed term.

*Theorem 36.1 (Soundness of evaluation) \[Paper proof only: Session 35, Theorem 35.8\].* For every type $`T`, every closed term $`t` with $`\vdash t:T` and every value $`v`, if $`t\Downarrow v` then $`\llbracket t\rrbracket =\llbracket v\rrbracket `.

This is [Session 35, Theorem 35.8](chapter-35/index.html#ch35-s4), restated. Its proof is an induction on the derivation of $`t\Downarrow v`. At type $`\mathsf{Nat}` soundness says: if $`t\Downarrow\overline{n}` then $`\llbracket t\rrbracket =n`. It says nothing about a term for which no derivation is known. The converse direction holds at the *ground types* $`\mathsf{Nat}` and $`\mathsf{Bool}`. Recall that $`\llbracket \mathsf{Bool}\rrbracket ` is the flat domain with elements $`\bot`, $`\mathrm{tt}` and $`\mathrm{ff}`, with $`\llbracket \mathsf{true}\rrbracket =\mathrm{tt}` and $`\llbracket \mathsf{false}\rrbracket =\mathrm{ff}`.

*Theorem 36.2 (Computational adequacy) \[Paper proof only: Session 37, §37.4\].* Let $`t` be a closed term. If $`\vdash t:\mathsf{Nat}` and $`\llbracket t\rrbracket =n` for a number $`n`, then $`t\Downarrow\overline{n}`. If $`\vdash t:\mathsf{Bool}` and $`\llbracket t\rrbracket =\mathrm{tt}`, then $`t\Downarrow\mathsf{true}`; if $`\vdash t:\mathsf{Bool}` and $`\llbracket t\rrbracket =\mathrm{ff}`, then $`t\Downarrow\mathsf{false}`.

This is Theorem 31 of the Cambridge notes. With Theorem 36.1 it gives, for every closed term $`t` of type $`\mathsf{Nat}` and every number $`n`: $`t\Downarrow\overline{n}` if and only if $`\llbracket t\rrbracket =n`. In particular the calculation $`\llbracket K\,\overline{1}\rrbracket =0` alone guarantees that $`K\,\overline{1}\Downarrow\overline{0}` has a derivation.

*Soundness does not give adequacy.* Let $`\Downarrow^{-}` be the judgment defined by all evaluation rules of Session 35 except the fixed-point rule. Every derivation of $`t\Downarrow^{-}v` is also a derivation of $`t\Downarrow v`, so Theorem 36.1 holds for $`\Downarrow^{-}`. Adequacy fails for $`\Downarrow^{-}`. A derivation of $`K\,\overline{1}\Downarrow^{-}v` would end with the application rule, whose first premise evaluates $`K=\mathsf{fix}\ G`. This term is not a value, and no remaining rule has a fixed-point term in its conclusion. So $`K\,\overline{1}` has no value under $`\Downarrow^{-}`, although $`\llbracket K\,\overline{1}\rrbracket =0`. A proof of adequacy must therefore use the fixed-point rule. Session 37 uses it in step 6 of its board case.

*Induction on the term is not enough.* Try to prove Theorem 36.2 by induction on $`t`. Take $`t=t_1\,t_2` with $`\vdash t_1:\mathsf{Nat}\to\mathsf{Nat}` and $`\vdash t_2:\mathsf{Nat}`, and suppose $`\llbracket t\rrbracket =\llbracket t_1\rrbracket (\llbracket t_2\rrbracket )=n`. The theorem speaks only of ground types, so there is no induction hypothesis for $`t_1`. The hypothesis for $`t_2` may give nothing either. Let $`\Omega=\mathsf{fix}\,(\lambda x{:}\mathsf{Nat}.\,x)`. Session 35 showed that $`\llbracket \Omega\rrbracket =\bot` and that $`\Omega` has no value. Yet $`(\lambda x{:}\mathsf{Nat}.\,0)\,\Omega\Downarrow\overline{0}`. Finally, the application rule evaluates the body of the operator with $`t_2` substituted, and that term is not a subterm of $`t`. What is missing is a statement at every type that describes how a term of function type behaves when it is applied. §36.2 supplies it.

# The formal approximation relation
%%%
tag := "ch36-s2"
%%%

At a ground type an element of the domain makes a promise about evaluation. The number 0 is the meaning of $`K\,\overline{1}` and promises $`K\,\overline{1}\Downarrow\overline{0}`. That derivation exists, so we will say that 0 approximates $`K\,\overline{1}`. The element $`\bot` promises nothing. So it approximates every closed term of type $`\mathsf{Nat}`, including $`\overline{5}`, whose meaning is 5. The number 3 does not approximate $`\overline{5}`, because $`\overline{5}` evaluates only to itself.

At a function type a closed term evaluates to an abstraction, and the abstraction shows nothing about its results until it is applied. So we test a semantic function on arguments. Let $`i` be the identity function on $`\mathbb{N}_\bot=\llbracket \mathsf{Nat}\rrbracket ` and let $`I=\lambda x{:}\mathsf{Nat}.\,x`. Give $`I` a closed term $`u` of type $`\mathsf{Nat}`, and give $`i` an element $`d` that approximates $`u`. We ask that $`i(d)` approximate $`I\,u`. If $`d=n`, then $`u\Downarrow\overline{n}`. The application rule then gives $`I\,u\Downarrow\overline{n}`: its first premise is $`I\Downarrow I`, and its second premise is $`[x\mapsto u]x=u\Downarrow\overline{n}`. So $`i(n)=n` approximates $`I\,u`. If $`d=\bot`, then $`i(d)=\bot`, which approximates every term. The test succeeds for every such pair $`(d,u)`.

*Definition 36.3 (Formal approximation relation).* For each type $`T`, define a relation $`d\lhd_T t` between elements $`d\in\llbracket T\rrbracket ` and closed terms $`t` with $`\vdash t:T`, by recursion on $`T`:

$$`\begin{aligned}
d\lhd_{\mathsf{Nat}}t\ &\iff\ \forall n\in\mathbb{N},\ d=n\Rightarrow t\Downarrow\overline{n}\\
d\lhd_{\mathsf{Bool}}t\ &\iff\ \bigl(d=\mathrm{tt}\Rightarrow t\Downarrow\mathsf{true}\bigr)\ \wedge\ \bigl(d=\mathrm{ff}\Rightarrow t\Downarrow\mathsf{false}\bigr)\\
f\lhd_{T\to S}t\ &\iff\ \forall d\in\llbracket T\rrbracket ,\ \forall u\ \text{with}\ \vdash u:T,\ \ d\lhd_T u\Rightarrow f(d)\lhd_S t\,u
\end{aligned}`

Read $`d\lhd_T t` as “$`d` approximates $`t`”. A pair $`(d,u)` with $`d\lhd_T u` is a *related pair* at $`T`. The arrow clause uses only the relations at the smaller types $`T` and $`S`, so the recursion is well founded. This is Definition 27 of the Cambridge notes. As in [Session 33](chapter-33/index.html), the relation is defined by induction on types, and at an arrow type related arguments must give related results. Here the two sides differ in kind: a semantic element on the left, a closed term on the right.

The identity example shows $`i\lhd_{\mathsf{Nat}\to\mathsf{Nat}}I`. The arrow clause quantifies over every related pair, including pairs whose left side is not the meaning of the right side, such as $`(\bot,\overline{5})`. A single failing pair refutes the relation. Let $`c` be the constant function on $`\mathbb{N}_\bot` with value 1, and take the related pair $`(2,\overline{2})`. The arrow clause for $`c\lhd_{\mathsf{Nat}\to\mathsf{Nat}}I` requires $`1\lhd_{\mathsf{Nat}}I\,\overline{2}`, that is, $`I\,\overline{2}\Downarrow\overline{1}`. A derivation of $`I\,\overline{2}\Downarrow v` ends with the application rule, whose second premise is $`\overline{2}\Downarrow v`, so $`v=\overline{2}`. Hence $`c\lhd_{\mathsf{Nat}\to\mathsf{Nat}}I` fails. A proof of $`f\lhd_{T\to S}t`, by contrast, must treat an arbitrary related pair.

# Closure properties
%%%
tag := "ch36-s3"
%%%

Two evaluation rules of Session 35 are used in this section and in Session 37. The application rule evaluates the operator to an abstraction and then evaluates its body with the unevaluated argument substituted. The fixed-point rule unfolds $`\mathsf{fix}\ t` once.

$$`\frac{t_1\Downarrow\lambda x{:}T.\,t_0\qquad[x\mapsto t_2]t_0\Downarrow v}{t_1\,t_2\Downarrow v}\qquad\qquad\frac{t\,(\mathsf{fix}\ t)\Downarrow v}{\mathsf{fix}\ t\Downarrow v}`

An application and a fixed-point term are not values. So the application rule is the only rule whose conclusion evaluates an application, and the fixed-point rule is the only rule whose conclusion evaluates a fixed-point term.

The approximations $`g_j` of §36.1 form an increasing sequence with $`\bigsqcup_j g_j=\llbracket K\rrbracket `. Session 37 shows $`g_j\lhd_{\mathsf{Nat}\to\mathsf{Nat}}K` for every $`j`. Look at one related argument pair, $`(1,\overline{1})`. The results $`g_0(1)=\bot`, $`g_1(1)=\bot`, $`g_2(1)=0`, $`g_3(1)=0`, … form an increasing sequence in $`\mathbb{N}_\bot`. Each of them approximates $`K\,\overline{1}`: $`\bot` approximates every term, and 0 approximates $`K\,\overline{1}` because $`K\,\overline{1}\Downarrow\overline{0}`. Their least upper bound is 0, and the evidence that it approximates $`K\,\overline{1}` is the evidence for stage 2. The next lemma says that the passage from the stages to the limit always works.

*Lemma 36.4 (The related set is admissible) \[Paper proof only: this section\].* For every type $`T` and every closed term $`t` with $`\vdash t:T`: (a) $`\bot\lhd_T t`; (b) for every increasing sequence $`d_0\sqsubseteq d_1\sqsubseteq\cdots` in $`\llbracket T\rrbracket `, if $`d_j\lhd_T t` for every $`j`, then $`\bigsqcup_j d_j\lhd_T t`.

So the set $`\{d\in\llbracket T\rrbracket \mid d\lhd_T t\}` is admissible in the sense of [Session 34](chapter-34/index.html): it contains $`\bot` and the least upper bound of every increasing sequence in it. This is Lemma 33 of the Cambridge notes.

*Proof of (a).* Induction on $`T`, with the property $`\forall t,\ \bot\lhd_T t` over closed terms $`t` of type $`T`. At $`\mathsf{Nat}`, $`\bot` is not a number, so the implication in Definition 36.3 has a false premise for every $`n`. The case $`\mathsf{Bool}` is the same. At $`T\to S`, the least element of $`\llbracket T\to S\rrbracket ` is the function with constant value $`\bot` (Session 34). For a related pair $`(d,u)` at $`T`, its result $`\bot` approximates $`t\,u` by the hypothesis at $`S`, applied to the term $`t\,u`. $`\square`

*Proof of (b).* We prove $`Q(T)` for every type $`T` by induction on $`T`:

$$`Q(T)\coloneqq\forall t,\ \forall(d_j)_j,\ \bigl(\forall j,\ d_j\lhd_T t\bigr)\Rightarrow\bigsqcup_j d_j\lhd_T t.`

Here $`t` ranges over closed terms of type $`T` and $`(d_j)_j` over increasing sequences in $`\llbracket T\rrbracket `. The term $`t` is quantified inside $`Q(T)`, because the arrow case applies the hypothesis to a different term.

*Case Nat.* Suppose $`d_j\lhd_{\mathsf{Nat}}t` for every $`j`, and let $`d=\bigsqcup_j d_j`.

1. By Definition 36.3 at $`\mathsf{Nat}`, fix $`n\in\mathbb{N}` and assume $`d=n`. We must show $`t\Downarrow\overline{n}`.
2. Some $`d_k` is a number. Otherwise every $`d_j` is $`\bot`, so $`\bot` is an upper bound of the increasing sequence and $`d=\bot\neq n`.
3. Let $`d_k=m`. For $`j\ge k`, $`m=d_k\sqsubseteq d_j`, and in the flat domain the only element above the number $`m` is $`m` itself. So $`d_j=m` for $`j\ge k`, and $`d_j\sqsubseteq d_k=m` for $`j<k`. Thus $`m` is an upper bound of the increasing sequence, and every upper bound lies above $`d_k=m`. Hence $`d=m`. So $`m=n` and $`d_k=n`.
4. Apply the hypothesis $`d_k\lhd_{\mathsf{Nat}}t` with this $`n`. It gives $`t\Downarrow\overline{n}`.

*Case Bool.* As for $`\mathsf{Nat}`, with $`\mathrm{tt}` and $`\mathrm{ff}` in place of $`n` (Exercise 36.1).

*Case of an arrow type.* Let the type be $`T\to S`. The induction hypothesis used is

$$`Q(S):\quad\forall t'',\ \forall(e_j)_j,\ \bigl(\forall j,\ e_j\lhd_S t''\bigr)\Rightarrow\bigsqcup_j e_j\lhd_S t''.`

Let $`f_0\sqsubseteq f_1\sqsubseteq\cdots` be an increasing sequence in $`\llbracket T\to S\rrbracket ` with $`f_j\lhd_{T\to S}t` for every $`j`, and let $`f=\bigsqcup_j f_j`.

1. By Definition 36.3 at $`T\to S`, fix $`d\in\llbracket T\rrbracket ` and a closed term $`u` of type $`T` with $`d\lhd_T u`. We must show $`f(d)\lhd_S t\,u`.
2. For each $`j`, apply the arrow clause of $`f_j\lhd_{T\to S}t` to the pair $`(d,u)`. This gives $`f_j(d)\lhd_S t\,u`.
3. Since $`f_j\sqsubseteq f_{j+1}` in the pointwise order, $`f_j(d)\sqsubseteq f_{j+1}(d)`. So $`f_0(d)\sqsubseteq f_1(d)\sqsubseteq\cdots` is an increasing sequence in $`\llbracket S\rrbracket `.
4. Apply $`Q(S)` with $`t''=t\,u` and $`e_j=f_j(d)`. Step 2 supplies its premise. This gives $`\bigsqcup_j f_j(d)\lhd_S t\,u`.
5. The least upper bound of an increasing sequence of continuous functions is computed pointwise (Session 34), so $`f(d)=\bigsqcup_j f_j(d)`. Hence $`f(d)\lhd_S t\,u`.

Since $`(d,u)` was an arbitrary related pair, $`f\lhd_{T\to S}t`. $`\square`

In step 4 the term $`t\,u` stays fixed while the semantic side moves along the increasing sequence. A hypothesis stated only for the single term $`t` would not apply to $`t\,u`. This is the choice made in [Session 3](chapter-03/index.html#ch03-s2), where the final store was quantified inside the induction property.

By the fixed-point rule, every value of $`G\,K` is a value of $`K`: a derivation of $`G\,(\mathsf{fix}\ G)\Downarrow v` becomes a derivation of $`K\Downarrow v` when the fixed-point rule is added at its root. So $`K` keeps every promise that $`G\,K` keeps. The next lemma turns this observation into a statement about the relation.

*Lemma 36.5 (Closure under evaluation) \[Paper proof only: this section\].* Let $`T` be a type and let $`t,t'` be closed terms of type $`T`. If $`t\Downarrow v` implies $`t'\Downarrow v` for every value $`v`, then $`d\lhd_T t` implies $`d\lhd_T t'` for every $`d\in\llbracket T\rrbracket `.

This is Lemma 35 of the Cambridge notes. For the example, it says that every element approximating $`G\,K` approximates $`K`.

*Proof.* Induction on $`T` with the property

$$`E(T)\coloneqq\forall t,\ \forall t',\ \bigl(\forall v,\ t\Downarrow v\Rightarrow t'\Downarrow v\bigr)\Rightarrow\forall d,\ \bigl(d\lhd_T t\Rightarrow d\lhd_T t'\bigr).`

At $`\mathsf{Nat}`, if $`d=n` then $`t\Downarrow\overline{n}` by $`d\lhd_{\mathsf{Nat}}t`, so $`t'\Downarrow\overline{n}`. The case $`\mathsf{Bool}` is the same. At $`T\to S`, assume that every value of $`t` is a value of $`t'`, and that $`f\lhd_{T\to S}t`. Fix a related pair $`(d,u)` at $`T`. The arrow clause gives $`f(d)\lhd_S t\,u`. Every value of $`t\,u` is a value of $`t'\,u`. Indeed, a derivation of $`t\,u\Downarrow v` ends with the application rule, with premises $`t\Downarrow\lambda x{:}T.\,t_0` and $`[x\mapsto u]t_0\Downarrow v`. The assumption turns the first premise into $`t'\Downarrow\lambda x{:}T.\,t_0`, and the application rule gives $`t'\,u\Downarrow v`. The hypothesis $`E(S)`, applied to the terms $`t\,u` and $`t'\,u`, gives $`f(d)\lhd_S t'\,u`. $`\square`

Lemma 36.4 lets Scott induction from Session 34 work with the set of elements that approximate one fixed term. Lemma 36.5 moves the relation along one evaluation rule. Session 37 combines the two in its fixed-point case.

# Exercises
%%%
tag := "ch36-s4"
number := false
%%%

*36.1.* Write the case Bool of Lemma 36.4(b) in the style of the case Nat.

*36.2.* Let $`c_0` be the constant function on $`\mathbb{N}_\bot` with value 0, and let $`\Omega=\mathsf{fix}\,(\lambda x{:}\mathsf{Nat}.\,x)` as in §36.1. The closed term $`\lambda x{:}\mathsf{Nat}.\,\Omega` evaluates to itself. Show that $`c_0\lhd_{\mathsf{Nat}\to\mathsf{Nat}}\lambda x{:}\mathsf{Nat}.\,\Omega` fails. Explain why knowing only that a term evaluates to an abstraction cannot establish the arrow clause.

*36.3.* Determine the set $`\{d\in\mathbb{N}_\bot\mid d\lhd_{\mathsf{Nat}}t\}` for $`t=\overline{3}`, for $`t=\Omega`, and for $`t=(\lambda x{:}\mathsf{Nat}.\,x)\,\overline{3}`. Use Lemma 36.5 to explain why the first and the third sets are equal.

*Further problem.* Downward closure. Fix a closed term $`t` of type $`T`. Show that if $`d\lhd_T t` and $`d'\sqsubseteq d`, then $`d'\lhd_T t`. In the arrow case, say which term stays fixed as you move down in the domain. Then show: if $`\llbracket K\rrbracket \lhd_{\mathsf{Nat}\to\mathsf{Nat}}K`, then $`g_j\lhd_{\mathsf{Nat}\to\mathsf{Nat}}K` for every $`j`, although $`g_j` is not the meaning of $`K`.

# Reading for the Seminar
%%%
tag := "ch36-s5"
number := false
%%%

*Definitions · 10 minutes.* Put soundness and adequacy for $`K\,\overline{1}` side by side and say which direction each gives. Write the three clauses of Definition 36.3 and check the identity example.

*Joint proof · 30 minutes.* Prove Lemma 36.4(b). Write $`Q(T)` with its quantifier over $`t`. Do the case Nat. Then do the arrow case: one person fixes the related pair, another applies the arrow clause at every stage, and a third applies $`Q(S)` to $`t\,u` and uses the pointwise least upper bound.

*Proof review · 20 minutes.* Refute $`c\lhd I` for the constant-one function. Prove the arrow case of Lemma 36.5. Use Exercise 36.2 to see why returning an abstraction is not enough.

*Facilitator’s hint.* In the arrow case the term $`t\,u` is the same at every stage. Only the semantic side moves along the increasing sequence.

# Solutions and Further Reading
%%%
tag := "ch36-s6"
number := false
%%%

*36.1.* Suppose $`d_j\lhd_{\mathsf{Bool}}t` for every $`j`, and let $`d=\bigsqcup_j d_j`. Assume $`d=\mathrm{tt}`. As in step 2, some $`d_k` differs from $`\bot`. As in step 3, $`d_j=d_k` for $`j\ge k` and $`d=d_k`. So $`d_k=\mathrm{tt}`, and $`d_k\lhd_{\mathsf{Bool}}t` gives $`t\Downarrow\mathsf{true}`. The assumption $`d=\mathrm{ff}` is handled in the same way.

*36.2.* The pair $`(0,\overline{0})` is related, because $`\overline{0}\Downarrow\overline{0}`. Since $`c_0(0)=0`, the arrow clause would require $`(\lambda x{:}\mathsf{Nat}.\,\Omega)\,\overline{0}\Downarrow\overline{0}`. A derivation of this ends with the application rule, whose second premise is $`[x\mapsto\overline{0}]\Omega=\Omega\Downarrow\overline{0}`. But $`\Omega` has no value. The evaluation of the abstraction to itself is only the first premise of the application rule. The arrow clause constrains the second premise, the body after substitution. Both $`\lambda x{:}\mathsf{Nat}.\,0` and $`\lambda x{:}\mathsf{Nat}.\,\Omega` are values, and $`c_0` is the meaning of the first.

*36.3.* The sets are $`\{\bot,3\}`, $`\{\bot\}` and $`\{\bot,3\}`. The numeral $`\overline{3}` evaluates only to itself, and $`\Omega` has no value. A derivation of $`(\lambda x{:}\mathsf{Nat}.\,x)\,\overline{3}\Downarrow v` ends with the application rule, whose second premise is $`\overline{3}\Downarrow v`. So the first and third terms have the same values, and Lemma 36.5, applied in both directions, makes their sets equal.

*Further problem.* Induct on $`T`, with the term quantified inside the property. At a ground type, if $`d'=\bot` use Lemma 36.4(a). Otherwise $`d'` is a number or a truth value, and $`d'\sqsubseteq d` in a flat domain forces $`d'=d`. At $`T\to S`, let $`f'\sqsubseteq f` and $`f\lhd t`. Fix a related pair $`(d,u)`. The arrow clause gives $`f(d)\lhd_S t\,u`. The pointwise order gives $`f'(d)\sqsubseteq f(d)`. The hypothesis at $`S`, applied to the same term $`t\,u`, gives $`f'(d)\lhd_S t\,u`. The pair $`(d,u)` and the term $`t\,u` stay fixed. For $`K`: each $`g_j` lies below $`\bigsqcup_j g_j=\llbracket K\rrbracket `, so downward closure gives $`g_j\lhd K`. For $`j=1`, $`g_1(1)=\bot` while $`\llbracket K\rrbracket (1)=0`.

*Further reading.* The adequacy theorem for PCF is due to Plotkin, “LCF considered as a programming language”, _Theoretical Computer Science_ 5 (1977). In the Cambridge notes, read Definition 27 and Lemmas 33 and 35 alongside §§36.2–36.3.
