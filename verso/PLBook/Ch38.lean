import VersoManual

open Verso.Genre Manual

#doc (Manual) "Using Adequacy" =>
%%%
tag := "ch38"
file := "chapter-38"
%%%

Session 35 built a thirteen-line derivation of $`K\ \overline{1}\Downarrow 0` by hand. A program that adds two numbers by recursion needs a longer one: evaluated at $`\overline{2}` and $`\overline{1}`, it calls itself three times. Adequacy replaces that derivation by a calculation of the meaning. This session computes the meaning of the addition program and concludes what it evaluates to. Then it shows that two different programs have equal meanings and concludes that they evaluate to the same numeral.

*In this session.*

* *Definitions.* PCF terms and typing, the evaluation rules B-Value to B-Fix with the convention that $`t\Downarrow v` relates closed terms of one type, the meaning $`\llbracket t\rrbracket\rho` and the fact $`\llbracket\overline{n}\rrbracket=n` ([Session 35, Definitions 35.1–35.5](chapter-35/index.html#ch35-s1)). Soundness of evaluation, Theorem 35.8 ([Session 35, §35.4](chapter-35/index.html#ch35-s4)). Computational adequacy, Theorem 36.1 ([Session 36, §36.1](chapter-36/index.html#ch36-s1)), proved in [Session 37, §37.4](chapter-37/index.html#ch37-s4), and the consequence proved there: a closed term of type Nat has meaning $`\bot` exactly when it has no evaluation. The flat domain $`\mathbb{N}_\bot` and the fixed-point equation $`f(\mathrm{lfp}(f))=\mathrm{lfp}(f)` ([Session 34, Proposition 34.4](chapter-34/index.html#ch34-s1)). Canonical forms ([C.8](lambda-card/index.html#lambda-c8), Row 1).
* *New terms.* Full abstraction, named in §38.3 and used in no proof. [Glossary](glossary/index.html)
* *Corollary 38.2 (Equal meanings at type Nat).* Let $`t` and $`t'` be closed terms with $`\vdash t:\mathsf{Nat}`, $`\vdash t':\mathsf{Nat}` and $`\llbracket t\rrbracket=\llbracket t'\rrbracket`. Then for every natural number $`n`, $`t\Downarrow\overline{n}` if and only if $`t'\Downarrow\overline{n}`.
* *Board case.* Compute $`\llbracket A\ \overline{2}\ \overline{1}\rrbracket=3` and conclude $`A\ \overline{2}\ \overline{1}\Downarrow\overline{3}` (§38.1, six steps). Then prove Corollary 38.2 and apply it to $`A\ u\ w` and $`A\ w\ u` (§38.2).
* *Proof outline.* Meanings are computed with the clauses of Definition 35.5 and the fixed-point equation. No evaluation derivation is built. Lemma 38.1 is an induction on the first argument of $`A`. Corollary 38.2 goes from evaluation to meaning by Theorem 35.8 and back by Theorem 36.1.
* *From Session 37.* Session 37 proved adequacy. This last session of Part 3 adds no theory. It applies soundness and adequacy to a term that the earlier sessions did not treat, and it states what adequacy does not give.

# Computing a meaning
%%%
tag := "ch38-s1"
%%%

Two theorems connect evaluation and meaning. Soundness (Session 35, Theorem 35.8) goes from evaluation to meaning: if $`\vdash t:T` and $`t\Downarrow v`, then $`\llbracket t\rrbracket=\llbracket v\rrbracket`. Adequacy goes back, at ground types only. For example, $`\llbracket K\ \overline{1}\rrbracket=0` by Session 35, Proposition 35.6, and adequacy alone gives $`K\ \overline{1}\Downarrow 0`.

*Theorem 36.1 (Computational adequacy), restated.* Let $`t` be a closed term. If $`\vdash t:\mathsf{Nat}` and $`\llbracket t\rrbracket=n` for a natural number $`n`, then $`t\Downarrow\overline{n}`. If $`\vdash t:\mathsf{Bool}` and $`\llbracket t\rrbracket=\mathrm{tt}`, then $`t\Downarrow\mathsf{true}`. If $`\vdash t:\mathsf{Bool}` and $`\llbracket t\rrbracket=\mathrm{ff}`, then $`t\Downarrow\mathsf{false}`.

Every use of the theorem checks three premises. First, the term is closed: evaluation is defined only for closed terms (Definition 35.3), and a term with a free variable has a meaning only in an environment. Second, the term has a ground type, Nat or Bool: §38.3 shows that at a function type equal meanings do not give equal values. Third, the meaning is a number or a truth value. When the meaning is $`\bot`, adequacy concludes nothing, and Session 37, §37.4 uses soundness to show that the term has no evaluation. We apply the theorem to the following closed terms.

$$`J=\lambda p{:}\mathsf{Nat}\to\mathsf{Nat}\to\mathsf{Nat}.\ \lambda x{:}\mathsf{Nat}.\ \lambda y{:}\mathsf{Nat}.\ \mathsf{if}\ \mathsf{iszero}\ x\ \mathsf{then}\ y\ \mathsf{else}\ \mathsf{succ}\ (p\ (\mathsf{pred}\ x)\ y),\qquad A=\mathsf{fix}\ J.`

The arrow associates to the right and application to the left, so $`A\ \overline{2}\ \overline{1}` is $`(A\ \overline{2})\ \overline{1}`. Under $`p{:}\mathsf{Nat}\to\mathsf{Nat}\to\mathsf{Nat},\,x{:}\mathsf{Nat},\,y{:}\mathsf{Nat}` the conditional has type Nat. T-Abs three times and T-Fix give $`\vdash A:\mathsf{Nat}\to\mathsf{Nat}\to\mathsf{Nat}`, and T-App twice gives $`\vdash A\ \overline{2}\ \overline{1}:\mathsf{Nat}`. We call $`A` the addition term. On numerals it moves one successor at a time from its first argument to the result. Let $`\Phi=\llbracket J\rrbracket` and $`a=\llbracket A\rrbracket`. Write $`\mathit{inc}` for the function on $`\mathbb{N}_\bot` (not the term $`\mathit{inc}` of Session 33) with $`\mathit{inc}(n)=n+1` and $`\mathit{inc}(\bot)=\bot`, so that the succ clause of Definition 35.5 reads $`\llbracket\mathsf{succ}\ t_1\rrbracket\rho=\mathit{inc}(\llbracket t_1\rrbracket\rho)`. For $`g\in\llbracket\mathsf{Nat}\to\mathsf{Nat}\to\mathsf{Nat}\rrbracket` and $`d,e\in\mathbb{N}_\bot`, the abstraction clause three times gives $`\Phi(g)(d)(e)=\llbracket\mathsf{if}\ \mathsf{iszero}\ x\ \mathsf{then}\ y\ \mathsf{else}\ \mathsf{succ}\ (p\ (\mathsf{pred}\ x)\ y)\rrbracket\rho` with $`\rho=\rho_\varnothing[p\mapsto g][x\mapsto d][y\mapsto e]`. The iszero and conditional clauses give three cases, as for the countdown in Session 35, §35.3. The fix clause gives $`a=\mathrm{lfp}(\Phi)`, and the fixed-point equation gives $`a=\Phi(a)`, so the cases with $`g=a` describe $`a` itself.

1. $`\Phi(g)(\bot)(e)=\bot`.
2. $`\Phi(g)(0)(e)=\llbracket y\rrbracket\rho=e`.
3. $`\Phi(g)(k+1)(e)=\mathit{inc}(\llbracket p\ (\mathsf{pred}\ x)\ y\rrbracket\rho)=\mathit{inc}(g(k)(e))`, because $`\llbracket\mathsf{pred}\ x\rrbracket\rho=k`.

*Board case.* We must show $`A\ \overline{2}\ \overline{1}\Downarrow\overline{3}`.

1. The term $`A\ \overline{2}\ \overline{1}` is closed, and $`\vdash A\ \overline{2}\ \overline{1}:\mathsf{Nat}` (shown above).
2. The equation $`a=\Phi(a)` and case 2 with $`e=1` give $`a(0)(1)=\Phi(a)(0)(1)=1`.
3. The equation $`a=\Phi(a)`, case 3 with $`k=0` and step 2 give $`a(1)(1)=\mathit{inc}(a(0)(1))=\mathit{inc}(1)=2`.
4. The equation $`a=\Phi(a)`, case 3 with $`k=1` and step 3 give $`a(2)(1)=\mathit{inc}(a(1)(1))=\mathit{inc}(2)=3`.
5. The application clause twice and $`\llbracket\overline{n}\rrbracket=n` give $`\llbracket A\ \overline{2}\ \overline{1}\rrbracket=a(\llbracket\overline{2}\rrbracket)(\llbracket\overline{1}\rrbracket)=a(2)(1)=3`.
6. Apply Theorem 36.1 at type Nat with $`t=A\ \overline{2}\ \overline{1}` and $`n=3`. Steps 1 and 5 supply its premises. So $`A\ \overline{2}\ \overline{1}\Downarrow\overline{3}`.

No derivation was built. A derivation of $`A\ \overline{2}\ \overline{1}\Downarrow\overline{3}` uses B-Fix once for each call of $`A`, three times in all, as the derivation for $`K\ \overline{1}` in Session 35, §35.2 used it twice. Adequacy says that such a derivation exists, not how large it is. Steps 2–4 used only the fixed-point equation, not the fact that $`a` is the least fixed point. Leastness matters when the equation does not fix the value: for $`\Omega=\mathsf{fix}\ (\lambda x{:}\mathsf{Nat}.x)` the equation holds for every element of $`\mathbb{N}_\bot`, and only leastness gives $`\llbracket\Omega\rrbracket=\bot`.

*Lemma 38.1 (Meaning of the addition term).* For all natural numbers $`m,n`, $`a(m)(n)=m+n`. For every $`d\in\mathbb{N}_\bot`, $`a(\bot)(d)=\bot` and $`a(d)(\bot)=\bot`.

*Proof.* Case 1 and $`a=\Phi(a)` give $`a(\bot)(d)=\bot`. The rest is an induction on $`m` with

$$`R(m)\coloneqq a(m)(\bot)=\bot\ \wedge\ \forall n\in\mathbb{N},\ a(m)(n)=m+n.`

Case 2 gives $`a(0)(e)=e` for every $`e\in\mathbb{N}_\bot`, hence $`R(0)`. Assume $`R(m)`. Case 3 gives $`a(m+1)(e)=\mathit{inc}(a(m)(e))`. At $`e=\bot`, $`R(m)` gives $`\mathit{inc}(\bot)=\bot`. At $`e=n`, $`R(m)` gives $`\mathit{inc}(m+n)=(m+1)+n`. So $`R(m+1)` holds. $`\square`

# Equal meanings
%%%
tag := "ch38-s2"
%%%

Compare $`A\ \overline{2}\ \overline{1}` with $`A\ \overline{1}\ \overline{2}`. Lemma 38.1 gives both the meaning 3. A derivation for the first uses B-Fix three times, and its innermost call returns $`\overline{1}`. A derivation for the second uses B-Fix twice, and its innermost call returns $`\overline{2}`. The derivations differ, and both terms evaluate to $`\overline{3}`. The general fact uses both directions between evaluation and meaning.

*Corollary 38.2 (Equal meanings at type Nat).* Let $`t` and $`t'` be closed terms with $`\vdash t:\mathsf{Nat}`, $`\vdash t':\mathsf{Nat}` and $`\llbracket t\rrbracket=\llbracket t'\rrbracket`. Then for every natural number $`n`, $`t\Downarrow\overline{n}` if and only if $`t'\Downarrow\overline{n}`.

*Proof.* Fix $`n` and assume $`t\Downarrow\overline{n}`. We must show $`t'\Downarrow\overline{n}`. (1) Theorem 35.8 gives $`\llbracket t\rrbracket=\llbracket\overline{n}\rrbracket=n`. (2) The premise $`\llbracket t\rrbracket=\llbracket t'\rrbracket` gives $`\llbracket t'\rrbracket=n`. (3) Theorem 36.1 at type Nat, applied to the closed term $`t'`, gives $`t'\Downarrow\overline{n}`. The converse is (1)–(3) with $`t` and $`t'` exchanged. $`\square`

Since $`t\Downarrow v` requires $`\vdash v:\mathsf{Nat}` (Definition 35.3) and every value of type Nat is a numeral (C.8, Row 1), the corollary also says that $`t` has an evaluation exactly when $`t'` has one. Now let $`u` and $`w` be any closed terms of type Nat. By Lemma 38.1, $`a(d)(e)=a(e)(d)` for all $`d,e\in\mathbb{N}_\bot`: both sides are $`m+n` when $`d=m` and $`e=n` are numbers, and $`\bot` otherwise. The application clause gives $`\llbracket A\ u\ w\rrbracket=a(\llbracket u\rrbracket)(\llbracket w\rrbracket)=a(\llbracket w\rrbracket)(\llbracket u\rrbracket)=\llbracket A\ w\ u\rrbracket`. By Corollary 38.2, for every $`n`, $`A\ u\ w\Downarrow\overline{n}` if and only if $`A\ w\ u\Downarrow\overline{n}`. We did not need to know whether $`u` and $`w` have evaluations. For $`u=\Omega` and $`w=\overline{0}`, Lemma 38.1 gives both terms the meaning $`\bot`, so by Session 37, §37.4 neither has an evaluation. Operationally, $`A\ \Omega\ \overline{0}` fails in its guard, which must evaluate $`\Omega`, and $`A\ \overline{0}\ \Omega` fails in its result, which is $`\Omega`. A proof of the equivalence from the evaluation rules alone would have to compare derivations of different shapes for every $`u` and $`w`.

# What adequacy does not give
%%%
tag := "ch38-s3"
%%%

Adequacy concludes only at ground types. Consider $`\lambda x{:}\mathsf{Nat}.\ A\ x\ \overline{0}` and $`\lambda x{:}\mathsf{Nat}.\ x`. By the abstraction clause and Lemma 38.1, the first means $`d\mapsto a(d)(0)`, which maps each number $`m` to $`m+0=m` and $`\bot` to $`\bot`. So both terms mean the identity on $`\mathbb{N}_\bot`. Both are values, and a value evaluates only to itself. So the two terms have equal meanings and evaluate to different values. At a function type Theorem 36.1 has no conclusion. Equal meanings give equal results only under ground observation: for every closed $`u` of type Nat, the application clause gives $`\llbracket(\lambda x{:}\mathsf{Nat}.\ A\ x\ \overline{0})\ u\rrbracket=\llbracket(\lambda x{:}\mathsf{Nat}.\ x)\ u\rrbracket`, and Corollary 38.2 applies to the two applications.

Each clause of Definition 35.5 computes the meaning of a term from the meanings of its immediate subterms. So replacing a closed subterm of a program by a closed term of the same type with the same meaning leaves the meaning of the program unchanged, and by Corollary 38.2 no closed program of type Nat can tell the two subterms apart. The converse question is whether two closed terms that no closed program of ground type can tell apart always have the same meaning. A semantics for which the answer is yes is *fully abstract*, and the question is called *full abstraction*. For PCF and the semantics of Session 35 the answer is no. The domain $`\llbracket\mathsf{Bool}\to\mathsf{Bool}\to\mathsf{Bool}\rrbracket` contains a _parallel or_: a function that returns $`\mathrm{tt}` when either argument is $`\mathrm{tt}`, even if the other is $`\bot`. No PCF term has this meaning. Plotkin gave two closed terms whose meanings agree at every function that some PCF term means and differ at parallel or, and he proved that no closed program of ground type tells them apart. The proof lies outside this book (Further Reading).

# Exercises
%%%
tag := "ch38-s4"
number := false
%%%

*38.1.* Let $`L=\lambda x{:}\mathsf{Nat}.\ A\ x\ x`. Compute $`\llbracket L\ \overline{3}\rrbracket` with Lemma 38.1 and state what Theorem 36.1 gives. List the three premises you checked.

*38.2.* Compute $`\llbracket A\ \overline{0}\ (\mathsf{pred}\ \overline{0})\rrbracket`. Which theorem shows that the term has no evaluation, soundness or adequacy? In an attempted derivation, find the judgment that no rule concludes.

*Further problem.* Without Theorem 36.1, prove that $`u\Downarrow\overline{n}` implies $`A\ u\ \overline{0}\Downarrow\overline{n}` for every closed term $`u` and natural number $`n`. Use induction on $`n` as in Session 35, Exercise 35.2. Then prove the same fact with Lemma 38.1 and Corollary 38.2, and compare what each proof gives.

# Reading for the Seminar
%%%
tag := "ch38-s5"
number := false
%%%

*Definitions · 10 minutes.* State soundness and adequacy side by side with all their premises. Write the three cases of $`\Phi` and the fixed-point equation for $`a`.

*Joint proof · 30 minutes.* One person carries out the six steps of the board case in §38.1. A second proves Lemma 38.1 and writes $`R(m)` on the board. A third proves Corollary 38.2 and applies it to $`A\ u\ w` and $`A\ w\ u`, including $`u=\Omega` and $`w=\overline{0}`.

*Proof review · 20 minutes.* Compare $`\lambda x{:}\mathsf{Nat}.\ A\ x\ \overline{0}` with $`\lambda x{:}\mathsf{Nat}.\ x` and say which conclusion adequacy does not give. Do Exercise 38.2. Read the paragraph on full abstraction.

*Facilitator’s hint.* Every conclusion about evaluation passes through one of two theorems. Soundness goes from an evaluation to a meaning, and adequacy from a meaning to an evaluation. Name the theorem at each step.

# Solutions and Further Reading
%%%
tag := "ch38-s6"
number := false
%%%

*38.1.* The application and abstraction clauses give $`\llbracket L\ \overline{3}\rrbracket=\llbracket A\ x\ x\rrbracket(\rho_\varnothing[x\mapsto 3])=a(3)(3)=6`. The term $`L\ \overline{3}` is closed. T-App twice and T-Abs give $`\vdash L:\mathsf{Nat}\to\mathsf{Nat}`, and T-App gives $`\vdash L\ \overline{3}:\mathsf{Nat}`. The meaning 6 is a number. Theorem 36.1 gives $`L\ \overline{3}\Downarrow\overline{6}`.

*38.2.* The pred clause gives $`\llbracket\mathsf{pred}\ \overline{0}\rrbracket=\bot`, so $`\llbracket A\ \overline{0}\ (\mathsf{pred}\ \overline{0})\rrbracket=a(0)(\bot)=\bot` by Lemma 38.1. Soundness shows that the term has no evaluation: an evaluation would end in a numeral $`\overline{n}`, and Theorem 35.8 would give the meaning $`n\neq\bot`. Adequacy is not used. In an attempted derivation the guard gives $`\mathsf{iszero}\ \overline{0}\Downarrow\mathsf{true}`, and B-IfTrue needs an evaluation of the branch $`y` with $`\mathsf{pred}\ \overline{0}` substituted. No rule concludes $`\mathsf{pred}\ \overline{0}\Downarrow v`: B-PredSucc needs $`\overline{0}\Downarrow\mathsf{succ}\ nv_1`, and $`\overline{0}` evaluates only to itself.

*Further problem.* Induct on $`n` with $`Q(n)\coloneqq\forall u,\ (u\Downarrow\overline{n})\Rightarrow A\ u\ \overline{0}\Downarrow\overline{n}`. Unfold $`A` with B-Fix and B-App as in lines 1–4 of Session 35, §35.2, and apply B-App twice. It remains to derive $`\mathsf{if}\ \mathsf{iszero}\ u\ \mathsf{then}\ \overline{0}\ \mathsf{else}\ \mathsf{succ}\ (A\ (\mathsf{pred}\ u)\ \overline{0})\Downarrow\overline{n}`. For $`n=0`, B-IszeroZero and B-IfTrue with $`\overline{0}\Downarrow\overline{0}` give it. For $`n+1`, B-IszeroSucc gives the guard $`\mathsf{false}` and B-PredSucc gives $`\mathsf{pred}\ u\Downarrow\overline{n}`. $`Q(n)` gives $`A\ (\mathsf{pred}\ u)\ \overline{0}\Downarrow\overline{n}`, and B-Succ and B-IfFalse give the result $`\overline{n+1}`. With Lemma 38.1, $`\llbracket A\ u\ \overline{0}\rrbracket=a(\llbracket u\rrbracket)(0)=\llbracket u\rrbracket`, and Corollary 38.2 gives both directions at once, with no strengthened induction. The operational proof gives one direction and builds the derivation.

*Further reading.* G. D. Plotkin, “LCF considered as a programming language”, _Theoretical Computer Science_ 5 (1977), defines PCF, proves adequacy, and shows with parallel or that the semantics is not fully abstract. The same paper shows that adding a parallel conditional to the language makes the semantics fully abstract. The Cambridge notes treat the question in their chapter on full abstraction. Pierce, _Types and Programming Languages_, §12.1, proves that every well-typed term of the simply typed lambda calculus evaluates to a value. Its proof defines, by recursion on types, a set of terms for each type, and the arrow clause quantifies over the arguments in the set at the argument type, as Definition 36.2 does for related pairs. PCF has no such theorem, because $`\Omega` has no evaluation.

# Sources and Formalization
%%%
tag := "ch38-notes"
number := false
%%%

Theorem 36.1 is Theorem 31 of the Cambridge _Denotational Semantics_ lecture notes for 2025–26 (version of 5 December 2024). The addition term $`A` is this book’s. [Cambridge notes](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

* *Theorem 36.1.* Restated from Session 36; see [its notes](chapter-36/index.html#ch36-notes).
* *Lemma 38.1.* Formulated in this book. Paper proof only ([§38.1](chapter-38/index.html#ch38-s1)).
* *Corollary 38.2.* Formulated in this book. Paper proof only ([§38.2](chapter-38/index.html#ch38-s2)).
