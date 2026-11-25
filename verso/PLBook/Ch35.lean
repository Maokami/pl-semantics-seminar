import VersoManual

open Verso.Genre Manual

#doc (Manual) "Recursion and Evaluation in PCF" =>
%%%
tag := "ch35"
file := "chapter-35"
%%%

* *Definitions.* Types, terms, values, typing rules and the substitution $`[x\mapsto s]t` of the [Lambda language card C.2–C.3](lambda-card/index.html#lambda-c2), without Unit. Call by name ([C.1](lambda-card/index.html#lambda-c1)) and canonical forms ([C.8](lambda-card/index.html#lambda-c8), Row 1). The substitution and permutation lemmas for typing ([Session 25](chapter-25/index.html)). Derivations and their height ([Session 1, §1.4](chapter-01/index.html#ch01-s4); [Session 2, §2.4](chapter-02/index.html#ch02-s4)). Bottom $`\bot`, the order $`\sqsubseteq` and least upper bounds $`\bigsqcup` ([Session 8](chapter-08/index.html)). Domains, continuous functions, flat domains, function domains ordered pointwise, and the least fixed point $`\mathrm{lfp}(f)=\bigsqcup_{j}f^j(\bot)` of a continuous function $`f`, which satisfies $`f(\mathrm{lfp}(f))=\mathrm{lfp}(f)` ([Session 34](chapter-34/index.html)). PCF itself is defined in Definitions 35.1–35.5.
* *New terms.* PCF, numeral, recursion operator, soundness of evaluation. [Glossary and label key](glossary/index.html)
* *Theorem 35.8 \[Paper proof only: proof in this section\].* For every closed term $`t`, type $`T` and value $`v`, if $`\vdash t:T` and $`t\Downarrow v`, then $`\llbracket t\rrbracket=\llbracket v\rrbracket`.
* *Source.* Cambridge _Denotational Semantics_ lecture notes, §5.2 and chapter 6. They define PCF, its evaluation relation and its denotational semantics, and prove that evaluation is sound, which is Theorem 35.8. We use their rules and semantic clauses and write terms in the notation of the Lambda language card. The countdown example and Proposition 35.6 are this book’s. [Notes.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)
* *Board case.* B-Fix. First derive $`K\ \overline{1}\Downarrow 0` for the countdown $`K` (§35.2) and compute its approximations $`g_0,g_1,g_2` at the inputs 0 and 1 (§35.3). Then prove the B-Fix case and read it at line 4 of the derivation, where B-Fix is used.
* *Proof outline.* Induct on the derivation $`D` of $`t\Downarrow v` with $`P(D)\coloneqq\llbracket t\rrbracket=\llbracket v\rrbracket`. In each case compute $`\llbracket t\rrbracket` by the clause of Definition 35.5 for the conclusion, and apply the induction hypotheses to the premises. B-App uses Lemma 35.7 (substitution). B-Fix uses the fixed-point equation $`f(\mathrm{lfp}(f))=\mathrm{lfp}(f)`.
* *From Session 34.* Session 34 obtained the least fixed point of a continuous function as the least upper bound of its approximations. Here the term $`\mathsf{fix}\ t` means the least fixed point of the meaning of $`t`, and an evaluation unfolds $`\mathsf{fix}\ t` once at each use of B-Fix.

A recursive function can be run, and it can be given a meaning. Take the function $`K` of §35.1, which counts its argument down to zero and returns zero. Evaluating $`K\ \overline{1}` unfolds the recursive definition twice. To compute the meaning of $`K` at 1, we start from the function that knows no results and apply the recursive definition repeatedly; the approximation at stage 2 is the first that answers at 1. This session defines both computations for PCF and proves that they never disagree: a term that evaluates to a value has the same meaning as that value.

# PCF
%%%
tag := "ch35-s1"
%%%

PCF is the typed language of Booleans, natural numbers and functions from the [Lambda language card](lambda-card/index.html), with two changes. Application is evaluated by name, and a *recursion operator* $`\mathsf{fix}` is added.

*Definition 35.1 (Types, terms and values).*

$$`T ::= \mathsf{Bool}\mid\mathsf{Nat}\mid T\to T`

$$`t ::= x\mid\lambda x{:}T.t\mid t\ t\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{if}\ t\ \mathsf{then}\ t\ \mathsf{else}\ t\mid 0\mid\mathsf{succ}\ t\mid\mathsf{pred}\ t\mid\mathsf{iszero}\ t\mid\mathsf{fix}\ t`

$$`v ::= \mathsf{true}\mid\mathsf{false}\mid nv\mid\lambda x{:}T.t\qquad\qquad nv ::= 0\mid\mathsf{succ}\ nv`

All forms except $`\mathsf{fix}\ t` are those of C.2–C.3, with the same free variables, alpha-equivalence and substitution. The form $`\mathsf{fix}\ t` binds no variable, so $`[x\mapsto s](\mathsf{fix}\ t)=\mathsf{fix}\ ([x\mapsto s]t)`. For a natural number $`n`, the *numeral* $`\overline{n}` is the numeric value with $`n` successors: $`\overline{0}=0` and $`\overline{n+1}=\mathsf{succ}\ \overline{n}`. Every numeric value is a numeral.

*Definition 35.2 (Typing).* The judgment $`\Gamma\vdash t:T` is defined by the rules of C.2, the rules T-Var, T-Abs and T-App of C.3, and

$$`\frac{\Gamma\vdash t_1:T_1\to T_1}{\Gamma\vdash\mathsf{fix}\ t_1:T_1}\;\textsf{T-Fix}`

Each form of term is the conclusion of exactly one typing rule. So a term has at most one typing derivation in a given context, and at most one type. Let

$$`G=\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\ \lambda x{:}\mathsf{Nat}.\ \mathsf{if}\ \mathsf{iszero}\ x\ \mathsf{then}\ 0\ \mathsf{else}\ f\ (\mathsf{pred}\ x),\qquad K=\mathsf{fix}\ G.`

Under $`f{:}\mathsf{Nat}\to\mathsf{Nat},x{:}\mathsf{Nat}` the conditional has type Nat. T-Abs twice gives $`\vdash G:(\mathsf{Nat}\to\mathsf{Nat})\to(\mathsf{Nat}\to\mathsf{Nat})`, and T-Fix gives $`\vdash K:\mathsf{Nat}\to\mathsf{Nat}`. The term $`G` describes a function in terms of a given function $`f`. The term $`K` is the function that $`G` describes in terms of itself. We call $`K` the *countdown*: it counts its argument down to zero and returns zero.

*Definition 35.3 (Evaluation).* The judgment $`t\Downarrow v`, read “$`t` evaluates to $`v`”, is defined by the following rules.

$$`\frac{}{v\Downarrow v}\;\textsf{B-Value}\qquad\frac{t_1\Downarrow nv_1}{\mathsf{succ}\ t_1\Downarrow\mathsf{succ}\ nv_1}\;\textsf{B-Succ}\qquad\frac{t_1\Downarrow\mathsf{succ}\ nv_1}{\mathsf{pred}\ t_1\Downarrow nv_1}\;\textsf{B-PredSucc}`

$$`\frac{t_1\Downarrow 0}{\mathsf{iszero}\ t_1\Downarrow\mathsf{true}}\;\textsf{B-IszeroZero}\qquad\frac{t_1\Downarrow\mathsf{succ}\ nv_1}{\mathsf{iszero}\ t_1\Downarrow\mathsf{false}}\;\textsf{B-IszeroSucc}`

$$`\frac{t_1\Downarrow\mathsf{true}\quad t_2\Downarrow v}{\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\Downarrow v}\;\textsf{B-IfTrue}\qquad\frac{t_1\Downarrow\mathsf{false}\quad t_3\Downarrow v}{\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\Downarrow v}\;\textsf{B-IfFalse}`

$$`\frac{t_1\Downarrow\lambda x{:}T_{11}.t_{12}\quad[x\mapsto t_2]t_{12}\Downarrow v}{t_1\ t_2\Downarrow v}\;\textsf{B-App}\qquad\frac{t_1\ (\mathsf{fix}\ t_1)\Downarrow v}{\mathsf{fix}\ t_1\Downarrow v}\;\textsf{B-Fix}`

Following the source, a judgment $`t\Downarrow v` is formed only when $`\vdash t:T` and $`\vdash v:T` for one type $`T`. A rule instance may be used only if each of its judgments has this form. So every term in a derivation is closed and typable.

B-App substitutes the operand $`t_2` without evaluating it, as in call by name. B-Fix unfolds the recursion once: to evaluate $`\mathsf{fix}\ t_1`, evaluate $`t_1` applied to $`\mathsf{fix}\ t_1`. No rule evaluates the body of an abstraction. There is no rule for $`\mathsf{pred}\ 0`, unlike E-PredZero in C.2. We follow the source: $`\mathsf{pred}\ 0` has no evaluation.

For example, let $`\Omega=\mathsf{fix}\ (\lambda x{:}\mathsf{Nat}.x)`, so that $`\vdash\Omega:\mathsf{Nat}`. Then $`(\lambda y{:}\mathsf{Nat}.0)\ \Omega\Downarrow 0` by B-App. Its first premise is $`\lambda y{:}\mathsf{Nat}.0\Downarrow\lambda y{:}\mathsf{Nat}.0` by B-Value, and its second is $`[y\mapsto\Omega]0=0\Downarrow 0` by B-Value. The operand $`\Omega` is never evaluated. Indeed $`\Omega` has no evaluation. Suppose $`D` is a derivation of $`\Omega\Downarrow v` of least height, as in Session 2, §2.4. Since $`\Omega` is not a value, $`D` ends with B-Fix. Its premise $`(\lambda x{:}\mathsf{Nat}.x)\ \Omega\Downarrow v` ends with B-App, whose second premise is $`[x\mapsto\Omega]x=\Omega\Downarrow v`. That premise has a derivation of smaller height than $`D`, which contradicts the choice of $`D`.

# Evaluating a recursive function
%%%
tag := "ch35-s2"
%%%

Substituting $`K` for $`f` in the body of $`G` gives the abstraction $`H`:

$$`H=\lambda x{:}\mathsf{Nat}.\,H_x,\qquad H_u=\mathsf{if}\ \mathsf{iszero}\ u\ \mathsf{then}\ 0\ \mathsf{else}\ K\ (\mathsf{pred}\ u).`

For a closed term $`u`, $`[x\mapsto u]H_x=H_u`. The following thirteen judgments form a derivation of $`K\ \overline{1}\Downarrow 0`. Each line names its rule and the lines of its premises.

1. $`G\Downarrow G` by B-Value.
2. $`H\Downarrow H` by B-Value.
3. $`G\ K\Downarrow H` by B-App from 1 and 2. The body of $`G` with $`K` for $`f` is $`H`.
4. $`K\Downarrow H` by B-Fix from 3, because $`K=\mathsf{fix}\ G` and $`G\ (\mathsf{fix}\ G)=G\ K`.
5. $`\overline{1}\Downarrow\mathsf{succ}\ 0` by B-Value, because $`\overline{1}=\mathsf{succ}\ 0`.
6. $`\mathsf{iszero}\ \overline{1}\Downarrow\mathsf{false}` by B-IszeroSucc from 5.
7. $`\mathsf{pred}\ \overline{1}\Downarrow 0` by B-PredSucc from 5.
8. $`\mathsf{iszero}\ (\mathsf{pred}\ \overline{1})\Downarrow\mathsf{true}` by B-IszeroZero from 7.
9. $`0\Downarrow 0` by B-Value.
10. $`H_{\mathsf{pred}\ \overline{1}}\Downarrow 0` by B-IfTrue from 8 and 9.
11. $`K\ (\mathsf{pred}\ \overline{1})\Downarrow 0` by B-App from 4 and 10.
12. $`H_{\overline{1}}\Downarrow 0` by B-IfFalse from 6 and 11.
13. $`K\ \overline{1}\Downarrow 0` by B-App from 4 and 12.

Line 4 is a premise twice, at lines 11 and 13. Drawn as a tree, the derivation contains two copies of lines 1–4, so B-Fix is used twice: once for the outer call and once for the recursive call. Neither copy assumes that a call of $`K` terminates, since lines 1–4 stop at the abstraction $`H`. Call by name passes $`\mathsf{pred}\ \overline{1}`, not $`0`, to the recursive call (line 11), and its value is computed only when the guard inspects it (line 7). The branch $`K\ (\mathsf{pred}\ (\mathsf{pred}\ \overline{1}))` is never evaluated, because B-IfTrue has no premise for it. For every $`n`, $`K\ \overline{n}\Downarrow 0` with $`n+1` uses of B-Fix (Exercise 35.2).

# The meaning of a term
%%%
tag := "ch35-s3"
%%%

*Definition 35.4 (Domains and environments).* $`\mathbb{N}_\bot` is the flat domain of natural numbers: the set $`\mathbb{N}` with a new least element $`\bot`, in which distinct numbers are incomparable. $`\mathbb{B}_\bot` is the flat domain on $`\mathbb{B}=\{\mathrm{tt},\mathrm{ff}\}`. Each type $`T` gives a domain $`\llbracket T\rrbracket`:

$$`\llbracket\mathsf{Nat}\rrbracket=\mathbb{N}_\bot,\qquad\llbracket\mathsf{Bool}\rrbracket=\mathbb{B}_\bot,\qquad\llbracket T_1\to T_2\rrbracket=\text{the continuous functions from }\llbracket T_1\rrbracket\text{ to }\llbracket T_2\rrbracket\text{, ordered pointwise.}`

As in [Session 33, Definition 33.4](chapter-33/index.html#ch33-s2), an environment for a context $`\Gamma` is a function $`\rho` on $`\mathrm{dom}(\Gamma)` with $`\rho(x)\in\llbracket T\rrbracket` for each binding $`x{:}T` of $`\Gamma`. The empty context has one environment, the empty function $`\rho_\varnothing`. The environment $`\rho[x\mapsto d]` maps $`x` to $`d` and agrees with $`\rho` at every other variable. It updates an environment, whereas $`[x\mapsto s]t` substitutes in a term. The truth values $`\mathrm{tt},\mathrm{ff}` are distinct from the terms $`\mathsf{true},\mathsf{false}`, and the number $`n` is distinct from the numeral $`\overline{n}`.

*Definition 35.5 (Meaning).* For $`\Gamma\vdash t:T` and an environment $`\rho` for $`\Gamma`, the *meaning* $`\llbracket t\rrbracket\rho\in\llbracket T\rrbracket` is defined by structural recursion on $`t`. Here $`n` ranges over $`\mathbb{N}`.

$$`\begin{aligned}
&\llbracket x\rrbracket\rho=\rho(x)\qquad\llbracket 0\rrbracket\rho=0\qquad\llbracket\mathsf{true}\rrbracket\rho=\mathrm{tt}\qquad\llbracket\mathsf{false}\rrbracket\rho=\mathrm{ff}\\
&\llbracket\lambda x{:}T_1.t_2\rrbracket\rho=\text{the function }d\mapsto\llbracket t_2\rrbracket(\rho[x\mapsto d])\text{ on }\llbracket T_1\rrbracket\\
&\llbracket t_1\ t_2\rrbracket\rho=(\llbracket t_1\rrbracket\rho)(\llbracket t_2\rrbracket\rho)\\
&\llbracket\mathsf{fix}\ t_1\rrbracket\rho=\mathrm{lfp}(\llbracket t_1\rrbracket\rho)
\end{aligned}`

$$`\llbracket\mathsf{succ}\ t_1\rrbracket\rho=\begin{cases}n+1&\text{if }\llbracket t_1\rrbracket\rho=n\\\bot&\text{if }\llbracket t_1\rrbracket\rho=\bot\end{cases}\qquad\llbracket\mathsf{pred}\ t_1\rrbracket\rho=\begin{cases}n&\text{if }\llbracket t_1\rrbracket\rho=n+1\\\bot&\text{if }\llbracket t_1\rrbracket\rho\in\{0,\bot\}\end{cases}`

$$`\llbracket\mathsf{iszero}\ t_1\rrbracket\rho=\begin{cases}\mathrm{tt}&\text{if }\llbracket t_1\rrbracket\rho=0\\\mathrm{ff}&\text{if }\llbracket t_1\rrbracket\rho=n+1\\\bot&\text{if }\llbracket t_1\rrbracket\rho=\bot\end{cases}\qquad\llbracket\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\rrbracket\rho=\begin{cases}\llbracket t_2\rrbracket\rho&\text{if }\llbracket t_1\rrbracket\rho=\mathrm{tt}\\\llbracket t_3\rrbracket\rho&\text{if }\llbracket t_1\rrbracket\rho=\mathrm{ff}\\\bot&\text{if }\llbracket t_1\rrbracket\rho=\bot\end{cases}`

For a closed term $`t`, write $`\llbracket t\rrbracket` for $`\llbracket t\rrbracket\rho_\varnothing`. The abstraction clause must give a continuous function, and the fix clause needs $`\llbracket t_1\rrbracket\rho` to be continuous. The source proves, by induction on $`t`, that $`\llbracket t\rrbracket\rho` is continuous in each value $`\rho(x)`. We use this fact without proof. Two further facts follow from the clauses by induction. First, $`\llbracket\overline{n}\rrbracket=n` for every $`n`. Second, $`\llbracket t\rrbracket\rho` depends only on the values of $`\rho` at the free variables of $`t`, so $`\llbracket t\rrbracket\rho=\llbracket t\rrbracket` when $`t` is closed.

Now compute the meaning of $`G`. Let $`F=\llbracket G\rrbracket`. For $`g\in\llbracket\mathsf{Nat}\to\mathsf{Nat}\rrbracket` and $`d\in\mathbb{N}_\bot`, the abstraction clause twice gives $`F(g)(d)=\llbracket\mathsf{if}\ \mathsf{iszero}\ x\ \mathsf{then}\ 0\ \mathsf{else}\ f\ (\mathsf{pred}\ x)\rrbracket\rho` with $`\rho=\rho_\varnothing[f\mapsto g][x\mapsto d]`. The iszero clause gives $`\mathrm{tt}` at $`d=0`, $`\mathrm{ff}` at $`d=k+1` and $`\bot` at $`d=\bot`. The conditional clause then gives three cases.

1. $`F(g)(\bot)=\bot`.
2. $`F(g)(0)=\llbracket 0\rrbracket\rho=0`.
3. $`F(g)(k+1)=\llbracket f\ (\mathsf{pred}\ x)\rrbracket\rho=g(\llbracket\mathsf{pred}\ x\rrbracket\rho)=g(k)`.

By the fix clause, $`\llbracket K\rrbracket=\mathrm{lfp}(F)=\bigsqcup_j g_j`. Here $`g_0` is the least element of $`\llbracket\mathsf{Nat}\to\mathsf{Nat}\rrbracket`, the function with value $`\bot` everywhere, and $`g_{j+1}=F(g_j)`. We call $`g_j` the approximation of $`\llbracket K\rrbracket` at stage $`j`. The three cases above are the three clauses of the countdown operator of [Session 34, §34.2](chapter-34/index.html#ch34-s2), so $`g_j` is the function $`z_j` there, and the first part of Proposition 35.6 restates Lemma 34.6(3). At input 1, case 3 and then case 2 give

$$`g_0(1)=\bot,\qquad g_1(1)=g_0(0)=\bot,\qquad g_2(1)=g_1(0)=F(g_0)(0)=0.`

The table shows the first four stages at four inputs.

$$`\begin{array}{c|cccc} j & g_j(\bot) & g_j(0) & g_j(1) & g_j(2)\\ \hline 0 & \bot & \bot & \bot & \bot\\ 1 & \bot & 0 & \bot & \bot\\ 2 & \bot & 0 & 0 & \bot\\ 3 & \bot & 0 & 0 & 0 \end{array}`

The first answer at input 1 appears at stage 2. The derivation of $`K\ \overline{1}\Downarrow 0` in §35.2 used B-Fix twice.

*Proposition 35.6 (Approximations of the countdown) \[This book\] \[Paper proof only: proof in this section\].* For every natural number $`j`, $`g_j(\bot)=\bot`, and for every natural number $`k`, $`g_j(k)=0` if $`k<j` and $`g_j(k)=\bot` if $`k\ge j`. Consequently $`\llbracket K\rrbracket(\bot)=\bot`, and $`\llbracket K\ \overline{k}\rrbracket=\llbracket K\rrbracket(k)=0` for every natural number $`k`.

*Proof.* By induction on $`j` with the property

$$`Q(j)\coloneqq g_j(\bot)=\bot\ \wedge\ \forall k\in\mathbb{N},\ \bigl(k<j\Rightarrow g_j(k)=0\bigr)\wedge\bigl(k\ge j\Rightarrow g_j(k)=\bot\bigr).`

$`Q(0)` holds because $`g_0` has value $`\bot` everywhere and no $`k` satisfies $`k<0`. Assume $`Q(j)`. Case 1 gives $`g_{j+1}(\bot)=\bot`. Case 2 gives $`g_{j+1}(0)=0`, and $`0<j+1`. Case 3 gives $`g_{j+1}(k+1)=g_j(k)`. By $`Q(j)` this is $`0` if $`k<j`, that is, if $`k+1<j+1`, and $`\bot` if $`k\ge j`, that is, if $`k+1\ge j+1`. So $`Q(j+1)` holds.

A least upper bound in a function domain is computed at each input (Session 34). At $`\bot` every $`g_j` gives $`\bot`. At $`k` the values are $`\bot` for $`j\le k` and $`0` for $`j>k`, and their least upper bound in $`\mathbb{N}_\bot` is $`0`. Finally $`\llbracket K\ \overline{k}\rrbracket=\llbracket K\rrbracket(\llbracket\overline{k}\rrbracket)=\llbracket K\rrbracket(k)` by the application clause. $`\square`

# Soundness of evaluation
%%%
tag := "ch35-s4"
%%%

Proposition 35.6 gives $`\llbracket K\ \overline{1}\rrbracket=0`, and §35.2 derives $`K\ \overline{1}\Downarrow 0`. The two computations agree. Theorem 35.8 says that they always agree. Its B-App case needs one lemma. For example, substituting $`\overline{2}` for $`x` in $`\mathsf{succ}\ x` gives $`\llbracket\mathsf{succ}\ \overline{2}\rrbracket=3`, and the meaning of $`\mathsf{succ}\ x` in an environment that maps $`x` to $`\llbracket\overline{2}\rrbracket=2` is also $`3`.

*Lemma 35.7 (Substitution) \[Paper proof only: proof in this section\].* Let $`\Gamma,x{:}S\vdash t:T` and $`\vdash s:S`. Then for every environment $`\rho` for $`\Gamma`,

$$`\llbracket[x\mapsto s]t\rrbracket\rho=\llbracket t\rrbracket(\rho[x\mapsto\llbracket s\rrbracket]).`

The left side is defined because $`\Gamma\vdash[x\mapsto s]t:T` by the substitution lemma of Session 25, whose T-Fix case is immediate. The source states this property, in its chapter 6, for an open term $`s`.

*Proof.* By induction on $`t`, with the property $`\forall\Gamma,T,\rho,\ (\Gamma,x{:}S\vdash t:T)\Rightarrow\llbracket[x\mapsto s]t\rrbracket\rho=\llbracket t\rrbracket(\rho[x\mapsto\llbracket s\rrbracket])`. If $`t=x`, both sides are $`\llbracket s\rrbracket`, because $`s` is closed. If $`t` is another variable $`y`, both sides are $`\rho(y)`. If $`t=\lambda y{:}T_1.t_2`, rename $`y` so that $`y\neq x`; since $`s` is closed, no other renaming is needed. At each $`d\in\llbracket T_1\rrbracket` the left side gives $`\llbracket[x\mapsto s]t_2\rrbracket(\rho[y\mapsto d])`. Apply the induction hypothesis for $`t_2` with the context $`\Gamma,y{:}T_1` (permuting the bindings, Session 25) and the environment $`\rho[y\mapsto d]`. It gives $`\llbracket t_2\rrbracket(\rho[y\mapsto d][x\mapsto\llbracket s\rrbracket])`. Updates at the distinct variables $`x` and $`y` commute, so this is the right side at $`d`. Every other form binds no variable. Substitution acts on each immediate subterm, and the clause for the form combines the meanings of the immediate subterms in the same environment. Apply the induction hypothesis to each immediate subterm. $`\square`

*Theorem 35.8 (Soundness of evaluation) \[Paper proof only: proof in this section\].* For every closed term $`t`, type $`T` and value $`v`, if $`\vdash t:T` and $`t\Downarrow v`, then $`\llbracket t\rrbracket=\llbracket v\rrbracket`.

We prove $`P(D)` for every derivation $`D`, by induction on $`D`. For $`D` with conclusion $`t\Downarrow v`, the induction property is

$$`P(D)\coloneqq\llbracket t\rrbracket=\llbracket v\rrbracket.`

Both sides are defined, because every judgment of a derivation concerns closed typable terms (Definition 35.3).

*B-Fix (board case).* Suppose $`D` ends with B-Fix. Then $`t=\mathsf{fix}\ t_1` with $`\vdash t_1:T\to T`, and the premise of $`D` is $`D_1:t_1\ (\mathsf{fix}\ t_1)\Downarrow v`. Its induction hypothesis is

$$`P(D_1):\quad\llbracket t_1\ (\mathsf{fix}\ t_1)\rrbracket=\llbracket v\rrbracket.`

We must show $`\llbracket\mathsf{fix}\ t_1\rrbracket=\llbracket v\rrbracket`. Write $`f=\llbracket t_1\rrbracket`, a continuous function on $`\llbracket T\rrbracket`.

1. The fix clause of Definition 35.5 gives $`\llbracket\mathsf{fix}\ t_1\rrbracket=\mathrm{lfp}(f)`.
2. The fixed-point equation of Session 34 gives $`\mathrm{lfp}(f)=f(\mathrm{lfp}(f))`.
3. By step 1, $`f(\mathrm{lfp}(f))=\llbracket t_1\rrbracket(\llbracket\mathsf{fix}\ t_1\rrbracket)`. The application clause gives $`\llbracket t_1\rrbracket(\llbracket\mathsf{fix}\ t_1\rrbracket)=\llbracket t_1\ (\mathsf{fix}\ t_1)\rrbracket`.
4. Apply $`P(D_1)`: $`\llbracket t_1\ (\mathsf{fix}\ t_1)\rrbracket=\llbracket v\rrbracket`.

Together, $`\llbracket\mathsf{fix}\ t_1\rrbracket=\mathrm{lfp}(f)=f(\mathrm{lfp}(f))=\llbracket t_1\ (\mathsf{fix}\ t_1)\rrbracket=\llbracket v\rrbracket`. Steps 1–3 prove the *unfolding equation* $`\llbracket\mathsf{fix}\ t_1\rrbracket=\llbracket t_1\ (\mathsf{fix}\ t_1)\rrbracket`. It is the meaning of one use of B-Fix.

*Check on the countdown.* In §35.2, B-Fix is used at line 4, with $`t_1=G`. There the unfolding equation reads $`\llbracket K\rrbracket=\llbracket G\ K\rrbracket=F(\llbracket K\rrbracket)`, and the B-Fix case concludes $`\llbracket K\rrbracket=\llbracket H\rrbracket`. Applied to line 13, the theorem gives $`\llbracket K\ \overline{1}\rrbracket=\llbracket 0\rrbracket=0`. Proposition 35.6 obtains the same value as the least upper bound $`\bigsqcup_j g_j(1)`, reached at $`g_2(1)=0`. The theorem predicts the value. It does not say at which stage the value appears.

*B-App.* Suppose $`D` ends with B-App. Then $`t=t_1\ t_2`, and the premises are $`D_1:t_1\Downarrow\lambda x{:}T_{11}.t_{12}` and $`D_2:[x\mapsto t_2]t_{12}\Downarrow v`. By Definition 35.3 and inversion of T-App and T-Abs, $`\vdash t_2:T_{11}` and $`x{:}T_{11}\vdash t_{12}:T`. The application clause, $`P(D_1)`, the abstraction clause, Lemma 35.7 with the empty context, and $`P(D_2)` give, in this order,

$$`\llbracket t_1\ t_2\rrbracket=\llbracket t_1\rrbracket(\llbracket t_2\rrbracket)=\llbracket\lambda x{:}T_{11}.t_{12}\rrbracket(\llbracket t_2\rrbracket)=\llbracket t_{12}\rrbracket(\rho_\varnothing[x\mapsto\llbracket t_2\rrbracket])=\llbracket[x\mapsto t_2]t_{12}\rrbracket=\llbracket v\rrbracket.`

The operand $`t_2` is never evaluated. Its meaning enters only through Lemma 35.7, and it may be $`\bot`.

*The remaining rules.* For B-Value, $`t=v`. For B-IfTrue, $`P(D_1)` gives $`\llbracket t_1\rrbracket=\llbracket\mathsf{true}\rrbracket=\mathrm{tt}`, so the conditional clause gives $`\llbracket t\rrbracket=\llbracket t_2\rrbracket`, and $`P(D_2)` gives $`\llbracket t_2\rrbracket=\llbracket v\rrbracket`. B-IfFalse is symmetric. In the four rules for numbers, the numeric value $`nv_1` is a numeral $`\overline{n}`, so $`\llbracket nv_1\rrbracket=n`. For B-Succ, $`P(D_1)` gives $`\llbracket t_1\rrbracket=n`, so $`\llbracket\mathsf{succ}\ t_1\rrbracket=n+1=\llbracket\mathsf{succ}\ nv_1\rrbracket`. For B-PredSucc, $`P(D_1)` gives $`\llbracket t_1\rrbracket=n+1`, so $`\llbracket\mathsf{pred}\ t_1\rrbracket=n=\llbracket nv_1\rrbracket`. For B-IszeroZero and B-IszeroSucc, $`P(D_1)` gives $`\llbracket t_1\rrbracket=0` and $`\llbracket t_1\rrbracket=n+1`, and the iszero clause gives $`\mathrm{tt}=\llbracket\mathsf{true}\rrbracket` and $`\mathrm{ff}=\llbracket\mathsf{false}\rrbracket`. This proves $`P(D)` for every derivation $`D`, and hence the theorem. $`\square`

*Scope of the theorem.* Theorem 35.8 runs from evaluation to meaning. It can still show that a term has no evaluation. If $`\Omega\Downarrow v`, then $`\vdash v:\mathsf{Nat}`, so $`v` is a numeral $`\overline{m}` by canonical forms, and the theorem gives $`\llbracket\Omega\rrbracket=m`. But $`\llbracket\Omega\rrbracket` is the least fixed point of the identity on $`\mathbb{N}_\bot`, which is $`\bot`. So $`\Omega` has no evaluation, as §35.1 showed with heights. The converse of the theorem fails at function types. The values $`\lambda x{:}\mathsf{Nat}.x` and $`\lambda x{:}\mathsf{Nat}.\mathsf{pred}\ (\mathsf{succ}\ x)` have the same meaning, the identity on $`\mathbb{N}_\bot`, but each evaluates only to itself. At type Nat the converse holds: if $`\vdash t:\mathsf{Nat}` and $`\llbracket t\rrbracket=n`, then $`t\Downarrow\overline{n}`. This is computational adequacy, proved in [Sessions 36–37](chapter-36/index.html).

# Exercises
%%%
tag := "ch35-s5"
number := false
%%%

*35.1.* Find the least stage $`j` with $`g_j(3)=0`. In the derivation of $`K\ \overline{3}\Downarrow 0`, list the terms that the guards inspect, the value each guard obtains, and the number of uses of B-Fix.

*35.2.* Prove $`K\ \overline{n}\Downarrow 0` for every natural number $`n`. Induction on $`n` with the property $`K\ \overline{n}\Downarrow 0` fails at the recursive call. Find the failing step, and strengthen the property to every closed $`u` with $`u\Downarrow\overline{n}`.

*35.3.* Evaluate $`(\lambda y{:}\mathsf{Nat}.0)\ \Omega`. The meaning of $`\lambda y{:}\mathsf{Nat}.0` is the constant function $`c_0` of Session 34, with $`c_0(d)=0` for every $`d\in\mathbb{N}_\bot`. Compare $`c_0` with $`\llbracket K\rrbracket`. Use Theorem 35.8 to show that $`K\ \Omega` has no evaluation.

*35.4.* Replace B-App by a call-by-value rule with the three premises $`t_1\Downarrow\lambda x{:}T_{11}.t_{12}`, $`t_2\Downarrow v_2` and $`[x\mapsto v_2]t_{12}\Downarrow v`. Prove the new case of Theorem 35.8. Then find a closed term of type Nat whose meaning is a number but which has no evaluation under the new rule.

*Further problem.* Write $`\mathsf{not}\ u` for $`\mathsf{if}\ u\ \mathsf{then}\ \mathsf{false}\ \mathsf{else}\ \mathsf{true}`. Let $`E=\mathsf{fix}\ (\lambda f{:}\mathsf{Nat}\to\mathsf{Bool}.\ \lambda x{:}\mathsf{Nat}.\ \mathsf{if}\ \mathsf{iszero}\ x\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{not}\ (f\ (\mathsf{pred}\ x)))`, and let $`e_j` be the approximations of $`\llbracket E\rrbracket`. Prove by induction on $`j` that $`e_j(\bot)=\bot`, that $`e_j(k)` is $`\mathrm{tt}` for even $`k` and $`\mathrm{ff}` for odd $`k` when $`k<j`, and that $`e_j(k)=\bot` when $`k\ge j`. Then prove, without Sessions 36–37, that $`E\ \overline{n}\Downarrow\mathsf{true}` for even $`n` and $`E\ \overline{n}\Downarrow\mathsf{false}` for odd $`n`.

# Reading for the Seminar
%%%
tag := "ch35-s6"
number := false
%%%

*Definitions · 10 minutes.* Write the types of $`G` and $`K`. Derive $`K\Downarrow H` (lines 1–4 of §35.2) and say why it assumes nothing about the termination of a call of $`K`. Write the clauses of Definition 35.5 for abstraction, application and $`\mathsf{fix}`.

*Joint proof · 30 minutes.* One person builds the derivation of $`K\ \overline{1}\Downarrow 0` from the inner guard outward. A second person computes $`g_0,g_1,g_2` at the inputs 0 and 1 from the three cases of $`F`. A third person proves the B-Fix case of Theorem 35.8 and reads it at line 4 of the derivation.

*Proof review · 20 minutes.* Prove the B-App case with Lemma 35.7. Use Exercise 35.4 to locate where call by name enters. Apply Theorem 35.8 to $`K\ \Omega` and explain how a theorem about evaluations shows that a term has none.

*Facilitator’s hint.* Count the unfoldings of $`K` separately from the evaluation of the arithmetic. The input 0 still needs one unfolding.

# Solutions and Further Reading
%%%
tag := "ch35-s7"
number := false
%%%

*35.1.* The least stage is $`j=4`, by Proposition 35.6. The guards inspect $`\overline{3}`, $`\mathsf{pred}\ \overline{3}`, $`\mathsf{pred}\ (\mathsf{pred}\ \overline{3})` and $`\mathsf{pred}\ (\mathsf{pred}\ (\mathsf{pred}\ \overline{3}))`, which evaluate to $`\overline{3}`, $`\overline{2}`, $`\overline{1}` and $`0`. The first three guards give $`\mathsf{false}` and the last gives $`\mathsf{true}`. B-Fix is used four times, once for each call of $`K`.

*35.2.* With the property $`K\ \overline{n}\Downarrow 0`, the step for $`n+1` must evaluate $`K\ (\mathsf{pred}\ \overline{n+1})`. Its argument is not the numeral $`\overline{n}`, so the induction hypothesis does not apply. Prove instead, by induction on $`n`, the property $`Q'(n)\coloneqq\forall u,\ (u\Downarrow\overline{n})\Rightarrow K\ u\Downarrow 0`. In both cases use B-App with line 4 of §35.2 as its first premise, so it remains to derive $`H_u\Downarrow 0`. For $`n=0`, B-IszeroZero gives $`\mathsf{iszero}\ u\Downarrow\mathsf{true}`, and B-IfTrue with $`0\Downarrow 0` gives $`H_u\Downarrow 0`. For $`n+1`, $`u\Downarrow\mathsf{succ}\ \overline{n}` gives $`\mathsf{iszero}\ u\Downarrow\mathsf{false}` by B-IszeroSucc and $`\mathsf{pred}\ u\Downarrow\overline{n}` by B-PredSucc. $`Q'(n)` applied to $`\mathsf{pred}\ u` gives $`K\ (\mathsf{pred}\ u)\Downarrow 0`, and B-IfFalse gives $`H_u\Downarrow 0`. Take $`u=\overline{n}` with B-Value. Each call adds one copy of line 4, so the derivation of $`K\ \overline{n}\Downarrow 0` uses B-Fix $`n+1` times.

*35.3.* $`(\lambda y{:}\mathsf{Nat}.0)\ \Omega\Downarrow 0` by B-App, as in §35.1. The functions $`c_0` and $`\llbracket K\rrbracket` agree at every natural number and differ at $`\bot`: $`c_0(\bot)=0`, while $`\llbracket K\rrbracket(\bot)=\bot` by Proposition 35.6. If $`K\ \Omega\Downarrow v`, then $`v` is a numeral $`\overline{m}` and Theorem 35.8 gives $`\llbracket K\ \Omega\rrbracket=m`. But $`\llbracket K\ \Omega\rrbracket=\llbracket K\rrbracket(\llbracket\Omega\rrbracket)=\llbracket K\rrbracket(\bot)=\bot`. So $`K\ \Omega` has no evaluation. Operationally, the guard of $`H_\Omega` must evaluate $`\Omega`. Applying the two functions to $`\Omega` distinguishes them by evaluation.

*35.4.* The induction hypotheses are $`\llbracket t_1\rrbracket=\llbracket\lambda x{:}T_{11}.t_{12}\rrbracket`, $`\llbracket t_2\rrbracket=\llbracket v_2\rrbracket` and $`\llbracket[x\mapsto v_2]t_{12}\rrbracket=\llbracket v\rrbracket`. Then $`\llbracket t_1\ t_2\rrbracket=\llbracket t_{12}\rrbracket(\rho_\varnothing[x\mapsto\llbracket t_2\rrbracket])=\llbracket t_{12}\rrbracket(\rho_\varnothing[x\mapsto\llbracket v_2\rrbracket])=\llbracket[x\mapsto v_2]t_{12}\rrbracket=\llbracket v\rrbracket`, by Lemma 35.7 with $`s=v_2`. So the call-by-value rule is also sound. The term $`(\lambda y{:}\mathsf{Nat}.0)\ \Omega` has meaning $`0`, but the new rule needs a derivation of $`\Omega\Downarrow v_2`, and there is none. With these meanings, the converse of Theorem 35.8 at type Nat fails for call by value.

*Further problem.* The meaning of $`\mathsf{not}\ u` is $`\mathrm{ff}`, $`\mathrm{tt}` or $`\bot` when the meaning of $`u` is $`\mathrm{tt}`, $`\mathrm{ff}` or $`\bot`, by the conditional clause. As for $`F`, the functional of $`E` maps $`e` to the function with value $`\bot` at $`\bot`, $`\mathrm{tt}` at $`0`, and the negation of $`e(k)` at $`k+1`. Induct on $`j` as in Proposition 35.6. For $`k+1<j+1` the hypothesis gives the parity of $`k` at $`e_j(k)`, and negation turns it into the parity of $`k+1`. For $`k+1\ge j+1`, $`e_j(k)=\bot`, and its negation is $`\bot`. For the evaluations, strengthen as in Exercise 35.2: for every closed $`u` with $`u\Downarrow\overline{n}`, $`E\ u` evaluates to $`\mathsf{true}` if $`n` is even and to $`\mathsf{false}` if $`n` is odd. Induct on $`n`, unfolding $`E` with B-Fix and B-App as in lines 1–4 of §35.2. For $`n=0` the guard gives $`\mathsf{true}`, and B-IfTrue returns $`\mathsf{true}`. For $`n+1` the guard gives $`\mathsf{false}` and $`\mathsf{pred}\ u\Downarrow\overline{n}`. The induction hypothesis evaluates $`E\ (\mathsf{pred}\ u)` to the Boolean for the parity of $`n`, and the conditional $`\mathsf{not}` returns the other Boolean.

*Further reading · Different approximations, the same limit.* Replace the conditional in $`G` by $`\mathsf{if}\ \mathsf{iszero}\ x\ \mathsf{then}\ 0\ \mathsf{else}\ 0`. The new functional ignores its argument $`g`, so its approximation at stage 1 is already its least fixed point, which equals $`\llbracket K\rrbracket`. The countdown first answers at input $`k` only at stage $`k+1`. Equal meanings can have different increasing sequences of approximations. In the other direction, $`\lambda y{:}\mathsf{Nat}.\Omega` evaluates to itself, yet its application to $`0` has no evaluation. An evaluation to an abstraction says nothing about its applications, which is why Sessions 36–37 describe a function term by the evaluations of its applications.

*Further reading · Sources.* The Cambridge notes, chapter 6, also prove that meanings are compositional and use soundness to compare programs in all contexts. PCF comes from G. D. Plotkin, “LCF considered as a programming language”, _Theoretical Computer Science_ 5 (1977). Pierce, _Types and Programming Languages_, §11.11, adds $`\mathsf{fix}` to a call-by-value language with small-step rules. [Cambridge notes.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)
