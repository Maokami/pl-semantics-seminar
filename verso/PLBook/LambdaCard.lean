import VersoManual

open Verso.Genre Manual

#doc (Manual) "Lambda Language Card" =>
%%%
tag := "lambda-card"
file := "lambda-card"
number := false
%%%

C.1 accompanies [Session 22](chapter-22/index.html) and [Session 23](chapter-23/index.html). C.2 accompanies [Session 24](chapter-24/index.html). C.3 accompanies [Session 25](chapter-25/index.html) and [Session 26](chapter-26/index.html). C.4 accompanies [Session 27](chapter-27/index.html). C.5 accompanies [Session 28](chapter-28/index.html) and [Session 29](chapter-29/index.html). C.6 accompanies [Session 30](chapter-30/index.html), and C.7 accompanies [Session 31](chapter-31/index.html). C.8 collects the safety statements of Sessions 24–31 for [Session 32](chapter-32/index.html). Syntax, rules, rule names and notation follow Pierce, _Types and Programming Languages_ (TAPL). The last section lists the source sections. Inference rules, axioms and derivations are as in [A.3](imp-card/index.html#imp-a3). [English–Korean glossary](glossary/index.html)

*The language.* Part 2 studies one call-by-value language that grows section by section. The *typed language* of Session $`n` consists of the constructs of C.2, C.3, C.4, the let construct of C.5, C.6 and C.7 whose session is at most $`n`. Two further forms erase its type annotations: the untyped fragment of C.1 (Sessions 22–23) and the inference form of C.5 (Sessions 28–29). In a grammar, $`\cdots` stands for the forms given in the earlier sections of the typed language.

*Letters.* $`t,s,u` range over terms, $`v` over values, $`x,y,z` over term variables, $`T,S,U` over types, $`X,Y,Z` over type variables, $`\Gamma` over typing contexts, $`\sigma,\gamma` over type substitutions, $`C` over constraint sets, $`l` over locations, $`\mu` over stores and $`\Sigma` over store typings. Subscripts and primes only distinguish metavariables, as in $`t_1`, $`t_{12}` and $`t'`. In Part 1, $`\sigma,\sigma',\sigma''` denote IMP states and $`\sigma_1,\sigma_2` denote intermediate states, $`\mu` is a variant (Session 13), $`\gamma` a concretization (Session 17), and $`C` and $`S` are code and a stack (stack machine card). In Part 2 these letters have the meanings listed here.

*Judgments.* One step of evaluation is written $`t\to t'`, read “$`t` steps to $`t'`”. From Session 30 it is written $`t\mid\mu\to t'\mid\mu'`. Evaluation is small-step, call by value and left to right, and no rule steps inside an abstraction. The typing judgment is $`\Gamma\mid\Sigma\vdash t:T`. It is an inductively defined relation, separate from the syntax of terms: it holds exactly when it has a finite derivation by the typing rules below. Until Session 30, $`\Sigma` is the empty store typing and is not written. Thus $`\Gamma\vdash t:T` abbreviates $`\Gamma\mid\varnothing\vdash t:T`, and $`\vdash t:T` abbreviates $`\varnothing\mid\varnothing\vdash t:T`. A term $`t` is *well typed* if $`\vdash t:T` for some type $`T` (from Session 30: $`\varnothing\mid\Sigma\vdash t:T` for some $`\Sigma` and $`T`).

*Parentheses.* Application associates to the left and binds more tightly than every other form except projection. Projections associate to the left: $`t.2.1` is $`(t.2).1`. The body of an abstraction and the last part of if, let and case extend as far to the right as possible. The arrow associates to the right: $`T_1\to T_2\to T_3` is $`T_1\to(T_2\to T_3)`. The constructors $`\times` and $`+` bind more tightly than $`\to`. Other groupings are written with parentheses.

# C.1 Untyped lambda terms · Sessions 22–23
%%%
tag := "lambda-c1"
number := false
%%%

The untyped fragment has three term forms and one form of value:

$$`t ::= x\mid\lambda x.t\mid t\ t\qquad\qquad v ::= \lambda x.t`

A term is a variable, an *abstraction* $`\lambda x.t`, or an *application* $`t_1\,t_2`. The abstraction $`\lambda x.t` binds its *parameter* $`x` in its *body* $`t`. An occurrence of $`x` is *bound* when it lies in the body of an abstraction with parameter $`x`; it belongs to the nearest such abstraction. Every other occurrence is *free*. A *value* is an abstraction. By the rules for parentheses above, $`\lambda x.f\,x\,y` is $`\lambda x.((f\,x)\,y)`.

*Free variables.* The set $`\mathrm{FV}(t)` is defined by structural recursion:

$$`\mathrm{FV}(x)=\{x\}\qquad\mathrm{FV}(\lambda x.t_1)=\mathrm{FV}(t_1)\setminus\{x\}\qquad\mathrm{FV}(t_1\,t_2)=\mathrm{FV}(t_1)\cup\mathrm{FV}(t_2)`

A term $`t` is *closed* if $`\mathrm{FV}(t)=\varnothing`. For example, $`\mathrm{FV}(\lambda x.(\lambda x.x)\,y)=\{y\}`.

*Alpha-equivalence.* Rename the parameter of one abstraction $`\lambda x.t_1` inside a term, together with the free occurrences of $`x` in $`t_1`, to a variable that occurs nowhere in $`t_1`. Terms related by a finite sequence of such renamings and their reverses are *alpha-equivalent*. Thus $`\lambda x.\lambda y.x` and $`\lambda a.\lambda b.a` are alpha-equivalent, while $`\lambda a.\lambda b.b` is not alpha-equivalent to them. Alpha-equivalent terms are identified. Every definition and rule below applies to any representative, and a bound variable is renamed whenever a side condition requires it.

*Capture-avoiding substitution.* The term $`[x\mapsto s]t` replaces the free occurrences of $`x` in $`t` by $`s`:

$$`\begin{aligned}
[x\mapsto s]x&=s\\
[x\mapsto s]y&=y&&\text{if }y\neq x\\
[x\mapsto s](\lambda y.t_1)&=\lambda y.\,[x\mapsto s]t_1&&\text{if }y\neq x\text{ and }y\notin\mathrm{FV}(s)\\
[x\mapsto s](t_1\,t_2)&=([x\mapsto s]t_1)\,([x\mapsto s]t_2)
\end{aligned}`

When $`y=x` or $`y\in\mathrm{FV}(s)`, first rename the parameter $`y` to a variable that differs from $`x` and occurs nowhere in $`s` and $`t_1`. The third equation then applies. For example, $`[x\mapsto y](\lambda y.x\,y)=\lambda z.y\,z`, and $`[x\mapsto s](\lambda x.t_1)=\lambda x.t_1`.

*Call-by-value evaluation.* A *redex* is a term of the form $`(\lambda x.t_{12})\,t_2`. One step $`t\to t'` is defined by three rules:

$$`\frac{t_1\to t_1'}{t_1\,t_2\to t_1'\,t_2}\;\textsf{E-App1}\qquad\frac{t_2\to t_2'}{v_1\,t_2\to v_1\,t_2'}\;\textsf{E-App2}`

$$`\frac{}{(\lambda x.t_{12})\,v_2\to[x\mapsto v_2]t_{12}}\;\textsf{E-AppAbs}`

The operator is evaluated first. The operand is evaluated once the operator is a value. A redex is contracted only when its operand is a value. A rule without an evaluation premise, such as E-AppAbs, is a *computation rule*. A rule with an evaluation premise is a *congruence rule*. A term $`t` is a *normal form* if no $`t'` satisfies $`t\to t'`. Every value is a normal form. Write $`t\to^*t'` when $`t'` is reached from $`t` in zero or more steps, as for the finite paths of [A.6](imp-card/index.html#imp-a6).

*Call by name, for comparison.* The one-step relation $`t\to_{\mathrm n}t'` substitutes the operand without evaluating it. It has two rules:

$$`\frac{t_1\to_{\mathrm n}t_1'}{t_1\,t_2\to_{\mathrm n}t_1'\,t_2}\;\textsf{N-App1}\qquad\frac{}{(\lambda x.t_{12})\,t_2\to_{\mathrm n}[x\mapsto t_2]t_{12}}\;\textsf{N-AppAbs}`

Let $`\Omega=(\lambda x.x\,x)\,(\lambda x.x\,x)`. Then $`\Omega\to\Omega` by E-AppAbs. The term $`(\lambda y.\lambda z.z)\,\Omega` steps to itself by E-App2, whereas $`(\lambda y.\lambda z.z)\,\Omega\to_{\mathrm n}\lambda z.z` by N-AppAbs. The names N-App1 and N-AppAbs are this book’s.

# C.2 Booleans and natural numbers · Session 24
%%%
tag := "lambda-c2"
number := false
%%%

The typed language starts with Booleans and natural numbers. It has no variables yet.

$$`t ::= \mathsf{true}\mid\mathsf{false}\mid\mathsf{if}\ t\ \mathsf{then}\ t\ \mathsf{else}\ t\mid 0\mid\mathsf{succ}\ t\mid\mathsf{pred}\ t\mid\mathsf{iszero}\ t`

$$`v ::= \mathsf{true}\mid\mathsf{false}\mid nv\qquad\qquad nv ::= 0\mid\mathsf{succ}\ nv`

In $`\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3` the term $`t_1` is the *guard*. A *numeric value* $`nv` is $`0` or the successor of a numeric value. The term $`\mathsf{succ}\ (\mathsf{pred}\ 0)` is not a value: its argument must still step.

*Evaluation.*

$$`\frac{}{\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\to t_2}\;\textsf{E-IfTrue}\qquad\frac{}{\mathsf{if}\ \mathsf{false}\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\to t_3}\;\textsf{E-IfFalse}`

$$`\frac{t_1\to t_1'}{\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3\to\mathsf{if}\ t_1'\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3}\;\textsf{E-If}\qquad\frac{t_1\to t_1'}{\mathsf{succ}\ t_1\to\mathsf{succ}\ t_1'}\;\textsf{E-Succ}`

$$`\frac{}{\mathsf{pred}\ 0\to 0}\;\textsf{E-PredZero}\qquad\frac{}{\mathsf{pred}\ (\mathsf{succ}\ nv_1)\to nv_1}\;\textsf{E-PredSucc}\qquad\frac{t_1\to t_1'}{\mathsf{pred}\ t_1\to\mathsf{pred}\ t_1'}\;\textsf{E-Pred}`

$$`\frac{}{\mathsf{iszero}\ 0\to\mathsf{true}}\;\textsf{E-IszeroZero}\qquad\frac{}{\mathsf{iszero}\ (\mathsf{succ}\ nv_1)\to\mathsf{false}}\;\textsf{E-IszeroSucc}\qquad\frac{t_1\to t_1'}{\mathsf{iszero}\ t_1\to\mathsf{iszero}\ t_1'}\;\textsf{E-IsZero}`

A closed term is *stuck* if it is a normal form but not a value. For example, $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` and $`\mathsf{succ}\ \mathsf{false}` are stuck.

*Types and typing.*

$$`T ::= \mathsf{Bool}\mid\mathsf{Nat}`

$$`\frac{}{\Gamma\vdash\mathsf{true}:\mathsf{Bool}}\;\textsf{T-True}\qquad\frac{}{\Gamma\vdash\mathsf{false}:\mathsf{Bool}}\;\textsf{T-False}\qquad\frac{\Gamma\vdash t_1:\mathsf{Bool}\quad\Gamma\vdash t_2:T\quad\Gamma\vdash t_3:T}{\Gamma\vdash\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3:T}\;\textsf{T-If}`

$$`\frac{}{\Gamma\vdash 0:\mathsf{Nat}}\;\textsf{T-Zero}\qquad\frac{\Gamma\vdash t_1:\mathsf{Nat}}{\Gamma\vdash\mathsf{succ}\ t_1:\mathsf{Nat}}\;\textsf{T-Succ}\qquad\frac{\Gamma\vdash t_1:\mathsf{Nat}}{\Gamma\vdash\mathsf{pred}\ t_1:\mathsf{Nat}}\;\textsf{T-Pred}\qquad\frac{\Gamma\vdash t_1:\mathsf{Nat}}{\Gamma\vdash\mathsf{iszero}\ t_1:\mathsf{Bool}}\;\textsf{T-IsZero}`

Here $`\Gamma` is a typing context (C.3). The rules of this section do not inspect it. Session 24 uses only the empty context and writes $`\vdash t:T`. For example, $`\vdash\mathsf{if}\ \mathsf{iszero}\ 0\ \mathsf{then}\ \mathsf{succ}\ 0\ \mathsf{else}\ 0:\mathsf{Nat}`. The stuck term $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` has no type, because T-If requires the guard to have type Bool. T-If types both branches, including the one that evaluation discards.

# C.3 Functions and Unit · Sessions 25–26
%%%
tag := "lambda-c3"
number := false
%%%

$$`T ::= \cdots\mid T\to T\mid\mathsf{Unit}`

$$`t ::= \cdots\mid x\mid\lambda x{:}T.t\mid t\ t\mid\mathsf{unit}\qquad\qquad v ::= \cdots\mid\lambda x{:}T.t\mid\mathsf{unit}`

The annotation $`T` in $`\lambda x{:}T.t` is the *parameter type*. The abstraction binds $`x` in $`t`. Free variables, alpha-equivalence and substitution extend those of C.1. In particular $`\mathrm{FV}(\lambda x{:}T.t_1)=\mathrm{FV}(t_1)\setminus\{x\}`, and $`[x\mapsto s](\lambda y{:}T.t_1)=\lambda y{:}T.\,[x\mapsto s]t_1` under the side condition of C.1. Constants have no free variables and are unchanged by substitution. At every construct that binds no variable, $`\mathrm{FV}` takes the union over the immediate subterms and substitution acts on each immediate subterm. Each later section names its binders. At each of them, substitution renames the bound variable as in C.1.

*Typing contexts.*

$$`\Gamma ::= \varnothing\mid\Gamma,x{:}T`

A *typing context* is a finite sequence of bindings. $`\mathrm{dom}(\Gamma)` is the set of variables it binds, and $`x{:}T\in\Gamma` means that the binding $`x{:}T` occurs in $`\Gamma`. The extension $`\Gamma,x{:}T` is formed only when $`x\notin\mathrm{dom}(\Gamma)`. A bound variable is renamed when necessary to meet this condition.

*Typing.*

$$`\frac{x{:}T\in\Gamma}{\Gamma\vdash x:T}\;\textsf{T-Var}\qquad\frac{\Gamma,x{:}T_1\vdash t_2:T_2}{\Gamma\vdash\lambda x{:}T_1.t_2:T_1\to T_2}\;\textsf{T-Abs}`

$$`\frac{\Gamma\vdash t_1:T_{11}\to T_{12}\quad\Gamma\vdash t_2:T_{11}}{\Gamma\vdash t_1\,t_2:T_{12}}\;\textsf{T-App}\qquad\frac{}{\Gamma\vdash\mathsf{unit}:\mathsf{Unit}}\;\textsf{T-Unit}`

*Evaluation.* E-App1 and E-App2 are the rules of C.1, with $`v` now ranging over all values of the typed language. The computation rule carries the annotation:

$$`\frac{}{(\lambda x{:}T_{11}.t_{12})\,v_2\to[x\mapsto v_2]t_{12}}\;\textsf{E-AppAbs}`

The constant $`\mathsf{unit}` is a value and has no rule. For example, $`\vdash(\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x)\,0:\mathsf{Nat}` by T-App, and $`(\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x)\,0\to\mathsf{succ}\ 0` by E-AppAbs. Erasing each annotation, so that $`\lambda x{:}T.` becomes $`\lambda x.`, maps the function terms of this section to C.1 and E-AppAbs to the rule of C.1.

*Sequencing.* The term $`t_1;t_2` abbreviates $`(\lambda x{:}\mathsf{Unit}.t_2)\,t_1`, where $`x\notin\mathrm{FV}(t_2)`. It evaluates $`t_1` to a value, discards it and continues with $`t_2`. Session 30 uses it.

# C.4 Products and sums · Session 27
%%%
tag := "lambda-c4"
number := false
%%%

$$`T ::= \cdots\mid T\times T\mid T+T`

$$`t ::= \cdots\mid\{t,t\}\mid t.1\mid t.2\mid\mathsf{inl}\ t\ \mathsf{as}\ T\mid\mathsf{inr}\ t\ \mathsf{as}\ T\mid\mathsf{case}\ t\ \mathsf{of}\ \mathsf{inl}\ x\Rightarrow t\mid\mathsf{inr}\ x\Rightarrow t`

$$`v ::= \cdots\mid\{v,v\}\mid\mathsf{inl}\ v\ \mathsf{as}\ T\mid\mathsf{inr}\ v\ \mathsf{as}\ T`

The *projections* $`t.1` and $`t.2` select the components of a *pair* $`\{t_1,t_2\}`. The *injections* $`\mathsf{inl}\ t\ \mathsf{as}\ T` and $`\mathsf{inr}\ t\ \mathsf{as}\ T` carry the whole sum type $`T`, which the injected term alone does not determine. In $`\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2`, the variable $`x_1` is bound in $`t_1` and $`x_2` is bound in $`t_2`.

*Evaluation of pairs.*

$$`\frac{}{\{v_1,v_2\}.1\to v_1}\;\textsf{E-PairBeta1}\qquad\frac{}{\{v_1,v_2\}.2\to v_2}\;\textsf{E-PairBeta2}\qquad\frac{t_1\to t_1'}{t_1.1\to t_1'.1}\;\textsf{E-Proj1}\qquad\frac{t_1\to t_1'}{t_1.2\to t_1'.2}\;\textsf{E-Proj2}`

$$`\frac{t_1\to t_1'}{\{t_1,t_2\}\to\{t_1',t_2\}}\;\textsf{E-Pair1}\qquad\frac{t_2\to t_2'}{\{v_1,t_2\}\to\{v_1,t_2'\}}\;\textsf{E-Pair2}`

*Evaluation of sums.*

$$`\frac{}{\mathsf{case}\ (\mathsf{inl}\ v_0\ \mathsf{as}\ T_0)\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2\to[x_1\mapsto v_0]t_1}\;\textsf{E-CaseInl}`

$$`\frac{}{\mathsf{case}\ (\mathsf{inr}\ v_0\ \mathsf{as}\ T_0)\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2\to[x_2\mapsto v_0]t_2}\;\textsf{E-CaseInr}`

$$`\frac{t_0\to t_0'}{\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2\to\mathsf{case}\ t_0'\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2}\;\textsf{E-Case}`

$$`\frac{t_1\to t_1'}{\mathsf{inl}\ t_1\ \mathsf{as}\ T_2\to\mathsf{inl}\ t_1'\ \mathsf{as}\ T_2}\;\textsf{E-Inl}\qquad\frac{t_1\to t_1'}{\mathsf{inr}\ t_1\ \mathsf{as}\ T_2\to\mathsf{inr}\ t_1'\ \mathsf{as}\ T_2}\;\textsf{E-Inr}`

*Typing.*

$$`\frac{\Gamma\vdash t_1:T_1\quad\Gamma\vdash t_2:T_2}{\Gamma\vdash\{t_1,t_2\}:T_1\times T_2}\;\textsf{T-Pair}\qquad\frac{\Gamma\vdash t_1:T_{11}\times T_{12}}{\Gamma\vdash t_1.1:T_{11}}\;\textsf{T-Proj1}\qquad\frac{\Gamma\vdash t_1:T_{11}\times T_{12}}{\Gamma\vdash t_1.2:T_{12}}\;\textsf{T-Proj2}`

$$`\frac{\Gamma\vdash t_1:T_1}{\Gamma\vdash\mathsf{inl}\ t_1\ \mathsf{as}\ T_1+T_2:T_1+T_2}\;\textsf{T-Inl}\qquad\frac{\Gamma\vdash t_1:T_2}{\Gamma\vdash\mathsf{inr}\ t_1\ \mathsf{as}\ T_1+T_2:T_1+T_2}\;\textsf{T-Inr}`

$$`\frac{\Gamma\vdash t_0:T_1+T_2\quad\Gamma,x_1{:}T_1\vdash t_1:T\quad\Gamma,x_2{:}T_2\vdash t_2:T}{\Gamma\vdash\mathsf{case}\ t_0\ \mathsf{of}\ \mathsf{inl}\ x_1\Rightarrow t_1\mid\mathsf{inr}\ x_2\Rightarrow t_2:T}\;\textsf{T-Case}`

For example, $`\{\mathsf{succ}\ 0,\mathsf{true}\}.2\to\mathsf{true}` by E-PairBeta2, and $`\vdash\mathsf{inl}\ 0\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Bool}:\mathsf{Nat}+\mathsf{Bool}` by T-Inl.

# C.5 Inference form, let and type schemes · Sessions 28–29
%%%
tag := "lambda-c5"
number := false
%%%

*Unannotated terms · Session 28.* The inference form erases the type annotations of the typed language:

$$`t ::= x\mid\lambda x.t\mid t\ t\mid\mathsf{unit}\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{if}\ t\ \mathsf{then}\ t\ \mathsf{else}\ t\mid 0\mid\mathsf{succ}\ t\mid\mathsf{pred}\ t\mid\mathsf{iszero}\ t\mid\{t,t\}\mid t.1\mid t.2`

Session 29 adds $`\mathsf{let}\ x=t\ \mathsf{in}\ t` (below). Values and evaluation rules are those of C.1–C.4 with the annotations erased. Thus E-AppAbs reads $`(\lambda x.t_{12})\,v_2\to[x\mapsto v_2]t_{12}`, and $`t_1;t_2` abbreviates $`(\lambda x.t_2)\,t_1` with $`x\notin\mathrm{FV}(t_2)`. Sums are not part of the inference form.

*Types with type variables.*

$$`T ::= X\mid\mathsf{Bool}\mid\mathsf{Nat}\mid\mathsf{Unit}\mid T\to T\mid T\times T`

Type variables $`X,Y,Z` are drawn from an infinite set. In this section a type variable stands for a type that inference has not yet determined, and it needs no binder. $`\mathrm{FV}(T)` is the set of type variables occurring in $`T`.

*Typing unannotated terms.* The typing rules are those of C.2–C.4 for the forms above, with T-Abs replaced by its unannotated form. In it the parameter type $`T_1` is any type:

$$`\frac{\Gamma,x{:}T_1\vdash t_2:T_2}{\Gamma\vdash\lambda x.t_2:T_1\to T_2}\;\textsf{T-Abs}`

For example, $`\vdash\lambda x.x:\mathsf{Nat}\to\mathsf{Nat}` and $`\vdash\lambda x.x:X\to X`.

*Type substitutions.* A *type substitution* $`\sigma=[X_1\mapsto T_1,\ldots,X_n\mapsto T_n]`, with distinct $`X_i`, is a finite map from type variables to types. $`\mathrm{dom}(\sigma)=\{X_1,\ldots,X_n\}`, and $`[\,]` is the empty substitution. $`\sigma T` replaces every occurrence of each $`X_i` in $`T` by $`T_i`, all at once. For example, $`[X\mapsto\mathsf{Nat},Y\mapsto X\to X](X\to Y)=\mathsf{Nat}\to(X\to X)`. A substitution acts on a context by acting on each type in it, and on a constraint set by acting on both sides of each equation. Composition is $`(\sigma\circ\gamma)T=\sigma(\gamma T)`. We say $`\sigma` is *more general* than $`\sigma'`, written $`\sigma\sqsubseteq\sigma'`, if $`\sigma'=\gamma\circ\sigma` for some substitution $`\gamma`.

*Constraint sets.* A *constraint set* $`C` is a finite set of equations $`S=T` between types. A substitution $`\sigma` *unifies* $`C` if $`\sigma S` and $`\sigma T` are identical for every equation $`S=T` in $`C`. A *principal unifier* of $`C` is a unifier $`\sigma` of $`C` such that $`\sigma\sqsubseteq\sigma'` for every unifier $`\sigma'` of $`C`.

*Constraint typing.* The judgment $`\Gamma\vdash t:T\mid_{\mathcal X}C` reads: $`t` has type $`T` under $`\Gamma` whenever the equations in $`C` hold. $`\mathcal X` is the set of type variables introduced in the derivation. Every type variable that a rule adds to $`\mathcal X` is *fresh*: it differs from every other type variable in the derivation, in $`\Gamma` and in the other parts of the conclusion. TAPL writes this requirement as explicit side conditions.

$$`\frac{x{:}T\in\Gamma}{\Gamma\vdash x:T\mid_{\varnothing}\varnothing}\;\textsf{CT-Var}\qquad\frac{\Gamma,x{:}X\vdash t_2:T_2\mid_{\mathcal X}C\quad X\ \text{fresh}}{\Gamma\vdash\lambda x.t_2:X\to T_2\mid_{\mathcal X\cup\{X\}}C}\;\textsf{CT-AbsInf}`

$$`\frac{\Gamma\vdash t_1:T_1\mid_{\mathcal X_1}C_1\quad\Gamma\vdash t_2:T_2\mid_{\mathcal X_2}C_2\quad X\ \text{fresh}}{\Gamma\vdash t_1\,t_2:X\mid_{\mathcal X_1\cup\mathcal X_2\cup\{X\}}C_1\cup C_2\cup\{T_1=T_2\to X\}}\;\textsf{CT-App}`

$$`\frac{}{\Gamma\vdash\mathsf{true}:\mathsf{Bool}\mid_{\varnothing}\varnothing}\;\textsf{CT-True}\qquad\frac{}{\Gamma\vdash\mathsf{false}:\mathsf{Bool}\mid_{\varnothing}\varnothing}\;\textsf{CT-False}\qquad\frac{}{\Gamma\vdash 0:\mathsf{Nat}\mid_{\varnothing}\varnothing}\;\textsf{CT-Zero}`

$$`\frac{\Gamma\vdash t_1:T\mid_{\mathcal X}C}{\Gamma\vdash\mathsf{succ}\ t_1:\mathsf{Nat}\mid_{\mathcal X}C\cup\{T=\mathsf{Nat}\}}\;\textsf{CT-Succ}\qquad\frac{\Gamma\vdash t_1:T\mid_{\mathcal X}C}{\Gamma\vdash\mathsf{pred}\ t_1:\mathsf{Nat}\mid_{\mathcal X}C\cup\{T=\mathsf{Nat}\}}\;\textsf{CT-Pred}`

$$`\frac{\Gamma\vdash t_1:T\mid_{\mathcal X}C}{\Gamma\vdash\mathsf{iszero}\ t_1:\mathsf{Bool}\mid_{\mathcal X}C\cup\{T=\mathsf{Nat}\}}\;\textsf{CT-IsZero}`

$$`\frac{\Gamma\vdash t_1:T_1\mid_{\mathcal X_1}C_1\quad\Gamma\vdash t_2:T_2\mid_{\mathcal X_2}C_2\quad\Gamma\vdash t_3:T_3\mid_{\mathcal X_3}C_3}{\Gamma\vdash\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3:T_2\mid_{\mathcal X_1\cup\mathcal X_2\cup\mathcal X_3}C_1\cup C_2\cup C_3\cup\{T_1=\mathsf{Bool},T_2=T_3\}}\;\textsf{CT-If}`

*Unit and pairs.* TAPL gives no constraint rules for these forms. This book uses the following.

$$`\frac{}{\Gamma\vdash\mathsf{unit}:\mathsf{Unit}\mid_{\varnothing}\varnothing}\;\textsf{CT-Unit}\qquad\frac{\Gamma\vdash t_1:T_1\mid_{\mathcal X_1}C_1\quad\Gamma\vdash t_2:T_2\mid_{\mathcal X_2}C_2}{\Gamma\vdash\{t_1,t_2\}:T_1\times T_2\mid_{\mathcal X_1\cup\mathcal X_2}C_1\cup C_2}\;\textsf{CT-Pair}`

$$`\frac{\Gamma\vdash t_1:T\mid_{\mathcal X}C\quad X_1,X_2\ \text{fresh}}{\Gamma\vdash t_1.1:X_1\mid_{\mathcal X\cup\{X_1,X_2\}}C\cup\{T=X_1\times X_2\}}\;\textsf{CT-Proj1}\qquad\frac{\Gamma\vdash t_1:T\mid_{\mathcal X}C\quad X_1,X_2\ \text{fresh}}{\Gamma\vdash t_1.2:X_2\mid_{\mathcal X\cup\{X_1,X_2\}}C\cup\{T=X_1\times X_2\}}\;\textsf{CT-Proj2}`

For example, under $`x{:}X` the rule CT-Var gives $`x:X\mid_{\varnothing}\varnothing`, and CT-Succ gives $`\mathsf{succ}\ x:\mathsf{Nat}\mid_{\varnothing}\{X=\mathsf{Nat}\}`. Then CT-AbsInf gives $`\vdash\lambda x.\mathsf{succ}\ x:X\to\mathsf{Nat}\mid_{\{X\}}\{X=\mathsf{Nat}\}`.

*Solutions and principal types.* Suppose $`\Gamma\vdash t:S\mid_{\mathcal X}C`. A *solution* for $`(\Gamma,t,S,C)` is a pair $`(\sigma,T)` such that $`\sigma` unifies $`C` and $`\sigma S=T`. It is *principal* if $`\sigma\sqsubseteq\sigma'` for every solution $`(\sigma',T')`. The type $`T` of a principal solution is a *principal type* of $`t` under $`\Gamma`.

*Unification.* The function $`\mathrm{unify}` takes a constraint set and either fails or returns a substitution. Its cases are tried in order:

$$`\begin{aligned}
\mathrm{unify}(\varnothing)&=[\,]\\
\mathrm{unify}(\{S=T\}\cup C')&=\begin{cases}
\mathrm{unify}(C') & \text{if } S \text{ and } T \text{ are identical}\\
\mathrm{unify}([X\mapsto T]C')\circ[X\mapsto T] & \text{if } S \text{ is a variable } X \text{ and } X\notin\mathrm{FV}(T)\\
\mathrm{unify}([X\mapsto S]C')\circ[X\mapsto S] & \text{if } T \text{ is a variable } X \text{ and } X\notin\mathrm{FV}(S)\\
\mathrm{unify}(C'\cup\{S_1=T_1,S_2=T_2\}) & \text{if } S=S_1\to S_2 \text{ and } T=T_1\to T_2\\
\mathrm{unify}(C'\cup\{S_1=T_1,S_2=T_2\}) & \text{if } S=S_1\times S_2 \text{ and } T=T_1\times T_2\\
\text{fail} & \text{otherwise}
\end{cases}
\end{aligned}`

The test $`X\notin\mathrm{FV}(T)` is the *occurs check*. The product case is this book’s addition to TAPL’s algorithm. Session 28 proves, for the types built from type variables, Bool, Nat and $`\to`, that $`\mathrm{unify}(C)` fails exactly when $`C` has no unifier, and otherwise returns a principal unifier of $`C`. Its Exercise 28.4 adds the product case. For example, on $`\{X\to X=\mathsf{Nat}\to Y\}` the arrow case gives $`\{X=\mathsf{Nat},X=Y\}`. Taking $`X=\mathsf{Nat}` first, the result is $`[Y\mapsto\mathsf{Nat}]\circ[X\mapsto\mathsf{Nat}]`, while $`\{X=X\to Y\}` fails the occurs check.

*let · Session 29.* The term $`\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2` binds $`x` in $`t_2` but not in $`t_1`, so $`\mathrm{FV}(\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2)=\mathrm{FV}(t_1)\cup(\mathrm{FV}(t_2)\setminus\{x\})`. It belongs to both the typed language and the inference form. No let term is a value.

$$`\frac{}{\mathsf{let}\ x=v_1\ \mathsf{in}\ t_2\to[x\mapsto v_1]t_2}\;\textsf{E-LetV}\qquad\frac{t_1\to t_1'}{\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2\to\mathsf{let}\ x=t_1'\ \mathsf{in}\ t_2}\;\textsf{E-Let}`

In the typed language, let is typed by

$$`\frac{\Gamma\vdash t_1:T_1\quad\Gamma,x{:}T_1\vdash t_2:T_2}{\Gamma\vdash\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2:T_2}\;\textsf{T-Let}`

In the inference form, let is typed with type schemes.

*Type schemes · Session 29.* A *type scheme* has the form $`\forall X_1\ldots X_n.T` with $`n\ge 0`, where $`T` is a type of this section. For $`n=0` it is the type $`T`. Schemes occur only in contexts. In the inference form a context binds each variable to a scheme, $`\Gamma ::= \varnothing\mid\Gamma,x{:}\forall X_1\ldots X_n.T`, and a variable bound by an abstraction receives a scheme with $`n=0`. A scheme is never the type of a term and never occurs inside a type. Its quantifier is not the type $`\forall X.T` of C.7. $`\mathrm{FV}(\forall X_1\ldots X_n.T)=\mathrm{FV}(T)\setminus\{X_1,\ldots,X_n\}`, and $`\mathrm{FV}(\Gamma)` is the union of $`\mathrm{FV}` over the schemes in $`\Gamma`. An *instance* of $`\forall X_1\ldots X_n.T` is a type $`[X_1\mapsto T_1,\ldots,X_n\mapsto T_n]T`. Schemes that differ only in the names of their quantified variables are identified. A type substitution $`\sigma` acts on a scheme by first renaming its quantified variables to fresh variables that are not in $`\mathrm{dom}(\sigma)` and occur in no type $`\sigma X` with $`X\in\mathrm{dom}(\sigma)`, and then acting on its body (Session 29, §29.3).

*Generalization.* With schemes in the context, T-Var and T-Let are replaced by the following two rules. For $`n=0` they are T-Var and T-Let.

$$`\frac{x{:}\forall X_1\ldots X_n.T\in\Gamma}{\Gamma\vdash x:[X_1\mapsto T_1,\ldots,X_n\mapsto T_n]T}\;\textsf{T-VarInst}`

$$`\frac{\Gamma\vdash t_1:T_1\quad\Gamma,x{:}\forall X_1\ldots X_n.T_1\vdash t_2:T_2\quad\{X_1,\ldots,X_n\}\cap\mathrm{FV}(\Gamma)=\varnothing}{\Gamma\vdash\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2:T_2}\;\textsf{T-LetGen}`

The last premise of T-LetGen is the *generalization condition*: a type variable may be quantified only if it is not free in $`\Gamma`. The constraint rules follow the procedure of TAPL §22.7. CT-VarInst replaces CT-Var, and CT-LetGen types let.

$$`\frac{x{:}\forall X_1\ldots X_n.T\in\Gamma\quad Y_1,\ldots,Y_n\ \text{fresh}}{\Gamma\vdash x:[X_1\mapsto Y_1,\ldots,X_n\mapsto Y_n]T\mid_{\{Y_1,\ldots,Y_n\}}\varnothing}\;\textsf{CT-VarInst}`

$$`\frac{\begin{gathered}\Gamma\vdash t_1:S_1\mid_{\mathcal X_1}C_1\qquad\sigma=\mathrm{unify}(C_1)\qquad\{Y_1,\ldots,Y_n\}=\mathrm{FV}(\sigma S_1)\setminus\mathrm{FV}(\sigma\Gamma)\\\sigma\Gamma,x{:}\forall Y_1\ldots Y_n.\sigma S_1\vdash t_2:S_2\mid_{\mathcal X_2}C_2\end{gathered}}{\Gamma\vdash\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2:S_2\mid_{\mathcal X_1\cup\mathcal X_2}C_1\cup C_2}\;\textsf{CT-LetGen}`

CT-LetGen solves the constraints of $`t_1` first and applies the solution to $`\Gamma` before computing the quantified variables. If $`\mathrm{unify}(C_1)` fails, the let term has no constraint typing. The conclusion keeps $`C_1`, so that the equations on the variables of $`\Gamma` remain in force. For example, in $`\mathsf{let}\ \mathit{id}=\lambda x.x\ \mathsf{in}\ \mathsf{if}\ \mathit{id}\ \mathsf{true}\ \mathsf{then}\ \mathit{id}\ 0\ \mathsf{else}\ 0`, the right-hand side gives $`X\to X` with no constraints, so $`\mathit{id}{:}\forall X.X\to X`. The two occurrences of $`\mathit{id}` receive the fresh instances $`Y_1\to Y_1` and $`Y_2\to Y_2`, which unify with $`\mathsf{Bool}\to Z_1` and $`\mathsf{Nat}\to Z_2`. The whole term has type Nat.

# C.6 References · Session 30
%%%
tag := "lambda-c6"
number := false
%%%

$$`T ::= \cdots\mid\mathsf{Ref}\ T`

$$`t ::= \cdots\mid\mathsf{ref}\ t\mid{!}t\mid t\mathrel{:=}t\mid l\qquad\qquad v ::= \cdots\mid l`

The term $`\mathsf{ref}\ t` allocates a new cell, $`{!}t` reads a cell and $`t_1\mathrel{:=}t_2` writes one. *Locations* $`l` are drawn from an infinite set. A *program* is a term without locations; locations arise only during evaluation.

*Stores.* The *store* is the memory of a running term. This store is not the state of Part 1. An IMP state is a total function $`\mathrm{Name}\to\mathbb Z`: every variable name has an integer from the start. A store $`\mu` is a partial map $`\mathrm{Location}\rightharpoonup\mathrm{Value}` with a finite domain. Write $`\varnothing` for the empty store, $`\mathrm{dom}(\mu)` for its domain and $`\mu(l)` for the value at $`l\in\mathrm{dom}(\mu)`. For $`l\notin\mathrm{dom}(\mu)`, the extension $`(\mu,l\mapsto v)` also maps $`l` to $`v`. For $`l\in\mathrm{dom}(\mu)`, the update $`[l\mapsto v]\mu` maps $`l` to $`v` and agrees with $`\mu` elsewhere.

*Evaluation.* One step is now $`t\mid\mu\to t'\mid\mu'`. Each computation rule of the earlier sections keeps the store: $`t\to t'` becomes $`t\mid\mu\to t'\mid\mu`. Each congruence rule carries the store change of its premise to its conclusion. For example, E-App1 becomes

$$`\frac{t_1\mid\mu\to t_1'\mid\mu'}{t_1\,t_2\mid\mu\to t_1'\,t_2\mid\mu'}\;\textsf{E-App1}`

The new rules are:

$$`\frac{l\notin\mathrm{dom}(\mu)}{\mathsf{ref}\ v_1\mid\mu\to l\mid(\mu,l\mapsto v_1)}\;\textsf{E-RefV}\qquad\frac{t_1\mid\mu\to t_1'\mid\mu'}{\mathsf{ref}\ t_1\mid\mu\to\mathsf{ref}\ t_1'\mid\mu'}\;\textsf{E-Ref}`

$$`\frac{\mu(l)=v}{{!}l\mid\mu\to v\mid\mu}\;\textsf{E-DerefLoc}\qquad\frac{t_1\mid\mu\to t_1'\mid\mu'}{{!}t_1\mid\mu\to{!}t_1'\mid\mu'}\;\textsf{E-Deref}\qquad\frac{}{l\mathrel{:=}v_2\mid\mu\to\mathsf{unit}\mid[l\mapsto v_2]\mu}\;\textsf{E-Assign}`

$$`\frac{t_1\mid\mu\to t_1'\mid\mu'}{t_1\mathrel{:=}t_2\mid\mu\to t_1'\mathrel{:=}t_2\mid\mu'}\;\textsf{E-Assign1}\qquad\frac{t_2\mid\mu\to t_2'\mid\mu'}{v_1\mathrel{:=}t_2\mid\mu\to v_1\mathrel{:=}t_2'\mid\mu'}\;\textsf{E-Assign2}`

E-Assign applies only when $`l\in\mathrm{dom}(\mu)`, since the update is defined only there. A program $`t` starts in the empty store, as $`t\mid\varnothing`. The closure $`t\mid\mu\to^*t'\mid\mu'` is zero or more steps.

*Store typings.* A *store typing* $`\Sigma` is a finite map from locations to types. $`\Sigma(l)` is the type of the values stored at $`l`; the location itself has type $`\mathsf{Ref}\ \Sigma(l)`. Here $`\Sigma` is not the set of IMP states of [A.2](imp-card/index.html#imp-a2). $`\varnothing` is the empty store typing, and $`(\Sigma,l{:}T)` extends $`\Sigma` at $`l\notin\mathrm{dom}(\Sigma)`. Write $`\Sigma\subseteq\Sigma'`, and say that $`\Sigma'` *extends* $`\Sigma`, if $`\mathrm{dom}(\Sigma)\subseteq\mathrm{dom}(\Sigma')` and $`\Sigma'(l)=\Sigma(l)` for every $`l\in\mathrm{dom}(\Sigma)`.

*Typing.* The judgment is now written in full as $`\Gamma\mid\Sigma\vdash t:T`. Each earlier typing rule is read with the same $`\Sigma` in every premise and in the conclusion. The new rules are:

$$`\frac{\Sigma(l)=T_1}{\Gamma\mid\Sigma\vdash l:\mathsf{Ref}\ T_1}\;\textsf{T-Loc}\qquad\frac{\Gamma\mid\Sigma\vdash t_1:T_1}{\Gamma\mid\Sigma\vdash\mathsf{ref}\ t_1:\mathsf{Ref}\ T_1}\;\textsf{T-Ref}\qquad\frac{\Gamma\mid\Sigma\vdash t_1:\mathsf{Ref}\ T_{11}}{\Gamma\mid\Sigma\vdash{!}t_1:T_{11}}\;\textsf{T-Deref}`

$$`\frac{\Gamma\mid\Sigma\vdash t_1:\mathsf{Ref}\ T_{11}\quad\Gamma\mid\Sigma\vdash t_2:T_{11}}{\Gamma\mid\Sigma\vdash t_1\mathrel{:=}t_2:\mathsf{Unit}}\;\textsf{T-Assign}`

*Well-typed stores.* A store $`\mu` is *well typed* under $`\Gamma` and $`\Sigma`, written $`\Gamma\mid\Sigma\vdash\mu`, if $`\mathrm{dom}(\mu)=\mathrm{dom}(\Sigma)` and $`\Gamma\mid\Sigma\vdash\mu(l):\Sigma(l)` for every $`l\in\mathrm{dom}(\mu)`. Stored values are typed under the whole of $`\Sigma`, so a stored value may mention its own location.

In $`t_1;t_2`, the semicolon binds less tightly than $`\mathrel{:=}`. For example, with sequencing from C.3,

$$`\mathsf{let}\ r=\mathsf{ref}\ 0\ \mathsf{in}\ (r\mathrel{:=}\mathsf{succ}\ ({!}r);\ {!}r)\mid\varnothing\ \to^*\ \mathsf{succ}\ 0\mid(\varnothing,l\mapsto\mathsf{succ}\ 0).`

The program has type Nat under the empty store typing. After the first step, which allocates $`l`, the term is typed under $`(\varnothing,l{:}\mathsf{Nat})`.

*References in the inference form.* T-Ref, T-Deref and T-Assign apply to unannotated terms unchanged. Programs contain no locations, so inference uses the empty store typing.

*Constraint rules for references.* TAPL gives no constraint rules for references. This book uses the following, and $`\mathrm{unify}` gains a case for Ref.

$$`\frac{\Gamma\vdash t_1:T_1\mid_{\mathcal X}C}{\Gamma\vdash\mathsf{ref}\ t_1:\mathsf{Ref}\ T_1\mid_{\mathcal X}C}\;\textsf{CT-Ref}\qquad\frac{\Gamma\vdash t_1:T_1\mid_{\mathcal X}C\quad X\ \text{fresh}}{\Gamma\vdash{!}t_1:X\mid_{\mathcal X\cup\{X\}}C\cup\{T_1=\mathsf{Ref}\ X\}}\;\textsf{CT-Deref}`

$$`\frac{\Gamma\vdash t_1:T_1\mid_{\mathcal X_1}C_1\quad\Gamma\vdash t_2:T_2\mid_{\mathcal X_2}C_2}{\Gamma\vdash t_1\mathrel{:=}t_2:\mathsf{Unit}\mid_{\mathcal X_1\cup\mathcal X_2}C_1\cup C_2\cup\{T_1=\mathsf{Ref}\ T_2\}}\;\textsf{CT-Assign}`

$$`\mathrm{unify}(\{\mathsf{Ref}\ S_1=\mathsf{Ref}\ T_1\}\cup C')=\mathrm{unify}(C'\cup\{S_1=T_1\}).`

*Value restriction.* With references, T-LetGen and CT-LetGen may quantify type variables ($`n>0`) only when $`t_1` is a value. Otherwise $`x` receives the scheme with $`n=0`. Without this restriction the program

$$`\mathsf{let}\ r=\mathsf{ref}\ (\lambda x.x)\ \mathsf{in}\ (r\mathrel{:=}(\lambda x.\mathsf{succ}\ x);\ ({!}r)\ \mathsf{true})`

would be typed with $`r{:}\forall X.\mathsf{Ref}\ (X\to X)`, instantiated at Nat for the write and at Bool for the read. It evaluates to $`\mathsf{succ}\ \mathsf{true}`, which is stuck.

# C.7 Type abstraction · Session 31
%%%
tag := "lambda-c7"
number := false
%%%

$$`T ::= \cdots\mid X\mid\forall X.T\mid\{\exists X,T\}`

$$`t ::= \cdots\mid\lambda X.t\mid t\ [T]\mid\{{*}T,t\}\ \mathsf{as}\ T\mid\mathsf{let}\ \{X,x\}=t\ \mathsf{in}\ t\qquad\qquad v ::= \cdots\mid\lambda X.t\mid\{{*}T,v\}\ \mathsf{as}\ T`

$`\forall X.T` is a *universal type* and $`\{\exists X,T\}` an *existential type*. Each binds $`X` in $`T`. A *type abstraction* $`\lambda X.t` binds $`X` in $`t`, and a *type application* $`t\ [T]` supplies a type argument. A *package* $`\{{*}T_1,t_2\}\ \mathsf{as}\ T` hides the *representation type* $`T_1`. *Unpacking* $`\mathsf{let}\ \{X,x\}=t_1\ \mathsf{in}\ t_2` binds $`X` and $`x` in $`t_2`. Type application associates to the left together with application: $`t\ [T]\ s` is $`(t\ [T])\ s`.

*Type variables and substitution.* Here type variables are bound by $`\forall`, $`\exists`, type abstraction and unpacking. They are not the unknowns of C.5. $`\mathrm{FV}(T)` is the set of free type variables of $`T`: $`\mathrm{FV}(X)=\{X\}`, $`\mathrm{FV}(\forall X.T)=\mathrm{FV}(\{\exists X,T\})=\mathrm{FV}(T)\setminus\{X\}`, and the other type constructors take unions. Types that differ only in the names of bound type variables are identified. $`[X\mapsto S]T` replaces the free occurrences of $`X` in $`T` by $`S`, first renaming each bound type variable of $`T` that occurs free in $`S`. For example, $`[X\mapsto Y](\forall Y.X\to Y)=\forall Z.Y\to Z`. On a term, $`[X\mapsto S]t` applies this substitution to every type written in $`t`: parameter types, type arguments, package types and injection annotations. Term substitution $`[x\mapsto s]t` renames a bound type variable of $`t` when it occurs free in a type written in $`s`.

*Contexts.*

$$`\Gamma ::= \cdots\mid\Gamma,X`

$`\mathrm{dom}(\Gamma)` now contains the type variables bound in $`\Gamma`. The extension $`\Gamma,X` is formed only when $`X\notin\mathrm{dom}(\Gamma)`, renaming the bound type variable if necessary.

*Well-formed types and contexts.* A type is *well formed* in $`\Gamma` if each of its free type variables is bound in $`\Gamma`. A context is well formed if, in each binding $`x{:}T`, the type $`T` is well formed in the part of the context to its left. The typing rules are used only with well-formed contexts. Every type written in a term must be well formed in the context of the rule that inspects it, and the types in a store typing are closed. TAPL leaves these conditions implicit. Without them T-TAbs could bind a type variable that is already free in $`\Gamma`.

*Evaluation.*

$$`\frac{t_1\to t_1'}{t_1\ [T_2]\to t_1'\ [T_2]}\;\textsf{E-TApp}\qquad\frac{}{(\lambda X.t_{12})\ [T_2]\to[X\mapsto T_2]t_{12}}\;\textsf{E-TappTabs}`

$$`\frac{t_{12}\to t_{12}'}{\{{*}T_{11},t_{12}\}\ \mathsf{as}\ T_1\to\{{*}T_{11},t_{12}'\}\ \mathsf{as}\ T_1}\;\textsf{E-Pack}\qquad\frac{t_1\to t_1'}{\mathsf{let}\ \{X,x\}=t_1\ \mathsf{in}\ t_2\to\mathsf{let}\ \{X,x\}=t_1'\ \mathsf{in}\ t_2}\;\textsf{E-Unpack}`

$$`\frac{}{\mathsf{let}\ \{X,x\}=(\{{*}T_{11},v_{12}\}\ \mathsf{as}\ T_1)\ \mathsf{in}\ t_2\to[X\mapsto T_{11}][x\mapsto v_{12}]t_2}\;\textsf{E-UnpackPack}`

*Typing.*

$$`\frac{\Gamma,X\vdash t_2:T_2}{\Gamma\vdash\lambda X.t_2:\forall X.T_2}\;\textsf{T-TAbs}\qquad\frac{\Gamma\vdash t_1:\forall X.T_{12}}{\Gamma\vdash t_1\ [T_2]:[X\mapsto T_2]T_{12}}\;\textsf{T-TApp}`

$$`\frac{\Gamma\vdash t_2:[X\mapsto U]T_2}{\Gamma\vdash\{{*}U,t_2\}\ \mathsf{as}\ \{\exists X,T_2\}:\{\exists X,T_2\}}\;\textsf{T-Pack}`

$$`\frac{\Gamma\vdash t_1:\{\exists X,T_{12}\}\quad\Gamma,X,x{:}T_{12}\vdash t_2:T_2\quad X\notin\mathrm{FV}(T_2)}{\Gamma\vdash\mathsf{let}\ \{X,x\}=t_1\ \mathsf{in}\ t_2:T_2}\;\textsf{T-Unpack}`

The side condition $`X\notin\mathrm{FV}(T_2)` of T-Unpack keeps the abstract type $`X` inside its scope: the type of the body may not mention it. TAPL obtains this restriction from the scope of $`X` in the context. This card writes it as a premise. For example, let

$$`\mathit{counter}=\{{*}\mathsf{Nat},\{0,\{\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x,\ \lambda x{:}\mathsf{Nat}.x\}\}\}\ \mathsf{as}\ \{\exists X,X\times((X\to X)\times(X\to\mathsf{Nat}))\}.`

T-Pack types it, since its second component has type $`[X\mapsto\mathsf{Nat}](X\times((X\to X)\times(X\to\mathsf{Nat})))`. The client $`\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ c.2.2\ (c.2.1\ c.1)` has type Nat and evaluates to $`\mathsf{succ}\ 0`. The client $`\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ c.1` has no type, because its body has type $`X`.

# C.8 The safety table · Sessions 24–32
%%%
tag := "lambda-c8"
number := false
%%%

*Values are normal forms.* In C.2–C.7 a value cannot take a step, in any store when the semantics uses stores. To prove this, induct on the structure of the value: no computation rule has a value on the left of its conclusion. The only congruence rules that could step from a value are E-Succ, E-Pair1, E-Pair2, E-Inl, E-Inr and E-Pack; each requires a step of an immediate component that is itself a value, which the induction hypothesis excludes.

*General statements.* The statements quantify over the typed language of the session. Before Session 30 they read as follows.

* *Progress.* For every term $`t` and type $`T`: if $`\vdash t:T`, then $`t` is a value or there is a term $`t'` with $`t\to t'`.
* *Preservation.* For every context $`\Gamma`, terms $`t,t'` and type $`T`: if $`\Gamma\vdash t:T` and $`t\to t'`, then $`\Gamma\vdash t':T`.

The premise $`\vdash t:T` of progress types $`t` in the empty context. Every free variable of a typed term lies in $`\mathrm{dom}(\Gamma)`, so $`t` is closed. The premise cannot be dropped: $`x{:}\mathsf{Nat}\to\mathsf{Nat}\vdash x\ 0:\mathsf{Nat}`, and $`x\ 0` is neither a value nor able to step. From Session 30 the statements read as follows.

* *Progress.* For every term $`t`, type $`T` and store typing $`\Sigma`: if $`\varnothing\mid\Sigma\vdash t:T`, then $`t` is a value or, for every store $`\mu` with $`\varnothing\mid\Sigma\vdash\mu`, there are $`t'` and $`\mu'` with $`t\mid\mu\to t'\mid\mu'`.
* *Preservation.* In the typed language of Session 30, let $`\Gamma` be any context. In the language extended with type abstraction (Session 31), take $`\Gamma=\varnothing` for every row of the table. For all $`\Sigma,\mu,t,t',\mu',T`, if $`\Gamma\mid\Sigma\vdash t:T`, $`\Gamma\mid\Sigma\vdash\mu` and $`t\mid\mu\to t'\mid\mu'`, then there is a store typing $`\Sigma'` with $`\Sigma\subseteq\Sigma'`, $`\Gamma\mid\Sigma'\vdash t':T` and $`\Gamma\mid\Sigma'\vdash\mu'`. The [allocation example in §31.3](chapter-31/index.html#ch31-s3) explains the restriction.

The store typing may grow, because allocation adds a location. For the typed languages of Sessions 24–29, take $`\Sigma=\varnothing` in the Session 30 statements and omit the stores.

*Safety.* If $`\varnothing\mid\Sigma\vdash t:T`, $`\varnothing\mid\Sigma\vdash\mu` and $`t\mid\mu\to^*t'\mid\mu'`, then $`t'` is a value or $`t'\mid\mu'` takes a step. Before Session 30: if $`\vdash t:T` and $`t\to^*t'`, then $`t'` is a value or $`t'` takes a step. Safety follows from progress and from preservation with $`\Gamma=\varnothing`, by induction on the number of steps. Thus the evaluation of a well-typed program never gets stuck.

*Form of the table.* The table has one row per construct group. A row names the session that adds it and has three entries.

* *Canonical forms.* For each type constructor of the row: if $`v` is a value and $`\varnothing\mid\Sigma\vdash v:T` for a type $`T` with that constructor, then $`v` has the stated shape.
* *Progress.* For each typing rule of the row: the progress statement for derivations of $`\varnothing\mid\Sigma\vdash t:T` that end with that rule, assuming it for those immediate subderivations whose context is empty. The entry names the evaluation rules that supply the step.
* *Preservation.* For each evaluation rule of the row: the preservation statement for steps by that rule, assuming it for the evaluation premise. The entry gives $`\Sigma'` and names each lemma used besides inversion and the induction hypothesis.

Before Session 30, read $`\Sigma` and $`\Sigma'` as $`\varnothing` and omit the stores. Sessions 24–29 then write an entry $`\Sigma'=\Sigma` as “no lemma” when it names no lemma, and as “uses” the named lemma otherwise: the case needs only inversion, a typing rule and that lemma. In a preservation entry, “premise” means that $`\Sigma'` is the store typing that the induction hypothesis gives for the evaluation premise. From Session 30, the other immediate subterms are then retyped under $`\Sigma'` by store weakening (Row 5). When a row is added, each earlier canonical-forms statement gains cases: its proof must exclude the new forms of value. Likewise the substitution lemma and the lemmas it uses (Session 25, Lemmas 25.1–25.4) gain one case for each new typing rule. Session 27, Lemma 27.4 adds the cases for C.4.

*Row 1 · Booleans and natural numbers · Session 24.*

* *Canonical forms.* If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\mathsf{Bool}`, then $`v=\mathsf{true}` or $`v=\mathsf{false}`. If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\mathsf{Nat}`, then $`v` is a numeric value $`nv`.
* *Progress.* T-True, T-False, T-Zero: the term is a value. T-Succ: $`\mathsf{succ}\ t_1` is a value or steps by E-Succ. T-If: steps by E-If, E-IfTrue or E-IfFalse. T-Pred: steps by E-Pred, E-PredZero or E-PredSucc. T-IsZero: steps by E-IsZero, E-IszeroZero or E-IszeroSucc.
* *Preservation.* E-IfTrue, E-IfFalse, E-PredZero, E-PredSucc, E-IszeroZero, E-IszeroSucc: $`\Sigma'=\Sigma`. E-If, E-Succ, E-Pred, E-IsZero: premise.

*Row 2 · Functions and Unit · Session 26.*

* *Canonical forms.* If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:T_1\to T_2`, then $`v=\lambda x{:}T_1.t_2` for some $`x` and $`t_2`. If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\mathsf{Unit}`, then $`v=\mathsf{unit}`.
* *Progress.* T-Var: no derivation of $`\varnothing\mid\Sigma\vdash x:T` exists. T-Abs, T-Unit: the term is a value. T-App: steps by E-App1, E-App2 or E-AppAbs.
* *Preservation.* E-AppAbs: $`\Sigma'=\Sigma`. It uses the *substitution lemma* of Session 25: if $`\Gamma,x{:}S\mid\Sigma\vdash t:T` and $`\Gamma\mid\Sigma\vdash s:S`, then $`\Gamma\mid\Sigma\vdash[x\mapsto s]t:T`. E-App1, E-App2: premise.

*Row 3 · Products and sums · Session 27.*

* *Canonical forms.* If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:T_1\times T_2`, then $`v=\{v_1,v_2\}` for values $`v_1,v_2`. If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:T_1+T_2`, then $`v=\mathsf{inl}\ v_1\ \mathsf{as}\ T_1+T_2` for a value $`v_1`, or $`v=\mathsf{inr}\ v_2\ \mathsf{as}\ T_1+T_2` for a value $`v_2`.
* *Progress.* T-Pair: $`\{t_1,t_2\}` is a value or steps by E-Pair1 or E-Pair2. T-Proj1: steps by E-Proj1 or E-PairBeta1. T-Proj2: steps by E-Proj2 or E-PairBeta2. T-Inl, T-Inr: the term is a value or steps by E-Inl, respectively E-Inr. T-Case: steps by E-Case, E-CaseInl or E-CaseInr.
* *Preservation.* E-PairBeta1, E-PairBeta2: $`\Sigma'=\Sigma`. E-CaseInl, E-CaseInr: $`\Sigma'=\Sigma`, using the substitution lemma. E-Pair1, E-Pair2, E-Proj1, E-Proj2, E-Inl, E-Inr, E-Case: premise.

*Row 4 · let · Session 29.* The row concerns let in the typed language, typed by T-Let.

* *Canonical forms.* None: no value is a let term.
* *Progress.* T-Let: steps by E-Let or E-LetV.
* *Preservation.* E-LetV: $`\Sigma'=\Sigma`, using the substitution lemma. E-Let: premise.

*Row 5 · References · Session 30.*

* *Canonical forms.* If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\mathsf{Ref}\ T_1`, then $`v` is a location $`l` with $`\Sigma(l)=T_1`.
* *Progress.* T-Loc: the term is a value. T-Ref: steps by E-Ref or E-RefV; a location $`l\notin\mathrm{dom}(\mu)` exists because $`\mathrm{dom}(\mu)` is finite. T-Deref: steps by E-Deref or E-DerefLoc; $`\mu(l)` is defined because $`l\in\mathrm{dom}(\Sigma)=\mathrm{dom}(\mu)`. T-Assign: steps by E-Assign1, E-Assign2 or E-Assign; E-Assign applies because $`l\in\mathrm{dom}(\Sigma)=\mathrm{dom}(\mu)`, as for T-Deref.
* *Preservation.* E-RefV: $`\Sigma'=(\Sigma,l{:}T_1)`, where $`T_1` is the type of the stored value. It uses *store weakening*: if $`\Gamma\mid\Sigma\vdash t:T` and $`\Sigma\subseteq\Sigma'`, then $`\Gamma\mid\Sigma'\vdash t:T`. E-DerefLoc: $`\Sigma'=\Sigma`, using $`\Gamma\mid\Sigma\vdash\mu`. E-Assign: $`\Sigma'=\Sigma`. It uses *store update*: if $`\Gamma\mid\Sigma\vdash\mu`, $`\Sigma(l)=T` and $`\Gamma\mid\Sigma\vdash v:T`, then $`\Gamma\mid\Sigma\vdash[l\mapsto v]\mu`. E-Ref, E-Deref, E-Assign1, E-Assign2: premise.

Session 30 also restates Rows 1–4 in the store form. Their computation rules take $`\Sigma'=\Sigma` and keep the store, and their congruence rules use store weakening for the other immediate subterms.

*Row 6 · Universal and existential types · Session 31.* Session 31 states this row without proof.

* *Canonical forms.* If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\forall X.T_{12}`, then $`v=\lambda X.t_{12}` for some $`t_{12}`. If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\{\exists X,T_{12}\}`, then $`v=\{{*}T_{11},v_{12}\}\ \mathsf{as}\ \{\exists X,T_{12}\}` for a type $`T_{11}` and a value $`v_{12}`.
* *Progress.* T-TAbs: the term is a value. T-TApp: steps by E-TApp or E-TappTabs. T-Pack: the term is a value or steps by E-Pack. T-Unpack: steps by E-Unpack or E-UnpackPack.
* *Preservation.* E-TappTabs: $`\Sigma'=\Sigma`. It uses the *type substitution lemma*: if $`\Gamma,X,\Delta\mid\Sigma\vdash t:T` and $`S` is well formed in $`\Gamma`, then $`\Gamma,[X\mapsto S]\Delta\mid\Sigma\vdash[X\mapsto S]t:[X\mapsto S]T`. Here $`\Delta` is a sequence of bindings and $`[X\mapsto S]\Delta` substitutes in its types. E-UnpackPack: $`\Sigma'=\Sigma`, using the substitution lemma, the type substitution lemma and the side condition $`X\notin\mathrm{FV}(T_2)` of T-Unpack, which gives $`[X\mapsto T_{11}]T_2=T_2`. E-TApp, E-Pack, E-Unpack: premise.

# Source sections
%%%
tag := "lambda-sources"
number := false
%%%

Section numbers refer to Benjamin C. Pierce, _Types and Programming Languages_, MIT Press, 2002. The presentations of typing unannotated terms, the constraint rules for Unit and pairs, and the generalization rules in [C.5](lambda-card/index.html#lambda-c5) are formulated in this book, as are the constraint rules for references in [C.6](lambda-card/index.html#lambda-c6). The names N-App1, N-AppAbs, T-VarInst, T-LetGen, CT-VarInst and CT-LetGen are also local to this book. Other rule names follow TAPL. [Table of contents.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

* C.1: §5.3 (syntax, free variables, substitution and the call-by-value rules); §5.1 (evaluation strategies, including call by name); §5.2 (the term $`\Omega`); §3.5 (computation and congruence rules, normal forms, multi-step evaluation).
* C.2: §§3.2 and 3.5 (terms, values and evaluation, stuck terms); §§8.1–8.2 (types and typing rules).
* C.3: §§9.1–9.2 (function types, typing contexts and the typing rules); §11.2 (Unit); §11.3 (sequencing as a derived form).
* C.4: §11.6 (pairs); §11.9 (sums with type annotations); §9.4 (the Curry–Howard correspondence, read in Session 27).
* C.5: §22.1 (type variables and type substitutions); §22.3 (constraint typing); §22.4 (unification); §22.5 (principal types); §22.6 (unannotated abstractions); §11.5 (let); §22.7 (let-polymorphism and generalization).
* C.6: §§13.1–13.3 (references, locations, stores and evaluation); §13.4 (store typings and well-typed stores); §13.5 (safety); §22.7 (the value restriction).
* C.7: §23.3 (System F); §23.5 (its basic properties); §24.1 (existential types); §24.2 (data abstraction with existentials).
* C.8: §8.3 (Row 1); §9.3 (Row 2 and the substitution lemma); §13.5 (Row 5); §23.5 and §24.1 (Row 6). TAPL presents the rules of Rows 3 and 4 in §§11.5, 11.6 and 11.9.
