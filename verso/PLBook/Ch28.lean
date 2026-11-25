import VersoManual

open Verso.Genre Manual

#doc (Manual) "Typechecking and Inference" =>
%%%
tag := "ch28"
file := "chapter-28"
%%%

* *Definitions.* Typing rules and typing contexts of [C.2](lambda-card/index.html#lambda-c2) and [C.3](lambda-card/index.html#lambda-c3). From [C.5](lambda-card/index.html#lambda-c5): unannotated terms, types with type variables, the unannotated rule T-Abs, type substitutions, their composition and the order $`\sqsubseteq`, constraint sets, unifiers and principal unifiers, constraint typing, solutions and principal types, the function $`\mathrm{unify}` and the occurs check. Structural induction and induction on derivations ([Session 1, §1.5](chapter-01/index.html#ch01-s5)).
* *New terms.* Type substitution, constraint set, principal unifier, occurs check, principal type. [Glossary and label key](glossary/index.html)
* *Theorem 28.4 (Unification).* For every constraint set $`C`: (a) the computation of $`\mathrm{unify}(C)` terminates; (b) if it returns $`\sigma`, then $`\sigma` unifies $`C`; (c) if $`\sigma'` unifies $`C`, then it returns some $`\sigma` with $`\sigma\sqsubseteq\sigma'`. Hence $`\mathrm{unify}(C)` fails exactly when $`C` has no unifier, and otherwise returns a principal unifier of $`C`.
* *Source.* Pierce, _Types and Programming Languages_ (TAPL): constraint typing in §22.3, unification and its correctness in §22.4, principal types in §22.5, and CT-AbsInf for unannotated abstractions in §22.6. TAPL proves Theorem 28.4 for the same algorithm on the same types, built from type variables, Bool, Nat and $`\to`. TAPL proves the counterparts of Proposition 28.5 and Corollary 28.6 for annotated abstractions. Proposition 28.2 and Lemma 28.3 are this book’s. [Source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)
* *Board case.* Two parts. First, generate the constraints of $`u=\lambda f.\lambda x.f\,(f\,x)` and run $`\mathrm{unify}` on them (§28.2, steps 1–8). Second, the variable case of Theorem 28.4(c) (§28.3, steps 1–7): from $`\sigma'X=\sigma'T`, show that $`\sigma'` unifies $`[X\mapsto T]C'`, apply the induction hypothesis, and compare $`\gamma\circ\sigma_1\circ[X\mapsto T]` with $`\sigma'` on each type variable.
* *Proof outline.* (a) Each recursive call lowers the number of type variables, or keeps it and lowers the total size of the types. (b) and (c) by induction on the number of calls $`k(C)`. For (c) the induction property is $`Q(C)\coloneqq\forall\sigma',\ (\sigma'\text{ unifies }C)\Rightarrow\mathrm{unify}(C)\text{ returns some }\sigma\text{ with }\sigma\sqsubseteq\sigma'`. The variable case uses Lemma 28.3. Failure cannot occur, because a substitution keeps outermost constructors and cannot make a type identical to a larger type containing it.
* *From Session 27.* Sessions 24–27 typed terms whose abstractions carry their parameter type, and proved that evaluation preserves types. This session asks how a type is found. With annotations, a function computes it (§28.1). Without them, types contain type variables, which stand for types not yet determined. Unit and sums are left out, and products appear only in Exercise 28.4.

The annotation in $`\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x` tells a checker the type of $`x` before it looks at the body. Erase it. In $`(\lambda x.\mathsf{succ}\ x)\,0` the type of $`x` is still forced, because $`\mathsf{succ}` requires a number. In $`\lambda f.\lambda x.f\,(f\,x)` nothing requires Bool or Nat. The two uses of $`f` force only that the result type of $`f` be its parameter type. This session writes such requirements as equations between types and solves them by unification. The main theorem says that unification fails only when the equations have no unifier, and otherwise returns a unifier from which every other unifier is obtained.

# Checking annotated terms
%%%
tag := "ch28-s1"
%%%

In this section terms are those of [C.2](lambda-card/index.html#lambda-c2) and [C.3](lambda-card/index.html#lambda-c3) without $`\mathsf{unit}`, so every abstraction carries its parameter type. Types are built from Bool, Nat and $`\to`. For each form of term exactly one typing rule has a conclusion of that form.

Take $`(\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x)\,0` in the empty context. T-Abs reads the parameter type Nat from the annotation, and T-Var and T-Succ type the body at Nat, so the operator has type $`\mathsf{Nat}\to\mathsf{Nat}`. T-Zero gives the operand type Nat. T-App requires the operand type to be the domain of the operator type. Both are Nat, so the term has type Nat. Each step looked up the context, read the annotation, or compared two types already computed.

*Definition 28.1 (The checker).* The function $`\mathrm{check}` takes a context $`\Gamma` and an annotated term $`t`, and returns a type or fails:

$$`\begin{aligned}
\mathrm{check}(\Gamma,x)&=T&&\text{if }x{:}T\in\Gamma\\
\mathrm{check}(\Gamma,\lambda x{:}T_1.t_2)&=T_1\to T_2&&\text{if }\mathrm{check}((\Gamma,x{:}T_1),t_2)=T_2\\
\mathrm{check}(\Gamma,t_1\,t_2)&=T_{12}&&\text{if }\mathrm{check}(\Gamma,t_1)=T_{11}\to T_{12}\text{ and }\mathrm{check}(\Gamma,t_2)=T_{11}\\
\mathrm{check}(\Gamma,\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3)&=T&&\text{if }\mathrm{check}(\Gamma,t_1)=\mathsf{Bool},\ \mathrm{check}(\Gamma,t_2)=T\text{ and }\mathrm{check}(\Gamma,t_3)=T\\
\mathrm{check}(\Gamma,\mathsf{succ}\ t_1)&=\mathsf{Nat}&&\text{if }\mathrm{check}(\Gamma,t_1)=\mathsf{Nat}
\end{aligned}`

The clauses for $`\mathsf{true}`, $`\mathsf{false}`, $`0`, $`\mathsf{pred}` and $`\mathsf{iszero}` follow T-True, T-False, T-Zero, T-Pred and T-IsZero in the same way. In every other case $`\mathrm{check}` fails. For example, on $`(\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x)\,\mathsf{true}` the application clause compares Nat with Bool and fails. As in C.3, the extension $`\Gamma,x{:}T_1` renames the parameter if $`x\in\mathrm{dom}(\Gamma)`. Each recursive call is on an immediate subterm, so $`\mathrm{check}` terminates.

*Proposition 28.2 (Correctness of the checker).* For every context $`\Gamma`, annotated term $`t` and type $`T`: $`\mathrm{check}(\Gamma,t)=T` if and only if $`\Gamma\vdash t:T`.

*Proof.* (⇒) By structural induction on $`t`, with $`P(t)\coloneqq\forall\Gamma,\ \forall T,\ \mathrm{check}(\Gamma,t)=T\Rightarrow\Gamma\vdash t:T`. The conditions of each clause are the premises of the one typing rule for that form, and the induction hypotheses turn the recursive results into derivations of them. The abstraction clause calls $`\mathrm{check}` under $`\Gamma,x{:}T_1`, so $`\Gamma` must be quantified inside $`P(t)`. (⇐) By induction on the derivation of $`\Gamma\vdash t:T`. In the T-App case the induction hypotheses give $`\mathrm{check}(\Gamma,t_1)=T_{11}\to T_{12}` and $`\mathrm{check}(\Gamma,t_2)=T_{11}`, so the application clause returns $`T_{12}`. The other cases are similar. $`\square`

Since $`\mathrm{check}(\Gamma,t)` has at most one result, a term has at most one type under $`\Gamma`. When $`\mathrm{check}` fails, the term has no type under $`\Gamma`.

Every test in Definition 28.1 compares types that are already known. The type of a parameter is known because the abstraction carries it. Without the annotation, the checker reaches the body of $`\lambda x.t_2` before anything is known about $`x`. Inference instead gives $`x` a type variable, turns each comparison into an equation, and solves the equations after it has visited the whole term.

# Constraints and the unification algorithm
%%%
tag := "ch28-s2"
%%%

From now on terms are unannotated and types may contain type variables. This session uses the following part of [C.5](lambda-card/index.html#lambda-c5):

$$`T ::= X\mid\mathsf{Bool}\mid\mathsf{Nat}\mid T\to T\qquad t ::= x\mid\lambda x.t\mid t\ t\mid\mathsf{true}\mid\mathsf{false}\mid\mathsf{if}\ t\ \mathsf{then}\ t\ \mathsf{else}\ t\mid 0\mid\mathsf{succ}\ t\mid\mathsf{pred}\ t\mid\mathsf{iszero}\ t`

Unit, pairs and the product case of $`\mathrm{unify}` are left out. Exercise 28.4 adds the product case. Write $`\mathrm{FV}(C)` for the set of type variables occurring in a constraint set $`C`. In a constraint set, $`S=T` is an equation that may or may not hold. Everywhere else an equals sign between two types states that they are identical.

Constraint typing $`\Gamma\vdash t:S\mid_{\mathcal X}C` visits a term once, as $`\mathrm{check}` does. Where $`\mathrm{check}` compares two types, it adds an equation to $`C`. Where $`\mathrm{check}` reads an annotation, CT-AbsInf uses a fresh type variable. The rules for functions are:

$$`\frac{x{:}T\in\Gamma}{\Gamma\vdash x:T\mid_{\varnothing}\varnothing}\;\textsf{CT-Var}\qquad\frac{\Gamma,x{:}X\vdash t_2:T_2\mid_{\mathcal X}C\quad X\ \text{fresh}}{\Gamma\vdash\lambda x.t_2:X\to T_2\mid_{\mathcal X\cup\{X\}}C}\;\textsf{CT-AbsInf}`

$$`\frac{\Gamma\vdash t_1:T_1\mid_{\mathcal X_1}C_1\quad\Gamma\vdash t_2:T_2\mid_{\mathcal X_2}C_2\quad X\ \text{fresh}}{\Gamma\vdash t_1\,t_2:X\mid_{\mathcal X_1\cup\mathcal X_2\cup\{X\}}C_1\cup C_2\cup\{T_1=T_2\to X\}}\;\textsf{CT-App}`

The constant rules give Bool or Nat with no equations. CT-Succ, CT-Pred and CT-IsZero add $`T=\mathsf{Nat}` for the type $`T` of the argument, and CT-If adds $`T_1=\mathsf{Bool}` and $`T_2=T_3`. Let $`s=(\lambda x.\mathsf{succ}\ x)\,0`. Reading the derivation from the root, CT-App chooses the fresh $`Y` and CT-AbsInf the fresh $`X`:

$$`\begin{aligned}
x{:}X&\vdash x:X\mid_{\varnothing}\varnothing&&\textsf{CT-Var}\\
x{:}X&\vdash\mathsf{succ}\ x:\mathsf{Nat}\mid_{\varnothing}\{X=\mathsf{Nat}\}&&\textsf{CT-Succ}\\
&\vdash\lambda x.\mathsf{succ}\ x:X\to\mathsf{Nat}\mid_{\{X\}}\{X=\mathsf{Nat}\}&&\textsf{CT-AbsInf}\\
&\vdash 0:\mathsf{Nat}\mid_{\varnothing}\varnothing&&\textsf{CT-Zero}\\
&\vdash s:Y\mid_{\{X,Y\}}C_s&&\textsf{CT-App}
\end{aligned}`

Here $`C_s=\{X=\mathsf{Nat},\ X\to\mathsf{Nat}=\mathsf{Nat}\to Y\}`. The second equation records the comparison that $`\mathrm{check}` made at the application. The substitution $`[X\mapsto\mathsf{Nat},Y\mapsto\mathsf{Nat}]` unifies $`C_s`, and it maps the type $`Y` of $`s` to Nat, the type of the annotated term.

*Substitutions.* By C.5, $`(\sigma\circ\gamma)T=\sigma(\gamma T)`, so $`\gamma` acts first. Two substitutions are *equal* if they give identical results on every type. A substitution leaves Bool and Nat unchanged and acts on $`S\to T` by acting on $`S` and on $`T`. So, by structural induction on types, two substitutions that agree on every type variable are equal. For example, $`[Y\mapsto\mathsf{Nat}]\circ[X\mapsto\mathsf{Nat}]=[X\mapsto\mathsf{Nat},Y\mapsto\mathsf{Nat}]`. Hence $`[X\mapsto\mathsf{Nat}]\sqsubseteq[X\mapsto\mathsf{Nat},Y\mapsto\mathsf{Nat}]`.

*Running unify.* The function $`\mathrm{unify}` of C.5 selects an equation $`S=T` of $`C`, and $`C'` is the set of the other equations. Any equation may be selected. Fix one rule for this choice, so that $`\mathrm{unify}` is a function. Theorem 28.4 holds for every such rule. On $`C_s`:

$$`\begin{aligned}
\mathrm{unify}(C_s)&=\mathrm{unify}(\{\mathsf{Nat}\to\mathsf{Nat}=\mathsf{Nat}\to Y\})\circ[X\mapsto\mathsf{Nat}]&&\text{second case, on }X=\mathsf{Nat}\\
&=\mathrm{unify}(\{\mathsf{Nat}=\mathsf{Nat},\ \mathsf{Nat}=Y\})\circ[X\mapsto\mathsf{Nat}]&&\text{arrow case}\\
&=\mathrm{unify}(\{\mathsf{Nat}=Y\})\circ[X\mapsto\mathsf{Nat}]&&\text{first case}\\
&=[Y\mapsto\mathsf{Nat}]\circ[X\mapsto\mathsf{Nat}]&&\text{third case, and }\mathrm{unify}(\varnothing)=[\,]
\end{aligned}`

*The board term.* Let $`u=\lambda f.\lambda x.f\,(f\,x)`. Reading the derivation from the root, CT-AbsInf gives $`f` the fresh $`X` and $`x` the fresh $`Y`. Let $`\Gamma=f{:}X,x{:}Y`.

1. CT-Var gives $`\Gamma\vdash f:X\mid_{\varnothing}\varnothing` and $`\Gamma\vdash x:Y\mid_{\varnothing}\varnothing`.
2. CT-App with the fresh $`Z_1` gives $`\Gamma\vdash f\,x:Z_1\mid_{\{Z_1\}}\{X=Y\to Z_1\}`.
3. CT-App with the fresh $`Z_2`, the operator $`f` of step 1 and the operand $`f\,x` of step 2 gives $`\Gamma\vdash f\,(f\,x):Z_2\mid_{\{Z_1,Z_2\}}C_u`, where $`C_u=\{X=Y\to Z_1,\ X=Z_1\to Z_2\}`. Both occurrences of $`f` receive the same $`X` from $`\Gamma`, so both equations constrain $`X`.
4. CT-AbsInf twice gives $`\vdash u:X\to Y\to Z_2\mid_{\{X,Y,Z_1,Z_2\}}C_u`.
5. Run $`\mathrm{unify}` on $`C_u`. Select $`X=Y\to Z_1`. The second case applies, since $`X\notin\mathrm{FV}(Y\to Z_1)=\{Y,Z_1\}`. It gives $`\mathrm{unify}(C_u)=\mathrm{unify}(\{Y\to Z_1=Z_1\to Z_2\})\circ[X\mapsto Y\to Z_1]`.
6. The arrow case gives $`\mathrm{unify}(\{Y=Z_1,\ Z_1=Z_2\})`.
7. Select $`Y=Z_1`. The second case gives $`\mathrm{unify}(\{Z_1=Z_2\})\circ[Y\mapsto Z_1]`, since $`[Y\mapsto Z_1]` leaves $`Z_1=Z_2` unchanged.
8. Select $`Z_1=Z_2`. The second case gives $`\mathrm{unify}(\varnothing)\circ[Z_1\mapsto Z_2]=[Z_1\mapsto Z_2]`.

Hence $`\mathrm{unify}(C_u)=[Z_1\mapsto Z_2]\circ[Y\mapsto Z_1]\circ[X\mapsto Y\to Z_1]`. To write it as one map, apply the factors to each variable, rightmost first. For instance, $`X` becomes $`Y\to Z_1`, then $`Z_1\to Z_1`, then $`Z_2\to Z_2`. So

$$`\mathrm{unify}(C_u)=[X\mapsto Z_2\to Z_2,\ Y\mapsto Z_2,\ Z_1\mapsto Z_2],`

and it maps the type $`X\to Y\to Z_2` of $`u` to $`(Z_2\to Z_2)\to Z_2\to Z_2`. The composition matters. The three bindings applied at once, $`[X\mapsto Y\to Z_1,Y\mapsto Z_1,Z_1\mapsto Z_2]`, map $`X` to $`Y\to Z_1` but $`Y\to Z_1` to $`Z_1\to Z_2`, so they do not unify $`C_u`.

Another unifier of $`C_u` is $`\sigma'=[X\mapsto\mathsf{Nat}\to\mathsf{Nat},\ Y\mapsto\mathsf{Nat},\ Z_1\mapsto\mathsf{Nat},\ Z_2\mapsto\mathsf{Nat}]`. It equals $`[Z_2\mapsto\mathsf{Nat}]\circ\mathrm{unify}(C_u)`, since both map $`X` to $`\mathsf{Nat}\to\mathsf{Nat}` and $`Y,Z_1,Z_2` to Nat. So $`\mathrm{unify}(C_u)\sqsubseteq\sigma'`. On the other hand, $`\mathrm{unify}` fails on $`\{X=X\to Y\}`, the constraint set of $`\lambda x.x\,x`: the occurs check blocks the second case and no other case applies. It also fails on $`\{\mathsf{Bool}=\mathsf{Nat}\}`, the constraint set of $`\mathsf{succ}\ \mathsf{true}`.

# Correctness of unification
%%%
tag := "ch28-s3"
%%%

The *size* of a type counts its nodes: $`\mathrm{size}(X)=\mathrm{size}(\mathsf{Bool})=\mathrm{size}(\mathsf{Nat})=1` and $`\mathrm{size}(S\to T)=1+\mathrm{size}(S)+\mathrm{size}(T)`. Let $`\mathrm{size}(C)` be the sum of the sizes of both sides of all equations of $`C`. The *degree* of $`C` is the pair $`(|\mathrm{FV}(C)|,\mathrm{size}(C))`. Pairs are compared lexicographically: one pair is smaller than another if its first component is smaller, or if the first components are equal and its second component is smaller. In the run on $`C_u` the degrees are $`(4,8)`, $`(3,6)`, $`(3,4)`, $`(2,2)` and $`(0,0)`, each smaller than the one before.

*Theorem 28.4 (Unification).* For every constraint set $`C`:
(a) the computation of $`\mathrm{unify}(C)` terminates, by failing or by returning a substitution;
(b) if $`\mathrm{unify}(C)` returns $`\sigma`, then $`\sigma` unifies $`C`;
(c) if $`\sigma'` unifies $`C`, then $`\mathrm{unify}(C)` returns a substitution $`\sigma` with $`\sigma\sqsubseteq\sigma'`.
Consequently $`\mathrm{unify}(C)` fails exactly when $`C` has no unifier. Otherwise it returns a principal unifier of $`C`.

*Proof of (a).* Each case of $`\mathrm{unify}` stops or calls $`\mathrm{unify}` once on a set of smaller degree. The first case removes an equation $`S=S`: no type variable is added and the size drops. The second case removes $`X`: the set $`[X\mapsto T]C'` contains no $`X`, because $`X\notin\mathrm{FV}(T)`, and no type variable outside $`\mathrm{FV}(C)`, so the first component drops. The third case is the same with $`S` in place of $`T`. The arrow case adds no type variable and removes two arrow nodes. A sequence of degrees that decreases at every call is finite: the first component can drop at most $`|\mathrm{FV}(C)|` times, and between two drops the second component, a natural number, drops at every call. $`\square`

Let $`k(C)` be the number of calls of $`\mathrm{unify}` in the computation of $`\mathrm{unify}(C)`, the first call included. By (a) it is a natural number. If the first call makes a recursive call on a set $`C''`, then $`k(C'')=k(C)-1`. Parts (b) and (c) are proved by induction on $`k(C)`.

*Proof of (b).* The induction property is $`B(C)\coloneqq\forall\sigma,\ (\mathrm{unify}(C)=\sigma)\Rightarrow\sigma\text{ unifies }C`. For $`C=\varnothing`, $`[\,]` unifies $`\varnothing`. In the first case $`\sigma=\mathrm{unify}(C')` unifies $`C'` by $`B(C')`, and $`\sigma S=\sigma T` because $`S` and $`T` are identical. In the second case $`\sigma=\sigma_1\circ[X\mapsto T]`, where $`\sigma_1=\mathrm{unify}([X\mapsto T]C')` unifies $`[X\mapsto T]C'` by the induction hypothesis. For each equation $`U_1=U_2` of $`C'`, $`\sigma U_1=\sigma_1([X\mapsto T]U_1)=\sigma_1([X\mapsto T]U_2)=\sigma U_2`. For the selected equation, $`\sigma X=\sigma_1T=\sigma_1([X\mapsto T]T)=\sigma T`, because $`X\notin\mathrm{FV}(T)`. The third case is symmetric. In the arrow case $`\sigma` unifies $`C'\cup\{S_1=T_1,S_2=T_2\}` by the induction hypothesis, so $`\sigma(S_1\to S_2)=\sigma S_1\to\sigma S_2=\sigma T_1\to\sigma T_2=\sigma(T_1\to T_2)`. $`\square`

In the run on $`C_u`, the selected equation $`X=Y\to Z_1` holds under $`\sigma'`: both sides become $`\mathsf{Nat}\to\mathsf{Nat}`. So replacing $`X` by $`Y\to Z_1` before applying $`\sigma'` changes nothing. For example, $`\sigma'([X\mapsto Y\to Z_1](X\to Z_2))=\sigma'((Y\to Z_1)\to Z_2)=(\mathsf{Nat}\to\mathsf{Nat})\to\mathsf{Nat}=\sigma'(X\to Z_2)`.

*Lemma 28.3 (Solved variable).* For every substitution $`\sigma'`, type variable $`X` and types $`T,U`: if $`\sigma'X=\sigma'T`, then $`\sigma'([X\mapsto T]U)=\sigma'U`.

*Proof.* By structural induction on $`U`. If $`U=X`, then $`\sigma'([X\mapsto T]X)=\sigma'T=\sigma'X`. If $`U` is another type variable, Bool or Nat, then $`[X\mapsto T]U=U`. If $`U=U_1\to U_2`, the induction hypotheses for $`U_1` and $`U_2` give $`\sigma'([X\mapsto T]U)=\sigma'([X\mapsto T]U_1)\to\sigma'([X\mapsto T]U_2)=\sigma'U_1\to\sigma'U_2=\sigma'U`. $`\square`

*Proof of (c).* The induction property is

$$`Q(C)\coloneqq\forall\sigma',\ (\sigma'\text{ unifies }C)\Rightarrow\mathrm{unify}(C)\text{ returns some }\sigma\text{ with }\sigma\sqsubseteq\sigma'.`

The induction hypothesis is $`Q(C'')` for the set $`C''` of the recursive call. Fix $`\sigma'` that unifies $`C`. Before the general variable case, follow it on the first call of the run on $`C_u`, with the unifier $`\sigma'` of §28.2. There $`[X\mapsto Y\to Z_1]C'=\{Y\to Z_1=Z_1\to Z_2\}`, and $`\sigma'` maps both of its sides to $`\mathsf{Nat}\to\mathsf{Nat}`. The recursive call returns $`\sigma_1=[Z_1\mapsto Z_2]\circ[Y\mapsto Z_1]`, and $`\sigma'=\gamma\circ\sigma_1` with $`\gamma=[X\mapsto\mathsf{Nat}\to\mathsf{Nat},Z_2\mapsto\mathsf{Nat}]`. Here $`\gamma` must map $`X`, because $`\sigma_1` leaves $`X` unchanged. At $`X` the composite $`\gamma\circ\sigma_1\circ[X\mapsto Y\to Z_1]` gives $`\gamma(Z_2\to Z_2)=\mathsf{Nat}\to\mathsf{Nat}=\sigma'X`.

*Variable case.* Suppose $`\mathrm{unify}` selects $`X=T` with $`X\notin\mathrm{FV}(T)`, so the second case applies and $`C=\{X=T\}\cup C'`. We must show that $`\mathrm{unify}(C)` returns some $`\sigma` with $`\sigma\sqsubseteq\sigma'`.

1. $`\sigma'` unifies the selected equation, so $`\sigma'X=\sigma'T`.
2. Let $`U_1=U_2` be an equation of $`C'`. By Lemma 28.3 with step 1, and since $`\sigma'` unifies $`C'`, $`\sigma'([X\mapsto T]U_1)=\sigma'U_1=\sigma'U_2=\sigma'([X\mapsto T]U_2)`. So $`\sigma'` unifies $`[X\mapsto T]C'`.
3. The computation of $`\mathrm{unify}(C)` calls $`\mathrm{unify}([X\mapsto T]C')`. Apply the induction hypothesis $`Q([X\mapsto T]C')` to $`\sigma'` and step 2. It gives that $`\mathrm{unify}([X\mapsto T]C')` returns some $`\sigma_1`, and that $`\sigma'=\gamma\circ\sigma_1` for some substitution $`\gamma`.
4. By the second case of $`\mathrm{unify}`, $`\mathrm{unify}(C)` returns $`\sigma=\sigma_1\circ[X\mapsto T]`. It remains to show $`\sigma'=\gamma\circ\sigma`. We compare both sides on each type variable.
5. For a type variable $`Z\neq X`: $`(\gamma\circ\sigma)Z=\gamma(\sigma_1([X\mapsto T]Z))=\gamma(\sigma_1Z)=\sigma'Z`, by step 3.
6. For $`X`: $`(\gamma\circ\sigma)X=\gamma(\sigma_1([X\mapsto T]X))=\gamma(\sigma_1T)=\sigma'T=\sigma'X`, by step 3 applied to the type $`T` and then step 1.
7. By steps 5 and 6 the two substitutions agree on every type variable, so $`\sigma'=\gamma\circ\sigma`. That is, $`\sigma\sqsubseteq\sigma'`.

*Other cases.* If $`C=\varnothing`, then $`\mathrm{unify}(C)=[\,]` and $`\sigma'=\sigma'\circ[\,]`. In the first case $`\sigma'` unifies $`C'`, and $`Q(C')` gives the result, since $`\mathrm{unify}(C)=\mathrm{unify}(C')`. The third case is the variable case with the two sides exchanged. In the arrow case $`\sigma'S_1\to\sigma'S_2=\sigma'T_1\to\sigma'T_2`. Two arrow types are identical only if their domains are identical and their codomains are identical. So $`\sigma'` unifies $`C'\cup\{S_1=T_1,S_2=T_2\}`, and the induction hypothesis for that set gives the result.

*Failure cannot occur.* Suppose $`\mathrm{unify}` reaches fail at the selected equation $`S=T`. Since no earlier case applies, one of the following holds. (i) $`S` is a type variable $`X`, $`X\in\mathrm{FV}(T)`, and $`T` is not $`X`. Then $`T` is an arrow containing $`X`, and structural induction on $`T` gives $`\mathrm{size}(\sigma'T)>\mathrm{size}(\sigma'X)`, contradicting $`\sigma'X=\sigma'T`. (ii) $`T` is a type variable that occurs in $`S`, and $`S` is not that variable. This is (i) with the sides exchanged. (iii) Neither side is a type variable, and their outermost constructors, among Bool, Nat and $`\to`, differ. A substitution keeps the outermost constructor of a type that is not a variable, so $`\sigma'S` and $`\sigma'T` differ, a contradiction. This completes the proof of (c). $`\square`

*The consequence.* If $`C` has no unifier, then by (b) $`\mathrm{unify}(C)` cannot return a substitution, so by (a) it fails. If $`C` has a unifier, then by (c) $`\mathrm{unify}(C)` returns some $`\sigma`, which unifies $`C` by (b). Since $`\mathrm{unify}(C)` has only one result, (c) gives $`\sigma\sqsubseteq\sigma''` for every unifier $`\sigma''` of $`C`. So $`\sigma` is a principal unifier. $`\square`

# Principal types
%%%
tag := "ch28-s4"
%%%

The type $`(Z_2\to Z_2)\to Z_2\to Z_2` computed for $`u` in §28.2 is a type of $`u`: under $`f{:}Z_2\to Z_2,x{:}Z_2`, T-App twice types $`f\,(f\,x)` at $`Z_2`, and T-Abs twice gives the rest. So is its image $`(\mathsf{Nat}\to\mathsf{Nat})\to\mathsf{Nat}\to\mathsf{Nat}` under $`[Z_2\mapsto\mathsf{Nat}]`. Every image has the form $`(U\to U)\to U\to U`, so $`(\mathsf{Bool}\to\mathsf{Nat})\to\mathsf{Bool}\to\mathsf{Nat}` is not one. The following results say that the types of $`u` are exactly these images.

*Proposition 28.5 (Constraint typing).* Let $`\vdash t:S\mid_{\mathcal X}C`.
(a) If $`\sigma` unifies $`C`, then $`\vdash t:\sigma S`.
(b) If $`\vdash t:T`, then some unifier $`\sigma'` of $`C` satisfies $`\sigma'S=T`.

*Proof of (a).* We prove that if $`\Gamma\vdash t:S\mid_{\mathcal X}C` and $`\sigma` unifies $`C`, then $`\sigma\Gamma\vdash t:\sigma S`, by induction on the constraint typing derivation. CT-AbsInf: the induction hypothesis gives $`\sigma\Gamma,x{:}\sigma X\vdash t_2:\sigma T_2`, and the unannotated T-Abs with parameter type $`\sigma X` gives $`\sigma\Gamma\vdash\lambda x.t_2:\sigma(X\to T_2)`. CT-App: $`\sigma` unifies $`C_1`, $`C_2` and $`T_1=T_2\to X`, so the induction hypotheses give $`\sigma\Gamma\vdash t_1:\sigma T_2\to\sigma X` and $`\sigma\Gamma\vdash t_2:\sigma T_2`, and T-App gives $`\sigma\Gamma\vdash t_1\,t_2:\sigma X`. The other rules are similar, using $`\sigma\mathsf{Bool}=\mathsf{Bool}` and $`\sigma\mathsf{Nat}=\mathsf{Nat}`. $`\square`

Part (b) is stated without proof. Its proof gives each fresh type variable the type found at its place in the given derivation of $`\vdash t:T` (Further Reading).

*Corollary 28.6 (Principal types).* Let $`\vdash t:S\mid_{\mathcal X}C`. If $`\mathrm{unify}(C)` fails, then $`t` has no type. If $`\mathrm{unify}(C)` returns $`\sigma`, then $`\vdash t:\sigma S`, and for every type $`T` with $`\vdash t:T` there is a substitution $`\gamma` with $`T=\gamma(\sigma S)`. Moreover $`\sigma S` is a principal type of $`t` (C.5).

*Proof.* If $`\vdash t:T`, Proposition 28.5(b) gives a unifier $`\sigma'` of $`C` with $`\sigma'S=T`, so $`\mathrm{unify}(C)` does not fail by Theorem 28.4. If $`\mathrm{unify}(C)` returns $`\sigma`, then $`\sigma` unifies $`C` by Theorem 28.4(b), and $`\vdash t:\sigma S` by Proposition 28.5(a). Given $`\vdash t:T`, take $`\sigma'` as before. Theorem 28.4(c) gives $`\sigma'=\gamma\circ\sigma` for some $`\gamma`, so $`T=\sigma'S=\gamma(\sigma S)`. Finally, every solution $`(\sigma'',T'')` for $`(\varnothing,t,S,C)` has $`\sigma''` unifying $`C`, so $`\sigma\sqsubseteq\sigma''` by Theorem 28.4(c), and $`(\sigma,\sigma S)` is a principal solution. $`\square`

*What is proved and what is stated.* Theorem 28.4 is proved completely in §28.3, and Proposition 28.5(a) above. Proposition 28.5(b) is only stated. The corollary uses it for two claims: that $`t` has no type when $`\mathrm{unify}(C)` fails, and that every type of $`t` is some $`\gamma(\sigma S)`. Its other claims rest on proved results only.

For annotated terms Proposition 28.2 gives at most one type. An unannotated term can have many: $`\lambda x.x` has types $`\mathsf{Nat}\to\mathsf{Nat}` and $`\mathsf{Bool}\to\mathsf{Bool}`. The principal type takes the place of the unique type, since every type of the term is obtained from it by a substitution.

# Exercises
%%%
tag := "ch28-s5"
number := false
%%%

*28.1.* A faulty checker returns $`T_{11}` instead of $`T_{12}` in the application clause of Definition 28.1. Find a closed annotated term on which it returns a type that the term does not have. Would tests that only apply identity functions find the error?

*28.2.* Generate the constraints of $`\lambda f.\lambda x.f\,x`, run $`\mathrm{unify}`, and give the principal type. Which equation fixes the type of $`f`?

*28.3.* Generate the constraints of $`0\ \mathsf{true}` and of $`\lambda x.x\,x`. For each, explain why $`\mathrm{unify}` reaches fail, and name the subcase of “Failure cannot occur” in §28.3 that excludes a unifier.

*28.4.* Add the types $`S\times T` and the product case of C.5 to $`\mathrm{unify}`. Extend the proofs of Lemma 28.3 and of parts (a), (b) and (c) of Theorem 28.4.

*Further problem.* Find the principal type of $`\lambda x.\lambda f.f\,(f\,x)`. Can the term have type $`\mathsf{Bool}\to(\mathsf{Bool}\to\mathsf{Nat})\to\mathsf{Nat}`? Locate the equation at which $`\mathrm{unify}` fails, and explain why typing the inner application $`f\,x` alone does not reveal the problem.

# Reading for the Seminar
%%%
tag := "ch28-s6"
number := false
%%%

*Definitions · 10 minutes.* Run $`\mathrm{check}` on $`(\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x)\,0`. Erase the annotation, generate $`C_s` and run $`\mathrm{unify}` on it. Point to the equation of $`C_s` that records the comparison $`\mathrm{check}` made at the application.

*Joint proof · 30 minutes.* The board case. One person generates $`C_u` for $`u=\lambda f.\lambda x.f\,(f\,x)` and runs $`\mathrm{unify}` (steps 1–8 of §28.2), writing the result as one map. A second writes $`Q(C)` and steps 1–3 of the variable case. A third does steps 4–7, first on the first call of the run on $`C_u` with $`\sigma'` and $`\gamma=[X\mapsto\mathsf{Nat}\to\mathsf{Nat},Z_2\mapsto\mathsf{Nat}]`, then in general.

*Proof review · 20 minutes.* Say which claims of Theorem 28.4, Proposition 28.5 and Corollary 28.6 are proved and which are only stated. Do Exercise 28.3 and match each failure with a subcase of the failure argument. Explain what goes wrong if the occurs check is dropped.

*Facilitator’s hint.* In step 6 the substitution $`[X\mapsto T]` acts first and replaces $`X` by $`T`. Step 1 then turns $`\sigma'T` back into $`\sigma'X`.

# Solutions and Further Reading
%%%
tag := "ch28-s7"
number := false
%%%

*28.1.* Take $`(\lambda x{:}\mathsf{Nat}.\mathsf{true})\,0`. The operator has type $`\mathsf{Nat}\to\mathsf{Bool}` and the operand Nat, so the comparison succeeds. The correct checker returns Bool and the faulty one returns Nat. By Proposition 28.2 the term has type Bool, and a term has at most one type, so Nat is wrong. An identity function has a type $`T\to T` whose domain and codomain coincide, so on its applications both checkers return $`T`. A test needs a function whose domain and codomain differ.

*28.2.* Give $`f` the type $`X`, $`x` the type $`Y`, and the application the fresh $`Z`. CT-App gives $`C=\{X=Y\to Z\}`, and the term has type $`X\to Y\to Z`. The second case of $`\mathrm{unify}` gives $`[X\mapsto Y\to Z]`, so the principal type is $`(Y\to Z)\to Y\to Z`. The equation $`X=Y\to Z` fixes the type of $`f`.

*28.3.* For $`0\ \mathsf{true}`, CT-App with a fresh $`Y` gives $`\{\mathsf{Nat}=\mathsf{Bool}\to Y\}`. Neither side is a type variable and the outermost constructors are Nat and $`\to`, so no case applies. This is subcase (iii). For $`\lambda x.x\,x`, $`x` receives $`X`, and CT-App with a fresh $`Y` gives $`\{X=X\to Y\}`. The occurs check blocks the second case, the third case needs a variable on the right, and the arrow case needs an arrow on the left. This is subcase (i): a unifier $`\sigma'` would need $`\sigma'X=\sigma'(X\to Y)`, whose size is at least $`\mathrm{size}(\sigma'X)+2`.

*28.4.* Let $`\mathrm{size}(S\times T)=1+\mathrm{size}(S)+\mathrm{size}(T)`. Lemma 28.3 and part (b) gain a case written like the arrow case, with $`\times` for $`\to`. (a) The product case adds no type variable and removes two $`\times` nodes. (c) Two product types are identical only if their components are, so $`\sigma'` unifies the new set and the induction hypothesis applies. In the failure argument, $`\times` is one more outermost constructor that substitutions keep, and the size argument of (i) also covers a variable inside a product.

*Further problem.* Give $`x` the type $`X`, $`f` the type $`Y`, and the two applications the fresh $`Z_1` and $`Z_2`. Then $`C=\{Y=X\to Z_1,\ Y=Z_1\to Z_2\}` and the term has type $`X\to Y\to Z_2`. Selecting from left to right, $`\mathrm{unify}` returns $`[Z_1\mapsto Z_2]\circ[X\mapsto Z_1]\circ[Y\mapsto X\to Z_1]`, and the principal type is $`Z_2\to(Z_2\to Z_2)\to Z_2`. By Corollary 28.6 every type of the term has the form $`U\to(U\to U)\to U`, and the demanded type would need $`U=\mathsf{Bool}` and $`U=\mathsf{Nat}`. To locate the failure, add $`X\to Y\to Z_2=\mathsf{Bool}\to(\mathsf{Bool}\to\mathsf{Nat})\to\mathsf{Nat}` to $`C`. The arrow case gives $`X=\mathsf{Bool}`, $`Y=\mathsf{Bool}\to\mathsf{Nat}` and $`Z_2=\mathsf{Nat}`, which turn the two equations for $`f` into $`\mathsf{Bool}\to\mathsf{Nat}=\mathsf{Bool}\to Z_1` and $`\mathsf{Bool}\to\mathsf{Nat}=Z_1\to\mathsf{Nat}`. The first gives $`Z_1=\mathsf{Nat}`, and the second then gives $`\mathsf{Bool}=\mathsf{Nat}`, where $`\mathrm{unify}` fails. The inner application $`f\,x` is well typed with $`x{:}\mathsf{Bool}` and $`f{:}\mathsf{Bool}\to\mathsf{Nat}`. The outer one passes a number to $`f`, whose domain is Bool.

*Further reading · Comparing types in a checker.* The application clause of Definition 28.1 compares two types node by node. A comparison of outermost constructors alone would accept an operand of type $`(\mathsf{Bool}\to\mathsf{Nat})\to\mathsf{Nat}` where $`(\mathsf{Nat}\to\mathsf{Bool})\to\mathsf{Nat}` is required. With subtyping the rule T-App itself changes (TAPL, chapter 15). TAPL §10.3 implements the checker, and TAPL §9.3 proves that a term has at most one type.

*Further reading · Completeness of constraint typing.* Proposition 28.5(b) is proved by induction on the derivation of $`\vdash t:T`, building the unifier as it goes. The parameter variable of each abstraction receives the parameter type that T-Abs chose there, and the result variable of each application receives the type of that application. The type variables of different subderivations are distinct, so the substitutions built for them can be joined into one. TAPL §22.3 proves this for annotated abstractions, and TAPL §22.6 explains why CT-AbsInf behaves the same way.

*Further reading · Choice and renaming.* The rule for choosing an equation can change the result of $`\mathrm{unify}`. For example, $`\mathrm{unify}(\{X=Y\})=[X\mapsto Y]` and $`\mathrm{unify}(\{Y=X\})=[Y\mapsto X]`, although both sets have the same unifiers. Each result is more general than the other: $`[Y\mapsto X]=[Y\mapsto X]\circ[X\mapsto Y]` and $`[X\mapsto Y]=[X\mapsto Y]\circ[Y\mapsto X]`. So principal unifiers are not unique, and neither are principal types: $`(Y\to Y)\to Y\to Y` is as good a principal type of $`u` as $`(Z_2\to Z_2)\to Z_2\to Z_2`.

*Further reading · The occurs check and infinite types.* Subcase (i) of the failure argument rests on types being finite trees. If types could be infinite trees, $`X=X\to Y` would have a unifier mapping $`X` to the infinite tree $`((\cdots\to Y)\to Y)\to Y`. TAPL, chapters 20 and 21, studies such recursive types.

*Further reading · Session 29.* The rule CT-LetGen of C.5 calls $`\mathrm{unify}` on the constraints of the right-hand side of a let, applies the result, and quantifies the type variables that are not free in the context. Session 29 relies on Theorem 28.4 at that step.

# Sources and Formalization
%%%
tag := "ch28-notes"
number := false
%%%

* *Proposition 28.2.* Formulated in this book. Paper proof only (proof in [§28.1](chapter-28/index.html#ch28-s1)).
* *Lemma 28.3.* Formulated in this book. Paper proof only (proof in [§28.3](chapter-28/index.html#ch28-s3)).
* *Theorem 28.4.* Source: TAPL §22.4. Paper proof only (proof in [§28.3](chapter-28/index.html#ch28-s3)).
* *Proposition 28.5.* Corresponds to TAPL §22.3. Paper proof only (part (a) in [§28.4](chapter-28/index.html#ch28-s4); part (b) for annotated abstractions in TAPL §22.3).
* *Corollary 28.6.* Corresponds to TAPL §22.5. Paper proof only (proof in [§28.4](chapter-28/index.html#ch28-s4)).
