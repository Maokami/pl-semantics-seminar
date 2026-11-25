import VersoManual

open Verso.Genre Manual

#doc (Manual) "Type Abstraction: System F and Existential Types" =>
%%%
tag := "ch31"
file := "chapter-31"
%%%

* *Definitions.* The typed language of Session 31 ([Lambda language card](lambda-card/index.html)). This session uses Bool and Nat ([C.2](lambda-card/index.html#lambda-c2)), functions and Unit ([C.3](lambda-card/index.html#lambda-c3)), pairs and projections ([C.4](lambda-card/index.html#lambda-c4)), and everything in [C.7](lambda-card/index.html#lambda-c7): type variables in contexts, well-formed types, the substitution $`[X\mapsto S]T` and its action on terms, and the rules E-TApp, E-TappTabs, E-Pack, E-Unpack, E-UnpackPack, T-TAbs, T-TApp, T-Pack and T-Unpack. Inversion of typing ([Session 26, Lemma 26.1](chapter-26/index.html#ch26-s1); [Session 27, Lemma 27.1](chapter-27/index.html#ch27-s1)). The substitution lemma ([Session 25, Theorem 25.5](chapter-25/index.html#ch25-s3)). Store typings ([C.6](lambda-card/index.html#lambda-c6)). The safety table and its Rows 1–5 ([C.8](lambda-card/index.html#lambda-c8)).
* *New terms.* Type abstraction, universal type, existential type, abstract type, escape condition. [Glossary and label key](glossary/index.html)
* *Proposition 31.1 (Typing and instantiating twice), Proposition 31.2 (Opening the counter) and Proposition 31.3 (The escape condition rejects a client).* Let $`\mathit{twice}=\lambda X.\lambda f{:}X\to X.\lambda x{:}X.f\ (f\ x)`, and let $`\mathit{counter}` and $`\mathit{Counter}` be as in §31.2. (31.1) $`\vdash\mathit{twice}:\forall X.(X\to X)\to X\to X`, $`\vdash\mathit{twice}\ [\mathsf{Nat}]:(\mathsf{Nat}\to\mathsf{Nat})\to\mathsf{Nat}\to\mathsf{Nat}`, and $`\mathit{twice}\ [\mathsf{Nat}]\to\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\lambda x{:}\mathsf{Nat}.f\ (f\ x)`. (31.2) The client $`\mathit{client}=\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ c.2.2\ (c.2.1\ c.1)` satisfies $`\vdash\mathit{client}:\mathsf{Nat}`, and its first step is by E-UnpackPack. (31.3) There is no type $`T` with $`\vdash\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ c.1:T`.
* *Source.* Benjamin C. Pierce, _Types and Programming Languages_ (TAPL). The rules of C.7 for universal types are those of System F (§23.3), and §23.5 states progress and preservation for System F. The rules for existential types are those of §24.1, and §24.2 uses them to build a counter as an abstract data type. TAPL’s counter uses records. This book’s counter is written with pairs. TAPL’s examples in §23.4 include $`\mathit{twice}` under the name double. TAPL obtains the escape condition from the scope of $`X`, and C.7 writes it as a premise of T-Unpack. Theorem 31.5 states Row 6 of the safety table without proof. [Source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)
* *Board case.* Three computations. (1) Derive the type of $`\mathit{twice}` in seven numbered lines, instantiate it at Nat by T-TApp, and take the step by E-TappTabs (§31.1). (2) Type the counter by T-Pack, type the body of $`\mathit{client}` under the context $`X,\ c{:}X\times((X\to X)\times(X\to\mathsf{Nat}))`, close with T-Unpack, and take the step by E-UnpackPack (§31.2). (3) Show by inversion that the body $`c.1` has type $`X`, so the escape condition of T-Unpack fails (§31.3).
* *Proof outline.* For each form of term exactly one typing rule has a conclusion of that form. A derivation is therefore built from the outermost form of the term inward, and inversion reads it back. Each step is one computation rule that substitutes a type for a type variable: E-TappTabs for a type application, E-UnpackPack for an unpacking. For Proposition 31.3, inversion forces the last rule to be T-Unpack and the type of the body to be $`X`. Theorem 31.5 (Row 6: canonical forms, progress, preservation) is stated without proof. Lemma 31.4 (type substitution) is proved in Further Reading.
* *From Session 30.* Session 30 generalized at let only when the right-hand side is a value, because generalizing $`\mathsf{ref}\ (\lambda x.x)` lets two uses of one cell choose different types. Here the quantifier becomes part of a type, $`\forall X.T`, and every instantiation is written as a type application. T-TAbs generalizes any term $`t`, value or not. The abstraction $`\lambda X.t` is a value and no rule steps inside it, so each type application evaluates the body anew for its own type argument. Row 6 keeps the store typing $`\Sigma` of Session 30. The examples of this session have no locations, and $`\vdash t:T` abbreviates $`\varnothing\mid\varnothing\vdash t:T` ([Lambda card, Judgments](lambda-card/index.html)).

The terms $`\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\lambda x{:}\mathsf{Nat}.f\ (f\ x)` and $`\lambda f{:}\mathsf{Bool}\to\mathsf{Bool}.\lambda x{:}\mathsf{Bool}.f\ (f\ x)` both apply a function twice. They differ only in their annotations, yet the typed language of Session 30 needs both, because an abstraction has one parameter type. This session adds a type parameter. The single term $`\mathit{twice}` takes a type as its first argument, and its caller writes $`\mathit{twice}\ [\mathsf{Nat}]` or $`\mathit{twice}\ [\mathsf{Bool}]`. The session also adds the reverse arrangement, in which the implementer chooses a type and hides it. A counter represented by a number is given to clients that know only that some type has a start value, an increment and a read operation. A client may read the counter. It may not return the counter itself, because the type of the result would name the hidden type outside the place where that name is valid.

# Type abstraction and type application
%%%
tag := "ch31-s1"
%%%

[C.7](lambda-card/index.html#lambda-c7) adds type variables $`X,Y,Z` to the types. Two of its term forms concern universal types. A *type abstraction* $`\lambda X.t` binds the type variable $`X` in the types written in $`t`. A *type application* $`t\ [T]` supplies the type argument $`T`. A *universal type* $`\forall X.T` is the type of a type abstraction whose body has type $`T` for every choice of $`X`. A term now has two kinds of binder. In $`\mathit{twice}=\lambda X.\lambda f{:}X\to X.\lambda x{:}X.f\ (f\ x)` the binder $`\lambda X` binds the three occurrences of $`X` in the annotations. The binders $`\lambda f` and $`\lambda x` bind the occurrences of $`f` and $`x` in the body $`f\ (f\ x)`.

A context may now bind type variables: $`\Gamma ::= \cdots\mid\Gamma,X`. A type is *well formed* in $`\Gamma` if each of its free type variables is bound in $`\Gamma`. Every type written in a term must be well formed in the context of the rule that inspects it (C.7). For example, $`X\vdash\lambda x{:}X.x:X\to X` by T-Var and T-Abs, but $`\lambda x{:}X.x` has no type in the empty context, where $`X` is not well formed. The extension $`\Gamma,X` requires $`X\notin\mathrm{dom}(\Gamma)`, and a bound type variable is renamed when necessary. The rules for the new forms are:

$$`\frac{\Gamma,X\vdash t_2:T_2}{\Gamma\vdash\lambda X.t_2:\forall X.T_2}\;\textsf{T-TAbs}\qquad\frac{\Gamma\vdash t_1:\forall X.T_{12}}{\Gamma\vdash t_1\ [T_2]:[X\mapsto T_2]T_{12}}\;\textsf{T-TApp}`

$$`\frac{t_1\to t_1'}{t_1\ [T_2]\to t_1'\ [T_2]}\;\textsf{E-TApp}\qquad\frac{}{(\lambda X.t_{12})\ [T_2]\to[X\mapsto T_2]t_{12}}\;\textsf{E-TappTabs}`

T-TAbs types the body under the extra binding $`X`. T-TApp substitutes the type argument into the body of the universal type. E-TappTabs substitutes it into the body of the type abstraction, where it replaces $`X` in every annotation. No rule steps inside a type abstraction, so $`\lambda X.t` is a value whatever $`t` is.

Take the identity $`\mathit{id}=\lambda X.\lambda x{:}X.x`. T-Var gives $`X,\ x{:}X\vdash x:X`, T-Abs gives $`X\vdash\lambda x{:}X.x:X\to X`, and T-TAbs gives $`\vdash\mathit{id}:\forall X.X\to X`. Since $`[X\mapsto\mathsf{Nat}](X\to X)=\mathsf{Nat}\to\mathsf{Nat}`, T-TApp gives $`\vdash\mathit{id}\ [\mathsf{Nat}]:\mathsf{Nat}\to\mathsf{Nat}`. The term $`\mathit{id}\ [\mathsf{Nat}]\ 0` takes two steps:

$$`\mathit{id}\ [\mathsf{Nat}]\ 0\ \to\ (\lambda x{:}\mathsf{Nat}.x)\ 0\ \to\ 0.`

The first step is E-TappTabs, lifted by E-App1. It replaces a type variable in an annotation. The second step is E-AppAbs. It replaces a term variable in the body.

*Proposition 31.1 (Typing and instantiating twice).*

* (a) $`\vdash\mathit{twice}:\forall X.(X\to X)\to X\to X`.
* (b) $`\vdash\mathit{twice}\ [\mathsf{Nat}]:(\mathsf{Nat}\to\mathsf{Nat})\to\mathsf{Nat}\to\mathsf{Nat}`.
* (c) $`\mathit{twice}\ [\mathsf{Nat}]\to\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\lambda x{:}\mathsf{Nat}.f\ (f\ x)`, and the result has the type in (b).

*Proof (board case).* We must derive two typings and one step. The arrow associates to the right, so $`(X\to X)\to X\to X` is $`(X\to X)\to(X\to X)`. Write $`\Gamma_{\mathrm{tw}}=X,\ f{:}X\to X,\ x{:}X`. This context is well formed, because $`X\to X` and $`X` are well formed in the context $`X`. Each line names its rule and the lines of its premises.

1. $`\Gamma_{\mathrm{tw}}\vdash x:X` by T-Var, since $`x{:}X\in\Gamma_{\mathrm{tw}}`.
2. $`\Gamma_{\mathrm{tw}}\vdash f:X\to X` by T-Var, since $`f{:}X\to X\in\Gamma_{\mathrm{tw}}`.
3. $`\Gamma_{\mathrm{tw}}\vdash f\ x:X` by T-App from 2 and 1.
4. $`\Gamma_{\mathrm{tw}}\vdash f\ (f\ x):X` by T-App from 2 and 3.
5. $`X,\ f{:}X\to X\vdash\lambda x{:}X.f\ (f\ x):X\to X` by T-Abs from 4.
6. $`X\vdash\lambda f{:}X\to X.\lambda x{:}X.f\ (f\ x):(X\to X)\to X\to X` by T-Abs from 5.
7. $`\vdash\mathit{twice}:\forall X.(X\to X)\to X\to X` by T-TAbs from 6. This is (a).
8. $`\vdash\mathit{twice}\ [\mathsf{Nat}]:(\mathsf{Nat}\to\mathsf{Nat})\to\mathsf{Nat}\to\mathsf{Nat}` by T-TApp from 7, since $`[X\mapsto\mathsf{Nat}]((X\to X)\to X\to X)=(\mathsf{Nat}\to\mathsf{Nat})\to\mathsf{Nat}\to\mathsf{Nat}`. The type argument Nat is well formed in the empty context. This is (b).
9. The term $`\mathit{twice}\ [\mathsf{Nat}]` has the form $`(\lambda X.t_{12})\ [T_2]` with $`t_{12}=\lambda f{:}X\to X.\lambda x{:}X.f\ (f\ x)` and $`T_2=\mathsf{Nat}`. E-TappTabs gives $`\mathit{twice}\ [\mathsf{Nat}]\to[X\mapsto\mathsf{Nat}]t_{12}`. The substitution replaces $`X` in the annotations $`X\to X` and $`X`. The body $`f\ (f\ x)` contains no type and is unchanged. So the result is $`\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\lambda x{:}\mathsf{Nat}.f\ (f\ x)`.
10. Lines 1–6 with Nat in place of $`X`, and without the binding $`X`, derive $`\vdash\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\lambda x{:}\mathsf{Nat}.f\ (f\ x):(\mathsf{Nat}\to\mathsf{Nat})\to\mathsf{Nat}\to\mathsf{Nat}`. This is the type of line 8, which proves (c). $`\square`

T-TAbs is used once, at line 7. It applies only after $`f` and $`x` have been discharged, because the premise of T-TAbs has $`X` as its last binding, and the bindings of $`f` and $`x` mention $`X`, so they lie to its right. Line 10 is an instance of Lemma 31.4 in §31.3: substituting a well-formed type for a type variable turns a derivation into a derivation.

Three variations fail. Let $`\mathit{inc}=\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x`. The term $`\mathit{twice}\ \mathit{inc}` has no type: T-App needs an operator of function type, and T-TAbs, the only rule for a type abstraction, gives $`\mathit{twice}` a universal type. The text $`\mathit{twice}\ [0]` is not a term, because only a type may stand in brackets. The term $`\mathit{twice}\ [Y]` has no type in the empty context, because $`Y` is not well formed there.

# Packages and unpacking
%%%
tag := "ch31-s2"
%%%

A universal type lets the caller choose a type. An existential type lets the implementer choose it and hide it. A *package* $`\{{*}U,t_2\}\ \mathsf{as}\ \{\exists X,T_2\}` pairs a type $`U`, its *representation type*, with a term $`t_2` of type $`[X\mapsto U]T_2`. Its type, the *existential type* $`\{\exists X,T_2\}`, records only that $`t_2` has type $`T_2` for some choice of $`X`.

The annotation after $`\mathsf{as}` decides what is hidden. The pair $`\{0,\mathsf{succ}\ 0\}` has type $`\mathsf{Nat}\times\mathsf{Nat}`. This type is $`[X\mapsto\mathsf{Nat}](X\times\mathsf{Nat})`, and also $`[X\mapsto\mathsf{Nat}](\mathsf{Nat}\times X)` and $`[X\mapsto\mathsf{Nat}](X\times X)`. So T-Pack below types three packages with the same representation type and the same pair: $`\{{*}\mathsf{Nat},\{0,\mathsf{succ}\ 0\}\}` with the annotation $`\{\exists X,X\times\mathsf{Nat}\}`, with $`\{\exists X,\mathsf{Nat}\times X\}`, or with $`\{\exists X,X\times X\}`. A client of the first may use the second component as a number, but the first only as a value of the unknown type $`X`. A client of the third learns that the two components have the same type, and nothing else.

*Unpacking* $`\mathsf{let}\ \{X,x\}=t_1\ \mathsf{in}\ t_2` evaluates $`t_1` to a package and binds both of its parts in $`t_2`: the type variable $`X` and the term variable $`x`. We call a term that unpacks a package a *client* of the package. Inside $`t_2` the type variable $`X` is the *abstract type*. The client may use it, but no rule identifies it with the representation type. The side condition $`X\notin\mathrm{FV}(T_2)` of T-Unpack is the *escape condition*: the type of the body may not mention the abstract type. The rules are:

$$`\frac{\Gamma\vdash t_2:[X\mapsto U]T_2}{\Gamma\vdash\{{*}U,t_2\}\ \mathsf{as}\ \{\exists X,T_2\}:\{\exists X,T_2\}}\;\textsf{T-Pack}\qquad\frac{\Gamma\vdash t_1:\{\exists X,T_{12}\}\quad\Gamma,X,x{:}T_{12}\vdash t_2:T_2\quad X\notin\mathrm{FV}(T_2)}{\Gamma\vdash\mathsf{let}\ \{X,x\}=t_1\ \mathsf{in}\ t_2:T_2}\;\textsf{T-Unpack}`

$$`\frac{t_{12}\to t_{12}'}{\{{*}T_{11},t_{12}\}\ \mathsf{as}\ T_1\to\{{*}T_{11},t_{12}'\}\ \mathsf{as}\ T_1}\;\textsf{E-Pack}\qquad\frac{t_1\to t_1'}{\mathsf{let}\ \{X,x\}=t_1\ \mathsf{in}\ t_2\to\mathsf{let}\ \{X,x\}=t_1'\ \mathsf{in}\ t_2}\;\textsf{E-Unpack}`

$$`\frac{}{\mathsf{let}\ \{X,x\}=(\{{*}T_{11},v_{12}\}\ \mathsf{as}\ T_1)\ \mathsf{in}\ t_2\to[X\mapsto T_{11}][x\mapsto v_{12}]t_2}\;\textsf{E-UnpackPack}`

The counter of C.7 has a start value, an increment and a read operation, written as nested pairs. Let

$$`\mathit{inc}=\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x,\qquad\mathit{read}=\lambda x{:}\mathsf{Nat}.x,\qquad v_0=\{0,\{\mathit{inc},\mathit{read}\}\},`

$$`T_{\mathrm c}=X\times((X\to X)\times(X\to\mathsf{Nat})),\qquad\mathit{Counter}=\{\exists X,T_{\mathrm c}\},\qquad\mathit{counter}=\{{*}\mathsf{Nat},v_0\}\ \mathsf{as}\ \mathit{Counter}.`

For a term $`c` of type $`T_{\mathrm c}`, the start value is $`c.1`, the increment is $`c.2.1` and the read operation is $`c.2.2`. Projections associate to the left, so $`c.2.1` is $`(c.2).1`. The representation type of $`\mathit{counter}` is Nat, and the type $`\mathit{Counter}` hides it.

*Proposition 31.2 (Unpacking the counter).* Let $`\mathit{client}=\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ c.2.2\ (c.2.1\ c.1)`.

* (a) $`\vdash\mathit{counter}:\mathit{Counter}`.
* (b) $`\vdash\mathit{client}:\mathsf{Nat}`.
* (c) $`\mathit{client}\to v_0.2.2\ (v_0.2.1\ v_0.1)` by E-UnpackPack.

*Proof (board case).* We must derive two typings and one step. For (a):

1. $`\vdash 0:\mathsf{Nat}` by T-Zero.
2. $`\vdash\mathit{inc}:\mathsf{Nat}\to\mathsf{Nat}` by T-Var, T-Succ and T-Abs, and $`\vdash\mathit{read}:\mathsf{Nat}\to\mathsf{Nat}` by T-Var and T-Abs.
3. $`\vdash\{\mathit{inc},\mathit{read}\}:(\mathsf{Nat}\to\mathsf{Nat})\times(\mathsf{Nat}\to\mathsf{Nat})` by T-Pair from 2.
4. $`\vdash v_0:\mathsf{Nat}\times((\mathsf{Nat}\to\mathsf{Nat})\times(\mathsf{Nat}\to\mathsf{Nat}))` by T-Pair from 1 and 3. This type is $`[X\mapsto\mathsf{Nat}]T_{\mathrm c}`.
5. $`\vdash\mathit{counter}:\mathit{Counter}` by T-Pack from 4, with $`U=\mathsf{Nat}` and $`T_2=T_{\mathrm c}`.

For (b), write $`\Gamma_{\mathrm c}=X,\ c{:}T_{\mathrm c}`. This context is well formed, because $`T_{\mathrm c}` mentions only $`X`.

6. $`\Gamma_{\mathrm c}\vdash c:X\times((X\to X)\times(X\to\mathsf{Nat}))` by T-Var.
7. $`\Gamma_{\mathrm c}\vdash c.1:X` by T-Proj1 from 6.
8. $`\Gamma_{\mathrm c}\vdash c.2:(X\to X)\times(X\to\mathsf{Nat})` by T-Proj2 from 6.
9. $`\Gamma_{\mathrm c}\vdash c.2.1:X\to X` by T-Proj1 from 8, and $`\Gamma_{\mathrm c}\vdash c.2.2:X\to\mathsf{Nat}` by T-Proj2 from 8.
10. $`\Gamma_{\mathrm c}\vdash c.2.1\ c.1:X` by T-App from 9 and 7.
11. $`\Gamma_{\mathrm c}\vdash c.2.2\ (c.2.1\ c.1):\mathsf{Nat}` by T-App from 9 and 10.
12. $`\vdash\mathit{client}:\mathsf{Nat}` by T-Unpack from 5 and 11, with $`T_{12}=T_{\mathrm c}` and $`T_2=\mathsf{Nat}`. The escape condition holds, since $`\mathrm{FV}(\mathsf{Nat})=\varnothing`.

For (c):

13. The term $`\mathit{client}` has the form of the left side of E-UnpackPack with $`T_{11}=\mathsf{Nat}`, $`v_{12}=v_0` and $`t_2=c.2.2\ (c.2.1\ c.1)`. The rule gives $`\mathit{client}\to[X\mapsto\mathsf{Nat}][c\mapsto v_0]t_2`. Term substitution gives $`[c\mapsto v_0]t_2=v_0.2.2\ (v_0.2.1\ v_0.1)`. This term contains no type variable, so $`[X\mapsto\mathsf{Nat}]` leaves it unchanged. $`\square`

Line 10 is where the abstract type does its work. The increment takes an $`X` and returns an $`X`, and the start value is an $`X`, so the two fit without the client knowing that $`X` is Nat. After the step the abstract type is gone. The result $`v_0.2.2\ (v_0.2.1\ v_0.1)` is an ordinary term of type Nat, and seven more steps lead to $`\mathsf{succ}\ 0` (Exercise 31.1).

Inside the body the client cannot use what the package hides. The term $`\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ \mathsf{succ}\ (c.1)` has no type. T-Succ would need $`\Gamma_{\mathrm c}\vdash c.1:\mathsf{Nat}`, but T-Var and T-Proj1 give $`c.1` only the type $`X`, and the type variable $`X` is not the type Nat. Evaluation would have no trouble: the term reaches $`\mathsf{succ}\ 0` in two steps. Typing rejects it because it relies on the representation type.

# The escape condition and the safety table
%%%
tag := "ch31-s3"
%%%

Unpacking a package gives the client a name $`X` for the representation type, valid inside the body. The escape condition keeps this name from leaving the body in the type of the result.

*Proposition 31.3 (The escape condition rejects a client).* Let $`\mathit{leak}=\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ c.1`. There is no type $`T` with $`\vdash\mathit{leak}:T`.

*Proof (board case).* We must show that no derivation $`D` of $`\vdash\mathit{leak}:T` exists, for any type $`T`. Suppose $`D` is such a derivation.

1. The only typing rule whose conclusion is an unpacking is T-Unpack. So $`D` ends with T-Unpack, and its premises give a type $`T_{12}` with $`\vdash\mathit{counter}:\{\exists X,T_{12}\}` and $`X,\ c{:}T_{12}\vdash c.1:T`, and the escape condition $`X\notin\mathrm{FV}(T)`.
2. The only typing rule whose conclusion is a package is T-Pack, and it gives the package the type written after $`\mathsf{as}`. So $`\{\exists X,T_{12}\}=\mathit{Counter}`, and $`T_{12}=T_{\mathrm c}`. The second premise of step 1 is therefore $`\Gamma_{\mathrm c}\vdash c.1:T`.
3. The only typing rule whose conclusion is a first projection is T-Proj1. So $`\Gamma_{\mathrm c}\vdash c:T\times S` for some type $`S`.
4. The only typing rule whose conclusion is a variable is T-Var. So $`c{:}T\times S\in\Gamma_{\mathrm c}`. The only binding of $`c` in $`\Gamma_{\mathrm c}` is $`c{:}X\times((X\to X)\times(X\to\mathsf{Nat}))`. Comparing first components gives $`T=X`.
5. Then $`\mathrm{FV}(T)=\{X\}`, and the escape condition of step 1 fails. So $`D` does not exist. $`\square`

Renaming the bound type variable does not help. For $`\mathsf{let}\ \{Y,c\}=\mathit{counter}\ \mathsf{in}\ c.1`, step 4 gives $`T=Y`, and $`Y\notin\mathrm{FV}(Y)` fails again. Evaluation alone notices nothing: $`\mathit{leak}\to v_0.1\to 0` by E-UnpackPack and E-PairBeta1.

Without the escape condition, typing would accept terms that get stuck. Let $`\mathit{not}=\lambda b{:}\mathsf{Bool}.\mathsf{if}\ b\ \mathsf{then}\ \mathsf{false}\ \mathsf{else}\ \mathsf{true}`, and take two packages of the same existential type:

$$`p_{\mathsf N}=\{{*}\mathsf{Nat},\{0,\mathit{inc}\}\}\ \mathsf{as}\ \{\exists X,X\times(X\to X)\},\qquad p_{\mathsf B}=\{{*}\mathsf{Bool},\{\mathsf{true},\mathit{not}\}\}\ \mathsf{as}\ \{\exists X,X\times(X\to X)\}.`

Drop the escape condition from T-Unpack. Then $`\mathsf{let}\ \{X,d\}=p_{\mathsf B}\ \mathsf{in}\ d.2` gets the type $`X\to X`, and $`\mathsf{let}\ \{X,c\}=p_{\mathsf N}\ \mathsf{in}\ c.1` gets the type $`X`. T-App accepts the first applied to the second, at type $`X`. Four steps, by E-UnpackPack and a pair rule for each operand, lead to $`\mathit{not}\ 0`. E-AppAbs then gives $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{false}\ \mathsf{else}\ \mathsf{true}`, which is stuck (C.2). The two occurrences of $`X` are two abstract types that share a name. Inside its own body each stands for its own representation type, and outside the bodies nothing tells them apart. The type $`X` of the application is not even well formed in the empty context.

*The safety table.* The steps of Propositions 31.1 and 31.2 kept the type. In line 10 of Proposition 31.1, the derivation of the result came from the derivation of the body by putting Nat in place of $`X`. The next lemma does this in general. It carries the store typing $`\Sigma` of [C.6](lambda-card/index.html#lambda-c6), since the typed language of this session includes references.

*Lemma 31.4 (Type substitution).* For all contexts $`\Gamma`, sequences of bindings $`\Delta`, store typings $`\Sigma`, terms $`t`, types $`S,T` and type variables $`X`: if $`\Gamma,X,\Delta\mid\Sigma\vdash t:T` and $`S` is well formed in $`\Gamma`, then $`\Gamma,[X\mapsto S]\Delta\mid\Sigma\vdash[X\mapsto S]t:[X\mapsto S]T`. Here $`[X\mapsto S]\Delta` substitutes in the types of $`\Delta`.

In line 10 of Proposition 31.1, $`\Gamma` and $`\Delta` are empty, $`\Sigma=\varnothing`, $`S=\mathsf{Nat}`, and the premise is line 6. In an unpacking, $`\Delta` is the binding $`x{:}T_{12}` of the package’s term variable.

*Theorem 31.5 (Row 6 · Universal and existential types).* The entries are read as in [C.8](lambda-card/index.html#lambda-c8). This session states them without proof.

* *Canonical forms.* If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\forall X.T_{12}`, then $`v=\lambda X.t_{12}` for some $`t_{12}`. If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\{\exists X,T_{12}\}`, then $`v=\{{*}T_{11},v_{12}\}\ \mathsf{as}\ \{\exists X,T_{12}\}` for a type $`T_{11}` and a value $`v_{12}`.
* *Progress.* T-TAbs: the term is a value. T-TApp: steps by E-TApp or E-TappTabs. T-Pack: the term is a value or steps by E-Pack. T-Unpack: steps by E-Unpack or E-UnpackPack.
* *Preservation.* E-TappTabs: $`\Sigma'=\Sigma`, using Lemma 31.4. E-UnpackPack: $`\Sigma'=\Sigma`, using the substitution lemma (C.8, Row 2), Lemma 31.4 and the escape condition, which gives $`[X\mapsto T_{11}]T_2=T_2`. E-TApp, E-Pack, E-Unpack: premise.

As in C.8, “premise” means that the case applies the induction hypothesis to the evaluation premise, takes the store typing $`\Sigma'` that it gives, and rebuilds the typing with the same rule. In the case E-UnpackPack, Lemma 31.4 types the result at $`[X\mapsto T_{11}]T_2`. Only the escape condition makes this the type $`T_2` of the unpacking. For $`\mathit{leak}` without the condition, $`T_2` would be $`X`, while the result $`v_0.1` has type Nat. Preservation would fail at the first step.

Row 6 adds two forms of value, type abstractions and packages. As C.8 requires, each earlier canonical-forms statement gains two exclusion cases. For example, no type abstraction has type Nat, because T-TAbs gives it a universal type, and no package has a function type, because T-Pack gives it an existential type.

# Exercises
%%%
tag := "ch31-s4"
number := false
%%%

*31.1.* (a) Evaluate $`\mathit{twice}\ [\mathsf{Nat}]\ \mathit{inc}\ 0` to a value. (b) Continue the evaluation of $`\mathit{client}` from $`v_0.2.2\ (v_0.2.1\ v_0.1)` to a value. For each step, name the computation rule and the congruence rules that lift it.

*31.2.* Let $`U=\forall X.X\to X`. Derive $`\vdash\mathit{id}\ [U]\ \mathit{id}:U` and evaluate the term. Which type replaces $`X` in the step by E-TappTabs?

*31.3.* Let $`\mathit{both}=\lambda k{:}(\forall X.X\to X).\{k\ [\mathsf{Nat}]\ 0,\ k\ [\mathsf{Bool}]\ \mathsf{true}\}`. Derive its type and evaluate $`\mathit{both}\ \mathit{id}`. Why does the unannotated term $`\lambda k.\{k\ 0,\ k\ \mathsf{true}\}` have no type by the rules of [C.5](lambda-card/index.html#lambda-c5)?

*31.4.* For each body $`t_2` below, give its type under $`\Gamma_{\mathrm c}` and decide whether $`\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ t_2` has a type. (a) $`c.2.1\ c.1`. (b) $`c.2.2\ c.1`. (c) $`\lambda u{:}\mathsf{Unit}.c.2.2\ (c.2.1\ c.1)`. (d) $`\lambda u{:}\mathsf{Unit}.c.2.1\ c.1`.

*31.5.* Show that $`\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ \mathsf{let}\ \{Y,d\}=\mathit{counter}\ \mathsf{in}\ d.2.2\ (c.2.1\ d.1)` has no type, although both packages are the same. Does its evaluation get stuck?

*Further problem.* Let $`\mathit{next}=\mathsf{let}\ \{X,c\}=\mathit{counter}\ \mathsf{in}\ \{{*}X,\{c.2.1\ c.1,\ c.2\}\}\ \mathsf{as}\ \mathit{Counter}`. Show $`\vdash\mathit{next}:\mathit{Counter}`, and check the escape condition. Evaluate $`\mathit{next}` to a value, and name the type written in the term that changes in the step by E-UnpackPack. What does $`\mathsf{let}\ \{X,c\}=\mathit{next}\ \mathsf{in}\ c.2.2\ c.1` evaluate to?

# Reading for the Seminar
%%%
tag := "ch31-s5"
number := false
%%%

*Definitions · 10 minutes.* Write T-TAbs, T-TApp, E-TappTabs, T-Pack, T-Unpack and E-UnpackPack. Mark the binders in $`\mathit{twice}` and in $`\mathit{client}`, and say which binder each of the two steps removes.

*Joint proof · 30 minutes.* Do the three board computations. For Proposition 31.1, write lines 1–8 and the step. For Proposition 31.2, write lines 1–12 and the step. For Proposition 31.3, write the five inversion steps. After each step, write the type of the result.

*Proof review · 20 minutes.* Do Exercise 31.4. Then drop the escape condition and run the application of §31.3 to the stuck term. Read Theorem 31.5 aloud, and match its preservation entries for E-TappTabs and E-UnpackPack with the steps of Propositions 31.1 and 31.2.

*Facilitator’s hint.* Keep two columns on the board: the type that the implementer chose (Nat) and the type that the client may assume ($`X`). A type application lets the caller choose. A package lets the implementer choose.

# Solutions and Further Reading
%%%
tag := "ch31-s6"
number := false
%%%

*31.1.* (a) There are five steps. Every term on the path has type Nat.

1. $`\mathit{twice}\ [\mathsf{Nat}]\to\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\lambda x{:}\mathsf{Nat}.f\ (f\ x)` by E-TappTabs, lifted by E-App1 twice.
2. $`(\lambda f{:}\mathsf{Nat}\to\mathsf{Nat}.\lambda x{:}\mathsf{Nat}.f\ (f\ x))\ \mathit{inc}\to\lambda x{:}\mathsf{Nat}.\mathit{inc}\ (\mathit{inc}\ x)` by E-AppAbs, lifted by E-App1.
3. $`(\lambda x{:}\mathsf{Nat}.\mathit{inc}\ (\mathit{inc}\ x))\ 0\to\mathit{inc}\ (\mathit{inc}\ 0)` by E-AppAbs.
4. $`\mathit{inc}\ 0\to\mathsf{succ}\ 0` by E-AppAbs, lifted by E-App2. The term is $`\mathit{inc}\ (\mathsf{succ}\ 0)`.
5. $`\mathit{inc}\ (\mathsf{succ}\ 0)\to\mathsf{succ}\ (\mathsf{succ}\ 0)` by E-AppAbs.

(b) Write $`w=\{\mathit{inc},\mathit{read}\}`, so that $`v_0=\{0,w\}`. There are seven steps, and every term has type Nat.

1. $`v_0.2\to w` by E-PairBeta2, lifted by E-Proj2 and E-App1. The term is $`w.2\ (v_0.2.1\ v_0.1)`.
2. $`w.2\to\mathit{read}` by E-PairBeta2, lifted by E-App1. The term is $`\mathit{read}\ (v_0.2.1\ v_0.1)`.
3. $`v_0.2\to w` by E-PairBeta2, lifted by E-Proj1, E-App1 and E-App2. The term is $`\mathit{read}\ (w.1\ v_0.1)`.
4. $`w.1\to\mathit{inc}` by E-PairBeta1, lifted by E-App1 and E-App2. The term is $`\mathit{read}\ (\mathit{inc}\ v_0.1)`.
5. $`v_0.1\to 0` by E-PairBeta1, lifted by E-App2 twice. The term is $`\mathit{read}\ (\mathit{inc}\ 0)`.
6. $`\mathit{inc}\ 0\to\mathsf{succ}\ 0` by E-AppAbs, lifted by E-App2. The term is $`\mathit{read}\ (\mathsf{succ}\ 0)`.
7. $`\mathit{read}\ (\mathsf{succ}\ 0)\to\mathsf{succ}\ 0` by E-AppAbs.

*31.2.* §31.1 gives $`\vdash\mathit{id}:U`. Since $`[X\mapsto U](X\to X)=U\to U`, T-TApp gives $`\vdash\mathit{id}\ [U]:U\to U`, and T-App with $`\vdash\mathit{id}:U` gives $`\vdash\mathit{id}\ [U]\ \mathit{id}:U`. The term steps to $`(\lambda x{:}U.x)\ \mathit{id}` by E-TappTabs, lifted by E-App1. The universal type $`U` replaces $`X`. E-AppAbs then gives $`\mathit{id}`, a value of type $`U`. A type argument may itself be a universal type.

*31.3.* Under $`k{:}\forall X.X\to X`, T-Var and T-TApp give $`k\ [\mathsf{Nat}]:\mathsf{Nat}\to\mathsf{Nat}` and $`k\ [\mathsf{Bool}]:\mathsf{Bool}\to\mathsf{Bool}`. T-App types the two components at Nat and Bool, T-Pair gives $`\mathsf{Nat}\times\mathsf{Bool}`, and T-Abs gives $`\vdash\mathit{both}:(\forall X.X\to X)\to\mathsf{Nat}\times\mathsf{Bool}`. E-AppAbs gives $`\mathit{both}\ \mathit{id}\to\{\mathit{id}\ [\mathsf{Nat}]\ 0,\ \mathit{id}\ [\mathsf{Bool}]\ \mathsf{true}\}`. The first component takes the two steps of §31.1 under E-Pair1, the second takes two steps under E-Pair2, and the value is $`\{0,\mathsf{true}\}`. In C.5 a parameter $`k` receives one type $`T_1`, a scheme with no quantified variables. T-App on $`k\ 0` and on $`k\ \mathsf{true}` needs $`T_1=\mathsf{Nat}\to S_1` and $`T_1=\mathsf{Bool}\to S_2` for some $`S_1,S_2`, which forces $`\mathsf{Nat}=\mathsf{Bool}`. Only a let-bound variable receives a scheme with quantified variables.

*31.4.* (a) $`X`. Rejected by the escape condition. (b) Nat. Accepted, and the term evaluates to $`0`. (c) $`\mathsf{Unit}\to\mathsf{Nat}`. Accepted, since $`X\notin\mathrm{FV}(\mathsf{Unit}\to\mathsf{Nat})`. E-UnpackPack gives the value $`\lambda u{:}\mathsf{Unit}.v_0.2.2\ (v_0.2.1\ v_0.1)`, which carries the operations of the package in its body. Applied to $`\mathsf{unit}`, it evaluates to $`\mathsf{succ}\ 0`. (d) $`\mathsf{Unit}\to X`. Rejected: the abstract type occurs inside a larger type, and the escape condition excludes every free occurrence.

*31.5.* The inner unpacking types $`d` as $`Y\times((Y\to Y)\times(Y\to\mathsf{Nat}))`, the body of $`\mathit{Counter}` with its bound variable renamed to $`Y`. So $`d.1:Y`, while $`c.2.1:X\to X`. T-App needs the type of the argument to equal the domain, and $`Y` is not $`X`. No rule identifies the two abstract types, although both come from the same package. The evaluation does not get stuck. Two steps by E-UnpackPack give $`v_0.2.2\ (v_0.2.1\ v_0.1)`, and Exercise 31.1(b) continues to $`\mathsf{succ}\ 0`. Typing rejects some terms that run safely.

*Further problem.* Lines 10 and 8 of Proposition 31.2 and T-Pair give $`\Gamma_{\mathrm c}\vdash\{c.2.1\ c.1,\ c.2\}:T_{\mathrm c}`. Rename the bound variable of $`\mathit{Counter}` to $`Y`, so $`\mathit{Counter}=\{\exists Y,[X\mapsto Y]T_{\mathrm c}\}` and $`[Y\mapsto X]([X\mapsto Y]T_{\mathrm c})=T_{\mathrm c}`. T-Pack with the representation type $`X`, which is well formed in $`\Gamma_{\mathrm c}`, gives the package the type $`\mathit{Counter}`. T-Unpack then gives $`\vdash\mathit{next}:\mathit{Counter}`. The escape condition holds, because $`\mathit{Counter}` has no free type variable. E-UnpackPack gives $`\{{*}\mathsf{Nat},\{v_0.2.1\ v_0.1,\ v_0.2\}\}\ \mathsf{as}\ \mathit{Counter}`: the substitution $`[X\mapsto\mathsf{Nat}]` changes the representation type $`X` to Nat. E-Pack then lifts five steps, four in the first component and one in the second, and the value is $`\{{*}\mathsf{Nat},\{\mathsf{succ}\ 0,w\}\}\ \mathsf{as}\ \mathit{Counter}`. The term $`\mathsf{let}\ \{X,c\}=\mathit{next}\ \mathsf{in}\ c.2.2\ c.1` evaluates to $`\mathsf{succ}\ 0`: the new package starts where the old counter stood after one increment. The escape condition does not forbid returning a counter. It forbids a result type that mentions $`X`, and a new package gives the counter the closed type $`\mathit{Counter}`.

*Further reading · Proof of Lemma 31.4.* Fix $`\Gamma`, $`X` and $`S` with $`S` well formed in $`\Gamma`. The proof is by induction on a derivation $`D` of $`\Gamma_D\mid\Sigma\vdash t:T`, with

$$`P(D)\coloneqq\forall\Delta,\ \bigl(\Gamma_D=\Gamma,X,\Delta\bigr)\Rightarrow\bigl(\Gamma,[X\mapsto S]\Delta\mid\Sigma\vdash[X\mapsto S]t:[X\mapsto S]T\bigr),`

where $`\Gamma_D`, $`\Sigma`, $`t` and $`T` are read from the conclusion of $`D`. The sequence $`\Delta` is quantified inside $`P(D)`, because the premises of T-Abs, T-TAbs, T-Unpack, T-Case and T-Let extend the context. In the case T-Var with $`x{:}T\in\Gamma`, the type $`T` is well formed in a part of $`\Gamma`, which does not bind $`X`, so $`[X\mapsto S]T=T`. With $`x{:}T\in\Delta`, the binding $`x{:}[X\mapsto S]T` lies in $`[X\mapsto S]\Delta`. In T-Loc the type comes from $`\Sigma`, whose types are closed. In T-TAbs and T-Unpack the bound type variable $`Y` is renamed so that $`Y\neq X` and $`Y\notin\mathrm{FV}(S)`. The hypothesis then applies with $`\Delta,Y` (and $`\Delta,Y,x{:}T_{12}` for T-Unpack), and the condition $`Y\notin\mathrm{FV}(T_2)` survives the substitution. T-TApp and T-Pack use the equation $`[X\mapsto S]([Y\mapsto T_2]T_{12})=[Y\mapsto[X\mapsto S]T_2]([X\mapsto S]T_{12})` for $`Y\neq X` and $`Y\notin\mathrm{FV}(S)`, proved by structural induction on $`T_{12}`. Every other case applies the hypothesis to each premise and reuses the rule.

*Further reading · Church encodings.* System F can define Booleans and numbers from functions and type abstraction alone (TAPL §23.4). The values $`\lambda X.\lambda x{:}X.\lambda y{:}X.x` and $`\lambda X.\lambda x{:}X.\lambda y{:}X.y` of type $`\forall X.X\to X\to X` select the first or the second of two arguments and play the roles of true and false. The type $`\mathit{CNat}=\forall X.(X\to X)\to X\to X` encodes numbers: the number $`n` is $`\lambda X.\lambda f{:}X\to X.\lambda x{:}X.f\ (\cdots(f\ x))` with $`n` applications of $`f`. So $`\mathit{twice}` encodes 2, and Exercise 31.1(a) converts it to the numeric value $`\mathsf{succ}\ (\mathsf{succ}\ 0)`. The successor is $`\lambda n{:}\mathit{CNat}.\lambda X.\lambda f{:}X\to X.\lambda x{:}X.f\ (n\ [X]\ f\ x)`.

*Further reading · Two implementations.* Two packages of type $`\mathit{Counter}` may use different representation types. [Session 33](chapter-33/index.html) asks when no client can tell two such packages apart. TAPL §24.2 develops abstract data types with existential types, using records.

# Sources and Formalization
%%%
tag := "ch31-notes"
number := false
%%%

* *Proposition 31.1.* Formulated in this book. Paper proof only ([§31.1](chapter-31/index.html#ch31-s1)).
* *Proposition 31.2.* Formulated in this book. Paper proof only ([§31.2](chapter-31/index.html#ch31-s2)).
* *Proposition 31.3.* Formulated in this book. Paper proof only ([§31.3](chapter-31/index.html#ch31-s3)).
* *Lemma 31.4.* Formulated in this book. Paper proof only ([Solutions and Further Reading](chapter-31/index.html#ch31-s6)).
* *Theorem 31.5.* Corresponds to TAPL §§23.5, 24.1. Paper proof only (TAPL §§23.5, 24.1; no proof in this book).
