import VersoManual

open Verso.Genre Manual

#doc (Manual) "Weakening and Typed Substitution" =>
%%%
tag := "ch25"
file := "chapter-25"
%%%

* *Definitions.* Free variables, alpha-equivalence and capture-avoiding substitution ([C.1](lambda-card/index.html#lambda-c1), extended to annotated abstractions and constants in [C.3](lambda-card/index.html#lambda-c3)). The typing rules of [C.2](lambda-card/index.html#lambda-c2). Typing contexts, $`\mathrm{dom}(\Gamma)`, the extension $`\Gamma,x{:}T` and the rules T-Var, T-Abs, T-App and T-Unit ([C.3](lambda-card/index.html#lambda-c3)). Derivations ([A.3](imp-card/index.html#imp-a3)), side conditions ([A.5](imp-card/index.html#imp-a5)), induction on derivations ([Session 1, §1.5](chapter-01/index.html#ch01-s5)), the height of a derivation ([Session 2, §2.4](chapter-02/index.html#ch02-s4)) and induction on height ([Session 3, §3.1](chapter-03/index.html#ch03-s1)).
* *New terms.* Typing context, permutation of a context, weakening, substitution lemma. [Glossary and label key](glossary/index.html)
* *Theorem 25.5 \[Paper proof only: proof in §25.3\].* For all contexts $`\Gamma`, variables $`x`, terms $`s,t` and types $`S,T`: if $`\Gamma,x{:}S\vdash t:T` and $`\Gamma\vdash s:S`, then $`\Gamma\vdash[x\mapsto s]t:T`.
* *Source.* Pierce, _Types and Programming Languages_ (TAPL), §9.3: permutation (Lemma 25.2), weakening (Lemma 25.4) and the preservation of types under substitution (Theorem 25.5) for the simply typed lambda calculus. The proofs here follow the same plan and cover every rule of C.2 and C.3. \[This book\] Lemmas 25.1 and 25.3 make the convention on bound variables of C.1 precise for derivations. [Card source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)
* *Board case.* The abstraction case of Theorem 25.5, in six numbered steps (§25.3). The context of the premise shows that the parameter $`y` is new. Lemma 25.1 lets substitution pass under the binder. Permutation moves $`x{:}S` to the end of the premise's context. Weakening adds $`y{:}T_1` to the derivation of $`s`. The induction hypothesis applies to the permuted premise, and T-Abs closes the case.
* *Proof outline.* Fix $`x,S,s`. Induction on the height of a derivation $`D` of $`\Gamma,x{:}S\vdash t:T`, with $`P(D)\coloneqq(\Gamma\vdash s:S)\Rightarrow(\Gamma\vdash[x\mapsto s]t:T)`, where $`\Gamma,t,T` are read from the conclusion of $`D`. The variable case uses $`\Gamma\vdash s:S` or T-Var. The other cases without a binder rebuild the last rule from the induction hypotheses. In the abstraction case the premise's context ends with the parameter's binding, not with $`x{:}S`. Permutation reorders it without changing the height, so the induction hypothesis is applied to a derivation that is not a subderivation of $`D`. This is why the induction is on height.
* *From Session 24.* Session 24 typed terms without variables, and its rules never inspected the context. Here T-Var reads the type of a variable from the context, and T-Abs extends the context. Session 26 uses Theorem 25.5 for the preservation case of E-AppAbs, which replaces a parameter by an argument ([C.8](lambda-card/index.html#lambda-c8), Row 2).

Let $`\Gamma` be the context $`n{:}\mathsf{Nat}`. Under the extra binding $`x{:}\mathsf{Nat}`, the term $`\lambda z{:}\mathsf{Bool}.\,\mathsf{if}\ z\ \mathsf{then}\ x\ \mathsf{else}\ 0` has type $`\mathsf{Bool}\to\mathsf{Nat}`. Under $`\Gamma` alone, $`\mathsf{succ}\ n` has type $`\mathsf{Nat}`. Replace $`x` by $`\mathsf{succ}\ n`. Does $`\lambda z{:}\mathsf{Bool}.\,\mathsf{if}\ z\ \mathsf{then}\ \mathsf{succ}\ n\ \mathsf{else}\ 0` have type $`\mathsf{Bool}\to\mathsf{Nat}` under $`\Gamma`? Its derivation must type $`\mathsf{succ}\ n` under $`n{:}\mathsf{Nat},z{:}\mathsf{Bool}`, a context with a binding that the given derivation of $`\mathsf{succ}\ n` never saw. This session proves that the answer is always yes.

# Contexts and derivations
%%%
tag := "ch25-s1"
%%%

The typing judgment $`\Gamma\vdash t:T` holds when it has a finite derivation by the rules of C.2 and C.3. It is a relation between contexts, terms and types, defined separately from the syntax of terms. A *typing context* $`\Gamma` is a finite sequence of bindings $`x{:}T` (C.3). The extension $`\Gamma,x{:}T` is formed only when $`x\notin\mathrm{dom}(\Gamma)`, so each variable is bound at most once in a context.

Let $`\Gamma_2` be the context $`n{:}\mathsf{Nat},x{:}\mathsf{Nat},z{:}\mathsf{Bool}`. The derivation $`E_2` types the body of the opening example. Its leaves are instances of T-Var, T-Var and T-Zero.

$$`E_2:\quad\frac{\dfrac{z{:}\mathsf{Bool}\in\Gamma_2}{\Gamma_2\vdash z:\mathsf{Bool}}\,\textsf{T-Var}\qquad\dfrac{x{:}\mathsf{Nat}\in\Gamma_2}{\Gamma_2\vdash x:\mathsf{Nat}}\,\textsf{T-Var}\qquad\dfrac{}{\Gamma_2\vdash 0:\mathsf{Nat}}\,\textsf{T-Zero}}{\Gamma_2\vdash\mathsf{if}\ z\ \mathsf{then}\ x\ \mathsf{else}\ 0:\mathsf{Nat}}\;\textsf{T-If}`

The derivation $`E` adds one T-Abs node below $`E_2`:

$$`E:\quad\frac{\Gamma_2\vdash\mathsf{if}\ z\ \mathsf{then}\ x\ \mathsf{else}\ 0:\mathsf{Nat}}{n{:}\mathsf{Nat},x{:}\mathsf{Nat}\vdash\lambda z{:}\mathsf{Bool}.\,\mathsf{if}\ z\ \mathsf{then}\ x\ \mathsf{else}\ 0:\mathsf{Bool}\to\mathsf{Nat}}\;\textsf{T-Abs}`

Read $`E` from the root upwards. T-Abs moves the binding $`z{:}\mathsf{Bool}` from the term into the context of its premise, so all three leaves share $`\Gamma_2`. The leaf for $`z` looks up $`z{:}\mathsf{Bool}`, the leaf for $`x` looks up $`x{:}\mathsf{Nat}`, and no leaf looks up $`n{:}\mathsf{Nat}`. So a typing judgment does not say that every variable of its context occurs in the term. It says that the context supplies the type of every variable that the derivation looks up. Adding a binding for a new variable keeps every lookup. This is weakening (§25.2). Deleting $`x{:}\mathsf{Nat}` destroys the leaf for $`x`. Substitution (§25.3) must replace that leaf by a derivation for the argument.

The premise $`x{:}T\in\Gamma` of T-Var is a side condition (A.5). It is checked, not derived, so a T-Var node is a leaf. The *height* $`h(D)` of a typing derivation $`D` is defined as in Session 2, §2.4: zero when its last rule has no typing premise, and otherwise one plus the greatest height of an immediate subderivation. In $`E_2` the three leaves have height 0 and the root has height 1. The derivation $`E` has height 2.

In $`E`, the free variables $`z` and $`x` of the body lie in $`\mathrm{dom}(\Gamma_2)=\{n,x,z\}`. The only free variable $`x` of the term at the root lies in $`\mathrm{dom}(n{:}\mathsf{Nat},x{:}\mathsf{Nat})=\{n,x\}`.

*Lemma 25.1 (Free variables lie in the context) \[This book\] \[Paper proof only: proof in this section\].* For every context $`\Gamma`, term $`t` and type $`T`, if $`\Gamma\vdash t:T` then $`\mathrm{FV}(t)\subseteq\mathrm{dom}(\Gamma)`.

*Proof.* Induction on a derivation $`D` of $`\Gamma\vdash t:T`, with $`F(D)\coloneqq\mathrm{FV}(t)\subseteq\mathrm{dom}(\Gamma)`. If $`D` ends with T-Var, then $`t=x` with $`x{:}T\in\Gamma`, so $`\mathrm{FV}(t)=\{x\}\subseteq\mathrm{dom}(\Gamma)`. The constants have no free variables. For T-If, T-Succ, T-Pred, T-IsZero and T-App, every premise has the context $`\Gamma`, and $`\mathrm{FV}(t)` is the union of the free variables of the immediate subterms, so the induction hypotheses give $`F(D)`. If $`D` ends with T-Abs, then $`t=\lambda y{:}T_1.t_2` and the premise $`D_2` derives $`\Gamma,y{:}T_1\vdash t_2:T_2`. Its induction hypothesis is $`F(D_2):\ \mathrm{FV}(t_2)\subseteq\mathrm{dom}(\Gamma)\cup\{y\}`. Hence $`\mathrm{FV}(t)=\mathrm{FV}(t_2)\setminus\{y\}\subseteq\mathrm{dom}(\Gamma)`. $`\square`

With $`\Gamma` empty, Lemma 25.1 says that a term $`t` with $`\vdash t:T` is closed. C.8 uses this remark for progress.

# Permutation and weakening
%%%
tag := "ch25-s2"
%%%

The bindings of $`\Gamma_2` can be listed in another order, for instance $`n{:}\mathsf{Nat},z{:}\mathsf{Bool},x{:}\mathsf{Nat}`. Each leaf of $`E_2` still finds its binding, so the same three rules and T-If derive the same judgment over the reordered context. A context $`\Delta` is a *permutation* of $`\Gamma` if $`\Delta` and $`\Gamma` consist of the same bindings, possibly in a different order. Then $`\mathrm{dom}(\Delta)=\mathrm{dom}(\Gamma)`.

*Lemma 25.2 (Permutation) \[Paper proof only: proof in this section\].* If $`\Gamma\vdash t:T` and $`\Delta` is a permutation of $`\Gamma`, then $`\Delta\vdash t:T` by a derivation of the same height.

*Proof.* Induction on a derivation $`D` of $`\Gamma\vdash t:T`, with

$$`Q(D)\coloneqq\forall\Delta,\ \Delta\text{ is a permutation of }\Gamma\ \Rightarrow\ \Delta\vdash t:T\text{ by a derivation of height }h(D).`

The permutation is quantified inside $`Q(D)`, because the premise of T-Abs has a longer context. T-Var: $`x{:}T\in\Gamma` gives $`x{:}T\in\Delta`. The axioms of C.2 and T-Unit do not inspect the context. For T-If, T-Succ, T-Pred, T-IsZero and T-App, apply the induction hypothesis of each premise at the same $`\Delta` and use the same rule. T-Abs: the premise $`D_2` derives $`\Gamma,y{:}T_1\vdash t_2:T_2`. Since $`y\notin\mathrm{dom}(\Gamma)=\mathrm{dom}(\Delta)`, the context $`\Delta,y{:}T_1` is formed, and it is a permutation of $`\Gamma,y{:}T_1`. So $`Q(D_2)` gives $`\Delta,y{:}T_1\vdash t_2:T_2` by a derivation of height $`h(D_2)`, and T-Abs gives $`\Delta\vdash t:T`. Each new derivation uses the rule of $`D` at its root, above premises of the same heights, so its height is $`h(D)`. $`\square`

Weakening adds a binding $`y{:}U` to every context of a derivation. This fails at a T-Abs node whose parameter is $`y`. Take $`\vdash\lambda y{:}\mathsf{Nat}.\,y:\mathsf{Nat}\to\mathsf{Nat}`, derived by T-Var and T-Abs, and add $`y{:}\mathsf{Bool}`. The premise would need the context $`y{:}\mathsf{Bool},y{:}\mathsf{Nat}`, which is not formed. The same term is written $`\lambda w{:}\mathsf{Nat}.\,w` (C.1), and its derivation has the premise $`y{:}\mathsf{Bool},w{:}\mathsf{Nat}\vdash w:\mathsf{Nat}`. The next lemma performs this renaming in any derivation.

*Lemma 25.3 (Renaming the parameter) \[This book\] \[Paper proof only: proof in this section\].* Let $`D` derive $`\Gamma\vdash t:T` and end with T-Abs, and let $`V` be a finite set of variables. Then $`\Gamma\vdash t:T` has a derivation of height $`h(D)` that ends with T-Abs and whose parameter is not in $`V`.

*Proof.* Let $`t=\lambda w{:}T_1.t_2`, and let $`D_2` derive the premise $`\Gamma,w{:}T_1\vdash t_2:T_2`. Choose a variable $`z\notin V` that occurs nowhere in $`D`. Replace $`w` by $`z` at every occurrence in every judgment of $`D_2`. Because $`z` is new, distinct variables stay distinct. So, by induction on $`D_2`, every side condition $`x{:}T\in\Delta` and every extension remains valid, and every node becomes an instance of the same rule. The context $`\Gamma` does not change, since $`w\notin\mathrm{dom}(\Gamma)`. The result derives $`\Gamma,z{:}T_1\vdash t_2':T_2` with height $`h(D_2)`, where $`t_2'` is $`t_2` with $`w` replaced by $`z`. No abstraction inside $`t_2` has the parameter $`w`, because $`D_2` types each of them under a context that already binds $`w`. So $`t_2'=[w\mapsto z]t_2`, and $`\lambda z{:}T_1.t_2'` is alpha-equivalent to $`\lambda w{:}T_1.t_2`, hence equal to $`t` (C.1). T-Abs completes the derivation. $`\square`

For example, $`n{:}\mathsf{Nat}\vdash\mathsf{succ}\ n:\mathsf{Nat}` has a derivation of height 1, by T-Var and T-Succ. Adding $`z{:}\mathsf{Bool}` to both contexts gives a derivation of $`n{:}\mathsf{Nat},z{:}\mathsf{Bool}\vdash\mathsf{succ}\ n:\mathsf{Nat}`, again of height 1.

*Lemma 25.4 (Weakening) \[Paper proof only: proof in this section\].* If $`\Gamma\vdash t:T` and $`y\notin\mathrm{dom}(\Gamma)`, then $`\Gamma,y{:}U\vdash t:T` for every type $`U`, by a derivation of the same height.

*Proof.* Induction on height. For a derivation $`D` of $`\Gamma\vdash t:T` let

$$`W(D)\coloneqq\forall y,U,\ y\notin\mathrm{dom}(\Gamma)\ \Rightarrow\ \Gamma,y{:}U\vdash t:T\text{ by a derivation of height }h(D).`

Let $`D` have height $`h`, and assume $`W(D')` for every derivation $`D'` of height less than $`h`. T-Var: $`x{:}T\in\Gamma` gives $`x{:}T\in(\Gamma,y{:}U)`. The axioms of C.2 and T-Unit: the same axiom. T-If, T-Succ, T-Pred, T-IsZero and T-App: apply $`W` to each premise and use the same rule. T-Abs: by Lemma 25.3 with $`V=\{y\}`, the judgment $`\Gamma\vdash t:T` has a derivation of height $`h` that ends with T-Abs and whose parameter $`z` differs from $`y`. Then $`t=\lambda z{:}T_1.t_2`, and the premise $`D_2'` of that derivation derives $`\Gamma,z{:}T_1\vdash t_2:T_2` with height $`h-1`. Since $`y\notin\mathrm{dom}(\Gamma,z{:}T_1)`, $`W(D_2')` gives $`\Gamma,z{:}T_1,y{:}U\vdash t_2:T_2` with height $`h-1`. The context $`\Gamma,y{:}U,z{:}T_1` is formed, since $`z\notin\mathrm{dom}(\Gamma)` and $`z\neq y`. Lemma 25.2 reorders to it with height $`h-1`, and T-Abs gives $`\Gamma,y{:}U\vdash t:T` with height $`h`. $`\square`

Here $`D_2'` is the premise of the renamed derivation, not necessarily a subderivation of $`D`. Its height is $`h-1`, so induction on height covers it. Induction on derivations as in Session 1, §1.5 gives hypotheses only for the immediate subderivations of $`D`.

# Substitution preserves typing
%%%
tag := "ch25-s3"
%%%

Return to the opening example: $`\Gamma=n{:}\mathsf{Nat}`, $`S=\mathsf{Nat}`, $`s=\mathsf{succ}\ n` and $`t=\lambda z{:}\mathsf{Bool}.\,\mathsf{if}\ z\ \mathsf{then}\ x\ \mathsf{else}\ 0`. By the equations of C.1 and C.3, $`[x\mapsto s]t=\lambda z{:}\mathsf{Bool}.\,\mathsf{if}\ z\ \mathsf{then}\ \mathsf{succ}\ n\ \mathsf{else}\ 0`. With $`\Gamma_3=n{:}\mathsf{Nat},z{:}\mathsf{Bool}`, its body has the following derivation.

$$`\frac{\dfrac{z{:}\mathsf{Bool}\in\Gamma_3}{\Gamma_3\vdash z:\mathsf{Bool}}\,\textsf{T-Var}\qquad\dfrac{\dfrac{n{:}\mathsf{Nat}\in\Gamma_3}{\Gamma_3\vdash n:\mathsf{Nat}}\,\textsf{T-Var}}{\Gamma_3\vdash\mathsf{succ}\ n:\mathsf{Nat}}\,\textsf{T-Succ}\qquad\dfrac{}{\Gamma_3\vdash 0:\mathsf{Nat}}\,\textsf{T-Zero}}{\Gamma_3\vdash\mathsf{if}\ z\ \mathsf{then}\ \mathsf{succ}\ n\ \mathsf{else}\ 0:\mathsf{Nat}}\;\textsf{T-If}`

T-Abs then gives $`\Gamma\vdash[x\mapsto s]t:\mathsf{Bool}\to\mathsf{Nat}`. Compared with $`E_2`, the context has lost $`x{:}\mathsf{Nat}`. The leaf for $`x` has become the derivation of $`\mathsf{succ}\ n` from the example before Lemma 25.4, weakened by $`z{:}\mathsf{Bool}`. The height has grown from 1 to 2. The argument $`s` is open: it uses $`n` from $`\Gamma`.

*Theorem 25.5 (Substitution lemma) \[Paper proof only: proof in this section\].* For all contexts $`\Gamma`, variables $`x`, terms $`s,t` and types $`S,T`: if $`\Gamma,x{:}S\vdash t:T` and $`\Gamma\vdash s:S`, then $`\Gamma\vdash[x\mapsto s]t:T`.

We call Theorem 25.5 the *substitution lemma*, as C.8 does. It concerns typing. The substitution lemma for IMP expressions in Sessions 1 and 11 concerns evaluation and is a different statement. Its first hypothesis includes that the context $`\Gamma,x{:}S` is formed, so $`x\notin\mathrm{dom}(\Gamma)`.

*Proof.* Fix $`x`, $`S` and $`s`. For a derivation $`D` of a judgment $`\Gamma,x{:}S\vdash t:T`, whose context ends with the binding $`x{:}S`, let

$$`P(D)\coloneqq(\Gamma\vdash s:S)\Rightarrow(\Gamma\vdash[x\mapsto s]t:T).`

Read $`\Gamma`, $`t` and $`T` from the conclusion of $`D`. We prove $`P(D)` for every such $`D` by induction on its height. Let $`D` have height $`h`, and assume $`P(D')` for every derivation $`D'` of height less than $`h` whose context ends with $`x{:}S`. Assume $`\Gamma\vdash s:S`. We consider the last rule of $`D`.

*Variable.* $`D` ends with T-Var, so $`t` is a variable $`w` with $`w{:}T\in(\Gamma,x{:}S)`. If $`w=x`, then $`T=S`, because $`x\notin\mathrm{dom}(\Gamma)` and $`x{:}S` is the only binding of $`x`. Then $`[x\mapsto s]x=s`, and $`\Gamma\vdash s:S` is the assumption. If $`w\neq x`, then $`w{:}T\in\Gamma` and $`[x\mapsto s]w=w`, so T-Var gives $`\Gamma\vdash w:T`.

*Constants.* If $`D` ends with T-True, T-False, T-Zero or T-Unit, then $`[x\mapsto s]t=t` (C.3), and the same axiom gives $`\Gamma\vdash t:T`.

*Rules without a binder.* Let $`D` end with T-If, T-Succ, T-Pred, T-IsZero or T-App, with premises $`D_i` deriving $`\Gamma,x{:}S\vdash t_i:T_i` for the immediate subterms $`t_i` of $`t`. For T-App, $`t=t_1\,t_2`, $`T_1=T_{11}\to T_{12}`, $`T_2=T_{11}` and $`T=T_{12}`. Each $`D_i` has height less than $`h`, and its induction hypothesis is

$$`P(D_i):\quad(\Gamma\vdash s:S)\Rightarrow(\Gamma\vdash[x\mapsto s]t_i:T_i).`

The assumption gives $`\Gamma\vdash[x\mapsto s]t_i:T_i` for each $`i`. Substitution acts on each immediate subterm (C.1, C.3), so the same rule gives $`\Gamma\vdash[x\mapsto s]t:T`.

*Abstraction (board case).* We must show $`\Gamma\vdash[x\mapsto s](\lambda y{:}T_1.t_2):T_1\to T_2`. Suppose $`D` ends with T-Abs. Then $`t=\lambda y{:}T_1.t_2`, $`T=T_1\to T_2`, and $`D` has one premise $`D_2:\Gamma,x{:}S,y{:}T_1\vdash t_2:T_2` of height $`h-1`. The induction hypothesis will be applied to a derivation $`D_2'` built in step 3, whose context is $`\Gamma,y{:}T_1,x{:}S`. Read with $`\Gamma,y{:}T_1` in place of $`\Gamma`, it is

$$`P(D_2'):\quad(\Gamma,y{:}T_1\vdash s:S)\Rightarrow(\Gamma,y{:}T_1\vdash[x\mapsto s]t_2:T_2).`

1. The context of $`D_2` is formed, so $`y\notin\mathrm{dom}(\Gamma,x{:}S)`. Hence $`y\neq x` and $`y\notin\mathrm{dom}(\Gamma)`.
2. Lemma 25.1 applied to $`\Gamma\vdash s:S` gives $`\mathrm{FV}(s)\subseteq\mathrm{dom}(\Gamma)`, so $`y\notin\mathrm{FV}(s)`. Together with $`y\neq x`, the abstraction equation of substitution (C.1, C.3) applies without renaming: $`[x\mapsto s](\lambda y{:}T_1.t_2)=\lambda y{:}T_1.\,[x\mapsto s]t_2`.
3. The context $`\Gamma,y{:}T_1,x{:}S` is formed, by step 1 and $`x\notin\mathrm{dom}(\Gamma)`. It is a permutation of $`\Gamma,x{:}S,y{:}T_1`. Lemma 25.2 applied to $`D_2` gives a derivation $`D_2'` of $`\Gamma,y{:}T_1,x{:}S\vdash t_2:T_2` with height $`h-1`.
4. Lemma 25.4 applied to $`\Gamma\vdash s:S`, with the new variable $`y` (step 1) and the type $`T_1`, gives $`\Gamma,y{:}T_1\vdash s:S`.
5. The context of $`D_2'` ends with $`x{:}S`, and its height $`h-1` is less than $`h`. So the induction hypothesis $`P(D_2')` holds. Step 4 supplies its premise, and it gives $`\Gamma,y{:}T_1\vdash[x\mapsto s]t_2:T_2`.
6. T-Abs, with $`y\notin\mathrm{dom}(\Gamma)` from step 1, gives $`\Gamma\vdash\lambda y{:}T_1.\,[x\mapsto s]t_2:T_1\to T_2`. By step 2 this is $`\Gamma\vdash[x\mapsto s](\lambda y{:}T_1.t_2):T_1\to T_2`.

This proves $`P(D)` for every derivation $`D` whose context ends with $`x{:}S`. Given the two hypotheses of Theorem 25.5, apply $`P(D)` to a derivation $`D` of $`\Gamma,x{:}S\vdash t:T`. $`\square`

Why is the induction hypothesis not applied to $`D_2` itself? $`P` is stated for derivations whose context ends with $`x{:}S`, and the context of $`D_2` ends with $`y{:}T_1`. Step 3 moves $`x{:}S` to the end. The derivation $`D_2'` is not a subderivation of $`D`, so induction on derivations would not supply $`P(D_2')`. Induction on height does, because Lemma 25.2 keeps the height. The context $`\Gamma` is not fixed before the induction. It is read from $`D`, so the hypothesis for $`D_2'` speaks about the longer context $`\Gamma,y{:}T_1`. A context fixed in advance would give no hypothesis for that context, just as a final store fixed in advance failed in [Session 3, §3.2](chapter-03/index.html#ch03-s2).

In the opening example, $`y` is $`z`, $`T_1=\mathsf{Bool}` and $`D_2` is $`E_2`. Step 1 gives $`z\neq x` and $`z\neq n`. Step 2 uses $`\mathrm{FV}(\mathsf{succ}\ n)=\{n\}`. Step 3 reorders $`\Gamma_2` to $`n{:}\mathsf{Nat},z{:}\mathsf{Bool},x{:}\mathsf{Nat}`. Step 4 is the weakened derivation of $`\mathsf{succ}\ n`. Inside step 5, the T-If case and then the variable case with $`w=x` put that derivation at the leaf for $`x`. The result is the derivation displayed above.

Session 26 applies Theorem 25.5 to the step E-AppAbs, $`(\lambda x{:}T_{11}.t_{12})\,v_2\to[x\mapsto v_2]t_{12}`, with $`s=v_2`. Preservation in C.8 is stated for every context $`\Gamma`, so $`v_2` may have free variables, as $`s` has here.

# Exercises
%%%
tag := "ch25-s4"
number := false
%%%

*25.1.* Let $`\Gamma=f{:}\mathsf{Nat}\to\mathsf{Bool}` and suppose $`\Gamma\vdash s:\mathsf{Nat}`. Follow the proof of Theorem 25.5 for a derivation of $`\Gamma,x{:}\mathsf{Nat}\vdash f\,x:\mathsf{Bool}`. Write both induction hypotheses as formulas, and say which case uses $`\Gamma\vdash s:\mathsf{Nat}`.

*25.2.* Let $`\Gamma=y{:}\mathsf{Nat}`. Derive $`\Gamma,x{:}\mathsf{Nat}\vdash\lambda y{:}\mathsf{Bool}.\,x:\mathsf{Bool}\to\mathsf{Nat}`, and name the parameter that its T-Abs node must use. Compute $`[x\mapsto y]` of the term. Then replace $`x` by $`y` literally in $`\lambda y{:}\mathsf{Bool}.\,x` and type the result. Which steps of the board case exclude the second result?

*25.3.* Suppose the extension $`\Gamma,y{:}U` were allowed when $`y\in\mathrm{dom}(\Gamma)`, and T-Var used the rightmost binding of the variable. Give a counterexample to Lemma 25.4. Which case of its proof fails?

*25.4.* Let $`\Delta` be a sequence of bindings. Prove by induction on derivations, without heights and without Lemma 25.2: if $`\Gamma,x{:}S,\Delta\vdash t:T` and $`\Gamma\vdash s:S`, then $`\Gamma,\Delta\vdash[x\mapsto s]t:T`. Which case uses weakening, and how many times?

*Further problem.* Let $`\Gamma=f{:}\mathsf{Nat}\to\mathsf{Bool}` and $`V=\lambda y{:}\mathsf{Nat}.\,f\,y`. Consider $`(\lambda g{:}\mathsf{Nat}\to\mathsf{Bool}.\,\lambda f{:}\mathsf{Nat}.\,g\,f)\,V`. Derive its type under $`\Gamma`, take the E-AppAbs step, and follow the abstraction case of Theorem 25.5 through the remaining binder. What would literal replacement of $`g` by $`V` produce?

# Reading for the Seminar
%%%
tag := "ch25-s5"
number := false
%%%

*Definitions · 10 minutes.* Draw $`E_2` and $`E`, write the context at every node, and compute the heights. State Lemmas 25.2 and 25.4 for the contexts of the opening example.

*Joint proof · 30 minutes.* Write $`P(D)` and present the variable case. Then present the abstraction case in six steps. Before step 5, ask the group in which context $`s` must be typed, and why the induction hypothesis cannot be applied to $`D_2` directly.

*Proof review · 20 minutes.* Work Exercise 25.2 with and without renaming, and mark the T-Var leaf whose lookup changes. Discuss how Exercise 25.4 removes the need for Lemma 25.2.

*Facilitator’s hint.* Circle the binder that is still in scope after the substitution. Weakening adds exactly its binding to the derivation of $`s`, and permutation moves $`x{:}S` past it.

# Solutions and Further Reading
%%%
tag := "ch25-s6"
number := false
%%%

*25.1.* The derivation ends with T-App. Its premises are $`D_1:\Gamma,x{:}\mathsf{Nat}\vdash f:\mathsf{Nat}\to\mathsf{Bool}` and $`D_2:\Gamma,x{:}\mathsf{Nat}\vdash x:\mathsf{Nat}`, both by T-Var. The hypotheses are $`P(D_1):(\Gamma\vdash s:\mathsf{Nat})\Rightarrow(\Gamma\vdash[x\mapsto s]f:\mathsf{Nat}\to\mathsf{Bool})` and $`P(D_2):(\Gamma\vdash s:\mathsf{Nat})\Rightarrow(\Gamma\vdash[x\mapsto s]x:\mathsf{Nat})`. For $`D_1` the variable case with $`w=f\neq x` gives $`[x\mapsto s]f=f` and $`\Gamma\vdash f:\mathsf{Nat}\to\mathsf{Bool}` by T-Var, without the assumption. For $`D_2` the variable case with $`w=x` gives $`[x\mapsto s]x=s`, and the assumption $`\Gamma\vdash s:\mathsf{Nat}` is the conclusion. T-App gives $`\Gamma\vdash f\,s:\mathsf{Bool}`, and $`f\,s=[x\mapsto s](f\,x)`.

*25.2.* The context $`\Gamma,x{:}\mathsf{Nat},y{:}\mathsf{Bool}` is not formed, since $`y\in\mathrm{dom}(\Gamma)`. So T-Abs uses the representative $`\lambda w{:}\mathsf{Bool}.\,x` with $`w\notin\{x,y\}`, and its premise $`\Gamma,x{:}\mathsf{Nat},w{:}\mathsf{Bool}\vdash x:\mathsf{Nat}` holds by T-Var. Then $`[x\mapsto y](\lambda w{:}\mathsf{Bool}.\,x)=\lambda w{:}\mathsf{Bool}.\,y`, and Theorem 25.5 gives $`y{:}\mathsf{Nat}\vdash\lambda w{:}\mathsf{Bool}.\,y:\mathsf{Bool}\to\mathsf{Nat}`. Literal replacement gives $`\lambda y{:}\mathsf{Bool}.\,y`, in which $`y` is the parameter. Its type is $`\mathsf{Bool}\to\mathsf{Bool}`: the lookup of $`y{:}\mathsf{Nat}` is lost and the type changes. Step 1 makes the parameter differ from every variable of $`\Gamma`. Step 2 then gives $`y\notin\mathrm{FV}(s)` by Lemma 25.1.

*25.3.* $`y{:}\mathsf{Nat}\vdash\mathsf{succ}\ y:\mathsf{Nat}` by T-Var and T-Succ. Under $`y{:}\mathsf{Nat},y{:}\mathsf{Bool}`, T-Var gives $`y:\mathsf{Bool}`, so T-Succ does not apply and $`\mathsf{succ}\ y` has no type. The T-Var case of Lemma 25.4 fails: the new binding hides the old one, so a lookup in $`\Gamma` is no longer a lookup in $`\Gamma,y{:}U`.

*25.4.* For $`D` deriving $`\Gamma,x{:}S,\Delta\vdash t:T`, take $`P(D)\coloneqq(\Gamma\vdash s:S)\Rightarrow(\Gamma,\Delta\vdash[x\mapsto s]t:T)`, with $`\Gamma` and $`\Delta` read from $`D`. In the variable case with $`w=x`, $`T=S`, and $`\Gamma,\Delta\vdash s:S` follows from $`\Gamma\vdash s:S` by Lemma 25.4, applied once per binding of $`\Delta`. Each variable of $`\Delta` is new, because $`\Gamma,x{:}S,\Delta` is formed. In the variable case with $`w\neq x`, the binding of $`w` lies in $`\Gamma,\Delta`. In the abstraction case the premise $`\Gamma,x{:}S,\Delta,y{:}T_1\vdash t_2:T_2` already has the required form, with $`\Delta,y{:}T_1` in place of $`\Delta`. So the hypothesis of the immediate premise applies. As before, $`y\notin\mathrm{dom}(\Gamma)\cup\{x\}`, Lemma 25.1 gives $`y\notin\mathrm{FV}(s)`, and T-Abs closes the case. Every hypothesis used concerns an immediate subderivation, so induction on derivations suffices. Theorem 25.5 is the case of empty $`\Delta`. Weakening has moved from the abstraction case to the variable case.

*Further problem.* Since $`f\in\mathrm{dom}(\Gamma)`, T-Abs cannot add $`f{:}\mathsf{Nat}` to a context that contains $`\Gamma`. The derivation uses the representative $`\lambda g{:}\mathsf{Nat}\to\mathsf{Bool}.\,\lambda w{:}\mathsf{Nat}.\,g\,w`. Under $`\Gamma,g{:}\mathsf{Nat}\to\mathsf{Bool},w{:}\mathsf{Nat}`, T-Var and T-App give $`g\,w:\mathsf{Bool}`. Two T-Abs nodes give the type $`(\mathsf{Nat}\to\mathsf{Bool})\to(\mathsf{Nat}\to\mathsf{Bool})`. Under $`\Gamma,y{:}\mathsf{Nat}`, T-App gives $`f\,y:\mathsf{Bool}`, so $`\Gamma\vdash V:\mathsf{Nat}\to\mathsf{Bool}` by T-Abs. T-App types the application at $`\mathsf{Nat}\to\mathsf{Bool}`. $`V` is a value, so E-AppAbs gives $`[g\mapsto V](\lambda w{:}\mathsf{Nat}.\,g\,w)`. Since $`w\neq g` and $`w\notin\mathrm{FV}(V)=\{f\}`, this is $`\lambda w{:}\mathsf{Nat}.\,V\,w`. In Theorem 25.5 take $`x=g`, $`S=\mathsf{Nat}\to\mathsf{Bool}` and $`s=V`. In its abstraction case, step 4 gives $`\Gamma,w{:}\mathsf{Nat}\vdash V:\mathsf{Nat}\to\mathsf{Bool}`. Inside step 5, the variable case for $`g` returns this derivation of $`V`, T-Var types $`w`, T-App gives $`\Gamma,w{:}\mathsf{Nat}\vdash V\,w:\mathsf{Bool}`, and T-Abs gives $`\Gamma\vdash\lambda w{:}\mathsf{Nat}.\,V\,w:\mathsf{Nat}\to\mathsf{Bool}`, the type before the step. Literal replacement in $`\lambda f{:}\mathsf{Nat}.\,g\,f` would give $`\lambda f{:}\mathsf{Nat}.\,(\lambda y{:}\mathsf{Nat}.\,f\,y)\,f`. The free $`f` of $`V` is captured by the parameter $`f{:}\mathsf{Nat}`, and $`f\,y` applies a number. The result has no type. Because $`V` is open, this step takes place under the nonempty context $`\Gamma`. Preservation in C.8 is stated for every context.

*Typing does not determine the substitution.* Let $`\Gamma=y{:}\mathsf{Bool}`, so that $`\Gamma,x{:}\mathsf{Bool}\vdash\lambda w{:}\mathsf{Bool}.\,x:\mathsf{Bool}\to\mathsf{Bool}`. Capture-avoiding substitution gives $`[x\mapsto y](\lambda w{:}\mathsf{Bool}.\,x)=\lambda w{:}\mathsf{Bool}.\,y`, and literal replacement in $`\lambda y{:}\mathsf{Bool}.\,x` gives $`\lambda y{:}\mathsf{Bool}.\,y`. Both have type $`\mathsf{Bool}\to\mathsf{Bool}` under $`\Gamma`. So the capturing result has the type that Theorem 25.5 promises, and a type check of the result cannot detect capture. Evaluation can. Substitute $`\mathsf{true}` for $`y` in both terms and apply each to $`\mathsf{false}`. E-AppAbs gives $`(\lambda w{:}\mathsf{Bool}.\,\mathsf{true})\,\mathsf{false}\to\mathsf{true}` and $`(\lambda y{:}\mathsf{Bool}.\,y)\,\mathsf{false}\to\mathsf{false}`. The free variables of C.1 detect the difference before any step: $`\mathrm{FV}(\lambda w{:}\mathsf{Bool}.\,y)=\{y\}`, while $`\mathrm{FV}(\lambda y{:}\mathsf{Bool}.\,y)=\varnothing`. Theorem 25.5 constrains the type of the result of substitution. It does not specify the operation.

*Nameless and intrinsically typed terms.* In a nameless representation a variable is the position of its binding in the context (TAPL, §6.1). If each term is indexed by its context and its type, every term is typed by construction, and the typing judgment is no longer a separate relation. Weakening becomes a renaming of positions that skips the new binding. Substitution becomes a map from the positions of one context to terms over another. Passing it under a binder weakens every replacement term by the new binding, which is step 4 of the board case. Theorem 25.5 is then the type of the substitution function. This book keeps the typing judgment as a relation separate from the syntax (C.3), and Lemma 25.3 is the form that the identification of alpha-equivalent terms (TAPL, §5.3) takes for derivations.
