import VersoManual

open Verso.Genre Manual

#doc (Manual) "References and the Value Restriction" =>
%%%
tag := "ch30"
file := "chapter-30"
%%%

* *Definitions.* [Lambda card C.6](lambda-card/index.html#lambda-c6): locations $`l`, stores $`\mu` with extension $`(\mu,l\mapsto v)` and update $`[l\mapsto v]\mu`, the steps $`t\mid\mu\to t'\mid\mu'` with E-RefV, E-Ref, E-DerefLoc, E-Deref, E-Assign, E-Assign1, E-Assign2 and the lifted earlier rules, store typings $`\Sigma` and extension $`\Sigma\subseteq\Sigma'`, the rules T-Loc, T-Ref, T-Deref and T-Assign, well-typed stores $`\Gamma\mid\Sigma\vdash\mu`, and the value restriction. The typed language and the judgment $`\Gamma\mid\Sigma\vdash t:T` ([Lambda card, Judgments](lambda-card/index.html)). Sequencing $`t_1;t_2` ([C.3](lambda-card/index.html#lambda-c3)). The inference form, type schemes, T-VarInst and T-LetGen ([C.5](lambda-card/index.html#lambda-c5), [Session 29](chapter-29/index.html)). The statements from Session 30 on, the form of the safety table and Rows 1–4 ([C.8](lambda-card/index.html#lambda-c8)). Inversion, canonical forms, progress, and preservation by induction on the evaluation derivation ([Session 24](chapter-24/index.html#ch24-s3)). The weakening and substitution lemmas ([Session 25](chapter-25/index.html)).
* *New terms.* Location, store (of a running term), store typing, well-typed store, value restriction. [Glossary and label key](glossary/index.html)
* *Theorem 30.6 (Preservation).* For every $`\Gamma`, $`\Sigma`, $`\mu`, $`t`, $`t'`, $`\mu'` and $`T`: if $`\Gamma\mid\Sigma\vdash t:T`, $`\Gamma\mid\Sigma\vdash\mu` and $`t\mid\mu\to t'\mid\mu'`, then there is a store typing $`\Sigma'` with $`\Sigma\subseteq\Sigma'`, $`\Gamma\mid\Sigma'\vdash t':T` and $`\Gamma\mid\Sigma'\vdash\mu'`.
* *Source.* Pierce, _Types and Programming Languages_ (TAPL). The constructs, evaluation rules, store typings and typing rules of C.6 are those of §§13.1–13.4. §13.5 states progress and preservation for the simply typed lambda calculus with Unit and references, together with the two store lemmas used here. Theorems 30.5–30.6 and Lemmas 30.2–30.3 are the same statements for the typed language of this session, which also has Bool, Nat, products, sums and let. §22.7 shows that let-polymorphism is unsound with references and introduces the value restriction. Lemmas 30.1 and 30.4 are this book’s. [Source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)
* *Board case.* Preservation, case E-RefV (allocation). Invert the typing of $`\mathsf{ref}\ v_1`. Extend $`\Sigma` at the fresh location. Type the result with T-Loc. Check the new store cell by cell with store weakening.
* *Proof outline.* Fix $`\Gamma` and induct on the evaluation derivation $`E:t\mid\mu\to t'\mid\mu'`, with $`Q(E)\coloneqq\forall\Sigma,T,\ (\Gamma\mid\Sigma\vdash t:T\land\Gamma\mid\Sigma\vdash\mu)\Rightarrow\exists\Sigma',\ \Sigma\subseteq\Sigma'\land\Gamma\mid\Sigma'\vdash t':T\land\Gamma\mid\Sigma'\vdash\mu'`. E-RefV takes $`\Sigma'=(\Sigma,l{:}T_1)`. The other computation rules take $`\Sigma'=\Sigma`, and E-Assign uses store update (Lemma 30.3). A congruence rule takes $`\Sigma'` from the induction hypothesis and retypes the other immediate subterms by store weakening (Lemma 30.2).
* *From Session 29.* Session 29 typed let in two ways: by T-Let in the typed language, and by T-LetGen with type schemes in the inference form. Until now a step changed only the term. From this session a step can also change a store, and preservation may enlarge the store typing. Generalization at let must now be restricted to values.

Two variables can name one cell. In the program

$$`\mathsf{let}\ r=\mathsf{ref}\ 0\ \mathsf{in}\ \mathsf{let}\ q=r\ \mathsf{in}\ (q\mathrel{:=}\mathsf{succ}\ 0;\ {!}r)`

the write goes through $`q` and the read through $`r`, and the read returns $`\mathsf{succ}\ 0`. After its first step the program contains a location, and no typing rule of Sessions 24–29 gives a location a type. This session types locations with a store typing and proves that a step keeps the type, even a step that allocates. The same sharing breaks the polymorphic let of Session 29, and the value restriction repairs it.

# Locations and stores
%%%
tag := "ch30-s1"
%%%

[C.6](lambda-card/index.html#lambda-c6) adds three forms of term: $`\mathsf{ref}\ t` allocates a new cell, $`{!}t` reads a cell, and $`t_1\mathrel{:=}t_2` writes one. A *location* $`l` names a cell. Locations are values that arise only during evaluation; a program contains none. A *store* $`\mu` is a finite map from locations to values, and $`\mu(l)` is the content of the cell at $`l`. A program starts in the empty store $`\varnothing`, and one step is now $`t\mid\mu\to t'\mid\mu'`. In Part 2 the word store means such a map $`\mu`, the memory of a running term, and not the IMP store of Part 1, which maps every variable name to an integer.

The opening program takes six steps from $`\varnothing`. Its sequence abbreviates $`(\lambda y{:}\mathsf{Unit}.{!}r)\,(q\mathrel{:=}\mathsf{succ}\ 0)` ([C.3](lambda-card/index.html#lambda-c3)).

1. E-RefV, lifted by E-Let, allocates a location $`l\notin\mathrm{dom}(\varnothing)`: $`\mathsf{ref}\ 0\mid\varnothing\to l\mid(\varnothing,l\mapsto 0)`. The term becomes $`\mathsf{let}\ r=l\ \mathsf{in}\ \mathsf{let}\ q=r\ \mathsf{in}\ (q\mathrel{:=}\mathsf{succ}\ 0;\ {!}r)`.
2. E-LetV substitutes $`l` for $`r`: $`\mathsf{let}\ q=l\ \mathsf{in}\ (q\mathrel{:=}\mathsf{succ}\ 0;\ {!}l)`.
3. E-LetV substitutes $`l` for $`q`: $`(\lambda y{:}\mathsf{Unit}.{!}l)\,(l\mathrel{:=}\mathsf{succ}\ 0)`. Steps 2 and 3 keep the store $`(\varnothing,l\mapsto 0)`.
4. E-Assign, lifted by E-App2, writes the cell: $`(\lambda y{:}\mathsf{Unit}.{!}l)\,\mathsf{unit}\mid(\varnothing,l\mapsto\mathsf{succ}\ 0)`.
5. E-AppAbs gives $`{!}l`.
6. E-DerefLoc reads the cell: $`\mathsf{succ}\ 0\mid(\varnothing,l\mapsto\mathsf{succ}\ 0)`.

Steps 2 and 3 copy the location, not the cell, so the write in step 4 and the read in step 6 reach the same cell. If the program binds $`q` to $`\mathsf{ref}\ ({!}r)` instead, a second allocation creates a cell at another location, the write goes there, and the read returns $`0` (Exercise 30.1). Both programs have type Nat. Their types do not tell them apart; the number of cells does.

What type should $`l` have after step 1? Its cell holds $`0`, so $`\mathsf{Ref}\ \mathsf{Nat}` is the natural answer. Reading the type off the cell fails in two ways. First, the typing of a term would depend on the store, which changes at every write. Second, a cell can mention its own location. The program $`\mathsf{let}\ r=\mathsf{ref}\ (\lambda y{:}\mathsf{Unit}.y)\ \mathsf{in}\ r\mathrel{:=}(\lambda y{:}\mathsf{Unit}.({!}r)\,y)` ends with the store $`(\varnothing,l\mapsto\lambda y{:}\mathsf{Unit}.({!}l)\,y)`. To type $`l` from its contents we must type this abstraction, which contains $`l`, which sends us back to the same cell.

A *store typing* $`\Sigma` (C.6) fixes in advance the type of the contents of each cell; it is not the set of IMP stores of A.2. T-Loc reads it, and never the store:

$$`\frac{\Sigma(l)=T_1}{\Gamma\mid\Sigma\vdash l:\mathsf{Ref}\ T_1}\;\textsf{T-Loc}`

Let $`\Sigma_c=(\varnothing,l{:}\mathsf{Unit}\to\mathsf{Unit})` and $`\Gamma_y=(\varnothing,y{:}\mathsf{Unit})`. The derivation below types the contents of the cyclic cell. Its leaf for $`l` consults $`\Sigma_c`, so the derivation is finite.

$$`\dfrac{\dfrac{\dfrac{\dfrac{\Sigma_c(l)=\mathsf{Unit}\to\mathsf{Unit}}{\Gamma_y\mid\Sigma_c\vdash l:\mathsf{Ref}\ (\mathsf{Unit}\to\mathsf{Unit})}\;\textsf{T-Loc}}{\Gamma_y\mid\Sigma_c\vdash{!}l:\mathsf{Unit}\to\mathsf{Unit}}\;\textsf{T-Deref}\qquad\dfrac{y{:}\mathsf{Unit}\in\Gamma_y}{\Gamma_y\mid\Sigma_c\vdash y:\mathsf{Unit}}\;\textsf{T-Var}}{\Gamma_y\mid\Sigma_c\vdash({!}l)\,y:\mathsf{Unit}}\;\textsf{T-App}}{\varnothing\mid\Sigma_c\vdash\lambda y{:}\mathsf{Unit}.({!}l)\,y:\mathsf{Unit}\to\mathsf{Unit}}\;\textsf{T-Abs}`

A store $`\mu` is *well typed* under $`\Gamma` and $`\Sigma`, written $`\Gamma\mid\Sigma\vdash\mu`, if $`\mathrm{dom}(\mu)=\mathrm{dom}(\Sigma)` and $`\Gamma\mid\Sigma\vdash\mu(l):\Sigma(l)` for every $`l\in\mathrm{dom}(\mu)` (C.6). Each stored value is typed under the whole of $`\Sigma`. So the derivation above shows that the cyclic store is well typed under $`\Sigma_c`. The store $`(\varnothing,l\mapsto 0)` of the opening trace is well typed under $`(\varnothing,l{:}\mathsf{Nat})`. It is not well typed under $`(\varnothing,l{:}\mathsf{Bool})`, since $`0` does not have type Bool, nor under $`\varnothing`, since the domains differ.

# Inversion, weakening and update
%%%
tag := "ch30-s2"
%%%

Each form of term in C.6 is the conclusion of exactly one typing rule. For example, a derivation of $`\varnothing\mid\varnothing\vdash\mathsf{ref}\ 0:T` must end with T-Ref. Its premise types $`0`, so it ends with T-Zero, and $`T=\mathsf{Ref}\ \mathsf{Nat}`. As in [Session 24, Lemma 24.1](chapter-24/index.html#ch24-s2), inversion reads the premises off the form.

*Lemma 30.1 (Inversion for references).* For all $`\Gamma`, $`\Sigma`, $`T`, terms $`t_1,t_2` and locations $`l`:

* (a) If $`\Gamma\mid\Sigma\vdash l:T`, then $`l\in\mathrm{dom}(\Sigma)` and $`T=\mathsf{Ref}\ \Sigma(l)`.
* (b) If $`\Gamma\mid\Sigma\vdash\mathsf{ref}\ t_1:T`, then $`T=\mathsf{Ref}\ T_1` for a type $`T_1` with $`\Gamma\mid\Sigma\vdash t_1:T_1`.
* (c) If $`\Gamma\mid\Sigma\vdash{!}t_1:T`, then $`\Gamma\mid\Sigma\vdash t_1:\mathsf{Ref}\ T`.
* (d) If $`\Gamma\mid\Sigma\vdash t_1\mathrel{:=}t_2:T`, then $`T=\mathsf{Unit}`, and $`\Gamma\mid\Sigma\vdash t_1:\mathsf{Ref}\ T_{11}` and $`\Gamma\mid\Sigma\vdash t_2:T_{11}` for a type $`T_{11}`.

*Proof.* T-Loc, T-Ref, T-Deref and T-Assign are the only typing rules whose conclusions have these forms. By inversion ([Session 1, §1.4](chapter-01/index.html#ch01-s4)), a derivation of the hypothesis ends with that rule. Its conclusion fixes $`T`, and its premises are the remaining claims. $`\square`

A step may add a location to the store typing, and the terms typed before the step must keep their types. Let $`\Sigma_1=(\varnothing,l_1{:}\mathsf{Nat})` and $`\Sigma_2=(\Sigma_1,l_2{:}\mathsf{Bool})`. T-Loc, T-Deref and T-Succ give $`\varnothing\mid\Sigma_1\vdash\mathsf{succ}\ ({!}l_1):\mathsf{Nat}`. The same three rules give $`\varnothing\mid\Sigma_2\vdash\mathsf{succ}\ ({!}l_1):\mathsf{Nat}`, because the T-Loc leaf reads $`\Sigma_2(l_1)=\Sigma_1(l_1)=\mathsf{Nat}`. Under $`(\varnothing,l_1{:}\mathsf{Bool})` the term has no type. That map changes an old binding, so it does not extend $`\Sigma_1`.

*Lemma 30.2 (Store weakening).* For all $`\Gamma`, $`\Sigma`, $`\Sigma'`, $`t` and $`T`: if $`\Gamma\mid\Sigma\vdash t:T` and $`\Sigma\subseteq\Sigma'`, then $`\Gamma\mid\Sigma'\vdash t:T`.

*Proof.* Fix $`\Sigma\subseteq\Sigma'`. We prove $`P(D)` for every typing derivation $`D` under $`\Sigma` by induction on $`D`, where for $`D:\Gamma\mid\Sigma\vdash t:T`

$$`P(D)\coloneqq\Gamma\mid\Sigma'\vdash t:T.`

If $`D` ends with T-Loc, then $`t=l`, $`l\in\mathrm{dom}(\Sigma)` and $`T=\mathsf{Ref}\ \Sigma(l)`. The definition of $`\Sigma\subseteq\Sigma'` gives $`\Sigma'(l)=\Sigma(l)`, and T-Loc gives $`\Gamma\mid\Sigma'\vdash l:\mathsf{Ref}\ \Sigma(l)`. Every other rule has the same store typing in its premises and its conclusion and does not inspect it. Apply the induction hypotheses to the premises and then the same rule. A premise may have a larger context than the conclusion, as in T-Abs; $`P` is read with the context of each derivation. $`\square`

A write keeps the store typing. Step 4 of the opening trace replaces $`0` by $`\mathsf{succ}\ 0` in a cell of type Nat. T-Assign admits $`l\mathrel{:=}t_2` only when $`t_2` has the type $`\Sigma(l)`. Under $`(\varnothing,l{:}\mathsf{Nat})` it rejects $`l\mathrel{:=}\mathsf{true}`.

*Lemma 30.3 (Store update).* For all $`\Gamma`, $`\Sigma`, $`\mu`, $`l`, $`v` and $`T`: if $`\Gamma\mid\Sigma\vdash\mu`, $`\Sigma(l)=T` and $`\Gamma\mid\Sigma\vdash v:T`, then $`\Gamma\mid\Sigma\vdash[l\mapsto v]\mu`.

*Proof.* Since $`l\in\mathrm{dom}(\Sigma)=\mathrm{dom}(\mu)`, the update is defined, and $`\mathrm{dom}([l\mapsto v]\mu)=\mathrm{dom}(\mu)=\mathrm{dom}(\Sigma)`. Let $`l'\in\mathrm{dom}(\mu)`. If $`l'=l`, the cell holds $`v`, and $`\Gamma\mid\Sigma\vdash v:\Sigma(l)` by hypothesis. If $`l'\neq l`, the cell still holds $`\mu(l')`, and $`\Gamma\mid\Sigma\vdash\mu(l'):\Sigma(l')` because $`\mu` is well typed. $`\square`

# Progress and preservation
%%%
tag := "ch30-s3"
%%%

Let $`\Sigma_1=(\varnothing,l{:}\mathsf{Nat})`. Then $`\varnothing\mid\Sigma_1\vdash l:\mathsf{Ref}\ \mathsf{Nat}` and $`\varnothing\mid\Sigma_1\vdash{!}l:\mathsf{Nat}`. In the store $`(\varnothing,l\mapsto 0)` the term $`{!}l` steps to $`0` by E-DerefLoc. In the store $`\varnothing` it has no step, because E-DerefLoc needs a cell at $`l`, and it is not a value. The store $`\varnothing` is not well typed under $`\Sigma_1`. So progress must assume a well-typed store, and the canonical form of a Ref value must connect $`\Sigma` with that store.

*Lemma 30.4 (Canonical forms).* Let $`v` be a value and $`\Sigma` a store typing.

* (a) If $`\varnothing\mid\Sigma\vdash v:\mathsf{Ref}\ T_1`, then $`v` is a location $`l` with $`\Sigma(l)=T_1`.
* (b) If $`v` is a location, then $`\varnothing\mid\Sigma\vdash v:T` holds for no type $`T` of the form $`\mathsf{Bool}`, $`\mathsf{Nat}`, $`T_1\to T_2`, $`\mathsf{Unit}`, $`T_1\times T_2` or $`T_1+T_2`.

*Proof.* (b) By Lemma 30.1(a), every type of a location has the form $`\mathsf{Ref}\ \Sigma(l)`. (a) By the grammar of values, $`v` is $`\mathsf{true}`, $`\mathsf{false}`, a numeric value, an abstraction, $`\mathsf{unit}`, a pair, an injection or a location. The typing rules for the first seven forms are T-True, T-False, T-Zero, T-Succ, T-Abs, T-Unit, T-Pair, T-Inl and T-Inr, and none of them concludes a Ref type. So $`v` is a location $`l`. Lemma 30.1(a) gives $`\mathsf{Ref}\ T_1=\mathsf{Ref}\ \Sigma(l)`, so $`\Sigma(l)=T_1`. $`\square`

By (b), the canonical-forms statements of Rows 1–3 in [C.8](lambda-card/index.html#lambda-c8) keep their proofs: the new form of value never has their types.

*Theorem 30.5 (Progress).* For every term $`t`, type $`T` and store typing $`\Sigma`: if $`\varnothing\mid\Sigma\vdash t:T`, then $`t` is a value or, for every store $`\mu` with $`\varnothing\mid\Sigma\vdash\mu`, there are $`t'` and $`\mu'` with $`t\mid\mu\to t'\mid\mu'`.

*Proof.* Fix $`\Sigma`. We prove $`P(D)` for every typing derivation $`D:\Gamma\mid\Sigma\vdash t:T` by induction on $`D`, as in [Session 26, Theorem 26.3](chapter-26/index.html#ch26-s2), with

$$`P(D)\coloneqq(\Gamma=\varnothing)\Rightarrow\bigl(t\ \text{is a value}\ \lor\ \forall\mu,\ (\varnothing\mid\Sigma\vdash\mu)\Rightarrow\exists t',\mu',\ t\mid\mu\to t'\mid\mu'\bigr).`

The cases of Rows 1–4 are those of Sessions 24–29 with the store passed along. A computation rule keeps $`\mu`, and a congruence rule passes on the store change of its premise. Lemma 30.4(b) excludes locations wherever those cases use canonical forms. The new cases follow. In each, assume $`\Gamma=\varnothing` and fix $`\mu` with $`\varnothing\mid\Sigma\vdash\mu`.

* T-Loc: $`t=l` is a value.
* T-Ref: $`t=\mathsf{ref}\ t_1`. If $`t_1` is a value $`v_1`, choose $`l\notin\mathrm{dom}(\mu)`. One exists, because $`\mathrm{dom}(\mu)` is finite and there are infinitely many locations. E-RefV applies. Otherwise the induction hypothesis for the premise gives $`t_1\mid\mu\to t_1'\mid\mu'`, and E-Ref applies.
* T-Deref: $`t={!}t_1` with $`\varnothing\mid\Sigma\vdash t_1:\mathsf{Ref}\ T`. If $`t_1` steps, E-Deref applies. If $`t_1` is a value, Lemma 30.4(a) makes it a location $`l\in\mathrm{dom}(\Sigma)=\mathrm{dom}(\mu)`. So $`\mu(l)` is defined, and E-DerefLoc applies.
* T-Assign: $`t=t_1\mathrel{:=}t_2`. If $`t_1` steps, E-Assign1 applies. If $`t_1` is a value and $`t_2` steps, E-Assign2 applies. If both are values, Lemma 30.4(a) makes $`t_1` a location $`l\in\mathrm{dom}(\mu)`, and E-Assign applies. $`\square`

Preservation must let the store typing grow. The opening program has type Nat under $`\varnothing`. After step 1 the term $`\mathsf{let}\ r=l\ \mathsf{in}\ \ldots` contains $`l`, so it has a type only under a store typing that maps $`l`. Under $`\Sigma_1=(\varnothing,l{:}\mathsf{Nat})` it has type Nat, and the store $`(\varnothing,l\mapsto 0)` is well typed. Steps 2–6 keep $`\Sigma_1`. The write in step 4 stores a value of type Nat, and every term on the way has type Nat.

*Theorem 30.6 (Preservation).* For every $`\Gamma`, $`\Sigma`, $`\mu`, $`t`, $`t'`, $`\mu'` and $`T`: if $`\Gamma\mid\Sigma\vdash t:T`, $`\Gamma\mid\Sigma\vdash\mu` and $`t\mid\mu\to t'\mid\mu'`, then there is a store typing $`\Sigma'` with $`\Sigma\subseteq\Sigma'`, $`\Gamma\mid\Sigma'\vdash t':T` and $`\Gamma\mid\Sigma'\vdash\mu'`.

Fix $`\Gamma`. We prove $`Q(E)` for every evaluation derivation $`E` by induction on $`E`. For $`E:t\mid\mu\to t'\mid\mu'` the induction property is

$$`Q(E)\coloneqq\forall\Sigma,T,\ (\Gamma\mid\Sigma\vdash t:T\ \land\ \Gamma\mid\Sigma\vdash\mu)\Rightarrow\exists\Sigma',\ \Sigma\subseteq\Sigma'\ \land\ \Gamma\mid\Sigma'\vdash t':T\ \land\ \Gamma\mid\Sigma'\vdash\mu'.`

As in [Session 24, Theorem 24.4](chapter-24/index.html#ch24-s3), $`T` is quantified inside $`Q(E)`, so the induction hypothesis applies at the type of the subterm that steps. The board case uses three rules of C.6.

$$`\frac{l\notin\mathrm{dom}(\mu)}{\mathsf{ref}\ v_1\mid\mu\to l\mid(\mu,l\mapsto v_1)}\;\textsf{E-RefV}\qquad\frac{\Gamma\mid\Sigma\vdash t_1:T_1}{\Gamma\mid\Sigma\vdash\mathsf{ref}\ t_1:\mathsf{Ref}\ T_1}\;\textsf{T-Ref}\qquad\frac{\Sigma(l)=T_1}{\Gamma\mid\Sigma\vdash l:\mathsf{Ref}\ T_1}\;\textsf{T-Loc}`

*Case E-RefV (board case).* Suppose $`E` ends with E-RefV. Then $`t=\mathsf{ref}\ v_1`, $`t'=l` and $`\mu'=(\mu,l\mapsto v_1)` for a location $`l\notin\mathrm{dom}(\mu)`. E-RefV has no evaluation premise, so there is no induction hypothesis.

1. Fix $`\Sigma` and $`T`. Assume $`D:\Gamma\mid\Sigma\vdash\mathsf{ref}\ v_1:T` and $`\Gamma\mid\Sigma\vdash\mu`. We must find $`\Sigma'` with $`\Sigma\subseteq\Sigma'`, $`\Gamma\mid\Sigma'\vdash l:T` and $`\Gamma\mid\Sigma'\vdash(\mu,l\mapsto v_1)`.
2. Lemma 30.1(b), applied to $`D`, gives a type $`T_1` with $`T=\mathsf{Ref}\ T_1` and $`\Gamma\mid\Sigma\vdash v_1:T_1`.
3. The hypothesis $`\Gamma\mid\Sigma\vdash\mu` gives $`\mathrm{dom}(\mu)=\mathrm{dom}(\Sigma)`. Since $`l\notin\mathrm{dom}(\mu)`, also $`l\notin\mathrm{dom}(\Sigma)`. So $`\Sigma'\coloneqq(\Sigma,l{:}T_1)` is defined. It agrees with $`\Sigma` on $`\mathrm{dom}(\Sigma)`, so $`\Sigma\subseteq\Sigma'`.
4. $`\Sigma'(l)=T_1`, so T-Loc gives $`\Gamma\mid\Sigma'\vdash l:\mathsf{Ref}\ T_1`, that is, $`\Gamma\mid\Sigma'\vdash t':T`.
5. It remains to prove $`\Gamma\mid\Sigma'\vdash\mu'`. The domains agree: $`\mathrm{dom}(\mu')=\mathrm{dom}(\mu)\cup\{l\}=\mathrm{dom}(\Sigma)\cup\{l\}=\mathrm{dom}(\Sigma')`.
6. The new cell: $`\mu'(l)=v_1` and $`\Sigma'(l)=T_1`. Lemma 30.2, applied to $`\Gamma\mid\Sigma\vdash v_1:T_1` (step 2) and $`\Sigma\subseteq\Sigma'` (step 3), gives $`\Gamma\mid\Sigma'\vdash v_1:T_1`.
7. An old cell $`l'\in\mathrm{dom}(\mu)`: $`\mu'(l')=\mu(l')` and $`\Sigma'(l')=\Sigma(l')`. The hypothesis $`\Gamma\mid\Sigma\vdash\mu` gives $`\Gamma\mid\Sigma\vdash\mu(l'):\Sigma(l')`. Lemma 30.2 gives $`\Gamma\mid\Sigma'\vdash\mu(l'):\Sigma'(l')`.
8. Steps 5–7 prove $`\Gamma\mid\Sigma'\vdash\mu'`. With steps 3 and 4 this proves $`Q(E)`.

Step 3 is the only use of freshness (Exercise 30.2). With $`\Sigma'=\Sigma`, step 4 would fail, because $`l\notin\mathrm{dom}(\Sigma)`. Steps 6 and 7 need Lemma 30.2 because each value was typed under $`\Sigma`, while $`\Gamma\mid\Sigma'\vdash\mu'` types it under $`\Sigma'`. In the opening trace, the premise of step 1 is this case with $`\Sigma=\varnothing`, $`v_1=0`, $`T_1=\mathsf{Nat}` and $`\Sigma'=\Sigma_1`.

*Case E-DerefLoc.* Here $`t={!}l`, $`t'=\mu(l)` and $`\mu'=\mu`. Let $`\Gamma\mid\Sigma\vdash{!}l:T` and $`\Gamma\mid\Sigma\vdash\mu`. Lemma 30.1(c) and (a) give $`\Sigma(l)=T`. Since $`\mu` is well typed, $`\Gamma\mid\Sigma\vdash\mu(l):\Sigma(l)`. Take $`\Sigma'=\Sigma`.

*Case E-Assign.* Here $`t=l\mathrel{:=}v_2`, $`t'=\mathsf{unit}` and $`\mu'=[l\mapsto v_2]\mu`. Lemma 30.1(d) and (a) give $`T=\mathsf{Unit}`, $`\Sigma(l)=T_{11}` and $`\Gamma\mid\Sigma\vdash v_2:T_{11}`. T-Unit types $`\mathsf{unit}`, and Lemma 30.3 gives $`\Gamma\mid\Sigma\vdash[l\mapsto v_2]\mu`. Take $`\Sigma'=\Sigma`. Assignment changes the store but not its domain, and T-Assign forces the new value to have the old type $`\Sigma(l)`.

*Case E-Assign1.* Here $`t=t_1\mathrel{:=}t_2` and $`t'=t_1'\mathrel{:=}t_2`. The premise is $`E_1:t_1\mid\mu\to t_1'\mid\mu'`, with

$$`Q(E_1):\quad\forall\Sigma_0,S,\ (\Gamma\mid\Sigma_0\vdash t_1:S\ \land\ \Gamma\mid\Sigma_0\vdash\mu)\Rightarrow\exists\Sigma',\ \Sigma_0\subseteq\Sigma'\ \land\ \Gamma\mid\Sigma'\vdash t_1':S\ \land\ \Gamma\mid\Sigma'\vdash\mu'.`

Let $`\Gamma\mid\Sigma\vdash t:T` and $`\Gamma\mid\Sigma\vdash\mu`. Lemma 30.1(d) gives $`T=\mathsf{Unit}`, $`\Gamma\mid\Sigma\vdash t_1:\mathsf{Ref}\ T_{11}` and $`\Gamma\mid\Sigma\vdash t_2:T_{11}`. Apply $`Q(E_1)` at $`\Sigma_0=\Sigma` and $`S=\mathsf{Ref}\ T_{11}`. It gives $`\Sigma'` with $`\Sigma\subseteq\Sigma'`, $`\Gamma\mid\Sigma'\vdash t_1':\mathsf{Ref}\ T_{11}` and $`\Gamma\mid\Sigma'\vdash\mu'`. Lemma 30.2 gives $`\Gamma\mid\Sigma'\vdash t_2:T_{11}`, and T-Assign gives $`\Gamma\mid\Sigma'\vdash t':\mathsf{Unit}`. E-Assign2, E-Ref and E-Deref are similar. In E-Assign2 the operand that Lemma 30.2 retypes is the value $`v_1`.

*Rows 1–4.* Each computation rule of the earlier rows keeps the store. Take $`\Sigma'=\Sigma` and argue as in Sessions 24–29 with $`\Sigma` fixed. E-AppAbs, E-CaseInl, E-CaseInr and E-LetV use the substitution lemma with $`\Sigma`, as Row 2 of C.8 states it. Its proof in Session 25, and the proof of the weakening lemma it uses, gain the cases T-Loc, T-Ref, T-Deref and T-Assign. The case T-Loc holds because T-Loc does not read the context and $`[x\mapsto s]l=l`. The other three apply the induction hypotheses to the premises and the same rule. Each congruence rule of the earlier rows is treated like E-Assign1: the induction hypothesis gives $`\Sigma'`, and Lemma 30.2 retypes the other immediate subterms.

This proves $`Q(E)` for every $`E`. Apply it at the given $`\Sigma` and $`T`. $`\square`

# Row 5 of the safety table
%%%
tag := "ch30-s4"
%%%

Lemma 30.4 and the proofs of Theorems 30.5–30.6 give a new row of the safety table in [C.8](lambda-card/index.html#lambda-c8).

*Row 5 · References · Session 30.*

* *Canonical forms.* If $`v` is a value and $`\varnothing\mid\Sigma\vdash v:\mathsf{Ref}\ T_1`, then $`v` is a location $`l` with $`\Sigma(l)=T_1` (Lemma 30.4(a)).
* *Progress.* T-Loc: the term is a value. T-Ref: steps by E-Ref or E-RefV; a location $`l\notin\mathrm{dom}(\mu)` exists because $`\mathrm{dom}(\mu)` is finite. T-Deref: steps by E-Deref or E-DerefLoc; $`\mu(l)` is defined because $`l\in\mathrm{dom}(\Sigma)=\mathrm{dom}(\mu)`. T-Assign: steps by E-Assign1, E-Assign2 or E-Assign; E-Assign applies because $`l\in\mathrm{dom}(\Sigma)=\mathrm{dom}(\mu)`, as for T-Deref.
* *Preservation.* E-RefV: $`\Sigma'=(\Sigma,l{:}T_1)`, where $`T_1` is the type of the stored value; store weakening (Lemma 30.2). E-DerefLoc: $`\Sigma'=\Sigma`, using $`\Gamma\mid\Sigma\vdash\mu`. E-Assign: $`\Sigma'=\Sigma`; store update (Lemma 30.3). E-Ref, E-Deref, E-Assign1, E-Assign2: premise.

Rows 1–4 are restated in the store form. Their computation rules take $`\Sigma'=\Sigma` and keep the store. Their congruence rules take $`\Sigma'` from the premise and use store weakening for the other immediate subterms. Each earlier canonical-forms statement gains the case of a location, which Lemma 30.4(b) excludes.

*Safety.* From this session C.8 states safety for a term together with a store: if $`\varnothing\mid\Sigma\vdash t:T`, $`\varnothing\mid\Sigma\vdash\mu` and $`t\mid\mu\to^*t'\mid\mu'`, then $`t'` is a value or $`t'\mid\mu'` takes a step. Fix $`T`. For a path $`\pi:t\mid\mu\to^*t'\mid\mu'` ([A.6](imp-card/index.html#imp-a6)) take

$$`R(\pi)\coloneqq\forall\Sigma,\ (\varnothing\mid\Sigma\vdash t:T\ \land\ \varnothing\mid\Sigma\vdash\mu)\Rightarrow\exists\Sigma',\ \varnothing\mid\Sigma'\vdash t':T\ \land\ \varnothing\mid\Sigma'\vdash\mu'.`

The store typing is quantified inside $`R(\pi)`, because each step may enlarge it. Induction on $`\pi`, with Theorem 30.6 at $`\Gamma=\varnothing` for the first step, proves $`R(\pi)`. Theorem 30.5 at the final $`\Sigma'` finishes the proof. For a program, take $`\Sigma=\varnothing` and $`\mu=\varnothing`.

# The value restriction
%%%
tag := "ch30-s5"
%%%

In Session 29 the inference-form term $`\mathsf{let}\ \mathit{id}=\lambda x.x\ \mathsf{in}\ \mathsf{if}\ \mathit{id}\ \mathsf{true}\ \mathsf{then}\ \mathit{id}\ 0\ \mathsf{else}\ 0` gives $`\mathit{id}` the scheme $`\forall X.X\to X` and uses it at Bool and at Nat ([C.5](lambda-card/index.html#lambda-c5)). Theorems 30.5–30.6 concern the typed language, in which T-Let types let and nothing is generalized. The inference form types references by T-Ref, T-Deref and T-Assign (C.6). Drop for the moment the value restriction of C.6, so that T-LetGen may quantify type variables whatever the right-hand side is, and consider

$$`u=\mathsf{let}\ r=\mathsf{ref}\ (\lambda x.x)\ \mathsf{in}\ (r\mathrel{:=}(\lambda x.\mathsf{succ}\ x);\ ({!}r)\ \mathsf{true}).`

*Proposition 30.7 (Generalizing a non-value).* If T-LetGen may quantify type variables for every right-hand side, then $`\vdash u:\mathsf{Bool}` and $`u\mid\varnothing\to^*\mathsf{succ}\ \mathsf{true}\mid(\varnothing,l\mapsto\lambda x.\mathsf{succ}\ x)`, and $`\mathsf{succ}\ \mathsf{true}` is stuck. So safety fails for the inference form with this rule.

*Proof.* The typing. Write $`\Gamma_r` for the context $`\varnothing,r{:}\forall X.\mathsf{Ref}\ (X\to X)`.

1. T-VarInst with $`n=0`, the unannotated T-Abs with parameter type $`X`, and T-Ref give $`\vdash\mathsf{ref}\ (\lambda x.x):\mathsf{Ref}\ (X\to X)`. The generalization condition holds, since $`X\notin\mathrm{FV}(\varnothing)`. So T-LetGen may bind $`r{:}\forall X.\mathsf{Ref}\ (X\to X)`.
2. T-VarInst with $`X\mapsto\mathsf{Nat}` gives $`\Gamma_r\vdash r:\mathsf{Ref}\ (\mathsf{Nat}\to\mathsf{Nat})`. With $`\Gamma_r\vdash\lambda x.\mathsf{succ}\ x:\mathsf{Nat}\to\mathsf{Nat}`, T-Assign gives $`\Gamma_r\vdash r\mathrel{:=}(\lambda x.\mathsf{succ}\ x):\mathsf{Unit}`.
3. T-VarInst with $`X\mapsto\mathsf{Bool}` gives $`\Gamma_r\vdash r:\mathsf{Ref}\ (\mathsf{Bool}\to\mathsf{Bool})`. T-Deref, T-True and T-App give $`\Gamma_r\vdash({!}r)\ \mathsf{true}:\mathsf{Bool}`.
4. The sequence is $`(\lambda y.({!}r)\ \mathsf{true})\,(r\mathrel{:=}(\lambda x.\mathsf{succ}\ x))`. T-Abs with parameter type Unit and T-App give it type Bool, and T-LetGen gives $`\vdash u:\mathsf{Bool}`.

The evaluation, from the empty store.

1. E-RefV, lifted by E-Let, allocates $`l` with contents $`\lambda x.x`.
2. E-LetV substitutes $`l` for $`r`: $`(\lambda y.({!}l)\ \mathsf{true})\,(l\mathrel{:=}(\lambda x.\mathsf{succ}\ x))`.
3. E-Assign, lifted by E-App2, gives $`(\lambda y.({!}l)\ \mathsf{true})\,\mathsf{unit}` and the store $`(\varnothing,l\mapsto\lambda x.\mathsf{succ}\ x)`.
4. E-AppAbs gives $`({!}l)\ \mathsf{true}`.
5. E-DerefLoc, lifted by E-App1, gives $`(\lambda x.\mathsf{succ}\ x)\ \mathsf{true}`.
6. E-AppAbs gives $`\mathsf{succ}\ \mathsf{true}`, which is stuck ([C.2](lambda-card/index.html#lambda-c2)). $`\square`

The typing used two instances of one scheme, as if each occurrence of $`r` had its own cell. Evaluation allocates once, in step 1, and E-LetV puts the same location $`l` at both occurrences. No preservation statement in the form of Theorem 30.6 can hold for this typing. Suppose it gave store typings $`\Sigma'\subseteq\Sigma''` after steps 1 and 2. The term after step 2 contains $`l\mathrel{:=}(\lambda x.\mathsf{succ}\ x)`, which by Lemma 30.1(d) and (a) needs $`\Sigma''(l)=\mathsf{Nat}\to\mathsf{Nat}`. It also contains $`({!}l)\ \mathsf{true}`, which by Lemma 30.1(c) and (a) needs $`\Sigma''(l)` of the form $`\mathsf{Bool}\to T'`. A store typing gives $`l` one type, so preservation fails at step 1 or at step 2. The generalization condition of Session 29 does not help. It protects the type variables of $`\Gamma`, and here $`\Gamma` is empty; the danger lies in a cell that the store shares.

Compare the term that replaces each occurrence of $`r` in the body by its own copy of $`\mathsf{ref}\ (\lambda x.x)`. It allocates two cells. The write fills the first, the read returns $`\lambda x.x` from the second, and the result is $`\mathsf{true}`. T-LetGen types a let as if each occurrence of the bound variable held its own copy of the right-hand side. For a value $`v_1` this is exact: E-LetV substitutes $`v_1` for every occurrence, and nothing has been evaluated before. A right-hand side that still has to be evaluated runs once, and its cells are shared.

The *value restriction* (C.6) lets T-LetGen and CT-LetGen quantify type variables only when the right-hand side is a value. Otherwise the variable receives a scheme with $`n=0`. In $`u` the right-hand side $`\mathsf{ref}\ (\lambda x.x)` is not a value, so $`r` gets a single type $`\mathsf{Ref}\ (T_1\to T_1)`. The write needs $`T_1=\mathsf{Nat}` and the read needs $`T_1=\mathsf{Bool}`, so $`u` has no type. In constraint typing the constraint set forces $`X=\mathsf{Nat}` and $`X=\mathsf{Bool}`, and unify fails. A value that allocates when it is called is still generalized. In $`\mathsf{let}\ f=\lambda y.\mathsf{ref}\ y\ \mathsf{in}\ \{{!}(f\ 0),{!}(f\ \mathsf{true})\}` the scheme of $`f` is $`\forall X.X\to\mathsf{Ref}\ X`, each call allocates its own cell, and the term has type $`\mathsf{Nat}\times\mathsf{Bool}`. Proposition 30.7 shows that some restriction is needed. This book does not prove that the inference form with the value restriction is safe.

# Exercises
%%%
tag := "ch30-s6"
number := false
%%%

*30.1.* Replace $`\mathsf{let}\ q=r` by $`\mathsf{let}\ q=\mathsf{ref}\ ({!}r)` in the opening program. Trace the evaluation from $`\varnothing` and name the rules of each step. Give the final term and store, and a store typing after each allocation.

*30.2.* Suppose E-RefV dropped its premise $`l\notin\mathrm{dom}(\mu)` and, for $`l\in\mathrm{dom}(\mu)`, overwrote the cell at $`l`. (a) Which step of the board case fails? (b) Give a program of the typed language that has a type and whose evaluation can reach a stuck term.

*30.3.* Find a store $`\mu` and two different store typings $`\Sigma_1,\Sigma_2` with $`\varnothing\mid\Sigma_1\vdash\mu` and $`\varnothing\mid\Sigma_2\vdash\mu`. What does this say about the $`\Sigma'` in Theorem 30.6?

*30.4.* Under the value restriction, decide for each term of the inference form whether $`g` is generalized and whether the term has a type. (a) $`\mathsf{let}\ g=(\lambda z.z)\,(\lambda x.x)\ \mathsf{in}\ \{g\ 0,g\ \mathsf{true}\}`. (b) $`\mathsf{let}\ g=\lambda y.(\lambda z.z)\,(\lambda x.x)\,y\ \mathsf{in}\ \{g\ 0,g\ \mathsf{true}\}`. Is generalizing $`g` in (a) unsafe?

*Further problem.* Renaming a fresh location. Suppose $`\mathsf{ref}\ v` can step in the same store $`\mu` by choosing either of two fresh locations $`l_1` or $`l_2`. Define the swap of $`l_1` and $`l_2` on terms, stores and store typings. Assume $`\varnothing\mid\Sigma\vdash\mathsf{ref}\ v:T` and $`\varnothing\mid\Sigma\vdash\mu`. Explain why the swap fixes the initial configuration and carries one result of the step, with its store typing, to the other, even when $`v` contains locations.

# Reading for the Seminar
%%%
tag := "ch30-s7"
number := false
%%%

*Definitions · 10 minutes.* Trace the opening program with one row per location and one column per step. Write a store typing under each column. Type the cyclic cell of §30.1 with T-Loc.

*Joint proof · 30 minutes.* Present the E-RefV case of Theorem 30.6 in eight steps. Mark the use of freshness (step 3) and the two uses of store weakening (steps 6 and 7). Then present the E-Assign case and name the lemma it needs.

*Proof review · 20 minutes.* Present Proposition 30.7: derive the typing with two instances, run the six steps, and identify the shared location. Show how the value restriction rejects $`u`. Use Exercise 30.2 to test the board case.

*Facilitator’s hint.* The location as a term has type $`\mathsf{Ref}\ T_1`. The entry $`\Sigma(l)` records only the type $`T_1` of its contents.

# Solutions and Further Reading
%%%
tag := "ch30-s8"
number := false
%%%

*30.1.* There are eight steps.

1. E-RefV under E-Let allocates $`l_1`. The store is $`(\varnothing,l_1\mapsto 0)`, with store typing $`(\varnothing,l_1{:}\mathsf{Nat})`.
2. E-LetV gives $`\mathsf{let}\ q=\mathsf{ref}\ ({!}l_1)\ \mathsf{in}\ (q\mathrel{:=}\mathsf{succ}\ 0;\ {!}l_1)`.
3. E-DerefLoc under E-Ref under E-Let gives $`\mathsf{let}\ q=\mathsf{ref}\ 0\ \mathsf{in}\ \ldots`.
4. E-RefV under E-Let allocates $`l_2\neq l_1`, since $`l_2\notin\mathrm{dom}(\varnothing,l_1\mapsto 0)`. The store is $`((\varnothing,l_1\mapsto 0),l_2\mapsto 0)`, with store typing $`((\varnothing,l_1{:}\mathsf{Nat}),l_2{:}\mathsf{Nat})`.
5. E-LetV gives $`(\lambda y{:}\mathsf{Unit}.{!}l_1)\,(l_2\mathrel{:=}\mathsf{succ}\ 0)`.
6. E-Assign under E-App2 writes $`\mathsf{succ}\ 0` into the cell at $`l_2`.
7. E-AppAbs gives $`{!}l_1`.
8. E-DerefLoc gives $`0`.

The final configuration is $`0\mid((\varnothing,l_1\mapsto 0),l_2\mapsto\mathsf{succ}\ 0)`.

*30.2.* (a) Step 3. If $`l\in\mathrm{dom}(\Sigma)`, then $`(\Sigma,l{:}T_1)` is undefined, and every $`\Sigma'` with $`\Sigma\subseteq\Sigma'` keeps $`\Sigma'(l)=\Sigma(l)`. When $`\Sigma(l)\neq T_1`, step 4 fails: T-Loc gives $`l` only the type $`\mathsf{Ref}\ \Sigma(l)`. (b) Take $`\mathsf{let}\ r=\mathsf{ref}\ 0\ \mathsf{in}\ \mathsf{let}\ q=\mathsf{ref}\ \mathsf{true}\ \mathsf{in}\ \mathsf{succ}\ ({!}r)`, of type Nat. The first allocation gives $`l` holding $`0`, and E-LetV puts $`l` for $`r`. If the second allocation chooses $`l` again, the store becomes $`(\varnothing,l\mapsto\mathsf{true})`. After E-LetV the term is $`\mathsf{succ}\ ({!}l)`, which steps to the stuck term $`\mathsf{succ}\ \mathsf{true}`.

*30.3.* Take the cyclic store $`\mu=(\varnothing,l\mapsto\lambda y{:}\mathsf{Unit}.({!}l)\,y)` of §30.1, $`\Sigma_1=(\varnothing,l{:}\mathsf{Unit}\to\mathsf{Unit})` and $`\Sigma_2=(\varnothing,l{:}\mathsf{Unit}\to\mathsf{Nat})`. Under $`\Sigma_2`, $`{!}l` has type $`\mathsf{Unit}\to\mathsf{Nat}`, so $`({!}l)\,y` has type Nat and the stored abstraction has type $`\mathsf{Unit}\to\mathsf{Nat}=\Sigma_2(l)`. The derivation of §30.1 covers $`\Sigma_1`. So a store does not determine its store typing. Theorem 30.6 asserts that some suitable $`\Sigma'` exists. It does not compute $`\Sigma'` from $`\mu'`.

*30.4.* (a) The right-hand side is an application, not a value, so $`g` is not generalized. It gets one type $`S\to S`. The component $`g\ 0` needs $`S=\mathsf{Nat}` and $`g\ \mathsf{true}` needs $`S=\mathsf{Bool}`, so the term has no type. Generalizing would be safe here: the right-hand side allocates nothing, and the term evaluates to $`\{0,\mathsf{true}\}`. The value restriction rejects some safe programs. (b) The right-hand side is an abstraction, hence a value. It has type $`X\to X`, $`g` receives $`\forall X.X\to X`, and the term has type $`\mathsf{Nat}\times\mathsf{Bool}`. Wrapping a right-hand side in $`\lambda y.\ldots\,y` makes it a value without changing what it computes when applied.

*Further problem.* Let the swap exchange $`l_1` and $`l_2` and fix every other location. On a term it renames each location wherever it occurs, also inside abstractions, and leaves variables, types and the other constructors unchanged. On a store it renames each location in the domain and in each stored value. On a store typing it renames the domain; types contain no locations. By induction on typing derivations, every location in a term typed under $`\Sigma` lies in $`\mathrm{dom}(\Sigma)`, and the same holds for each stored value of a store well typed under $`\Sigma`. Since $`l_1,l_2\notin\mathrm{dom}(\mu)=\mathrm{dom}(\Sigma)`, neither location occurs in $`\mathsf{ref}\ v`, in $`\mu` or in $`\Sigma`, so the swap fixes all three. The result $`l_1\mid(\mu,l_1\mapsto v)` with store typing $`(\Sigma,l_1{:}T_1)` is carried to $`l_2\mid(\mu,l_2\mapsto v)` with $`(\Sigma,l_2{:}T_1)`. Every T-Loc leaf of the old derivations is renamed consistently. E-RefV makes one-step evaluation nondeterministic in the choice of the fresh location, but two choices differ only by such a renaming.

*Further reading · Recursion through the store.* The typed language of Sessions 24–29 has no recursion operator. The cyclic cell of §30.1 nevertheless gives a typed program that never stops. The program $`\mathsf{let}\ r=\mathsf{ref}\ (\lambda y{:}\mathsf{Unit}.y)\ \mathsf{in}\ (r\mathrel{:=}(\lambda y{:}\mathsf{Unit}.({!}r)\,y);\ ({!}r)\ \mathsf{unit})` has type Unit and never stops. After the write, $`({!}l)\ \mathsf{unit}` steps to $`(\lambda y{:}\mathsf{Unit}.({!}l)\,y)\ \mathsf{unit}` by E-DerefLoc under E-App1, and back to $`({!}l)\ \mathsf{unit}` by E-AppAbs. Safety is not affected: every term on the path is typed and takes a step. Store typings impose no well-foundedness condition on the chain of locations reachable from a value.

*Further reading · Polymorphism and references.* TAPL §22.7 introduces the value restriction and points to the literature on its soundness and on alternatives to it. This book does not prove that the inference form with the value restriction is safe. [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Sources and Formalization
%%%
tag := "ch30-notes"
number := false
%%%

* *Lemma 30.1.* Formulated in this book. Paper proof only (proof in [§30.2](chapter-30/index.html#ch30-s2)).
* *Lemma 30.2.* Corresponds to TAPL §13.5. Paper proof only (proof in [§30.2](chapter-30/index.html#ch30-s2)).
* *Lemma 30.3.* Corresponds to TAPL §13.5. Paper proof only (proof in [§30.2](chapter-30/index.html#ch30-s2)).
* *Lemma 30.4.* Formulated in this book. Paper proof only (proof in [§30.3](chapter-30/index.html#ch30-s3)).
* *Theorem 30.5.* Corresponds to TAPL §13.5. Paper proof only (proof in [§30.3](chapter-30/index.html#ch30-s3)).
* *Theorem 30.6.* Corresponds to TAPL §13.5. Paper proof only (proof in [§30.3](chapter-30/index.html#ch30-s3)).
* *Proposition 30.7.* Corresponds to TAPL §22.7. Paper proof only (proof in [§30.5](chapter-30/index.html#ch30-s5)).
