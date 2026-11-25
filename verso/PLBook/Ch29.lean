import VersoManual

open Verso.Genre Manual

#doc (Manual) "Let-Polymorphism" =>
%%%
tag := "ch29"
file := "chapter-29"
%%%

The identity $`\lambda x.x` has type $`\mathsf{Nat}\to\mathsf{Nat}` and type $`\mathsf{Bool}\to\mathsf{Bool}` (C.5). The program $`\mathsf{let}\ \mathit{id}=\lambda x.x\ \mathsf{in}\ \{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\}` evaluates to $`\{0,\mathsf{true}\}`. If the context gives $`\mathit{id}` one type, the first component forces its domain to be Nat and the second forces Bool, so the program has no type. The substituted program $`\{(\lambda x.x)\ 0,(\lambda x.x)\ \mathsf{true}\}` has type $`\mathsf{Nat}\times\mathsf{Bool}`, because the two copies of $`\lambda x.x` are typed separately. This session gives $`\mathit{id}` the type scheme $`\forall X.X\to X`, and each occurrence takes its own instance. The question is which type variables a let may quantify. A type variable that is free in the context may not be quantified. §29.3 shows a program that would otherwise be typed and get stuck.

*In this session.*

* *Definitions.* The let construct, E-LetV, E-Let and T-Let; type schemes, their instances and free variables, T-VarInst, T-LetGen, CT-VarInst and CT-LetGen ([C.5](lambda-card/index.html#lambda-c5)). The inference form, the unannotated T-Abs, type variables, $`\mathrm{FV}(T)`, type substitutions, constraint typing and $`\mathrm{unify}` (C.5, Session 28). Pairs and T-Pair ([C.4](lambda-card/index.html#lambda-c4), Session 27). Stuck terms ([C.2](lambda-card/index.html#lambda-c2)). The weakening and substitution lemmas (Session 25) and the safety table ([C.8](lambda-card/index.html#lambda-c8)). Inversion and induction on derivations ([Session 1, §§1.4–1.5](chapter-01/index.html#ch01-s4)).
* *New terms.* Let-polymorphism, type scheme, instance, generalization, generalization condition. [Glossary](glossary/index.html)
* *Theorem 29.3 (Generalization) and Proposition 29.4 (The condition is needed).* (Generalization) For every context $`\Gamma`, term $`t`, type $`T` and type variables $`X_1,\ldots,X_n` of the inference form: if $`\Gamma\vdash t:T` and $`\{X_1,\ldots,X_n\}\cap\mathrm{FV}(\Gamma)=\varnothing`, then $`\Gamma\vdash t:S` for every instance $`S` of $`\forall X_1\ldots X_n.T`. (The condition is needed) If the last premise of T-LetGen is dropped, the closed term $`u=\mathsf{let}\ f=\lambda y.(\mathsf{let}\ k=y\ \mathsf{in}\ k)\ \mathsf{in}\ \mathsf{if}\ f\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` has type Bool and reaches the stuck term $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` in three steps.
* *Board case.* Two derivations in the inference form. (a) Derive $`\vdash\mathsf{let}\ \mathit{id}=\lambda x.x\ \mathsf{in}\ \{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\}:\mathsf{Nat}\times\mathsf{Bool}`, giving each occurrence of $`\mathit{id}` its own instance of $`\forall X.X\to X`. (b) Derive $`\vdash u:\mathsf{Bool}` with the last premise of T-LetGen dropped, mark the generalization that violates it, and evaluate $`u` to the stuck term.
* *Proof outline.* Lemma 29.2 by induction on the typing derivation $`D` of $`\Gamma\vdash t:T`, with $`P(D)\coloneqq\forall\sigma,\ \sigma\Gamma\vdash t:\sigma T`. Its case T-LetGen renames the quantified variables, and the renaming leaves $`\Gamma` unchanged because of the generalization condition. Theorem 29.3: apply Lemma 29.2 to $`\sigma=[X_1\mapsto S_1,\ldots,X_n\mapsto S_n]`; the condition gives $`\sigma\Gamma=\Gamma`. Proposition 29.4: build the derivation of board case (b), then apply E-LetV, E-AppAbs and E-LetV.
* *From Session 28.* In Session 28 a variable bound by an abstraction has one type at all its occurrences, possibly with type variables that unification later fixes. Here a variable bound by let receives a type scheme, and each occurrence may take a different instance. Unification is unchanged. CT-LetGen calls it on the right-hand side of a let before it generalizes.

# Let in the typed language
%%%
tag := "ch29-s1"
%%%

The term $`\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2` binds $`x` in $`t_2` but not in $`t_1` ([C.5](lambda-card/index.html#lambda-c5)). From this session on it belongs to the typed language and to the inference form. No let term is a value. The evaluation rules first evaluate $`t_1` to a value and then substitute it:

$$`\frac{}{\mathsf{let}\ x=v_1\ \mathsf{in}\ t_2\to[x\mapsto v_1]t_2}\;\textsf{E-LetV}\qquad\frac{t_1\to t_1'}{\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2\to\mathsf{let}\ x=t_1'\ \mathsf{in}\ t_2}\;\textsf{E-Let}`

For example, $`\mathsf{let}\ x=\mathsf{pred}\ (\mathsf{succ}\ 0)\ \mathsf{in}\ \{x,\mathsf{iszero}\ x\}` reaches a value in three steps.

1. E-Let, with E-PredSucc as its premise, gives $`\mathsf{let}\ x=0\ \mathsf{in}\ \{x,\mathsf{iszero}\ x\}`.
2. E-LetV gives $`\{0,\mathsf{iszero}\ 0\}`.
3. E-Pair2, with E-IszeroZero as its premise, gives the value $`\{0,\mathsf{true}\}`.

The right-hand side is evaluated once, before it is substituted. In the typed language, let is typed by

$$`\frac{\Gamma\vdash t_1:T_1\quad\Gamma,x{:}T_1\vdash t_2:T_2}{\Gamma\vdash\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2:T_2}\;\textsf{T-Let}`

In the example, T-Zero, T-Succ and T-Pred give $`\vdash\mathsf{pred}\ (\mathsf{succ}\ 0):\mathsf{Nat}`. T-Var, T-IsZero and T-Pair give $`x{:}\mathsf{Nat}\vdash\{x,\mathsf{iszero}\ x\}:\mathsf{Nat}\times\mathsf{Bool}`. T-Let then gives the let the type $`\mathsf{Nat}\times\mathsf{Bool}`. T-Let is the only typing rule whose conclusion is a let. So inverting $`\Gamma\vdash\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2:T_2` gives a type $`T_1` with $`\Gamma\vdash t_1:T_1` and $`\Gamma,x{:}T_1\vdash t_2:T_2`. The weakening and substitution lemmas of Session 25 gain a T-Let case. It is handled like their T-Abs case, since let binds $`x` in $`t_2` as an abstraction binds its parameter.

*Proposition 29.1 (Row 4 of the safety table).* In the typed language, let adds the following row to the safety table of C.8.

* *Canonical forms.* None: no value is a let term.
* *Progress.* T-Let: the term steps by E-Let or E-LetV.
* *Preservation.* E-LetV: uses the substitution lemma. E-Let: premise.

*Proof.* Progress is proved by induction on the typing derivation $`D:\Gamma\vdash t:T`, with $`P(D)\coloneqq(\Gamma=\varnothing)\Rightarrow\bigl(t\ \text{is a value}\ \lor\ \exists t',\ t\to t'\bigr)`, as in [Session 26, Theorem 26.3](chapter-26/index.html#ch26-s2). Suppose $`D` ends with T-Let and $`\Gamma=\varnothing`. Then $`t=\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2`, with premise $`D_1:\ \vdash t_1:T_1`. Its context is empty, so $`P(D_1)` gives $`t_1\ \text{is a value}\ \lor\ \exists t_1',\ t_1\to t_1'`. The premise for $`t_2` has the context $`x{:}T_1`, and its hypothesis is not used. If $`t_1\to t_1'`, E-Let gives $`t\to\mathsf{let}\ x=t_1'\ \mathsf{in}\ t_2`. If $`t_1` is a value $`v_1`, E-LetV gives $`t\to[x\mapsto v_1]t_2`. No canonical form is needed, because E-LetV accepts every value. Preservation is proved by induction on the evaluation derivation $`E:t\to t'`, with $`Q(E)\coloneqq\forall\Gamma\ \forall T,\ (\Gamma\vdash t:T)\Rightarrow(\Gamma\vdash t':T)`. Let $`\Gamma\vdash t:T` and invert it. For E-LetV, inversion gives $`\Gamma\vdash v_1:T_1` and $`\Gamma,x{:}T_1\vdash t_2:T`, and the substitution lemma gives $`\Gamma\vdash[x\mapsto v_1]t_2:T`. For E-Let, inversion gives $`\Gamma\vdash t_1:T_1` and $`\Gamma,x{:}T_1\vdash t_2:T`. The hypothesis $`Q(E_1)` for the premise $`E_1:t_1\to t_1'`, at $`\Gamma` and $`T_1`, gives $`\Gamma\vdash t_1':T_1`. T-Let gives $`\Gamma\vdash\mathsf{let}\ x=t_1'\ \mathsf{in}\ t_2:T`. $`\square`

Row 4 adds no value, so the canonical-forms statements of Rows 1–3 gain no case.

# Type schemes and two instances
%%%
tag := "ch29-s2"
%%%

From here on we work in the inference form of C.5. Its typing judgment $`\Gamma\vdash t:T` uses the rules of C.2–C.4 for the unannotated forms, the unannotated T-Abs, and the rules T-VarInst and T-LetGen below. First try T-Let in this form. Let $`\Gamma=\mathit{id}{:}T_1` and suppose $`\Gamma\vdash\{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\}:S`. Inverting T-Pair and then T-App gives $`\Gamma\vdash\mathit{id}:U_1\to S_1` with $`\Gamma\vdash 0:U_1`, and $`\Gamma\vdash\mathit{id}:U_2\to S_2` with $`\Gamma\vdash\mathsf{true}:U_2`. T-Zero and T-True force $`U_1=\mathsf{Nat}` and $`U_2=\mathsf{Bool}`. The only type of $`\mathit{id}` under $`\Gamma` is $`T_1`, so $`\mathsf{Nat}\to S_1=T_1=\mathsf{Bool}\to S_2`. This is impossible. The application $`(\lambda\mathit{id}.\{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\})\ (\lambda x.x)` fails in the same way, because T-Abs also gives its parameter one type.

A *type scheme* $`\forall X_1\ldots X_n.T` (C.5) lists its *quantified variables* $`X_1,\ldots,X_n`. An *instance* of the scheme is a type $`[X_1\mapsto S_1,\ldots,X_n\mapsto S_n]T`, for any types $`S_1,\ldots,S_n`. For example, the instances of $`\forall X.X\to X` include $`\mathsf{Nat}\to\mathsf{Nat}`, $`\mathsf{Bool}\to\mathsf{Bool}` and $`(Y\to Y)\to(Y\to Y)`. A scheme may also contain type variables that are not quantified. The instances of $`\forall X.X\to X\times Y` include $`\mathsf{Nat}\to\mathsf{Nat}\times Y` and $`\mathsf{Bool}\to\mathsf{Bool}\times Y`. Within one instance, every occurrence of $`X` is replaced by the same type. In every instance, $`Y` stays unchanged. The scheme has $`\mathrm{FV}(\forall X.X\to X\times Y)=\{Y\}`. In the inference form a context binds each variable to a scheme, and $`\mathrm{FV}(\Gamma)` is the union of the free variables of its schemes. A variable bound by an abstraction receives a scheme with no quantified variable, which is a type.

With schemes in the context, two rules replace T-Var and T-Let. For $`n=0` they are T-Var and T-Let.

$$`\frac{x{:}\forall X_1\ldots X_n.T\in\Gamma}{\Gamma\vdash x:[X_1\mapsto T_1,\ldots,X_n\mapsto T_n]T}\;\textsf{T-VarInst}`

$$`\frac{\Gamma\vdash t_1:T_1\quad\Gamma,x{:}\forall X_1\ldots X_n.T_1\vdash t_2:T_2\quad\{X_1,\ldots,X_n\}\cap\mathrm{FV}(\Gamma)=\varnothing}{\Gamma\vdash\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2:T_2}\;\textsf{T-LetGen}`

T-VarInst types an occurrence of $`x` at an instance of its scheme. T-LetGen performs *generalization*: it quantifies type variables of the type $`T_1` of $`t_1`. Its last premise is the *generalization condition*: no quantified variable may be free in $`\Gamma`. *Let-polymorphism* is the resulting ability to use a let-bound variable at several instances. T-VarInst is the only rule whose conclusion types a variable, and T-LetGen is the only rule whose conclusion types a let.

*Board case (a).* We must show $`\vdash\mathsf{let}\ \mathit{id}=\lambda x.x\ \mathsf{in}\ \{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\}:\mathsf{Nat}\times\mathsf{Bool}`. The term is a let, so the derivation ends with T-LetGen. Write $`\Gamma_1=\mathit{id}{:}\forall X.X\to X`.

1. Right-hand side. T-VarInst with $`n=0` gives $`x{:}X\vdash x:X`. T-Abs gives $`\vdash\lambda x.x:X\to X`.
2. Generalization condition. The context of the let is empty, and $`\{X\}\cap\mathrm{FV}(\varnothing)=\varnothing`. So T-LetGen may quantify $`X`, and the body is typed under $`\Gamma_1`.
3. First occurrence. T-VarInst with $`X\mapsto\mathsf{Nat}` gives $`\Gamma_1\vdash\mathit{id}:\mathsf{Nat}\to\mathsf{Nat}`. T-Zero gives $`\Gamma_1\vdash 0:\mathsf{Nat}`, and T-App gives $`\Gamma_1\vdash\mathit{id}\ 0:\mathsf{Nat}`.
4. Second occurrence. T-VarInst with $`X\mapsto\mathsf{Bool}` gives $`\Gamma_1\vdash\mathit{id}:\mathsf{Bool}\to\mathsf{Bool}`. T-True and T-App give $`\Gamma_1\vdash\mathit{id}\ \mathsf{true}:\mathsf{Bool}`.
5. T-Pair gives $`\Gamma_1\vdash\{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\}:\mathsf{Nat}\times\mathsf{Bool}`.
6. T-LetGen, with steps 1, 5 and 2 as its three premises, gives the conclusion shown below.

$$`\frac{\vdash\lambda x.x:X\to X\qquad\Gamma_1\vdash\{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\}:\mathsf{Nat}\times\mathsf{Bool}\qquad\{X\}\cap\mathrm{FV}(\varnothing)=\varnothing}{\vdash\mathsf{let}\ \mathit{id}=\lambda x.x\ \mathsf{in}\ \{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\}:\mathsf{Nat}\times\mathsf{Bool}}\;\textsf{T-LetGen}`

Steps 3 and 4 choose their instances independently. T-Let would have fixed one type for $`\mathit{id}` in step 2, and the first paragraph of this section shows that no single type serves both steps. The two instances used are also types of $`\lambda x.x` itself in the empty context. §29.3 proves that this holds whenever the generalization condition is met.

# The generalization condition
%%%
tag := "ch29-s3"
%%%

Compare two derivations. In the empty context, $`\vdash\lambda x.x:X\to X`. Replacing $`X` by Bool throughout its derivation gives $`x{:}\mathsf{Bool}\vdash x:\mathsf{Bool}` and $`\vdash\lambda x.x:\mathsf{Bool}\to\mathsf{Bool}`. In the context $`y{:}Y`, T-VarInst gives $`y{:}Y\vdash y:Y`. Replacing $`Y` by Bool in the type alone would give $`y{:}Y\vdash y:\mathsf{Bool}`, which is not derivable. T-VarInst is the only rule for a variable, and the only instance of the scheme $`Y` is $`Y`. Replacing $`Y` in the context as well gives $`y{:}\mathsf{Bool}\vdash y:\mathsf{Bool}`, a judgment under another context. A type variable that is free in the context stands for one type: the type of the value that $`y` will hold. Only type variables that are not free in the context may be replaced in the type alone.

*Substitution on schemes.* Two schemes that differ only in the names of their quantified variables are identified, as alpha-equivalent terms are in [C.1](lambda-card/index.html#lambda-c1). For example, $`\forall X.X\to X` and $`\forall Z.Z\to Z` have the same instances. A type substitution $`\sigma` *avoids* a type variable $`Z` if $`Z\notin\mathrm{dom}(\sigma)` and $`Z` occurs in no type $`\sigma W` with $`W\in\mathrm{dom}(\sigma)`. To apply $`\sigma` to a scheme, first rename its quantified variables to variables that $`\sigma` avoids. Then $`\sigma(\forall X_1\ldots X_n.T)=\forall X_1\ldots X_n.\sigma T`. For example, $`[Y\mapsto X](\forall X.X\to Y)=\forall Z.Z\to X`. Renaming first prevents capture, as in [Session 22, §22.2](chapter-22/index.html#ch22-s2). $`\sigma\Gamma` applies $`\sigma` to each scheme of $`\Gamma`. If no variable of $`\mathrm{dom}(\sigma)` is free in $`\Gamma`, then $`\sigma\Gamma=\Gamma`. Indeed, after renaming, $`\sigma` acts on each scheme $`\forall Y_1\ldots Y_m.U` of $`\Gamma` as on $`U`. A variable of $`\mathrm{dom}(\sigma)` that occurred in $`U` would be one of the $`Y_j`, which $`\sigma` avoids, or free in $`\Gamma`. So $`\sigma U=U`.

*Lemma 29.2 (Typing under a type substitution).* For every context $`\Gamma`, term $`t`, type $`T` and type substitution $`\sigma`: if $`\Gamma\vdash t:T`, then $`\sigma\Gamma\vdash t:\sigma T`.

*Proof.* By induction on the typing derivation $`D` of $`\Gamma\vdash t:T`, with

$$`P(D)\coloneqq\forall\sigma,\ \sigma\Gamma\vdash t:\sigma T.`

The substitution is quantified inside $`P(D)`, as the final store was in [Session 3, §3.2](chapter-03/index.html#ch03-s2). The case T-LetGen applies the induction hypothesis for its first premise at a substitution other than $`\sigma`.

*T-VarInst.* Here $`t=x`, $`x{:}\forall X_1\ldots X_n.U\in\Gamma` and $`T=[X_1\mapsto S_1,\ldots,X_n\mapsto S_n]U`. Rename $`X_1,\ldots,X_n` to variables that $`\sigma` avoids. Then $`x{:}\forall X_1\ldots X_n.\sigma U\in\sigma\Gamma`, and T-VarInst with the types $`\sigma S_1,\ldots,\sigma S_n` gives $`\sigma\Gamma\vdash x:[X_1\mapsto\sigma S_1,\ldots,X_n\mapsto\sigma S_n](\sigma U)`. This type is $`\sigma T`. At an occurrence of $`X_i` in $`U`, both types have $`\sigma S_i`, since $`\sigma X_i=X_i`. At an occurrence of another variable $`W`, both have $`\sigma W`, since $`\sigma W` contains no $`X_i`.

*T-Abs.* Here $`t=\lambda x.t_2`, $`T=T_1\to T_2`, and the premise is $`D_2:\Gamma,x{:}T_1\vdash t_2:T_2`. $`P(D_2)` at $`\sigma` gives $`\sigma\Gamma,x{:}\sigma T_1\vdash t_2:\sigma T_2`. T-Abs gives $`\sigma\Gamma\vdash\lambda x.t_2:\sigma T_1\to\sigma T_2`, which is $`\sigma T`.

*T-LetGen.* Here $`t=\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2`. The premises are $`D_1:\Gamma\vdash t_1:T_1`, $`D_2:\Gamma,x{:}\forall X_1\ldots X_n.T_1\vdash t_2:T` and $`\{X_1,\ldots,X_n\}\cap\mathrm{FV}(\Gamma)=\varnothing`. Choose distinct variables $`Y_1,\ldots,Y_n` that $`\sigma` avoids and that occur neither in $`\Gamma` nor in $`T_1`. Let $`\rho=[X_1\mapsto Y_1,\ldots,X_n\mapsto Y_n]`.

1. By the generalization condition, no $`X_i` is free in $`\Gamma`. So $`\rho\Gamma=\Gamma`, and $`P(D_1)` at $`\sigma\circ\rho` gives $`\sigma\Gamma\vdash t_1:\sigma(\rho T_1)`.
2. Renaming gives $`\forall X_1\ldots X_n.T_1=\forall Y_1\ldots Y_n.\rho T_1`. Since $`\sigma` avoids each $`Y_i`, it maps this scheme to $`\forall Y_1\ldots Y_n.\sigma(\rho T_1)`. $`P(D_2)` at $`\sigma` gives $`\sigma\Gamma,x{:}\forall Y_1\ldots Y_n.\sigma(\rho T_1)\vdash t_2:\sigma T`.
3. No $`Y_i` is free in $`\sigma\Gamma`, because $`Y_i` does not occur in $`\Gamma` and $`\sigma` introduces no $`Y_i`.
4. T-LetGen, with steps 1, 2 and 3 as its premises, gives $`\sigma\Gamma\vdash\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2:\sigma T`.

*Other rules.* $`\sigma` leaves Bool, Nat and Unit unchanged, $`\sigma(T\to S)=\sigma T\to\sigma S` and $`\sigma(T\times S)=\sigma T\times\sigma S`. So the same rule applies to the induction hypotheses at $`\sigma`. For example, for T-App, $`\sigma\Gamma\vdash t_1:\sigma T_{11}\to\sigma T_{12}` and $`\sigma\Gamma\vdash t_2:\sigma T_{11}` give $`\sigma\Gamma\vdash t_1\ t_2:\sigma T_{12}`. $`\square`

*Theorem 29.3 (Generalization).* For every context $`\Gamma`, term $`t`, type $`T` and type variables $`X_1,\ldots,X_n`: if $`\Gamma\vdash t:T` and $`\{X_1,\ldots,X_n\}\cap\mathrm{FV}(\Gamma)=\varnothing`, then $`\Gamma\vdash t:[X_1\mapsto S_1,\ldots,X_n\mapsto S_n]T` for all types $`S_1,\ldots,S_n`.

*Proof.* Let $`\sigma=[X_1\mapsto S_1,\ldots,X_n\mapsto S_n]`. No variable of $`\mathrm{dom}(\sigma)` is free in $`\Gamma`, so $`\sigma\Gamma=\Gamma`. Lemma 29.2 gives $`\sigma\Gamma\vdash t:\sigma T`, that is, $`\Gamma\vdash t:[X_1\mapsto S_1,\ldots,X_n\mapsto S_n]T`. $`\square`

So every instance of a scheme formed by T-LetGen is a type of $`t_1` in the same context. This is what evaluation needs. E-LetV replaces each occurrence of $`x` in $`t_2` by the value $`v_1`. In a derivation by T-LetGen, T-VarInst typed each occurrence at an instance $`S` of $`\forall X_1\ldots X_n.T_1`. Theorem 29.3, applied to the first premise and the generalization condition, gives $`\Gamma\vdash v_1:S`. So each occurrence of $`x` can be replaced by a derivation for $`v_1`. Further Reading states the resulting substitution lemma.

*Proposition 29.4 (The condition is needed).* Let $`\textsf{T-LetGen}^{-}` be T-LetGen without its last premise, and let

$$`u=\mathsf{let}\ f=\lambda y.(\mathsf{let}\ k=y\ \mathsf{in}\ k)\ \mathsf{in}\ \mathsf{if}\ f\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}.`

With $`\textsf{T-LetGen}^{-}` in place of T-LetGen, $`\vdash u:\mathsf{Bool}`. Moreover $`u\to^*\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}`, which is stuck.

The function $`\lambda y.(\mathsf{let}\ k=y\ \mathsf{in}\ k)` returns its argument, as $`\lambda x.x` does. The proof gives it the scheme $`\forall Y\,Z.Y\to Z`, which turns a number into a Boolean.

*Board case (b).* We must show $`\vdash u:\mathsf{Bool}` with $`\textsf{T-LetGen}^{-}`, and that $`u` reaches a stuck term. Write $`\Gamma_2=y{:}Y`, $`\Gamma_3=y{:}Y,k{:}\forall Y.Y` and $`\Gamma_4=f{:}\forall Y\,Z.Y\to Z`. In $`\Gamma_3` the quantifier binds the same $`Y` that is free in the type of $`y`.

1. T-VarInst with $`n=0` gives $`\Gamma_2\vdash y:Y`.
2. Quantify $`Y` at the inner let, so that $`k` receives $`\forall Y.Y`. T-LetGen would require $`\{Y\}\cap\mathrm{FV}(\Gamma_2)=\varnothing`, but $`\mathrm{FV}(\Gamma_2)=\{Y\}`. This premise fails, and $`\textsf{T-LetGen}^{-}` does not check it.
3. T-VarInst with $`Y\mapsto Z` gives $`\Gamma_3\vdash k:Z`.
4. $`\textsf{T-LetGen}^{-}`, with steps 1 and 3 as premises, gives $`\Gamma_2\vdash\mathsf{let}\ k=y\ \mathsf{in}\ k:Z`. T-Abs gives $`\vdash\lambda y.(\mathsf{let}\ k=y\ \mathsf{in}\ k):Y\to Z`.
5. The outer let has the empty context, so quantifying $`Y` and $`Z` meets the condition, and $`f` receives $`\forall Y\,Z.Y\to Z`. T-VarInst with $`Y\mapsto\mathsf{Nat}` and $`Z\mapsto\mathsf{Bool}` gives $`\Gamma_4\vdash f:\mathsf{Nat}\to\mathsf{Bool}`. T-Zero and T-App give $`\Gamma_4\vdash f\ 0:\mathsf{Bool}`. T-True, T-False and T-If give $`\Gamma_4\vdash\mathsf{if}\ f\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}:\mathsf{Bool}`. T-LetGen gives $`\vdash u:\mathsf{Bool}`.
6. Evaluate. E-LetV substitutes the abstraction for $`f` and gives $`\mathsf{if}\ (\lambda y.(\mathsf{let}\ k=y\ \mathsf{in}\ k))\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}`. E-If with E-AppAbs as its premise gives $`\mathsf{if}\ (\mathsf{let}\ k=0\ \mathsf{in}\ k)\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}`. E-If with E-LetV as its premise gives $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}`.
7. This term is stuck (C.2). It is not a value. Its guard $`0` is a value, so E-If does not apply, and $`0` is neither true nor false, so E-IfTrue and E-IfFalse do not apply. $`\square`

Only step 2 breaks a rule. Step 5 is a correct use of T-LetGen, but it generalizes a wrong type: $`\lambda y.(\mathsf{let}\ k=y\ \mathsf{in}\ k)` has no type $`\mathsf{Nat}\to\mathsf{Bool}` (Exercise 29.4). Once step 2 is allowed, Theorem 29.3 fails. With the condition, step 2 may quantify only variables that do not occur in the type $`S` of $`y`. Every instance of the scheme of $`k` is then $`S`, so every type of $`\lambda y.(\mathsf{let}\ k=y\ \mathsf{in}\ k)` has the form $`S\to S`. The instance of $`f` in step 5 is then $`\mathsf{Nat}\to\mathsf{Nat}`, the guard $`f\ 0` has type Nat, and T-If fails. So $`u` has no type.

# Generalization in inference
%%%
tag := "ch29-s4"
%%%

Session 28 computes types by constraint typing. Two rules of C.5 handle schemes. CT-VarInst gives each occurrence of a let-bound variable fresh type variables in place of the quantified ones. CT-LetGen types $`\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2` under $`\Gamma` in four steps.

1. Compute $`\Gamma\vdash t_1:S_1\mid_{\mathcal X_1}C_1`.
2. Compute $`\sigma=\mathrm{unify}(C_1)`. If unification fails, the let has no constraint typing. By [Session 28, Theorem 28.3](chapter-28/index.html#ch28-s3), unification fails exactly when $`C_1` has no unifier, and otherwise $`\sigma` is a principal unifier of $`C_1`.
3. Quantify $`\{Y_1,\ldots,Y_n\}=\mathrm{FV}(\sigma S_1)\setminus\mathrm{FV}(\sigma\Gamma)`.
4. Type $`t_2` under $`\sigma\Gamma,x{:}\forall Y_1\ldots Y_n.\sigma S_1`, and keep $`C_1\cup C_2` in the conclusion.

Step 3 is the generalization condition, checked against the solved context $`\sigma\Gamma`. In board case (a), step 1 gives $`\vdash\lambda x.x:X\to X\mid_{\{X\}}\varnothing`. Then $`\sigma=[\,]`, and step 3 quantifies $`\mathrm{FV}(X\to X)\setminus\varnothing=\{X\}`. CT-VarInst gives the two occurrences of $`\mathit{id}` the types $`Y_1\to Y_1` and $`Y_2\to Y_2`. CT-App adds $`Y_1\to Y_1=\mathsf{Nat}\to Z_1` and $`Y_2\to Y_2=\mathsf{Bool}\to Z_2`, and CT-Pair gives the pair the type $`Z_1\times Z_2`. Unification sets $`Y_1=Z_1=\mathsf{Nat}` and $`Y_2=Z_2=\mathsf{Bool}`, so the principal type is $`\mathsf{Nat}\times\mathsf{Bool}`.

The solved context matters when unification learns something about a variable of $`\Gamma`. Consider $`\lambda f.\mathsf{let}\ h=\lambda x.f\ x\ \mathsf{in}\ \{h\ 0,h\ \mathsf{true}\}`. CT-AbsInf gives $`f` a fresh variable $`F`. Under $`f{:}F`, step 1 gives $`\lambda x.f\ x:X\to Z\mid_{\{X,Z\}}\{F=X\to Z\}`, where $`X` is the type of $`x` and $`Z` the type of $`f\ x`. Step 2 gives $`\sigma=[F\mapsto X\to Z]`, so $`\sigma S_1=X\to Z` and $`\sigma\Gamma=f{:}X\to Z`. Step 3 quantifies $`\{X,Z\}\setminus\{X,Z\}=\varnothing`, and $`h` receives the type $`X\to Z`. The body then requires $`X=\mathsf{Nat}` and $`X=\mathsf{Bool}`, so the constraint set of the whole term has no unifier. This is correct: $`h` passes both arguments to the one function $`f`.

If step 3 used $`\Gamma` in place of $`\sigma\Gamma`, it would quantify $`\{X,Z\}\setminus\{F\}=\{X,Z\}`, and $`h` would receive $`\forall X\,Z.X\to Z`. The term would then be typed, and so would its application to $`\lambda n.\mathsf{iszero}\ n`. That application reaches $`\{\mathsf{true},\mathsf{iszero}\ \mathsf{true}\}` in seven steps, and this pair is stuck. The equation $`F=X\to Z` concerns the type of $`f`, which is bound outside the let. For the same reason step 4 keeps $`C_1` in the conclusion.

# Exercises
%%%
tag := "ch29-s5"
number := false
%%%

*29.1.* In CT-VarInst, give both occurrences of $`\mathit{id}` in $`\mathsf{let}\ \mathit{id}=\lambda x.x\ \mathsf{in}\ \{\mathit{id}\ 0,\mathit{id}\ \mathsf{true}\}` the same variable $`Y`. Write the constraint set of the body and run $`\mathrm{unify}` on it. Which equations conflict?

*29.2.* Let $`\Gamma=y{:}Y`. (a) Which type variables may T-LetGen quantify in $`\mathsf{let}\ k=\lambda x.y\ \mathsf{in}\ \{k\ 0,k\ \mathsf{true}\}`? Derive the type of this term under $`\Gamma`. (b) Answer the same questions for $`\mathsf{let}\ k=\lambda x.\{x,y\}\ \mathsf{in}\ \{k\ 0,k\ \mathsf{true}\}`. Which components of the result can differ?

*29.3.* Derive $`\vdash\mathsf{let}\ \mathit{id}=\lambda x.x\ \mathsf{in}\ (\mathsf{let}\ h=\mathit{id}\ \mathit{id}\ \mathsf{in}\ \{h\ 0,h\ \mathsf{true}\}):\mathsf{Nat}\times\mathsf{Bool}`. Name the instance at each occurrence of $`\mathit{id}`. Then show that $`\lambda x.x\ x` has no type.

*29.4.* With $`\textsf{T-LetGen}^{-}`, steps 1–4 of board case (b) give $`y{:}Y\vdash\mathsf{let}\ k=y\ \mathsf{in}\ k:Z`. Show that $`y{:}\mathsf{Nat}\vdash\mathsf{let}\ k=y\ \mathsf{in}\ k:\mathsf{Bool}` is not derivable, even with $`\textsf{T-LetGen}^{-}`. Which result of §29.3 fails for $`\textsf{T-LetGen}^{-}`, and at which step of which case does its proof break?

*Further problem.* Give a scheme for $`\mathit{dup}` in $`\mathsf{let}\ \mathit{dup}=\lambda x.\{x,x\}\ \mathsf{in}\ \{\mathit{dup}\ 0,\mathit{dup}\ \mathsf{true}\}`, and the type of this term. Can T-LetGen give $`\mathit{dup}` the scheme $`\forall X\,Y.X\to X\times Y`?

# Reading for the Seminar
%%%
tag := "ch29-s6"
number := false
%%%

*Definitions · 10 minutes.* Write $`\forall X.X\to X\times Y` and two of its instances. Circle the variable that never changes. Compute $`\mathrm{FV}` of the context $`y{:}Y,k{:}\forall X.X\to X\times Y`.

*Joint proof · 30 minutes.* Present board case (a), with each instance of $`\mathit{id}` in its own colour. Then present board case (b). Stop at step 2 and compute $`\mathrm{FV}(\Gamma_2)` before quantifying. Finish with the three evaluation steps.

*Proof review · 20 minutes.* Read the T-LetGen case of Lemma 29.2 and locate its one use of the generalization condition. Do Exercise 29.4. Compare the two free-variable computations for $`\lambda f.\mathsf{let}\ h=\lambda x.f\ x\ \mathsf{in}\ \{h\ 0,h\ \mathsf{true}\}` in §29.4.

*Facilitator’s hint.* Before quantifying, list the free variables of every scheme in the context, skipping the quantified variables of each scheme. A variable on that list stands for one type shared with an enclosing binder.

# Solutions and Further Reading
%%%
tag := "ch29-s7"
number := false
%%%

*29.1.* Both occurrences receive $`Y\to Y`. The body has the constraint set $`\{Y\to Y=\mathsf{Nat}\to Z_1,\ Y\to Y=\mathsf{Bool}\to Z_2\}`. The arrow case of $`\mathrm{unify}` turns it into $`Y=\mathsf{Nat}`, $`Y=Z_1`, $`Y=\mathsf{Bool}` and $`Y=Z_2`. The equations $`Y=\mathsf{Nat}` and $`Y=\mathsf{Bool}` conflict: after one of them is solved, the other becomes an equation between Nat and Bool, and $`\mathrm{unify}` fails. Fresh variables keep the two instances apart, as steps 3 and 4 of board case (a) do.

*29.2.* (a) Under $`\Gamma`, $`\lambda x.y` has type $`X\to Y`. Since $`\mathrm{FV}(\Gamma)=\{Y\}`, only $`X` may be quantified, and $`k{:}\forall X.X\to Y`. The instances $`\mathsf{Nat}\to Y` and $`\mathsf{Bool}\to Y` give the pair the type $`Y\times Y`, and the let has this type. (b) Now $`\lambda x.\{x,y\}:X\to X\times Y` and $`k{:}\forall X.X\to X\times Y`. The let has type $`(\mathsf{Nat}\times Y)\times(\mathsf{Bool}\times Y)`. The first components follow the argument. The second components are both $`Y`, the one type of $`y`.

*29.3.* Write $`\Gamma_1=\mathit{id}{:}\forall X.X\to X`. In $`\mathit{id}\ \mathit{id}`, the first occurrence takes the instance $`(Y\to Y)\to(Y\to Y)` and the second takes $`Y\to Y`. T-App gives $`\Gamma_1\vdash\mathit{id}\ \mathit{id}:Y\to Y`. Since $`\mathrm{FV}(\Gamma_1)=\varnothing`, T-LetGen may quantify $`Y`, and $`h{:}\forall Y.Y\to Y`. The body is typed as in steps 3–5 of board case (a), and two uses of T-LetGen give $`\mathsf{Nat}\times\mathsf{Bool}`. For $`\lambda x.x\ x`, T-Abs gives $`x` one type $`T_1`, and T-VarInst gives both occurrences the type $`T_1`. T-App then requires $`T_1=T_1\to S` for some $`S`. A type is never a proper part of itself, so no $`T_1` exists. In $`\mathit{id}\ \mathit{id}` the two instances are different types, and this equation does not arise.

*29.4.* Under $`y{:}\mathsf{Nat}`, T-VarInst gives $`y` only the type Nat. Any scheme for $`k` is then $`\forall Z_1\ldots Z_m.\mathsf{Nat}`, whose only instance is Nat, so the let has only the type Nat. Lemma 29.2 with $`\sigma=[Y\mapsto\mathsf{Nat},Z\mapsto\mathsf{Bool}]` would turn the first judgment into the second. So Lemma 29.2 fails for $`\textsf{T-LetGen}^{-}`. Its proof breaks in the case T-LetGen, at step 1: $`\rho\Gamma=\Gamma` needs the quantified variable $`Y` not to be free in $`\Gamma=y{:}Y`. Theorem 29.3 fails with it. By inversion of T-Abs, $`\lambda y.(\mathsf{let}\ k=y\ \mathsf{in}\ k)` has no type $`\mathsf{Nat}\to\mathsf{Bool}`, although step 5 of board case (b) gives $`f` a scheme with this instance.

*Further problem.* $`\vdash\lambda x.\{x,x\}:X\to X\times X`, so $`\mathit{dup}{:}\forall X.X\to X\times X`, and the term has type $`(\mathsf{Nat}\times\mathsf{Nat})\times(\mathsf{Bool}\times\mathsf{Bool})`. The scheme $`\forall X\,Y.X\to X\times Y` would need $`\vdash\lambda x.\{x,x\}:X\to X\times Y`. Inverting T-Abs and T-Pair gives $`x{:}X\vdash x:Y`, but T-VarInst gives $`x` only the type $`X`, and $`X\neq Y`. A quantified variable may change between uses of $`\mathit{dup}`. Within one instance, all its occurrences are replaced by the same type.

*Further reading · Typing let by substitution.* TAPL §22.7 first obtains let-polymorphism with a rule that types the body after substitution:

$$`\frac{\Gamma\vdash[x\mapsto t_1]t_2:T_2\quad\Gamma\vdash t_1:T_1}{\Gamma\vdash\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2:T_2}\;\textsf{T-LetPoly}`

It needs no schemes, but it types $`t_1` once for every occurrence of $`x`. Its second premise types $`t_1` even when $`x` does not occur. The scheme rules type $`t_1` once. Pierce then describes the scheme-based algorithm and discusses its cost.

*Further reading · Safety for the inference form.* The preservation case E-LetV for T-LetGen needs a substitution lemma for schemes: if $`\Gamma,x{:}\forall X_1\ldots X_n.T_1\vdash t_2:T_2`, $`\Gamma\vdash v_1:T_1` and $`\{X_1,\ldots,X_n\}\cap\mathrm{FV}(\Gamma)=\varnothing`, then $`\Gamma\vdash[x\mapsto v_1]t_2:T_2`. The proof is by induction on the derivation for $`t_2`. At an occurrence of $`x`, T-VarInst used an instance $`S`, and Theorem 29.3 gives $`\Gamma\vdash v_1:S`. A weakening lemma for the inference form extends this to the context of the occurrence. Its T-LetGen case first renames the quantified variables by Lemma 29.2, so that they stay out of the added bindings. Session 30 shows that with references the generalization condition is not enough, and restricts generalization to values.

*Further reading · Damas and Milner.* T-VarInst and T-LetGen are a syntax-directed form of the type system of Luis Damas and Robin Milner, “Principal type-schemes for functional programs”, POPL 1982. In that system, instantiation and generalization are separate rules. The paper proves that its inference algorithm finds a most general type scheme. Its predecessor is Robin Milner, “A theory of type polymorphism in programming”, _Journal of Computer and System Sciences_ 17 (1978).

# Sources and Formalization
%%%
tag := "ch29-notes"
number := false
%%%

Pierce, _Types and Programming Languages_ (TAPL), §22.7, describes let-polymorphism: at a let, the type variables of the right-hand side that are not free in the context are generalized, and each use of the let-bound variable receives fresh instances. Pierce explains there why variables free in the context must not be generalized. The rules T-VarInst, T-LetGen, CT-VarInst and CT-LetGen are this book’s formulation (C.5), and so are Theorem 29.3 and Propositions 29.1 and 29.4. Lemma 29.2 corresponds to Pierce’s preservation of typing under type substitution, which is stated for terms whose annotations may contain type variables. The let construct and T-Let are those of TAPL §11.5. [Source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

* *Proposition 29.1.* Formulated in this book. Paper proof only ([§29.1](chapter-29/index.html#ch29-s1)).
* *Lemma 29.2.* Corresponds to TAPL §22.1. Paper proof only ([§29.3](chapter-29/index.html#ch29-s3)).
* *Theorem 29.3.* Formulated in this book. Paper proof only ([§29.3](chapter-29/index.html#ch29-s3)).
* *Proposition 29.4.* Formulated in this book. Paper proof only ([§29.3](chapter-29/index.html#ch29-s3)).
