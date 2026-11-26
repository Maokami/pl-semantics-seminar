import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Representation Independence" =>
%%%
tag := "ch33"
file := "chapter-33"
%%%

Session 31 hid the representation of a counter behind the type $`\mathit{Counter}`. A second package of the same type can represent the count $`n` by a pair of numbers. A client unpacks either package without knowing which one it unpacked. The client of [Session 31, Proposition 31.2](chapter-31/index.html#ch31-s2) evaluates to $`\mathsf{succ}\ 0` with both packages. Does every client give the same result with both? Typing alone cannot answer. A package whose read operation always returns $`0` also has type $`\mathit{Counter}`, and the same client gives $`0` with it. This session answers the question by relating the two representations and checking the relation once for each operation.

*In this session.*

* *Definitions.* Function types, abstraction, application, typing contexts and the rules T-Var, T-Abs and T-App ([C.3](lambda-card/index.html#lambda-c3)). Natural numbers ([C.2](lambda-card/index.html#lambda-c2)) and pairs and projections ([C.4](lambda-card/index.html#lambda-c4)), used only to write the packages of §33.1. Packages, existential types, unpacking, the abstract type and the escape condition ([C.7](lambda-card/index.html#lambda-c7)). The interface $`\mathit{Counter}=\{\exists X,T_{\mathrm c}\}`, the package $`\mathit{counter}` and the client of Proposition 31.2 ([Session 31, §31.2](chapter-31/index.html#ch31-s2)). Structural induction ([Session 1, §1.1](chapter-01/index.html#ch01-s1)) and induction on derivations ([Session 1, §1.5](chapter-01/index.html#ch01-s5)). This session adds Definitions 33.1 and 33.3–33.5.
* *New terms.* Environment, meaning of a type and of a term, logical relation, fundamental theorem, representation independence. [Glossary](glossary/index.html)
* *Theorem 33.6 (Fundamental theorem) and Corollary 33.7 (Representation independence).* (33.6) Fix sets $`A,A'` and a relation $`R\subseteq A\times A'`. For every derivation of $`\Gamma\vdash t:T` in the client fragment and all environments $`\rho` for $`\Gamma` at $`A` and $`\rho'` for $`\Gamma` at $`A'`: if $`\rho\mathrel{R_\Gamma}\rho'`, then $`\llbracket t\rrbracket_A\rho\mathrel{R_T}\llbracket t\rrbracket_{A'}\rho'`. (33.7) Let $`\rho` and $`\rho'` be environments for the counter context $`\Gamma_{\mathrm{ctr}}` at $`A` and $`A'`. Suppose $`R` relates the two start values, the two increments map related elements to related elements, and the two read operations map related elements to equal numbers. Then $`\llbracket t\rrbracket_A\rho=\llbracket t\rrbracket_{A'}\rho'` for every $`t` with $`\Gamma_{\mathrm{ctr}}\vdash t:\mathsf{Nat}`. The natural counter and the pair counter satisfy these conditions with $`n\approx(a,b)\iff n=a`.
* *Board case.* The counter (§33.4). Write the two implementations as environments $`\rho_{\mathrm N}` (representation $`\mathbb N`) and $`\rho_{\mathrm P}` (representation $`\mathbb N\times\mathbb N`), and the relation $`n\approx(a,b)\iff n=a`. Prove in five numbered steps that the two increments are related at $`X\to X`. The start value and the read operation take one line each.
* *Proof outline.* Give each type a set and each typed term an element of that set (Definition 33.4). Lift $`R` to every type: $`R` itself at $`X`, equality at Nat, and at an arrow type, related arguments give related results (Definition 33.5). Theorem 33.6 is proved by induction on the typing derivation. Its induction property quantifies over related environments, because the abstraction case applies the induction hypothesis to two extended environments. For Corollary 33.7, the three conditions say exactly that the two environments are related, and the relation at Nat is equality.
* *From Session 32.* Part 2 ended with the safety table: a well-typed term does not get stuck. This session opens Part 3. Each entry concerned one term and its evaluation. This session compares two programs: do two packages of the same type give the same result to every client? The proof is again an induction on typing derivations, now with a property that relates two meanings of one term. Session 31 showed that a client cannot use the representation type. This session proves what that restriction guarantees.

# Two counters and a relation
%%%
tag := "ch33-s1"
%%%

[Session 31, §31.2](chapter-31/index.html#ch31-s2) defined the interface and the first package:

$$`T_{\mathrm c}=X\times((X\to X)\times(X\to\mathsf{Nat})),\qquad\mathit{Counter}=\{\exists X,T_{\mathrm c}\},\qquad\mathit{counter}=\{{*}\mathsf{Nat},v_0\}\ \mathsf{as}\ \mathit{Counter},`

where $`v_0=\{0,\{\mathit{inc},\mathit{read}\}\}`, $`\mathit{inc}=\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x` and $`\mathit{read}=\lambda x{:}\mathsf{Nat}.x`. The second package keeps the count in the first component of a pair. The second component also counts the increments, and no operation reads it.

$$`\mathit{inc}'=\lambda y{:}\mathsf{Nat}\times\mathsf{Nat}.\{\mathsf{succ}\ y.1,\ \mathsf{succ}\ y.2\},\qquad\mathit{read}'=\lambda y{:}\mathsf{Nat}\times\mathsf{Nat}.y.1,`

$$`v_0'=\{\{0,0\},\{\mathit{inc}',\mathit{read}'\}\},\qquad\mathit{counter}'=\{{*}\mathsf{Nat}\times\mathsf{Nat},v_0'\}\ \mathsf{as}\ \mathit{Counter}.`

The typing rules of C.2–C.4 give $`v_0'` the type $`[X\mapsto\mathsf{Nat}\times\mathsf{Nat}]T_{\mathrm c}`, so T-Pack gives $`\vdash\mathit{counter}':\mathit{Counter}`. The client $`\mathsf{let}\ \{X,c\}=\mathit{counter}'\ \mathsf{in}\ c.2.2\ (c.2.1\ c.1)` reaches $`\{\mathsf{succ}\ 0,\mathsf{succ}\ 0\}.1` and then the value $`\mathsf{succ}\ 0`, as the client of Proposition 31.2 does with $`\mathit{counter}`.

Read Nat as the set $`\mathbb N` and pairs as ordered pairs. The *natural counter* has the start value $`0\in\mathbb N`, the increment $`n\mapsto n+1` and the read operation $`n\mapsto n`. The *pair counter* has the start value $`(0,0)\in\mathbb N\times\mathbb N`, the increment $`(a,b)\mapsto(a+1,b+1)` and the read operation $`(a,b)\mapsto a`. A number $`n` and a pair $`(a,b)` represent the same count when $`n=a`. Write

$$`n\approx(a,b)\iff n=a\qquad(n,a,b\in\mathbb N).`

So $`3\approx(3,3)` and also $`3\approx(3,0)`: the relation ignores the second component, which no operation reads. The start values are related, since $`0\approx(0,0)`. The two increments map related elements to related elements, and the two read operations give equal numbers on related elements. §33.4 checks these facts in detail.

A client that only increments and reads can be described without terms.

*Definition 33.1 (Client trees).* A *client tree* $`k` is built by the grammar

$$`k ::= \mathsf{done}\mid\mathsf{adv}\ k\mid\mathsf{test}\ k\ k`

Let $`A` be a set with functions $`f:A\to A` (the increment) and $`g:A\to\mathbb N` (the read operation). The *counter observation* $`\mathrm{obs}(k,d)\in\mathbb N` of a tree $`k` from an element $`d\in A` (an observation in the sense of [Session 7, §7.1](chapter-07/index.html#ch07-s1)) is defined by structural recursion on $`k`:

$$`\begin{aligned}
\mathrm{obs}(\mathsf{done},d)&=g(d),\\
\mathrm{obs}(\mathsf{adv}\ k_1,d)&=\mathrm{obs}(k_1,f(d)),\\
\mathrm{obs}(\mathsf{test}\ k_1\ k_2,d)&=\mathrm{obs}(k_1,d)\text{ if }g(d)=0,\text{ and }\mathrm{obs}(k_2,d)\text{ otherwise.}
\end{aligned}`

For a second set $`A'` with $`f':A'\to A'` and $`g':A'\to\mathbb N`, write $`\mathrm{obs}'` for the observation built from $`f'` and $`g'`.

For example, take $`k=\mathsf{test}\ (\mathsf{adv}\ \mathsf{done})\ \mathsf{done}` and the natural counter from $`0`. The reading $`g(0)` is $`0`, so $`\mathrm{obs}(k,0)=\mathrm{obs}(\mathsf{adv}\ \mathsf{done},0)=\mathrm{obs}(\mathsf{done},1)=1`. For the pair counter from $`(0,0)`, the reading is $`0` as well, and $`\mathrm{obs}'(k,(0,0))=\mathrm{obs}'(\mathsf{done},(1,1))=1`.

*Proposition 33.2 (Client trees agree on related elements).* Let $`A,f,g` and $`A',f',g'` be as in Definition 33.1, and let $`R\subseteq A\times A'`. Suppose that for all $`d\in A` and $`d'\in A'` with $`d\mathrel{R}d'`, both $`f(d)\mathrel{R}f'(d')` and $`g(d)=g'(d')`. Then $`\mathrm{obs}(k,d)=\mathrm{obs}'(k,d')` for every client tree $`k` and all $`d\mathrel{R}d'`.

*Proof.* By structural induction on $`k`, with the induction property

$$`Q(k)\coloneqq\forall d\in A,\ \forall d'\in A',\ d\mathrel{R}d'\Rightarrow\mathrm{obs}(k,d)=\mathrm{obs}'(k,d').`

For $`\mathsf{done}`, fix $`d\mathrel{R}d'`. The second assumption gives $`g(d)=g'(d')`, which is the claim. For $`\mathsf{adv}\ k_1`, fix $`d\mathrel{R}d'`. The first assumption gives $`f(d)\mathrel{R}f'(d')`, and $`Q(k_1)` applied to this new pair gives $`\mathrm{obs}(k_1,f(d))=\mathrm{obs}'(k_1,f'(d'))`, which is the claim. For $`\mathsf{test}\ k_1\ k_2`, fix $`d\mathrel{R}d'`. Since $`g(d)=g'(d')`, both sides choose the same subtree $`k_i`, and $`Q(k_i)` applied to $`(d,d')` gives the claim. $`\square`

The case $`\mathsf{adv}\ k_1` uses the induction hypothesis at a new pair of elements. So $`Q(k)` must quantify over all related pairs, not only over the start values. For the two counters, take $`R` to be $`\approx` and start from $`0\approx(0,0)`.

The Lean code below checks Proposition 33.2. Reading it is optional. Its three tree forms are, in order, $`\mathsf{done}`, $`\mathsf{adv}` and $`\mathsf{test}`. A set is a Lean type, and a relation is a predicate on two arguments.

```lean
namespace CounterClients
inductive Client where
  | read
  | next (rest : Client)
  | branchZero (yes no : Client)

def observe {S : Type} (step : S → S) (readout : S → Nat) :
    Client → S → Nat
  | .read, s => readout s
  | .next k, s => observe step readout k (step s)
  | .branchZero yes no, s =>
    if readout s = 0 then observe step readout yes s
    else observe step readout no s

theorem simulation {S T : Type} (ss : S → S) (ts : T → T)
    (sr : S → Nat) (tr : T → Nat) (R : S → T → Prop)
    (stepEq : ∀ s t, R s t → R (ss s) (ts t))
    (readEq : ∀ s t, R s t → sr s = tr t)
    (k : Client) (s : S) (t : T) (h : R s t) :
    observe ss sr k s = observe ts tr k t := by
  induction k generalizing s t with
  | read => exact readEq s t h
  | next k ih => exact ih _ _ (stepEq s t h)
  | branchZero yes no ihYes ihNo =>
    simp only [observe, readEq s t h]
    split
    · exact ihYes _ _ h
    · exact ihNo _ _ h
end CounterClients
```

# Meaning of types and terms
%%%
tag := "ch33-s2"
%%%

A client tree cannot hand an operation to a function. The following term does. Its variables $`\mathit{start}`, $`\mathit{tick}` and $`\mathit{get}` stand for the start value, the increment and the read operation. It passes the increment to a function that applies its argument twice:

$$`t_{\mathrm h}=\mathit{get}\ (u\ \mathit{tick}),\qquad u=\lambda h{:}X\to X.\,h\ (h\ \mathit{start}).`

To compare the results of such clients, each type gets a set and each term an element of that set.

*Definition 33.3 (Client fragment).* The types and terms of the *client fragment* are

$$`T ::= X\mid\mathsf{Nat}\mid T\to T\qquad\qquad t ::= x\mid\lambda x{:}T.t\mid t\ t`

Here $`X` is one fixed type variable. The typing judgment $`\Gamma\vdash t:T` is derived by T-Var, T-Abs and T-App of [C.3](lambda-card/index.html#lambda-c3), with contexts that bind term variables only. The type $`X` behaves like a base type. It stands for the abstract type in the body of an unpacking ([C.7](lambda-card/index.html#lambda-c7)). The *counter context* is

$$`\Gamma_{\mathrm{ctr}}=\mathit{start}{:}X,\ \mathit{tick}{:}X\to X,\ \mathit{get}{:}X\to\mathsf{Nat}.`

A *client body* is a term $`t` with $`\Gamma_{\mathrm{ctr}}\vdash t:T` for some type $`T` of the fragment.

A client $`\mathsf{let}\ \{X,c\}=p\ \mathsf{in}\ t_2` of Session 31 uses the package through $`c.1`, $`c.2.1` and $`c.2.2`. Suppose $`t_2` uses $`c` only in these three forms and lies otherwise in the fragment. Replacing the three forms by $`\mathit{start}`, $`\mathit{tick}` and $`\mathit{get}` gives a client body. The body $`c.2.2\ (c.2.1\ c.1)` of Proposition 31.2 becomes $`\mathit{get}\ (\mathit{tick}\ \mathit{start})`.

For example, $`\Gamma_{\mathrm{ctr}}\vdash t_{\mathrm h}:\mathsf{Nat}`. T-Var and T-App twice give $`\Gamma_{\mathrm{ctr}},h{:}X\to X\vdash h\ (h\ \mathit{start}):X`. T-Abs gives $`\Gamma_{\mathrm{ctr}}\vdash u:(X\to X)\to X`. T-App with $`\mathit{tick}:X\to X` gives $`u\ \mathit{tick}:X`, and T-App with $`\mathit{get}:X\to\mathsf{Nat}` gives the type Nat.

*Definition 33.4 (Meaning).* Let $`A` be a set, the meaning of $`X`. The *meaning* of a type is a set:

$$`\llbracket X\rrbracket_A=A,\qquad\llbracket\mathsf{Nat}\rrbracket_A=\mathbb N,\qquad\llbracket T_1\to T_2\rrbracket_A=\text{the set of all functions from }\llbracket T_1\rrbracket_A\text{ to }\llbracket T_2\rrbracket_A.`

An *environment* for a context $`\Gamma` at $`A` is a function $`\rho` on $`\mathrm{dom}(\Gamma)` with $`\rho(x)\in\llbracket T\rrbracket_A` for each binding $`x{:}T` of $`\Gamma`. The environment $`\rho[x\mapsto d]` maps $`x` to $`d` and agrees with $`\rho` at every other variable. For a derivation of $`\Gamma\vdash t:T` and an environment $`\rho` for $`\Gamma` at $`A`, the *meaning* $`\llbracket t\rrbracket_A\rho\in\llbracket T\rrbracket_A` is defined by recursion on the derivation, with one clause for each rule:

$$`\begin{aligned}
\llbracket x\rrbracket_A\rho&=\rho(x)&&\textsf{T-Var}\\
\llbracket\lambda x{:}T_1.t_2\rrbracket_A\rho&=\text{the function }d\mapsto\llbracket t_2\rrbracket_A(\rho[x\mapsto d])\text{ on }\llbracket T_1\rrbracket_A&&\textsf{T-Abs}\\
\llbracket t_1\ t_2\rrbracket_A\rho&=(\llbracket t_1\rrbracket_A\rho)(\llbracket t_2\rrbracket_A\rho)&&\textsf{T-App}
\end{aligned}`

Each clause gives an element of the right set. At T-Var, the binding $`x{:}T` of $`\Gamma` gives $`\rho(x)\in\llbracket T\rrbracket_A`. At T-Abs, $`\rho[x\mapsto d]` is an environment for $`\Gamma,x{:}T_1` for each $`d\in\llbracket T_1\rrbracket_A`, since $`x\notin\mathrm{dom}(\Gamma)` (C.3). So the body has a meaning in $`\llbracket T_2\rrbracket_A`. At T-App, the operator means a function from $`\llbracket T_{11}\rrbracket_A` to $`\llbracket T_{12}\rrbracket_A`, and the operand means an element of $`\llbracket T_{11}\rrbracket_A`. Every function counts, and the fragment has no recursion, so every typed term has a meaning. The meaning does not evaluate the term. It reads the term as a description of an element of a set.

The two counters of §33.1 give two environments for $`\Gamma_{\mathrm{ctr}}`, one at $`\mathbb N` and one at $`\mathbb N\times\mathbb N`:

$$`\rho_{\mathrm N}:\quad\mathit{start}\mapsto 0,\quad\mathit{tick}\mapsto(n\mapsto n+1),\quad\mathit{get}\mapsto(n\mapsto n),`

$$`\rho_{\mathrm P}:\quad\mathit{start}\mapsto(0,0),\quad\mathit{tick}\mapsto((a,b)\mapsto(a+1,b+1)),\quad\mathit{get}\mapsto((a,b)\mapsto a).`

Compute the meaning of $`t_{\mathrm h}` in both. In the environment $`\rho_{\mathrm N}[h\mapsto\varphi]`, the body $`h\ (h\ \mathit{start})` means $`\varphi(\varphi(0))`. So $`\llbracket u\rrbracket_{\mathbb N}\rho_{\mathrm N}` is the function $`\varphi\mapsto\varphi(\varphi(0))` on the functions from $`\mathbb N` to $`\mathbb N`. Applied to $`n\mapsto n+1` it gives $`2`, and the read operation gives $`\llbracket t_{\mathrm h}\rrbracket_{\mathbb N}\rho_{\mathrm N}=2`. In the same way, $`\llbracket u\rrbracket_{\mathbb N\times\mathbb N}\rho_{\mathrm P}` is the function $`\varphi'\mapsto\varphi'(\varphi'((0,0)))` on the functions from $`\mathbb N\times\mathbb N` to itself. Applied to the increment it gives $`(2,2)`, and the read operation gives $`\llbracket t_{\mathrm h}\rrbracket_{\mathbb N\times\mathbb N}\rho_{\mathrm P}=2`. The two meanings of $`u` are functions on different sets, so they are not equal. Yet $`t_{\mathrm h}` gives the same number. §33.3 says how the two meanings of $`u` correspond.

# The logical relation and the fundamental theorem
%%%
tag := "ch33-s3"
%%%

Fix two sets $`A,A'` and a relation $`R\subseteq A\times A'`. In the example, $`A=\mathbb N`, $`A'=\mathbb N\times\mathbb N` and $`R` is $`\approx`.

*Definition 33.5 (Logical relation).* For each type $`T` of the fragment, a relation $`R_T\subseteq\llbracket T\rrbracket_A\times\llbracket T\rrbracket_{A'}` is defined by recursion on $`T`:

$$`R_X=R,\qquad R_{\mathsf{Nat}}=\{(n,n)\mid n\in\mathbb N\},`

$$`\varphi\mathrel{R_{T_1\to T_2}}\varphi'\iff\text{for all }d\in\llbracket T_1\rrbracket_A\text{ and }d'\in\llbracket T_1\rrbracket_{A'},\ d\mathrel{R_{T_1}}d'\Rightarrow\varphi(d)\mathrel{R_{T_2}}\varphi'(d').`

The family of relations $`R_T` is the *logical relation* built from $`R`. Environments $`\rho` for $`\Gamma` at $`A` and $`\rho'` for $`\Gamma` at $`A'` are *related*, written $`\rho\mathrel{R_\Gamma}\rho'`, if $`\rho(x)\mathrel{R_T}\rho'(x)` for every binding $`x{:}T` of $`\Gamma`.

At $`X` the logical relation is the chosen relation. At Nat it is equality, because a number is what a client observes. At an arrow type it says that related arguments give related results. The arrow clause uses only $`R_{T_1}` and $`R_{T_2}` at the smaller types, so the recursion is well founded.

Take $`R` to be $`\approx` and write $`\approx_T` for $`R_T`. Unfold the arrow clause. Then $`\rho_{\mathrm N}(\mathit{tick})\approx_{X\to X}\rho_{\mathrm P}(\mathit{tick})` says that the two increments map related elements to related elements, and $`\rho_{\mathrm N}(\mathit{get})\approx_{X\to\mathsf{Nat}}\rho_{\mathrm P}(\mathit{get})` says that the two read operations give equal numbers on related elements. These are the two assumptions of Proposition 33.2. So $`\rho_{\mathrm N}\approx_{\Gamma_{\mathrm{ctr}}}\rho_{\mathrm P}` says that the start values are related and that both assumptions hold.

*Theorem 33.6 (Fundamental theorem).* For all sets $`A,A'`, every relation $`R\subseteq A\times A'`, every derivation of $`\Gamma\vdash t:T` in the client fragment, and all environments $`\rho` for $`\Gamma` at $`A` and $`\rho'` for $`\Gamma` at $`A'`: if $`\rho\mathrel{R_\Gamma}\rho'`, then $`\llbracket t\rrbracket_A\rho\mathrel{R_T}\llbracket t\rrbracket_{A'}\rho'`.

The theorem is called the *fundamental theorem* of the logical relation: every well-typed term is related to itself. Fix $`A`, $`A'` and $`R`. We prove $`P(D)` for every derivation $`D` by induction on $`D`, with the induction property

$$`P(D)\coloneqq\forall\rho,\rho',\ \rho\mathrel{R_\Gamma}\rho'\Rightarrow\llbracket t\rrbracket_A\rho\mathrel{R_T}\llbracket t\rrbracket_{A'}\rho'.`

Read $`\Gamma,t,T` from the conclusion $`\Gamma\vdash t:T` of $`D`. The variables $`\rho` and $`\rho'` range over the environments for $`\Gamma` at $`A` and at $`A'`.

*Variable.* Suppose $`D` ends with T-Var. Then $`t=x` with $`x{:}T` in $`\Gamma`. Fix $`\rho\mathrel{R_\Gamma}\rho'`. The two meanings are $`\rho(x)` and $`\rho'(x)`, and $`\rho(x)\mathrel{R_T}\rho'(x)` because the environments are related.

*Application.* Suppose $`D` ends with T-App. Then $`t=t_1\ t_2` and $`T=T_{12}`, and the premises are $`D_1:\Gamma\vdash t_1:T_{11}\to T_{12}` and $`D_2:\Gamma\vdash t_2:T_{11}`. Their induction hypotheses are

$$`\begin{aligned}
P(D_1)&:\quad\forall\rho,\rho',\ \rho\mathrel{R_\Gamma}\rho'\Rightarrow\llbracket t_1\rrbracket_A\rho\mathrel{R_{T_{11}\to T_{12}}}\llbracket t_1\rrbracket_{A'}\rho',\\
P(D_2)&:\quad\forall\rho,\rho',\ \rho\mathrel{R_\Gamma}\rho'\Rightarrow\llbracket t_2\rrbracket_A\rho\mathrel{R_{T_{11}}}\llbracket t_2\rrbracket_{A'}\rho'.
\end{aligned}`

Fix $`\rho\mathrel{R_\Gamma}\rho'`. $`P(D_1)` relates the two meanings of $`t_1` at $`T_{11}\to T_{12}`, and $`P(D_2)` relates the two meanings of $`t_2` at $`T_{11}`. The arrow clause, applied to the second pair, gives $`(\llbracket t_1\rrbracket_A\rho)(\llbracket t_2\rrbracket_A\rho)\mathrel{R_{T_{12}}}(\llbracket t_1\rrbracket_{A'}\rho')(\llbracket t_2\rrbracket_{A'}\rho')`. By Definition 33.4 these are the two meanings of $`t_1\ t_2`.

*Abstraction.* Suppose $`D` ends with T-Abs. Then $`t=\lambda x{:}T_1.t_2` and $`T=T_1\to T_2`, and the premise is $`D_2:\Gamma,x{:}T_1\vdash t_2:T_2`. Its induction hypothesis is

$$`P(D_2):\quad\forall\eta,\eta',\ \eta\mathrel{R_{\Gamma,x:T_1}}\eta'\Rightarrow\llbracket t_2\rrbracket_A\eta\mathrel{R_{T_2}}\llbracket t_2\rrbracket_{A'}\eta'.`

1. Fix $`\rho\mathrel{R_\Gamma}\rho'`. By the arrow clause we must show: for all $`d\in\llbracket T_1\rrbracket_A` and $`d'\in\llbracket T_1\rrbracket_{A'}` with $`d\mathrel{R_{T_1}}d'`, we have $`\llbracket t_2\rrbracket_A(\rho[x\mapsto d])\mathrel{R_{T_2}}\llbracket t_2\rrbracket_{A'}(\rho'[x\mapsto d'])`. Fix such $`d` and $`d'`.
2. The extended environments are related at $`\Gamma,x{:}T_1`. At $`x` they give $`d` and $`d'`, which are related at $`T_1`. At each binding $`y{:}S` of $`\Gamma` they give $`\rho(y)` and $`\rho'(y)`, because $`y\neq x`, and these are related at $`S` because $`\rho\mathrel{R_\Gamma}\rho'`.
3. $`P(D_2)` with $`\eta=\rho[x\mapsto d]` and $`\eta'=\rho'[x\mapsto d']` gives the claim of step 1. $`\square`

The abstraction case applies the induction hypothesis to the extended environments, not to $`\rho` and $`\rho'`. This is why $`P(D)` quantifies over environments. In the same way, $`Q(k)` in Proposition 33.2 quantified over related elements, and [Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2) quantified the final state inside its induction property.

The Lean code below checks Theorem 33.6. Reading it is optional. It represents a typing derivation directly, as a term indexed by its context and its type. A variable is represented by its position in the context, counted from the most recent binding, so variable names play no role. The types are the abstract type, Nat and arrows. A set is a Lean type, and the meaning of an arrow type is the Lean function type. The meaning of types, environments and their extension, the meaning of terms, the logical relation and related environments follow Definitions 33.4 and 33.5. The last declaration is Theorem 33.6, and its three cases are the three cases above.

```lean
namespace TypedCounter

inductive Ty where
  | rep | nat | arr (a b : Ty)

def Val (S : Type) : Ty → Type
  | .rep => S
  | .nat => Nat
  | .arr a b => Val S a → Val S b

def Rel {S T : Type} (R : S → T → Prop) :
    (a : Ty) → Val S a → Val T a → Prop
  | .rep => R
  | .nat => Eq
  | .arr a b => fun f g =>
      ∀ x y, Rel R a x y → Rel R b (f x) (g y)

inductive Var : List Ty → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

inductive Term : List Ty → Ty → Type where
  | var : Var Γ a → Term Γ a
  | lam : Term (a :: Γ) b → Term Γ (.arr a b)
  | app : Term Γ (.arr a b) → Term Γ a → Term Γ b

abbrev Env (S : Type) (Γ : List Ty) :=
  ∀ {a}, Var Γ a → Val S a

def extend (ρ : Env S Γ) (x : Val S a) : Env S (a :: Γ)
  | _, .here => x
  | _, .there i => ρ i

def denote {S : Type} : Term Γ a → Env S Γ → Val S a
  | .var i, ρ => ρ i
  | .lam body, ρ => fun x => denote body (extend ρ x)
  | .app f u, ρ => denote f ρ (denote u ρ)

def EnvRel (R : S → T → Prop) (ρ : Env S Γ) (η : Env T Γ) :=
  ∀ {a} (i : Var Γ a), Rel R a (ρ i) (η i)

theorem fundamental (R : S → T → Prop) (e : Term Γ a)
    (ρ : Env S Γ) (η : Env T Γ) (h : EnvRel R ρ η) :
    Rel R a (denote e ρ) (denote e η) := by
  induction e with
  | var i => exact h i
  | app f u ihf ihu => exact ihf ρ η h _ _ (ihu ρ η h)
  | lam body ih =>
    intro x y hxy
    apply ih (extend ρ x) (extend η y)
    intro t i
    cases i with
    | here => exact hxy
    | there j => exact h j

end TypedCounter
```

# Representation independence
%%%
tag := "ch33-s4"
%%%

Two implementations of an abstract type are *representation independent* when every client gives the same observable result with either of them. Here an implementation of the counter is an environment for $`\Gamma_{\mathrm{ctr}}`, and the observable result of a client body of type Nat is its meaning, a number.

*Corollary 33.7 (Representation independence).* Let $`\rho` and $`\rho'` be environments for $`\Gamma_{\mathrm{ctr}}` at sets $`A` and $`A'`, and let $`R\subseteq A\times A'`. Suppose

* (i) $`\rho(\mathit{start})\mathrel{R}\rho'(\mathit{start})`;
* (ii) for all $`d\in A` and $`d'\in A'` with $`d\mathrel{R}d'`: $`\rho(\mathit{tick})(d)\mathrel{R}\rho'(\mathit{tick})(d')`;
* (iii) for all $`d\in A` and $`d'\in A'` with $`d\mathrel{R}d'`: $`\rho(\mathit{get})(d)=\rho'(\mathit{get})(d')`.

Then $`\llbracket t\rrbracket_A\rho=\llbracket t\rrbracket_{A'}\rho'` for every client body $`t` with $`\Gamma_{\mathrm{ctr}}\vdash t:\mathsf{Nat}`. The conditions hold for $`\rho_{\mathrm N}`, $`\rho_{\mathrm P}` and $`\approx`.

*Proof.* By Definition 33.5, $`\rho\mathrel{R_{\Gamma_{\mathrm{ctr}}}}\rho'` requires $`\rho(\mathit{start})\mathrel{R_X}\rho'(\mathit{start})`, $`\rho(\mathit{tick})\mathrel{R_{X\to X}}\rho'(\mathit{tick})` and $`\rho(\mathit{get})\mathrel{R_{X\to\mathsf{Nat}}}\rho'(\mathit{get})`. Since $`R_X=R` and $`R_{\mathsf{Nat}}` is equality, the arrow clause turns these three requirements into (i), (ii) and (iii). So $`\rho\mathrel{R_{\Gamma_{\mathrm{ctr}}}}\rho'`. Theorem 33.6 with $`\Gamma=\Gamma_{\mathrm{ctr}}` and $`T=\mathsf{Nat}` gives $`\llbracket t\rrbracket_A\rho\mathrel{R_{\mathsf{Nat}}}\llbracket t\rrbracket_{A'}\rho'`, which is the claimed equality. It remains to check (i)–(iii) for the two counters.

The quantifier over clients in Corollary 33.7 ranges over the typed fragment of Definition 33.3. In that fragment a client can manipulate the hidden type through the supplied operations. At the hidden type $`X` the two representations need only be related; at the observable type $`\mathsf{Nat}` the relation is equality. Extending this result to clients using references or type abstraction would require cases for those constructs in the fundamental theorem.

*Board case: the increment.* We must show (ii) for $`\rho_{\mathrm N}`, $`\rho_{\mathrm P}` and $`\approx`, that is, $`\rho_{\mathrm N}(\mathit{tick})\approx_{X\to X}\rho_{\mathrm P}(\mathit{tick})`.

1. Here $`A=\mathbb N` and $`A'=\mathbb N\times\mathbb N`. Fix $`n\in\mathbb N` and $`(a,b)\in\mathbb N\times\mathbb N` with $`n\approx(a,b)`. By the definition of $`\approx`, $`n=a`.
2. By the definitions of $`\rho_{\mathrm N}` and $`\rho_{\mathrm P}`, $`\rho_{\mathrm N}(\mathit{tick})(n)=n+1` and $`\rho_{\mathrm P}(\mathit{tick})(a,b)=(a+1,b+1)`.
3. By the definition of $`\approx`, $`n+1\approx(a+1,b+1)` holds if and only if $`n+1=a+1`.
4. From $`n=a` in step 1, $`n+1=a+1`. So $`n+1\approx(a+1,b+1)`.
5. The numbers $`n,a,b` were arbitrary, so (ii) holds.

*Start value.* (i) is $`0\approx(0,0)`, which holds because $`0=0`. *Read operation.* For (iii), fix $`n\approx(a,b)`, so $`n=a`. Then $`\rho_{\mathrm N}(\mathit{get})(n)=n` and $`\rho_{\mathrm P}(\mathit{get})(a,b)=a`, and these are equal. $`\square`

For the client body $`t_{\mathrm h}` of §33.2, Corollary 33.7 gives $`\llbracket t_{\mathrm h}\rrbracket_{\mathbb N}\rho_{\mathrm N}=\llbracket t_{\mathrm h}\rrbracket_{\mathbb N\times\mathbb N}\rho_{\mathrm P}` without computing either side. §33.2 computed $`2` for both. Inside the proof, Theorem 33.6 relates the two meanings of $`u` at $`(X\to X)\to X`: the functions $`\varphi\mapsto\varphi(\varphi(0))` and $`\varphi'\mapsto\varphi'(\varphi'((0,0)))` map related increments to related elements (Exercise 33.1).

*What the corollary does not say.* First, the result type matters. The client body $`\mathit{start}` has type $`X`. Theorem 33.6 gives only $`0\approx(0,0)`, and the two meanings, a number and a pair, differ. The escape condition of Session 31 rejects every client whose result type mentions $`X`. For a type $`T` without $`X`, the relation $`R_T` is equality (Exercise 33.3). So every client body whose type satisfies the escape condition has equal meanings in related environments.

Second, the corollary compares meanings, not evaluations. Suppose we want to conclude that every client evaluates to the same value with $`\mathit{counter}` and with $`\mathit{counter}'`. We also need that the evaluation of a client computes its meaning. Sessions 36–37 prove a theorem of this kind, adequacy, for PCF. For the client of Proposition 31.2 the two agree: it evaluates to $`\mathsf{succ}\ 0` with both packages, and its body $`\mathit{get}\ (\mathit{tick}\ \mathit{start})` means $`1` in both environments.

Third, the fragment is small. Numbers and pairs each add cases to the proof of Theorem 33.6 (Exercises 33.3 and 33.4). Recursion needs the domains of Sessions 34–35. Type abstraction is discussed under Further Reading.

Fourth, the relation must be found. Theorem 33.6 holds for every $`R`, but the corollary needs an $`R` that satisfies (i)–(iii). If some client body of type Nat has different meanings in $`\rho` and $`\rho'`, then no such relation exists (Exercise 33.2).

# Exercises
%%%
tag := "ch33-s5"
number := false
%%%

*33.1.* Let $`u=\lambda h{:}X\to X.\,h\ (h\ \mathit{start})`. (a) Show directly from Definition 33.5 that $`\llbracket u\rrbracket_{\mathbb N}\rho_{\mathrm N}\approx_{(X\to X)\to X}\llbracket u\rrbracket_{\mathbb N\times\mathbb N}\rho_{\mathrm P}`. (b) What does Theorem 33.6 give for the client body $`\mathit{tick}\ \mathit{start}`? Is it an equality?

*33.2.* Let $`\rho_{\mathrm Z}` agree with $`\rho_{\mathrm P}` except that $`\rho_{\mathrm Z}(\mathit{get})` is the constant function $`(a,b)\mapsto 0`. (a) Find a client body of type Nat whose meanings in $`\rho_{\mathrm N}` and $`\rho_{\mathrm Z}` differ. (b) Conclude that no relation $`R\subseteq\mathbb N\times(\mathbb N\times\mathbb N)` satisfies (i)–(iii) of Corollary 33.7 for $`\rho_{\mathrm N}` and $`\rho_{\mathrm Z}`. (c) For $`R` equal to $`\approx`, which condition fails, and at which pair?

*33.3.* (a) Show by induction on $`T`: if $`X` does not occur in $`T`, then $`\llbracket T\rrbracket_A=\llbracket T\rrbracket_{A'}` and $`R_T` is equality on this set. (b) Add the constant $`0` and the form $`\mathsf{succ}\ t` of [C.2](lambda-card/index.html#lambda-c2) to the fragment, with the rules T-Zero and T-Succ and the meanings $`\llbracket 0\rrbracket_A\rho=0` and $`\llbracket\mathsf{succ}\ t_1\rrbracket_A\rho=\llbracket t_1\rrbracket_A\rho+1`. Prove the two new cases of Theorem 33.6.

*33.4.* Add the product type $`T\times T`, pairs and projections of [C.4](lambda-card/index.html#lambda-c4) to the fragment, with $`\llbracket T_1\times T_2\rrbracket_A=\llbracket T_1\rrbracket_A\times\llbracket T_2\rrbracket_A`. Give the clause for $`R_{T_1\times T_2}` and prove the cases T-Pair and T-Proj1. Then show that the two packages of §33.1 give related environments for the context $`c{:}T_{\mathrm c}`.

*Further problem.* A third package of type $`\mathit{Counter}` has the representation type Nat, the start value $`\mathsf{succ}\ 0`, the increment $`\lambda x{:}\mathsf{Nat}.\mathsf{succ}\ x` and the read operation $`\lambda x{:}\mathsf{Nat}.\mathsf{pred}\ x`. As sets, its start value is $`1`, its increment is $`m\mapsto m+1`, and its read operation maps $`m` to $`m-1` when $`m\geq 1` and $`0` to $`0`. Find a relation between the natural counter and this counter that satisfies (i)–(iii), and conclude for client trees and for client bodies. Is equality on $`\mathbb N` such a relation?

# Reading for the Seminar
%%%
tag := "ch33-s6"
number := false
%%%

*Definitions · 10 minutes.* Write the two counters as the environments $`\rho_{\mathrm N}` and $`\rho_{\mathrm P}`, and write the relation $`\approx`. Write $`\llbracket T\rrbracket_A` for $`X`, Nat and $`X\to X`. Compute the meaning of $`t_{\mathrm h}` in both environments.

*Joint proof · 30 minutes.* Write Definition 33.5 and unfold it at $`X\to X` and at $`X\to\mathsf{Nat}`. Then do the board case: the increment in five steps, the start value and the read operation in one line each, and the application of Theorem 33.6 to $`t_{\mathrm h}`. With the remaining time, go through the abstraction case of Theorem 33.6, keeping both extended environments on the board.

*Proof review · 20 minutes.* Do Exercise 33.2: replace the read operation of the pair counter by the constant zero function and find the condition that fails. Explain why the induction property of Theorem 33.6 quantifies over environments, and compare the case $`\mathsf{adv}\ k_1` of Proposition 33.2. The System F remark under Further Reading is optional.

*Facilitator’s hint.* Keep two columns on the board, one for each implementation, and write related elements on the same row. To check a relation at an arrow type, take one row of related arguments and produce one row of related results.

# Solutions and Further Reading
%%%
tag := "ch33-s7"
number := false
%%%

*33.1.* (a) $`\llbracket u\rrbracket_{\mathbb N}\rho_{\mathrm N}` is $`\varphi\mapsto\varphi(\varphi(0))` and $`\llbracket u\rrbracket_{\mathbb N\times\mathbb N}\rho_{\mathrm P}` is $`\varphi'\mapsto\varphi'(\varphi'((0,0)))`. Fix $`\varphi\approx_{X\to X}\varphi'`. Since $`0\approx(0,0)`, the arrow clause gives $`\varphi(0)\approx\varphi'((0,0))`. Applying it again gives $`\varphi(\varphi(0))\approx\varphi'(\varphi'((0,0)))`. This is the arrow clause at $`(X\to X)\to X`. (b) $`\Gamma_{\mathrm{ctr}}\vdash\mathit{tick}\ \mathit{start}:X`, so Theorem 33.6 gives $`1\approx(1,1)`. The meanings are a number and a pair, so they are not equal. A client cannot return this value, because its type mentions $`X`.

*33.2.* (a) The body $`\mathit{get}\ (\mathit{tick}\ \mathit{start})` means $`1` in $`\rho_{\mathrm N}` and $`0` in $`\rho_{\mathrm Z}`. (b) If some $`R` satisfied (i)–(iii), Corollary 33.7 would give $`1=0`. (c) Conditions (i) and (ii) hold as in §33.4, because $`\rho_{\mathrm Z}` agrees with $`\rho_{\mathrm P}` at $`\mathit{start}` and $`\mathit{tick}`. Condition (iii) fails at $`1\approx(1,1)`: the left read gives $`1` and the right read gives $`0`. It holds at the pairs $`0\approx(0,b)`.

*33.3.* (a) If $`X` does not occur in $`T`, then $`T` is Nat, or $`T=T_1\to T_2` with $`X` in neither $`T_1` nor $`T_2`. For Nat, both sets are $`\mathbb N` and $`R_{\mathsf{Nat}}` is equality. For an arrow, the induction hypothesis gives $`\llbracket T_i\rrbracket_A=\llbracket T_i\rrbracket_{A'}` with equality as $`R_{T_i}`, for $`i=1,2`. So the two sets of functions coincide, and $`\varphi\mathrel{R_{T_1\to T_2}}\varphi'` says $`\varphi(d)=\varphi'(d)` for every $`d`. Two functions on the same set are equal exactly when they agree at every argument. (b) Case T-Zero: both meanings are $`0`, which are related at Nat. Case T-Succ: the premise has type Nat, so its induction hypothesis gives $`\llbracket t_1\rrbracket_A\rho=\llbracket t_1\rrbracket_{A'}\rho'` for related $`\rho,\rho'`. Adding one to both sides gives equal numbers.

*33.4.* Define $`(d_1,d_2)\mathrel{R_{T_1\times T_2}}(d_1',d_2')` if $`d_1\mathrel{R_{T_1}}d_1'` and $`d_2\mathrel{R_{T_2}}d_2'`. The pair $`\{t_1,t_2\}` means $`(\llbracket t_1\rrbracket_A\rho,\llbracket t_2\rrbracket_A\rho)`, and $`t_1.1` means the first component of $`\llbracket t_1\rrbracket_A\rho`. Case T-Pair: the two induction hypotheses relate the components, so the pairs are related. Case T-Proj1: the induction hypothesis relates the two pairs, and the product clause relates their first components. For the context $`c{:}T_{\mathrm c}`, the environments map $`c` to $`(0,(n\mapsto n+1,\ n\mapsto n))` and to $`((0,0),((a,b)\mapsto(a+1,b+1),\ (a,b)\mapsto a))`. By the product and arrow clauses, these are related at $`T_{\mathrm c}` exactly when (i)–(iii) hold, which §33.4 checked.

*Further problem.* Relate $`n` to $`m` when $`m=n+1`. (i) $`0` is related to $`1`. (ii) If $`m=n+1`, then $`m+1=(n+1)+1`. (iii) If $`m=n+1`, then $`m\geq 1` and the right read gives $`m-1=n`, which is the left read. Proposition 33.2 and Corollary 33.7 apply. Equality is not such a relation: it fails (i), because $`0\neq 1`. Both representation sets are $`\mathbb N`. The relation, not the set, records which elements represent the same count.

*Further reading · System F.* Theorem 33.6 gives the single type variable $`X` the relation $`R` and keeps Nat fixed. Reynolds’s abstraction theorem extends this idea to System F (Session 31). Each type variable, bound by $`\forall` or $`\exists`, is interpreted by an arbitrary relation, and the arrow clause stays as in Definition 33.5. Two values of a universal type are related when, for every two types and every relation between them, their instances at those types are related. Two packages of an existential type are related when some relation between their representations relates their components. The second clause is Corollary 33.7 built into the logical relation. For all of System F the meaning of types can no longer be plain sets, and the relations are usually defined on closed terms through evaluation. As an example of the first clause, let $`p` be a closed term of type $`\forall X.X\to X` in System F without recursion. The abstraction theorem relates $`p` to itself. Fix a type, a value $`a` of that type, and the relation that relates $`a` to $`a` and nothing else. The two instances of $`p` at that type are related at $`X\to X`, and $`a` is related to $`a`. So the results of applying the two instances to $`a` are related, and each result is $`a`. The term $`p` behaves as the identity. Pfenning’s notes develop representation independence and parametricity along these lines. [Pfenning, Representation Independence, §1.](https://www.cs.cmu.edu/~fp/courses/15814-f25/lectures/16-independence.pdf) [Pfenning, Parametricity.](https://www.cs.cmu.edu/~fp/courses/15814-f19/lectures/16-parametricity.pdf)

*Further reading · Normalization.* Why does a proof of termination need a clause about function application? In the pure, simply typed language of [Session 26](chapter-26/index.html#ch26), an abstraction is already a value. Knowing that its evaluation terminates tells us nothing yet about what happens when we call it. Pierce, _Types and Programming Languages_, §12.1, strengthens the induction claim by defining a predicate $`R_T` on closed terms of type $`T`. At a base type it requires evaluation to a value. At $`A\to B` it requires both termination and the following property: for every $`u` satisfying $`R_A`, the application $`t\,u` satisfies $`R_B`. Both predicates on the right concern smaller types.

For example, suppose $`f` satisfies $`R_{A\to A}` and $`u` satisfies $`R_A`. Apply the arrow clause once to obtain $`R_A(f\,u)` and again to obtain $`R_A(f\,(f\,u))`. Mere termination of $`f` and $`u` would not justify either inference. The general proof substitutes closed terms satisfying the corresponding predicates for the free variables of a well-typed term. With the empty substitution it gives termination for closed programs. This is a unary predicate on terms; Definition 33.5 instead relates two interpretations of a term. They use the same idea at an arrow type: test a function on arguments satisfying the hypothesis.

# Sources and Formalization
%%%
tag := "ch33-notes"
number := false
%%%

The statements and proofs are this book’s, over the set meaning of Definition 33.4. They follow Frank Pfenning’s lecture notes on representation independence, whose §3 chooses a relation between two representations of an abstract type. TAPL §24.2 builds a counter as an abstract data type with records. Session 31 and this session write it with pairs. The Lean code in §33.1 and §33.3 checks Proposition 33.2 and Theorem 33.6 over definitions local to those sections. [Pfenning, Representation Independence, §3.](https://www.cs.cmu.edu/~fp/courses/15814-f25/lectures/16-independence.pdf) [Pfenning, Parametricity.](https://www.cs.cmu.edu/~fp/courses/15814-f19/lectures/16-parametricity.pdf)

* *Proposition 33.2.* Formulated in this book. Checked in Lean ([`simulation`](lean/CounterClients.html#simulation)) in [§33.1](chapter-33/index.html#ch33-s1).
* *Theorem 33.6.* Formulated in this book. Checked in Lean ([`fundamental`](lean/TypedCounter.html#fundamental)) in [§33.3](chapter-33/index.html#ch33-s3).
* *Corollary 33.7.* Formulated in this book. Paper proof only ([§33.4](chapter-33/index.html#ch33-s4)).
