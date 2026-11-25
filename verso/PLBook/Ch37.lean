import VersoManual

open Verso.Genre Manual

#doc (Manual) "Computational Adequacy: The Proof" =>
%%%
tag := "ch37"
file := "chapter-37"
%%%

Theorem 36.1 follows once we know $`\llbracket t\rrbracket \lhd_T t` for every closed term $`t` of every type $`T`. A proof by induction on $`t` must pass through the body of an abstraction, and that body has a free variable. So we prove a statement about terms with free variables. Each free variable receives a semantic element on the left of $`\lhd` and a closed term on the right, and the two must be related.

*In this session.*

* *Definitions.* Definition 36.2 (the relations $`\lhd_T`), Lemma 36.3 (the related set is admissible), Lemma 36.4 (closure under evaluation) and the statement of Theorem 36.1 ([Session 36](chapter-36/index.html)). Typing contexts, the typing and evaluation rules, environments $`\rho` with their extension $`\rho[y\mapsto d]`, and the meaning $`\llbracket t\rrbracket \rho` of a term with free variables ([Session 35](chapter-35/index.html)). Scott induction and least fixed points $`\mathrm{lfp}(f)` ([Session 34](chapter-34/index.html)). Substitution $`[x\mapsto u]t` ([C.1](lambda-card/index.html#lambda-c1)) and the substitution lemma for typing ([Session 25](chapter-25/index.html)).
* *New terms.* Closing substitution, related environment and substitution. [Glossary](glossary/index.html)
* *Theorem 37.2 (Fundamental theorem for the formal approximation relation).* Let $`\Gamma=x_1{:}T_1,\ldots,x_k{:}T_k` and $`\Gamma\vdash t:T`. For every environment $`\rho` for $`\Gamma` and all closed terms $`u_1,\ldots,u_k` with $`\vdash u_i:T_i`, if $`\rho(x_i)\lhd_{T_i}u_i` for every $`i`, then $`\llbracket t\rrbracket \rho\lhd_T[\vec{x}\mapsto\vec{u}]t`.
* *Board case.* The fixed-point case of Theorem 37.2 (§37.3), in eight numbered steps.
* *Proof outline.* Induction on the typing derivation, with $`P(\Gamma\vdash t:T)\coloneqq\forall\rho,\ \forall\vec{u},\ \rho\lhd_\Gamma\vec{u}\Rightarrow\llbracket t\rrbracket \rho\lhd_T[\vec{x}\mapsto\vec{u}]t`. Application instantiates the arrow clause of the operator’s hypothesis with the operand’s pair. Abstraction applies the body’s hypothesis to an extended pair and returns with Lemma 36.4. The fixed point applies Scott induction to the admissible set of Lemma 36.3 and unfolds once with Lemma 36.4. Adequacy is the case of the empty context.
* *From Session 36.* Session 36 defined $`\lhd_T` for closed terms and proved Lemmas 36.3 and 36.4. This session uses them as stated and proves Theorem 36.1. The new step is to handle free variables: each variable receives a semantic element on the left and a closed term on the right.

# Related environments and substitutions
%%%
tag := "ch37-s1"
%%%

Take the context $`y{:}\mathsf{Nat}\to\mathsf{Nat},\,x{:}\mathsf{Nat}` and the term $`y\,x`. Give the variables semantic values by the environment $`\rho(y)=i`, $`\rho(x)=5`, and closed terms by the substitution of $`I` for $`y` and $`\overline{5}` for $`x`, with $`i` and $`I` the identities of [§36.2](chapter-36/index.html#ch36-s2). Both pairs are related: $`i\lhd_{\mathsf{Nat}\to\mathsf{Nat}}I` by §36.2, and $`5\lhd_{\mathsf{Nat}}\overline{5}` since $`\overline{5}\Downarrow\overline{5}`. The meaning of the term is $`\llbracket y\,x\rrbracket \rho=\rho(y)(\rho(x))=i(5)`. The term after substitution is $`I\,\overline{5}`. The arrow clause of $`i\lhd I`, applied to the pair $`(5,\overline{5})`, gives $`i(5)\lhd_{\mathsf{Nat}}I\,\overline{5}`. The argument used nothing about $`i`, $`I`, 5 or $`\overline{5}` except the two relations. The same two lines work for every related choice of values and closed terms.

*Definition 37.1 (Closing substitution, related environment and substitution).* Let $`\Gamma=x_1{:}T_1,\ldots,x_k{:}T_k`. A *closing substitution* for $`\Gamma` is a list $`\vec{u}=u_1,\ldots,u_k` of closed terms with $`\vdash u_i:T_i`. For a term $`t`, the term $`[\vec{x}\mapsto\vec{u}]t` replaces each free occurrence of each $`x_i` in $`t` by $`u_i`. An environment $`\rho` for $`\Gamma` and a closing substitution $`\vec{u}` for $`\Gamma` are *related*, written $`\rho\lhd_\Gamma\vec{u}`, if $`\rho(x_i)\lhd_{T_i}u_i` for every $`i`.

Since the $`u_i` are closed, no variable capture can occur, and replacing the $`x_i` one at a time gives the same term. Two facts about closing substitutions are used below. First, if $`\Gamma\vdash t:T` then $`\vdash[\vec{x}\mapsto\vec{u}]t:T`. This is the substitution lemma of Session 25 applied once for each variable; for PCF its proof has one more case, the fixed point, which goes like the successor case. Second, substitution passes through each term former. For example, $`[\vec{x}\mapsto\vec{u}](t_1\,t_2)=([\vec{x}\mapsto\vec{u}]t_1)\,([\vec{x}\mapsto\vec{u}]t_2)` and $`[\vec{x}\mapsto\vec{u}](\mathsf{fix}\ t_1)=\mathsf{fix}\,([\vec{x}\mapsto\vec{u}]t_1)`. For an abstraction whose parameter $`y` is not among $`x_1,\ldots,x_k`, $`[\vec{x}\mapsto\vec{u}](\lambda y{:}S.\,t_1)=\lambda y{:}S.\,[\vec{x}\mapsto\vec{u}]t_1`, because no $`u_i` contains $`y` free. For the same reason, substituting a closed term $`u` for $`y` afterwards gives $`[y\mapsto u]([\vec{x}\mapsto\vec{u}]t_1)=[\vec{x}\mapsto\vec{u},\,y\mapsto u]t_1`.

*Theorem 37.2 (Fundamental theorem for the formal approximation relation).* Let $`\Gamma=x_1{:}T_1,\ldots,x_k{:}T_k` and $`\Gamma\vdash t:T`. For every environment $`\rho` for $`\Gamma` and every closing substitution $`\vec{u}` for $`\Gamma`, if $`\rho\lhd_\Gamma\vec{u}` then $`\llbracket t\rrbracket \rho\lhd_T[\vec{x}\mapsto\vec{u}]t`.

This is Theorem 30 of the Cambridge notes, which call it the fundamental property. Its shape is that of the fundamental theorem of [Session 33](chapter-33/index.html): every well-typed term is related to itself. Here the meaning of the term stands on the left and its closed instance on the right.

We prove $`P(\mathcal{D})` for every typing derivation $`\mathcal{D}` by induction on $`\mathcal{D}`. For a derivation with conclusion $`\Gamma\vdash t:T`,

$$`P(\Gamma\vdash t:T)\coloneqq\forall\rho,\ \forall\vec{u},\ \rho\lhd_\Gamma\vec{u}\Rightarrow\llbracket t\rrbracket \rho\lhd_T[\vec{x}\mapsto\vec{u}]t.`

The environment and the substitution are quantified inside $`P`, as the final state was in [Session 3](chapter-03/index.html#ch03-s2). The abstraction case applies the hypothesis for the body to an extended pair, not to the pair fixed at the start of the case.

# The cases other than the fixed point
%%%
tag := "ch37-s2"
%%%

In each case fix $`\rho` and $`\vec{u}` with $`\rho\lhd_\Gamma\vec{u}`. For any term $`t'` write $`t'^{*}` for $`[\vec{x}\mapsto\vec{u}]t'`. The clauses of Definition 35.5 and the evaluation rules are those of Session 35.

*Variable.* If $`t=x_i`, then $`\llbracket x_i\rrbracket \rho=\rho(x_i)` and $`x_i^{*}=u_i`. The assumption $`\rho(x_i)\lhd_{T_i}u_i` is the claim.

*Constants.* $`\llbracket 0\rrbracket \rho=0` and $`0^{*}=0`. The only number equal to 0 is 0, and $`0\Downarrow0` because 0 is a value. So $`0\lhd_{\mathsf{Nat}}0`. The constants $`\mathsf{true}` and $`\mathsf{false}` are handled in the same way.

*Successor and predecessor.* Let $`t=\mathsf{succ}\ t_1`, with hypothesis $`\llbracket t_1\rrbracket \rho\lhd_{\mathsf{Nat}}t_1^{*}`. If $`\llbracket \mathsf{succ}\ t_1\rrbracket \rho=m`, then $`m=n+1` where $`\llbracket t_1\rrbracket \rho=n`, because the successor of $`\bot` is $`\bot`. The hypothesis gives $`t_1^{*}\Downarrow\overline{n}`, and B-Succ gives $`\mathsf{succ}\ t_1^{*}\Downarrow\overline{n+1}`. For $`t=\mathsf{pred}\ t_1`: if $`\llbracket \mathsf{pred}\ t_1\rrbracket \rho=n`, then $`\llbracket t_1\rrbracket \rho=n+1`, because the predecessor of 0 and of $`\bot` is $`\bot`. The hypothesis gives $`t_1^{*}\Downarrow\mathsf{succ}\ \overline{n}`, and B-PredSucc gives $`\mathsf{pred}\ t_1^{*}\Downarrow\overline{n}`. The zero test is Exercise 37.2.

*Conditional.* Let $`t=\mathsf{if}\ t_1\ \mathsf{then}\ t_2\ \mathsf{else}\ t_3` with $`\Gamma\vdash t:T`. The hypotheses give $`\llbracket t_1\rrbracket \rho\lhd_{\mathsf{Bool}}t_1^{*}`, $`\llbracket t_2\rrbracket \rho\lhd_T t_2^{*}` and $`\llbracket t_3\rrbracket \rho\lhd_T t_3^{*}`. If $`\llbracket t_1\rrbracket \rho=\bot`, the meaning of $`t` is $`\bot`, and Lemma 36.3(a) applies. If $`\llbracket t_1\rrbracket \rho=\mathrm{tt}`, the meaning of $`t` is $`\llbracket t_2\rrbracket \rho`, and the first hypothesis gives $`t_1^{*}\Downarrow\mathsf{true}`. With that premise B-IfTrue turns every derivation of $`t_2^{*}\Downarrow v` into a derivation of $`t^{*}\Downarrow v`. Lemma 36.4 moves $`\llbracket t_2\rrbracket \rho\lhd_T t_2^{*}` to $`\llbracket t_2\rrbracket \rho\lhd_T t^{*}`. The case $`\mathrm{ff}` is symmetric. The type $`T` may be a function type, so the clause of Definition 36.2 cannot be checked directly; Lemma 36.4 does it at every type.

*Application.* Let $`t=t_1\,t_2` with premises $`\Gamma\vdash t_1:S\to T` and $`\Gamma\vdash t_2:S`.

1. The hypothesis for $`t_1` gives $`\llbracket t_1\rrbracket \rho\lhd_{S\to T}t_1^{*}`, and the one for $`t_2` gives $`\llbracket t_2\rrbracket \rho\lhd_S t_2^{*}`.
2. Apply the arrow clause of the first relation to the related pair $`(\llbracket t_2\rrbracket \rho,\,t_2^{*})`. This gives $`\llbracket t_1\rrbracket \rho\,(\llbracket t_2\rrbracket \rho)\lhd_T t_1^{*}\,t_2^{*}`.
3. The left side is $`\llbracket t_1\,t_2\rrbracket \rho`, and the right side is $`(t_1\,t_2)^{*}`.

*Abstraction.* Let $`t=\lambda y{:}S.\,t_1` with premise $`\Gamma,y{:}S\vdash t_1:U` and $`T=S\to U`. Rename $`y` if necessary so that it is not among $`x_1,\ldots,x_k`. The hypothesis for the premise is

$$`P(\Gamma,y{:}S\vdash t_1:U):\quad\forall\rho',\ \forall\vec{u}',\ \rho'\lhd_{\Gamma,y:S}\vec{u}'\Rightarrow\llbracket t_1\rrbracket \rho'\lhd_U[\vec{x},y\mapsto\vec{u}']t_1.`

1. We must show $`\llbracket \lambda y{:}S.\,t_1\rrbracket \rho\lhd_{S\to U}\lambda y{:}S.\,t_1^{*}`. Fix a related pair $`(d,u)` at $`S`. We must show $`\llbracket \lambda y{:}S.\,t_1\rrbracket \rho\,(d)\lhd_U(\lambda y{:}S.\,t_1^{*})\,u`.
2. By the clause for abstraction, $`\llbracket \lambda y{:}S.\,t_1\rrbracket \rho\,(d)=\llbracket t_1\rrbracket (\rho[y\mapsto d])`.
3. The environment $`\rho[y\mapsto d]` and the closing substitution $`\vec{u},u` are related for $`\Gamma,y{:}S`: at each $`x_i` by assumption, and at $`y` because $`d\lhd_S u`.
4. Apply the hypothesis to this pair. It gives $`\llbracket t_1\rrbracket (\rho[y\mapsto d])\lhd_U[\vec{x}\mapsto\vec{u},\,y\mapsto u]t_1`, and this term equals $`[y\mapsto u]t_1^{*}`.
5. Every value of $`[y\mapsto u]t_1^{*}` is a value of $`(\lambda y{:}S.\,t_1^{*})\,u`. B-App has the first premise $`\lambda y{:}S.\,t_1^{*}\Downarrow\lambda y{:}S.\,t_1^{*}`, since an abstraction is a value, and the second premise $`[y\mapsto u]t_1^{*}\Downarrow v`.
6. Lemma 36.4, applied to steps 4 and 5, gives $`\llbracket \lambda y{:}S.\,t_1\rrbracket \rho\,(d)\lhd_U(\lambda y{:}S.\,t_1^{*})\,u`.

# The fixed-point case
%%%
tag := "ch37-s3"
%%%

First the case of the closed term $`K=\mathsf{fix}\ G` from Session 35, §35.1, done by hand. In this paragraph every relation is at $`\mathsf{Nat}\to\mathsf{Nat}`, and we omit the subscript. The hypothesis for the premise $`\vdash G:(\mathsf{Nat}\to\mathsf{Nat})\to(\mathsf{Nat}\to\mathsf{Nat})`, with the empty environment and substitution, gives $`\llbracket G\rrbracket \lhd_{(\mathsf{Nat}\to\mathsf{Nat})\to(\mathsf{Nat}\to\mathsf{Nat})}G`. The approximations are $`g_0=\bot` and $`g_{j+1}=\llbracket G\rrbracket (g_j)`. Lemma 36.3(a) gives $`g_0\lhd K`. If $`g_j\lhd K`, the arrow clause for $`\llbracket G\rrbracket ` applied to the related pair $`(g_j,K)` gives $`g_{j+1}\lhd G\,K`. Every value of $`G\,K` is a value of $`K` ([§36.3](chapter-36/index.html#ch36-s3)), so Lemma 36.4 gives $`g_{j+1}\lhd K`. Hence $`g_j\lhd K` for every $`j`, and Lemma 36.3(b) gives $`\llbracket K\rrbracket =\bigsqcup_j g_j\lhd K`. The term $`K` is the same at every stage. Only the semantic element moves.

Scott induction ([Session 34, Theorem 34.8](chapter-34/index.html#ch34-s3)), applied to the property $`d\in\mathcal{A}`, packages these three steps. For a continuous function $`f` on a domain $`D` and an admissible set $`\mathcal{A}\subseteq D`: if $`f(d)\in\mathcal{A}` for every $`d\in\mathcal{A}`, then $`\mathrm{lfp}(f)\in\mathcal{A}`.

*Fixed point.* Suppose the typing derivation ends with T-Fix. Then $`t=\mathsf{fix}\ t_1`, and the premise is $`\Gamma\vdash t_1:T\to T`. Its induction hypothesis is

$$`P(\Gamma\vdash t_1:T\to T):\quad\forall\rho',\ \forall\vec{u}',\ \rho'\lhd_\Gamma\vec{u}'\Rightarrow\llbracket t_1\rrbracket \rho'\lhd_{T\to T}[\vec{x}\mapsto\vec{u}']t_1.`

Write $`f=\llbracket t_1\rrbracket \rho`, $`h=t_1^{*}` and $`w=\mathsf{fix}\ h`. Then $`w=(\mathsf{fix}\ t_1)^{*}`. The term $`h` is closed with $`\vdash h:T\to T`, and $`w` is closed with $`\vdash w:T`.

1. We must show $`\llbracket \mathsf{fix}\ t_1\rrbracket \rho\lhd_T w`. By the clause for the fixed point, $`\llbracket \mathsf{fix}\ t_1\rrbracket \rho=\mathrm{lfp}(f)`, where $`f` is a continuous function on $`\llbracket T\rrbracket `. So we must show $`\mathrm{lfp}(f)\lhd_T w`.
2. Apply the induction hypothesis to the given pair $`\rho,\vec{u}`. This gives $`f\lhd_{T\to T}h`.
3. Let $`\mathcal{A}=\{d\in\llbracket T\rrbracket \mid d\lhd_T w\}`. Lemma 36.3, applied to the closed term $`w`, says that $`\mathcal{A}` is admissible.
4. By Scott induction for $`f` and $`\mathcal{A}`, it suffices to show $`f(d)\in\mathcal{A}` for every $`d\in\mathcal{A}`. Fix $`d\in\llbracket T\rrbracket ` with $`d\lhd_T w`.
5. Apply the arrow clause of step 2 to the related pair $`(d,w)`. This gives $`f(d)\lhd_T h\,w`.
6. By B-Fix, a derivation of $`h\,(\mathsf{fix}\ h)\Downarrow v` becomes a derivation of $`\mathsf{fix}\ h\Downarrow v`. Since $`\mathsf{fix}\ h=w`, every value of $`h\,w` is a value of $`w`.
7. Apply Lemma 36.4 to the terms $`h\,w` and $`w`, using step 6, to the relation of step 5. This gives $`f(d)\lhd_T w`, that is, $`f(d)\in\mathcal{A}`.
8. Scott induction now gives $`\mathrm{lfp}(f)\in\mathcal{A}`, that is, $`\llbracket \mathsf{fix}\ t_1\rrbracket \rho\lhd_T(\mathsf{fix}\ t_1)^{*}`.

This completes the induction and proves Theorem 37.2. $`\square`

In step 5 the term $`w` appears twice: as the term to be formally approximated and as the argument given to $`h`. This works because $`\mathcal{A}` is the set for the single term $`w`. If the term were allowed to change from stage to stage, Lemma 36.3(b) would not apply. Step 6 is the only use of B-Fix in the whole proof, as §36.1 said there must be one.

# Adequacy
%%%
tag := "ch37-s4"
%%%

*Proof of Theorem 36.1.* Let $`t` be closed with $`\vdash t:\mathsf{Nat}`, and suppose $`\llbracket t\rrbracket =n`. Apply Theorem 37.2 with the empty context, $`k=0`. There is one environment, the empty one, and one closing substitution, the empty list. They are related, because Definition 37.1 then requires nothing. The empty substitution leaves $`t` unchanged. So the theorem gives $`\llbracket t\rrbracket \lhd_{\mathsf{Nat}}t`. Definition 36.2 at $`\mathsf{Nat}`, used with this $`n`, gives $`t\Downarrow\overline{n}`. For $`\vdash t:\mathsf{Bool}`, the clause at $`\mathsf{Bool}` gives $`t\Downarrow\mathsf{true}` from $`\llbracket t\rrbracket =\mathrm{tt}` and $`t\Downarrow\mathsf{false}` from $`\llbracket t\rrbracket =\mathrm{ff}`. $`\square`

For $`K\,\overline{1}`, the computation of approximations in Session 35 gives $`\llbracket K\,\overline{1}\rrbracket =0`, and Theorem 36.1 turns this into the existence of a derivation of $`K\,\overline{1}\Downarrow\overline{0}`. The derivation built by hand in Session 35 is one such derivation, so the two accounts check each other.

At a ground type the meaning $`\bot` is also exact. Let $`\vdash t:\mathsf{Nat}`. If $`t` has a value, that value has type $`\mathsf{Nat}`, because a judgment $`t\Downarrow v` is formed only when $`t` and $`v` have one type (Session 35, Definition 35.3), so it is a numeral $`\overline{n}`. Theorem 35.8 then gives $`\llbracket t\rrbracket =n\ne\bot`. If $`t` has no value, Theorem 36.1 rules out $`\llbracket t\rrbracket =n` for every $`n`, so $`\llbracket t\rrbracket =\bot`. Thus $`\llbracket t\rrbracket =\bot` exactly when $`t` has no value. The first direction uses soundness and the second uses adequacy. The relation $`\bot\lhd_{\mathsf{Nat}}t` alone says nothing (Exercise 37.1).

# Exercises
%%%
tag := "ch37-s5"
number := false
%%%

*37.1.* Let $`\vdash t:\mathsf{Nat}` and $`\llbracket t\rrbracket =\bot`. Does $`\llbracket t\rrbracket \lhd_{\mathsf{Nat}}t` by itself imply that $`t` has no value? Which theorem shows that it has none?

*37.2.* Write the zero-test case of Theorem 37.2 in the style of the successor case. Use B-IszeroZero and B-IszeroSucc.

*37.3.* Suppose $`\rho` and $`\vec{u}` were fixed before the induction, so that the property of a derivation with conclusion $`\Gamma\vdash t:T` were only $`\llbracket t\rrbracket \rho\lhd_T[\vec{x}\mapsto\vec{u}]t`. Which case of §37.2 can no longer be proved? Name the step that fails.

*37.4.* Replace $`\Downarrow` by the judgment $`\Downarrow^{-}` of [§36.1](chapter-36/index.html#ch36-s1), which lacks B-Fix, in Definition 36.2, in Lemmas 36.3 and 36.4 and in the proof of Theorem 37.2. Which proofs still go through? Which step of §37.3 fails? Check the answer against $`K\,\overline{1}`.

*Further problem.* Let $`t` and $`t'` be closed terms of type $`\mathsf{Nat}\to\mathsf{Nat}` with $`\llbracket t\rrbracket =\llbracket t'\rrbracket `. Show that for every closed term $`u` of type $`\mathsf{Nat}` and every number $`n`, $`t\,u\Downarrow\overline{n}` if and only if $`t'\,u\Downarrow\overline{n}`. Then give two closed terms of type $`\mathsf{Nat}\to\mathsf{Nat}` with the same meaning that do not evaluate to the same value.

# Reading for the Seminar
%%%
tag := "ch37-s6"
number := false
%%%

*Definitions · 10 minutes.* Write the induction property $`P` with its two inner quantifiers. Work the example $`y\,x` of §37.1 on the board, and compare it with the application case.

*Joint proof · 30 minutes.* The fixed-point case. Begin with the hand computation for $`K`: $`g_0,g_1,g_2\lhd K`. Then one person sets up $`f`, $`h`, $`w` and $`\mathcal{A}` (steps 1–4), another applies the hypothesis and B-Fix (steps 5–6), and a third applies Lemma 36.4 and Scott induction (steps 7–8).

*Proof review · 20 minutes.* Derive Theorem 36.1 (§37.4) and apply it to $`K\,\overline{1}`. Go through the abstraction case and locate the extended pair. Use Exercise 37.4 to locate the one place where B-Fix enters.

*Facilitator’s hint.* The term $`w` never changes. Only the semantic element moves along the increasing sequence of approximations.

# Solutions and Further Reading
%%%
tag := "ch37-s7"
number := false
%%%

*37.1.* No. Lemma 36.3(a) gives $`\bot\lhd_{\mathsf{Nat}}t` for every closed $`t`, so the relation carries no information here. Suppose $`t\Downarrow v`. The value is a numeral $`\overline{n}`, and Theorem 35.8 gives $`\llbracket t\rrbracket =n`, contradicting $`\llbracket t\rrbracket =\bot`. So $`t` has no value. The argument uses soundness, not adequacy.

*37.2.* Let $`t=\mathsf{iszero}\ t_1`, with hypothesis $`\llbracket t_1\rrbracket \rho\lhd_{\mathsf{Nat}}t_1^{*}`. The meaning $`\llbracket \mathsf{iszero}\ t_1\rrbracket \rho` is $`\mathrm{tt}` if $`\llbracket t_1\rrbracket \rho=0`, $`\mathrm{ff}` if $`\llbracket t_1\rrbracket \rho=n+1` for some $`n`, and $`\bot` if $`\llbracket t_1\rrbracket \rho=\bot`. If it is $`\mathrm{tt}`, the hypothesis gives $`t_1^{*}\Downarrow0`, and B-IszeroZero gives $`\mathsf{iszero}\ t_1^{*}\Downarrow\mathsf{true}`. If it is $`\mathrm{ff}`, the hypothesis gives $`t_1^{*}\Downarrow\mathsf{succ}\ \overline{n}`, and B-IszeroSucc gives $`\mathsf{iszero}\ t_1^{*}\Downarrow\mathsf{false}`.

*37.3.* The abstraction case, at step 4. There the hypothesis for the body is applied to $`\rho[y\mapsto d]` and $`\vec{u},u`, where the pair $`(d,u)` was chosen in step 1, after the induction hypothesis was formed. The premise $`\Gamma,y{:}S\vdash t_1:U` also has a larger context than $`\Gamma`. A fixed $`\rho` is not an environment for it, and fixing a value for $`y` in advance would fix $`d` before step 1 chooses it.

*37.4.* Lemma 36.3 uses no evaluation rule, and Lemma 36.4 uses only B-App, so both proofs go through for $`\Downarrow^{-}`. The cases of §37.2 use only B-Value, B-Succ, B-PredSucc, B-IszeroZero, B-IszeroSucc, B-IfTrue, B-IfFalse and B-App, which $`\Downarrow^{-}` keeps. Step 6 of §37.3 fails: without B-Fix, a value of $`h\,w` need not be a value of $`w`. For $`K`, the relation $`\llbracket K\rrbracket \lhd K` for $`\Downarrow^{-}` would require $`K\,\overline{1}\Downarrow^{-}\overline{0}` at the related pair $`(1,\overline{1})`, and §36.1 showed that $`K\,\overline{1}` has no value under $`\Downarrow^{-}`.

*Further problem.* The clause for application gives $`\llbracket t\,u\rrbracket =\llbracket t\rrbracket (\llbracket u\rrbracket )=\llbracket t'\rrbracket (\llbracket u\rrbracket )=\llbracket t'\,u\rrbracket `. If $`t\,u\Downarrow\overline{n}`, Theorem 35.8 gives $`\llbracket t\,u\rrbracket =n`, so $`\llbracket t'\,u\rrbracket =n`, and Theorem 36.1 gives $`t'\,u\Downarrow\overline{n}`. The converse is symmetric. The terms $`\lambda x{:}\mathsf{Nat}.\,x` and $`\lambda x{:}\mathsf{Nat}.\,(\lambda z{:}\mathsf{Nat}.\,z)\,x` both mean the identity on $`\mathbb{N}_\bot`. Each is a value and evaluates only to itself, and they are different terms. Equal meanings at a function type give equal results on ground observations, not equal values.

*Further reading · Stages and derivations.* Adequacy is an existence result. Let $`t=\mathsf{fix}\ h` be closed of type $`\mathsf{Nat}\to\mathsf{Nat}` and $`f=\llbracket h\rrbracket `. Suppose a program computes the stages $`f^{j}(\bot)(k)` mechanically and finds the number 3 at some stage $`j`. These stages form an increasing sequence in the flat domain $`\mathbb{N}_\bot` whose least upper bound is $`\mathrm{lfp}(f)(k)=\llbracket t\,\overline{k}\rrbracket `, so $`\llbracket t\,\overline{k}\rrbracket =3`, and adequacy supplies a derivation of $`t\,\overline{k}\Downarrow\overline{3}`. Nothing relates the stage $`j` to the size of that derivation. If the first hundred stages give $`\bot`, nothing follows, since an increasing sequence may first reach a number at stage 101. To conclude that a term has no value, one needs a proof that the limit is $`\bot`, and then the argument at the end of §37.4 applies.

*Further reading · Full abstraction.* Adequacy compares meanings only through ground observations. Session 38, §38.3, asks the converse question, full abstraction, and its Further Reading gives the sources.

# Sources and Formalization
%%%
tag := "ch37-notes"
number := false
%%%

Cambridge _Denotational Semantics_ lecture notes for 2025–26 (version of 5 December 2024). Theorem 37.2 is their Theorem 30 and Theorem 36.1 their Theorem 31. Lemma 36.3 is their Lemmas 32 and 33, and Lemma 36.4 is their Lemma 35. [Cambridge notes](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

* *Theorem 37.2.* Source: Cambridge notes, Theorem 30. Paper proof only ([§37.2](chapter-37/index.html#ch37-s2)–[§37.3](chapter-37/index.html#ch37-s3)).
