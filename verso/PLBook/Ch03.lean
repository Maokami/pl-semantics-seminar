import VersoManual
import PLBook.IMP.Determinacy

open Verso.Genre Manual

#doc (Manual) "Inversion and Determinacy" =>
%%%
tag := "ch03"
file := "chapter-03"
%%%

*Session 3 · Inversion and Determinacy*　Read §§3.1–3.3 · Presenter ＿＿＿＿ · Preparation time ＿＿＿＿

* *Definitions.* [IMP language card A.1–A.5](imp-card/index.html), especially the six execution rules in A.5.
* *New terms.* Determinacy, height of a derivation, induction on derivations, induction property, partial function. [Glossary and label key](glossary/index.html)
* *Theorem 3.2 \[This book\] \[Checked\].* For every command $`c` and stores $`s,t,u`, if $`s\vdash c\Downarrow t` and $`s\vdash c\Downarrow u`, then $`t=u`.
* *Source.* The execution relation is defined by the six big-step rules for commands in Xavier Leroy’s compiler verification course (IMP, as presented in A.5). \[Corresponding: CS Lemma 7.9\] Nipkow and Klein prove the corresponding theorem for their IMP in _Concrete Semantics_, §7.2.5. [Definitions and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf)
* *Board case.* Sequencing. Invert the second derivation $`E` and identify the intermediate stores before comparing the final stores.
* *Proof outline.* For $`D:s\vdash c\Downarrow t`, take $`P(D)\coloneqq\forall u,\ (s\vdash c\Downarrow u)\Rightarrow t=u`. Quantify $`u` inside the induction property so the first induction hypothesis can be applied at the intermediate store and the second at the final store.
* *From Session 2.* Inverting one sequence derivation gave an intermediate store. Here each derivation supplies its own intermediate store. The first induction hypothesis proves that the two stores are equal.

Two people derive terminating executions of the same program from the same store. Their proofs introduce different names for the intermediate stores. To compare their final results one must first prove that those intermediate stores agree. The example exposes a choice in the induction property that also occurs in proofs about type systems and compilers.

# Induction over evidence
%%%
tag := "ch03-s1"
%%%

Consider two derivations for `x := 1; x := 2` starting in the same store $`s`. In $`D` name the intermediate store $`m` and the final store $`t`. In the second derivation $`E` use $`n` and $`u`. Each leaf below is an instance of the assignment rule.

$$`D:\quad\frac{\dfrac{}{s\vdash x:=1\Downarrow m}\qquad\dfrac{}{m\vdash x:=2\Downarrow t}}{s\vdash(x:=1\,;\,x:=2)\Downarrow t}`

$$`E:\quad\frac{\dfrac{}{s\vdash x:=1\Downarrow n}\qquad\dfrac{}{n\vdash x:=2\Downarrow u}}{s\vdash(x:=1\,;\,x:=2)\Downarrow u}`

To compare the executions of the second assignment from the same store, we first need $`m=n`. Here both left leaves give $`s[x\mapsto1]`. The right leaves give $`t=m[x\mapsto2]` and $`u=n[x\mapsto2]`. In §3.2 the first command can itself be a loop, so identifying the intermediate stores will require an induction hypothesis.

A derivation of $`s\vdash c\Downarrow t` is a finite tree of applications of the execution rules. Its *height* is zero when the last rule has no execution premises. Otherwise it is one plus the greatest height of an immediate execution subderivation. A guard test is a side condition checked by calculation ([A.5](imp-card/index.html#imp-a5)). Thus even the false loop rule has height zero.

An *induction property* $`P` assigns a statement to each derivation $`D`. To prove $`\forall D,\ P(D)` by *induction on derivations*, show for each possible last rule that $`P(D)` follows from the induction hypotheses for its immediate execution subderivations. A loop premise may concern exactly the command at the root, yet the premise tree has smaller height. Induction on syntax alone would give a hypothesis for the body and none for the next execution of the loop.

*Inversion* works in the opposite direction to rule application. If $`s \vdash c\ \text{;}\ d \Downarrow t` is derivable, its last rule must be sequence, so there exists $`u` with derivations of $`s \vdash c \Downarrow u` and $`u \vdash d \Downarrow t`. Each inversion recovers an intermediate store from one particular tree.

The conditional has one rule. Put $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`. Its premise is an execution of whichever command the Boolean value $`B(b,s)` selects. Evaluating this selection gives two derived rules \[This book\] \[Corresponding: CS IfTrue, IfFalse\] \[Checked\].

$$`\frac{B(b,s)=\mathsf{true}\quad s\vdash c\Downarrow t}{s\vdash I\Downarrow t}
\qquad
\frac{B(b,s)=\mathsf{false}\quad s\vdash d\Downarrow t}{s\vdash I\Downarrow t}`

For the left rule the selected command is $`c`, so its given derivation supplies the premise of the conditional rule. The right rule follows by the same calculation with $`d`. Inverting a conditional execution therefore gives a derivation for the selected branch even before we distinguish the two Boolean values.

For the sequence rule, let $`D` be the derivation formed from the two premises shown below. The induction step has the following form.

$$`\frac{\begin{gathered}D_1:s\vdash c_1\Downarrow m\qquad D_2:m\vdash c_2\Downarrow t\\P(D_1)\qquad P(D_2)\end{gathered}}{P(D)}\qquad(D:s\vdash(c_1;c_2)\Downarrow t)`

For $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1` with $`B(b,s)=\mathsf{true}`, let $`D` end with the iteration rule. Its second premise is another execution of $`W`.

$$`\frac{\begin{gathered}D_1:s\vdash c_1\Downarrow m\qquad D_2:m\vdash W\Downarrow t\\P(D_1)\qquad P(D_2)\end{gathered}}{P(D)}\qquad(D:s\vdash W\Downarrow t)`

Induction on height justifies this principle. For a derivation of height $`h`, assume $`P` holds for every derivation of height less than $`h`. Each immediate subderivation then supplies the induction hypothesis required by the last rule.

# Comparing two derivations
%%%
tag := "ch03-s2"
%%%

*Lemma 3.1 (Update uniqueness) \[This book\] \[Checked\].* For fixed $`s,x,e`, every execution of $`x \mathrel{:=} e` from $`s` ends in $`s\left\lbrack {x\mapsto\operatorname{eval}\left( {e,s} \right)} \right\rbrack`. Inversion leaves only the assignment rule. The evaluation function of A.3 supplies a single integer $`\operatorname{eval}\left( {e,s} \right)`, and store update names a single function. Thus any two resulting stores agree at $`x` and at every other name.

*Theorem 3.2 (Determinacy) \[This book\] \[Checked\].* For every $`c,s,t,u`, if $`s \vdash c \Downarrow t` and $`s \vdash c \Downarrow u` then $`t = u`.

We prove $`P(D)` for every derivation $`D` by induction on $`D`. The induction property is

$$`P(D)\quad ≔ \quad\forall u,\bigl(s \vdash c \Downarrow u\bigr)\Longrightarrow t = u.`

Read $`s,c,t` from the conclusion $`s\vdash c\Downarrow t` of $`D`. The quantifier over $`u` is inside $`P(D)`. At each premise we can therefore choose the final store of the derivation with which we compare it.

*Sequence.* Suppose $`c=c_1;c_2`. The premises of $`D` are $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash c_2\Downarrow t`. Their induction hypotheses are

$$`\begin{aligned}
P(D_1)&:\quad\forall v,\ (s\vdash c_1\Downarrow v)\Rightarrow m=v,\\
P(D_2)&:\quad\forall v,\ (m\vdash c_2\Downarrow v)\Rightarrow t=v.
\end{aligned}`

1. Fix $`u` and take the second derivation $`E:s\vdash(c_1;c_2)\Downarrow u`. Its last rule must be sequence. Inversion gives a store $`n` and premises $`E_1:s\vdash c_1\Downarrow n` and $`E_2:n\vdash c_2\Downarrow u`.
2. Apply $`P(D_1)` with $`v=n` to $`E_1`. This gives $`m=n`.
3. Rewrite $`E_2` using this equality. It now proves $`m\vdash c_2\Downarrow u`.
4. Apply $`P(D_2)` with $`v=u` to the rewritten $`E_2`. This gives $`t=u`.

Applying this second hypothesis before the replacement would require $`E_{2}` to start in $`m`, a fact the inversion alone did not supply.

*Skip, assignment, and conditional.* Both skip derivations end in $`s`. Lemma 3.1 handles assignment. For a conditional, let $`k` be the command selected by $`B(b,s)`. The premise of $`D` is $`D_1:s\vdash k\Downarrow t`, with $`P(D_1):\forall v,\ (s\vdash k\Downarrow v)\Rightarrow t=v`. Inverting the second derivation $`E` gives $`E_1:s\vdash k\Downarrow u` with the same $`k`, since $`B` is a function of the guard and the common initial store. Apply $`P(D_1)` to $`u` and $`E_1`.

*Loop exit.* If $`D` ends by the exit rule, then $`B(b,s)=\mathsf{false}` and $`t=s`. The iteration rule would require $`B(b,s)=\mathsf{true}`. The second derivation $`E` therefore uses the exit rule too, so $`u=s=t`.

*Loop iteration.* Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`. The last rule of $`D` gives $`B(b,s)=\mathsf{true}`, $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash W\Downarrow t`. Its induction hypotheses are

$$`\begin{aligned}
P(D_1)&:\quad\forall v,\ (s\vdash c_1\Downarrow v)\Rightarrow m=v,\\
P(D_2)&:\quad\forall v,\ (m\vdash W\Downarrow v)\Rightarrow t=v.
\end{aligned}`

The second derivation $`E:s\vdash W\Downarrow u` cannot end with the exit rule, which requires $`B(b,s)=\mathsf{false}` in that same store. Inverting $`E` gives $`E_1:s\vdash c_1\Downarrow n` and $`E_2:n\vdash W\Downarrow u` for some $`n`. Apply $`P(D_1)` to $`n` and $`E_1` to obtain $`m=n`. Rewrite $`E_2` as $`m\vdash W\Downarrow u` and apply $`P(D_2)` to $`u` and this derivation. The result is $`t=u`. The hypothesis for $`D_2` concerns the very same command $`W`. Induction on command syntax would supply no such hypothesis.

This proves $`P(D)` for every derivation $`D`. Given the two derivations in Theorem 3.2, apply $`P(D)` to the final store $`u` and the second derivation $`E` to conclude $`t=u`. $`\square`

What if $`u` were fixed before the induction? For $`D:s\vdash c\Downarrow t` the weaker induction property would be

$$`P_u(D)\coloneqq (s\vdash c\Downarrow u)\Rightarrow t=u.`

In the sequence case this gives $`P_u(D_1):(s\vdash c_1\Downarrow u)\Rightarrow m=u`. But $`E_1` ends in $`n`. In the opening example $`c_1` assigns one to $`x`, so $`n=s[x\mapsto1]`, whereas $`u=n[x\mapsto2]`. Since $`n(x)=1` and $`u(x)=2`, $`E_1` cannot supply the premise. Quantifying over the final store inside $`P` allows us to use $`n` here.

It is equally important that intermediate equality is a statement about complete stores. Imagine the suffix reads `z` rather than `x`. Knowing that the two prefix results agree at `x` alone gives no license to transfer a proof of the suffix from one input to the other. The first hypothesis yields pointwise equality for *every* lookup because its conclusion identifies stores as functions. Rewriting the suffix premise of $`E` by this equality preserves its program and final store while changing its displayed initial store to the one expected by the second hypothesis.

# Scope of the theorem
%%%
tag := "ch03-s3"
%%%

Consider $`x \neq y` and the command `x := y; y := x + 1`. If two derivations both start in a store with $`y = 5`, the result at $`x` must be 5 and at $`y` must be 6. If their initial stores differ at a third variable $`z`, their final stores can differ at $`z`. The premise “same initial store” is equality of the complete functions in Theorem 3.2.

Determinacy states that there is *at most one* final store. For example, let $`W=\mathsf{while\ true\ do\ skip}`. If $`s\vdash W\Downarrow t` had a derivation, choose one of least height. Its last rule must be iteration, and skip leaves $`s` unchanged. The second premise would therefore derive the very same judgment at smaller height, a contradiction. The empty set of final stores satisfies the uniqueness claim.

For a fixed command, a *partial function* on stores assigns a unique output to each input at which it is defined. Its *graph* is the set of those input–output pairs. Theorem 3.2 makes the terminating execution relation such a graph. For each input store the set of final stores is either empty or a singleton. In the latter case take its unique member as the output; in the former leave the function undefined.

# Exercises
%%%
tag := "ch03-s4"
number := false
%%%

*3.1.* In the proof for $`c_1;c_2`, write down the induction hypothesis for the execution of $`c_2`, including its quantifier. Locate the equality that permits its use.

*3.2.* Add a command `choose c or d` with one rule permitting any result of $`c` and another permitting any result of $`d` from the initial store. Give a one-variable counterexample and identify the step in the proof of Theorem 3.2 that fails.

*3.3.* Prove that any two finite executions of a conditional with the same guard, branches, and initial store agree when both branch relations are deterministic.

*Further problem.* A proposed command `if b then c else d` is given an additional rule allowing skip whenever the guard is false. Is determinacy preserved for all choices of branches? Give an exact condition on the false branch under which the extended conditional has at most one terminating result, assuming both branches are deterministic.

# Reading for the Seminar
%%%
tag := "ch03-s5"
number := false
%%%

*Definitions · 10 minutes.* Draw two sequence derivations with intermediate stores named independently. Read the outer universal quantifier in the theorem aloud.

*Joint proof · 30 minutes.* Write the induction property for the first tree. Invite one person to invert the second tree, another to apply the first hypothesis, and a third to substitute the equality and apply the second hypothesis.

*Proof review · 20 minutes.* Repeat the argument for a true loop. Identify precisely which hypothesis would be missing under induction on command syntax. Use Exercise 3.2 to test the proof.

*Facilitator’s hint.* Mark the starting store in each premise of the second command. Hold the second induction hypothesis fixed and ask what its argument must prove.

# Solutions and Further Reading
%%%
tag := "ch03-s6"
number := false
%%%

*3.1.* The hypothesis is $`\forall v,\ (m\vdash c_2\Downarrow v)\Rightarrow t=v`. Inversion supplies $`E_2:n\vdash c_2\Downarrow u`. The first hypothesis gives $`m=n`, so substitution supplies the premise at $`v=u`.

*3.2.* Choose between assigning 0 and assigning 1 to $`x`. Both choice rules apply in the same store and their branch results differ at $`x`. Inversion lists both rules correctly. What fails is the inference that the second derivation $`E` used the same choice rule as $`D`. The induction hypothesis for one branch cannot be applied to an execution of the other.

*3.3.* Invert each conditional derivation using the single rule in A.5. Each yields an execution of the selected command $`k`. Since $`B(b,s)` is a function of $`b` and $`s`, both select the same $`k`. Determinacy of that branch gives equality of the two final stores.

Compare the introduction and elimination of inductive predicates in _The Hitchhiker’s Guide to Logical Verification_, §9.4. When reading a mechanized proof, check which variables remain universally quantified after induction. [Lean course materials.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

*Further problem.* Take the guard constantly false, the false branch `x := 1`, and an initial store with $`s(x)=0`. The conditional rule selects the false branch and yields $`s[x\mapsto1]`, whereas the added rule can yield $`s`. Thus a proof that each branch by itself is deterministic leaves open a conflict between two applicable rules.

The exact condition is that for every store `s` where the guard is false and every `t`, if the false branch runs from `s` to `t`, then `t = s`. Necessity follows by deriving both conditional results and appealing to determinacy of the extended conditional. For sufficiency, consider a pair of derivations from one store. A true guard forces both derivations to use the true branch, where the assumed branch determinacy applies. With a false guard, the extra rule directly returns `s` and the condition forces any ordinary false-branch result to be `s` as well. A divergent false branch imposes no additional obligation at that input; the new rule supplies its only possible terminating outcome.

*Further reading · Bounded evaluation.* An evaluator that accepts a fuel bound limits the search for a derivation. Suppose it explores at most a specified derivation height and emits a result only upon constructing a complete tree. Increasing the bound can reveal a formerly unavailable result. Once a result has been certified by a tree, no larger successful run from the same inputs can certify a different store. Apply Theorem 3.2 to the two trees to obtain equality of the reported stores. To infer from a failed bounded search that no final store exists, one would also need to know that every possible successful tree fits within the given bound. A bound justified only by the size of the source command cannot supply this fact for loops whose iteration count depends on the input.
