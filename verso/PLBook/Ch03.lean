import VersoManual
import PLBook.IMP.Determinacy

open Verso.Genre Manual

#doc (Manual) "Inversion and Determinacy" =>
%%%
tag := "ch03"
file := "chapter-03"
%%%

* *Definitions.* [IMP language card A.1–A.5](imp-card/index.html), especially the six execution rules in A.5.
* *New terms.* Command determinacy, partial function and its graph. [Glossary and label key](glossary/index.html)
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

Use derivations as in [Session 1, Definition 1.5](chapter-01/index.html#ch01-s4) and their heights as in [Session 2, §2.4](chapter-02/index.html#ch02-s4). Each assignment leaf above has height zero, and each sequence root has height one.

Apply [Session 1, §1.5](chapter-01/index.html#ch01-s5) to execution trees. To prove $`\forall D,\ P(D)`, the induction hypotheses now concern the immediate execution premises of Definition 2.1. A loop premise may concern exactly the command at the root, yet the premise tree has smaller height. Induction on syntax alone would give a hypothesis for the body and none for the next execution of the loop.

Inversion ([A.3](imp-card/index.html#imp-a3)) works in the opposite direction to rule application. If $`s\vdash c_1;c_2\Downarrow t` is derivable, its last rule must be the sequence rule, so there is a store $`m` with derivations of $`s\vdash c_1\Downarrow m` and $`m\vdash c_2\Downarrow t`. As [Proposition 2.2](chapter-02/index.html#ch02-s3) shows, each inversion recovers an intermediate store from one particular derivation. For a conditional, the [single conditional rule](chapter-02/index.html#ch02-s2) is the only defining rule with that conclusion. Inverting an execution of $`I` recovers an execution of $`k`, the branch selected by $`B(b,s)`. The two derived rules construct executions for the two guard values.

For the sequence rule, let $`D` be the derivation formed from the two premises shown below. The induction step has the following form.

$$`\frac{\begin{gathered}D_1:s\vdash c_1\Downarrow m\qquad D_2:m\vdash c_2\Downarrow t\\P(D_1)\qquad P(D_2)\end{gathered}}{P(D)}\qquad(D:s\vdash(c_1;c_2)\Downarrow t)`

For $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1` with $`B(b,s)=\mathsf{true}`, let $`D` end with the loop iteration rule. Its last premise, $`m\vdash W\Downarrow t`, is another execution of $`W`.

$$`\frac{\begin{gathered}D_1:s\vdash c_1\Downarrow m\qquad D_2:m\vdash W\Downarrow t\\P(D_1)\qquad P(D_2)\end{gathered}}{P(D)}\qquad(D:s\vdash W\Downarrow t)`

Induction on height justifies this principle. For each natural number $`h`, prove $`P(D)` for every derivation $`D` of height $`h`, assuming $`P` already holds for every derivation of smaller height. By the definition of height, each immediate execution subderivation of $`D` has height at most $`h-1`, so this assumption supplies exactly the induction hypotheses that the last rule requires.

# Comparing two derivations
%%%
tag := "ch03-s2"
%%%

*Lemma 3.1 (Assignment result) \[This book\] \[Checked\].* For all $`s,x,e,t`, if $`s\vdash x:=e\Downarrow t` then $`t=s[x\mapsto\mathrm{eval}(e,s)]`.

*Proof.* The assignment rule is the only rule of A.5 whose conclusion has an assignment. So a derivation of $`s\vdash x:=e\Downarrow t` consists of that rule alone, and its conclusion forces $`t=s[x\mapsto\mathrm{eval}(e,s)]`. $`\square`

*Theorem 3.2 (Determinacy) \[This book\] \[Checked\].* For every $`c,s,t,u`, if $`s \vdash c \Downarrow t` and $`s \vdash c \Downarrow u` then $`t = u`.

We prove $`P(D)` for every derivation $`D` by induction on $`D`. The induction property is

$$`P(D)\coloneqq\forall u,\ (s\vdash c\Downarrow u)\Rightarrow t=u.`

Read $`s,c,t` from the conclusion $`s\vdash c\Downarrow t` of $`D`. The quantifier over $`u` is inside $`P(D)`. Each premise hypothesis therefore holds for every final store. We can instantiate it at the final store of the matching premise of the second derivation.

*Sequence.* Suppose $`D` ends with the sequence rule. Then $`c=c_1;c_2`, and for some store $`m` the premises of $`D` are $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash c_2\Downarrow t`. Their induction hypotheses are as follows. We name the bound store $`v` to keep it apart from the $`u` of step 1.

$$`\begin{aligned}
P(D_1)&:\quad\forall v,\ (s\vdash c_1\Downarrow v)\Rightarrow m=v,\\
P(D_2)&:\quad\forall v,\ (m\vdash c_2\Downarrow v)\Rightarrow t=v.
\end{aligned}`

1. To prove $`P(D)`, fix $`u` and assume a second derivation $`E:s\vdash(c_1;c_2)\Downarrow u`. We must show $`t=u`. The last rule of $`E` must be the sequence rule. Inversion gives a store $`n` and premises $`E_1:s\vdash c_1\Downarrow n` and $`E_2:n\vdash c_2\Downarrow u`.
2. Apply $`P(D_1)` with $`v=n` to $`E_1`. This gives $`m=n`.
3. Rewrite $`E_2` using this equality. It now proves $`m\vdash c_2\Downarrow u`.
4. Apply $`P(D_2)` with $`v=u` to the rewritten $`E_2`. This gives $`t=u`.

Step 3 needs $`m=n` as an equality of complete stores. Suppose $`c_2` were `y := z`, where $`x,y,z` are distinct. Knowing only $`m(x)=n(x)` would not turn $`E_2:n\vdash y:=z\Downarrow u` into a derivation from $`m`, because $`u(y)=n(z)` may differ from $`m(z)`. The hypothesis $`P(D_1)` gives $`m=n` as functions (A.2), so $`E_2` is already a derivation of $`m\vdash c_2\Downarrow u`.

*Skip, assignment, and conditional.* For skip, the skip rule gives $`t=s` from $`D` and $`u=s` from $`E`. For assignment, Lemma 3.1 applied to $`D` and to $`E` gives $`t=s[x\mapsto\mathrm{eval}(e,s)]=u`. For a conditional, let $`k` be the command selected by $`B(b,s)`. The premise of $`D` is $`D_1:s\vdash k\Downarrow t`, with $`P(D_1):\forall v,\ (s\vdash k\Downarrow v)\Rightarrow t=v`. Inverting the second derivation $`E` gives $`E_1:s\vdash k\Downarrow u` with the same $`k`, since $`B` is a function of the guard and the common initial store. Apply $`P(D_1)` to $`u` and $`E_1`.

*Loop exit.* If $`D` ends by the loop exit rule, then $`B(b,s)=\mathsf{false}` and $`t=s`. The loop iteration rule would require $`B(b,s)=\mathsf{true}`. The second derivation $`E` therefore uses the loop exit rule too, so $`u=s=t`.

*Loop iteration.* Suppose $`D` ends with the loop iteration rule. Then $`c=W=\mathsf{while}\ b\ \mathsf{do}\ c_1` (we write $`c_1` for the body because $`c` names the whole command), and $`D` gives $`B(b,s)=\mathsf{true}`, $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash W\Downarrow t` for some store $`m`. Its induction hypotheses are

$$`\begin{aligned}
P(D_1)&:\quad\forall v,\ (s\vdash c_1\Downarrow v)\Rightarrow m=v,\\
P(D_2)&:\quad\forall v,\ (m\vdash W\Downarrow v)\Rightarrow t=v.
\end{aligned}`

1. Fix $`u` and assume $`E:s\vdash W\Downarrow u`. We must show $`t=u`. Since $`B(b,s)=\mathsf{true}`, $`E` cannot end with the loop exit rule, which requires $`B(b,s)=\mathsf{false}`. So $`E` ends with the loop iteration rule, and inversion gives $`E_1:s\vdash c_1\Downarrow n` and $`E_2:n\vdash W\Downarrow u` for some store $`n`.
2. Apply $`P(D_1)` at $`v=n` to $`E_1`. This gives $`m=n`.
3. Rewrite $`E_2` using this equality to obtain $`m\vdash W\Downarrow u`.
4. Apply $`P(D_2)` at $`v=u` to the rewritten $`E_2`. This gives $`t=u`.

The hypothesis for $`D_2` concerns the very same command $`W`. Induction on command syntax would supply no such hypothesis.

This proves $`P(D)` for every derivation $`D`. Given the two derivations in Theorem 3.2, apply $`P(D)` to the final store $`u` and the second derivation $`E` to conclude $`t=u`. $`\square`

What if $`u` were fixed before the induction? For $`D:s\vdash c\Downarrow t` the weaker induction property would be

$$`P_u(D)\coloneqq (s\vdash c\Downarrow u)\Rightarrow t=u.`

In the sequence case this gives $`P_u(D_1):(s\vdash c_1\Downarrow u)\Rightarrow m=u`. But $`E_1` ends in $`n`. In the opening example $`c_1` assigns one to $`x`, so $`n=s[x\mapsto1]`, whereas $`u=n[x\mapsto2]`. Since $`n(x)=1` and $`u(x)=2`, $`E_1` cannot supply the premise. Quantifying over the final store inside $`P` allows us to use $`n` here.

# Scope of the theorem
%%%
tag := "ch03-s3"
%%%

Consider $`x\neq y` and the command `x := y; y := x + 1`. Take two stores $`s` and $`s'` with $`s(y)=s'(y)=5`. Both executions end with 5 at $`x` and 6 at $`y`. If $`s` and $`s'` differ at a third variable $`z`, the final stores also differ at $`z`. So "the same initial store" in Theorem 3.2 means equality of complete functions.

Determinacy states that there is *at most one* final store. We call a command *deterministic* when it has at most one final store from each initial store. Theorem 3.2 says that every IMP command is deterministic. For example, let $`W=\mathsf{while\ true\ do\ skip}`. The least-height argument in [Session 2, §2.4](chapter-02/index.html#ch02-s4) proves that this loop has no terminating derivation. The empty set of final stores satisfies the uniqueness claim.

A *partial function* from stores to stores gives at most one output for each input. At some inputs it may give none. Its *graph* is the set of its input–output pairs. Fix a command $`c`. By Theorem 3.2, for each store $`s` the set of stores $`t` with $`s\vdash c\Downarrow t` is empty or has one element. So the pairs $`(s,t)` with $`s\vdash c\Downarrow t` form the graph of a partial function. At $`s` take the unique $`t` if there is one, and leave the function undefined otherwise.

# Exercises
%%%
tag := "ch03-s4"
number := false
%%%

*3.1.* In the proof for $`c_1;c_2`, write down the induction hypothesis for the execution of $`c_2`, including its quantifier. Locate the equality that permits its use.

*3.2.* Add a command `choose c or d` with one rule permitting any result of $`c` and another permitting any result of $`d` from the initial store. Give a one-variable counterexample. Write the choice case in the style of the conditional case and identify the sentence of the conditional case that has no counterpart.

*3.3.* Prove that any two finite executions of a conditional with the same guard, branches, and initial store agree when both branches are deterministic.

*Further problem.* A proposed command `if b then c else d` is given an additional rule. If $`B(b,s)=\mathsf{false}`, the rule concludes $`s\vdash\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d\Downarrow s`. Is determinacy preserved for all choices of branches? Give an exact condition on the false branch under which the extended conditional has at most one terminating result, assuming both branches are deterministic.

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

*3.2.* Choose between assigning 0 and assigning 1 to $`x`. Both choice rules apply in the same store and their branch results differ at $`x`. Inversion lists both rules correctly. What fails is the inference that the second derivation $`E` used the same choice rule as $`D`. The induction hypothesis for one branch cannot be applied to an execution of the other. In the conditional case this is the sentence identifying the selected command: “with the same $`k`, since $`B` is a function of the guard and the common initial store.”

*3.3.* Invert each conditional derivation using the single rule in A.5. Each yields an execution of the selected command $`k`. Since $`B(b,s)` is a function of $`b` and $`s`, both select the same $`k`. Determinacy of that branch gives equality of the two final stores.

*Further problem.* Take the guard constantly false, the false branch `x := 1`, and an initial store with $`s(x)=0`. The conditional rule selects the false branch and yields $`s[x\mapsto1]`, whereas the added rule can yield $`s`. Thus a proof that each branch by itself is deterministic leaves open a conflict between two applicable rules.

The exact condition is that for every store $`s` where the guard is false and every $`t`, if the false branch runs from $`s` to $`t`, then $`t = s`. Necessity follows by deriving both conditional results and appealing to determinacy of the extended conditional. For sufficiency, consider a pair of derivations from one store. A true guard forces both derivations to use the true branch, where the assumed branch determinacy applies. With a false guard, the extra rule directly returns $`s` and the condition forces any ordinary false-branch result to be $`s` as well. A divergent false branch imposes no additional obligation at that input; the new rule supplies its only possible terminating outcome.

Compare the introduction and elimination of inductive predicates in _The Hitchhiker’s Guide to Logical Verification_, §9.4. When reading a mechanized proof, check which variables remain universally quantified after induction. [Lean course materials.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

*Further reading · Bounded evaluation.* An evaluator that accepts a fuel bound limits the search for a derivation. Suppose it explores at most a specified derivation height and emits a result only upon constructing a complete tree. Increasing the bound can reveal a formerly unavailable result. Once a result has been certified by a tree, no larger successful run from the same inputs can certify a different store. Apply Theorem 3.2 to the two trees to obtain equality of the reported stores. To infer from a failed bounded search that no final store exists, one would also need to know that every possible successful tree fits within the given bound. A bound justified only by the size of the source command cannot supply this fact for loops whose iteration count depends on the input.
