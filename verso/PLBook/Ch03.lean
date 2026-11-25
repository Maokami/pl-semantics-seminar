import VersoManual
import PLBook.IMP.Determinacy

open Verso.Genre Manual

#doc (Manual) "Inversion and Determinacy" =>
%%%
tag := "ch03"
file := "chapter-03"
%%%

Two people derive terminating executions of the same program from the same state. Their proofs introduce different names for the intermediate states. To compare their final results one must first prove that those intermediate states agree. The example exposes a choice in the induction property that also occurs in proofs about type systems and compilers.

*In this session.*

* *Definitions.* [IMP language card A.1–A.5](imp-card/index.html), especially the six execution rules in A.5 (Session 2, Definition 2.1). Inversion ([Session 1, §1.4](chapter-01/index.html#ch01-s4)) and induction on derivations ([Session 1, §1.5](chapter-01/index.html#ch01-s5)). The height of an execution derivation ([Session 2, §2.4](chapter-02/index.html#ch02-s4)) and sequence inversion ([Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3)).
* *New terms.* Command determinacy, partial function and its graph. [Glossary](glossary/index.html)
* *Theorem 3.2 (Determinacy).* For every command $`c` and states $`\sigma,\sigma',\sigma''`, if $`\sigma\vdash c\Downarrow\sigma'` and $`\sigma\vdash c\Downarrow\sigma''`, then $`\sigma'=\sigma''`.
* *Board case.* Sequencing. Invert the second derivation $`E` and identify the intermediate states before comparing the final states.
* *Proof outline.* For $`D:\sigma\vdash c\Downarrow\sigma'`, take $`P(D)\coloneqq\forall \sigma'',\ (\sigma\vdash c\Downarrow\sigma'')\Rightarrow \sigma'=\sigma''`. Quantify $`\sigma''` inside the induction property so the first induction hypothesis can be applied at the intermediate state and the second at the final state.
* *From Session 2.* Inverting one sequence derivation gave an intermediate state. Here each derivation supplies its own intermediate state. The first induction hypothesis proves that the two states are equal.

# Induction over evidence
%%%
tag := "ch03-s1"
%%%

Consider two derivations for `x := 1; x := 2` starting in the same state $`\sigma`. In $`D` name the intermediate state $`\sigma_1` and the final state $`\sigma'`. In the second derivation $`E` use $`\sigma_2` and $`\sigma''`. Each leaf below is an instance of the assignment rule.

$$`D:\quad\frac{\dfrac{}{\sigma\vdash x:=1\Downarrow\sigma_1}\qquad\dfrac{}{\sigma_1\vdash x:=2\Downarrow\sigma'}}{\sigma\vdash(x:=1\,;\,x:=2)\Downarrow\sigma'}`

$$`E:\quad\frac{\dfrac{}{\sigma\vdash x:=1\Downarrow\sigma_2}\qquad\dfrac{}{\sigma_2\vdash x:=2\Downarrow\sigma''}}{\sigma\vdash(x:=1\,;\,x:=2)\Downarrow\sigma''}`

To compare the executions of the second assignment from the same state, we first need $`\sigma_1=\sigma_2`. Here both left leaves give $`\sigma[x\mapsto1]`. The right leaves give $`\sigma'=\sigma_1[x\mapsto2]` and $`\sigma''=\sigma_2[x\mapsto2]`. In §3.2 the first command can itself be a loop, so identifying the intermediate states will require an induction hypothesis.

Use derivations as in [Session 1, Definition 1.5](chapter-01/index.html#ch01-s4) and their heights as in [Session 2, §2.4](chapter-02/index.html#ch02-s4). Each assignment leaf above has height zero, and each sequence root has height one.

Apply [Session 1, §1.5](chapter-01/index.html#ch01-s5) to execution trees. To prove $`\forall D,\ P(D)`, the induction hypotheses now concern the immediate execution premises of Session 2, Definition 2.1. A loop premise may concern exactly the command at the root, yet the premise tree has smaller height. Induction on syntax alone would give a hypothesis for the body and none for the next execution of the loop.

Inversion ([A.3](imp-card/index.html#imp-a3)) works in the opposite direction to rule application. If $`\sigma\vdash c_1;c_2\Downarrow\sigma'` is derivable, its last rule must be the sequence rule, so there is a state $`\sigma_1` with derivations of $`\sigma\vdash c_1\Downarrow\sigma_1` and $`\sigma_1\vdash c_2\Downarrow\sigma'`. As [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3) shows, each inversion recovers an intermediate state from one particular derivation. For a conditional, the [single conditional rule](chapter-02/index.html#ch02-s2) is the only defining rule with that conclusion. Inverting an execution of $`I` recovers an execution of $`k`, the branch selected by $`B(b,\sigma)`. The two derived rules construct executions for the two guard values.

For the sequence rule, let $`D` be the derivation formed from the two premises shown below. The induction step has the following form.

$$`\frac{\begin{gathered}D_1:\sigma\vdash c_1\Downarrow\sigma_1\qquad D_2:\sigma_1\vdash c_2\Downarrow\sigma'\\P(D_1)\qquad P(D_2)\end{gathered}}{P(D)}\qquad(D:\sigma\vdash(c_1;c_2)\Downarrow\sigma')`

For $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1` with $`B(b,\sigma)=\mathsf{true}`, let $`D` end with the loop iteration rule. Its last premise, $`\sigma_1\vdash W\Downarrow\sigma'`, is another execution of $`W`.

$$`\frac{\begin{gathered}D_1:\sigma\vdash c_1\Downarrow\sigma_1\qquad D_2:\sigma_1\vdash W\Downarrow\sigma'\\P(D_1)\qquad P(D_2)\end{gathered}}{P(D)}\qquad(D:\sigma\vdash W\Downarrow\sigma')`

Induction on height justifies this principle. For each natural number $`h`, prove $`P(D)` for every derivation $`D` of height $`h`, assuming $`P` already holds for every derivation of smaller height. By the definition of height, each immediate execution subderivation of $`D` has height at most $`h-1`, so this assumption supplies exactly the induction hypotheses that the last rule requires.

# Comparing two derivations
%%%
tag := "ch03-s2"
%%%

*Lemma 3.1 (Assignment result).* For all $`\sigma,x,e,\sigma'`, if $`\sigma\vdash x:=e\Downarrow\sigma'` then $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`.

*Proof.* The assignment rule is the only rule of A.5 whose conclusion has an assignment. So a derivation of $`\sigma\vdash x:=e\Downarrow\sigma'` consists of that rule alone, and its conclusion forces $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. $`\square`

*Theorem 3.2 (Determinacy).* For every $`c,\sigma,\sigma',\sigma''`, if $`\sigma \vdash c \Downarrow \sigma'` and $`\sigma \vdash c \Downarrow \sigma''` then $`\sigma' = \sigma''`.

We prove $`P(D)` for every derivation $`D` by induction on $`D`. The induction property is

$$`P(D)\coloneqq\forall \sigma'',\ (\sigma\vdash c\Downarrow\sigma'')\Rightarrow \sigma'=\sigma''.`

Read $`\sigma,c,\sigma'` from the conclusion $`\sigma\vdash c\Downarrow\sigma'` of $`D`. The quantifier over $`\sigma''` is inside $`P(D)`. Each premise hypothesis therefore holds for every final state. We can instantiate it at the final state of the matching premise of the second derivation.

*Sequence.* Suppose $`D` ends with the sequence rule. Then $`c=c_1;c_2`, and for some state $`\sigma_1` the premises of $`D` are $`D_1:\sigma\vdash c_1\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash c_2\Downarrow\sigma'`. Their induction hypotheses are as follows. We name the bound state $`\sigma'''` to keep it apart from the $`\sigma''` of step 1.

$$`\begin{aligned}
P(D_1)&:\quad\forall \sigma''',\ (\sigma\vdash c_1\Downarrow\sigma''')\Rightarrow \sigma_1=\sigma''',\\
P(D_2)&:\quad\forall \sigma''',\ (\sigma_1\vdash c_2\Downarrow\sigma''')\Rightarrow \sigma'=\sigma'''.
\end{aligned}`

1. To prove $`P(D)`, fix $`\sigma''` and assume a second derivation $`E:\sigma\vdash(c_1;c_2)\Downarrow\sigma''`. We must show $`\sigma'=\sigma''`. The last rule of $`E` must be the sequence rule. Inversion gives a state $`\sigma_2` and premises $`E_1:\sigma\vdash c_1\Downarrow\sigma_2` and $`E_2:\sigma_2\vdash c_2\Downarrow\sigma''`.
2. Apply $`P(D_1)` with $`\sigma'''=\sigma_2` to $`E_1`. This gives $`\sigma_1=\sigma_2`.
3. Rewrite $`E_2` using this equality. It now proves $`\sigma_1\vdash c_2\Downarrow\sigma''`.
4. Apply $`P(D_2)` with $`\sigma'''=\sigma''` to the rewritten $`E_2`. This gives $`\sigma'=\sigma''`.

Step 3 needs $`\sigma_1=\sigma_2` as an equality of complete states. Suppose $`c_2` were `y := z`, where $`x,y,z` are distinct. Knowing only $`\sigma_1(x)=\sigma_2(x)` would not turn $`E_2:\sigma_2\vdash y:=z\Downarrow\sigma''` into a derivation from $`\sigma_1`, because $`\sigma''(y)=\sigma_2(z)` may differ from $`\sigma_1(z)`. The hypothesis $`P(D_1)` gives $`\sigma_1=\sigma_2` as functions (A.2), so $`E_2` is already a derivation of $`\sigma_1\vdash c_2\Downarrow\sigma''`.

*Skip, assignment, and conditional.* For skip, the skip rule gives $`\sigma'=\sigma` from $`D` and $`\sigma''=\sigma` from $`E`. For assignment, Lemma 3.1 applied to $`D` and to $`E` gives $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]=\sigma''`. For a conditional, let $`k` be the command selected by $`B(b,\sigma)`. The premise of $`D` is $`D_1:\sigma\vdash k\Downarrow\sigma'`, with $`P(D_1):\forall \sigma''',\ (\sigma\vdash k\Downarrow\sigma''')\Rightarrow \sigma'=\sigma'''`. Inverting the second derivation $`E` gives $`E_1:\sigma\vdash k\Downarrow\sigma''` with the same $`k`, since $`B` is a function of the guard and the common initial state. Apply $`P(D_1)` to $`\sigma''` and $`E_1`.

*Loop exit.* If $`D` ends by the loop exit rule, then $`B(b,\sigma)=\mathsf{false}` and $`\sigma'=\sigma`. The loop iteration rule would require $`B(b,\sigma)=\mathsf{true}`. The second derivation $`E` therefore uses the loop exit rule too, so $`\sigma''=\sigma=\sigma'`.

*Loop iteration.* Suppose $`D` ends with the loop iteration rule. Then $`c=W=\mathsf{while}\ b\ \mathsf{do}\ c_1` (we write $`c_1` for the body because $`c` names the whole command), and $`D` gives $`B(b,\sigma)=\mathsf{true}`, $`D_1:\sigma\vdash c_1\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash W\Downarrow\sigma'` for some state $`\sigma_1`. Its induction hypotheses are

$$`\begin{aligned}
P(D_1)&:\quad\forall \sigma''',\ (\sigma\vdash c_1\Downarrow\sigma''')\Rightarrow \sigma_1=\sigma''',\\
P(D_2)&:\quad\forall \sigma''',\ (\sigma_1\vdash W\Downarrow\sigma''')\Rightarrow \sigma'=\sigma'''.
\end{aligned}`

1. Fix $`\sigma''` and assume $`E:\sigma\vdash W\Downarrow\sigma''`. We must show $`\sigma'=\sigma''`. Since $`B(b,\sigma)=\mathsf{true}`, $`E` cannot end with the loop exit rule, which requires $`B(b,\sigma)=\mathsf{false}`. So $`E` ends with the loop iteration rule, and inversion gives $`E_1:\sigma\vdash c_1\Downarrow\sigma_2` and $`E_2:\sigma_2\vdash W\Downarrow\sigma''` for some state $`\sigma_2`.
2. Apply $`P(D_1)` at $`\sigma'''=\sigma_2` to $`E_1`. This gives $`\sigma_1=\sigma_2`.
3. Rewrite $`E_2` using this equality to obtain $`\sigma_1\vdash W\Downarrow\sigma''`.
4. Apply $`P(D_2)` at $`\sigma'''=\sigma''` to the rewritten $`E_2`. This gives $`\sigma'=\sigma''`.

The hypothesis for $`D_2` concerns the very same command $`W`. Induction on command syntax would supply no such hypothesis.

This proves $`P(D)` for every derivation $`D`. Given the two derivations in Theorem 3.2, apply $`P(D)` to the final state $`\sigma''` and the second derivation $`E` to conclude $`\sigma'=\sigma''`. $`\square`

What if $`\sigma''` were fixed before the induction? For $`D:\sigma\vdash c\Downarrow\sigma'` the weaker induction property would be

$$`P_{\sigma''}(D)\coloneqq (\sigma\vdash c\Downarrow\sigma'')\Rightarrow \sigma'=\sigma''.`

In the sequence case this gives $`P_{\sigma''}(D_1):(\sigma\vdash c_1\Downarrow\sigma'')\Rightarrow \sigma_1=\sigma''`. But $`E_1` ends in $`\sigma_2`. In the opening example $`c_1` assigns one to $`x`, so $`\sigma_2=\sigma[x\mapsto1]`, whereas $`\sigma''=\sigma_2[x\mapsto2]`. Since $`\sigma_2(x)=1` and $`\sigma''(x)=2`, $`E_1` cannot supply the premise. Quantifying over the final state inside $`P` allows us to use $`\sigma_2` here.

# Scope of the theorem
%%%
tag := "ch03-s3"
%%%

Consider $`x\neq y` and the command `x := y; y := x + 1`. Take two states $`\sigma` and $`\sigma'` with $`\sigma(y)=\sigma'(y)=5`. Both executions end with 5 at $`x` and 6 at $`y`. If $`\sigma` and $`\sigma'` differ at a third variable $`z`, the final states also differ at $`z`. So "the same initial state" in Theorem 3.2 means equality of complete functions.

Determinacy states that there is *at most one* final state. As [Session 1, Corollary 1.4](chapter-01/index.html#ch01-s5) called the evaluation judgment deterministic, we call a command *deterministic* when it has at most one final state from each initial state. Theorem 3.2 says that every IMP command is deterministic. For example, let $`W=\mathsf{while\ true\ do\ skip}`. The least-height argument in [Session 2, §2.4](chapter-02/index.html#ch02-s4) proves that this loop has no terminating derivation. The empty set of final states satisfies the uniqueness claim.

A *partial function* from states to states gives at most one output for each input. At some inputs it may give none. Its *graph* is the set of its input–output pairs. Fix a command $`c`. By Theorem 3.2, for each state $`\sigma` the set of states $`\sigma'` with $`\sigma\vdash c\Downarrow\sigma'` is empty or has one element. So the pairs $`(\sigma,\sigma')` with $`\sigma\vdash c\Downarrow\sigma'` form the graph of a partial function. At $`\sigma` take the unique $`\sigma'` if there is one, and leave the function undefined otherwise.

# Exercises
%%%
tag := "ch03-s4"
number := false
%%%

*3.1.* In the proof for $`c_1;c_2`, write down the induction hypothesis for the execution of $`c_2`, including its quantifier. Locate the equality that permits its use.

*3.2.* Add a command `choose c or d` with one rule permitting any result of $`c` and another permitting any result of $`d` from the initial state. Give a one-variable counterexample. Write the choice case in the style of the conditional case and identify the sentence of the conditional case that has no counterpart.

*3.3.* Prove that any two finite executions of a conditional with the same guard, branches, and initial state agree when both branches are deterministic.

*Further problem.* A proposed command `if b then c else d` is given an additional rule. If $`B(b,\sigma)=\mathsf{false}`, the rule concludes $`\sigma\vdash\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d\Downarrow\sigma`. Is determinacy preserved for all choices of branches? Give an exact condition on the false branch under which the extended conditional has at most one terminating result, assuming both branches are deterministic.

# Reading for the Seminar
%%%
tag := "ch03-s5"
number := false
%%%

*Definitions · 10 minutes.* Draw two sequence derivations with intermediate states named independently. Read the outer universal quantifier in the theorem aloud.

*Joint proof · 30 minutes.* Write the induction property for the first tree. Invite one person to invert the second tree, another to apply the first hypothesis, and a third to substitute the equality and apply the second hypothesis.

*Proof review · 20 minutes.* Repeat the argument for a true loop. Identify precisely which hypothesis would be missing under induction on command syntax. Use Exercise 3.2 to test the proof.

*Facilitator’s hint.* Mark the starting state in each premise of the second command. Hold the second induction hypothesis fixed and ask what its argument must prove.

# Solutions and Further Reading
%%%
tag := "ch03-s6"
number := false
%%%

*3.1.* The hypothesis is $`\forall \sigma''',\ (\sigma_1\vdash c_2\Downarrow\sigma''')\Rightarrow \sigma'=\sigma'''`. Inversion supplies $`E_2:\sigma_2\vdash c_2\Downarrow\sigma''`. The first hypothesis gives $`\sigma_1=\sigma_2`, so substitution supplies the premise at $`\sigma'''=\sigma''`.

*3.2.* Choose between assigning 0 and assigning 1 to $`x`. Both choice rules apply in the same state and their branch results differ at $`x`. Inversion lists both rules correctly. What fails is the inference that the second derivation $`E` used the same choice rule as $`D`. The induction hypothesis for one branch cannot be applied to an execution of the other. In the conditional case this is the sentence identifying the selected command: “with the same $`k`, since $`B` is a function of the guard and the common initial state.”

*3.3.* Invert each conditional derivation using the single rule in A.5. Each yields an execution of the selected command $`k`. Since $`B(b,\sigma)` is a function of $`b` and $`\sigma`, both select the same $`k`. Determinacy of that branch gives equality of the two final states.

*Further problem.* Take the guard constantly false, the false branch `x := 1`, and an initial state with $`\sigma(x)=0`. The conditional rule selects the false branch and yields $`\sigma[x\mapsto1]`, whereas the added rule can yield $`\sigma`. Thus a proof that each branch by itself is deterministic leaves open a conflict between two applicable rules.

The exact condition is that for every state $`\sigma` where the guard is false and every $`\sigma'`, if the false branch runs from $`\sigma` to $`\sigma'`, then $`\sigma' = \sigma`. Necessity follows by deriving both conditional results and appealing to determinacy of the extended conditional. For sufficiency, consider a pair of derivations from one state. A true guard forces both derivations to use the true branch, where the assumed branch determinacy applies. With a false guard, the extra rule directly returns $`\sigma` and the condition forces any ordinary false-branch result to be $`\sigma` as well. A divergent false branch imposes no additional obligation at that input; the new rule supplies its only possible terminating outcome.

Compare the introduction and elimination of inductive predicates in _The Hitchhiker’s Guide to Logical Verification_, §9.4. When reading a mechanized proof, check which variables remain universally quantified after induction. [Lean course materials.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

*Further reading · Bounded execution.* An interpreter that accepts a fuel bound limits the search for a derivation. Suppose it explores at most a specified derivation height and emits a result only upon constructing a complete tree. Increasing the bound can reveal a formerly unavailable result. Once a result has been certified by a tree, no larger successful run from the same inputs can certify a different state. Apply Theorem 3.2 to the two trees to obtain equality of the reported states. To infer from a failed bounded search that no final state exists, one would also need to know that every possible successful tree fits within the given bound. A bound justified only by the size of the source command cannot supply this fact for loops whose iteration count depends on the input.

# Sources and Formalization
%%%
tag := "ch03-notes"
number := false
%%%

The execution relation is defined by the six big-step rules for commands in Xavier Leroy’s compiler verification course (IMP, as presented in A.5). Nipkow and Klein prove the corresponding theorem for their IMP in _Concrete Semantics_, §7.2.5. [Source and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf)

* *Lemma 3.1.* Formulated in this book. Checked in Lean ([`assignmentResult`](lean/Determinacy.html#assignmentResult) · [IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 3.2.* Formulated in this book. Corresponds to CS Lemma 7.9. Checked in Lean ([`deterministic`](lean/Determinacy.html#deterministic) · [IMP card references](imp-card/index.html#imp-sources)).
