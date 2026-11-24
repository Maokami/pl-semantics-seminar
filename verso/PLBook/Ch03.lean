import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Inversion and Determinacy" =>
%%%
tag := "ch03"
file := "chapter-03"
%%%

[Chapter PDF](print/chapter-03.pdf) · [Session 3](seminar/index.html#week-03)

Two people derive terminating executions of the same program from the same store. Their proofs introduce different names for the intermediate stores. To compare their final results one must first prove that those intermediate stores agree. The example exposes a choice in the induction statement that also occurs in proofs about type systems and compilers.

*Sources.* Winskel, _The Formal Semantics of Programming Languages_, §3.4, on induction over derivations. Read the command rules of §2.4 alongside the induction principle. We use the integer IMP and the seven rules of Chapter 2. The shared proof is the sequence case of Theorem 3.2. [Winskel, chapters 2–3.](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)

# Induction over evidence
%%%
tag := "ch03-s1"
%%%

A derivation of $`s \vdash c \Downarrow t` is a finite tree of applications of the execution rules. Its height is zero for an axiom and one plus the maximum height of its immediate execution subderivations when it has any. Treat a guard test as a side condition. With this convention the false loop rule also has height zero.

To prove a statement for all such derivations, show that each rule preserves the statement when it holds for the immediate subderivations. This follows by induction on height. A loop premise may concern exactly the command at the root, yet the premise tree has smaller height. Induction on syntax alone would give a hypothesis for the body and none for the next execution of the loop.

*Inversion* works in the opposite direction to rule application. If $`s \vdash c\ \text{;}\ d \Downarrow t` is derivable, its last rule must be sequence, so there exists $`u` with derivations of $`s \vdash c \Downarrow u` and $`u \vdash d \Downarrow t`. An existential witness is obtained from that particular tree. Two separate inversions need not initially produce the same witness.

Write the induction principle for a sequence as a conditional statement about four objects: a derivation for its prefix, a derivation for its suffix, and a proof of the desired property for each of those derivations. Only after introducing those four objects may we conclude the property for the compound derivation. The hypotheses apply to the actual children in the supplied tree. They cannot be applied to an arbitrary future execution of either command unless the property itself quantifies over such executions.

Height induction explains that restriction. Suppose the claim holds for every derivation shorter than height `h`, and inspect a tree of height `h`. Each child has smaller height, so the property is available for that child including all quantifiers *inside* the property. Extra variables that were fixed outside the induction remain fixed, however. For determinacy this difference is decisive: the competing tree at the root ends in one state, but its competing prefix ends in an intermediate state. Choosing the rival result inside the induction property is what permits its later instantiation at both places. This is the same strengthening one makes in arithmetic induction when a recursive call changes an auxiliary parameter.

# Comparing two derivations
%%%
tag := "ch03-s2"
%%%

*Lemma 3.1 (Update uniqueness).* For fixed $`s,x,e`, every execution of $`x \mathrel{:=} e` from $`s` ends in $`s\left\lbrack {x\mapsto\operatorname{eval}\left( {e,s} \right)} \right\rbrack`. Inversion leaves only the assignment rule. Chapter 1 supplies a single integer $`\operatorname{eval}\left( {e,s} \right)`, and state update names a single function. Thus any two resulting states agree at $`x` and at every other name.

*Theorem 3.2 (Determinacy).* For every $`c,s,t,u`, if $`s \vdash c \Downarrow t` and $`s \vdash c \Downarrow u` then $`t = u`.

*Induction assertion.* Choose the first derivation $`D` of $`s \vdash c \Downarrow t`. Prove the property

$$`P(D)\quad ≔ \quad\forall u,\bigl(s \vdash c \Downarrow u\bigr)\Longrightarrow t = u.`

The rival final state and its derivation may be chosen anew at each induction hypothesis. The command and its initial state at a child are fixed by the first derivation at that child.

*Sequence.* Write $`D_{1}:\bigl(s \vdash c \Downarrow m\bigr)` and $`D_{2}:\bigl(m \vdash d \Downarrow t\bigr)` for the premises of $`D`. Now choose any rival sequence derivation ending in $`u`. Invert it to obtain $`E_{1}:\bigl(s \vdash c \Downarrow n\bigr)` and $`E_{2}:\bigl(n \vdash d \Downarrow u\bigr)`. The induction hypothesis for $`D_{1}` applies to $`E_{1}`, giving $`m = n`. Replace $`n` by $`m` in $`E_{2}`. The induction hypothesis for $`D_{2}` now applies to $`E_{2}` and yields $`t = u`. Applying this second hypothesis before the replacement would require $`E_{2}` to start in $`m`, a fact the inversion alone did not supply.

*Skip, assignment, and conditional.* Both skip derivations end in $`s`. Lemma 3.1 handles assignment. At a conditional the guard is evaluated in the common state $`s` by a total Boolean function. Thus both derivations select the same branch. Apply the hypothesis for that branch’s derivation.

*Loop exit.* If $`D` ends because the guard is false, a rival true rule would require the guard to be true at the same state. The rival derivation must therefore use the exit rule, with result $`s`.

*Loop iteration.* If $`D` ends by the true rule, the rival must also use that rule. Invert both to obtain body derivations from $`s` and recursive loop derivations from their respective body results. First use the body hypothesis to identify those results. The second hypothesis, for the recursive loop derivation in $`D`, now identifies the two final states. Both uses concern strict subtrees of $`D`. This exhausts the execution rules. $`\square`

Here is the obstacle if the rival result is fixed too soon. Consider a sequence that writes one to `x` and then writes two to `x`. Suppose the induction property for every subtree says only that any competitor *ending with two at x* has the same result as that subtree. The desired root competitor does end with two. After inverting it, the competing execution of the first assignment ends with one. Feeding that premise to the weakened induction hypothesis would require one to equal two. The command is deterministic; the proposed induction property has simply discarded the case needed to prove it.

It is equally important that intermediate equality is a statement about complete stores. Imagine the suffix reads `z` rather than `x`. Knowing that the two prefix results agree at `x` alone gives no license to transfer a proof of the suffix from one input to the other. The first hypothesis yields pointwise equality for *every* lookup because its conclusion identifies states as functions. Rewriting the competitor's suffix premise by this equality preserves its program and final state while changing its displayed initial state to the one expected by the second hypothesis.

The sequence argument can be checked for arbitrary relations. Here `e` and `f` express determinacy of the prefix and suffix. The proof first identifies their inputs at the join; only then can `f` compare the two suffix derivations.

```lean
example {S : Type} (R T : S → S → Prop)
    (e : ∀ s u v, R s u → R s v → u = v)
    (f : ∀ s u v, T s u → T s v → u = v)
    {s t t' : S} (h : ∃ u, R s u ∧ T u t)
    (k : ∃ v, R s v ∧ T v t') : t = t' := by
  obtain ⟨u, hu, ht⟩ := h
  obtain ⟨v, hv, ht'⟩ := k
  cases e s u v hu hv
  exact f u t t' ht ht'
```

# Scope of the theorem
%%%
tag := "ch03-s3"
%%%

Consider $`x \neq y` and the command `x := y; y := x + 1`. If two derivations both start in a store with $`y = 5`, the result at $`x` must be 5 and at $`y` must be 6. If their initial stores differ at a third variable $`z`, their final stores can differ at $`z`. The premise “same initial state” is equality of the complete functions in Theorem 3.2.

Determinacy states *at most one* final state. The empty set of final states satisfies that condition. An always-true loop with body skip has no finite derivation, as shown in Chapter 2. A terminating implementation of a bounded evaluator can also exhaust its depth bound on an execution whose ordinary derivation is merely taller than the bound. Neither situation supplies two distinct final states.

Determinacy makes a terminating relation the graph of a *partial* function. For each input store form the set of final stores appearing in terminating judgments. The theorem says that this set is either empty or a singleton. A mathematical partial function can therefore assign to the input the unique member in the singleton case and be undefined in the empty case. This construction describes a semantic object; it does not give an algorithm for choosing between empty and singleton sets by inspecting arbitrary command syntax.

An evaluator that accepts a fuel bound answers a different question. Suppose it explores at most a specified derivation height and emits a result only upon constructing a complete tree. Increasing the bound can reveal a formerly unavailable result. Once a result has been certified by a tree, no larger successful run from the same inputs can certify a different state. Theorem 3.2 proves precisely that stability assertion. To infer from a failed bounded search that no final state exists, one would also need to know that every possible successful tree fits within the given bound. A bound justified only by the size of the source command cannot supply this fact for loops whose iteration count depends on the input.

# Exercises
%%%
tag := "ch03-s4"
number := false
%%%

*3.1.* In the sequence proof write down the type of the second induction hypothesis with its quantifier. Locate the equality that permits its use.

*3.2.* Add a command `choose c or d` with one rule permitting any result of $`c` and another permitting any result of $`d` from the original state. Give a one-variable counterexample to Theorem 3.2 and identify the invalid inversion step.

*3.3.* Prove that any two finite executions of a conditional with the same guard, branches, and initial state agree when both branch relations are deterministic.

*Further problem.* A proposed command `if b then c else d` is given an additional rule allowing skip whenever the guard is false. Is determinacy preserved for all choices of branches? Give an exact condition on the false branch under which the extended conditional has at most one terminating result, assuming both branches are deterministic.

# Reading for the Seminar
%%%
tag := "ch03-s5"
number := false
%%%

*Definitions · 10 minutes.* Draw two sequence derivations with middle states named independently. Read the outer universal quantifier in the theorem aloud.

*Joint proof · 30 minutes.* Write the induction property for the first tree. Invite one person to invert the second tree, another to apply the first hypothesis, and a third to substitute the equality and apply the second hypothesis.

*Proof review · 20 minutes.* Repeat the argument for a true loop. Identify precisely which hypothesis would be missing under induction on command syntax. Use Exercise 3.2 to test the proof.

*Facilitator’s hint.* Mark the starting state in each premise of the second command. Hold the second induction hypothesis fixed and ask what its argument must prove.

# Solutions and Further Reading
%%%
tag := "ch03-s6"
number := false
%%%

*3.1.* The hypothesis is $`\forall u,\bigl(m \vdash d \Downarrow u\bigr)\Longrightarrow t = u`. Inversion supplies $`n \vdash d \Downarrow u`. The first hypothesis gives $`m = n`, so substitution supplies a derivation with start state $`m`.

*3.2.* Choose between assigning 0 and assigning 1 to $`x`. Both choice rules apply in the same state and their branch results differ at $`x`. The last-rule argument used for conditionals relied on incompatible guard conditions. The new rules have no such side conditions.

*3.3.* Invert both derivations. If the test is true both use the first branch, whose determinacy identifies the results. The false case uses determinacy of the second branch. Mixed cases would give both truth values to one Boolean evaluation.

Compare the introduction and elimination of inductive predicates in _The Hitchhiker’s Guide to Logical Verification_, §9.4. When reading a mechanized proof, check which variables remain universally quantified after induction. [Lean course materials.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

*Further problem.* Take the guard constantly false, the false branch `x := 1`, and an initial store with `s(x) = 0`. The original false rule yields `s[x ↦ 1]`, whereas the added rule can yield `s`. Thus a proof that each branch by itself is deterministic leaves open a conflict between two applicable rules.

The exact condition is that for every store `s` where the guard is false and every `t`, if the false branch runs from `s` to `t`, then `t = s`. Necessity follows by deriving both conditional results and appealing to determinacy of the extended conditional. For sufficiency, consider a pair of derivations from one store. A true guard forces both derivations to use the true branch, where the assumed branch determinacy applies. With a false guard, the extra rule directly returns `s` and the condition forces any ordinary false-branch result to be `s` as well. A divergent false branch imposes no additional obligation at that input; the new rule supplies its only possible terminating outcome.
