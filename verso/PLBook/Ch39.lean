import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Abstract Interpretation and Analysis Soundness" =>
%%%
tag := "ch39"
file := "chapter-39"
%%%

[Chapter PDF](print/chapter-39.pdf) · [Session 39](seminar/index.html#week-39)

If both branches assign seven to a variable, the assignment is known after the join even when the test itself cannot be decided statically. If one branch assigns eight, keeping seven as an unconditional fact would be unsound. An abstract state gives precise meaning to “known” by specifying the concrete states consistent with it.

*Sources.* Leroy’s _Compiler Verification_ course, Lean port, `Constprop.lean`. Read `matches'`, `Le`, `Join` and the conditional case of `Cexec_sound`. For the general pattern of concretization and sound transfer, compare _Concrete Semantics_, chapter 13. [Abstract stores.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Constprop.lean#L214-L254) [Transfer and soundness.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Constprop.lean#L431-L482) [Concrete Semantics.](https://concrete-semantics.org/concrete-semantics.pdf)

# Known constants
%%%
tag := "ch39-s1"
%%%

A concrete store $`s` assigns every variable an integer. An abstract store $`S` is a finite partial map from variables to integers. An absent key signifies an unknown value. Say $`s` matches $`S` if for every entry $`x\mapsto n` of $`S`, $`s(x) = n`. Write $`\gamma(S)` for the set of matching concrete states; this set is the *concretization*. The empty abstract map, Top, represents every concrete store.

Order stores by loss of precision: $`S \sqsubseteq T` when every entry of $`T` also occurs in $`S` with the same value. Then $`\gamma(S) \subseteq \gamma(T)`, since a concrete state satisfying all of the stronger facts also satisfies the retained facts. The join $`S \sqcup T` retains exactly their common entries. Both operands are below it, and any common upper bound can require only entries common to both, proving that it is the least upper bound. Its concretization contains the union of the two concrete sets but can be larger.

View a map as a finite conjunction of equations. The abstract state recording x = 3 and y = 5 represents precisely the stores satisfying both. Deleting the equation about y admits stores with any value there while preserving the restriction on x. This example fixes the direction of the order without relying on a diagram: if S contains both facts and T only the first, every model of S is a model of T. Conversely, a store with x = 3 and y = 8 is a model of T outside the concretization of S.

The word “top” refers to this order on *sets of possibilities*. The top map contains zero bindings and represents the largest possible set of concrete stores. Joining it with a nonempty constant map again yields top. One way to check this calculation is to choose any variable allegedly still fixed in the join. Since a state drawn from top can assign that variable any integer, there is no fixed value valid for all of those inputs. Even a domain representing arbitrary disjunctions must admit all stores here, because one input already denotes all stores. In the example in the final section, both branches impose a restriction; there a disjunctive domain can retain information lost by the join.

# Transfer and joins
%%%
tag := "ch39-s2"
%%%

Abstract evaluation of a literal returns the known integer. A variable lookup may return unknown. For addition or subtraction, if both operands are known return the arithmetic result; otherwise return unknown. Whenever this evaluator returns a known integer, every matching concrete state gives that integer, by induction on the expression. A similar argument relates abstract and concrete Boolean evaluation.

For assignment update the target’s entry if the right side is known, and remove any old entry if the right side is unknown. Sequence sends the abstract result of its prefix into the transfer for its suffix. At a conditional analyze only the selected branch when the abstract guard is known; when it is unknown take the join of both branch outputs. Write $`C\left( {S,c} \right)` for this abstract command transfer. The port also computes an inductive upper bound for loops.

*Theorem 39.1 (conditional case of analysis soundness).* Suppose $`s \in \gamma(S)` and $`s \vdash c \Downarrow t`. Then $`t \in \gamma\left( {C\left( {S,c} \right)} \right)`. In the Lean port this concrete judgment is `cexec s c t`. The capitalized `Cexec S c` denotes the abstract output store. For the conditional case assume the theorem for each branch. Invert the concrete derivation to identify the selected branch and its terminating derivation. If the abstract guard is known, Boolean soundness forces the same selection and the branch hypothesis suffices. Otherwise the branch hypothesis puts $`t` in the concretization of that branch result. Each operand is below its join, so $`t` matches the joined state. This proves the case for both possible concrete guard outcomes.

In the unknown-guard proof there are two different unknowns. The analyzer receives the abstract guard result “unknown”; the running program receives the concrete Boolean computed in its actual state. The proof need not guess that Boolean. It can invert the supplied concrete execution derivation, which already identifies the branch taken. If that branch is the left one, the induction hypothesis says that the resulting concrete store satisfies every equation of the left abstract output. What remains is a purely mathematical implication: every binding retained at the join is among those equations. Repeating the reasoning with the right branch discharges the other possible derivation.

The elementary lemma below captures both routes through the join, using predicates over a variable and an integer to stand for bindings. Intersection is appropriate here because these predicates describe facts. Their meaning as sets of concrete stores becomes less precise after intersection.

```lean
def modelsFacts (s : String → Int) (facts : String → Int → Prop) : Prop :=
  ∀ x n, facts x n → s x = n

example (s : String → Int) (l r : String → Int → Prop)
    (h : modelsFacts s l ∨ modelsFacts s r) :
    modelsFacts s (fun x n => l x n ∧ r x n) := by
  intro x n hboth
  rcases h with hl | hr
  · exact hl x n hboth.1
  · exact hr x n hboth.2
```

The program analysis additionally ensures that these collections of bindings describe partial maps and that each branch hypothesis applies to the concrete derivation.

*Collecting the results.* For a set of input stores X, let $`\operatorname{post}_c(X)=\{t\mid \exists s\in X.\;(s\vdash c\Downarrow t)\}`. The transfer soundness condition is $`\operatorname{post}_c(\gamma(S))\subseteq\gamma(C(S,c))`. For a branch that sets x to either 0 or 1, every reachable output has one of these two values. The constant map obtained by joining the branches may admit x = 2 as well. Inclusion proves safety of the approximation even when equality fails. Concrete Semantics §§13.3–13.5 develops the same test for other abstract domains.

# A precision loss
%%%
tag := "ch39-s3"
%%%

Starting with no facts, let one branch write $`\left( {x,y} \right) = \left( {0,0} \right)` and another write $`\left( {x,y} \right) = \left( {1,1} \right)`, for distinct names. Neither variable has a constant value common to the branches. The join is the empty map, which also permits $`\left( {0,1} \right)`. This spurious pair demonstrates loss of the *relation* $`x = y`. The abstract domain can express equations to integer constants for individual variables only. Including spurious states weakens what can safely be concluded. It does not remove either real outcome.

Could an alternative join keep the relation x = y using exactly the same representation? Consider any single map that admits both (0,0) and (1,1), with all other variables fixed identically if desired. It cannot bind x to an integer: the two stores disagree there. For the same reason it cannot bind y. Therefore the store (0,1) with identical values everywhere else also satisfies every entry of the map. No choice of join algorithm on these maps can avoid this particular loss while still representing both original stores by one map. The restriction comes from the abstract domain itself.

Now append an assignment that reads the difference x − y. In either genuine branch its value is zero. After the join, a third store admitted by the abstract map can give negative one, so replacing the difference by zero cannot be justified solely from the post-join map. One could establish the result by simplifying inside each branch, by tracking equalities between variables, or by preserving the disjunction longer. These approaches rely on different evidence. The soundness theorem for constant maps remains valid even where it gives too little information for the desired transformation.

# Exercises
%%%
tag := "ch39-s4"
number := false
%%%

1. Join maps `{x↦7, y↦2}` and `{x↦7, y↦3, z↦0}`. Give a matching store for the join that matches neither input.
2. Show why leaving the old binding for $`x` in place after `x := y` with unknown $`y` can violate the theorem.
3. Suppose the entry for $`x` is absent. What can the constant domain infer about `x - x` using only the arithmetic transfer described here?

*Further problem.* Design two branch result maps whose join is strictly less precise than their concrete disjunction. Then find a concrete equality that holds on both branches and prove that no single constant map can express exactly this disjunction.

# Reading for the Seminar
%%%
tag := "ch39-s5"
number := false
%%%

*Definitions · 10 minutes.* List the concrete obligations imposed by a partial abstract map.

*Joint proof · 30 minutes.* Prove the unknown-guard case with both possible concrete branch selections. Use the defining direction of the precision order to justify the join step.

*Proof review · 20 minutes.* Find a spurious store for a join and check whether it contradicts the statement of soundness.

*Facilitator’s hint.* Pick a fact retained by the join. Which two abstract branch results had to agree about that exact variable and value?

# Solutions
%%%
tag := "ch39-s6"
number := false
%%%

*1.* Retain just $`x\mapsto 7`. A state with $`x = 7,y = 99` satisfies the join but neither operand, regardless of its other components.

*2.* Start with known $`x = 4` and a concrete state with $`y = 6`. After assignment $`x = 6`, contradicting a retained claim $`x = 4`.

*3.* With $`x` unknown the compositional abstract subtraction returns unknown. Concrete subtraction gives zero at every state. Recognizing the repeated syntax could improve this transfer while preserving soundness.

*Further problem.* Use maps recording (x,y) = (2,3) and (x,y) = (5,6), leaving other names unrestricted. Every represented store satisfies y = x + 1. A single constant map representing both families cannot constrain x or y, since each takes two values. Nor can it constrain another variable, which is unrestricted in each family. Hence the only possible common map is empty. Its concretization includes, for instance, (2,6), which satisfies neither branch description and violates the equality. Forgetting the relation is forced by representing the whole result with one map. Attributing the imprecision to the abstract guard alone would miss the problem: even supplying the two exact branch outputs to the join cannot recover this relation in the chosen domain.
