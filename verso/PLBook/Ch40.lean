import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Constant Propagation and Program Transformation" =>
%%%
tag := "ch40"
file := "chapter-40"
%%%

[Chapter PDF](print/chapter-40.pdf) · [Session 40](seminar/index.html#week-40)

Knowing a constant after a branch is a property of program states. Replacing a later variable read with a literal is a change to the program. The proof that the changed program has the same result uses the analysis theorem from Chapter 39 at the intermediate state.

*Sources.* Nipkow and Klein, _Concrete Semantics_, §10.2, on constant folding and propagation. Compare the definitions `cp_com`, `Cexec` and the theorem `cp_com_correct_terminating` in Leroy’s Lean port. Track the different abstract stores used at the two parts of a sequence. [Concrete Semantics.](https://concrete-semantics.org/concrete-semantics.pdf) [Lean transformation and theorem.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Constprop.lean#L548-L607)

# Transfer versus rewriting
%%%
tag := "ch40-s1"
%%%

Write $`C\left( {S,c} \right)` for the outgoing abstract store and $`P\left( {S,c} \right)` for the transformed *command*. The expression transformation replaces a variable by a literal when $`S` records its value and can fold an arithmetic operation on known literals. If $`s` matches $`S`, evaluation of the transformed expression in $`s` agrees with the original. Prove this by structural induction: a replaced lookup uses the matching fact, an untouched lookup uses the same store, and folding must implement the identical integer operation on equal operands. The Boolean version also preserves the guard truth value for matching inputs.

For a sequence the command transformation produces a sequence with first command $`P\left( {S,c} \right)` and second command $`P\left( {C\left( {S,c} \right),d} \right)`. An assignment still writes its target and uses the transformed right side. A conditional rewrites its guard and branches, selecting a single branch if the guard becomes constant. At a loop the store for rewriting the body *and guard* must be valid at all reachable loop heads; the entry facts alone can cease to hold after an iteration.

It is useful to distinguish two uses of an empty abstract entry during rewriting. If the analyzer knows x = 3 it may substitute the integer literal for a read of x. If it has no entry for x, the safe rewrite is to keep the read; treating a missing entry as zero would silently change many computations. At an addition, these local choices compose. For example a map knowing x = 3 but having no fact about y justifies changing x + y to 3 + y in every matching state. It does not justify producing a numeric literal for the entire sum.

For sequencing, the outgoing map is a claim about *normal final states*. Suppose the prefix is an infinite loop on a particular input. There is then no intermediate concrete store at which this particular run executes the optimized suffix. The analysis can still compute a conservative abstract output and the compiler can still rewrite the suffix syntactically. The terminating-execution theorem makes no demand to invent a state for an unreachable suffix. This explains why the statement quantifies over a concrete execution premise instead of treating the analysis as an executable predictor of termination.

# A join feeding a transformation
%%%
tag := "ch40-s2"
%%%

Choose distinct variables and an unknown guard depending on $`g`.

```
if g = 0 then (x := 4; y := 1)
         else (x := 4; y := 2);
z := x + 3
```

The semicolon after the conditional introduces the common suffix. From the empty map both branches end with known $`x = 4`, while they disagree about $`y`. Their join records only $`x = 4`. The suffix is consequently rewritten as `z := 7`. In an execution starting at $`g = 0` the intermediate store has $`x = 4,y = 1`; starting at $`g = 9` it has $`x = 4,y = 2`. Each satisfies the fact needed for folding the suffix. Replacing $`y` by 1 after the join would have no such justification.

Trace two inputs all the way to the final store. Starting with g = 0, the true branch writes x = 4 followed by y = 1. The source suffix reads the newly written 4 and produces 7. The transformed suffix writes the literal 7. Starting with g = 9, y instead becomes 2; the x lookup still yields 4. Thus the argument for the transformed suffix uses a single common equation despite two potentially different full intermediate stores. Both programs retain the branch-specific value of y, which matters because the theorem will compare *entire* final stores.

A tempting shortcut is to propagate into the suffix using whichever branch was traversed last by the *compiler*. Suppose that traversal ends with the else branch and so leaves y = 2 in a mutable table. If the next statement were a read of y, substituting 2 would be wrong on the true branch. The safe join follows control flow, not traversal order. On the board this is easy to check: under each proposed substitution write the set of concrete incoming edges on which its equality has been established. An unconditional suffix may use the equality only if every feasible incoming edge is covered.

# Preservation of terminating executions
%%%
tag := "ch40-s3"
%%%

*Theorem 40.1.* If a concrete state $`s` matches $`S` and $`s \vdash c \Downarrow t`, then $`s \vdash P\left( {S,c} \right) \Downarrow t`. The concluding state is the same entire store. The source derivation is a premise; the statement alone gives no converse implication or assertion about an input on which the source diverges.

For a sequence invert the original execution to obtain $`s \vdash c \Downarrow u` and $`u \vdash d \Downarrow t`. The transformation hypothesis for $`c` provides $`s \vdash P\left( {S,c} \right) \Downarrow u`. Independently, analysis soundness applied to that *original* prefix execution gives $`u \in \gamma\left( {C\left( {S,c} \right)} \right)`. The transformation hypothesis for $`d` can now be instantiated at this outgoing store and yields $`u \vdash P\left( {C\left( {S,c} \right),d} \right) \Downarrow t`. The sequence rule combines the two transformed derivations. A hypothesis about expression simplification alone would not supply the middle-state fact.

At a conditional use Boolean expression preservation to select the same branch. If constant folding removes the surrounding conditional, the branch derivation itself supplies the transformed result. At a loop the abstract invariant provides initial and preserved matching; induction on the finite loop execution processes successive visits. The source proof in the port supplies these additional cases.

Isolate the point at which equality of complete intermediate stores is used. The prefix preservation hypothesis returns *exactly u* from the optimized prefix, and the analysis theorem supplies facts about that very u. Thus the next induction hypothesis starts from the same concrete state on both sides. In Chapter 42 the target may have a different intermediate state; the proof will then need an explicit relation between the two. Here equality permits the use of ordinary substitution in the mathematical proof.

The following general lemma spells out the data flow independently of the particular command syntax. The predicates pre and mid express the entry and intermediate analysis facts.

```lean
example {State : Type} (pre mid : State → Prop)
    (firstStep suffix : State → State → Prop)
    (targetPrefix targetSuffix : State → State → Prop)
    (safe : ∀ s u, pre s → firstStep s u → mid u)
    (first : ∀ s u, pre s → firstStep s u → targetPrefix s u)
    (second : ∀ u t, mid u → suffix u t → targetSuffix u t)
    {s u t : State} (hs : pre s) (hu : firstStep s u) (ht : suffix u t) :
    targetPrefix s u ∧ targetSuffix u t :=
  ⟨first s u hs hu, second u t (safe s u hs hu) ht⟩
```

Notice the two uses of the same original prefix evidence. One constructs target execution and one establishes matching facts. The target sequence rule is the remaining step that combines the two conclusions.

# Exercises
%%%
tag := "ch40-s4"
number := false
%%%

1. Change the else branch to set $`x = 5`. Can the suffix still be replaced by `z := 7`? Give a concrete counterexample if attempted.
2. Suppose $`S` records $`x = 4` and the concrete input instead has $`x = 9`. Apply `z := x` to show why initial matching is a necessary premise.
3. Why is the target end state in this theorem stronger than agreement on a chosen subset of variables?

*Further problem.* Consider a loop whose input x is known to be zero, whose guard is x < 2, and whose body increments x. Show what can happen if a compiler simplifies the guard once using only the entry map. Which fact must a valid loop-head map forget?

# Reading for the Seminar
%%%
tag := "ch40-s5"
number := false
%%%

*Definitions · 10 minutes.* Compute both abstract branch outputs and their join by hand.

*Joint proof · 30 minutes.* Prove the sequence case, writing separate lines for transformed prefix execution and outgoing abstract matching. Apply the suffix hypothesis only after obtaining both.

*Proof review · 20 minutes.* Change a branch constant and attempt the same rewrite. Identify which proof premise can no longer be built.

*Facilitator’s hint.* Ask what the suffix transformer used when it replaced the read. The concrete intermediate store must match exactly that abstract store.

# Solutions
%%%
tag := "ch40-s6"
number := false
%%%

*1.* The join now forgets $`x`. In a state with $`g = 9` the else branch sets $`x = 5` and the source suffix writes 8. Writing 7 would change the final store.

*2.* Rewriting gives `z := 4`. From the proposed input the source writes 9 and the target writes 4. This input does not satisfy the theorem’s initial premise.

*3.* Identical final stores agree at every name, hence also at any chosen subset. Chapter 42 instead permits differences at names outside the observation set, which makes removal of dead writes possible.

*Further problem.* At entry the guard evaluates to true. Replacing it by the literal true on every visit produces an infinite loop, even if the body itself is left intact. The original visits x = 0, 1, 2, then exits with x = 2. Thus the incorrect transformed command lacks the terminating derivation required for this input. A sound map describing every loop head cannot retain x = 0: after the first body execution a concrete state at the head has x = 1. The constant domain must forget the binding for x when it covers both visits. Rewriting the guard at that common head then leaves a runtime comparison. The example also shows why an expression rewrite can be correct for one evaluation and unsound when the rewritten syntax is evaluated again later.
