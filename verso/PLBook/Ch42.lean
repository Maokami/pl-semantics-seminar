import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Correctness of Dead-Code Elimination" =>
%%%
tag := "ch42"
file := "chapter-42"
%%%

[Chapter PDF](print/chapter-42.pdf) · [Session 42](seminar/index.html#week-42)

Deleting an assignment usually changes a final state. A correctness theorem for dead-code elimination must tell us which parts of that state the observer can read. Its proof needs a second set of names: the ones on which the original and transformed executions must agree initially.

*Sources.* Nipkow and Klein, _Concrete Semantics_, §§10.3–10.4, on live-variable analysis. In Leroy’s Lean port read `dce`, the agreement predicate, and `dce_correct_terminating`. Follow the assignment and sequence cases and identify the role of the loop obligations from Chapter 41. [Concrete Semantics.](https://concrete-semantics.org/concrete-semantics.pdf) [Transformation, agreement and theorem.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Deadcode.lean#L127-L218)

# Observations and transformation
%%%
tag := "ch42-s1"
%%%

For a set $`L`, write $`s\underset{L}{\approx}t` if $`s(x) = t(x)` for every $`x \in L`. Let $`B\left( {c,L} \right)` denote the backwards liveness transfer of Chapter 41. If two states agree on the variables read by a pure expression, its evaluations coincide (Chapter 1). This remains true for subtraction and guards by adding the corresponding structural induction cases.

Write $`D\left( {c,L} \right)` for the transformed command. Keep an assignment `x := e` when $`x \in L` and replace it by skip otherwise. Skip stays skip. For a sequence $`c\ \text{;}\ d` transform $`d` with $`L` and $`c` with $`B\left( {d,L} \right)`. For a conditional transform both branches with $`L` and retain the guard. For a loop transform the body at the computed loop-head set $`H = B\left( {W,L} \right)` and retain the guard. Expressions and guards in this language are total and have no side effects. Consequently deleting an unused arithmetic computation cannot suppress a visible effect or an arithmetic failure.

A useful first test of observational equivalence is an assignment whose destination the observer cannot name. Let the initial stores agree on z and suppose one program writes seven to x while the other executes skip, with x and z distinct. Both reach final stores with the same z. If we subsequently install a continuation that reads x into z, that equivalence may disappear. Choosing the observation set is a semantic contract with the surrounding program. The backward transfer computes the contract required by a known continuation, allowing dead-code elimination to compose across a sequence.

Agreement on a set is reflexive, symmetric and transitive because integer equality is. It also weakens when the set shrinks. In a proof the last property is frequently used in only one direction: agreement on the whole loop-head set entails agreement on guard variables because those names lie in the head set. Agreement only on guard variables does not determine arbitrary head-live values. Keeping the direction explicit helps when a proof moves backwards through program syntax and then forwards through an execution derivation.

# A theorem about two initial states
%%%
tag := "ch42-s2"
%%%

*Theorem 42.1.* Suppose $`s \vdash c \Downarrow t` and $`s\underset{B{({c,L})}}{\approx}u`. Then some $`v` satisfies $`u \vdash D\left( {c,L} \right) \Downarrow v` and $`t\underset{L}{\approx}v`. Quantification covers every $`L,u` for each original terminating derivation. Taking $`u = s` gives the usual same-input optimization theorem. Identical final states are unnecessary.

Induct on the original execution. For a dead assignment, $`x \notin L` and $`B\left( {c,L} \right) = L`. The transformed skip returns $`u`. At each $`y \in L`, the source update also leaves $`y` unchanged, so the initial agreement gives final agreement. For a live assignment initial agreement covers all variables read by $`e`, hence both evaluations produce the same integer. Both states write this integer at $`x`, and agreement at every other observed name follows from the other part of the pre-set $`L \smallsetminus \left\{ x \right\}`.

For a sequence put $`M = B\left( {d,L} \right)`. Initial agreement is on $`B\left( {c,M} \right)`. The first induction hypothesis at observation $`M` gives a transformed intermediate state agreeing there with the original intermediate state. That is exactly the premise of the second hypothesis at $`L`. Its result gives final agreement, and the sequence rule composes the two transformed executions.

For a conditional initial agreement includes all guard reads and the transfer set of the selected branch. For a loop, $`H` contains the guard reads, $`L`, and $`B\left( {\text{body},H} \right)` by Chapter 41. Thus an exit preserves the required observation. In an iteration, apply the body hypothesis to obtain agreement at $`H` and then the hypothesis for the smaller remaining loop derivation. All these hypotheses arise from finite execution evidence. The theorem does not quantify over original infinite runs.

Focus on the live-write case at a single observed name z. If z is the destination x, the source and transformed final stores must return the newly computed integer; there is no need for the original stores to agree on the old x unless x itself occurs on the right-hand side. If z is different, the stores return their previous values at z. Agreement is available there because z was observed and survived removal of x from the pre-set. These two cases exhaust all possible reads from the observation set. The argument does not invoke equality of whole maps.

Here is the corresponding proof for the eliminated write. The update and membership predicates use only their mathematical definitions. The fresh target state on the skip side is its input u.

```lean
def storeWrite (s : Nat → Int) (x : Nat) (v : Int) (z : Nat) : Int :=
  if z = x then v else s z

example (s u : Nat → Int) (obs : Nat → Prop) (x : Nat) (v : Int)
    (dead : ¬ obs x) (agree : ∀ z, obs z → s z = u z) :
    ∀ z, obs z → storeWrite s x v z = u z := by
  intro z hz
  have unequal : z ≠ x := fun h => dead (h ▸ hz)
  simpa [storeWrite, unequal] using agree z hz
```

The contradiction inside the proof is the mathematical content of the word “dead” in this case. It rules out exactly the lookup at which the eliminated write could change an observation.

# A slice of a state
%%%
tag := "ch42-s3"
%%%

Choose distinct variables and observe only `out` at the end:

```
tmp := x + 1; out := tmp + 2; scratch := y
```

The final assignment is dead, leaving `{out}` needed before it. Moving backwards across the middle assignment gives `{tmp}`, and across the first gives `{x}`. Thus the transformed program keeps the first two assignments even though `tmp` is outside the final observation. It replaces the last by skip.

With $`x = 4,y = 9` and initial scratch zero, the original and transformed program both return `out = 7`. The original writes nine to scratch while the transformed program leaves zero there. For the more general two-input theorem, even $`y` can differ initially: only $`x` appears in the computed pre-set.

Repeat the example with two genuinely different initial stores to see why the theorem quantifies over both. Let the source start with x = 4, y = 9 and scratch = 0; let the target start with x = 4, y = 20 and scratch = 100. The initial agreement on the computed pre-set holds because it asks only about x. After the first assignments both stores contain tmp = 5 even if their old tmp entries differed. At the next program point agreement on tmp is all the remaining computation needs. Both executions then produce out = 7. The source updates scratch to 9 and the transformed target leaves scratch equal to 100.

Notice how the set of names being compared changes at every stage. Equality of just x at entry becomes equality of just tmp in the middle and then equality of out at the end. Insisting on the final observation set as the relation at every intermediate point would make the induction false or too weak to continue: equality of out before its assignment says nothing about the two reads of tmp. This example also ties the entire course together: a structural computation over syntax chooses what to compare, while an induction over operational evidence proves that the transformed program actually produces a corresponding execution.

# Exercises
%%%
tag := "ch42-s4"
number := false
%%%

1. Add scratch to the final observation. Recompute the backwards sets and state which assignment must now be kept.
2. Reverse the first two assignments in §42.3. Which initial value determines the final output now?
3. Give a language extension in which deleting `scratch := e` solely because scratch is dead could be unsound. Specify the missing observation.

*Further problem.* In the loop-free fragment, does a second pass of dead-code elimination change the syntax further? Prove, for every command `c` and observation set `L`, both `B(D(c,L),L) = B(c,L)` and `D(D(c,L),L) = D(c,L)`. Keep sequence nodes and guards exactly as in the transformation defined above. Explain why the first claim is needed in the sequence case of the second.

# Reading for the Seminar
%%%
tag := "ch42-s5"
number := false
%%%

*Definitions · 10 minutes.* Mark the final observations before calculating any backwards sets.

*Joint proof · 30 minutes.* Prove the dead and live assignment cases with two distinct starting stores. Use the sequence case to explain why a variable outside the final set may still be needed.

*Proof review · 20 minutes.* Run the example with different initial values for the unobserved names and then add a new observation as in Exercise 1.

*Facilitator’s hint.* For a dead write, fix an arbitrary observed name. Its inequality with the assignment target is precisely what lets the two final reads be compared.

# Solutions
%%%
tag := "ch42-s6"
number := false
%%%

*1.* Starting with `{out,scratch}`, transfer across the last write gives `{out,y}`, then `{tmp,y}`, then `{x,y}`. All three assignments remain.

*2.* The middle write to tmp in the new order is dead relative to out. The first assignment, now `out := tmp + 2`, reads the *initial* tmp. The required input set therefore contains tmp alone.

*3.* If evaluating $`e` can emit output, deleting it may change the trace while preserving observed final variables. If it can diverge or raise an error, suitable termination or error observations may also distinguish the programs. The purity and totality premises explain why these issues did not enter the proof here.

*Further problem.* Use simultaneous structural induction on the original command, with each assertion quantified over all final observation sets. Skip is fixed by both transformations. A dead assignment becomes skip, and its backward transfer returns the same incoming requirement as skip. A live assignment remains syntactically identical. These facts establish both assertions for leaves. A conditional retains its guard. The two branch induction hypotheses preserve the backward sets, hence their union with the guard reads. They also show that both transformed branches remain fixed on the second pass.

For a sequence `c; d`, write `M = B(d,L)`. On the second pass the prefix is transformed with the demand of the already transformed suffix. By the first induction hypothesis for `d`, this demand is precisely `M`. Apply both induction hypotheses for `c` at `M`, and the second hypothesis for `d` at `L`. The two incoming requirements now agree, and the second transformation returns exactly the same sequence of transformed subcommands. This proves syntactic idempotence for the stated transformation. Chapter 41's loop analysis would require a separate argument about the computed loop-head demand.
