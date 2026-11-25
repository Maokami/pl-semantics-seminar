import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Correspondence of Command Semantics" =>
%%%
tag := "ch09"
file := "chapter-09"
%%%

[Chapter PDF](print/chapter-09.pdf) · [Session 10](seminar/index.html#week-10)

A denotational definition by functions, a denotational definition by relations, and the operational rules give three independent accounts of a terminating command. The intermediate store in sequential composition is where they meet. For a loop the bridge is the number of finite unfoldings needed by an execution.

*Sources.* Glynn Winskel, _The Formal Semantics of Programming Languages_, chapter 5 on the denotational semantics of IMP. Read the relational clauses for composition and iteration. Compare Reynolds, _Theories of Programming Languages_, §2.2 on command meanings as functions. The joint proof is the sequence case of Theorem 10.2 in both directions. [Winskel.](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf) [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Independent definitions
%%%
tag := "ch09-s1"
%%%

Let $`\Sigma` be the states, $`f_{c}:\Sigma\rightarrow\Sigma_{\bot}` the transformer of Chapters 8–9, and $`s \vdash c \Downarrow t` the terminating judgment of Chapter 2. Define $`D(c)` as a subset of $`\Sigma \times \Sigma` by recursion on the command’s syntax. A partial function defines a relation by its graph, but this definition of $`D` does not refer to $`f`.

For skip use the diagonal, consisting of $`\left( {s,s} \right)` for every state. For assignment use every pair $`\left( {s,s\left\lbrack {x\mapsto\operatorname{eval}\left( {e,s} \right)} \right\rbrack} \right)`. For sequencing put $`\left( {s,t} \right) \in D\left( {c\ \text{;}\ d} \right)` if there exists $`u` with $`\left( {s,u} \right) \in D(c)` and $`\left( {u,t} \right) \in D(d)`. A conditional accepts a pair in the relation of the branch selected by the guard in $`s`.

For a loop with guard $`b` and body $`a`, define an operation $`G` on relations. The pair $`\left( {s,t} \right)` belongs to $`G(R)` precisely if one of these conditions holds:

1. The guard is false at $`s` and $`t = s`.
2. The guard is true at $`s` and some $`u` satisfies $`\left( {s,u} \right) \in D(a)` and $`\left( {u,t} \right) \in R`.

Set $`R_{0} = \varnothing`, $`R_{n + 1} = G\left( R_{n} \right)`, and $`D(W) = \bigcup_{n \geq 0}R_{n}`. The relations increase under inclusion because $`G` is monotone. A member of the union has a finite stage witness. In fact this union is a fixed point: a true-branch witness in $`G\left( {\bigcup_{n}R_{n}} \right)` uses one recursive pair from some stage $`n`, so the new pair occurs at stage $`n + 1`. Exit pairs occur at stage 1. Conversely each positive stage is included in the image of the union by monotonicity. Every fixed point contains all stages by induction, so it contains their union.

*Testing an independently stated clause.* Suppose a conditional has guard `x = 0`, true branch `x := 1`, and false branch skip. For any input with `x = 0` the relation contains exactly the pair from that input to its update at `x`. For an input with `x = 1` it contains the diagonal pair. The relational clause restricts the *first* coordinate by the guard. If the true-branch clause instead tested the guard in the second coordinate, the genuine update from zero to one would fail the restriction. The execution rules determine the branch before the assignment, so this modified definition could not satisfy correspondence.

There is a useful change of representation behind this test. A store predicate `P` determines the restricted diagonal `{(s,s) | P(s)}`. Compose it with the relation of the true branch, then take the union with the corresponding composition for the complementary predicate and the false branch. The result is precisely the conditional relation. Composing the restricted diagonal *after* a branch would test its output. Distinguishing the two compositions uses only the definition of a relational witness and gives a compact way to detect the mistaken coordinate before tackling loops.

# The sequence case
%%%
tag := "ch09-s2"
%%%

*Theorem 10.2.* For deterministic integer IMP with total pure expressions and tests, for all commands $`c` and ordinary states $`s,t`,

$$`f_{c}(s) = t\quad\Longleftrightarrow\quad\left( {s,t} \right) \in D(c)\quad\Longleftrightarrow\quad s \vdash c \Downarrow t.`

We prove the two equivalences simultaneously by structural induction on $`c`. At skip and assignment the three definitions identify the same single result. At a conditional they all use the same truth value to select a branch, so the branch hypothesis applies.

For a sequence $`a\ \text{;}\ b`, a state result of its transformer implies that $`f_{a}(s)` is an ordinary state $`u` and $`f_{b}(u) = t`. Indeed the strict extension would return bottom if the prefix did. The two induction hypotheses convert these equalities into membership in $`D(a)` and $`D(b)`. This witnesses relational composition. Conversely, a relational witness $`u` gives the same two function equations by induction. Substitution into the strict composition formula returns $`t`.

Starting from the relational witness, the same hypotheses provide execution trees for $`a` from $`s` to $`u` and for $`b` from $`u` to $`t`. Join them with the sequence rule. Conversely invert a sequence derivation and use its own intermediate state to build the two relational premises. Each direction constructs the witness that its target definition demands.

The middle-state argument admits a small Lean statement independent of IMP syntax. Take arbitrary types of inputs, intermediate values, and outputs. Read `f s = some u` as membership in the graph of `f`. Relational composition introduces an existential witness on the right.

```lean
example {α β γ : Type} (f : α → Option β) (g : β → Option γ)
    (s : α) (t : γ) :
    (f s).bind g = some t ↔ ∃ u, f s = some u ∧ g u = some t := by
  cases f s with
  | none => simp [Option.bind]
  | some u => simp [Option.bind]
```

In the first case the existential demands an ordinary intermediate value from a computation that returned none. In the second case any proposed witness must equal the particular `u` in `f s = some u`, because the constructor `some` is injective. After this equality is used, the remaining premise is exactly the equation for the suffix. Both directions in the proof rely on this same witness calculation. The corresponding statement for two arbitrary relations still uses an existential, but a successful first relation can supply several possible intermediate states. The simplification to one particular value here comes from representing the first computation by a function.

# The loop case
%%%
tag := "ch09-s3"
%%%

The structural induction hypothesis already gives the correspondence for the body $`a` on *all* inputs and outputs. It supplies no hypothesis for the loop itself. Use the approximants $`w_{n}` from Chapter 9 and the relations $`R_{n}` from §10.1 to carry out a second induction.

*Finite-stage lemma.* $`w_{n}(s) = t` if and only if $`\left( {s,t} \right) \in R_{n}`. At zero both assertions are false for ordinary $`t`. At stage $`n + 1` the false guard requires $`s = t` on each side. A true guard on the functional side requires a normal $`u = f_{a}(s)` and $`w_{n}(u) = t`. The body correspondence supplies $`\left( {s,u} \right) \in D(a)` and the stage hypothesis gives $`\left( {u,t} \right) \in R_{n}`. Together these witness the true branch of $`G`. Both equivalences can be read backwards for the converse. Taking the union on one side and pointwise supremum on the other preserves the match because a state in the flat function result is reached at a finite stage.

To link relations to execution, start with a finite loop derivation. If its last rule is exit, put the pair in $`R_{1}`. Otherwise the body premise gives a relational pair by the structural hypothesis for $`a`. The recursive loop derivation is a strict subtree. Induction on that subtree gives membership in some $`R_{n}`, and the same middle state gives membership for the original pair in $`R_{n + 1}`. In the reverse direction induct on the stage witnessing membership. The exit branch gives the exit rule. The true branch gives a body derivation by body correspondence and a recursive loop derivation at the previous stage. Join them with the iteration rule. This completes Theorem 10.2. $`\square`

*Using correspondence to transfer a law.* Write `W` for a loop and `U` for its one-step unfolding. Chapter 7 proved that $`s \vdash W \Downarrow t` and $`s \vdash U \Downarrow t` are equivalent for all ordinary `s,t`. Fix an input `s`. If `f_W(s)` returns an ordinary state `t`, the operational correspondence gives a run of `W` to `t`. Unfolding gives a run of `U` to exactly the same `t`. Applying correspondence backwards yields `f_U(s) = t`. If `f_W(s)` is bottom, a state result for `f_U(s)` would yield a run of `U` and hence of `W`, contradicting the choice of this case. These cases show equality of the two lifted outcomes at every input.

The argument makes a distinction important for reasoning about divergence. There is no inference rule with a terminating conclusion of the form “the final store is bottom.” To use the correspondence theorem in the bottom case, we quantify over *ordinary* candidate outputs and rule them all out. This works because the lifted outcome set has exactly one other element. If one added two different exceptional outcomes, an ordinary-output correspondence alone would no longer determine which exception had occurred. A theorem for the enlarged language would need observations covering those outcomes as well.

# Exercises
%%%
tag := "ch09-s4"
number := false
%%%

*10.1.* For a state $`s` on which a command has no terminating execution, characterize $`f_{c}(s)` and the possible pairs starting at $`s` in $`D(c)`.

*10.2.* For a loop with exactly two completed body executions before exit, write the three relational witnesses from the end backwards, giving their first stage indices.

*10.3.* A binary choice has two different possible final states from one input. Which step in identifying a relation with the graph of a partial state transformer becomes impossible?

*Further problem.* Let `id` be the diagonal relation on stores. Characterize commands whose relation `D(c)` is included in `id`. Use correspondence to prove what happens if such a command precedes an arbitrary suffix `d`. Give an example showing why inclusion alone does not justify deleting the prefix.

# Reading for the Seminar
%%%
tag := "ch09-s5"
number := false
%%%

*Preparation.* For sequential composition identify the same intermediate store in the derivation, the relational composition and the function computation.

*Definitions · 10 minutes.* Write the loop exit pair at stage one. Calculate the first stage for a run with two body executions.

*Joint proof · 30 minutes.* In §10.3 convert a terminating loop derivation to a finite stage by induction on its recursive premise. Reverse the construction by induction on the stage. At a true guard identify separately the body correspondence and the hypothesis for the remaining loop.

*Proof review · 20 minutes.* Start with an ordinary result of the functional loop. Use flatness to find a finite approximation and the finite-stage lemma to obtain a relational pair. Reconstruct its execution and explain why stage zero cannot witness exit.

*Facilitator’s hint.* Name the body result before naming the loop result. The former comes from the smaller syntax tree and the latter from a smaller stage or derivation.

# Solutions and Further Reading
%%%
tag := "ch09-s6"
number := false
%%%

*10.1.* The transformer returns bottom, since a state result would produce a derivation by the theorem. There is no pair $`\left( {s,t} \right)` in the relation for any $`t`.

*10.2.* With successive states $`s,u,t`, the exit at $`t` gives $`\left( {t,t} \right) \in R_{1}`. The second body and that exit give $`\left( {u,t} \right) \in R_{2}`. The first body and that witness give $`\left( {s,t} \right) \in R_{3}`. The stage-count result of Chapter 9 proves these indices are the first.

*10.3.* A partial function assigns at most one ordinary output to each input. Both pairs cannot belong to its graph. The relational composition argument itself still allows several witnesses and results.

Optional: _The Hitchhiker’s Guide to Logical Verification_, §§11.2–11.7, develops relational denotations in Lean. The powerset of pairs is a complete lattice under inclusion, so the Knaster–Tarski theorem gives a least fixed point for a monotone operator. Our finite-stage construction also uses the particular witness structure of $`G` to show its union is fixed. [Hitchhiker’s Guide.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

*Further problem.* Inclusion in the diagonal means that every terminating execution leaves the initial store unchanged. By Theorem 10.2 the transformer therefore either gives bottom or returns its input at every store. Write `A` for the set of inputs at which it returns. Then `D(c)` contains exactly the diagonal pairs `(s,s)` with `s ∈ A`. The possible middle store in a terminating execution of `c; d` is forced to be `s`. The composition relation consists exactly of the pairs `(s,t)` of `D(d)` whose first coordinate belongs to `A`.

For an example, choose `c` to repeat skip while `x > 0` and let `d` be skip. The prefix relation is diagonal on the stores where `x ≤ 0`. At an input with positive `x`, the prefix and hence the sequence have no terminating result, whereas deleting the prefix gives skip and returns the input. To justify removal for every suffix and every input, taking skip as the suffix shows that `D(c)` must equal the full diagonal.
