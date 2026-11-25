import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Liveness and Loop Fixed Points" =>
%%%
tag := "ch41"
file := "chapter-41"
%%%

[Chapter PDF](print/chapter-41.pdf) · [Session 41](seminar/index.html#week-41)

To preserve a future read of $`z`, a backwards analysis may need $`y` before an assignment to $`z` and $`x` before an earlier assignment to $`y`. A loop sends information back to its own entry. The names required at a loop head must cover both immediate exit and another iteration.

*Sources.* Nipkow and Klein, _Concrete Semantics_, §10.4, on liveness. Compare Leroy’s Lean port at `deadcode_fixpoint_rec`, `live`, and `live_while_charact`. Distinguish the condition checked at an early stop from the guarantee on fuel exhaustion. [Concrete Semantics.](https://concrete-semantics.org/concrete-semantics.pdf) [Lean loop analysis.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Deadcode.lean#L68-L126)

# Backward transfer
%%%
tag := "ch41-s1"
%%%

For a set $`L` of names observed after a command, let $`B\left( {c,L} \right)` be the variables required before its execution for the dead-code transformation. Skip returns $`L`. For `x := e`, if $`x \in L` return $`\left( {L \smallsetminus \left\{ x \right\}} \right) \cup F(e)`, where $`F(e)` contains the variable names read by $`e`. If $`x \notin L`, return $`L`: the dead assignment may be omitted and its operand need not be read. Expressions are pure and total. For a sequence apply the suffix transfer first and then the prefix transfer. For a conditional take both branch transfers and the guard’s free names.

For a loop with guard $`b`, body $`c`, and outgoing observation $`L`, define

$$`F_{W}(X) = F(b) \cup L \cup B\left( {c,X} \right).`

The guard names determine the next choice, $`L` covers an immediate exit, and $`B\left( {c,X} \right)` must suffice to reach another head agreeing on $`X`. A sound head set $`H` meets $`F_{W}(H) \subseteq H`. This inclusion is the property used by the transformation proof; the returned set need not be minimal.

The transfer for assignment depends on whether the destination is observed. Start with an observation containing x and z after x := y + 1. To reproduce x we need the old y; to reproduce z we retain the old z. The old x contributes nothing because it is overwritten before it could reach an observer. Change the observation to just z. Now the update to x can be removed completely. Because evaluating the arithmetic expression has no effect and always terminates, the old y is no longer required either. This distinction explains why the transfer explicitly tests membership of the destination before inserting variables from the right-hand side.

Forward execution and backward calculation run in opposite orders but use the same program point between two commands. For c followed by d, imagine the final observer inspecting L. The suffix first tells us what agreement must hold immediately before d. These names are the observations required immediately after c. Applying the prefix transfer to that set computes the needed initial agreement. This reasoning also explains the recurrence for a loop: the point following one body execution is an input to the next guard, so its requirements are those of the head itself.

# Iteration by hand
%%%
tag := "ch41-s2"
%%%

Use the loop below with observation $`L = \left\{ z \right\}`, distinct $`g,x,y,z`, and a guard testing $`g`.

```
while g > 0 do (z := y; y := x; g := g - 1)
```

Here decrement is addition of $`- 1`. Start with $`X_{0} = \varnothing` and form $`X_{i + 1} = F_{W}(X_{i})`. In the first body transfer no output is needed, so all three assignments may be skipped. Consequently $`X_{1} = \left\{ {g,z} \right\}`. At the next body transfer the decrement needs old $`g`, the assignment to unneeded $`y` adds nothing, and `z := y` replaces $`z` by $`y`. The body requires $`g,y`. Reintroducing exit and guard gives $`X_{2} = \left\{ {g,y,z} \right\}`.

Now the middle assignment sees $`y` needed and introduces $`x`. The earlier assignment to $`z` still introduces $`y`. The body requires $`g,x,y` and $`X_{3} = \left\{ {g,x,y,z} \right\}`. Applying the transfer again gives the same head set. The variable $`x` entered only on the third application: observing $`z` after a later iteration can require the old $`x` through an intermediate $`y`.

Why does the first pass fail to reveal x? At the first visit to the body, no requirement has yet passed around its back edge. In a single iteration that exits immediately afterwards, z takes the *old y*. The write of x into y can affect z only on a subsequent visit. Choose initial g = 2, y = 8, x = 5. At the first head z can have any value. After one iteration z is 8, y is 5 and g is 1. After the second, z is 5 and g is zero. Changing only the initial x to 6 changes the finally observed z to 6. This pair of executions refutes a claim that the head requirement can permanently omit x.

The converse boundaries matter too. If the initial guard is false, the final z is simply the old z; a correct head set must include z for this immediate exit. If the guard is initially true and g = 1, the first iteration reveals old y. These three input families explain why the backwards chain discovers old z, old y and old x in succession. The analysis joins all possibilities in one head set even though an individual run need not inspect every one of those initial values.

# Fuel and the fallback set
%%%
tag := "ch41-s3"
%%%

The Lean function starts at the empty set with fuel 20. If fuel is positive it computes $`X' = F_{W}(X)`; if $`X' \subseteq X` it returns $`X`, otherwise it recurses with one less fuel and $`X'`. At zero it returns the supplied default. For a loop that default is $`L \cup F_{c}(W)`, where $`F_{c}` collects variables read in guards and right-hand sides anywhere in the loop. It can be much smaller than the universe of all variable names.

Why is the fallback safe? The bound `live_upper_bound` gives $`B\left( {c,X} \right) \subseteq F_{c}(c) \cup X`. With $`X` equal to the default this is a subset of the default. That set also contains $`L` and all guard reads, so it satisfies $`F_{W}(X) \subseteq X`. An early return satisfies the same condition by the actual test. The three inclusions of `live_while_charact` unpack precisely these obligations. The proof does not require that 20 iterations reach a least fixed point.

On the fallback path the proof uses an upper bound with a definite orientation. Every name demanded by one more unfolding *starting from H* must already lie in H. The reverse inclusion only says that each earlier guess is still demanded; the guesses computed during iteration can meet that weaker property long before the computation is safe to stop. In the worked loop the first nonempty guess contains g and z, and the next pass discovers y. Ending there would miss an input on which a one-iteration execution depends.

The Lean check below uses characteristic predicates on names and ordinary implication for inclusion. It records the three consequences of a safe loop-head estimate. This small theorem requires neither iteration nor a least-fixed-point construction.

```lean
example {V : Type} (guard after body head : V → Prop)
    (closed : ∀ x, (guard x ∨ after x ∨ body x) → head x) :
    (∀ x, guard x → head x) ∧
    (∀ x, after x → head x) ∧
    (∀ x, body x → head x) :=
  ⟨fun x hx => closed x (Or.inl hx),
   fun x hx => closed x (Or.inr (Or.inl hx)),
   fun x hx => closed x (Or.inr (Or.inr hx))⟩
```

In the application, body denotes the backwards transfer evaluated at this very head. The earlier default-bound argument establishes the premise even if fuel is exhausted. The three resulting projections are precisely what the execution proof uses.

*Further reading: interval widening.* For the variables of a fixed finite program, a strictly increasing chain of live-variable sets can add only finitely many names. An interval analysis of an unbounded counter can instead produce `[0,0]`, `[0,1]`, `[0,2]`, and so on. A widening may replace an increasing upper endpoint by positive infinity to force stabilization while retaining all reachable values. This solves a different convergence problem from the fuel fallback in the Lean liveness analysis. See Concrete Semantics §13.9.

# Exercises
%%%
tag := "ch41-s4"
number := false
%%%

1. Use §41.2 with empty output observation. Compute its stable head set. Why is the guard still present?
2. Add `unused := spare` to the loop, with fresh variables and the original observation. Compare the converged analysis and the fallback set.
3. What would go wrong with returning the empty set unconditionally when fuel runs out?

*Further problem.* The loop writes z := y and then y := x. Experiment with the reversed order, y := x followed by z := y, keeping the same guard, decrement and final observation. Which initial value disappears from the stable head requirement? Justify this by both backward transfer and executions.

# Reading for the Seminar
%%%
tag := "ch41-s5"
number := false
%%%

*Definitions · 10 minutes.* Do the sequence transfer from its last assignment towards its first.

*Joint proof · 30 minutes.* Calculate head sets until stable and prove the three inclusions at the last set. Derive those inclusions independently for the fallback using the upper-bound lemma.

*Proof review · 20 minutes.* Add the unobserved read in Exercise 2 and see where the fallback loses precision.

*Facilitator’s hint.* Keep the after-loop observation fixed. The changing set specifies what is needed for another visit to the loop head.

# Solutions
%%%
tag := "ch41-s6"
number := false
%%%

*1.* The first application inserts $`g`. The decrement requires that same $`g`, and no observation requires $`y` or $`z`, so the next set is again the singleton at $`g`. Agreement on the guard supports matching loop control.

*2.* Since the new destination is dead, the converged transfer ignores its right side. The fallback collects all syntactic reads and therefore includes `spare`.

*3.* The empty set could omit a guard read or an observed exit variable. Then agreement on the returned set need not imply identical guard decisions or agreement on final observations.

*Further problem.* Start from the empty guess; guard and exit introduce g and z. In the next pass the decrement keeps g, z := y replaces the needed z by y, and y := x replaces that y immediately by x. Combining with guard and exit yields g, x, z. A further pass leaves that set unchanged. Old y is absent. Operationally, on every iteration the assignment to y overwrites it before z reads it. Immediate exit still observes old z, and a positive number of iterations produces a z determined by x. Varying only the initial y cannot alter the observed final z. Compare the original order, in which an execution with g = 1 copied the initial y to z. This distinction tests the order of the two transfer calls inside sequence analysis.
