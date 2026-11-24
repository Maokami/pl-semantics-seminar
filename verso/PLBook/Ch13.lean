import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Total Correctness and Termination" =>
%%%
tag := "ch12"
file := "chapter-12"
%%%

[Chapter PDF](print/chapter-12.pdf) · [Session 13](seminar/index.html#week-13)

A loop that leaves its state unchanged preserves every assertion. When its guard stays true, the preservation proof tells us nothing about when control reaches the statement following the loop. A termination proof must account for both the work of a single iteration and the number of remaining iterations.

*Sources.* _The Hitchhiker’s Guide to Logical Verification_ (2026), §10.8, starting p. 151. Compare the quantification over final states with partial correctness in Chapter 12. In the while rule locate the quantity measured before the body and compared after it. Our example uses two counters and an integer-valued store. [Guide, 2026 edition.](https://raw.githubusercontent.com/lean-forward/logical_verification_2026/460f6be0846eefc3d9441e4e48d75753fcfe1709/hitchhikers_guide_2026_desktop.pdf) [Lean companion.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

# The total triple
%%%
tag := "ch12-s1"
%%%

In deterministic IMP the total-correctness judgment $`\models_{\mathrm{tot}} \{P\}\,c\,\{Q\}` means that for every state $`s` satisfying $`P` there exists a final state $`t` such that $`s \vdash c \Downarrow t` and $`Q(t)`. By determinacy that final state is unique. Equivalently we can give two proofs, one of partial correctness and one that every permitted initial state admits a terminating derivation. This equivalence uses the deterministic semantics of Chapter 3.

A *variant* is a measure of the state that strictly decreases after each completed iteration that started with a true guard. Here its values lie in the natural numbers, including zero. Strict decrease there admits induction: to prove a property at $`k` we may assume it at every $`j < k`. Mere decrease among unbounded signed integers would allow the infinite chain $`0, - 1, - 2,\ldots`.

*How the quantifiers change a proof.* Let a command with input `n` repeatedly decrement a positive `x` initialized to `n` and stop when `x ≤ 0`. Suppose `n ≥ 0`. A partial correctness proof may fix an arbitrary terminating derivation and show its final `x` is zero: nonnegativity is preserved, and the exit guard gives the opposite inequality. For total correctness one must *produce* a derivation for each allowed value of `n`. Induction on that value supplies it. Zero gives the exit rule; a positive input supplies one body execution followed by the derivation for the smaller counter. A theorem about the final values of derivations alone supplies no induction parameter and no execution witness.

Determinacy matters when moving between formulations. Imagine a new binary choice command that may either assign zero to `x` or assign one. From every input there exists a terminating run with final `x = 0`. The other branch violates the corresponding partial triple. If the second branch instead diverged, the same existence statement would leave that behavior invisible. In deterministic IMP there is no competing execution to consider. For a nondeterministic extension the intended guarantee should specify which choices must terminate and which of their final states must satisfy the postcondition.

# The while rule
%%%
tag := "ch12-s2"
%%%

Let $`I` be an invariant, $`b` a guard, $`c` the body, and $`v` a function into the natural numbers on states satisfying $`I`. For every $`k` assume the following *total* body triple. From any state satisfying $`I`, $`b`, and $`v = k`, the body terminates in a state satisfying $`I` and $`v < k`. The symbol $`k` denotes a mathematical parameter fixed before execution.

*Theorem 13.1.* From every $`I`-state the loop terminates in a state satisfying $`I` with a false guard.

*Proof.* Use strong induction on $`k` with the assertion quantified over *every* $`I`-state whose measure is $`k`. Fix such a state $`s`. A false guard gives an immediate exit derivation with final state $`s`. If the guard is true, the total body triple produces an actual intermediate state $`u` and a body derivation. Its measure is some $`j < k`, so the induction hypothesis gives a terminating loop derivation from $`u`, ending with the required exit assertion. The iteration rule combines the two derivations. When $`k = 0` the true-guard case is impossible under the body premise: it would produce a natural number below zero. This completes the induction.

*Why the old measure is a parameter.* Write the body obligation with `k = v(s)` fixed by the caller. What must be proved is `v(u) < k` for the actual final state `u`. Recomputing both occurrences of the variant after execution would ask for `v(u) < v(u)`. Introducing a fresh mathematical variable is enough to retain the old value; it costs no storage in the executing command. The induction statement should likewise quantify over all states of a given measure. Two states with the same measure may differ in every other coordinate, so a claim specialized to the original initial state often cannot be applied at the successor.

The natural-number proof is an instance of induction on a *well-founded relation*, a relation that supports induction from all strictly smaller elements. A common choice for nested phases is lexicographic order on pairs of naturals: `(i′,j′)` is smaller than `(i,j)` when `i′ < i` or when `i′ = i` and `j′ < j`. Its induction principle follows from strong induction on the first coordinate and, with that coordinate fixed, strong induction on the second. It permits the second coordinate to increase when the first strictly decreases. The body must still terminate and provide an actual smaller pair.

# Two counters
%%%
tag := "ch12-s3"
%%%

Assume distinct variables $`p,q` start with nonnegative integer values. Decrement means addition of $`- 1`. The disjunction in the guard means that at least one counter is positive.

```
while p > 0 or q > 0 do
  if p > 0 then p := p - 1 else q := q - 1
```

Take $`I` to assert $`p \geq 0` and $`q \geq 0`, and take $`v = p + q` on these states. Test the premise of Theorem 13.1 with old sum $`k`. In the first branch $`p \geq 1`, the assignment terminates, the updated $`p` is nonnegative, and the new sum is $`k - 1`. In the second branch $`p = 0` by the invariant and the failed test. The outer guard therefore implies $`q \geq 1`. The other assignment also terminates, preserves both bounds, and gives the same strict decrease. From $`\left( {1,2} \right)` the successive loop heads are $`\left( {0,2} \right),\left( {0,1} \right),\left( {0,0} \right)` after the initial head. At the final failed guard, both counters are zero. The theorem and the exit implication establish total correctness.

A variant equal to $`p` alone would prove strict decrease in the first branch. In the second it could stay zero throughout several successful iterations. A state predicate that describes those iterations correctly may still be an unsuitable measure of their remaining work.

*When the sum stops decreasing.* Consider a modified first branch that performs `p := p − 1; q := q + 1` and leaves the second branch unchanged. Starting from `(2,0)`, the successive heads are `(1,1)`, `(0,2)`, `(0,1)`, and `(0,0)`. Summing the two coordinates no longer witnesses progress during the first two iterations. However, the lexicographic pair `(p,q)` decreases in both branches. It has natural-valued coordinates by the invariant, and fits the induction argument of the preceding section.

For this particular transfer there is also a scalar variant. Seek a weighted sum `A·p + B·q` with positive integer coefficients. The change in the first branch is `−A + B`, which is negative whenever `A > B`. The change in the second branch is `−B`. The smallest positive choice is `A = 2` and `B = 1`. The resulting measure is nonnegative and decreases by exactly one in either branch. It therefore gives the exact iteration count from every input. The coefficients have an interpretation in terms of remaining work: each initial unit of `p` must first be moved into `q` and then removed, while each initial unit of `q` only has to be removed.

For the weighted variant, the following are the two branch obligations on mathematical integers. Each establishes that its new measure remains nonnegative and is strictly below the same saved entry measure. Consequently all comparisons take place in the nonnegative part of the integers, ordered like the naturals.

```lean
example (p q : Int) (hp : 0 < p) (hq : 0 ≤ q) :
    0 ≤ 2 * (p - 1) + (q + 1) ∧ 2 * (p - 1) + (q + 1) < 2 * p + q := by
  omega

example (p q : Int) (hp : p = 0) (hq : 0 < q) :
    0 ≤ 2 * p + (q - 1) ∧ 2 * p + (q - 1) < 2 * p + q := by
  omega
```

# Exercises
%%%
tag := "ch12-s4"
number := false
%%%

1. Replace strict decrease in Theorem 13.1 by nonincrease. Give an invariant and a loop that satisfy the weakened premise but run forever.
2. Replace the *total* body premise by its partial counterpart while retaining strict decrease. Exhibit a counterexample.
3. In the two-counter loop, show that starting with sum $`k` yields exactly $`k` body executions. Identify the extra equality used beyond Theorem 13.1.

*Further problem.* On a store with nonnegative integers `x,y`, repeat the following while both are positive: if `x ≥ y` subtract `y` from `x`, otherwise subtract `x` from `y`. Find a natural-valued variant and prove total correctness for the postcondition that at least one coordinate is zero. Does this measure give the exact iteration count?

# Reading for the Seminar
%%%
tag := "ch12-s5"
number := false
%%%

*Definitions · 10 minutes.* Trace the two-counter loop and record the value of the variant at each head.

*Joint proof · 30 minutes.* Write the induction assertion with its quantifiers. For the true guard put the body derivation and recursive loop derivation on the board. Justify where each comes from.

*Proof review · 20 minutes.* Test the theorem after weakening each of its two termination premises as in Exercises 1 and 2.

*Facilitator’s hint.* A partial triple can be valid for a body with no final state. Ask where the proof obtains its intermediate state.

# Solutions
%%%
tag := "ch12-s6"
number := false
%%%

*1.* Use a constantly true guard, body skip, invariant true, and variant constantly zero. Every execution of the body ends with the same measure. The loop never reaches an exit.

*2.* Use a constantly true outer guard and, as body, another loop with constantly true guard and body skip. Choose variant zero and invariant true. No body execution terminates, so every partial obligation about its final state holds vacuously. The outer loop has no terminating derivation.

*3.* At zero the guard is false. At each positive sum, nonnegativity ensures the guard is true and one body execution takes the sum to exactly $`k - 1`. Induction on $`k` gives exactly $`1 + \left( {k - 1} \right)` executions in the positive case. A general variant could decrease by more than one.

*Further problem.* Preserve nonnegativity of both coordinates and use their sum as a natural-valued variant. In the first branch the guard gives `y > 0` and the branch test gives `x ≥ y`. The new value `x − y` is therefore nonnegative, and the sum strictly decreases by the positive quantity `y`. In the second branch `y > x` and `x > 0`. The new value `y − x` is nonnegative and the sum decreases by `x`. Both bodies are single total assignments. These facts give the total body premise at an arbitrary fixed old sum.

By Theorem 13.1 the loop reaches a head at which the guard is false and the invariant still holds. Since both coordinates are nonnegative, one must now be zero, which is exactly the postcondition. The sum does not give an exact iteration count. From `(3,3)` a single step reaches `(0,3)`, although the initial measure was six. A natural measure that drops by at least one bounds the number of iterations from above; its precise decrement and its value at exit determine whether one can strengthen this bound to an equality.
