import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Loop Invariants" =>
%%%
tag := "ch11"
file := "chapter-11"
%%%

[Chapter PDF](print/chapter-11.pdf) · [Session 12](seminar/index.html#week-12)

After the first two iterations of a summation loop the accumulator contains three. After the third it contains six. To verify summation for every input we need an equation that remains true when one more summand is added. We also need enough information about the index to recover the requested sum when the guard becomes false.

*Sources.* _The Hitchhiker’s Guide to Logical Verification_ (2026), §§10.5–10.7, pp. 147–151. Follow the invariant in the addition program, then locate the obligations produced by the verification condition generator. We derive those obligations for summation over an interval. Reynolds, _Theories of Programming Languages_, §3.4 gives the while rule. [Guide, 2026 edition.](https://raw.githubusercontent.com/lean-forward/logical_verification_2026/460f6be0846eefc3d9441e4e48d75753fcfe1709/hitchhikers_guide_2026_desktop.pdf) [Lean companion.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709) [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Partial correctness
%%%
tag := "ch11-s1"
%%%

Let $`s \vdash c \Downarrow t` mean that command $`c` terminates from $`s` in $`t`. An assertion is a predicate on states. A partial-correctness triple with precondition $`P` and postcondition $`Q` means that for all $`s,t`, if $`P(s)` and $`s \vdash c \Downarrow t` hold, then $`Q(t)` holds. An assertion $`I` is an invariant for a loop with guard $`b` and body $`c` if every terminating execution of the body from a state satisfying $`I` and $`b` ends in a state satisfying $`I`. An invariant is asserted at loop heads, including the final test.

Given a precondition $`P` at entry and a desired postcondition $`Q`, the following three obligations suffice. As in Chapter 2, $`B(b,s)` holds when guard $`b` evaluates to true in state $`s`.

1. *Entry.* For every $`s`, $`P(s)` implies $`I(s)`.
2. *Preservation.* For every $`s,t`, if $`I(s)`, $`B(b,s)` and $`s \vdash c \Downarrow t`, then $`I(t)`.
3. *Exit.* For every $`s`, $`I(s)` and $`\neg B(b,s)` imply $`Q(s)`.

*Soundness.* Induct on a terminating loop derivation starting with $`I`. If the last rule exits, the final state equals the initial state, so use the exit obligation. If it iterates, the true guard and body derivation establish $`I` at the intermediate state by preservation. Apply the induction hypothesis to the smaller loop derivation starting there. Entry permits the argument to begin at any $`P`-state.

*Reachable states and inductive assertions.* Fix a set of initial stores and define `H` to be the set of all stores reached at the loop head after finitely many completed iterations from those entries. Include the stores reached before the first guard test. Then `H` satisfies entry and preservation by its definition. For preservation, append one terminating execution of the body to the finite history that witnesses reachability of the given head. This also proves minimality: for any assertion satisfying entry and preservation, induction on the length of a history puts each store in `H` inside that assertion. Restrict the entry set to the stores immediately after any initialization code.

The exact set `H` is rarely easy to describe with arithmetic formulas. An invariant used in a proof can therefore include stores unreachable from the intended entries. Preservation and exit must both hold on those extra stores as well. For instance with entry `x = 0` and body `x := x + 2` under guard `x < 9`, all reachable head values are even. The predicate `x ≤ 10` includes the unreachable value 9 and still satisfies preservation. However, it cannot on its own establish the exact exit value 10, since at 9 the guard is already false. Adding evenness makes the exit conclusion follow.

# Summation
%%%
tag := "ch11-s2"
%%%

Use distinct integer variables $`i,a,n`. The input $`n` stays fixed throughout. In the code, the right side of an assignment reads the current state.

```
i := 0; a := 0;
while i < n do (i := i + 1; a := a + i)
```

For $`n \geq 0` we claim that any final state satisfies $`2a = n\left( {n + 1} \right)`. Multiplication in this assertion is ordinary integer multiplication in the specification. The program uses only additions and a comparison. The invariant at the head is

$$`I\quad \equiv \quad 0 \leq i \leq n\quad \land \quad 2a = i\left( {i + 1} \right).`

At entry the two initialization assignments give $`i = a = 0`, and $`0 \leq n` supplies the upper bound. For preservation, let $`j` and $`A` be the old values of $`i` and $`a`. The guard gives $`j < n`. Because these are integers, $`j + 1 \leq n`. The first assignment writes $`j + 1`. The second reads this *new* index and writes $`A + j + 1`. The required equation follows:

$$`2\left( {A + j + 1} \right) = j\left( {j + 1} \right) + 2\left( {j + 1} \right) = \left( {j + 1} \right)\left( {j + 2} \right).`

At exit, $`i \geq n` from the false guard combines with $`i \leq n` from the invariant to give $`i = n`. Substitution yields the postcondition.

*Deriving the accumulator equation.* At a head with index `j`, let `S(j)` be the sum of the integers from 1 through `j`, with `S(0) = 0`. The two assignments implement the recurrence `S(j + 1) = S(j) + j + 1`. This suggests the direct invariant `a = S(i)`. To use the closed arithmetic invariant in the text, prove once by induction that `2S(j) = j(j + 1)` for every natural `j`. The step expands twice the recurrence and factors out `j + 1`. The invariant's bound `i ≥ 0` makes the identity applicable even though the program stores integers.

The doubled equation avoids introducing integer division into the proof. Stating `a = i(i + 1)/2` would require a convention for division and, depending on that convention, a proof that the product is divisible by two. The doubled version needs just addition, multiplication, and equality in the assertion language. The recurrence also predicts which proof would survive changing the summand. If the body accumulated `2i` after incrementing, the recurrence would be `T(j + 1) = T(j) + 2(j + 1)` and the corresponding equation would be `a = i(i + 1)`. The index bounds and the exit argument would be identical.

The preservation calculation has two independent conclusions. The updated index stays within bounds by discreteness of integers; the accumulator equation follows by substituting the old invariant and expanding the two products. Lean's `omega` handles the linear inequalities, while `grind` can normalize the polynomial identity.

```lean
example (i a n : Int) (lo : 0 ≤ i) (guard : i < n)
    (eqn : 2 * a = i * (i + 1)) :
    (0 ≤ i + 1 ∧ i + 1 ≤ n) ∧
      2 * (a + (i + 1)) = (i + 1) * (i + 2) := by
  constructor
  · omega
  · grind
```

# Deriving the body obligation backwards
%%%
tag := "ch11-s3"
%%%

For any postcondition $`R`, the assertion required before $`x ≔ e` is $`R` evaluated in the updated state (Chapter 10). Apply this rule to the two assignments in reverse order. Immediately before $`a ≔ a + i` we need $`0 \leq i \leq n` and $`2\left( {a + i} \right) = i\left( {i + 1} \right)`. Before $`i ≔ i + 1` this becomes $`0 \leq i + 1 \leq n` and $`2\left( {a + i + 1} \right) = \left( {i + 1} \right)\left( {i + 2} \right)`. The old invariant and guard entail precisely these conditions. A verification condition generator computes these formulas once supplied with a loop invariant. Choosing the invariant still requires knowledge of the program.

*Recording the assertion inside the body.* Introduce the name `J` for the assertion immediately after the index increment. One can write `J` as `1 ≤ i ≤ n ∧ 2a = (i − 1)i`. To establish it, let the old index be `j`. The true guard and bounds give `1 ≤ j + 1 ≤ n`. Substituting `j + 1` for `i` in the equation of `J` gives `2a = j(j + 1)`, precisely the old loop invariant. To use `J` at the second assignment, add `2i` to each side. The result is `2(a + i) = (i − 1)i + 2i = i(i + 1)`, the loop-head equation for the updated accumulator.

This written intermediate assertion can locate an error at a specific statement. Suppose an implementation increments the index and then executes `a := a + i + 1`. It still establishes `J` after the increment. Pulling the invariant through the second assignment now requires `2(a + i + 1) = i(i + 1)`. Already at the first iteration with `n = 1`, the intermediate values are `i = 1` and `a = 0`. The left side is four and the right side two. The failing implication gives an actual reachable counterexample to preservation for the modified program.

*Soundness and relative completeness.* Soundness takes a proof in the Hoare calculus and establishes semantic validity. Relative completeness starts with a valid triple. For deterministic IMP, if the assertion language can express the required intermediate predicates and true implications between assertions are available in the rule of consequence, the calculus can derive the triple. For a sequence, an intermediate assertion describes exactly the states from which the suffix satisfies the postcondition on termination. The ability to express that assertion matters even when the sequence rule itself is simple. Neither direction asserts that a particular program terminates; Chapter 12 adds that obligation. See Winskel §§7.2–7.4.

# Exercises
%%%
tag := "ch11-s4"
number := false
%%%

1. Remove $`i \leq n` from the invariant. Exhibit a state satisfying the weakened invariant and the exit guard that violates the postcondition.
2. Reverse the assignments in the body. Start with $`n = 2` and derive the accumulator equation that the modified body preserves.
3. Explain why the proof of §11.1 contains no induction hypothesis for a nonterminating execution.

*Further problem.* Suppose the summation loop accumulates odd numbers by executing `a := a + i + i + 1; i := i + 1` from an initialization `a = i = 0` while `i < n`. For nonnegative integer `n`, find an invariant establishing final `a = n²`. Give the intermediate assertion between assignments and identify which values are read.

# Reading for the Seminar
%%%
tag := "ch11-s5"
number := false
%%%

*Definitions · 10 minutes.* Execute the first two iterations with $`n = 3`. Put the old and new index in separate columns.

*Joint proof · 30 minutes.* Write entry, preservation and exit without their proofs. Have one participant obtain the body obligation backwards and another establish it from the old values.

*Proof review · 20 minutes.* Try the weakened invariant of Exercise 1. Decide whether its failure refutes the program or just the proposed proof.

*Facilitator’s hint.* At exit, ask for the two separate inequalities needed to infer equality. Only one comes from the guard.

# Solutions
%%%
tag := "ch11-s6"
number := false
%%%

*1.* Take $`n = 1,i = 2,a = 3`. The guard is false and $`2a = 6 = i\left( {i + 1} \right)`, whereas $`n\left( {n + 1} \right) = 2`. This state need not be reachable. An entailment between assertions must hold at every state satisfying its hypotheses.

*2.* The accumulator becomes $`0` and then $`1`. Since the old index is now the summand, the new equation is $`2a = i\left( {i - 1} \right)`. At index $`j + 1` the left side becomes $`j\left( {j - 1} \right) + 2j = j\left( {j + 1} \right)`, as required.

*3.* Partial correctness quantifies over finite terminating derivations. If there is none at an input, that input contributes no final-state obligation. Chapter 12 adds the missing existence argument.

*Further problem.* At the head take `0 ≤ i ≤ n ∧ a = i²`. Initialization establishes this for every `n ≥ 0`. Let `j` be the old index. With a true guard, discreteness gives `j + 1 ≤ n`. The accumulator assignment reads the old `a = j²` and the old `i = j` twice, so the new accumulator is `j² + 2j + 1 = (j + 1)²`. The index still equals `j` at this point. A sufficient intermediate assertion is therefore `0 ≤ i < n ∧ a = (i + 1)²`.

The index assignment now writes `j + 1` without changing the accumulator. The intermediate assertion yields both the new bound and equality with the square of the new index. This proves preservation of the loop-head assertion. At exit the unchanged upper bound and the failed test force `i = n`, hence `a = n²`. This is a partial correctness argument. Its algebraic step also explains the choice of summand: increasing the index by one increases its square by exactly the old index doubled plus one.
