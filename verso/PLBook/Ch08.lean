import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Finite Approximations of a Loop" =>
%%%
tag := "ch08"
file := "chapter-08"
%%%

[Chapter PDF](print/chapter-08.pdf) · [Session 9](seminar/index.html#week-09)

The equation “execute the body, then execute the loop again” admits spurious solutions. For an always-true loop whose body is skip, the equation merely requires that a proposed meaning equal itself. To choose the meaning determined by finite terminating executions, start with no known results and unfold the loop a finite number of times.

*Sources.* Reynolds, _Theories of Programming Languages_, §§2.3–2.4, especially the least fixed-point theorem. Fix the meaning of the body before varying the meaning of the recursive occurrence. The joint theorem identifies exactly which finite runs are visible at a particular unfolding depth. [Reynolds, chapter 2.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# The unfolding operation
%%%
tag := "ch08-s1"
%%%

Fix a guard $`b` with truth value $`B\left( {b,s} \right)` in each state and a body meaning $`g:\Sigma\rightarrow\Sigma_{\bot}`. The flat lifted outcomes and their pointwise function order are those of Chapter 7. For a proposed meaning $`h` of the recursive occurrence, define $`F(h)` by

$$`F(h)(s) = \left\{ \begin{matrix} {s\ } & {\text{if the guard is false at}\ s} \\ {\bot\ } & {\text{if the guard is true and}\ g(s) = \bot} \\ {h(u)\ } & {\text{if the guard is true and}\ g(s) = u \in \Sigma} \end{matrix} \right..`

An *iteration* counts one completed body execution. Testing the false guard at exit executes zero bodies. Let $`w_{0}(s) = \bot` at every input and put $`w_{n + 1} = F\left( w_{n} \right)` for natural $`n`. The first approximation $`w_{1}` can already discover an exit without executing a body. In the true case it consults $`w_{0}` on the successor state, so it cannot yet report a terminating state there.

*Monotonicity.* If $`h \sqsubseteq h'`, then $`F(h) \sqsubseteq F\left( h' \right)`. At an input taking either of the first two cases the results are identical. In the remaining case compare $`h(u)` and $`h'(u)`. Since $`w_{0}` is least, $`w_{0} \sqsubseteq w_{1}`. Monotonicity propagates the inequality to every adjacent pair.

*Body divergence and recursive divergence.* Take a body that returns its input whenever `y = 0` and diverges otherwise. Such a meaning is realizable with a loop that repeatedly executes skip while `y ≠ 0`. Use `x > 0` as the guard of the outer loop. On an input with `x = 0` and `y = 1`, every positive approximation returns the input. The guard bypasses the body. On an input with `x = 1` and `y = 1`, every positive approximation gives bottom because the body gives bottom. In this branch changing the proposed recursive meaning `h` can have no effect.

There is a third case. At `x = 1` and `y = 0` the body returns the same state `s` and the guard stays true. Consequently `F(h)(s) = h(s)` for *every* proposal `h`. Starting the iteration at bottom again gives bottom at every stage, this time by induction rather than by inspecting the body alone. Both diverging inputs ultimately have the same denotation. The defining equation distinguishes their explanations: one never reaches a recursive call, the other repeatedly reaches one. A proof of monotonicity compares proposed recursive meanings only in this last branch.

# Counting completed bodies
%%%
tag := "ch08-s2"
%%%

A loop terminates after exactly $`k` body executions in this model when there exist states $`s_{0},\ldots,s_{k}` starting at $`s_{0} = s`, with the guard true and $`g\left( s_{i} \right) = s_{i + 1}` at each $`i < k`, and the guard false at $`s_{k}`. These states determine the final result $`s_{k}`. If $`k = 0`, the starting state already satisfies the exit condition.

*Theorem 8.1.* For any such run and any $`n`, the result $`w_{n}(s)` is bottom for $`n \leq k` and equals $`s_{k}` for $`n \geq k + 1`.

*Proof.* Induct on $`k`, stating the claim for all allowed starting states and all $`n`. For $`k = 0`, $`w_{0}` gives bottom. Every positive stage tests the false guard and returns $`s = s_{0}`. For a run of length $`k + 1`, the initial guard is true and $`g(s) = u` begins a run of length $`k`. Stage zero returns bottom. At stage $`n + 1`, the equation gives $`w_{n + 1}(s) = w_{n}(u)`. The induction hypothesis applied at $`u` gives bottom for $`n \leq k` and the final state for $`n \geq k + 1`. Shifting the stage index back by one proves the claim for length $`k + 1`. $`\square`

*Converse.* If $`w_{n}(s) = t` is a state, there is a finite run to $`t` with fewer than $`n` body executions. Induct on $`n`. The premise is impossible at zero. At the next stage a false guard gives an immediate exit. A true guard must yield an ordinary body result $`u` and a state result from the preceding approximation at $`u`. Prepend this body execution to the shorter run supplied by induction. This argument excludes a fabricated state result at any finite depth.

*Example.* Let the body increment $`x` and the guard be $`x < 2`. At the state with $`x = 2`, stage 1 already returns that state. From $`x = 1`, stage 1 gives bottom and stage 2 returns the state with $`x = 2`. From $`x = 0`, the first state result is at stage 3. These are three distinct inputs to the *same* functions $`w_{n}`. Store coordinates other than $`x` are preserved.

*Which computation does the counter measure?* Consider an outer loop with guard `x > 0` and body `(while y > 0 do y := y − 1); x := 0`. Let the input have `x = 1` and `y = 100`. The inner loop completes one hundred body executions. The assignment then changes `x` to zero, and the outer guard becomes false. The outer run has exactly one completed body. Its result first occurs in `w₂`. The entire inner computation is included in the already fixed meaning `g` of the outer body.

Taking the inner loop in isolation gives a different calculation. At the same input its own first state result occurs at its stage 101. There is no contradiction between the two indices: each approximating sequence belongs to a specific occurrence of a loop, with its own fixed body meaning. Neither index measures machine time or counts all execution-rule applications. A single outer body can also fail to complete, in which case there is no successor state to which a smaller outer approximation can be applied. This example explains why the statement of Theorem 8.1 specifies a sequence of *completed* body executions and includes a final false test.

A single natural-valued counter suffices to check the stage shift. The loop decrements a positive counter. Stage zero has no known outcome, a positive stage recognizes an exit at zero, and a positive counter consumes one stage to execute a body. In the successor case of the proof the smaller counter has precisely one fewer available unfolding.

```lean
def countdownApprox : Nat → Nat → Option Nat
  | 0, _ => none
  | _ + 1, 0 => some 0
  | stage + 1, counter + 1 => countdownApprox stage counter

example (k : Nat) :
    countdownApprox k k = none ∧ countdownApprox (k + 1) k = some 0 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih => exact ih
```

# Least fixed point
%%%
tag := "ch08-s3"
%%%

For an increasing sequence $`h_{n}` define its supremum pointwise as in Chapter 7. Call $`F` continuous here if it preserves suprema of such sequences. Our $`F` is continuous: for fixed $`s`, the exit and diverging-body branches are constant in $`h_{n}`, and the ordinary true branch evaluates the sequence at one fixed $`u`. In all three cases, taking the pointwise supremum before or after applying $`F` gives the same outcome.

Set $`w` equal to the supremum of the $`w_{n}`. Continuity gives $`F(w) = \sup_{n}F\left( w_{n} \right) = \sup_{n}w_{n + 1} = w`. Dropping the first, least element leaves the same upper bounds. To prove leastness, take any fixed point $`p = F(p)`. By induction, $`w_{0} \sqsubseteq p` and $`w_{n} \sqsubseteq p` implies $`F\left( w_{n} \right) \sqsubseteq F(p) = p`. Thus $`p` bounds the chain, and $`w \sqsubseteq p`. This is the Kleene construction for this loop operator.

*What leastness rules out.* Let `W` be `while x > 0 do skip`. For states where `x ≤ 0` its defining equation forces any fixed point `p` to return its input. For states with `x > 0` the equation reduces to `p(s) = p(s)`. At these inputs one may freely choose bottom or any state at all and still obtain a mathematical solution. In particular the everywhere-identity function is a fixed point. Assigning that meaning to the loop would allow an execution to return immediately at `x = 1`.

To identify the least solution, compute the stages as functions of the input. The first positive stage returns `s` on `x ≤ 0` and bottom on `x > 0`. Applying the operator again leaves this function unchanged. Its pointwise supremum is thus already attained at stage one. It lies below every fixed point since they agree on every forced exit and bottom lies below every outcome on the other inputs. Notice that the order compares complete results only at the same state. The proof never ranks stores according to how small their `x` value is. The order used to choose a denotation and an integer order used to prove termination serve different purposes.

# Exercises
%%%
tag := "ch08-s4"
number := false
%%%

*8.1.* For a false guard and a body that would diverge on every input, compute $`w_{0},w_{1},w_{2}`.

*8.2.* For a true guard and a skip body, exhibit two different fixed points and identify the least one.

*8.3.* Explain why an ordinary state at the supremum must already occur at some finite stage in this model.

*Further problem.* Let one integer variable `x` be decremented by two while `x > 0`. Derive an explicit positive stage at which each input returns and compute its final value. Does the increasing chain of transformers stabilize at a single finite stage on all integer inputs?

# Reading for the Seminar
%%%
tag := "ch08-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the three branches of the unfolding operation, including the exit case.

*Joint proof · 30 minutes.* Fill a table of stages 0 to 3 at inputs with x equal to 0, 1 and 2. State and prove the general stage bound. Check the base case by drawing a run with zero bodies.

*Proof review · 20 minutes.* Prove the converse by induction on the stage index. Identify the specific equality in the fixed-point proof that needs continuity.

*Facilitator’s hint.* Use separate indices for the number of bodies and the approximation stage. After one body the remaining run and the available stage both decrease.

# Solutions
%%%
tag := "ch08-s6"
number := false
%%%

*8.1.* Stage zero is constantly bottom. Both positive stages return the original input state. No branch evaluates the body.

*8.2.* Here $`F(h) = h`. Both the constantly bottom function and the identity on states are fixed points, and every function lies above the constantly bottom function.

*8.3.* On each input the chain lies in a flat order. A chain consisting only of bottoms has supremum bottom. If the supremum is a state, some chain element is a state, and every later element equals it. This deduction uses flatness of the result space.

*Further problem.* At an input with `x ≤ 0` the guard is initially false. The loop returns its input at stage one. For `x > 0`, write its value as either `2j` with `j ≥ 1` or `2j + 1` with `j ≥ 0`. In the even case, after `j` completed bodies the value is zero, and each preceding head is positive. Theorem 8.1 gives the first successful stage `j + 1`. In the odd case one reaches 1 after `j` bodies; one more produces −1 and exits. The first successful stage is `j + 2`. Every other store coordinate is preserved.

These formulas yield a finite stage for each input. Nevertheless, for each natural `n ≥ 1` choose `x = 2n`. The stage `n` output on that input is bottom whereas stage `n + 1` returns an ordinary store. Stages zero and one also differ at an initially false guard. Hence no two consecutive transformer stages coincide, even though the least fixed point is defined at every input.
