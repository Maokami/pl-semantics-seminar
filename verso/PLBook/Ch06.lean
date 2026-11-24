import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Program Equivalence" =>
%%%
tag := "ch06"
file := "chapter-06"
%%%

[Chapter PDF](print/chapter-06.pdf) · [Session 7](seminar/index.html#week-07)

A source transformation may change the number of command steps while preserving the final store of every terminating run. To make this claim precise we must choose the input states, the observations at the end of a run, and the executions that contribute observations. We use the deterministic integer IMP of Chapters 2–5.

*Sources.* Nipkow and Klein, _Concrete Semantics_, §7.2.4 on command equivalence. Read the definition as a statement quantified over two stores. The joint theorem is the unfolding of a while command. For a Lean comparison, consult _The Hitchhiker’s Guide to Logical Verification_, chapter 9, exercise Q2.1. Our argument uses the guards and execution rules of Chapter 2. [Concrete Semantics, chapter 7.](https://concrete-semantics.org/concrete-semantics.pdf) [Hitchhiker’s Guide.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

# Equivalence as equality of observations
%%%
tag := "ch06-s1"
%%%

*Definition 6.1.* For a command $`c` and initial state $`s`, put $`R_{c}(s) = \left\{ t \in \Sigma\ \mid s \vdash c \Downarrow t \right\}`, where $`\Sigma` is the set of stores. Commands $`c` and $`d` are equivalent, written $`c \equiv d`, if $`R_{c}(s) = R_{d}(s)` for every $`s`. Equivalently, for every pair $`s,t`, $`s \vdash c \Downarrow t` holds exactly when $`s \vdash d \Downarrow t` does.

Equality of sets gives reflexivity, symmetry and transitivity. The definition also makes sense for relations with several results. In the present language Chapter 3 ensures each result set is empty or a singleton. The observation is the whole final store. Intermediate changes and the number of steps are absent from $`R_{c}`.

*Example 6.2.* For any state, `x := x + 0` returns that same state. Its value at $`x` is $`s(x) + 0 = s(x)`, and at any other name it agrees by definition of update. Hence it is equivalent to skip. One of the commands takes an assignment step in the small-step semantics and skip takes zero steps. Chapter 5 explains why this is consistent with equivalence.

*Removing a dead assignment.* Let `x` and `y` be distinct. Consider the pair `x := 0; x := y + 1` and `x := y + 1`. To prove equivalence, choose an arbitrary input `s`. After the first assignment the store is `u = s[x ↦ 0]`. Since `u(y) = s(y)`, the last assignment writes exactly the value written by the shorter command. At `x` both results contain `s(y) + 1`. At each name distinct from `x` both equal the initial store. Extensional equality of stores and the execution rules give equality of the singleton result sets at every input.

Two assumptions do separate work here. The second expression must give the same result after the first write. Replacing `y + 1` by `x + 1` violates that condition, as witnessed by an initial value `s(x) = 4`. The first assignment must also complete. If a language admitted an expression that could diverge, erasing an assignment whose expression diverges could turn an empty result set into a singleton even when the assigned variable is never read. The ordinary integer expressions of this chapter meet the termination condition. This explains which parts of the proof may be reused when the expression language changes.

# Loop unfolding
%%%
tag := "ch06-s2"
%%%

Let $`W` stand for `while b do a` and $`U` for `if b then (a; W) else skip`, where the abbreviation $`W` denotes the original loop. All occurrences of $`b` have the same total, side-effect-free meaning $`B`.

*Theorem 6.3.* $`W \equiv U`.

*Forward proof.* Fix two arbitrary states and a derivation of $`s \vdash W \Downarrow t`. If its last rule is the exit rule, then $`B\left( {b,s} \right)` is false and $`t = s`. Use skip and the false conditional rule to derive $`s \vdash U \Downarrow t`. If its last rule is iteration, the premises give $`B\left( {b,s} \right)` true, $`s \vdash a \Downarrow u`, and $`u \vdash W \Downarrow t` for some $`u`. Join the last two derivations by the sequence rule, then use the true conditional rule. The loop subtree from $`u` is already present in the hypothesis.

*Reverse proof.* Now start with a derivation of $`s \vdash U \Downarrow t`. Invert its conditional rule. The false branch provides $`s \vdash \operatorname{skip} \Downarrow t`, hence $`t = s` and the loop exit rule applies. The true branch provides $`s \vdash a\ \text{;}\ W \Downarrow t`. Invert sequence to obtain its middle state $`u` and a derivation for each side. Together with the true guard, these are the premises of the loop iteration rule. This proves the reverse implication for all states and hence the equivalence. $`\square`

This argument uses inversion followed by construction. It requires no hypothesis that the two commands terminate on every input. If no terminating derivation exists on one side, the implication from the other side rules out a terminating derivation there as well. The result is a statement about finite execution evidence.

*Finite unfolding as a proof technique.* Define `U₀ = W` and define `Uₙ₊₁` by replacing the recursive loop in one copy of the unfolded conditional by `Uₙ`. For example, `U₂` tests the guard, executes a body if necessary, tests the guard in the resulting store, and on a second true test executes the body followed by `W`. A false test at either site exits through skip. Each test must use its own input state. Hoisting both tests to the entry substitutes a different condition whenever the body changes a name read by the guard.

For a concrete calculation take the guard `x < y`, the body `x := y`, and an initial store with `x = 0` and `y = 2`. The first test is true. The second sees the intermediate store with `x = y = 2` and exits. More generally, if executing the body always makes a true guard false, inversion shows that each terminating run has at most one body execution. In that special case replacing the residual loop after the first body by skip preserves the result, provided the body is allowed to diverge on both sides. The extra fact needed for this stronger rewrite is a property of the body and guard together.

# Replacement within a larger command
%%%
tag := "ch06-s3"
%%%

The unfolded loop often occurs inside another program. Equivalence supports replacement within a suffix because the surrounding sequence can see only the middle store left by its first operand.

*Proposition 6.4.* If $`c \equiv d` then $`c\ \text{;}\ k \equiv d\ \text{;}\ k` for every $`k`.

*Proof.* Invert $`s \vdash c\ \text{;}\ k \Downarrow t` to obtain $`s \vdash c \Downarrow u` and $`u \vdash k \Downarrow t`. By the hypothesis, $`s \vdash d \Downarrow u` has a derivation. Reuse the execution of $`k` from that same $`u`. The sequence rule gives $`s \vdash d\ \text{;}\ k \Downarrow t`. For the reverse implication interchange $`c` and $`d` using symmetry. $`\square`

Suppose instead we observed only the final value of $`x`. From any initial state, `y := 1` and `y := 2` would agree at $`x` when $`x \neq y`. The suffix `x := y` would distinguish them. Reusing a suffix proof requires enough agreement at the join for the suffix’s later reads. Chapter 42 will make an explicit set of observed variables part of a transformation theorem.

*Replacement inside a loop.* Suppose `a ≡ a′`, and write `W` and `W′` for the loops with the common guard `b` and these two bodies. A loop may run its body many times, so a single application of the premise to the entry state does not establish the required implication. Fix a derivation of $`s \vdash W \Downarrow t`. Induct on the number of iteration rules down its recursive loop branch. At zero the derivation ends with the exit rule. The unchanged guard is false, so the very same exit proves $`s \vdash W' \Downarrow t`.

At a positive number, inversion exposes a state `u` with $`s \vdash a \Downarrow u` and a derivation of $`u \vdash W \Downarrow t` with one fewer iteration. Equivalence provides $`s \vdash a' \Downarrow u`. Because the result is the same entire store, the induction hypothesis applies to the residual loop starting at exactly `u`. The iteration rule reconstructs $`s \vdash W' \Downarrow t`. Exchanging the bodies proves the converse. This proof permits the number of small steps taken *inside* a body to change. What remains aligned from one iteration to the next is the store passed to the guard. The same reasoning supplies the loop case when proving that replacement is valid in every command context by induction on the surrounding syntax.

For a suffix context, equivalence at *every* potential middle store can be used directly under an existential. This checked proof preserves the witness in both directions. It makes no determinacy assumption.

```lean
example {S : Type} (R R' K : S → S → Prop)
    (eqv : ∀ s u, R s u ↔ R' s u) (s t : S) :
    (∃ u, R s u ∧ K u t) ↔ (∃ u, R' s u ∧ K u t) := by
  constructor
  · rintro ⟨u, left, right⟩
    exact ⟨u, (eqv s u).mp left, right⟩
  · rintro ⟨u, left, right⟩
    exact ⟨u, (eqv s u).mpr left, right⟩
```

*Proposition 6.5 (Observing a store one variable at a time).* Fix a variable `out`. For any variable y, run c from s, append `out := y`, and observe only the final integer in `out`. Let $`O(c,s,y)` be the set of integers this experiment can return; it is empty if c has no terminating run. In deterministic IMP, two commands are equivalent in the sense of Definition 6.1 if and only if $`O(c,s,y)=O(d,s,y)` for every initial store s and every variable y.

*Proof.* The assignment rule gives $`O(c,s,y)=\{t(y)\mid t\in R_c(s)\}`. Equal result sets therefore give equal observations. Conversely suppose all observations agree, and choose a terminating result t of c from s. The experiment y = out returns t(out), so d must terminate from s. Fix its result u. For every y the observation for c contains t(y). Determinacy of d makes its observation set the singleton $`\{u(y)\}`. Hence t(y) = u(y) for every y, and equality of stores as functions gives t = u. This proves one inclusion; interchange c and d for the other. The variable out need not be fresh: the assignment reads y before it writes out.

*Where determinacy enters.* Suppose commands could choose between two outcomes. One command sets (x,y) to either (0,0) or (1,1); another sets it to either (0,1) or (1,0). Take x and y distinct and leave other variables unchanged. Reading any single coordinate gives the same set for both commands. Yet only the first command admits an outcome with x = y. In the proof above, fixing one result u before varying the tested variable is the step that fails. This counterexample concerns the stated family of tests; a suffix that computes x + y distinguishes the commands.

# Exercises
%%%
tag := "ch06-s4"
number := false
%%%

*6.1.* Use the sequence characterization from Chapter 2 to prove associativity up to equivalence of command sequencing. Name both middle states.

*6.2.* Refute the proposed equivalence of a while command and `if b then a else skip`. Give a terminating integer example and compute both final stores.

*6.3.* If one loop emits an output before diverging and another silently diverges, would the definition in §6.1 distinguish them, assuming it records only terminating stores? What additional observation would suffice?

*Further problem.* Decide whether `if b then (c; k) else (d; k)` and `(if b then c else d); k` are equivalent for arbitrary commands in IMP. Then examine the proposed counterpart that moves a *prefix* in front of a test. Identify a sufficient condition on the prefix and guard, and exhibit a failure when it is dropped.

# Reading for the Seminar
%%%
tag := "ch06-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the two commands in Theorem 6.3 and quantify explicitly over the initial and final stores.

*Joint proof · 30 minutes.* Use Theorem 6.3 and Proposition 6.4 to replace a loop inside a sequence. Derive the observation formula of Proposition 6.5 from the assignment rule.

*Proof review · 20 minutes.* Prove the reverse implication of Proposition 6.5. Mark where one final store is fixed for all variables; test that step on the two nondeterministic commands.

*Facilitator’s hint.* Underline the recursive loop judgment already available as a premise. Ask where exactly that same judgment belongs in the target tree.

# Solutions
%%%
tag := "ch06-s6"
number := false
%%%

*6.1.* A run of the left association first executes $`c`, then $`d`, then $`k`, through states $`s,u,v,t`. Two inversions recover the three subderivations. Compose $`d` with $`k` at $`v`, then compose $`c` with that result at $`u`. The reverse direction regroups the same three derivations in the opposite order.

*6.2.* Use guard $`x < 2`, body `x := x + 1`, and initial value zero. One conditional execution leaves $`x = 1`. Two loop iterations followed by an exit leave $`x = 2`. All other names agree.

*6.3.* Both result sets would be empty, so the proposed observation identifies them. Observing a finite prefix containing the first output separates them. The choice of observations must be revisited when the language gains output.

*Further problem.* Fix an initial store. Both commands with the common suffix inspect the guard there. If it is true, a terminating execution on either side consists of a run of `c` to some middle store followed by a run of `k` from there. The same witnesses yield executions in either syntax tree. The false branch replaces `c` by `d` and gives the same argument.

For the prefix version compare `if b then (k; c) else (k; d)` with `k; (if b then c else d)`. It suffices that every terminating execution of `k` from any `s` to `u` preserves the truth value of `b`. Both derivations then use that same prefix execution, select the same branch, and reuse its derivation. If the prefix diverges neither command yields a result. For a counterexample use `x = 0` as guard, `x := 1` as prefix, and branches assigning 1 or 2 to a distinct `y`. From `x = 0` the two programs end with different values of `y`.
