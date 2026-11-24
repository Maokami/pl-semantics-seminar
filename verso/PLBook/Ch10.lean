import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Hoare Triples and Assignment" =>
%%%
tag := "ch10"
file := "chapter-10"
%%%

[Chapter PDF](print/chapter-10.pdf) · [Session 11](seminar/index.html#week-11)

Suppose a command will increase $`x` by 3 and the required final value is 8. Before the command we need $`x = 5`. A Hoare rule generalizes this backwards calculation to every state predicate. Its soundness is a theorem about the forward execution relation.

*Sources.* Winskel, _The Formal Semantics of Programming Languages_, §6.4, gives the assignment rule for partial correctness. [Book.](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf) Reynolds, _Theories of Programming Languages_, §§3.1–3.3. Read the interpretation of specifications and the rules for assignment and sequencing. The shared proof derives the assignment rule by pulling a set of acceptable final states back through the update. [Reynolds, chapter 3.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Assertions and validity
%%%
tag := "ch10-s1"
%%%

An *assertion* is a predicate on states, equivalently a subset of $`\Sigma`. We write $`P(s)` for membership. The partial-correctness triple $`\{P\}\,c\,\{Q\}` is *valid*, written $`\models \{P\}\,c\,\{Q\}`, precisely when

$$`\forall s,t \in \Sigma,\left( {P(s) \land (s \vdash c \Downarrow t)} \right)\Longrightarrow Q(t).`

Thus a terminating execution from a state satisfying $`P` must end in $`Q`. The universal condition holds vacuously on an initial state from which no execution terminates. This distinction matters when inferring what a valid specification promises.

A proof system manipulates triples as formal conclusions of rules. Write $`\vdash_{\mathrm H} \{P\}\,c\,\{Q\}` when the triple has a derivation in the Hoare proof system. Soundness says that every such derivation establishes semantic validity. For each rule, fixing arbitrary states and using semantic validity of its premises proves preservation of validity. Induction on a full rule derivation then yields soundness for the system covered by those rules.

*Constructing a counterexample to validity.* A specification is invalid precisely when there are stores `s,t` for which all three facts `P(s)`, $`s \vdash c \Downarrow t`, and the failure of `Q(t)` can be established. Consider the proposed triple with precondition `x ≤ y`, command `x := x + 1`, and postcondition `x ≤ y`, for distinct names. Choose a store with `x = y = 0`. The assignment rule gives a final store with `x = 1` and `y = 0`. This pair witnesses invalidity. Running a second example where the initial inequality is strict cannot repair the universal statement.

Now strengthen the precondition to `x < y`. Let `s` be arbitrary with that property. Inversion of the assignment judgment gives `t(x) = s(x) + 1` and `t(y) = s(y)`. The discreteness of the integers yields `s(x) + 1 ≤ s(y)`, as required. This proof uses a fact about the type of values in addition to the assignment rule. With rational variables the strengthened triple would fail, for instance on `x = 0` and `y = 1/2`. The domains in the definition of a store are part of the specification's mathematical hypotheses.

# The inverse image of a postcondition
%%%
tag := "ch10-s2"
%%%

Fix a variable $`x` and arithmetic expression $`e`. Define $`U(s) = s\left\lbrack {x\mapsto\operatorname{eval}\left( {e,s} \right)} \right\rbrack`. For any postcondition $`Q` the inverse image $`U^{- 1}(Q)` is the predicate taking $`s` to $`Q\left( {U(s)} \right)`. The notation requires no inverse function. Assigning a constant may send many different initial states to the same output.

*Theorem 10.1 (Assignment).* The triple with precondition $`U^{- 1}(Q)`, command `x := e`, and postcondition $`Q` is valid. For any predicate $`P`, the triple with $`P` in its place is valid if and only if $`\forall s,P(s)\Longrightarrow Q\left( {U(s)} \right)`.

*Proof.* Suppose $`P` implies that condition and fix $`s,t` satisfying $`P(s)` and $`s \vdash x := e \Downarrow t`. Inversion of assignment gives $`t = U(s)`. Apply the assumption at $`s` to obtain $`Q(t)`. Conversely assume the triple with $`P` is valid. For every $`s` satisfying $`P`, the assignment axiom constructs a terminating execution to $`U(s)`. Validity gives $`Q\left( {U(s)} \right)`. Taking $`P = U^{- 1}(Q)` establishes the rule. $`\square`

In the implication ordering on predicates, a weaker condition permits a larger set of states. The theorem says the inverse image is the *weakest sufficient precondition* here. Any other sufficient set is contained in it. Assignment terminates at every state in this model.

*Calculation.* If $`Q(s)` means $`s(x) = 8`, the inverse image for `x := x + 3` is $`s(x) + 3 = 8`, equivalent over mathematical integers to $`s(x) = 5`. For `x := 8` every input is acceptable. For `x := 7` the acceptable set is empty. All three calculations use exactly the same postcondition.

*What an assignment preserves.* Let `P` be a predicate whose truth is unchanged when the value of `x` alone is changed. More explicitly, whenever two stores agree at all names other than `x`, they agree on the truth of `P`. For each store `s` the stores `s` and `U(s)` meet this premise by the definition of update. Thus `P(U(s))` is equivalent to `P(s)`, and the assignment rule validates the triple with `P` both before and after the assignment. The expression assigned to `x` may read any names, including `x` itself. Preservation depends here on what the assertion observes.

Inverse images also distribute over conjunction. To require both `P` and `Q` after the assignment, require both `P(U(s))` and `Q(U(s))` beforehand. Applying the preceding preservation fact when `P` is independent of `x` simplifies this to `P(s)` and `Q(U(s))`. For instance, for `x := y + 1` with distinct names and postcondition `y ≥ 0 ∧ x ≥ 4`, one obtains `y ≥ 0 ∧ y + 1 ≥ 4`. This calculation justifies carrying an unchanged conjunct across a command, and identifies which conjunct actually contributes a new condition on entry.

Here is the inverse-image calculation as a general fact about an update function `U`. The premise `t = U s` represents the graph of a total deterministic update. For necessity, choose its actual output and prove the graph condition by reflexivity.

```lean
example {S : Type} (U : S → S) (P Q : S → Prop) :
    (∀ s t, P s → t = U s → Q t) ↔ (∀ s, P s → Q (U s)) := by
  constructor
  · intro valid s hp
    exact valid s (U s) hp rfl
  · intro pre s t hp eq
    rw [eq]
    exact pre s hp
```

# From state update to syntactic substitution
%%%
tag := "ch10-s3"
%%%

Consider the assertion syntax $`a_{1} = a_{2}` for arithmetic expressions, evaluated as equality of their integer values in the state. Substituting $`e` for $`x` in each side yields a formula over the original state. By the substitution lemma in Chapter 1, §1.6, each substituted side at $`s` equals the original side at $`U(s)`. Equality is therefore preserved in both directions. The same argument extends to Boolean connectives by their truth tables. For formulas with binders the substitution must also avoid variable capture.

For example, with distinct $`x,y`, take the postcondition $`x = y + 1` and the command `y := x`. Substituting for $`y` produces $`x = x + 1`, which no integer satisfies. The execution sets $`y` equal to $`x`, so indeed no run can make $`x` one greater than $`y` afterward. This example also shows why replacing variables on the wrong side of the assignment would give the wrong precondition.

*Repeated occurrences and bound names.* For `x := x + 1` consider the arithmetic postcondition `x + x = y` with distinct names. The precondition is `(x + 1) + (x + 1) = y`. Both occurrences denote reads from the final store, so both receive the replacement. The occurrences of `x` newly introduced inside `x + 1` refer to the original store and receive no further replacement. This follows directly from the variable case of structural substitution: reaching `x` returns the replacement expression as a whole. An algorithm that recursively processed that returned expression would fail to terminate in this example.

With quantifiers, also distinguish a name bound by a formula from a free state variable. For example, suppose assertion syntax allows an integer binder and postcondition `∃y, x < y`. For the assignment `x := y`, first rename the bound variable to a fresh `z`, giving `∃z, x < z`. Substitution now yields `∃z, y < z`, which is true at every integer store. Blind replacement would produce `∃y, y < y`, which is false everywhere. One can alternatively use separate sets of names for logical variables and program variables. Either convention must preserve the meaning of the free `y` in the assigned expression.

# Backwards reasoning through a sequence
%%%
tag := "ch10-s4"
%%%

Suppose `{P} c {R}` and `{R} d {Q}` are valid. Invert any terminating execution of $`c\ \text{;}\ d` from a $`P`-state to get the intermediate $`u`. The first triple gives $`R(u)` and the second gives $`Q(t)`. This proves the sequencing rule. When both commands are assignments, denote their updates by $`U_{1},U_{2}`. Working backwards yields the precondition $`s\mapsto Q\left( {U_{2}\left( {U_{1}(s)} \right)} \right)`: take the inverse image for the last assignment first.

*An intermediate assertion need not be exact.* Suppose we want to establish `z ≥ 2` after `x := y + 1; z := x + x` with three distinct names. The backwards calculation gives `x + x ≥ 2` immediately before the final assignment and `(y + 1) + (y + 1) ≥ 2` before the sequence. Over integers these predicates simplify to `x ≥ 1` and `y ≥ 0` respectively. From any permitted initial store the first assignment establishes precisely the fact needed at the join.

Suppose instead the available precondition is `y ≥ 10`. One may choose `x ≥ 11` as the intermediate assertion. The prefix establishes it, and it implies `x + x ≥ 2` for the suffix. This establishes a valid triple for the narrower group of inputs. Starting with `y ≥ 0` and choosing that stronger intermediate assertion would fail at the prefix, as the initial value zero demonstrates. Conversely choosing `x ≥ 0` would make the prefix easy but the suffix obligation false at zero. The intermediate predicate in a sequence proof must sit between what the prefix guarantees and what the suffix requires; the assignment calculations specify the latter exactly.

# Exercises
%%%
tag := "ch10-s5"
number := false
%%%

*10.1.* Compute the weakest precondition for `x := y + 2; y := x + 1` with postcondition $`y = 10` and $`x \neq y` as names.

*10.2.* Explain why the valid triple `{true} while true do skip {false}` establishes no contradiction.

*10.3.* Derive the consequence rule: a stronger precondition and a weaker postcondition preserve validity. Specify both implication directions.

*Further problem.* For distinct variables consider `x := y; y := x` and postcondition `x = y ∧ y ≥ 4`. Derive its weakest precondition. Compare this result with a simultaneous swap `(x,y) := (y,x)` in which both right-hand sides use the initial store. Explain precisely where the two backwards calculations differ.

# Reading for the Seminar
%%%
tag := "ch10-s6"
number := false
%%%

*Definitions · 10 minutes.* Fix a postcondition as a set of states and draw an update arrow into that set.

*Joint proof · 30 minutes.* Derive both implications of Theorem 10.1. In the necessity direction ask who supplies the terminating execution. Compute the inverse images for a constant and a dependent assignment.

*Proof review · 20 minutes.* Work backwards through Exercise 10.1, then check the result by executing forwards. Relate the two calculations using the substitution lemma.

*Facilitator’s hint.* Write Q applied to the updated store before performing any textual replacement. Track the initial and final occurrences of the same name separately.

# Solutions
%%%
tag := "ch10-s7"
number := false
%%%

*10.1.* Pull $`y = 10` back through the last assignment to obtain $`x + 1 = 10`, hence $`x = 9`. Pull that back through the first to obtain $`y + 2 = 9`, hence initial $`y = 7`. Starting at any such state the program writes 9 to $`x` and 10 to $`y`.

*10.2.* There is no final state $`t` satisfying the execution premise, so there is no counterexample pair to the universal implication. Total correctness adds a separate termination obligation.

*10.3.* If $`P'(s)\Longrightarrow P(s)` for all $`s` and $`Q(t)\Longrightarrow Q'(t)` for all $`t`, apply the old triple to $`P(s)` and the execution, then use the second implication. This proves validity from $`P'` to $`Q'`.

*Further problem.* Begin at the end of the sequence. Pulling the postcondition back through `y := x` replaces every free occurrence of `y` with `x`, giving `x = x ∧ x ≥ 4`. This simplifies to `x ≥ 4`. Pull through `x := y` to obtain `y ≥ 4`. Necessity can be seen directly: the first assignment reads the old `y` and the second copies precisely that value, so a final common value of at least four requires the old `y` to be at least four.

In a simultaneous swap, the output at `x` is the old `y` and the output at `y` is the old `x`. The inverse image is consequently `y = x ∧ x ≥ 4`. The two replacements in this calculation act on original occurrences simultaneously. Processing already substituted material sequentially would incorrectly turn the equality into a tautology. An input with `x = 1` and `y = 5` separates the preconditions: the sequence yields two fives, whereas the simultaneous swap yields five and one.
