import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Type Safety for Arithmetic Expressions" =>
%%%
tag := "ch16"
file := "chapter-16"
%%%

[Chapter PDF](print/chapter-16.pdf) · [Session 17](seminar/index.html#week-17)

The term `if 0 then true else false` is closed. Its guard is already a numeral, yet neither conditional reduction rule selects a branch. A type system can exclude such a stuck computation before evaluation begins. We now use Pierce’s language of natural numbers and Booleans; the state and signed integers of Chapter 1 play no role.

*Sources.* Pierce, _Types and Programming Languages_, chapter 8, especially §§8.2–8.3, pp. 92–98. Read the canonical forms lemma and reconstruct the conditional case of progress. The evaluation rules are in §3.5. [Book and section numbers.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Terms, values and steps
%%%
tag := "ch16-s1"
%%%

Terms are `true`, `false`, `0`, `succ t`, `pred t`, `iszero t`, and `if g then a else b`. A *numeric value* is zero or the successor of a numeric value. The values are the numeric values and the two Boolean constants. For example `succ (pred 0)` is a term, and its argument must still step before it becomes a value.

A conditional steps its guard if possible; a true guard selects the first branch and a false guard selects the second. Each unary operation steps its operand if that operand steps. The remaining computation rules send `pred 0` to zero and `pred (succ nv)` to the numeric value `nv`. Similarly `iszero 0` returns true and `iszero (succ nv)` returns false. Successor applied to a numeric value is already a value. Write $`t\rightarrow t'` for one such step. A term is *stuck* when it is neither a value nor able to step.

The definition of a numeric value has a premise all the way down its spine. Inspect `pred (succ (if true then 0 else succ 0))`. To use the computation rule for predecessor immediately, its operand would have to be the successor of a numeric value. The conditional inside the successor is still a computation. First the conditional selects zero. The successor propagation rule lifts that step over the surrounding successor, and the predecessor propagation rule lifts the result over the outer predecessor. These three rule applications justify one step of the complete term, to `pred (succ 0)`. Now the predecessor computation rule returns zero in one further step. Counting the nodes in the proof of one step and counting steps of execution answer different questions.

By comparison, `pred (succ false)` admits no such path. The inner Boolean already is a value, so it cannot step. The successor fails the definition of a numeric value because its child is false. Thus the outer computation rule and both possible propagation attempts fail. The syntax still contains a predecessor immediately above a successor. The numeric-value premise is what rules out cancelling them here.

# Typing and canonical forms
%%%
tag := "ch16-s2"
%%%

There are two types, Bool and Nat. The judgment $`t:A` holds when the following rules yield it. The Boolean constants have type Bool, and zero has type Nat. Successor and predecessor take Nat and return Nat. The zero test takes Nat and returns Bool. For a conditional the guard must have type Bool and both branches must have the same type $`A`; the result type is $`A`. Each rule constrains every syntactic child even when only one branch will run.

*Lemma 16.1 (Canonical forms).* A value of type Bool is true or false. A value of type Nat is a numeric value. For the first claim inspect the possible values. Zero can have only Nat from its typing rule, and a successor can have only Nat. This leaves the two Boolean forms. For the second claim the two Boolean forms are excluded by the same inspection. What remains is numeric by the definition of a value. The value hypothesis matters: `iszero 0` has type Bool and is neither Boolean constant.

The canonical forms argument combines information obtained by looking at two different derivations. A value derivation certifies that the inspected term belongs to one of a small number of syntactic classes. A typing derivation identifies which of those classes remain possible. For the conditional guard, knowing its type alone leaves possibilities such as `iszero (pred 0)`, whose first step must take place inside the guard. Knowing only that it is a value also leaves `succ 0`, which cannot select a branch. Meeting the two hypotheses together leaves exactly the information needed for a computation rule.

The following checked example isolates the reasoning at *already established values*. It represents unary numeric values by Lean naturals, and uses a relation assigning each kind of value its corresponding object-language type. Inspecting a proof of Boolean typing eliminates the numeric alternative. This smaller lemma deliberately omits reducible expressions. In the full theorem an additional premise recognizing values is what permits this smaller choice of constructors in the first place.

```lean
namespace ValueForms
inductive Ty where | nat | bool
inductive Val where | num (n : Nat) | yes | no
inductive Has : Val → Ty → Prop where
  | num (n : Nat) : Has (.num n) .nat
  | yes : Has .yes .bool
  | no : Has .no .bool

theorem boolean {v : Val} (h : Has v .bool) : v = .yes ∨ v = .no := by
  cases h with
  | yes => exact Or.inl rfl
  | no => exact Or.inr rfl
end ValueForms
```

# Progress and preservation
%%%
tag := "ch16-s3"
%%%

*Progress.* Every well-typed term in this language is a value or takes a step. Induct on the typing derivation. Constants are values. For a conditional use the induction hypothesis on the guard. A guard step lifts into a step of the conditional. If the guard is a value, its Bool type and Lemma 16.1 give the two cases that select a branch. No assumption about immediate reducibility of the branches is required. For the three unary forms, a step of the argument lifts into the outer term. If the argument is a value, its Nat type implies it is numeric. Successor then forms a value, while predecessor and the zero test each have a rule for zero and for a successor.

*Preservation.* If $`t:A` and $`t\rightarrow t'`, then $`t':A`. Induct on the step. A computation selecting a branch returns a term already typed $`A` by the conditional typing premise. For a step inside the guard, apply the induction hypothesis at Bool, retain the two original branch premises, and rebuild the typing rule. The same rebuilding works under unary operators. The predecessor rules return zero or the inner numeral, both of type Nat; the zero test returns a Boolean constant. These cases exhaust the steps.

Starting from a well-typed term, preservation keeps every term in a finite sequence well typed. If the last term cannot step, progress makes it a value. This argument establishes safety without putting a bound on the length of a computation.

The two safety theorems quantify over different evidence. To use preservation on `if iszero 0 then succ 0 else 0`, begin with a derivation of a particular step. If the step reduces the guard, its premise is `iszero 0 → true`. Invert the conditional typing to recover both branch typings at Nat and the guard typing at Bool. Preservation for the guard step gives a new Boolean guard typing; rebuild exactly the conditional that remains after the step. On the next step the guard is already true. Inverting the same three typing premises now yields the typing of `succ 0` immediately. In the first case the proof constructs a replacement typing node; in the second it reuses an existing premise.

For progress, even before an evaluator has chosen a step, the typing tree supplies the input to induction. The guard hypothesis tells us either that a guard step exists or that the guard is a value. In the latter branch Boolean canonical forms decides which computation rule to use. This order matters when composing progress with preservation over many steps. Progress holds at the next configuration only after preservation has restored its typing premise. Iterating progress by itself would leave the argument without an induction invariant.

# Exercises
%%%
tag := "ch16-s4"
number := false
%%%

1. Type and reduce `if iszero (pred (succ 0)) then 0 else succ 0`. Give the static type at every step.
2. Exhibit an ill-typed conditional that evaluates to a numeric value. Explain why it does not contradict progress.
3. Drop the guard typing premise alone. Which safety theorem fails on the opening example?

*Further problem.* Keep the original typing and evaluation rules, but add the one-step rule `if true then t else u → true`. Give a closed source term witnessing the failure of preservation. Does the original progress theorem still hold? Does one-step evaluation remain deterministic?

# Reading for the Seminar
%%%
tag := "ch16-s5"
number := false
%%%

*Definitions · 10 minutes.* Classify a Boolean constant, a Boolean computation and a stuck guard.

*Joint proof · 30 minutes.* Prove canonical forms at Bool from the list of values. Prove progress at the conditional, marking the exact place where that lemma applies.

*Proof review · 20 minutes.* Try a guard with type Nat after removing its typing premise. Contrast this case with an ill-typed unused branch.

*Facilitator’s hint.* The guard induction hypothesis gives a disjunction. Only its value branch permits the use of canonical forms.

# Solutions
%%%
tag := "ch16-s6"
number := false
%%%

*1.* The guard’s predecessor reduces to zero, the zero test returns true, and the conditional returns zero. Each entire term has type Nat. The intermediate guard always has type Bool.

*2.* For example `if true then 0 else true` steps to zero, although the branches have incompatible types. Progress makes a claim about terms that have a typing derivation.

*3.* The newly admitted term has type Bool, is not a value and cannot step. This refutes progress directly. The failed derivation occurs before any step for preservation to inspect.

*Further problem.* Use the source `if true then 0 else succ 0`. Its guard has type Bool, both branches have type Nat, and the conditional rule therefore assigns Nat to the whole term. The new rule produces true, whose only typing is Bool. The preservation statement requires *every* permitted step from a well-typed source to retain the source type, so this one step refutes it. The original computation rule still permits a step to zero from exactly the same source. Since zero and true are different terms, the extended relation is nondeterministic. Progress survives: take an arbitrary closed typing derivation and apply the old progress theorem. If the term was a value, its value status is unchanged. If there was an old step, its derivation is still admitted by the extended rules. Progress asks for the existence of a step from a nonvalue, with no uniqueness or result-typing condition.
