import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Failure and Exception Handling" =>
%%%
tag := "ch32"
file := "chapter-32"
%%%

[Chapter PDF](print/chapter-32.pdf) · [Session 33](seminar/index.html#week-33)

An assignment scheduled after an unsuccessful command should not run. A semantics recording only final states cannot tell whether the prefix explicitly reported failure or ran forever. Adding a separate failure outcome lets us specify how sequencing and handlers respond to it.

*Sources.* Reynolds, _Theories of Programming Languages_, §5.1, pp. 97–100, on the fail command. Pierce, _Types and Programming Languages_, §§14.1–14.3, compares raising, handling and carrying values. The tagged imperative relations below specify our own choices about state and handlers. [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html) [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Tagged outcomes
%%%
tag := "ch32-s1"
%%%

Keep integer IMP and add `fail`. Write $`s \vdash c \Downarrow r` for a terminating execution with result $`r`. The result is either $`\text{ok}(t)` for a normal final state $`t` or the distinguished result $`\text{fail}`. Skip and assignment return their usual states tagged ok. The fail command immediately returns fail. A diverging command has no finite derivation for either tag. These three behaviors can already be observed with skip, fail, and an infinite loop.

For $`c\ \text{;}\ d` there are two rules. If $`s \vdash c \Downarrow \text{fail}`, the entire sequence returns fail. If $`s \vdash c \Downarrow \text{ok}(u)` and $`u \vdash d \Downarrow r`, the sequence returns $`r`, including a possible failure of $`d`. Conditionals pass through the outcome of the selected branch. A true-guard loop propagates body failure immediately; after body success it continues from the new state. False-guard exit returns the current state tagged ok.

Consider `while x > 0 do fail`. If the initial state gives `x` the value three, the guard evaluates to true and the body produces failure immediately. The true-guard rule for a failing body has just these two premises. Its conclusion gives a finite derivation of failure for the entire loop. If the state gives `x` the value zero, the false-guard rule gives normal return with the original state. To see that these are the only possibilities, inspect the last rule of a proposed derivation. For each state exactly one guard premise can hold. In the positive case the rule that would recur on the loop requires normal return of `fail`, for which there is no rule.

The distinction matters when writing an evaluator. A useful result type for the mathematical meaning of these commands is `Option (Except Unit State)`, where `State` is the set of states and `Unit` has a single element. Here `some (.ok t)` represents ordinary return and `some (.error ())` represents a finite execution that fails. The outer `none` represents divergence. This is a description of possible meanings. Computing which of the three cases holds for every program and initial state would decide termination. In particular, exhausting a finite execution budget cannot establish that the mathematical result is `none`.

# Sequencing
%%%
tag := "ch32-s2"
%%%

*Proposition 32.1.* A sequence returns a normal state $`t` exactly when some $`u` is a normal result of its prefix and $`t` is a normal result of its suffix started at $`u`. Inversion on the sequence derivation excludes the failure rule because its conclusion has a different tag. The remaining rule supplies $`u` and both premises. Conversely, join those premises with the second rule. A sequence returns fail exactly when its prefix fails, or its prefix returns some $`u` and its suffix fails from $`u`; inversion and rule construction give the two directions again.

For `fail; x := 7`, the proof of failure has only the premise for the prefix. For `x := 7; fail`, the proof uses the updated state in its second premise. Their observable outcomes in this model are both fail because this result carries no state. The two derivation trees still document different executions. Replacing the first fail by a diverging prefix gives no finite sequence derivation at all.

Associativity of sequencing concerns all three outcomes. Write `p` for the result of the first command at the initial state, and `f` and `g` for the functions from states to results given by the next two commands. Define `continueWith p f` to return the missing result on divergence, to propagate a failure, and to apply `f` to the state on normal return. The two bracketings of three commands now give the two sides of the equation below. The type parameters allow successive computations to pass different sorts of values, although the command language uses a state at every position.

```lean
def continueWith {α β : Type} (p : Option (Except Unit α))
    (f : α → Option (Except Unit β)) : Option (Except Unit β) :=
  match p with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok x) => f x

example {α β γ : Type} (p : Option (Except Unit α))
    (f : α → Option (Except Unit β)) (g : β → Option (Except Unit γ)) :
    continueWith (continueWith p f) g =
      continueWith p (fun x => continueWith (f x) g) := by
  cases p with
  | none => rfl
  | some r => cases r <;> rfl
```

There is a reason the proof never inspects the third command. If the first command diverges or fails, both sides already have the same determined outcome. If it returns `x`, both sides reduce to precisely the same expression, `continueWith (f x) g`. In the big-step semantics, the same argument uses the inversion result above to recover each successful intermediate state before reconstructing the derivation with the other bracketing.

# Handlers and the state at a raise
%%%
tag := "ch32-s3"
%%%

As a separate extension choose exception outcomes $`\text{raise}\left( {k,t} \right)` carrying an exception label $`k` and the state $`t` at the raise. Define `throw k` to produce this outcome from the current state. Sequencing propagates a raised outcome unchanged. A handler `try c catch k => h` passes a normal result through, passes any raised label other than $`k` through, and runs $`h` in the saved state upon receiving the matching label. The outcome of $`h` becomes the outcome of the whole handler. These rules make prior writes visible in the handler.

Run `try (x := 3; throw K) catch K => y := x` starting with $`x = y = 0`. The protected assignment sets $`x` to three. The raise carries that state, so the handler reads three and writes three to $`y`. A rollback design instead starting the handler in the state before the try would yield a different result. The state passed to the handler is part of the language definition.

A handler's scope becomes visible when its handler body raises another exception. Suppose the initial state gives both `x` and `y` the value zero. Run the following nested command.

```
try
  (try (x := 1; throw K)
   catch K => (x := x + 1; throw J))
catch J => y := x
```

The protected command first updates `x`. It returns `raise(K,t₁)`, where `t₁(x) = 1`. The inner handler matches `K` and begins in `t₁`. Its assignment produces `t₂` with `t₂(x) = 2`, and its last command returns `raise(J,t₂)`. This is the outcome of the whole inner handler. The outer handler therefore matches `J` and runs `y := x` in `t₂`. Its normal result has both variables equal to two.

Change the second throw to `throw K`. The inner handler has already selected its handler body. The rule returns that body's outcome directly, so it cannot invoke itself on the new `K`. The enclosing handler matches only `J`, and its pass-through rule yields `raise(K,t₂)` for the entire command. This example separates two questions needed to reconstruct a handler derivation. The label determines which enclosing handler can run. The state in the raised outcome determines which earlier writes that handler can observe.

A handler can distinguish two protected computations that both raise the same exception if they leave different stores visible on entry to the handler. Specify whether the handler receives the entry store or the store at the point of failure before comparing programs.

# Exercises
%%%
tag := "ch32-s4"
number := false
%%%

1. Does `fail; while true do skip` have a finite result? Give the full shape of its derivation.
2. Compare `try (throw J) catch K => skip` for distinct labels with a failed lookup of a handler after infinite execution.
3. In the handler extension prove that normal termination of a sequence still requires normal termination of its prefix.

*Further problem.* Moving a handler across a sequence. For distinct variables `x` and `y` compare `try (c; d) catch K => h` with `(try c catch K => h); d`. Give one counterexample in which `c` raises and `h` returns normally, and another in which `c` returns normally. Then give sufficient semantic hypotheses ensuring the two commands have the same outcome from every state, including divergence.

# Reading for the Seminar
%%%
tag := "ch32-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the result tags and one program witnessing each behavior, including absence of any result.

*Joint proof · 30 minutes.* Draw both derivations of the example with x and y initially zero. When the handler starts in the state at the raise, its final pair is (3,3); when it starts in the entry state, its final pair is (0,0). Locate the unique rule premise in which the input state differs.

*Proof review · 20 minutes.* Compare the store carried by a raised exception with the bare failure result of §32.1. Use the sequencing rule to explain why the suffix is skipped in each case.

*Facilitator’s hint.* Inspect the tag of the prefix before introducing a suffix premise. The failure propagation rule has no such premise.

# Solutions
%%%
tag := "ch32-s6"
number := false
%%%

*1.* The fail axiom gives the prefix failure immediately. One application of the sequence failure rule yields failure for the full command. The suffix has no premise.

*2.* The first program has a finite derivation ending with a raised $`J` in the initial state. A diverging protected computation supplies no finite outcome to the handler, so the handler cannot inspect any label.

*3.* Inspect the last rule for the sequence. Propagating an exception concludes with a raised tag. A normal conclusion must use the normal-prefix rule and therefore includes a derivation to an intermediate normal state.

*Further problem.* For the first example start with both variables zero and take `c = throw K`, `h = x := 1`, and `d = y := x`. On the left the handler updates only `x`. On the right the handler returns normally, so `d` also writes one to `y`. For a second example take `c = skip`, `d = throw K` and `h = skip`. On the left the exception from `d` is caught. On the right it escapes.

One sufficient pair of hypotheses is that `c` cannot raise `K` in any initial state and that `d` cannot raise `K` in any state returned normally by `c`. To prove sufficiency, classify the execution of `c`. Divergence gives divergence on both sides because the handler and sequence both wait for an outcome. A different raised label passes through unchanged on both sides. On normal return both commands run `d` at the same intermediate state. The second hypothesis excludes the only possible outcome on which the enclosing handler could affect the result of `d`. Hence normal return, an unmatched raise and divergence each agree.
