import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Continuations and the CPS Transformation" =>
%%%
tag := "ch34"
file := "chapter-34"
%%%

[Chapter PDF](print/chapter-34.pdf) · [Session 34](seminar/index.html#week-34)

During evaluation of `(x + 2) + y`, obtaining the value of the inner sum leaves an outer addition to perform. A continuation represents the work still waiting for that value. Making this parameter explicit yields a program in continuation-passing style (CPS).

*Sources.* Xavier Leroy, _Control Structures for Programming Languages_, chapter 6, on continuations and the CPS transformation. Follow the continuation passed to a non-tail subexpression. We derive a translation for pure arithmetic so that its correctness can be proved directly. Compare Reynolds, _Theories of Programming Languages_, §§12.1–12.3 for the functional-language development. [Leroy, chapter 6.](https://xavierleroy.org/control-structures/book/main009.html) [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Answers and continuations
%%%
tag := "ch34-s1"
%%%

Fix a state $`s` of Chapter 1 and an answer set $`R`. The ordinary evaluator assigns an integer to an expression. A continuation has type $`{\mathbb{Z}}\rightarrow R`; given the intermediate integer, it produces an answer. To recover an ordinary integer result, choose $`R = {\mathbb{Z}}` and the identity continuation. A continuation may instead test whether the result is zero, in which case $`R` can be the Boolean set.

Write $`C\left( {e,s,k} \right)` for the CPS computation with continuation $`k`. Specify left-to-right evaluation by the following translation clauses. In the pseudocode, functions introduced by the translation have fresh parameter names.

```
C(lit n, s, k)   = k(n)
C(var x, s, k)   = k(s(x))
C(add a b, s, k) = C(a, s, λu. C(b, s, λv. k(u + v)))
```

When $`a` returns its integer $`u`, the outer continuation still has to evaluate $`b`. When $`b` returns $`v`, that work has become applying $`k` to $`u + v`. Each call is in *tail position*, meaning its result is the entire answer of the enclosing function call. The pending work is represented by functions capturing $`b,s,k` and then $`u,k`.

The generated continuations have only two new shapes at an addition. This makes it possible to represent them as data, a transformation called *defunctionalization*. Fix the state for the entire evaluation. A stack of frames records what should happen to the next integer: `Right(b)` means that the left child has just returned and the right child `b` must be evaluated, while `Combine(u)` means that the next integer must be added to the saved left value `u`. Keep the caller's final continuation `k : ℤ → R` separately. Every frame consumes an integer as an intermediate value. Only calling `k` produces an answer in `R`.

To evaluate `add a b`, push `Right(b)` and begin evaluating `a`. When a value `u` meets `Right(b)`, replace that frame by `Combine(u)` and begin evaluating `b`. When a value `v` meets `Combine(u)`, pop the frame and pass `u + v` to the remaining stack. A value presented to an empty stack goes to `k`. These cases follow by substituting a value into the two anonymous functions in the translation. The first function needs the expression `b` later, hence the expression field in its frame. The second needs the integer `u` later, hence the integer field in its frame. Both access the earlier pending work through the rest of the stack.

# A trace
%%%
tag := "ch34-s2"
%%%

Take $`s(x) = 3`, $`s(y) = 4` and the final continuation $`k(r) = 2r`. The outer sum installs the continuation $`h(u) = C\left( {y,s,\lambda v.k\left( {u + v} \right)} \right)` for the inner sum. The variable lookup returns 3 to the continuation that next evaluates literal 2. After that literal the inner addition sends 5 to $`h`. Now $`y` returns 4 and the last continuation computes $`k\left( {5 + 4} \right) = 18`. The sequence of computed integers is 3, 2, 5, 4, 9; the final answer is 18. Changing $`k` changes what the caller does with 9 while leaving the expression’s own value intact.

Parentheses change the pending work even when they leave the answer fixed. With the same state and caller, evaluate `x + (2 + y)`. Use a stack written with its next frame on the left. Looking up `x` yields three with only `Right(2 + y)` on the stack. Resuming at this frame replaces it with `Combine(3)`. Evaluating the inner sum pushes `Right(y)` above that frame. At the literal two the stack is therefore `[Right(y), Combine(3)]`. Its top frame schedules the lookup of `y` and leaves `[Combine(2), Combine(3)]` waiting. The lookup returns four. The first combination produces six, the next produces nine, and the caller doubles nine.

Compare the point just after the lookup of `y` in the original parenthesization, `(x + 2) + y`. There the stack contains just `Combine(5)`: the left sum has already been computed. Both expressions look up `x` before `y`, but only the first parenthesization in the preceding paragraph holds two unfinished additions at the lookup of `y`. Their common answer uses associativity of integer addition. The derivation of the sequence of frames uses only the syntax tree and the left-to-right CPS clauses, so no arithmetic law could by itself determine that sequence.

# Correctness
%%%
tag := "ch34-s3"
%%%

*Theorem 34.1.* For every expression $`e`, state $`s` and continuation $`k:{\mathbb{Z}}\rightarrow R`, $`C\left( {e,s,k} \right) = k\left( {\operatorname{eval}\left( {e,s} \right)} \right)`. Prove this by structural induction on $`e`, quantifying the induction assertion over all continuations. At a literal and variable the two sides coincide by their defining clauses. At $`\text{add}\left( {a,b} \right)`, abbreviating constructor names in the argument, apply the hypothesis for $`a` with continuation $`u\mapsto C\left( {b,s,\lambda v.k\left( {u + v} \right)} \right)`. The result is $`C\left( {b,s,\lambda v.k\left( {\operatorname{eval}\left( {a,s} \right) + v} \right)} \right)`. Now apply the hypothesis for $`b` with this new continuation. It gives $`k\left( {\operatorname{eval}\left( {a,s} \right) + \operatorname{eval}\left( {b,s} \right)} \right)`, which equals the required result by direct evaluation of the sum.

A hypothesis proved only for the identity continuation cannot be applied at the first recursive call. The theorem’s quantifier is forced by the translation itself. This proof uses pure, total arithmetic, with both subexpressions reading the same state. With effects one would also specify the state passed to the next continuation.

The following definition uses natural numbers as variable names. Fixing the state `s` outside the recursion records that every occurrence of a variable reads the same state. The answer type `R` remains arbitrary. At a binary node, the second recursive call occurs in the continuation supplied to the first one, exactly as in the mathematical translation.

```lean
inductive CpsArithmetic where
  | lit (n : Int)
  | var (x : Nat)
  | add (a b : CpsArithmetic)

def CpsArithmetic.value (s : Nat → Int) : CpsArithmetic → Int
  | .lit n => n
  | .var x => s x
  | .add a b => a.value s + b.value s

def CpsArithmetic.cps {R : Type} (s : Nat → Int) :
    CpsArithmetic → (Int → R) → R
  | .lit n, k => k n
  | .var x, k => k (s x)
  | .add a b, k => a.cps s (fun u => b.cps s (fun v => k (u + v)))

example {R : Type} (s : Nat → Int) (e : CpsArithmetic) :
    ∀ k : Int → R, e.cps s k = k (e.value s) := by
  induction e with
  | lit n => intro k; rfl
  | var x => intro k; rfl
  | add a b iha ihb =>
    intro k
    simp only [CpsArithmetic.cps, CpsArithmetic.value, iha, ihb]
```

The position of `∀ k` matters when reading the proof. Induction takes place before the chosen continuation is introduced. Hence `iha` can rewrite the whole call on `a`, including the newly constructed function that appears as its argument. The resulting call on `b` is then an instance of `ihb`. Specializing the theorem to the identity function recovers the source integer in every state.

The continuation describes what the rest of the program will observe. In this pure fragment the CPS equation quantifies over all result continuations; instantiating it with the identity recovers the ordinary final value.

# Exercises
%%%
tag := "ch34-s4"
number := false
%%%

1. Compute the answer in §34.2 when the continuation tests whether its argument is odd. State its answer type.
2. Add unary negation to the source grammar. Give its CPS clause and prove the new induction case.
3. Reverse the two recursive evaluations in the addition clause while keeping the operands of addition in source order. Does the theorem still hold for pure arithmetic?

*Further problem.* State-passing CPS. Add `postinc x` to arithmetic expressions: it returns the previous value of `x` and increments that variable. Give a left-to-right direct evaluator and CPS clauses for this operation and addition. State and prove the strengthened correctness equation. Using `x + postinc x`, show by calculation why the theorem need not hold if just the CPS translation switches evaluation order.

# Reading for the Seminar
%%%
tag := "ch34-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the type of the final continuation and of the one awaiting the right operand.

*Joint proof · 30 minutes.* Build the two continuations for addition from the type of the desired answer. Prove the addition equation with the induction hypotheses instantiated explicitly.

*Proof review · 20 minutes.* Trace a continuation returning a Boolean, then try proving correctness with only identity as hypothesis.

*Facilitator’s hint.* The induction hypothesis for the left child must accept a function that still evaluates the right child. Write that function out before applying induction.

# Solutions
%%%
tag := "ch34-s6"
number := false
%%%

*1.* The intermediate value is 9, so the answer is true in the Boolean set.

*2.* Use $`C\left( {a,s,\lambda u.k\left( {- u} \right)} \right)`. The induction hypothesis gives $`k\left( {- \operatorname{eval}\left( {a,s} \right)} \right)`, the desired equation.

*3.* Evaluate $`b` first and bind its result $`v`, then evaluate $`a` and call $`k\left( {u + v} \right)`. Applying the two induction hypotheses in reversed order yields the same equation. If the operands emitted events, their traces could distinguish these translations.

*Further problem.* Let the direct evaluator `E(e,s)` return a pair `(n,t)`. Literals and variables return their usual integers with state `s`. For `postinc x` return `(s(x), s[x ↦ s(x)+1])`. For addition evaluate the left child at `s`, obtaining `(u,t)`, then the right child at `t`, obtaining `(v,w)`. Return `(u+v,w)`.

Use a continuation taking both an integer and a state. For `postinc x` call it on the direct evaluator's pair. For addition use `C(a,s,λu t. C(b,t,λv w. k(u+v,w)))`. Prove for all states and continuations that whenever `E(e,s)=(n,t)`, the CPS result is `k(n,t)`. All leaf cases are defining equations. At addition apply the hypothesis for `a` with the displayed first continuation. Its intermediate state is exactly the initial state required by the hypothesis for `b` with the inner continuation. That second application yields the required answer at the final state.

If `x` initially holds three, left-to-right evaluation reads three, then returns three while storing four: the sum is six. Evaluating the increment first instead reads four in the other operand, producing seven with the same final state. The continuation returning just the integer already distinguishes the translations.
