import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Evaluation Strategies" =>
%%%
tag := "ch14"
file := "chapter-14"
%%%

[Chapter PDF](print/chapter-14.pdf) · [Session 15](seminar/index.html#week-15)

A caller passes two pieces of code to an evaluator: a function and its argument. The function may return without ever inspecting the argument. If the argument runs forever, deciding when to evaluate it determines whether the whole application returns.

*Sources.* Reynolds, _Theories of Programming Languages_, §§10.3–10.4, pp. 201–207. Compare the normal-order and eager treatments of application. We compare their behavior at the outermost result of a closed pure term using two weak strategies, each stopping at a lambda. Pierce, _Types and Programming Languages_, §5.1 introduces related reduction strategies. [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html) [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Two one-step relations
%%%
tag := "ch14-s1"
%%%

Use the terms and capture-avoiding substitution of Chapter 13. A value in this chapter is an abstraction. A *redex* is an expression to which a reduction rule applies. A beta step replaces an application of an abstraction by its body with its parameter replaced by the argument. To specify a strategy we must also say which redex can be chosen and when the argument is eligible.

Call-by-name first evaluates the operator of an application. Once the operator is an abstraction, it substitutes the entire unevaluated argument. The only rules are these, with the subscript $`n` denoting one name step:

$$`\frac{f\to_{\mathrm n} f'}{f\, a\to_{\mathrm n} f'\, a}\quad\left( {\lambda x.b} \right)\, a\to_{\mathrm n} b\left\lbrack {a/x} \right\rbrack.`

Call-by-value evaluates the operator, then the operand. Its beta rule requires a value operand. Write $`v,w` for values. The subscript $`v` on an arrow denotes a value step:

$$`\frac{f\to_{\mathrm v} f'}{f\, a\to_{\mathrm v} f'\, a}\quad\frac{a\to_{\mathrm v} a'}{v\, a\to_{\mathrm v} v\, a'}`

$$`\left( {\lambda x.b} \right)\, w\to_{\mathrm v} b\left\lbrack {w/x} \right\rbrack.`

Neither relation descends beneath an abstraction. Thus observing convergence here means reaching an abstraction in finitely many steps. Full normalization may inspect its body as well. For each strategy at most one step is possible: at an application the outer form and the operator’s value status determine which rule can apply, and the recursive positions inherit uniqueness by induction.

One can predict a complete first step by marking the particular hole in which the next redex must lie. Write a hole as `□`. For name evaluation the permitted contexts are `□` and `E a`, recursively. For value evaluation they are `□`, `E a` and `v E`, where the operator in the last case must already be a value. Filling the hole with a reducible application gives the whole term. Each constructor surrounding the hole corresponds to one propagation rule in the earlier presentation.

For example, take `((λf. f) I) ((λw. w) I)`, with `I = λz. z`. Both strategies begin in the operator, even though the operand contains another beta redex. The left application reduces to `I`; the whole term is now `I ((λw. w) I)`. Name evaluation accepts it immediately as an outer redex. Value evaluation moves the hole to the operand, because the outer operator is a value and the operand has yet to become one. This gives a mechanical way to read a derivation backwards: identify the hole from the outside in, perform one beta step there, then rebuild the surrounding application nodes unchanged.

# An ignored argument
%%%
tag := "ch14-s2"
%%%

Let $`I = \lambda z.z`, $`D = \lambda u.\left( {u\, u} \right)`, and $`\Omega = D\, D`. The operand $`D` is a value. Substituting it for both occurrences of $`u` in the body yields $`D\, D` again. Consequently $`\Omega` takes a step back to itself under either strategy. Repetition gives an infinite sequence of steps, even though all the printed terms look identical.

Take $`M = \left( {\lambda x.I} \right)\,\Omega`, with $`x` fresh. Under call-by-name the outer beta rule gives $`I\left\lbrack {\Omega/x} \right\rbrack = I` in one step. Under call-by-value the operator is already a value but the operand is an application. Only the operand rule applies. Its premise steps $`\Omega` to itself, so its conclusion steps $`M` to itself. By uniqueness, every finite run still ends at $`M`, which is an application. Thus no finite run reaches a value. The arguments for convergence and divergence use the actual strategy rules in different ways.

The distinction can be measured at the level of functions as well as at individual programs. Consider the closed function `K = λx. λz. z`. Used on the ordinary argument `I`, both weak strategies immediately return `λz. z`. That agreement on value arguments does not settle their agreement on all closed arguments. The application context `K □` permits a computation in its hole. Filling it with the closed diverging term gives precisely the two observations just established: a function value under name evaluation and divergence under value evaluation.

Change the body to `x I` so that the function must inspect its argument in operator position. On the same diverging input, name evaluation first obtains `Ω I`. Its next step reduces the operator `Ω` to itself, and this repeats forever. Value evaluation again remains at the original application. Thus a difference in the number or position of initial steps need not give a difference in convergence. To show separation of the strategies one needs both sides of the original example: a finite path that actually reaches a value, and an argument excluding every such path for the other strategy.

For this single application we can quotient the computation down to two configurations. Name evaluation moves from the original application to its final value. Value evaluation leaves the application at precisely the same configuration. The induction in Lean establishes the claim about *all* finite value prefixes; the correspondence of the two displayed transitions with the actual beta and operand rules was derived above. At the final value, the option result `none` records the absence of a next step.

```lean
namespace StrategyPrefix
inductive Point where | app | result
  deriving DecidableEq

def byName : Point → Option Point
  | .app => some .result
  | .result => none

def byValue : Point → Option Point
  | .app => some .app
  | .result => none

def after (step : Point → Option Point) : Nat → Point → Option Point
  | 0, p => some p
  | n+1, p => (step p).bind (after step n)

example : after byName 1 .app = some .result := rfl
example (n : Nat) : after byValue n .app = some .app := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
end StrategyPrefix
```

# Repeated uses of a parameter
%%%
tag := "ch14-s3"
%%%

Set $`A = \left( {\lambda z.z} \right)\, I`. It steps to $`I` in one step under either strategy. Consider $`\left( {\lambda x.x\, x} \right)\, A`. Under call-by-value, first evaluate $`A` and perform the outer beta step to obtain $`I\, I`, which returns $`I`. Under call-by-name, the first step produces $`A\, A`. Evaluate its operator, obtaining $`I\, A`. This reduces to $`A`, which must be evaluated again. The result is $`I` in each case. The two copies distinguish call-by-name from *call-by-need*, which stores a result for reuse when a delayed argument is demanded again. We assume no sharing rule in the name semantics.

Duplication has a numerical cost even for arguments that return normally. Define `A₀ = I` and `Aₖ₊₁ = (λz.z) Aₖ`. With either weak strategy, evaluating `Aₖ` to its outer value costs exactly `k` beta steps. Under name evaluation each outer identity immediately exposes its argument. Under value evaluation each identity waits until its argument returns, then passes that value upward. Induction on `k` verifies both counts.

Now evaluate `(λx. x x) Aₖ`. With values, the first `k` steps reduce the argument to `I`. The outer substitution and the final `I I` together cost two further steps. With names, the first beta step produces `Aₖ Aₖ`. Reducing its operator costs `k`; applying the resulting identity costs one step and exposes the second copy. That copy costs another `k`, for a total of `2k + 2`. In this example the cost difference is exactly `k`. The count concerns beta steps in the stated semantics. An implementation of call-by-need would also perform operations to create, force and update a shared delayed computation, so the same numerical cost model cannot be carried over without additional rules.

# Exercises
%%%
tag := "ch14-s4"
number := false
%%%

1. Count the steps in §14.3 under each strategy. Identify the precise step at which the argument is duplicated.
2. For `λz. Ω`, classify weak evaluation under both strategies. Can repeated beta contraction inside its body terminate?
3. Replace the function in $`M` by $`I`. Does call-by-name now terminate?

*Further problem.* For fresh names `x,u`, put `L = (λx. λu. x) Ω`. Trace evaluation of both `L` and `L I` under each weak strategy. Which observations change when a caller supplies one more argument?

# Reading for the Seminar
%%%
tag := "ch14-s5"
number := false
%%%

*Definitions · 10 minutes.* Annotate each use of a congruence rule and each beta rule in the one-step definitions.

*Joint proof · 30 minutes.* Build the finite name evaluation of $`M`. Then prove, by induction on the number of value steps, that every finite value-strategy prefix ends at $`M`.

*Proof review · 20 minutes.* Trace the repeated-use example, distinguishing substitution of code from reuse of an already computed value.

*Facilitator’s hint.* When a term steps to itself, an infinite path exists. To exclude a second, terminating path use uniqueness of the selected step.

# Solutions
%%%
tag := "ch14-s6"
number := false
%%%

*1.* Value takes three steps: reduce $`A` inside the argument, perform the outer substitution, then reduce $`I\, I`. Name takes four: duplicate $`A` at the outer beta step, reduce the left $`A`, apply $`I`, then reduce the remaining $`A`.

*2.* An abstraction is already a weak value under both strategies. If contraction proceeds inside the body, the only redex there is $`\Omega`, whose contraction reproduces it. The term has no beta-normal form.

*3.* The first name step in $`I\,\Omega` yields $`\Omega`. Each subsequent step reproduces it, so this term diverges under name as well.

*Further problem.* Under call-by-name the operator of `L` is already an abstraction, so one beta step substitutes the closed term `Ω` and yields `λu. Ω`. This is a value under the weak rules. In `L I`, that same step occurs in operator position; the next step applies the resulting abstraction to `I` and leaves `Ω`. Every subsequent step returns `Ω` itself, so this second experiment never reaches a value. Under call-by-value, `L` already has a value operator but still requires a value operand. The only possible step evaluates `Ω` to itself and leaves `L` unchanged. In `L I`, the operator must step first, which carries that self-step to the enclosing application. Neither value run can reach an abstraction, by uniqueness of the selected step. Thus observing the returned function and observing the result of calling it are distinct experiments even though their programs share the entire expression `L`.
