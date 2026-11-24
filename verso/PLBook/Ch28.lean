import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Recursion and Evaluation in PCF" =>
%%%
tag := "ch28"
file := "chapter-28"
%%%

[Chapter PDF](print/chapter-28.pdf) · [Session 27](seminar/index.html#week-27)

A recursive function returning zero after counting down may already have a meaning at input zero while its meaning at input one is still bottom. A finite evaluation derivation counts how often the recursive definition is used. A finite semantic approximation bounds how many such unfoldings are available.

*Sources.* Cambridge _Denotational Semantics_, lectures 4–5 and notes §§5.1–5.2 and chapter 6. Compare the application and fix rules in Figure 3 with the denotational clause for fix. We write ordinary decimal numerals for unary PCF numerals. [Lectures.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/materials.html) [Notes and rules.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

# Syntax and evaluation
%%%
tag := "ch28-s1"
%%%

PCF has the ground types Nat and Bool, function types, typed abstractions, application and a fixed-point construct. It includes zero, successor, predecessor, a zero test, Boolean constants and a conditional. If $`H:A\rightarrow A`, then $`\text{fix}(H):A`. Closed values are numerals, Booleans and function abstractions at their respective types. Write $`t \Downarrow v` for a finite evaluation derivation. The name strategy evaluates an operator to a lambda and evaluates its body after replacing the parameter by the *unevaluated* argument. A conditional evaluates its guard and only the selected branch. Successor, predecessor and the zero test inspect a numeric operand. In the notes the predecessor rule applies to a positive numeral; our program uses it only there.

For fix, from $`H\,\left( {\text{fix}(H)} \right) \Downarrow v` conclude $`\text{fix}(H) \Downarrow v`. This rule may be used multiple times in a finite tree, but each premise must itself have a finite derivation. The definition does not permit a circular proof.

At a function type a canonical value is a lambda. Obtaining this value and evaluating its body are two separate observations. For example, let `L` be the closed abstraction with an unused natural parameter and constant body two. To evaluate `L (fix (λx:Nat. x))` in the rules of this chapter, derive that the operator evaluates to `L`, then substitute the entire operand in its body. There is no occurrence of the parameter in two, so the body premise is simply the value derivation for two. The application therefore terminates. A rule that first required a numeral for the operand would introduce an extra premise that cannot be discharged.

A related distinction applies under the lambda. The closed abstraction `λu:Nat. fix (λx:Nat. x)` evaluates to itself as a function value. Once applied to zero it exposes the fixed point in the body and admits no numeral result. Consequently a finite derivation to a function does not by itself answer a question about a particular application. This is the operational reason Chapter 29 will specify the behavior of a function by relating its applications at related inputs. A requirement that it merely return a lambda would discard the information needed about the body.

*Recursion and termination.* In Chapter 18 the pure simply typed calculus admitted a normalization theorem. Here `fix (λx:Nat. x)` has type Nat. Under PCF’s evaluation rule for fix, a derivation of a numeral for this term would require a strictly smaller derivation for the same term after unfolding and evaluating the identity application. No finite derivation exists. The semantic functional is the identity, whose iterates from bottom are all bottom. Type preservation, normalization and adequacy are thus three separate claims.

# An operational calculation
%%%
tag := "ch28-s2"
%%%

Write $`G` for the following closed term and $`K` for its fixed point. The type of $`G` is $`\left( {N\rightarrow N} \right)\rightarrow\left( {N\rightarrow N} \right)`, where $`N` abbreviates Nat.

```
λf:Nat→Nat. λx:Nat.
  if zero?(x) then 0 else f (pred x)
```

Unfolding $`K` once and evaluating $`G\, K` yields the lambda with the same body but $`K` in place of $`f`. Apply that lambda to 1. The test of 1 gives false, so we must evaluate `K (pred 1)`. Unfold $`K` again to produce the same lambda. After substitution its test is `zero?(pred 1)`. The premise $`\mathrm{pred}\,1\Downarrow 0` yields true for the guard, and the selected zero literal evaluates to zero. The conditional, application and fix rules justify both uses of the function abstraction as indicated, giving $`K\, 1 \Downarrow 0`. Counting only the evaluations of $`K` to a function, there are two. Call-by-name delays the computation of the second argument until the next guard inspects it.

To reconstruct the finite proof, give the abstraction returned by `K` the name `B`. A proof of $`K\Downarrow B` has last rule fix. Its premise evaluates `G K`, first obtaining `G` itself as a lambda, then obtaining the body with `K` substituted, which is `B`. This small tree may be used in two places in the larger calculation. It supplies the operator premise of the outer application, and a second copy supplies the operator premise of the recursive application. Neither use presupposes that `K 1` already terminates. The proof of $`K\Downarrow B` stops at an abstraction in each case.

In the outer body substitute the syntax `1` for `x`. The branch predicate evaluates to false, so the outstanding goal is the evaluation of `K (pred 1)`. In the inner body substitute the syntax `pred 1`. Its test evaluates to true and the numeral zero discharges the branch goal. Although the false branch of this inner body still contains a further application of `K`, it contributes no premise to the conditional rule. Writing both branches as required premises would make the proof follow code that the chosen PCF semantics never executes.

# A semantic calculation
%%%
tag := "ch28-s3"
%%%

Interpret Nat by the flat natural domain and arrows by the continuous function spaces of Chapter 27. The semantic functional $`F` induced by $`G` returns the following map from an argument function $`g`: at bottom its result is bottom, at zero it is zero, and at $`k + 1` it is $`g(k)`. These clauses follow because the guard is strict and the conditional chooses a single branch. The meaning of $`K` is the least fixed point of $`F`.

Start with the bottom function $`g_{0}` and set $`g_{j + 1} = F\left( g_{j} \right)`. At input one, $`g_{0}(1) = \bot`, $`g_{1}(1) = g_{0}(0) = \bot` and $`g_{2}(1) = g_{1}(0) = 0`. The first numeral thus occurs at stage two, just as two unfolds were needed in §28.2. In general induction on $`j` gives $`g_{j}(k) = 0` for $`k < j` and bottom for $`k \geq j`. Each stage remains bottom at bottom. On every ordinary input the least upper bound is zero.

A ground recursion with no base case is $`\Omega_{N} = \text{fix}\left( {\lambda x:N.x} \right)`. Its functional is the identity. Every iterate of bottom equals bottom. Operationally a proposed finite derivation for $`\Omega_{N}` would require evaluation of the identity applied to $`\Omega_{N}`, whose body premise is a strictly smaller derivation of the original judgment. A finite tree cannot contain such an infinite descent.

Finite unfoldings can give a different result at the same *stage* while having the same ordinary results at the limit. Replace the body of `G` by a function which tests its argument and returns zero in both branches. This function still demands a value for the guard before returning. Its semantic functional ignores the proposed recursive argument altogether. One iteration of that functional therefore already gives zero at every ordinary input and bottom at bottom. The original functional gives its first zero at input `k` only at iteration `k + 1`. The limiting functions agree pointwise despite these different chains of approximants.

It is also possible to change the value at bottom while keeping all the ordinary answers. Replace the complete conditional, including its guard, by the literal zero. Now the resulting function ignores its natural argument. Applied to a divergent argument it returns zero immediately in call-by-name PCF. Evaluating the original or the two-identical-branches version on that argument demands a Boolean guard, which never arrives. The example explains why the semantics includes a bottom input even when its function is used chiefly to compute answers for ordinary natural numbers. Equivalence on every numeral alone would miss a distinction a closed PCF argument can observe.

The stage bound can be checked for every numeral at once. This finite evaluator computes the semantic approximants at ordinary inputs. A separate equation would give bottom as the result at a bottom input at every stage.

```lean
def pcfCountApprox : Nat → Nat → Option Nat
  | 0, _ => none
  | _ + 1, 0 => some 0
  | j + 1, k + 1 => pcfCountApprox j k

example (j k : Nat) :
    pcfCountApprox j k = some 0 ↔ k < j := by
  induction j generalizing k with
  | zero => simp [pcfCountApprox]
  | succ j ih =>
    cases k with
    | zero => simp [pcfCountApprox]
    | succ k => simpa [pcfCountApprox] using ih k
```

# Exercises
%%%
tag := "ch28-s4"
number := false
%%%

1. Compute the first stage giving a numeral at input three and trace the sequence of arguments inspected by the guards.
2. Evaluate $`\left( {\lambda x:N.0} \right)\,\Omega_{N}` under the course’s strategy. Predict what a value strategy would do.
3. Compare the denotation of $`K` with the constant-zero function on the entire flat domain. Give a PCF argument showing the operational distinction.

*Further problem.* A recursive parity test. In call-by-name PCF define `even : Nat → Bool` using one fixed point, a zero test, predecessor, and conditionals. Let stage zero be the everywhere-bottom function. Prove by induction on the stage number `j` that stage `j` returns the correct parity on precisely the natural inputs less than `j`. Relate this calculation to a finite evaluation derivation at any given numeral without appealing to the adequacy theorem of the next chapter.

# Reading for the Seminar
%%%
tag := "ch28-s5"
number := false
%%%

*Definitions · 10 minutes.* Give the types of $`G` and $`K`, and derive the function value returned by unfolding $`K`.

*Joint proof · 30 minutes.* Build the evaluation of $`K\, 1` from its inner guard outward. On a second board compute $`g_{0},g_{1},g_{2}` at zero and one.

*Proof review · 20 minutes.* Test the two proposed constant-zero behaviors at a diverging argument. Connect the result to strictness of the guard.

*Facilitator’s hint.* Count unfoldings of the recursive function separately from evaluation of arithmetic operations. The base input still needs one unfolding.

# Solutions
%%%
tag := "ch28-s6"
number := false
%%%

*1.* The first stage is four. The guards inspect values three, two, one and zero; after each positive guard the recursive call receives a predecessor expression.

*2.* Name substitution puts the unused operand into no occurrence, leaving zero. A value strategy would first require the diverging operand to yield a value.

*3.* At bottom $`K` denotes bottom, while the constant-zero map returns zero. Applying the two programs to $`\Omega_{N}` distinguishes them: the first demands the argument in its zero test, and the second ignores it.

*Further problem.* Define Boolean negation by `neg b = if b then false else true`. Take the fixed point of `λf. λx. if zero?(x) then true else neg (f (pred x))`. Its stage-zero approximation returns bottom everywhere. At each successor stage input zero returns true. On input `k + 1`, the new approximation negates the preceding stage's answer at `k`. Negation is strict because its conditional evaluates the guard. Thus the answer is ordinary precisely when `k < j` at the preceding stage, equivalently when `k + 1 < j + 1`. For those inputs, negation changes the parity of `k` to the parity of its successor. At a bottom input the initial zero test remains bottom at every stage.

For the operational claim, strengthen the induction statement: every closed argument evaluating to the numeral `k` yields its parity when supplied to `even`. At zero, unfold the fixed point, apply its abstraction and choose the true branch. At a successor, the predecessor of the current argument evaluates to the previous numeral. The induction hypothesis supplies the recursive guard's finite derivation. Negation and the outer conditional then complete the derivation at the successor.
