import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Function Domains and Fixed-Point Induction" =>
%%%
tag := "ch27"
file := "chapter-27"
%%%

[Chapter PDF](print/chapter-27.pdf) · [Session 26](seminar/index.html#week-26)

A recursive definition can give an answer at input zero before it gives one at input one. Each finite approximation is already a function on the entire input domain. To pass from approximants to the recursive function we must specify how to compare functions and which properties survive their limit.

*Sources.* Cambridge _Denotational Semantics_, lecture 3 and notes §§3.3, 4.1–4.3. Read the function-space construction and the hypotheses of Scott induction. Connect the chain of functions below with Chapter 9’s loop approximants. [Lecture 3.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Lecture3.pdf) [Notes.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

# Pointwise order
%%%
tag := "ch27-s1"
%%%

An increasing chain is a sequence $`x_{0} \sqsubseteq x_{1} \sqsubseteq \ldots` in a partial order. Its least upper bound is written $`\sup_{n}x_{n}`. Use domains with a least element $`\bot` and a least upper bound for each increasing countable chain. A continuous map here is monotone and preserves these chain bounds. For domains $`D,E`, order their continuous maps pointwise: $`f \sqsubseteq g` means that $`f(x) \sqsubseteq g(x)` for all $`x`. The bottom map has constant result $`\bot_{E}`.

For an increasing chain $`f_{n}`, put $`h(x) = \sup_{n}f_{n}(x)`. The upper-bound and leastness claims for $`h` follow at each input separately. It remains to check $`h` is continuous. For a chain $`x_{m}` the double family $`f_{n}(x_{m})` increases in both indices. Any entry is below the diagonal entry at index $`\max\left( {n,m} \right)`. Hence both iterated bounds equal the bound of the diagonal. Using continuity of each $`f_{n}` gives $`h\left( {\sup_{m}x_{m}} \right) = \sup_{m}h\left( x_{m} \right)`. This justifies taking the pointwise bound inside the space of continuous maps.

The diagonal argument can be proved without presupposing an operation that takes the supremum of an arbitrary two-dimensional array. Set `dₖ = fₖ(xₖ)`. If `k ≤ j` then `fₖ(xₖ) ⊑ fⱼ(xₖ) ⊑ fⱼ(xⱼ)`. The first inequality uses pointwise order of functions and the second uses monotonicity of the single function `fⱼ`. Thus the diagonal forms one of the chains for which a supremum is known to exist. Let its bound be `d`. For arbitrary `n,m` choose `k = max(n,m)`. The same two inequalities give `fₙ(xₘ) ⊑ dₖ ⊑ d`. Hence `d` bounds each row and each column, and therefore their iterated suprema. Conversely, either iterated supremum bounds every diagonal element, so each lies above `d`. Antisymmetry gives equality.

There is a separate reason for requiring continuity of the component functions. Order natural numbers by their usual order and adjoin a largest element infinity. The map to flat Booleans that is bottom at each finite number and true at infinity is monotone. Along the chain of all finite numbers its outputs remain bottom, while at their supremum it gives true. In the function-space argument, replacing evaluation at the input limit by the limit along a row is the step that this map would invalidate.

# A chain with strictly growing support
%%%
tag := "ch27-s2"
%%%

Take the flat natural domain, obtained by placing bottom below each natural and leaving distinct naturals incomparable. Define $`f_{n}` to return zero on natural inputs $`k < n` and bottom everywhere else, including at bottom. These strict maps are continuous because an increasing chain in a flat domain either stays bottom or stabilizes at its first ordinary value. At input two we see bottom at stages zero, one, two and zero as the *result* at stage three. At input bottom the result is always bottom. The pointwise limit returns zero on every ordinary input. There is no finite stage that supplies all these answers simultaneously.

One can generate the chain with a continuous operator $`F` on functions: its output is bottom at bottom, zero at input zero, and $`f(k)` at input $`k + 1`. It preserves chain bounds by inspecting each input separately. With $`f_{0}` constantly bottom we have $`f_{n + 1} = F\left( f_{n} \right)`. Its limit is the least fixed point by the argument of Chapter 9.

Changing a single line of the recurrence clarifies how semantic approximations depend on evaluation of an argument. Keep the zero and successor clauses but let the output at bottom be zero. A monotone function on a flat domain that sends bottom to the ordinary value zero must send *every* input to zero. Indeed bottom lies below every natural input, so monotonicity places zero below that input's output, and the only element above zero in the flat order is zero. At an early stage the proposed recurrence also sends some successor to bottom. These two demands conflict. Checking the bottom clause is part of checking that the construction even returns a function in the specified domain.

The original finite approximants can be calculated without a domain-theory library. The code uses `none` for missing information at ordinary inputs and `some 0` for an available answer. It evaluates only finite stages. The separate order-theoretic argument supplies the least upper bound of the whole chain.

```lean
def countdownStage : Nat → Nat → Option Nat
  | 0, _ => none
  | _ + 1, 0 => some 0
  | j + 1, k + 1 => countdownStage j k

example : countdownStage 2 2 = none ∧ countdownStage 3 2 = some 0 :=
  ⟨rfl, rfl⟩
```

# Scott induction
%%%
tag := "ch27-s3"
%%%

A predicate $`P` on a domain is *chain-closed* if whenever it holds of every element of an increasing chain, it also holds of the chain’s least upper bound. Suppose $`P(\bot)` and $`P(f)` implies $`P\left( {F(f)} \right)`, where $`F` is continuous. If $`P` is chain-closed, it holds at the least fixed point of $`F`. Indeed ordinary induction establishes $`P` at each iterate of bottom. Chain closure transfers this to their least upper bound, and continuity identifies that bound with the least fixed point.

For the operator in §27.2 take the property “every defined output is zero.” It holds at the bottom map. One unfolding either produces zero, copies a previous result, or returns bottom; the property is preserved. At a fixed input any nonbottom output of the chain limit must already occur at some finite stage, by flatness. Thus the property is chain-closed and holds of the recursive function.

The direction of the implication in the zero-output property permits a limit proof. Fix an input and suppose that the limit reports an ordinary answer there. In a flat codomain the chain of answers at that input must have reached that very answer. Choose such a stage, use its zero-output property, and conclude that the limit answer is zero. The chosen stage may depend on the input. This dependence is harmless because the conclusion is a separate implication for each input.

Now consider the stronger-looking assertion that some natural input is still unanswered. At stage `n` choose input `n` itself. This gives an existential witness at every stage of §27.2. Yet at the limit each fixed natural input has received zero. The witnesses move to larger and larger inputs, so none of them witnesses the proposed limit property. One can express the logical error as an exchange between “at every stage there exists an unanswered input” and “there exists an input unanswered at every stage.” The first statement has a simple proof and the second is false. The chain-closure premise of Scott induction is what requires us to examine this exchange before arguing about a recursive program.

# Exercises
%%%
tag := "ch27-s4"
number := false
%%%

1. Determine the least $`n` with $`f_{n}(4) = 0`. Show that the same $`n` need not work at another input.
2. The property “the set of inputs with defined output is finite” holds at every approximant in §27.2. Check the induction hypotheses individually.
3. Give a continuous map on a flat domain that does not send bottom to bottom. Which premise in the definition permits it?

*Further problem.* Fixed-point fusion. Let `F : D → D` and `G : E → E` be continuous and let `h : D → E` be continuous and strict, meaning it sends bottom to bottom. Assume `h ∘ F = G ∘ h`. Prove that `h(lfp F) = lfp G`. Exhibit continuous maps satisfying the commutation equation for which the conclusion fails if strictness is dropped.

# Reading for the Seminar
%%%
tag := "ch27-s5"
number := false
%%%

*Definitions · 10 minutes.* Draw three successive finite graphs and the pointwise column for one input.

*Joint proof · 30 minutes.* Prove the zero-output property by Scott induction, giving a separate justification for its chain closure.

*Proof review · 20 minutes.* Try the finite-support property and locate the precise invalid inference from finite stages to the limit.

*Facilitator’s hint.* For a universal claim about inputs, first fix one input. The stage at which a result appears may depend on it.

# Solutions
%%%
tag := "ch27-s6"
number := false
%%%

*1.* The least stage is five. For input five the least stage is six, so there is no uniform stage covering all naturals.

*2.* Bottom has empty support. One unfolding of a finite-support function adds input zero and shifts its ordinary support by one, preserving finiteness. The limit has infinite support. Thus the missing hypothesis is exactly chain closure.

*3.* The constant-zero map takes even bottom to zero and preserves increasing nonempty chain bounds. Mapping bottom to bottom is an additional property called strictness.

*Further problem.* Write `d₀` and `e₀` for the least elements of the two domains. For every natural stage `n` prove `h(Fⁿ(d₀)) = Gⁿ(e₀)`. At zero the claim is precisely strictness. For the successor stage apply the commutation hypothesis at `Fⁿ(d₀)` and substitute the inductive equality into `G`. By the least-fixed-point construction, `lfp F` is the supremum of its approximants from `d₀`. Continuity of `h` sends this supremum to the supremum of their images. The stage equation identifies that chain with the approximants of `G` from `e₀`. Its supremum is `lfp G`.

For a counterexample take both domains to be the two-element chain `⊥ < 1`. Let `F` and `G` be the identity, and `h` the constant function with value one. All three maps preserve increasing chain bounds, and every map commutes with identity. Both least fixed points are bottom. Their images in the proposed equality are respectively one and bottom. The induction fails already at stage zero.
