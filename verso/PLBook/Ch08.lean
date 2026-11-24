import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "State Transformers and the Information Order" =>
%%%
tag := "ch07"
file := "chapter-07"
%%%

[Chapter PDF](print/chapter-07.pdf) · [Session 8](seminar/index.html#week-08)

An assignment determines a new integer state for every initial state. A command containing a loop can fail to return a state. Sequential composition must accept either possibility as the result of its first command. This distinction determines the type of a command meaning and the operation used to compose two meanings.

*Sources.* John C. Reynolds, _Theories of Programming Languages_, §§2.2–2.3. Read the denotation of sequencing and the ordering of approximations. We restrict attention to deterministic, error-free integer IMP with no observable intermediate output. The shared calculation derives sequencing in both possible cases for its first result. [Reynolds, chapter 2.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Lifted outcomes
%%%
tag := "ch07-s1"
%%%

Let $`\Sigma` be the set of integer states. Form the disjoint union $`\Sigma_{\bot}` of a fresh element $`\bot` and a copy of $`\Sigma`. We write a state $`t` also for its copy. In a completed command meaning, $`\bot` denotes divergence. In a partial approximation it records that no final state is available at this stage. The same mathematical element is used in both roles, so an approximation returning $`\bot` is insufficient evidence that the program diverges.

A command meaning is a total mathematical function $`f:\Sigma\rightarrow\Sigma_{\bot}`. It represents a partial state transformation, defined at $`s` exactly when $`f(s)` is a state. Define the *flat order* on outcomes by $`r \sqsubseteq q` if $`r = \bot` or $`r = q`. Distinct states are incomparable. Set $`f \sqsubseteq g` if $`f(s) \sqsubseteq g(s)` for every state $`s`. For example, a function specifying the final state only for inputs with $`x = 0` lies below one that agrees there and also specifies the results for $`x = 1`. Revising a previously specified final state would violate this ordering.

*Lemma 8.1.* An increasing sequence of outcomes either stays at bottom forever or reaches a state and stays there. Its least upper bound is respectively bottom or that state.

*Proof.* If the sequence reaches $`t \in \Sigma`, then every later outcome lies above $`t`. Flatness forces it to equal $`t`. All earlier elements lie below $`t`, and every upper bound must be above $`t`, so $`t` is the least upper bound. In the remaining case every element equals bottom, which itself bounds the sequence. $`\square`

*An increasing family without a final finite stage.* Fix a variable `x`. For each natural number `n` define a transformer `pₙ` that returns its input store when `|s(x)| < n` and gives bottom elsewhere. The absolute value is the ordinary absolute value on integers. At stage zero every input gives bottom. At stage one precisely the stores with `s(x) = 0` have a known result. Increasing the threshold preserves all these results and adds new ones, hence `pₙ ⊑ pₙ₊₁`.

For each *fixed* store `s` the outcome has stabilized by stage `|s(x)| + 1`. Its least upper bound is therefore `s`. Pointwise, the least upper bound of the transformers is the identity. No member of the sequence equals this identity on all stores. Given any proposed stage `n`, choose an input with `s(x) = n`. Its result is still bottom at that stage. Thus “every input has a sufficient stage” and “one stage suffices for every input” have different truth values. A denotation can specify outcomes everywhere even though every finite approximation leaves some input unspecified. The distinction will matter for loops that terminate on every input after an unbounded number of iterations.

# Interpreting command constructors
%%%
tag := "ch07-s2"
%%%

Write $`f_{c}` for the meaning assigned to command $`c`. The meaning of skip is the injection $`s\mapsto s`. For assignment use $`s\mapsto s\left\lbrack {x\mapsto\operatorname{eval}\left( {e,s} \right)} \right\rbrack`. A conditional chooses $`f_{c}(s)` or $`f_{d}(s)` according to the truth of its guard in $`s`. A *compositional* interpretation gives the meaning of a compound command by applying an operation to its immediate constituents’ meanings. Chapter 9 supplies the operation for a loop.

For $`g:\Sigma\rightarrow\Sigma_{\bot}`, its *strict extension* $`g^{\dagger}:\Sigma_{\bot}\rightarrow\Sigma_{\bot}` is defined by $`g^{\dagger}(\bot) = \bot` and $`g^{\dagger}(u) = g(u)` for an ordinary state $`u`. The adjective “strict” means that the new function sends bottom to bottom. Define the meaning of a sequence by

$$`f_{c\ \text{;}\ d}(s) = f_{d}^{\dagger}\left( f_{c}(s) \right).`

Ordinary application $`f_{d}(f_{c}(s))` would have a type mismatch: the inner result lives in the lifted set, and the outer input expects an ordinary state.

*Calculation.* Suppose the suffix assigns 7 to $`y`. If the prefix returns $`u`, then the sequence returns $`u\left\lbrack {y\mapsto 7} \right\rbrack`. If the prefix returns bottom, the whole sequence returns bottom. No input is supplied to the assignment in that case. If the prefix terminates and the suffix diverges on that particular result, strict extension returns the suffix’s bottom outcome as well.

*Composing the graphs.* Associate to a transformer `f` the set of pairs `graph(f) = {(s,u) | f(s) returns u}`. Let `h` execute `f` followed by `g`. For ordinary states `s,t`, expand the two cases of strict extension. If `f(s)` is bottom, the pair `(s,t)` is absent from `graph(h)` for every `t`. If `f(s)` returns `u`, the pair occurs just when `g(u)` returns `t`. Combining the cases gives a single criterion: some ordinary `u` satisfies both `(s,u) ∈ graph(f)` and `(u,t) ∈ graph(g)`.

This calculation also determines the set of inputs at which composition returns. Let `dom(f)` consist of the stores where `f` returns an ordinary result. The composite requires an input in `dom(f)` whose *image* belongs to `dom(g)`. For example, suppose the prefix always assigns zero to `x`, and the suffix returns its input only when `x = 0` and diverges otherwise. The sequence returns on every input, including those where running the suffix alone would diverge. Intersecting the two domains at the same input would therefore give the wrong answer. The intermediate store in the graph formula is essential even for a calculation concerned only with termination.

# Laws of sequencing
%%%
tag := "ch07-s3"
%%%

*Proposition 8.2.* Sequencing is associative on these meanings. For meanings $`f,g,h` and every initial state $`s`, composing $`f` then $`g` then $`h` gives the same result under either grouping.

*Proof.* If $`f(s) = \bot`, the first strict extension propagates bottom under both groupings. Otherwise write $`f(s) = u`. If $`g(u) = \bot`, both groupings return bottom again. If $`g(u) = v` is a state, both groupings return $`h(v)`, whether that is a state or bottom. The cases cover the disjoint lifted set. Equality at all $`s` proves equality of functions. $`\square`

*Proposition 8.3.* If $`f \sqsubseteq f'` and $`g \sqsubseteq g'`, the composite with $`f,g` lies below the composite with $`f',g'`.

*Proof.* Fix $`s`. A bottom result on the left is below any result on the right. A state result $`v` on the left requires a state $`u = f(s)` with $`g(u) = v`. The two function inequalities and flatness force $`f'(s) = u` and $`g'(u) = v`. Thus the right composite returns $`v` too. This property of preserving the order is called monotonicity. $`\square`

The strict extension can be calculated with Lean's type `Option α`, whose constructors are `none` and `some a`. Interpret `none` as the fresh bottom and `some a` as an ordinary outcome. The operation `p.bind f` inspects `p`. It returns `none` when `p` is `none` and computes `f a` when `p = some a`. In the theorem below the types of intermediate results may differ. Specializing all three types to stores gives the associativity calculation for commands.

```lean
example {α β γ : Type} (p : Option α)
    (f : α → Option β) (g : β → Option γ) :
    (p.bind f).bind g = p.bind (fun a => (f a).bind g) := by
  cases p <;> rfl
```

Why is one case split sufficient here when the mathematical proof also inspected the second result? In the ordinary case both sides reduce to the *same expression*, `(f a).bind g`. Its value may still depend on an unknown argument and an unknown function. Reflexivity suffices because equality holds before either is evaluated. The types also reveal the role of grouping. On the right the partially applied suffix is a function expecting an ordinary `a`. The outside bind supplies that argument precisely when the first computation returns one.

# Exercises
%%%
tag := "ch07-s4"
number := false
%%%

*8.1.* An analyst proposes ordering normal final states by their integer value at $`x`. Show why this would allow an approximation to change a known result.

*8.2.* Prove that composing with skip before or after any meaning preserves it, including on a diverging input.

*8.3.* On the set of all transformer functions, find the least upper bound of an increasing sequence $`f_{0},f_{1},\ldots` and justify that it is least.

*Further problem.* Let `T` be the set of all transformers from stores to lifted stores ordered pointwise. Given two transformers `f,g`, characterize exactly when they have a common upper bound. In that case construct their least upper bound. Compare the criterion with Lemma 8.1 for increasing sequences.

# Reading for the Seminar
%%%
tag := "ch07-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the input and output types of each of two transformers. Introduce the state injection and the fresh outcome.

*Joint proof · 30 minutes.* Let one group compute the suffix assignment after a terminating prefix and another after a diverging prefix. Use the two answers to define strict extension. Prove associativity with the same case split.

*Proof review · 20 minutes.* Replace the prefix by a more defined approximation. Use Proposition 8.3 to decide whether an already observed state result can change.

*Facilitator’s hint.* Fix one initial state, and split on the value of the inner function before attempting to apply the outer function.

# Solutions
%%%
tag := "ch07-s6"
number := false
%%%

*8.1.* A transformer already returning a state with $`x = 2` could be “improved” to one returning $`x = 3`. They disagree on a directly observable final value. Flatness treats both normal states as maximal.

*8.2.* Skip first returns $`s`, so strict extension of $`f` returns $`f(s)`. Skip last preserves an ordinary result $`u` and propagates a bottom result, yielding $`f(s)` in both cases.

*8.3.* Define $`g(s)` to be the least upper bound of the outcomes $`f_{n}(s)` given by Lemma 8.1. Every $`f_{n}` lies below $`g` pointwise. If $`h` bounds the whole sequence, $`h(s)` bounds those outcomes at each $`s`, so $`g(s) \sqsubseteq h(s)`. Hence $`g \sqsubseteq h`.

*Further problem.* Agreement is required wherever both transformers return ordinary results. If `f(s)` and `g(s)` were distinct ordinary stores, any upper bound at that input would have to lie above both. In a flat order an ordinary store can only be bounded above by itself. Distinct stores therefore rule out a common upper bound.

Conversely, assume agreement on that overlap. Define `h(s)` to be the result of `f(s)` when ordinary, and otherwise the result of `g(s)`. At an input where neither is defined it gives bottom. Checking these cases shows that both transformers lie below `h`. For leastness consider any common upper bound `k`. Where `h(s)` is ordinary, at least one of the two transformers already has that result and forces `k(s)` to equal it. Where `h(s)` is bottom the required inequality holds automatically. Thus `h ⊑ k`. In an increasing sequence agreement on overlaps is automatic. Arbitrary pairs of transformers need not have this compatibility.
