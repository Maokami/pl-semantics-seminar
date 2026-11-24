import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Products, Exponentials and Typed Terms" =>
%%%
tag := "ch26"
file := "chapter-26"
%%%

[Chapter PDF](print/chapter-26.pdf) · [Session 20](seminar/index.html#week-20)

In a typing derivation for $`f\, a`, both $`f` and $`a` may depend on the same variables. Pairing their meanings keeps that shared input intact. Evaluation can then consume the resulting function–argument pair. These two operations provide the interpretation of application.

*Sources.* The definitions of pairing, evaluation and currying are given below. For a fuller treatment see Roy Crole, _Categories for Types_, chapter 2 on products and exponentials and chapter 4 on functional type theory. Follow the domains of the arrows in the exponential universal property. The term syntax is the simply typed calculus of Chapter 18. [Crole, publisher’s edition.](https://www.cambridge.org/core/books/categories-for-types/258841251C62FED1DACD20884E59E61C)

# Contexts and products
%%%
tag := "ch26-s1"
%%%

A category has objects, composable arrows and identity arrows. Composition is associative and has those identities as units. Write $`g \circ f` for applying $`f` first. A terminal object $`1` receives exactly one arrow from each object. A binary product $`A \times B` has projections $`\pi_{1},\pi_{2}` to its two factors. For arrows $`u:G\rightarrow A` and $`v:G\rightarrow B` there is a unique pairing $`\left\langle {u,v} \right\rangle:G\rightarrow A \times B` whose projections are $`u` and $`v`.

Assign an object to each base type. Interpret the empty context by $`1`. Extending a context with a variable of type $`A` changes its object from $`G` to $`G \times A`. A judgment in that context with result type $`B` denotes an arrow from the context object to the object for $`B`. The new variable denotes the second projection; earlier variables are recovered through the first. Weakening an existing meaning $`u:G\rightarrow B` gives $`u \circ \pi_{1}:G \times A\rightarrow B`.

Take a context with two declarations, `x:A, y:B`. With the product convention above, its object is `(1 × A) × B`. A point in the category of sets has the form `((⋆,a),b)`. The meaning of `y` is the outer second projection. To recover `x`, use the outer first projection to obtain `(⋆,a)` and then the inner second projection to obtain `a`. Both variables therefore have arrows with the *same* domain, even though they were declared at different steps of context construction. A derivation can pair these two arrows to exchange the order in which it presents their values.

Suppose a substitution into this context supplies a term of type A and a term of type B, both in some context with object `D`. Call their meanings `u : D → A` and `v : D → B`. The assembled substitution is the arrow `⟨⟨!,u⟩,v⟩`, where `! : D → 1` is the unique arrow to the terminal object. Composing with either variable recovers its assigned meaning by the projection equations. This construction makes simultaneous substitution meaningful without choosing any order for evaluating the two assigned terms. The categorical description here concerns the pure typed language.

# Exponentials and application
%%%
tag := "ch26-s2"
%%%

An exponential $`B^{A}` has an evaluation arrow $`\mathrm{ev}:B^{A} \times A\rightarrow B`. For every $`h:G \times A\rightarrow B` there is a unique arrow $`\Lambda(h):G\rightarrow B^{A}` satisfying

$$`\mathrm{ev} \circ \left\langle {\Lambda(h) \circ \pi_{1},\pi_{2}} \right\rangle = h.`

The arrow $`\Lambda(h)` is the curry of $`h`; in sets, $`\mathrm{ev}(f,a)=f(a)`. Its inverse sends $`k:G\rightarrow B^{A}` to the map on $`G \times A` that pairs $`k \circ \pi_{1}` with $`\pi_{2}` and evaluates. A category with a terminal object, binary products and all these exponentials is *cartesian closed*.

Interpret the type $`A\rightarrow B` by $`B^{A}`. For a body with meaning $`h:G \times A\rightarrow B`, interpret its abstraction by $`\Lambda(h)`. For an operator meaning $`f:G\rightarrow B^{A}` and argument meaning $`a:G\rightarrow A`, the application meaning is

$$`G\overset{\langle{f,a}\rangle}{\rightarrow}B^{A} \times A\overset{\mathrm{ev}}{\rightarrow}B.`

For example, in the category of sets a point $`g` is a simultaneous assignment of values to the context. Pairing produces $`\left( {f(g),a(g)} \right)` and evaluation returns $`f(g)\left( {a(g)} \right)`. The input assignment is used twice by the pairing.

In sets, choose `A` to contain exactly two Booleans and `B` to contain the two numbers zero and one. There are four functions from `A` to `B`, because the two Boolean inputs each require a choice of one output. Take a context that stores one such function `f` and one Boolean `x`. The meaning of the term `f x` must inspect both components. For the assignment consisting of the function that sends true to one and false to zero and the argument false, it gives zero. Keeping the function component fixed and changing only the argument to true gives one. Keeping true fixed and changing the function to the constant-zero function changes the answer back to zero.

This dependence on two components yields a useful uniqueness check on the interpretation. Pairing the two variable projections gives the identity on their product, up to the harmless initial terminal factor in context notation. Indeed both composites with the projections match those of the identity, so the uniqueness clause for products forces equality. In this particular context the application term therefore denotes the evaluation arrow itself under that identification. Applying an arbitrary function-producing term to an arbitrary argument-producing term is the same construction after changing the input assignment by the arrow that pairs their meanings.

# The beta equation
%%%
tag := "ch26-s3"
%%%

Apply an abstraction with body $`h` to an argument $`a` in the original context. Its meaning is $`\mathrm{ev} \circ \left\langle {\Lambda(h),a} \right\rangle`. The semantic substitution of $`a` for the new variable has meaning $`h \circ \left\langle {\text{id}_{G},a} \right\rangle`. Both arrows have source $`G` and target $`B`. To prove equality, take the exponential equation of §20.2 and precompose both sides with $`s = \left\langle {\text{id}_{G},a} \right\rangle:G\rightarrow G \times A`. Pairing commutes with precomposition by uniqueness of the arrow with its specified projections. The product laws give $`\pi_{1} \circ s = \text{id}_{G}` and $`\pi_{2} \circ s = a`. Thus the left side becomes $`\mathrm{ev} \circ \left\langle {\Lambda(h),a} \right\rangle` and the right side becomes $`h \circ s`, as claimed. For a syntactic body the general substitution law identifies this latter composite with the interpretation of the substituted term; it follows by induction on typing.

The same calculation works when an occurrence of a variable is duplicated in the body. Let `G` be the set of integers, let the parameter and result types both denote the integers, and choose the body `(g,x) ↦ x + x + g`. Apply its abstraction to the argument `g ↦ g + 1`. At `g = 3`, forming the extended assignment yields `(3,4)`, and passing that assignment to the body gives eleven. Evaluating the function associated with three and applying it to four gives the same result. Both occurrences of the local variable read the same component of the extended assignment. An occurrence of the old variable still reads three.

The equation can be checked for arbitrary sets and arbitrary assignments without simplifying this arithmetic. The pair on the right below represents the simultaneous retention of the old context and the addition of the argument value. Unfolding the lambda on the left produces the right side by the computation rule for functions in Lean. This verifies the equation in the set-like interpretation by types and functions. The proof above using universal properties supplies the result for other cartesian closed categories.

```lean
example {G A B : Type} (h : G × A → B) (a : G → A) (g : G) :
    (fun x ↦ h (g, x)) (a g) = h ((fun r ↦ (r, a r)) g) := rfl
```

# Exercises
%%%
tag := "ch26-s4"
number := false
%%%

1. Interpret the identity abstraction $`\lambda x:A.x` in the empty context. Give the body arrow before currying.
2. In sets take $`G = A = B = {\mathbb{Z}}`, $`h\left( {g,x} \right) = g + x`, and $`a(g) = 2g`. Compute the meaning of the beta equation at $`g = 3`.
3. Explain why $`f \circ a` is in general ill typed for the arrows used in §20.2.

*Further problem.* Substitution under an abstraction. Let `h : G × A → B` interpret a body and let `u : D → G` change its surrounding assignment. Prove `curry(h) ∘ u = curry(h ∘ (u × id_A))` without using elements of a set. Construct `u × id_A` explicitly from the product projections. Track each arrow's source and target before invoking exponential uniqueness.

# Reading for the Seminar
%%%
tag := "ch26-s5"
number := false
%%%

*Definitions · 10 minutes.* Recall the beta step in Chapter 19. State its preservation conclusion as a typing judgment. At the end compare it with the equality of arrows obtained here. Write the sources and targets of both projections for $`G \times A`. Interpret the newest variable and a weakened old one.

*Joint proof · 30 minutes.* Construct the application arrow using pairing. Then derive the beta equation using the exponential equation and the two projection identities.

*Proof review · 20 minutes.* Evaluate both sides in sets for Exercise 2 and reconstruct the categorical proof without referring to elements.

*Facilitator’s hint.* Verify each side has source $`G` before simplifying. The exponential equation itself starts at $`G \times A`, which is why the proof precomposes it.

# Solutions
%%%
tag := "ch26-s6"
number := false
%%%

*1.* The body is $`\pi_{2}:1 \times A\rightarrow A`. Its curry has type $`1\rightarrow A^{A}` and selects the identity function in sets.

*2.* The curried function at 3 sends $`x` to $`3 + x`. Its argument is 6, giving 9. On the substitution side the pairing first supplies $`\left( {3,6} \right)` and $`h` returns 9.

*3.* The codomain of $`a` is $`A`, whereas the domain of $`f` is $`G`. Even if these objects happen to agree, that composite would land in $`B^{A}`. Evaluation of the paired arrows is what gives an arrow to $`B`.

*Further problem.* Write `π₁` and `π₂` for the projections from `D × A`. Form `w = ⟨u ∘ π₁, π₂⟩ : D × A → G × A`. It changes the outer assignment while keeping the new bound variable. The right side of the proposed equation is the unique arrow `D → Bᴬ` whose application in context `D × A` recovers `h ∘ w`. It remains to check the left side against that specification.

Its application is `ev ∘ ⟨curry(h) ∘ u ∘ π₁, π₂⟩`. By the two projection equations for `w` and uniqueness of pairing, the paired arrow factors as `⟨curry(h) ∘ π₁′, π₂′⟩ ∘ w`, where primes denote the projections from `G × A`. Composing with `ev` and using the defining equation for `curry(h)` reduces this to `h ∘ w`. Exponential uniqueness now proves equality of the two arrows out of `D`. The unmodified second projection in `w` explains why the substituted outer assignment leaves the newly introduced variable available to the body.
