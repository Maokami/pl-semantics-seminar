import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Initial Algebras and Structural Recursion" =>
%%%
tag := "ch25"
file := "chapter-25"
%%%

[Chapter PDF](print/chapter-25.pdf) · [Session 4](seminar/index.html#week-04)

The evaluator in Chapter 1 specifies a result at each leaf and combines two results at an addition. Counting nodes uses the same recursion with different operations. We can characterize the expression datatype by what it allows us to do for *every* choice of such operations.

*Sources.* Reynolds, _Theories of Programming Languages_, §§1.1–1.2, pp. 1–11, on abstract syntax and its compositional interpretation. We formulate the initial-algebra argument explicitly for the integer arithmetic fragment and recover the evaluator as an instance. [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Algebras for a signature
%%%
tag := "ch25-s1"
%%%

Fix the integers and a set $`V` of variables. An algebra for the expression signature consists of a carrier set $`A`, maps $`l_{A}:{\mathbb{Z}}\rightarrow A` and $`v_{A}:V\rightarrow A`, and a binary operation $`p_{A}:A \times A\rightarrow A`. No associativity, commutativity or identity equations are assumed. For example, an algebra on natural numbers can give each leaf size one and set $`p_{A}({i,j}) = 1 + i + j`.

Between algebras $`A,B`, a *homomorphism* is a function $`h:A\rightarrow B` satisfying three equations for all inputs:

$$`h\left( l_{A}(n) \right) = l_{B}(n),\quad h\left( v_{A}(x) \right) = v_{B}(x),`

$$`h\left( p_{A}({a,b}) \right) = p_{B}({h{(a)},h{(b)}}).`

Identity functions satisfy these equations and composites of two homomorphisms satisfy them by substitution. Thus the algebras and their homomorphisms form a category. An object is *initial* if for every object in the category there is exactly one morphism from it to that object.

A common alternative notation collects the input shapes into $`F(X) = {\mathbb{Z}} + V + \left( {X \times X} \right)`, where $`+` is tagged disjoint union. Each algebra is one map $`F(A)\rightarrow A`. Its three branches are exactly the operations listed above. The tags distinguish an integer literal from a variable even if the underlying sets happen to overlap.

To see how much information the signature leaves open, take the carrier to be finite words over the two symbols L and V. Send every literal to the one-letter word L, every variable to V, and an addition to the concatenation of its two child words in their given order. The trees `add(var(x),lit(7))` and `add(lit(7),var(x))` then receive the words VL and LV. For the integer interpretation the values of these trees agree in every state, by commutativity of addition. Both interpretations satisfy the same signature. It is the choice of operations on a carrier that makes an algebra sensitive to leaf order.

The length of a word gives a homomorphism to another algebra. On natural numbers, let both leaf operations return one and let the binary operation be ordinary addition. Check the binary law at arbitrary words `u` and `v`. The length of their concatenation counts each position of `u` followed by each position of `v`, giving the sum of the two lengths. The two leaf laws hold because each letter has length one. Consequently, interpreting a tree as a word and taking its length counts leaves, even though the intermediate interpretation records their order. This is an instance in which preserving all three operations has a visible computational consequence.

# Existence and uniqueness
%%%
tag := "ch25-s2"
%%%

Let $`E` be the set of finite trees with constructors lit, var and add. Take these three constructors as the operations of an algebra with carrier $`E`. *Theorem 4.1.* This algebra is initial.

Fix any algebra $`A`. Define $`h` by recursion on finite trees. At a literal return $`l_{A}(n)`, at a variable return $`v_{A}(x)`, and at an addition return $`p_{A}({h{(e_{1})},h{(e_{2})}})`. Each recursive call has smaller tree height, so a result is defined for every tree. The homomorphism equations now hold by the three defining clauses. This proves existence.

For uniqueness take any homomorphism $`g:E\rightarrow A`. Prove $`g(e) = h(e)` by structural induction on $`e`. At a literal both sides equal $`l_{A}(n)`; at a variable both equal $`v_{A}(x)`. At an addition the homomorphism law gives $`g\left( {\text{add}\left( {e_{1},e_{2}} \right)} \right) = p_{A}({g{(e_{1})},g{(e_{2})}})`. Replace both child results by the induction hypotheses and use the defining clause for $`h`. Equality at every input gives equality of functions. The unique map $`h` is called the *fold* into $`A`.

Consider the tree `add(add(var(x),lit(1)),lit(2))`. To show that two candidate folds agree at this tree, one must know that they agree at `add(var(x),lit(1))` as well as at `lit(2)`. Agreement just at all leaves would leave the interpretation of the inner addition unspecified. Conversely, agreement on the two immediate children is sufficient however large those children are. The binary homomorphism equation takes those two equalities as input and produces the equality at the parent.

One can record the induction as an ordinary Lean theorem. The target operations are parameters so the proof below applies, for example, to the word and length interpretations above. The final case exposes precisely the two hypotheses needed to rewrite the arguments of `plus`.

```lean
inductive FoldTree where
  | lit : Int → FoldTree
  | var : Nat → FoldTree
  | add : FoldTree → FoldTree → FoldTree

def FoldTree.foldInto {A : Type} (lit : Int → A) (var : Nat → A)
    (plus : A → A → A) : FoldTree → A
  | .lit n => lit n
  | .var x => var x
  | .add a b => plus (a.foldInto lit var plus) (b.foldInto lit var plus)

theorem foldInto_unique {A : Type} (lit : Int → A) (var : Nat → A)
    (plus : A → A → A) (g : FoldTree → A)
    (hl : ∀ n, g (.lit n) = lit n) (hv : ∀ x, g (.var x) = var x)
    (ha : ∀ a b, g (.add a b) = plus (g a) (g b)) :
    ∀ t, g t = t.foldInto lit var plus := by
  intro t
  induction t with
  | lit n => exact hl n
  | var x => exact hv x
  | add a b iha ihb => simp only [FoldTree.foldInto, ha, iha, ihb]
```

# Evaluation as a fold
%%%
tag := "ch25-s3"
%%%

Choose carrier $`A = \left( {\Sigma\rightarrow{\mathbb{Z}}} \right)` for the state set $`\Sigma = \left( {V\rightarrow{\mathbb{Z}}} \right)`. A literal produces the constant function at its integer. A variable produces the function taking $`s` to $`s(x)`. For two functions $`f,g`, their combination takes $`s` to $`f(s) + g(s)`. The fold now takes a tree to a function. Applying the fold of `add(var(x),lit(4))` to a state with $`s(x) = 3` gives $`3 + 4 = 7`. The equations of Chapter 1 say exactly that its evaluator, with state supplied last, is a homomorphism to this algebra. The uniqueness just proved identifies the two functions on *all* trees and states.

The tree `add(lit(1),lit(2))` and `lit(3)` receive the same evaluation function. Their sizes are three and one in the size algebra. Imposing integer arithmetic identities on trees themselves would remove the possibility of interpreting them freely in the size algebra.

Fix a state `s` temporarily. It determines a second algebra with carrier the integers. Interpret a literal by its integer, a variable `x` by `s(x)`, and a pair by its sum. There are now two routes from an expression to an integer. One can interpret the whole tree in the function algebra and apply the resulting function to `s`. Alternatively, one can fold directly into this integer algebra using the fixed assignment. To compare them, consider the map sending any function `q` to `q(s)`. It preserves literal and variable interpretations by evaluation. For addition it preserves the operation because the pointwise sum evaluated at `s` is precisely `q(s) + r(s)`. The composite along the first route is therefore a homomorphism into the fixed-state algebra. Initiality identifies it with the second route.

This argument also explains when a variable can be interpreted by a fixed integer. Such a choice is legitimate if the interpretation is meant for one specified state. Suppose instead that the required result is the meaning of the variable at every state. Two states assigning respectively two and five to the same name demand distinct results. A single integer cannot answer both queries. A function can retain this dependence while still letting addition operate on the meanings of immediate subexpressions.

# Exercises
%%%
tag := "ch25-s4"
number := false
%%%

1. Give the operations for a fold that returns the set of variable names occurring in a tree.
2. Suppose $`u:A\rightarrow B` is a homomorphism. Prove that composing the fold into $`A` with $`u` gives the fold into $`B`.
3. If the expression set were enlarged by a cyclic object $`q = \text{add}\left( {q,q} \right)`, show that the size algebra could admit no homomorphism from that enlarged object.

*Further problem.* Simultaneous folds. Let `A` and `B` be any two algebras for the expression signature. Give operations on `A × B` so that folding once produces, at each tree, both of the original folds. Prove the result from initiality. Why does the same argument fail if the product's addition swaps its left and right children in its second coordinate?

# Reading for the Seminar
%%%
tag := "ch25-s5"
number := false
%%%

*Definitions · 10 minutes.* Begin with the expression tree for x + 4 in Chapter 1. Assign each leaf its value in a fixed state, then assign each leaf size one. Evaluate the same tree in the size algebra and in the function algebra. Write the types of the three operations in each.

*Joint proof · 30 minutes.* Prove existence by constructing a fold into an unspecified algebra. Erase its recursion equations as assumptions about a competitor and derive the competitor’s equality by induction.

*Proof review · 20 minutes.* At the addition node compare any candidate homomorphism with the fold. Use the two child equalities to justify the root equality. Exercise 2 on fusion extends this calculation.

*Facilitator’s hint.* For uniqueness, leave the receiving algebra arbitrary. Fix a competing homomorphism and apply its own law before invoking a child induction hypothesis.

# Solutions
%%%
tag := "ch25-s6"
number := false
%%%

*1.* Use subsets of $`V` as carrier. A literal gives the empty set, a variable its singleton, and addition the union of the two child sets.

*2.* A composite of homomorphisms is a homomorphism, hence the composite in question is one from the initial algebra to $`B`. Uniqueness identifies it with the fold into $`B`.

*3.* Its image $`k` would be a natural number satisfying $`k = 1 + 2k`, impossible since the right side is larger. The theorem used the strictly smaller heights of children of finite trees.

*Further problem.* Interpret a literal as `(lA(n), lB(n))` and a variable as `(vA(x), vB(x))`. On two pairs `(a,b)` and `(a′,b′)` define addition to give `(pA(a,a′), pB(b,b′))`. Projection onto either coordinate now preserves all three operations: the projection of a literal or variable is its interpretation in that component, and projection of a combined pair gives the combination of the projections in the same order. Compose each projection with the fold into the product. Each composite is a homomorphism from the expression algebra, so by uniqueness it is the corresponding component fold. Equality in a Cartesian product is componentwise, proving the claimed result for every expression.

Swapping the two arguments only in the second coordinate would ask the second projection to preserve addition by the equation `pB(b′,b) = pB(b,b′)`. The signature imposes no such law. Choose `B` to be strings, interpret a literal by its decimal representation, and use concatenation. At the sum of literals one and two the usual fold returns `"12"`, whereas the swapped component returns `"21"`.
