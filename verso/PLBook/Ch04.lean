import VersoManual
import PLBook.IMP.Fold

open Verso.Genre Manual

#doc (Manual) "Expression Folds and Their Uniqueness" =>
%%%
tag := "ch25"
file := "chapter-25"
%%%

* *Definitions.* The four constructors of IMP expressions and the evaluator of Session 1, Definitions 1.1–1.3. [IMP language card A.1–A.3](imp-card/index.html#imp-a1)
* *New terms.* Fold, constructor equation. [Glossary](glossary/index.html)
* *Theorem 4.1 \[This book\] \[Checked\].* For every set $`A` equipped with a literal operation, a variable operation, and two binary operations, exactly one function from expressions to $`A` satisfies the four constructor equations of §4.1.
* *Source.* The organizer’s S1 seminar develops the uniqueness argument. Here it applies to the string names and four expression constructors of Leroy’s IMP. [Sources and proof declarations](imp-card/index.html#imp-sources)
* *Board case.* At an addition node, use the two induction hypotheses to compare the results of two functions satisfying the same equations.
* *Proof outline.* Define one function by recursion on finite trees. For every competing function, prove pointwise equality by structural induction.
* *From Session 1.* Evaluation in a fixed store returns an integer. The same recursion can count nodes or record the order of leaves by changing the operations performed at the nodes.

The evaluator in Session 1 specifies a result at each leaf and combines two results at an addition. Counting nodes uses the same recursion with different operations. We can characterize the expression datatype by what it allows us to do for *every* choice of such operations.

# Four operations on a set
%%%
tag := "ch25-s1"
%%%

Fix a store $`s` with $`s(x)=3`. To evaluate $`x+4`, interpret the variable by lookup, the literal by its integer, and the root by integer addition. The result is seven. At the root of $`x-4` use subtraction instead, giving minus one. This interpretation takes values in $`\mathbb Z`.

To count nodes, give each leaf size one and combine sizes $`i,j` by $`1+i+j` at either binary node. The same two trees now both have size three. Here the result set is the natural numbers.

Write $`E` for the expressions of Session 1, Definition 1.1, and $`V` for the set of variable names (strings). Choose a set $`A` and four operations

$$`L:\mathbb Z\to A,\qquad V_A:V\to A,\qquad P,M:A\times A\to A.`

No associativity, commutativity or identity equations are assumed. A *constructor equation* specifies the result of a function on trees whose root is one particular constructor. For $`h:E\to A` the four equations are

$$`\begin{aligned}
h(n)&=L(n) & h(x)&=V_A(x)\\
h(e_1+e_2)&=P(h(e_1),h(e_2)) & h(e_1-e_2)&=M(h(e_1),h(e_2)).
\end{aligned}`

They hold for every integer $`n`, name $`x` and pair of expressions $`e_1,e_2`. A *fold* computes its result by these equations, replacing each constructor by its specified operation.

To see how much information the four operations can express, take the set of results to be finite words over the two symbols L and V. Send every literal to the one-letter word L, every variable to V, and either binary node to the concatenation of its two child words in their given order. The trees `add(var(x),lit(7))` and `add(lit(7),var(x))` then receive the words VL and LV. For the integer interpretation the values of these trees agree in every store, by commutativity of addition. The word interpretation records the order of the leaves.

Now take the length of the resulting word. On natural numbers, let both leaf operations return one and let both binary operations be ordinary addition. Check the length equation at arbitrary words `u` and `v`. The length of their concatenation counts each position of `u` followed by each position of `v`, giving the sum of the two lengths. The two leaf laws hold because each letter has length one. Consequently, interpreting a tree as a word and taking its length counts leaves, even though the intermediate interpretation records their order.

# Existence and uniqueness
%%%
tag := "ch25-s2"
%%%

*Theorem 4.1 (Existence and uniqueness of a fold) \[This book\] \[Checked\].* For every set $`A` and choice of $`L,V_A,P,M` as in §4.1 there is exactly one function $`h:E\to A` satisfying all four constructor equations.

*Existence.* Define $`h` by recursion on finite trees. At a literal return $`L(n)`, at a variable return $`V_A(x)`, at an addition apply $`P` to the two child results, and at a subtraction apply $`M` to them in left-to-right order. Each recursive call has smaller tree height, so a result is defined for every tree. The four defining clauses give precisely the four equations.

*Uniqueness.* Fix another function $`g:E\to A` satisfying the equations. Use structural induction (Session 1, §1.1) with property $`Q(e)\coloneqq g(e)=h(e)`. At a literal both sides equal $`L(n)`. At a variable both equal $`V_A(x)`.

1. At $`e=e_1+e_2`, the induction hypotheses are $`Q(e_1):g(e_1)=h(e_1)` and $`Q(e_2):g(e_2)=h(e_2)`.
2. The constructor equation for $`g` gives $`g(e_1+e_2)=P(g(e_1),g(e_2))`.
3. Substitute the first hypothesis in the left argument of $`P` and the second in its right argument. The result is $`P(h(e_1),h(e_2))`.
4. The defining equation for $`h` identifies that result with $`h(e_1+e_2)`. This proves $`Q(e_1+e_2)`.

At $`e=e_1-e_2`, the same child hypotheses give $`g(e_1-e_2)=M(g(e_1),g(e_2))=M(h(e_1),h(e_2))=h(e_1-e_2)`. Equality at every input gives equality of functions. $`\square`

Consider the tree `add(add(var(x),lit(1)),lit(2))`. To show that two candidate folds agree at this tree, one must know that they agree at `add(var(x),lit(1))` as well as at `lit(2)`. Agreement just at all leaves would leave the interpretation of the inner addition unspecified. Conversely, agreement on the two immediate children is sufficient however large those children are. The constructor equation for addition takes those two equalities as input and produces the equality at the parent.

# Evaluation as a fold
%%%
tag := "ch25-s3"
%%%

Now allow the store to vary. Choose $`A=\Sigma\to\mathbb Z`, where $`\Sigma` is the set of stores of Session 1, Definition 1.2. A literal produces the constant function at its integer. A variable produces the function taking $`s` to $`s(x)`. For two functions $`f,g`, their sum takes $`s` to $`f(s)+g(s)` and their difference takes $`s` to $`f(s)-g(s)`. The fold now takes a tree to a function. Applying the fold of `add(var(x),lit(4))` to a store with $`s(x)=3` gives $`3+4=7`. By Definition 1.3, the function sending $`e` to $`(s\mapsto\mathrm{eval}(e,s))` satisfies all four equations. Theorem 4.1 identifies it with this fold on every tree.

The tree `add(lit(1),lit(2))` and `lit(3)` receive the same evaluation function. The node counts are three and one. Imposing integer arithmetic identities on trees themselves would remove the possibility of counting their nodes in this way.

Return to the fixed store of §4.1. There are now two routes from an expression to an integer. One can interpret the whole tree as a function and apply the resulting function to $`s`. Alternatively, one can fold directly into the integers using lookup in $`s`. To compare them, consider the map sending any function $`q` to $`q(s)`. It preserves literal and variable interpretations by evaluation. Evaluating a pointwise sum at $`s` gives $`q(s)+r(s)`, and evaluating a pointwise difference gives $`q(s)-r(s)`. Thus the first route satisfies the four equations for the second. Uniqueness identifies the two routes.

This argument also explains when a variable can be interpreted by a fixed integer. Such a choice is legitimate if the interpretation is meant for one specified store. Suppose instead that the required result is the meaning of the variable at every store. Two stores assigning respectively two and five to the same name demand distinct results. A single integer cannot answer both queries. A function can retain this dependence while still letting addition operate on the meanings of immediate subexpressions.

# Exercises
%%%
tag := "ch25-s4"
number := false
%%%

1. Give the operations for a fold that returns the set of variable names occurring in a tree.
2. Suppose $`A,B` each have four operations as in §4.1, and $`u:A\to B` commutes with them. For instance, $`u(P_A(a,b))=P_B(u(a),u(b))`, and similarly for the other three operations. Prove that composing the fold into $`A` with $`u` gives the fold into $`B`.
3. If the expression set were enlarged by a cyclic object $`q=\operatorname{add}(q,q)`, show that the node-counting equations could have no solution on that enlarged set.

*Further problem.* Simultaneous folds. Let $`A` and $`B` be any two sets with four operations as in §4.1. Give operations on $`A\times B` so that folding once produces, at each tree, both of the original folds. Prove the result by uniqueness. Why does the same argument fail if the product's addition swaps its left and right children in its second coordinate?

# Reading for the Seminar
%%%
tag := "ch25-s5"
number := false
%%%

*Definitions · 10 minutes.* Begin with the expression tree for x + 4 in Session 1. Assign each leaf its value in a fixed store, then assign each leaf size one. Evaluate the same tree in the two interpretations. Write the types of the four operations in each.

*Joint proof · 30 minutes.* Prove existence by constructing a fold into an arbitrary set with four operations. Write the same four equations for a second function. Use them to prove that the two functions agree on every tree.

*Proof review · 20 minutes.* At the addition node compare any competing function with the fold. Use the two child equalities to justify the root equality. Exercise 2 extends this calculation.

*Facilitator’s hint.* For uniqueness, leave the set of results arbitrary. Fix a competing function and apply its own constructor equation before invoking a child induction hypothesis.

# Solutions
%%%
tag := "ch25-s6"
number := false
%%%

*1.* Use subsets of $`V` as results. A literal gives the empty set, a variable its singleton, and both binary operations take the union of the two child sets.

*2.* Write $`h` for the fold into $`A`. At an addition, $`u(h(e_1+e_2))=u(P_A(h(e_1),h(e_2)))=P_B(u(h(e_1)),u(h(e_2)))`. The other three equations for the composite follow by applying the corresponding hypothesis on $`u`. Uniqueness identifies the composite with the fold into $`B`.

*3.* Its image $`k` would be a natural number satisfying $`k = 1 + 2k`, impossible since the right side is larger. The theorem used the strictly smaller heights of children of finite trees.

*Further problem.* Interpret a literal as `(lA(n), lB(n))` and a variable as `(vA(x), vB(x))`. On two pairs `(a,b)` and `(a′,b′)` define addition to give `(pA(a,a′), pB(b,b′))`. Define subtraction componentwise in the same order. Projection onto either coordinate now preserves all four operations: the projection of a literal or variable is its interpretation in that component, and projection of a combined pair gives the combination of the projections in the same order. Compose each projection with the fold into the product. Each composite satisfies the four equations for its component, so by uniqueness it is the corresponding component fold. Equality in a Cartesian product is componentwise, proving the claimed result for every expression.

Swapping the two arguments only in the second coordinate would ask the second projection to preserve addition by the equation `pB(b′,b) = pB(b,b′)`. The constructor equations impose no such law. Choose `B` to be strings, interpret a literal by its decimal representation, and use concatenation for both binary operations; variables may give the empty word. At the sum of literals one and two the usual fold returns `"12"`, whereas the swapped component returns `"21"`.

*Further reading.* The organizer’s [S1 seminar](static/slides/s1/index.html#/15) gives the categorical formulation of Theorem 4.1. For a comparison with compositional interpretation, see [Reynolds, §§1.1–1.2](https://www.cs.cmu.edu/~jcr/tpl-toc.html).

In Session 14 the result set will consist of functions describing what a compiled instruction sequence does to a stack. Proving that compiled execution and expression evaluation satisfy the same four constructor equations will let us identify them by Theorem 4.1.
