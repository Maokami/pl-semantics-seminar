import VersoManual
import PLBook.IMP.Arithmetic

open Verso.Genre Manual

#doc (Manual) "Arithmetic Expressions" =>
%%%
tag := "ch01"
file := "chapter-01"
%%%

* *Definitions.* Arithmetic expressions, stores, the evaluation function, free variables and the evaluation judgment (Definitions 1.1–1.5; [IMP language card A.1–A.3](imp-card/index.html)).
* *New terms.* Inference rule, derivation, inversion, structural induction, induction on derivations. [Glossary and label key](glossary/index.html)
* *Theorem 1.3 (Correspondence).* For every expression $`e`, store $`s` and integer $`n`, $`s\vdash e\Downarrow n` if and only if $`\mathrm{eval}(e,s)=n`.
* *Source.* The syntax, stores and evaluation function follow the arithmetic fragment of Leroy’s IMP. The four evaluation rules are formulated here on that syntax. Winskel identifies the graph of an expression’s meaning, the set of pairs of a store and the value in that store, with the pairs of stores and integers justified by his rules. [Source and proof references](imp-card/index.html#imp-sources) · [Winskel, §5.3, pp. 61–62](https://doi.org/10.7551/mitpress/3054.001.0001)
* *Board case.* Addition in both directions. In one direction the two children of a derivation give equalities. In the other the two children of an expression give derivations.
* *Proof outline.* From a derivation with result $`n`, prove that the evaluator returns $`n` by induction on that derivation. For the converse, construct a derivation of the computed result by structural induction on the expression.
* *Starting point.* We begin with the expression $`x+4` and a store in which $`x` holds $`3`.

In a store where the variable $`x` holds $`3`, the expression $`x + 4` has value $`7`. This chapter gives two precise accounts of that sentence. The first is a function that computes the value from the leaves of the expression up. The second is a set of rules that justify a proposed value step by step. We shall prove that a proposed value has a justification by the rules exactly when the function returns it. The same example runs through every section.

# Abstract syntax and stores
%%%
tag := "ch01-s1"
%%%

*Definition 1.1 (Arithmetic expressions).* Let $`x` range over variable names (strings) and $`n` over mathematical integers. An expression is a finite tree built with four constructors:

$$`e ::= n \mid x \mid (e_1+e_2) \mid (e_1-e_2).`

A minus sign at an internal node denotes binary subtraction. A negative integer at a leaf is a literal.

The symbol $`::=` introduces alternatives, separated by vertical bars. In the grammar $`x` stands for any name. In the example $`x+4` it is one particular name.

A *constructor* builds a tree from its parts. We write $`\operatorname{lit}(n)`, $`\operatorname{var}(x)`, $`\operatorname{add}(e_1,e_2)` and $`\operatorname{sub}(e_1,e_2)` when we want to name the constructors explicitly. A programmer may read Definition 1.1 as a datatype with these four cases. We use $`x + 4` as a concrete notation for $`\operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(4)} \right)`, the tree

$$`\begin{matrix} & \operatorname{add} & \\ \swarrow & & \searrow \\ \operatorname{var}(x) & & \operatorname{lit}(4) \end{matrix}`

Every expression has exactly one outermost constructor, and the children of a binary node are uniquely determined and ordered. So in a definition or proof by cases on the root, each expression falls under exactly one case. Write $`V=\mathrm{Name}` for the set of strings, $`\mathbb Z` for the set of integers and $`E` for the set of expression trees.

*Structural induction* proves a property $`P(e)` by considering each constructor. At a binary node, the claims $`P(e_1)` and $`P(e_2)` for its two immediate children are the *induction hypotheses*. The property $`P` is the *induction property*. To prove $`\forall e\in E,\ P(e)`, that is, $`P(e)` for every expression $`e`, it suffices to prove

$$`\begin{aligned}
&P(n)\ \text{for every integer}\ n,\qquad P(x)\ \text{for every name}\ x,\\
&P(e_1)\land P(e_2)\Rightarrow P(e_1+e_2)\ \text{ and }\ P(e_1)\land P(e_2)\Rightarrow P(e_1-e_2)\ \text{ for all}\ e_1,e_2.
\end{aligned}`

Here $`\land` reads “and” and $`\Rightarrow` (also written $`\Longrightarrow`) reads “implies”. Why may the binary cases assume $`P(e_1)` and $`P(e_2)`? Take $`x+4`. The leaf cases give $`P(\operatorname{var}(x))` and $`P(\operatorname{lit}(4))`, and the addition case turns these into $`P(x+4)`. Every expression is built from its leaves in finitely many such steps, so the four cases reach every node. The induction hypotheses are the claims already obtained for the children.

*Definition 1.2 (Stores).* A store records the current integer value of every variable in IMP. We represent it by a total function $`s:\mathrm{Name}\to\mathbb Z`. Write $`\Sigma` for the set of stores. The update $`s[x\mapsto n]` is the function whose value at $`x` is $`n` and whose value at each other name $`y` is $`s(y)`. Equality of stores means equality at every name.

For example, let $`s` return $`3` at $`x` and $`0` everywhere else, including at names such as $`y` that do not occur in $`x+4`. The symbol $`x` is an element of $`V`, the tree $`\operatorname{var}(x)` is an element of $`E`, and the value $`s(x) = 3` is an element of $`\mathbb{Z}`. Only the last of these depends on the chosen store.

An update builds a new store and leaves $`s` unchanged: $`s[x\mapsto 8]` has value $`8` at $`x` and $`s(y)` at every other name $`y`, while $`s(x)` is still $`3`.

# Evaluation
%%%
tag := "ch01-s2"
%%%

*Definition 1.3 (Evaluation).* The evaluation function is defined by *structural recursion*. There is one equation per constructor, and recursive calls are made only on immediate children. At each binary node it obtains the two operand values in the same store.

$$`\begin{aligned}
\mathrm{eval}(n,s)&=n & \mathrm{eval}(x,s)&=s(x)\\
\mathrm{eval}(e_1+e_2,s)&=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)\\
\mathrm{eval}(e_1-e_2,s)&=\mathrm{eval}(e_1,s)-\mathrm{eval}(e_2,s).
\end{aligned}`

Here $`\mathrm{eval}:E\times\Sigma\to\mathbb Z`. On the left of the first equation, $`n` is the leaf $`\operatorname{lit}(n)`; on the right it is an integer. On the left of the third equation, $`+` constructs a tree. On the right it adds two integers. Both recursive calls use the given store.

Calling $`\mathrm{eval}` only on immediate children is what makes the equations a definition. For each fixed store, the first two equations give the value at every leaf, and a binary equation gives the value at a node from the values at its two children. Every tree is built from its leaves in finitely many steps, so the equations determine a unique total function.

*Example 1.1.* If $`s(x) = 3`, then

$$`\begin{aligned}
\mathrm{eval}(\operatorname{add}(\operatorname{var}(x),\operatorname{lit}(4)),s)
&=\mathrm{eval}(\operatorname{var}(x),s)+\mathrm{eval}(\operatorname{lit}(4),s)&&\text{by the addition equation}\\
&=3+4=7&&\text{by the variable and literal equations.}
\end{aligned}`

In $`s[x\mapsto8]` only the lookup at $`\operatorname{var}(x)` changes, and the result is $`8+4=12`.

# Free variables and the coincidence lemma
%%%
tag := "ch01-s3"
%%%

Example 1.1 read the store only at $`x`. The free variables of an expression are the names it reads.

*Definition 1.4 (Free variables).* The function $`\operatorname{FV}:E\rightarrow\mathcal{P}(V)` assigns a set of variable names to each expression. Here $`\mathcal{P}(V)` is the set of all subsets of $`V`, $`\varnothing` is the empty set, and $`\cup` denotes set union. Define

$$`\begin{aligned}
\mathrm{FV}(n)&=\varnothing & \mathrm{FV}(x)&=\{x\}\\
\mathrm{FV}(e_1+e_2)&=\mathrm{FV}(e_1)\cup\mathrm{FV}(e_2)\\
\mathrm{FV}(e_1-e_2)&=\mathrm{FV}(e_1)\cup\mathrm{FV}(e_2).
\end{aligned}`

An occurrence is one leaf labelled with a variable name. A *binder* introduces a local name within a specified part of a term, its scope. An occurrence is *free* if no enclosing binder binds it. A function parameter is a binder: in a function with parameter $`x` and body $`x+y`, the occurrence of $`y` is free and that of $`x` is not. Our four constructors introduce no binders, so every variable occurrence is free. Two occurrences of the same name contribute one element to the set. For our example, $`\mathrm{FV}(x+4)=\{x\}\cup\varnothing=\{x\}`.

For $`S \subseteq V`, let $`s \rvert_{S}:S\rightarrow{\mathbb{Z}}` denote the restriction of $`s` to $`S`. Thus $`s \rvert_{S} = t\rvert_{S}`, read “$`s` and $`t` agree on $`S`”, holds exactly when $`s(x) = t(x)` for every $`x \in S`.

If a store $`t` agrees with $`s` on $`\mathrm{FV}(x+4)`, that is, $`t(x)=s(x)`, then

$$`\mathrm{eval}(x+4,s)=s(x)+4=t(x)+4=\mathrm{eval}(x+4,t).`

This calculation used one fact per node: the agreement $`t(x)=s(x)` at the leaf $`\operatorname{var}(x)`, no fact about the stores at the leaf $`\operatorname{lit}(4)`, since a literal does not read the store, and the addition equation at the root. No single calculation covers every shape of tree. Structural induction supplies such a calculation node by node.

*Lemma 1.1 (Coincidence).* For every $`e \in E` and $`s,t \in \Sigma`,

$$`s \rvert_{\operatorname{FV}{(e)}} = t \rvert_{\operatorname{FV}{(e)}}\quad\Longrightarrow\quad\operatorname{eval}\left( {e,s} \right) = \operatorname{eval}\left( {e,t} \right).`

*Proof.* By structural induction on $`e` we prove the property below. The symbol $`\coloneqq` reads “is defined as”, and $`\square` marks the end of a proof.

$$`P(e)\ \coloneqq\ \forall s,t\in\Sigma,\quad s|_{\mathrm{FV}(e)}=t|_{\mathrm{FV}(e)}
\ \Longrightarrow\ \mathrm{eval}(e,s)=\mathrm{eval}(e,t).`

In each case fix $`s` and $`t` that agree on $`\mathrm{FV}(e)`. The goal is $`\mathrm{eval}(e,s)=\mathrm{eval}(e,t)`.

If $`e=n`, both evaluations give $`n`. If $`e=x`, then $`\mathrm{FV}(e)=\{x\}`, so $`s(x)=t(x)`, and $`\mathrm{eval}(x,s)=s(x)=t(x)=\mathrm{eval}(x,t)`.

If $`e=e_1+e_2`, the induction hypotheses are the same statement for the two children:

$$`P(e_i):\ \forall s,t\in\Sigma,\quad s|_{\mathrm{FV}(e_i)}=t|_{\mathrm{FV}(e_i)}\ \Longrightarrow\ \mathrm{eval}(e_i,s)=\mathrm{eval}(e_i,t)\qquad(i=1,2).`

1. Goal: $`s` and $`t` satisfy the left-hand sides of the implications in $`P(e_1)` and $`P(e_2)`, that is, they agree on $`\mathrm{FV}(e_1)` and on $`\mathrm{FV}(e_2)`. Each name in $`\mathrm{FV}(e_1)` lies in $`\mathrm{FV}(e)=\mathrm{FV}(e_1)\cup\mathrm{FV}(e_2)`, where $`s` and $`t` agree. The same holds for $`\mathrm{FV}(e_2)`. This step uses the agreement assumed in the lemma.
2. Goal: equal values at the root. Apply the addition equation, then $`P(e_1)` and $`P(e_2)` at $`s,t`, then the addition equation again.

$$`\begin{aligned}\mathrm{eval}(e_1+e_2,s)&=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)\\ &=\mathrm{eval}(e_1,t)+\mathrm{eval}(e_2,t)\\ &=\mathrm{eval}(e_1+e_2,t).\end{aligned}`

If $`e=e_1-e_2`, $`\mathrm{FV}(e)` is the same union, so step 1 is unchanged. Subtract the operand values in their original order to obtain

$$`\mathrm{eval}(e,s)=\mathrm{eval}(e_1,s)-\mathrm{eval}(e_2,s)
=\mathrm{eval}(e_1,t)-\mathrm{eval}(e_2,t)=\mathrm{eval}(e,t).\quad\square`

*Corollary 1.2 (Store update).* For every $`e\in E`, $`s\in\Sigma`, $`x\in V` and $`n\in\mathbb Z` with $`x\notin\mathrm{FV}(e)`,

$$`\operatorname{eval}\left( {e,s\left\lbrack {x\mapsto n} \right\rbrack} \right) = \operatorname{eval}\left( {e,s} \right).`

*Proof.* Let $`y\in\mathrm{FV}(e)`. Since $`x\notin\mathrm{FV}(e)`, $`y\neq x`, so $`s[x\mapsto n](y)=s(y)` by the definition of update. Thus $`s[x\mapsto n]` and $`s` agree on $`\mathrm{FV}(e)`. Apply Lemma 1.1. $`\square`

For instance, $`y\notin\mathrm{FV}(x+4)`, so Corollary 1.2 applied to the name $`y` gives $`\mathrm{eval}(x+4,s[y\mapsto5])=\mathrm{eval}(x+4,s)=7`. The hypothesis that the updated name is not free is needed: $`x\in\mathrm{FV}(x+4)`, and the update $`s[x\mapsto8]` changes the value to $`12`.

# Evaluation judgments
%%%
tag := "ch01-s4"
%%%

Why is $`7` a possible result for $`x+4` in $`s`, and could $`8` also be justified? We answer by rules that justify proposed results without running $`\mathrm{eval}`. Write $`s \vdash e \Downarrow n` for the claim that $`e` evaluates to $`n` in $`s`. Such a claim is a *judgment*. The turnstile $`\vdash` separates the input store from the expression, and the result after $`\Downarrow` is an integer. Both $`s\vdash x+4\Downarrow7` and $`s\vdash x+4\Downarrow8` are judgments; the rules decide which can be justified.

An *inference rule* puts its premises above the line and its conclusion below. Once every premise is justified, so is the conclusion. A rule with no premises is an *axiom*. Four rules govern evaluation. Like $`n`, the letters $`n_1` and $`n_2` stand for integers.

$$`\frac{}{s\vdash n\Downarrow n}\qquad\frac{}{s\vdash x\Downarrow s(x)}`

$$`\frac{s\vdash e_1\Downarrow n_1\quad s\vdash e_2\Downarrow n_2}{s\vdash e_1+e_2\Downarrow n_1+n_2}
\qquad\frac{s\vdash e_1\Downarrow n_1\quad s\vdash e_2\Downarrow n_2}{s\vdash e_1-e_2\Downarrow n_1-n_2}`

We refer to the four rules as the literal axiom, the variable axiom, the addition rule and the subtraction rule. The letters in a rule are placeholders. Replacing each letter by one particular object at all its occurrences gives an instance of the rule. The instance of the variable axiom for our store $`s` and the particular name $`x` is $`s\vdash \operatorname{var}(x)\Downarrow s(x)`, that is, $`s\vdash \operatorname{var}(x)\Downarrow3`.

*Example 1.2.* Take $`s(x) = 3`. We justify $`s\vdash x+4\Downarrow7` in three steps.

1. The variable axiom gives $`s \vdash \operatorname{var}(x) \Downarrow 3`.
2. The literal axiom with $`n:=4` gives $`s \vdash \operatorname{lit}(4) \Downarrow 4`. Here $`\operatorname{lit}(4)` is a tree and the final $`4` an integer; in the axiom $`s\vdash n\Downarrow n` the first $`n` likewise stands for the tree $`\operatorname{lit}(n)`.
3. The addition rule with $`e_1:=\operatorname{var}(x)`, $`e_2:=\operatorname{lit}(4)`, $`n_1:=3` and $`n_2:=4` has these two judgments as its premises. Its conclusion is $`s\vdash x+4\Downarrow 3+4`, that is, $`s\vdash x+4\Downarrow7`.

Writing each conclusion under the judgments that justify its premises gives a tree. The integer $`7` enters only at the root, as the sum $`n_1+n_2`.

$$`\frac{\frac{}{s \vdash \operatorname{var}(x) \Downarrow 3}\quad\frac{}{s \vdash \operatorname{lit}(4) \Downarrow 4}}{s \vdash \operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(4)} \right) \Downarrow 7}`

Could $`8` be justified? Read the construction backwards. Suppose any tree built in this way ends with $`s\vdash x+4\Downarrow n`.

1. The axioms conclude judgments about leaves and the subtraction rule about a subtraction. So the root is the addition rule, with premises $`s\vdash\operatorname{var}(x)\Downarrow n_1` and $`s\vdash\operatorname{lit}(4)\Downarrow n_2` for some integers $`n_1,n_2`, and $`n=n_1+n_2`.
2. Only the variable axiom concludes a judgment about a variable, and its result is $`s(x)`. So $`n_1=3`.
3. Only the literal axiom concludes a judgment about $`\operatorname{lit}(4)`. So $`n_2=4`.
4. Hence $`n=7`. No such tree ends with $`s\vdash x+4\Downarrow 8`.

Both activities have names. A *derivation* is a finite tree of rule applications whose root is the judgment proved and whose children derive the premise judgments. The tree of Example 1.2 is a derivation. If $`D` is a derivation whose root is the judgment $`J`, we write $`D:J` and say that $`D` derives $`J`. The *last rule* of a derivation is the rule applied at its root. *Inversion* recovers the possible last rules of a derivation, together with the premises and equalities forced by their conclusions. The backward reading in steps 1–4 was inversion.

*Definition 1.5 (Evaluation judgment).* Write $`s\vdash e\Downarrow n` when the judgment has a finite derivation by the four rules above.

From here on, a statement $`s\vdash e\Downarrow n`, as in Theorem 1.3, asserts that the judgment has a derivation. A phrase such as “the judgment $`s\vdash x+4\Downarrow8`” only names the claim.

Each constructor appears in the conclusion of exactly one rule. So the outermost constructor in a judgment fixes the last rule of each of its derivations, as at the root for $`x+4`.

Identify the judgment $`s\vdash e\Downarrow n` with the triple $`(s,e,n)\in\Sigma\times E\times\mathbb Z`. A set of triples is closed under the rules if, for every instance of a rule, it contains the conclusion whenever it contains all the premises. An axiom has no premises, so a closed set contains every instance of an axiom. The triples with derivations form the least closed set: it is closed, and it is a subset of every closed set. Solutions and Further Reading gives the short proof. Being closed is not enough. The set of all triples is closed under every rule and contains $`s \vdash \operatorname{lit}(4) \Downarrow 9`. No derivation has that conclusion: its last rule would be the literal axiom, whose result for this leaf is $`4`. In the least closed set, every triple is the conclusion of a rule instance whose premises are again in the set, so inversion is valid there. In the set of all triples, $`s \vdash \operatorname{lit}(4) \Downarrow 9` is the conclusion of no rule instance, so inversion fails, and $`\operatorname{lit}(4)` would have the two results $`4` and $`9`.

# Correspondence and determinacy
%%%
tag := "ch01-s5"
%%%

For $`x+4`, §1.4 found exactly one derivable result, the computed value $`7`. The following theorem says the same for every expression and store.

*Theorem 1.3 (Correspondence).* For every $`e \in E`, $`s \in \Sigma`, and $`n \in {\mathbb{Z}}`,

$$`s \vdash e \Downarrow n\quad\Longleftrightarrow\quad\operatorname{eval}\left( {e,s} \right) = n.`

The two directions start from different material.

* From left to right we are _given_ a derivation $`D:s\vdash e\Downarrow n`. We take it apart: its last rule and its premise derivations, which are smaller trees, are in hand. So we use induction on $`D`.
* From right to left we are given only the _expression_ $`e` and must _build_ a derivation. There is none yet to take apart, but $`e` can be taken apart: its outermost constructor says which rule goes at the root, and its children say what the premises are about. So we use structural induction on $`e`.

*Induction on derivations* is structural induction for derivation trees, whose immediate subtrees are the premise derivations of the last rule. To prove $`\forall D,\ P(D)`, prove $`P(D)` when $`D` is a single axiom, and $`P(D_1)\land P(D_2)\Rightarrow P(D)` when $`D` ends with the addition or subtraction rule applied to $`D_1` and $`D_2`. Here $`P(D_1)` and $`P(D_2)` are the induction hypotheses.

*Proof (from a derivation to a value).* By Definition 1.5, $`s\vdash e\Downarrow n` gives a derivation $`D:s\vdash e\Downarrow n`, so it suffices to prove a property of every derivation. For $`D:s\vdash e\Downarrow n`, read $`s`, $`e` and $`n` from the conclusion of $`D`, and let

$$`P(D)\coloneqq\mathrm{eval}(e,s)=n.`

We prove $`P(D)` for every $`D` by induction on $`D`. In the literal and variable cases the conclusion agrees with the corresponding equation of Definition 1.3. For instance, the variable axiom concludes $`s\vdash x\Downarrow s(x)`, and $`\mathrm{eval}(x,s)=s(x)`. For addition:

1. Goal: express $`e` and $`n` through the premises. The last rule is the addition rule. Its premise derivations are $`D_1:s\vdash e_1\Downarrow n_1` and $`D_2:s\vdash e_2\Downarrow n_2`. Its conclusion is $`s\vdash e_1+e_2\Downarrow n_1+n_2`, so $`e=e_1+e_2` and $`n=n_1+n_2`.
2. Goal: facts about the children. The two induction hypotheses are $`P(D_1):\mathrm{eval}(e_1,s)=n_1` and $`P(D_2):\mathrm{eval}(e_2,s)=n_2`.
3. Goal: $`\mathrm{eval}(e,s)=n`. By the addition equation of Definition 1.3, then step 2, then step 1, $`\mathrm{eval}(e_1+e_2,s)=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)=n_1+n_2=n`.

For subtraction, the last rule fixes $`n=n_1-n_2`. Applying the two induction hypotheses in the subtraction equation gives $`\mathrm{eval}(e_1-e_2,s)=n_1-n_2=n`.

*Proof (from a value to a derivation).* Fix a store $`s`. Every rule uses the store of its conclusion in its premises, so $`s` stays the same throughout. By structural induction on $`e` we prove

$$`Q(e)\coloneqq s\vdash e\Downarrow\mathrm{eval}(e,s).`

For a literal use the literal axiom. For a variable use the variable axiom, whose result $`s(x)` is $`\mathrm{eval}(x,s)`. For addition:

1. Goal: derivations for the children. The induction hypotheses $`Q(e_1):s\vdash e_1\Downarrow\mathrm{eval}(e_1,s)` and $`Q(e_2):s\vdash e_2\Downarrow\mathrm{eval}(e_2,s)` supply them.
2. Goal: a derivation whose root concerns $`e_1+e_2`. Place the addition rule with $`n_1:=\mathrm{eval}(e_1,s)` and $`n_2:=\mathrm{eval}(e_2,s)` below these two derivations, so that their roots are its premises. Its result is $`\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)`.
3. Goal: the result that $`Q(e_1+e_2)` requires. By Definition 1.3 this integer is $`\mathrm{eval}(e_1+e_2,s)`.

For subtraction, use the subtraction rule on the same two child derivations. Its result is $`\mathrm{eval}(e_1,s)-\mathrm{eval}(e_2,s)=\mathrm{eval}(e_1-e_2,s)`. Finally, if $`\mathrm{eval}(e,s)=n`, the derivation just constructed has the required result $`n`. $`\square`

The induction on syntax builds a derivation of the computed integer, but the theorem speaks of any candidate integer $`n`. The final sentence of the reverse proof uses the assumption $`\mathrm{eval}(e,s)=n` to identify the two. For $`x+4` the construction rebuilds the tree of Example 1.2.

*Corollary 1.4 (Unique result).* For every $`e\in E` and $`s\in\Sigma` there is an integer $`n` with $`s\vdash e\Downarrow n`, and if also $`s\vdash e\Downarrow m` then $`n=m`. In words, the evaluation judgment is *total* (every expression has a result in every store) and *deterministic* (it has at most one result).

*Proof.* Take $`n=\mathrm{eval}(e,s)`. The reverse direction of Theorem 1.3 gives $`s\vdash e\Downarrow n`. If $`s\vdash e\Downarrow m`, the forward direction gives $`\mathrm{eval}(e,s)=m`, so $`n=m`. $`\square`

# Exercises
%%%
tag := "ch01-s7"
number := false
%%%

*1.1.* Let $`e = \operatorname{add}\left( {\operatorname{var}(x),\operatorname{add}\left( {\operatorname{lit}(4),\operatorname{var}(z)} \right)} \right)`, with $`x,y,z` distinct. Suppose $`s(x) = 2`, $`s(y) = 9`, and $`s(z) = 5`. Compute $`\operatorname{eval}\left( {e,s} \right)` and $`\operatorname{FV}(e)` using their defining equations. Use Corollary 1.2 to determine $`\operatorname{eval}\left( {e,s\left\lbrack {y\mapsto - 1} \right\rbrack} \right)`.

*1.2.* Let $`e = \operatorname{add}\left( {\operatorname{var}(x),\operatorname{var}(y)} \right)`, with $`x \neq y`.

1. Give two stores that agree at $`x` and yield different values for $`e`.
2. Give two stores that disagree at both $`x` and $`y` and yield the same value for $`e`. State the converse of Lemma 1.1 and explain why this example refutes it.

*1.3.* Write $`{\mathbb{N}} = \left\{ {0,1,2,\ldots} \right\}` for the natural numbers. Let $`E_+` be the expressions built from literals, variables and addition. For each $`x \in V`, define $`m_{x}:E_+\rightarrow{\mathbb{N}}` by structural recursion so that $`m_{x}(e)` counts the occurrences of $`x` in $`e`. Prove by structural induction that for every $`e \in E_+`, every $`s \in \Sigma`, and every $`k \in {\mathbb{Z}}`,

$$`\operatorname{eval}\left( {e,s\left\lbrack {x\mapsto s(x) + k} \right\rbrack} \right) = \operatorname{eval}\left( {e,s} \right) + k \cdot m_{x}(e).`

Call $`S \subseteq V` sufficient for $`e` if agreement on $`S` implies equal evaluations of $`e`. Use Lemma 1.1 and the equation with $`k = 1` to show that $`\operatorname{FV}(e)` is the least sufficient set under inclusion.

*1.4.* Extend the grammar with $`\operatorname{neg}(e)` for integer negation. Add one equation to Definition 1.3 and one rule to Definition 1.5. Prove the new case in each direction of Theorem 1.3. Write down exactly what your induction hypothesis supplies in each proof.

*Further problem.* Now include binary subtraction, as in Definition 1.1. Say that a name is essential to an expression if two stores differing only at that name can give different values. Does membership in the set of free variables characterize essential names? Give an exact decision procedure for the full language and justify both directions.

# Reading for the Seminar
%%%
tag := "ch01-s8"
number := false
%%%

*Definitions · 10 minutes.* Copy the addition rule from §1.4, the addition equation from §1.2 and Theorem 1.3 onto the board. Fix $`s(x) = 3`. Ask one participant to compute $`x + 4` and another to justify the result by drawing the two axioms and the rule that uses them. Where does the number $`7` enter the derivation? Then ask whether $`8` could be justified, and read the tree from its root. Example 1.2 gives the board solution. The presenter covers the printed proof and rehearses the two constructions below.

*Joint proof · 30 minutes.* Divide the board into two columns. Use $`e = \operatorname{add}\left( {e_{1},e_{2}} \right)` in both. Write the given information at the top and the goal at the bottom. Leave room for participants to supply the intermediate steps.

1. *Given a derivation of* $`s \vdash e \Downarrow n`. Recover its last rule. Label the two premise results $`n_1` and $`n_2`. Which fact about $`n` comes from the rule itself? What further equality comes from applying the induction hypothesis to each premise? Combine the three equalities to compute $`\operatorname{eval}\left( {e,s} \right)`.
2. *Given the tree* $`e`. The goal is a derivation of $`s \vdash e \Downarrow \operatorname{eval}\left( {e,s} \right)`. Write the two child judgments that structural induction supplies, including their results. Use the addition rule to assemble them and check the result at the root against the goal.

*Proof review · 20 minutes.* Test the two implications. Consider two independent changes to Definition 1.5. In each case keep the evaluator and the other rules fixed, and take the least relation generated by the modified rules.

1. Delete the variable axiom. Can a derivable result disagree with the evaluator? Does every expression still have a derivation? Test $`\operatorname{var}(x)`.
2. Restore the variable axiom and add an axiom allowing $`\operatorname{lit}(0)` to evaluate to $`1` in any store. Does every computed result still have a derivation? Does every derivation give the computed result? Test $`\operatorname{lit}(0)`.

*Facilitator’s hint.* Point to the left column if someone assumes all evaluations exist. That proof starts with a derivation already in hand. In the right column, ask which rule the speaker can actually place at the root. The instructor can give this hint without taking over the induction.

# Solutions and Further Reading
%%%
tag := "ch01-s9"
number := false
%%%

*Reading for the Seminar.* Deleting the variable axiom leaves a subset of the original derivations. Every remaining derivation therefore gives the evaluator’s result, by the forward implication of Theorem 1.3 for the original rules. But no remaining rule concludes a judgment about $`\operatorname{var}(x)`, although $`\operatorname{eval}\left( {\operatorname{var}(x),s} \right) = s(x)`. Thus the reverse implication fails.

Adding the extra axiom preserves every original derivation. The reverse implication still holds. The new axiom derives $`s \vdash \operatorname{lit}(0) \Downarrow 1`, while $`\operatorname{eval}\left( {\operatorname{lit}(0),s} \right) = 0`. Thus the forward implication fails, and the original literal axiom gives a second result for this same tree and store.

*1.1.* The evaluation equations give $`\operatorname{eval}\left( {e,s} \right) = 2 + \left( {4 + 5} \right) = 11`. The free-variable equations give $`\operatorname{FV}(e) = \left\{ x \right\} \cup \left( {\varnothing \cup \left\{ z \right\}} \right) = \left\{ {x,z} \right\}`. Since $`y \notin \operatorname{FV}(e)`, Corollary 1.2 gives $`\operatorname{eval}\left( {e,s\left\lbrack {y\mapsto - 1} \right\rbrack} \right) = 11`.

*1.2.* Write the coordinates in the order $`\left( {x,y} \right)` and give every other name value zero. The stores $`\left( {1,2} \right)` and $`\left( {1,3} \right)` agree at $`x` but yield $`3` and $`4`. The stores $`\left( {1,2} \right)` and $`\left( {2,1} \right)` both yield $`3`, although they disagree at both free names. Thus equal results at two stores do not imply agreement on the free variables.

*1.3.* A literal has occurrence count zero. A variable leaf has count one if it carries $`x` and zero otherwise. At an addition, add the two counts. For a literal, the value changes by zero. For a variable, updating the store changes its value by $`k` exactly when the leaf carries $`x`. For an addition, the two induction hypotheses say the changes in its children are $`k \cdot m_{x}\left( e_{1} \right)` and $`k \cdot m_{x}\left( e_{2} \right)`. Adding these changes gives $`k \cdot m_{x}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)} \right)`.

Lemma 1.1 proves sufficiency of $`\operatorname{FV}(e)`. If a sufficient set $`S` omits some $`x \in \operatorname{FV}(e)`, then the occurrence count at $`x` is positive. Take any store and increase only its value at $`x` by one. The stores agree on $`S` but the equation just proved gives different evaluation results. This contradicts sufficiency. Therefore $`\operatorname{FV}(e) \subseteq S` for every sufficient $`S`.

*1.4.* The equation is $`\operatorname{eval}\left( {\operatorname{neg}(e),s} \right) = - \operatorname{eval}\left( {e,s} \right)`. The new rule is

$$`\frac{s \vdash e \Downarrow n_1}{s \vdash \operatorname{neg}(e) \Downarrow - n_1}.`

Given a derivation ending with that rule, the induction hypothesis for its premise gives $`\operatorname{eval}\left( {e,s} \right) = n_1`. The new equation yields the conclusion. Conversely, structural induction supplies a derivation with result $`\operatorname{eval}\left( {e,s} \right)` for the child. Apply the new rule once to construct the goal derivation.

*Further problem.* The variable `x` occurs twice in `x − x`, yet its value is zero in every store. To decide whether a name matters, assign each name a signed integer coefficient. Its coefficient in a literal is zero. In a variable leaf it is one when the names agree and zero otherwise. Add the coefficients at an addition node and subtract the right coefficient from the left at a subtraction node.

Fix a name and two stores that agree elsewhere, and let `d` be the second store's value at that name minus the first store's value there. Structural induction gives a stronger statement: the second evaluation minus the first is the coefficient times `d`. For a same-name leaf the difference is exactly `d`; at a subtraction node the two induction hypotheses give `a*d − b*d = (a−b)*d`. The literal, other-name, and addition cases follow directly from their evaluation equations. If the coefficient vanishes, the difference always vanishes. If it is nonzero, choose a store and increase that coordinate by one. The values then differ by the nonzero coefficient. This calculation also explains why the coincidence lemma (Lemma 1.1) holds in the full language although free variables need not be essential.

*Further reading · Syntax and meaning.*

*Comparison with TAPL.* In §§3.2–3.3 Pierce builds Boolean and natural-number terms inductively. A proof about a conditional has a hypothesis for each of its three immediate subterms. Our grammar has two binary constructors, so each binary induction step has two hypotheses. To recover the induction principle for a new grammar, inspect the recursive arguments of each constructor.

*The evaluator in Concrete Semantics.* In [_Concrete Semantics_, §§3.1.1–3.1.2, pp. 27–29](https://concrete-semantics.org/), Nipkow and Klein write N, V and Plus for the literal, variable and addition constructors. Their function aval first takes a tree, then a store. For example, aval (Plus (V x) (N 4)) s evaluates the tree from Example 1.1 in store s. It computes $`s(x)+4`. Section 1.2 defines the same style of evaluator for our four constructors. [Companion theory, AExp, definition of aval.](https://isabelle.in.tum.de/library/HOL/HOL-IMP/AExp.html)

*Compositional interpretation.* In §§1.1–1.2 Reynolds interprets the constructors of predicate logic by operations on their meanings. For our arithmetic language, the meaning of an expression that may contain variables is a function from stores to integers. Write $`\llbracket e\rrbracket(s) = \operatorname{eval}\left( {e,s} \right)`. The meaning of a literal is the constant function with value $`n`. A variable denotes the function that looks up its name. To interpret addition, take two such functions $`f,g:\Sigma\rightarrow{\mathbb{Z}}` and form their pointwise sum, the function sending $`s` to $`f(s) + g(s)`. Then

$$`\llbracket \operatorname{add}\left( {e_{1},e_{2}} \right)\rrbracket(s) = \llbracket e_{1}\rrbracket(s) + \llbracket e_{2}\rrbracket(s).`

This is precisely the third evaluation equation. It is compositional because the two functions $`\llbracket e_{1}\rrbracket` and $`\llbracket e_{2}\rrbracket` supply everything needed to interpret their sum. As a consequence, $`\operatorname{var}(x)` and $`\operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(0)} \right)` are distinct syntax trees with the same meaning: for every $`s`, the equation reduces the second value to $`s(x) + 0 = s(x)`. Equality of meanings requires equality at every store; agreement in a single calculation would leave the other stores open. In the same way $`x+y` and $`y+x` have the same meaning by commutativity of integer addition, applied once at the root, while the two trees remain distinct.

*Further reading · Free variables.*

An expression is *closed* if its set of free variables is empty. Any two stores agree on the empty set, which has no name at which they could differ. So by Lemma 1.1 a closed expression has the same value in every store.

Only the restriction of a store to the finite set of free names matters. Any two extensions of this restricted assignment to all names give the same value: take the two extensions as the stores in the coincidence lemma. Thus an evaluator supplied with a full store also defines a value from just the restricted assignment, and choosing zero or any other default for the missing names gives the same result. This is why a later data-flow analysis can reason about sets of names even though the execution rules operate on complete stores.

*Further reading · Judgments.*

*Notation in the source.* Winskel writes $`\langle a,\sigma\rangle \rightarrow n` (§2.2, p. 13) and $`\langle c,\sigma\rangle \rightarrow \sigma'` (§2.4, p. 19) for complete expression and command evaluations. Here the double downward arrow serves that role in both judgments. His addition rule makes the sum of the two premise results a side condition on the conclusion. Definition 1.5 writes that sum directly in the conclusion. [Winskel, §§2.2, 2.4](https://doi.org/10.7551/mitpress/3054.001.0001)

The BigStep chapter of _PLFA_ uses $`\gamma \vdash M \Downarrow V` for evaluation of a lambda term. Its $`\gamma` is an environment that binds variables to closures (terms paired with environments for their free variables). In our imperative language the object supplied to the left of the turnstile is the current store of integer variables. [PLFA, BigStep](https://plfa.github.io/BigStep/#big-step-evaluation)

*Least closed subset.* The triples with derivations are closed under the rules, since a rule placed under derivations of its premises gives a derivation of its conclusion. Every closed subset contains them: it contains the conclusion of each axiom at the leaves of a derivation, and then each conclusion below, down to the root. So they form the least closed subset, as §1.4 states.

*A direct proof of determinacy.* In §3.2, Proposition 3.3, Winskel proves uniqueness directly from the rules by structural induction on the expression. Here is the addition case for our grammar. Fix $`e = \operatorname{add}\left( {e_{1},e_{2}} \right)` and suppose two derivations have results $`n` and $`n'` in the same store. Inverting their last rules produces child results $`n_1,n_2` and $`n_1',n_2'`, with $`n = n_1 + n_2` and $`n' = n_1' + n_2'`. The induction hypothesis for $`e_{1}` applies to its two evaluations in this store, so $`n_1 = n_1'`. The hypothesis for $`e_{2}` gives $`n_2 = n_2'`. Hence $`n = n'`. The axiom cases force the results to be the literal or the value stored at the given name. This proof establishes uniqueness even before an evaluator has been defined. Existence is a separate assertion, supplied here by the reverse direction of Theorem 1.3.

Induction on the expression works here because each premise of a rule concerns a child of the expression in the conclusion. The forward direction of Theorem 1.3 could be proved the same way. In Session 2 a premise of the loop iteration rule concerns the same loop in a new store: a smaller derivation, but not a smaller command. Induction on derivations still gives a hypothesis for that premise, and induction on command syntax does not.

*Further reading · Sources.*

Glynn Winskel, [_The Formal Semantics of Programming Languages: An Introduction_](https://doi.org/10.7551/mitpress/3054.001.0001) (MIT Press, 1993). In chapter 2, [§§2.1–2.2, pp. 11–16](https://doi.org/10.7551/mitpress/3054.001.0001), read the formation rules, the definition of a store and the evaluations of a number, a location and a sum. Our grammar includes subtraction and takes strings as variable names. In chapter 3, [§3.2, Proposition 3.3, p. 30](https://doi.org/10.7551/mitpress/3054.001.0001), trace the two derivations for a sum. Proposition 3.3 proves determinacy, and Exercise 3.4 on the same page asks for existence. Theorem 1.3 of this chapter supplies both facts by relating the rules to a function. The corresponding graph equality is Winskel’s §5.3, Lemma 5.3.

Tobias Nipkow and Gerwin Klein, [_Concrete Semantics with Isabelle/HOL_](https://concrete-semantics.org/), chapter 3, §§3.1.1–3.1.2, pp. 27–29. For §1.2, read from the datatype for arithmetic expressions to the equations for aval. [Isabelle theory and worked evaluations.](https://isabelle.in.tum.de/library/HOL/HOL-IMP/AExp.html)

John C. Reynolds, [_Theories of Programming Languages_](https://www.cs.cmu.edu/~jcr/tpl-toc.html) (Cambridge University Press, 1998), chapter 1, §§1.1–1.2, pp. 1–11, and §1.4, starting p. 15. For §1.2 and [Session 11, §11.1](chapter-11/index.html#ch11-s1). Follow how an interpretation is specified on constructors. For binding, track which variable occurrences remain free after substitution.

Benjamin C. Pierce, [_Types and Programming Languages_](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf) (MIT Press, 2002), chapter 3, §§3.2–3.3, pp. 26–31. Optional for §1.1. Derive the induction cases from Pierce’s grammar, then do the same for Definition 1.1.

Xavier Leroy’s _Compiler Verification_ course, Lean 4 port by Wojciech Różowski. [Arithmetic expressions and free variables](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L14-L64). Optional for §1.3. Compare the coincidence proof there with the agreement hypothesis of Lemma 1.1.

# Sources and Formalization
%%%
tag := "ch01-notes"
number := false
%%%

* *Lemma 1.1.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Corollary 1.2.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 1.3.* Formulated in this book. Corresponds to Winskel Lemma 5.3. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Corollary 1.4.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Definition 1.5.* Formulated in this book.
