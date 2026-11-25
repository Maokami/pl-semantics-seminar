import VersoManual
import PLBook.IMP.Arithmetic

open Verso.Genre Manual

#doc (Manual) "Arithmetic Expressions" =>
%%%
tag := "ch01"
file := "chapter-01"
%%%

* *Definitions.* Arithmetic expressions, stores, the evaluation function and the evaluation judgment (Definitions 1.1–1.3 and 1.5; [IMP language card A.1–A.3](imp-card/index.html)).
* *New terms.* Inference rule, derivation, inversion, structural induction, induction on derivations. [Glossary and label key](glossary/index.html)
* *Theorem 1.3 \[This book\] \[Checked\].* For every expression $`e`, store $`s` and integer $`n`, $`s\vdash e\Downarrow n` if and only if $`\mathrm{eval}(e,s)=n`.
* *Source.* The syntax, stores and evaluation function follow the arithmetic fragment of Leroy’s IMP. The four evaluation rules are formulated here on that syntax. \[Corresponding: Winskel Lemma 5.3\] Winskel identifies the graph of an expression’s meaning with the pairs of stores and integers justified by his rules. [Formalization](imp-card/index.html#imp-sources) · [Winskel, §5.3, pp. 61–62](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)
* *Board case.* Addition in both directions. In one direction the two children of a derivation give equalities. In the other the two children of an expression give derivations.
* *Proof outline.* From a derivation with result $`n`, prove that the evaluator returns $`n` by induction on that derivation. For the converse, construct a derivation of the computed result by structural induction on the expression.
* *Starting point.* We begin with a finite expression tree and a store that gives values to its variable names.

The expression $`x + 4` has value $`7` when $`x` holds $`3`, and value $`12` when $`x` holds $`8`. The expression is the same tree in both calculations. One way to evaluate the tree is to compute its value from the leaves up. Another is to give rules for justifying a proposed value. We shall prove that a proposed value has such a justification exactly when the computation returns it.

# Abstract Syntax and Stores
%%%
tag := "ch01-s1"
%%%

*Definition 1.1 (Arithmetic expressions).* Let $`x` range over variable names (strings) and $`n` over mathematical integers. An expression is a finite tree built with four constructors:

$$`e ::= n \mid x \mid (e_1+e_2) \mid (e_1-e_2).`

A minus sign at an internal node denotes binary subtraction. A negative integer at a leaf is a literal.

The symbol $`::=` introduces alternatives, separated by vertical bars. A *constructor* builds a tree. We write $`\operatorname{lit}(n)`, $`\operatorname{var}(x)`, $`\operatorname{add}(e_1,e_2)` and $`\operatorname{sub}(e_1,e_2)` when we want to name the constructors explicitly. Every expression has exactly one outermost constructor, and the children of a binary node are uniquely determined and ordered. We use $`x + 4` as a concrete notation for $`\operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(4)} \right)`. Write $`V=\mathrm{Name}` for the set of strings and $`E` for the set of expression trees.

*Structural induction* proves a property $`P(e)` by considering each constructor. At a binary node, the claims $`P(e_1)` and $`P(e_2)` for its two immediate children are the *induction hypotheses*.

For example, to prove $`\forall e\in E,\ P(e)`, prove $`P(n)` and $`P(x)` for all leaves. For arbitrary $`e_1,e_2`, assume $`P(e_1)` and $`P(e_2)` and prove both $`P(e_1+e_2)` and $`P(e_1-e_2)`. Each child is smaller than its parent. A leaf has height zero, and a binary node has height one greater than the maximum of its children's heights.

*Definition 1.2 (Stores).* A store is a total function $`s:\mathrm{Name}\to\mathbb Z`. Write $`\Sigma` for the set of stores. The update $`s[x\mapsto n]` is the function whose value at $`x` is $`n` and whose value at each other name $`y` is $`s(y)`. Equality of stores means equality at every name.

For example, let $`s` return $`3` at $`x` and $`0` everywhere else. The symbol $`x` is an element of $`V`, the tree $`\operatorname{var}(x)` is an element of $`E`, and the value $`s(x) = 3` is an element of $`\mathbb{Z}`. Only the last of these depends on the chosen store.

A store supplies a value for every string, including strings absent from a particular expression. The tree for `x + x` contains two occurrences even when the two variable labels are equal. Later the recursion computing a value will visit both children. Counting variable names in a set will give a different account of the same tree.

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

Here $`\mathrm{eval}:E\times\Sigma\to\mathbb Z`. On the left of the third equation, $`+` constructs a tree. On the right it adds two integers. Both recursive calls use the given store. For each fixed store, the first two clauses determine the values at height zero. The two binary clauses determine the values at greater heights from values already determined at smaller heights. The equations therefore determine a unique total function.

*Example 1.1.* If $`s(x) = 3`, then

$$`\begin{matrix} {\operatorname{eval}\left( {\operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(4)} \right),s} \right)} & {= \operatorname{eval}\left( {\operatorname{var}(x),s} \right) + \operatorname{eval}\left( {\operatorname{lit}(4),s} \right)} \\ & {= 3 + 4 = 7.} \end{matrix}`

# Free Variables and the Coincidence Lemma
%%%
tag := "ch01-s3"
%%%

*Definition 1.4 (Free variables).* The function $`\operatorname{FV}:E\rightarrow\mathcal{P}(V)` assigns a set of variable names to each expression. Here $`\mathcal{P}(V)` is the set of all subsets of $`V`, $`\varnothing` is the empty set, and $`\cup` denotes set union. Define

$$`\begin{aligned}
\mathrm{FV}(n)&=\varnothing & \mathrm{FV}(x)&=\{x\}\\
\mathrm{FV}(e_1+e_2)&=\mathrm{FV}(e_1)\cup\mathrm{FV}(e_2)\\
\mathrm{FV}(e_1-e_2)&=\mathrm{FV}(e_1)\cup\mathrm{FV}(e_2).
\end{aligned}`

An occurrence is one leaf labelled with a variable name. A *binder* introduces a local name within a specified part of a term, its scope. An occurrence is *free* if no enclosing binder binds it. Our four constructors introduce no binders, so every variable occurrence is free. Two occurrences of the same name contribute one element to the set. For $`S \subseteq V`, let $`s \rvert_{S}:S\rightarrow{\mathbb{Z}}` denote the restriction of $`s` to $`S`. Thus $`s \rvert_{S} = t\rvert_{S}` holds exactly when $`s(x) = t(x)` for every $`x \in S`.

For $`x-3`, two stores that agree at $`x` give the same answer, whatever values they assign to other names.

*Lemma 1.1 (Coincidence) \[This book\] \[Checked\].* For every $`e \in E` and $`s,t \in \Sigma`,

$$`s \rvert_{\operatorname{FV}{(e)}} = t \rvert_{\operatorname{FV}{(e)}}\quad\Longrightarrow\quad\operatorname{eval}\left( {e,s} \right) = \operatorname{eval}\left( {e,t} \right).`

*Proof.* By structural induction on $`e` we prove

$$`P(e)\ \coloneqq\ \forall s,t\in\Sigma,\quad s|_{\mathrm{FV}(e)}=t|_{\mathrm{FV}(e)}
\ \Longrightarrow\ \mathrm{eval}(e,s)=\mathrm{eval}(e,t).`

Fix $`s` and $`t` that agree on $`\mathrm{FV}(e)`.

If $`e=n`, both evaluations give $`n`. If $`e=x`, then $`\mathrm{FV}(e)=\{x\}`, so $`s(x)=t(x)` gives the required equality.

If $`e=e_1+e_2`, the induction hypotheses are $`P(e_1)` and $`P(e_2)`. Since $`\mathrm{FV}(e)=\mathrm{FV}(e_1)\cup\mathrm{FV}(e_2)`, the stores $`s,t` agree on $`\mathrm{FV}(e_1)` and on $`\mathrm{FV}(e_2)`. Applying $`P(e_1)` and $`P(e_2)` at $`s,t` gives $`\mathrm{eval}(e_i,s)=\mathrm{eval}(e_i,t)` for $`i=1,2`. Therefore

$$`\begin{aligned}\mathrm{eval}(e_1+e_2,s)&=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)\\ &=\mathrm{eval}(e_1,t)+\mathrm{eval}(e_2,t)\\ &=\mathrm{eval}(e_1+e_2,t).\end{aligned}`

If $`e=e_1-e_2`, $`\mathrm{FV}(e)` is the same union, so the same two applications of $`P(e_1)` and $`P(e_2)` give equal operand values. Subtract them in their original order to obtain

$$`\mathrm{eval}(e,s)=\mathrm{eval}(e_1,s)-\mathrm{eval}(e_2,s)
=\mathrm{eval}(e_1,t)-\mathrm{eval}(e_2,t)=\mathrm{eval}(e,t).\quad\square`

*Corollary 1.2 (Store update) \[This book\] \[Checked\].* For every $`e\in E`, $`s\in\Sigma`, $`x\in V` and $`n\in\mathbb Z` with $`x\notin\mathrm{FV}(e)`,

$$`\operatorname{eval}\left( {e,s\left\lbrack {x\mapsto n} \right\rbrack} \right) = \operatorname{eval}\left( {e,s} \right).`

*Proof.* The update leaves every variable in $`\operatorname{FV}(e)` unchanged. Apply Lemma 1.1.$`\square`

An expression is *closed* if its set of free variables is empty. Any two stores agree on the empty set, so a closed expression has the same value in every store by Lemma 1.1.

# Evaluation Judgments
%%%
tag := "ch01-s4"
%%%

Definition 1.3 computes a value. We can also specify which triples of store, expression, and integer constitute valid evaluations. Write $`s \vdash e \Downarrow n` for the *judgment* that $`e` evaluates to $`n` in $`s`. The symbol $`\Downarrow` here represents a complete evaluation.

The turnstile $`\vdash` separates the input store from the expression being evaluated. In $`s\vdash e\Downarrow n` the result is an integer.

*Definition 1.5 (Evaluation judgment) \[This book\].* Write $`s\vdash e\Downarrow n` when the judgment has a finite derivation by the following rules. An *inference rule* puts its premises above the line and its conclusion below. A rule with no premises is an *axiom*. A *derivation* is a finite tree of rule applications whose root is the judgment proved and whose children derive the premise judgments. If $`D` is a derivation whose root is the judgment $`J`, we write $`D:J` and say that $`D` derives $`J`.

$$`\frac{}{s\vdash n\Downarrow n}\qquad\frac{}{s\vdash x\Downarrow s(x)}`

$$`\frac{s\vdash e_1\Downarrow m\quad s\vdash e_2\Downarrow n}{s\vdash e_1+e_2\Downarrow m+n}
\qquad\frac{s\vdash e_1\Downarrow m\quad s\vdash e_2\Downarrow n}{s\vdash e_1-e_2\Downarrow m-n}`

Equivalently, these triples form the least subset of $`\Sigma\times E\times\mathbb Z` closed under the four rules. A subset is closed under a rule if it contains the conclusion whenever it contains all the premises. “Least” refers to inclusion. Indeed, the triples with finite derivations are closed under the rules by adjoining a root. Every closed subset contains all such triples, by induction from the leaves to the root.

*Example 1.2.* Take a store $`s` with $`s(x) = 3`. The two leaves justify the premises of the addition rule.

$$`\frac{\frac{}{s \vdash \operatorname{var}(x) \Downarrow 3}\quad\frac{}{s \vdash \operatorname{lit}(4) \Downarrow 4}}{s \vdash \operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(4)} \right) \Downarrow 7}`

Conversely, suppose the same addition evaluates to $`n`. Only the addition rule has that outer constructor in its conclusion. Its premises require the values $`3` and $`4`, so $`n = 7`. *Inversion* recovers the possible last rules of a derivation, together with the premises and equalities forced by their conclusions.

Closure alone would admit additional judgments. For example, the set of all triples is closed under every rule above. In that set $`s \vdash \operatorname{lit}(4) \Downarrow 9` would also hold. No finite derivation can have that conclusion. Its last rule would have to be the literal axiom, whose result for this leaf is $`4`. Taking the least closed subset makes inversion valid. For an arbitrary sum, inspecting its last rule yields two particular integers together with derivations for them. Those witnesses come from the supplied derivation.

# Correspondence and Determinacy
%%%
tag := "ch01-s5"
%%%

For fixed $`e` and $`s`, Definition 1.3 supplies an integer. Definition 1.5 gives a test of what can be justified by the rules. The following theorem identifies the set of justifiable results as the singleton containing the computed integer.

*Theorem 1.3 (Correspondence) \[This book\] \[Checked\].* For every $`e \in E`, $`s \in \Sigma`, and $`n \in {\mathbb{Z}}`,

$$`s \vdash e \Downarrow n\quad\Longleftrightarrow\quad\operatorname{eval}\left( {e,s} \right) = n.`

*Proof (from a derivation to a value).* Use *induction on derivations*: for each possible last rule assume the claim for its immediate premise derivations and prove it for the conclusion. For $`D:s\vdash e\Downarrow n`, the statement to be proved (the *induction property*) is $`P(D)\coloneqq\mathrm{eval}(e,s)=n`. In the literal and variable cases the conclusion agrees with the corresponding equation of Definition 1.3. For addition:

1. The last rule is the addition rule with $`m:=a` and $`n:=b`. Its premises are $`D_1:s\vdash e_1\Downarrow a` and $`D_2:s\vdash e_2\Downarrow b`. Its conclusion is $`s\vdash e_1+e_2\Downarrow a+b`, so $`e=e_1+e_2` and $`n=a+b`. Here $`a` and $`b` name the operand values, and $`n` names the result at the root.
2. The two induction hypotheses are $`P(D_1):\mathrm{eval}(e_1,s)=a` and $`P(D_2):\mathrm{eval}(e_2,s)=b`.
3. By the addition equation of Definition 1.3 and the two hypotheses, $`\mathrm{eval}(e_1+e_2,s)=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)=a+b=n`.

For subtraction, the last rule fixes $`n=a-b`. Applying the two induction hypotheses in the subtraction equation gives $`\mathrm{eval}(e_1-e_2,s)=a-b=n`.

*Proof (from a value to a derivation).* Fix a store $`s`. By structural induction on $`e` we prove $`Q(e)\coloneqq s\vdash e\Downarrow\mathrm{eval}(e,s)`. For a literal use the literal axiom. For a variable use the variable axiom. For addition:

1. The hypotheses are $`Q(e_1):s\vdash e_1\Downarrow\mathrm{eval}(e_1,s)` and $`Q(e_2):s\vdash e_2\Downarrow\mathrm{eval}(e_2,s)`.
2. Adjoin the addition rule with $`m:=\mathrm{eval}(e_1,s)` and $`n:=\mathrm{eval}(e_2,s)` at the root of these two derivations. Its result is $`\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)`.
3. By Definition 1.3 this integer is $`\mathrm{eval}(e_1+e_2,s)`, as required.

For subtraction, use the subtraction rule on the same two child judgments. Its result is $`\mathrm{eval}(e_1,s)-\mathrm{eval}(e_2,s)=\mathrm{eval}(e_1-e_2,s)`. Finally, if $`\mathrm{eval}(e,s)=n`, the derivation just constructed has the required result $`n`. $`\square`

The final sentence of the reverse proof matters. The induction on syntax produces a derivation whose result is *the computed integer*. The theorem was stated for *any* candidate integer. The given equality identifies the candidate with the result of the constructed derivation. This is where the result of the computation enters the reverse direction.

*Corollary 1.4 (Unique result) \[This book\] \[Checked\].* For every $`e\in E` and $`s\in\Sigma` there is an integer $`n` with $`s\vdash e\Downarrow n`, and if also $`s\vdash e\Downarrow m` then $`n=m`. In words, the evaluation judgment is *total* (every expression has a result in every store) and *deterministic* (it has at most one result).

*Proof.* Take $`n=\mathrm{eval}(e,s)`. The reverse direction of Theorem 1.3 gives $`s\vdash e\Downarrow n`. If $`s\vdash e\Downarrow m`, the forward direction gives $`\mathrm{eval}(e,s)=m`, so $`n=m`. $`\square`

The forward proof begins with evidence of evaluation and examines its last rule. The reverse proof begins with syntax and constructs that evidence. In this language an addition has exactly one premise per child. For a command that repeats its body, one premise may concern the very same command in a new store. It is then a smaller premise derivation even though the command itself has the same syntax.

# Substitution · Session 11 reading
%%%
tag := "ch01-s6"
number := false
%%%

Read this section in Session 11, when assignment is related to substitution in an assertion.

*Definition 1.6 (Substitution).* For $`e,t \in E` and $`x \in V`, write $`e\left\lbrack {t/x} \right\rbrack` for the tree obtained by replacing each occurrence of $`x` in $`e` with $`t`. The replacement is simultaneous. Variable occurrences inside the inserted tree are left as they were.

$$`\begin{matrix} {\operatorname{lit}(n)\left\lbrack {t/x} \right\rbrack} & {= \operatorname{lit}(n)} \\ {\operatorname{var}(y)\left\lbrack {t/x} \right\rbrack} & {= \left\{ \begin{matrix} {t\ } & {\text{if}\ y = x} \\ {\operatorname{var}(y)\ } & {\text{if}\ y \neq x} \end{matrix} \right.} \\ {\operatorname{add}\left( {e_{1},e_{2}} \right)\left\lbrack {t/x} \right\rbrack} & {= \operatorname{add}\left( {e_{1}\left\lbrack {t/x} \right\rbrack,e_{2}\left\lbrack {t/x} \right\rbrack} \right).} \end{matrix}`

For subtraction, $`(e_1-e_2)[t/x]=e_1[t/x]-e_2[t/x]`.

*Example 1.3.* Substitute $`x + 1` for $`x` in $`x + x`. The resulting expression is $`\left( {x + 1} \right) + \left( {x + 1} \right)`. If $`s(x) = 2`, it evaluates to $`6`. Evaluating the original $`x + x` in the updated store $`s\left\lbrack {x\mapsto 3} \right\rbrack` gives the same result. The value assigned to $`x` by this update is computed in the original store.

*Theorem 1.5 (Substitution lemma) \[This book\] \[Paper proof only: proof in this section\].* For $`e,t \in E`, $`x \in V` and $`s \in \Sigma`,

$$`\operatorname{eval}\left( {e\left\lbrack {t/x} \right\rbrack,s} \right) = \operatorname{eval}\left( {e,s\left\lbrack {x\mapsto\operatorname{eval}\left( {t,s} \right)} \right\rbrack} \right).`

*Proof.* Set $`u = \operatorname{eval}\left( {t,s} \right)` and $`s' = s\left\lbrack {x\mapsto u} \right\rbrack`. Use structural induction on $`e`. For a literal, both sides give its integer. For $`\operatorname{var}(y)` with $`y = x`, the left side evaluates the inserted tree to $`u` and the right side reads $`s'(x) = u`. When $`y \neq x`, the original leaf remains, and $`s'(y) = s(y)`. For an addition, the definitions of substitution and evaluation give

$$`\begin{matrix} {\operatorname{eval}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)\left\lbrack {t/x} \right\rbrack,s} \right)} & {= \operatorname{eval}\left( {e_{1}\left\lbrack {t/x} \right\rbrack,s} \right) + \operatorname{eval}\left( {e_{2}\left\lbrack {t/x} \right\rbrack,s} \right)} \\ & {= \operatorname{eval}\left( {e_{1},s'} \right) + \operatorname{eval}\left( {e_{2},s'} \right)} \\ & {= \operatorname{eval}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right),s'} \right).} \end{matrix}`

The middle equality uses the two induction hypotheses. For subtraction the same two equalities identify the minuends and the subtrahends. Subtracting gives the desired equality.$`\square`

In an imperative language an assignment to $`x` changes the store in which subsequent expressions are evaluated. The lemma gives a way to calculate their values in the original store by substituting the right-hand side of the assignment.

*Substitution under a binder.* Reynolds §1.4 treats languages with binding. For example, let $`P` be a predicate of two integers and consider the formula $`\forall y,P\left( {x,y} \right)` with $`x \neq y`. Substituting the free variable $`y` for $`x` should preserve the inserted variable’s dependence on the surrounding store. A literal replacement gives $`\forall y,P\left( {y,y} \right)`, where the quantifier captures it. Choose a fresh name $`z`, rename the bound variable, and then substitute to get $`\forall z,P\left( {y,z} \right)`. Definition 1.6 needs no renaming step because none of our arithmetic constructors binds a name.

Successive substitutions can expose a dependency between two assignments. Let the expression to observe be `x + y`, with distinct names, and consider the instructions `x := y; y := 1`. Starting from a store giving `x = 9` and `y = 4`, the final expression has value 5. To express the observation in the original store, eliminate the *later* assignment first. Replacing `y` by 1 in the observed expression gives `x + 1`. Now eliminate the earlier assignment by replacing `x` by `y`, giving `y + 1`. Its value at the original store is indeed 5.

Doing the two textual replacements in program order would first give `y + y` and then `1 + 1`. The loss of the old lookup of `y` identifies the error. The instructions update stores in their execution order. An observation of the final store is transported in the opposite direction, from the final observation back across each update. Each transport step is one application of the substitution lemma. This same calculation will reappear for a Boolean observation when a postcondition is moved back across a sequence of assignments.

# Exercises
%%%
tag := "ch01-s7"
number := false
%%%

*1.1 (Evaluation).* Let $`e = \operatorname{add}\left( {\operatorname{var}(x),\operatorname{add}\left( {\operatorname{lit}(4),\operatorname{var}(z)} \right)} \right)`, with $`x,y,z` distinct. Suppose $`s(x) = 2`, $`s(y) = 9`, and $`s(z) = 5`. Compute $`\operatorname{eval}\left( {e,s} \right)` and $`\operatorname{FV}(e)` using their defining equations. Use Corollary 1.2 to determine $`\operatorname{eval}\left( {e,s\left\lbrack {y\mapsto - 1} \right\rbrack} \right)`.

*1.2 (Coincidence).* Let $`e = \operatorname{add}\left( {\operatorname{var}(x),\operatorname{var}(y)} \right)`, with $`x \neq y`.

1. Give two stores that agree at $`x` and yield different values for $`e`.
2. Give two stores that disagree at both $`x` and $`y` and yield the same value for $`e`. State the converse of Lemma 1.1 and explain why this example refutes it.

*1.3 (Variable occurrences).* Write $`{\mathbb{N}} = \left\{ {0,1,2,\ldots} \right\}` for the natural numbers. Let $`E_+` be the expressions built from literals, variables and addition. For each $`x \in V`, define $`m_{x}:E_+\rightarrow{\mathbb{N}}` by structural recursion so that $`m_{x}(e)` counts the occurrences of $`x` in $`e`. Prove by structural induction that for every $`e \in E_+`, every $`s \in \Sigma`, and every $`k \in {\mathbb{Z}}`,

$$`\operatorname{eval}\left( {e,s\left\lbrack {x\mapsto s(x) + k} \right\rbrack} \right) = \operatorname{eval}\left( {e,s} \right) + k \cdot m_{x}(e).`

Call $`S \subseteq V` sufficient for $`e` if agreement on $`S` implies equal evaluations of $`e`. Use Lemma 1.1 and the equation with $`k = 1` to show that $`\operatorname{FV}(e)` is the least sufficient set under inclusion.

*1.4 (Derivations).* Extend the grammar with $`\operatorname{neg}(e)` for integer negation. Add one equation to Definition 1.3 and one rule to Definition 1.5. Prove the new case in each direction of Theorem 1.3. Write down exactly what your induction hypothesis supplies in each proof.

*1.5 (Substitution · Session 11).* For distinct names $`x` and $`y`, take $`e = x + y` and $`t = y + 1`. Compare $`e\left\lbrack {t/x} \right\rbrack` and $`e\left\lbrack {x/y} \right\rbrack` in a store with $`s(x) = 4` and $`s(y) = 2`. For each substitution identify the single store update that yields the same result on the original tree.

*Further problem.* Now include binary subtraction, as in Definition 1.1. Say that a name is essential to an expression if two stores differing only at that name can give different values. Does membership in the set of free variables characterize essential names? Give an exact decision procedure for the full language and justify both directions.

# Seminar Worksheet
%%%
tag := "ch01-s8"
number := false
%%%

*Board setup.* Copy the sum rule from §1.4, the sum equation from §1.2, and Theorem 1.3. Cover the printed proof and rehearse the two constructions below. Participants need the theorem and these two definitions in front of them.

*0–10 minutes · Example.* Fix $`s(x) = 3`. Ask one participant to compute $`x + 4` and another to justify the result by drawing the two axioms and the rule that uses them. Where does the number $`7` enter the derivation? Example 1.2 gives the board solution.

*10–40 minutes · Correspondence.* Divide the board into two columns. Use $`e = \operatorname{add}\left( {e_{1},e_{2}} \right)` in both. Write the given information at the top and the goal at the bottom. Leave room for participants to supply the intermediate steps.

1. *Given a derivation of* $`s \vdash e \Downarrow n`. Recover its last rule. Label the two premise results $`a` and $`b`. Which fact about $`n` comes from the rule itself? What further equality comes from applying the induction hypothesis to each premise? Combine the three equalities to compute $`\operatorname{eval}\left( {e,s} \right)`.
2. *Given the tree* $`e`. The goal is a derivation of $`s \vdash e \Downarrow \operatorname{eval}\left( {e,s} \right)`. Write the two child judgments that structural induction supplies, including their results. Use the sum rule to assemble them and check the result at the root against the goal.

*40–60 minutes · Testing the two implications.* Consider two independent changes to Definition 1.5. In each case keep the evaluator and the other rules fixed, and take the least relation generated by the modified rules.

1. Delete the variable axiom. Can a derivable result disagree with the evaluator? Does every expression still have a derivation? Test $`\operatorname{var}(x)`.
2. Restore the variable axiom and add an axiom allowing $`\operatorname{lit}(0)` to evaluate to $`1` in any store. Does every computed result still have a derivation? Does every derivation give the computed result? Test $`\operatorname{lit}(0)`.

*Facilitator’s hint.* Point to the left column if someone assumes all evaluations exist. That proof starts with a derivation already in hand. In the right column, ask which rule the speaker can actually place at the root. The instructor can give this hint without taking over the induction.

# Solutions
%%%
tag := "ch01-s9"
number := false
%%%

*Seminar worksheet.* Deleting the variable axiom leaves a subset of the original derivations. Every remaining derivation therefore gives the evaluator’s result, by the forward implication of Theorem 1.3 for the original rules. But no remaining rule concludes a judgment about $`\operatorname{var}(x)`, although $`\operatorname{eval}\left( {\operatorname{var}(x),s} \right) = s(x)`. Thus the reverse implication fails.

Adding the extra axiom preserves every original derivation. The reverse implication still holds. The new axiom derives $`s \vdash \operatorname{lit}(0) \Downarrow 1`, while $`\operatorname{eval}\left( {\operatorname{lit}(0),s} \right) = 0`. Thus the forward implication fails, and the original literal axiom gives a second result for this same tree and store.

*1.1.* The evaluation equations give $`\operatorname{eval}\left( {e,s} \right) = 2 + \left( {4 + 5} \right) = 11`. The free-variable equations give $`\operatorname{FV}(e) = \left\{ x \right\} \cup \left( {\varnothing \cup \left\{ z \right\}} \right) = \left\{ {x,z} \right\}`. Since $`y \notin \operatorname{FV}(e)`, Corollary 1.2 gives $`\operatorname{eval}\left( {e,s\left\lbrack {y\mapsto - 1} \right\rbrack} \right) = 11`.

*1.2.* Write the coordinates in the order $`\left( {x,y} \right)` and give every other name value zero. The stores $`\left( {1,2} \right)` and $`\left( {1,3} \right)` agree at $`x` but yield $`3` and $`4`. The stores $`\left( {1,2} \right)` and $`\left( {2,1} \right)` both yield $`3`, although they disagree at both free names. Thus equal results at two stores do not imply agreement on the free variables.

*1.3.* A literal has occurrence count zero. A variable leaf has count one if it carries $`x` and zero otherwise. At an addition, add the two counts. For a literal, the value changes by zero. For a variable, updating the store changes its value by $`k` exactly when the leaf carries $`x`. For an addition, the two induction hypotheses say the changes in its children are $`k \cdot m_{x}\left( e_{1} \right)` and $`k \cdot m_{x}\left( e_{2} \right)`. Adding these changes gives $`k \cdot m_{x}\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)} \right)`.

Lemma 1.1 proves sufficiency of $`\operatorname{FV}(e)`. If a sufficient set $`S` omits some $`x \in \operatorname{FV}(e)`, then the occurrence count at $`x` is positive. Take any store and increase only its value at $`x` by one. The stores agree on $`S` but the equation just proved gives different evaluation results. This contradicts sufficiency. Therefore $`\operatorname{FV}(e) \subseteq S` for every sufficient $`S`.

*1.4.* The equation is $`\operatorname{eval}\left( {\operatorname{neg}(e),s} \right) = - \operatorname{eval}\left( {e,s} \right)`. The new rule is

$$`\frac{s \vdash e \Downarrow a}{s \vdash \operatorname{neg}(e) \Downarrow - a}.`

Given a derivation ending with that rule, the induction hypothesis for its premise gives $`\operatorname{eval}\left( {e,s} \right) = a`. The new equation yields the conclusion. Conversely, structural induction supplies a derivation with result $`\operatorname{eval}\left( {e,s} \right)` for the child. Apply the new rule once to construct the goal derivation.

*1.5.* The first substitution produces $`\left( {y + 1} \right) + y`, with value $`\left( {2 + 1} \right) + 2 = 5`. Evaluating $`x + y` in $`s\left\lbrack {x\mapsto 3} \right\rbrack` gives the same value. The second produces $`x + x`, with value $`4 + 4 = 8`. Its corresponding store is $`s\left\lbrack {y\mapsto 4} \right\rbrack`. In both cases the value stored by the update is computed in the original store.

*Further problem.* The variable `x` occurs twice in `x − x`, yet its value is zero in every store. To decide whether a name matters, assign each name a signed integer coefficient. Its coefficient in a literal is zero. In a variable leaf it is one when the names agree and zero otherwise. Add the coefficients at an addition node and subtract the right coefficient from the left at a subtraction node.

Fix a name and two stores that agree elsewhere, and let `d` be the second store's value at that name minus the first store's value there. Structural induction gives a stronger statement: the second evaluation minus the first is the coefficient times `d`. For a same-name leaf the difference is exactly `d`; at a subtraction node the two induction hypotheses give `a*d − b*d = (a−b)*d`. The literal, other-name, and addition cases follow directly from their evaluation equations. If the coefficient vanishes, the difference always vanishes. If it is nonzero, choose a store and increase that coordinate by one. The values then differ by the nonzero coefficient. This calculation also explains why the original free-variable agreement lemma remains true in the full language.

# Annotated References
%%%
tag := "ch01-s10"
number := false
%%%

*Further reading on syntax and meaning.*

*Comparison with TAPL.* In §§3.2–3.3 Pierce builds Boolean and natural-number terms inductively. A proof about a conditional has a hypothesis for each of its three immediate subterms. Our grammar has two binary constructors, so each binary induction step has two hypotheses. To recover the induction principle for a new grammar, inspect the recursive arguments of each constructor.

A constructor determines which questions may be asked of a tree. Suppose a reader hands us an expression with a plus sign at its root. We may ask for its two ordered children. If the root is a numeral, we may ask for its integer label. No test on the store can change the answers to these questions. This is why a definition by cases on expressions starts by inspecting a constructor even when a later case needs to read a store.

*The evaluator in Concrete Semantics.* In [_Concrete Semantics_, §§3.1.1–3.1.2, pp. 27–29](https://concrete-semantics.org/), Nipkow and Klein write N, V and Plus for the literal, variable and addition constructors. Their function aval first takes a tree, then a store. For example, aval (Plus (V x) (N 4)) s evaluates the tree from Example 1.1 in store s. It computes $`s(x)+4`. Replacing $`s` by a different store changes only the lookup. Section 1.5 uses the same style of evaluator for our four constructors. [Companion theory, AExp, definition of aval.](https://isabelle.in.tum.de/library/HOL/HOL-IMP/AExp.html)

*Compositional interpretation.* In §§1.1–1.2 Reynolds interprets the constructors of predicate logic by operations on their meanings. For our arithmetic language, the meaning of an expression that may contain variables is a function from stores to integers. Write $`D(e)(s) = \operatorname{eval}\left( {e,s} \right)`. The meaning of a literal is the constant function with value $`n`. A variable denotes the function that looks up its name. To interpret addition, take two such functions $`f,g:\Sigma\rightarrow{\mathbb{Z}}` and form their pointwise sum, the function sending $`s` to $`f(s) + g(s)`. Then

$$`D\left( {\operatorname{add}\left( {e_{1},e_{2}} \right)} \right)(s) = D\left( e_{1} \right)(s) + D\left( e_{2} \right)(s).`

This is precisely the third evaluation equation. It is compositional because the two functions $`D\left( e_{1} \right)` and $`D\left( e_{2} \right)` supply everything needed to interpret their sum.

As a consequence, $`\operatorname{var}(x)` and $`\operatorname{add}\left( {\operatorname{var}(x),\operatorname{lit}(0)} \right)` are distinct syntax trees with the same meaning. For every $`s`, the equation reduces the second value to $`s(x) + 0 = s(x)`. Equality of these two meanings requires equality at every store. Agreement in a single calculation would leave open their behaviour at other stores.

Fix an expression and let the store vary. The resulting map on stores is constant for a literal. For a variable it is the projection that reads the named coordinate. For addition it is the pointwise sum of two maps, and for subtraction their pointwise difference. For example, if the values of `x` and `y` at a store are 3 and 5, the maps for `x + y` and `y + x` both give 8. To show these maps equal, replace 3 and 5 by arbitrary integers supplied by an arbitrary store and use commutativity of integer addition. The syntax trees can still be distinguished by inspecting the label of the left child.

The proof of commutativity uses the defining equation once on each side. It does not need an induction on either child: the commutative law applies to the two integers they produce, however deeply nested the children may be.

*Further reading on free variables.*

The agreement hypothesis has a direction that is easy to reverse by accident. Take the expression `x + y` and two stores that give the pairs `(1,4)` and `(2,3)` at the two variables. Both evaluations give 5. Neither coordinate agrees. Consequently an equality of results for one pair of stores does not allow us to infer coordinatewise agreement on the free variables. The lemma instead tells us how to produce an equality of results *from* enough equalities of inputs.

A slightly stronger way to read the statement is to retain only the restriction of a store to the finite set of names in the expression. Any two extensions of this restricted assignment to all names give the same value. To see this, take the two extensions as the stores in the coincidence lemma; for a free name, equality follows because both extend the same assignment. Thus an evaluator supplied with a full store can be used to define a value from just the restricted assignment. Choosing zero for every missing variable gives one concrete extension. Choosing a different default gives the same result. This argument explains why a later data-flow analysis can reason about sets of names even though the execution rules operate on complete stores.

*Further reading on judgments.*

*Notation in the source.* Winskel writes $`\langle a,\sigma\rangle \rightarrow n` (§2.2, p. 13) and $`\langle c,\sigma\rangle \rightarrow \sigma'` (§2.4, p. 19) for complete expression and command evaluations. Here the double downward arrow serves that role in both judgments. His addition rule makes the sum of the two premise results a side condition on the conclusion. Definition 1.5 writes that sum directly in the conclusion. [Winskel, §§2.2, 2.4](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf#page=34)

The BigStep chapter of _PLFA_ uses $`\gamma \vdash M \Downarrow V` for evaluation of a lambda term. Its $`\gamma` is an environment that binds variables to closures (terms paired with environments for their free variables). In our imperative language the object supplied to the left of the turnstile is the current store of integer variables. [PLFA, BigStep](https://plfa.github.io/BigStep/#big-step-evaluation)

*A direct proof of determinacy.* In §3.2, Proposition 3.3, Winskel proves uniqueness directly from the rules by structural induction on the expression. Here is the addition case for our grammar. Fix $`e = \operatorname{add}\left( {e_{1},e_{2}} \right)` and suppose two derivations have results $`r` and $`q` in the same store. Inverting their last rules produces child results $`a,b` and $`a',b'`, with $`r = a + b` and $`q = a' + b'`. The induction hypothesis for $`e_{1}` applies to its two evaluations in this store, so $`a = a'`. The hypothesis for $`e_{2}` gives $`b = b'`. Hence $`r = q`. The axiom cases force the results to be the literal or the value stored at the given name. This proof establishes uniqueness even before an evaluator has been defined. Existence is a separate assertion, supplied here by the reverse direction of Theorem 1.3.

*Source comparisons.*

Glynn Winskel, [_The Formal Semantics of Programming Languages: An Introduction_](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf) (MIT Press, 1993). In chapter 2, [§§2.1–2.2, pp. 11–16](https://web.cecs.pdx.edu/~apt/cs558/winskel2.1-5.pdf), read the formation rules, the definition of a store and the evaluations of a number, a location and a sum. Winskel also gives rules for subtraction and multiplication. Our grammar includes subtraction and takes strings as variable names. In chapter 3, [§3.2, Proposition 3.3, p. 30](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf), trace the two derivations for a sum. Proposition 3.3 proves determinacy. Exercise 3.4 on the same page asks for existence. Theorem 1.3 of this chapter supplies both facts by relating the rules to a function. The corresponding graph equality appears in Winskel’s §5.3, Lemma 5.3.

*Companion readings by topic.*

Tobias Nipkow and Gerwin Klein, [_Concrete Semantics with Isabelle/HOL_](https://concrete-semantics.org/), chapter 3, §§3.1.1–3.1.2, pp. 27–29. To revisit the computation in §1.2, start at the datatype for arithmetic expressions and stop after the equations for aval. The authors take variable names to be strings. The IMP syntax of Definition 1.1 makes the same choice. [Isabelle theory and worked evaluations.](https://isabelle.in.tum.de/library/HOL/HOL-IMP/AExp.html)

John C. Reynolds, [_Theories of Programming Languages_](https://www.cs.cmu.edu/~jcr/tpl-toc.html) (Cambridge University Press, 1998), chapter 1, §§1.1–1.2, pp. 1–11, and §1.4, starting p. 15. For §1.2 and the Session 11 reading above. Follow how an interpretation is specified on constructors. For binding, track which variable occurrences remain free after substitution.

Benjamin C. Pierce, [_Types and Programming Languages_](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf) (MIT Press, 2002), chapter 3, §§3.2–3.3, pp. 26–31. Optional for §1.1 here. Derive the induction cases from Pierce’s grammar, then do the same for Definition 1.1.

Xavier Leroy’s _Compiler Verification_ course, Lean 4 port by Wojciech Różowski. [Arithmetic expressions and free variables](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L14-L60). Optional for §1.3 here. Compare the coincidence proof there with the agreement hypothesis of Lemma 1.1.
