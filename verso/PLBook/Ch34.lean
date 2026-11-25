import VersoManual

open Verso.Genre Manual

#doc (Manual) "Function Domains and Fixed-Point Induction" =>
%%%
tag := "ch34"
file := "chapter-34"
%%%

* *Definitions.* The information order, strictness, increasing sequences and least upper bounds ([Session 8, Definitions 8.3, 8.7 and 8.9, Lemma 8.10, Proposition 8.11](chapter-08/index.html#ch08-s4)). The unfolding operator of a loop, its approximations, fixed points, least fixed points and continuous operators on state transformers ([Session 9, Definitions 9.1 and 9.4, Theorem 9.5](chapter-09/index.html#ch09-s3)). This session adds Definitions 34.1, 34.2 and 34.7.
* *New terms.* Domain, continuous function, function domain, admissible property, Scott induction. [Glossary and label key](glossary/index.html)
* *Theorem 34.8 (Scott induction, also called fixed-point induction).* Let $`D` be a domain, $`f:D\to D` a continuous function and $`P` an admissible property of elements of $`D`: $`P(\bot)` holds and $`P` is chain-closed. If $`P(d)\Rightarrow P(f(d))` for every $`d\in D`, then $`P(\mathrm{lfp}(f))`, where $`\mathrm{lfp}(f)=\bigsqcup_n f^n(\bot)` is the least fixed point of $`f`.
* *Source.* Cambridge _Denotational Semantics_ lecture notes for 2025–26 (version of 5 December 2024): function domains in §3.3 (Definition 15); chain-closed and admissible subsets, Scott induction, its examples and the rules for building chain-closed subsets in §§4.1–4.3. Definition 34.7 uses their Theorem 17(i)–(ii) and Remark 4. A property $`P` here corresponds to the subset of elements at which $`P` holds. The notes also prove the least fixed-point theorem for continuous functions (their Theorem 6), Proposition 34.4 here. Session 9 proved the least fixed-point theorem for loop operators. Theorem 34.8 is their Theorem 17. Nipkow and Klein prove the least fixed-point theorem for continuous functions on sets ordered by inclusion. [Cambridge notes](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf) · [Concrete Semantics, §11.1.2, p. 185](https://concrete-semantics.org/concrete-semantics.pdf#page=195)
* *Board case.* Theorem 34.8 in six numbered steps. Then its use in Proposition 34.9 for the countdown definition: check the property at the least element, check chain-closure at one fixed input, and check preservation in the three clauses of the definition.
* *Proof outline.* Prove $`Q(n)\coloneqq P(f^n(\bot))` by induction on $`n`. The base uses $`P(\bot)` and the step uses preservation. The elements $`f^n(\bot)` form an increasing sequence, so chain-closure gives $`P` at its least upper bound. Proposition 34.4 identifies that least upper bound as the least fixed point.
* *From Session 33.* Session 33 proved a property of every well-typed term by checking that each typing rule preserves it. Here the object is a recursive definition, and a property is checked at the least element, through one unfolding, and through least upper bounds. Domains and least fixed points generalize the state transformers and loop meanings of Sessions 8 and 9.

Consider the recursive definition $`z(0)=0` and $`z(k+1)=z(k)` for natural numbers $`k`. Read as a program, $`z` counts its argument down to zero and returns zero. A machine that may unfold the definition at most $`n` times answers at the inputs $`0,\ldots,n-1` and has no answer yet at the others. Each such partial answer is a function on all inputs, with $`\bot` where the answer is missing. This session asks three questions. How are such functions compared? Is the least upper bound of the approximations again a function of the same kind? Which properties of the approximations hold at the least upper bound? Session 35 uses the answers to give the recursive programs of PCF a meaning.

# Domains and continuous functions
%%%
tag := "ch34-s1"
%%%

Session 8 ordered outcomes by definedness. The same construction works for natural numbers. Let $`\mathbb N_\bot=\mathbb N\cup\{\bot\}` and put $`d\sqsubseteq d'` when $`d=\bot` or $`d=d'`. Then $`\bot\sqsubseteq3` and $`\bot\sqsubseteq5`, while $`3` and $`5` are incomparable. The order does not compare numbers by size.

Part 3 keeps the direction of [Session 8, Definition 8.7](chapter-08/index.html#ch08-s4). Read $`d\sqsubseteq d'` as “$`d` is less defined than or equal to $`d'`”. The less defined element is on the left, $`\bot` is the least element, and a least upper bound lies above every element of its sequence.

*Definition 34.1 (Domain).* A *domain* is a set $`D` with a relation $`\sqsubseteq` such that

1. $`\sqsubseteq` is reflexive, antisymmetric and transitive, as listed for outcomes in Session 8, §8.4;
2. $`D` has a least element $`\bot_D`, that is, $`\bot_D\sqsubseteq d` for every $`d\in D`;
3. every increasing sequence $`d_0\sqsubseteq d_1\sqsubseteq\cdots` in $`D` has a least upper bound $`\bigsqcup_n d_n` in the sense of Session 8, Definition 8.9.

We write $`\bot` for $`\bot_D` when the domain is clear. This is a new use of the word: the domain $`\mathrm{dom}(\Gamma)` of a context (C.3) and the domain of a function type (Session 26) are not domains in this sense. The Cambridge notes use the same word, and call an increasing sequence a *chain*. For a set $`X`, the *flat domain* $`X_\bot=X\cup\{\bot\}` has $`d\sqsubseteq d'` when $`d=\bot` or $`d=d'`. The outcomes $`\Sigma_\bot` of Session 8 are the case $`X=\Sigma`, and $`\mathbb N_\bot` is the case $`X=\mathbb N`. The proof of Lemma 8.10 uses only that an element other than $`\bot` lies below itself alone, so it applies to every flat domain. An increasing sequence in $`X_\bot` is $`\bot` at every index, with least upper bound $`\bot`, or it reaches an element of $`X` at some index $`k` and stays there, and that element is its least upper bound. Hence $`X_\bot` is a domain. The state transformers form a domain by Proposition 8.11. Their least element returns $`\bot` at every store.

A program cannot test whether its argument is $`\bot`, because a computation that has not finished cannot be observed to have failed. Consider $`\delta:\mathbb N_\bot\to\mathbb N_\bot` with $`\delta(\bot)=0` and $`\delta(k)=\bot` for every $`k\in\mathbb N`. Then $`\bot\sqsubseteq3`, but $`\delta(\bot)=0\not\sqsubseteq\bot=\delta(3)`. More information about the input gives less information about the output. The next definition excludes such functions.

*Definition 34.2 (Monotone and continuous functions).* Let $`D` and $`E` be domains. A function $`f:D\to E` is *monotone* if $`d\sqsubseteq d'` implies $`f(d)\sqsubseteq f(d')`. It is *strict* if $`f(\bot_D)=\bot_E`. It is *continuous* if it is monotone and, for every increasing sequence $`d_0\sqsubseteq d_1\sqsubseteq\cdots` in $`D`,

$$`f\Bigl(\bigsqcup_n d_n\Bigr)=\bigsqcup_n f(d_n).`

Monotonicity makes the sequence $`f(d_n)` increase, so the right side exists. [Session 9, §9.3](chapter-09/index.html#ch09-s3) stated the same condition for operators on state transformers. The word strict is the one of Session 8, Definition 8.3. Every constant function is continuous, because both sides of the equation equal the constant. A continuous function need not be strict.

*Lemma 34.3 (Functions out of a flat domain).* Let $`X_\bot` be a flat domain and $`E` a domain. Every monotone function $`f:X_\bot\to E` is continuous.

*Proof.* Let $`d_0\sqsubseteq d_1\sqsubseteq\cdots` be increasing in $`X_\bot`. By Lemma 8.10 for $`X_\bot` there is an index $`k` with $`d_i\sqsubseteq d_k` for every $`i` and $`\bigsqcup_i d_i=d_k`. If every $`d_i` is $`\bot`, take $`k=0`. By monotonicity $`f(d_i)\sqsubseteq f(d_k)` for every $`i`, so $`f(d_k)` is an upper bound of the $`f(d_i)`. Every upper bound lies above $`f(d_k)`, which is one of them. Hence $`\bigsqcup_i f(d_i)=f(d_k)=f(\bigsqcup_i d_i)`. $`\square`

[Session 9](chapter-09/index.html#ch09-s2) built the meaning of a loop by starting from the state transformer that returns $`\bot` everywhere and applying the unfolding operator again and again. Theorem 9.5 proved that the least upper bound is the least fixed point. The argument works for every continuous function on a domain. For $`f:D\to D` put $`f^0(\bot)=\bot` and $`f^{n+1}(\bot)=f(f^n(\bot))`. As in Session 9, a *fixed point* of $`f` is an element $`d` with $`f(d)=d`, and a *least fixed point* is a fixed point below every fixed point.

*Proposition 34.4 (Least fixed point).* Let $`D` be a domain and $`f:D\to D` continuous.

* (a) $`f^0(\bot)\sqsubseteq f^1(\bot)\sqsubseteq f^2(\bot)\sqsubseteq\cdots`.
* (b) The least upper bound $`\mathrm{lfp}(f)\coloneqq\bigsqcup_n f^n(\bot)` satisfies $`f(\mathrm{lfp}(f))=\mathrm{lfp}(f)`.
* (c) $`\mathrm{lfp}(f)\sqsubseteq d` for every $`d\in D` with $`f(d)\sqsubseteq d`. In particular $`\mathrm{lfp}(f)` is the least fixed point of $`f`.

*Proof.* (a) Induction on $`n` with $`R(n)\coloneqq f^n(\bot)\sqsubseteq f^{n+1}(\bot)`. $`R(0)` holds because $`\bot` is least. From $`R(n)`, monotonicity gives $`f(f^n(\bot))\sqsubseteq f(f^{n+1}(\bot))`, which is $`R(n+1)`. (b) Continuity gives $`f(\mathrm{lfp}(f))=\bigsqcup_n f(f^n(\bot))=\bigsqcup_n f^{n+1}(\bot)`. The sequences $`f^n(\bot)` and $`f^{n+1}(\bot)` have the same upper bounds, because every element lies above the first entry $`f^0(\bot)=\bot`. So they have the same least upper bound $`\mathrm{lfp}(f)`. (c) Induction on $`n` with $`S(n)\coloneqq f^n(\bot)\sqsubseteq d`. $`S(0)` holds because $`\bot` is least. From $`S(n)`, monotonicity and $`f(d)\sqsubseteq d` give $`f^{n+1}(\bot)=f(f^n(\bot))\sqsubseteq f(d)\sqsubseteq d`. So $`d` is an upper bound of the sequence, and $`\mathrm{lfp}(f)\sqsubseteq d`. A fixed point $`d` satisfies $`f(d)\sqsubseteq d` by reflexivity. $`\square`

The unfolding operator of a loop is continuous on the domain of state transformers. Exercise 34.4 checks this for one loop, and the argument is the same for every loop. With $`f` that operator, $`f^n(\bot)` is the approximation $`w_n` and $`\mathrm{lfp}(f)` is $`f_W`. Theorem 9.5 is this instance. Session 9 proved the fixed-point equation by inspecting the operator at one store at a time instead of quoting continuity.

# Function domains
%%%
tag := "ch34-s2"
%%%

Return to the countdown. For each stage $`n` define $`z_n:\mathbb N_\bot\to\mathbb N_\bot` by $`z_n(\bot)=\bot` and, for $`k\in\mathbb N`,

$$`z_n(k)=\begin{cases}0 & \text{if } k<n,\\ \bot & \text{if } k\ge n.\end{cases}`

We say that a function $`g` *answers* at $`k` when $`g(k)\ne\bot`. The function $`z_n` answers exactly at the inputs that $`n` unfoldings reach.

$$`\begin{array}{c|cccc|c} k & z_0(k) & z_1(k) & z_2(k) & z_3(k) & z(k)\\ \hline 0 & \bot & 0 & 0 & 0 & 0\\ 1 & \bot & \bot & 0 & 0 & 0\\ 2 & \bot & \bot & \bot & 0 & 0 \end{array}`

Each row increases from left to right in $`\mathbb N_\bot`. Comparing functions input by input, $`z_0\sqsubseteq z_1\sqsubseteq\cdots`. At an input $`k` the row is $`\bot` up to stage $`k` and $`0` from stage $`k+1` on, so by Lemma 8.10 its least upper bound is $`0`. At $`\bot` every entry is $`\bot`. The least upper bound is the function $`z` with $`z(\bot)=\bot` and $`z(k)=0`. It differs from every $`z_n`, since $`z_n(n)=\bot` but $`z(n)=0`. The stage at which an answer appears depends on the input. Each $`z_n` is monotone because it sends $`\bot` to $`\bot`, so it is continuous by Lemma 34.3.

*Proposition 34.5 (Function domain).* Let $`D` and $`E` be domains. Let $`[D\to E]` be the set of continuous functions from $`D` to $`E`, ordered pointwise: $`g\sqsubseteq g'` when $`g(d)\sqsubseteq g'(d)` for every $`d\in D`. Then $`[D\to E]` is a domain, called a *function domain*. Its least element is the function with constant value $`\bot_E`. Every increasing sequence $`g_0\sqsubseteq g_1\sqsubseteq\cdots` in $`[D\to E]` has its least upper bound computed at each input:

$$`\Bigl(\bigsqcup_n g_n\Bigr)(d)=\bigsqcup_n g_n(d).`

*Proof.* Reflexivity, antisymmetry and transitivity hold at each input because they hold in $`E`. Equality at every input is equality of functions. The constant function with value $`\bot_E` is continuous and lies below every $`g`. Let $`g_0\sqsubseteq g_1\sqsubseteq\cdots` be increasing. At each $`d` the elements $`g_n(d)` increase, so $`h(d)\coloneqq\bigsqcup_n g_n(d)` exists in $`E`. As in Proposition 8.11, $`h` is an upper bound of the $`g_n`, and $`h\sqsubseteq g'` for every upper bound $`g'`. It remains to show that $`h` is continuous.

1. $`h` is monotone. Let $`d\sqsubseteq d'`. For every $`n`, $`g_n(d)\sqsubseteq g_n(d')\sqsubseteq h(d')`. So $`h(d')` is an upper bound of the $`g_n(d)`, and $`h(d)\sqsubseteq h(d')`.
2. Let $`d_0\sqsubseteq d_1\sqsubseteq\cdots` be increasing in $`D` with least upper bound $`d`. By step 1 the $`h(d_i)` increase. Put $`r=\bigsqcup_i h(d_i)`. We must show $`h(d)=r`.
3. Each $`d_i\sqsubseteq d`, so step 1 gives $`h(d_i)\sqsubseteq h(d)`. Hence $`r\sqsubseteq h(d)`.
4. Fix $`n`. For every $`i`, $`g_n(d_i)\sqsubseteq h(d_i)\sqsubseteq r`. Continuity of $`g_n` gives $`g_n(d)=\bigsqcup_i g_n(d_i)\sqsubseteq r`. This is the only use of continuity of the $`g_n`. Solutions and Further Reading shows a monotone function that is not continuous.
5. Step 4 holds for every $`n`, so $`r` is an upper bound of the $`g_n(d)`, and $`h(d)\sqsubseteq r`. Antisymmetry with step 3 gives $`h(d)=r`. $`\square`

The recursive definition of $`z` becomes a function on the domain $`[\mathbb N_\bot\to\mathbb N_\bot]`. As in Session 9, §9.1, replace $`z` on the right by a proposed solution $`g` and read the right side as an operation on $`g`. The first clause below says that the program needs its argument: with no input there is no answer. For $`g\in[\mathbb N_\bot\to\mathbb N_\bot]` define the *countdown operator* by

$$`F(g)(\bot)=\bot,\qquad F(g)(0)=0,\qquad F(g)(k+1)=g(k)\quad(k\in\mathbb N).`

*Lemma 34.6 (Countdown operator).*

* (a) For every $`g\in[\mathbb N_\bot\to\mathbb N_\bot]`, $`F(g)\in[\mathbb N_\bot\to\mathbb N_\bot]`.
* (b) $`F:[\mathbb N_\bot\to\mathbb N_\bot]\to[\mathbb N_\bot\to\mathbb N_\bot]` is continuous.
* (c) $`F^n(\bot)=z_n` for every $`n`. Hence $`\mathrm{lfp}(F)=z`, and $`z` is the least fixed point of $`F` by Proposition 34.4.

*Proof.* (a) Let $`d\sqsubseteq d'` in $`\mathbb N_\bot`. Then $`d=\bot` or $`d=d'`. If $`d=\bot`, then $`F(g)(d)=\bot\sqsubseteq F(g)(d')`. If $`d=d'` there is nothing to show. So $`F(g)` is monotone, and continuous by Lemma 34.3. (b) Let $`g\sqsubseteq g'`. At $`\bot` and at $`0` the functions $`F(g)` and $`F(g')` agree, and $`F(g)(k+1)=g(k)\sqsubseteq g'(k)=F(g')(k+1)`. So $`F` is monotone. Let $`g_0\sqsubseteq g_1\sqsubseteq\cdots` have least upper bound $`h`. By Proposition 34.5 we must show $`F(h)(d)=\bigsqcup_n F(g_n)(d)` at each $`d`. At $`\bot` both sides are $`\bot`, and at $`0` both are $`0`. At $`k+1`, Proposition 34.5 for $`h` gives $`F(h)(k+1)=h(k)=\bigsqcup_n g_n(k)=\bigsqcup_n F(g_n)(k+1)`. (c) Induction on $`n` with $`T(n)\coloneqq F^n(\bot)=z_n`. Both sides of $`T(0)` return $`\bot` everywhere. Assume $`T(n)`, so $`F^{n+1}(\bot)=F(z_n)`. At $`\bot` it gives $`\bot`. At $`0` it gives $`0=z_{n+1}(0)`. At $`k+1` it gives $`z_n(k)`, which is $`0` exactly when $`k<n`, that is, when $`k+1<n+1`. So $`F(z_n)=z_{n+1}`. The least upper bound of the $`z_n` is $`z`, as computed above. $`\square`

# Scott induction
%%%
tag := "ch34-s3"
%%%

Every entry of the table is $`0` or $`\bot`. In the order of $`\mathbb N_\bot` this says $`z_n(d)\sqsubseteq0` at every input $`d`. Here $`z` was computed, and $`z(d)\sqsubseteq0` can be read off. For most recursive definitions the approximations have no closed formula. We want to prove a property of the least fixed point by three checks that do not compute the approximations: at $`\bot`, through one application of the operator, and through least upper bounds.

*Definition 34.7 (Chain-closed and admissible properties).* Let $`D` be a domain and $`P` a property of elements of $`D`. The property $`P` is *chain-closed* if for every increasing sequence $`d_0\sqsubseteq d_1\sqsubseteq\cdots` in $`D`,

$$`\bigl(\forall n,\ P(d_n)\bigr)\Rightarrow P\Bigl(\bigsqcup_n d_n\Bigr).`

It is *admissible* if it is chain-closed and $`P(\bot)` holds. A function $`f:D\to D` *preserves* $`P` if $`P(d)\Rightarrow P(f(d))` for every $`d\in D`. A set $`\mathcal A\subseteq D` is *admissible* if the property $`d\in\mathcal A` is admissible.

*Theorem 34.8 (Scott induction, also called fixed-point induction).* Let $`D` be a domain, $`f:D\to D` continuous, and $`P` an admissible property of elements of $`D`. If $`f` preserves $`P`, then $`P(\mathrm{lfp}(f))`.

*Proof.* We must show $`P(\mathrm{lfp}(f))`, where $`\mathrm{lfp}(f)=\bigsqcup_n f^n(\bot)` (Proposition 34.4). We first prove $`Q(n)` for every $`n` by induction on $`n`, with the induction property

$$`Q(n)\quad\coloneqq\quad P\bigl(f^n(\bot)\bigr).`

1. Base. $`f^0(\bot)=\bot`, and $`P(\bot)` holds because $`P` is admissible. So $`Q(0)` holds.
2. Step. The induction hypothesis is $`Q(n):\ P(f^n(\bot))`. Apply preservation with $`d=f^n(\bot)`. It gives $`P(f(f^n(\bot)))`, which is $`Q(n+1)` because $`f^{n+1}(\bot)=f(f^n(\bot))`.
3. By steps 1 and 2 and induction on $`n`, $`P(f^n(\bot))` holds for every $`n`.
4. By Proposition 34.4(a), $`f^0(\bot)\sqsubseteq f^1(\bot)\sqsubseteq\cdots` is an increasing sequence. This step uses monotonicity of $`f`.
5. $`P` is chain-closed. Apply Definition 34.7 to the sequence of step 4, using step 3 for its premise. It gives $`P(\bigsqcup_n f^n(\bot))`, that is, $`P(\mathrm{lfp}(f))`.
6. By Proposition 34.4(b) and (c), $`\mathrm{lfp}(f)` is the least fixed point of $`f`. Continuity of $`f` is used only here. $`\square`

*Proposition 34.9 (The countdown answers zero).* Let $`z=\mathrm{lfp}(F)` for the countdown operator $`F`. Then $`z(d)\sqsubseteq0` for every $`d\in\mathbb N_\bot`. At each input, $`z` returns $`0` or $`\bot`.

*Proof.* We must show $`P(z)`, where $`P` is the property of elements of $`[\mathbb N_\bot\to\mathbb N_\bot]` given by

$$`P(g)\quad\coloneqq\quad\forall d\in\mathbb N_\bot,\ g(d)\sqsubseteq0.`

We apply Theorem 34.8 with the domain $`[\mathbb N_\bot\to\mathbb N_\bot]` of Proposition 34.5 and the continuous function $`F` of Lemma 34.6(b). The formula for $`z_n` is not used.

1. $`P(\bot)`. The least element of $`[\mathbb N_\bot\to\mathbb N_\bot]` is the function with constant value $`\bot` (Proposition 34.5), and $`\bot\sqsubseteq0`.
2. $`P` is chain-closed. Let $`g_0\sqsubseteq g_1\sqsubseteq\cdots` be increasing with $`P(g_n)` for every $`n`, and let $`h=\bigsqcup_n g_n`. We must show $`P(h)`. Fix $`d\in\mathbb N_\bot`. By $`P(g_n)`, $`g_n(d)\sqsubseteq0` for every $`n`, so $`0` is an upper bound of the increasing sequence $`g_n(d)`. By Proposition 34.5, $`h(d)=\bigsqcup_n g_n(d)` is the least upper bound, so $`h(d)\sqsubseteq0`.
3. $`F` preserves $`P`. Assume $`P(g)`. We must show $`F(g)(d)\sqsubseteq0` for every $`d`. Suppose $`d=\bot`. Then $`F(g)(\bot)=\bot\sqsubseteq0`. Suppose $`d=0`. Then $`F(g)(0)=0\sqsubseteq0`. Suppose $`d=k+1`. Then $`F(g)(k+1)=g(k)`, and $`P(g)` at the input $`k` gives $`g(k)\sqsubseteq0`.
4. By steps 1 and 2, $`P` is admissible. Theorem 34.8 with step 3 gives $`P(\mathrm{lfp}(F))`, that is, $`P(z)`. $`\square`

Lemma 34.6(c) confirms the result, since $`z(\bot)=\bot` and $`z(k)=0`. In step 2 the input $`d` is fixed before the stages are compared. The property $`P(g)` says $`g\sqsubseteq c_0`, where $`c_0` is the constant function with value $`0`. So Proposition 34.4(c) would also give it from $`F(c_0)\sqsubseteq c_0`. Exercise 34.4 proves a property that has no such form.

Chain-closure cannot be dropped. Let $`U(g)\coloneqq\exists k\in\mathbb N,\ g(k)=\bot` be the property “some natural input has no answer”. $`U` holds at the least element. $`F` preserves $`U`: if $`g(k)=\bot`, then $`F(g)(k+1)=g(k)=\bot`. Yet $`z(k)=0` for every $`k`, so $`U(z)` fails. By Theorem 34.8, $`U` is not chain-closed. The approximations show the failure. $`U(z_n)` holds with the witness $`k=n`, but the witness moves to larger inputs as $`n` grows, and no input is $`\bot` at every stage. The statement $`\forall n\,\exists k,\ z_n(k)=\bot` is true. The statement $`\exists k\,\forall n,\ z_n(k)=\bot` is false. Chain-closure is the hypothesis that forces us to check this exchange of quantifiers before arguing about a recursive definition.

# Exercises
%%%
tag := "ch34-s4"
number := false
%%%

*34.1.* Find the least $`n` with $`z_n(4)=0`. Show that the same $`n` does not work at input $`5`.

*34.2.* Let $`\mathrm{Fin}(g)` say that the set $`\{k\in\mathbb N\mid g(k)\ne\bot\}` is finite. Check that $`\mathrm{Fin}(\bot)` holds, that $`F` preserves $`\mathrm{Fin}`, and that $`\mathrm{Fin}(z)` fails. Which hypothesis of Theorem 34.8 fails? Exhibit an increasing sequence that shows it.

*34.3.* Give a continuous function $`\mathbb N_\bot\to\mathbb N_\bot` that is not strict. Which part of Definition 34.2 permits it?

*34.4.* Let $`W=\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1` from Session 9, and write $`F_W` for its unfolding operator (Definition 9.1). (a) Show that $`F_W` is continuous on the domain of state transformers, and that $`\mathrm{lfp}(F_W)=f_W`. (b) Prove by Theorem 34.8, without the formula for $`f_W`, that for every store $`s`, if $`f_W(s)` is a store $`t` then $`t(x)\ge2`. Which step uses Lemma 8.10?

*Further problem.* Let $`D` and $`E` be domains, let $`f:D\to D` and $`g:E\to E` be continuous, and let $`h:D\to E` be continuous and strict. Assume $`h(f(d))=g(h(d))` for every $`d\in D`. Prove $`h(\mathrm{lfp}(f))=\mathrm{lfp}(g)`. Show that the conclusion can fail when $`h` is not strict.

# Reading for the Seminar
%%%
tag := "ch34-s5"
number := false
%%%

*Definitions · 10 minutes.* State the order direction aloud: the left side is less defined. Write the three clauses of $`F`. Fill the table of $`z_n(k)` for $`k=0,1,2` and stages 0 to 3, and read one row from left to right.

*Joint proof · 30 minutes.* Prove Theorem 34.8 in its six steps, writing $`Q(n)` and its induction hypothesis. Then prove Proposition 34.9. One person checks $`P` at the least element, another checks chain-closure at a fixed input, and a third checks preservation in the three clauses of $`F`.

*Proof review · 20 minutes.* Check the hypotheses of Theorem 34.8 for the property $`U`. Locate the hypothesis that fails and write the two quantifier orders. Repeat with Exercise 34.2.

*Facilitator’s hint.* For a claim about all inputs, fix one input first. The stage at which an answer appears may depend on it. Before applying chain-closure, name the increasing sequence it is applied to.

# Solutions and Further Reading
%%%
tag := "ch34-s6"
number := false
%%%

*34.1.* $`z_n(4)=0` exactly when $`4<n`, so the least stage is $`5`. At input $`5`, $`z_5(5)=\bot`, and the least stage there is $`6`. No single stage serves every input.

*34.2.* $`\mathrm{Fin}(\bot)` holds because $`\bot` answers nowhere. If $`\mathrm{Fin}(g)`, then $`F(g)` answers at $`0` and at the $`k+1` where $`g` answers, a finite set. $`\mathrm{Fin}(z)` fails because $`z` answers at every natural number. $`F` is continuous, $`\mathrm{Fin}(\bot)` holds and $`F` preserves $`\mathrm{Fin}`, so by Theorem 34.8 chain-closure must fail. The sequence $`z_0\sqsubseteq z_1\sqsubseteq\cdots` shows it: $`z_n` answers exactly at $`0,\ldots,n-1`, while its least upper bound $`z` answers everywhere.

*34.3.* The constant function $`c_0` with value $`0`. It is monotone because $`0\sqsubseteq0`, and both sides of the equation in Definition 34.2 equal $`0`. Definition 34.2 asks for monotonicity and preservation of least upper bounds, not for $`f(\bot)=\bot`. Strictness is a separate property. The first clause of the countdown operator makes each $`F(g)` strict.

*34.4.* (a) Monotonicity is Lemma 9.2. Let $`h_0\sqsubseteq h_1\sqsubseteq\cdots` have least upper bound $`h`, computed store by store (Proposition 8.11). Fix $`s`. If $`s(x)\ge2`, the guard is false and $`F_W(h)(s)=s=\bigsqcup_n F_W(h_n)(s)`. Otherwise the body returns $`m=s[x\mapsto s(x)+1]`, and case 3 of Definition 9.1 gives $`F_W(h)(s)=h(m)=\bigsqcup_n h_n(m)=\bigsqcup_n F_W(h_n)(s)`. Case 2 does not occur. By Proposition 8.11 the right sides are the values of $`\bigsqcup_n F_W(h_n)`, so $`F_W` is continuous. The elements $`F_W^n(\bot)` are the approximations $`w_n`, so $`\mathrm{lfp}(F_W)=f_W` by Definition 9.4. (b) Let $`P(h)` say: for every store $`s`, if $`h(s)` is a store $`t` then $`t(x)\ge2`. $`P(\bot)` holds because $`\bot` returns no store. Chain-closure: let $`h=\bigsqcup_n h_n` with $`P(h_n)` for every $`n`, and suppose $`h(s)=t` is a store. By Lemma 8.10, $`h_n(s)=t` for some $`n`, and $`P(h_n)` gives $`t(x)\ge2`. Preservation: assume $`P(h)` and fix $`s`. If $`s(x)\ge2`, then $`F_W(h)(s)=s`, and $`s(x)\ge2`. Otherwise $`F_W(h)(s)=h(m)`, and $`P(h)` at $`m` applies. Theorem 34.8 gives $`P(f_W)`. Lemma 8.10 is used in the chain-closure step. Unlike Proposition 34.9, $`P` is not of the form $`h\sqsubseteq d` for one state transformer $`d`: two different stores with $`x\ge2` would both have to lie below $`d(s)`, and different stores have no common upper bound. Session 9 computed $`f_W(s)=s[x\mapsto\max(s(x),2)]`, which agrees.

*Further problem.* Prove $`V(n)\coloneqq h(f^n(\bot_D))=g^n(\bot_E)` by induction on $`n`. $`V(0)` is strictness. From $`V(n)`, the hypothesis at $`f^n(\bot_D)` gives $`h(f^{n+1}(\bot_D))=g(h(f^n(\bot_D)))=g(g^n(\bot_E))=g^{n+1}(\bot_E)`. Continuity of $`h` then gives $`h(\mathrm{lfp}(f))=\bigsqcup_n h(f^n(\bot_D))=\bigsqcup_n g^n(\bot_E)=\mathrm{lfp}(g)`. For a counterexample take $`D=E=\{\bot,1\}` with $`\bot\sqsubseteq1`, let $`f` and $`g` be the identity, and let $`h` be constant with value $`1`. All three are continuous, and $`h(f(d))=1=g(h(d))`. Both least fixed points are $`\bot`, but $`h(\bot)=1`. The induction fails at $`V(0)`.

*Further reading · Monotone is not enough.* Let $`\mathbb N_\omega` be the natural numbers in their usual order with a largest element $`\omega` added. It is a domain: an increasing sequence that stops growing has its last value as least upper bound, and one that grows without bound has $`\omega`. Let $`\mathbb B_\bot` be the flat domain over $`\mathbb B=\{\mathrm{tt},\mathrm{ff}\}`, and let $`u(k)=\bot` for natural numbers $`k` and $`u(\omega)=\mathrm{tt}`. Then $`u` is monotone, but $`u(\bigsqcup_k k)=\mathrm{tt}` while $`\bigsqcup_k u(k)=\bot`. The output at the least upper bound is not determined by the outputs at the finite stages. Proposition 34.4(b) needs continuity for the same reason. Add a top element $`\omega+1` above $`\omega`, and let $`f(k)=k+1`, $`f(\omega)=f(\omega+1)=\omega+1`. This $`f` is monotone. Starting from the least element $`0`, the elements $`f^n(0)=n` have least upper bound $`\omega`, and $`f(\omega)=\omega+1\ne\omega`.

*Further reading · Staying inside the function domain.* Change the first clause of the countdown operator to $`F'(g)(\bot)=0`. Then $`F'(\bot)(\bot)=0` and $`F'(\bot)(1)=\bot`, while $`\bot\sqsubseteq1`. So $`F'(\bot)` is not monotone, and $`F'` does not map $`[\mathbb N_\bot\to\mathbb N_\bot]` into itself. In general a monotone function on $`\mathbb N_\bot` that sends $`\bot` to $`0` sends every input to $`0`, because $`0\sqsubseteq g(k)` forces $`g(k)=0`. Lemma 34.6(a) is the check that this cannot happen for $`F`.

*Further reading · Building chain-closed properties.* The Cambridge notes, §4.2, give rules for building chain-closed properties. For continuous $`g,g':D\to E`, the properties $`g(d)\sqsubseteq g'(d)` and $`g(d)=g'(d)` of $`d` are chain-closed: if $`g(d_n)\sqsubseteq g'(d_n)` for every $`n`, then $`g(\bigsqcup_n d_n)=\bigsqcup_n g(d_n)\sqsubseteq\bigsqcup_n g'(d_n)=g'(\bigsqcup_n d_n)`. If each of a family of properties is chain-closed, so is their conjunction. A property of $`g\in[D\to E]` of the form “$`Q_d(g(d))` for every $`d`”, with each $`Q_d` chain-closed on $`E`, is chain-closed because least upper bounds are computed at each input. Step 2 of Proposition 34.9 is this rule with $`Q_d(r)\coloneqq r\sqsubseteq0`. Every property of a flat domain is chain-closed, because an increasing sequence there reaches its least upper bound (Lemma 8.10). Exercise 34.4 uses this. An existential quantifier can break chain-closure, as the property $`U` shows. So can negation: the property “not $`z\sqsubseteq g`” holds at every $`z_n` and fails at $`z`.

# Sources and Formalization
%%%
tag := "ch34-notes"
number := false
%%%

* *Lemma 34.3.* Formulated in this book. Paper proof only ([§34.1](chapter-34/index.html#ch34-s1)).
* *Proposition 34.4.* Source: Cambridge notes, Theorem 6. Corresponds to CS Theorem 11.12. Paper proof only ([§34.1](chapter-34/index.html#ch34-s1)).
* *Proposition 34.5.* Source: Cambridge notes §3.3, Definition 15 and its proof. Paper proof only ([§34.2](chapter-34/index.html#ch34-s2)).
* *Lemma 34.6.* Formulated in this book. Paper proof only ([§34.2](chapter-34/index.html#ch34-s2)).
* *Theorem 34.8.* Source: Cambridge notes, Theorem 17. The notions of chain closure and admissibility in Definition 34.7 follow conditions (i) and (ii) of that theorem and Remark 4. Paper proof only ([§34.3](chapter-34/index.html#ch34-s3)).
* *Proposition 34.9.* Formulated in this book. Paper proof only ([§34.3](chapter-34/index.html#ch34-s3)).
