import VersoManual
import PLBook.IMP.Denotation

open Verso.Genre Manual

#doc (Manual) "Finite Approximations of a Loop" =>
%%%
tag := "ch09"
file := "chapter-09"
%%%

* *Definitions.* Stores and guard values $`B(b,s)` ([IMP language card A.2 and A.4](imp-card/index.html#imp-a4)). Outcomes $`\Sigma_\bot`, state transformers, strict extension $`h^\dagger`, and the meanings $`f_c` of skip, assignment, sequencing and conditionals ([Session 8, §§8.1–8.2](chapter-08/index.html#ch08-s1)). The information order on outcomes and on state transformers, increasing sequences and least upper bounds ([Session 8, Definitions 8.7 and 8.9](chapter-08/index.html#ch08-s4)). The form of an increasing sequence of outcomes and its least upper bound ([Session 8, Lemma 8.10](chapter-08/index.html#ch08-s4)), and the least upper bound of state transformers ([Session 8, Proposition 8.11](chapter-08/index.html#ch08-s4)).
* *New terms.* Unfolding operator, approximation, fixed point, least fixed point, continuous operator. [Glossary and label key](glossary/index.html)
* *Theorem 9.5 (Least fixed point).* For every loop $`W=\mathsf{while}\ b\ \mathsf{do}\ c`, the least upper bound $`f_W` of the approximations $`w_0\sqsubseteq w_1\sqsubseteq\cdots` satisfies $`F(f_W)=f_W`, and $`f_W\sqsubseteq g` for every state transformer $`g` with $`F(g)=g`.
* *Source.* Reynolds, _Theories of Programming Languages_, §2.4, proves the least fixed-point theorem for continuous functions and uses it to define the meaning of a loop as a state transformer. We prove the instance for the unfolding operator of a loop directly. Nipkow and Klein prove the same statement for continuous functions on sets and apply it to loop meanings that are relations between stores. [Reynolds, contents](https://www.cs.cmu.edu/~jcr/tpl-toc.html) · [Concrete Semantics, §11.1.2, p. 185](https://concrete-semantics.org/concrete-semantics.pdf#page=195)
* *Board case.* Part (a), that $`f_W` is a fixed point. Fix a store $`s` and split on the three cases of Definition 9.1. In the third case the outcomes at $`s` are the outcomes at the body’s result $`m`, one stage later.
* *Proof outline.* (a) At each store, compare the sequence $`w_n(s)` with the sequence $`w_n(m)` using $`w_{n+1}(s)=w_n(m)` and Lemma 8.10. (b) Prove $`Q(n)\coloneqq w_n\sqsubseteq g` by induction on $`n` with Lemma 9.2, then take the least upper bound at each store.
* *From Session 8.* Session 8 gave a meaning to every command except the loop. Here the meaning of a loop is the least upper bound of an increasing sequence of state transformers, computed store by store with Lemma 8.10.

Session 8 gave a meaning $`f_c:\Sigma\to\Sigma_\bot` to every command except the loop. [Session 7](chapter-07/index.html) showed that $`W=\mathsf{while}\ b\ \mathsf{do}\ c` has the same executions as $`\mathsf{if}\ b\ \mathsf{then}\ (c;W)\ \mathsf{else}\ \mathsf{skip}`. So $`f_W` should satisfy an equation in which $`f_W` occurs on both sides. For $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}` that equation says $`f_W(s)=f_W(s)` at every store. Every state transformer satisfies it, including the identity, which would claim that the loop returns at once. This session chooses one solution. Start from a state transformer that knows no results, unfold the loop a finite number of times, and take the limit.

# The unfolding operator
%%%
tag := "ch09-s1"
%%%

Take $`W=\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1`. By [A.4](imp-card/index.html#imp-a4) the guard $`x<2` abbreviates $`\neg(2\le x)`, so $`B(x<2,s)=\mathsf{true}` exactly when $`s(x)<2`. The body returns $`s[x\mapsto s(x)+1]`. If $`f_W` is to respect the unfolding of Session 7, it must satisfy

$$`f_W(s)=\begin{cases} s & \text{if } s(x)\ge2,\\ f_W\bigl(s[x\mapsto s(x)+1]\bigr) & \text{if } s(x)<2.\end{cases}`

The right side uses $`f_W` at another store. Replace $`f_W` on the right by a proposed meaning $`h` and read the right side as an operation on $`h`.

*Definition 9.1 (Unfolding operator and approximations).* Fix $`W=\mathsf{while}\ b\ \mathsf{do}\ c` and the meaning $`f_c` of its body. For a state transformer $`h:\Sigma\to\Sigma_\bot`, define the state transformer $`F(h)` by

$$`F(h)(s)=\begin{cases} h^\dagger\bigl(f_c(s)\bigr) & \text{if } B(b,s)=\mathsf{true},\\ s & \text{if } B(b,s)=\mathsf{false}.\end{cases}`

The function $`F` from state transformers to state transformers is the *unfolding operator* of $`W`. The *approximations* of $`W` are the state transformers $`w_n` defined by $`w_0(s)=\bot` for every store $`s` and $`w_{n+1}=F(w_n)`. We call $`n` the *stage* of $`w_n`.

The state transformer $`F(h)` is the meaning that Session 8 gives to $`\mathsf{if}\ b\ \mathsf{then}\ (c;W)\ \mathsf{else}\ \mathsf{skip}` when $`h` is used as the meaning of $`W`. Expanding the strict extension gives three cases at each store $`s`.

1. If $`B(b,s)=\mathsf{false}`, then $`F(h)(s)=s`.
2. If $`B(b,s)=\mathsf{true}` and $`f_c(s)=\bot`, then $`F(h)(s)=\bot`.
3. If $`B(b,s)=\mathsf{true}` and $`f_c(s)=m` with $`m\in\Sigma`, then $`F(h)(s)=h(m)`.

Only case 3 consults $`h`, and only at the single store $`m`. Case 2 occurs only when the body has no result.

Return to the example. Its body always returns a store, so case 2 never occurs. Take $`s(x)=1` and put $`m=s[x\mapsto2]`. Case 3 gives $`w_2(s)=w_1(m)`. The guard is false at $`m`, so case 1 gives $`w_1(m)=F(w_0)(m)=m`. Thus $`w_2(s)=s[x\mapsto2]`. The same calculation at three inputs gives the following table.

$$`\begin{array}{c|cccc} s(x) & w_0(s) & w_1(s) & w_2(s) & w_3(s)\\ \hline 2 & \bot & s & s & s\\ 1 & \bot & \bot & s[x\mapsto2] & s[x\mapsto2]\\ 0 & \bot & \bot & \bot & s[x\mapsto2] \end{array}`

A store in the table is a final result. An entry $`\bot` says that the stage is too small to reach the exit. A store first appears at stage 1 from $`s(x)=2`, which needs no execution of the body, at stage 2 from $`s(x)=1`, which needs one, and at stage 3 from $`s(x)=0`, which needs two. In general, if the loop exits from $`s` after exactly $`k` completed executions of the body, then $`w_n(s)=\bot` for $`n\le k` and $`w_n(s)` is the store at the exit for $`n\ge k+1`. If $`w_n(s)` is a store, the loop exits from $`s` after fewer than $`n` executions of the body. Solutions and Further Reading states and proves this count.

# The increasing sequence of approximations
%%%
tag := "ch09-s2"
%%%

Read each row of the table from left to right. Each entry is $`\bot` or equal to the entry on its right. In the information order of Session 8, Definition 8.7, this says $`w_0\sqsubseteq w_1\sqsubseteq w_2\sqsubseteq w_3` at these three stores. A later stage never revises a result found at an earlier stage. It can only add results. The next two lemmas prove this for every loop.

*Lemma 9.2 (Monotonicity of the unfolding operator).* For all state transformers $`h,h'`, if $`h\sqsubseteq h'` then $`F(h)\sqsubseteq F(h')`.

*Proof.* Fix a store $`s` and use the three cases of Definition 9.1. In case 1 both sides equal $`s`. In case 2 both sides equal $`\bot`. In case 3 we have $`F(h)(s)=h(m)` and $`F(h')(s)=h'(m)`, and $`h(m)\sqsubseteq h'(m)` is the assumption $`h\sqsubseteq h'` at the store $`m`. $`\square`

*Lemma 9.3 (Increasing approximations).* For every natural number $`n`, $`w_n\sqsubseteq w_{n+1}`.

*Proof.* By induction on $`n` with the property

$$`P(n)\quad\coloneqq\quad w_n\sqsubseteq w_{n+1}.`

For $`P(0)`, $`w_0(s)=\bot\sqsubseteq w_1(s)` at every store $`s`. For the step, the induction hypothesis is $`P(n):\ w_n\sqsubseteq w_{n+1}`. Lemma 9.2 gives $`F(w_n)\sqsubseteq F(w_{n+1})`. By Definition 9.1 this is $`w_{n+1}\sqsubseteq w_{n+2}`, which is $`P(n+1)`. $`\square`

*Definition 9.4 (Meaning of a loop).* At each store $`s` the outcomes $`w_0(s)\sqsubseteq w_1(s)\sqsubseteq\cdots` increase by Lemma 9.3. Define $`f_W(s)` as their least upper bound:

$$`f_W(s)=\bigsqcup_{n\ge0}w_n(s).`

By Lemma 8.10, $`f_W(s)=t` if some $`w_n(s)` is the store $`t`, and $`f_W(s)=\bot` if every $`w_n(s)` is $`\bot`. By [Session 8, Proposition 8.11](chapter-08/index.html#ch08-s4), the state transformer $`f_W` is the least upper bound of the $`w_n` in the information order. With Session 8 this gives a meaning $`f_c` to every command by structural recursion, since the body $`c` is an immediate part of $`W`.

In the example, $`f_W(s)=s[x\mapsto\max(s(x),2)]`. From $`s(x)=j\le 2` the store first appears at stage $`3-j`. Hence for each $`n`, every store $`s` with $`s(x)=2-n` has $`w_n(s)=\bot`, while $`f_W(s)` is a store. No single approximation equals $`f_W`.

# The least fixed point
%%%
tag := "ch09-s3"
%%%

Take $`W=\mathsf{while}\ 0<x\ \mathsf{do}\ \mathsf{skip}`. By A.4 the guard abbreviates $`\neg(x\le0)`. The body returns its input, so case 3 of Definition 9.1 has $`m=s`, and

$$`F(h)(s)=\begin{cases} s & \text{if } s(x)\le0,\\ h(s) & \text{if } s(x)>0.\end{cases}`

A *fixed point* of $`F` is a state transformer $`g` with $`F(g)=g`. Here $`F(g)=g` says $`g(s)=s` when $`s(x)\le0` and $`g(s)=g(s)` when $`s(x)>0`. The second condition holds for every $`g`. So the identity state transformer $`\mathrm{id}(s)=s` is a fixed point. So is the state transformer $`\ell` of [Session 8, §8.1](chapter-08/index.html#ch08-s1), with $`\ell(s)=s` when $`s(x)\le0` and $`\ell(s)=\bot` when $`s(x)>0`. The identity claims that the loop returns at once from a store with $`s(x)=1`. The least-height argument of [Session 2, §2.4](chapter-02/index.html#ch02-s4), applied to this loop, shows that no terminating derivation exists there.

The approximations select $`\ell`. Stage 1 gives $`w_1=F(w_0)=\ell`, and $`F(\ell)=\ell`, so $`w_n=\ell` for every $`n\ge1` and $`f_W=\ell`. Moreover $`\ell\sqsubseteq g` for every fixed point $`g`. Both return $`s` when $`s(x)\le0`, and $`\ell(s)=\bot` lies below $`g(s)` otherwise. A fixed point that lies below every fixed point is a *least fixed point*. There is at most one, since two least fixed points lie below each other and the information order is antisymmetric. The order compares two outcomes at the same store. It never compares stores by the size of $`x`.

*Theorem 9.5 (Least fixed point).* Let $`W=\mathsf{while}\ b\ \mathsf{do}\ c` have unfolding operator $`F` and approximations $`w_n` (Definition 9.1), and let $`f_W=\bigsqcup_n w_n` (Definition 9.4). Then (a) $`F(f_W)=f_W`, and (b) $`f_W\sqsubseteq g` for every state transformer $`g` with $`F(g)=g`.

Part (a) says that $`f_W` solves the loop equation. Part (b) says that it is the least solution.

*Proof of (a).* We must show $`F(f_W)(s)=f_W(s)` for every store $`s`. Fix $`s`. By Definition 9.1, for every $`n`,

$$`w_0(s)=\bot,\qquad w_{n+1}(s)=F(w_n)(s).`

Split on the three cases of Definition 9.1 at $`s`.

*Case 1.* $`B(b,s)=\mathsf{false}`.

1. Case 1 gives $`F(h)(s)=s` for every $`h`. With $`h=f_W` this is $`F(f_W)(s)=s`. With $`h=w_n` it is $`w_{n+1}(s)=s` for every $`n`.
2. The outcomes at $`s` are $`\bot,s,s,\ldots`. By Lemma 8.10 their least upper bound is $`s`. So $`f_W(s)=s=F(f_W)(s)`.

*Case 2.* $`B(b,s)=\mathsf{true}` and $`f_c(s)=\bot`.

1. Case 2 gives $`F(h)(s)=\bot` for every $`h`. With $`h=f_W` this is $`F(f_W)(s)=\bot`. With $`h=w_n` it is $`w_{n+1}(s)=\bot` for every $`n`.
2. Every outcome at $`s` is $`\bot`, so $`f_W(s)=\bot=F(f_W)(s)`.

*Case 3.* $`B(b,s)=\mathsf{true}` and $`f_c(s)=m` with $`m\in\Sigma`. Case 3 gives $`F(h)(s)=h(m)` for every $`h`. With $`h=w_n` this is the shift $`w_{n+1}(s)=w_n(m)` for every $`n`. The outcomes at $`s` are the outcomes at $`m`, one stage later:

$$`\begin{array}{c|ccccc} n & 0 & 1 & 2 & 3 & \cdots\\ \hline w_n(s) & \bot & w_0(m) & w_1(m) & w_2(m) & \cdots \end{array}`

1. With $`h=f_W`, case 3 gives $`F(f_W)(s)=f_W(m)`. We must show $`f_W(s)=f_W(m)`.
2. By Lemma 9.3 the outcomes $`w_n(m)` increase. Lemma 8.10 leaves two possibilities: either $`w_n(m)=\bot` for every $`n`, or $`w_k(m)=t` for some $`k` and some store $`t`.
3. Suppose $`w_n(m)=\bot` for every $`n`. Then $`f_W(m)=\bot`. Also $`w_0(s)=\bot` and $`w_{n+1}(s)=w_n(m)=\bot`, so every outcome at $`s` is $`\bot` and $`f_W(s)=\bot=f_W(m)`.
4. Suppose $`w_k(m)=t`. Then $`f_W(m)=t` by Lemma 8.10. The shift gives $`w_{k+1}(s)=w_k(m)=t`. The outcomes at $`s` increase by Lemma 9.3 and include the store $`t`, so Lemma 8.10 gives $`f_W(s)=t=f_W(m)`.

In every case $`F(f_W)(s)=f_W(s)`. Since $`s` was arbitrary, $`F(f_W)=f_W`. $`\square`

*Proof of (b).* Let $`F(g)=g`. We prove by induction on $`n`

$$`Q(n)\quad\coloneqq\quad w_n\sqsubseteq g.`

For $`Q(0)`, $`w_0(s)=\bot\sqsubseteq g(s)` at every store $`s`. For the step, the induction hypothesis is $`Q(n):\ w_n\sqsubseteq g`. Lemma 9.2 gives $`F(w_n)\sqsubseteq F(g)`. The left side is $`w_{n+1}` and the right side is $`g`, so $`Q(n+1)` holds. Now fix $`s`. By $`Q(n)` for every $`n`, $`g(s)` is an upper bound of the outcomes $`w_n(s)`. Their least upper bound satisfies $`f_W(s)\sqsubseteq g(s)`. Hence $`f_W\sqsubseteq g`. $`\square`

*Continuity.* Part (b) used only Lemma 9.2. Part (a) used one more property of $`F`: in case 3, $`F(h)(s)` depends on $`h` only through the single outcome $`h(m)`. An operator $`\Phi` on state transformers is monotone if $`h\sqsubseteq h'` implies $`\Phi(h)\sqsubseteq\Phi(h')`; Lemma 9.2 says that $`F` is monotone. Call a monotone operator $`\Phi` on state transformers *continuous* if $`\Phi(\bigsqcup_n h_n)=\bigsqcup_n\Phi(h_n)` for every increasing sequence $`h_0\sqsubseteq h_1\sqsubseteq\cdots` of state transformers, where $`\bigsqcup_n h_n` is taken store by store (Session 8, Proposition 8.11). Monotonicity makes the sequence $`\Phi(h_n)` increase, so the right side exists. For the approximations, $`\bigsqcup_n F(w_n)=\bigsqcup_n w_{n+1}=f_W`, because dropping the first outcome of an increasing sequence does not change its least upper bound (Lemma 8.10). So part (a) is this equation for the sequence $`w_n`. Reynolds proves the theorem for every continuous function on an order with a least element in which every increasing sequence has a least upper bound. In _Concrete Semantics_ the order is inclusion of sets, the iteration starts from the empty relation, and Lemma 11.13 shows that the relational loop operator is continuous.

# Exercises
%%%
tag := "ch09-s4"
number := false
%%%

*9.1.* For a loop whose guard is false at every store and whose body gives $`\bot` at every store, compute $`w_0`, $`w_1`, $`w_2` and $`f_W`.

*9.2.* For $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`, exhibit two different fixed points of $`F` and identify the least one. Compare it with $`f_W`.

*9.3.* Show that if $`f_W(s)` is a store $`t`, then $`w_n(s)=t` for some $`n`. Which property of the information order does the argument use?

*9.4.* Suppose only $`F(g)\sqsubseteq g`. Show that $`f_W\sqsubseteq g`. Which step of the proof of Theorem 9.5(b) changes?

*Further problem.* Let $`W=\mathsf{while}\ 0<x\ \mathsf{do}\ x:=x-2`. Using the count at the end of §9.1, find for each input the first stage at which $`w_n(s)` is a store, and compute that store. Does the increasing sequence of approximations stop changing at a single finite stage on all inputs?

# Reading for the Seminar
%%%
tag := "ch09-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the three cases of the unfolding operator. Fill the table of stages 0 to 3 at $`s(x)=0,1,2` for $`\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1`.

*Joint proof · 30 minutes.* Prove Theorem 9.5(a). Give one case to each of three people. In case 3, write the outcomes at $`s` and at $`m` in two rows and shift the second row one stage to the right.

*Proof review · 20 minutes.* Prove part (b) by induction on $`n`, writing $`Q(n)` and its induction hypothesis. Use $`\mathsf{while}\ 0<x\ \mathsf{do}\ \mathsf{skip}` to show why part (a) alone does not determine the meaning of a loop. Identify the step of part (a) that uses the fact that case 3 consults $`h` at a single store.

*Facilitator’s hint.* Fix one store before comparing two state transformers. Keep the stage $`n` of an approximation separate from the number of completed bodies of a run. After one body, both decrease by one.

# Solutions and Further Reading
%%%
tag := "ch09-s6"
number := false
%%%

*9.1.* Case 1 applies at every store, so $`F(h)(s)=s` for every $`h`. Stage 0 is constantly $`\bot`. Stages 1 and 2 return the input store, and so does $`f_W`. The body is never consulted.

*9.2.* Here $`F(h)(s)=h^\dagger(s)=h(s)`, so every state transformer is a fixed point. The constantly $`\bot` state transformer and the identity are two of them. The constantly $`\bot` state transformer lies below every state transformer, so it is the least fixed point. Every $`w_n` is constantly $`\bot`, so $`f_W` is constantly $`\bot`, as Theorem 9.5 requires.

*9.3.* The outcomes $`w_n(s)` increase by Lemma 9.3. By Lemma 8.10 either all of them are $`\bot`, and then $`f_W(s)=\bot`, or some $`w_n(s)` is a store and $`f_W(s)` is that store. Since $`f_W(s)=t` is a store, the second possibility holds and $`w_n(s)=t`. The argument uses the fact that a store lies below only itself: an increasing sequence that reaches a store stays there, so its least upper bound occurs at a finite stage.

*9.4.* Only the induction step changes. From $`Q(n)`, Lemma 9.2 gives $`w_{n+1}=F(w_n)\sqsubseteq F(g)`, and $`F(g)\sqsubseteq g` gives $`w_{n+1}\sqsubseteq g` by transitivity. The final paragraph is unchanged. _Concrete Semantics_, Theorem 10.29, defines the least fixed point as the intersection of all such $`g` for monotone functions on sets.

*Further problem.* If $`s(x)\le0`, the guard is false and $`w_n(s)=s` for every $`n\ge1`. If $`s(x)=2j` with $`j\ge1`, then after $`j` completed bodies the value of $`x` is $`0`, and every earlier guard test sees a positive value. The count gives first stage $`j+1` and result $`s[x\mapsto0]`. If $`s(x)=2j+1` with $`j\ge0`, then after $`j` bodies the value is $`1`, and one more body gives $`-1` and exits. The first stage is $`j+2` and the result is $`s[x\mapsto-1]`.

Each input has a finite first stage, yet no single stage serves all inputs. For $`n\ge1` take $`s(x)=2n`. Then $`w_n(s)=\bot` but $`w_{n+1}(s)=s[x\mapsto0]`. Stages 0 and 1 also differ at any store with $`s(x)\le0`. Hence $`w_n\ne w_{n+1}` for every $`n`, although $`f_W(s)` is a store at every input.

*Further reading · Counting completed bodies.* Fix $`W=\mathsf{while}\ b\ \mathsf{do}\ c`. A list of stores $`s_0,\ldots,s_k` is a *run* of $`k` completed bodies from $`s` if $`s_0=s`, if $`B(b,s_i)=\mathsf{true}` and $`f_c(s_i)=s_{i+1}` for each $`i<k`, and if $`B(b,s_k)=\mathsf{false}`. The count stated in §9.1 is the following property, proved by induction on $`k`.

$$`R(k)\quad\coloneqq\quad\forall s,\ \text{for every run } s_0,\ldots,s_k \text{ from } s,\ \forall n,\quad w_n(s)=\begin{cases}\bot & \text{if } n\le k,\\ s_k & \text{if } n\ge k+1.\end{cases}`

For $`R(0)`, stage 0 gives $`\bot`, and every positive stage is in case 1 at $`s` and returns $`s=s_0`. For the step, assume $`R(k)` and take a run $`s_0,\ldots,s_{k+1}` from $`s`. The guard is true at $`s` and $`f_c(s)=s_1`, and $`s_1,\ldots,s_{k+1}` is a run of $`k` completed bodies from $`s_1`. Stage 0 gives $`\bot`. Case 3 gives $`w_{n+1}(s)=w_n(s_1)`. By $`R(k)` at $`s_1`, this is $`\bot` for $`n\le k` and $`s_{k+1}` for $`n\ge k+1`. Shifting the index by one gives $`R(k+1)`.

Conversely, if $`w_n(s)=t` is a store, there is a run from $`s` ending in $`t` with fewer than $`n` completed bodies. Induct on $`n`. Stage 0 gives no store. At stage $`n+1`, case 1 gives the run of zero bodies with $`t=s`. Case 2 gives $`\bot` and cannot occur. Case 3 gives $`w_n(m)=t`. The induction hypothesis supplies a run from $`m` with fewer than $`n` bodies, and placing $`s` in front gives a run from $`s` with fewer than $`n+1`. No stage produces a result that the loop does not reach.

*Further reading · Which loop the count measures.* Consider $`\mathsf{while}\ 0<x\ \mathsf{do}\ \bigl((\mathsf{while}\ 0<y\ \mathsf{do}\ y:=y-1);\ x:=0\bigr)` from a store with $`s(x)=1` and $`s(y)=100`. The inner loop completes one hundred bodies, and the assignment sets $`x` to zero. The outer loop completes one body, so its result first appears at its stage 2. The inner loop by itself first returns at its own stage 101. Each sequence of approximations belongs to one loop, whose body meaning is fixed. Neither index counts machine steps.

*Further reading · Two ways to diverge.* Let the body be $`\mathsf{while}\ y\ne0\ \mathsf{do}\ \mathsf{skip}`, which returns its input when $`y=0` and gives $`\bot` otherwise, and let the outer guard be $`0<x`. At $`s(x)=0`, case 1 returns the input at every positive stage. At $`s(x)=1` and $`s(y)=1`, case 2 gives $`\bot` at every stage without consulting $`h`. At $`s(x)=1` and $`s(y)=0`, case 3 applies with $`m=s`, so $`F(h)(s)=h(s)` for every $`h`, and induction on $`n` gives $`w_n(s)=\bot`. Both diverging inputs have meaning $`\bot`. The first never reaches the recursive occurrence. The second reaches it at every stage.

*Further reading · Sources.* Reynolds, _Theories of Programming Languages_, §§2.3–2.4, defines domains and continuous functions and proves the least fixed-point theorem in general. _Concrete Semantics_, §11.1, defines loop meanings as relations: Example 11.2 is the loop $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`, and Example 11.14 computes the approximations of a countdown loop. Leroy’s course, §9.1, computes a least fixed point by iterating from a least element when every strictly increasing sequence is finite. The iteration then stops at a finite stage, which the further problem shows cannot be expected for loop meanings. [Reynolds, contents](https://www.cs.cmu.edu/~jcr/tpl-toc.html) · [Concrete Semantics, §11.1](https://concrete-semantics.org/concrete-semantics.pdf#page=190) · [Leroy’s course, fixed points](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Fixpoints.lean)

*Further reading · Special lecture S2.* The organizer’s special lecture [S2 (order, approximation and fixed points)](static/slides/s2/index.html) proves the least fixed-point theorem for continuous functions in general and obtains the loop meaning of this session as an instance.

# Sources and Formalization
%%%
tag := "ch09-notes"
number := false
%%%

* *Lemma 9.2.* Formulated in this book. Corresponds to CS Lemma 11.3. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 9.3.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 9.5.* Source: Reynolds §2.4, specialized to loop unfolding. Corresponds to CS Theorem 11.12. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
