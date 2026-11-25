import VersoManual
import PLBook.IMP.Denotation

open Verso.Genre Manual

#doc (Manual) "Finite Approximations of a Loop" =>
%%%
tag := "ch09"
file := "chapter-09"
%%%

Session 8 gave a meaning $`f_c:\Sigma\to\Sigma_\bot` to every command except the loop. [Session 7](chapter-07/index.html) showed that $`W=\mathsf{while}\ b\ \mathsf{do}\ c` has the same executions as $`\mathsf{if}\ b\ \mathsf{then}\ (c;W)\ \mathsf{else}\ \mathsf{skip}`. So $`f_W` should satisfy an equation in which $`f_W` occurs on both sides. For $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}` that equation says $`f_W(\sigma)=f_W(\sigma)` at every state. Every state transformer satisfies it, including the identity, which would claim that the loop returns at once. This session chooses one solution. Start from a state transformer that knows no results, unfold the loop a finite number of times, and take the limit.

*In this session.*

* *Definitions.* States and guard values $`B(b,\sigma)` ([IMP language card A.2 and A.4](imp-card/index.html#imp-a4)). Outcomes $`\Sigma_\bot`, state transformers, strict extension $`h^\dagger`, and the meanings $`f_c` of skip, assignment, sequencing and conditionals ([Session 8, §§8.1–8.2](chapter-08/index.html#ch08-s1)). The information order on outcomes and on state transformers, increasing sequences and least upper bounds ([Session 8, Definitions 8.7 and 8.9](chapter-08/index.html#ch08-s4)). The form of an increasing sequence of outcomes and its least upper bound ([Session 8, Lemma 8.10](chapter-08/index.html#ch08-s4)), and the least upper bound of state transformers ([Session 8, Proposition 8.11](chapter-08/index.html#ch08-s4)).
* *New terms.* Unfolding operator, approximation, fixed point, least fixed point, continuous operator. [Glossary](glossary/index.html)
* *Theorem 9.5 (Least fixed point).* For every loop $`W=\mathsf{while}\ b\ \mathsf{do}\ c`, the least upper bound $`f_W` of the approximations $`w_0\sqsubseteq w_1\sqsubseteq\cdots` satisfies $`F(f_W)=f_W`, and $`f_W\sqsubseteq g` for every state transformer $`g` with $`F(g)=g`.
* *Board case.* Part (a), that $`f_W` is a fixed point. Fix a state $`\sigma` and split on the three cases of Definition 9.1. In the third case the outcomes at $`\sigma` are the outcomes at the body’s result $`\sigma_1`, one stage later.
* *Proof outline.* (a) At each state, compare the sequence $`w_n(\sigma)` with the sequence $`w_n(\sigma_1)` using $`w_{n+1}(\sigma)=w_n(\sigma_1)` and Lemma 8.10. (b) Prove $`Q(n)\coloneqq w_n\sqsubseteq g` by induction on $`n` with Lemma 9.2, then take the least upper bound at each state.
* *From Session 8.* Session 8 gave a meaning to every command except the loop. Here the meaning of a loop is the least upper bound of an increasing sequence of state transformers, computed state by state with Lemma 8.10.

# The unfolding operator
%%%
tag := "ch09-s1"
%%%

Take $`W=\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1`. By [A.4](imp-card/index.html#imp-a4) the guard $`x<2` abbreviates $`\neg(2\le x)`, so $`B(x<2,\sigma)=\mathsf{true}` exactly when $`\sigma(x)<2`. The body returns $`\sigma[x\mapsto \sigma(x)+1]`. If $`f_W` is to respect the unfolding of Session 7, it must satisfy

$$`f_W(\sigma)=\begin{cases} \sigma & \text{if } \sigma(x)\ge2,\\ f_W\bigl(\sigma[x\mapsto \sigma(x)+1]\bigr) & \text{if } \sigma(x)<2.\end{cases}`

The right side uses $`f_W` at another state. Replace $`f_W` on the right by a proposed meaning $`h` and read the right side as an operation on $`h`.

*Definition 9.1 (Unfolding operator and approximations).* Fix $`W=\mathsf{while}\ b\ \mathsf{do}\ c` and the meaning $`f_c` of its body. For a state transformer $`h:\Sigma\to\Sigma_\bot`, define the state transformer $`F(h)` by

$$`F(h)(\sigma)=\begin{cases} h^\dagger\bigl(f_c(\sigma)\bigr) & \text{if } B(b,\sigma)=\mathsf{true},\\ \sigma & \text{if } B(b,\sigma)=\mathsf{false}.\end{cases}`

The function $`F` from state transformers to state transformers is the *unfolding operator* of $`W`. The *approximations* of $`W` are the state transformers $`w_n` defined by $`w_0(\sigma)=\bot` for every state $`\sigma` and $`w_{n+1}=F(w_n)`. We call $`n` the *stage* of $`w_n`.

The state transformer $`F(h)` is the meaning that Session 8 gives to $`\mathsf{if}\ b\ \mathsf{then}\ (c;W)\ \mathsf{else}\ \mathsf{skip}` when $`h` is used as the meaning of $`W`. Expanding the strict extension gives three cases at each state $`\sigma`.

1. If $`B(b,\sigma)=\mathsf{false}`, then $`F(h)(\sigma)=\sigma`.
2. If $`B(b,\sigma)=\mathsf{true}` and $`f_c(\sigma)=\bot`, then $`F(h)(\sigma)=\bot`.
3. If $`B(b,\sigma)=\mathsf{true}` and $`f_c(\sigma)=\sigma_1` with $`\sigma_1\in\Sigma`, then $`F(h)(\sigma)=h(\sigma_1)`.

Only case 3 consults $`h`, and only at the single state $`\sigma_1`. Case 2 occurs only when the body has no result.

Return to the example. Its body always returns a state, so case 2 never occurs. Take $`\sigma(x)=1` and put $`\sigma_1=\sigma[x\mapsto2]`. Case 3 gives $`w_2(\sigma)=w_1(\sigma_1)`. The guard is false at $`\sigma_1`, so case 1 gives $`w_1(\sigma_1)=F(w_0)(\sigma_1)=\sigma_1`. Thus $`w_2(\sigma)=\sigma[x\mapsto2]`. The same calculation at three inputs gives the following table.

$$`\begin{array}{c|cccc} \sigma(x) & w_0(\sigma) & w_1(\sigma) & w_2(\sigma) & w_3(\sigma)\\ \hline 2 & \bot & \sigma & \sigma & \sigma\\ 1 & \bot & \bot & \sigma[x\mapsto2] & \sigma[x\mapsto2]\\ 0 & \bot & \bot & \bot & \sigma[x\mapsto2] \end{array}`

A state in the table is a final result. An entry $`\bot` says that the stage is too small to reach the exit. A state first appears at stage 1 from $`\sigma(x)=2`, which needs no execution of the body, at stage 2 from $`\sigma(x)=1`, which needs one, and at stage 3 from $`\sigma(x)=0`, which needs two. In general, if the loop exits from $`\sigma` after exactly $`k` completed executions of the body, then $`w_n(\sigma)=\bot` for $`n\le k` and $`w_n(\sigma)` is the state at the exit for $`n\ge k+1`. If $`w_n(\sigma)` is a state, the loop exits from $`\sigma` after fewer than $`n` executions of the body. Solutions and Further Reading states and proves this count.

# The increasing sequence of approximations
%%%
tag := "ch09-s2"
%%%

Read each row of the table from left to right. Each entry is $`\bot` or equal to the entry on its right. In the information order of Session 8, Definition 8.7, this says $`w_0\sqsubseteq w_1\sqsubseteq w_2\sqsubseteq w_3` at these three states. A later stage never revises a result found at an earlier stage. It can only add results. The next two lemmas prove this for every loop.

*Lemma 9.2 (Monotonicity of the unfolding operator).* For all state transformers $`h,h'`, if $`h\sqsubseteq h'` then $`F(h)\sqsubseteq F(h')`.

*Proof.* Fix a state $`\sigma` and use the three cases of Definition 9.1. In case 1 both sides equal $`\sigma`. In case 2 both sides equal $`\bot`. In case 3 we have $`F(h)(\sigma)=h(\sigma_1)` and $`F(h')(\sigma)=h'(\sigma_1)`, and $`h(\sigma_1)\sqsubseteq h'(\sigma_1)` is the assumption $`h\sqsubseteq h'` at the state $`\sigma_1`. $`\square`

*Lemma 9.3 (Increasing approximations).* For every natural number $`n`, $`w_n\sqsubseteq w_{n+1}`.

*Proof.* By induction on $`n` with the property

$$`P(n)\quad\coloneqq\quad w_n\sqsubseteq w_{n+1}.`

For $`P(0)`, $`w_0(\sigma)=\bot\sqsubseteq w_1(\sigma)` at every state $`\sigma`. For the step, the induction hypothesis is $`P(n):\ w_n\sqsubseteq w_{n+1}`. Lemma 9.2 gives $`F(w_n)\sqsubseteq F(w_{n+1})`. By Definition 9.1 this is $`w_{n+1}\sqsubseteq w_{n+2}`, which is $`P(n+1)`. $`\square`

*Definition 9.4 (Meaning of a loop).* At each state $`\sigma` the outcomes $`w_0(\sigma)\sqsubseteq w_1(\sigma)\sqsubseteq\cdots` increase by Lemma 9.3. Define $`f_W(\sigma)` as their least upper bound:

$$`f_W(\sigma)=\bigsqcup_{n\ge0}w_n(\sigma).`

By Lemma 8.10, $`f_W(\sigma)=\sigma'` if some $`w_n(\sigma)` is the state $`\sigma'`, and $`f_W(\sigma)=\bot` if every $`w_n(\sigma)` is $`\bot`. By [Session 8, Proposition 8.11](chapter-08/index.html#ch08-s4), the state transformer $`f_W` is the least upper bound of the $`w_n` in the information order. With Session 8 this gives a meaning $`f_c` to every command by structural recursion, since the body $`c` is an immediate part of $`W`.

In the example, $`f_W(\sigma)=\sigma[x\mapsto\max(\sigma(x),2)]`. From $`\sigma(x)=j\le 2` the state first appears at stage $`3-j`. Hence for each $`n`, every state $`\sigma` with $`\sigma(x)=2-n` has $`w_n(\sigma)=\bot`, while $`f_W(\sigma)` is a state. No single approximation equals $`f_W`.

# The least fixed point
%%%
tag := "ch09-s3"
%%%

Take $`W=\mathsf{while}\ 0<x\ \mathsf{do}\ \mathsf{skip}`. By A.4 the guard abbreviates $`\neg(x\le0)`. The body returns its input, so case 3 of Definition 9.1 has $`\sigma_1=\sigma`, and

$$`F(h)(\sigma)=\begin{cases} \sigma & \text{if } \sigma(x)\le0,\\ h(\sigma) & \text{if } \sigma(x)>0.\end{cases}`

A *fixed point* of $`F` is a state transformer $`g` with $`F(g)=g`. Here $`F(g)=g` says $`g(\sigma)=\sigma` when $`\sigma(x)\le0` and $`g(\sigma)=g(\sigma)` when $`\sigma(x)>0`. The second condition holds for every $`g`. So the identity state transformer $`\mathrm{id}(\sigma)=\sigma` is a fixed point. So is the state transformer $`\ell` of [Session 8, §8.1](chapter-08/index.html#ch08-s1), with $`\ell(\sigma)=\sigma` when $`\sigma(x)\le0` and $`\ell(\sigma)=\bot` when $`\sigma(x)>0`. The identity claims that the loop returns at once from a state with $`\sigma(x)=1`. The least-height argument of [Session 2, §2.4](chapter-02/index.html#ch02-s4), applied to this loop, shows that no terminating derivation exists there.

The approximations select $`\ell`. Stage 1 gives $`w_1=F(w_0)=\ell`, and $`F(\ell)=\ell`, so $`w_n=\ell` for every $`n\ge1` and $`f_W=\ell`. Moreover $`\ell\sqsubseteq g` for every fixed point $`g`. Both return $`\sigma` when $`\sigma(x)\le0`, and $`\ell(\sigma)=\bot` lies below $`g(\sigma)` otherwise. A fixed point that lies below every fixed point is a *least fixed point*. There is at most one, since two least fixed points lie below each other and the information order is antisymmetric. The order compares two outcomes at the same state. It never compares states by the size of $`x`.

*Theorem 9.5 (Least fixed point).* Let $`W=\mathsf{while}\ b\ \mathsf{do}\ c` have unfolding operator $`F` and approximations $`w_n` (Definition 9.1), and let $`f_W=\bigsqcup_n w_n` (Definition 9.4). Then (a) $`F(f_W)=f_W`, and (b) $`f_W\sqsubseteq g` for every state transformer $`g` with $`F(g)=g`.

Part (a) says that $`f_W` solves the loop equation. Part (b) says that it is the least solution.

*Proof of (a).* We must show $`F(f_W)(\sigma)=f_W(\sigma)` for every state $`\sigma`. Fix $`\sigma`. By Definition 9.1, for every $`n`,

$$`w_0(\sigma)=\bot,\qquad w_{n+1}(\sigma)=F(w_n)(\sigma).`

Split on the three cases of Definition 9.1 at $`\sigma`.

*Case 1.* $`B(b,\sigma)=\mathsf{false}`.

1. Case 1 gives $`F(h)(\sigma)=\sigma` for every $`h`. With $`h=f_W` this is $`F(f_W)(\sigma)=\sigma`. With $`h=w_n` it is $`w_{n+1}(\sigma)=\sigma` for every $`n`.
2. The outcomes at $`\sigma` are $`\bot,\sigma,\sigma,\ldots`. By Lemma 8.10 their least upper bound is $`\sigma`. So $`f_W(\sigma)=\sigma=F(f_W)(\sigma)`.

*Case 2.* $`B(b,\sigma)=\mathsf{true}` and $`f_c(\sigma)=\bot`.

1. Case 2 gives $`F(h)(\sigma)=\bot` for every $`h`. With $`h=f_W` this is $`F(f_W)(\sigma)=\bot`. With $`h=w_n` it is $`w_{n+1}(\sigma)=\bot` for every $`n`.
2. Every outcome at $`\sigma` is $`\bot`, so $`f_W(\sigma)=\bot=F(f_W)(\sigma)`.

*Case 3.* $`B(b,\sigma)=\mathsf{true}` and $`f_c(\sigma)=\sigma_1` with $`\sigma_1\in\Sigma`. Case 3 gives $`F(h)(\sigma)=h(\sigma_1)` for every $`h`. With $`h=w_n` this is the shift $`w_{n+1}(\sigma)=w_n(\sigma_1)` for every $`n`. The outcomes at $`\sigma` are the outcomes at $`\sigma_1`, one stage later:

$$`\begin{array}{c|ccccc} n & 0 & 1 & 2 & 3 & \cdots\\ \hline w_n(\sigma) & \bot & w_0(\sigma_1) & w_1(\sigma_1) & w_2(\sigma_1) & \cdots \end{array}`

1. With $`h=f_W`, case 3 gives $`F(f_W)(\sigma)=f_W(\sigma_1)`. We must show $`f_W(\sigma)=f_W(\sigma_1)`.
2. By Lemma 9.3 the outcomes $`w_n(\sigma_1)` increase. Lemma 8.10 leaves two possibilities: either $`w_n(\sigma_1)=\bot` for every $`n`, or $`w_k(\sigma_1)=\sigma'` for some $`k` and some state $`\sigma'`.
3. Suppose $`w_n(\sigma_1)=\bot` for every $`n`. Then $`f_W(\sigma_1)=\bot`. Also $`w_0(\sigma)=\bot` and $`w_{n+1}(\sigma)=w_n(\sigma_1)=\bot`, so every outcome at $`\sigma` is $`\bot` and $`f_W(\sigma)=\bot=f_W(\sigma_1)`.
4. Suppose $`w_k(\sigma_1)=\sigma'`. Then $`f_W(\sigma_1)=\sigma'` by Lemma 8.10. The shift gives $`w_{k+1}(\sigma)=w_k(\sigma_1)=\sigma'`. The outcomes at $`\sigma` increase by Lemma 9.3 and include the state $`\sigma'`, so Lemma 8.10 gives $`f_W(\sigma)=\sigma'=f_W(\sigma_1)`.

In every case $`F(f_W)(\sigma)=f_W(\sigma)`. Since $`\sigma` was arbitrary, $`F(f_W)=f_W`. $`\square`

*Proof of (b).* Let $`F(g)=g`. We prove by induction on $`n`

$$`Q(n)\quad\coloneqq\quad w_n\sqsubseteq g.`

For $`Q(0)`, $`w_0(\sigma)=\bot\sqsubseteq g(\sigma)` at every state $`\sigma`. For the step, the induction hypothesis is $`Q(n):\ w_n\sqsubseteq g`. Lemma 9.2 gives $`F(w_n)\sqsubseteq F(g)`. The left side is $`w_{n+1}` and the right side is $`g`, so $`Q(n+1)` holds. Now fix $`\sigma`. By $`Q(n)` for every $`n`, $`g(\sigma)` is an upper bound of the outcomes $`w_n(\sigma)`. Their least upper bound satisfies $`f_W(\sigma)\sqsubseteq g(\sigma)`. Hence $`f_W\sqsubseteq g`. $`\square`

*Continuity.* Part (b) used only Lemma 9.2. Part (a) used one more property of $`F`: in case 3, $`F(h)(\sigma)` depends on $`h` only through the single outcome $`h(\sigma_1)`. An operator $`\Phi` on state transformers is monotone if $`h\sqsubseteq h'` implies $`\Phi(h)\sqsubseteq\Phi(h')`; Lemma 9.2 says that $`F` is monotone. Call a monotone operator $`\Phi` on state transformers *continuous* if $`\Phi(\bigsqcup_n h_n)=\bigsqcup_n\Phi(h_n)` for every increasing sequence $`h_0\sqsubseteq h_1\sqsubseteq\cdots` of state transformers, where $`\bigsqcup_n h_n` is taken state by state (Session 8, Proposition 8.11). Monotonicity makes the sequence $`\Phi(h_n)` increase, so the right side exists. For the approximations, $`\bigsqcup_n F(w_n)=\bigsqcup_n w_{n+1}=f_W`, because dropping the first outcome of an increasing sequence does not change its least upper bound (Lemma 8.10). So part (a) is this equation for the sequence $`w_n`. Reynolds proves the theorem for every continuous function on an order with a least element in which every increasing sequence has a least upper bound. In _Concrete Semantics_ the order is inclusion of sets, the iteration starts from the empty relation, and Lemma 11.13 shows that the relational loop operator is continuous.

# Exercises
%%%
tag := "ch09-s4"
number := false
%%%

*9.1.* For a loop whose guard is false at every state and whose body gives $`\bot` at every state, compute $`w_0`, $`w_1`, $`w_2` and $`f_W`.

*9.2.* For $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`, exhibit two different fixed points of $`F` and identify the least one. Compare it with $`f_W`.

*9.3.* Show that if $`f_W(\sigma)` is a state $`\sigma'`, then $`w_n(\sigma)=\sigma'` for some $`n`. Which property of the information order does the argument use?

*9.4.* Suppose only $`F(g)\sqsubseteq g`. Show that $`f_W\sqsubseteq g`. Which step of the proof of Theorem 9.5(b) changes?

*Further problem.* Let $`W=\mathsf{while}\ 0<x\ \mathsf{do}\ x:=x-2`. Using the count at the end of §9.1, find for each input the first stage at which $`w_n(\sigma)` is a state, and compute that state. Does the increasing sequence of approximations stop changing at a single finite stage on all inputs?

# Reading for the Seminar
%%%
tag := "ch09-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the three cases of the unfolding operator. Fill the table of stages 0 to 3 at $`\sigma(x)=0,1,2` for $`\mathsf{while}\ x<2\ \mathsf{do}\ x:=x+1`.

*Joint proof · 30 minutes.* Prove Theorem 9.5(a). Give one case to each of three people. In case 3, write the outcomes at $`\sigma` and at $`\sigma_1` in two rows and shift the second row one stage to the right.

*Proof review · 20 minutes.* Prove part (b) by induction on $`n`, writing $`Q(n)` and its induction hypothesis. Use $`\mathsf{while}\ 0<x\ \mathsf{do}\ \mathsf{skip}` to show why part (a) alone does not determine the meaning of a loop. Identify the step of part (a) that uses the fact that case 3 consults $`h` at a single state.

*Facilitator’s hint.* Fix one state before comparing two state transformers. Keep the stage $`n` of an approximation separate from the number of completed bodies of a run. After one body, both decrease by one.

# Solutions and Further Reading
%%%
tag := "ch09-s6"
number := false
%%%

*9.1.* Case 1 applies at every state, so $`F(h)(\sigma)=\sigma` for every $`h`. Stage 0 is constantly $`\bot`. Stages 1 and 2 return the input state, and so does $`f_W`. The body is never consulted.

*9.2.* Here $`F(h)(\sigma)=h^\dagger(\sigma)=h(\sigma)`, so every state transformer is a fixed point. The constantly $`\bot` state transformer and the identity are two of them. The constantly $`\bot` state transformer lies below every state transformer, so it is the least fixed point. Every $`w_n` is constantly $`\bot`, so $`f_W` is constantly $`\bot`, as Theorem 9.5 requires.

*9.3.* The outcomes $`w_n(\sigma)` increase by Lemma 9.3. By Lemma 8.10 either all of them are $`\bot`, and then $`f_W(\sigma)=\bot`, or some $`w_n(\sigma)` is a state and $`f_W(\sigma)` is that state. Since $`f_W(\sigma)=\sigma'` is a state, the second possibility holds and $`w_n(\sigma)=\sigma'`. The argument uses the fact that a state lies below only itself: an increasing sequence that reaches a state stays there, so its least upper bound occurs at a finite stage.

*9.4.* Only the induction step changes. From $`Q(n)`, Lemma 9.2 gives $`w_{n+1}=F(w_n)\sqsubseteq F(g)`, and $`F(g)\sqsubseteq g` gives $`w_{n+1}\sqsubseteq g` by transitivity. The final paragraph is unchanged. _Concrete Semantics_, Theorem 10.29, defines the least fixed point as the intersection of all such $`g` for monotone functions on sets.

*Further problem.* If $`\sigma(x)\le0`, the guard is false and $`w_n(\sigma)=\sigma` for every $`n\ge1`. If $`\sigma(x)=2j` with $`j\ge1`, then after $`j` completed bodies the value of $`x` is $`0`, and every earlier guard test sees a positive value. The count gives first stage $`j+1` and result $`\sigma[x\mapsto0]`. If $`\sigma(x)=2j+1` with $`j\ge0`, then after $`j` bodies the value is $`1`, and one more body gives $`-1` and exits. The first stage is $`j+2` and the result is $`\sigma[x\mapsto-1]`.

Each input has a finite first stage, yet no single stage serves all inputs. For $`n\ge1` take $`\sigma(x)=2n`. Then $`w_n(\sigma)=\bot` but $`w_{n+1}(\sigma)=\sigma[x\mapsto0]`. Stages 0 and 1 also differ at any state with $`\sigma(x)\le0`. Hence $`w_n\ne w_{n+1}` for every $`n`, although $`f_W(\sigma)` is a state at every input.

*Further reading · Counting completed bodies.* Fix $`W=\mathsf{while}\ b\ \mathsf{do}\ c`. A list of states $`\sigma_0,\ldots,\sigma_k` is a *run* of $`k` completed bodies from $`\sigma` if $`\sigma_0=\sigma`, if $`B(b,\sigma_i)=\mathsf{true}` and $`f_c(\sigma_i)=\sigma_{i+1}` for each $`i<k`, and if $`B(b,\sigma_k)=\mathsf{false}`. The count stated in §9.1 is the following property, proved by induction on $`k`.

$$`R(k)\quad\coloneqq\quad\forall \sigma,\ \text{for every run } \sigma_0,\ldots,\sigma_k \text{ from } \sigma,\ \forall n,\quad w_n(\sigma)=\begin{cases}\bot & \text{if } n\le k,\\ \sigma_k & \text{if } n\ge k+1.\end{cases}`

For $`R(0)`, stage 0 gives $`\bot`, and every positive stage is in case 1 at $`\sigma` and returns $`\sigma=\sigma_0`. For the step, assume $`R(k)` and take a run $`\sigma_0,\ldots,\sigma_{k+1}` from $`\sigma`. The guard is true at $`\sigma` and $`f_c(\sigma)=\sigma_1`, and $`\sigma_1,\ldots,\sigma_{k+1}` is a run of $`k` completed bodies from $`\sigma_1`. Stage 0 gives $`\bot`. Case 3 gives $`w_{n+1}(\sigma)=w_n(\sigma_1)`. By $`R(k)` at $`\sigma_1`, this is $`\bot` for $`n\le k` and $`\sigma_{k+1}` for $`n\ge k+1`. Shifting the index by one gives $`R(k+1)`.

Conversely, if $`w_n(\sigma)=\sigma'` is a state, there is a run from $`\sigma` ending in $`\sigma'` with fewer than $`n` completed bodies. Induct on $`n`. Stage 0 gives no state. At stage $`n+1`, case 1 gives the run of zero bodies with $`\sigma'=\sigma`. Case 2 gives $`\bot` and cannot occur. Case 3 gives $`w_n(\sigma_1)=\sigma'`. The induction hypothesis supplies a run from $`\sigma_1` with fewer than $`n` bodies, and placing $`\sigma` in front gives a run from $`\sigma` with fewer than $`n+1`. No stage produces a result that the loop does not reach.

*Further reading · Which loop the count measures.* Consider $`\mathsf{while}\ 0<x\ \mathsf{do}\ \bigl((\mathsf{while}\ 0<y\ \mathsf{do}\ y:=y-1);\ x:=0\bigr)` from a state with $`\sigma(x)=1` and $`\sigma(y)=100`. The inner loop completes one hundred bodies, and the assignment sets $`x` to zero. The outer loop completes one body, so its result first appears at its stage 2. The inner loop by itself first returns at its own stage 101. Each sequence of approximations belongs to one loop, whose body meaning is fixed. Neither index counts machine steps.

*Further reading · Two ways to diverge.* Let the body be $`\mathsf{while}\ y\ne0\ \mathsf{do}\ \mathsf{skip}`, which returns its input when $`y=0` and gives $`\bot` otherwise, and let the outer guard be $`0<x`. At $`\sigma(x)=0`, case 1 returns the input at every positive stage. At $`\sigma(x)=1` and $`\sigma(y)=1`, case 2 gives $`\bot` at every stage without consulting $`h`. At $`\sigma(x)=1` and $`\sigma(y)=0`, case 3 applies with $`\sigma_1=\sigma`, so $`F(h)(\sigma)=h(\sigma)` for every $`h`, and induction on $`n` gives $`w_n(\sigma)=\bot`. Both diverging inputs have meaning $`\bot`. The first never reaches the recursive occurrence. The second reaches it at every stage.

*Further reading · Sources.* Reynolds, _Theories of Programming Languages_, §§2.3–2.4, defines domains and continuous functions and proves the least fixed-point theorem in general. _Concrete Semantics_, §11.1, defines loop meanings as relations: Example 11.2 is the loop $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`, and Example 11.14 computes the approximations of a countdown loop. Leroy’s course, §9.1, computes a least fixed point by iterating from a least element when every strictly increasing sequence is finite. The iteration then stops at a finite stage, which the further problem shows cannot be expected for loop meanings. [Reynolds, contents](https://www.cs.cmu.edu/~jcr/tpl-toc.html) · [Concrete Semantics, §11.1](https://concrete-semantics.org/concrete-semantics.pdf#page=190) · [Leroy’s course, fixed points](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Fixpoints.lean)

*Further reading · Special lecture S2.* The organizer’s special lecture [S2 (order, approximation and fixed points)](static/slides/s2/index.html) proves the least fixed-point theorem for continuous functions in general and obtains the loop meaning of this session as an instance.

# Sources and Formalization
%%%
tag := "ch09-notes"
number := false
%%%

Reynolds, _Theories of Programming Languages_, §2.4, proves the least fixed-point theorem for continuous functions and uses it to define the meaning of a loop as a state transformer. We prove the instance for the unfolding operator of a loop directly. Nipkow and Klein prove the same statement for continuous functions on sets and apply it to loop meanings that are relations between states. [Reynolds, contents](https://www.cs.cmu.edu/~jcr/tpl-toc.html) · [Concrete Semantics, §11.1.2, p. 185](https://concrete-semantics.org/concrete-semantics.pdf#page=195)

* *Lemma 9.2.* Formulated in this book. Corresponds to CS Lemma 11.3. Checked in Lean ([`unfoldMono`](lean/Denotation.html#unfoldMono) · [IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 9.3.* Formulated in this book. Checked in Lean ([`approxIncreasing`](lean/Denotation.html#approxIncreasing) · [IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 9.5.* Source: Reynolds §2.4, specialized to loop unfolding. Corresponds to CS Theorem 11.12. Checked in Lean ([`whileDenotationLeastFixed`](lean/Denotation.html#whileDenotationLeastFixed) · [IMP card references](imp-card/index.html#imp-sources)).
