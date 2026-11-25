import VersoManual

open Verso.Genre Manual

#doc (Manual) "Abstract Interpretation and Analysis Soundness" =>
%%%
tag := "ch17"
file := "chapter-17"
%%%

Consider the command `if y ≤ 0 then (x := 7; z := 0) else (x := 7; z := 1)`, run from a store about which nothing is known. Which branch runs depends on the value of $`y`, so a compiler cannot decide it. Still, every terminating run ends with 7 at $`x`. A following `w := x + 1` could therefore be compiled as `w := 8`. If the second branch assigned 8 to $`x`, the claim “$`x` is 7” would be false on some runs. This session makes “known” precise, computes the known facts for every command, and proves that they hold in every final store. Session 18 uses these facts to rewrite programs.

*In this session.*

* *Definitions.* Stores, update and $`\mathrm{eval}` ([IMP language card A.2–A.3](imp-card/index.html#imp-a2)). Guards and their values $`B(b,s)` ([A.4](imp-card/index.html#imp-a4)). The execution judgment $`s\vdash c\Downarrow t` and its six rules ([A.5](imp-card/index.html#imp-a5)). Induction on execution derivations by height ([Session 3, §3.1](chapter-03/index.html#ch03-s1)). The invariant argument for a loop execution ([Session 12, §12.3](chapter-12/index.html#ch12-s3)).
* *New terms.* Abstract store, concretization, precision order, join, abstract transfer. [Glossary](glossary/index.html)
* *Theorem 17.8 (Soundness of the analysis).* For every command $`c`, stores $`s,t` and abstract store $`A`, if $`s\vdash c\Downarrow t` and $`s\in\gamma(A)`, then $`t\in\gamma(f^{\sharp}_{c}(A))`.
* *Board case.* Conditional. Invert the execution to find the branch that ran, then split on the abstract value of the guard. When that value is $`\top`, pass from the branch result to the join with Lemma 17.3.
* *Proof outline.* Structural induction on $`c` with $`P(c)\coloneqq\forall s,t,A,\ (s\vdash c\Downarrow t\land s\in\gamma(A))\Rightarrow t\in\gamma(f^{\sharp}_{c}(A))`. The abstract store is quantified inside $`P(c)` because the sequence case applies the hypothesis for $`c_2` at $`f^{\sharp}_{c_1}(A)`. In the loop case, fix $`X=f^{\sharp}_{W}(A)` and prove $`s\in\gamma(X)\Rightarrow t\in\gamma(X)` by a second induction on the loop execution, using Lemma 17.7.
* *From Session 16.* Session 16 proved a property of every terminating execution by induction on its derivation, with the code position and the stack quantified inside the induction property. Here the outer induction is on the command, because the abstract transfer is defined by recursion on the command, and the abstract store is quantified inside. Induction on derivations returns inside the loop case, as in Session 12.

# Abstract stores
%%%
tag := "ch17-s1"
%%%

After the conditional above, the analysis should record one fact, $`x=7`, and nothing about $`y` or $`z`. A finite list of such facts describes a set of stores.

*Definition 17.1 (Abstract stores and concretization).* An *abstract value* is an integer or the symbol $`\top`, read “unknown”. Write $`\mathbb Z^{\top}=\mathbb Z\cup\{\top\}`. An *abstract store* is a function $`A:\mathrm{Name}\to\mathbb Z^{\top}` with $`A(x)=\top` for all but finitely many names $`x`. Write $`\Sigma^{\sharp}` for the set of abstract stores. An *entry* of $`A` is a pair $`x\mapsto n` with $`A(x)=n\in\mathbb Z`. We write an abstract store by listing its entries, as in $`\{x\mapsto7\}`. The abstract store $`\{\}` has no entries. The update $`A[x\mapsto a]` is defined as for stores (A.2). When $`a=\top` it removes the entry for $`x`. The *concretization* of $`A` is the set of stores

$$`\gamma(A)=\{\,s\in\Sigma\mid s(x)=n\ \text{for every entry}\ x\mapsto n\ \text{of}\ A\,\}.`

We say that $`A` *describes* $`s` when $`s\in\gamma(A)`. For example, $`\gamma(\{x\mapsto7\})` is the set of stores with $`s(x)=7`, whatever their values at other names, and $`\gamma(\{\})=\Sigma`.

Take $`A_1=\{x\mapsto3,\ y\mapsto5\}` and $`A_2=\{x\mapsto3\}`. Every entry of $`A_2` is an entry of $`A_1`. A store described by $`A_1` has 3 at $`x`, so it is described by $`A_2`. The store with 3 at $`x` and 8 at $`y` is described by $`A_2` but not by $`A_1`. Thus $`A_1` records more and describes fewer stores.

*Definition 17.2 (Precision order and join).* For abstract values $`a,a'` define

$$`a\sqsubseteq a'\quad\text{means}\quad a'=\top\ \text{or}\ a=a'.`

For abstract stores define $`A\sqsubseteq A'` when $`A(x)\sqsubseteq A'(x)` for every name $`x`. Equivalently, every entry of $`A'` is an entry of $`A`. The *join* of abstract values is $`a\sqcup a'=a` if $`a=a'`, and $`a\sqcup a'=\top` otherwise. The join of abstract stores is taken name by name, $`(A\sqcup A')(x)=A(x)\sqcup A'(x)`. Its entries are the entries common to $`A` and $`A'`.

Read $`A\sqsubseteq A'` as “$`A` is at least as precise as $`A'`”. The smaller side records more entries and describes fewer stores. In the example above $`A_1\sqsubseteq A_2`. The greatest abstract store is $`\{\}`. It records nothing and describes every store. This order has the shape of the information order of [Session 8, Definition 8.7](chapter-08/index.html#ch08-s4) turned upside down: there $`\bot` is least and the smaller outcome carries less information, while here $`\top` is greatest and the smaller abstract store carries more.

In the opening example the two branches end with $`\{x\mapsto7,\ z\mapsto0\}` and $`\{x\mapsto7,\ z\mapsto1\}`. Their join is $`\{x\mapsto7\}`. It lies above both. Any abstract store above both can contain only common entries, so it lies above the join. The join describes every store that either branch result describes, and more: a store with 7 at $`x` and 5 at $`z` is described by the join but by neither branch result.

*Lemma 17.3 (Order, join and concretization).* For all abstract stores $`A,A'`: (a) if $`A\sqsubseteq A'` then $`\gamma(A)\subseteq\gamma(A')`; (b) $`A\sqsubseteq A\sqcup A'` and $`A'\sqsubseteq A\sqcup A'`; (c) $`A\sqsubseteq\{\}`.

*Proof.* (a) Let $`s\in\gamma(A)` and let $`x\mapsto n` be an entry of $`A'`. It is an entry of $`A`, so $`s(x)=n`. (b) Every entry of $`A\sqcup A'` is an entry of $`A` and of $`A'`. (c) $`\{\}` has no entries. $`\square`

# Abstract transfer
%%%
tag := "ch17-s2"
%%%

Let $`A=\{x\mapsto7\}`. The expression $`x+1` has the value 8 in every store described by $`A`. The expression $`x+y` has no known value, since $`A` records nothing about $`y`. The guard $`y\le0` has no known value either, so the analysis of the opening conditional must take both branches into account.

*Definition 17.4 (Abstract evaluation).* For an abstract store $`A`, abstract evaluation follows A.3:

$$`\begin{aligned}
\mathrm{eval}^{\sharp}(n,A)&=n \qquad \mathrm{eval}^{\sharp}(x,A)=A(x)\\
\mathrm{eval}^{\sharp}(e_1+e_2,A)&=n_1+n_2 \qquad \mathrm{eval}^{\sharp}(e_1-e_2,A)=n_1-n_2.
\end{aligned}`

In the second line $`n_1=\mathrm{eval}^{\sharp}(e_1,A)` and $`n_2=\mathrm{eval}^{\sharp}(e_2,A)` must both be integers. If either is $`\top`, the sum and the difference evaluate to $`\top`. The abstract value $`B^{\sharp}(b,A)` of a guard is $`\mathsf{true}`, $`\mathsf{false}` or $`\top`. The constants give their own values. A comparison compares its two operand values when both are integers. Negation exchanges true and false. Conjunction is computed when both operands have value true or false. In every other case the result is $`\top`.

*Lemma 17.5 (Soundness of abstract evaluation).* Let $`s\in\gamma(A)`. For every expression $`e` and integer $`n`, if $`\mathrm{eval}^{\sharp}(e,A)=n` then $`\mathrm{eval}(e,s)=n`. For every guard $`b`, if $`B^{\sharp}(b,A)` is $`\mathsf{true}` or $`\mathsf{false}`, then $`B(b,s)=B^{\sharp}(b,A)`.

*Proof.* Structural induction on $`e` with $`Q(e)\coloneqq\forall n,\ \mathrm{eval}^{\sharp}(e,A)=n\Rightarrow\mathrm{eval}(e,s)=n`. For a literal both sides are the literal. For a variable, $`\mathrm{eval}^{\sharp}(x,A)=n` means that $`x\mapsto n` is an entry of $`A`, so $`s(x)=n`. For a sum with integer value $`n`, both operands have integer values $`n_1,n_2` with $`n=n_1+n_2`. Then $`Q(e_1)` and $`Q(e_2)` give $`\mathrm{eval}(e_1,s)=n_1` and $`\mathrm{eval}(e_2,s)=n_2`, and A.3 gives $`\mathrm{eval}(e_1+e_2,s)=n`. Differences are alike. For guards use structural induction on $`b`. Comparisons use the statement for expressions, and negation and conjunction use the hypotheses for their operands. $`\square`

For the opening command, start from $`\{\}`. The first branch gives $`\{x\mapsto7\}` and then $`\{x\mapsto7,\ z\mapsto0\}`. The second gives $`\{x\mapsto7,\ z\mapsto1\}`. Since $`\mathrm{eval}^{\sharp}(y,\{\})=\top`, the guard has value $`\top`, and the result is the join $`\{x\mapsto7\}`. After `w := x + 1` the abstract store is $`\{x\mapsto7,\ w\mapsto8\}`.

*Definition 17.6 (Abstract transfer).* The abstract transfer $`f^{\sharp}_{c}:\Sigma^{\sharp}\to\Sigma^{\sharp}` of a command $`c` is defined by structural recursion on $`c`. For $`I=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`,

$$`\begin{aligned}
f^{\sharp}_{\mathsf{skip}}(A)&=A\\
f^{\sharp}_{x:=e}(A)&=A[x\mapsto\mathrm{eval}^{\sharp}(e,A)]\\
f^{\sharp}_{c_1;c_2}(A)&=f^{\sharp}_{c_2}(f^{\sharp}_{c_1}(A))\\
f^{\sharp}_{I}(A)&=f^{\sharp}_{c_1}(A)\quad\text{if }B^{\sharp}(b,A)=\mathsf{true}\\
f^{\sharp}_{I}(A)&=f^{\sharp}_{c_2}(A)\quad\text{if }B^{\sharp}(b,A)=\mathsf{false}\\
f^{\sharp}_{I}(A)&=f^{\sharp}_{c_1}(A)\sqcup f^{\sharp}_{c_2}(A)\quad\text{if }B^{\sharp}(b,A)=\top.
\end{aligned}`

For $`W=\mathsf{while}\ b\ \mathsf{do}\ c` and an abstract store $`A`, put $`\Phi_A(X)=A\sqcup f^{\sharp}_{c}(X)` and define the iterates $`X_0=A` and $`X_{j+1}=\Phi_A(X_j)`. Then $`f^{\sharp}_{W}(A)=X_j` for the least $`j<20` with $`X_{j+1}=X_j`. If there is no such $`j`, then $`f^{\sharp}_{W}(A)=\{\}`. Each iterate joins the entry store $`A` with the result of one more abstract run of the body. The guard of the loop is not used. The loop clause applies $`f^{\sharp}_{c}` at abstract stores other than $`A`, which the recursion on the body provides.

Take `x := 0; y := 5; while x ≤ 10 do x := x + 1`. The loop starts from $`A=\{x\mapsto0,\ y\mapsto5\}`. The body gives $`f^{\sharp}_{c}(X_0)=\{x\mapsto1,\ y\mapsto5\}`, so $`X_1=A\sqcup\{x\mapsto1,\ y\mapsto5\}=\{y\mapsto5\}`. Since $`X_1` has no entry for $`x`, $`f^{\sharp}_{c}(X_1)=\{y\mapsto5\}` and $`X_2=\{y\mapsto5\}=X_1`. So $`f^{\sharp}_{W}(A)=\{y\mapsto5\}`. Every run ends with 11 at $`x` and 5 at $`y`, a store this result describes. The entry $`x\mapsto0` of $`A` holds only before the first iteration, and the iteration removes it.

*Lemma 17.7 (Loop result).* Let $`W=\mathsf{while}\ b\ \mathsf{do}\ c`, let $`A` be an abstract store and let $`X=f^{\sharp}_{W}(A)`. Then $`\Phi_A(X)\sqsubseteq X`.

*Proof.* If $`X=X_j` with $`X_{j+1}=X_j`, then $`\Phi_A(X)=X_{j+1}=X`, and $`\sqsubseteq` is reflexive. Otherwise $`X=\{\}`, and Lemma 17.3(c) applies. $`\square`

By Lemma 17.3(b), $`A\sqsubseteq\Phi_A(X)` and $`f^{\sharp}_{c}(X)\sqsubseteq\Phi_A(X)`. Lemma 17.3(a) turns these and Lemma 17.7 into $`\gamma(A)\subseteq\gamma(\Phi_A(X))\subseteq\gamma(X)` and $`\gamma(f^{\sharp}_{c}(X))\subseteq\gamma(\Phi_A(X))\subseteq\gamma(X)`. We name the two resulting inclusions:

$$`\gamma(A)\subseteq\gamma(X)\quad\text{(entry)},\qquad \gamma(f^{\sharp}_{c}(X))\subseteq\gamma(X)\quad\text{(preservation)}.`

In the example, $`X=\{y\mapsto5\}` and $`f^{\sharp}_{c}(X)=X`. The bound of 20 iterations affects only precision. When none of $`X_0,\ldots,X_{19}` is stable, the result $`\{\}` still satisfies Lemma 17.7.

# Soundness of the analysis
%%%
tag := "ch17-s3"
%%%

In the opening example, a run from a store with $`s(y)=3` takes the second branch and ends with 7 at $`x` and 1 at $`z`. The result $`\{x\mapsto7\}` describes this final store. Theorem 17.8 states this for every command, every terminating run, and every abstract store that describes the initial store.

*Theorem 17.8 (Soundness of the analysis).* For every command $`c`, stores $`s,t` and abstract store $`A`, if $`s\vdash c\Downarrow t` and $`s\in\gamma(A)`, then $`t\in\gamma(f^{\sharp}_{c}(A))`.

We prove $`P(c)` for every command $`c` by structural induction, with

$$`P(c)\coloneqq\forall s,t,A,\ \bigl(s\vdash c\Downarrow t\ \land\ s\in\gamma(A)\bigr)\Rightarrow t\in\gamma(f^{\sharp}_{c}(A)).`

*Skip and assignment.* For skip, inversion gives $`t=s`, and $`f^{\sharp}_{\mathsf{skip}}(A)=A`. For $`x:=e`, inversion gives $`t=s[x\mapsto\mathrm{eval}(e,s)]`. Let $`y\mapsto n` be an entry of $`A[x\mapsto\mathrm{eval}^{\sharp}(e,A)]`. If $`y=x`, then $`\mathrm{eval}^{\sharp}(e,A)=n`, and Lemma 17.5 gives $`t(x)=\mathrm{eval}(e,s)=n`. If $`y\neq x`, then $`y\mapsto n` is an entry of $`A`, so $`t(y)=s(y)=n`.

*Sequence.* Let $`c=c_1;c_2`. Assume $`s\vdash c_1;c_2\Downarrow t` and $`s\in\gamma(A)`. Inversion gives a store $`m` with $`s\vdash c_1\Downarrow m` and $`m\vdash c_2\Downarrow t`. Apply $`P(c_1)` at $`s,m,A` to get $`m\in\gamma(f^{\sharp}_{c_1}(A))`. Apply $`P(c_2)` at $`m,t` and the abstract store $`f^{\sharp}_{c_1}(A)` to get $`t\in\gamma(f^{\sharp}_{c_2}(f^{\sharp}_{c_1}(A)))=\gamma(f^{\sharp}_{c_1;c_2}(A))`. The second hypothesis is used at an abstract store other than $`A`. This is why $`P(c)` quantifies $`A`.

*Conditional (board case).* Let $`c=I=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`. The induction hypotheses are as follows. We name the bound stores $`u,v` and the bound abstract store $`A'`.

$$`\begin{aligned}
P(c_1)&:\quad\forall u,v,A',\ \bigl(u\vdash c_1\Downarrow v\land u\in\gamma(A')\bigr)\Rightarrow v\in\gamma(f^{\sharp}_{c_1}(A')),\\
P(c_2)&:\quad\forall u,v,A',\ \bigl(u\vdash c_2\Downarrow v\land u\in\gamma(A')\bigr)\Rightarrow v\in\gamma(f^{\sharp}_{c_2}(A')).
\end{aligned}`

1. Fix $`s,t,A`. Assume $`D:s\vdash I\Downarrow t` and $`s\in\gamma(A)`. We must show $`t\in\gamma(f^{\sharp}_{I}(A))`.
2. The conditional rule is the only rule of A.5 for a conditional. Inversion of $`D` gives $`s\vdash k\Downarrow t`, where $`k` is $`c_1` if $`B(b,s)=\mathsf{true}` and $`c_2` if $`B(b,s)=\mathsf{false}`.
3. Apply $`P(k)` with $`u=s`, $`v=t` and $`A'=A`. This gives $`t\in\gamma(f^{\sharp}_{k}(A))`.
4. Case $`B^{\sharp}(b,A)=\mathsf{true}`. Lemma 17.5, applied to $`s\in\gamma(A)`, gives $`B(b,s)=\mathsf{true}`. So $`k=c_1`, and by Definition 17.6 $`f^{\sharp}_{I}(A)=f^{\sharp}_{c_1}(A)=f^{\sharp}_{k}(A)`. Step 3 is the claim.
5. Case $`B^{\sharp}(b,A)=\mathsf{false}`. In the same way $`B(b,s)=\mathsf{false}`, $`k=c_2` and $`f^{\sharp}_{I}(A)=f^{\sharp}_{k}(A)`.
6. Case $`B^{\sharp}(b,A)=\top`. Then $`f^{\sharp}_{I}(A)=f^{\sharp}_{c_1}(A)\sqcup f^{\sharp}_{c_2}(A)`. Whether $`k` is $`c_1` or $`c_2`, Lemma 17.3(b) gives $`f^{\sharp}_{k}(A)\sqsubseteq f^{\sharp}_{I}(A)`. Lemma 17.3(a) turns this into $`\gamma(f^{\sharp}_{k}(A))\subseteq\gamma(f^{\sharp}_{I}(A))`. With step 3, $`t\in\gamma(f^{\sharp}_{I}(A))`.

Step 6 does not need to know which branch ran. The analysis sees $`\top` for the guard, while the run computes a definite $`B(b,s)`. Inversion in step 2 already names the branch, and the join lies above both branch results. In steps 4 and 5, Lemma 17.5 excludes a run through the other branch: a guard value known from $`A` is the value in every store that $`A` describes.

*Loop.* Let $`c=W=\mathsf{while}\ b\ \mathsf{do}\ c_1` (we write $`c_1` for the body because $`c` names the whole command). Then $`\Phi_A(X)=A\sqcup f^{\sharp}_{c_1}(X)`, and the hypothesis is $`P(c_1)`. Fix $`A` and put $`X=f^{\sharp}_{W}(A)`. We must show

$$`\forall s,t,\ \bigl(s\vdash W\Downarrow t\ \land\ s\in\gamma(A)\bigr)\Rightarrow t\in\gamma(X).`

The hypothesis $`P(c_1)` covers executions of the body. A derivation of $`s\vdash W\Downarrow t` also contains a further execution of $`W`, which no structural hypothesis covers. So we use a second induction, on the derivation $`D:s\vdash W\Downarrow t` ([Session 3, §3.1](chapter-03/index.html#ch03-s1)), with $`X` fixed:

$$`L(D)\coloneqq s\in\gamma(X)\Rightarrow t\in\gamma(X).`

If $`D` ends with the loop exit rule, then $`t=s` and $`L(D)` holds. Suppose $`D` ends with the loop iteration rule, with premises $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash W\Downarrow t`. The hypothesis for $`D_2` is $`L(D_2):m\in\gamma(X)\Rightarrow t\in\gamma(X)`. Assume $`s\in\gamma(X)`.

1. Apply $`P(c_1)` with $`u=s`, $`v=m` and $`A'=X`. This gives $`m\in\gamma(f^{\sharp}_{c_1}(X))`.
2. The preservation inclusion gives $`m\in\gamma(X)`.
3. $`L(D_2)` gives $`t\in\gamma(X)`.

Finally let $`D:s\vdash W\Downarrow t` and $`s\in\gamma(A)`. The entry inclusion gives $`s\in\gamma(X)`, and $`L(D)` gives $`t\in\gamma(X)`. This completes the induction. $`\square`

For a loop, then, two facts about the single abstract store $`X` must be shown. Every store described by $`A` is described by $`X` (entry). One execution of the body from a store described by $`X` ends in a store described by $`X` (preservation). The guard plays no role. The property $`L` keeps $`X` fixed, while $`P` lets the abstract store vary. This is the argument of Session 12, §12.3, with $`\gamma(X)` as the loop invariant.

Theorem 17.8 speaks only about terminating executions, and it gives an inclusion. In the opening example the result $`\{x\mapsto7\}` also describes stores with 5 at $`z`, which no run reaches. Soundness says that every recorded fact is true. It does not say that every true fact is recorded (Exercise 17.3).

# Exercises
%%%
tag := "ch17-s4"
number := false
%%%

*17.1.* Compute the join of $`\{x\mapsto7,\ y\mapsto2\}` and $`\{x\mapsto7,\ y\mapsto3,\ z\mapsto0\}`. Give a store described by the join but by neither operand.

*17.2.* Suppose the transfer of $`x:=e` kept the old entry for $`x` when $`\mathrm{eval}^{\sharp}(e,A)=\top`. Using `x := y` and $`A=\{x\mapsto4\}`, find a run that violates Theorem 17.8. Which sentence of the assignment case fails?

*17.3.* Let $`A` have no entry for $`x`. Compute $`\mathrm{eval}^{\sharp}(x-x,A)` and compare it with $`\mathrm{eval}(x-x,s)`. Does this contradict Theorem 17.8?

*17.4.* Suppose the loop transfer returned $`A` itself. Let $`W` be `while x ≤ 0 do x := x + 1` and $`A=\{x\mapsto0\}`. Find a run of $`W` that violates Theorem 17.8. Which of the two inclusions fails? Compute $`f^{\sharp}_{W}(A)` by Definition 17.6.

*Further problem.* Design two branch results whose join describes stores that neither describes. Find an equation between two variables that holds in every store either branch result describes. Prove that no single abstract store describes exactly the union of the two sets of stores.

# Reading for the Seminar
%%%
tag := "ch17-s5"
number := false
%%%

*Definitions · 10 minutes.* Read an abstract store as a list of equations that a store must satisfy. Compute the join in the opening example and the iterates $`X_0,X_1,X_2` of the loop example in §17.2.

*Joint proof · 30 minutes.* Write $`P(c)` and the two hypotheses of the conditional case. Prove the case for all three values of $`B^{\sharp}(b,A)`. In step 6, consider both branches the run may have taken, and justify the passage to the join by the direction of the order.

*Proof review · 20 minutes.* State the two inclusions the loop case needs and check them for the loop example. Use Exercise 17.4 to see which inclusion fails when the loop transfer returns $`A`. Find a store described by a join that no run reaches, and check that it does not contradict Theorem 17.8.

*Facilitator’s hint.* Pick an entry of the join. Which two branch results had to agree on that name and that value?

# Solutions and Further Reading
%%%
tag := "ch17-s6"
number := false
%%%

*17.1.* The join is $`\{x\mapsto7\}`. A store with 7 at $`x` and 99 at $`y` is described by the join. Whatever its value at $`z`, it is described by neither operand, since $`99\neq2` and $`99\neq3`.

*17.2.* Take $`s` with $`s(x)=4` and $`s(y)=6`. Then $`s\in\gamma(\{x\mapsto4\})`, and the run ends in $`t=s[x\mapsto6]`. Since $`\mathrm{eval}^{\sharp}(y,A)=\top`, the modified transfer returns $`\{x\mapsto4\}`, which does not describe $`t`. The failing sentence is the case $`y=x`: it assumes that the entry for $`x` in the result comes from $`\mathrm{eval}^{\sharp}(e,A)=n`. The kept entry $`x\mapsto4` does not.

*17.3.* $`\mathrm{eval}^{\sharp}(x,A)=\top`, so $`\mathrm{eval}^{\sharp}(x-x,A)=\top`, while $`\mathrm{eval}(x-x,s)=0` in every store. There is no contradiction. Lemma 17.5 speaks only when the abstract value is an integer, and Theorem 17.8 only asks that recorded entries be true. A transfer that recognized the repeated operand would also be sound, and more precise.

*17.4.* From a store with $`s(x)=0` the body runs once and gives $`m` with $`m(x)=1`. The guard is then false, so $`t=m`, and $`A=\{x\mapsto0\}` does not describe $`t`. With $`X=A` the entry inclusion holds, but preservation fails. For the body $`c`, which is `x := x + 1`, $`f^{\sharp}_{c}(A)=\{x\mapsto1\}`, and $`\gamma(\{x\mapsto1\})\not\subseteq\gamma(\{x\mapsto0\})`. By Definition 17.6, $`X_1=\{x\mapsto0\}\sqcup\{x\mapsto1\}=\{\}`. Since $`f^{\sharp}_{c}(\{\})=\{\}`, also $`X_2=\{\}=X_1`, so $`f^{\sharp}_{W}(A)=\{\}`.

*Further problem.* Use the results recording $`(x,y)=(2,3)` and $`(x,y)=(5,6)`, with no other entries. Every store they describe satisfies $`y=x+1`. An abstract store that describes the stores of both cannot have an entry for $`x` or $`y`, since each takes two values. It cannot have an entry for another name, which is unrestricted in both sets. So it is $`\{\}`, which describes, for instance, a store with $`(x,y)=(2,6)`. That store violates the equation. The loss comes from describing the result by one abstract store, not from the guard. Even the two exact branch results cannot be joined without it.

*Further reading · A lost relation.* Start from $`\{\}` and let one branch set $`(x,y)` to $`(0,0)` and the other to $`(1,1)`. The join is $`\{\}`, which also describes $`(0,1)`. The equation $`x=y` holds after both branches, but no abstract store can record a relation between two names. A later `w := x - y` gives 0 on every run, yet the analysis after the join gives $`\mathrm{eval}^{\sharp}(x-y,\{\})=\top`. A transformation that needs this fact must find it by other means, such as simplifying inside each branch or tracking equalities between variables. Theorem 17.8 still holds. It only gives too little information here.

*Further reading · Sets of final stores.* For a set $`M` of stores, let $`\mathrm{post}_c(M)=\{t\mid\exists s\in M,\ s\vdash c\Downarrow t\}`. Theorem 17.8 says $`\mathrm{post}_c(\gamma(A))\subseteq\gamma(f^{\sharp}_{c}(A))` for every $`c` and $`A`. In the opening example the inclusion is strict. _Concrete Semantics_, §13.3, builds this view of sets of stores into a collecting semantics, and §§13.4–13.5 prove a generic abstract interpreter correct against it.

*Further reading · Iteration without a bound.* Leroy’s course also gives a loop transfer without the bound of 20. It proves that this transfer is monotone, that is, $`A\sqsubseteq A'` implies $`f^{\sharp}_{c}(A)\sqsubseteq f^{\sharp}_{c}(A')`. It also proves that every strictly increasing sequence of abstract stores is finite, because each strict step up removes an entry. Iterating $`\Phi_A` from $`A` therefore stops at an $`X` with $`\Phi_A(X)=X`, and this $`X` lies below every abstract store $`Y` with $`\Phi_A(Y)\sqsubseteq Y`. The loop case of §17.3 needs only the entry and preservation inclusions, and the course proves the order facts behind them for this version too. Compare the least fixed point of a loop meaning in [Session 9](chapter-09/index.html), which is approached by approximations that become more defined. Here the iterates become less precise.

*Further reading · Sources.* Nipkow and Klein, _Concrete Semantics_, §10.2, analyse constant propagation with a table of constants. Their Lemma 10.9 (p. 162) has the shape of Theorem 17.8. Their transfer does not evaluate guards and does not iterate at loops. Their §§13.1–13.5 develop abstract interpretation in general, and §13.6.2 (p. 254) obtains constant propagation as an instance. [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf) · [Leroy’s course, constant propagation](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Constprop.lean)

# Sources and Formalization
%%%
tag := "ch17-notes"
number := false
%%%

Abstract stores, their order and join, abstract evaluation, the abstract transfer of commands with its bounded iteration for loops, and Theorem 17.8 are those of the constant propagation chapter of Xavier Leroy’s _Compiler Verification_ course. Nipkow and Klein prove the same statement for their table of constants. Their transfer always joins at a conditional and, at a loop, forgets every variable assigned in the body. [Source and proof references](imp-card/index.html#imp-sources) · [Leroy’s course, constant propagation](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Constprop.lean) · [Concrete Semantics, §10.2, p. 162](https://concrete-semantics.org/concrete-semantics.pdf#page=172)

* *Lemma 17.3.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 17.5.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 17.7.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 17.8.* Corresponds to CS Lemma 10.9. Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
