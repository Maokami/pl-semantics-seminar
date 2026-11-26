import VersoManual
import PLBook.IMP.Hoare

open Verso.Genre Manual

#doc (Manual) "Total Correctness and Termination" =>
%%%
tag := "ch13"
file := "chapter-13"
%%%

Start two loops in a state with $`x=3`. Their guard $`0<x` is the derived notation of [A.4](imp-card/index.html#imp-a4) for $`\neg(x\le0)`, so it is true at $`\sigma` exactly when $`0<\sigma(x)`. The loop $`W_{\mathrm{dec}}=\mathsf{while}\ 0<x\ \mathsf{do}\ x:=x-1` reaches its test with $`x` equal to 3, 2, 1 and 0, and stops. The loop $`W_{\mathrm{skip}}=\mathsf{while}\ 0<x\ \mathsf{do}\ \mathsf{skip}` reaches its test with $`x=3` again and again and never stops. Yet the proof system of Session 12 derives $`\{0\le x\}\,W\,\{x=0\}` for both loops $`W`. This session gives triples a meaning that requires termination, adds to the while rule a number that must decrease, and proves the new rules sound.

*In this session.*

* *Definitions.* States and update ([A.2](imp-card/index.html#imp-a2)). Guards, their values $`B(b,\sigma)` and the derived notations $`e_1<e_2` and $`b_1\lor b_2` ([A.4](imp-card/index.html#imp-a4)). The execution judgment $`\sigma\vdash c\Downarrow\sigma'` and its six rules ([A.5](imp-card/index.html#imp-a5), Session 2, Definition 2.1). Determinacy ([Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2)). Assertions, triples and partial correctness $`\models\{P\}\,c\,\{Q\}` ([Session 11, Definition 11.4](chapter-11/index.html#ch11-s2)). The substituted assertion $`Q[e/x]` ([Session 11, Definition 11.5](chapter-11/index.html#ch11-s3)). Guard assertions $`\mathrm{T}_b,\mathrm{F}_b`, conjunction of assertions and the Hoare proof system $`\vdash_{\mathrm H}` ([Session 12, §§12.1–12.2](chapter-12/index.html#ch12-s1)). Nested induction ([Session 10, §10.3](chapter-10/index.html#ch10-s3)).
* *New terms.* Total correctness, variant, total-correctness proof system, strong induction. [Glossary](glossary/index.html)
* *Theorem 13.3 (Soundness for total correctness).* For all assertions $`P,Q` and every command $`c`, if $`\vdash_{\mathrm{tot}}\{P\}\,c\,\{Q\}` then $`\models_{\mathrm{tot}}\{P\}\,c\,\{Q\}`.
* *Board case.* The total while rule: termination by a variant. Prove $`L(j)` by strong induction on the value $`j` of the variant. In the true-guard case, the hypothesis for the body premise with the same $`j` produces the body’s final state $`\sigma_1`, the induction hypothesis at $`\sigma_1` produces the rest of the loop, and the loop iteration rule joins them. Five steps.
* *Proof outline.* Induction on the derivation $`H` of $`\vdash_{\mathrm{tot}}\{P\}\,c\,\{Q\}` with $`V_{\mathrm{tot}}(H)\coloneqq\forall\sigma,\ P(\sigma)\Rightarrow\exists\sigma',\ \bigl(\sigma\vdash c\Downarrow\sigma'\land Q(\sigma')\bigr)`. Each case builds an execution with a rule of A.5 from the executions that the hypotheses supply. In the while case a nested strong induction on $`j` proves $`L(j)\coloneqq\forall\sigma,\ \bigl(P(\sigma)\land\mu(\sigma)=j\bigr)\Rightarrow\exists\sigma',\ \bigl(\sigma\vdash W\Downarrow\sigma'\land P(\sigma')\land B(b,\sigma')=\mathsf{false}\bigr)`.
* *From Session 12.* A triple valid in the sense of Session 11, Definition 11.4, promises nothing when no execution ends, and the soundness proof of Session 12 inverted a given execution. Here a valid triple promises an execution, and each case of the proof builds one. In the loop case there is no given execution to induct on, so the induction runs on the value of the variant.

# Total correctness
%%%
tag := "ch13-s1"
%%%

In both loops of the opening, the assertion $`0\le x` is a loop invariant ([Session 12, Definition 12.1](chapter-12/index.html#ch12-s1)). The body $`x:=x-1` runs only when $`0<x`, so the new value of $`x` is at least 0. The body $`\mathsf{skip}` changes nothing. When the guard is false, $`0\le x` and $`x\le0` give $`x=0`. So the rules of [Session 12, Definition 12.2](chapter-12/index.html#ch12-s2) derive $`\vdash_{\mathrm H}\{0\le x\}\,W\,\{x=0\}` for $`W=W_{\mathrm{dec}}` and for $`W=W_{\mathrm{skip}}`. [Session 12, Theorem 12.3](chapter-12/index.html#ch12-s3) makes both triples valid.

The second triple is valid for a reason that the triple does not show. Let $`\sigma(x)=1`. The least-height argument of [Session 2, §2.4](chapter-02/index.html#ch02-s4) for $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}` applies to $`W_{\mathrm{skip}}` with one change. The loop exit rule needs $`B(0<x,\sigma)=\mathsf{false}`, which fails because $`\sigma(x)=1`. The body $`\mathsf{skip}` returns $`\sigma`, so the loop premise is again the judgment being derived. Hence $`\sigma\vdash W_{\mathrm{skip}}\Downarrow\sigma'` has no derivation for any $`\sigma'`. Partial correctness holds at $`\sigma` because there is no final state to check.

*Definition 13.1 (Total correctness).* A triple $`\{P\}\,c\,\{Q\}` is *valid for total correctness*, written $`\models_{\mathrm{tot}}\{P\}\,c\,\{Q\}`, when

$$`\forall\sigma,\ P(\sigma)\Rightarrow\exists\sigma',\ \bigl(\sigma\vdash c\Downarrow\sigma'\land Q(\sigma')\bigr).`

Compare [Session 11, Definition 11.4](chapter-11/index.html#ch11-s2). There the final state is quantified by "for every" and appears on the left of the implication. Here it is quantified by "there exists" and must be produced. For $`W_{\mathrm{skip}}` the state with $`\sigma(x)=1` satisfies $`0\le x`, but no $`\sigma'` exists. So $`\models_{\mathrm{tot}}\{0\le x\}\,W_{\mathrm{skip}}\,\{x=0\}` fails. For $`W_{\mathrm{dec}}` the run from a state with $`0\le\sigma(x)` ends after $`\sigma(x)` executions of the body, in a state with $`x=0`. §13.3 proves that such a run exists from every such state.

The definition asks for one terminating execution whose final state satisfies $`Q`. IMP is deterministic ([Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2)), so $`\sigma'` is the only final state from $`\sigma`. Hence every triple valid for total correctness is also valid for partial correctness (Exercise 13.1). Nipkow and Klein note that their definition assumes a deterministic language. With a command that chooses between two commands, one run could satisfy $`Q` while another does not.

# Variants and the total while rule
%%%
tag := "ch13-s2"
%%%

Why does $`W_{\mathrm{dec}}` stop? At its successive tests $`x` takes the values 3, 2, 1, 0. Each execution of the body lowers $`x` by one, and $`x` cannot go below 0 while the invariant holds. A natural number cannot decrease forever. In $`W_{\mathrm{skip}}` the same quantity stays at 3.

A *variant* is a function $`\mu:\Sigma\to\mathbb N` from states to natural numbers. It is a mathematical function, not part of the program. It may use any mathematical operation, and the program never computes it. For $`W_{\mathrm{dec}}` take $`\mu(\sigma)=\max(\sigma(x),0)`. The maximum makes $`\mu(\sigma)` a natural number at every state, and $`\mu(\sigma)=\sigma(x)` at every state with $`0\le\sigma(x)`. Nipkow and Klein use the same device in their Example 12.12. In general, an integer quantity that has a lower bound on the states satisfying the invariant becomes a variant in this way: subtract the bound and take the maximum with 0.

To say that the body lowers $`\mu`, we must compare the value of $`\mu` at the final state with its value at the initial state. An assertion sees only one state. So we record the initial value in a natural number $`j`, fixed before the body runs. For a variant $`\mu` and $`j\in\mathbb N`, define the assertions

$$`(\mu=j)(\sigma)\coloneqq\bigl(\mu(\sigma)=j\bigr),\qquad(\mu<j)(\sigma)\coloneqq\bigl(\mu(\sigma)<j\bigr).`

The triple $`\{P\wedge\mathrm{T}_b\wedge(\mu=j)\}\,c\,\{P\wedge(\mu<j)\}` says that the body, started at a state where the variant equals $`j`, ends at a state where the variant is below the same $`j`. The number $`j` is not a program name, and the body cannot change it. Without $`j`, the postcondition could only compare $`\mu` at the final state with itself.

*Definition 13.2 (Total-correctness proof system).* Write $`\vdash_{\mathrm{tot}}\{P\}\,c\,\{Q\}` when the triple has a derivation by the following rules. The Hoare skip, Hoare assignment, Hoare sequence and Hoare conditional rules and the consequence rule are those of Session 12, Definition 12.2, with $`\vdash_{\mathrm H}` replaced by $`\vdash_{\mathrm{tot}}`. The while rule is replaced by the *total while rule*, in which $`\mu` is a variant:

$$`\frac{\forall j\in\mathbb N,\ \vdash_{\mathrm{tot}}\{P\wedge\mathrm{T}_b\wedge(\mu=j)\}\ c\ \{P\wedge(\mu<j)\}}{\vdash_{\mathrm{tot}}\{P\}\ \mathsf{while}\ b\ \mathsf{do}\ c\ \{P\wedge\mathrm{F}_b\}}`

There are two well-founded arguments in the soundness proof. One passes from the proof of a triple to a proof of one of its premises. Inside the loop case another passes from the current value of the variant to a smaller natural number. Only the second argument needs the measure supplied by the program proof.

The total while rule has one premise for each natural number $`j`. So a derivation in this system is not a finite tree as in [A.3](imp-card/index.html#imp-a3): it can branch infinitely often at this rule. Every path from its root still ends after finitely many rules, and in this session a derivation means such a tree. Induction on derivations ([Session 1, §1.5](chapter-01/index.html#ch01-s5)) still applies; "Derivations with infinitely many premises" in the Solutions and Further Reading gives the reason. At the total while rule there is one induction hypothesis for each $`j`. In practice one derives the premise once, for an arbitrary fixed $`j`.

*A derivation for $`W_{\mathrm{dec}}`.* Write $`b` for $`0<x`, $`P` for $`0\le x`, and $`\mu(\sigma)=\max(\sigma(x),0)`. Fix $`j\in\mathbb N`. Each line follows from earlier lines by the rule named at its end.

1. $`\vdash_{\mathrm{tot}}\{(P\wedge(\mu<j))[(x-1)/x]\}\ x:=x-1\ \{P\wedge(\mu<j)\}`. Hoare assignment rule.
2. $`\vdash_{\mathrm{tot}}\{P\wedge\mathrm{T}_b\wedge(\mu=j)\}\ x:=x-1\ \{P\wedge(\mu<j)\}`. Consequence rule on line 1. For the first implication assume $`0\le\sigma(x)`, $`0<\sigma(x)` and $`\max(\sigma(x),0)=j`. Then $`j=\sigma(x)\ge1`. The precondition of line 1 holds at $`\sigma` when $`0\le\sigma(x)-1` and $`\max(\sigma(x)-1,0)<j`. Both hold, because $`\sigma(x)-1=j-1\ge0`. The second implication is $`\forall\sigma',\ (P\wedge(\mu<j))(\sigma')\Rightarrow(P\wedge(\mu<j))(\sigma')`.
3. $`\vdash_{\mathrm{tot}}\{P\}\ W_{\mathrm{dec}}\ \{P\wedge\mathrm{F}_b\}`. Total while rule, with line 2 for every $`j`.
4. $`\vdash_{\mathrm{tot}}\{P\}\ W_{\mathrm{dec}}\ \{x=0\}`. Consequence rule on line 3. The first implication is $`\forall\sigma,\ P(\sigma)\Rightarrow P(\sigma)`. For the second, $`(P\wedge\mathrm{F}_b)(\sigma')` says $`0\le\sigma'(x)` and $`\sigma'(x)\le0`, so $`\sigma'(x)=0`.

For $`W_{\mathrm{skip}}` line 2 has no counterpart. The body $`\mathsf{skip}` returns its initial state, so a variant equal to $`j` before the body is still $`j` after it.

*Choosing a variant.* The variant must decrease at every execution of the body, not only at most of them. Let $`x,y` be distinct names and

$$`W_2=\mathsf{while}\ (0<x\lor 0<y)\ \mathsf{do}\ \bigl(\mathsf{if}\ 0<x\ \mathsf{then}\ x:=x-1\ \mathsf{else}\ y:=y-1\bigr).`

The guard uses the derived notation of A.4 in which $`b_1\lor b_2` abbreviates $`\neg(\neg b_1\land\neg b_2)`. So it is true at $`\sigma` exactly when $`0<\sigma(x)` or $`0<\sigma(y)`. From $`x=1,y=2` the loop tests see $`(x,y)` equal to $`(1,2)`, $`(0,2)`, $`(0,1)` and $`(0,0)`. Take $`P_2\coloneqq(0\le x\land 0\le y)` and $`\mu_2(\sigma)=\max(\sigma(x),0)+\max(\sigma(y),0)`, which equals $`\sigma(x)+\sigma(y)` at states satisfying $`P_2`. Its values at the four tests are 3, 2, 1, 0. The candidate $`\max(\sigma(x),0)` takes the values 1, 0, 0, 0. It stays at 0 during the second and third executions of the body, so it fails the premise of the total while rule.

To check the premise for $`\mu_2`, assume $`P_2(\sigma)`, a true guard and $`\mu_2(\sigma)=j`. If $`0<\sigma(x)`, the body runs $`x:=x-1`. The new value of $`x` is at least 0, and $`\mu_2` becomes $`j-1`. Otherwise $`\sigma(x)=0` by $`P_2`, so the guard gives $`0<\sigma(y)`. The body runs $`y:=y-1`, the new value of $`y` is at least 0, and again $`\mu_2` becomes $`j-1`. A derivation of the premise uses the Hoare conditional rule, with lines 1–2 above adapted to each branch. When the guard is false, $`P_2` gives $`x=y=0`.

# Soundness for total correctness
%%%
tag := "ch13-s3"
%%%

Line 4 of §13.2 should mean the following. From every state with $`0\le\sigma(x)`, the loop $`W_{\mathrm{dec}}` has a terminating execution, and its final state has $`x=0`. That is validity for total correctness. The theorem below gives it for every derivation at once.

*Theorem 13.3 (Soundness for total correctness).* For all assertions $`P,Q` and every command $`c`, if $`\vdash_{\mathrm{tot}}\{P\}\,c\,\{Q\}` then $`\models_{\mathrm{tot}}\{P\}\,c\,\{Q\}`.

We prove $`V_{\mathrm{tot}}(H)` for every derivation $`H` by induction on $`H`. For $`H` with conclusion $`\vdash_{\mathrm{tot}}\{P\}\,c\,\{Q\}` the induction property is

$$`V_{\mathrm{tot}}(H)\coloneqq\forall\sigma,\ P(\sigma)\Rightarrow\exists\sigma',\ \bigl(\sigma\vdash c\Downarrow\sigma'\land Q(\sigma')\bigr).`

Read $`P,c,Q` from the conclusion of $`H`. We write the hypotheses with bound states $`\sigma'',\sigma'''`. In Session 12 each case received an execution and inverted it. Here each case must produce an execution, and it does so by applying a rule of A.5. Except in the while case, fix $`\sigma` with $`P(\sigma)`. We must find $`\sigma'` with $`\sigma\vdash c\Downarrow\sigma'` and $`Q(\sigma')`.

*Hoare skip rule.* Then $`c=\mathsf{skip}` and $`Q=P`. The skip rule gives $`\sigma\vdash\mathsf{skip}\Downarrow\sigma`. Take $`\sigma'=\sigma`. Then $`Q(\sigma')` is $`P(\sigma)`.

*Hoare assignment rule.* Then $`c` is $`x:=e` and $`P=Q[e/x]`. Take $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. The assignment rule gives $`\sigma\vdash x:=e\Downarrow\sigma'`. By the definition of $`Q[e/x]`, $`P(\sigma)` is $`Q(\sigma')`.

*Hoare sequence rule.* Then $`c=(c_1;c_2)`, and the premises are $`H_1:\ \vdash_{\mathrm{tot}}\{P\}\,c_1\,\{R\}` and $`H_2:\ \vdash_{\mathrm{tot}}\{R\}\,c_2\,\{Q\}` for some assertion $`R`. The hypotheses are

$$`\begin{aligned}
V_{\mathrm{tot}}(H_1)&:\quad\forall\sigma'',\ P(\sigma'')\Rightarrow\exists\sigma''',\ \bigl(\sigma''\vdash c_1\Downarrow\sigma'''\land R(\sigma''')\bigr),\\
V_{\mathrm{tot}}(H_2)&:\quad\forall\sigma'',\ R(\sigma'')\Rightarrow\exists\sigma''',\ \bigl(\sigma''\vdash c_2\Downarrow\sigma'''\land Q(\sigma''')\bigr).
\end{aligned}`

$`V_{\mathrm{tot}}(H_1)` with $`\sigma''=\sigma` gives a state $`\sigma_1` with $`\sigma\vdash c_1\Downarrow\sigma_1` and $`R(\sigma_1)`. $`V_{\mathrm{tot}}(H_2)` with $`\sigma''=\sigma_1` gives a state $`\sigma'` with $`\sigma_1\vdash c_2\Downarrow\sigma'` and $`Q(\sigma')`. The sequence rule gives $`\sigma\vdash(c_1;c_2)\Downarrow\sigma'`.

*Hoare conditional rule.* Then $`c=I=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`, and the premises are $`H_1:\ \vdash_{\mathrm{tot}}\{P\wedge\mathrm{T}_b\}\,c_1\,\{Q\}` and $`H_2:\ \vdash_{\mathrm{tot}}\{P\wedge\mathrm{F}_b\}\,c_2\,\{Q\}`. The hypotheses are

$$`\begin{aligned}
V_{\mathrm{tot}}(H_1)&:\quad\forall\sigma'',\ \bigl(P(\sigma'')\land B(b,\sigma'')=\mathsf{true}\bigr)\Rightarrow\exists\sigma''',\ \bigl(\sigma''\vdash c_1\Downarrow\sigma'''\land Q(\sigma''')\bigr),\\
V_{\mathrm{tot}}(H_2)&:\quad\forall\sigma'',\ \bigl(P(\sigma'')\land B(b,\sigma'')=\mathsf{false}\bigr)\Rightarrow\exists\sigma''',\ \bigl(\sigma''\vdash c_2\Downarrow\sigma'''\land Q(\sigma''')\bigr).
\end{aligned}`

If $`B(b,\sigma)=\mathsf{true}`, then $`V_{\mathrm{tot}}(H_1)` with $`\sigma''=\sigma` gives $`\sigma'` with $`\sigma\vdash c_1\Downarrow\sigma'` and $`Q(\sigma')`. The branch selected by $`B(b,\sigma)` is $`c_1`, so the conditional rule of A.5 gives $`\sigma\vdash I\Downarrow\sigma'`. Otherwise $`B(b,\sigma)=\mathsf{false}`, $`V_{\mathrm{tot}}(H_2)` gives $`\sigma'` with $`\sigma\vdash c_2\Downarrow\sigma'` and $`Q(\sigma')`, and the conditional rule with selected branch $`c_2` gives $`\sigma\vdash I\Downarrow\sigma'`.

*Consequence rule.* The premises are $`\forall\sigma,\ P(\sigma)\Rightarrow P_1(\sigma)`, a derivation $`H_1:\ \vdash_{\mathrm{tot}}\{P_1\}\,c\,\{Q_1\}` and $`\forall\sigma',\ Q_1(\sigma')\Rightarrow Q(\sigma')`. Only $`H_1` has a hypothesis: $`V_{\mathrm{tot}}(H_1):\ \forall\sigma'',\ P_1(\sigma'')\Rightarrow\exists\sigma''',\ \bigl(\sigma''\vdash c\Downarrow\sigma'''\land Q_1(\sigma''')\bigr)`. The first implication gives $`P_1(\sigma)`. $`V_{\mathrm{tot}}(H_1)` with $`\sigma''=\sigma` gives $`\sigma'` with $`\sigma\vdash c\Downarrow\sigma'` and $`Q_1(\sigma')`. The second implication gives $`Q(\sigma')`.

*Total while rule: termination by a variant.* Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`. We write $`c_1` for the body because $`c` names the whole command. Suppose $`H` ends with the total while rule, with variant $`\mu`. Then $`c=W`, $`Q=P\wedge\mathrm{F}_b`, and for each $`j\in\mathbb N` there is a premise $`H_j:\ \vdash_{\mathrm{tot}}\{P\wedge\mathrm{T}_b\wedge(\mu=j)\}\,c_1\,\{P\wedge(\mu<j)\}`. For every $`j\in\mathbb N` its hypothesis is

$$`V_{\mathrm{tot}}(H_j):\quad\forall\sigma'',\ \bigl(P(\sigma'')\land B(b,\sigma'')=\mathsf{true}\land\mu(\sigma'')=j\bigr)\Rightarrow\exists\sigma''',\ \bigl(\sigma''\vdash c_1\Downarrow\sigma'''\land P(\sigma''')\land\mu(\sigma''')<j\bigr).`

We must show

$$`V_{\mathrm{tot}}(H):\quad\forall\sigma,\ P(\sigma)\Rightarrow\exists\sigma',\ \bigl(\sigma\vdash W\Downarrow\sigma'\land P(\sigma')\land B(b,\sigma')=\mathsf{false}\bigr).`

In Session 12 the while case was an induction on a given execution of $`W`. Here no execution is given, since producing one is the goal. A nested induction runs instead on the value of the variant at the initial state. For $`j\in\mathbb N` the induction property is

$$`L(j)\coloneqq\forall\sigma,\ \bigl(P(\sigma)\land\mu(\sigma)=j\bigr)\Rightarrow\exists\sigma',\ \bigl(\sigma\vdash W\Downarrow\sigma'\land P(\sigma')\land B(b,\sigma')=\mathsf{false}\bigr).`

We prove $`L(j)` for every $`j` by *strong induction*: we prove $`L(j)` assuming $`L(j')` for every $`j'<j`. This principle follows from ordinary induction on $`j` applied to the property $`\forall j'<j,\ L(j')`. [Session 3, §3.1](chapter-03/index.html#ch03-s1) used it for the height of a derivation. Fix $`j`. The induction hypothesis is

$$`\forall j'<j,\ L(j').`

Fix $`\sigma` with $`P(\sigma)` and $`\mu(\sigma)=j`. We must show $`\exists\sigma',\ \bigl(\sigma\vdash W\Downarrow\sigma'\land P(\sigma')\land B(b,\sigma')=\mathsf{false}\bigr)`.

*Guard false.* If $`B(b,\sigma)=\mathsf{false}`, the loop exit rule gives $`\sigma\vdash W\Downarrow\sigma`. Take $`\sigma'=\sigma`. Then $`P(\sigma')` holds and $`B(b,\sigma')=\mathsf{false}`.

*Guard true.* Suppose $`B(b,\sigma)=\mathsf{true}`.

1. We have $`P(\sigma)`, $`B(b,\sigma)=\mathsf{true}` and $`\mu(\sigma)=j`.
2. Apply $`V_{\mathrm{tot}}(H_j)`, the hypothesis of the premise for this same $`j`, with $`\sigma''=\sigma` to the three facts of step 1. It gives a state $`\sigma_1` with $`D_1:\sigma\vdash c_1\Downarrow\sigma_1`, $`P(\sigma_1)` and $`\mu(\sigma_1)<j`.
3. Put $`j'=\mu(\sigma_1)`. Since $`j'<j`, the induction hypothesis gives $`L(j')`. Apply $`L(j')` at the state $`\sigma_1` to $`P(\sigma_1)` and $`\mu(\sigma_1)=j'`. It gives a state $`\sigma'` with $`D_2:\sigma_1\vdash W\Downarrow\sigma'`, $`P(\sigma')` and $`B(b,\sigma')=\mathsf{false}`.
4. The loop iteration rule, with side condition $`B(b,\sigma)=\mathsf{true}` and premises $`D_1` and $`D_2`, gives $`\sigma\vdash W\Downarrow\sigma'`.
5. So this $`\sigma'` satisfies $`\sigma\vdash W\Downarrow\sigma'`, $`P(\sigma')` and $`B(b,\sigma')=\mathsf{false}`, as required.

This proves $`L(j)` for every $`j`. To prove $`V_{\mathrm{tot}}(H)`, fix $`\sigma` with $`P(\sigma)`, put $`j=\mu(\sigma)`, and apply $`L(j)`. Every rule of Definition 13.2 preserves $`V_{\mathrm{tot}}`, so $`V_{\mathrm{tot}}(H)` holds for every derivation $`H`. $`\square`

*Where each condition of the rule is used.* There is no separate base case. When $`j=0` the induction hypothesis is empty, but the true-guard case cannot occur: step 2 would give a natural number $`\mu(\sigma_1)<0`. Step 2 uses only the premise $`H_j` with $`j=\mu(\sigma)`, the value fixed before the body runs. It needs a total premise, because a partial premise would not produce $`\sigma_1` (Exercise 13.4). Step 3 needs strict decrease, because $`L(j)` itself is not among the hypotheses (Exercise 13.3). Step 3 also applies $`L(j')` at the state $`\sigma_1`, not at $`\sigma`. This is why $`\sigma` is quantified inside $`L(j)`, as the final state was quantified inside the induction property of [Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2).

Applied to line 4 of §13.2, Theorem 13.3 gives $`\models_{\mathrm{tot}}\{0\le x\}\,W_{\mathrm{dec}}\,\{x=0\}`. From $`\sigma(x)=3` the proof of $`L(3)` uses $`L(2)` at the state with $`x=2`, which uses $`L(1)`, which uses $`L(0)`. At $`x=0` the guard is false and the loop exit rule ends the derivation. For $`W_{\mathrm{skip}}` the triple $`\{0\le x\}\,W_{\mathrm{skip}}\,\{x=0\}` is not valid for total correctness (§13.1). By Theorem 13.3 it has no derivation in the total-correctness proof system, whatever variant one tries.

# Exercises
%%%
tag := "ch13-s4"
number := false
%%%

*13.1.* Prove that $`\models_{\mathrm{tot}}\{P\}\,c\,\{Q\}` implies $`\models\{P\}\,c\,\{Q\}`, and mark the step that uses Session 3, Theorem 3.2. Then add the command `choose c or d` of [Session 3, Exercise 3.2](chapter-03/index.html#ch03-s4). Give assertions $`P,Q` and a command for which the first triple holds and the second fails.

*13.2.* Take the summation program of [Session 12, §12.1](chapter-12/index.html#ch12-s1) with the invariant $`J` and the variant $`\mu(\sigma)=\max(\sigma(n)-\sigma(i),0)`. Redo lines 1–5 of the derivation in Session 12, §12.2, for $`\vdash_{\mathrm{tot}}` with the postcondition $`J\wedge(\mu<j)` for the body. Which implication is new? What does Theorem 13.3 then say about the program?

*13.3.* Replace $`(\mu<j)` in the total while rule by the assertion $`(\mu\le j)`, defined in the same way. Find an assertion $`P`, a variant and a loop for which the weakened premise is derivable for every $`j` but the conclusion is not valid for total correctness. Which step of the board case fails?

*13.4.* Keep $`(\mu<j)`, but replace $`\vdash_{\mathrm{tot}}` in the premise of the total while rule by $`\vdash_{\mathrm H}` of Session 12. Give a counterexample. Which step of the board case fails?

*13.5.* In the loop $`W_2` of §13.2, let $`P_2(\sigma)` and $`\mu_2(\sigma)=k`. Show that every derivation of an execution of $`W_2` from $`\sigma` uses the loop iteration rule exactly $`k` times. Which facts beyond the premise of the total while rule do you need?

*Further problem.* Let $`x,y` be distinct names and $`W_g=\mathsf{while}\ (0<x\land 0<y)\ \mathsf{do}\ \bigl(\mathsf{if}\ y\le x\ \mathsf{then}\ x:=x-y\ \mathsf{else}\ y:=y-x\bigr)`. Find a variant and prove $`\models_{\mathrm{tot}}\{0\le x\land 0\le y\}\,W_g\,\{x=0\lor y=0\}`. Does your variant give the exact number of executions of the body?

# Reading for the Seminar
%%%
tag := "ch13-s5"
number := false
%%%

*Definitions · 10 minutes.* Trace $`W_2` from $`x=1,y=2` and record $`\mu_2` at each loop test. Record $`\max(\sigma(x),0)` as well and find the executions of the body where it does not decrease. Write Definition 13.1 next to Session 11, Definition 11.4, and circle the quantifier that changed.

*Joint proof · 30 minutes.* Write $`V_{\mathrm{tot}}(H)`. Go briefly through the Hoare sequence and conditional cases, and name the rule of A.5 that builds the execution in each. Then present the total while case: write $`V_{\mathrm{tot}}(H_j)`, the property $`L(j)` with its quantifiers, the guard-false case, and steps 1–5 of the guard-true case. Justify where $`D_1` and $`D_2` come from.

*Proof review · 20 minutes.* Weaken each of the two termination conditions of the total while rule, as in Exercises 13.3 and 13.4. Locate the step of the board case that fails.

*Facilitator’s hint.* A partial triple can be valid for a body with no final state. Ask where the proof obtains its intermediate state $`\sigma_1`. Then ask why step 3 applies the induction hypothesis at $`\sigma_1` and not at $`\sigma`.

# Solutions and Further Reading
%%%
tag := "ch13-s6"
number := false
%%%

*13.1.* Assume $`\models_{\mathrm{tot}}\{P\}\,c\,\{Q\}`, $`P(\sigma)` and $`\sigma\vdash c\Downarrow\sigma''`. Total correctness gives $`\sigma'` with $`\sigma\vdash c\Downarrow\sigma'` and $`Q(\sigma')`. Session 3, Theorem 3.2, gives $`\sigma'=\sigma''`, so $`Q(\sigma'')`. For the choice command take $`c=(\mathsf{choose}\ x:=0\ \mathsf{or}\ x:=1)`, $`P` true at every state and $`Q` the assertion $`x=0`. From every state one choice ends with $`x=0`, so the total triple holds. The other choice ends with $`x=1`, so the partial triple fails. The step $`\sigma'=\sigma''` has no counterpart.

*13.2.* Line 1 is now $`\vdash_{\mathrm{tot}}\{(J\wedge(\mu<j))[(a+i)/a]\}\ a:=a+i\ \{J\wedge(\mu<j)\}`, and lines 2–3 change in the same way. The consequence step of line 4 must now also show, from $`J(\sigma)`, $`\sigma(i)<\sigma(n)` and $`\max(\sigma(n)-\sigma(i),0)=j`, that $`\max(\sigma(n)-\sigma(i)-1,0)<j`. This holds because $`j=\sigma(n)-\sigma(i)\ge1`. That implication is new. The total while rule replaces line 5, and lines 6–11 are unchanged with $`\vdash_{\mathrm{tot}}`. Theorem 13.3 then says that from every state with $`\sigma(n)\ge0` the program terminates, in a state with $`2a=n(n+1)`.

*13.3.* Take $`W_0=\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`, $`P` true at every state, and $`\mu(\sigma)=0` at every state. For each $`j` the Hoare skip rule gives $`\vdash_{\mathrm{tot}}\{P\wedge\mathrm{T}_{\mathsf{true}}\wedge(\mu=j)\}\,\mathsf{skip}\,\{P\wedge\mathrm{T}_{\mathsf{true}}\wedge(\mu=j)\}`. The consequence rule, with the implication $`\forall\sigma',\ (P\wedge\mathrm{T}_{\mathsf{true}}\wedge(\mu=j))(\sigma')\Rightarrow(P\wedge(\mu\le j))(\sigma')`, gives the weakened premise. The weakened rule then derives $`\vdash_{\mathrm{tot}}\{P\}\,W_0\,\{P\wedge\mathrm{F}_{\mathsf{true}}\}`. No state has a terminating execution of $`W_0` (Session 2, §2.4), so this triple is not valid for total correctness. Step 3 fails. The body ends in $`\sigma_1=\sigma` with $`\mu(\sigma_1)=j`, and $`L(j)` is not among the hypotheses $`\forall j'<j,\ L(j')`.

*13.4.* Take $`W=\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ W_0`, with $`W_0` as in 13.3, $`P` true at every state and $`\mu(\sigma)=0`. By Session 12, Exercise 12.4, $`\vdash_{\mathrm H}\{P\wedge\mathrm{T}_{\mathsf{true}}\wedge(\mu=j)\}\,W_0\,\{P\wedge(\mu<j)\}` for every $`j`, although $`(\mu<0)` holds at no state. The modified rule derives $`\vdash_{\mathrm{tot}}\{P\}\,W\,\{P\wedge\mathrm{F}_{\mathsf{true}}\}`. But $`W` has no terminating execution. Its guard is always true, so the last rule of such a derivation would be the loop iteration rule, whose body premise is a terminating execution of $`W_0`. By Session 2, §2.4, there is none. Step 2 fails. The hypothesis of a partial premise speaks only about executions of the body that exist. It does not produce $`\sigma_1`.

*13.5.* Use induction on $`k`. If $`k=0`, then $`P_2` gives $`\sigma(x)=\sigma(y)=0`, the guard is false, and the only rule that concludes the execution is the loop exit rule. If $`k>0`, then $`P_2` makes one counter positive, so the guard is true and the last rule is the loop iteration rule. Inverting its body premise with the conditional rule and Session 3, Lemma 3.1, shows that its final state $`\sigma_1` is $`\sigma` with one positive counter lowered by one. So $`P_2(\sigma_1)` and $`\mu_2(\sigma_1)=k-1`. The induction hypothesis gives $`k-1` uses in the loop premise, and $`k` in all. Two facts go beyond the premise: $`\mu_2` decreases by exactly one, and the guard is true at every state with $`P_2` and a positive $`\mu_2`. A variant that decreases by at least one bounds the number of executions of the body by its initial value.

*Further problem.* Take $`P_g\coloneqq(0\le x\land 0\le y)` and $`\mu_g(\sigma)=\max(\sigma(x),0)+\max(\sigma(y),0)`. Assume $`P_g(\sigma)`, a true guard and $`\mu_g(\sigma)=j`. The guard gives $`0<\sigma(x)` and $`0<\sigma(y)`. If $`\sigma(y)\le\sigma(x)`, the body sets $`x` to $`\sigma(x)-\sigma(y)\ge0`, and $`\mu_g` decreases by $`\sigma(y)>0`. Otherwise $`\sigma(x)<\sigma(y)`, the body sets $`y` to $`\sigma(y)-\sigma(x)>0`, and $`\mu_g` decreases by $`\sigma(x)>0`. These are the implications of a derivation of the premise, built as for $`W_2` in §13.2. The total while rule gives $`\vdash_{\mathrm{tot}}\{P_g\}\,W_g\,\{P_g\wedge\mathrm{F}_b\}`, where $`b` is the guard. A false guard means $`x\le0` or $`y\le0`, and with $`P_g` one of them is 0. So the consequence rule gives the required triple, and Theorem 13.3 makes it valid for total correctness. The variant does not count executions exactly. From $`(3,3)` one execution reaches $`(0,3)` and stops, while $`\mu_g` fell from 6 to 3.

*Further reading · Well-founded orders.* Strong induction on the natural numbers is one case of induction on a *well-founded relation*, a relation with no infinite descending chain. Lexicographic order on pairs of natural numbers is another: $`(a',b')` lies below $`(a,b)` when $`a'<a`, or when $`a'=a` and $`b'<b`. Its induction principle follows from strong induction on the first coordinate and, with that coordinate fixed, strong induction on the second. It allows the second coordinate to increase when the first strictly decreases. Change the first branch of $`W_2` to $`x:=x-1;\ y:=y+1`. From $`(2,0)` the loop tests see $`(2,0)`, $`(1,1)`, $`(0,2)`, $`(0,1)` and $`(0,0)`. The sum stays 2 during the first two iterations, but the pair $`(x,y)` decreases lexicographically in both branches. A while rule whose variant takes values in a well-founded order is sound, and the proof of Theorem 13.3 goes through with induction on that order in place of strong induction. For this loop a natural-number variant also exists: $`2x+y` on states with $`0\le x` and $`0\le y`. It decreases by exactly one in both branches. Each initial unit of $`x` must first move into $`y` and then be removed, and each initial unit of $`y` only has to be removed.

*Further reading · Derivations with infinitely many premises.* [Session 3, §3.1](chapter-03/index.html#ch03-s1) justified induction on execution derivations by their height, a natural number. A derivation that uses the total while rule can have infinitely many premise derivations, and its height need not be a natural number. Induction on derivations remains valid. Suppose every rule carries the induction property from its premise derivations to its conclusion, and the property fails at some derivation. Then it fails at one of that derivation’s premise derivations. Repeating this gives an infinite path from the root, which a derivation does not have. Theorem 13.3 never uses height.

*Further reading · The rule of Nipkow and Klein.* Their defining while rule uses a relation $`\rho` between states and natural numbers in place of $`\mu`. Its premise asks the body to end at a state related to a smaller number, and its precondition asks the initial state to be related to some number. Taking $`\rho(\sigma,j)` to mean $`\mu(\sigma)=j` gives the total while rule. They also prove completeness as Theorem 12.15: every triple valid for total correctness is derivable (_Concrete Semantics_, §12.5, pp. 213–214). Its key Lemma 12.14 takes $`\rho(\sigma,j)` to mean that the loop runs from $`\sigma` with exactly $`j` iterations, and uses determinacy to show that this number is unique. Their Exercise 12.22 (p. 215) gives a while rule whose invariant is indexed by the number of remaining iterations. [Concrete Semantics, §12.5](https://concrete-semantics.org/concrete-semantics.pdf#page=222)

# Sources and Formalization
%%%
tag := "ch13-notes"
number := false
%%%

Validity for total correctness, the while rule with a variant, and the soundness lemma are in _Concrete Semantics_, §12.5. The defining while rule of Nipkow and Klein uses a relation between states and natural numbers. They derive from it a rule with a function from states to natural numbers, and that derived rule is the total while rule of this session. They prove soundness as Lemma 12.13 for their own execution relation, which has two conditional rules and a different guard language. Here validity refers to the execution relation of A.5. [Concrete Semantics, §12.5, pp. 212–214](https://concrete-semantics.org/concrete-semantics.pdf#page=222)

* *Theorem 13.3.* Corresponds to CS Lemma 12.13. Checked in Lean ([`totalHoareSound`](lean/Hoare.html#totalHoareSound) · [IMP card references](imp-card/index.html#imp-sources)).
