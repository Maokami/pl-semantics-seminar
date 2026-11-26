import VersoManual
import PLBook.IMP.Hoare

open Verso.Genre Manual

#doc (Manual) "Loop Invariants" =>
%%%
tag := "ch12"
file := "chapter-12"
%%%

The program below adds the integers from 1 to $`n`. With $`n=3` the loop test is reached four times, with $`(i,a)` equal to $`(0,0)`, $`(1,1)`, $`(2,3)` and $`(3,6)`. Each pair satisfies $`2a=i(i+1)`, and the last test fails with $`i=n`. Checking one value of $`n` at a time never ends. We need one assertion that holds before the loop, survives one more execution of the body, and gives the result when the guard fails. This session turns that argument into a proof rule and proves that every triple derived by the rules of Hoare logic is valid.

*In this session.*

* *Definitions.* States and update ([A.2](imp-card/index.html#imp-a2)). Guards, their values $`B(b,\sigma)` and the derived notation $`e_1<e_2` ([A.4](imp-card/index.html#imp-a4)). The execution judgment $`\sigma\vdash c\Downarrow\sigma'` and its six rules ([A.5](imp-card/index.html#imp-a5), Session 2, Definition 2.1). Assertions, triples $`\{P\}\,c\,\{Q\}`, validity $`\models\{P\}\,c\,\{Q\}` ([Session 11, Definition 11.4](chapter-11/index.html#ch11-s2)). The substituted assertion $`Q[e/x]` and the validity of assignment triples ([Session 11, Definition 11.5 and Theorem 11.7](chapter-11/index.html#ch11-s3)). Sequence inversion ([Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3)), the assignment result ([Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2)) and the validity of sequences and consequence ([Session 11, Proposition 11.9](chapter-11/index.html#ch11-s4)).
* *New terms.* Guard assertion, loop invariant, Hoare proof system, derivable triple, soundness. [Glossary](glossary/index.html)
* *Theorem 12.3 (Soundness).* For all assertions $`P,Q` and every command $`c`, if $`\vdash_{\mathrm H}\{P\}\,c\,\{Q\}` then $`\models\{P\}\,c\,\{Q\}`.
* *Board case.* The while rule. Take the hypothesis $`V(H_1)` for the body and prove $`L(D)` by induction on the loop execution $`D:\sigma\vdash W\Downarrow\sigma'`. The iteration case takes four steps.
* *Proof outline.* Induction on the derivation $`H` of $`\vdash_{\mathrm H}\{P\}\,c\,\{Q\}` with $`V(H)\coloneqq\forall\sigma,\sigma',\ (P(\sigma)\land\sigma\vdash c\Downarrow\sigma')\Rightarrow Q(\sigma')`. Most cases invert the execution of $`c` and apply the hypotheses of the premises. In the while case a nested induction (Session 10, §10.3), on the height of $`D:\sigma\vdash W\Downarrow\sigma'`, proves $`L(D)\coloneqq P(\sigma)\Rightarrow(P(\sigma')\land B(b,\sigma')=\mathsf{false})`.
* *From Session 11.* Session 11 proved one triple valid at a time, directly from the execution rules. Here rules combine into derivations, and one induction proves every derivable triple valid. For the loop, the hypothesis about the rest of the run comes from induction on execution derivations, as in Session 3.

# Invariants of a summation loop
%%%
tag := "ch12-s1"
%%%

Let $`i,a,n` be distinct names. The program is

$$`i:=0;\ \bigl(a:=0;\ W\bigr),\qquad W=\mathsf{while}\ i<n\ \mathsf{do}\ c,\qquad c=\bigl(i:=i+1;\ a:=a+i\bigr).`

The guard $`i<n` is the derived notation of [A.4](imp-card/index.html#imp-a4). It abbreviates $`\neg(n\le i)`, so $`B(i<n,\sigma)=\mathsf{true}` exactly when $`\sigma(i)<\sigma(n)`. Every right-hand side uses only names, literals and addition, so it is an expression of [A.1](imp-card/index.html#imp-a1). No assignment changes $`n`.

Recall from [Session 11](chapter-11/index.html) that an assertion is a predicate on states, and that $`\{P\}\,c\,\{Q\}` is valid, written $`\models\{P\}\,c\,\{Q\}`, when

$$`\forall\sigma,\sigma',\ \bigl(P(\sigma)\land\sigma\vdash c\Downarrow\sigma'\bigr)\Rightarrow Q(\sigma').`

In examples we write an assertion as a formula over names, where each name $`x` stands for the integer $`\sigma(x)`. For example, $`2a=i(i+1)` is the assertion that holds at $`\sigma` exactly when $`2\sigma(a)=\sigma(i)\bigl(\sigma(i)+1\bigr)`. An assertion is a mathematical statement about integers, so it may multiply. This does not add multiplication to the expressions of A.1. Programs still use only the four constructors of A.1, and $`\mathrm{eval}` is never applied to an assertion.

A guard and an assertion are different objects. A guard $`b` is syntax whose value $`B(b,\sigma)` is a Boolean. An assertion is a proposition about $`\sigma`. To use a guard in an assertion we compare its value with a Boolean constant. For a guard $`b` and assertions $`P,R`, define the *guard assertions* $`\mathrm{T}_b,\mathrm{F}_b` and the conjunction $`P\wedge R` by

$$`\mathrm{T}_b(\sigma)\coloneqq\bigl(B(b,\sigma)=\mathsf{true}\bigr),\qquad\mathrm{F}_b(\sigma)\coloneqq\bigl(B(b,\sigma)=\mathsf{false}\bigr),\qquad(P\wedge R)(\sigma)\coloneqq P(\sigma)\land R(\sigma).`

This conjunction combines assertions. It is not the guard constructor $`b_1\land b_2` of A.4. Each state satisfies exactly one of $`\mathrm{T}_b` and $`\mathrm{F}_b`, because $`B(b,\sigma)` is one of the two Boolean values. In the example, $`\mathrm{T}_{i<n}(\sigma)` holds when $`\sigma(i)<\sigma(n)`, and $`\mathrm{F}_{i<n}(\sigma)` holds when $`\sigma(n)\le\sigma(i)`.

*Definition 12.1 (Loop invariant).* An assertion $`P` is a *loop invariant* of $`\mathsf{while}\ b\ \mathsf{do}\ c` when $`\models\{P\wedge\mathrm{T}_b\}\,c\,\{P\}`, that is,

$$`\forall\sigma,\sigma',\ \bigl(P(\sigma)\land B(b,\sigma)=\mathsf{true}\land\sigma\vdash c\Downarrow\sigma'\bigr)\Rightarrow P(\sigma').`

For the summation program take

$$`J\coloneqq\bigl(0\le i\le n\ \land\ 2a=i(i+1)\bigr),\qquad P_{\mathrm{sum}}\coloneqq(0\le n),\qquad Q_{\mathrm{sum}}\coloneqq\bigl(2a=n(n+1)\bigr).`

Three facts about $`J` lead from $`P_{\mathrm{sum}}` to $`Q_{\mathrm{sum}}`.

*Preservation: $`J` is a loop invariant of $`W`.* Assume $`J(\sigma)`, $`B(i<n,\sigma)=\mathsf{true}` and $`\sigma\vdash c\Downarrow\sigma'`. Put $`j=\sigma(i)`. [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3) splits the execution of $`c` at a state $`\sigma_1`, and [Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2) computes both assignments: $`\sigma_1=\sigma[i\mapsto j+1]` and $`\sigma'=\sigma_1[a\mapsto\sigma(a)+j+1]`. So $`\sigma'(i)=j+1`, $`\sigma'(a)=\sigma(a)+j+1` and $`\sigma'(n)=\sigma(n)`. The guard gives $`j<\sigma(n)`. No integer lies strictly between $`j` and $`j+1`, so $`j+1\le\sigma(n)`, and $`0\le j` gives $`0\le j+1`. The second assignment reads the new index $`j+1`. With $`2\sigma(a)=j(j+1)` from $`J(\sigma)`,

$$`2\bigl(\sigma(a)+j+1\bigr)=j(j+1)+2(j+1)=(j+1)(j+2).`

Hence $`J(\sigma')`.

*Entry.* If $`P_{\mathrm{sum}}(\sigma)`, then $`J` holds at $`\sigma[i\mapsto0][a\mapsto0]`. The bounds read $`0\le0\le\sigma(n)` and the equation reads $`2\cdot0=0\cdot1`.

*Exit.* If $`J(\sigma)` and $`\mathrm{F}_{i<n}(\sigma)`, then $`\sigma(n)\le\sigma(i)` from the guard and $`\sigma(i)\le\sigma(n)` from $`J`. So $`\sigma(i)=\sigma(n)`, and the equation of $`J` becomes $`2\sigma(a)=\sigma(n)\bigl(\sigma(n)+1\bigr)`, which is $`Q_{\mathrm{sum}}(\sigma)`. Only one of the two inequalities comes from the guard.

Informally, a terminating run reaches the loop test finitely often. Entry gives $`J` at the first test, preservation carries $`J` from each test to the next, and exit gives $`Q_{\mathrm{sum}}` at the last test. §12.2 states this argument as a rule. §12.3 replaces "each test" by an induction on the execution derivation of the loop.

# The Hoare proof system
%%%
tag := "ch12-s2"
%%%

Validity is a statement about executions. A proof system derives triples by rules that mention no execution. For an assertion $`Q`, a name $`x` and an expression $`e`, recall the substituted assertion $`Q[e/x]` of [Session 11, Definition 11.5](chapter-11/index.html#ch11-s3):

$$`Q[e/x](\sigma)\Longleftrightarrow Q\bigl(\sigma[x\mapsto\mathrm{eval}(e,\sigma)]\bigr).`

By Lemma 3.1 it holds at $`\sigma` exactly when $`Q` holds after $`x:=e` runs from $`\sigma`. For example, by Session 11, Lemma 11.6, $`\bigl(2a=i(i+1)\bigr)[(a+i)/a]` is the assertion $`2(a+i)=i(i+1)`. Repeated substitutions are read from left to right: $`J[(a+i)/a][(i+1)/i]` is $`\bigl(J[(a+i)/a]\bigr)[(i+1)/i]`.

*Definition 12.2 (Hoare proof system).* Write $`\vdash_{\mathrm H}\{P\}\,c\,\{Q\}`, and call the triple *derivable*, when it has a finite derivation by the six rules below. The letters $`P,P_1,Q,Q_1,R` range over assertions. To keep these rules apart from the execution rules of A.5, we call them the Hoare skip, Hoare assignment, Hoare sequence and Hoare conditional rules, the while rule and the consequence rule.

$$`\frac{}{\vdash_{\mathrm H}\{P\}\ \mathsf{skip}\ \{P\}}\qquad
\frac{}{\vdash_{\mathrm H}\{Q[e/x]\}\ x:=e\ \{Q\}}`

$$`\frac{\vdash_{\mathrm H}\{P\}\ c_1\ \{R\}\qquad\vdash_{\mathrm H}\{R\}\ c_2\ \{Q\}}{\vdash_{\mathrm H}\{P\}\ (c_1;c_2)\ \{Q\}}`

$$`\frac{\vdash_{\mathrm H}\{P\wedge\mathrm{T}_b\}\ c_1\ \{Q\}\qquad\vdash_{\mathrm H}\{P\wedge\mathrm{F}_b\}\ c_2\ \{Q\}}{\vdash_{\mathrm H}\{P\}\ \mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\ \{Q\}}`

$$`\frac{\vdash_{\mathrm H}\{P\wedge\mathrm{T}_b\}\ c\ \{P\}}{\vdash_{\mathrm H}\{P\}\ \mathsf{while}\ b\ \mathsf{do}\ c\ \{P\wedge\mathrm{F}_b\}}`

$$`\frac{\forall\sigma,\ P(\sigma)\Rightarrow P_1(\sigma)\qquad\vdash_{\mathrm H}\{P_1\}\ c\ \{Q_1\}\qquad\forall\sigma',\ Q_1(\sigma')\Rightarrow Q(\sigma')}{\vdash_{\mathrm H}\{P\}\ c\ \{Q\}}`

The Hoare assignment rule is the rule justified in Session 11. In the conditional and while rules the guard enters only through $`\mathrm{T}_b` and $`\mathrm{F}_b`. The consequence rule is the only rule with premises that are not triples. Its two implications are mathematical facts about all states and have no derivation in this system. The while rule always yields the postcondition $`P\wedge\mathrm{F}_b`. The consequence rule then replaces it by a weaker postcondition.

*A derivation for the summation program.* Write $`b` for $`i<n`. Each line follows from earlier lines by the rule named at its end.

1. $`\vdash_{\mathrm H}\{J[(a+i)/a]\}\ a:=a+i\ \{J\}`. Hoare assignment rule.
2. $`\vdash_{\mathrm H}\{J[(a+i)/a][(i+1)/i]\}\ i:=i+1\ \{J[(a+i)/a]\}`. Hoare assignment rule.
3. $`\vdash_{\mathrm H}\{J[(a+i)/a][(i+1)/i]\}\ c\ \{J\}`. Hoare sequence rule on lines 2 and 1.
4. $`\vdash_{\mathrm H}\{J\wedge\mathrm{T}_b\}\ c\ \{J\}`. Consequence rule on line 3. Its first implication is $`\forall\sigma,\ (J\wedge\mathrm{T}_b)(\sigma)\Rightarrow J[(a+i)/a][(i+1)/i](\sigma)`. The right side unfolds to $`0\le\sigma(i)+1\le\sigma(n)` and $`2\bigl(\sigma(a)+\sigma(i)+1\bigr)=\bigl(\sigma(i)+1\bigr)\bigl(\sigma(i)+2\bigr)`, which is the preservation calculation of §12.1. The second implication is $`\forall\sigma',\ J(\sigma')\Rightarrow J(\sigma')`.
5. $`\vdash_{\mathrm H}\{J\}\ W\ \{J\wedge\mathrm{F}_b\}`. While rule on line 4.
6. $`\vdash_{\mathrm H}\{J\}\ W\ \{Q_{\mathrm{sum}}\}`. Consequence rule on line 5, with $`\forall\sigma,\ J(\sigma)\Rightarrow J(\sigma)` and the exit implication of §12.1.
7. $`\vdash_{\mathrm H}\{J[0/a]\}\ a:=0\ \{J\}`. Hoare assignment rule.
8. $`\vdash_{\mathrm H}\{J[0/a]\}\ (a:=0;W)\ \{Q_{\mathrm{sum}}\}`. Hoare sequence rule on lines 7 and 6.
9. $`\vdash_{\mathrm H}\{J[0/a][0/i]\}\ i:=0\ \{J[0/a]\}`. Hoare assignment rule.
10. $`\vdash_{\mathrm H}\{J[0/a][0/i]\}\ i:=0;(a:=0;W)\ \{Q_{\mathrm{sum}}\}`. Hoare sequence rule on lines 9 and 8.
11. $`\vdash_{\mathrm H}\{P_{\mathrm{sum}}\}\ i:=0;(a:=0;W)\ \{Q_{\mathrm{sum}}\}`. Consequence rule on line 10. Its first implication is the entry fact of §12.1, since $`J[0/a][0/i](\sigma)` is $`J\bigl(\sigma[i\mapsto0][a\mapsto0]\bigr)`. Its second implication is $`\forall\sigma',\ Q_{\mathrm{sum}}(\sigma')\Rightarrow Q_{\mathrm{sum}}(\sigma')`.

Apart from the trivial implications $`J\Rightarrow J` and $`Q_{\mathrm{sum}}\Rightarrow Q_{\mathrm{sum}}`, the implications used in lines 4, 6 and 11 are exactly the three facts of §12.1. States occur only inside those implications. Nothing yet connects line 11 to executions of the program.

# Soundness of the proof system
%%%
tag := "ch12-s3"
%%%

Line 11 of §12.2 should mean the following. From every state with $`\sigma(n)\ge0`, every terminating execution of the summation program ends in a state $`\sigma'` with $`2\sigma'(a)=\sigma'(n)\bigl(\sigma'(n)+1\bigr)`. That is the validity of the triple. The theorem below gives validity for every derivation at once.

*Theorem 12.3 (Soundness).* For all assertions $`P,Q` and every command $`c`, if $`\vdash_{\mathrm H}\{P\}\,c\,\{Q\}` then $`\models\{P\}\,c\,\{Q\}`.

We prove $`V(H)` for every derivation $`H` by induction on $`H`, as in [Session 1, §1.5](chapter-01/index.html#ch01-s5). For $`H` with conclusion $`\vdash_{\mathrm H}\{P\}\,c\,\{Q\}` the induction property is

$$`V(H)\coloneqq\forall\sigma,\sigma',\ \bigl(P(\sigma)\land\sigma\vdash c\Downarrow\sigma'\bigr)\Rightarrow Q(\sigma').`

Read $`P,c,Q` from the conclusion of $`H`. Each premise derivation $`H_1` or $`H_2` that concludes a triple has the induction hypothesis $`V(H_1)` or $`V(H_2)`. We write the hypotheses with bound states $`\sigma'',\sigma'''`. Except in the while case, fix $`\sigma,\sigma'` with $`P(\sigma)` and $`\sigma\vdash c\Downarrow\sigma'`. We must show $`Q(\sigma')`.

*Hoare skip rule.* Then $`c=\mathsf{skip}` and $`Q=P`. Inversion of $`\sigma\vdash\mathsf{skip}\Downarrow\sigma'` gives $`\sigma'=\sigma`, so $`Q(\sigma')` is $`P(\sigma)`.

*Hoare assignment rule.* Then $`c` is $`x:=e` and $`P=Q[e/x]`. This is [Session 11, Theorem 11.7](chapter-11/index.html#ch11-s3): Lemma 3.1 gives $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`, and by the definition of $`Q[e/x]`, $`P(\sigma)` is $`Q(\sigma')`.

*Hoare sequence rule.* Then $`c=(c_1;c_2)`, and the premises are $`H_1:\ \vdash_{\mathrm H}\{P\}\,c_1\,\{R\}` and $`H_2:\ \vdash_{\mathrm H}\{R\}\,c_2\,\{Q\}` for some assertion $`R`. The hypotheses are

$$`\begin{aligned}
V(H_1)&:\quad\forall\sigma'',\sigma''',\ \bigl(P(\sigma'')\land\sigma''\vdash c_1\Downarrow\sigma'''\bigr)\Rightarrow R(\sigma'''),\\
V(H_2)&:\quad\forall\sigma'',\sigma''',\ \bigl(R(\sigma'')\land\sigma''\vdash c_2\Downarrow\sigma'''\bigr)\Rightarrow Q(\sigma''').
\end{aligned}`

As in [Session 11, Proposition 11.9(a)](chapter-11/index.html#ch11-s4), Proposition 2.2 gives a state $`\sigma_1` with $`\sigma\vdash c_1\Downarrow\sigma_1` and $`\sigma_1\vdash c_2\Downarrow\sigma'`. $`V(H_1)` with $`\sigma''=\sigma,\sigma'''=\sigma_1` gives $`R(\sigma_1)`. $`V(H_2)` with $`\sigma''=\sigma_1,\sigma'''=\sigma'` gives $`Q(\sigma')`.

*Hoare conditional rule.* Then $`c=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`, and the premises are $`H_1:\ \vdash_{\mathrm H}\{P\wedge\mathrm{T}_b\}\,c_1\,\{Q\}` and $`H_2:\ \vdash_{\mathrm H}\{P\wedge\mathrm{F}_b\}\,c_2\,\{Q\}`. The hypotheses are

$$`\begin{aligned}
V(H_1)&:\quad\forall\sigma'',\sigma''',\ \bigl(P(\sigma'')\land B(b,\sigma'')=\mathsf{true}\land\sigma''\vdash c_1\Downarrow\sigma'''\bigr)\Rightarrow Q(\sigma'''),\\
V(H_2)&:\quad\forall\sigma'',\sigma''',\ \bigl(P(\sigma'')\land B(b,\sigma'')=\mathsf{false}\land\sigma''\vdash c_2\Downarrow\sigma'''\bigr)\Rightarrow Q(\sigma''').
\end{aligned}`

The single conditional rule of A.5 is the only rule that concludes this execution. Inversion gives $`\sigma\vdash k\Downarrow\sigma'`, where $`k` is the branch selected by $`B(b,\sigma)`. If $`B(b,\sigma)=\mathsf{true}`, then $`k=c_1` and $`V(H_1)` with $`\sigma''=\sigma,\sigma'''=\sigma'` gives $`Q(\sigma')`. Otherwise $`B(b,\sigma)=\mathsf{false}`, $`k=c_2`, and $`V(H_2)` gives $`Q(\sigma')`.

*Consequence rule.* This is the argument of [Session 11, Proposition 11.9(b)](chapter-11/index.html#ch11-s4). The premises are $`\forall\sigma'',\ P(\sigma'')\Rightarrow P_1(\sigma'')`, a derivation $`H_1:\ \vdash_{\mathrm H}\{P_1\}\,c\,\{Q_1\}` and $`\forall\sigma''',\ Q_1(\sigma''')\Rightarrow Q(\sigma''')`. Only $`H_1` has a hypothesis: $`V(H_1):\ \forall\sigma'',\sigma''',\ (P_1(\sigma'')\land\sigma''\vdash c\Downarrow\sigma''')\Rightarrow Q_1(\sigma''')`. The first implication gives $`P_1(\sigma)`. $`V(H_1)` with $`\sigma''=\sigma,\sigma'''=\sigma'` gives $`Q_1(\sigma')`. The second implication gives $`Q(\sigma')`.

*While rule.* Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c_1`. We write $`c_1` for the body because $`c` names the whole command. Suppose $`H` ends with the while rule. Then $`c=W`, $`Q=P\wedge\mathrm{F}_b`, and the premise is $`H_1:\ \vdash_{\mathrm H}\{P\wedge\mathrm{T}_b\}\,c_1\,\{P\}`. Its hypothesis is

$$`V(H_1):\quad\forall\sigma'',\sigma''',\ \bigl(P(\sigma'')\land B(b,\sigma'')=\mathsf{true}\land\sigma''\vdash c_1\Downarrow\sigma'''\bigr)\Rightarrow P(\sigma''').`

By Definition 12.1, $`V(H_1)` says that $`P` is a loop invariant of $`W`. We must show

$$`V(H):\quad\forall\sigma,\sigma',\ \bigl(P(\sigma)\land\sigma\vdash W\Downarrow\sigma'\bigr)\Rightarrow\bigl(P(\sigma')\land B(b,\sigma')=\mathsf{false}\bigr).`

The induction on $`H` gives no hypothesis about $`W` itself. After one execution of the body, the rest of the run is again an execution of $`W`. We therefore prove a claim about execution derivations, by induction on their height as in [Session 3, §3.1](chapter-03/index.html#ch03-s1). For a derivation $`D:\sigma\vdash W\Downarrow\sigma'`, with $`\sigma,\sigma'` read from its conclusion, the induction property is

$$`L(D)\coloneqq P(\sigma)\Rightarrow\bigl(P(\sigma')\land B(b,\sigma')=\mathsf{false}\bigr).`

We prove $`L(D)` for every derivation $`D` of an execution of $`W`, assuming $`L` for every such derivation of smaller height. $`D` fixes both states, so unlike Session 3 the property has no inner quantifier. Only the loop exit rule and the loop iteration rule of A.5 conclude an execution of $`W`.

*Loop exit.* Suppose $`D` ends with the loop exit rule. Then $`B(b,\sigma)=\mathsf{false}` and $`\sigma'=\sigma`. Assume $`P(\sigma)`. Then $`P(\sigma')` because $`\sigma'=\sigma`, and $`B(b,\sigma')=B(b,\sigma)=\mathsf{false}`.

*Loop iteration.* Suppose $`D` ends with the loop iteration rule. Its side condition is $`B(b,\sigma)=\mathsf{true}`, and its premises are $`D_1:\sigma\vdash c_1\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash W\Downarrow\sigma'` for some state $`\sigma_1`. The premise $`D_2` again executes $`W` and has smaller height than $`D`. Its induction hypothesis is

$$`L(D_2):\quad P(\sigma_1)\Rightarrow\bigl(P(\sigma')\land B(b,\sigma')=\mathsf{false}\bigr).`

We must show $`L(D):\ P(\sigma)\Rightarrow\bigl(P(\sigma')\land B(b,\sigma')=\mathsf{false}\bigr)`.

1. Assume $`P(\sigma)`.
2. The side condition of $`D` gives $`B(b,\sigma)=\mathsf{true}`.
3. Apply $`V(H_1)` with $`\sigma''=\sigma` and $`\sigma'''=\sigma_1` to step 1, step 2 and $`D_1`. This gives $`P(\sigma_1)`.
4. Apply $`L(D_2)` to step 3. This gives $`P(\sigma')` and $`B(b,\sigma')=\mathsf{false}`.

Step 3 uses the Hoare hypothesis $`V(H_1)` for the body premise $`D_1`, which does not execute $`W`. Step 4 uses the execution hypothesis $`L(D_2)` for the rest of the loop. In Session 3 the body premise also had an execution hypothesis. Here none is needed, because $`V(H_1)` already covers every execution of $`c_1`.

This proves $`L(D)` for every derivation of an execution of $`W`. To prove $`V(H)`, fix $`\sigma,\sigma'` with $`P(\sigma)` and a derivation $`D:\sigma\vdash W\Downarrow\sigma'`. Then $`L(D)` gives $`P(\sigma')` and $`B(b,\sigma')=\mathsf{false}`, which is $`(P\wedge\mathrm{F}_b)(\sigma')`.

Every rule of Definition 12.2 preserves $`V`, so $`V(H)` holds for every derivation $`H`. $`\square`

Applied to line 11 of §12.2, the theorem covers the run with $`n=3` from the opening. That run ends with $`i=3` and $`a=6`, and indeed $`2\cdot6=3\cdot4`.

*Scope of the theorem.* Validity speaks only about terminating executions. Let $`W_0=\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`. [Session 2, §2.4](chapter-02/index.html#ch02-s4) shows that $`W_0` has no terminating derivation. Since $`B(\mathsf{true},\sigma)=\mathsf{true}` at every state, the assertion $`\mathrm{F}_{\mathsf{true}}` holds at no state. Exercise 12.4 derives $`\vdash_{\mathrm H}\{P\}\,W_0\,\{Q\}` for all assertions $`P,Q`. Theorem 12.3 makes these triples valid. They are valid because no execution of $`W_0` terminates, so validity has no instance to check. A derivable triple does not promise termination. [Session 13](chapter-13/index.html) adds that obligation.

Soundness starts with a proof tree and concludes something about every terminating execution. *Completeness* asks for the opposite direction: given a valid triple, can one construct a proof? For a logic with assertions written in a fixed language, *relative completeness* asks this question assuming the language can express the assertions needed in the proof and that true implications between assertions are available. Theorem 12.3 establishes the soundness direction. The [further reading](chapter-12/index.html#ch12-s6) explains the role of weakest preconditions in the converse.

# Exercises
%%%
tag := "ch12-s4"
number := false
%%%

*12.1.* Remove $`i\le n` from $`J`. Give a state that satisfies the weakened assertion and $`\mathrm{F}_{i<n}` but not $`Q_{\mathrm{sum}}`. Which line of the derivation in §12.2 can no longer be justified?

*12.2.* Reverse the assignments in the body, so that it reads $`a:=a+i;\ i:=i+1`. Run the loop with $`n=2`. Find an equation between $`a` and $`i` such that $`0\le i\le n` together with that equation is a loop invariant, and check preservation.

*12.3.* Replace the premise of the while rule by $`\vdash_{\mathrm H}\{P\wedge\mathrm{F}_b\}\,c\,\{P\}`. Let $`P` be the assertion $`x=0`. Use the modified rule to derive $`\vdash_{\mathrm H}\{P\}\ \mathsf{while}\ x<1\ \mathsf{do}\ x:=5\ \{P\wedge\mathrm{F}_{x<1}\}` and show that this triple is not valid. Which step of the iteration case fails?

*12.4.* Let $`W_0=\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`. For arbitrary assertions $`P,Q`, derive $`\vdash_{\mathrm H}\{P\}\,W_0\,\{Q\}` in four lines in the style of §12.2. Explain why the proof of Theorem 12.3 needs no case for a run that does not terminate.

*Further problem.* A loop accumulates odd numbers. Starting from $`a=i=0`, it executes $`a:=a+i+i+1;\ i:=i+1` while $`i<n`. For $`n\ge0`, find a loop invariant that gives the final value $`a=n^2`. Give the assertion between the two assignments and say which values each assignment reads.

# Reading for the Seminar
%%%
tag := "ch12-s5"
number := false
%%%

*Definitions · 10 minutes.* Execute the summation loop with $`n=3` and list $`i` and $`a` at each loop test. Write $`\mathrm{T}_b`, $`\mathrm{F}_b` and Definition 12.1. Check preservation for one iteration, with the old and the new index in separate columns.

*Joint proof · 30 minutes.* Write $`V(H)` and go briefly through the Hoare skip, assignment and sequence cases. Then present the while case: write $`V(H_1)`, the claim $`L(D)`, the loop exit case, and steps 1–4 of the iteration case.

*Proof review · 20 minutes.* Use Exercise 12.3 to locate the step that fails under a wrong while rule. Try the weakened invariant of Exercise 12.1 and decide whether its failure refutes the program or only the proposed proof.

*Facilitator’s hint.* In step 3, ask which hypothesis covers the body and which covers the rest of the loop. In the exit fact of §12.1, ask for the two inequalities that give $`i=n`. Only one comes from the guard.

# Solutions and Further Reading
%%%
tag := "ch12-s6"
number := false
%%%

*12.1.* Take $`\sigma(n)=1`, $`\sigma(i)=2` and $`\sigma(a)=3`. Then $`\sigma(n)\le\sigma(i)`, so $`\mathrm{F}_{i<n}(\sigma)` holds. Also $`0\le\sigma(i)` and $`2\sigma(a)=6=\sigma(i)\bigl(\sigma(i)+1\bigr)`. But $`\sigma(n)\bigl(\sigma(n)+1\bigr)=2\ne6`. The exit implication used in line 6 fails. This state need not be reachable. An implication premise of the consequence rule must hold at every state. The failure refutes the proposed proof, not the program.

*12.2.* The loop tests see $`(i,a)=(0,0),(1,0),(2,1)`. The equation is $`2a=i(i-1)`. For preservation let $`j=\sigma(i)` with $`2\sigma(a)=j(j-1)`. The body writes $`\sigma(a)+j` and then $`j+1`, and $`2\bigl(\sigma(a)+j\bigr)=j(j-1)+2j=(j+1)j`. The bounds follow as in §12.1. At exit $`2a=n(n-1)`.

*12.3.* The assertion $`P\wedge\mathrm{F}_{x<1}` requires $`\sigma(x)=0` and $`1\le\sigma(x)`, so no state satisfies it. The Hoare assignment rule gives $`\vdash_{\mathrm H}\{P[5/x]\}\,x:=5\,\{P\}`. The consequence rule gives the modified premise. Its first implication, $`\forall\sigma,\ (P\wedge\mathrm{F}_{x<1})(\sigma)\Rightarrow P[5/x](\sigma)`, holds because no state satisfies its left side. Its second implication is $`\forall\sigma',\ P(\sigma')\Rightarrow P(\sigma')`. The modified rule then gives the triple. From a state with $`\sigma(x)=0` the guard is true, the body yields $`\sigma_1=\sigma[x\mapsto5]`, and the guard is false at $`\sigma_1`. The loop exit rule gives $`\sigma'=\sigma_1`, and $`P(\sigma')` fails. In the iteration case, step 3 needs the hypothesis at a state where $`B(b,\sigma)=\mathsf{true}`. The modified hypothesis covers only states where the guard is false.

*12.4.* (1) $`\vdash_{\mathrm H}\{P\wedge\mathrm{T}_{\mathsf{true}}\}\,\mathsf{skip}\,\{P\wedge\mathrm{T}_{\mathsf{true}}\}` by the Hoare skip rule. (2) $`\vdash_{\mathrm H}\{P\wedge\mathrm{T}_{\mathsf{true}}\}\,\mathsf{skip}\,\{P\}` by the consequence rule, with the postcondition implication $`(P\wedge\mathrm{T}_{\mathsf{true}})(\sigma')\Rightarrow P(\sigma')`. (3) $`\vdash_{\mathrm H}\{P\}\,W_0\,\{P\wedge\mathrm{F}_{\mathsf{true}}\}` by the while rule. (4) $`\vdash_{\mathrm H}\{P\}\,W_0\,\{Q\}` by the consequence rule. Its postcondition implication $`(P\wedge\mathrm{F}_{\mathsf{true}})(\sigma')\Rightarrow Q(\sigma')` holds because the left side holds at no state. In (2) and (4) the precondition implication is trivial. The property $`V(H)` quantifies over final states of terminating executions, and $`L(D)` over finite derivations. A run that does not terminate has no final state and no derivation, so it gives nothing to prove.

*Further problem.* At the loop test take $`0\le i\le n\land a=i^2`. Initialization establishes it for every $`n\ge0`. Let $`j` be the old index. A true guard gives $`j<n`, hence $`j+1\le n`. The first assignment reads the old $`a=j^2` and the old $`i=j` twice, so the new accumulator is $`j^2+2j+1=(j+1)^2`. The index is still $`j` at that point. A sufficient assertion between the assignments is therefore $`0\le i<n\land a=(i+1)^2`. The second assignment writes $`j+1` and leaves $`a` unchanged. The assertion between the assignments gives the new bound and the equality with the square of the new index. At exit the bound and the false guard force $`i=n`, hence $`a=n^2`.

*Further reading · Reachable states.* Fix a set of states at which a loop starts. Let $`\mathrm{Reach}` be the set of states at which the loop test is reached after finitely many complete iterations, including the starting states. $`\mathrm{Reach}` contains the starting states and is closed under one execution of the body from a state where the guard is true. It is the least such set. Every assertion that holds at the starting states and is a loop invariant holds at every state of $`\mathrm{Reach}`, by induction on the number of iterations. An invariant used in a proof may hold at states outside $`\mathrm{Reach}`, and preservation and exit must hold there too. For example, start with $`x=0` and run $`x:=x+2` while $`x<9`. Every value reached at the test is even. The assertion $`x\le10` is a loop invariant, but it also holds where $`x` has the unreachable value 9, at which the guard is already false. So it cannot give the exit value 10. Adding "$`x` is even" gives it.

*Further reading · Finding the accumulator equation.* Let $`S(j)` be the sum of the integers from 1 to $`j`, with $`S(0)=0`. The body implements $`S(j+1)=S(j)+j+1`, which suggests the assertion $`a=S(i)`. Induction on $`j` proves $`2S(j)=j(j+1)` for every natural number $`j`. The bound $`0\le i` in $`J` makes this identity applicable to the integer $`\sigma(i)`. The doubled equation avoids division. The assertion $`a=i(i+1)/2` would need a convention for integer division and a proof that the product is even.

*Further reading · Locating an error with an intermediate assertion.* Between the two assignments of the summation body the assertion $`R\coloneqq\bigl(1\le i\le n\land 2a=(i-1)i\bigr)` holds. It implies $`J[(a+i)/a]`, because $`2(a+i)=(i-1)i+2i=i(i+1)`. Suppose the second assignment were $`a:=a+i+1`. Then $`R` would have to imply $`2(a+i+1)=i(i+1)`. With $`n=1`, the first iteration reaches $`i=1` and $`a=0` between the assignments. The left side is 4 and the right side is 2. This state is reached by the modified program, so the failed implication is a real counterexample to preservation.

*Further reading · Completeness and verification conditions.* Nipkow and Klein also prove the converse of soundness for assertions that are predicates on states: every valid triple is derivable (_Concrete Semantics_, Theorem 12.5, p. 206). The proof uses the weakest precondition of a command, the assertion that holds at $`\sigma` when every terminating execution from $`\sigma` ends in the postcondition (Fact 12.3 and Lemma 12.4, pp. 204–205). §12.3.2 relates this result to Cook’s relative completeness. §12.4 computes the implications of a derivation, such as those of lines 4, 6 and 11 of §12.2, from a program annotated with invariants. [Concrete Semantics, §§12.3–12.4](https://concrete-semantics.org/concrete-semantics.pdf)

# Sources and Formalization
%%%
tag := "ch12-notes"
number := false
%%%

The six proof rules are those of _Concrete Semantics_, Fig. 12.3, where assertions are predicates on states. They are written here for the guards of A.4. Nipkow and Klein prove soundness as Lemma 12.2 for their own execution relation, which has two conditional rules and a different guard language. Here validity refers to the execution relation of A.5. [Concrete Semantics, §§12.2–12.3, pp. 192–204](https://concrete-semantics.org/concrete-semantics.pdf)

* *Theorem 12.3.* Corresponds to CS Lemma 12.2. Checked in Lean ([`hoareSound`](lean/Hoare.html#hoareSound) · [IMP card references](imp-card/index.html#imp-sources)).
