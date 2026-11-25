import VersoManual

open Verso.Genre Manual

#doc (Manual) "Constant Propagation" =>
%%%
tag := "ch18"
file := "chapter-18"
%%%

* *Definitions.* Expressions, guards, commands, $`\mathrm{eval}(e,s)`, $`B(b,s)` and the six execution rules ([IMP language card A.1–A.5](imp-card/index.html#imp-a1); Session 2, Definition 2.1). Sequence inversion ([Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3)) and the assignment result ([Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2)). Abstract stores $`A`, the relation “$`A` describes $`s`”, written $`s\in\gamma(A)`, the abstract store $`\{\}` with no entries, the abstract transfer $`f^{\sharp}_{c}(A)`, the loop result $`f^{\sharp}_{W}(A)` with its entry and preservation inclusions ([Session 17, §17.2](chapter-17/index.html#ch17-s2)), and the soundness theorem ([Session 17, Theorem 17.8](chapter-17/index.html#ch17-s3)).
* *New terms.* Program transformation, constant propagation, constant folding, simplifying constructor, loop-head store. [Glossary and label key](glossary/index.html)
* *Theorem 18.4 (Preservation of terminating executions).* For every command $`c`, abstract store $`A` and stores $`s,t`, if $`s\in\gamma(A)` and $`s\vdash c\Downarrow t`, then $`s\vdash\mathrm{cp}(A,c)\Downarrow t`.
* *Source.* Xavier Leroy’s _Compiler Verification_ course, constant propagation (§§8.1–8.3 of its Lean port). The simplifying constructors, the transformation $`\mathrm{cp}`, Lemmas 18.1–18.3 and Theorem 18.4 are taken from there. The abstract stores and the transfer $`f^{\sharp}_{c}(A)` come from the same chapter, as presented in Session 17. Nipkow and Klein prove, for a simpler analysis that forgets every variable assigned in a loop body and a transformation that leaves guards unchanged, that the original and the transformed command have the same terminating executions from every store that the table describes. [Source and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics, §10.2, p. 163](https://concrete-semantics.org/concrete-semantics.pdf#page=173)
* *Board case.* Conditional. Invert the execution to find the selected branch. Apply that branch’s induction hypothesis at the same abstract store. Lemma 18.2 shows that the transformed guard selects the transformed branch, and Lemma 18.3(a) rebuilds the execution. Five steps.
* *Proof outline.* Structural induction on $`c` with $`P(c)\coloneqq\forall A,s,t,\ (s\in\gamma(A)\land s\vdash c\Downarrow t)\Rightarrow s\vdash\mathrm{cp}(A,c)\Downarrow t`. The abstract store is quantified inside $`P(c)`, because the sequence case applies the hypothesis for $`c_2` at $`f^{\sharp}_{c_1}(A)` and the loop case applies the hypothesis for the body at the loop-head store. Session 17, Theorem 17.8, shows that the abstract store used to rewrite the rest of the program describes the intermediate store of a sequence and the store after each iteration of a loop. The loop case adds an inner induction on the loop execution.
* *From Session 17.* Session 17 proved that $`f^{\sharp}_{c}(A)` describes every final store of $`c` from a store described by $`A`. No program was changed. Here the same theorem justifies changing a program. It is applied to the original execution, at the store where the transformed program continues.

A compiler sees `z := x + 3` after a conditional whose two branches both set $`x` to 4, and replaces it by `z := 7`. The branches set $`y` to different values, so a read of $`y` there could not be replaced. Session 17 explains which facts are known after the conditional: every store that reaches the suffix is described by the abstract store $`\{x\mapsto4\}`. This session defines the rewrite and proves that it is safe. On every terminating execution, the rewritten program ends in the same final store as the original.

# Rewriting expressions with known constants
%%%
tag := "ch18-s1"
%%%

A *program transformation* maps each program to another program. Take the abstract store $`A=\{x\mapsto4\}`. Every store $`s\in\gamma(A)` has $`s(x)=4`. In such a store `x + 3` and `7` have the same value, and so do `y + x` and `y + 4`. Replacing the read of $`x` by the literal 4 is *constant propagation*. Computing $`4+3` at compile time is *constant folding*. The read of $`y` stays, because $`A` has no entry for $`y`. A missing entry means that the value is unknown, not that it is zero. Rewriting `y + x` to `4` would change its value at every store in $`\gamma(A)` with $`s(y)\neq0`.

Folding is done by functions that build an expression and simplify it at the same time. For example, $`3\mathbin{\hat+}4` is the literal 7, while $`y\mathbin{\hat+}4` is the sum $`y+4`.

*Definition 18.1 (Simplifying constructors).* Six functions build an expression or a guard from its parts: $`e_1\mathbin{\hat+}e_2`, $`e_1\mathbin{\hat-}e_2`, $`e_1\mathbin{\hat=}e_2`, $`e_1\mathbin{\hat\le}e_2`, $`\hat\neg\,b` and $`b_1\mathbin{\hat\land}b_2`. Each returns the plain constructor of A.1 or A.4 applied to its arguments, unless a simplifying equation applies. For literals $`n_1,n_2`, $`n_1\mathbin{\hat+}n_2` and $`n_1\mathbin{\hat-}n_2` are the literals with values $`n_1+n_2` and $`n_1-n_2`. The comparison $`n_1\mathbin{\hat=}n_2` is the guard $`\mathsf{true}` if $`n_1=n_2` and $`\mathsf{false}` otherwise, and $`n_1\mathbin{\hat\le}n_2` likewise. Further, $`\hat\neg\,\mathsf{true}=\mathsf{false}`, $`\hat\neg\,\mathsf{false}=\mathsf{true}`, $`\hat\neg\,\neg b=b`, $`\mathsf{true}\mathbin{\hat\land}b=b\mathbin{\hat\land}\mathsf{true}=b` and $`\mathsf{false}\mathbin{\hat\land}b=b\mathbin{\hat\land}\mathsf{false}=\mathsf{false}`. The arithmetic constructors also drop an added zero and regroup literals: $`e\mathbin{\hat+}0=e`, and $`(x+1)\mathbin{\hat-}(y+1)=x-y`. A function of this kind is a *simplifying constructor*. The complete equations are listed in Solutions and Further Reading. The proofs below use only Lemma 18.1.

*Lemma 18.1 (Simplifying constructors keep values).* For every store $`s`, all expressions $`e_1,e_2` and all guards $`b,b_1,b_2`,

$$`\begin{aligned}
\mathrm{eval}(e_1\mathbin{\hat+}e_2,s)&=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s), & \mathrm{eval}(e_1\mathbin{\hat-}e_2,s)&=\mathrm{eval}(e_1,s)-\mathrm{eval}(e_2,s),\\
B(e_1\mathbin{\hat=}e_2,s)&=B(e_1=e_2,s), & B(e_1\mathbin{\hat\le}e_2,s)&=B(e_1\le e_2,s),\\
B(\hat\neg\,b,s)&=B(\neg b,s), & B(b_1\mathbin{\hat\land}b_2,s)&=B(b_1\land b_2,s).
\end{aligned}`

*Proof.* By cases on the equation that defines the left-hand side. A plain constructor gives the right-hand side by A.3 or A.4. Each simplifying equation replaces a term by one with the same value at every store. Regrouping uses associativity and commutativity of integer addition. $`\square`

*Definition 18.2 (Constant propagation in expressions and guards).* For an abstract store $`A`, define $`\mathrm{cp}(A,e)` and $`\mathrm{cp}(A,b)` by structural recursion:

$$`\begin{aligned}
\mathrm{cp}(A,n)&=n, & \mathrm{cp}(A,x)&=n\ \text{ if } A \text{ has the entry } x\mapsto n,\quad \mathrm{cp}(A,x)=x\ \text{ if } A \text{ has no entry for } x,\\
\mathrm{cp}(A,e_1+e_2)&=\mathrm{cp}(A,e_1)\mathbin{\hat+}\mathrm{cp}(A,e_2), & \mathrm{cp}(A,e_1-e_2)&=\mathrm{cp}(A,e_1)\mathbin{\hat-}\mathrm{cp}(A,e_2),\\
\mathrm{cp}(A,\mathsf{true})&=\mathsf{true}, & \mathrm{cp}(A,\mathsf{false})&=\mathsf{false},\\
\mathrm{cp}(A,e_1=e_2)&=\mathrm{cp}(A,e_1)\mathbin{\hat=}\mathrm{cp}(A,e_2), & \mathrm{cp}(A,e_1\le e_2)&=\mathrm{cp}(A,e_1)\mathbin{\hat\le}\mathrm{cp}(A,e_2),\\
\mathrm{cp}(A,\neg b)&=\hat\neg\,\mathrm{cp}(A,b), & \mathrm{cp}(A,b_1\land b_2)&=\mathrm{cp}(A,b_1)\mathbin{\hat\land}\mathrm{cp}(A,b_2).
\end{aligned}`

With $`A=\{x\mapsto4\}` this gives $`\mathrm{cp}(A,x+3)=4\mathbin{\hat+}3=7` and $`\mathrm{cp}(A,y+x)=y\mathbin{\hat+}4=y+4`. For guards, $`\mathrm{cp}(A,x\le5)=4\mathbin{\hat\le}5=\mathsf{true}`. With $`\{\}` in place of $`A`, no variable is replaced, and only the simplifying constructors change the expression.

*Lemma 18.2 (Propagation keeps values).* For every abstract store $`A` and every store $`s\in\gamma(A)`, $`\mathrm{eval}(\mathrm{cp}(A,e),s)=\mathrm{eval}(e,s)` for every expression $`e`, and $`B(\mathrm{cp}(A,b),s)=B(b,s)` for every guard $`b`.

*Proof.* Fix $`A` and $`s\in\gamma(A)`. Use structural induction on $`e` with $`Q(e)\coloneqq\mathrm{eval}(\mathrm{cp}(A,e),s)=\mathrm{eval}(e,s)`. For a literal, $`\mathrm{cp}(A,n)=n`. For a variable $`x` with an entry $`x\mapsto n` in $`A`, $`\mathrm{eval}(n,s)=n=s(x)`, because $`s` satisfies every entry of $`A`. For a variable without an entry, $`\mathrm{cp}(A,x)=x`. For a sum, the hypotheses are $`Q(e_1)` and $`Q(e_2)`, and

$$`\begin{aligned}
\mathrm{eval}(\mathrm{cp}(A,e_1+e_2),s)&=\mathrm{eval}(\mathrm{cp}(A,e_1)\mathbin{\hat+}\mathrm{cp}(A,e_2),s) && \text{Definition 18.2}\\
&=\mathrm{eval}(\mathrm{cp}(A,e_1),s)+\mathrm{eval}(\mathrm{cp}(A,e_2),s) && \text{Lemma 18.1}\\
&=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)=\mathrm{eval}(e_1+e_2,s) && Q(e_1),\ Q(e_2),\ \text{A.3}.
\end{aligned}`

A difference is handled in the same way. For guards use structural induction on $`b` with $`Q'(b)\coloneqq B(\mathrm{cp}(A,b),s)=B(b,s)`. The constants are unchanged. A comparison uses Lemma 18.1 and the expression part. Negation and conjunction use Lemma 18.1 and the hypotheses for their operands. $`\square`

# Rewriting commands
%%%
tag := "ch18-s2"
%%%

Start from $`\{\}` with `x := 4; if x = 4 then y := 1 else y := 2`. Session 17’s transfer gives $`f^{\sharp}_{x:=4}(\{\})=\{x\mapsto4\}`, so the guard of the conditional becomes $`4\mathbin{\hat=}4=\mathsf{true}`. A conditional whose guard is the constant $`\mathsf{true}` can be replaced by its first branch. The result is `x := 4; y := 1`. Two more simplifying constructors do this for conditionals and loops.

*Definition 18.3 (Constant propagation in commands).* For a guard $`b` and commands $`c,d`,

$$`\widehat{\mathsf{if}}(b,c,d)=\begin{cases}c&\text{if } b \text{ is } \mathsf{true},\\ d&\text{if } b \text{ is } \mathsf{false},\\ \mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d&\text{otherwise,}\end{cases}\qquad
\widehat{\mathsf{while}}(b,c)=\begin{cases}\mathsf{skip}&\text{if } b \text{ is } \mathsf{false},\\ \mathsf{while}\ b\ \mathsf{do}\ c&\text{otherwise.}\end{cases}`

Here “$`b` is $`\mathsf{true}`” means that $`b` is the constant guard itself, not merely a guard whose value is true. For an abstract store $`A`, define $`\mathrm{cp}(A,c)` by structural recursion:

$$`\begin{aligned}
\mathrm{cp}(A,\mathsf{skip})&=\mathsf{skip}\\
\mathrm{cp}(A,x:=e)&=(x:=\mathrm{cp}(A,e))\\
\mathrm{cp}(A,c_1;c_2)&=\mathrm{cp}(A,c_1);\mathrm{cp}(f^{\sharp}_{c_1}(A),c_2)\\
\mathrm{cp}(A,\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2)&=\widehat{\mathsf{if}}(\mathrm{cp}(A,b),\mathrm{cp}(A,c_1),\mathrm{cp}(A,c_2))\\
\mathrm{cp}(A,\mathsf{while}\ b\ \mathsf{do}\ c_1)&=\widehat{\mathsf{while}}(\mathrm{cp}(X,b),\mathrm{cp}(X,c_1))\quad\text{where } X=f^{\sharp}_{\mathsf{while}\ b\ \mathsf{do}\ c_1}(A).
\end{aligned}`

The second command of a sequence is rewritten with the abstract store after the first. Both branches of a conditional are rewritten with the store before it. The guard and the body of a loop are rewritten with $`X`, the result of the transfer of Session 17 for the whole loop, not with the store at loop entry. By the entry and preservation inclusions of [Session 17, §17.2](chapter-17/index.html#ch17-s2) and Theorem 17.8 for the body, $`X` describes the store at every test of the guard on a run that starts in $`\gamma(A)`. We call $`X` the *loop-head store*.

*Lemma 18.3 (Executions of the simplified conditional and loop).* For every guard $`b`, all commands $`c,d` and all stores $`s,m,t`:

* (a) Let $`k` be $`c` if $`B(b,s)=\mathsf{true}` and $`d` otherwise. If $`s\vdash k\Downarrow t`, then $`s\vdash\widehat{\mathsf{if}}(b,c,d)\Downarrow t`.
* (b) If $`B(b,s)=\mathsf{false}`, then $`s\vdash\widehat{\mathsf{while}}(b,c)\Downarrow s`.
* (c) If $`B(b,s)=\mathsf{true}`, $`s\vdash c\Downarrow m` and $`m\vdash\widehat{\mathsf{while}}(b,c)\Downarrow t`, then $`s\vdash\widehat{\mathsf{while}}(b,c)\Downarrow t`.

*Proof.* (a) If $`b` is $`\mathsf{true}`, then $`B(b,s)=\mathsf{true}`, so $`k=c=\widehat{\mathsf{if}}(b,c,d)`. The case $`\mathsf{false}` is symmetric. Otherwise $`\widehat{\mathsf{if}}(b,c,d)` is the plain conditional, and the conditional rule of A.5 applies. (b) If $`b` is $`\mathsf{false}`, the skip rule gives $`s\vdash\mathsf{skip}\Downarrow s`. Otherwise the loop exit rule applies to the plain loop. (c) Since $`B(\mathsf{false},s)=\mathsf{false}`, the guard $`b` is not $`\mathsf{false}`. So $`\widehat{\mathsf{while}}(b,c)` is the plain loop, and the loop iteration rule applies. $`\square`

Parts (b) and (c) say that the simplified loop obeys the two loop rules of A.5.

*A join before a rewrite.* Let $`I=\mathsf{if}\ g=0\ \mathsf{then}\ (x:=4;\ y:=1)\ \mathsf{else}\ (x:=4;\ y:=2)` and consider $`I;\ z:=x+3` from $`\{\}`. The guard $`g=0` becomes $`g\mathbin{\hat=}0`, which is the plain guard $`g=0`, so $`\mathrm{cp}(\{\},I)=I`. The abstract value of the guard is unknown, so Session 17 joins the two branch results: $`f^{\sharp}_{I}(\{\})=\{x\mapsto4,y\mapsto1\}\sqcup\{x\mapsto4,y\mapsto2\}=\{x\mapsto4\}`. The suffix is rewritten with this store:

$$`\mathrm{cp}(\{\},\ I;\ z:=x+3)=I;\ z:=7.`

From a store with $`g=0`, the true branch reaches an intermediate store with $`x=4,y=1`. From a store with $`g=9`, the false branch reaches $`x=4,y=2`. Both intermediate stores are described by $`\{x\mapsto4\}`, and in both the original suffix writes $`4+3=7`. The value of $`y` differs between the two stores, so replacing a read of $`y` after the join would have no justification.

*A loop.* Let $`W=\mathsf{while}\ x\le y\ \mathsf{do}\ x:=x+1` and consider $`(x:=0;\ y:=2);\ W` from $`\{\}`. Before the loop the abstract store is $`A=\{x\mapsto0,y\mapsto2\}`. Session 17 computes the loop-head store $`X=f^{\sharp}_{W}(A)=\{y\mapsto2\}`. It satisfies the two inclusions of Session 17: $`\gamma(A)\subseteq\gamma(X)`, and $`\gamma(f^{\sharp}_{x:=x+1}(X))\subseteq\gamma(X)` because $`f^{\sharp}_{x:=x+1}(X)=\{y\mapsto2\}`. The guard becomes $`x\mathbin{\hat\le}2`, which is $`x\le2`, and the body is unchanged:

$$`\mathrm{cp}(\{\},\ (x:=0;\ y:=2);\ W)=(x:=0;\ y:=2);\ \mathsf{while}\ x\le2\ \mathsf{do}\ x:=x+1.`

Both programs pass the guard with $`x=0,1,2` and stop with $`x=3`. Suppose instead the guard were rewritten with the entry store $`A`. It would become $`0\mathbin{\hat\le}2=\mathsf{true}`, and the loop would become $`\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ x:=x+1`, which has no terminating execution. The fact $`x=0` holds at the first test of the guard only. The rewritten guard is evaluated at every test.

# Preservation of terminating executions
%%%
tag := "ch18-s3"
%%%

In the join example, start from a store $`s` with $`s(g)=9`. The original program runs the false branch to a store $`m` with $`m(x)=4` and $`m(y)=2`, then writes 7 to $`z`. The transformed program runs the same branch to the same $`m` and writes the literal 7 to $`z`. Both end in $`m[z\mapsto7]`. The theorem states this for every program, every abstract store and every terminating execution.

The proof uses Session 17, Theorem 17.8: for every command $`c`, abstract store $`A` and stores $`s,t`,

$$`\bigl(s\in\gamma(A)\land s\vdash c\Downarrow t\bigr)\Rightarrow t\in\gamma(f^{\sharp}_{c}(A)).`

*Theorem 18.4 (Preservation of terminating executions).* For every command $`c`, abstract store $`A` and stores $`s,t`, if $`s\in\gamma(A)` and $`s\vdash c\Downarrow t`, then $`s\vdash\mathrm{cp}(A,c)\Downarrow t`.

We prove $`P(c)` for every command $`c` by structural induction on $`c` (A.4), with the induction property

$$`P(c)\coloneqq\forall A,s,t,\ \bigl(s\in\gamma(A)\land s\vdash c\Downarrow t\bigr)\Rightarrow s\vdash\mathrm{cp}(A,c)\Downarrow t.`

The abstract store is quantified inside $`P(c)`. Definition 18.3 rewrites $`c_2` in a sequence with $`f^{\sharp}_{c_1}(A)` and the body of a loop with $`X`, so the hypotheses must be usable at those stores. The induction is on the command, not on the derivation as in Session 3. In a loop iteration, the last premise $`m\vdash W\Downarrow t` concerns the same loop. A hypothesis for it at the abstract store $`X` would speak about $`\mathrm{cp}(X,W)`, whose loop-head store is $`f^{\sharp}_{W}(X)`. To identify it with the loop we are building we would need $`f^{\sharp}_{W}(X)=X`, a fact about how Session 17 computes loop-head stores. The loop case instead uses an inner induction with $`X` fixed.

*Skip and assignment.* For skip, the derivation ends with the skip rule, so $`t=s`, and $`\mathrm{cp}(A,\mathsf{skip})=\mathsf{skip}`. For $`c=(x:=e)`, Session 3, Lemma 3.1 gives $`t=s[x\mapsto\mathrm{eval}(e,s)]`. Lemma 18.2 gives $`\mathrm{eval}(\mathrm{cp}(A,e),s)=\mathrm{eval}(e,s)`, so the assignment rule derives $`s\vdash x:=\mathrm{cp}(A,e)\Downarrow t`.

*Conditional (board case).* Suppose $`c=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`. The induction hypotheses for the branches are

$$`\begin{aligned}
P(c_1)&:\quad\forall A',s',t',\ \bigl(s'\in\gamma(A')\land s'\vdash c_1\Downarrow t'\bigr)\Rightarrow s'\vdash\mathrm{cp}(A',c_1)\Downarrow t',\\
P(c_2)&:\quad\forall A',s',t',\ \bigl(s'\in\gamma(A')\land s'\vdash c_2\Downarrow t'\bigr)\Rightarrow s'\vdash\mathrm{cp}(A',c_2)\Downarrow t'.
\end{aligned}`

1. Fix $`A,s,t` with $`s\in\gamma(A)` and a derivation $`D:s\vdash c\Downarrow t`. We must show $`s\vdash\widehat{\mathsf{if}}(\mathrm{cp}(A,b),\mathrm{cp}(A,c_1),\mathrm{cp}(A,c_2))\Downarrow t`, since this command is $`\mathrm{cp}(A,c)` by Definition 18.3.
2. $`D` ends with the conditional rule, the only rule of A.5 whose conclusion has a conditional. Inversion gives $`D_1:s\vdash k\Downarrow t`, where $`k=c_1` if $`B(b,s)=\mathsf{true}` and $`k=c_2` otherwise.
3. Apply $`P(k)`, the hypothesis of the selected branch, at $`A'=A`, $`s'=s`, $`t'=t` to $`s\in\gamma(A)` and $`D_1`. This gives $`s\vdash\mathrm{cp}(A,k)\Downarrow t`.
4. Apply Lemma 18.2 to the guard $`b` and $`s\in\gamma(A)`. This gives $`B(\mathrm{cp}(A,b),s)=B(b,s)`. So $`\mathrm{cp}(A,k)` is $`\mathrm{cp}(A,c_1)` if $`B(\mathrm{cp}(A,b),s)=\mathsf{true}` and $`\mathrm{cp}(A,c_2)` otherwise.
5. Apply Lemma 18.3(a) to the guard $`\mathrm{cp}(A,b)` and the commands $`\mathrm{cp}(A,c_1),\mathrm{cp}(A,c_2)`. By step 4 the command it selects at $`s` is $`\mathrm{cp}(A,k)`, so step 3 is its premise. This gives the claim of step 1.

If $`\mathrm{cp}(A,b)` is the constant $`\mathsf{true}`, the transformed command is $`\mathrm{cp}(A,c_1)` alone. Step 4 then gives $`B(b,s)=\mathsf{true}` for every $`s\in\gamma(A)`, so the deleted branch is never selected from a store in $`\gamma(A)`. Both branches are rewritten with the same $`A`, and this case does not need Theorem 17.8.

*Sequence.* Suppose $`c=c_1;c_2`. The hypotheses $`P(c_1)` and $`P(c_2)` have the form displayed for the conditional. Fix $`A,s,t` with $`s\in\gamma(A)` and $`D:s\vdash c_1;c_2\Downarrow t`. We must show $`s\vdash\mathrm{cp}(A,c_1);\mathrm{cp}(f^{\sharp}_{c_1}(A),c_2)\Downarrow t`. Sequence inversion (Session 2, Proposition 2.2) gives a store $`m` with $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash c_2\Downarrow t`.

1. Apply $`P(c_1)` at $`A,s,m` to $`s\in\gamma(A)` and $`D_1`. This gives $`s\vdash\mathrm{cp}(A,c_1)\Downarrow m`.
2. Apply Session 17, Theorem 17.8, to $`s\in\gamma(A)` and $`D_1`. This gives $`m\in\gamma(f^{\sharp}_{c_1}(A))`.
3. Apply $`P(c_2)` at $`f^{\sharp}_{c_1}(A),m,t` to step 2 and $`D_2`. This gives $`m\vdash\mathrm{cp}(f^{\sharp}_{c_1}(A),c_2)\Downarrow t`.
4. The sequence rule joins steps 1 and 3.

Step 2 uses the original derivation $`D_1`, not the transformed one. Step 1 returns exactly the store $`m`, so step 3 starts from the same store on both sides. In Session 20 the transformed program may reach a different intermediate store, and the proof will need a relation between the two stores.

*Loop.* Suppose $`c=W=\mathsf{while}\ b\ \mathsf{do}\ c_1` (we write $`c_1` for the body because $`c` names the whole command). The hypothesis is $`P(c_1)`. Fix $`A,s,t` with $`s\in\gamma(A)` and $`D:s\vdash W\Downarrow t`. We must show $`s\vdash\mathrm{cp}(A,W)\Downarrow t`. Let $`X=f^{\sharp}_{W}(A)` and $`W'=\widehat{\mathsf{while}}(\mathrm{cp}(X,b),\mathrm{cp}(X,c_1))`, so $`\mathrm{cp}(A,W)=W'`. Session 17, §17.2, gives the entry and preservation inclusions for the loop-head store:

$$`\text{(i)}\ \ \gamma(A)\subseteq\gamma(X),\qquad\text{(ii)}\ \ \gamma(f^{\sharp}_{c_1}(X))\subseteq\gamma(X).`

By induction on loop executions $`E:u\vdash W\Downarrow v` (Session 3, §3.1), with $`X` and $`W'` fixed, we prove

$$`R(E)\coloneqq u\in\gamma(X)\Rightarrow u\vdash W'\Downarrow v.`

If $`E` ends with the loop exit rule, then $`B(b,u)=\mathsf{false}` and $`v=u`. Lemma 18.2 at $`X` gives $`B(\mathrm{cp}(X,b),u)=\mathsf{false}`, and Lemma 18.3(b) gives $`u\vdash W'\Downarrow u`. If $`E` ends with the loop iteration rule, then $`B(b,u)=\mathsf{true}` and there are $`E_1:u\vdash c_1\Downarrow m` and $`E_2:m\vdash W\Downarrow v` with the hypothesis $`R(E_2):m\in\gamma(X)\Rightarrow m\vdash W'\Downarrow v`. Assume $`u\in\gamma(X)`. We must show $`u\vdash W'\Downarrow v`.

1. Lemma 18.2 at $`X` gives $`B(\mathrm{cp}(X,b),u)=\mathsf{true}`.
2. Apply $`P(c_1)` at $`X,u,m` to $`u\in\gamma(X)` and $`E_1`. This gives $`u\vdash\mathrm{cp}(X,c_1)\Downarrow m`.
3. Session 17, Theorem 17.8, applied to $`u\in\gamma(X)` and $`E_1` gives $`m\in\gamma(f^{\sharp}_{c_1}(X))`. By (ii), $`m\in\gamma(X)`.
4. Apply $`R(E_2)` to step 3. This gives $`m\vdash W'\Downarrow v`.
5. Lemma 18.3(c) with steps 1, 2 and 4 gives $`u\vdash W'\Downarrow v`.

Finally, inclusion (i) gives $`s\in\gamma(X)`, and $`R(D)` gives $`s\vdash W'\Downarrow t`. Step 3 is where $`X` matters. With the entry store $`A` in place of $`X`, step 3 would need $`m\in\gamma(A)`. In the loop of §18.2 this fails after the first iteration, where $`m(x)=1`.

This proves $`P(c)` for every command $`c`, which is Theorem 18.4. $`\square`

*Scope.* The theorem assumes a terminating execution of the original program. If the first command of a sequence diverges from $`s`, no store reaches the second command, and the rewritten second command is never run from $`s`. The theorem says nothing about such inputs. The premise $`s\in\gamma(A)` cannot be dropped (Exercise 18.2). The theorem gives one direction only: it does not say that a terminating execution of $`\mathrm{cp}(A,c)` comes from one of $`c` (Further problem).

# Exercises
%%%
tag := "ch18-s4"
number := false
%%%

*18.1.* In the join example, change the false branch to `x := 5; y := 2`. Compute $`f^{\sharp}_{I}(\{\})` and $`\mathrm{cp}(\{\},\ I;\ z:=x+3)`. Give an input on which replacing the suffix by `z := 7` changes the final store.

*18.2.* Let $`A=\{x\mapsto4\}` and $`c=(z:=x)`. Compute $`\mathrm{cp}(A,c)`. Run both commands from a store with $`s(x)=9`. Which hypothesis of Theorem 18.4 fails?

*18.3.* A compiler keeps a single table while it walks through a program. At a conditional it processes the true branch, then the false branch, and continues after the conditional with the table left by the false branch. Find a program and an input on which this compiler changes the final store. Which step of the sequence case fails?

*18.4.* Session 20 removes assignments whose results are never read and proves only that final stores agree on a set of observed variables. For `x := 1; y := 2` and the observed set $`\{y\}`, show that deleting the first assignment keeps the value of $`y` but not the final store. Why does the conclusion of Theorem 18.4 give agreement on every observed set?

*Further problem.* Let $`c` contain no loop, $`s\in\gamma(A)` and $`s\vdash\mathrm{cp}(A,c)\Downarrow t`. Prove $`s\vdash c\Downarrow t`. First show by structural induction that every loop-free command has a terminating execution from every store. Then use Theorem 18.4 and Session 3, Theorem 3.2. Which step fails when $`c` contains a loop?

# Reading for the Seminar
%%%
tag := "ch18-s5"
number := false
%%%

*Definitions · 10 minutes.* Compute both abstract branch results of the join example, their join, and the transformed program. Then rewrite the loop example once with the loop-head store and once with the entry store.

*Joint proof · 30 minutes.* Prove the conditional case in five steps. Then prove the sequence case, writing separate lines for the transformed first command and for the fact that the intermediate store lies in $`\gamma(f^{\sharp}_{c_1}(A))`. Apply the hypothesis for $`c_2` only after obtaining both.

*Proof review · 20 minutes.* Rewrite the loop guard with the entry store and run the loop case. Identify the step that can no longer be proved. Use Exercise 18.3 to test the sequence case.

*Facilitator’s hint.* Ask which abstract store was used to rewrite the code that is about to run. That abstract store must describe the concrete store at that point.

# Solutions and Further Reading
%%%
tag := "ch18-s6"
number := false
%%%

*18.1.* $`f^{\sharp}_{I}(\{\})=\{x\mapsto4,y\mapsto1\}\sqcup\{x\mapsto5,y\mapsto2\}=\{\}`, since the two results have no common entry. So $`\mathrm{cp}(\{\},\ I;\ z:=x+3)=I;\ z:=x+3`, because $`x\mathbin{\hat+}3=x+3`. From a store with $`g=9` the false branch sets $`x` to 5 and the original suffix writes 8. Writing 7 would change the final store.

*18.2.* $`\mathrm{cp}(A,c)=(z:=4)`. From $`s` with $`s(x)=9` the original ends with $`z=9` and the transformed command with $`z=4`. The store $`s` is not described by $`A`, so the premise $`s\in\gamma(A)` fails. The conclusion fails with it.

*18.3.* Take $`(\mathsf{if}\ g=0\ \mathsf{then}\ y:=1\ \mathsf{else}\ y:=2);\ z:=y`. The compiler leaves the table $`\{y\mapsto2\}` and rewrites the suffix to `z := 2`. From a store with $`g=0` the original writes 1 to $`z`. Session 17’s transfer gives $`\{y\mapsto1\}\sqcup\{y\mapsto2\}=\{\}` after the conditional. In the sequence case, step 3 needs the intermediate store $`m` to be described by the abstract store used for the suffix. Here $`m(y)=1`, so $`m` is not described by $`\{y\mapsto2\}`, and Theorem 17.8 only gives $`m\in\gamma(\{\})`.

*18.4.* From a store with $`s(x)=0`, the original ends with $`x=1,y=2` and the shortened command with $`x=0,y=2`. The values of $`y` agree and the final stores differ. Theorem 18.4 gives the same final store $`t` on both sides. Equal stores agree at every variable, hence on every observed set.

*Further problem.* Existence: skip and assignment each have one rule that applies from every store. For $`c_1;c_2`, the hypothesis for $`c_1` gives $`s\vdash c_1\Downarrow m`, and the hypothesis for $`c_2` at $`m` gives $`m\vdash c_2\Downarrow t'`. For a conditional, the hypothesis for the selected branch applies. So $`s\vdash c\Downarrow t'` for some $`t'`. Theorem 18.4 gives $`s\vdash\mathrm{cp}(A,c)\Downarrow t'`. Determinacy for the command $`\mathrm{cp}(A,c)` gives $`t=t'`, so $`s\vdash c\Downarrow t`. With a loop the first step fails: $`c` may have no terminating execution from $`s`, and Theorem 18.4 alone does not exclude that $`\mathrm{cp}(A,c)` has one. Nipkow and Klein prove both directions for their transformation (CS Lemma 10.12).

*Further reading · The complete simplifying constructors.* Leroy’s course defines them as follows (§8.1). Write $`\overline{k}` for the literal with value $`k`, and read “$`e` is $`e_1+\overline{m}`” as “$`e` is a sum whose right operand is a literal”. An auxiliary function adds a literal: $`\mathrm{addc}(e,n)` is $`e` if $`n=0`. Otherwise it is $`\overline{m+n}` if $`e` is $`\overline{m}`, $`e_1+\overline{m+n}` if $`e` is $`e_1+\overline{m}`, and $`e+\overline{n}` in all other cases. In the following lists the first matching line applies.

* $`a_1\mathbin{\hat+}a_2`: $`\mathrm{addc}(a_2,m)` if $`a_1=\overline{m}`; $`\mathrm{addc}(a_1,m)` if $`a_2=\overline{m}`; $`\mathrm{addc}(e_1+e_2,m_1+m_2)` if $`a_1=e_1+\overline{m_1}` and $`a_2=e_2+\overline{m_2}`; $`\mathrm{addc}(e_1+a_2,m_1)` if $`a_1=e_1+\overline{m_1}`; $`\mathrm{addc}(a_1+e_2,m_2)` if $`a_2=e_2+\overline{m_2}`; otherwise $`a_1+a_2`.
* $`a_1\mathbin{\hat-}a_2`: $`\mathrm{addc}(a_1,-m)` if $`a_2=\overline{m}`; $`\mathrm{addc}(e_1-e_2,m_1-m_2)` if $`a_1=e_1+\overline{m_1}` and $`a_2=e_2+\overline{m_2}`; $`\mathrm{addc}(e_1-a_2,m_1)` if $`a_1=e_1+\overline{m_1}`; $`\mathrm{addc}(a_1-e_2,-m_2)` if $`a_2=e_2+\overline{m_2}`; otherwise $`a_1-a_2`.
* $`a_1\mathbin{\hat=}a_2`: $`\mathsf{true}` or $`\mathsf{false}` if both are literals; $`e_1=\overline{n_2-n_1}` if $`a_1=e_1+\overline{n_1}` and $`a_2=\overline{n_2}`; otherwise $`a_1=a_2`. The constructor $`\hat\le` is the same with $`\le`.
* $`\hat\neg` and $`\hat\land` are given completely in Definition 18.1.

*Further reading · A coarser analysis.* In _Concrete Semantics_, §10.2, the table after a loop is the table before it with every variable assigned in the body removed. Leroy’s loop-head store can keep more. For $`\mathsf{while}\ b\ \mathsf{do}\ (y:=2;\ x:=x+1)` entered with $`\{y\mapsto2\}`, the loop-head store is $`\{y\mapsto2\}`, because each iteration assigns the same constant to $`y`. The coarser table forgets $`y`. Nipkow and Klein also leave guards unchanged, and fold a sum only when both operands fold to literals. In return they prove that the two commands have the same terminating executions from stores that the table describes, using equivalence of commands under a precondition (CS §10.2.3).

# Sources and Formalization
%%%
tag := "ch18-notes"
number := false
%%%

* *Lemma 18.1.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 18.2.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 18.3.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 18.4.* Corresponds to CS Lemma 10.12. Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
