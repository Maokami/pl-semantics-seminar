import VersoManual
import PLBook.IMP.Hoare

open Verso.Genre Manual

#doc (Manual) "Hoare Triples and Assignment" =>
%%%
tag := "ch11"
file := "chapter-11"
%%%

A command increases $`x` by 3, and afterwards $`x` must equal 8. Which initial states are acceptable? Exactly those with $`x=5`. The answer comes from replacing $`x` by $`x+3` in the requirement: $`x+3=8`. This session proves that such replacement is correct for every assignment and every requirement written with expressions.

*In this session.*

* *Definitions.* States and update, expression evaluation, guard values and execution ([IMP language card A.2–A.5](imp-card/index.html#imp-a2)). Structural induction ([A.1](imp-card/index.html#imp-a1)). The assignment result ([Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2)) and sequence inversion ([Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3)).
* *New terms.* Substitution, assertion, Hoare triple, partial correctness, substituted assertion. [Glossary](glossary/index.html)
* *Theorem 11.7 (Validity of assignment triples).* For every assertion $`Q`, name $`x` and expression $`e`, $`\models\{Q[e/x]\}\,x:=e\,\{Q\}`. If $`Q` is written $`\varphi(a_1,\ldots,a_j)` with expressions $`a_1,\ldots,a_j`, then $`\models\{\varphi(a_1[e/x],\ldots,a_j[e/x])\}\,x:=e\,\{\varphi(a_1,\ldots,a_j)\}`.
* *Board case.* Theorem 11.7 for a postcondition written with expressions (the four steps at the end of §11.3). Invert the execution, then apply the substitution lemma to each expression. Prepare the variable case of Lemma 11.3.
* *Proof outline.* Lemma 11.3 is proved by structural induction on $`a` with $`e,x,\sigma` fixed, for $`L(a)\coloneqq\mathrm{eval}(a[e/x],\sigma)=\mathrm{eval}(a,\sigma[x\mapsto\mathrm{eval}(e,\sigma)])`. Theorem 11.7 needs no induction. Inversion gives the final state $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. The precondition at $`\sigma` is then the postcondition at $`\sigma'`.
* *From Session 10.* Session 10 related terminating executions to the meaning of a command. Hoare logic asks a different question about the same execution relation. It does not compute the final state. It states a property that every final state has.

# Substitution
%%%
tag := "ch11-s1"
%%%

An assignment $`x:=e` changes the value of $`x` and nothing else. A later expression that reads $`x` sees the value of $`e` computed in the earlier state. Substitution expresses this with syntax.

*Definition 11.1 (Substitution).* For expressions $`a,e` and a name $`x`, the expression $`a[e/x]` is obtained from $`a` by replacing each occurrence of $`x` with $`e`. It is defined by structural recursion on $`a`:

$$`\begin{aligned}
n[e/x]&=n\\
y[e/x]&=e\quad\text{if }y=x, & y[e/x]&=y\quad\text{if }y\neq x\\
(a_1+a_2)[e/x]&=a_1[e/x]+a_2[e/x], & (a_1-a_2)[e/x]&=a_1[e/x]-a_2[e/x].
\end{aligned}`

Read $`a[e/x]` as “$`a` with $`e` for $`x`”. The replacement is simultaneous and happens once. Occurrences of $`x` inside the inserted copy of $`e` are not replaced again. For example, $`x[(x+1)/x]` is $`x+1`, not $`(x+1)+1`. A definition that also processed the inserted tree would never terminate on this example.

*Example 11.2.* Substitute $`x+1` for $`x` in $`x+x`. The result is $`(x+1)+(x+1)`. If $`\sigma(x)=2`, it evaluates to 6. Now evaluate the original $`x+x` in the updated state $`\sigma[x\mapsto3]`. The result is again 6. The value 3 stored at $`x` is $`\mathrm{eval}(x+1,\sigma)`, computed in the original state.

*Lemma 11.3 (Substitution lemma).* For all expressions $`a,e`, every name $`x` and every state $`\sigma`,

$$`\mathrm{eval}(a[e/x],\sigma)=\mathrm{eval}\bigl(a,\,\sigma[x\mapsto\mathrm{eval}(e,\sigma)]\bigr).`

*Proof.* Fix $`e`, $`x` and $`\sigma`, and put $`\sigma''=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. We prove by structural induction on $`a` the induction property

$$`L(a)\quad\coloneqq\quad\mathrm{eval}(a[e/x],\sigma)=\mathrm{eval}(a,\sigma'').`

*Literal.* Here $`n[e/x]=n`, and both sides equal $`n`.

*Variable, same name.* Let $`a=x`. We must show $`\mathrm{eval}(x[e/x],\sigma)=\mathrm{eval}(x,\sigma'')`.

1. By Definition 11.1, $`x[e/x]=e`. So the left side is $`\mathrm{eval}(e,\sigma)`.
2. By A.3, the right side is $`\sigma''(x)`.
3. By A.2, the update stores $`\mathrm{eval}(e,\sigma)` at $`x`, so $`\sigma''(x)=\mathrm{eval}(e,\sigma)`. The two sides agree.

*Variable, other name.* Let $`a=y` with $`y\neq x`. Then $`y[e/x]=y`, so the left side is $`\sigma(y)`. The right side is $`\sigma''(y)`, which equals $`\sigma(y)` because the update changes only $`x`.

*Addition.* Let $`a=a_1+a_2`. The induction hypotheses are

$$`\begin{aligned}
L(a_1)&:\quad\mathrm{eval}(a_1[e/x],\sigma)=\mathrm{eval}(a_1,\sigma''),\\
L(a_2)&:\quad\mathrm{eval}(a_2[e/x],\sigma)=\mathrm{eval}(a_2,\sigma'').
\end{aligned}`

Definition 11.1, then A.3, then the two hypotheses, then A.3 again give

$$`\mathrm{eval}(a[e/x],\sigma)=\mathrm{eval}(a_1[e/x],\sigma)+\mathrm{eval}(a_2[e/x],\sigma)=\mathrm{eval}(a_1,\sigma'')+\mathrm{eval}(a_2,\sigma'')=\mathrm{eval}(a,\sigma'').`

*Subtraction.* The same chain with subtraction in place of addition proves $`L(a_1-a_2)` from $`L(a_1)` and $`L(a_2)`. $`\square`

Only the variable case uses the update. The state $`\sigma` stays fixed in the induction because every recursive call in A.3 uses the same state.

# Assertions and triples
%%%
tag := "ch11-s2"
%%%

Let $`x,y` be distinct names. Should every final state of `x := x + 1` satisfy $`x\le y` when the initial state does? Start in a state with $`x=y=0`. The assignment rule gives the final state with $`x=1` and $`y=0`, where $`x\le y` fails. Now require $`x<y` at the start instead, and take an initial state $`\sigma` with $`\sigma(x)<\sigma(y)`. By [Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2), the final state $`\sigma'` satisfies $`\sigma'(x)=\sigma(x)+1` and $`\sigma'(y)=\sigma(y)`. Over the integers $`\sigma(x)<\sigma(y)` implies $`\sigma(x)+1\le\sigma(y)`. So every final state satisfies $`x\le y`.

*Definition 11.4 (Assertions and triples).* An *assertion* is a statement $`P(\sigma)` about a state $`\sigma` that is either true or false for each $`\sigma\in\Sigma`. Two assertions are equal when they hold at the same states. An assertion is mathematics, not program syntax. It may use multiplication, quantifiers over integers and fixed integers. A *Hoare triple* $`\{P\}\,c\,\{Q\}` consists of a *precondition* $`P`, a command $`c` and a *postcondition* $`Q`. The triple is *valid*, written $`\models\{P\}\,c\,\{Q\}`, when

$$`\forall\sigma,\sigma'\in\Sigma,\quad\bigl(P(\sigma)\land\sigma\vdash c\Downarrow\sigma'\bigr)\Longrightarrow Q(\sigma').`

This notion of validity is called *partial correctness*. It constrains only the terminating executions.

Most assertions in this book read the state only through expressions. Let $`a_1,\ldots,a_j` be expressions and let $`\varphi` be a statement about $`j` integers $`n_1,\ldots,n_j` that mentions no names. The assertion *written* $`\varphi(a_1,\ldots,a_j)` holds at $`\sigma` when $`\varphi(\mathrm{eval}(a_1,\sigma),\ldots,\mathrm{eval}(a_j,\sigma))` is true. Thus a name $`x` in a concrete assertion stands for its value $`\sigma(x)`. For example, $`x\le y` is written $`\varphi(x,y)` with $`\varphi(n_1,n_2)\coloneqq(n_1\le n_2)`.

In *axiomatic semantics* we describe a command by the assertions that rules allow us to prove about it. Hoare logic uses triples for this purpose. Definition 11.4 tells us how to test a triple against executions. [Section 12.2](chapter-12/index.html#ch12-s2) will give rules for deriving triples, and §12.3 will prove the rules sound.

Take $`c=(x:=x+1)`. Let $`\sigma(x)=3` and write $`\sigma'=\sigma[x\mapsto4]`. The four readings below use the same command.

* *Big-step execution.* $`\sigma\vdash c\Downarrow\sigma'`. The assignment rule gives the whole final state.
* *Small-step execution.* $`\langle c,\sigma\rangle\to\langle\mathsf{skip},\sigma'\rangle`. Assignment takes one command step because the rule uses the evaluation function on the right-hand side to compute the new state directly.
* *Denotation.* For every state $`\rho`, $`f_c(\rho)=\rho[x\mapsto\rho(x)+1]`, viewed as an element of $`\Sigma_\bot`. Applying this function to $`\sigma` gives $`\sigma'`.
* *Hoare specification.* $`\models\{x=3\}\,c\,\{x=4\}`. For every initial state satisfying the precondition, every terminating execution ends with 4 at $`x`. The assignment also preserves $`y` for $`y\ne x`, but that fact cannot be read from this postcondition.

An invalid triple has a witness: states $`\sigma,\sigma'` with $`P(\sigma)`, $`\sigma\vdash c\Downarrow\sigma'` and not $`Q(\sigma')`. The two states in the opening example of this section are such a witness. Partial correctness asks nothing of a state from which no execution terminates. Let $`W=\mathsf{while\ true\ do\ skip}`. By [Session 2, §2.4](chapter-02/index.html#ch02-s4), no state has a terminating execution of $`W`. Hence $`\models\{P\}\,W\,\{Q\}` for all assertions $`P,Q`, even when $`Q` holds at no state. Session 13 adds termination to the specification.

# Validity of assignment triples
%%%
tag := "ch11-s3"
%%%

Return to the opening question. Let $`Q` be $`x=8`. By Lemma 3.1 the final state of `x := x + 3` from $`\sigma` is $`\sigma'=\sigma[x\mapsto\sigma(x)+3]`. So $`Q(\sigma')` holds exactly when $`\sigma(x)+3=8`. The acceptable initial states are those at which $`Q` holds after the update.

*Definition 11.5 (Substituted assertion).* For an assertion $`Q`, a name $`x` and an expression $`e`, the assertion $`Q[e/x]` is defined by

$$`Q[e/x](\sigma)\quad\Longleftrightarrow\quad Q\bigl(\sigma[x\mapsto\mathrm{eval}(e,\sigma)]\bigr)\qquad\text{for every }\sigma\in\Sigma.`

Definition 11.5 uses the state update, not text. For an assertion written with expressions, text suffices. Take distinct $`x,y`, the postcondition $`y\ge0\land x\ge4` and the command `x := y + 1`. The postcondition is written with $`a_1=y` and $`a_2=x`. Substitution gives $`a_1[(y+1)/x]=y` and $`a_2[(y+1)/x]=y+1`, hence the candidate $`y\ge0\land y+1\ge4`. Check it against Definition 11.5. The updated state $`\sigma''=\sigma[x\mapsto\sigma(y)+1]` has $`\sigma''(y)=\sigma(y)` and $`\sigma''(x)=\sigma(y)+1`, so the postcondition at $`\sigma''` is the candidate at $`\sigma`.

*Lemma 11.6 (Substitution in an assertion).* Let $`Q` be written $`\varphi(a_1,\ldots,a_j)`. For every name $`x` and expression $`e`,

$$`Q[e/x]=\varphi\bigl(a_1[e/x],\ldots,a_j[e/x]\bigr).`

*Proof.* Fix $`\sigma` and put $`\sigma''=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. By Definitions 11.5 and 11.4, $`Q[e/x](\sigma)` holds exactly when $`\varphi(\mathrm{eval}(a_1,\sigma''),\ldots,\mathrm{eval}(a_j,\sigma''))` is true. For each $`i`, Lemma 11.3 with $`a=a_i` gives $`\mathrm{eval}(a_i,\sigma'')=\mathrm{eval}(a_i[e/x],\sigma)`. Replacing each argument gives $`\varphi(\mathrm{eval}(a_1[e/x],\sigma),\ldots,\mathrm{eval}(a_j[e/x],\sigma))`, which is the right side at $`\sigma`. $`\square`

The same assertion can be written in more than one way. For example, $`x\le y` is also written with the single expression $`x-y` and the statement $`n_1\le0`. Lemma 11.6 gives the same $`Q[e/x]` for every way of writing $`Q`, because Definition 11.5 does not depend on the writing. The lemma also recovers §11.2: $`(x\le y)[(x+1)/x]` is $`x+1\le y`, which over the integers says $`x<y`.

Substitution runs against the direction of execution. For the postcondition $`x=y+1` and the command `y := x`, Lemma 11.6 gives $`x=x+1`, which holds at no state. Indeed, after `y := x` the two names hold equal values.

Session 12 introduces a proof system whose rules derive triples without mentioning executions, and proves every derived triple valid. Its rule for assignment has no premises and concludes $`\{Q[e/x]\}\,x:=e\,\{Q\}`. Theorem 11.7 below is the assignment case of that proof.

*Theorem 11.7 (Validity of assignment triples).* For every assertion $`Q`, name $`x` and expression $`e`,

$$`\models\{Q[e/x]\}\,x:=e\,\{Q\}.`

If $`Q` is written $`\varphi(a_1,\ldots,a_j)`, then $`\models\{\varphi(a_1[e/x],\ldots,a_j[e/x])\}\,x:=e\,\{\varphi(a_1,\ldots,a_j)\}`.

*Proof.* We must show: for all states $`\sigma,\sigma'`, if $`Q[e/x](\sigma)` and $`\sigma\vdash x:=e\Downarrow\sigma'`, then $`Q(\sigma')`.

1. Fix $`\sigma` and $`\sigma'`. Assume $`Q[e/x](\sigma)` and a derivation $`D` of $`\sigma\vdash x:=e\Downarrow\sigma'`.
2. Suppose $`D` ends with some rule of A.5. Only the assignment rule has an assignment in its conclusion, so $`D` ends with it. [Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2) gives $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`.
3. By Definition 11.5, the assumption $`Q[e/x](\sigma)` states $`Q(\sigma[x\mapsto\mathrm{eval}(e,\sigma)])`. By step 2 this is $`Q(\sigma')`.

For the second statement, Lemma 11.6 identifies the precondition $`\varphi(a_1[e/x],\ldots,a_j[e/x])` with $`Q[e/x]`. The first statement applies. $`\square`

*Board case.* Prove the second statement with Lemma 11.6 unfolded. We must show: for all states $`\sigma,\sigma'`, if $`\varphi(\mathrm{eval}(a_1[e/x],\sigma),\ldots,\mathrm{eval}(a_j[e/x],\sigma))` and $`\sigma\vdash x:=e\Downarrow\sigma'`, then $`\varphi(\mathrm{eval}(a_1,\sigma'),\ldots,\mathrm{eval}(a_j,\sigma'))`.

1. Fix $`\sigma` and $`\sigma'`. Assume the precondition at $`\sigma` and a derivation $`D` of $`\sigma\vdash x:=e\Downarrow\sigma'`.
2. Suppose $`D` ends with the assignment rule, the only rule whose conclusion is an assignment. Lemma 3.1 gives $`\sigma'=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`.
3. For each $`i`, apply Lemma 11.3 with $`a=a_i`. It gives $`\mathrm{eval}(a_i[e/x],\sigma)=\mathrm{eval}(a_i,\sigma[x\mapsto\mathrm{eval}(e,\sigma)])`. By step 2 the right side is $`\mathrm{eval}(a_i,\sigma')`.
4. In the assumed precondition, replace each argument $`\mathrm{eval}(a_i[e/x],\sigma)` by $`\mathrm{eval}(a_i,\sigma')`, using step 3. The result is $`\varphi(\mathrm{eval}(a_1,\sigma'),\ldots,\mathrm{eval}(a_j,\sigma'))`, the postcondition at $`\sigma'`. $`\square`

Step 3 is the only step that uses the syntax of expressions. It is applied once to each expression and never to $`\varphi`.

With the postcondition $`x=8`, Lemma 11.6 gives the precondition $`8=8` for `x := 8` and $`7=8` for `x := 7`. The first holds at every state. The second holds at none. The next proposition shows that, for `x := 7` and this postcondition, no precondition that holds at some state gives a valid triple.

*Proposition 11.8 (Preconditions of an assignment).* For all assertions $`P,Q`, every name $`x` and expression $`e`,

$$`\models\{P\}\,x:=e\,\{Q\}\quad\Longleftrightarrow\quad\forall\sigma\in\Sigma,\ P(\sigma)\Rightarrow Q[e/x](\sigma).`

*Proof.* (⇐) Fix $`\sigma,\sigma'` with $`P(\sigma)` and $`\sigma\vdash x:=e\Downarrow\sigma'`. The assumption gives $`Q[e/x](\sigma)`. Theorem 11.7 applied to $`\sigma`, $`\sigma'` and this execution gives $`Q(\sigma')`. (⇒) Fix $`\sigma` with $`P(\sigma)`. The assignment rule of A.5 derives $`\sigma\vdash x:=e\Downarrow\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. Validity gives $`Q(\sigma[x\mapsto\mathrm{eval}(e,\sigma)])`, which is $`Q[e/x](\sigma)`. $`\square`

The direction (⇒) needs an execution to exist, and every assignment terminates. So $`Q[e/x]` follows from every precondition that makes the triple valid.

# Sequences of assignments
%%%
tag := "ch11-s4"
%%%

Let $`x,y` be distinct. Take the postcondition $`x+y=5` and the command `x := y; y := 1`. Theorem 11.7 for the second assignment gives $`\models\{x+1=5\}\,y:=1\,\{x+y=5\}`, since $`(x+y)[1/y]=x+1`. Theorem 11.7 for the first assignment, with postcondition $`x+1=5`, gives $`\models\{y+1=5\}\,x:=y\,\{x+1=5\}`. The next proposition joins the two triples. Check one state: from $`x=9`, $`y=4` the precondition $`y+1=5` holds, and the program ends with $`x=4`, $`y=1` and $`x+y=5`.

*Proposition 11.9 (Sequence and consequence).* For all assertions and commands,

* (a) if $`\models\{P\}\,c\,\{Q\}` and $`\models\{Q\}\,d\,\{R\}`, then $`\models\{P\}\,c;d\,\{R\}`;
* (b) if $`P'(\sigma)\Rightarrow P(\sigma)` for every $`\sigma`, $`\models\{P\}\,c\,\{Q\}`, and $`Q(\sigma)\Rightarrow Q'(\sigma)` for every $`\sigma`, then $`\models\{P'\}\,c\,\{Q'\}`.

*Proof.* (a) Fix $`\sigma,\sigma'` with $`P(\sigma)` and $`\sigma\vdash c;d\Downarrow\sigma'`. [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3) gives a state $`\sigma_1` with $`\sigma\vdash c\Downarrow\sigma_1` and $`\sigma_1\vdash d\Downarrow\sigma'`. The first triple gives $`Q(\sigma_1)`. The second triple, applied to $`\sigma_1` and $`\sigma'`, gives $`R(\sigma')`. (b) Fix $`\sigma,\sigma'` with $`P'(\sigma)` and $`\sigma\vdash c\Downarrow\sigma'`. The first implication gives $`P(\sigma)`, the triple gives $`Q(\sigma')`, and the second implication gives $`Q'(\sigma')`. $`\square`

The example processed the later assignment first. States are updated in program order. A postcondition is carried back in the opposite order. Doing the two replacements in program order would first replace $`x` by $`y`, giving $`y+y=5`, and then $`y` by 1, giving $`1+1=5`, which holds at no state. That order loses the old value of $`y` read by the first assignment.

For any sequence of assignments, repeated substitution from the end computes a precondition mechanically. What remains is one implication from the given precondition to the computed one. Proposition 11.9(b) turns that implication into a valid triple with the given precondition.

# Exercises
%%%
tag := "ch11-s5"
number := false
%%%

*11.1.* For distinct names $`x,y`, take $`a=x+y` and $`e=y+1`. Compute $`a[e/x]` and $`a[x/y]` in a state with $`\sigma(x)=4` and $`\sigma(y)=2`. For each substitution, give the single state update that yields the same value on the original $`a`.

*11.2.* For distinct names $`x,y`, compute the precondition given by Theorem 11.7 and Proposition 11.9 for `x := y + 2; y := x + 1` and the postcondition $`y=10`. Check it by executing forwards from one state.

*11.3.* A proposed forward rule concludes $`\{Q\}\,x:=e\,\{Q[e/x]\}`. Give an assertion $`Q`, an expression $`e` and a state that show this triple is not valid in general.

*11.4.* Suppose $`x\notin\mathrm{FV}(a_i)` for every $`i`, where $`\mathrm{FV}` is the free-variable set of [Session 1, Definition 1.4](chapter-01/index.html#ch01-s3). Prove $`a_i[e/x]=a_i` and conclude $`\models\{Q\}\,x:=e\,\{Q\}` for $`Q=\varphi(a_1,\ldots,a_j)`. Which result of Session 1 gives the same conclusion without substitution?

*11.5.* Let $`W=\mathsf{while\ true\ do\ skip}`. Explain why every triple $`\{P\}\,W\,\{Q\}` is valid. Then show that $`\{P\}\,(W;c)\,\{Q\}` is valid for every command $`c`.

*11.6.* Define $`b[e/x]` for the guards of A.4 by structural recursion. Prove $`B(b[e/x],\sigma)=B(b,\sigma[x\mapsto\mathrm{eval}(e,\sigma)])`. Which cases use Lemma 11.3?

*Further problem.* For distinct names consider `x := y; y := x` and the postcondition $`x=y\land y\ge4`. Compute its precondition. Compare it with a simultaneous swap $`(x,y):=(y,x)`, in which both right sides read the initial state. Explain where the two backward calculations differ.

# Reading for the Seminar
%%%
tag := "ch11-s6"
number := false
%%%

*Definitions · 10 minutes.* Compute Example 11.2 in both orders: substitute and then evaluate; update and then evaluate. Draw the postcondition $`x=8` as a set of states and an arrow from $`\sigma` to $`\sigma[x\mapsto\sigma(x)+3]`.

*Joint proof · 30 minutes.* One person proves the variable case of Lemma 11.3, both subcases. Then prove Theorem 11.7 by the four board steps. One person inverts the execution, another applies Lemma 11.3 to each expression, and a third rewrites the precondition. Finish with Proposition 11.8 and ask who supplies the execution in the direction (⇒).

*Proof review · 20 minutes.* Work Exercise 11.2 backwards, then check the result by executing forwards from one state. Use Exercise 11.3 to test the direction of the rule.

*Facilitator’s hint.* Write $`Q` applied to the updated state before doing any textual replacement. Track the initial and the final value of the same name separately.

# Solutions and Further Reading
%%%
tag := "ch11-s7"
number := false
%%%

*11.1.* $`a[e/x]=(y+1)+y` has value $`(2+1)+2=5`. Evaluating $`x+y` in $`\sigma[x\mapsto3]` gives the same value, and $`3=\mathrm{eval}(y+1,\sigma)`. $`a[x/y]=x+x` has value $`4+4=8`. Its update is $`\sigma[y\mapsto4]`, with $`4=\mathrm{eval}(x,\sigma)`. In both cases the stored value is computed in the original state.

*11.2.* Through `y := x + 1` the postcondition $`y=10` becomes $`x+1=10`. Through `x := y + 2` this becomes $`(y+2)+1=10`, that is $`y=7`. From any state with $`y=7` the program writes 9 to $`x` and then 10 to $`y`.

*11.3.* Take $`Q` to be $`x=0` and $`e=x+1`. By Lemma 11.6, $`Q[e/x]` is $`x+1=0`. Start in a state with $`x=0`, so $`Q` holds. The final state has $`x=1`, where $`x+1=0` fails.

*11.4.* By structural induction on $`a`: a literal is unchanged; a variable leaf is a name $`y\neq x`, since $`x\notin\mathrm{FV}(y)=\{y\}`; at a binary node $`x` is in neither child’s set, and the two induction hypotheses give the result. Lemma 11.6 then gives $`Q[e/x]=\varphi(a_1,\ldots,a_j)=Q`, and Theorem 11.7 gives the triple. Without substitution, [Session 1, Corollary 1.2](chapter-01/index.html#ch01-s3) gives $`\mathrm{eval}(a_i,\sigma[x\mapsto n])=\mathrm{eval}(a_i,\sigma)` for every $`n`, so $`Q` holds at $`\sigma` exactly when it holds at the updated state.

*11.5.* No state $`\sigma'` satisfies $`\sigma\vdash W\Downarrow\sigma'`, so the premise of validity never holds. An execution $`\sigma\vdash(W;c)\Downarrow\sigma'` would give, by [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3), a state $`\sigma_1` with $`\sigma\vdash W\Downarrow\sigma_1`. There is none, so $`\{P\}\,(W;c)\,\{Q\}` is valid as well. Session 12, Exercise 12.4, derives $`\{P\}\,W\,\{Q\}` in the proof system of that session.

*11.6.* Constants are unchanged. Comparisons substitute into both operands: $`(a_1\le a_2)[e/x]=(a_1[e/x]\le a_2[e/x])`, and likewise for $`=`. Negation and conjunction substitute into their operands. Put $`\sigma''=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]`. In the comparison cases, Lemma 11.3 applied to each operand turns $`\mathrm{eval}(a_i[e/x],\sigma)` into $`\mathrm{eval}(a_i,\sigma'')`. The cases for negation and conjunction use the induction hypotheses for their operands. This is CS Lemma 12.1 for the guards of A.4.

*Further problem.* Through `y := x` the postcondition becomes $`x=x\land x\ge4`, that is $`x\ge4`. Through `x := y` this becomes $`y\ge4`. The simultaneous swap sends $`\sigma` to a state whose value at $`x` is $`\sigma(y)` and at $`y` is $`\sigma(x)`. Its precondition is $`y=x\land x\ge4`. The two substitutions act on the original occurrences at once. Performing them one after the other on already substituted text would turn the equation into $`x=x`. The state with $`x=1`, $`y=5` separates the two preconditions: the sequence ends with two fives, the swap with five and one.

*Further reading · Syntactic and semantic assertions.* _Concrete Semantics_ §12.2.1 (pp. 193–199) first presents Hoare logic with assertions as formulas and the rule $`\{P[a/x]\}\ x ::= a\ \{P\}` (Fig. 12.1, p. 195). Section 12.2.2 (pp. 199–200) then treats assertions as predicates on states and writes the precondition of assignment with the updated state, as in Definition 11.5. Its Lemma 12.1 connects the two presentations for Boolean expressions. Lemma 11.6 plays that role here.

*Further reading · Weakest preconditions.* _Concrete Semantics_ §12.3.1 (pp. 204–205) defines the weakest precondition of a command and a postcondition: it holds at $`\sigma` when every terminating execution from $`\sigma` ends in a state satisfying the postcondition. Fact 12.3 says a triple is valid exactly when its precondition implies the weakest precondition. For an assignment the weakest precondition is $`Q[e/x]`, which is Proposition 11.8. The same section uses weakest preconditions to prove completeness of Hoare logic.

*Further reading · Names bound inside assertions.* In Definition 11.4 a quantifier inside $`\varphi` ranges over integers and binds no name, so substitution never meets a binder. Some assertion languages let a formula bind a name that the program also uses. Take the postcondition $`\exists y,\ x<y` and the command `x := y`. Blind replacement gives $`\exists y,\ y<y`, false at every state. Renaming the bound name first gives $`\exists z,\ x<z` and then $`\exists z,\ y<z`, true at every state. Under Definition 11.4 the postcondition is $`\varphi(x)` with $`\varphi(n_1)\coloneqq\exists k\in\mathbb Z,\ n_1<k`, and Lemma 11.6 gives $`\varphi(y)` directly. Session 22 treats substitution that avoids capture.

*Further reading · Choosing an intermediate assertion.* For distinct $`x,y,z`, require $`z\ge2` after `x := y + 1; z := x + x`. Carrying the postcondition back gives $`x\ge1` before the second assignment and $`y\ge0` before the sequence. From the stronger precondition $`y\ge10`, the intermediate assertion $`x\ge11` also works. From $`y\ge0` it fails at $`y=0`. An intermediate assertion must lie between what the prefix guarantees and what the suffix requires. Substitution computes the latter exactly.

# Sources and Formalization
%%%
tag := "ch11-notes"
number := false
%%%

Triples and validity follow Nipkow and Klein, _Concrete Semantics_, §12.2.2 (assertions as predicates on states), applied to the execution relation of A.5. The triple of Theorem 11.7 is the conclusion of their rule Assign (Fig. 12.3). Theorem 11.7 is the assignment case of their soundness proof (p. 204). Nipkow and Klein state Lemma 11.6 for Boolean expressions. Their Exercise 3.3 poses Lemma 11.3 for their arithmetic expressions. [Concrete Semantics, §§12.2–12.3, pp. 192–205](https://concrete-semantics.org/concrete-semantics.pdf)

* *Lemma 11.3.* Formulated in this book. Corresponds to CS Exercise 3.3. Checked in Lean ([`evalSubst`](lean/Hoare.html#evalSubst) · [IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 11.6.* Formulated in this book. Corresponds to CS Lemma 12.1. Checked in Lean ([`writtenSubst`](lean/Hoare.html#writtenSubst) · [IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 11.7.* Formulated in this book. Corresponds to CS Lemma 12.2, assignment case. Checked in Lean ([`assignmentValid`](lean/Hoare.html#assignmentValid), [`writtenAssignmentValid`](lean/Hoare.html#writtenAssignmentValid) · [IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 11.8.* Formulated in this book. Checked in Lean ([`assignmentPrecondition`](lean/Hoare.html#assignmentPrecondition) · [IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 11.9.* Formulated in this book. Checked in Lean ([`validSequence`](lean/Hoare.html#validSequence), [`validConsequence`](lean/Hoare.html#validConsequence) · [IMP card references](imp-card/index.html#imp-sources)).
