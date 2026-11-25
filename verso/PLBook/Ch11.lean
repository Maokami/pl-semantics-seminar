import VersoManual
import PLBook.IMP.Hoare

open Verso.Genre Manual

#doc (Manual) "Hoare Triples and Assignment" =>
%%%
tag := "ch11"
file := "chapter-11"
%%%

* *Definitions.* Stores and update, expression evaluation, guard values and execution ([IMP language card A.2–A.5](imp-card/index.html#imp-a2)). Structural induction ([A.1](imp-card/index.html#imp-a1)). The assignment result ([Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2)) and sequence inversion ([Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3)).
* *New terms.* Substitution, assertion, Hoare triple, partial correctness, substituted assertion. [Glossary and label key](glossary/index.html)
* *Theorem 11.8 (Validity of assignment triples).* For every assertion $`Q`, name $`x` and expression $`e`, $`\models\{Q[e/x]\}\,x:=e\,\{Q\}`. If $`Q` is written $`\varphi(a_1,\ldots,a_j)` with expressions $`a_1,\ldots,a_j`, then $`\models\{\varphi(a_1[e/x],\ldots,a_j[e/x])\}\,x:=e\,\{\varphi(a_1,\ldots,a_j)\}`.
* *Source.* Triples and validity follow Nipkow and Klein, _Concrete Semantics_, §12.2.2 (assertions as predicates on stores), applied to the execution relation of A.5. The triple of Theorem 11.8 is the conclusion of their rule Assign (Fig. 12.3). Theorem 11.8 is the assignment case of their soundness proof (p. 204). Nipkow and Klein state Lemma 11.6 for Boolean expressions. Their Exercise 3.3 poses Lemma 11.3 for their arithmetic expressions. [Concrete Semantics, §§12.2–12.3, pp. 192–205](https://concrete-semantics.org/concrete-semantics.pdf)
* *Board case.* Theorem 11.8 for a postcondition written with expressions (the four steps at the end of §11.3). Invert the execution, then apply the substitution lemma to each expression. Prepare the variable case of Lemma 11.3.
* *Proof outline.* Lemma 11.3 is proved by structural induction on $`a` with $`e,x,s` fixed, for $`L(a)\coloneqq\mathrm{eval}(a[e/x],s)=\mathrm{eval}(a,s[x\mapsto\mathrm{eval}(e,s)])`. Theorem 11.8 needs no induction. Inversion gives the final store $`t=s[x\mapsto\mathrm{eval}(e,s)]`. The precondition at $`s` is then the postcondition at $`t`.
* *From Session 10.* Session 10 related terminating executions to the denotation of a command. Hoare logic asks a different question about the same execution relation. It does not compute the final store. It states a property that every final store has.

A command increases $`x` by 3, and afterwards $`x` must equal 8. Which initial stores are acceptable? Exactly those with $`x=5`. The answer comes from replacing $`x` by $`x+3` in the requirement: $`x+3=8`. This session proves that such replacement is correct for every assignment and every requirement written with expressions.

# Substitution
%%%
tag := "ch11-s1"
%%%

An assignment $`x:=e` changes the value of $`x` and nothing else. A later expression that reads $`x` sees the value of $`e` computed in the earlier store. Substitution expresses this with syntax.

*Definition 11.1 (Substitution).* For expressions $`a,e` and a name $`x`, the expression $`a[e/x]` is obtained from $`a` by replacing each occurrence of $`x` with $`e`. It is defined by structural recursion on $`a`:

$$`\begin{aligned}
n[e/x]&=n\\
y[e/x]&=e\quad\text{if }y=x, & y[e/x]&=y\quad\text{if }y\neq x\\
(a_1+a_2)[e/x]&=a_1[e/x]+a_2[e/x], & (a_1-a_2)[e/x]&=a_1[e/x]-a_2[e/x].
\end{aligned}`

Read $`a[e/x]` as “$`a` with $`e` for $`x`”. The replacement is simultaneous and happens once. Occurrences of $`x` inside the inserted copy of $`e` are not replaced again. For example, $`x[(x+1)/x]` is $`x+1`, not $`(x+1)+1`. A definition that also processed the inserted tree would never terminate on this example.

*Example 11.2.* Substitute $`x+1` for $`x` in $`x+x`. The result is $`(x+1)+(x+1)`. If $`s(x)=2`, it evaluates to 6. Now evaluate the original $`x+x` in the updated store $`s[x\mapsto3]`. The result is again 6. The value 3 stored at $`x` is $`\mathrm{eval}(x+1,s)`, computed in the original store.

*Lemma 11.3 (Substitution lemma).* For all expressions $`a,e`, every name $`x` and every store $`s`,

$$`\mathrm{eval}(a[e/x],s)=\mathrm{eval}\bigl(a,\,s[x\mapsto\mathrm{eval}(e,s)]\bigr).`

*Proof.* Fix $`e`, $`x` and $`s`, and put $`u=s[x\mapsto\mathrm{eval}(e,s)]`. We prove by structural induction on $`a` the induction property

$$`L(a)\quad\coloneqq\quad\mathrm{eval}(a[e/x],s)=\mathrm{eval}(a,u).`

*Literal.* Here $`n[e/x]=n`, and both sides equal $`n`.

*Variable, same name.* Let $`a=x`. We must show $`\mathrm{eval}(x[e/x],s)=\mathrm{eval}(x,u)`.

1. By Definition 11.1, $`x[e/x]=e`. So the left side is $`\mathrm{eval}(e,s)`.
2. By A.3, the right side is $`u(x)`.
3. By A.2, the update stores $`\mathrm{eval}(e,s)` at $`x`, so $`u(x)=\mathrm{eval}(e,s)`. The two sides agree.

*Variable, other name.* Let $`a=y` with $`y\neq x`. Then $`y[e/x]=y`, so the left side is $`s(y)`. The right side is $`u(y)`, which equals $`s(y)` because the update changes only $`x`.

*Addition.* Let $`a=a_1+a_2`. The induction hypotheses are

$$`\begin{aligned}
L(a_1)&:\quad\mathrm{eval}(a_1[e/x],s)=\mathrm{eval}(a_1,u),\\
L(a_2)&:\quad\mathrm{eval}(a_2[e/x],s)=\mathrm{eval}(a_2,u).
\end{aligned}`

Definition 11.1, then A.3, then the two hypotheses, then A.3 again give

$$`\mathrm{eval}(a[e/x],s)=\mathrm{eval}(a_1[e/x],s)+\mathrm{eval}(a_2[e/x],s)=\mathrm{eval}(a_1,u)+\mathrm{eval}(a_2,u)=\mathrm{eval}(a,u).`

*Subtraction.* The same chain with subtraction in place of addition proves $`L(a_1-a_2)` from $`L(a_1)` and $`L(a_2)`. $`\square`

Only the variable case uses the update. The store $`s` stays fixed in the induction because every recursive call in A.3 uses the same store.

# Assertions and triples
%%%
tag := "ch11-s2"
%%%

Let $`x,y` be distinct names. Should every final store of `x := x + 1` satisfy $`x\le y` when the initial store does? Start in a store with $`x=y=0`. The assignment rule gives the final store with $`x=1` and $`y=0`, where $`x\le y` fails. Now require $`x<y` at the start instead, and take an initial store $`s` with $`s(x)<s(y)`. By [Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2), the final store $`t` satisfies $`t(x)=s(x)+1` and $`t(y)=s(y)`. Over the integers $`s(x)<s(y)` implies $`s(x)+1\le s(y)`. So every final store satisfies $`x\le y`.

*Definition 11.4 (Assertions and triples).* An *assertion* is a statement $`P(s)` about a store $`s` that is either true or false for each $`s\in\Sigma`. Two assertions are equal when they hold at the same stores. An assertion is mathematics, not program syntax. It may use multiplication, quantifiers over integers and fixed integers. A *Hoare triple* $`\{P\}\,c\,\{Q\}` consists of a *precondition* $`P`, a command $`c` and a *postcondition* $`Q`. The triple is *valid*, written $`\models\{P\}\,c\,\{Q\}`, when

$$`\forall s,t\in\Sigma,\quad\bigl(P(s)\land s\vdash c\Downarrow t\bigr)\Longrightarrow Q(t).`

This notion of validity is called *partial correctness*. It constrains only the terminating executions.

Most assertions in this book read the store only through expressions. Let $`a_1,\ldots,a_j` be expressions and let $`\varphi` be a statement about $`j` integers $`n_1,\ldots,n_j` that mentions no names. The assertion *written* $`\varphi(a_1,\ldots,a_j)` holds at $`s` when $`\varphi(\mathrm{eval}(a_1,s),\ldots,\mathrm{eval}(a_j,s))` is true. Thus a name $`x` in a concrete assertion stands for its value $`s(x)`. For example, $`x\le y` is written $`\varphi(x,y)` with $`\varphi(n_1,n_2)\coloneqq(n_1\le n_2)`.

An invalid triple has a witness: stores $`s,t` with $`P(s)`, $`s\vdash c\Downarrow t` and not $`Q(t)`. The two stores in the opening example of this section are such a witness. Partial correctness asks nothing of a store from which no execution terminates. Let $`W=\mathsf{while\ true\ do\ skip}`. By [Session 2, §2.4](chapter-02/index.html#ch02-s4), no store has a terminating execution of $`W`. Hence $`\models\{P\}\,W\,\{Q\}` for all assertions $`P,Q`, even when $`Q` holds at no store. Session 13 adds termination to the specification.

# The assignment rule
%%%
tag := "ch11-s3"
%%%

Return to the opening question. Let $`Q` be $`x=8`. By Lemma 3.1 the final store of `x := x + 3` from $`s` is $`t=s[x\mapsto s(x)+3]`. So $`Q(t)` holds exactly when $`s(x)+3=8`. The acceptable initial stores are those at which $`Q` holds after the update.

*Definition 11.5 (Substituted assertion).* For an assertion $`Q`, a name $`x` and an expression $`e`, the assertion $`Q[e/x]` is defined by

$$`Q[e/x](s)\quad\Longleftrightarrow\quad Q\bigl(s[x\mapsto\mathrm{eval}(e,s)]\bigr)\qquad\text{for every }s\in\Sigma.`

Definition 11.5 uses the store update, not text. For an assertion written with expressions, text suffices. Take distinct $`x,y`, the postcondition $`y\ge0\land x\ge4` and the command `x := y + 1`. The postcondition is written with $`a_1=y` and $`a_2=x`. Substitution gives $`a_1[(y+1)/x]=y` and $`a_2[(y+1)/x]=y+1`, hence the candidate $`y\ge0\land y+1\ge4`. Check it against Definition 11.5. The updated store $`u=s[x\mapsto s(y)+1]` has $`u(y)=s(y)` and $`u(x)=s(y)+1`, so the postcondition at $`u` is the candidate at $`s`.

*Lemma 11.6 (Substitution in an assertion).* Let $`Q` be written $`\varphi(a_1,\ldots,a_j)`. For every name $`x` and expression $`e`,

$$`Q[e/x]=\varphi\bigl(a_1[e/x],\ldots,a_j[e/x]\bigr).`

*Proof.* Fix $`s` and put $`u=s[x\mapsto\mathrm{eval}(e,s)]`. By Definitions 11.5 and 11.4, $`Q[e/x](s)` holds exactly when $`\varphi(\mathrm{eval}(a_1,u),\ldots,\mathrm{eval}(a_j,u))` is true. For each $`i`, Lemma 11.3 with $`a=a_i` gives $`\mathrm{eval}(a_i,u)=\mathrm{eval}(a_i[e/x],s)`. Replacing each argument gives $`\varphi(\mathrm{eval}(a_1[e/x],s),\ldots,\mathrm{eval}(a_j[e/x],s))`, which is the right side at $`s`. $`\square`

The same assertion can be written in more than one way. For example, $`x\le y` is also written with the single expression $`x-y` and the statement $`n_1\le0`. Lemma 11.6 gives the same $`Q[e/x]` for every way of writing $`Q`, because Definition 11.5 does not depend on the writing. The lemma also recovers §11.2: $`(x\le y)[(x+1)/x]` is $`x+1\le y`, which over the integers says $`x<y`.

Substitution runs against the direction of execution. For the postcondition $`x=y+1` and the command `y := x`, Lemma 11.6 gives $`x=x+1`, which holds at no store. Indeed, after `y := x` the two names hold equal values.

Session 12 introduces a proof system whose rules derive triples without mentioning executions, and proves every derived triple valid. Its rule for assignment has no premises and concludes $`\{Q[e/x]\}\,x:=e\,\{Q\}`. Theorem 11.8 below is the assignment case of that proof.

*Theorem 11.8 (Validity of assignment triples).* For every assertion $`Q`, name $`x` and expression $`e`,

$$`\models\{Q[e/x]\}\,x:=e\,\{Q\}.`

If $`Q` is written $`\varphi(a_1,\ldots,a_j)`, then $`\models\{\varphi(a_1[e/x],\ldots,a_j[e/x])\}\,x:=e\,\{\varphi(a_1,\ldots,a_j)\}`.

*Proof.* We must show: for all stores $`s,t`, if $`Q[e/x](s)` and $`s\vdash x:=e\Downarrow t`, then $`Q(t)`.

1. Fix $`s` and $`t`. Assume $`Q[e/x](s)` and a derivation $`D` of $`s\vdash x:=e\Downarrow t`.
2. Suppose $`D` ends with some rule of A.5. Only the assignment rule has an assignment in its conclusion, so $`D` ends with it. [Session 3, Lemma 3.1](chapter-03/index.html#ch03-s2) gives $`t=s[x\mapsto\mathrm{eval}(e,s)]`.
3. By Definition 11.5, the assumption $`Q[e/x](s)` states $`Q(s[x\mapsto\mathrm{eval}(e,s)])`. By step 2 this is $`Q(t)`.

For the second statement, Lemma 11.6 identifies the precondition $`\varphi(a_1[e/x],\ldots,a_j[e/x])` with $`Q[e/x]`. The first statement applies. $`\square`

*Board case.* Prove the second statement with Lemma 11.6 unfolded. We must show: for all stores $`s,t`, if $`\varphi(\mathrm{eval}(a_1[e/x],s),\ldots,\mathrm{eval}(a_j[e/x],s))` and $`s\vdash x:=e\Downarrow t`, then $`\varphi(\mathrm{eval}(a_1,t),\ldots,\mathrm{eval}(a_j,t))`.

1. Fix $`s` and $`t`. Assume the precondition at $`s` and a derivation $`D` of $`s\vdash x:=e\Downarrow t`.
2. Suppose $`D` ends with the assignment rule, the only rule whose conclusion is an assignment. Lemma 3.1 gives $`t=s[x\mapsto\mathrm{eval}(e,s)]`.
3. For each $`i`, apply Lemma 11.3 with $`a=a_i`. It gives $`\mathrm{eval}(a_i[e/x],s)=\mathrm{eval}(a_i,s[x\mapsto\mathrm{eval}(e,s)])`. By step 2 the right side is $`\mathrm{eval}(a_i,t)`.
4. In the assumed precondition, replace each argument $`\mathrm{eval}(a_i[e/x],s)` by $`\mathrm{eval}(a_i,t)`, using step 3. The result is $`\varphi(\mathrm{eval}(a_1,t),\ldots,\mathrm{eval}(a_j,t))`, the postcondition at $`t`. $`\square`

Step 3 is the only step that uses the syntax of expressions. It is applied once to each expression and never to $`\varphi`.

With the postcondition $`x=8`, Lemma 11.6 gives the precondition $`8=8` for `x := 8` and $`7=8` for `x := 7`. The first holds at every store. The second holds at none. The next proposition shows that, for `x := 7` and this postcondition, no precondition that holds at some store gives a valid triple.

*Proposition 11.9 (Preconditions of an assignment).* For all assertions $`P,Q`, every name $`x` and expression $`e`,

$$`\models\{P\}\,x:=e\,\{Q\}\quad\Longleftrightarrow\quad\forall s\in\Sigma,\ P(s)\Rightarrow Q[e/x](s).`

*Proof.* (⇐) Fix $`s,t` with $`P(s)` and $`s\vdash x:=e\Downarrow t`. The assumption gives $`Q[e/x](s)`. Theorem 11.8 applied to $`s`, $`t` and this execution gives $`Q(t)`. (⇒) Fix $`s` with $`P(s)`. The assignment rule of A.5 derives $`s\vdash x:=e\Downarrow s[x\mapsto\mathrm{eval}(e,s)]`. Validity gives $`Q(s[x\mapsto\mathrm{eval}(e,s)])`, which is $`Q[e/x](s)`. $`\square`

The direction (⇒) needs an execution to exist, and every assignment terminates. So $`Q[e/x]` follows from every precondition that makes the triple valid.

# Sequences of assignments
%%%
tag := "ch11-s4"
%%%

Let $`x,y` be distinct. Take the postcondition $`x+y=5` and the command `x := y; y := 1`. Theorem 11.8 for the second assignment gives $`\models\{x+1=5\}\,y:=1\,\{x+y=5\}`, since $`(x+y)[1/y]=x+1`. Theorem 11.8 for the first assignment, with postcondition $`x+1=5`, gives $`\models\{y+1=5\}\,x:=y\,\{x+1=5\}`. The next proposition joins the two triples. Check one store: from $`x=9`, $`y=4` the precondition $`y+1=5` holds, and the program ends with $`x=4`, $`y=1` and $`x+y=5`.

*Proposition 11.10 (Sequence and consequence).* For all assertions and commands,

1. if $`\models\{P\}\,c\,\{Q\}` and $`\models\{Q\}\,d\,\{R\}`, then $`\models\{P\}\,c;d\,\{R\}`;
2. if $`P'(s)\Rightarrow P(s)` for every $`s`, $`\models\{P\}\,c\,\{Q\}`, and $`Q(s)\Rightarrow Q'(s)` for every $`s`, then $`\models\{P'\}\,c\,\{Q'\}`.

*Proof.* (1) Fix $`s,t` with $`P(s)` and $`s\vdash c;d\Downarrow t`. [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3) gives a store $`m` with $`s\vdash c\Downarrow m` and $`m\vdash d\Downarrow t`. The first triple gives $`Q(m)`. The second triple, applied to $`m` and $`t`, gives $`R(t)`. (2) Fix $`s,t` with $`P'(s)` and $`s\vdash c\Downarrow t`. The first implication gives $`P(s)`, the triple gives $`Q(t)`, and the second implication gives $`Q'(t)`. $`\square`

The example processed the later assignment first. Stores are updated in program order. A postcondition is carried back in the opposite order. Doing the two replacements in program order would first replace $`x` by $`y`, giving $`y+y=5`, and then $`y` by 1, giving $`1+1=5`, which holds at no store. That order loses the old value of $`y` read by the first assignment.

For any sequence of assignments, repeated substitution from the end computes a precondition mechanically. What remains is one implication from the given precondition to the computed one. Proposition 11.10(2) turns that implication into a valid triple with the given precondition.

# Exercises
%%%
tag := "ch11-s5"
number := false
%%%

*11.1.* For distinct names $`x,y`, take $`a=x+y` and $`e=y+1`. Compute $`a[e/x]` and $`a[x/y]` in a store with $`s(x)=4` and $`s(y)=2`. For each substitution, give the single store update that yields the same value on the original $`a`.

*11.2.* For distinct names $`x,y`, compute the precondition given by Theorem 11.8 and Proposition 11.10 for `x := y + 2; y := x + 1` and the postcondition $`y=10`. Check it by executing forwards from one store.

*11.3.* A proposed forward rule concludes $`\{Q\}\,x:=e\,\{Q[e/x]\}`. Give an assertion $`Q`, an expression $`e` and a store that show this triple is not valid in general.

*11.4.* Suppose $`x\notin\mathrm{FV}(a_i)` for every $`i`, where $`\mathrm{FV}` is the free-variable set of [Session 1, Definition 1.4](chapter-01/index.html#ch01-s3). Prove $`a_i[e/x]=a_i` and conclude $`\models\{Q\}\,x:=e\,\{Q\}` for $`Q=\varphi(a_1,\ldots,a_j)`. Which result of Session 1 gives the same conclusion without substitution?

*11.5.* Let $`W=\mathsf{while\ true\ do\ skip}`. Explain why every triple $`\{P\}\,W\,\{Q\}` is valid. Then show that $`\{P\}\,(W;c)\,\{Q\}` is valid for every command $`c`.

*11.6.* Define $`b[e/x]` for the guards of A.4 by structural recursion. Prove $`B(b[e/x],s)=B(b,s[x\mapsto\mathrm{eval}(e,s)])`. Which cases use Lemma 11.3?

*Further problem.* For distinct names consider `x := y; y := x` and the postcondition $`x=y\land y\ge4`. Compute its precondition. Compare it with a simultaneous swap $`(x,y):=(y,x)`, in which both right sides read the initial store. Explain where the two backward calculations differ.

# Reading for the Seminar
%%%
tag := "ch11-s6"
number := false
%%%

*Definitions · 10 minutes.* Compute Example 11.2 in both orders: substitute and then evaluate; update and then evaluate. Draw the postcondition $`x=8` as a set of stores and an arrow from $`s` to $`s[x\mapsto s(x)+3]`.

*Joint proof · 30 minutes.* One person proves the variable case of Lemma 11.3, both subcases. Then prove Theorem 11.8 by the four board steps. One person inverts the execution, another applies Lemma 11.3 to each expression, and a third rewrites the precondition. Finish with Proposition 11.9 and ask who supplies the execution in the direction (⇒).

*Proof review · 20 minutes.* Work Exercise 11.2 backwards, then check the result by executing forwards from one store. Use Exercise 11.3 to test the direction of the rule.

*Facilitator’s hint.* Write $`Q` applied to the updated store before doing any textual replacement. Track the initial and the final value of the same name separately.

# Solutions and Further Reading
%%%
tag := "ch11-s7"
number := false
%%%

*11.1.* $`a[e/x]=(y+1)+y` has value $`(2+1)+2=5`. Evaluating $`x+y` in $`s[x\mapsto3]` gives the same value, and $`3=\mathrm{eval}(y+1,s)`. $`a[x/y]=x+x` has value $`4+4=8`. Its update is $`s[y\mapsto4]`, with $`4=\mathrm{eval}(x,s)`. In both cases the stored value is computed in the original store.

*11.2.* Through `y := x + 1` the postcondition $`y=10` becomes $`x+1=10`. Through `x := y + 2` this becomes $`(y+2)+1=10`, that is $`y=7`. From any store with $`y=7` the program writes 9 to $`x` and then 10 to $`y`.

*11.3.* Take $`Q` to be $`x=0` and $`e=x+1`. By Lemma 11.6, $`Q[e/x]` is $`x+1=0`. Start in a store with $`x=0`, so $`Q` holds. The final store has $`x=1`, where $`x+1=0` fails.

*11.4.* By structural induction on $`a`: a literal is unchanged; a variable leaf is a name $`y\neq x`, since $`x\notin\mathrm{FV}(y)=\{y\}`; at a binary node $`x` is in neither child’s set, and the two induction hypotheses give the result. Lemma 11.6 then gives $`Q[e/x]=\varphi(a_1,\ldots,a_j)=Q`, and Theorem 11.8 gives the triple. Without substitution, [Session 1, Corollary 1.2](chapter-01/index.html#ch01-s3) gives $`\mathrm{eval}(a_i,s[x\mapsto n])=\mathrm{eval}(a_i,s)` for every $`n`, so $`Q` holds at $`s` exactly when it holds at the updated store.

*11.5.* No store $`t` satisfies $`s\vdash W\Downarrow t`, so the premise of validity never holds. An execution $`s\vdash(W;c)\Downarrow t` would give, by [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3), a store $`m` with $`s\vdash W\Downarrow m`. There is none, so $`\{P\}\,(W;c)\,\{Q\}` is valid as well. Session 12, Exercise 12.4, derives $`\{P\}\,W\,\{Q\}` in the proof system of that session.

*11.6.* Constants are unchanged. Comparisons substitute into both operands: $`(a_1\le a_2)[e/x]=(a_1[e/x]\le a_2[e/x])`, and likewise for $`=`. Negation and conjunction substitute into their operands. Put $`u=s[x\mapsto\mathrm{eval}(e,s)]`. In the comparison cases, Lemma 11.3 applied to each operand turns $`\mathrm{eval}(a_i[e/x],s)` into $`\mathrm{eval}(a_i,u)`. The cases for negation and conjunction use the induction hypotheses for their operands. This is CS Lemma 12.1 for the guards of A.4.

*Further problem.* Through `y := x` the postcondition becomes $`x=x\land x\ge4`, that is $`x\ge4`. Through `x := y` this becomes $`y\ge4`. The simultaneous swap sends $`s` to a store whose value at $`x` is $`s(y)` and at $`y` is $`s(x)`. Its precondition is $`y=x\land x\ge4`. The two substitutions act on the original occurrences at once. Performing them one after the other on already substituted text would turn the equation into $`x=x`. The store with $`x=1`, $`y=5` separates the two preconditions: the sequence ends with two fives, the swap with five and one.

*Syntactic and semantic assertions.* _Concrete Semantics_ §12.2.1 (pp. 193–199) first presents Hoare logic with assertions as formulas and the rule $`\{P[a/x]\}\ x ::= a\ \{P\}` (Fig. 12.1, p. 195). Section 12.2.2 (pp. 199–200) then treats assertions as predicates on stores and writes the precondition of assignment with the updated store, as in Definition 11.5. Its Lemma 12.1 connects the two presentations for Boolean expressions. Lemma 11.6 plays that role here.

*Weakest preconditions.* _Concrete Semantics_ §12.3.1 (pp. 204–205) defines the weakest precondition of a command and a postcondition: it holds at $`s` when every terminating execution from $`s` ends in a store satisfying the postcondition. Fact 12.3 says a triple is valid exactly when its precondition implies the weakest precondition. For an assignment the weakest precondition is $`Q[e/x]`, which is Proposition 11.9. The same section uses weakest preconditions to prove completeness of Hoare logic.

*Names bound inside assertions.* In Definition 11.4 a quantifier inside $`\varphi` ranges over integers and binds no name, so substitution never meets a binder. Some assertion languages let a formula bind a name that the program also uses. Take the postcondition $`\exists y,\ x<y` and the command `x := y`. Blind replacement gives $`\exists y,\ y<y`, false at every store. Renaming the bound name first gives $`\exists z,\ x<z` and then $`\exists z,\ y<z`, true at every store. Under Definition 11.4 the postcondition is $`\varphi(x)` with $`\varphi(n_1)\coloneqq\exists k\in\mathbb Z,\ n_1<k`, and Lemma 11.6 gives $`\varphi(y)` directly. Session 22 treats substitution that avoids capture.

*Choosing an intermediate assertion.* For distinct $`x,y,z`, require $`z\ge2` after `x := y + 1; z := x + x`. Carrying the postcondition back gives $`x\ge1` before the second assignment and $`y\ge0` before the sequence. From the stronger precondition $`y\ge10`, the intermediate assertion $`x\ge11` also works. From $`y\ge0` it fails at $`y=0`. An intermediate assertion must lie between what the prefix guarantees and what the suffix requires. Substitution computes the latter exactly.

# Sources and Formalization
%%%
tag := "ch11-notes"
number := false
%%%

* *Lemma 11.3.* Formulated in this book. Corresponds to CS Exercise 3.3. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 11.6.* Formulated in this book. Corresponds to CS Lemma 12.1. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 11.8.* Formulated in this book. Corresponds to CS Lemma 12.2, assignment case. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 11.9.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 11.10.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
