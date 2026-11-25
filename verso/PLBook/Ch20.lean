import VersoManual

open Verso.Genre Manual

#doc (Manual) "Correctness of Dead-Assignment Elimination" =>
%%%
tag := "ch20"
file := "chapter-20"
%%%

* *Definitions.* Commands, stores, update and big-step execution ([IMP language card A.2, A.4–A.5](imp-card/index.html#imp-a5)). Free variables $`\mathrm{FV}(e)`, the restriction $`s|_X` and the coincidence lemma ([Session 1, Definition 1.4 and Lemma 1.1](chapter-01/index.html#ch01-s3)). Induction on execution derivations with a quantified induction property ([Session 3, §3.2](chapter-03/index.html#ch03-s2)). Free variables of a guard $`\mathrm{FV}(b)`, the observed set and the liveness transfer $`\mathrm{live}(c,L)` ([Session 19, Definitions 19.1–19.3](chapter-19/index.html#ch19-s1)). The loop-head inclusions ([Session 19, Theorem 19.6](chapter-19/index.html#ch19-s3)).
* *New terms.* Agreement on a set, dead assignment, dead-assignment elimination. [Glossary and label key](glossary/index.html)
* *Theorem 20.2 (Correctness of dead-assignment elimination).* For every command $`c`, finite set of names $`L` and stores $`s,t,u`: if $`s\vdash c\Downarrow t` and $`s|_{\mathrm{live}(c,L)}=u|_{\mathrm{live}(c,L)}`, then some store $`v` satisfies $`u\vdash\mathrm{elim}(c,L)\Downarrow v` and $`t|_L=v|_L`.
* *Source.* Definition 20.1 is the dead-code elimination of Xavier Leroy’s compiler verification course (Lean port), on the IMP of the language card. Lemma 20.1 and Theorem 20.2 are its lemma on guards and its correctness theorem for terminating runs. The Lean proof assumes one fact about finite sets as an axiom, stated in §20.2. Nipkow and Klein prove the same statement for their optimizer in _Concrete Semantics_, §10.3.3, and note in §10.4.1 that the statement and its proof carry over to the liveness used here. [Formalization](imp-card/index.html#imp-sources) · [Concrete Semantics, §10.3.3, p. 170](https://concrete-semantics.org/concrete-semantics.pdf#page=180)
* *Board case.* Assignment $`x:=e`, in both subcases: $`x\in L`, where the assignment is kept, and $`x\notin L`, where it is replaced by skip.
* *Proof outline.* Induct on $`D:s\vdash c\Downarrow t` with $`P(D)\coloneqq\forall L,\ \forall u,\ s|_{\mathrm{live}(c,L)}=u|_{\mathrm{live}(c,L)}\Rightarrow\exists v,\ (u\vdash\mathrm{elim}(c,L)\Downarrow v)\land t|_L=v|_L`. Keep $`L` and $`u` inside $`P(D)`: the sequence case applies the first hypothesis at the set $`\mathrm{live}(c_2,L)`, and the loop iteration case applies the body hypothesis at the loop-head set. Lemma 20.1 compares guards. The loop cases use only the three inclusions of Theorem 19.6.
* *From Session 19.* Session 19 computed the names live before a command and proved three inclusions for the loop-head set. Here those sets become the hypothesis of a theorem that relates a run of the original command to a run of the transformed command.

Run `y := x + 1; z := y + 2; x := w` and afterwards read only $`z`. The last assignment cannot change $`z`, so a compiler may replace it by skip. The two programs then end in different stores. After the original, $`x` holds the initial value of $`w`. After the transformed program, $`x` keeps its initial value. A correctness theorem must say which names are compared at the end. Its proof must also say on which names the two runs agree at the start, and that set changes from one program point to the next.

# Observations and the transformation
%%%
tag := "ch20-s1"
%%%

Let $`x,y,z,w` be distinct names and let

$$`c_0=y:=x+1;\ (z:=y+2;\ x:=w).`

The observed set $`L` is the finite set of names whose final values we compare. Take $`L=\{z\}`. [Session 19, Definition 19.2](chapter-19/index.html#ch19-s1) defines the liveness transfer $`\mathrm{live}(c,L)`, the set of names live before $`c` when the names in $`L` are observed after $`c`. We recall its clauses for every command form except the loop. Here $`\mathrm{FV}(b)` is the set of names that occur in the guard $`b` (Definition 19.1).

$$`\begin{aligned}
\mathrm{live}(\mathsf{skip},L)&=L\\
\mathrm{live}(x:=e,L)&=(L\smallsetminus\{x\})\cup\mathrm{FV}(e)\quad\text{if}\ x\in L\\
\mathrm{live}(x:=e,L)&=L\quad\text{if}\ x\notin L\\
\mathrm{live}(c_1;c_2,L)&=\mathrm{live}(c_1,\mathrm{live}(c_2,L))\\
\mathrm{live}(\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2,L)&=\mathrm{FV}(b)\cup\mathrm{live}(c_1,L)\cup\mathrm{live}(c_2,L)
\end{aligned}`

For $`W=\mathsf{while}\ b\ \mathsf{do}\ c`, Definition 19.3 computes the loop-head set $`H=\mathrm{live}(W,L)` by bounded iteration, and [Session 19, Theorem 19.6](chapter-19/index.html#ch19-s3) proves three inclusions:

$$`\text{(1)}\ \ \mathrm{FV}(b)\subseteq H,\qquad\text{(2)}\ \ L\subseteq H,\qquad\text{(3)}\ \ \mathrm{live}(c,H)\subseteq H.`

The proof in §20.2 uses only these inclusions. It never uses the iteration that produced $`H`.

Compute $`\mathrm{live}(c_0,\{z\})` from the end. In $`x:=w` we have $`x\notin\{z\}`, so the set before it is $`\{z\}`. In $`z:=y+2` we have $`z\in\{z\}`, so the set before it is $`(\{z\}\smallsetminus\{z\})\cup\{y\}=\{y\}`. In $`y:=x+1` we have $`y\in\{y\}`, so $`\mathrm{live}(c_0,\{z\})=\{x\}`. Read from right to left as in Session 19:

$$`\{x\}\xleftarrow{\ y:=x+1\ }\{y\}\xleftarrow{\ z:=y+2\ }\{z\}\xleftarrow{\ x:=w\ }\{z\}.`

*Definition 20.1 (Dead-assignment elimination).* For a command $`c` and a finite set of names $`L`, the command $`\mathrm{elim}(c,L)` is defined by structural recursion on $`c`:

$$`\begin{aligned}
\mathrm{elim}(\mathsf{skip},L)&=\mathsf{skip}\\
\mathrm{elim}(x:=e,L)&=(x:=e)\quad\text{if}\ x\in L\\
\mathrm{elim}(x:=e,L)&=\mathsf{skip}\quad\text{if}\ x\notin L\\
\mathrm{elim}(c_1;c_2,L)&=\mathrm{elim}(c_1,\mathrm{live}(c_2,L));\ \mathrm{elim}(c_2,L)\\
\mathrm{elim}(\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2,L)&=\mathsf{if}\ b\ \mathsf{then}\ \mathrm{elim}(c_1,L)\ \mathsf{else}\ \mathrm{elim}(c_2,L)\\
\mathrm{elim}(\mathsf{while}\ b\ \mathsf{do}\ c,L)&=\mathsf{while}\ b\ \mathsf{do}\ \mathrm{elim}(c,\mathrm{live}(\mathsf{while}\ b\ \mathsf{do}\ c,L)).
\end{aligned}`

The assignment in $`\mathrm{elim}(x:=e,L)` is *dead* if $`x\notin L`. In a sequence, the first command is transformed with the set live before the second. A loop body is transformed with the loop-head set, because after the body the execution returns to the loop head. Guards are never changed. For the example, $`\mathrm{elim}(c_0,\{z\})=y:=x+1;\ (z:=y+2;\ \mathsf{skip})`.

Stores $`s` and $`u` *agree on* a set $`X` of names if $`s(y)=u(y)` for every $`y\in X`. [Session 1, §1.3](chapter-01/index.html#ch01-s3) writes this $`s|_X=u|_X`. Agreement passes to subsets: if $`X\subseteq Y` and $`s|_Y=u|_Y`, then $`s|_X=u|_X`.

Run $`c_0` from a store $`s` with $`s(x)=4`, $`s(w)=9` and $`0` at every other name. Run $`\mathrm{elim}(c_0,\{z\})` from a store $`u` with $`u(x)=4`, $`u(y)=100`, $`u(z)=-3`, $`u(w)=20` and $`0` at every other name. The two stores agree on $`\{x\}`. After the first assignment both hold $`5` at $`y`, so they agree on $`\{y\}`. After the second both hold $`7` at $`z`. The original then writes $`9` to $`x`, and the transformed command skips. The final stores agree on $`\{z\}`. They differ at $`x` and at $`w`. At each program point the stores agree on the set computed for that point.

# Two executions, one induction
%%%
tag := "ch20-s2"
%%%

The guard $`x\le y\land\neg(z=0)` has $`\mathrm{FV}=\{x,y,z\}`. Two stores that agree on $`x`, $`y` and $`z` give it the same value, whatever they hold at $`w`.

*Lemma 20.1 (Guard coincidence).* For every guard $`b`, every finite set of names $`X` with $`\mathrm{FV}(b)\subseteq X`, and all stores $`s,u`: if $`s|_X=u|_X`, then $`B(b,s)=B(b,u)`.

*Proof.* Agreement passes to the subset $`\mathrm{FV}(b)`. So it suffices to prove $`Q(b)` for every guard $`b` by structural induction on $`b`, where

$$`Q(b)\coloneqq\forall s,u,\quad s|_{\mathrm{FV}(b)}=u|_{\mathrm{FV}(b)}\Rightarrow B(b,s)=B(b,u).`

The constants $`\mathsf{true}` and $`\mathsf{false}` read no store. For $`e_1=e_2` and $`e_1\le e_2`, each $`\mathrm{FV}(e_i)` is a subset of $`\mathrm{FV}(b)`, so Lemma 1.1 gives $`\mathrm{eval}(e_i,s)=\mathrm{eval}(e_i,u)` for $`i=1,2`, and the comparison receives equal operands. For $`\neg b_1`, the set $`\mathrm{FV}(\neg b_1)` equals $`\mathrm{FV}(b_1)`, and $`Q(b_1)` gives equal values before the negation. For $`b_1\land b_2`, each $`\mathrm{FV}(b_i)` is a subset of $`\mathrm{FV}(b)`, and $`Q(b_1)`, $`Q(b_2)` give equal values of both operands. $`\square`

*Theorem 20.2 (Correctness of dead-assignment elimination).* For every command $`c`, finite set of names $`L` and stores $`s,t,u`: if $`s\vdash c\Downarrow t` and $`s|_{\mathrm{live}(c,L)}=u|_{\mathrm{live}(c,L)}`, then some store $`v` satisfies $`u\vdash\mathrm{elim}(c,L)\Downarrow v` and $`t|_L=v|_L`.

Taking $`u=s` gives the familiar form: from the same initial store, the transformed command terminates, and its final store agrees with the original one on $`L`. The theorem allows two initial stores because the proof needs them. In §20.1 the stores after the first assignment differ at $`z` and at $`w`. The sequence case applies an induction hypothesis to such a pair, using only their agreement on $`\{y\}`.

*What the external check assumes.* The Lean development represents a finite set of names by a hash set. It states one fact about these sets as an axiom, without proof: a name belongs to the union of two sets if and only if it belongs to one of them. For the mathematical sets of this book this is the definition of union, and the paper proof below does not need it. The external checks of this session hold relative to this one axiom.

*Proof.* We prove $`P(D)` for every derivation $`D:s\vdash c\Downarrow t` by induction on $`D` ([Session 3, §3.1](chapter-03/index.html#ch03-s1)). Here $`L` and $`X` range over finite sets of names, and $`s,c,t` are read from the conclusion of $`D`. If $`L` is finite, so is $`\mathrm{live}(c,L)`, since it is a subset of $`\mathrm{RV}(c)\cup L` ([Session 19, Lemma 19.5](chapter-19/index.html#ch19-s3)). So the hypotheses and Lemma 20.1 may be applied at the sets $`\mathrm{live}(c_2,L)`, $`\mathrm{live}(c,L)` and $`H` used below.

$$`P(D)\coloneqq\forall L,\ \forall u,\quad s|_{\mathrm{live}(c,L)}=u|_{\mathrm{live}(c,L)}\ \Rightarrow\ \exists v,\ \bigl(u\vdash\mathrm{elim}(c,L)\Downarrow v\bigr)\land t|_L=v|_L.`

*Assignment (board case).* Suppose $`D` ends with the assignment rule. Then $`c=(x:=e)` and $`t=s[x\mapsto\mathrm{eval}(e,s)]`. The rule has no execution premises, so there is no induction hypothesis. Fix $`L` and $`u`, and assume

$$`(\mathrm{A})\qquad s|_{\mathrm{live}(x:=e,L)}=u|_{\mathrm{live}(x:=e,L)}.`

We must show that some $`v` satisfies $`u\vdash\mathrm{elim}(x:=e,L)\Downarrow v` and $`t|_L=v|_L`. Split on whether $`x\in L`.

*Kept subcase.* Suppose $`x\in L`. Then $`\mathrm{elim}(x:=e,L)=(x:=e)` and $`\mathrm{live}(x:=e,L)=(L\smallsetminus\{x\})\cup\mathrm{FV}(e)`.

1. Agreement (A) passes to both parts of the union: $`s|_{\mathrm{FV}(e)}=u|_{\mathrm{FV}(e)}` and $`s|_{L\smallsetminus\{x\}}=u|_{L\smallsetminus\{x\}}`.
2. Apply Lemma 1.1 to the first agreement. This gives $`\mathrm{eval}(e,s)=\mathrm{eval}(e,u)`.
3. Let $`v=u[x\mapsto\mathrm{eval}(e,u)]`. The assignment rule gives $`u\vdash x:=e\Downarrow v`.
4. Fix $`y\in L`. We must show $`t(y)=v(y)`. If $`y=x`, then A.2 and step 2 give $`t(x)=\mathrm{eval}(e,s)=\mathrm{eval}(e,u)=v(x)`. If $`y\neq x`, then $`y\in L\smallsetminus\{x\}`, and A.2 with the second agreement of step 1 gives $`t(y)=s(y)=u(y)=v(y)`.
5. Hence $`t|_L=v|_L`.

*Dead subcase.* Suppose $`x\notin L`. Then $`\mathrm{elim}(x:=e,L)=\mathsf{skip}` and $`\mathrm{live}(x:=e,L)=L`.

1. Agreement (A) reads $`s|_L=u|_L`.
2. Let $`v=u`. The skip rule gives $`u\vdash\mathsf{skip}\Downarrow u`.
3. Fix $`y\in L`. We must show $`t(y)=u(y)`. Since $`y\in L` and $`x\notin L`, we have $`y\neq x`.
4. By A.2 and $`y\neq x`, $`t(y)=s[x\mapsto\mathrm{eval}(e,s)](y)=s(y)`. By step 1, $`s(y)=u(y)`.
5. Hence $`t|_L=v|_L`.

Neither subcase compares the initial values of $`x`. In the kept subcase, $`x` belongs to the set in (A) only if $`x\in\mathrm{FV}(e)`, as in $`x:=x+1`. In the dead subcase, $`e` is never evaluated on the transformed side, so $`\mathrm{FV}(e)` is not needed. Apart from the equations for $`\mathrm{elim}` and $`\mathrm{live}`, step 3 of the dead subcase is the only place where $`x\notin L` is used.

*Skip.* Then $`t=s`, $`\mathrm{elim}(\mathsf{skip},L)=\mathsf{skip}` and $`\mathrm{live}(\mathsf{skip},L)=L`. Take $`v=u`. The hypothesis is $`s|_L=u|_L`, which is $`t|_L=v|_L`.

*Sequence.* Suppose $`D` ends with the sequence rule. Then $`c=c_1;c_2` and the premises are $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash c_2\Downarrow t`. We write $`X,u',v'` for the bound variables of the hypotheses to keep them apart from $`L,u,v`.

$$`\begin{aligned}
P(D_1)&:\ \forall X,\ \forall u',\ s|_{\mathrm{live}(c_1,X)}=u'|_{\mathrm{live}(c_1,X)}\Rightarrow\exists v',\ \bigl(u'\vdash\mathrm{elim}(c_1,X)\Downarrow v'\bigr)\land m|_X=v'|_X,\\
P(D_2)&:\ \forall X,\ \forall u',\ m|_{\mathrm{live}(c_2,X)}=u'|_{\mathrm{live}(c_2,X)}\Rightarrow\exists v',\ \bigl(u'\vdash\mathrm{elim}(c_2,X)\Downarrow v'\bigr)\land t|_X=v'|_X.
\end{aligned}`

Fix $`L` and $`u`, and let $`M=\mathrm{live}(c_2,L)`. Then $`\mathrm{live}(c,L)=\mathrm{live}(c_1,M)` and $`\mathrm{elim}(c,L)=\mathrm{elim}(c_1,M);\mathrm{elim}(c_2,L)`. Assume $`s|_{\mathrm{live}(c_1,M)}=u|_{\mathrm{live}(c_1,M)}`. Apply $`P(D_1)` at $`X=M`, $`u'=u`. This gives a store $`n` with $`u\vdash\mathrm{elim}(c_1,M)\Downarrow n` and $`m|_M=n|_M`. Since $`M=\mathrm{live}(c_2,L)`, apply $`P(D_2)` at $`X=L`, $`u'=n`. This gives $`v` with $`n\vdash\mathrm{elim}(c_2,L)\Downarrow v` and $`t|_L=v|_L`. The sequence rule gives $`u\vdash\mathrm{elim}(c,L)\Downarrow v`. The first hypothesis was used at $`M`, not at $`L`. This is why $`L` is quantified inside $`P(D)`.

*Conditional.* Suppose $`c=\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2`, let $`k` be the branch selected by $`B(b,s)`, and let $`D_1:s\vdash k\Downarrow t` be the premise, with

$$`P(D_1):\ \forall X,\ \forall u',\ s|_{\mathrm{live}(k,X)}=u'|_{\mathrm{live}(k,X)}\Rightarrow\exists v',\ \bigl(u'\vdash\mathrm{elim}(k,X)\Downarrow v'\bigr)\land t|_X=v'|_X.`

Fix $`L` and $`u`, and assume that $`s` and $`u` agree on $`\mathrm{live}(c,L)=\mathrm{FV}(b)\cup\mathrm{live}(c_1,L)\cup\mathrm{live}(c_2,L)`. Lemma 20.1 gives $`B(b,u)=B(b,s)`, so the transformed conditional selects $`\mathrm{elim}(k,L)` at $`u`. Agreement passes to $`\mathrm{live}(k,L)`. Apply $`P(D_1)` at $`X=L`, $`u'=u` to get $`v` with $`u\vdash\mathrm{elim}(k,L)\Downarrow v` and $`t|_L=v|_L`. The conditional rule finishes the case.

*Loop exit.* Suppose $`D` ends with the loop exit rule. Then $`c=W=\mathsf{while}\ b\ \mathsf{do}\ c_1` (we write $`c_1` for the body because $`c` names the whole command), $`B(b,s)=\mathsf{false}` and $`t=s`. Fix $`L` and $`u`, let $`H=\mathrm{live}(W,L)`, and assume $`s|_H=u|_H`. Then $`\mathrm{elim}(W,L)=\mathsf{while}\ b\ \mathsf{do}\ \mathrm{elim}(c_1,H)`. By inclusion (1), $`\mathrm{FV}(b)\subseteq H`, so Lemma 20.1 gives $`B(b,u)=\mathsf{false}`. The loop exit rule gives $`u\vdash\mathrm{elim}(W,L)\Downarrow u`. Take $`v=u`. By inclusion (2), $`L\subseteq H`, so $`t|_L=s|_L=u|_L`.

*Loop iteration.* Suppose $`D` ends with the loop iteration rule. Then $`c=W` as above, $`B(b,s)=\mathsf{true}`, and the premises are $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash W\Downarrow t`. The hypotheses are

$$`\begin{aligned}
P(D_1)&:\ \forall X,\ \forall u',\ s|_{\mathrm{live}(c_1,X)}=u'|_{\mathrm{live}(c_1,X)}\Rightarrow\exists v',\ \bigl(u'\vdash\mathrm{elim}(c_1,X)\Downarrow v'\bigr)\land m|_X=v'|_X,\\
P(D_2)&:\ \forall X,\ \forall u',\ m|_{\mathrm{live}(W,X)}=u'|_{\mathrm{live}(W,X)}\Rightarrow\exists v',\ \bigl(u'\vdash\mathrm{elim}(W,X)\Downarrow v'\bigr)\land t|_X=v'|_X.
\end{aligned}`

Fix $`L` and $`u`, let $`H=\mathrm{live}(W,L)`, and assume $`s|_H=u|_H`. We must show that some $`v` satisfies $`u\vdash\mathrm{elim}(W,L)\Downarrow v` and $`t|_L=v|_L`.

1. By inclusion (1), $`\mathrm{FV}(b)\subseteq H`, so Lemma 20.1 gives $`B(b,u)=\mathsf{true}`.
2. By inclusion (3), $`\mathrm{live}(c_1,H)\subseteq H`, so agreement passes to $`\mathrm{live}(c_1,H)`. Apply $`P(D_1)` at $`X=H`, $`u'=u`. This gives $`n` with $`u\vdash\mathrm{elim}(c_1,H)\Downarrow n` and $`m|_H=n|_H`.
3. Since $`H=\mathrm{live}(W,L)`, apply $`P(D_2)` at $`X=L`, $`u'=n`. This gives $`v` with $`n\vdash\mathrm{elim}(W,L)\Downarrow v` and $`t|_L=v|_L`.
4. The loop iteration rule for $`\mathsf{while}\ b\ \mathsf{do}\ \mathrm{elim}(c_1,H)`, with steps 1–3, gives $`u\vdash\mathrm{elim}(W,L)\Downarrow v`.

The hypothesis $`P(D_2)` concerns the same loop $`W`. Induction on command syntax would not supply it.

This proves $`P(D)` for every derivation $`D`. Given the premises of Theorem 20.2, apply $`P(D)` to $`L` and $`u`. $`\square`

# What the theorem does not say
%%%
tag := "ch20-s3"
%%%

Theorem 20.2 starts from a terminating run of the original command. If $`c` has no terminating run from $`s`, the theorem says nothing about $`\mathrm{elim}(c,L)` from $`u`. It also goes in one direction only, from a run of $`c` to a run of $`\mathrm{elim}(c,L)`. Nipkow and Klein prove the converse direction for their optimizer as Lemma 10.20. [Session 21](chapter-21/index.html) collects the premises and observations of this theorem and of the earlier correctness theorems.

The final stores agree on $`L`, and in general nowhere else. In §20.1 they differ at $`x` and at $`w`. [Session 7, Definition 7.1](chapter-07/index.html#ch07-s1) calls two commands equivalent only when their final stores are equal. Theorem 20.2 compares the names in $`L` only.

Expressions and guards always terminate and change no store. So deleting a dead assignment can change only the final value of a name outside $`L`. If evaluating an expression could also print or fail, the deletion could remove that effect (Exercise 20.4).

# Exercises
%%%
tag := "ch20-s4"
number := false
%%%

*20.1.* Observe $`L=\{x,z\}` after $`c_0`. Compute the set at each program point from the end. Which assignments does $`\mathrm{elim}(c_0,L)` keep? On which names must the initial stores agree?

*20.2.* Exchange the first two assignments: $`z:=y+2;\ (y:=x+1;\ x:=w)`, with $`L=\{z\}`. Compute the sets and the transformed command. Which initial value determines the final value of $`z`?

*20.3.* A proposed analysis returns $`H'=\mathrm{FV}(b)\cup L` for every loop. It satisfies inclusions (1) and (2) of Theorem 19.6. Take $`L=\{z\}` and $`W=\mathsf{while}\ g\le 0\ \mathsf{do}\ (z:=y;\ g:=g+1)`, with $`g,y,z` distinct, and transform the body with $`H'`. Find stores $`s,u` that agree on $`H'` for which the conclusion of Theorem 20.2 fails. Which step of the loop iteration case breaks?

*20.4.* Suppose evaluating an expression could also print a value. Give a dead assignment whose deletion changes what is printed. What must a correctness theorem for that language compare besides the names in $`L`?

*Further problem.* Let $`c` contain no loop. Prove $`\mathrm{live}(\mathrm{elim}(c,L),L)=\mathrm{live}(c,L)` and $`\mathrm{elim}(\mathrm{elim}(c,L),L)=\mathrm{elim}(c,L)` for every $`L`. Explain why the first claim is needed in the sequence case of the second.

# Reading for the Seminar
%%%
tag := "ch20-s5"
number := false
%%%

*Definitions · 10 minutes.* Compute the sets of $`c_0` from the end towards the start. Mark the dead assignment and write $`\mathrm{elim}(c_0,\{z\})`.

*Joint proof · 30 minutes.* Prove the assignment case, both subcases, with two different initial stores $`s` and $`u`. Then do the sequence case and point to the hypothesis that is applied at a set other than $`L`.

*Proof review · 20 minutes.* Rerun the example of §20.1 with other values of $`u` at $`y`, $`z` and $`w`. In the loop iteration case, name the inclusion of Theorem 19.6 used by each step. Exercise 20.3 shows what happens without inclusion (3).

*Facilitator’s hint.* In the dead subcase, fix an observed name $`y`. The fact $`y\neq x` is exactly what lets the two final lookups be compared.

# Solutions and Further Reading
%%%
tag := "ch20-s6"
number := false
%%%

*20.1.* Before $`x:=w`: $`x\in L`, so the set is $`\{z\}\cup\{w\}=\{z,w\}`. Before $`z:=y+2`: $`\{w\}\cup\{y\}=\{y,w\}`. Before $`y:=x+1`: $`\{w\}\cup\{x\}=\{x,w\}`. All three assignments are kept, so $`\mathrm{elim}(c_0,L)=c_0`. The initial stores must agree on $`x` and $`w`.

*20.2.* Before $`x:=w` the set is $`\{z\}`, since $`x\notin\{z\}`. Before $`y:=x+1` it is again $`\{z\}`, since $`y\notin\{z\}`. Before $`z:=y+2` it is $`\{y\}`. The transformed command is $`z:=y+2;\ (\mathsf{skip};\ \mathsf{skip})`. The final $`z` is the initial $`y` plus 2. The initial $`x` does not matter.

*20.3.* Here $`H'=\{g,z\}`. The body has $`\mathrm{live}(g:=g+1,H')=\{g,z\}` and $`\mathrm{live}(z:=y,\{g,z\})=\{g,y\}`. Both assignments are kept, so the transformed loop is $`W` itself. Let $`s` and $`u` hold $`0` at $`g` and at $`z`, with $`s(y)=1` and $`u(y)=2`. They agree on $`H'`. Each run performs one iteration and stops with $`g=1`. The final values of $`z` are $`1` and $`2`. By Session 3, Theorem 3.2, the run from $`u` is unique, so no store $`v` satisfies the conclusion. Step 2 of the loop iteration case breaks: it needs agreement on $`\mathrm{live}(c_1,H')=\{g,y\}`, and agreement on $`H'` says nothing about $`y`. Inclusion (3) of Theorem 19.6 is what step 2 uses.

*20.4.* Take $`L=\varnothing` and an assignment $`x:=e`, where evaluating $`e` prints a value. Then $`\mathrm{elim}(x:=e,\varnothing)=\mathsf{skip}`. The original prints and the transformed command does not, yet the final stores agree on $`\varnothing`. A correctness theorem must also compare the printed output. If expressions could fail, Theorem 20.2 would still speak only of runs in which the original terminates. The transformed command could then succeed from a store where the original fails.

*Further problem.* Use structural induction on $`c`, with both claims quantified over all $`L`. Skip is fixed by both functions. A dead assignment becomes skip, and $`\mathrm{live}(\mathsf{skip},L)=L=\mathrm{live}(x:=e,L)`. A kept assignment is unchanged. For a conditional, the guard is kept, and the two branch hypotheses give equal sets and fixed branches. For $`c_1;c_2`, write $`M=\mathrm{live}(c_2,L)`. On the second pass the first command is transformed with $`\mathrm{live}(\mathrm{elim}(c_2,L),L)`, which equals $`M` by the first claim for $`c_2`. Then the hypotheses for $`c_1` at $`M` and for $`c_2` at $`L` give both claims. For loops the computed loop-head set needs a separate argument. _Concrete Semantics_, Exercise 10.13, treats loops for a liveness defined by a least fixed point.

*Further reading.* Nipkow and Klein, _Concrete Semantics_, §§10.3–10.4, pp. 164–177. Theorem 10.18 (p. 168) is Theorem 20.2 for the identity transformation: it proves the liveness analysis itself correct. Lemma 10.20 (p. 170) is the converse direction. Corollary 10.21 (p. 171) observes every name and combines both directions into equivalence in the sense of Session 7. With a finite $`L`, Theorem 20.2 gives one of the two inclusions of that equivalence when $`u=s` and $`L` contains every name assigned in $`c`. The proof also needs the fact that a command does not change a name it never assigns. [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf#page=174)

Xavier Leroy’s _Compiler Verification_ course, Lean 4 port by Wojciech Różowski, part 10, liveness analysis and dead code elimination. Compare its proof of the loop iteration case with the four steps above. [Lean course](https://github.com/leanprover/LeroyCompilerVerificationCourse/tree/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01)

# Sources and Formalization
%%%
tag := "ch20-notes"
number := false
%%%

* *Lemma 20.1.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 20.2.* Corresponds to CS Lemma 10.19. Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
