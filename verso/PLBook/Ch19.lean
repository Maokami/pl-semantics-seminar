import VersoManual

open Verso.Genre Manual

#doc (Manual) "Liveness and Loop Fixed Points" =>
%%%
tag := "ch19"
file := "chapter-19"
%%%

* *Definitions.* Expressions, guards, commands and big-step execution ([IMP language card A.1–A.5](imp-card/index.html)). Free variables $`\mathrm{FV}(e)`, the restriction $`s|_S` and Lemma 1.1 ([Session 1, §1.3](chapter-01/index.html#ch01-s3)). The unfolding $`U` of a loop ([Session 7, Theorem 7.3](chapter-07/index.html#ch07-s2)). Fixed points ([Session 9, §9.3](chapter-09/index.html#ch09-s3)).
* *New terms.* Live variable, liveness transfer, loop head, post-fixed point, bounded iteration with its fuel and fallback set. [Glossary and label key](glossary/index.html)
* *Theorem 19.6 (Loop-head inclusions).* For every guard $`b`, command $`c` and set of names $`L`, let $`W=\mathsf{while}\ b\ \mathsf{do}\ c` and $`H=\mathrm{live}(W,L)`. Then (1) $`\mathrm{FV}(b)\subseteq H`, (2) $`L\subseteq H` and (3) $`\mathrm{live}(c,H)\subseteq H`.
* *Source.* Xavier Leroy’s _Compiler Verification_ course, liveness analysis (§10.1 of the Lean port). Definitions 19.1–19.3 are its definitions, and Lemmas 19.4–19.5 and Theorem 19.6 are its results. The course’s Lean development takes one property of its finite sets as an axiom: a name is in a union exactly when it is in one of the two sets. Nipkow and Klein define the loop clause as a least fixed point and note that it satisfies the same three inclusions, their constraints (10.1). [Source and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics, §10.4, p. 172](https://concrete-semantics.org/concrete-semantics.pdf#page=182)
* *Board case.* Inclusion (3), $`\mathrm{live}(c,H)\subseteq H`. Lemma 19.4(a) gives two alternatives: the iteration stopped at a post-fixed point of $`F`, or it returned the fallback set $`D`. Prove the inclusion in each.
* *Proof outline.* Lemma 19.4(a), by induction on the fuel, says that the bounded iteration returns a post-fixed point of $`F` or the fallback set $`D`. At a post-fixed point, $`F(H)\subseteq H` contains all three inclusions, because $`F(H)` is the union of their left-hand sides. At the fallback, $`H=\mathrm{FV}(b)\cup\mathrm{RV}(c)\cup L` contains the first two left-hand sides by definition, and Lemma 19.5, $`\mathrm{live}(c,X)\subseteq\mathrm{RV}(c)\cup X` for every set $`X`, gives the third. Lemma 19.5 is proved by structural induction on the command, with the observed set quantified inside the induction property. Its loop case uses Lemma 19.4(b).
* *From Session 18.* Sessions 17 and 18 analysed a command forwards: an abstract store before the command gave an abstract store after it. Liveness runs backwards: the names observed after a command give the names needed before it. A loop again needs a set that one more turn of the loop does not enlarge, and a bounded iteration again searches for it. When the fuel runs out, the fallback is now a finite set read off the loop’s syntax.

Consider the loop $`W=\mathsf{while}\ 0<g\ \mathsf{do}\ (z:=y;\ y:=x;\ g:=g-1)` with distinct names $`g,x,y,z`, and suppose that only $`z` is read after it. Which initial values can change the final $`z`? Start with $`g=2`, $`y=8` and $`x=5`. The first iteration sets $`z` to 8, $`y` to 5 and $`g` to 1. The second sets $`z` to 5 and $`g` to 0, and the loop exits with $`z=5`. Change only the initial $`x` to 6, and the loop exits with $`z=6`. No assignment copies $`x` into $`z`, yet the initial $`x` matters: it reaches $`z` through $`y`, one iteration later. An analysis that reads the program backwards from $`z` must go around the loop twice to find $`x`.

# Names needed before a command
%%%
tag := "ch19-s1"
%%%

Take distinct names $`x,y,z` and the assignment $`x:=y+1`. Suppose that $`x` and $`z` are read after it. To reproduce the final $`x` we need the old $`y`. To reproduce the final $`z` we need the old $`z`, which the assignment leaves alone. The old $`x` is not needed: the assignment overwrites it before anything reads it. So before the assignment we need $`\{y,z\}`. Now suppose that only $`z` is read. Deleting the assignment does not change $`z`, and then $`y` is never read. So before it we need only $`\{z\}`. Evaluating $`y+1` has no other effect and always terminates (A.3), so skipping it loses nothing.

*Definition 19.1 (Names of guards and read names of commands).* Extend $`\mathrm{FV}` of Session 1, Definition 1.4, to guards (A.4):

$$`\begin{aligned}
\mathrm{FV}(\mathsf{true})&=\mathrm{FV}(\mathsf{false})=\varnothing & \mathrm{FV}(e_1=e_2)&=\mathrm{FV}(e_1\le e_2)=\mathrm{FV}(e_1)\cup\mathrm{FV}(e_2)\\
\mathrm{FV}(\neg b)&=\mathrm{FV}(b) & \mathrm{FV}(b_1\land b_2)&=\mathrm{FV}(b_1)\cup\mathrm{FV}(b_2).
\end{aligned}`

The *read names* $`\mathrm{RV}(c)` of a command are the names in its expressions and guards:

$$`\begin{aligned}
\mathrm{RV}(\mathsf{skip})&=\varnothing & \mathrm{RV}(x:=e)&=\mathrm{FV}(e) & \mathrm{RV}(c_1;c_2)&=\mathrm{RV}(c_1)\cup\mathrm{RV}(c_2)\\
\mathrm{RV}(\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2)&=\mathrm{FV}(b)\cup\mathrm{RV}(c_1)\cup\mathrm{RV}(c_2) & \mathrm{RV}(\mathsf{while}\ b\ \mathsf{do}\ c)&=\mathrm{FV}(b)\cup\mathrm{RV}(c).
\end{aligned}`

An assignment target is not a read name: $`\mathrm{RV}(x:=1)=\varnothing`. For the body $`c=(z:=y;\ y:=x;\ g:=g-1)` of the opening loop, $`\mathrm{RV}(c)=\{y\}\cup\{x\}\cup\{g\}=\{g,x,y\}`.

Fix a command $`c` and a set $`L` of names read after $`c`, the *observed set*. The liveness transfer computes a set $`\mathrm{live}(c,L)`. It is meant to contain every name whose value before $`c` can influence the value of a name of $`L` after $`c`. A name in $`\mathrm{live}(c,L)` is *live* before $`c`. The other names are *dead* there. Session 20 proves the guarantee that the removal of dead assignments needs.

*Definition 19.2 (Liveness transfer, loop-free clauses).* For every set $`L` of names,

$$`\begin{aligned}
\mathrm{live}(\mathsf{skip},L)&=L\\
\mathrm{live}(x:=e,L)&=(L\smallsetminus\{x\})\cup\mathrm{FV}(e)\ \text{ if } x\in L,\qquad \mathrm{live}(x:=e,L)=L\ \text{ if } x\notin L\\
\mathrm{live}(c_1;c_2,L)&=\mathrm{live}(c_1,\mathrm{live}(c_2,L))\\
\mathrm{live}(\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2,L)&=\mathrm{FV}(b)\cup\mathrm{live}(c_1,L)\cup\mathrm{live}(c_2,L).
\end{aligned}`

The clause for loops is Definition 19.3. The function is defined by structural recursion on the command. Its second argument changes in the recursive calls: in the sequence clause $`c_1` is analysed with $`\mathrm{live}(c_2,L)` in place of $`L`. Execution runs $`c_1` first, but the analysis starts at the end. The transfer of $`c_2` says which names must be right just before $`c_2`. That point is just after $`c_1`, so this set is the observed set for $`c_1`. At a conditional the analysis does not evaluate the guard. Either branch may run, so it takes the union of both transfers and adds the guard’s names, which decide the branch.

For the same body $`c` and the observed set $`\{g,y,z\}`, read the following line from right to left:

$$`\{g,x,y\}\xleftarrow{\ z:=y\ }\{g,x,z\}\xleftarrow{\ y:=x\ }\{g,y,z\}\xleftarrow{\ g:=g-1\ }\{g,y,z\}.`

The last assignment writes the observed $`g` and reads $`g`, so the set is unchanged. The middle one replaces the observed $`y` by $`x`, and the first replaces $`z` by $`y`. So $`\mathrm{live}(c,\{g,y,z\})=\{g,x,y\}`. Both ways of grouping the three assignments give this set, because the sequence clause composes the transfers.

# The loop head
%%%
tag := "ch19-s2"
%%%

The *loop head* is the point just before each test of the guard. The store there is the loop’s initial store at the first test and the body’s final store at each later test. So one set must serve both. Let $`W=\mathsf{while}\ b\ \mathsf{do}\ c` and $`U=\mathsf{if}\ b\ \mathsf{then}\ (c;W)\ \mathsf{else}\ \mathsf{skip}`. By Session 7, Theorem 7.3, $`W` and $`U` have the same executions. Let $`H`, the loop-head set, be the set the analysis gives the head of $`W` for the observed set $`L`. Apply Definition 19.2 to $`U`, with $`H` as the set needed before the inner $`W`:

$$`\mathrm{FV}(b)\cup\mathrm{live}(c,H)\cup\mathrm{live}(\mathsf{skip},L)=\mathrm{FV}(b)\cup L\cup\mathrm{live}(c,H).`

Define $`F(X)=\mathrm{FV}(b)\cup L\cup\mathrm{live}(c,X)` for every set $`X` of names. As in Session 9, $`F` is the *unfolding operator* of $`W`, here acting on sets of names. One more unfolding must not need more than the head provides: $`F(H)\subseteq H`. Since $`F(H)` is a union, this is three inclusions.

1. $`\mathrm{FV}(b)\subseteq H` (guard). If two stores satisfy $`s|_H=t|_H` at the head, they agree on the names of every operand of a comparison in $`b`. Lemma 1.1, applied to each operand, gives equal operand values, so $`B(b,s)=B(b,t)`: both runs exit or both iterate.
2. $`L\subseteq H` (exit). If the guard is false, the store at the head is the final store, so it must already carry $`L`.
3. $`\mathrm{live}(c,H)\subseteq H` (iteration). After the body the run is at the head again, where $`H` is needed. So $`\mathrm{live}(c,H)` is needed before the body, and the store before the body is the store at the head.

A set $`H` with $`F(H)\subseteq H` is a *post-fixed point* of $`F`. Every fixed point, $`F(H)=H`, is one. Many sets qualify: the set of all names always does. A smaller set at the head lets Session 20 delete more assignments, so the analysis searches upwards from $`\varnothing`. Let $`X_0=\varnothing` and $`X_{k+1}=F(X_k)`, and stop at the first $`k` with $`F(X_k)\subseteq X_k`.

For the opening loop, $`\mathrm{FV}(0<g)=\{g\}` because $`0<g` abbreviates $`\neg(g\le0)` (A.4). With $`L=\{z\}`, $`F(X)=\{g,z\}\cup\mathrm{live}(c,X)`. Each row computes $`\mathrm{live}(c,X_k)` from right to left as in §19.1:

$$`\begin{aligned}
\varnothing&\xleftarrow{\ z:=y\ }\varnothing\xleftarrow{\ y:=x\ }\varnothing\xleftarrow{\ g:=g-1\ }\varnothing=X_0, & F(X_0)&=\{g,z\}\\
\{g,y\}&\xleftarrow{\ z:=y\ }\{g,z\}\xleftarrow{\ y:=x\ }\{g,z\}\xleftarrow{\ g:=g-1\ }\{g,z\}=X_1, & F(X_1)&=\{g,y,z\}\\
\{g,x,y\}&\xleftarrow{\ z:=y\ }\{g,x,z\}\xleftarrow{\ y:=x\ }\{g,y,z\}\xleftarrow{\ g:=g-1\ }\{g,y,z\}=X_2, & F(X_2)&=\{g,x,y,z\}\\
\{g,x,y\}&\xleftarrow{\ z:=y\ }\{g,x,z\}\xleftarrow{\ y:=x\ }\{g,x,y,z\}\xleftarrow{\ g:=g-1\ }\{g,x,y,z\}=X_3, & F(X_3)&=\{g,x,y,z\}.
\end{aligned}`

The test first succeeds at $`X_3=\{g,x,y,z\}`. The runs of the opening paragraph explain each name. The guard reads $`g`. An immediate exit returns the old $`z`. One iteration copies the old $`y` into $`z`, and two iterations bring the old $`x` there. The requirement on $`z` becomes a requirement on $`y` after one pass through the body, and a requirement on $`x` after the second pass.

Each guess here also satisfies the reverse inclusion $`X_k\subseteq F(X_k)`: every name of the guess is demanded again. That is not enough. $`X_1=\{g,z\}` satisfies it, but stopping at $`X_1` would omit $`y`, and the run from $`g=1` copies the initial $`y` into $`z`. The test that ends the search must be $`F(X)\subseteq X`.

*Definition 19.3 (Bounded iteration and the loop clause).* Let $`F` be a function from sets of names to sets of names, let $`D` be a set of names, the *fallback set*, and let $`n` be a natural number, the *fuel*. Define $`\mathrm{iter}(F,D,n,X)` by recursion on $`n`:

$$`\begin{aligned}
\mathrm{iter}(F,D,0,X)&=D\\
\mathrm{iter}(F,D,n+1,X)&=X\ \text{ if } F(X)\subseteq X,\qquad \mathrm{iter}(F,D,n+1,X)=\mathrm{iter}(F,D,n,F(X))\ \text{ otherwise}.
\end{aligned}`

For $`W=\mathsf{while}\ b\ \mathsf{do}\ c`, the liveness transfer is

$$`\mathrm{live}(W,L)=\mathrm{iter}(F,D,20,\varnothing),\qquad F(X)=\mathrm{FV}(b)\cup L\cup\mathrm{live}(c,X),\qquad D=\mathrm{RV}(W)\cup L.`

For the opening loop the iteration returns $`X_3` after four applications of $`F`, long before the fuel runs out. Its fallback set is $`D=\{g\}\cup\{g,x,y\}\cup\{z\}=\{g,x,y,z\}`. The number 20 is the course’s choice, and nothing below depends on it. Nothing guarantees that the test succeeds within the fuel either. If it does not, the iteration returns $`D` without any test.

# The three inclusions
%%%
tag := "ch19-s3"
%%%

In §19.2 the iteration ended with $`F(X_3)\subseteq X_3`. If the fuel had been 2, it would have computed $`X_1` and $`X_2` and then returned $`D` at fuel 0. The first lemma says that these are the only two outcomes.

*Lemma 19.4 (Bounded iteration).* Let $`F` be a function from sets of names to sets of names and $`D` a set of names. (a) For every natural number $`n` and set $`X`, the set $`R=\mathrm{iter}(F,D,n,X)` satisfies $`F(R)\subseteq R` or $`R=D`. (b) If $`F(X)\subseteq D` for every $`X\subseteq D`, then $`\mathrm{iter}(F,D,20,\varnothing)\subseteq D`.

*Proof.* (a) By induction on $`n`, with the property

$$`P(n)\coloneqq\forall X,\quad F(\mathrm{iter}(F,D,n,X))\subseteq\mathrm{iter}(F,D,n,X)\ \lor\ \mathrm{iter}(F,D,n,X)=D.`

For $`n=0` the result is $`D`. For $`n+1`, fix $`X`. If $`F(X)\subseteq X`, the result is $`X` and the first alternative holds. Otherwise the result is $`\mathrm{iter}(F,D,n,F(X))`, and $`P(n)` at the set $`F(X)` gives the claim. The hypothesis is used at $`F(X)`, not at $`X`, so $`X` is quantified inside $`P(n)`.

(b) By induction on $`n`, with the property

$$`Q(n)\coloneqq\forall X,\quad X\subseteq D\Rightarrow\mathrm{iter}(F,D,n,X)\subseteq D.`

For $`n=0` the result is $`D`. For $`n+1`, fix $`X\subseteq D`. If $`F(X)\subseteq X`, the result is $`X\subseteq D`. Otherwise $`F(X)\subseteq D` by the assumption on $`F`, and $`Q(n)` at $`F(X)` bounds the result. Apply $`Q(20)` at $`\varnothing\subseteq D`. $`\square`

For the body $`c` of §19.1 and $`L=\{g,y,z\}`, $`\mathrm{live}(c,L)=\{g,x,y\}`, while $`\mathrm{RV}(c)\cup L=\{g,x,y,z\}`. The transfer never invents a name: every name it returns is observed or read by the command.

*Lemma 19.5 (Upper bound).* For every command $`c` and every set $`L` of names, $`\mathrm{live}(c,L)\subseteq\mathrm{RV}(c)\cup L`.

*Proof.* By structural induction on $`c`, with the property

$$`P(c)\coloneqq\forall L,\quad\mathrm{live}(c,L)\subseteq\mathrm{RV}(c)\cup L.`

Skip gives $`L`. An assignment $`x:=e` gives $`L` or $`(L\smallsetminus\{x\})\cup\mathrm{FV}(e)`, and both lie in $`\mathrm{FV}(e)\cup L`. For $`c_1;c_2`, let $`M=\mathrm{live}(c_2,L)`. $`P(c_2)` at $`L` gives $`M\subseteq\mathrm{RV}(c_2)\cup L`, and $`P(c_1)` at $`M` gives $`\mathrm{live}(c_1,M)\subseteq\mathrm{RV}(c_1)\cup M\subseteq\mathrm{RV}(c_1)\cup\mathrm{RV}(c_2)\cup L`. For a conditional, $`P(c_1)` and $`P(c_2)` at $`L` bound both branch transfers, and $`\mathrm{FV}(b)` is part of the read names. For a loop we write $`c_1` for the body, because $`c` names the whole command. The induction hypothesis is

$$`P(c_1):\quad\forall X,\quad\mathrm{live}(c_1,X)\subseteq\mathrm{RV}(c_1)\cup X.`

Let $`F` and $`D` be as in Definition 19.3, so $`D=\mathrm{FV}(b)\cup\mathrm{RV}(c_1)\cup L` is exactly the right-hand side of the claim. By Lemma 19.4(b) it suffices to show $`F(X)\subseteq D` for every $`X\subseteq D`. Fix such an $`X`. $`P(c_1)` at $`X` gives $`\mathrm{live}(c_1,X)\subseteq\mathrm{RV}(c_1)\cup X\subseteq D`. Also $`\mathrm{FV}(b)\subseteq D` and $`L\subseteq D`, so $`F(X)\subseteq D`. Here the hypothesis is used at $`X`, not at $`L`, which is why $`L` is quantified inside $`P(c)`. $`\square`

*Theorem 19.6 (Loop-head inclusions).* For every guard $`b`, command $`c` and set $`L` of names, let $`W=\mathsf{while}\ b\ \mathsf{do}\ c` and $`H=\mathrm{live}(W,L)`. Then

$$`\text{(1)}\ \ \mathrm{FV}(b)\subseteq H,\qquad\text{(2)}\ \ L\subseteq H,\qquad\text{(3)}\ \ \mathrm{live}(c,H)\subseteq H.`

For the opening loop, $`H=\{g,x,y,z\}` contains $`\mathrm{FV}(b)=\{g\}`, $`L=\{z\}` and $`\mathrm{live}(c,H)=\{g,x,y\}`, the last row of §19.2.

*Proof.* Let $`F` and $`D` be as in Definition 19.3, so $`H=\mathrm{iter}(F,D,20,\varnothing)` and $`D=\mathrm{FV}(b)\cup\mathrm{RV}(c)\cup L`. By Lemma 19.4(a) with $`n=20` and $`X=\varnothing`, $`F(H)\subseteq H` or $`H=D`. Inclusions (1) and (2): in the first alternative, $`\mathrm{FV}(b)\subseteq F(H)\subseteq H` and $`L\subseteq F(H)\subseteq H`. In the second, $`D` contains $`\mathrm{FV}(b)` and $`L` by its definition.

*Inclusion (3), the board case.* We must show $`\mathrm{live}(c,H)\subseteq H`.

1. Apply Lemma 19.4(a) with $`n=20` and $`X=\varnothing`. Since $`H=\mathrm{iter}(F,D,20,\varnothing)`, it gives $`F(H)\subseteq H` or $`H=D`.
2. _First alternative._ Suppose $`F(H)\subseteq H`. By the definition of $`F`, $`F(H)=\mathrm{FV}(b)\cup L\cup\mathrm{live}(c,H)`, so $`\mathrm{live}(c,H)\subseteq F(H)`.
3. Combine step 2 with $`F(H)\subseteq H` to get $`\mathrm{live}(c,H)\subseteq H`.
4. _Second alternative._ Suppose $`H=D`. Then $`H=\mathrm{FV}(b)\cup\mathrm{RV}(c)\cup L`, so $`\mathrm{RV}(c)\subseteq H`.
5. Apply Lemma 19.5 to the body $`c` and the set $`H`. The lemma holds for every set, so it may be used at $`H` in place of $`L`. It gives $`\mathrm{live}(c,H)\subseteq\mathrm{RV}(c)\cup H`.
6. By step 4, $`\mathrm{RV}(c)\cup H=H`. With step 5, $`\mathrm{live}(c,H)\subseteq H`.

This proves the three inclusions. $`\square`

The proof uses neither the number 20 nor any fact about which post-fixed point the iteration found. The choice of $`D` matters only in the second alternative, for (1), (2) and step 4 (Exercise 19.3). Session 20 uses the three inclusions as §19.2 describes: (1) in both loop cases of its proof to compare the guard values, (2) in the loop exit case and (3) in the loop iteration case.

# Exercises
%%%
tag := "ch19-s4"
number := false
%%%

*19.1.* Take the opening loop with nothing observed, $`L=\varnothing`. Compute $`\mathrm{live}(W,\varnothing)`. Why does it contain $`g`?

*19.2.* Append the assignment $`u:=v` to the body of the opening loop, with fresh names $`u,v`, and keep $`L=\{z\}`. Compute $`\mathrm{live}(W,\{z\})` and the fallback set $`D`. Suppose the fuel were 2 instead of 20. Which set would the iteration return? Check the three inclusions for it.

*19.3.* Replace the fallback set by $`\varnothing` in Definition 19.3, and take the fuel 2. Compute the result for the opening loop with $`L=\{z\}`. Which inclusions of Theorem 19.6 fail? Which step of its proof breaks?

*Further problem.* Exchange the first two assignments of the body: $`W'=\mathsf{while}\ 0<g\ \mathsf{do}\ (y:=x;\ z:=y;\ g:=g-1)`, with $`L=\{z\}`. Compute the loop-head set. Which initial value drops out? Justify the answer both by the transfer and by running the loop.

# Reading for the Seminar
%%%
tag := "ch19-s5"
number := false
%%%

*Definitions · 10 minutes.* Compute $`\mathrm{live}(c,\{g,y,z\})` for the body of the opening loop, from its last assignment to its first. Say which clause of Definition 19.2 each step uses.

*Joint proof · 30 minutes.* Compute $`X_0,\ldots,X_3` until the test succeeds, and check the three inclusions at $`X_3`. Then prove inclusion (3) of Theorem 19.6 for both alternatives of Lemma 19.4(a), using Lemma 19.5 for the fallback.

*Proof review · 20 minutes.* Work Exercise 19.2 with fuel 2 and match each check to a step of the board case. Use Exercise 19.3 to find the steps that need the fallback set. In the loop case of Lemma 19.5, say at which set the induction hypothesis is applied.

*Facilitator’s hint.* Keep the observed set $`L` fixed. The set that changes during the iteration is the guess for the loop head.

# Solutions and Further Reading
%%%
tag := "ch19-s6"
number := false
%%%

*19.1.* Here $`F(X)=\{g\}\cup\mathrm{live}(c,X)`. First $`F(\varnothing)=\{g\}`. At $`X_1=\{g\}`, the assignment $`g:=g-1` keeps $`\{g\}`, and the targets of $`y:=x` and $`z:=y` are dead, so $`F(X_1)=\{g\}\subseteq X_1`. The result is $`\{g\}`. The name $`g` is in every guess after $`X_0` because $`F` adds $`\mathrm{FV}(b)`, as inclusion (1) requires. Two runs that agree on $`g` at the head take the same guard decisions, hence the same number of iterations. This matters with nothing observed, because termination itself is compared. For $`\mathsf{while}\ 0<g\ \mathsf{do\ skip}`, a store with $`g=0` has a terminating execution and a store with $`g=1` has none. Session 20 proves that the transformed program terminates whenever the original does.

*19.2.* The name $`u` is never observed and never read, so it is in no guess. The clause for $`u:=v` returns its argument, and $`v` is never added. The iteration is the one in §19.2 and returns $`\{g,x,y,z\}`. The fallback set is $`D=\{g\}\cup\{g,v,x,y\}\cup\{z\}=\{g,v,x,y,z\}`. With fuel 2 the iteration computes $`X_1=\{g,z\}` and $`X_2=\{g,y,z\}`, reaches fuel 0, and returns $`D`. Check: $`\{g\}\subseteq D` and $`\{z\}\subseteq D`. From the end of the body, $`u:=v` leaves $`D` unchanged since $`u\notin D`, $`g:=g-1` leaves it unchanged, $`y:=x` gives $`\{g,v,x,z\}`, and $`z:=y` gives $`\{g,v,x,y\}\subseteq D`. These are steps 4–6 of the board case. The fallback keeps $`v`, which only a dead assignment reads. The result is safe but less precise.

*19.3.* The iteration again reaches fuel 0 at $`X_2` and now returns $`\varnothing`. Inclusion (1) fails, since $`\{g\}\not\subseteq\varnothing`, and so does (2), since $`\{z\}\not\subseteq\varnothing`. Inclusion (3) holds only because $`\mathrm{live}(c,\varnothing)=\varnothing`. In the proof, the second alternative breaks: $`H=D` no longer contains $`\mathrm{FV}(b)`, $`L` or $`\mathrm{RV}(c)`, so the arguments for (1) and (2) and step 4 fail. Two stores that agree on $`\varnothing` may differ at $`g`, and then their runs may take different numbers of iterations. They may also differ at $`z`, and then even an immediate exit gives different results.

*Further problem.* Start from $`\varnothing`. Guard and exit give $`X_1=\{g,z\}`. In the next pass, $`g:=g-1` keeps $`\{g,z\}`, $`z:=y` gives $`\{g,y\}`, and $`y:=x` gives $`\{g,x\}`. With guard and exit, $`X_2=\{g,x,z\}`. For the new body $`c'` the next pass is

$$`\{g,x\}\xleftarrow{\ y:=x\ }\{g,x,y\}\xleftarrow{\ z:=y\ }\{g,x,z\}\xleftarrow{\ g:=g-1\ }\{g,x,z\}=X_2,`

so $`F(X_2)=\{g,z\}\cup\{g,x\}=X_2` and the loop-head set is $`\{g,x,z\}`. The old $`y` is absent. In every iteration the assignment to $`y` overwrites it before $`z` reads it. An immediate exit still returns the old $`z`, and any positive number of iterations leaves the old $`x` in $`z`. Changing only the initial $`y` cannot change the final $`z`. In the original order, the run from $`g=1` copied the initial $`y` into $`z`. The exercise tests the order of the two transfers in the sequence clause.

*Further reading · Least post-fixed points.* Call $`F` _monotone_ if $`X\subseteq Y` implies $`F(X)\subseteq F(Y)`. For monotone $`F` the guesses increase, $`X_k\subseteq X_{k+1}`, and every post-fixed point $`P` contains every guess: $`X_0=\varnothing\subseteq P`, and $`X_k\subseteq P` gives $`X_{k+1}=F(X_k)\subseteq F(P)\subseteq P`. So when the test succeeds at $`X_k`, the set $`X_k` is the least post-fixed point of $`F`, and also a fixed point. Nipkow and Klein (_Concrete Semantics_, §10.4) define the loop clause as this least set, prove that their transfer is monotone (Lemma 10.30), and compute the set by iteration from $`\varnothing` (Lemma 10.32). They bound the number of steps by the number of read names of the body plus one. Their pre-fixpoint is our post-fixed point: both mean $`F(P)\subseteq P`. Leroy’s course, §9.1, proves the general statement: in an order without infinite strictly increasing chains, iterating a monotone function from the least element reaches a fixed point that lies below every post-fixed point. Theorem 19.6 needs none of this: neither monotonicity, nor leastness, nor a bound on the number of steps.

*Further reading · One-pass liveness.* _Concrete Semantics_, §10.3, first uses a simpler assignment clause, $`\mathrm{FV}(e)\cup(L\smallsetminus\{x\})`, in which the right-hand side is live even when the target is dead. With that clause one pass suffices for a loop: the set $`\mathrm{FV}(b)\cup L\cup\mathrm{live}(c,L)` satisfies inclusion (3) (CS Lemma 10.16). With the clause of Definition 19.2 the one-pass set can fail inclusion (3). CS Example 10.22 takes $`\mathsf{while}\ 0<x\ \mathsf{do}\ (x:=y;\ y:=z)` and $`L=\{x\}`. One pass gives $`\{x,y\}`, but the body transfer of $`\{x,y\}` is $`\{y,z\}`. This is why the loop clause iterates.

*Further reading · Widening.* For the names of a fixed program, a strictly increasing chain of sets can add only finitely many names. An interval analysis of an unbounded counter can instead produce $`[0,0]`, $`[0,1]`, $`[0,2]`, and so on without end. A widening replaces a growing upper endpoint by $`+\infty` to force the iteration to stop, while still covering every reachable value. It answers the convergence problem differently from the fallback set of Definition 19.3. See _Concrete Semantics_, §13.9.

*Further reading · Sources.* Xavier Leroy’s _Compiler Verification_ course, Lean port, §10 (liveness analysis and dead code elimination) and §9.1 (computing fixed points). Nipkow and Klein, _Concrete Semantics_, §§10.3–10.4, pp. 164–177. [Liveness in Leroy’s course](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Deadcode.lean) · [Fixed points in Leroy’s course](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Fixpoints.lean) · [Concrete Semantics, §10.3, p. 164](https://concrete-semantics.org/concrete-semantics.pdf#page=174)

# Sources and Formalization
%%%
tag := "ch19-notes"
number := false
%%%

* *Lemma 19.4.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 19.5.* Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 19.6.* Corresponds to CS §10.4. Externally checked: the statement matches a declaration of Leroy’s course ([IMP card references](imp-card/index.html#imp-sources)).
