import VersoManual
import PLBook.IMP.Equivalence

open Verso.Genre Manual

#doc (Manual) "Program Equivalence" =>
%%%
tag := "ch07"
file := "chapter-07"
%%%

* *Definitions.* The six execution rules: skip, assignment, sequence, conditional, loop exit and loop iteration ([IMP language card A.5](imp-card/index.html#imp-a5); Session 2, Definition 2.1). The derived rules for a true guard and for a false guard ([Session 2, §2.2](chapter-02/index.html#ch02-s2)). Inversion ([Session 1, §1.4](chapter-01/index.html#ch01-s4)) and sequence inversion ([Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3)). Determinacy ([Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2)).
* *New terms.* Program equivalence, observation, loop unfolding. [Glossary and label key](glossary/index.html)
* *Theorem 7.3 (Loop unfolding).* For every guard $`b`, command $`c` and stores $`s,t`, $`s\vdash\mathsf{while}\ b\ \mathsf{do}\ c\Downarrow t` if and only if $`s\vdash\mathsf{if}\ b\ \mathsf{then}\ (c;\mathsf{while}\ b\ \mathsf{do}\ c)\ \mathsf{else}\ \mathsf{skip}\Downarrow t`.
* *Source.* The execution rules follow Leroy’s IMP, as presented in A.5. Nipkow and Klein state the same unfolding for their IMP, whose conditional has two rules, with the same definition of equivalence. [Source and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics, §7.2.4, p. 82](https://concrete-semantics.org/concrete-semantics.pdf#page=92)
* *Board case.* The direction from the loop to its unfolding, when the loop derivation ends with the loop iteration rule. Then the short case of the loop exit rule.
* *Proof outline.* Case analysis on the last rule, with no induction. In each direction, invert the last rule of the given derivation and place its premises under other rules. The loop derivation from the intermediate store $`m` is reused unchanged.
* *From Session 6.* Session 6 compared two descriptions of the runs of one command: execution trees and paths to skip. Here we compare two different commands by one description, their initial–final store pairs, and ignore the shape and size of the evidence.

A compiler may replace `while b do c` by `if b then (c; while b do c) else skip`. The new command tests the guard and runs the body once before it reaches the loop. Its syntax tree is larger, and its derivations use different rules. In what sense do the two commands do the same thing? This session fixes one answer: from each initial store they reach the same final stores. We then prove that the rewrite meets it.

# Equivalence of commands
%%%
tag := "ch07-s1"
%%%

Let $`x` and $`y` be distinct names. Compare `x := 0; x := y + 1` with `x := y + 1`. Fix a store $`s`. In the first command the sequence rule passes through the intermediate store $`m=s[x\mapsto0]`. Since $`x\neq y`, $`m(y)=s(y)`, so the second assignment writes $`\mathrm{eval}(y+1,m)=s(y)+1`. The first command therefore ends in $`m[x\mapsto s(y)+1]` and the second in $`s[x\mapsto s(y)+1]`. Both stores hold $`s(y)+1` at $`x` and $`s(z)` at every other name $`z`, so they are equal. The two commands reach the same final store from every initial store, although only the first passes through $`m`.

Replace `y + 1` by `x + 1` and the agreement fails. From a store with $`s(x)=4`, the command `x := 0; x := x + 1` ends with 1 in $`x`, and `x := x + 1` ends with 5 in $`x`. The second assignment now reads the value written by the first.

*Definition 7.1 (Program equivalence).* For a command $`c`, let

$$`\mathrm{Exec}(c)=\{(s,t)\in\Sigma\times\Sigma\mid s\vdash c\Downarrow t\}`

be the set of its initial–final store pairs. Commands $`c` and $`d` are *equivalent*, written $`c\equiv d`, if $`\mathrm{Exec}(c)=\mathrm{Exec}(d)`. Spelled out,

$$`c\equiv d\quad\Longleftrightarrow\quad\forall s,t\in\Sigma,\ \bigl(s\vdash c\Downarrow t\iff s\vdash d\Downarrow t\bigr).`

The relation $`\equiv` is *program equivalence*. It is reflexive, symmetric and transitive, because equality of sets is.

An *observation* is what a notion of equivalence compares about a run. Definition 7.1 observes the entire final store of each terminating execution. It does not observe intermediate stores such as $`m` above, the shape of a derivation, or the number of steps. An initial store from which a command has no terminating execution contributes no pair.

By [Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2), each store $`s` is the first component of at most one pair in $`\mathrm{Exec}(c)`. Thus $`c\equiv d` says: from each store $`s`, either neither command has a terminating execution, or both have one and their final stores are equal.

*Example 7.2.* The commands `x := x + 0` and `skip` are equivalent. The only rule whose conclusion has an assignment at the root is the assignment rule. So every execution of `x := x + 0` from $`s` ends in $`s[x\mapsto s(x)+0]`. This store holds $`s(x)` at $`x` and $`s(z)` at every other name $`z`, so it equals $`s`. The only rule for skip also ends in $`s`. Hence both sets of pairs equal $`\{(s,s)\mid s\in\Sigma\}`. In the transitions of [A.6](imp-card/index.html#imp-a6) the assignment takes one step and skip takes none. Definition 7.1 does not observe this difference.

# Loop unfolding
%%%
tag := "ch07-s2"
%%%

Throughout this section fix a guard $`b` and a command $`c`, and write

$$`W=\mathsf{while}\ b\ \mathsf{do}\ c,\qquad U=\mathsf{if}\ b\ \mathsf{then}\ (c;W)\ \mathsf{else}\ \mathsf{skip}.`

We call $`U` the *unfolding* of $`W`, and the rewrite from $`W` to $`U` *loop unfolding*. The command $`U` tests the guard, runs the body once if the guard is true, and then runs the original loop $`W`. The $`W` inside $`U` is the same fixed loop; $`U` is not defined recursively.

Take the loop of [Session 2, §2.4](chapter-02/index.html#ch02-s4): $`b` is `x < 1`, $`c` is `x := x + 1`, and $`s(x)=0`. Put $`m=s[x\mapsto1]`. The guard is true in $`s` and false in $`m`. Session 2 derived $`s\vdash W\Downarrow m` with the loop iteration rule at the root:

$$`\frac{B(x<1,s)=\mathsf{true}\qquad\dfrac{}{s\vdash x:=x+1\Downarrow m}\qquad\dfrac{B(x<1,m)=\mathsf{false}}{m\vdash W\Downarrow m}}{s\vdash W\Downarrow m}`

The same two subderivations give a derivation for $`U`. Join them with the sequence rule, then apply the derived rule for a true guard:

$$`\frac{B(x<1,s)=\mathsf{true}\qquad\dfrac{\dfrac{}{s\vdash x:=x+1\Downarrow m}\qquad\dfrac{B(x<1,m)=\mathsf{false}}{m\vdash W\Downarrow m}}{s\vdash(x:=x+1;W)\Downarrow m}}{s\vdash U\Downarrow m}`

The leaves are the same. Only the rules that join them differ. In particular, the subderivation of $`m\vdash W\Downarrow m` appears unchanged in both trees. The general proof performs the same rearrangement.

For the command $`U`, the two derived rules of [Session 2, §2.2](chapter-02/index.html#ch02-s2) read as follows. The left one is the derived rule for a true guard, the right one the derived rule for a false guard.

$$`\frac{B(b,s)=\mathsf{true}\qquad s\vdash(c;W)\Downarrow t}{s\vdash U\Downarrow t}\qquad\qquad\frac{B(b,s)=\mathsf{false}\qquad s\vdash\mathsf{skip}\Downarrow t}{s\vdash U\Downarrow t}`

Inversion ([Session 1, §1.4](chapter-01/index.html#ch01-s4)) gives four facts.

1. A derivation of $`s\vdash W\Downarrow t` ends with the loop exit rule or the loop iteration rule. These are the only rules whose conclusion has a loop at the root.
2. A derivation of $`s\vdash U\Downarrow t` ends with the conditional rule, the only rule whose conclusion has a conditional at the root. Its premise derives $`s\vdash k\Downarrow t`, where $`k` is $`c;W` if $`B(b,s)=\mathsf{true}` and $`\mathsf{skip}` otherwise.
3. From a derivation of $`s\vdash(c;W)\Downarrow t`, [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3) gives a store $`m` with $`s\vdash c\Downarrow m` and $`m\vdash W\Downarrow t`.
4. A derivation of $`s\vdash\mathsf{skip}\Downarrow t` ends with the skip rule, so $`t=s`.

*Theorem 7.3 (Loop unfolding).* For every guard $`b`, command $`c` and stores $`s,t`,

$$`s\vdash W\Downarrow t\quad\Longleftrightarrow\quad s\vdash U\Downarrow t.`

Hence $`W\equiv U`.

*Proof of the forward direction.* As in Session 1, $`D:J` means that $`D` is a derivation of the judgment $`J`. We must show: if $`D:s\vdash W\Downarrow t`, then $`s\vdash U\Downarrow t`. The proof is by cases on the last rule of $`D`, with no induction. By fact 1 there are two cases.

*Iteration case.* Suppose $`D` ends with the loop iteration rule. Then $`D` has the form

$$`D:\quad\frac{B(b,s)=\mathsf{true}\qquad D_1:s\vdash c\Downarrow m\qquad D_2:m\vdash W\Downarrow t}{s\vdash W\Downarrow t}`

1. The premises of the last rule of $`D` give $`B(b,s)=\mathsf{true}`, a store $`m`, and derivations $`D_1:s\vdash c\Downarrow m` and $`D_2:m\vdash W\Downarrow t`.
2. Apply the sequence rule to $`D_1` and $`D_2`. This gives $`s\vdash(c;W)\Downarrow t`.
3. Apply the derived rule for a true guard to $`B(b,s)=\mathsf{true}` and the derivation of step 2. This gives $`s\vdash U\Downarrow t`.

The new derivation is

$$`\frac{B(b,s)=\mathsf{true}\qquad\dfrac{D_1:s\vdash c\Downarrow m\qquad D_2:m\vdash W\Downarrow t}{s\vdash(c;W)\Downarrow t}}{s\vdash U\Downarrow t}`

Step 2 uses $`D_2` as it stands. No induction hypothesis about $`D_2` is needed, because $`D_2` is moved, not transformed.

*Exit case.* Suppose $`D` ends with the loop exit rule.

1. The side condition and the conclusion of that rule give $`B(b,s)=\mathsf{false}` and $`t=s`.
2. The skip rule gives $`s\vdash\mathsf{skip}\Downarrow s`.
3. Apply the derived rule for a false guard to $`B(b,s)=\mathsf{false}` and the derivation of step 2. This gives $`s\vdash U\Downarrow s`, that is, $`s\vdash U\Downarrow t`.

*Proof of the reverse direction.* Let $`E:s\vdash U\Downarrow t`. By fact 2, $`E` ends with the conditional rule and has a premise $`E_1:s\vdash k\Downarrow t`. If $`B(b,s)=\mathsf{true}`, then $`k` is $`c;W`. Fact 3 gives a store $`m` with $`s\vdash c\Downarrow m` and $`m\vdash W\Downarrow t`. Together with $`B(b,s)=\mathsf{true}` these are the three premises of the loop iteration rule, which gives $`s\vdash W\Downarrow t`. If $`B(b,s)=\mathsf{false}`, then $`k` is skip, and fact 4 gives $`t=s`. The loop exit rule gives $`s\vdash W\Downarrow s`, that is, $`s\vdash W\Downarrow t`.

Both directions hold for all $`s` and $`t`. So $`\mathrm{Exec}(W)=\mathrm{Exec}(U)`, and $`W\equiv U`. $`\square`

The theorem has no termination hypothesis. Take $`b` to be true and $`c` to be skip. By [Session 2, §2.4](chapter-02/index.html#ch02-s4), $`W` has no terminating execution from any store. By the reverse direction neither has $`U`, since a derivation for $`U` would yield one for $`W`. Both sets of pairs are empty, hence equal.

Compare the loop iteration case of [Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2). There the loop premise had to be compared with a second derivation, and that required an induction hypothesis for it. Here the loop premise is only moved. The unfolding must keep the loop: replacing $`c;W` by $`c` alone gives a command that is not equivalent to $`W` (Exercise 7.2).

# Replacement before a suffix
%%%
tag := "ch07-s3"
%%%

An unfolded loop usually sits inside a larger program. Take the loop of §7.2 followed by `y := x`, for a name $`y\neq x`. From $`s(x)=0` the loop ends in $`m=s[x\mapsto1]`, and the suffix ends in $`m[y\mapsto1]`. By Theorem 7.3 the unfolding $`U` also ends in $`m` from $`s`. The same suffix derivation from $`m` then completes a run of $`U` followed by `y := x`. The next proposition does this for every initial store and every suffix.

*Proposition 7.4 (Replacement before a suffix).* For all commands $`c,d,a`, if $`c\equiv d` then $`(c;a)\equiv(d;a)`.

*Proof.* Fix $`s,t` and suppose $`s\vdash(c;a)\Downarrow t`. [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3) gives a store $`m` with $`s\vdash c\Downarrow m` and $`m\vdash a\Downarrow t`. Since $`c\equiv d`, also $`s\vdash d\Downarrow m`. The sequence rule, applied to this derivation and the given derivation of $`m\vdash a\Downarrow t`, gives $`s\vdash(d;a)\Downarrow t`. The converse is the same argument with $`c` and $`d` exchanged, which is allowed because $`\equiv` is symmetric. $`\square`

With Theorem 7.3 this gives $`(W;a)\equiv(U;a)` for every command $`a`.

The proof hands the entire intermediate store $`m` to the suffix. This is why Definition 7.1 observes the entire final store. Suppose instead that we observed only the final value of one name $`x`. For a name $`y\neq x`, the commands `y := 1` and `y := 2` would then count as equivalent, since both leave $`x` unchanged. The suffix `x := y` separates them: it leaves 1 in $`x` after the first and 2 after the second. With that weaker observation Proposition 7.4 would fail. Session 20 observes only a chosen set of names. Its theorem then compares runs from two stores that agree on a computed set of names, not on all names.

# Exercises
%%%
tag := "ch07-s4"
number := false
%%%

*7.1.* Prove $`((c_1;c_2);c_3)\equiv(c_1;(c_2;c_3))`. Name both intermediate stores, $`m_1` and $`m_2`.

*7.2.* Refute $`(\mathsf{while}\ b\ \mathsf{do}\ c)\equiv(\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ \mathsf{skip})`. Give a guard, a body and an initial store from which both commands terminate, and compute both final stores.

*7.3.* Suppose the language had an output command. One loop emits an output and then runs forever. Another runs forever without output. Does Definition 7.1 distinguish them? What additional observation would?

*7.4.* Prove $`(\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ c)\equiv c`. Which property of the single conditional rule makes each direction one step?

*Further problem.* Decide whether $`\mathsf{if}\ b\ \mathsf{then}\ (c;a)\ \mathsf{else}\ (d;a)` and $`(\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d);a` are equivalent for all commands. Then examine the counterpart that moves a common *prefix* out of the branches: compare $`\mathsf{if}\ b\ \mathsf{then}\ (a;c)\ \mathsf{else}\ (a;d)` with $`a;(\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d)`. Give a sufficient condition on $`a` and $`b`, and a counterexample when it fails.

# Reading for the Seminar
%%%
tag := "ch07-s5"
number := false
%%%

*Definitions · 10 minutes.* Write $`W` and $`U`, and state Theorem 7.3 with both store quantifiers explicit. Say what Definition 7.1 does not observe, using the example that opens §7.1.

*Joint proof · 30 minutes.* The presenter proves the forward direction of Theorem 7.3: the iteration case, then the exit case. A participant proves the reverse direction for a true guard by inverting the conditional rule and then the sequence. Finish by using Theorem 7.3 and Proposition 7.4 to replace a loop inside a sequence.

*Proof review · 20 minutes.* Run the forward proof for the candidate of Exercise 7.2 and locate the step that fails. Ask which property of $`D_2` the proof never used.

*Facilitator’s hint.* Underline the recursive loop judgment already available as a premise. Ask where exactly that same judgment belongs in the target tree.

# Solutions and Further Reading
%%%
tag := "ch07-s6"
number := false
%%%

*7.1.* Let $`s\vdash((c_1;c_2);c_3)\Downarrow t`. Proposition 2.2, applied twice, gives stores $`m_1,m_2` with $`s\vdash c_1\Downarrow m_1`, $`m_1\vdash c_2\Downarrow m_2` and $`m_2\vdash c_3\Downarrow t`. The sequence rule applied to the last two gives $`m_1\vdash(c_2;c_3)\Downarrow t`. The sequence rule applied to the first and this one gives $`s\vdash(c_1;(c_2;c_3))\Downarrow t`. The converse regroups the same three derivations. Nipkow and Klein prove this as Lemma 7.2 (_Concrete Semantics_, §7.2.3). Session 8 proves the same law for a semantics that assigns a function to each command.

*7.2.* Take the guard `x < 2`, the body `x := x + 1` and $`s(x)=0`. The conditional runs the body once and ends with 1 in $`x`. The loop runs the body twice, exits, and ends with 2 in $`x`. All other names keep their values in both.

*7.3.* Neither command has a terminating execution. Both sets of pairs are empty, so Definition 7.1 identifies them. An observation that records the outputs produced so far, also on runs that do not terminate, separates them. When a language gains output, the choice of observation must be revisited.

*7.4.* The premise of the conditional rule is $`s\vdash k\Downarrow t`, where $`k` is the branch selected by $`B(b,s)`. Both branches are $`c`, so $`k=c` whatever the guard. Inverting the conditional rule gives $`s\vdash c\Downarrow t`. Conversely, the conditional rule turns $`s\vdash c\Downarrow t` into an execution of the conditional. Nipkow and Klein state this as Lemma 7.4. With their two conditional rules, the proof splits on the value of the guard.

*Further problem.* Fix $`s`. Both commands test $`b` in $`s`. If $`B(b,s)=\mathsf{true}`, a terminating execution of either command consists of a run of $`c` from $`s` to some $`m` and a run of $`a` from $`m`; inverting the conditional rule and Proposition 2.2 expose them. The same two derivations, regrouped, give an execution of the other command. A false guard gives the same argument with $`d`. So the two commands are equivalent.

For the prefix version it suffices that $`a` preserves the guard: whenever $`s\vdash a\Downarrow m`, $`B(b,m)=B(b,s)`. Both commands then run $`a` from $`s` to the same $`m` and select the same branch. If $`a` has no terminating execution from $`s`, neither command has one. For a counterexample take the guard `x = 0`, the prefix `x := 1`, and the branches `y := 1` and `y := 2`, with $`x\neq y`. From $`s(x)=0` the first command ends with 1 in $`y` and the second with 2 in $`y`.

*Further reading · The small-step view.* In the transitions of [A.6](imp-card/index.html#imp-a6), if $`B(b,s)=\mathsf{true}` then $`\langle W,s\rangle\to\langle c;W,s\rangle` and, by the conditional step, $`\langle U,s\rangle\to\langle c;W,s\rangle`. If the guard is false, both configurations step to $`\langle\mathsf{skip},s\rangle`. Inversion shows that each has exactly this one transition. Neither $`W` nor $`U` is skip, so a finite path from either to $`\langle\mathsf{skip},t\rangle` begins with that transition and continues from the same configuration. Hence $`\langle W,s\rangle\to^*\langle\mathsf{skip},t\rangle` exactly when $`\langle U,s\rangle\to^*\langle\mathsf{skip},t\rangle`, and the paths have equal length. Session 6, Theorem 6.2 turns this into a second proof of Theorem 7.3. The small-step loop rule is itself one loop unfolding. Example 7.2, by contrast, relates two commands whose paths have different lengths.

*Further reading · Replacement inside a loop.* Let $`c\equiv c'` and $`W'=\mathsf{while}\ b\ \mathsf{do}\ c'`. Then $`W\equiv W'`. A loop may run its body many times, so the hypothesis must be used at every iteration. For $`D:s\vdash W\Downarrow t` prove $`P(D)\coloneqq s\vdash W'\Downarrow t` by induction on the height of $`D` (Session 3, §3.1). If $`D` ends with the loop exit rule, then $`B(b,s)=\mathsf{false}` and $`t=s`, and the loop exit rule for $`W'` uses the same guard. If $`D` ends with the loop iteration rule, its premises are $`B(b,s)=\mathsf{true}`, $`D_1:s\vdash c\Downarrow m` and $`D_2:m\vdash W\Downarrow t`, with hypothesis $`P(D_2):m\vdash W'\Downarrow t`. From $`D_1` and $`c\equiv c'` we get $`s\vdash c'\Downarrow m`, and the loop iteration rule gives $`s\vdash W'\Downarrow t`. Exchange $`c` and $`c'` for the converse. Unlike in Theorem 7.3, the loop premise $`D_2` must be transformed, and the induction hypothesis does that. The store passed to each guard test is the same on both sides, while the derivations of the bodies may differ. Nipkow and Klein state this as Lemma 7.5 and derive it from their Lemma 7.6, which they prove by rule induction. With Proposition 7.4 and similar arguments for the right operand of a sequence and for the branches of a conditional, induction on the surrounding command shows that replacing a subcommand by an equivalent one gives an equivalent command. Nipkow and Klein call $`\equiv` a congruence for this reason.

*Further reading · Repeated unfolding.* Theorem 7.3 applies again to the copy of $`W` inside $`U`. With the replacement property just described, $`W\equiv\mathsf{if}\ b\ \mathsf{then}\ (c;U)\ \mathsf{else}\ \mathsf{skip}`. Each copy of the guard is tested in its own store. For the loop of §7.2 from $`s(x)=0`, the first test reads $`s`, where `x < 1` holds, and the second reads $`m=s[x\mapsto1]`, where it fails. The result is $`m`. Evaluating both tests in $`s` instead would run the body twice and end with 2 in $`x`.

*Further reading · Observing one name at a time.* Fix a name $`r`. For a command $`c`, a store $`s` and a name $`y`, let $`O(c,s,y)` be the set of values that $`c;(r:=y)` can leave in $`r` when started in $`s`. Proposition 2.2 and the assignment rule give $`O(c,s,y)=\{t(y)\mid s\vdash c\Downarrow t\}`. In IMP, $`c\equiv d` holds exactly when $`O(c,s,y)=O(d,s,y)` for all $`s` and $`y`. One direction follows from the formula. For the other, let $`s\vdash c\Downarrow t`. Then $`O(c,s,y)` is not empty, so $`d` has a terminating execution from $`s`, say to $`u`. By determinacy, $`O(c,s,y)=\{t(y)\}` and $`O(d,s,y)=\{u(y)\}` for every $`y`. So $`t(y)=u(y)` at every name, and $`t=u`. Determinacy is needed. Add the choice command of Session 3, Exercise 3.2. One command sets the pair of values at $`x,y` to $`(0,0)` or to $`(1,1)`; another sets it to $`(0,1)` or to $`(1,0)`. Each name alone shows the values 0 and 1 after either command, yet only the first can end with equal values at $`x` and $`y`. The step that fails is fixing one final store $`u` for all names $`y`.

Nipkow and Klein define the same equivalence of commands and state Lemmas 7.3–7.6 and 7.8 in _Concrete Semantics_, §7.2.4, pp. 82–83. Exercises 7.5 and 7.6 of that chapter (p. 93) ask for further equivalences of conditionals and loops. [Concrete Semantics, §7.2.4](https://concrete-semantics.org/concrete-semantics.pdf#page=92)

# Sources and Formalization
%%%
tag := "ch07-notes"
number := false
%%%

* *Theorem 7.3.* Formulated in this book. Corresponds to CS Lemma 7.3. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 7.4.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
