import VersoManual
import PLBook.IMP.Equivalence

open Verso.Genre Manual

#doc (Manual) "Program Equivalence" =>
%%%
tag := "ch07"
file := "chapter-07"
%%%

A compiler may replace `while b do c` by `if b then (c; while b do c) else skip`. The new command tests the guard and runs the body once before it reaches the loop. Its syntax tree is larger, and its derivations use different rules. In what sense do the two commands do the same thing? This session fixes one answer: from each initial state they reach the same final states. We then prove that the rewrite meets it.

*In this session.*

* *Definitions.* The six execution rules: skip, assignment, sequence, conditional, loop exit and loop iteration ([IMP language card A.5](imp-card/index.html#imp-a5); Session 2, Definition 2.1). The derived rules for a true guard and for a false guard ([Session 2, §2.2](chapter-02/index.html#ch02-s2)). Inversion ([Session 1, §1.4](chapter-01/index.html#ch01-s4)) and sequence inversion ([Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3)). Determinacy ([Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2)).
* *New terms.* Program equivalence, observation, loop unfolding. [Glossary](glossary/index.html)
* *Theorem 7.3 (Loop unfolding).* For every guard $`b`, command $`c` and states $`\sigma,\sigma'`, $`\sigma\vdash\mathsf{while}\ b\ \mathsf{do}\ c\Downarrow\sigma'` if and only if $`\sigma\vdash\mathsf{if}\ b\ \mathsf{then}\ (c;\mathsf{while}\ b\ \mathsf{do}\ c)\ \mathsf{else}\ \mathsf{skip}\Downarrow\sigma'`.
* *Board case.* The direction from the loop to its unfolding, when the loop derivation ends with the loop iteration rule. Then the short case of the loop exit rule.
* *Proof outline.* Case analysis on the last rule, with no induction. In each direction, invert the last rule of the given derivation and place its premises under other rules. The loop derivation from the intermediate state $`\sigma_1` is reused unchanged.
* *From Session 6.* Session 6 compared two descriptions of the runs of one command: execution trees and paths to skip. Here we compare two different commands by one description, their initial–final state pairs, and ignore the shape and size of the evidence.

# Equivalence of commands
%%%
tag := "ch07-s1"
%%%

Let $`x` and $`y` be distinct names. Compare `x := 0; x := y + 1` with `x := y + 1`. Fix a state $`\sigma`. In the first command the sequence rule passes through the intermediate state $`\sigma_1=\sigma[x\mapsto0]`. Since $`x\neq y`, $`\sigma_1(y)=\sigma(y)`, so the second assignment writes $`\mathrm{eval}(y+1,\sigma_1)=\sigma(y)+1`. The first command therefore ends in $`\sigma_1[x\mapsto \sigma(y)+1]` and the second in $`\sigma[x\mapsto \sigma(y)+1]`. Both states hold $`\sigma(y)+1` at $`x` and $`\sigma(z)` at every other name $`z`, so they are equal. The two commands reach the same final state from every initial state, although only the first passes through $`\sigma_1`.

Replace `y + 1` by `x + 1` and the agreement fails. From a state with $`\sigma(x)=4`, the command `x := 0; x := x + 1` ends with 1 in $`x`, and `x := x + 1` ends with 5 in $`x`. The second assignment now reads the value written by the first.

*Definition 7.1 (Program equivalence).* For a command $`c`, let

$$`\mathrm{Exec}(c)=\{(\sigma,\sigma')\in\Sigma\times\Sigma\mid \sigma\vdash c\Downarrow\sigma'\}`

be the set of its initial–final state pairs. Commands $`c` and $`d` are *equivalent*, written $`c\equiv d`, if $`\mathrm{Exec}(c)=\mathrm{Exec}(d)`. Spelled out,

$$`c\equiv d\quad\Longleftrightarrow\quad\forall \sigma,\sigma'\in\Sigma,\ \bigl(\sigma\vdash c\Downarrow\sigma'\iff \sigma\vdash d\Downarrow\sigma'\bigr).`

The relation $`\equiv` is *program equivalence*. It is reflexive, symmetric and transitive, because equality of sets is. By [Session 3, §3.3](chapter-03/index.html#ch03-s3), $`\mathrm{Exec}(c)` is the graph of a partial function.

An *observation* is what a notion of equivalence compares about a run. Definition 7.1 observes the entire final state of each terminating execution. It does not observe intermediate states such as $`\sigma_1` above, the shape of a derivation, or the number of steps. An initial state from which a command has no terminating execution contributes no pair.

By [Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2), each state $`\sigma` is the first component of at most one pair in $`\mathrm{Exec}(c)`. Thus $`c\equiv d` says: from each state $`\sigma`, either neither command has a terminating execution, or both have one and their final states are equal.

*Example 7.2.* The commands `x := x + 0` and `skip` are equivalent. The only rule whose conclusion has an assignment at the root is the assignment rule. So every execution of `x := x + 0` from $`\sigma` ends in $`\sigma[x\mapsto \sigma(x)+0]`. This state holds $`\sigma(x)` at $`x` and $`\sigma(z)` at every other name $`z`, so it equals $`\sigma`. The only rule for skip also ends in $`\sigma`. Hence both sets of pairs equal $`\{(\sigma,\sigma)\mid \sigma\in\Sigma\}`. In the transitions of [A.6](imp-card/index.html#imp-a6) the assignment takes one step and skip takes none. Definition 7.1 does not observe this difference.

# Loop unfolding
%%%
tag := "ch07-s2"
%%%

Throughout this section fix a guard $`b` and a command $`c`, and write

$$`W=\mathsf{while}\ b\ \mathsf{do}\ c,\qquad U=\mathsf{if}\ b\ \mathsf{then}\ (c;W)\ \mathsf{else}\ \mathsf{skip}.`

We call $`U` the *unfolding* of $`W`, and the rewrite from $`W` to $`U` *loop unfolding*. The command $`U` tests the guard, runs the body once if the guard is true, and then runs the original loop $`W`. The $`W` inside $`U` is the same fixed loop; $`U` is not defined recursively.

Take the loop of [Session 2, §2.4](chapter-02/index.html#ch02-s4): $`b` is `x < 1`, $`c` is `x := x + 1`, and $`\sigma(x)=0`. Put $`\sigma_1=\sigma[x\mapsto1]`. The guard is true in $`\sigma` and false in $`\sigma_1`. Session 2 derived $`\sigma\vdash W\Downarrow\sigma_1` with the loop iteration rule at the root:

$$`\frac{B(x<1,\sigma)=\mathsf{true}\qquad\dfrac{}{\sigma\vdash x:=x+1\Downarrow\sigma_1}\qquad\dfrac{B(x<1,\sigma_1)=\mathsf{false}}{\sigma_1\vdash W\Downarrow\sigma_1}}{\sigma\vdash W\Downarrow\sigma_1}`

The same two subderivations give a derivation for $`U`. Join them with the sequence rule, then apply the derived rule for a true guard:

$$`\frac{B(x<1,\sigma)=\mathsf{true}\qquad\dfrac{\dfrac{}{\sigma\vdash x:=x+1\Downarrow\sigma_1}\qquad\dfrac{B(x<1,\sigma_1)=\mathsf{false}}{\sigma_1\vdash W\Downarrow\sigma_1}}{\sigma\vdash(x:=x+1;W)\Downarrow\sigma_1}}{\sigma\vdash U\Downarrow\sigma_1}`

The leaves are the same. Only the rules that join them differ. In particular, the subderivation of $`\sigma_1\vdash W\Downarrow\sigma_1` appears unchanged in both trees. The general proof performs the same rearrangement.

For the command $`U`, the two derived rules of [Session 2, §2.2](chapter-02/index.html#ch02-s2) read as follows. The left one is the derived rule for a true guard, the right one the derived rule for a false guard.

$$`\frac{B(b,\sigma)=\mathsf{true}\qquad \sigma\vdash(c;W)\Downarrow\sigma'}{\sigma\vdash U\Downarrow\sigma'}\qquad\qquad\frac{B(b,\sigma)=\mathsf{false}\qquad \sigma\vdash\mathsf{skip}\Downarrow\sigma'}{\sigma\vdash U\Downarrow\sigma'}`

Inversion ([Session 1, §1.4](chapter-01/index.html#ch01-s4)) gives four facts.

1. A derivation of $`\sigma\vdash W\Downarrow\sigma'` ends with the loop exit rule or the loop iteration rule. These are the only rules whose conclusion has a loop at the root.
2. A derivation of $`\sigma\vdash U\Downarrow\sigma'` ends with the conditional rule, the only rule whose conclusion has a conditional at the root. Its premise derives $`\sigma\vdash k\Downarrow\sigma'`, where $`k` is $`c;W` if $`B(b,\sigma)=\mathsf{true}` and $`\mathsf{skip}` otherwise.
3. From a derivation of $`\sigma\vdash(c;W)\Downarrow\sigma'`, [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3) gives a state $`\sigma_1` with $`\sigma\vdash c\Downarrow\sigma_1` and $`\sigma_1\vdash W\Downarrow\sigma'`.
4. A derivation of $`\sigma\vdash\mathsf{skip}\Downarrow\sigma'` ends with the skip rule, so $`\sigma'=\sigma`.

*Theorem 7.3 (Loop unfolding).* For every guard $`b`, command $`c` and states $`\sigma,\sigma'`,

$$`\sigma\vdash W\Downarrow\sigma'\quad\Longleftrightarrow\quad \sigma\vdash U\Downarrow\sigma'.`

Hence $`W\equiv U`.

*Proof of the forward direction.* As in Session 1, $`D:J` means that $`D` is a derivation of the judgment $`J`. We must show: if $`D:\sigma\vdash W\Downarrow\sigma'`, then $`\sigma\vdash U\Downarrow\sigma'`. The proof is by cases on the last rule of $`D`, with no induction. By fact 1 there are two cases.

*Iteration case.* Suppose $`D` ends with the loop iteration rule. Then $`D` has the form

$$`D:\quad\frac{B(b,\sigma)=\mathsf{true}\qquad D_1:\sigma\vdash c\Downarrow\sigma_1\qquad D_2:\sigma_1\vdash W\Downarrow\sigma'}{\sigma\vdash W\Downarrow\sigma'}`

1. The premises of the last rule of $`D` give $`B(b,\sigma)=\mathsf{true}`, a state $`\sigma_1`, and derivations $`D_1:\sigma\vdash c\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash W\Downarrow\sigma'`.
2. Apply the sequence rule to $`D_1` and $`D_2`. This gives $`\sigma\vdash(c;W)\Downarrow\sigma'`.
3. Apply the derived rule for a true guard to $`B(b,\sigma)=\mathsf{true}` and the derivation of step 2. This gives $`\sigma\vdash U\Downarrow\sigma'`.

The new derivation is

$$`\frac{B(b,\sigma)=\mathsf{true}\qquad\dfrac{D_1:\sigma\vdash c\Downarrow\sigma_1\qquad D_2:\sigma_1\vdash W\Downarrow\sigma'}{\sigma\vdash(c;W)\Downarrow\sigma'}}{\sigma\vdash U\Downarrow\sigma'}`

Step 2 uses $`D_2` as it stands. No induction hypothesis about $`D_2` is needed, because $`D_2` is moved, not transformed.

*Exit case.* Suppose $`D` ends with the loop exit rule.

1. The side condition and the conclusion of that rule give $`B(b,\sigma)=\mathsf{false}` and $`\sigma'=\sigma`.
2. The skip rule gives $`\sigma\vdash\mathsf{skip}\Downarrow\sigma`.
3. Apply the derived rule for a false guard to $`B(b,\sigma)=\mathsf{false}` and the derivation of step 2. This gives $`\sigma\vdash U\Downarrow\sigma`, that is, $`\sigma\vdash U\Downarrow\sigma'`.

*Proof of the reverse direction.* Let $`E:\sigma\vdash U\Downarrow\sigma'`. By fact 2, $`E` ends with the conditional rule and has a premise $`E_1:\sigma\vdash k\Downarrow\sigma'`. If $`B(b,\sigma)=\mathsf{true}`, then $`k` is $`c;W`. Fact 3 gives a state $`\sigma_1` with $`\sigma\vdash c\Downarrow\sigma_1` and $`\sigma_1\vdash W\Downarrow\sigma'`. Together with $`B(b,\sigma)=\mathsf{true}` these are the three premises of the loop iteration rule, which gives $`\sigma\vdash W\Downarrow\sigma'`. If $`B(b,\sigma)=\mathsf{false}`, then $`k` is skip, and fact 4 gives $`\sigma'=\sigma`. The loop exit rule gives $`\sigma\vdash W\Downarrow\sigma`, that is, $`\sigma\vdash W\Downarrow\sigma'`.

Both directions hold for all $`\sigma` and $`\sigma'`. So $`\mathrm{Exec}(W)=\mathrm{Exec}(U)`, and $`W\equiv U`. $`\square`

The theorem has no termination hypothesis. Take $`b` to be true and $`c` to be skip. By [Session 2, §2.4](chapter-02/index.html#ch02-s4), $`W` has no terminating execution from any state. By the reverse direction neither has $`U`, since a derivation for $`U` would yield one for $`W`. Both sets of pairs are empty, hence equal.

Compare the loop iteration case of [Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2). There the loop premise had to be compared with a second derivation, and that required an induction hypothesis for it. Here the loop premise is only moved. The unfolding must keep the loop: replacing $`c;W` by $`c` alone gives a command that is not equivalent to $`W` (Exercise 7.2).

# Replacement before a suffix
%%%
tag := "ch07-s3"
%%%

An unfolded loop usually sits inside a larger program. Take the loop of §7.2 followed by `y := x`, for a name $`y\neq x`. From $`\sigma(x)=0` the loop ends in $`\sigma_1=\sigma[x\mapsto1]`, and the suffix ends in $`\sigma_1[y\mapsto1]`. By Theorem 7.3 the unfolding $`U` also ends in $`\sigma_1` from $`\sigma`. The same suffix derivation from $`\sigma_1` then completes a run of $`U` followed by `y := x`. The next proposition does this for every initial state and every suffix.

*Proposition 7.4 (Replacement before a suffix).* For all commands $`c,d,a`, if $`c\equiv d` then $`(c;a)\equiv(d;a)`.

*Proof.* Fix $`\sigma,\sigma'` and suppose $`\sigma\vdash(c;a)\Downarrow\sigma'`. [Session 2, Proposition 2.2](chapter-02/index.html#ch02-s3) gives a state $`\sigma_1` with $`\sigma\vdash c\Downarrow\sigma_1` and $`\sigma_1\vdash a\Downarrow\sigma'`. Since $`c\equiv d`, also $`\sigma\vdash d\Downarrow\sigma_1`. The sequence rule, applied to this derivation and the given derivation of $`\sigma_1\vdash a\Downarrow\sigma'`, gives $`\sigma\vdash(d;a)\Downarrow\sigma'`. The converse is the same argument with $`c` and $`d` exchanged, which is allowed because $`\equiv` is symmetric. $`\square`

With Theorem 7.3 this gives $`(W;a)\equiv(U;a)` for every command $`a`.

The proof hands the entire intermediate state $`\sigma_1` to the suffix. This is why Definition 7.1 observes the entire final state. Suppose instead that we observed only the final value of one name $`x`. For a name $`y\neq x`, the commands `y := 1` and `y := 2` would then count as equivalent, since both leave $`x` unchanged. The suffix `x := y` separates them: it leaves 1 in $`x` after the first and 2 after the second. With that weaker observation Proposition 7.4 would fail. Session 20 observes only a chosen set of names. Its theorem then compares runs from two states that agree on a computed set of names, not on all names.

# Exercises
%%%
tag := "ch07-s4"
number := false
%%%

*7.1.* Prove $`((c_1;c_2);c_3)\equiv(c_1;(c_2;c_3))`. Name both intermediate states, $`\sigma_1` and $`\sigma_2`.

*7.2.* Refute $`(\mathsf{while}\ b\ \mathsf{do}\ c)\equiv(\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ \mathsf{skip})`. Give a guard, a body and an initial state from which both commands terminate, and compute both final states.

*7.3.* Suppose the language had an output command. One loop emits an output and then runs forever. Another runs forever without output. Does Definition 7.1 distinguish them? What additional observation would?

*7.4.* Prove $`(\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ c)\equiv c`. Which property of the single conditional rule makes each direction one step?

*Further problem.* Decide whether $`\mathsf{if}\ b\ \mathsf{then}\ (c;a)\ \mathsf{else}\ (d;a)` and $`(\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d);a` are equivalent for all commands. Then examine the counterpart that moves a common *prefix* out of the branches: compare $`\mathsf{if}\ b\ \mathsf{then}\ (a;c)\ \mathsf{else}\ (a;d)` with $`a;(\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d)`. Give a sufficient condition on $`a` and $`b`, and a counterexample when it fails.

# Reading for the Seminar
%%%
tag := "ch07-s5"
number := false
%%%

*Definitions · 10 minutes.* Write $`W` and $`U`, and state Theorem 7.3 with both state quantifiers explicit. Say what Definition 7.1 does not observe, using the example that opens §7.1.

*Joint proof · 30 minutes.* The presenter proves the forward direction of Theorem 7.3: the iteration case, then the exit case. A participant proves the reverse direction for a true guard by inverting the conditional rule and then the sequence. Finish by using Theorem 7.3 and Proposition 7.4 to replace a loop inside a sequence.

*Proof review · 20 minutes.* Run the forward proof for the candidate of Exercise 7.2 and locate the step that fails. Ask which property of $`D_2` the proof never used.

*Facilitator’s hint.* Underline the recursive loop judgment already available as a premise. Ask where exactly that same judgment belongs in the target tree.

# Solutions and Further Reading
%%%
tag := "ch07-s6"
number := false
%%%

*7.1.* Let $`\sigma\vdash((c_1;c_2);c_3)\Downarrow\sigma'`. Session 2, Proposition 2.2, applied twice, gives states $`\sigma_1,\sigma_2` with $`\sigma\vdash c_1\Downarrow\sigma_1`, $`\sigma_1\vdash c_2\Downarrow\sigma_2` and $`\sigma_2\vdash c_3\Downarrow\sigma'`. The sequence rule applied to the last two gives $`\sigma_1\vdash(c_2;c_3)\Downarrow\sigma'`. The sequence rule applied to the first and this one gives $`\sigma\vdash(c_1;(c_2;c_3))\Downarrow\sigma'`. The converse regroups the same three derivations. Nipkow and Klein prove this as Lemma 7.2 (_Concrete Semantics_, §7.2.3). Session 8 proves the same law for a semantics that assigns a function to each command.

*7.2.* Take the guard `x < 2`, the body `x := x + 1` and $`\sigma(x)=0`. The conditional runs the body once and ends with 1 in $`x`. The loop runs the body twice, exits, and ends with 2 in $`x`. All other names keep their values in both.

*7.3.* Neither command has a terminating execution. Both sets of pairs are empty, so Definition 7.1 identifies them. An observation that records the outputs produced so far, also on runs that do not terminate, separates them. When a language gains output, the choice of observation must be revisited.

*7.4.* The premise of the conditional rule is $`\sigma\vdash k\Downarrow\sigma'`, where $`k` is the branch selected by $`B(b,\sigma)`. Both branches are $`c`, so $`k=c` whatever the guard. Inverting the conditional rule gives $`\sigma\vdash c\Downarrow\sigma'`. Conversely, the conditional rule turns $`\sigma\vdash c\Downarrow\sigma'` into an execution of the conditional. Nipkow and Klein state this as Lemma 7.4. With their two conditional rules, the proof splits on the value of the guard.

*Further problem.* Fix $`\sigma`. Both commands test $`b` in $`\sigma`. If $`B(b,\sigma)=\mathsf{true}`, a terminating execution of either command consists of a run of $`c` from $`\sigma` to some $`\sigma_1` and a run of $`a` from $`\sigma_1`; inverting the conditional rule and Session 2, Proposition 2.2 expose them. The same two derivations, regrouped, give an execution of the other command. A false guard gives the same argument with $`d`. So the two commands are equivalent.

For the prefix version it suffices that $`a` preserves the guard: whenever $`\sigma\vdash a\Downarrow\sigma_1`, $`B(b,\sigma_1)=B(b,\sigma)`. Both commands then run $`a` from $`\sigma` to the same $`\sigma_1` and select the same branch. If $`a` has no terminating execution from $`\sigma`, neither command has one. For a counterexample take the guard `x = 0`, the prefix `x := 1`, and the branches `y := 1` and `y := 2`, with $`x\neq y`. From $`\sigma(x)=0` the first command ends with 1 in $`y` and the second with 2 in $`y`.

*Further reading · The small-step view.* In the transitions of [A.6](imp-card/index.html#imp-a6), if $`B(b,\sigma)=\mathsf{true}` then $`\langle W,\sigma\rangle\to\langle c;W,\sigma\rangle` and, by the conditional step, $`\langle U,\sigma\rangle\to\langle c;W,\sigma\rangle`. If the guard is false, both configurations step to $`\langle\mathsf{skip},\sigma\rangle`. Inversion shows that each has exactly this one transition. Neither $`W` nor $`U` is skip, so a finite path from either to $`\langle\mathsf{skip},\sigma'\rangle` begins with that transition and continues from the same configuration. Hence $`\langle W,\sigma\rangle\to^*\langle\mathsf{skip},\sigma'\rangle` exactly when $`\langle U,\sigma\rangle\to^*\langle\mathsf{skip},\sigma'\rangle`, and the paths have equal length. Session 6, Theorem 6.2 turns this into a second proof of Theorem 7.3. The small-step loop rule is itself one loop unfolding. Example 7.2, by contrast, relates two commands whose paths have different lengths.

*Further reading · Replacement inside a loop.* Let $`c\equiv c'` and $`W'=\mathsf{while}\ b\ \mathsf{do}\ c'`. Then $`W\equiv W'`. A loop may run its body many times, so the hypothesis must be used at every iteration. For $`D:\sigma\vdash W\Downarrow\sigma'` prove $`P(D)\coloneqq \sigma\vdash W'\Downarrow\sigma'` by induction on the height of $`D` (Session 3, §3.1). If $`D` ends with the loop exit rule, then $`B(b,\sigma)=\mathsf{false}` and $`\sigma'=\sigma`, and the loop exit rule for $`W'` uses the same guard. If $`D` ends with the loop iteration rule, its premises are $`B(b,\sigma)=\mathsf{true}`, $`D_1:\sigma\vdash c\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash W\Downarrow\sigma'`, with hypothesis $`P(D_2):\sigma_1\vdash W'\Downarrow\sigma'`. From $`D_1` and $`c\equiv c'` we get $`\sigma\vdash c'\Downarrow\sigma_1`, and the loop iteration rule gives $`\sigma\vdash W'\Downarrow\sigma'`. Exchange $`c` and $`c'` for the converse. Unlike in Theorem 7.3, the loop premise $`D_2` must be transformed, and the induction hypothesis does that. The state passed to each guard test is the same on both sides, while the derivations of the bodies may differ. Nipkow and Klein state this as Lemma 7.5 and derive it from their Lemma 7.6, which they prove by rule induction. With Proposition 7.4 and similar arguments for the right operand of a sequence and for the branches of a conditional, induction on the surrounding command shows that replacing a subcommand by an equivalent one gives an equivalent command. Nipkow and Klein call $`\equiv` a congruence for this reason.

*Further reading · Repeated unfolding.* Theorem 7.3 applies again to the copy of $`W` inside $`U`. With the replacement property just described, $`W\equiv\mathsf{if}\ b\ \mathsf{then}\ (c;U)\ \mathsf{else}\ \mathsf{skip}`. Each copy of the guard is tested in its own state. For the loop of §7.2 from $`\sigma(x)=0`, the first test reads $`\sigma`, where `x < 1` holds, and the second reads $`\sigma_1=\sigma[x\mapsto1]`, where it fails. The result is $`\sigma_1`. Evaluating both tests in $`\sigma` instead would run the body twice and end with 2 in $`x`.

*Further reading · Observing one name at a time.* Fix a name $`r`. For a command $`c`, a state $`\sigma` and a name $`y`, let $`O(c,\sigma,y)` be the set of values that $`c;(r:=y)` can leave in $`r` when started in $`\sigma`. Session 2, Proposition 2.2 and the assignment rule give $`O(c,\sigma,y)=\{\sigma'(y)\mid \sigma\vdash c\Downarrow\sigma'\}`. In IMP, $`c\equiv d` holds exactly when $`O(c,\sigma,y)=O(d,\sigma,y)` for all $`\sigma` and $`y`. One direction follows from the formula. For the other, let $`\sigma\vdash c\Downarrow\sigma'`. Then $`O(c,\sigma,y)` is not empty, so $`d` has a terminating execution from $`\sigma`, say to $`\sigma''`. By determinacy, $`O(c,\sigma,y)=\{\sigma'(y)\}` and $`O(d,\sigma,y)=\{\sigma''(y)\}` for every $`y`. So $`\sigma'(y)=\sigma''(y)` at every name, and $`\sigma'=\sigma''`. Determinacy is needed. Add the choice command of Session 3, Exercise 3.2. One command sets the pair of values at $`x,y` to $`(0,0)` or to $`(1,1)`; another sets it to $`(0,1)` or to $`(1,0)`. Each name alone shows the values 0 and 1 after either command, yet only the first can end with equal values at $`x` and $`y`. The step that fails is fixing one final state $`\sigma''` for all names $`y`.

Nipkow and Klein define the same equivalence of commands and state Lemmas 7.3–7.6 and 7.8 in _Concrete Semantics_, §7.2.4, pp. 82–83. Exercises 7.5 and 7.6 of that chapter (p. 93) ask for further equivalences of conditionals and loops. [Concrete Semantics, §7.2.4](https://concrete-semantics.org/concrete-semantics.pdf#page=92)

# Sources and Formalization
%%%
tag := "ch07-notes"
number := false
%%%

The execution rules follow Leroy’s IMP, as presented in A.5. Nipkow and Klein state the same unfolding for their IMP, whose conditional has two rules, with the same definition of equivalence. [Source and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics, §7.2.4, p. 82](https://concrete-semantics.org/concrete-semantics.pdf#page=92)

* *Theorem 7.3.* Formulated in this book. Corresponds to CS Lemma 7.3. Checked in Lean ([`loopUnfolding`](lean/Equivalence.html#loopUnfolding) · [IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 7.4.* Formulated in this book. Checked in Lean ([`equivalentBeforeSuffix`](lean/Equivalence.html#equivalentBeforeSuffix) · [IMP card references](imp-card/index.html#imp-sources)).
