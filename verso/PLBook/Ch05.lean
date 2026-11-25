import VersoManual
import PLBook.IMP.Paths

open Verso.Genre Manual

#doc (Manual) "Transitions and Infinite Paths" =>
%%%
tag := "ch05"
file := "chapter-05"
%%%

A debugger can stop between the two assignments of a sequence. At the stopping point there is a current store and a remaining command. The one-step rules describe which pair may come next. It can describe a computation even when there is no final store. Rules of this kind form a small-step semantics, in contrast with the big-step semantics of Session 2, Definition 2.1, whose judgment relates a command directly to its final store.

*In this session.*

* *Definitions.* Commands, guard values, store update and terminating execution (Sessions 1–2, Definitions 1.2–1.3 and 2.1). [IMP language card A.6](imp-card/index.html#imp-a6)
* *New terms.* Configuration, transition, finite path, progress, infinite path. [Glossary](glossary/index.html)
* *Lemma 5.3 (Progress of commands) and Example 5.5 (An infinite path indexed by the natural numbers).* For every command $`c` and store $`s`, either $`c=\mathsf{skip}` or there are $`d,t` with $`\langle c,s\rangle\to\langle d,t\rangle`. For every store $`s`, an infinite path starts at $`\langle\mathsf{while\ true\ do\ skip},s\rangle`.
* *Board case.* Progress for $`c_1;c_2`. Inspect the left command $`c_1`. Exhibit a successor both when $`c_1` is skip and when it takes a step.
* *Proof outline.* Induct on the command, quantifying over its input store. To exhibit an infinite path from `while true do skip`, give a configuration at every natural index and check both kinds of adjacent edge.
* *From Session 4.* Sessions 2–4 described a computation by a finite tree, or computed its result by recursion on a finite tree. Here a computation is a sequence of configurations, and the sequence need not end. For `while true do skip`, the least-height argument of Session 2, §2.4 excluded a terminating derivation. Here two explicit transitions supply a witness for its infinite path.

# The step relation
%%%
tag := "ch05-s1"
%%%

*Definition 5.1 (The step relation).* A *configuration* $`\langle c,s\rangle` consists of a residual command $`c` (the work still to do) and the current store $`s`. Write $`p\to q` for one transition. Assignment evaluates its right-hand side in the current store and steps to skip with the updated store.

$$`\frac{}{\langle x:=e,s\rangle\to\langle\mathsf{skip},s[x\mapsto\mathrm{eval}(e,s)]\rangle}`

A sequence with skip on the left steps to its right command. A step of its left command lifts through the sequence, carrying the resulting store with it.

$$`\frac{}{\langle \mathsf{skip};d,s\rangle\to\langle d,s\rangle}
\qquad\frac{\langle c,s\rangle\to\langle c',t\rangle}{\langle c;d,s\rangle\to\langle c';d,t\rangle}`

For $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`, let $`k` be the branch selected by $`B(b,s)` as in Session 2, Definition 2.1. For $`W=\mathsf{while}\ b\ \mathsf{do}\ c`, a false guard exits and a true guard exposes the body.

$$`\frac{}{\langle I,s\rangle\to\langle k,s\rangle}\qquad
\frac{B(b,s)=\mathsf{false}}{\langle W,s\rangle\to\langle\mathsf{skip},s\rangle}\qquad
\frac{B(b,s)=\mathsf{true}}{\langle W,s\rangle\to\langle c;W,s\rangle}`

Skip itself has no outgoing step. We refer to the six rules as the small-step assignment rule, the skip-discarding rule, the lifting rule, and the small-step conditional, loop exit and loop iteration rules.

The lifting rule lifts a step of the left operand into a sequence. There is no rule taking an arbitrary step of the right operand while the left operand is pending. The small-step loop iteration rule installs a fresh copy of the body before the next guard test. Some textbooks instead unfold the loop to a conditional in one unconditional step. The choice changes trace lengths, so a proof that counts steps must use one convention consistently.

The syntax of a residual command determines where to search for its next instruction. For `(c1; c2); d`, inspect the left child `c1; c2`. If `c1` can step, its step is first lifted through the inner sequence and then through the outer one. These two applications of the lifting rule derive a *single* transition of the whole command. If `c1` is skip, the inner sequence may instead discard it. The enclosing sequence lifts that transition once. In neither case is the rightmost command inspected. The number of rule applications used to *justify* a step can therefore exceed one even when the number of executed steps is exactly one.

# Finite paths and termination
%%%
tag := "ch05-s2"
%%%

A finite path $`p\to^*q` either takes zero steps with $`p=q`, or has a first step $`p\to r` and a finite tail $`r\to^*q`. Write $`p\to^n q` when there are configurations $`p_0,\ldots,p_n` with $`p_0=p`, $`p_n=q` and $`p_i\to p_{i+1}` for every $`0\le i<n`. The natural number $`n` counts edges.

Length zero gives reflexivity. Concatenation adds path lengths and gives transitivity. Termination from $`\langle c,s\rangle` with result $`t` means $`\langle c,s\rangle\to^*\langle\mathsf{skip},t\rangle`.

*Example 5.2.* Let $`a` abbreviate `x := 2`, $`d` abbreviate `y := x`, with $`x \neq y`, and put $`m = s\left\lbrack {x\mapsto 2} \right\rbrack`, $`t = m\left\lbrack {y\mapsto 2} \right\rbrack`. The complete path is

$$`\left\langle {a\ \text{;}\ d,s} \right\rangle\rightarrow\left\langle {\mathsf{skip}\text{;}\ d,m} \right\rangle\rightarrow\left\langle {d,m} \right\rangle\rightarrow\left\langle {\mathsf{skip},t} \right\rangle.`

The middle step changes the remaining syntax and leaves the store unchanged. A finite prefix that stops at $`\left\langle {d,m} \right\rangle` has yet to execute the second assignment.

*Lemma 5.3 (Progress of commands).* For every command and store, either the command is skip or the configuration can step. In particular, a non-skip command always has a successor.

*Proof.* Use structural induction with the property

$$`P(c)\coloneqq\forall s,\quad c=\mathsf{skip}\ \lor\ \exists d,t,\ \langle c,s\rangle\to\langle d,t\rangle.`

1. Suppose $`c=c_1;c_2` and fix $`s`. Since $`c_1;c_2\neq\mathsf{skip}`, we must show the second alternative: $`\exists d,t,\ \langle c_1;c_2,s\rangle\to\langle d,t\rangle`. The two child hypotheses are $`P(c_1)` and $`P(c_2)`. Use $`P(c_1)` at $`s`.
2. If $`c_1=\mathsf{skip}`, the skip-discarding rule gives $`\langle\mathsf{skip};c_2,s\rangle\to\langle c_2,s\rangle`. Take $`c_2,s` as the witnesses.
3. Otherwise $`P(c_1)` at $`s` supplies $`c_1',t` with $`\langle c_1,s\rangle\to\langle c_1',t\rangle`. The lifting rule gives $`\langle c_1;c_2,s\rangle\to\langle c_1';c_2,t\rangle`. Take $`c_1';c_2,t` as the witnesses. Neither case requires a step of $`c_2`.

For skip the equality in the first alternative holds. An assignment can step by the first rule. For a conditional, the single rule steps to the selected branch. For a loop, evaluation of the guard gives either the exit edge or the edge exposing the body. This completes the cases. $`\square`

An irreducible configuration has no successor. An irreducible configuration with a residual command other than skip would be *stuck*. The lemma excludes stuck configurations for this grammar. Extending the language with a partial expression such as integer division would require a decision about division by zero and a new progress argument.

For a one-edge example, an assignment steps directly to skip. Its two endpoint configurations form a sequence with two entries. The following lemma relates the two path notations even when no length is given.

*Lemma 5.4 (Length of a finite path).* For all configurations $`p,q`, $`p\to^*q\iff\exists n\in\mathbb N,\ p\to^n q`.

*Proof.* For the forward implication induct on the finite-path derivation $`D:p\to^*q`, with $`P(D)\coloneqq\exists n,\ p\to^n q`. In the zero-step case take $`n=0`. In the step case the tail hypothesis gives $`r\to^j q` for some $`j`. Put the first edge $`p\to r` before that sequence to obtain $`p\to^{j+1}q`. For the converse, induct on $`n` with property $`Q(n)\coloneqq\forall p,q,\ (p\to^n q)\Rightarrow(p\to^*q)`. At zero the endpoints agree. At $`j+1` remove the first edge. Apply $`Q(j)` to the remaining sequence from $`r` to $`q` and reattach $`p\to r` by the finite-path step rule. $`\square`

There are two different closures in common use. Allowing zero steps means that skip terminates from every store even though it has no successor. Requiring at least one step would omit precisely such zero-length runs. A nonempty path may also return to its starting point if the transition system has a cycle. Therefore testing whether endpoints differ cannot decide which closure a given piece of evidence inhabits. One must retain the length or at least a first edge.

For a concrete use of concatenation, suppose a path takes a conditional with a true guard to its then branch in one step, and a second path runs that branch to skip in three steps. Their join is valid only when the first store and residual at the cut match the starting store and residual of the second path. Removing one of the two copies of the cut configuration leaves five configurations and four edges. Cutting the resulting path after its second edge is equally legitimate, but the new cut point might fall *inside* an assignment sequence. Path decomposition is determined by a chosen position; decomposing a big-step derivation instead follows its last rule.

# Infinite paths
%%%
tag := "ch05-s3"
%%%

An *infinite path* from $`p` is witnessed by a function $`f` from natural numbers to configurations with $`f(0)=p` and $`f(i)\to f(i+1)` for every $`i`. The coinductive presentation uses a predicate on configurations: the greatest predicate $`X`, under inclusion, satisfying $`X(p)\iff\exists q,\ p\to q\land X(q)`.

*Example 5.5 (An infinite path indexed by the natural numbers).* Fix any store $`s` and let $`W` be `while true do skip`. Put $`p=\langle W,s\rangle` and $`p'=\langle\mathsf{skip};W,s\rangle`. The small-step loop iteration rule gives $`p\to p'`. The skip-discarding rule gives $`p'\to p`. Set $`f(2i)=p` and $`f(2i+1)=p'`. At an even index the required edge is $`p\to p'`; at an odd index the next index is $`2(i+1)`, giving $`p'\to p`. Thus the function supplies every required edge, starting at $`p`.

The function gives the configuration at an index of our choice. With the predicate presentation we can instead exhibit a set closed under taking some next step: each member of $`\{p,p'\}` has a successor in that set. To see why this suffices, take the union $`U` of all sets with this property. Every member of $`U` has a successor in $`U`. Conversely, if $`p` has a successor in $`U`, adjoining $`p` to $`U` preserves the property, so $`p` already belongs to $`U`. Thus $`U` satisfies the displayed equation and contains every other solution. In particular both configurations satisfy the coinductive predicate.

A run can also be infinite without repeating a configuration. In `while true do x := x + 1`, start with $`s(x)=0`. Each return to the loop has a larger value of $`x`. A configuration diverges when an infinite path starts at it: a successor must be available at every index. Revisiting an identical configuration is a sufficient witness here, and is unnecessary in the definition.

# Exercises
%%%
tag := "ch05-s4"
number := false
%%%

*5.1.* How many steps does `if true then skip else x := 1` take to terminate? Compare with skip using our definition of termination.

*5.2.* Show that a positive-length path starting at $`\left\langle {\mathsf{skip},s} \right\rangle` is impossible. Decide whether the finite-path relation $`\to^*` nevertheless relates that configuration to itself.

*5.3.* For the always-incrementing loop starting at $`s(x)=0`, write its configuration at times $`3i`, $`3i + 1`, and $`3i + 2` to construct an infinite path.

*Further problem.* Extend the command syntax with `abort`, a command with no outgoing step, keeping skip as the sole successful result. Starting from `(x := 1); abort`, exhibit a maximal finite path. Which lemma in this chapter fails? Can one conclude that an execution is infinite merely because it cannot reach skip?

# Reading for the Seminar
%%%
tag := "ch05-s5"
number := false
%%%

*Definitions · 10 minutes.* Mark the command, store, and one-step arrow on the three-step sequence in §5.2.

*Joint proof · 30 minutes.* Prove the sequence case of progress, then construct the infinite path in §5.3. Have participants state the domain of the witness function and justify every even and odd edge.

*Proof review · 20 minutes.* Try the construction on the incrementing loop. Use progress to explain why a stuck configuration and an infinite path would represent distinct phenomena in an extended language.

*Facilitator’s hint.* After one true loop step the residual command is a sequence. Consult the leftmost command before choosing the next rule.

# Solutions and Further Reading
%%%
tag := "ch05-s6"
number := false
%%%

*5.1.* The conditional takes one step to $`\left\langle {\mathsf{skip},s} \right\rangle`, while skip already terminates by a zero-length path. Both have final store $`s`.

*5.2.* A positive-length path has a first edge. No conclusion of Definition 5.1 starts with skip. The zero-edge path still proves reflexivity.

*5.3.* Define $`s_{i}` by $`s_{i}(x) = i` and let it agree with the initial store elsewhere. With body $`a` and loop $`W`, the three configurations are $`\left\langle {W,s_{i}} \right\rangle`, $`\left\langle {a\ \text{;}\ W,s_{i}} \right\rangle`, and $`\left\langle {\mathsf{skip}\text{;}\ W,s_{i + 1}} \right\rangle`. Discarding skip returns to $`\left\langle {W,s_{i + 1}} \right\rangle`. These edges justify the witness at every index.

See Reynolds, §6.2, for a comparison of transition rules. [Reynolds, chapter 6](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

*Further problem.* At an arbitrary initial store `s`, the first edge lifts the assignment step and reaches `⟨skip; abort, s[x ↦ 1]⟩`. The next edge discards the leading skip, reaching `⟨abort, s[x ↦ 1]⟩`. This path is maximal, meaning that no further edge can extend it. In particular its last store is well defined, but the residual command is different from the designated successful final command. Recording only the last store of any maximal finite path would mistake this outcome for successful return.

The progress lemma fails already at `⟨abort,s⟩`, which is neither at skip nor able to step. There is no infinite path from the displayed starting configuration: the first two edges are forced and a third is impossible. Thus failure to reach skip is compatible with a finite stuck execution in the extended transition system. One alternative design makes abort a designated exceptional outcome. That design would require separate definitions of successful and exceptional termination and a corresponding reformulation of progress.

*Further reading · Determinacy of a step.* The rules also give uniqueness of the successor for the given grammar. Induct on the command with property $`\forall s,p,q,\ (\langle c,s\rangle\to p)\land(\langle c,s\rangle\to q)\Rightarrow p=q`. Assignment has exactly the prescribed result. In a conditional the guard selects one branch. In a loop it determines which of the two rules applies. In a sequence with left skip, lifting would require an impossible step from skip. In a sequence with any other left command, discarding is impossible and the induction hypothesis identifies the lifted successor when one exists. Together with progress this gives one successor at every nonterminal configuration, a fact that will help relate negative and positive accounts of divergence.

For deterministic IMP we can strengthen the connection between the two observations. Suppose there is no finite path from a given configuration to skip. Its command cannot be skip, since a path of length zero would suffice. Progress supplies its next configuration. A finite path to skip from the successor would extend backwards across the chosen edge to give one from the initial configuration. Hence the same absence property holds at the successor. Iterating this argument defines the configuration at each natural index. Uniqueness of the successor makes the resulting infinite sequence independent of any selection among alternatives.

In the other direction assume an infinite sequence and a finite path to skip start at the same configuration. An induction on the finite length shows that both executions agree at every position up to its endpoint: the starts agree, and determinacy identifies their next configurations. The infinite sequence would consequently have to take a step from skip at the next index, contrary to the rules. This particular exclusion uses determinacy. In a nondeterministic language, the existence of an infinite path can coexist with a different, terminating execution from the same input.

An infinite path requires a successor even at its first index. Hence an irreducible configuration cannot start such a path.

# Sources and Formalization
%%%
tag := "ch05-notes"
number := false
%%%

The six transition rules and progress statement are from Leroy’s IMP. In _Concrete Semantics_ a configuration has no successor exactly when its command is skip. [Source and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics, §7.3](https://concrete-semantics.org/concrete-semantics.pdf)

* *Lemma 5.3.* Source: Leroy’s IMP, progress for commands. Corresponds to CS Lemma 7.17. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 5.4.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Example 5.5.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
