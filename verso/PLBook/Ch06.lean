import VersoManual
import PLBook.IMP.Paths

open Verso.Genre Manual

#doc (Manual) "Equivalence of Terminating Evaluations" =>
%%%
tag := "ch06"
file := "chapter-06"
%%%

* *Definitions.* Terminating execution (Session 2, Definition 2.1), transitions and finite paths (Session 5, Definition 5.1 and Lemma 5.4). [IMP language card A.5–A.6](imp-card/index.html#imp-a5)
* *New terms.* Sequence context, path lifting. [Glossary](glossary/index.html)
* *Theorem 6.2 (Equivalence of terminating evaluations).* For every command $`c` and stores $`s,t`, $`s\vdash c\Downarrow t` if and only if $`\langle c,s\rangle\to^*\langle\mathsf{skip},t\rangle`.
* *Source.* Leroy proves the two implications for these IMP rules, with Lemma 6.3 as the key step of the reverse implication. Nipkow and Klein prove the same endpoint equivalence for their transition rules. [Sources and proof declarations](imp-card/index.html#imp-sources) · [Concrete Semantics, §7.3.1](https://concrete-semantics.org/concrete-semantics.pdf)
* *Board case.* From an execution tree for $`c_1;c_2`, lift the path for $`c_1` through the suffix $`c_2`, discard the leading skip, and join the path for $`c_2`.
* *Proof outline.* From a tree, induct on the execution derivation. From a path ending at skip, induct on its length, using Lemma 6.3 to reconstruct the execution before the first edge.
* *From Session 5.* There we characterized termination by reaching skip. Here we compare that endpoint with the final store certified by a Session 2 execution tree.

Session 2 represents a terminating execution by a tree. Session 5 represents it by a path ending at skip. For a sequence, the tree has one child per operand, whereas the path keeps the second operand in its residual command while the first executes. Matching the two pictures requires a lemma about executing a command inside a larger one.

# Paths inside sequences
%%%
tag := "ch06-s1"
%%%

Use the judgments of Session 2, Definition 2.1 and Session 5, §5.2. A *sequence context* with suffix $`k` is the operation sending a residual $`c` to $`c;k`. The suffix stays fixed, including when $`c` changes. Applying this operation to every command along a path, with the stores unchanged, is called *path lifting*.

For a particularly small trace take the assignment `x := 2` from store `s` to skip at `m = s[x ↦ 2]`. Fix the suffix `y := x`. Lifting produces one transition of the combined command whose target is `skip; y := x` in store `m`. For distinct names `x` and `y`, at this point the proof still knows that `y` has its *old* value. No transition of the suffix was used in the lifted path. Only after the skip is removed does the next assignment read the already updated `x`.

*Lemma 6.1 (Lifting).* If $`\left\langle {c,s} \right\rangle\rightarrow^{n}\left\langle {c',t} \right\rangle`, then

$$`\left\langle {c\ \text{;}\ k,s} \right\rangle\rightarrow^{n}\left\langle {c'\ \text{;}\ k,t} \right\rangle.`

*Proof.* For each configuration along the path replace its command by the sequence with suffix $`k`. Each original edge becomes exactly one edge by the lifting rule of Session 5, Definition 5.1. For $`n = 0` the transformed endpoints agree. The construction preserves every intermediate store. $`\square`

In particular, when $`c' = \operatorname{skip}` the final configuration in the lifted path *still contains the suffix*. One further step goes from $`\left\langle {\operatorname{skip}\text{;}\ k,t} \right\rangle` to $`\left\langle {k,t} \right\rangle`. Forgetting this step gives path segments whose endpoints cannot be joined.

The construction respects concatenation. If a prefix computation has been split into two paths at some residual `c'` and store `m`, lifting the paths separately yields the same cut point `c'; k` at `m`. Concatenate there to obtain the lifted full path. This observation permits a reader to group steps at any convenient intermediate computation without having to rediscover the behavior of the suffix for each group. It also explains an asymmetry of the rules: Session 5, Definition 5.1 has no rule that lifts a step of the right command while the left command is unfinished, so the command that changes in a sequence context is always the left one.

# From execution trees to paths
%%%
tag := "ch06-s2"
%%%

*Theorem 6.2 (Equivalence of terminating evaluations).* For all $`c,s,t`, $`s \vdash c \Downarrow t` holds if and only if $`\left\langle {c,s} \right\rangle\rightarrow^{*}\left\langle {\operatorname{skip},t} \right\rangle`.

For the forward direction, induct on the given execution derivation. For $`D:s\vdash c\Downarrow t` the induction property is

$$`P(D)\coloneqq\langle c,s\rangle\to^*\langle\mathsf{skip},t\rangle.`

At skip take a zero-edge path. At assignment take one update step. At a conditional take the selected branch step and append the path given by the branch hypothesis.

*Sequence case.*

1. We must show $`P(D):\langle c_1;c_2,s\rangle\to^*\langle\mathsf{skip},t\rangle`. The last rule of $`D:s\vdash(c_1;c_2)\Downarrow t` supplies $`D_1:s\vdash c_1\Downarrow m` and $`D_2:m\vdash c_2\Downarrow t`. The hypotheses are $`P(D_1):\langle c_1,s\rangle\to^*\langle\mathsf{skip},m\rangle` and $`P(D_2):\langle c_2,m\rangle\to^*\langle\mathsf{skip},t\rangle`.
2. By Session 5, Lemma 5.4 choose lengths $`i,j` for these paths. Apply Lemma 6.1 to the first path with suffix $`c_2`. This reaches $`\langle\mathsf{skip};c_2,m\rangle` in $`i` steps.
3. Discard the leading skip. This takes one step to $`\langle c_2,m\rangle`, the precise starting configuration of the second hypothesis.
4. Append the second path. The resulting path is

$$`\langle c_1;c_2,s\rangle\to^i\langle\mathsf{skip};c_2,m\rangle
\to\langle c_2,m\rangle\to^j\langle\mathsf{skip},t\rangle.`

Its length is $`i+1+j`. Lemma 5.4 gives the required finite path. If $`c_1` is already skip, $`i=0` and the edge discarding skip remains necessary.

*Loop cases.* For a false guard take the exit edge to skip. For a true guard, write $`W` for the loop, $`a` for its body, and $`m` for the body’s result. The small-step loop iteration rule first goes to $`\left\langle {a\ \text{;}\ W,s} \right\rangle`. Lift the body hypothesis to that context, discard skip at $`m`, then append the recursive loop hypothesis from $`m`. The two hypotheses are $`\langle a,s\rangle\to^*\langle\mathsf{skip},m\rangle` and $`\langle W,m\rangle\to^*\langle\mathsf{skip},t\rangle`. Induction is legitimate because both hypotheses concern child derivations. This proves the forward direction.

For example use `while x < 1 do x := x + 1` at a store with `x = 0`. Write $`W` for this loop, $`a` for the assignment and $`m=s[x\mapsto1]`. The four edges are

$$`\langle W,s\rangle\to\langle a;W,s\rangle\to\langle\mathsf{skip};W,m\rangle
\to\langle W,m\rangle\to\langle\mathsf{skip},m\rangle.`

# From paths to execution trees
%%%
tag := "ch06-s3"
%%%

For the reverse direction, induct on path length. By Session 5, Lemma 5.4, each finite path has some length $`j`. The induction property is

$$`Q(j)\coloneqq\forall c,s,t,\quad
\langle c,s\rangle\to^j\langle\mathsf{skip},t\rangle\ \Longrightarrow\ s\vdash c\Downarrow t.`

To apply the hypothesis to a shorter path we need to extend its reconstructed execution backwards by one edge.

*Lemma 6.3 (Execution before one step).* If $`\left\langle {c,s} \right\rangle\rightarrow\left\langle {d,s'} \right\rangle` and $`s' \vdash d \Downarrow t` then $`s \vdash c \Downarrow t`.

*Proof.* Induct on the derivation of the step, allowing an arbitrary final store $`t`. For an edge from $`\langle c,s\rangle` to $`\langle d,s'\rangle` the property is $`\forall t,\ (s'\vdash d\Downarrow t)\Rightarrow(s\vdash c\Downarrow t)`. For assignment the residual command is skip, so inversion gives $`t = s'`. The assignment rule supplies the result. When a completed left skip is discarded, prepend a skip derivation by the sequence rule. At a conditional use the known test and branch derivation. At a false loop exit use inversion on skip and the loop exit rule.

At a true loop step the residual is body followed by loop. Invert its big-step sequence to recover the intermediate store, body derivation and loop derivation. Use exactly these as premises of the loop iteration rule.

Finally suppose the step was lifted: $`c=c_1;k`, $`d=c_1';k`, and the premise is $`\left\langle {c_1,s} \right\rangle\rightarrow\left\langle {c_1',s'} \right\rangle`. Invert the given execution of $`c_1'\ \text{;}\ k` to get $`s' \vdash c_1' \Downarrow m` and $`m \vdash k \Downarrow t` for some $`m`. The premise hypothesis is $`\forall t,\ (s'\vdash c_1'\Downarrow t)\Rightarrow(s\vdash c_1\Downarrow t)`. Apply it at $`m` to obtain $`s \vdash c_1 \Downarrow m`. Join that execution to the suffix at $`m`. These cases exhaust the small-step rules. $`\square`

To finish Theorem 6.2, at length zero the endpoints agree: $`c=\mathsf{skip}` and $`s=t`. The skip rule gives the required execution. At length $`j+1`, let the first edge reach $`\langle d,s'\rangle`. The tail has length $`j` and ends at $`\langle\mathsf{skip},t\rangle`. Apply $`Q(j)` to $`d,s',t` to obtain $`s'\vdash d\Downarrow t`. Lemma 6.3 then gives $`s\vdash c\Downarrow t`. $`\square`

Work backwards through the path just computed. At the last configuration the skip rule proves execution to the final store. The previous step came from a loop with a false guard. Inverting the execution of skip identifies its starting and final stores, so the loop exit rule proves the predecessor's execution. The preceding disposal of skip is reversed by building a sequence execution with the skip rule as its left child. At this stage we have a big-step tree for `skip; W` in the updated store. Reversing the lifted assignment step must convert this into a tree for `(x := x + 1); W` in the old store.

The two stores just mentioned are precisely why Lemma 6.3 is about configurations and an arbitrary *common* final store. Inverting the existing sequence tree gives a particular middle store. In this example its left skip forces that middle store to be the updated one. Attach the assignment rule ending there, preserve the right subtree, and rebuild the sequence. Finally use the initial true guard to reconstruct the loop iteration rule. Each backwards move constructs a new derivation with the same final target, and none requires an inverse to the store update performed by assignment.

# What the endpoints record
%%%
tag := "ch06-s4"
%%%

The theorem identifies the possible *terminating final stores*. It does not identify the height of a derivation with the length of a path. For two successive assignments, both leaves have height zero and the sequence tree has height one (Session 2, §2.4). The path has length three: the two writes and the disposal of skip. Nor does the theorem alone construct an infinite execution when there is no terminating one. Session 5 supplied an explicit infinite witness for a particular program.

The endpoint theorem can transport facts that are stated solely in terms of endpoints. For example consider two small-step paths from the same initial configuration to skip, ending respectively in stores `t` and `u`. The backwards implication gives two derivations for the same command and initial store. Determinacy from Session 3 yields `t = u`. This is an alternative proof of uniqueness of *terminal results*. It does not by itself imply uniqueness of the first small step. An alternative transition system could split into two routes that later rejoin. Both routes could have the same terminal store while the initial configuration had two successors.

# Exercises
%%%
tag := "ch06-s5"
number := false
%%%

*6.1.* Count the small steps for two assignments composed sequentially. Give the size of the corresponding big-step tree, counting rule applications.

*6.2.* In Lemma 6.3’s true loop case, write the three premises needed by the big-step rule, with their stores.

*6.3.* A proposed lifting lemma claims that $`\left\langle {a,s} \right\rangle\rightarrow^{n}\left\langle {\operatorname{skip},t} \right\rangle` implies $`\left\langle {a\ \text{;}\ k,s} \right\rangle\rightarrow^{n}\left\langle {k,t} \right\rangle`. Refute it at $`n = 0` and repair its statement.

*Further problem.* Replace the assignment transition by two transitions through a fresh residual command `pending(x,v)`. The first evaluates the expression in the current store and records its integer value `v`; the second writes `v` and goes to skip. For loop-free source commands, justify that this refinement preserves terminating final stores and calculate the change in path length.

# Reading for the Seminar
%%%
tag := "ch06-s6"
number := false
%%%

*Definitions · 10 minutes.* Draw a sequence tree with intermediate store $`m`. Beside it put two finite paths with lengths $`i,j`.

*Joint proof · 30 minutes.* Prove Lemma 6.1 (Lifting) for a path with two edges, then for every finite path. Ask a participant to connect the two paths of the sequence case and label the extra edge.

*Proof review · 20 minutes.* Reconstruct the reverse direction for a lifted step. Check the case of a zero-length path and state what the theorem establishes about endpoints.

*Facilitator’s hint.* Cover the suffix in one configuration, do the left step, and restore the suffix. Compare the last residual to the desired start of the second path.

# Solutions and Further Reading
%%%
tag := "ch06-s7"
number := false
%%%

*6.1.* Each assignment takes one edge. One more discards skip between them, giving three edges. The tree has two applications of the assignment rule and one of the sequence rule. Here both counts are three. For `skip; skip`, one edge suffices although the execution tree still has three rule applications.

*6.2.* At $`s` the guard holds, the body runs from $`s` to $`m`, and the loop runs from $`m` to $`t`. The guard comes from the step. Both execution derivations and $`m` come from inversion of the residual sequence.

*6.3.* Set $`a = \operatorname{skip}` and $`s = t`. A zero-edge path leaves $`\operatorname{skip}\text{;}\ k` syntactically unchanged. The valid conclusion reaches $`\operatorname{skip}\text{;}\ k` in $`n` edges or $`k` in $`n + 1` edges.

*Further problem.* An old assignment edge from `⟨x := e,s⟩` to skip with updated store is replaced by an edge to `⟨pending(x,eval(e,s)),s⟩` and another to the original endpoint. The new syntax is unavailable in source programs, and its only rule performs the pending update. Inside a sequence, lift the first edge and then the second through the same left-operand context. No rule permits an unrelated suffix to execute between them. Conditional selection and discarding skip retain their original edges.

Proceed along a terminating old path replacing exactly these assignment edges, including the ones lifted through enclosing sequences. In the other direction, every reachable occurrence of a pending command in the active position arose from the preceding expression evaluation and is forced to perform its write next. Group each such pair into one old edge. This gives the same two endpoints and establishes preservation in both directions. If the original path has length `i` and executes `j` assignments, the refined path has length `i + j`. Count the assignments in the chosen branches; syntactically present assignments in untaken branches contribute zero.

*Further reading · Counting steps.* The forward construction gives a cost recurrence in addition to an existence proof. Assign to a big-step derivation the length of the small-step path obtained by the construction. The length is zero for skip and one for assignment. For a conditional add one to the length of the selected branch. For a sequence add the lengths of the two child derivations and one step discarding skip. For an exiting loop charge one guard step. For an iterating loop charge a guard step, the body path, a step discarding skip, and the recursively constructed loop path. All these quantities are computed from *finite subderivations*, so the recurrence is well founded.

To make an intermediate observation meaningful, specify what a path exposes. Suppose every assignment printed its assigned integer. The programs `skip` and `x := x` preserve the same store if one erases outputs. An observer recording the printed numbers could distinguish them. Recovering equality of such observations from two semantics would require a big-step judgment carrying the corresponding outputs and a proof of a strengthened correspondence theorem. Matching stores at skip remains enough for the present theorem because its conclusion asks only about termination and the resulting store.

# Sources and Formalization
%%%
tag := "ch06-notes"
number := false
%%%

* *Lemma 6.1.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 6.2.* Source: Leroy’s IMP, correspondence between executions and transitions. Corresponds to CS Corollary 7.16. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 6.3.* Source: Leroy’s IMP, execution before a transition. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
