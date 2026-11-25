import VersoManual
import PLBook.IMP.Paths

open Verso.Genre Manual

#doc (Manual) "Equivalence of Terminating Executions" =>
%%%
tag := "ch06"
file := "chapter-06"
%%%

Session 2 represents a terminating execution by a tree. Session 5 represents it by a path ending at skip. For a sequence, the tree has one child per operand, whereas the path keeps the second operand in its residual command while the first executes. Matching the two pictures requires a lemma about executing a command inside a larger one.

*In this session.*

* *Definitions.* Terminating execution (Session 2, Definition 2.1), transitions and finite paths (Session 5, Definition 5.1 and Lemma 5.4). [IMP language card A.5–A.6](imp-card/index.html#imp-a5)
* *New terms.* Sequence context, path lifting. [Glossary](glossary/index.html)
* *Theorem 6.2 (Equivalence of terminating executions).* For every command $`c` and states $`\sigma,\sigma'`, $`\sigma\vdash c\Downarrow\sigma'` if and only if $`\langle c,\sigma\rangle\to^*\langle\mathsf{skip},\sigma'\rangle`.
* *Board case.* From an execution tree for $`c_1;c_2`, lift the path for $`c_1` through the suffix $`c_2`, discard the leading skip, and join the path for $`c_2`.
* *Proof outline.* From a tree, induct on the execution derivation. From a path ending at skip, induct on its length, using Lemma 6.3 to reconstruct the execution before the first edge.
* *From Session 5.* There we characterized termination by reaching skip. Here we compare that endpoint with the final state certified by a Session 2 execution tree.

# Paths inside sequences
%%%
tag := "ch06-s1"
%%%

Use the judgments of Session 2, Definition 2.1 and Session 5, §5.2. A *sequence context* with suffix $`k` is the operation sending a residual $`c` to $`c;k`. The suffix stays fixed, including when $`c` changes. In this session $`k` is an arbitrary command, not the branch selected by a guard as in A.5. Applying this operation to every command along a path, with the states unchanged, is called *path lifting*.

For a particularly small trace take the assignment `x := 2` from state `σ` to skip at `σ₁ = σ[x ↦ 2]`. Fix the suffix `y := x`. Lifting produces one transition of the combined command whose target is `skip; y := x` in state `σ₁`. For distinct names `x` and `y`, at this point the proof still knows that `y` has its *old* value. No transition of the suffix was used in the lifted path. Only after the skip is removed does the next assignment read the already updated `x`.

*Lemma 6.1 (Lifting).* If $`\left\langle {c,\sigma} \right\rangle\rightarrow^{n}\left\langle {c',\sigma'} \right\rangle`, then

$$`\left\langle {c\ \text{;}\ k,\sigma} \right\rangle\rightarrow^{n}\left\langle {c'\ \text{;}\ k,\sigma'} \right\rangle.`

*Proof.* For each configuration along the path replace its command by the sequence with suffix $`k`. Each original edge becomes exactly one edge by the lifting rule of Session 5, Definition 5.1. For $`n = 0` the transformed endpoints agree. The construction preserves every intermediate state. $`\square`

In particular, when $`c' = \mathsf{skip}` the final configuration in the lifted path *still contains the suffix*. One further step goes from $`\left\langle {\mathsf{skip}\text{;}\ k,\sigma'} \right\rangle` to $`\left\langle {k,\sigma'} \right\rangle`. Forgetting this step gives path segments whose endpoints cannot be joined.

The construction respects concatenation. If a prefix computation has been split into two paths at some residual `c'` and state `σ₁`, lifting the paths separately yields the same cut point `c'; k` at `σ₁`. Concatenate there to obtain the lifted full path. This observation permits a reader to group steps at any convenient intermediate computation without having to rediscover the behavior of the suffix for each group. It also explains an asymmetry of the rules: Session 5, Definition 5.1 has no rule that lifts a step of the right command while the left command is unfinished, so the command that changes in a sequence context is always the left one.

# From execution trees to paths
%%%
tag := "ch06-s2"
%%%

*Theorem 6.2 (Equivalence of terminating executions).* For all $`c,\sigma,\sigma'`, $`\sigma \vdash c \Downarrow \sigma'` holds if and only if $`\left\langle {c,\sigma} \right\rangle\rightarrow^{*}\left\langle {\mathsf{skip},\sigma'} \right\rangle`.

For the forward direction, induct on the given execution derivation. For $`D:\sigma\vdash c\Downarrow\sigma'` the induction property is

$$`P(D)\coloneqq\langle c,\sigma\rangle\to^*\langle\mathsf{skip},\sigma'\rangle.`

At skip take a zero-edge path. At assignment take one update step. At a conditional take the selected branch step and append the path given by the branch hypothesis.

*Sequence case.*

1. We must show $`P(D):\langle c_1;c_2,\sigma\rangle\to^*\langle\mathsf{skip},\sigma'\rangle`. The last rule of $`D:\sigma\vdash(c_1;c_2)\Downarrow\sigma'` supplies $`D_1:\sigma\vdash c_1\Downarrow\sigma_1` and $`D_2:\sigma_1\vdash c_2\Downarrow\sigma'`. The hypotheses are $`P(D_1):\langle c_1,\sigma\rangle\to^*\langle\mathsf{skip},\sigma_1\rangle` and $`P(D_2):\langle c_2,\sigma_1\rangle\to^*\langle\mathsf{skip},\sigma'\rangle`.
2. By Session 5, Lemma 5.4 choose lengths $`i,j` for these paths. Apply Lemma 6.1 to the first path with suffix $`c_2`. This reaches $`\langle\mathsf{skip};c_2,\sigma_1\rangle` in $`i` steps.
3. Discard the leading skip. This takes one step to $`\langle c_2,\sigma_1\rangle`, the precise starting configuration of the second hypothesis.
4. Append the second path. The resulting path is

$$`\langle c_1;c_2,\sigma\rangle\to^i\langle\mathsf{skip};c_2,\sigma_1\rangle
\to\langle c_2,\sigma_1\rangle\to^j\langle\mathsf{skip},\sigma'\rangle.`

Its length is $`i+1+j`. Lemma 5.4 gives the required finite path. If $`c_1` is already skip, $`i=0` and the edge discarding skip remains necessary.

*Loop cases.* For a false guard take the exit edge to skip. For a true guard, write $`W` for the loop, $`a` for its body, and $`\sigma_1` for the body’s result. The small-step loop iteration rule first goes to $`\left\langle {a\ \text{;}\ W,\sigma} \right\rangle`. Lift the body hypothesis to that context, discard skip at $`\sigma_1`, then append the recursive loop hypothesis from $`\sigma_1`. The two hypotheses are $`\langle a,\sigma\rangle\to^*\langle\mathsf{skip},\sigma_1\rangle` and $`\langle W,\sigma_1\rangle\to^*\langle\mathsf{skip},\sigma'\rangle`. Induction is legitimate because both hypotheses concern child derivations. This proves the forward direction.

For example use `while x < 1 do x := x + 1` at a state with `x = 0`. Write $`W` for this loop, $`a` for the assignment and $`\sigma_1=\sigma[x\mapsto1]`. The four edges are

$$`\langle W,\sigma\rangle\to\langle a;W,\sigma\rangle\to\langle\mathsf{skip};W,\sigma_1\rangle
\to\langle W,\sigma_1\rangle\to\langle\mathsf{skip},\sigma_1\rangle.`

# From paths to execution trees
%%%
tag := "ch06-s3"
%%%

For the reverse direction, induct on path length. By Session 5, Lemma 5.4, each finite path has some length $`j`. The induction property is

$$`Q(j)\coloneqq\forall c,\sigma,\sigma',\quad
\langle c,\sigma\rangle\to^j\langle\mathsf{skip},\sigma'\rangle\ \Longrightarrow\ \sigma\vdash c\Downarrow\sigma'.`

To apply the hypothesis to a shorter path we need to extend its reconstructed execution backwards by one edge.

*Lemma 6.3 (Execution before one step).* If $`\left\langle {c,\sigma} \right\rangle\rightarrow\left\langle {d,\sigma_1} \right\rangle` and $`\sigma_1 \vdash d \Downarrow \sigma'` then $`\sigma \vdash c \Downarrow \sigma'`.

*Proof.* Induct on the derivation of the step, allowing an arbitrary final state $`\sigma'`. For an edge from $`\langle c,\sigma\rangle` to $`\langle d,\sigma_1\rangle` the property is $`\forall \sigma',\ (\sigma_1\vdash d\Downarrow\sigma')\Rightarrow(\sigma\vdash c\Downarrow\sigma')`. For assignment the residual command is skip, so inversion gives $`\sigma' = \sigma_1`. The assignment rule supplies the result. When a completed left skip is discarded, prepend a skip derivation by the sequence rule. At a conditional use the known test and branch derivation. At a false loop exit use inversion on skip and the loop exit rule.

At a true loop step the residual is body followed by loop. Invert its big-step sequence to recover the intermediate state, body derivation and loop derivation. Use exactly these as premises of the loop iteration rule.

Finally suppose the step was lifted: $`c=c_1;k`, $`d=c_1';k`, and the premise is $`\left\langle {c_1,\sigma} \right\rangle\rightarrow\left\langle {c_1',\sigma_1} \right\rangle`. Invert the given execution of $`c_1'\ \text{;}\ k` to get $`\sigma_1 \vdash c_1' \Downarrow \sigma_2` and $`\sigma_2 \vdash k \Downarrow \sigma'` for some $`\sigma_2`. The premise hypothesis is $`\forall \sigma',\ (\sigma_1\vdash c_1'\Downarrow\sigma')\Rightarrow(\sigma\vdash c_1\Downarrow\sigma')`. Apply it at $`\sigma_2` to obtain $`\sigma \vdash c_1 \Downarrow \sigma_2`. Join that execution to the suffix at $`\sigma_2`. These cases exhaust the small-step rules. $`\square`

To finish Theorem 6.2, at length zero the endpoints agree: $`c=\mathsf{skip}` and $`\sigma=\sigma'`. The skip rule gives the required execution. At length $`j+1`, let the first edge reach $`\langle d,\sigma_1\rangle`. The tail has length $`j` and ends at $`\langle\mathsf{skip},\sigma'\rangle`. Apply $`Q(j)` to $`d,\sigma_1,\sigma'` to obtain $`\sigma_1\vdash d\Downarrow\sigma'`. Lemma 6.3 then gives $`\sigma\vdash c\Downarrow\sigma'`. $`\square`

Work backwards through the path just computed. At the last configuration the skip rule proves execution to the final state. The previous step came from a loop with a false guard. Inverting the execution of skip identifies its starting and final states, so the loop exit rule proves the predecessor's execution. The preceding disposal of skip is reversed by building a sequence execution with the skip rule as its left child. At this stage we have a big-step tree for `skip; W` in the updated state. Reversing the lifted assignment step must convert this into a tree for `(x := x + 1); W` in the old state.

The two states just mentioned are precisely why Lemma 6.3 is about configurations and an arbitrary *common* final state. Inverting the existing sequence tree gives a particular middle state. In this example its left skip forces that middle state to be the updated one. Attach the assignment rule ending there, preserve the right subtree, and rebuild the sequence. Finally use the initial true guard to reconstruct the loop iteration rule. Each backwards move constructs a new derivation with the same final target, and none requires an inverse to the state update performed by assignment.

# What the endpoints record
%%%
tag := "ch06-s4"
%%%

The theorem identifies the possible *terminating final states*. It does not identify the height of a derivation with the length of a path. For two successive assignments, both leaves have height zero and the sequence tree has height one (Session 2, §2.4). The path has length three: the two writes and the disposal of skip. Nor does the theorem alone construct an infinite path when there is no terminating execution. Session 5 supplied an explicit infinite witness for a particular program.

The endpoint theorem can transport facts that are stated solely in terms of endpoints. For example consider two small-step paths from the same initial configuration to skip, ending respectively in states `σ'` and `σ''`. The backwards implication gives two derivations for the same command and initial state. Determinacy from Session 3 yields `σ' = σ''`. This is an alternative proof of uniqueness of *terminal results*. It does not by itself imply uniqueness of the first small step. An alternative transition system could split into two routes that later rejoin. Both routes could have the same terminal state while the initial configuration had two successors.

# Exercises
%%%
tag := "ch06-s5"
number := false
%%%

*6.1.* Count the small steps for two assignments composed sequentially. Give the size of the corresponding big-step tree, counting rule applications.

*6.2.* In Lemma 6.3’s true loop case, write the three premises needed by the big-step rule, with their states.

*6.3.* A proposed lifting lemma claims that $`\left\langle {a,\sigma} \right\rangle\rightarrow^{n}\left\langle {\mathsf{skip},\sigma'} \right\rangle` implies $`\left\langle {a\ \text{;}\ k,\sigma} \right\rangle\rightarrow^{n}\left\langle {k,\sigma'} \right\rangle`. Refute it at $`n = 0` and repair its statement.

*Further problem.* Replace the assignment transition by two transitions through a fresh residual command `pending(x,v)`. The first evaluates the expression in the current state and records its integer value `v`; the second writes `v` and goes to skip. For loop-free source commands, justify that this refinement preserves terminating final states and calculate the change in path length.

# Reading for the Seminar
%%%
tag := "ch06-s6"
number := false
%%%

*Definitions · 10 minutes.* Draw a sequence tree with intermediate state $`\sigma_1`. Beside it put two finite paths with lengths $`i,j`.

*Joint proof · 30 minutes.* Prove Lemma 6.1 (Lifting) for a path with two edges, then for every finite path. Ask a participant to connect the two paths of the sequence case and label the extra edge.

*Proof review · 20 minutes.* Reconstruct the reverse direction for a lifted step. Check the case of a zero-length path and state what the theorem establishes about endpoints.

*Facilitator’s hint.* Cover the suffix in one configuration, do the left step, and restore the suffix. Compare the last residual to the desired start of the second path.

# Solutions and Further Reading
%%%
tag := "ch06-s7"
number := false
%%%

*6.1.* Each assignment takes one edge. One more discards skip between them, giving three edges. The tree has two applications of the assignment rule and one of the sequence rule. Here both counts are three. For `skip; skip`, one edge suffices although the execution tree still has three rule applications.

*6.2.* At $`\sigma` the guard holds, the body runs from $`\sigma` to $`\sigma_1`, and the loop runs from $`\sigma_1` to $`\sigma'`. The guard comes from the step. Both execution derivations and $`\sigma_1` come from inversion of the residual sequence.

*6.3.* Set $`a = \mathsf{skip}` and $`\sigma = \sigma'`. A zero-edge path leaves $`\mathsf{skip}\text{;}\ k` syntactically unchanged. The valid conclusion reaches $`\mathsf{skip}\text{;}\ k` in $`n` edges or $`k` in $`n + 1` edges.

*Further problem.* An old assignment edge from `⟨x := e,σ⟩` to skip with updated state is replaced by an edge to `⟨pending(x,eval(e,σ)),σ⟩` and another to the original endpoint. The new syntax is unavailable in source programs, and its only rule performs the pending update. Inside a sequence, lift the first edge and then the second through the same left-operand context. No rule permits an unrelated suffix to execute between them. Conditional selection and discarding skip retain their original edges.

Proceed along a terminating old path replacing exactly these assignment edges, including the ones lifted through enclosing sequences. In the other direction, every reachable occurrence of a pending command in the active position arose from the preceding expression evaluation and is forced to perform its write next. Group each such pair into one old edge. This gives the same two endpoints and establishes preservation in both directions. If the original path has length `i` and executes `j` assignments, the refined path has length `i + j`. Count the assignments in the chosen branches; syntactically present assignments in untaken branches contribute zero.

*Further reading · Counting steps.* The forward construction gives a cost recurrence in addition to an existence proof. Assign to a big-step derivation the length of the small-step path obtained by the construction. The length is zero for skip and one for assignment. For a conditional add one to the length of the selected branch. For a sequence add the lengths of the two child derivations and one step discarding skip. For an exiting loop charge one guard step. For an iterating loop charge a guard step, the body path, a step discarding skip, and the recursively constructed loop path. All these quantities are computed from *finite subderivations*, so the recurrence is well founded.

To make an intermediate observation meaningful, specify what a path exposes. Suppose every assignment printed its assigned integer. The programs `skip` and `x := x` preserve the same state if one erases outputs. An observer recording the printed numbers could distinguish them. Recovering equality of such observations from two semantics would require a big-step judgment carrying the corresponding outputs and a proof of a strengthened correspondence theorem. Matching states at skip remains enough for the present theorem because its conclusion asks only about termination and the resulting state.

# Sources and Formalization
%%%
tag := "ch06-notes"
number := false
%%%

Leroy proves the two implications for these IMP rules, with Lemma 6.3 as the key step of the reverse implication. Nipkow and Klein prove the same endpoint equivalence for their transition rules. [Source and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics, §7.3.1](https://concrete-semantics.org/concrete-semantics.pdf)

* *Lemma 6.1.* Formulated in this book. Checked in Lean ([`liftLength`](lean/Paths.html#liftLength) · [IMP card references](imp-card/index.html#imp-sources)).
* *Theorem 6.2.* Source: Leroy’s IMP, correspondence between executions and transitions. Corresponds to CS Corollary 7.16. Checked in Lean ([`terminatingEquivalence`](lean/Paths.html#terminatingEquivalence) · [IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 6.3.* Source: Leroy’s IMP, execution before a transition. Checked in Lean ([`executionBeforeStep`](lean/Paths.html#executionBeforeStep) · [IMP card references](imp-card/index.html#imp-sources)).
