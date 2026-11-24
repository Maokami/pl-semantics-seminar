import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Equivalence of Terminating Evaluations" =>
%%%
tag := "ch05"
file := "chapter-05"
%%%

[Chapter PDF](print/chapter-05.pdf) · [Session 6](seminar/index.html#week-06)

Chapter 2 represents a terminating execution by a tree. Chapter 4 represents it by a path ending at skip. For a sequence, the tree has one child per operand, whereas the path keeps the second operand in its residual command while the first executes. Matching the two pictures requires a lemma about executing a command inside a larger one.

*Sources.* Tobias Nipkow and Gerwin Klein, _Concrete Semantics_, §7.3.1 on equivalence of big-step and small-step execution. Compare the sequence case with the Lean declarations `red_seq_steps` and `cexec_to_reds`. We use Chapter 4’s guard-selecting loop steps throughout. The joint proof is the sequence case in §5.2. [Concrete Semantics, chapter 7.](https://concrete-semantics.org/concrete-semantics.pdf) [Leroy, Imp.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean)

# Paths inside sequences
%%%
tag := "ch05-s1"
%%%

Recall $`s \vdash c \Downarrow t` for a finite execution derivation and $`\left\langle {c,s} \right\rangle\rightarrow^{*}\left\langle {d,t} \right\rangle` for zero or more steps. A *sequence context* with suffix $`k` is the operation sending a residual $`a` to $`a\ \text{;}\ k`. The suffix stays fixed, including when $`a` changes.

*Lemma 5.1 (Lifting).* If $`\left\langle {a,s} \right\rangle\rightarrow^{n}\left\langle {b,t} \right\rangle`, then

$$`\left\langle {a\ \text{;}\ k,s} \right\rangle\rightarrow^{n}\left\langle {b\ \text{;}\ k,t} \right\rangle.`

*Proof.* For each configuration along the path replace its command by the sequence with suffix $`k`. Each original edge becomes exactly one edge by the left-operand step rule. For $`n = 0` the transformed endpoints agree. The construction preserves every intermediate store. $`\square`

In particular, when $`b = \operatorname{skip}` the final configuration in the lifted path *still contains the suffix*. One further step goes from $`\left\langle {\operatorname{skip}\text{;}\ k,t} \right\rangle` to $`\left\langle {k,t} \right\rangle`. Forgetting this step gives path segments whose endpoints cannot be joined.

The lifting lemma can be seen as a map on paths with a fixed hole in a program. For a particularly small trace take the assignment `x := 2` from store `s` to skip at `u = s[x ↦ 2]`. Fix the suffix `y := x`. Lifting produces one transition of the combined command whose target is `skip; y := x` in store `u`. At this point the proof still knows that `y` has its *old* value. No transition of the suffix was used in the lifted path. Only after the skip is removed does the next assignment read the already updated `x`.

The construction respects concatenation. If a prefix computation has been split into two paths at some residual `b` and store `v`, lifting the paths separately yields the same cut point `b; k` at `v`. Concatenate there to obtain the lifted full path. This observation permits a reader to group steps at any convenient intermediate computation without having to rediscover the behavior of the suffix for each group. It also explains a syntactic asymmetry: placing a hole to the right of an *unfinished* prefix generally cannot lift a right-hand step under these evaluation rules.

To formalize lifting independently of a particular syntax, let `F` map configurations into a context and assume that `F` maps every edge to an edge. The following construction transports a whole path. Its index records the number of edges, which survives the induction unchanged.

```lean
inductive CountedPath {C : Type} (step : C → C → Prop) : Nat → C → C → Prop
  | stop (p) : CountedPath step 0 p p
  | next {n p q r} : step p q → CountedPath step n q r →
      CountedPath step (n+1) p r

example {C : Type} {step : C → C → Prop} (F : C → C)
    (liftEdge : ∀ a b, step a b → step (F a) (F b))
    {n p q} (path : CountedPath step n p q) :
    CountedPath step n (F p) (F q) := by
  induction path with
  | stop => exact .stop _
  | next edge _ ih => exact .next (liftEdge _ _ edge) ih
```

# From execution trees to paths
%%%
tag := "ch05-s2"
%%%

*Theorem 5.2.* $`s \vdash c \Downarrow t` holds if and only if $`\left\langle {c,s} \right\rangle\rightarrow^{*}\left\langle {\operatorname{skip},t} \right\rangle`.

For the forward direction, induct on the given execution derivation. At skip take a zero-edge path. At assignment take one update step. At a conditional take the selected branch step and append the path given by the branch hypothesis.

*Sequence case.* The last rule supplies a middle state $`u`. The induction hypotheses produce a path of some length $`m` for $`c` from $`s` to skip at $`u`, and a path of some length $`n` for $`d` from $`u` to skip at $`t`. Lift the first path by Lemma 5.1, discard the completed left operand, then follow the second path:

$$`\begin{matrix} \left\langle {c\ \text{;}\ d,s} \right\rangle & {\rightarrow^{m}\left\langle {\operatorname{skip}\text{;}\ d,u} \right\rangle} \\ & {\rightarrow\left\langle {d,u} \right\rangle\rightarrow^{n}\left\langle {\operatorname{skip},t} \right\rangle.} \end{matrix}`

Concatenation yields a path of length $`m + 1 + n`. If $`c` is already skip, $`m = 0` and the single administrative edge remains necessary.

*Loop cases.* For a false guard take the exit edge to skip. For a true guard, write $`W` for the loop, $`a` for its body, and $`u` for the body’s result. The small-step loop rule first goes to $`\left\langle {a\ \text{;}\ W,s} \right\rangle`. Lift the body hypothesis to that context, discard skip at $`u`, then append the recursive loop hypothesis from $`u`. Induction is legitimate because both hypotheses concern child derivations. This proves the forward direction.

The forward construction gives a cost recurrence in addition to an existence proof. Assign to a big-step derivation the length of the small-step path obtained by the construction. The length is zero for skip and one for assignment. For a conditional add one to the length of the selected branch. For a sequence add the lengths of the two child derivations and one administrative step. For an exiting loop charge one guard step. For an iterating loop charge a guard step, the body path, an administrative step, and the recursively constructed loop path. All these quantities are computed from *finite subderivations*, so the recurrence is well founded.

For example use `while x < 1 do x := x + 1` at a state with `x = 0`. The body path costs one and the recursive exit path costs one. The full iteration therefore costs four. The residual commands in order are the loop, the body followed by the loop, skip followed by the loop, the loop at the updated state, and skip. The derivation labels contain fewer visible changes of residual syntax. The recurrence makes the connection precise for this choice of transition rules; changing the rule for loop unfolding requires revisiting its cost clause.

# From paths to execution trees
%%%
tag := "ch05-s3"
%%%

Simply turning the path arrows around does not reconstruct which premises formed the last big-step rule. We first show how to extend a completed big-step execution backwards by *one* small step.

*Lemma 5.3.* If $`\left\langle {c,s} \right\rangle\rightarrow\left\langle {d,u} \right\rangle` and $`u \vdash d \Downarrow t` then $`s \vdash c \Downarrow t`.

*Proof.* Induct on the derivation of the step, allowing an arbitrary final state $`t`. For assignment the residual command is skip, so inversion gives $`t = u`. The assignment axiom supplies the result. When a completed left skip is discarded, prepend a skip derivation by the sequence rule. At a conditional use the known test and branch derivation. At a false loop exit use inversion on skip and the loop exit rule.

At a true loop step the residual is body followed by loop. Invert its big-step sequence to recover the intermediate state, body derivation and loop derivation. Use exactly these as premises of the true loop big-step rule.

Finally suppose the step was lifted from $`\left\langle {a,s} \right\rangle\rightarrow\left\langle {b,u} \right\rangle` inside a suffix $`k`. Invert the given execution of $`b\ \text{;}\ k` to get $`u \vdash b \Downarrow v` and $`v \vdash k \Downarrow t` for some $`v`. The induction hypothesis on the premise step gives $`s \vdash a \Downarrow v`. Join that execution to the suffix at $`v`. These cases exhaust the small-step rules. $`\square`

To finish Theorem 5.2, start at the end of the finite path with the skip axiom $`t \vdash \operatorname{skip} \Downarrow t`. Apply Lemma 5.3 to the last edge, then the preceding edge, until no edge remains. Induction on the path length justifies the construction, including a path of length zero.

Work backwards through the path just computed. At the last configuration the skip axiom proves execution to the final store. The previous step came from a loop with a false guard. Inverting the execution of skip identifies its starting and final stores, so the false loop rule proves the predecessor's execution. The preceding disposal of skip is reversed by building a sequence execution with the skip axiom as its left child. At this stage we have a big-step tree for `skip; W` in the updated state. Reversing the lifted assignment step must convert this into a tree for `(x := x + 1); W` in the old state.

The two states just mentioned are precisely why Lemma 5.3 is about configurations and an arbitrary *common* final store. Inverting the existing sequence tree gives a particular middle store. In this example its left skip forces that middle store to be the updated one. Attach the assignment axiom ending there, preserve the right subtree, and rebuild the sequence. Finally use the initial true guard to reconstruct the iteration rule. Each backwards move constructs a new derivation with the same final target, and none requires an inverse to the state update performed by assignment.

# What the endpoints record
%%%
tag := "ch05-s4"
%%%

The theorem identifies the possible *terminating final stores*. It does not identify the height of a derivation with the length of a path. For `skip; skip`, two skip axioms lie below the sequence rule, whereas a single small step discards the left skip. Nor does the theorem alone construct an infinite execution when there is no terminating one. Chapter 4 supplied an explicit infinite witness for a particular program.

The endpoint theorem can transport facts that are stated solely in terms of endpoints. For example consider two small-step paths from the same initial configuration to skip, ending respectively in stores `u` and `v`. The backwards implication gives two derivations for the same command and initial store. Determinacy from Chapter 3 yields `u = v`. This is an alternative proof of uniqueness of *terminal results*. It does not by itself imply uniqueness of the first small step. An alternative transition system could split into two routes that later rejoin. Both routes could have the same terminal store while the initial configuration had two successors.

To make an intermediate observation meaningful, specify what a path exposes. Suppose every assignment printed its assigned integer. The programs `skip` and `x := x` preserve the same store if one erases outputs. An observer recording the printed numbers could distinguish them. Recovering equality of such observations from two semantics would require a big-step judgment carrying the corresponding outputs and a proof of a strengthened correspondence theorem. Matching stores at skip remains enough for the present theorem because its conclusion asks only about termination and the resulting store.

# Exercises
%%%
tag := "ch05-s5"
number := false
%%%

*5.1.* Count the small steps for two assignments composed sequentially. Give the size of the corresponding big-step tree, counting rule applications.

*5.2.* In Lemma 5.3’s true loop case, write the three premises needed by the big-step rule, with their states.

*5.3.* A proposed lifting lemma claims that $`\left\langle {a,s} \right\rangle\rightarrow^{n}\left\langle {\operatorname{skip},t} \right\rangle` implies $`\left\langle {a\ \text{;}\ k,s} \right\rangle\rightarrow^{n}\left\langle {k,t} \right\rangle`. Refute it at $`n = 0` and repair its statement.

*Further problem.* Replace the assignment transition by two transitions through a fresh residual command `pending(x,v)`. The first evaluates the expression in the current store and records its integer value `v`; the second writes `v` and goes to skip. For loop-free source commands, justify that this refinement preserves terminating final stores and calculate the change in path length.

# Reading for the Seminar
%%%
tag := "ch05-s6"
number := false
%%%

*Definitions · 10 minutes.* Draw a sequence tree with middle state $`u`. Beside it put two finite paths with lengths $`m,n`.

*Joint proof · 30 minutes.* Build the context-lifting lemma for a path with two edges, then for every finite path. Ask a participant to connect the two paths of the sequence case and label the extra edge.

*Proof review · 20 minutes.* Reconstruct the reverse direction for a lifted step. Check the case of a zero-length path and state what the theorem establishes about endpoints.

*Facilitator’s hint.* Cover the suffix in one configuration, do the left step, and restore the suffix. Compare the last residual to the desired start of the second path.

# Solutions
%%%
tag := "ch05-s7"
number := false
%%%

*5.1.* Each assignment takes one edge. One more discards skip between them, giving three edges. The tree has two assignment axioms and one sequence inference. Here both counts are three, a coincidence that fails for `skip; skip`.

*5.2.* At $`s` the guard holds, the body runs from $`s` to $`v`, and the loop runs from $`v` to $`t`. The guard comes from the step. Both execution derivations and $`v` come from inversion of the residual sequence.

*5.3.* Set $`a = \operatorname{skip}` and $`s = t`. A zero-edge path leaves $`\operatorname{skip}\text{;}\ k` syntactically unchanged. The valid conclusion reaches $`\operatorname{skip}\text{;}\ k` in $`n` edges or $`k` in $`n + 1` edges.

*Further problem.* An old assignment edge from `⟨x := e,s⟩` to skip with updated store is replaced by an edge to `⟨pending(x,eval(e,s)),s⟩` and another to the original endpoint. The new syntax is unavailable in source programs, and its only rule performs the pending update. Inside a sequence, lift the first edge and then the second through the same left-operand context. No rule permits an unrelated suffix to execute between them. Conditional selection and discarding skip retain their original edges.

Proceed along a terminating old path replacing exactly these assignment edges, including the ones lifted through enclosing sequences. In the other direction, every reachable occurrence of a pending command in the active position arose from the preceding expression evaluation and is forced to perform its write next. Group each such pair into one old edge. This gives the same two endpoints and establishes preservation in both directions. If the original path has length `m` and executes `k` assignments, the refined path has length `m + k`. Count the assignments in the chosen branches; syntactically present assignments in untaken branches contribute zero.
