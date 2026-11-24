import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Simulation of Compiled Commands" =>
%%%
tag := "ch38"
file := "chapter-38"
%%%

[Chapter PDF](print/chapter-38.pdf) · [Session 38](seminar/index.html#week-38)

Switching from a completed skip to the next command in a sequence changes the source configuration. When that command’s machine code already starts at the current counter, the same source step costs zero target instructions. A proof for diverging programs has to exclude the possibility that infinitely many source steps all disappear this way.

*Sources.* Leroy’s _Compiler Verification_ course, Lean port, `Imp.lean` §6.2 on continuation steps and `Compil.lean` on `match_config`, `measure'`, and the `step_skip_seq` case of `simulation_step`. Read the continuation inversion lemma as well as the final case. Compare _Concrete Semantics_ §§8.3–8.4. [Source steps.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L441-L470) [Matching configurations and measure.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean#L609-L700) [Sequence case.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean#L905-L923) [Concrete Semantics.](https://concrete-semantics.org/concrete-semantics.pdf)

# Matching configurations
%%%
tag := "ch38-s1"
%%%

The source state $`\langle c,k,s\rangle` contains a command in focus, a continuation describing the work still pending, and a store. The frame `Kseq d k` says to run $`d` next and then follow $`k`. The source step is $`\langle \mathrm{skip},\mathrm{Kseq}(d,k),s\rangle \to \langle d,k,s\rangle`. The compiler emits the empty instruction list for skip.

For an ambient machine program $`C`, the relation `match_config` relates $`\langle c,k,s\rangle` to $`\langle p,[\,],s\rangle` when the code for $`c` occurs at $`p` and `compile_cont` holds for $`k` immediately after that code. The stacks at these command boundaries are empty and the two stores are equal. The continuation relation describes both contiguous continuations and transfers via unconditional branches. Consequently the start of the actual next command need not always be literally the current counter.

Write $`\to^{*}` for zero or more machine steps and $`\to^{+}` for one or more. The one-source-step theorem supplies a matching target configuration reachable either by a positive path, or by a possibly empty path accompanied by a strict decrease of a natural-valued source measure. This second disjunct is the one used for resuming a sequence.

The source continuation is part of the source's control state. For example, consider two source configurations focused on skip in identical stores. One has the stop continuation; the other has a pending assignment. The first is ready to finish, while the second will execute a write. A relation comparing only focused commands and stores would have no way to distinguish their future target behavior. The continuation relation resolves this ambiguity by constraining the code that begins where the current block ends.

It helps to read the configuration match as three checks on one proposed machine state. Is its operand stack empty at this command boundary? Does it have the very store occurring in the source configuration? Can the program be divided at its counter into the code for the focus followed by instructions implementing the continuation? The last check is relational, because the continuation implementation is permitted to transfer control by branches. Even though each source configuration records its continuation explicitly, an equivalent target state can encode the same information through its program counter and the surrounding code.

# The measure and the sequence case
%%%
tag := "ch38-s2"
%%%

The measure is the sum of `com_size c` and `cont_size k`. Skip and assignment each have command size one; a sequence or conditional has size one plus the sizes of both components, and a loop one plus its body size. The stop continuation has size zero. A sequence frame adds the pending command size to the tail size; a while frame uses just the tail size.

Before the source step the measure is $`1 + \lvert d\rvert + \lvert k\rvert`, where the bars denote the corresponding sizes. Afterwards it is $`\lvert d\rvert + \lvert k\rvert`. Thus the decrease is exactly one for every $`d,k,s`.

*Simulation case.* Invert the old configuration match. Because skip has code length zero, `compile_cont C (Kseq d k) p` holds at $`p` itself. The lemma `compile_cont_Kseq_inv` gives a counter $`p'` and a path from $`\langle p,[\,],s\rangle` to $`\langle p',[\,],s\rangle` with the compiled $`d` at $`p'` and the continuation $`k` matched at $`p' + \lvert K(d)\rvert`, where $`K(d)` denotes compiled code. These last two facts build the target match for $`\langle d,k,s\rangle`. Combine the path with the computed decrease to obtain the second disjunct. In the direct sequence-frame case the inversion takes $`p' = p` and the path is reflexive. With intervening branches, the lemma instead supplies the requisite finite path across them.

For a direct resumption, draw the target fragment beginning at p as two consecutive blocks: an empty block for skip followed by the code of d. The start of d is therefore p. The machine already satisfies the relation for the new focused command. We use the empty path with identical endpoints. This proves existence of the target path without executing the first instruction of d prematurely.

Now place an unconditional branch at p leading to the actual entry of d. The same source step still has the same natural-number decrease, but the empty target path can no longer be chosen using that layout argument. Inverting the sequence continuation supplies a finite path to the entry address together with a new code-occurrence premise. This is why the general theorem gives a star path in the decreasing alternative even though the simple picture contains zero steps.

The following arithmetic check is the measure calculation left after unfolding the two size functions for this particular step. The variables here stand for sizes, not for source commands.

```lean
example (sizeOfNext sizeOfTail : Nat) :
    sizeOfNext + sizeOfTail < 1 + (sizeOfNext + sizeOfTail) := by
  omega
```

The strict inequality uses the one unit contributed by the completed skip. Counting just the size of the focus would omit both pending contributions in the old configuration.

# From steps to runs
%%%
tag := "ch38-s3"
%%%

For finite runs concatenate the simulation paths using transitivity; the final configuration match is retained. For an infinite source run, suppose that after some point no target step occurs. Every remaining simulation segment is then empty and must use the decreasing-measure disjunct. Infinitely many strict decreases of naturals from a fixed starting value are impossible. Thus positive target segments occur arbitrarily far along the run, allowing construction of an infinite target path. The Lean development formalizes the productive extraction of the next positive segment separately from the single-step proof.

For a terminating run, “there is a finite target path” is preserved under concatenation even when one path is empty. For divergence there is a different issue: concatenating infinitely many empty paths would still provide no first target transition. Consider an abstract source with one configuration and a self-loop and a target that cannot step. Relate the source to the target and simulate every source step by zero target steps. The star-only simulation condition is satisfied, but the source has an infinite run and the target has none. This two-state illustration pinpoints the missing assumption.

A decreasing natural measure limits a consecutive stretch of empty simulation segments. If the source measure at the beginning of such a stretch is m, at most m strict decreases are possible before a segment must contribute a target step, assuming the source run continues. Once a positive segment is reached the measure may grow again. There is no need for a single global bound on the lengths of all future stretches. For each required target step one starts with the current source measure and uses well-founded induction to reach the next positive segment. This local argument supports the construction of an infinite target run.

# Exercises
%%%
tag := "ch38-s4"
number := false
%%%

1. Take $`d` to be an assignment and $`k` the stop continuation. Calculate both measures. What does the machine execute during the direct resumption step?
2. Why would command size alone be insufficient when $`d` is a large sequence?
3. Does the measure need to decrease on machine segments known to be positive? Explain from the theorem’s disjunction.

*Further problem.* Could the zero-step disjunct use a non-strict measure inequality if the compiler were required to preserve only finite source runs? Separate the finite-run induction from the argument extracting an infinite target path.

# Reading for the Seminar
%%%
tag := "ch38-s5"
number := false
%%%

*Definitions · 10 minutes.* Draw the four configurations in the simulation square. Expand the starting match with empty code for skip.

*Joint proof · 30 minutes.* Use the sequence inversion lemma to fill in the target corner, then compute the two measures. Instantiate the argument for contiguous code to obtain exactly zero machine steps.

*Proof review · 20 minutes.* Insert an unconditional branch before the continuation code. Identify which part of the general proof already permits a different counter.

*Facilitator’s hint.* The inversion lemma gives a star path. Zero steps are available in the direct case; the general statement does not assert equality of the two counters.

# Solutions
%%%
tag := "ch38-s6"
number := false
%%%

*1.* The measures are two and one. Direct resumption needs no instruction. The assignment instructions will execute when simulating subsequent source activity.

*2.* The focused size would change from one to the size of $`d`, potentially increasing. Including pending commands in the old measure accounts for $`d` on both sides.

*3.* No. A positive segment already contributes a target step to an infinite simulation. The measure obligation is needed when progress might otherwise be hidden indefinitely.

*Further problem.* A proof simulating a given finite source path by a finite target path does not need a measure. In the successor case, use the one-step simulation to reach a matching intermediate target and concatenate with the path supplied by induction. An empty segment composes by the identity law for finite paths. Replacing strict descent by nonincrease would preserve this use. For infinite runs the self-loop counterexample in §38.3 supplies a constant measure. Its source may keep stepping forever while the matched target stays still, satisfying nonincrease at each simulation step. The finite argument proves only matching for each chosen finite prefix. None of those conclusions says that the number of target transitions in the prefixes grows without bound.
