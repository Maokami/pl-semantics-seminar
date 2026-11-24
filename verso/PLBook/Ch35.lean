import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Nondeterminism and May and Must Termination" =>
%%%
tag := "ch35"
file := "chapter-35"
%%%

[Chapter PDF](print/chapter-35.pdf) · [Session 35](seminar/index.html#week-35)

A command offers two enabled alternatives. Choosing one may reach a final state immediately, while choosing the other may enter an infinite loop. A set of final states answers which normal results are possible. It leaves open whether every possible run actually produces one.

*Sources.* Reynolds, _Theories of Programming Languages_, chapter 7, especially §§7.1–7.2 and §7.4. Read how guarded alternatives admit multiple transitions and how this changes specifications. Our binary choice is the special case with two enabled guards. For an extended treatment read Winskel, chapter 14. [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html) [Winskel.](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)

# Executions and observations
%%%
tag := "ch35-s1"
%%%

Add binary choice `c ⊕ d` to the small-step language of Chapter 5. Its two possible first steps are $`\langle c\oplus d,s\rangle \to \langle c,s\rangle` and $`\langle c\oplus d,s\rangle \to \langle d,s\rangle`. Both are silent. This models two guarded alternatives with guards true. A run is a finite or infinite sequence of successive configurations. It is *maximal* if infinite or if its final configuration has no outgoing step. Normal final configurations are those with command skip. This definition would distinguish deadlock from successful termination in an extension that permits stuck commands.

An input *may terminate* if some finite run reaches a normal final configuration. It *must terminate* if every maximal run is finite and normally final. The second property does not require all runs to return the same state. The set of normal results consists of those states reached by some finite run. All choices here are unconstrained; our semantics assumes no fairness restriction on infinite runs.

Consider the following finite transition graph. At its root a scheduler may choose a step to a final vertex, or a step to a vertex with a self-loop. A finite path ending at the second vertex is a prefix of a run. It cannot serve as a maximal finite run, since the self-loop is enabled. Traversing that edge without end does give a maximal run. Listing reachable vertices alone therefore loses part of the evidence: we must also record which terminal vertices are normal and which paths continue indefinitely.

Three questions about this graph take three different forms of proof. To establish may termination, write down one finite path to a normal vertex. To refute must termination, construct one maximal path whose outcome fails the requirement. To establish must termination, account for *every* maximal path. In the deterministic language of Chapter 5, a terminating execution precluded an infinite execution from the same input because the next step was unique. The first transition at the root here violates that premise. Transplanting the deterministic argument would discard precisely the scheduler choice the graph is meant to represent.

# Two witnesses
%%%
tag := "ch35-s2"
%%%

Let $`L` be the deterministic loop `while true do skip`, and let $`M` be `skip ⊕ L`. In any state $`s` one choice step leads to skip in $`s`. This is a witness for may termination. The other choice step leads to $`L`. Its guard is always true and its skip body returns to the same loop head after a finite nonempty sequence of silent steps. Repeating that cycle gives an infinite maximal run from $`M`. This is a counterexample to must termination. The normal-result set of $`M` is the singleton containing $`s`, the same as for skip.

For `(x := 1) ⊕ (x := 2)`, either branch is a terminating assignment. Inverting the first transition exhausts the choices; in each case the remaining assignment terminates in one step. Thus this command must terminate, with two distinct possible final values at $`x`. Determinism, existence of a result and universal termination describe different properties.

The normal-result set projects an execution onto its last state, when there is one. Apply that projection to both branches of the mixed example separately. The skip branch contributes the singleton containing the starting state; the infinite-loop branch contributes the empty set. Taking their union gives the same singleton. This calculation proves the may observation and also explains exactly where the evidence against must termination disappears: set union has no record of a branch that contributes no member.

One simple mathematical record keeps this information for the present examples: pair the set of normal results with a Boolean that reports the existence of a divergent run. In the error-free language here, where every nonfinal configuration can step, skip has a singleton and a false flag; the mixed choice has the same singleton and a true flag. With two terminating assignments the flag is false but the set can have two elements. If stuck states become possible in an extension, a false divergence flag no longer suffices to establish must termination. A finite maximal path to a stuck state would also have to be excluded.

# Rules for binary choice
%%%
tag := "ch35-s3"
%%%

*Proposition 35.1.* May termination of a binary choice is equivalent to may termination of at least one operand. A terminating run cannot have zero steps, since a choice is not final. Inspect its first step and take its tail as the operand witness. Conversely prefix an operand witness by the matching choice step.

Must termination of a choice is equivalent to must termination of both operands. For the forward direction extend any maximal operand run backwards by the corresponding choice step. The result is still maximal; the hypothesis makes its tail finite and normally final. For the reverse direction every maximal choice run starts by selecting an operand, since an empty choice run can always be extended. Its tail is maximal for the selected operand, so that operand’s hypothesis gives normal termination. These arguments rely only on the permitted transitions and the specified notion of maximal run.

In a repeated choice, continually selecting an enabled continuation branch can yield an infinite run even when an exit alternative is offered infinitely often. A fairness requirement would restrict which schedules are considered. Any assertion about must termination must then specify the class of runs being quantified over.

A compositionality check helps distinguish the two rules. Suppose a prefix may either terminate with a zero in a variable or terminate with a one. Append a conditional that stops only in the first state and diverges in the second. The prefix must terminate; the complete sequence only may terminate. Thus a rule for must termination of a sequence needs the set of possible intermediate states as well as the termination status of its prefix. The binary-choice proof was simpler because entering a chosen operand did not supply it with an altered state.

For a small checked version of the quantifiers, represent an entire outcome by a Boolean: true for a normal result, false for an unsuccessful maximal run. A set of such outcomes is a predicate. The following calculation concerns that abstraction; the first-step argument above is what justifies using predicate union for this choice operator.

```lean
def everyNormal (outcomes : Bool → Prop) : Prop :=
  ∀ b, outcomes b → b = true

example (a b : Bool → Prop) :
    everyNormal (fun r => a r ∨ b r) ↔ everyNormal a ∧ everyNormal b := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩
  · rintro ⟨ha, hb⟩ r (hr | hr)
    · exact ha r hr
    · exact hb r hr
```

The two directions use different proof operations. One restricts a universal claim to each subset; the other inspects the reason a given outcome belongs to the union.

The observations here are may termination (at least one terminating run) and must termination (all maximal runs terminate). Two commands can have the same possible final stores while admitting different infinite runs.

# Exercises
%%%
tag := "ch35-s4"
number := false
%%%

1. Compute may and must for `L ⊕ L` and for `skip ⊕ skip`. Justify each universal claim.
2. A transformation replaces `skip ⊕ L` by skip. Which of the three observations in §35.1 does it preserve?
3. Suppose a command can choose between skip and a stuck configuration. Does the absence of infinite runs imply must termination under the definition above?

*Further problem.* Observe a final integer x, and suppose two prefixes may return exactly the same final states. Does appending a deterministic suffix preserve equality of may observations? Does the corresponding conclusion follow for must termination? Prove the first assertion or give a counterexample, and distinguish the two quantifiers in your answer.

# Reading for the Seminar
%%%
tag := "ch35-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the quantifiers in may and must and identify which runs are maximal.

*Joint proof · 30 minutes.* Construct the finite and infinite witnesses for the mixed choice. Then prove both equivalences of Proposition 35.1 by inspecting the first step.

*Proof review · 20 minutes.* Compare two terminating assignments returning distinct results. Explain why universal termination permits this example.

*Facilitator’s hint.* A finite prefix of an infinite run is not a counterexample to must termination unless it is maximal. Extend or close the run explicitly.

# Solutions
%%%
tag := "ch35-s6"
number := false
%%%

*1.* Either branch of the first diverges, so it neither may nor must terminate. Each maximal run of the second selects a skip branch and stops; it both may and must terminate.

*2.* The normal-result set and may termination agree at every input. Must termination changes from false to true.

*3.* No. The path selecting the stuck configuration is finite and maximal but its final command is not skip. The other branch supplies a witness of may termination.

*Further problem.* For may observations, decompose a successful run of the sequence at the point where the suffix starts. Its initial state is a member of the common prefix result set. The other prefix admits a run to that same state, so the same suffix run reproduces the observation. Exchanging prefixes proves the reverse inclusion. Determinism of the suffix was stronger than necessary for this existence argument. For must termination choose skip and the mixed choice of skip or divergence as prefixes, with skip for the suffix. The prefix result sets agree at each input. The mixed command still has an infinite run that never reaches its suffix, so only the first sequence must terminate. The decomposition used in the may argument started with a *successful* run; it supplied no intermediate state for this infinite path.
