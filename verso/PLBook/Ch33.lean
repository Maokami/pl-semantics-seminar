import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Output Traces and Divergence" =>
%%%
tag := "ch33"
file := "chapter-33"
%%%

[Chapter PDF](print/chapter-33.pdf) · [Session 33](seminar/index.html#week-33)

A process can print a result and then run forever. An observer who has already seen the result can distinguish that computation from one that stays silent forever. Returning bottom for both programs in a final-state semantics loses a visible observation.

*Sources.* Reynolds, _Theories of Programming Languages_, §§5.2–5.3, pp. 101–108, on intermediate output, sequences and continuity. We derive finite output observations directly from a labelled transition relation and then compare their information order with the sequence interpretation. [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Visible and silent steps
%%%
tag := "ch33-s1"
%%%

Extend the small-step language of Chapter 5 with `emit e`. A configuration is a residual command and a state. Write $`\langle c,s\rangle \xrightarrow{a} \langle d,u\rangle` for one step with label $`a`. A label is $`\tau` for silent computation or $`\text{out}(n)` for printing the integer $`n`. An emission from state $`s` steps to skip in the same state with visible label $`\text{out}\left( {\operatorname{eval}\left( {e,s} \right)} \right)`. Assignment, guard selection and structural sequencing steps are silent. Stepping the prefix of a sequence propagates its label. A skip configuration is terminal and has no outgoing steps.

A finite execution prefix is any finite sequence of consecutive steps from the initial configuration, including the empty sequence. Its *visible trace* is the list of printed integers obtained by deleting all silent labels. Let $`P\left( {c,s} \right)` collect these lists over all such finite execution prefixes. This set is prefix-closed: stop an execution immediately after the last retained output to realize each nonempty prefix of its list, and use zero steps for the empty list. A separate observation of termination records a terminal configuration and its state.

It helps to separate two operations on finite executions. Concatenation joins consecutive path segments whose meeting configurations agree. Projection erases the silent labels of a path and keeps its visible labels in order. If the first segment has labels `[τ,out(3),τ]` and the next has labels `[τ,out(5)]`, projecting their concatenation gives `[3,5]`. Projecting the segments separately gives `[3]` and `[5]`, whose concatenation has the same value. This equation depends only on the labels once the existence of the path has been established.

In Lean a label can be encoded by `Option Int`, using `none` for silence and `some n` for an emission. Induction on the first segment proves the general equation. Its silent case consumes the head of the input without consuming a cell in the output.

```lean
def printedLabels : List (Option Int) → List Int
  | [] => []
  | none :: xs => printedLabels xs
  | some n :: xs => n :: printedLabels xs

example (xs ys : List (Option Int)) :
    printedLabels (xs ++ ys) = printedLabels xs ++ printedLabels ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [printedLabels, ih]
```

The converse implication for paths would be too strong. An output list contains no record of the meeting configuration. To join two proposed executions, one must still verify that the source of the second is the target of the first.

# Printing before divergence
%%%
tag := "ch33-s2"
%%%

Let $`L` be `while true do skip`. Its transitions are silent and repeat a configuration indefinitely. For any initial state $`s`, $`P\left( {L,s} \right)` consists only of the empty list. For `emit 7; L` there is an initial output-labelled step of the sequence prefix, a silent sequencing step, and then the same loop. Thus the empty list and the one-element list containing seven are both observable. No longer list is observable: after that emission every reachable step is silent. Neither program reaches a terminal state.

The proof of the negative claim needs more than finding a run with one emission. Inspect the reachable residual commands: the first emission is possible only in the original prefix, and the remaining steps stay in the silent loop and its unfolding. This accounts for *every* finite prefix in this deterministic language.

Compare `emit 7; L` with `L; emit 7`. To determine whether the second program ever prints, list the rules whose conclusion steps a sequence. A step of its left operand propagates a label and leaves the right operand waiting. The other rule discards a completed left operand, exposing the right operand. Thus a first emission could come from the left operand while it is executing or from the right operand after the left has completed.

Neither possibility can occur here. All steps of `L` and its successive unfoldings are silent: guard tests, executing `skip` and rearranging the sequence introduce no emission. Moreover the unfolding of the true guard places another execution of `L` after its body. In each turn the body can finish but the loop as a whole cannot reach a terminal configuration. By induction on the length of a finite run of the sequence, its right operand consequently stays pending throughout. The visible projection is empty for every such run.

The two orderings therefore both run forever, while exactly one admits the finite observation `[7]`. Ten thousand silent steps before an eventual `emit 7` would still permit that singleton. Any finite delay can be traversed by some finite path. The silent divergence in the left operand of the second program prevents every such path from reaching the emission.

# Information in prefixes
%%%
tag := "ch33-s3"
%%%

Order finite and infinite lists by the prefix order $`u \preceq v`: reading $`v` begins with exactly $`u`. The empty list is least. A chain of increasingly long consistent finite output observations has as least upper bound their union by position. Each position that appears must retain the same integer in every longer prefix. If lengths are unbounded the limit is an infinite list. If the chain stabilizes it has the stable list as its limit.

The loop `while true do emit 1` has observations of arbitrarily many ones. For each $`k` we can exhibit a finite prefix with $`k` emissions by running $`k` iterations. Their least upper bound is the infinite stream of ones. This construction credits a finite observation only after a finite amount of execution. It explains the relevance of continuity in a model of intermediate outputs. Output prefixes alone do not record termination: skip and the silent loop both have just the empty output prefix. To answer a final-state question we must also record a termination observation.

A test on traces illustrates what continuity demands. Let the result set have two elements, `unknown` below `yes`. Define a test that returns `yes` exactly on traces that contain an occurrence of seven, and `unknown` elsewhere. Extending a trace cannot delete an occurrence, so the test is monotone. It also preserves suprema of increasing chains. If the union contains a seven at position `j`, some chain member already has a position `j`, with that same value. Conversely, an occurrence in any member persists in the union. These two implications show that the test on the union equals the supremum of its answers on the members.

Keep the same result set and test whether the trace is infinite. This test is monotone: an infinite trace cannot acquire a proper extension in the prefix order. Yet on the chain consisting of zero ones, one one, two ones, and so on, the answer is `unknown` at every finite stage. The supremum of those answers is `unknown`, while the answer on the union is `yes`. The defining equation for continuity fails. The distinction has a concrete reading for an observer. Seeing a seven requires one finite witness, its position. Observing another one, however many have already appeared, still leaves open the possibility that output ends there.

An observation can now be a finite sequence of outputs produced before termination or divergence. A single final-store observation collapses both a silent infinite loop and a program that prints once before looping.

# Exercises
%%%
tag := "ch33-s4"
number := false
%%%

1. Give two programs that print seven once and have exactly the same finite visible traces, although one terminates and the other diverges.
2. Compute all finite visible traces of `emit 1; emit 2; L`. Does the list containing only two occur?
3. Suppose a transformation preserves only terminating final states. Could it replace `emit 7; L` with $`L`? Test the two criteria separately.

*Further problem.* Composition of output observations. Show that knowing only `P(c,s)` is insufficient to calculate `P(c;d,s)`, even when `d` is fixed. Define `T(c,s)` to consist of pairs `(w,t)` such that some terminating run emits list `w` and finishes in state `t`. Give an exact formula for `P(c;d,s)` using `P` and `T`, and prove its two inclusions.

# Reading for the Seminar
%%%
tag := "ch33-s5"
number := false
%%%

*Definitions · 10 minutes.* Label every step up to the first repeated configuration in the silent example.

*Joint proof · 30 minutes.* Prove the exact two prefix sets for the silent and the printing loop, giving witnesses for inclusion and ruling out additional traces.

*Proof review · 20 minutes.* Compare finite prefixes, an infinite output stream, and a terminal observation on the exercise programs.

*Facilitator’s hint.* A finite trace may end before the process ends. Stop the transition sequence just after its first emission even when no terminating run exists.

# Solutions
%%%
tag := "ch33-s6"
number := false
%%%

*1.* Use `emit 7` and `emit 7; L`. Each permits just the empty trace and the singleton seven. Only the first has a terminal observation.

*2.* The possibilities are the empty list, `[1]` and `[1,2]`. Erasing silent steps never changes the order of visible events or removes a preceding visible event.

*3.* Both lack any terminating final state, so the proposed replacement agrees on that observation. The singleton seven witnesses failure to preserve the finite visible traces.

*Further problem.* From the same state, `skip` and the silent infinite loop have the same visible prefixes. After each is sequenced with `emit 7`, only the sequence beginning with `skip` has the singleton trace seven. Thus prefix equality alone does not determine the answer.

The formula is the union of `P(c,s)` with the set of concatenations `w ++ v` for which there exists `t` with `(w,t) ∈ T(c,s)` and `v ∈ P(d,t)`. To prove inclusion from left to right, take a witnessing finite path of `c;d`. If the structural sequencing step that exposes `d` has not occurred, projecting the steps of its left operand exhibits a prefix of `c` with the same trace. Otherwise split the path at that step. The first segment witnesses termination of `c` with some trace and state, and the remaining segment is a prefix of `d` from that state. The intervening structural step is silent. Conversely, lift any prefix of `c` through the sequencing context. To realize a concatenation, lift the whole witnessing terminating run, take the silent sequencing step, and append the witnessing path of `d`. Trace projection preserves concatenation.
