import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Big-Step Semantics of Commands" =>
%%%
tag := "ch02"
file := "chapter-02"
%%%

[Chapter PDF](print/chapter-02.pdf) · [Session 2](seminar/index.html#week-02)

A command can change the values available to a later expression. If $`x` initially holds 8, executing `x := 1; y := x + 3` leaves $`y` equal to 4. The second assignment reads an intermediate state. This chapter makes that state explicit in a derivation.

*Sources.* Read Glynn Winskel, _The Formal Semantics of Programming Languages_, §2.4, “The execution of commands.” Identify the premise that supplies the input to the second command in a sequence. We use the arithmetic fragment from Chapter 1 and write a terminating judgment as $`s \vdash c \Downarrow t`. The shared task is to derive the example above with its intermediate state fully specified. [Winskel, chapter 2.](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf)

# Syntax, guards, and states
%%%
tag := "ch02-s1"
%%%

Let $`V` be a set of names and $`\Sigma = \left( {V\rightarrow{\mathbb{Z}}} \right)` the set of integer states. In this chapter an arithmetic expression $`e` is built from integer literals, variables and addition as in Chapter 1. Its value in $`s` is $`\operatorname{eval}\left( {e,s} \right)`. For guards we allow truth constants, equality and order tests on arithmetic expressions, and Boolean negation. Write $`B\left( {b,s} \right)` for truth of guard $`b` in $`s`. Thus $`B\left( {x < 2,s} \right)` holds exactly when $`s(x) < 2`. Every guard on this grammar yields one truth value. A state update $`s\left\lbrack {x\mapsto n} \right\rbrack` sends $`x` to $`n` and every other name $`z` to $`s(z)`.

The commands are `skip`, assignment `x := e`, sequence `c; d`, conditional `if b then c else d`, and repetition `while b do c`. Parentheses fix the parse of nested commands. A state records the values of *all* names. Giving only the changed coordinates specifies the final state provided the other coordinates are understood to agree with the initial state.

State updates give a short calculation for detecting when two writes can be reordered. Fix distinct names `x` and `y`, and fix integers `a` and `b`. Compare the states obtained by writing `a` at `x` and `b` at `y` in opposite orders. To prove equality of the resulting functions, choose any name `z`. If it is `x`, both functions return `a`. If it is `y`, both return `b`. Every other lookup reaches the original state in either function. This establishes commutation for writes of *already determined integers* at distinct coordinates.

The corresponding claim about commands requires more. Run `x := 1; y := x` from a state where `x` holds zero. The writes address distinct names, yet the second right-hand side obtains its integer from the first updated store. In the reverse order `y` receives zero. A proof of commutation for command syntax therefore has to justify that each right-hand side yields the same integer after the other write. The coincidence lemma from Chapter 1 supplies this fact when neither command writes a free variable of the other expression. This separates two questions that are easy to collapse: which coordinate receives an update, and which coordinates determine the integer to be written.

# The execution relation
%%%
tag := "ch02-s2"
%%%

*Definition 2.1.* $`s \vdash c \Downarrow t` holds when there is a finite derivation by the rules below. A premise to the left of another premise need not be proved first, but a state name shared by two premises denotes the very same state. Below, $`I` abbreviates `if b then c else d`, and $`W` abbreviates `while b do c`.

$$`\frac{}{s \vdash \operatorname{skip} \Downarrow s}\quad\frac{}{s \vdash x \mathrel{:=} e \Downarrow s\left\lbrack {x\mapsto\operatorname{eval}\left( {e,s} \right)} \right\rbrack}`

$$`\frac{s \vdash c \Downarrow u\quad u \vdash d \Downarrow t}{s \vdash c\ \text{;}\ d \Downarrow t}`

$$`\frac{B\left( {b,s} \right)\quad s \vdash c \Downarrow t}{s \vdash I \Downarrow t}\quad\frac{\neg B\left( {b,s} \right)\quad s \vdash d \Downarrow t}{s \vdash I \Downarrow t}`

$$`\frac{\neg B\left( {b,s} \right)}{s \vdash W \Downarrow s}\quad\frac{B\left( {b,s} \right)\quad s \vdash c \Downarrow u\quad u \vdash W \Downarrow t}{s \vdash W \Downarrow t}`

In the assignment rule the right-hand side is evaluated in the old state. In the true loop rule, executing the body supplies $`u`. The recursive premise tests the guard anew in $`u`. The command in that premise is syntactically identical to the command at the root. A finite derivation may therefore have several nodes labelled with the same command.

Theorem 1.3 also allows an assignment rule with an explicit expression premise.

$$`\frac{\sigma \vdash e \Downarrow n}{\sigma \vdash x \mathrel{:=} e \Downarrow \sigma[x\mapsto n]}`

For example, if $`\sigma(x)=3`, the premise for `x := x + 4` yields $`n=7`. The conclusion updates the old store only after obtaining that integer. Either form derives the same final stores. Given an expression derivation, Theorem 1.3 identifies its result with the value in the assignment axiom. Conversely, the theorem supplies a derivation for that computed value. The axiom displayed in Definition 2.1 is the one used to count command derivations in Chapter 3. Recording the expression premise adds a subtree to the full derivation.

Winskel obtains the value of the right-hand side from an expression premise in his assignment rule (p. 20). Nipkow and Klein write $`(c,s)\Rightarrow t` for command execution and use their evaluator `aval a s` directly in the conclusion of the assignment axiom (p. 78). [Winskel, §2.4](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf#page=41) · [Concrete Semantics, §7.2.1, Fig. 7.1](https://concrete-semantics.org/concrete-semantics.pdf#page=88)

A rule can be read as a method for checking a proposed result. Consider `if x < y then x := y else y := x` in a state with coordinates `(2,5)`. A derivation ending in the else rule would require the assertion that 2 is at least 5. That premise cannot be produced. The remaining rule asks for a derivation of `x := y`. Its final state is forced by the assignment axiom, with coordinates `(5,5)` and all other names preserved. This reasoning eliminates an incorrect candidate such as `(5,2)` even though that candidate contains the two original integers.

Reading the rules from the bottom upwards does not always give an immediately terminating procedure. To construct a tree for a loop in a known input state, the guard determines which last rule could apply. A true guard still leaves a new loop judgment as a premise. Selecting the correct rule again and again may generate an infinite list of outstanding obligations. An execution judgment demands a finite tree in which all such branches close. By contrast, given a *completed* candidate tree, every node can be checked against its constructor and local guard conditions in a finite traversal.

# Sequential composition
%%%
tag := "ch02-s3"
%%%

*Proposition 2.2.* For all commands $`c,d` and states $`s,t`,

$$`s \vdash c\ \text{;}\ d \Downarrow t\Longleftrightarrow\exists u \in \Sigma,\; (s \vdash c \Downarrow u) \land (u \vdash d \Downarrow t).`

*Proof.* Given the derivation on the left, examine its final rule. Its conclusion has sequence at the root, so it must have arisen by the sequence rule. Its two premise derivations and their shared state witness the right side. Conversely choose the state and the two derivations supplied on the right. Place them under a new application of the sequence rule. The tree is finite because both of its subtrees are finite. $`\square`

*Worked derivation.* Let $`x \neq y`, let $`s(x) = 8`, and put $`u = s\left\lbrack {x\mapsto 1} \right\rbrack` and $`t = u\left\lbrack {y\mapsto 4} \right\rbrack`. The assignment axiom gives $`s \vdash x \mathrel{:=} 1 \Downarrow u`. Since $`u(x) = 1`, the equation for addition gives $`\operatorname{eval}\left( {x + 3,u} \right) = 4` and the assignment axiom gives $`u \vdash y \mathrel{:=} x + 3 \Downarrow t`. Proposition 2.2 combines these derivations. In particular $`t(x) = 1`, $`t(y) = 4`, and $`t(z) = s(z)` for any other name $`z`. Replacing $`u` with $`s` in the second calculation yields 11, a useful way to detect a disconnected pair of premise trees.

An intermediate state is hidden by the conclusion even when it contains information absent at both endpoints. For an explicit instance, initialize two distinct variables to zero and execute `x := 1; x := 0`. Both the initial and the final store have zero at `x`. Neither can be used as the witness required by the sequence rule: the conclusion of the first assignment forces one at that coordinate. The hidden store contains exactly the information the second premise must receive.

This observation permits a useful proof of reassociation. Invert a derivation of `(a; b); c` twice to expose states `u` and `v` such that `a` runs from the initial state to `u`, `b` runs from `u` to `v`, and `c` runs from `v` to the final state. Assemble the last two derivations first, producing a derivation of `b; c` from `u`. Combine that with the first derivation to obtain an execution of `a; (b; c)`. The converse reassembles the same three pieces in the opposite grouping. This argument changes the internal tree shape while preserving its intermediate *states* and the order of the constituent computations.

Here is the intermediate-store calculation on two integer coordinates. The first command copies the left coordinate to the right; the second adds the two current values into the left coordinate. Giving the second function the original input would instead leave the original right coordinate in the sum.

```lean
example (x y : Int) :
    (let copyRight := fun s : Int × Int => (s.1, s.1)
     let addLeft := fun s : Int × Int => (s.1 + s.2, s.2)
     addLeft (copyRight (x, y))) = (x + x, x) := by
  rfl
```

# A finite loop derivation
%%%
tag := "ch02-s4"
%%%

Take `while x < 1 do x := x + 1` with $`s(x) = 0`. Write $`u = s\left\lbrack {x\mapsto 1} \right\rbrack`. In $`s` the guard is true and the body has an assignment derivation ending in $`u`. In $`u` the guard is false, so the exit rule gives $`u \vdash W \Downarrow u`. These are exactly the premises of the true loop rule for $`s \vdash W \Downarrow u`. The proof contains one execution of the body and two tests of the guard.

The relation gives information about terminating executions. For `while true do skip` no finite tree exists. In a purported tree the exit rule is impossible and the true rule requires a strictly smaller derivation for the same loop from the same state. Choosing a derivation of minimal height would contradict this decrease. Chapter 4 gives a positive account of the infinite execution.

For the incrementing loop above, one can count the necessary rule uses without fixing the values of any unrelated variables. If the initial value of `x` is an integer `j ≤ 1`, the number of body executions is `1 − j`. Prove this by induction on that natural number. At zero the old value is already one. The guard is false, so the exit rule gives a derivation with no assignments. At a positive distance the old value is below one. The assignment rule increases it by one, preserving all other lookups, and the new distance is the previous distance minus one. The induction hypothesis supplies a complete loop derivation from that intermediate state. Place the assignment and recursive derivations beneath the true rule. This constructs a tree and counts its body executions at the same time.

For initial values larger than one, the guard is also false and the final value is the initial one. Thus the postcondition `x = 1` needs an input hypothesis even though the loop terminates for every integer. The result for arbitrary inputs is `x = max(j,1)` with the unchanged coordinates inherited from the original state. A single worked trace would not reveal the distinction between those two specifications.

# Exercises
%%%
tag := "ch02-s5"
number := false
%%%

*2.1.* Start at $`s(x) = 2` and execute `y := x; x := x + y`, with distinct names. Write down the entire intermediate and final states as updates of $`s`.

*2.2.* Prove that `skip; d` and $`d` have the same terminating initial–final state pairs.

*2.3.* Construct the loop derivation in §2.4 starting from $`s(x) = - 1`. How many uses of each loop rule appear?

*Further problem.* Add a simultaneous assignment `(x,y) := (e,f)` for distinct names. Give a big-step rule by evaluating both expressions in the input store. Derive its result when it swaps `x` and `y`. Characterize exactly when the two successive assignments `x := y; y := x` have that same result.

# Reading for the Seminar
%%%
tag := "ch02-s6"
number := false
%%%

*Definitions · 10 minutes.* Write the state update and the sequence rule. Give the initial value 8 and leave the intermediate state unnamed.

*Joint proof · 30 minutes.* Ask two participants to derive the assignments in §2.3. The second chooses its input by reading the first conclusion. Join both premises and prove Proposition 2.2 in both directions.

*Proof review · 20 minutes.* Change the order of the assignments. Identify which premise still has the old input. Ask a reader to reconstruct the loop exit in §2.4.

*Facilitator’s hint.* Write three state columns labelled initial, intermediate, final. Match each judgment to two endpoints before evaluating its expression.

# Solutions and Further Reading
%%%
tag := "ch02-s7"
number := false
%%%

*2.1.* The middle state is $`u = s\left\lbrack {y\mapsto 2} \right\rbrack`. Both $`u(x)` and $`u(y)` equal 2, so the final state is $`u\left\lbrack {x\mapsto 4} \right\rbrack`. All names outside the two updated coordinates retain their original values.

*2.2.* Proposition 2.2 yields a witness $`u`. Inverting the skip axiom forces $`u = s`, leaving $`s \vdash d \Downarrow t`. In the reverse direction choose $`u = s`, use skip and the given derivation for $`d`, and apply sequence.

*2.3.* The first body execution sets $`x` to 0 and the second sets it to 1. Build the proof from the final state upwards with one exit rule and two true rules. Each true rule also needs its own body derivation.

For a Lean comparison, inspect the constructors of `cexec`. Its conditional constructor delegates to the branch selected by a Boolean test. The two conditional rules in Definition 2.1 display that choice as a premise. The integer store in the Leroy port matches this chapter. The Lean exercises of _The Hitchhiker’s Guide to Logical Verification_, §9.3, use their own arithmetic model. [Leroy course, Imp.lean.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean) [Hitchhiker’s Guide, 2026 course files.](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

*Further problem.* Let `m = eval(e,s)` and `n = eval(f,s)`. The new rule concludes that the command executes from `s` to `s[x ↦ m][y ↦ n]`. There are no command premises. Both expressions have already been evaluated in `s`, and distinctness of the destination names ensures that either order of the two updates gives the same store. For a swap substitute `e = y` and `f = x`. At the two names the resulting store has values `s(y)` and `s(x)` respectively; all other names keep their old values.

For the sequence, the first assignment produces `u = s[x ↦ s(y)]`. The second reads `u(x) = s(y)` and writes that value to `y`. Its result thus has `s(y)` in both positions. Equality at `y` with the simultaneous result forces `s(x) = s(y)`. Conversely, if this equality holds, comparison at each of the two destinations and every other name proves equality of the full stores. Commutation of updates at distinct destinations alone does not justify sequential evaluation of the expressions.
