import VersoManual
import PLBook.IMP.Determinacy

open Verso.Genre Manual

#doc (Manual) "Big-Step Semantics of Commands" =>
%%%
tag := "ch02"
file := "chapter-02"
%%%

* *Definitions.* Stores, update and expression evaluation (Session 1, Definitions 1.2–1.3). Guard evaluation and command execution use [IMP language card A.4–A.5](imp-card/index.html#imp-a4).
* *New terms.* Guard, execution judgment, sequencing, derived rule, height of a derivation. [Glossary and label key](glossary/index.html)
* *Proposition 2.2 \[This book\] \[Checked\].* For any commands $`c,d` and stores $`s,t`, $`s\vdash(c;d)\Downarrow t` if and only if some store $`u` satisfies both $`s\vdash c\Downarrow u` and $`u\vdash d\Downarrow t`.
* *Source.* The guards, commands and six execution rules follow Leroy’s IMP. \[Corresponding: CS §7.2.3\] Nipkow and Klein derive the sequence equivalence for their execution relation. [Formalization](imp-card/index.html#imp-sources) · [Concrete Semantics, pp. 81–82](https://concrete-semantics.org/concrete-semantics.pdf)
* *Board case.* Derive `x := 1; y := x + 3`, name the intermediate store, and recover it from the completed tree.
* *Proof outline.* Invert the last rule of a sequence derivation to obtain a witness and two premises. Conversely, join the given premise trees with the sequence rule.
* *From Session 1.* Both operands of a sum are evaluated in the same store. The second command in a sequence starts in the store produced by the first.

A command can change the values available to a later expression. If $`x` initially holds 8, executing `x := 1; y := x + 3` leaves $`y` equal to 4. The second assignment reads an intermediate store. This chapter makes that store explicit in a derivation.

# Syntax, guards, and stores
%%%
tag := "ch02-s1"
%%%

Use $`\mathrm{eval}(e,s)` and $`s[x\mapsto n]` as in Session 1, Definitions 1.2–1.3. For instance, the guard $`x\le2` evaluates to true in a store where $`s(x)=1`.

A Boolean expression has one of six forms:

$$`b ::= \mathsf{true}\mid\mathsf{false}\mid(e_1=e_2)\mid(e_1\le e_2)\mid\neg b\mid(b_1\land b_2).`

Its value $`B(b,s)` is a Boolean. Constants give their own values. Comparisons test the integer values of both operands in $`s`. Negation exchanges true and false. Conjunction returns true exactly when both operands return true. In programs, $`e_1<e_2` abbreviates $`\neg(e_2\le e_1)`, $`e_1\ne e_2` abbreviates $`\neg(e_1=e_2)`, and $`p\lor q` abbreviates $`\neg(\neg p\land\neg q)`.

$$`c ::= \mathsf{skip}\mid x:=e\mid(c_1;c_2)\mid
\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\mid
\mathsf{while}\ b\ \mathsf{do}\ c.`

The Boolean expression controlling a conditional or loop is its *guard*.

Parentheses fix the parse of nested commands. A store records the values of *all* names. Giving only the changed coordinates specifies the final store provided the other coordinates are understood to agree with the initial store.

# The execution relation
%%%
tag := "ch02-s2"
%%%

*Definition 2.1 (Execution judgment).* In a *big-step semantics*, a judgment relates an entire computation to its result. The following six rules define $`s\vdash c\Downarrow t`. The judgment holds precisely when it has a finite derivation. Skip leaves the store unchanged. Assignment evaluates the right-hand side in the initial store. Sequencing binds its two premises through the intermediate store $`m`.

$$`\frac{}{s\vdash\mathsf{skip}\Downarrow s}\qquad
\frac{}{s\vdash x:=e\Downarrow s[x\mapsto\mathrm{eval}(e,s)]}`

$$`\frac{s\vdash c\Downarrow m\quad m\vdash d\Downarrow t}{s\vdash(c;d)\Downarrow t}`

For $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`, let $`k` denote $`c` when $`B(b,s)` is true and $`d` otherwise. There is one conditional rule:

$$`\frac{s\vdash k\Downarrow t}{s\vdash I\Downarrow t}`

Substituting either Boolean value for the guard gives a *derived rule*: every instance follows by applying the defining rule with that value.

Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c`. The guard tests above the lines below are *side conditions*. Evaluate the Boolean function to check each equality. Only a premise of the form $`s\vdash c\Downarrow t` requires an execution subderivation. A false guard ends the loop. A true guard requires both an execution of the body and a further execution of the loop starting in the body’s final store.

$$`\frac{B(b,s)=\mathsf{false}}{s\vdash W\Downarrow s}\qquad
\frac{B(b,s)=\mathsf{true}\quad s\vdash c\Downarrow m\quad m\vdash W\Downarrow t}{s\vdash W\Downarrow t}`

In the true loop rule, executing the body supplies $`m`. The recursive premise tests the guard anew in $`m`. The command in that premise is syntactically identical to the command at the root. A finite derivation may therefore have several nodes labelled with the same command.

*Conditional, true and false cases \[This book\] \[Corresponding: CS IfTrue, IfFalse\] \[Checked\].* The single conditional rule specializes to the following two derived rules.

$$`\frac{B(b,s)=\mathsf{true}\quad s\vdash c\Downarrow t}{s\vdash I\Downarrow t}
\qquad
\frac{B(b,s)=\mathsf{false}\quad s\vdash d\Downarrow t}{s\vdash I\Downarrow t}`

For the left rule the selected command is $`c`, so its given derivation supplies the premise of the conditional rule. The right rule follows by the same calculation with $`d`. Inverting a conditional execution therefore gives a derivation for the selected branch even before we distinguish the two Boolean values.

A rule can be read as a method for checking a proposed result. Consider `if x < y then x := y else y := x` in a store with coordinates $`(s(x),s(y))=(2,5)` for distinct names $`x,y`. Here the guard is true, so the single defining rule requires a derivation of `x := y`. Its final store is forced by the assignment axiom, with coordinates `(5,5)` and all other names preserved. This reasoning eliminates an incorrect candidate such as `(5,2)` even though that candidate contains the two original integers.

Reading the rules from the bottom upwards does not always give an immediately terminating procedure. To construct a tree for a loop in a known input store, the guard determines which last rule could apply. A true guard still leaves a new loop judgment as a premise. Selecting the correct rule again and again may generate an infinite list of outstanding obligations. An execution judgment demands a finite tree in which all such branches close. By contrast, given a *completed* candidate tree, every node can be checked against its constructor and local guard conditions in a finite traversal.

# Sequential composition
%%%
tag := "ch02-s3"
%%%

*Proposition 2.2 (Sequence inversion) \[This book\] \[Checked\].* For all commands $`c,d` and stores $`s,t`,

$$`s \vdash c\ \text{;}\ d \Downarrow t\Longleftrightarrow\exists u \in \Sigma,\; (s \vdash c \Downarrow u) \land (u \vdash d \Downarrow t).`

*Proof.* Given the derivation on the left, examine its final rule.

1. Its conclusion has sequence at the root, so it must have arisen by the sequence rule.
2. Read the store $`u` from the conclusion of its left premise $`s\vdash c\Downarrow u`. Its right premise is $`u\vdash d\Downarrow t`. These two derivations and their shared store witness the right side.
3. Conversely choose the store and the two derivations supplied on the right. Place them under a new application of the sequence rule. The tree is finite because both of its subtrees are finite. $`\square`

*Worked derivation.* Let $`x \neq y`, let $`s(x) = 8`, and put $`u = s\left\lbrack {x\mapsto 1} \right\rbrack` and $`t = u\left\lbrack {y\mapsto 4} \right\rbrack`. The assignment axiom gives $`s \vdash x \mathrel{:=} 1 \Downarrow u`. Since $`u(x) = 1`, the equation for addition gives $`\operatorname{eval}\left( {x + 3,u} \right) = 4` and the assignment axiom gives $`u \vdash y \mathrel{:=} x + 3 \Downarrow t`. Proposition 2.2 combines these derivations. In particular $`t(x) = 1`, $`t(y) = 4`, and $`t(z) = s(z)` for any other name $`z`. Replacing $`u` with $`s` in the second calculation yields 11, a useful way to detect a disconnected pair of premise trees.

$$`\frac{\dfrac{}{s\vdash x:=1\Downarrow u}\qquad
\dfrac{}{u\vdash y:=x+3\Downarrow t}}
{s\vdash(x:=1\,;\,y:=x+3)\Downarrow t}`

Reading upwards from the root recovers this very $`u` as the witness. Proposition 2.2 asserts the existence of such a store. Comparing the witnesses of two different trees is the subject of Session 3.

An intermediate store is hidden by the conclusion even when it contains information absent at both endpoints. For an explicit instance, initialize `x` to zero and execute `x := 1; x := 0`. Both the initial and the final store have zero at `x`. Neither can be used as the witness required by the sequence rule: the conclusion of the first assignment forces one at that coordinate. The hidden store contains exactly the information the second premise must receive.

# A finite loop derivation
%%%
tag := "ch02-s4"
%%%

Take `while x < 1 do x := x + 1` with $`s(x) = 0`. By [A.4](imp-card/index.html#imp-a4), $`e_1<e_2` abbreviates $`\neg(e_2\le e_1)`, so this guard tests $`\neg(1\le x)`. Write $`u = s\left\lbrack {x\mapsto 1} \right\rbrack`. In $`s` the guard is true and the body has an assignment derivation ending in $`u`. In $`u` the guard is false, so the exit rule gives $`u \vdash W \Downarrow u`. These are exactly the premises of the true loop rule for $`s \vdash W \Downarrow u`. The proof contains one execution of the body and two tests of the guard.

The *height of an execution derivation* is zero when its last rule has no execution premises. Otherwise it is one plus the greatest height of an immediate execution subderivation. In the example the assignment and exit each have height zero. The iteration that joins them has height one. The Boolean tests are side conditions in Definition 2.1.

The relation gives information about terminating executions. For `while true do skip` no finite tree exists. Suppose there were such a tree from $`s` to $`t` and choose one of least height for those endpoints. Its last rule must be iteration. Its first premise executes skip and therefore ends in $`s`. Its second premise derives the very same loop judgment from $`s` to $`t` at smaller height, a contradiction. Chapter 5 gives a positive account of the infinite execution.

# Exercises
%%%
tag := "ch02-s5"
number := false
%%%

*2.1.* Start at $`s(x) = 2` and execute `y := x; x := x + y`, with distinct names. Write down the entire intermediate and final stores as updates of $`s`.

*2.2.* Prove that `skip; d` and $`d` have the same terminating initial–final store pairs.

*2.3.* Construct the loop derivation in §2.4 starting from $`s(x) = - 1`. How many uses of each loop rule appear?

*Further problem.* Add a simultaneous assignment `(x,y) := (e,f)` for distinct names. Give a big-step rule by evaluating both expressions in the input store. Derive its result when it swaps `x` and `y`. Characterize exactly when the two successive assignments `x := y; y := x` have that same result.

# Reading for the Seminar
%%%
tag := "ch02-s6"
number := false
%%%

*Definitions · 10 minutes.* Write the store update and the sequence rule. Give the initial value 8 and leave the intermediate store unnamed.

*Joint proof · 30 minutes.* Ask two participants to derive the assignments in §2.3. The second chooses its input by reading the first conclusion. Join both premises and prove Proposition 2.2 in both directions.

*Proof review · 20 minutes.* Change the order of the assignments. Identify which premise still has the old input. Ask a reader to reconstruct the loop exit in §2.4.

*Facilitator’s hint.* Write three store columns labelled initial, intermediate, final. Match each judgment to two endpoints before evaluating its expression.

# Solutions and Further Reading
%%%
tag := "ch02-s7"
number := false
%%%

*2.1.* The middle store is $`u = s\left\lbrack {y\mapsto 2} \right\rbrack`. Both $`u(x)` and $`u(y)` equal 2, so the final store is $`u\left\lbrack {x\mapsto 4} \right\rbrack`. All names outside the two updated coordinates retain their original values.

*2.2.* Proposition 2.2 yields a witness $`u`. Inverting the skip axiom forces $`u = s`, leaving $`s \vdash d \Downarrow t`. In the reverse direction choose $`u = s`, use skip and the given derivation for $`d`, and apply sequence.

*2.3.* The first body execution sets $`x` to 0 and the second sets it to 1. Build the proof from the final store upwards with one exit rule and two true rules. Each true rule also needs its own body derivation.

*Further problem.* Let `m = eval(e,s)` and `n = eval(f,s)`. The new rule concludes that the command executes from `s` to `s[x ↦ m][y ↦ n]`. There are no command premises. Both expressions have already been evaluated in `s`, and distinctness of the destination names ensures that either order of the two updates gives the same store. For a swap substitute `e = y` and `f = x`. At the two names the resulting store has values `s(y)` and `s(x)` respectively; all other names keep their old values.

For the sequence, the first assignment produces `u = s[x ↦ s(y)]`. The second reads `u(x) = s(y)` and writes that value to `y`. Its result thus has `s(y)` in both positions. Equality at `y` with the simultaneous result forces `s(x) = s(y)`. Conversely, if this equality holds, comparison at each of the two destinations and every other name proves equality of the full stores. Commutation of updates at distinct destinations alone does not justify sequential evaluation of the expressions.

*Further reading · Reordering and regrouping commands.*

Store updates give a short calculation for detecting when two writes can be reordered. Fix distinct names `x` and `y`, and fix integers `a` and `b`. Compare the stores obtained by writing `a` at `x` and `b` at `y` in opposite orders. To prove equality of the resulting functions, choose any name `z`. If it is `x`, both functions return `a`. If it is `y`, both return `b`. Every other lookup reaches the original store in either function. This establishes commutation for writes of *already determined integers* at distinct coordinates.

The corresponding claim about commands requires more. Run `x := 1; y := x` from a store where `x` holds zero. The writes address distinct names, yet the second right-hand side obtains its integer from the first updated store. In the reverse order `y` receives zero. A proof of commutation for command syntax therefore has to justify that each right-hand side yields the same integer after the other write. The coincidence lemma (Session 1, Lemma 1.1) supplies this fact when neither command writes a free variable of the other expression. This separates two questions that are easy to collapse: which coordinate receives an update, and which coordinates determine the integer to be written.

This observation permits a useful proof of reassociation. Invert a derivation of `(a; b); c` twice to expose stores `u` and `v` such that `a` runs from the initial store to `u`, `b` runs from `u` to `v`, and `c` runs from `v` to the final store. Assemble the last two derivations first, producing a derivation of `b; c` from `u`. Combine that with the first derivation to obtain an execution of `a; (b; c)`. The converse reassembles the same three pieces in the opposite grouping. This argument changes the internal tree shape while preserving its intermediate *stores* and the order of the constituent computations.

Here is the intermediate-store calculation on two integer coordinates. The first command copies the left coordinate to the right; the second adds the two current values into the left coordinate. Giving the second function the original input would instead leave the original right coordinate in the sum.

Writing $`(a,b)` for the two initial values, the calculation is $`(a,b)\mapsto(a,a)\mapsto(a+a,a)`.

*Further reading · Assignment rules.*

Theorem 1.3 also allows an assignment rule with an explicit expression premise.

$$`\frac{s \vdash e \Downarrow n}{s \vdash x \mathrel{:=} e \Downarrow s[x\mapsto n]}`

For example, if $`s(x)=3`, the premise for `x := x + 4` yields $`n=7`. The conclusion updates the old store only after obtaining that integer. Either form derives the same final stores. Given an expression derivation, Theorem 1.3 identifies its result with the value in the assignment axiom. Conversely, the theorem supplies a derivation for that computed value. The axiom displayed in Definition 2.1 is the one used to count command derivations in Chapter 3. Recording the expression premise adds a subtree to the full derivation.

Winskel obtains the value of the right-hand side from an expression premise in his assignment rule (p. 20). Nipkow and Klein write $`(c,s)\Rightarrow t` for command execution and use their evaluator `aval a s` directly in the conclusion of the assignment axiom (p. 78). [Winskel, §2.4](https://www.cin.ufpe.br/~if721/intranet/TheFormalSemanticsofProgrammingLanguages.pdf#page=41) · [Concrete Semantics, §7.2.1, Fig. 7.1](https://concrete-semantics.org/concrete-semantics.pdf#page=88)

*Further reading · Counting loop iterations.*

For the incrementing loop above, one can count the necessary rule uses without fixing the values of any unrelated variables. If the initial value of `x` is an integer `j ≤ 1`, the number of body executions is `1 − j`. Prove this by induction on that natural number. At zero the old value is already one. The guard is false, so the exit rule gives a derivation with no assignments. At a positive distance the old value is below one. The assignment rule increases it by one, preserving all other lookups, and the new distance is the previous distance minus one. The induction hypothesis supplies a complete loop derivation from that intermediate store. Place the assignment and recursive derivations beneath the true rule. This constructs a tree and counts its body executions at the same time.

For initial values larger than one, the guard is also false and the final value is the initial one. Thus the postcondition `x = 1` needs an input hypothesis even though the loop terminates for every integer. The result for arbitrary inputs is `x = max(j,1)` with the unchanged coordinates inherited from the original store. A single worked trace would not reveal the distinction between those two specifications.

For the source presentation of the single conditional rule, see the [IMP language card](imp-card/index.html#imp-sources). For exercises using a different arithmetic model, see _The Hitchhiker’s Guide to Logical Verification_, §9.3. [Course materials](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)
