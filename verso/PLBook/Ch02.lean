import VersoManual
import PLBook.IMP.Determinacy

open Verso.Genre Manual

#doc (Manual) "Big-Step Semantics of Commands" =>
%%%
tag := "ch02"
file := "chapter-02"
%%%

A command can change the values available to a later expression. If $`x` initially holds 8, executing `x := 1; y := x + 3` leaves $`y` equal to 4. The second assignment reads an intermediate state. This chapter makes that state explicit in a derivation.

*In this session.*

* *Definitions.* States, update and expression evaluation (Session 1, Definitions 1.2–1.3). Guard evaluation and command execution use [IMP language card A.4–A.5](imp-card/index.html#imp-a4).
* *New terms.* Guard, execution judgment, sequencing, derived rule, height of a derivation. [Glossary](glossary/index.html)
* *Proposition 2.2 (Sequence inversion).* For any commands $`c,d` and states $`\sigma,\sigma'`, $`\sigma\vdash(c;d)\Downarrow\sigma'` if and only if some state $`\sigma_1` satisfies both $`\sigma\vdash c\Downarrow\sigma_1` and $`\sigma_1\vdash d\Downarrow\sigma'`.
* *Board case.* Derive `x := 1; y := x + 3`, name the intermediate state, and recover it from the completed tree.
* *Proof outline.* Invert the last rule of a sequence derivation to obtain a witness and two premises. Conversely, join the given premise trees with the sequence rule.
* *From Session 1.* Both operands of a sum are evaluated in the same state. The second command in a sequence starts in the state produced by the first.

# Syntax, guards, and states
%%%
tag := "ch02-s1"
%%%

Use $`\mathrm{eval}(e,\sigma)` and $`\sigma[x\mapsto n]` as in Session 1, Definitions 1.2–1.3. For instance, the test $`x\le2` is true in a state where $`\sigma(x)=1`.

A Boolean expression has one of six forms:

$$`b ::= \mathsf{true}\mid\mathsf{false}\mid(e_1=e_2)\mid(e_1\le e_2)\mid\neg b\mid(b_1\land b_2).`

Its value $`B(b,\sigma)` is a Boolean. Constants give their own values. Comparisons test the integer values of both operands in $`\sigma`. Negation exchanges true and false. Conjunction returns true exactly when both operands return true. In programs, $`e_1<e_2` abbreviates $`\neg(e_2\le e_1)`, $`e_1\ne e_2` abbreviates $`\neg(e_1=e_2)`, and $`b_1\lor b_2` abbreviates $`\neg(\neg b_1\land\neg b_2)`.

$$`c ::= \mathsf{skip}\mid x:=e\mid(c_1;c_2)\mid
\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\mid
\mathsf{while}\ b\ \mathsf{do}\ c.`

The Boolean expression controlling a conditional or loop is its *guard*.

Parentheses fix the parse of nested commands. A state records the values of *all* names. Giving only the changed coordinates specifies the final state provided the other coordinates are understood to agree with the initial state.

# The execution relation
%%%
tag := "ch02-s2"
%%%

Session 1 wrote $`\sigma\vdash e\Downarrow n` for evaluation. For a command $`c`, the *execution judgment* $`\sigma\vdash c\Downarrow\sigma'` asserts that $`c`, started in state $`\sigma`, terminates in state $`\sigma'`.

*Definition 2.1 (Execution judgment).* In a *big-step semantics*, a judgment relates an entire computation to its result. The following six rules define $`\sigma\vdash c\Downarrow\sigma'`. The judgment holds precisely when it has a finite derivation. Skip leaves the state unchanged. Assignment evaluates the right-hand side in the initial state. *Sequencing* runs the second command from the final state of the first: the sequence rule binds its two premises through the intermediate state $`\sigma_1`.

$$`\frac{}{\sigma\vdash\mathsf{skip}\Downarrow\sigma}\qquad
\frac{}{\sigma\vdash x:=e\Downarrow\sigma[x\mapsto\mathrm{eval}(e,\sigma)]}`

$$`\frac{\sigma\vdash c\Downarrow\sigma_1\quad \sigma_1\vdash d\Downarrow\sigma'}{\sigma\vdash(c;d)\Downarrow\sigma'}`

For $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`, let $`k` denote $`c` when $`B(b,\sigma)` is true and $`d` otherwise. There is one conditional rule:

$$`\frac{\sigma\vdash k\Downarrow\sigma'}{\sigma\vdash I\Downarrow\sigma'}`

Fixing the value of $`B(b,\sigma)`, as true or as false, gives a *derived rule*: each of its instances follows by one application of the defining rule. The guard $`b` itself is not replaced.

Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c`. The guard tests above the lines below are *side conditions*. Evaluate the Boolean function to check each equality. Only the execution judgments above a line, the rule's execution premises, require subderivations. A false guard ends the loop. A true guard requires both an execution of the body and a further execution of the loop starting in the body’s final state.

$$`\frac{B(b,\sigma)=\mathsf{false}}{\sigma\vdash W\Downarrow\sigma}\qquad
\frac{B(b,\sigma)=\mathsf{true}\quad \sigma\vdash c\Downarrow\sigma_1\quad \sigma_1\vdash W\Downarrow\sigma'}{\sigma\vdash W\Downarrow\sigma'}`

We refer to the six rules as the skip, assignment, sequence, conditional, loop exit and loop iteration rules.

In the loop iteration rule, executing the body supplies $`\sigma_1`. The recursive premise tests the guard anew in $`\sigma_1`. The command in that premise is syntactically identical to the command at the root. A finite derivation may therefore have several nodes labelled with the same command.

*Conditional, true and false cases.* The single conditional rule specializes to the following two derived rules.

$$`\frac{B(b,\sigma)=\mathsf{true}\quad \sigma\vdash c\Downarrow\sigma'}{\sigma\vdash I\Downarrow\sigma'}
\qquad
\frac{B(b,\sigma)=\mathsf{false}\quad \sigma\vdash d\Downarrow\sigma'}{\sigma\vdash I\Downarrow\sigma'}`

For the left rule the selected command is $`c`, so its given derivation supplies the premise of the conditional rule. The right rule follows by the same calculation with $`d`. Conversely, the single conditional rule is the only rule whose conclusion is a conditional. Inverting a derivation of $`\sigma\vdash I\Downarrow\sigma'` therefore gives a derivation of $`\sigma\vdash k\Downarrow\sigma'` for the selected command $`k`, before we distinguish the two Boolean values.

A rule can be read as a method for checking a proposed result. Consider `if x < y then x := y else y := x` in a state with $`(\sigma(x),\sigma(y))=(2,5)` for distinct names $`x,y`. By A.4 the guard $`x<y` abbreviates $`\neg(y\le x)`. Since $`5\le2` is false, the guard is true, so $`k` is `x := y` and the single conditional rule requires a derivation of $`\sigma\vdash x:=y\Downarrow\sigma'`. Its final state is forced by the assignment rule, with coordinates `(5,5)` and all other names preserved. This reasoning eliminates an incorrect candidate such as `(5,2)` even though that candidate contains the two original integers.

Reading the rules from the bottom upwards does not always give an immediately terminating procedure. To construct a tree for a loop in a known input state, the guard determines which last rule could apply. A true guard still leaves a new loop judgment as a premise. Selecting the correct rule again and again may generate an infinite list of outstanding obligations. An execution judgment demands a finite tree in which all such branches close. By contrast, given a *completed* candidate tree, every node can be checked against its constructor and local guard conditions in a finite traversal.

# Sequencing
%%%
tag := "ch02-s3"
%%%

*Worked derivation.* Let $`x \neq y`, let $`\sigma(x) = 8`, and put $`\sigma_1 = \sigma\left\lbrack {x\mapsto 1} \right\rbrack` and $`\sigma' = \sigma_1\left\lbrack {y\mapsto 4} \right\rbrack`. The assignment rule gives $`\sigma \vdash x \mathrel{:=} 1 \Downarrow \sigma_1`. Since $`\sigma_1(x) = 1`, the equation for addition gives $`\operatorname{eval}\left( {x + 3,\sigma_1} \right) = 4` and the assignment rule gives $`\sigma_1 \vdash y \mathrel{:=} x + 3 \Downarrow \sigma'`. The sequence rule combines these derivations. In particular $`\sigma'(x) = 1`, $`\sigma'(y) = 4`, and $`\sigma'(z) = \sigma(z)` for any other name $`z`. Replacing $`\sigma_1` with $`\sigma` in the second calculation yields 11, a useful way to detect a disconnected pair of premise trees.

$$`\frac{\dfrac{}{\sigma\vdash x:=1\Downarrow\sigma_1}\qquad
\dfrac{}{\sigma_1\vdash y:=x+3\Downarrow\sigma'}}
{\sigma\vdash(x:=1\,;\,y:=x+3)\Downarrow\sigma'}`

Reading upwards from the root recovers this very $`\sigma_1` as the witness.

*Proposition 2.2 (Sequence inversion).* For all commands $`c,d` and states $`\sigma,\sigma'`,

$$`\sigma \vdash c\ \text{;}\ d \Downarrow \sigma'\Longleftrightarrow\exists \sigma_1 \in \Sigma,\; (\sigma \vdash c \Downarrow \sigma_1) \land (\sigma_1 \vdash d \Downarrow \sigma').`

*Proof.* Suppose $`D` is a derivation of $`\sigma\vdash(c;d)\Downarrow\sigma'`. Examine its last rule.

1. The command in the conclusion of $`D` is a sequence. Among the six rules of Definition 2.1, only the sequence rule has a sequence in its conclusion. By inversion (Session 1, §1.4), $`D` ends with the sequence rule applied to the commands $`c,d` and the states $`\sigma,\sigma'`.
2. That rule has premises $`\sigma\vdash c\Downarrow\sigma_1` and $`\sigma_1\vdash d\Downarrow\sigma'` for some state $`\sigma_1`. The two premise derivations witness the right side.
3. Conversely, take the state $`\sigma_1` and the derivations of $`\sigma\vdash c\Downarrow\sigma_1` and $`\sigma_1\vdash d\Downarrow\sigma'` supplied on the right. Apply the sequence rule. The tree is finite because both of its subtrees are finite. $`\square`

Proposition 2.2 states that every derivation of a sequence contains such a state. Comparing the witnesses of two different trees is the subject of Session 3.

An intermediate state is hidden by the conclusion even when it contains information absent at both endpoints. For an explicit instance, initialize `x` to zero and execute `x := 1; x := 0`. Both the initial and the final state have zero at `x`. Neither can be used as the witness required by the sequence rule: the conclusion of the first assignment forces one at that coordinate. The hidden state contains exactly the information the second premise must receive.

# A finite loop derivation
%%%
tag := "ch02-s4"
%%%

Take `while x < 1 do x := x + 1` with $`\sigma(x) = 0`. By [A.4](imp-card/index.html#imp-a4), $`e_1<e_2` abbreviates $`\neg(e_2\le e_1)`, so this guard tests $`\neg(1\le x)`. Write $`\sigma_1 = \sigma\left\lbrack {x\mapsto 1} \right\rbrack`. In $`\sigma` the guard is true and the body has an assignment derivation ending in $`\sigma_1`. In $`\sigma_1` the guard is false, so the loop exit rule gives $`\sigma_1 \vdash W \Downarrow \sigma_1`. These are exactly the premises of the loop iteration rule for $`\sigma \vdash W \Downarrow \sigma_1`. The proof contains one execution of the body and two tests of the guard.

The *height of an execution derivation* is zero when its last rule has no execution premises. Otherwise it is one plus the greatest height of an immediate execution subderivation. In the example the derivations ending with the assignment and loop exit rules each have height zero. The derivation joining them by the loop iteration rule has height one. The Boolean tests are side conditions in Definition 2.1.

The relation gives information about terminating executions. Write $`W=\mathsf{while}\ \mathsf{true}\ \mathsf{do}\ \mathsf{skip}`. No finite tree has a conclusion of the form $`\sigma\vdash W\Downarrow\sigma'`. Suppose there were such a tree, and choose one of least height for those endpoints $`\sigma,\sigma'`. Only the loop exit rule and the loop iteration rule conclude a loop judgment. The loop exit rule needs $`B(\mathsf{true},\sigma)=\mathsf{false}`, but the constant has value true, so the last rule is the loop iteration rule. Its body premise is $`\sigma\vdash\mathsf{skip}\Downarrow\sigma_1` for some state $`\sigma_1`. Only the skip rule concludes a skip judgment, so inversion gives $`\sigma_1=\sigma`. Its loop premise is therefore $`\sigma\vdash W\Downarrow\sigma'`, the very same judgment, and by the definition of height its subderivation has smaller height. This contradicts the choice of a tree of least height. Session 5 gives a positive account of the infinite path.

# Exercises
%%%
tag := "ch02-s5"
number := false
%%%

*2.1.* Start at $`\sigma(x) = 2` and execute `y := x; x := x + y`, with distinct names. Write down the entire intermediate and final states as updates of $`\sigma`.

*2.2.* Prove that `skip; d` and $`d` have the same terminating initial–final state pairs.

*2.3.* Construct the loop derivation in §2.4 starting from $`\sigma(x) = - 1`. How many uses of each loop rule appear?

*Further problem.* Add a simultaneous assignment `(x,y) := (e,f)` for distinct names. Give a big-step rule by evaluating both expressions in the input state. Derive its result when it swaps `x` and `y`. Characterize exactly when the two successive assignments `x := y; y := x` have that same result.

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

*2.1.* The middle state is $`\sigma_1 = \sigma\left\lbrack {y\mapsto 2} \right\rbrack`. Both $`\sigma_1(x)` and $`\sigma_1(y)` equal 2, so the final state is $`\sigma_1\left\lbrack {x\mapsto 4} \right\rbrack`. All names outside the two updated coordinates retain their original values.

*2.2.* Proposition 2.2 yields a witness $`\sigma_1`. Inverting the skip rule forces $`\sigma_1 = \sigma`, leaving $`\sigma \vdash d \Downarrow \sigma'`. In the reverse direction choose $`\sigma_1 = \sigma`, use the skip rule and the given derivation for $`d`, and apply the sequence rule.

*2.3.* The first body execution sets $`x` to 0 and the second sets it to 1. Build the proof from the final state upwards with one application of the loop exit rule and two applications of the loop iteration rule. Each loop iteration also needs its own body derivation.

*Further problem.* Let `a = eval(e,σ)` and `b = eval(f,σ)`. The new rule concludes that the command executes from `σ` to `σ[x ↦ a][y ↦ b]`. There are no command premises. Both expressions have already been evaluated in `σ`, and distinctness of the destination names ensures that either order of the two updates gives the same state. For a swap substitute `e = y` and `f = x`. At the two names the resulting state has values `σ(y)` and `σ(x)` respectively; all other names keep their old values.

For the sequence, the first assignment produces `σ₁ = σ[x ↦ σ(y)]`. The second reads `σ₁(x) = σ(y)` and writes that value to `y`. Its result thus has `σ(y)` in both positions. Equality at `y` with the simultaneous result forces `σ(x) = σ(y)`. Conversely, if this equality holds, comparison at each of the two destinations and every other name proves equality of the full states. Commutation of updates at distinct destinations alone does not justify sequential evaluation of the expressions.

*Further reading · Reordering and regrouping commands.*

State updates give a short calculation for detecting when two writes can be reordered. Fix distinct names `x` and `y`, and fix integers `a` and `b`. Compare the states obtained by writing `a` at `x` and `b` at `y` in opposite orders. To prove equality of the resulting functions, choose any name `z`. If it is `x`, both functions return `a`. If it is `y`, both return `b`. Every other lookup reaches the original state in either function. This establishes commutation for writes of *already determined integers* at distinct coordinates.

The corresponding claim about commands requires more. Run `x := 1; y := x` from a state where `x` holds zero. The writes address distinct names, yet the second right-hand side obtains its integer from the first updated state. In the reverse order `y` receives zero. A proof of commutation for command syntax therefore has to justify that each right-hand side yields the same integer after the other write. The coincidence lemma (Session 1, Lemma 1.1) supplies this fact when neither command writes a free variable of the other expression. This separates two questions that are easy to collapse: which coordinate receives an update, and which coordinates determine the integer to be written.

Proposition 2.2 permits a short proof of reassociation. Invert a derivation of `(c₁; c₂); c₃` twice to expose states `σ₁` and `σ₂` such that `c₁` runs from the initial state to `σ₁`, `c₂` runs from `σ₁` to `σ₂`, and `c₃` runs from `σ₂` to the final state. Assemble the last two derivations first, producing a derivation of `c₂; c₃` from `σ₁`. Combine that with the first derivation to obtain an execution of `c₁; (c₂; c₃)`. The converse reassembles the same three pieces in the opposite grouping. This argument changes the internal tree shape while preserving its intermediate *states* and the order of the constituent computations.

Here is the intermediate-state calculation on two integer coordinates. The first command copies the left coordinate to the right; the second adds the two current values into the left coordinate. Giving the second function the original input would instead leave the original right coordinate in the sum.

Writing $`(a,b)` for the two initial values, the calculation is $`(a,b)\mapsto(a,a)\mapsto(a+a,a)`.

*Further reading · Assignment rules.*

Theorem 1.3 also allows an assignment rule with an explicit expression premise.

$$`\frac{\sigma \vdash e \Downarrow n}{\sigma \vdash x \mathrel{:=} e \Downarrow \sigma[x\mapsto n]}`

For example, if $`\sigma(x)=3`, the premise for `x := x + 4` yields $`n=7`. The conclusion updates the old state only after obtaining that integer. Either form derives the same final states. Given an expression derivation, Theorem 1.3 identifies its result with the value in the assignment rule. Conversely, the theorem supplies a derivation for that computed value. The assignment rule displayed in Definition 2.1 is the one used to count command derivations in Session 3. Recording the expression premise adds a subtree to the full derivation.

Winskel obtains the value of the right-hand side from an expression premise in his assignment rule (p. 20). Nipkow and Klein write $`(c,s)\Rightarrow t` for command execution and use their evaluator `aval a s` directly in the conclusion of the assignment rule (p. 78). [Winskel, §2.4](https://doi.org/10.7551/mitpress/3054.001.0001) · [Concrete Semantics, §7.2.1, Fig. 7.1](https://concrete-semantics.org/concrete-semantics.pdf#page=88)

*Further reading · Counting loop iterations.*

For the incrementing loop above, one can count the necessary rule uses without fixing the values of any unrelated variables. If the initial value of `x` is an integer `j ≤ 1`, the number of body executions is `1 − j`. Prove this by induction on that natural number. At zero the old value is already one. The guard is false, so the loop exit rule gives a derivation with no assignments. At a positive distance the old value is below one. The assignment rule increases it by one, preserving all other lookups, and the new distance is the previous distance minus one. The induction hypothesis supplies a complete loop derivation from that intermediate state. Place the assignment and recursive derivations beneath the loop iteration rule. This constructs a tree and counts its body executions at the same time.

For initial values larger than one, the guard is also false and the final value is the initial one. Thus the postcondition `x = 1` needs an input hypothesis even though the loop terminates for every integer. The result for arbitrary inputs is `x = max(j,1)` with the unchanged coordinates inherited from the original state. A single worked trace would not reveal the distinction between those two specifications.

For the source presentation of the single conditional rule, see the [IMP language card](imp-card/index.html#imp-sources). For exercises using a different arithmetic model, see _The Hitchhiker’s Guide to Logical Verification_, §9.3. [Course materials](https://github.com/lean-forward/logical_verification_2026/tree/460f6be0846eefc3d9441e4e48d75753fcfe1709)

# Sources and Formalization
%%%
tag := "ch02-notes"
number := false
%%%

The guards, commands and six execution rules follow Leroy’s IMP. Nipkow and Klein derive the sequence equivalence for their execution relation. [Source and proof references](imp-card/index.html#imp-sources) · [Concrete Semantics, pp. 81–82](https://concrete-semantics.org/concrete-semantics.pdf)

* *Conditional, true and false cases.* Formulated in this book. Corresponds to CS IfTrue, IfFalse. Checked in Lean ([`ifTrue`](lean/Determinacy.html#ifTrue), [`ifFalse`](lean/Determinacy.html#ifFalse) · [IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 2.2.* Formulated in this book. Corresponds to CS §7.2.3. Checked in Lean ([`sequenceExecution`](lean/Determinacy.html#sequenceExecution) · [IMP card references](imp-card/index.html#imp-sources)).
