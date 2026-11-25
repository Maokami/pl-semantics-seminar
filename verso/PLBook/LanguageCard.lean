import VersoManual

open Verso.Genre Manual

#doc (Manual) "IMP Language Card" =>
%%%
tag := "imp-card"
file := "imp-card"
number := false
%%%

A.1–A.3 accompany [Arithmetic Expressions](chapter-01/index.html). A.4–A.5 accompany [Big-Step Semantics of Commands](chapter-02/index.html) and supply the rules used in [Inversion and Determinacy](chapter-03/index.html). In the judgment $`s\vdash c\Downarrow t` the letters $`s,t` stand for complete stores, $`c` for a command, and the down arrow for a terminating execution. Session 4 uses the syntax of A.1 for [expression folds](chapter-25/index.html). A.6 gives the step and path judgments for [Session 5](chapter-04/index.html) and [Session 6](chapter-05/index.html). [English–Korean glossary](glossary/index.html)

# A.1 Arithmetic expressions · Session 1
%%%
tag := "imp-a1"
number := false
%%%

Let $`x` range over variable names (strings) and $`n` over mathematical integers. An expression is a finite tree built with four constructors:

$$`e ::= n \mid x \mid (e_1+e_2) \mid (e_1-e_2).`

A minus sign at an internal node denotes binary subtraction. A negative integer at a leaf is a literal.

*Structural induction* proves a property $`P(e)` by considering each constructor. At a binary node, the claims $`P(e_1)` and $`P(e_2)` for its two immediate children are the *induction hypotheses*.

# A.2 Stores and update · Session 1
%%%
tag := "imp-a2"
number := false
%%%

A store is a total function $`s:\mathrm{Name}\to\mathbb Z`. Write $`\Sigma` for the set of stores. The update $`s[x\mapsto n]` is the function whose value at $`x` is $`n` and whose value at each other name $`y` is $`s(y)`. Equality of stores means equality at every name.

# A.3 Expression evaluation · Session 1
%%%
tag := "imp-a3"
number := false
%%%

The evaluation function is defined by *structural recursion*. There is one equation per constructor, and recursive calls are made only on immediate children. At each binary node it obtains the two operand values in the same store.

$$`\begin{aligned}
\mathrm{eval}(n,s)&=n & \mathrm{eval}(x,s)&=s(x)\\
\mathrm{eval}(e_1+e_2,s)&=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)\\
\mathrm{eval}(e_1-e_2,s)&=\mathrm{eval}(e_1,s)-\mathrm{eval}(e_2,s).
\end{aligned}`

*Evaluation judgment \[This book\].* Write $`s\vdash e\Downarrow n` when the judgment has a finite derivation by the following rules. An *inference rule* puts its premises above the line and its conclusion below. A rule with no premises is an *axiom*. A *derivation* is a finite tree of rule applications whose root is the judgment proved and whose children derive the premise judgments. If $`D` is a derivation whose root is the judgment $`J`, we write $`D:J` and say that $`D` derives $`J`.

$$`\frac{}{s\vdash n\Downarrow n}\qquad\frac{}{s\vdash x\Downarrow s(x)}`

$$`\frac{s\vdash e_1\Downarrow m\quad s\vdash e_2\Downarrow n}{s\vdash e_1+e_2\Downarrow m+n}
\qquad\frac{s\vdash e_1\Downarrow m\quad s\vdash e_2\Downarrow n}{s\vdash e_1-e_2\Downarrow m-n}`

For example, if $`s(x)=2`, lookup and the literal rule supply the premises for $`s\vdash x-3\Downarrow -1`. *Inversion* recovers the possible last rules of a derivation, together with the premises and equalities forced by their conclusions.

# A.4 Guards and commands · Session 2
%%%
tag := "imp-a4"
number := false
%%%

A Boolean expression has one of six forms:

$$`b ::= \mathsf{true}\mid\mathsf{false}\mid(e_1=e_2)\mid(e_1\le e_2)\mid\neg b\mid(b_1\land b_2).`

Its value $`B(b,s)` is a Boolean. Constants give their own values. Comparisons test the integer values of both operands in $`s`. Negation exchanges true and false. Conjunction returns true exactly when both operands return true. In programs, $`e_1<e_2` abbreviates $`\neg(e_2\le e_1)`, $`e_1\ne e_2` abbreviates $`\neg(e_1=e_2)`, and $`p\lor q` abbreviates $`\neg(\neg p\land\neg q)`.

$$`c ::= \mathsf{skip}\mid x:=e\mid(c_1;c_2)\mid
\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\mid
\mathsf{while}\ b\ \mathsf{do}\ c.`

The Boolean expression controlling a conditional or loop is its *guard*.

# A.5 Big-step execution · Session 2
%%%
tag := "imp-a5"
number := false
%%%

In a *big-step semantics*, a judgment relates an entire computation to its result. The following six rules define $`s\vdash c\Downarrow t`. The judgment holds precisely when it has a finite derivation. Skip leaves the store unchanged. Assignment evaluates the right-hand side in the initial store. Sequencing binds its two premises through the intermediate store $`m`.

$$`\frac{}{s\vdash\mathsf{skip}\Downarrow s}\qquad
\frac{}{s\vdash x:=e\Downarrow s[x\mapsto\mathrm{eval}(e,s)]}`

$$`\frac{s\vdash c\Downarrow m\quad m\vdash d\Downarrow t}{s\vdash(c;d)\Downarrow t}`

For $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`, let $`k` denote $`c` when $`B(b,s)` is true and $`d` otherwise. There is one conditional rule:

$$`\frac{s\vdash k\Downarrow t}{s\vdash I\Downarrow t}`

Fixing the value of $`B(b,s)`, as true or as false, gives a *derived rule*: each of its instances follows by one application of the defining rule. The guard $`b` itself is not replaced.

Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c`. The guard tests above the lines below are *side conditions*. Evaluate the Boolean function to check each equality. Only the execution judgments above a line, the rule's execution premises, require subderivations. A false guard ends the loop. A true guard requires both an execution of the body and a further execution of the loop starting in the body’s final store.

$$`\frac{B(b,s)=\mathsf{false}}{s\vdash W\Downarrow s}\qquad
\frac{B(b,s)=\mathsf{true}\quad s\vdash c\Downarrow m\quad m\vdash W\Downarrow t}{s\vdash W\Downarrow t}`

We refer to the six rules as the skip, assignment, sequence, conditional, loop exit and loop iteration rules.

The *height of an execution derivation* is zero when its last rule has no execution premises. Otherwise it is one plus the greatest height of an immediate execution subderivation.

# A.6 Transitions and paths · Sessions 5–6
%%%
tag := "imp-a6"
number := false
%%%

A *configuration* $`\langle c,s\rangle` consists of a residual command $`c` (the work still to do) and the current store $`s`. Write $`p\to q` for one transition. Assignment evaluates its right-hand side in the current store and steps to skip with the updated store.

$$`\frac{}{\langle x:=e,s\rangle\to\langle\mathsf{skip},s[x\mapsto\mathrm{eval}(e,s)]\rangle}`

A sequence with skip on the left steps to its right command. A step of its left command lifts through the sequence, carrying the resulting store with it.

$$`\frac{}{\langle \mathsf{skip};d,s\rangle\to\langle d,s\rangle}
\qquad\frac{\langle c,s\rangle\to\langle c',t\rangle}{\langle c;d,s\rangle\to\langle c';d,t\rangle}`

For $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`, let $`k` be the branch selected by $`B(b,s)` as in Session 2, Definition 2.1. For $`W=\mathsf{while}\ b\ \mathsf{do}\ c`, a false guard exits and a true guard exposes the body.

$$`\frac{}{\langle I,s\rangle\to\langle k,s\rangle}\qquad
\frac{B(b,s)=\mathsf{false}}{\langle W,s\rangle\to\langle\mathsf{skip},s\rangle}\qquad
\frac{B(b,s)=\mathsf{true}}{\langle W,s\rangle\to\langle c;W,s\rangle}`

Skip itself has no outgoing step.

A finite path $`p\to^*q` either takes zero steps with $`p=q`, or has a first step $`p\to r` and a finite tail $`r\to^*q`. Write $`p\to^n q` when there are configurations $`p_0,\ldots,p_n` with $`p_0=p`, $`p_n=q` and $`p_i\to p_{i+1}` for every $`0\le i<n`. The natural number $`n` counts edges.

An *infinite path* from $`p` is witnessed by a function $`f` from natural numbers to configurations with $`f(0)=p` and $`f(i)\to f(i+1)` for every $`i`. The coinductive presentation uses a predicate on configurations: the greatest predicate $`X`, under inclusion, satisfying $`X(p)\iff\exists q,\ p\to q\land X(q)`.

# Source and proof references
%%%
tag := "imp-sources"
number := false
%%%

These references document the formalization. They are optional for seminar preparation.

*Source.* The shared definitions follow the Lean port of Xavier Leroy’s _Compiler Verification_ course at revision `a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01`. A.3 adds the book’s evaluation judgment on the same syntax. [IMP definitions](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean) · [Paths](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean)

* $`\mathrm{eval}(e,s)`, $`B(b,s)` and $`s[x\mapsto n]` correspond to `aeval s e`, `beval s b` and `update x n s`.
* $`s\vdash c\Downarrow t` corresponds to `cexec s c t`. The conditional rule is `cexec_ifthenelse`.
* One step is `red`. The finite closure is `star`. The two presentations of infinite execution are `infseq_with_function` and `infseq`.
* Definition 1.5 is `PLBook.IMP.Evaluates`. In `PLBook.IMP.Arithmetic`, membership in the free-variable set is `occurs`. Lemma 1.1 is `coincidence`, Corollary 1.2 is `updateIrrelevant`, Theorem 1.3 is `correspondence`, and Corollary 1.4 is `uniqueValue`, all in the namespace `PLBook.IMP`. Theorem 1.5 has a paper proof in the Session 11 reading.
* Proposition 2.2 is `PLBook.IMP.sequenceExecution` on the shared execution relation.
* The proof module `PLBook.IMP.Determinacy` checks Lemma 3.1 with `PLBook.IMP.assignmentResult` and Theorem 3.2 with `PLBook.IMP.deterministic` on the shared execution relation. The two derived conditional rules are `PLBook.IMP.ifTrue` and `PLBook.IMP.ifFalse`.
* Theorem 4.1 is `PLBook.IMP.uniqueFold` in `PLBook.IMP.Fold`. It includes existence and uniqueness for all four constructors of `aexp`. The operations take values in an arbitrary type.
* In `PLBook.IMP.Paths`, Lemma 5.3 is `progress` on the shared transition relation. The source statement is `red_progress`. [Progress for IMP commands](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L315-L335)
* Lemma 5.4 is `finiteIffLength`. The finite sequence in $`p\to^n q` is represented by `PathOfLength`: a single configuration at length zero, or a first edge followed by a sequence of length $`n` at length $`n+1`. Example 5.5 is `skipLoopInfinite` on `infseq_with_function`. Its checked witness alternates between the loop head and its unfolded body.
* Lemma 6.1 is `liftLength` and preserves the exact length. Leroy’s `red_seq_steps` lifts a finite path without specifying its length. [Sequence context in IMP](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L340-L356)
* Theorem 6.2 is `terminatingEquivalence`. The source gives the two implications separately in `cexec_to_reds` and `reds_to_cexec`. Lemma 6.3 is `executionBeforeStep`, with the same premise and conclusion as `red_append_cexec`. These book proofs use the shared IMP relations. [Forward implication](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L361-L385) · [Backward step and reverse implication](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L388-L405)
