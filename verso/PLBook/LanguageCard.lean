import VersoManual

open Verso.Genre Manual

#doc (Manual) "IMP Language Card" =>
%%%
tag := "imp-card"
file := "imp-card"
number := false
%%%

For [Inversion and Determinacy](chapter-03/index.html), read A.1–A.5. In the judgment $`s\vdash c\Downarrow t` the letters $`s,t` stand for complete stores, $`c` for a command, and the down arrow for a terminating execution. A.6 introduces a second judgment for individual steps. [English–Korean glossary](glossary/index.html)

# A.1 Arithmetic expressions · Session 1
%%%
tag := "imp-a1"
number := false
%%%

Let $`x` range over variable names (strings) and $`n` over mathematical integers. An expression is a finite tree built with four constructors:

$$`e ::= n \mid x \mid (e_1+e_2) \mid (e_1-e_2).`

A minus sign at an internal node denotes binary subtraction. A negative integer at a leaf is a literal.

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

The evaluation function is defined by structural recursion. At each binary node it first obtains the two operand values in the same store.

$$`\begin{aligned}
\mathrm{eval}(n,s)&=n & \mathrm{eval}(x,s)&=s(x)\\
\mathrm{eval}(e_1+e_2,s)&=\mathrm{eval}(e_1,s)+\mathrm{eval}(e_2,s)\\
\mathrm{eval}(e_1-e_2,s)&=\mathrm{eval}(e_1,s)-\mathrm{eval}(e_2,s).
\end{aligned}`

*Evaluation judgment \[This book\].* Write $`s\vdash e\Downarrow n` when the judgment has a finite derivation by the following rules. An inference rule puts its premises above the line and its conclusion below. Each premise receives its own derivation. A rule with no premises can be used at a leaf.

$$`\frac{}{s\vdash n\Downarrow n}\qquad\frac{}{s\vdash x\Downarrow s(x)}`

$$`\frac{s\vdash e_1\Downarrow m\quad s\vdash e_2\Downarrow n}{s\vdash e_1+e_2\Downarrow m+n}
\qquad\frac{s\vdash e_1\Downarrow m\quad s\vdash e_2\Downarrow n}{s\vdash e_1-e_2\Downarrow m-n}`

For example, if $`s(x)=2`, lookup and the literal rule supply the premises for $`s\vdash x-3\Downarrow -1`. Going from a conclusion to its possible last rules and their premises is *inversion*. Structural induction on an expression instead follows its constructors, with one *induction hypothesis* for each immediate subexpression: the claim is assumed for that subexpression when proving it for the whole expression.

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

The following six rules define $`s\vdash c\Downarrow t`. The judgment holds precisely when it has a finite derivation. Skip leaves the store unchanged. Assignment evaluates the right-hand side in the initial store. Sequencing binds its two premises through the intermediate store $`m`.

$$`\frac{}{s\vdash\mathsf{skip}\Downarrow s}\qquad
\frac{}{s\vdash x:=e\Downarrow s[x\mapsto\mathrm{eval}(e,s)]}`

$$`\frac{s\vdash c\Downarrow m\quad m\vdash d\Downarrow t}{s\vdash(c;d)\Downarrow t}`

For $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`, let $`k` denote $`c` when $`B(b,s)` is true and $`d` otherwise. There is one conditional rule:

$$`\frac{s\vdash k\Downarrow t}{s\vdash I\Downarrow t}`

Substituting either Boolean value for the guard gives a *derived rule*: every instance follows by applying the defining rule with that value.

Write $`W=\mathsf{while}\ b\ \mathsf{do}\ c`. The guard tests above the lines below are *side conditions*. Evaluate the Boolean function to check each equality. Only a premise of the form $`s\vdash c\Downarrow t` requires an execution subderivation. A false guard ends the loop. A true guard requires both an execution of the body and a further execution of the loop starting in the body’s final store.

$$`\frac{B(b,s)=\mathsf{false}}{s\vdash W\Downarrow s}\qquad
\frac{B(b,s)=\mathsf{true}\quad s\vdash c\Downarrow m\quad m\vdash W\Downarrow t}{s\vdash W\Downarrow t}`

# A.6 Transitions and paths · Sessions 5–6
%%%
tag := "imp-a6"
number := false
%%%

A configuration $`\langle c,s\rangle` consists of the residual command and the current store. Write $`p\to q` for one transition. Assignment steps to skip with the updated store. A sequence with skip on the left steps to its right command. A step of its left command lifts through the sequence, carrying the resulting store with it. A conditional steps to its selected branch. A loop with a false guard steps to skip; with a true guard it steps to the sequence of its body and the same loop. Selecting a branch, unfolding or exiting a loop, and dropping an initial skip all preserve the current store. Skip itself has no outgoing step.

A finite path $`p\to^*q` either takes zero steps with $`p=q`, or has a first step $`p\to r` and a finite tail $`r\to^*q`. In Session 5, $`p\to^n q` means that there are configurations $`p_0,\ldots,p_n` with $`p_0=p`, $`p_n=q` and $`p_i\to p_{i+1}` for every $`0\le i<n`. An infinite path can be exhibited by a function $`f` on the natural numbers such that $`f(0)=p` and $`f(i)\to f(i+1)` for every $`i`. The port also defines infinite execution coinductively, as the greatest predicate $`X` satisfying $`X(p)\iff\exists q,\ p\to q\land X(q)`.

# Source and proof references
%%%
tag := "imp-sources"
number := false
%%%

These references document the formalization. They are optional for seminar preparation.

*Source.* The shared definitions follow the Lean port of Xavier Leroy’s _Compiler Verification_ course at revision `a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01`. A.3 adds the book’s expression judgment on the same syntax. [IMP definitions](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean) · [Paths](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean)

* $`\mathrm{eval}(e,s)`, $`B(b,s)` and $`s[x\mapsto n]` correspond to `aeval s e`, `beval s b` and `update x n s`.
* $`s\vdash c\Downarrow t` corresponds to `cexec s c t`. The conditional rule is `cexec_ifthenelse`.
* One step is `red`. The finite closure is `star`. The two presentations of infinite execution are `infseq_with_function` and `infseq`.
* The proof module `PLBook.IMP.Determinacy` checks Lemma 3.1 with `PLBook.IMP.assignmentResult` and Theorem 3.2 with `PLBook.IMP.deterministic` on the shared execution relation. The two derived conditional rules are `PLBook.IMP.ifTrue` and `PLBook.IMP.ifFalse`.
