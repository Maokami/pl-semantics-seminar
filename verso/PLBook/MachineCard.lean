import VersoManual

open Verso.Genre Manual

#doc (Manual) "Stack Machine Card" =>
%%%
tag := "machine-card"
file := "machine-card"
number := false
%%%

B.1–B.6 accompany [Compiling Expressions to a Stack Machine](chapter-14/index.html). B.7 accompanies [Session 15](chapter-15/index.html). B.8–B.9 accompany [Session 16](chapter-16/index.html). The instruction set, the transition rules and the three compilation functions follow Leroy’s course without change: the same instructions, the same order of arguments and the same branch offsets. Expressions, guards, commands, stores and evaluation are those of the [IMP language card](imp-card/index.html). Letters: $`C` is the code of a whole program, $`K` a block of code, $`i` an instruction, $`\mathit{pc}` a program counter, $`S` a stack, $`s,t` stores, $`n` an integer and $`d` a branch distance. [English–Korean glossary](glossary/index.html)

# B.1 Instructions · Session 14
%%%
tag := "machine-b1"
number := false
%%%

Let $`n` and $`d` range over integers and $`x` over variable names. The machine has nine instructions:

$$`i ::= \mathsf{push}(n)\mid\mathsf{load}(x)\mid\mathsf{setvar}(x)\mid\mathsf{plus}\mid\mathsf{opp}\mid\mathsf{branch}(d)\mid\mathsf{beq}(d_1,d_0)\mid\mathsf{ble}(d_1,d_0)\mid\mathsf{halt}.`

Informally, $`\mathsf{push}(n)` pushes the integer $`n` on the stack, and $`\mathsf{load}(x)` pushes the current value of the variable $`x`. $`\mathsf{setvar}(x)` pops an integer and assigns it to $`x`. $`\mathsf{plus}` pops two integers and pushes their sum. $`\mathsf{opp}` pops one integer and pushes its opposite. $`\mathsf{branch}(d)` skips $`d` instructions, forward if $`d>0` and backward if $`d<0`. The *conditional branch instruction* $`\mathsf{beq}(d_1,d_0)` pops two integers and skips $`d_1` instructions if they are equal and $`d_0` instructions otherwise. $`\mathsf{ble}(d_1,d_0)` does the same with the test “the lower integer is less than or equal to the top integer”. $`\mathsf{halt}` stops the machine. B.4 makes each sentence exact.

There is no subtraction instruction. A *branch distance* is counted from the instruction that follows the branch. Thus $`\mathsf{branch}(0)` continues with the next instruction.

# B.2 Code and positions · Session 14
%%%
tag := "machine-b2"
number := false
%%%

*Code* is a finite list of instructions $`C=[i_0,i_1,\ldots,i_{\ell-1}]`. Its length $`|C|=\ell` is used as an integer. Concatenation is written $`C_1\mathbin{+\!\!+}C_2`. It is associative, the empty list $`[\,]` is its unit, and $`|C_1\mathbin{+\!\!+}C_2|=|C_1|+|C_2|`. Write $`i::K` for the list whose first instruction is $`i`, followed by the list $`K`.

Positions are integers and start at $`0`. The *instruction at position* $`\mathit{pc}` is $`C(\mathit{pc})=i_{\mathit{pc}}` when $`0\le\mathit{pc}<|C|`. For every other integer $`\mathit{pc}`, including negative ones, $`C(\mathit{pc})` is undefined.

A compiled block is placed inside a larger program. *Code at a position* is the relation

$$`\mathrm{at}(C,\mathit{pc},K)\quad\Longleftrightarrow\quad C=C_1\mathbin{+\!\!+}K\mathbin{+\!\!+}C_2\ \text{ for some } C_1,C_2 \text{ with } |C_1|=\mathit{pc}.`

For example, let $`C=[\mathsf{push}(1),\mathsf{load}(x),\mathsf{plus},\mathsf{setvar}(y)]`. Then $`C(2)=\mathsf{plus}`, and $`\mathrm{at}(C,1,[\mathsf{load}(x),\mathsf{plus}])` holds with $`C_1=[\mathsf{push}(1)]` and $`C_2=[\mathsf{setvar}(y)]`.

Three facts follow by regrouping the concatenation. The prefix $`C_1` grows by the part of the block that is stepped over.

1. If $`\mathrm{at}(C,\mathit{pc},i::K)`, then $`C(\mathit{pc})=i` and $`\mathrm{at}(C,\mathit{pc}+1,K)`.
2. If $`\mathrm{at}(C,\mathit{pc},K_1\mathbin{+\!\!+}K_2)`, then $`\mathrm{at}(C,\mathit{pc},K_1)` and $`\mathrm{at}(C,\mathit{pc}+|K_1|,K_2)`.
3. If $`\mathrm{at}(C,\mathit{pc},K_1\mathbin{+\!\!+}K_2\mathbin{+\!\!+}K_3)`, then $`\mathrm{at}(C,\mathit{pc}+|K_1|,K_2)`.

# B.3 Stacks and machine configurations · Session 14
%%%
tag := "machine-b3"
number := false
%%%

A *stack* is a finite list of integers with its top on the left. Write $`[\,]` for the empty stack and $`n::S` for the stack with $`n` on top of the stack $`S`. Thus $`[3,8,11]=3::8::11::[\,]` has $`3` on top. Write $`\mathrm{Stack}` for the set of stacks.

A *machine configuration* $`\langle\mathit{pc},S,s\rangle` has three components. The *program counter* $`\mathit{pc}` is the position of the next instruction. The stack $`S` holds intermediate results. The store $`s` (A.2) gives the values of variables. The code $`C` stays fixed during a run and is not part of the configuration.

# B.4 Transitions · Session 14
%%%
tag := "machine-b4"
number := false
%%%

Write $`C\vdash p\to q` when the machine running the code $`C` moves from the configuration $`p` to the configuration $`q` in one *transition*. The prefix $`C\vdash` distinguishes these transitions from the transitions of IMP commands in A.6. There is one rule for each instruction except $`\mathsf{halt}`. Each rule reads the instruction at the current program counter.

$$`\frac{C(\mathit{pc})=\mathsf{push}(n)}{C\vdash\langle\mathit{pc},S,s\rangle\to\langle\mathit{pc}+1,n::S,s\rangle}\qquad
\frac{C(\mathit{pc})=\mathsf{load}(x)}{C\vdash\langle\mathit{pc},S,s\rangle\to\langle\mathit{pc}+1,s(x)::S,s\rangle}`

$$`\frac{C(\mathit{pc})=\mathsf{setvar}(x)}{C\vdash\langle\mathit{pc},n::S,s\rangle\to\langle\mathit{pc}+1,S,s[x\mapsto n]\rangle}`

In the rule for $`\mathsf{plus}` the integer $`n_2` is on top and $`n_1` is below it. The sum is written $`n_1+n_2`.

$$`\frac{C(\mathit{pc})=\mathsf{plus}}{C\vdash\langle\mathit{pc},n_2::n_1::S,s\rangle\to\langle\mathit{pc}+1,(n_1+n_2)::S,s\rangle}\qquad
\frac{C(\mathit{pc})=\mathsf{opp}}{C\vdash\langle\mathit{pc},n::S,s\rangle\to\langle\mathit{pc}+1,(-n)::S,s\rangle}`

$$`\frac{C(\mathit{pc})=\mathsf{branch}(d)}{C\vdash\langle\mathit{pc},S,s\rangle\to\langle\mathit{pc}+1+d,S,s\rangle}`

The two conditional branch instructions pop $`n_2` from the top and $`n_1` from below it. For $`\mathsf{beq}(d_1,d_0)` let $`\delta` be $`d_1` when $`n_1=n_2` and $`d_0` otherwise. For $`\mathsf{ble}(d_1,d_0)` let $`\delta` be $`d_1` when $`n_1\le n_2` and $`d_0` otherwise.

$$`\frac{C(\mathit{pc})=\mathsf{beq}(d_1,d_0)}{C\vdash\langle\mathit{pc},n_2::n_1::S,s\rangle\to\langle\mathit{pc}+1+\delta,S,s\rangle}\qquad
\frac{C(\mathit{pc})=\mathsf{ble}(d_1,d_0)}{C\vdash\langle\mathit{pc},n_2::n_1::S,s\rangle\to\langle\mathit{pc}+1+\delta,S,s\rangle}`

Only $`\mathsf{setvar}` changes the store. Only the three branch instructions move the program counter by something other than one. A configuration has no transition when $`C(\mathit{pc})` is undefined, when $`C(\mathit{pc})=\mathsf{halt}`, or when the stack holds fewer integers than the instruction pops.

For example, take $`C=[\mathsf{push}(1),\mathsf{load}(x),\mathsf{plus},\mathsf{setvar}(y)]` and a store with $`s(x)=4`. From $`\langle0,[\,],s\rangle` the machine moves to $`\langle1,[1],s\rangle`, $`\langle2,[4,1],s\rangle`, $`\langle3,[5],s\rangle` and $`\langle4,[\,],s[y\mapsto5]\rangle`. Since $`C(4)` is undefined, the last configuration has no transition.

# B.5 Finite paths · Session 14
%%%
tag := "machine-b5"
number := false
%%%

A *finite path* of the machine, written $`C\vdash p\to^*q`, is defined as in A.6. Either it takes zero transitions and $`p=q`, or it has a first transition $`C\vdash p\to r` followed by a finite path $`C\vdash r\to^*q`. Every transition of the path uses the same code $`C`.

Two facts are used in every compiler proof. A single transition is a finite path. If $`C\vdash p\to^*q` and $`C\vdash q\to^*r`, then $`C\vdash p\to^*r`. The second fact, *joining* two paths, is proved by induction on the first path.

# B.6 Compiling arithmetic expressions · Session 14
%%%
tag := "machine-b6"
number := false
%%%

The function $`\mathrm{cexp}` sends each arithmetic expression (A.1) to code. It is defined by structural recursion:

$$`\begin{aligned}
\mathrm{cexp}(n)&=[\mathsf{push}(n)] \qquad \mathrm{cexp}(x)=[\mathsf{load}(x)]\\
\mathrm{cexp}(e_1+e_2)&=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{plus}]\\
\mathrm{cexp}(e_1-e_2)&=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{opp},\mathsf{plus}].
\end{aligned}`

Both operands are compiled first, the left one before the right one, and the operator comes last. A difference adds the opposite of the right operand to the left operand. For example,

$$`\mathrm{cexp}(x-(2+1))=[\mathsf{load}(x),\mathsf{push}(2),\mathsf{push}(1),\mathsf{plus},\mathsf{opp},\mathsf{plus}].`

The code $`\mathrm{cexp}(e)` contains only the instructions $`\mathsf{push}`, $`\mathsf{load}`, $`\mathsf{plus}` and $`\mathsf{opp}`. Session 14 proves that it advances the program counter by $`|\mathrm{cexp}(e)|`, pushes $`\mathrm{eval}(e,s)` on the stack and leaves the store unchanged.

# B.7 Compiling Boolean expressions · Session 15
%%%
tag := "machine-b7"
number := false
%%%

The code $`\mathrm{cbexp}(b,d_1,d_0)` for a guard $`b` (A.4) never puts a truth value on the stack. It is meant to leave the stack and the store unchanged, and then to continue $`d_1` instructions after its own end when $`B(b,s)=\mathsf{true}` and $`d_0` instructions after its own end when $`B(b,s)=\mathsf{false}`. Session 15 proves this. The two branch distances $`d_1,d_0` are integers.

$$`\begin{aligned}
\mathrm{cbexp}(\mathsf{true},d_1,d_0)&=[\,]\ \text{ if } d_1=0,\quad\text{otherwise } [\mathsf{branch}(d_1)]\\
\mathrm{cbexp}(\mathsf{false},d_1,d_0)&=[\,]\ \text{ if } d_0=0,\quad\text{otherwise } [\mathsf{branch}(d_0)]\\
\mathrm{cbexp}(e_1=e_2,d_1,d_0)&=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{beq}(d_1,d_0)]\\
\mathrm{cbexp}(e_1\le e_2,d_1,d_0)&=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{ble}(d_1,d_0)]\\
\mathrm{cbexp}(\neg b,d_1,d_0)&=\mathrm{cbexp}(b,d_0,d_1)\\
\mathrm{cbexp}(b_1\land b_2,d_1,d_0)&=\mathrm{cbexp}(b_1,0,|K_2|+d_0)\mathbin{+\!\!+}K_2\quad\text{where } K_2=\mathrm{cbexp}(b_2,d_1,d_0).
\end{aligned}`

Negation exchanges the two distances. In a conjunction, the code for $`b_1` continues into $`K_2` when $`b_1` is true. When $`b_1` is false it skips $`K_2` and then $`d_0` further instructions, which is where the false outcome of $`b_1\land b_2` must continue.

For example, $`\mathrm{cbexp}(x\le1,0,3)=[\mathsf{load}(x),\mathsf{push}(1),\mathsf{ble}(0,3)]`. With $`s(x)=4` the comparison pops $`n_2=1` and $`n_1=4`. Since $`4\le1` is false, the machine continues three instructions after the end of the block.

# B.8 Compiling commands · Session 16
%%%
tag := "machine-b8"
number := false
%%%

The code $`\mathrm{ccom}(c)` for a command $`c` (A.4) is meant to change the store as $`c` does, leave the stack unchanged, and finish at its own end. Session 16 proves this for terminating executions.

$$`\begin{aligned}
\mathrm{ccom}(\mathsf{skip})&=[\,]\\
\mathrm{ccom}(x:=e)&=\mathrm{cexp}(e)\mathbin{+\!\!+}[\mathsf{setvar}(x)]\\
\mathrm{ccom}(c_1;c_2)&=\mathrm{ccom}(c_1)\mathbin{+\!\!+}\mathrm{ccom}(c_2)\\
\mathrm{ccom}(\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2)&=\mathrm{cbexp}(b,0,|K_1|+1)\mathbin{+\!\!+}K_1\mathbin{+\!\!+}[\mathsf{branch}(|K_2|)]\mathbin{+\!\!+}K_2\\
\mathrm{ccom}(\mathsf{while}\ b\ \mathsf{do}\ c)&=K_b\mathbin{+\!\!+}K_c\mathbin{+\!\!+}[\mathsf{branch}(-(|K_b|+|K_c|+1))]
\end{aligned}`

In the conditional, $`K_1=\mathrm{ccom}(c_1)` and $`K_2=\mathrm{ccom}(c_2)`. In the loop, $`K_c=\mathrm{ccom}(c)` and $`K_b=\mathrm{cbexp}(b,0,|K_c|+1)`.

*Layout of the conditional.* Suppose its code is at $`\mathit{pc}` and write $`K_t=\mathrm{cbexp}(b,0,|K_1|+1)` for the test. The test starts at $`\mathit{pc}`, the code $`K_1` at $`\mathit{pc}+|K_t|`, the branch at $`\mathit{pc}+|K_t|+|K_1|`, the code $`K_2` at $`\mathit{pc}+|K_t|+|K_1|+1`, and the whole block ends at $`\mathit{pc}+|K_t|+|K_1|+1+|K_2|`. A true guard continues at the end of the test, which is the start of $`K_1`. A false guard skips $`|K_1|+1` instructions after the end of the test and reaches the start of $`K_2`. After $`K_1`, the branch skips $`K_2` and reaches the end of the block.

*Layout of the loop.* Suppose its code is at $`\mathit{pc}`. The test $`K_b` starts at $`\mathit{pc}`, the body $`K_c` at $`\mathit{pc}+|K_b|`, and the backward branch at $`\mathit{pc}+|K_b|+|K_c|`. The block ends at $`\mathit{pc}+|K_b|+|K_c|+1`. A true guard continues at the start of the body. A false guard continues at $`(\mathit{pc}+|K_b|)+|K_c|+1`, the end of the block. The backward branch continues at $`(\mathit{pc}+|K_b|+|K_c|)+1-(|K_b|+|K_c|+1)=\mathit{pc}`, the start of the test.

For example, $`\mathrm{ccom}(\mathsf{while}\ x\le1\ \mathsf{do}\ x:=x+1)` is

$$`[\mathsf{load}(x),\mathsf{push}(1),\mathsf{ble}(0,5),\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus},\mathsf{setvar}(x),\mathsf{branch}(-8)].`

Here $`|K_b|=3` and $`|K_c|=4`. Placed at position $`0`, the false outcome of the test at position $`2` continues at $`2+1+5=8`, the end. The branch at position $`7` continues at $`7+1-8=0`.

# B.9 Whole programs · Session 16
%%%
tag := "machine-b9"
number := false
%%%

A whole program $`c` is compiled to $`C=\mathrm{ccom}(c)\mathbin{+\!\!+}[\mathsf{halt}]`. A run starts in the configuration $`\langle0,[\,],s\rangle`. There are three possible behaviours.

* The machine *terminates* from $`s` with final store $`t` when there is a position $`\mathit{pc}` with $`C\vdash\langle0,[\,],s\rangle\to^*\langle\mathit{pc},[\,],t\rangle` and $`C(\mathit{pc})=\mathsf{halt}`.
* The machine *diverges* from $`s` when there is an infinite path of machine transitions from $`\langle0,[\,],s\rangle`, in the sense of A.6.
* The machine *goes wrong* from $`s` when $`C\vdash\langle0,[\,],s\rangle\to^*\langle\mathit{pc},S,t\rangle` for a configuration with no transition such that $`C(\mathit{pc})` is not $`\mathsf{halt}` (it may be undefined) or $`S\neq[\,]`.

For example, $`\mathrm{ccom}(x:=x+1)\mathbin{+\!\!+}[\mathsf{halt}]=[\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus},\mathsf{setvar}(x),\mathsf{halt}]`. From a store with $`s(x)=2` the machine reaches $`\langle4,[\,],s[x\mapsto3]\rangle`, where $`C(4)=\mathsf{halt}`. It terminates with final store $`s[x\mapsto3]`.

# Source and Lean names
%%%
tag := "machine-sources"
number := false
%%%

These references document the formalization. They are optional for seminar preparation. This is the only place in the book where the Lean names of the machine appear.

*Source.* All definitions on this card follow the compiler chapter of the Lean port of Xavier Leroy’s _Compiler Verification_ course at revision `a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01`. Finite paths come from its sequences module. [Machine and compiler](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean) · [Paths](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean)

* The instructions $`\mathsf{push}(n)`, $`\mathsf{load}(x)`, $`\mathsf{setvar}(x)`, $`\mathsf{plus}`, $`\mathsf{opp}`, $`\mathsf{branch}(d)`, $`\mathsf{beq}(d_1,d_0)`, $`\mathsf{ble}(d_1,d_0)` and $`\mathsf{halt}` are the constructors `Iconst n`, `Ivar x`, `Isetvar x`, `Iadd`, `Iopp`, `Ibranch d`, `Ibeq d1 d0`, `Ible d1 d0` and `Ihalt` of the type `instr`.
* Code is `List instr`. The length $`|C|` is `codelen C`. The equation $`C(\mathit{pc})=i` is `instr_at C pc = .some i`, and $`C(\mathit{pc})` undefined is `instr_at C pc = .none`.
* $`\mathrm{at}(C,\mathit{pc},K)` is `code_at C pc K`. The three facts of B.2 are `code_at_head` with `code_at_tail`, then `code_at_app_left` with `code_at_app_right`, then `code_at_app_right2`.
* A stack is `stack`, a list of integers whose head is the top. The configuration $`\langle\mathit{pc},S,s\rangle` is the triple `(pc, S, s)` of type `config`. The store and $`s[x\mapsto n]` are `store` and `update x n s`.
* $`C\vdash p\to q` is `transition C p q`. Its rules are `trans_const`, `trans_var`, `trans_setvar`, `trans_add`, `trans_opp`, `trans_branch`, `trans_beq` and `trans_ble`.
* $`C\vdash p\to^*q` is `transitions C p q`, defined as `star (transition C) p q`. A single transition as a path is `star_one`. Joining two paths is `star_trans`. An infinite path is `infseq`.
* $`\mathrm{cexp}(e)`, $`\mathrm{cbexp}(b,d_1,d_0)` and $`\mathrm{ccom}(c)` are `compile_aexp e`, `compile_bexp b d1 d0` and `compile_com c`. The compiled whole program is `compile_program c`.
* Termination, divergence and going wrong in B.9 are `machine_terminates`, `machine_diverges` and `machine_goes_wrong`. A configuration with no transition is `irred (transition C)`.
* Session 14, Corollary 14.4 is `compile_aexp_correct`. Session 15, Theorem 15.2 is `compile_bexp_correct`. Session 16, Theorem 16.2 is `compile_com_correct_terminating`. Each has the same quantifiers, premise and conclusion as the book's statement.
* Session 14, Definition 14.1 (list execution), Lemma 14.1, Theorem 14.2 and Lemma 14.3 have no counterpart in the source. Their proofs are given on paper in Session 14. Session 15, Definition 15.1 and Session 16, Definition 16.1 restate as definitions the informal specifications in the comments above `compile_bexp_correct` and `compile_com`. Session 16, Corollary 16.3 has no counterpart for the big-step execution of A.5; the source proves the same conclusion, `machine_terminates (compile_program c) s s'`, from its small-step semantics with continuations as `compile_program_correct_terminating_2`.
