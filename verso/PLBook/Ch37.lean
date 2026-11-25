import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Compiling Expressions to a Stack Machine" =>
%%%
tag := "ch37"
file := "chapter-37"
%%%

[Chapter PDF](print/chapter-37.pdf) · [Session 37](seminar/index.html#week-37)

After compiling the left operand of an addition, the machine stack already contains a partial result. A compiler theorem restricted to an empty initial stack cannot justify running the right operand at this point. The arbitrary stack in the statement below is essential even when every complete program starts with an empty one.

*Sources.* Nipkow and Klein, _Concrete Semantics_, §3.3, on compilation of expressions to stack code. Then read `compile_aexp_correct` in the Lean 4 port of Xavier Leroy’s _Compiler Verification_ course. The latter explicitly tracks both the ambient instruction list and the program counter. We follow its stack order and subtraction sequence. [Concrete Semantics.](https://concrete-semantics.org/concrete-semantics.pdf) [Lean statement and proof.](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Compil.lean#L347-L404)

# Source and target
%%%
tag := "ch37-s1"
%%%

An expression is an integer literal, a variable, a sum or a difference. The direct evaluator reads an integer store $`s` and uses mathematical integer arithmetic. The target has an ambient list $`C` of instructions and configurations $`\langle p,S,s\rangle`, with integer program counter $`p` and stack $`S` written with its top on the left. A constant instruction pushes its literal, a variable instruction pushes a lookup, opposite negates the top, and add replaces the top two values $`v,u` by $`u + v`. Each instruction advances the counter by one and preserves the store. A missing operand gives no such transition.

Let $`K(e)` be the compiled instruction list. For a literal or variable emit the matching push. For a sum concatenate $`K(a)`, $`K(b)`, and a single add. For a difference use the same operand order followed by opposite and add. Write $`|K|` for list length. The predicate `code_at C p K` means that $`C` splits into a prefix of length $`p`, the block $`K`, and a suffix. This premise permits a subexpression to reside inside a larger program.

A block occurrence includes more information than its first instruction. Suppose the compiler emits three instructions for a sum, and the ambient program contains the same push instruction at several addresses. A premise saying just “the instruction at p is the first push” cannot justify the second push or the final add. To use a complete occurrence, decompose the ambient program into a prefix, the emitted list, and a suffix. The prefix length determines p. Moving across the first operand's list extends that prefix by exactly the length of the list and leaves the remaining suffix of the block intact. No assumption about what comes after the block is needed.

Distinguish two possible meanings of an integer at this boundary. The target counter indexes instructions; an integer on the operand stack is a value being computed. Increasing the counter does not change a stack value, and pushing a negative literal does not move execution backwards. The store has a third role, supplying the values of source variables through load instructions. Stating the three components separately makes an expression compiler's contract visible: it advances the counter, extends the stack by one, and preserves the store.

# Correctness
%%%
tag := "ch37-s2"
%%%

*Theorem 37.1.* For every store, initial stack, ambient code and counter with $`K(e)` at $`p`, the generated block satisfies the following machine judgment, where the arrow denotes a finite sequence of steps in the fixed ambient program.

$$`\langle p,S,s\rangle \to^{*} \langle p + \lvert K(e)\rvert,\operatorname{eval}(e,s)::S,s\rangle.`

Here $`::` prepends to a list. The theorem stops at the block boundary even when another instruction is present there.

Induct on $`e`, keeping $`p` and $`S` arbitrary. A leaf takes one push step and establishes the result directly. For a sum write $`m = \lvert K(a)\rvert`, $`n = \lvert K(b)\rvert`, $`u = \operatorname{eval}\left( {a,s} \right)` and $`v = \operatorname{eval}\left( {b,s} \right)`. The block decomposition puts the first operand at $`p`, the second at $`p + m`, and add at $`p + m + n`. The first induction hypothesis reaches counter $`p + m` with stack $`u::S`. Apply the second hypothesis with this *new* counter and stack to reach $`p + m + n` with $`v::u::S`. Add now reaches $`p + m + n + 1` with $`\left( {u + v} \right)::S`. Concatenating the three paths proves the sum case.

For a difference use the same two paths. Opposite changes $`v::u::S` to $`\left( {- v} \right)::u::S`. Add returns $`\left( {u - v} \right)::S` at counter $`p + m + n + 2`. In both cases the unchanged suffix of the stack remains available to surrounding code.

Compile the expression `(1 + 2) + (4 − 3)` starting at counter 10 with incoming stack `[99]`. The left subexpression occupies three instructions. Its induction hypothesis applies at 10 with stack `[99]` and finishes at 13 with `[3, 99]`. The right subexpression occupies four instructions: the two literals, negation of the top element, and addition. Its hypothesis applies at 13 with that new stack and finishes at 17 with `[1, 3, 99]`. The final add at 17 leaves `[4, 99]` at 18. Quantifying over every starting counter and stack tail in the induction assertion is what licenses the second use of the hypothesis.

Return to `x + (2 + y)` in §33.2, with `x = 3` and `y = 4`. Starting at counter zero with stack tail `S`, the block `Ivar x, Iconst 2, Ivar y, Iadd, Iadd` leaves `4 :: 2 :: 3 :: S` at counter three. The next two instructions leave `6 :: 3 :: S` and `9 :: S`. At the corresponding lookup in the CPS machine, four meets `[Combine(2), Combine(3)]`. The saved left operands occur on the value stack; the two pending additions are encoded by the remaining instructions. The CPS caller doubles nine only after the expression returns; that operation belongs to the caller in the compiled execution as well.

There is also a useful list-level version of the continuation argument. A successful run of the operand blocks prepares exactly the stack needed for the next instruction. The following check isolates what the add instruction may do to *any* stack below its operands. Failure on short stacks is represented explicitly by an optional result.

```lean
def execAdd : List Int → Option (List Int)
  | right :: left :: tail => some ((left + right) :: tail)
  | _ => none

example (left right : Int) (tail : List Int) :
    execAdd (right :: left :: tail) = some ((left + right) :: tail) := rfl

example : execAdd [5] = none := rfl
```

The positive equation is used after both induction hypotheses. The negative example explains the stack precondition the compiler must discharge before requesting that step.

# A block inside a program
%%%
tag := "ch37-s3"
%%%

For `x - (2 + 1)` with $`s(x) = 8`, the block is `Ivar x, Iconst 2, Iconst 1, Iadd, Iopp, Iadd`. Starting at $`p = 4` with stack `[11]`, the successive stacks are `[8,11]`, `[2,8,11]`, `[1,2,8,11]`, `[3,8,11]`, `[-3,8,11]`, and `[5,11]`. The final counter is ten. The caller’s 11 never becomes an operand of any instruction in this block.

Suppose we test the generated block only by reading the top element after execution. A faulty implementation might consume the caller's entire stack and then push the correct answer. It would pass every isolated test that checks only that element. A caller computing “the current result plus an older result” would then fail on its next add. The universal tail in the theorem permits the caller to reason modularly even when the contents of that tail are unknown to the compiler.

Check this at two depths in the worked difference. Immediately before the inner add the stack contains three live operands above 11: 1, 2 and 8. The top two supply the inner sum, while 8 is reserved by the outer subtraction. After the inner add, negation acts on 3 alone. The final addition consumes negative three and eight and leaves 11 untouched. Reversing the order of the two emitted operand blocks would still make many tests involving only addition succeed because integer addition is commutative. Subtraction and a nonempty tail expose two independent classes of error. Each intermediate assertion in the correctness proof rules out one of them.

# Exercises
%%%
tag := "ch37-s4"
number := false
%%%

1. Compile `(x - 2) + 1` and trace it from the same state and stack. Which intermediate stack distinguishes the two source trees?
2. State exactly why an induction hypothesis that mentions only counter zero also fails at the second recursive call.
3. Suppose subtraction emitted opposite *before* the right operand code. Find source values showing failure.

*Further problem.* Let a complete target program run the compiled block for e followed by a fixed instruction sequence J. If starting J with the source value atop a tail S and store s finishes at machine state q, prove that the combined program can reach q. State exactly which ambient-code and counter assumptions are needed.

# Reading for the Seminar
%%%
tag := "ch37-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the instruction preconditions and put a nonempty suffix on the board.

*Joint proof · 30 minutes.* Derive the sum case at arbitrary $`p,S`, recording the code-at premise for the second call and the operand order at the final instruction.

*Proof review · 20 minutes.* Use the difference example to test the stack discipline and the last counter value.

*Facilitator’s hint.* Write the conclusion of the first induction hypothesis in full. It supplies both inputs that must change when invoking the second one.

# Solutions
%%%
tag := "ch37-s6"
number := false
%%%

*1.* Use `Ivar x, Iconst 2, Iopp, Iadd, Iconst 1, Iadd`. After the third instruction the stack is `[-2,8,11]`, and the final result above the suffix is 7.

*2.* The second block begins at $`p + \lvert K(a)\rvert` in the original ambient list. The induction hypothesis at zero says nothing about its instructions at that address.

*3.* With operands 8 and 3 the erroneous sequence negates 8, then pushes 3, then adds to obtain $`- 5` instead of 5.

*Further problem.* Fix the *same* ambient list C for both paths. Let K be the code for e and assume K occurs at p. State the suffix hypothesis at p plus the length of K, with initial stack consisting of eval(e,s) followed by S, and the same store s. If J is named explicitly, assume it is placed at that suffix address; the actual suffix hypothesis must concern transitions of C. The block theorem constructs the first path and gives exactly the three components of the suffix hypothesis's initial configuration. Finite-path transitivity now reaches q. A suffix proof run in a separate list at counter zero cannot simply be pasted here: instructions and any branch destinations must refer to the common ambient program. This exercise is a small consumer of the compiler theorem, which explains each of its quantified parameters.
