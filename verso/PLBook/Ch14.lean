import VersoManual

open Verso.Genre Manual

#doc (Manual) "Compiling Expressions to a Stack Machine" =>
%%%
tag := "ch14"
file := "chapter-14"
%%%

* *Definitions.* Expressions, stores and evaluation (Session 1, Definitions 1.1–1.3; [IMP language card A.1–A.3](imp-card/index.html#imp-a1)). Partial functions ([Session 3, §3.3](chapter-03/index.html#ch03-s3)). The four operations and [Session 4, Theorem 4.1](chapter-04/index.html#ch04-s2). Instructions, code, stacks, transitions, finite paths and the compiler for expressions ([Stack machine card B.1–B.6](machine-card/index.html#machine-b1)).
* *New terms.* Stack, program counter, code at a position, branch-free code, list execution. [Glossary and label key](glossary/index.html)
* *Theorem 14.2 (Compiled code pushes the value).* For every expression $`e`, store $`s` and stack $`S`, list execution of the compiled code $`\mathrm{cexp}(e)` from $`S` is defined and $`\mathrm{run}_s(\mathrm{cexp}(e))(S)=\mathrm{eval}(e,s)::S`.
* *Source.* The instructions, transitions and compiler are those of Leroy’s course, as recorded in the stack machine card. List execution, Theorem 14.2 and Lemma 14.3 are formulated here. Nipkow and Klein prove the same equation for list execution of their compiler, whose expressions have no subtraction. Corollary 14.4 is the correctness theorem for compiled expressions in Leroy’s course. [Definitions and Lean names](machine-card/index.html#machine-sources) · [Concrete Semantics, §3.3, p. 35](https://concrete-semantics.org/concrete-semantics.pdf)
* *Board case.* Sum. Show that the function “run the compiled code” and the function “push the value” satisfy the same constructor equation at $`e_1+e_2`.
* *Proof outline.* Fix the store. Let $`A` be the set of partial functions from stacks to stacks, with four operations read off the compiler. Check the four constructor equations for both functions, using Lemma 14.1 for the compiled code. Theorem 4.1 identifies the two functions. Lemma 14.3, proved by induction on the instruction list with the program counter and the stack quantified, carries the result over to the machine with addresses.
* *From Session 13.* Sessions 11–13 proved properties of source programs in one language. Here a compiler translates expressions into code for a second language, the stack machine, and the main theorem compares the two. Its proof reuses [Session 4, Theorem 4.1](chapter-04/index.html#ch04-s2), which was proved once, by structural induction, for every set with four operations. Here it is applied to a set of functions on stacks, so the proof of Theorem 14.2 needs no induction of its own.

Compile $`x+1` to the three instructions $`\mathsf{load}(x)`, $`\mathsf{push}(1)`, $`\mathsf{plus}`. Run them with $`s(x)=8`, starting from the stack $`[11]`. The stacks are $`[8,11]`, $`[1,8,11]` and $`[9,11]`. The value $`9` lands on top, and the $`11` below it is never touched. In the code for $`(x+1)+y`, the code for $`y` then starts from $`[9,11]`, a stack that already holds a partial result. A theorem about the empty initial stack alone could not justify that second run. The statement must hold for every initial stack, even though every complete program starts with an empty one.

# Code as a function on stacks
%%%
tag := "ch14-s1"
%%%

The [stack machine card](machine-card/index.html#machine-b1) fixes the machine. Code is a list of instructions. A machine configuration $`\langle\mathit{pc},S,s\rangle` consists of a program counter, a stack written with its top on the left, and a store. The compiler for expressions ([B.6](machine-card/index.html#machine-b6)) is

$$`\begin{aligned}
\mathrm{cexp}(n)&=[\mathsf{push}(n)] \qquad \mathrm{cexp}(x)=[\mathsf{load}(x)]\\
\mathrm{cexp}(e_1+e_2)&=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{plus}]\\
\mathrm{cexp}(e_1-e_2)&=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{opp},\mathsf{plus}].
\end{aligned}`

It emits only four of the nine instructions. None of the four changes the store, and each advances the program counter by one. The rule for $`\mathsf{plus}` in [B.4](machine-card/index.html#machine-b4) takes $`n_2::n_1::S` to $`(n_1+n_2)::S`. The integer pushed first is the left operand.

An integer plays three roles here. The program counter indexes instructions. An integer on the stack is a value being computed. The store gives the values of source variables, which $`\mathsf{load}` copies onto the stack. Pushing a negative literal does not move execution backwards. The contract of the expression compiler speaks about all three: the code advances the counter by its length, puts one value on the stack, and preserves the store.

Since these four instructions never jump, the program counter carries no information while they run. We can describe what a list of them does to a stack without mentioning addresses. The opening run is an example: in a store with $`s(x)=8`, the list $`[\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus}]` takes the stack $`[11]` to $`[9,11]`, one instruction at a time.

*Definition 14.1 (Branch-free code and list execution).* Code is *branch-free* if each of its instructions is $`\mathsf{push}(n)`, $`\mathsf{load}(x)`, $`\mathsf{plus}` or $`\mathsf{opp}`. For a store $`s` and branch-free code $`K`, the *list execution* $`\mathrm{run}_s(K)` is the partial function from stacks to stacks defined by recursion on $`K`:

$$`\begin{aligned}
\mathrm{run}_s([\,])(S)&=S\\
\mathrm{run}_s(\mathsf{push}(n)::K)(S)&=\mathrm{run}_s(K)(n::S)\\
\mathrm{run}_s(\mathsf{load}(x)::K)(S)&=\mathrm{run}_s(K)(s(x)::S)\\
\mathrm{run}_s(\mathsf{plus}::K)(n_2::n_1::S)&=\mathrm{run}_s(K)((n_1+n_2)::S)\\
\mathrm{run}_s(\mathsf{opp}::K)(n::S)&=\mathrm{run}_s(K)((-n)::S).
\end{aligned}`

On a stack with fewer than two integers, $`\mathrm{run}_s(\mathsf{plus}::K)` is undefined. On the empty stack, $`\mathrm{run}_s(\mathsf{opp}::K)` is undefined. When the right-hand side of an equation is undefined, so is its left-hand side.

Each equation copies the effect of one rule of B.4 on the stack. In all four cases $`\mathrm{run}_s(i::K)(S)=\mathrm{run}_s(K)\bigl(\mathrm{run}_s([i])(S)\bigr)`. A partial function is defined in Session 3, §3.3. Write $`f:\mathrm{Stack}\rightharpoonup\mathrm{Stack}` for a partial function from stacks to stacks. Two such functions are equal when, at every stack, both are undefined or both are defined with the same value. The composite $`f_2\circ f_1` applies $`f_1` first and then $`f_2`. It is defined at $`S` exactly when $`f_1(S)` is defined and $`f_2` is defined at $`f_1(S)`. Composition is written from right to left, while code is read from left to right.

Split $`[\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus}]` after its first instruction. With $`s(x)=8`, the first part takes $`[11]` to $`[8,11]`, and the second part takes $`[8,11]` to $`[9,11]`. This is the result of the whole list.

*Lemma 14.1 (Concatenation).* For every store $`s` and all branch-free $`K_1,K_2`, $`\mathrm{run}_s(K_1\mathbin{+\!\!+}K_2)=\mathrm{run}_s(K_2)\circ\mathrm{run}_s(K_1)`.

*Proof.* Fix $`s` and $`K_2`. Use structural induction on the list $`K_1`, with the property

$$`Q(K_1)\ \coloneqq\ \forall S,\quad\mathrm{run}_s(K_1\mathbin{+\!\!+}K_2)(S)=\mathrm{run}_s(K_2)\bigl(\mathrm{run}_s(K_1)(S)\bigr),`

where the two sides are undefined together. For $`K_1=[\,]` both sides are $`\mathrm{run}_s(K_2)(S)`. For $`K_1=i::K'` assume $`Q(K')`. Fix $`S` and let $`S_1=\mathrm{run}_s([i])(S)`. If $`S_1` is undefined, both sides are undefined. Otherwise, since $`(i::K')\mathbin{+\!\!+}K_2=i::(K'\mathbin{+\!\!+}K_2)`, the left side is $`\mathrm{run}_s(i::(K'\mathbin{+\!\!+}K_2))(S)=\mathrm{run}_s(K'\mathbin{+\!\!+}K_2)(S_1)`. Apply $`Q(K')` at the stack $`S_1` to rewrite this as $`\mathrm{run}_s(K_2)(\mathrm{run}_s(K')(S_1))`. Finally $`\mathrm{run}_s(K')(S_1)=\mathrm{run}_s(i::K')(S)`. $`\square`

The induction hypothesis is used at $`S_1`, not at $`S`. This is why $`Q` quantifies the stack. Nipkow and Klein use the same lemma for their execution function (CS §3.3). Concatenations of branch-free lists are branch-free, and each equation of B.6 emits only the four instructions above. By structural induction on $`e`, every $`\mathrm{cexp}(e)` is branch-free.

# Two functions with the same equations
%%%
tag := "ch14-s2"
%%%

Fix a store with $`s(x)=8` and take $`e=x+1`. Running the compiled code takes $`[11]` to $`[9,11]`, as in the opening example. Pushing the value $`\mathrm{eval}(x+1,s)=9` also takes $`[11]` to $`[9,11]`. We want this agreement for every expression and every stack.

Fix a store $`s`. Let $`A` be the set of partial functions $`\mathrm{Stack}\rightharpoonup\mathrm{Stack}`. Read four operations off the compiler:

$$`\begin{aligned}
L(n)&=(S\mapsto n::S) & V_A(x)&=(S\mapsto s(x)::S)\\
P(f_1,f_2)&=\mathrm{run}_s([\mathsf{plus}])\circ f_2\circ f_1 & M(f_1,f_2)&=\mathrm{run}_s([\mathsf{opp},\mathsf{plus}])\circ f_2\circ f_1.
\end{aligned}`

These are operations $`L:\mathbb Z\to A`, $`V_A:V\to A` and $`P,M:A\times A\to A` as in Session 4, §4.1, where $`V` is the set of variable names and $`E` the set of expressions. In $`P(f_1,f_2)` the function $`f_1` of the left operand acts first, then $`f_2`, and then the instruction $`\mathsf{plus}`. Define two functions from expressions to $`A`:

$$`g(e)=\mathrm{run}_s(\mathrm{cexp}(e)),\qquad h(e)=\bigl(S\mapsto\mathrm{eval}(e,s)::S\bigr).`

The function $`g` runs the compiled code. The function $`h` pushes the value.

*Theorem 14.2 (Compiled code pushes the value).* For every expression $`e`, store $`s` and stack $`S`, $`\mathrm{run}_s(\mathrm{cexp}(e))(S)` is defined and

$$`\mathrm{run}_s(\mathrm{cexp}(e))(S)=\mathrm{eval}(e,s)::S.`

*Proof.* Fix $`s`. By Theorem 4.1, exactly one function $`k:E\to A` satisfies the four constructor equations

$$`k(n)=L(n),\quad k(x)=V_A(x),\quad k(e_1+e_2)=P(k(e_1),k(e_2)),\quad k(e_1-e_2)=M(k(e_1),k(e_2)).`

We show that both $`g` and $`h` satisfy them. Uniqueness then gives $`g=h`.

*Literal and variable.* By B.6 and Definition 14.1, $`g(n)(S)=\mathrm{run}_s([\mathsf{push}(n)])(S)=n::S=L(n)(S)`. By A.3, $`h(n)(S)=\mathrm{eval}(n,s)::S=n::S`. In the same way $`g(x)(S)=s(x)::S=h(x)(S)=V_A(x)(S)`.

*Sum (board case).* We must show, for all expressions $`e_1,e_2`,

$$`g(e_1+e_2)=P\bigl(g(e_1),g(e_2)\bigr)\qquad\text{and}\qquad h(e_1+e_2)=P\bigl(h(e_1),h(e_2)\bigr).`

Both sides of each equation are partial functions on stacks. Fix $`e_1` and $`e_2`.

1. By B.6, $`\mathrm{cexp}(e_1+e_2)=\mathrm{cexp}(e_1)\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{plus}]`.
2. Apply Lemma 14.1 with $`K_1=\mathrm{cexp}(e_1)` and $`K_2=\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{plus}]`. Apply it again with $`K_1=\mathrm{cexp}(e_2)` and $`K_2=[\mathsf{plus}]`. This gives $`\mathrm{run}_s(\mathrm{cexp}(e_1+e_2))=\mathrm{run}_s([\mathsf{plus}])\circ\mathrm{run}_s(\mathrm{cexp}(e_2))\circ\mathrm{run}_s(\mathrm{cexp}(e_1))`.
3. The left side is $`g(e_1+e_2)`. The right side is $`\mathrm{run}_s([\mathsf{plus}])\circ g(e_2)\circ g(e_1)`, which is $`P(g(e_1),g(e_2))` by the definition of $`P`. This proves the equation for $`g`.
4. For $`h`, fix a stack $`S` and write $`n_1=\mathrm{eval}(e_1,s)` and $`n_2=\mathrm{eval}(e_2,s)`. By the definition of $`h`, $`h(e_1)(S)=n_1::S`.
5. Apply $`h(e_2)` to that stack: $`h(e_2)(n_1::S)=n_2::n_1::S`.
6. By Definition 14.1, $`\mathrm{run}_s([\mathsf{plus}])(n_2::n_1::S)=(n_1+n_2)::S`. Steps 4–6 compute $`P(h(e_1),h(e_2))(S)=(n_1+n_2)::S`.
7. By A.3, $`n_1+n_2=\mathrm{eval}(e_1+e_2,s)`. So the stack of step 6 is $`h(e_1+e_2)(S)`. Since $`S` was arbitrary, $`h(e_1+e_2)=P(h(e_1),h(e_2))`.

No induction hypothesis appears in these steps. The induction was done once, in the proof of Theorem 4.1. Step 5 applies $`h(e_2)` to the stack $`n_1::S`, which is never empty. This is where the arbitrary stack is needed. Knowing what the code of $`e_2` does to the empty stack alone would not determine what it does to $`n_1::S`.

*Difference.* Steps 1–3 with $`[\mathsf{opp},\mathsf{plus}]` in place of $`[\mathsf{plus}]` give $`g(e_1-e_2)=M(g(e_1),g(e_2))`. For $`h`, steps 4 and 5 give $`n_2::n_1::S`. Then $`\mathrm{run}_s([\mathsf{opp},\mathsf{plus}])` takes this stack to $`(-n_2)::n_1::S` and then to $`(n_1+(-n_2))::S=(n_1-n_2)::S`, which is $`h(e_1-e_2)(S)` by A.3.

Both $`g` and $`h` satisfy the four equations, so $`g=h`. Apply both sides to $`S`. Since $`h(e)(S)` is defined, so is $`g(e)(S)`, and the two stacks are equal. $`\square`

The theorem also shows that compiled code never runs out of operands, whatever stack it starts from. It constrains more than the top of the final stack. Suppose we tested compiled code only by reading the top value after a run from the empty stack. A faulty compiler whose code for a sum first discards the whole stack and then pushes the correct answer would pass every such test. A caller computing “the current result plus an older result” would then fail at its next $`\mathsf{plus}`. Theorem 14.2 rules this out because it identifies $`g(e)` with $`h(e)` at every stack: the stack $`S` must remain below the value. Reversing the order of the two operand blocks would also pass many tests that use only addition, since integer addition is commutative. Subtraction and a nonempty stack below the operands expose these two kinds of error.

# From lists to addresses
%%%
tag := "ch14-s3"
%%%

Sessions 15 and 16 place expression code inside larger programs that contain branches. There the machine of B.4 runs with a program counter, and the code sits at a position of a larger list ([B.2](machine-card/index.html#machine-b2)). Lemma 14.3 connects the two descriptions.

Let $`C` contain $`\mathrm{cexp}(x-(2+1))=[\mathsf{load}(x),\mathsf{push}(2),\mathsf{push}(1),\mathsf{plus},\mathsf{opp},\mathsf{plus}]` at position $`4`, and let $`s(x)=8`. From $`\langle4,[11],s\rangle` the machine passes through the counters $`5` to $`10` with the stacks $`[8,11]`, $`[2,8,11]`, $`[1,2,8,11]`, $`[3,8,11]`, $`[-3,8,11]` and $`[5,11]`. These are the stacks of list execution, and the final counter is $`4` plus the length six of the code. The caller’s $`11` never becomes an operand. Before the inner $`\mathsf{plus}` the stack holds three values above $`11`: the top two form the inner sum, while $`8` waits for the outer subtraction.

An occurrence of a block carries more information than its first instruction. The same push instruction may appear at several positions of $`C`. A premise saying only “the instruction at $`\mathit{pc}` is the first push” cannot justify the second push or the final $`\mathsf{plus}`. The relation $`\mathrm{at}(C,\mathit{pc},K)` splits $`C` into a prefix of length $`\mathit{pc}`, the block $`K` and a suffix. Stepping over one instruction extends the prefix by one and leaves the rest of the block intact (B.2, fact 1). No assumption about what follows the block is needed.

*Lemma 14.3 (Bridge).* Let $`K` be branch-free. For every code $`C`, store $`s`, position $`\mathit{pc}` and stacks $`S,S'`, if $`\mathrm{at}(C,\mathit{pc},K)` and $`\mathrm{run}_s(K)(S)=S'`, then

$$`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|K|,S',s\rangle.`

*Proof.* Fix $`C` and $`s`. Use structural induction on the list $`K`, with the property

$$`R(K)\ \coloneqq\ \forall\mathit{pc},S,S',\quad\mathrm{at}(C,\mathit{pc},K)\land\mathrm{run}_s(K)(S)=S'\ \Longrightarrow\ C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|K|,S',s\rangle.`

For $`K=[\,]` we have $`S'=S`, and the path with zero transitions ends at $`\mathit{pc}+0`. For $`K=i::K'` assume $`R(K')`. Let $`S_1=\mathrm{run}_s([i])(S)`. It is defined, and $`\mathrm{run}_s(K')(S_1)=S'`. By B.2, fact 1, $`C(\mathit{pc})=i` and $`\mathrm{at}(C,\mathit{pc}+1,K')`. Each of the four instructions has a rule in B.4 with the same effect on the stack, so $`C\vdash\langle\mathit{pc},S,s\rangle\to\langle\mathit{pc}+1,S_1,s\rangle`. For example, if $`i=\mathsf{plus}` then $`S=n_2::n_1::S_0` and $`S_1=(n_1+n_2)::S_0` for some $`n_1,n_2,S_0`. Apply $`R(K')` at the counter $`\mathit{pc}+1` and the stack $`S_1` to obtain $`C\vdash\langle\mathit{pc}+1,S_1,s\rangle\to^*\langle\mathit{pc}+1+|K'|,S',s\rangle`. Put the transition in front of this path (B.5), and note $`|K|=1+|K'|`. $`\square`

The induction hypothesis is used at the counter $`\mathit{pc}+1` and the stack $`S_1`. If $`R` fixed the counter and the stack outside the quantifier, the hypothesis would speak about the wrong position and the wrong stack. Lemma 14.3 needs branch-free code. A branch moves the counter to an address that list execution does not record. The instruction $`\mathsf{setvar}` changes the store, so it does not fit a function on stacks for one store. Session 16 handles it with one transition after the expression code.

Now compile $`(1+2)+(4-3)` and place the code at counter $`10` with the stack $`[99]`. The left operand occupies three instructions. Its code runs from counter $`10` and finishes at $`13` with $`[3,99]`. The right operand occupies four instructions: two pushes, $`\mathsf{opp}` and $`\mathsf{plus}`. Its code starts at $`13` with the new stack and finishes at $`17` with $`[1,3,99]`. The final $`\mathsf{plus}` at $`17` leaves $`[4,99]` at $`18`. The counter advanced by eight, the length of the code, and $`4=\mathrm{eval}((1+2)+(4-3),s)`.

*Corollary 14.4 (Compiled expressions on the machine).* For every code $`C`, store $`s`, expression $`e`, position $`\mathit{pc}` and stack $`S`, if $`\mathrm{at}(C,\mathit{pc},\mathrm{cexp}(e))` then

$$`C\vdash\langle\mathit{pc},S,s\rangle\to^*\langle\mathit{pc}+|\mathrm{cexp}(e)|,\ \mathrm{eval}(e,s)::S,\ s\rangle.`

*Proof.* The code $`\mathrm{cexp}(e)` is branch-free (§14.1). By Theorem 14.2, $`\mathrm{run}_s(\mathrm{cexp}(e))(S)=\mathrm{eval}(e,s)::S`. Apply Lemma 14.3 with $`K=\mathrm{cexp}(e)` and $`S'=\mathrm{eval}(e,s)::S`. $`\square`

This is the correctness theorem for expressions in Leroy’s course, and it is the form that Sessions 15 and 16 use. It stops at the end of the block even when another instruction follows.

# Exercises
%%%
tag := "ch14-s4"
number := false
%%%

*14.1.* Compile $`(x-2)+1` and run the code with $`s(x)=8` from the stack $`[11]`. Which intermediate stack distinguishes it from the run of $`x-(2+1)` in §14.3?

*14.2.* Suppose we knew only that $`\mathrm{run}_s(\mathrm{cexp}(e))([\,])=[\mathrm{eval}(e,s)]` for every $`e`. Inside a run of $`\mathrm{cexp}(e_1+e_2)` from $`[\,]`, from which stack does the code of $`e_2` start? Explain why the known fact does not determine the result for $`e_1+e_2`. In the proof of Lemma 14.3, at which counter and stack is the induction hypothesis used?

*14.3.* Suppose the compiler emitted $`\mathrm{cexp}(e_1)\mathbin{+\!\!+}[\mathsf{opp}]\mathbin{+\!\!+}\mathrm{cexp}(e_2)\mathbin{+\!\!+}[\mathsf{plus}]` for a difference. Find values for which the code computes a wrong result. Which step in the proof of Theorem 14.2 fails?

*Further problem.* Let a complete target program run the compiled block for $`e` followed by a fixed instruction sequence $`J`. Suppose that $`J`, started with the value of $`e` on top of a stack $`S` and with store $`s`, reaches a machine configuration $`q`. Prove that the combined program reaches $`q`. State exactly which assumptions about the code and the counter are needed.

# Reading for the Seminar
%%%
tag := "ch14-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the rules for $`\mathsf{push}`, $`\mathsf{load}`, $`\mathsf{plus}` and $`\mathsf{opp}`, each with a nonempty part of the stack below the operands. Run $`[\mathsf{load}(x),\mathsf{push}(1),\mathsf{plus}]` from $`[11]`.

*Joint proof · 30 minutes.* Write the four operations on $`A`. Verify the sum equation for $`g` with Lemma 14.1 and for $`h` by three stack updates. Conclude with Theorem 4.1.

*Proof review · 20 minutes.* Use the difference example at counter $`4` to check Lemma 14.3 and Corollary 14.4. Use Exercise 14.3 to find the equation that fails.

*Facilitator’s hint.* Write composition from right to left and code from left to right. In step 5 of the board case, ask which stack $`h(e_2)` receives.

# Solutions and Further Reading
%%%
tag := "ch14-s6"
number := false
%%%

*14.1.* The code is $`[\mathsf{load}(x),\mathsf{push}(2),\mathsf{opp},\mathsf{plus},\mathsf{push}(1),\mathsf{plus}]`. The stacks are $`[8,11]`, $`[2,8,11]`, $`[-2,8,11]`, $`[6,11]`, $`[1,6,11]` and $`[7,11]`. After the third instruction the stack is $`[-2,8,11]`, whereas the run of $`x-(2+1)` has $`[1,2,8,11]` there. The final values above $`11` are $`7` and $`5`.

*14.2.* The code of $`e_2` starts from $`[\mathrm{eval}(e_1,s)]`, not from $`[\,]`. The known fact speaks only about the empty stack, so it says nothing about this run. The operation $`P` applies the function of $`e_2` to whatever stack the function of $`e_1` produced, which is why an element of $`A` must be defined at every stack. In Lemma 14.3 the hypothesis is used at the counter $`\mathit{pc}+1` and at the stack after the first instruction. An induction property with the counter fixed at $`0` and the stack fixed at $`[\,]` would give a hypothesis about the wrong position and the wrong stack.

*14.3.* Take the literals $`8` and $`3`. The faulty code negates $`8`, then pushes $`3`, then adds, giving $`[-5]` instead of $`[5]`. The faulty code satisfies the difference equation for the operation $`M'(f_1,f_2)=\mathrm{run}_s([\mathsf{plus}])\circ f_2\circ\mathrm{run}_s([\mathsf{opp}])\circ f_1`. But $`M'(h(e_1),h(e_2))(S)=(n_2-n_1)::S`, so $`h` does not satisfy it. The difference case for $`h` fails, and Theorem 4.1 can no longer identify the two functions.

*Further problem.* Fix the same code $`C` for both paths. Let $`K=\mathrm{cexp}(e)` and assume $`\mathrm{at}(C,\mathit{pc},K)`. Assume that $`J` is placed at $`\mathit{pc}+|K|` in $`C`, and state the hypothesis about $`J` as a finite path of $`C` itself: $`C\vdash\langle\mathit{pc}+|K|,\mathrm{eval}(e,s)::S,s\rangle\to^*q`. Corollary 14.4 gives the first path, ending in exactly this configuration. Joining the two paths (B.5) reaches $`q`. A path of $`J` run as a separate list from counter $`0` cannot be pasted in. Its instructions and any branch destinations must refer to positions in the common code $`C`. This small consumer of the compiler theorem explains each of its quantified parameters.

*Further reading · A direct proof.* Leroy’s course proves Corollary 14.4 directly, by structural induction on $`e` with the counter and the stack quantified inside the induction property. In the sum case write $`\ell_1=|\mathrm{cexp}(e_1)|` and $`\ell_2=|\mathrm{cexp}(e_2)|`. By B.2, the code of $`e_1` is at $`\mathit{pc}`, the code of $`e_2` at $`\mathit{pc}+\ell_1`, and $`\mathsf{plus}` at $`\mathit{pc}+\ell_1+\ell_2`. The first induction hypothesis reaches the counter $`\mathit{pc}+\ell_1` with the stack $`n_1::S`. The second is applied at this new counter and stack, and reaches $`\mathit{pc}+\ell_1+\ell_2` with $`n_2::n_1::S`. One more transition reaches $`\mathit{pc}+\ell_1+\ell_2+1` with $`(n_1+n_2)::S`. Joining the three paths proves the sum case. The proof in this session separates the two concerns: Theorem 4.1 handles the stack, and Lemma 14.3 handles the addresses once for all branch-free code.

*Further reading · Sources.* Nipkow and Klein, _Concrete Semantics_, §3.3, define list execution as a total function and leave the result of an addition on a short stack unspecified. Their Exercise 3.10 asks for the partial version used here. Their Lemma 8.6 in §8.3 states the program-counter form for an extended machine. Leroy’s _Compiler Verification_ course compiles the same expressions to the machine of the stack machine card. [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf) · [Definitions and Lean names](machine-card/index.html#machine-sources)

# Sources and Formalization
%%%
tag := "ch14-notes"
number := false
%%%

* *Definition 14.1.* Formulated in this book.
* *Lemma 14.1.* Formulated in this book. Paper proof only ([§14.1](chapter-14/index.html#ch14-s1)).
* *Theorem 14.2.* Formulated in this book. Corresponds to CS §3.3. Paper proof only ([§14.2](chapter-14/index.html#ch14-s2)).
* *Lemma 14.3.* Formulated in this book. Paper proof only ([§14.3](chapter-14/index.html#ch14-s3)).
* *Corollary 14.4.* Externally checked: the statement matches a declaration of Leroy’s course ([machine-card references](machine-card/index.html#machine-sources)).
