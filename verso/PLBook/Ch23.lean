import VersoManual

open Verso.Genre Manual

#doc (Manual) "Evaluation Strategies" =>
%%%
tag := "ch23"
file := "chapter-23"
%%%

A function may return without using its operand. The term $`(\lambda y.\lambda z.z)\,\Omega` of [C.1](lambda-card/index.html#lambda-c1) applies such a function to $`\Omega`, a term that steps to itself forever. Call by value evaluates the operand before it substitutes it, so it repeats the step of $`\Omega` and never returns. Call by name substitutes $`\Omega` unevaluated, and the function discards it in one step. This session states the difference as a theorem about one term and proves it from the rules. The proof needs one more fact: from each term, each strategy allows at most one step.

*In this session.*

* *Definitions.* [Lambda card C.1](lambda-card/index.html#lambda-c1): terms, free variables and capture-avoiding substitution $`[x\mapsto s]t` ([Session 22](chapter-22/index.html)); values, redexes, the call-by-value rules E-App1, E-App2 and E-AppAbs, computation and congruence rules, normal forms, $`\to^*`, the call-by-name rules N-App1 and N-AppAbs, and the term $`\Omega`. Finite and infinite paths as in [A.6](imp-card/index.html#imp-a6). Induction on derivations ([Session 1, §1.5](chapter-01/index.html#ch01-s5)) with the second result quantified inside the induction property ([Session 3, Theorem 3.2](chapter-03/index.html#ch03-s2)).
* *New terms.* Evaluation strategy, call by value, call by name, determinacy of one-step evaluation, divergence. [Glossary](glossary/index.html)
* *Theorem 23.4 (Call by name returns where call by value diverges).* Let $`\mathsf{id}=\lambda x.x` and $`u=(\lambda y.\lambda z.z)\,\Omega\,\mathsf{id}`. (a) Under call by name, $`u\to_{\mathrm n}(\lambda z.z)\,\mathsf{id}\to_{\mathrm n}\mathsf{id}`, and $`\mathsf{id}` is a value. (b) Under call by value, $`u\to u`, and for every natural number $`k` and term $`s`, if $`u\to^k s` then $`s=u`. Hence no normal form, and in particular no value, is reachable from $`u` under call by value: $`u` diverges.
* *Board case.* Theorem 23.4, both parts. Evaluate $`u` step by step under call by name, naming each rule and computing each substitution. Derive the call-by-value step $`u\to u`. Then use Theorem 23.1 and induction on the length of a path to show that call by value never leaves $`u`.
* *Proof outline.* Call by name: N-AppAbs inside N-App1 discards $`\Omega` without evaluating it, and a second N-AppAbs gives $`\mathsf{id}`. Call by value: E-AppAbs gives $`\Omega\to\Omega`, and E-App2 and E-App1 lift this step to $`u\to u`. By Theorem 23.1 it is the only step from $`u`. Induction on $`k` proves $`Q(k)\coloneqq\forall s,\ (u\to^k s)\Rightarrow s=u`.
* *From Session 22.* Session 22 defined capture-avoiding substitution. Here each computation rule substitutes an operand for a parameter. The two strategies differ in when they do so. Call by value first evaluates the operand to a value. Call by name substitutes the operand as it stands.

# Two strategies
%%%
tag := "ch23-s1"
%%%

In an application $`t_1\,t_2` we call $`t_1` the *operator* and $`t_2` the *operand*. This operator is a term; the operators of Session 9 are functions on state transformers. Let $`\mathsf{id}=\lambda x.x`. The term

$$`\mathsf{id}\,(\mathsf{id}\,(\lambda z.\mathsf{id}\,z))`

contains three redexes: the whole term, its operand $`\mathsf{id}\,(\lambda z.\mathsf{id}\,z)`, and the term $`\mathsf{id}\,z` inside the abstraction. Contracting a redex $`(\lambda x.t_{12})\,t_2` replaces it by $`[x\mapsto t_2]t_{12}`. Contracting the whole term gives $`[x\mapsto\mathsf{id}\,(\lambda z.\mathsf{id}\,z)]x=\mathsf{id}\,(\lambda z.\mathsf{id}\,z)`. Contracting the operand gives the same term. Contracting $`\mathsf{id}\,z` gives $`\mathsf{id}\,(\mathsf{id}\,(\lambda z.z))`. An *evaluation strategy* is a set of one-step rules that decides which redex is contracted next.

This session compares two strategies. Both evaluate the operator first, and neither steps inside an abstraction.

* *Call by value* is the one-step relation $`t\to t'` of C.1, given by E-App1, E-App2 and E-AppAbs. It contracts a redex only when the operand is a value. It evaluates the operand once the operator is a value.
* *Call by name* is the one-step relation $`t\to_{\mathrm n}t'` of C.1, given by N-App1 and N-AppAbs. It contracts a redex whatever the operand is. No rule evaluates an operand.

$$`\frac{t_1\to t_1'}{t_1\,t_2\to t_1'\,t_2}\;\textsf{E-App1}\qquad\frac{t_2\to t_2'}{v_1\,t_2\to v_1\,t_2'}\;\textsf{E-App2}`

$$`\frac{}{(\lambda x.t_{12})\,v_2\to[x\mapsto v_2]t_{12}}\;\textsf{E-AppAbs}`

$$`\frac{t_1\to_{\mathrm n}t_1'}{t_1\,t_2\to_{\mathrm n}t_1'\,t_2}\;\textsf{N-App1}\qquad\frac{}{(\lambda x.t_{12})\,t_2\to_{\mathrm n}[x\mapsto t_2]t_{12}}\;\textsf{N-AppAbs}`

Write $`t\to_{\mathrm n}^*t'` for zero or more call-by-name steps. Write $`t\to^k s` when $`s` is reached from $`t` in exactly $`k` call-by-value steps, as in A.6 (which writes the number of steps as $`n`). In every rule the left side of the conclusion is an application. So a variable or an abstraction has no step under either strategy. In particular every value is a normal form (C.1).

Evaluate the example under call by value. E-AppAbs does not apply to the whole term, because its operand $`\mathsf{id}\,(\lambda z.\mathsf{id}\,z)` is not a value. The operator $`\mathsf{id}` is a value, so E-App2 applies. Its premise is the E-AppAbs step $`\mathsf{id}\,(\lambda z.\mathsf{id}\,z)\to[x\mapsto\lambda z.\mathsf{id}\,z]x=\lambda z.\mathsf{id}\,z`. A second E-AppAbs step finishes:

$$`\mathsf{id}\,(\mathsf{id}\,(\lambda z.\mathsf{id}\,z))\to\mathsf{id}\,(\lambda z.\mathsf{id}\,z)\to\lambda z.\mathsf{id}\,z.`

Under call by name, N-AppAbs contracts the whole term at once. Its operand is substituted as it stands: $`[x\mapsto\mathsf{id}\,(\lambda z.\mathsf{id}\,z)]x=\mathsf{id}\,(\lambda z.\mathsf{id}\,z)`. A second N-AppAbs step finishes:

$$`\mathsf{id}\,(\mathsf{id}\,(\lambda z.\mathsf{id}\,z))\to_{\mathrm n}\mathsf{id}\,(\lambda z.\mathsf{id}\,z)\to_{\mathrm n}\lambda z.\mathsf{id}\,z.`

The two paths pass through the same terms, but their first steps contract different redexes. Both stop at $`\lambda z.\mathsf{id}\,z`. It is a value, so neither strategy contracts the redex $`\mathsf{id}\,z` in its body. TAPL §5.1 compares strategies on this term.

# One step at a time
%%%
tag := "ch23-s2"
%%%

In the example of §23.1, call by value had only one possible first step. E-AppAbs needs a value operand, and the operand $`\mathsf{id}\,(\lambda z.\mathsf{id}\,z)` is an application. E-App1 needs a step of the operator $`\mathsf{id}`, which is a value. Only E-App2 remains. The same check works for every term. Terms are equal when they are alpha-equivalent (C.1).

*Theorem 23.1 (Determinacy of call by value).* For all terms $`t,t',t''`, if $`t\to t'` and $`t\to t''` then $`t'=t''`.

*Proof.* We prove $`P(D)` for every derivation $`D` of a step, by induction on $`D`. For $`D:t\to t'` the induction property is

$$`P(D)\coloneqq\forall s,\ (t\to s)\Rightarrow t'=s.`

As in Session 3, Theorem 3.2, the other result $`s` is quantified inside $`P(D)`. So an induction hypothesis can be applied to whatever step the second derivation contains. In each case fix $`s` and a second derivation $`E:t\to s`. We must show $`t'=s`. There is one case for each rule that can end $`D`.

*E-AppAbs.* Then $`t=(\lambda x.t_{12})\,v_2` and $`t'=[x\mapsto v_2]t_{12}`. The last rule of $`E` is not E-App1, whose premise would be a step of the value $`\lambda x.t_{12}`. It is not E-App2, whose premise would be a step of the value $`v_2`. So $`E` ends with E-AppAbs, and $`s=[x\mapsto v_2]t_{12}=t'`.

*E-App1.* Then $`t=t_1\,t_2` and $`t'=t_1'\,t_2`, and the premise of $`D` is $`D_1:t_1\to t_1'`. Its induction hypothesis is

$$`P(D_1):\quad\forall s_1,\ (t_1\to s_1)\Rightarrow t_1'=s_1.`

1. The last rule of $`E` is not E-App2 or E-AppAbs. Both require $`t_1` to be a value, but $`D_1` is a step of $`t_1` and values have no step.
2. So $`E` ends with E-App1. Inversion gives a premise $`E_1:t_1\to t_1''` and $`s=t_1''\,t_2`.
3. Apply $`P(D_1)` with $`s_1=t_1''` to $`E_1`. This gives $`t_1'=t_1''`, so $`t'=t_1'\,t_2=t_1''\,t_2=s`.

*E-App2.* Then $`t=v_1\,t_2` and $`t'=v_1\,t_2'`, and the premise of $`D` is $`D_2:t_2\to t_2'`, with

$$`P(D_2):\quad\forall s_2,\ (t_2\to s_2)\Rightarrow t_2'=s_2.`

The last rule of $`E` is not E-App1, whose premise would be a step of the value $`v_1`. It is not E-AppAbs, which requires $`t_2` to be a value, while $`D_2` is a step of $`t_2`. So $`E` ends with E-App2, with a premise $`E_2:t_2\to t_2''` and $`s=v_1\,t_2''`. Apply $`P(D_2)` with $`s_2=t_2''` to $`E_2`. This gives $`t_2'=t_2''`, so $`t'=s`.

This proves $`P(D)` for every $`D`. Let $`D` derive the first step $`t\to t'` of the theorem, and apply $`P(D)` with $`s=t''` to the second step. $`\square`

*Proposition 23.2 (Determinacy of call by name).* For all terms $`t,t',t''`, if $`t\to_{\mathrm n}t'` and $`t\to_{\mathrm n}t''` then $`t'=t''`.

*Proof.* Induction on the derivation $`D:t\to_{\mathrm n}t'`, with $`P_{\mathrm n}(D)\coloneqq\forall s,\ (t\to_{\mathrm n}s)\Rightarrow t'=s`. Fix $`s` and $`E:t\to_{\mathrm n}s`. If $`D` ends with N-AppAbs, then $`t=(\lambda x.t_{12})\,t_2`. The derivation $`E` cannot end with N-App1, whose premise would be a step of the value $`\lambda x.t_{12}`. So $`E` also ends with N-AppAbs, and $`s=[x\mapsto t_2]t_{12}=t'`. If $`D` ends with N-App1, then $`t=t_1\,t_2` and $`t'=t_1'\,t_2`, with premise $`D_1:t_1\to_{\mathrm n}t_1'` and induction hypothesis $`P_{\mathrm n}(D_1):\ \forall s_1,\ (t_1\to_{\mathrm n}s_1)\Rightarrow t_1'=s_1`. N-AppAbs would require $`t_1` to be an abstraction, and $`t_1` has a step. So $`E` ends with N-App1 too, with premise $`E_1:t_1\to_{\mathrm n}t_1''` and $`s=t_1''\,t_2`. Apply $`P_{\mathrm n}(D_1)` with $`s_1=t_1''` to $`E_1`. This gives $`t_1'=t_1''`, so $`t'=s`. $`\square`

Session 3 proved the same property for the execution of commands. Here it means that under each strategy the steps from a term form a single path: at each term there is at most one next term.

# An unused operand
%%%
tag := "ch23-s3"
%%%

Recall $`\Omega=(\lambda x.x\,x)\,(\lambda x.x\,x)` from C.1. Its operand is a value, so E-AppAbs applies. The substitution is computed clause by clause:

$$`[x\mapsto\lambda x.x\,x](x\,x)=([x\mapsto\lambda x.x\,x]x)\,([x\mapsto\lambda x.x\,x]x)=(\lambda x.x\,x)\,(\lambda x.x\,x)=\Omega.`

So $`\Omega\to\Omega`. The same substitution gives $`\Omega\to_{\mathrm n}\Omega` by N-AppAbs. By Theorem 23.1 and Proposition 23.2 this is the only step from $`\Omega` under either strategy.

*Definition 23.3 (Divergence).* A term $`t` *diverges* under call by value if there is no normal form $`s` with $`t\to^*s`. It diverges under call by name if there is no normal form $`s` with $`t\to_{\mathrm n}^*s`.

For example, $`\Omega` diverges under both strategies. The argument is steps 6–8 below with $`\Omega` in place of $`u`, and for call by name with Proposition 23.2 in place of Theorem 23.1. If a term diverges, every term reachable from it has a next term. By determinacy these terms form one infinite path as in A.6.

The term $`(\lambda y.\lambda z.z)\,\Omega` of the opening paragraph steps to itself by E-App2 and steps to $`\lambda z.z` by N-AppAbs. The theorem applies it to one more operand, so that call by name takes two steps and uses a congruence rule.

*Theorem 23.4 (Call by name returns where call by value diverges).* Let $`u=(\lambda y.\lambda z.z)\,\Omega\,\mathsf{id}`. (a) Under call by name, $`u\to_{\mathrm n}(\lambda z.z)\,\mathsf{id}\to_{\mathrm n}\mathsf{id}`, and $`\mathsf{id}` is a value. (b) Under call by value, $`u\to u`, and for every natural number $`k` and term $`s`, if $`u\to^k s` then $`s=u`. Hence $`u` diverges under call by value. In particular no value is reachable from $`u`.

*Proof.* We must show (a) and (b). Application associates to the left, so $`u` is $`((\lambda y.\lambda z.z)\,\Omega)\,\mathsf{id}`. Its operator is $`(\lambda y.\lambda z.z)\,\Omega` and its operand is $`\mathsf{id}`. Steps 1–3 prove (a) and steps 4–8 prove (b). Step 2 builds the first derivation below and step 5 builds the second.

$$`\frac{\dfrac{}{(\lambda y.\lambda z.z)\,\Omega\to_{\mathrm n}\lambda z.z}\;\textsf{N-AppAbs}}{(\lambda y.\lambda z.z)\,\Omega\,\mathsf{id}\to_{\mathrm n}(\lambda z.z)\,\mathsf{id}}\;\textsf{N-App1}`

$$`\frac{\dfrac{\dfrac{}{\Omega\to\Omega}\;\textsf{E-AppAbs}}{(\lambda y.\lambda z.z)\,\Omega\to(\lambda y.\lambda z.z)\,\Omega}\;\textsf{E-App2}}{(\lambda y.\lambda z.z)\,\Omega\,\mathsf{id}\to(\lambda y.\lambda z.z)\,\Omega\,\mathsf{id}}\;\textsf{E-App1}`

1. *Call by name.* The operator $`(\lambda y.\lambda z.z)\,\Omega` is a redex. N-AppAbs gives $`(\lambda y.\lambda z.z)\,\Omega\to_{\mathrm n}[y\mapsto\Omega](\lambda z.z)`. Since $`z\neq y` and $`z\notin\mathrm{FV}(\Omega)=\varnothing`, the abstraction clause of substitution applies: $`[y\mapsto\Omega](\lambda z.z)=\lambda z.\,[y\mapsto\Omega]z=\lambda z.z`.
2. N-App1, with the step of 1 as its premise, gives $`u\to_{\mathrm n}(\lambda z.z)\,\mathsf{id}`. The operand $`\Omega` has been discarded without a single step of its own.
3. N-AppAbs gives $`(\lambda z.z)\,\mathsf{id}\to_{\mathrm n}[z\mapsto\mathsf{id}]z=\mathsf{id}`. The term $`\mathsf{id}=\lambda x.x` is an abstraction, hence a value. This proves (a).
4. *Call by value.* E-AppAbs gives $`\Omega\to\Omega`, by the substitution computed above.
5. In $`(\lambda y.\lambda z.z)\,\Omega` the operator $`\lambda y.\lambda z.z` is a value. E-App2 with premise 4 gives $`(\lambda y.\lambda z.z)\,\Omega\to(\lambda y.\lambda z.z)\,\Omega`. E-App1 with this step as premise gives $`u\to u`.
6. Apply Theorem 23.1 to the step $`u\to u` of 5 and any step $`u\to s_1`. This gives $`s_1=u`. So $`u\to u` is the only step from $`u`.
7. We prove $`Q(k)\coloneqq\forall s,\ (u\to^k s)\Rightarrow s=u` by induction on $`k`. For $`k=0` the path has no step, so $`s=u`. For $`k+1`, a path $`u\to^{k+1}s` consists of a first step $`u\to s_1` and a path $`s_1\to^k s`. Step 6 gives $`s_1=u`, so the second part is a path $`u\to^k s`. The induction hypothesis $`Q(k)` applied to it gives $`s=u`.
8. By 7, every term $`s` with $`u\to^*s` is $`u` itself, and $`u` is not a normal form by 5. So no normal form is reachable from $`u`, and $`u` diverges under call by value. A value is a normal form, so no value is reachable either. $`\square`

Step 6 is where determinacy is used. Step 5 alone shows only that one infinite path exists, the path $`f` with $`f(i)=u` for every $`i`. Without step 6 another path from $`u` might take a different first step and reach a value.

The difference comes from one rule. N-AppAbs does not inspect its operand, so call by name discards $`\Omega` in step 1. E-AppAbs requires a value operand, so call by value must first evaluate $`\Omega`, and $`\Omega` never becomes a value.

*What the theorem does not say.* It concerns one term. On the term of §23.1 both strategies reach the same value. Call by name can also diverge: $`\mathsf{id}\,\Omega` diverges under both strategies (Exercise 23.3). When both strategies reach a value, the values can be different terms (Exercise 23.2). When they reach the same value, the numbers of steps can differ (Exercise 23.1). Whether call by name reaches a value whenever call by value does is not proved here (Further Reading).

# Exercises
%%%
tag := "ch23-s4"
number := false
%%%

*23.1.* Evaluate $`(\lambda x.x\,x)\,(\mathsf{id}\,\mathsf{id})` under both strategies. Name the rule of each step and count the steps. At which step does call by name copy the operand?

*23.2.* Evaluate $`(\lambda x.\lambda y.x)\,(\mathsf{id}\,\mathsf{id})` under both strategies until a value is reached. Are the two values the same term?

*23.3.* Show that $`\mathsf{id}\,\Omega` diverges under both strategies. Then show that $`\lambda z.\Omega` diverges under neither. What kind of rule would have to exist for evaluation to reach the $`\Omega` in its body?

*Further problem.* Let $`t=(\lambda y.\lambda z.y)\,\Omega`. Trace $`t` and $`t\,\mathsf{id}` under both strategies. Which of the four evaluations reach a value?

# Reading for the Seminar
%%%
tag := "ch23-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the five rules of §23.1. Evaluate $`\mathsf{id}\,(\mathsf{id}\,(\lambda z.\mathsf{id}\,z))` under both strategies. Name the rule of each step and mark the redex that each first step contracts.

*Joint proof · 30 minutes.* Theorem 23.4. One person carries out steps 1–3, computing each substitution. Another builds the three-rule derivation of $`u\to u`. A third writes the induction property $`Q(k)` and completes steps 6–8, pointing to the use of Theorem 23.1.

*Proof review · 20 minutes.* Write the E-App1 case of Theorem 23.1 and find the sentence that uses “values have no step”. Then do Exercise 23.1, distinguishing a copy of an unevaluated operand from the reuse of a computed value.

*Facilitator’s hint.* When a term steps to itself, an infinite path exists. To exclude a different path that reaches a value, use determinacy.

# Solutions and Further Reading
%%%
tag := "ch23-s6"
number := false
%%%

*23.1.* Call by value takes three steps. First, $`(\lambda x.x\,x)\,(\mathsf{id}\,\mathsf{id})\to(\lambda x.x\,x)\,\mathsf{id}` by E-App2 over E-AppAbs. Then $`(\lambda x.x\,x)\,\mathsf{id}\to\mathsf{id}\,\mathsf{id}` by E-AppAbs, since $`[x\mapsto\mathsf{id}](x\,x)=\mathsf{id}\,\mathsf{id}`. Last, $`\mathsf{id}\,\mathsf{id}\to\mathsf{id}` by E-AppAbs. Call by name takes four steps. The first, by N-AppAbs, copies the operand: $`(\lambda x.x\,x)\,(\mathsf{id}\,\mathsf{id})\to_{\mathrm n}(\mathsf{id}\,\mathsf{id})\,(\mathsf{id}\,\mathsf{id})`. Then $`\to_{\mathrm n}\mathsf{id}\,(\mathsf{id}\,\mathsf{id})` by N-App1 over N-AppAbs, $`\to_{\mathrm n}\mathsf{id}\,\mathsf{id}` by N-AppAbs, and $`\to_{\mathrm n}\mathsf{id}` by N-AppAbs. The copy $`\mathsf{id}\,\mathsf{id}` is evaluated twice. Both strategies reach $`\mathsf{id}`.

*23.2.* Call by value: $`(\lambda x.\lambda y.x)\,(\mathsf{id}\,\mathsf{id})\to(\lambda x.\lambda y.x)\,\mathsf{id}` by E-App2 over E-AppAbs. Then E-AppAbs gives $`[x\mapsto\mathsf{id}](\lambda y.x)=\lambda y.\mathsf{id}`, since $`y\neq x` and $`y\notin\mathrm{FV}(\mathsf{id})`. Call by name: N-AppAbs gives $`[x\mapsto\mathsf{id}\,\mathsf{id}](\lambda y.x)=\lambda y.\mathsf{id}\,\mathsf{id}` in one step. Both results are values. They are different terms: the body of one is an abstraction, the body of the other an application. Neither strategy steps inside an abstraction, so the difference remains.

*23.3.* Under call by value, the operator $`\mathsf{id}` is a value and the operand $`\Omega` is not. E-App2 with premise $`\Omega\to\Omega` gives $`\mathsf{id}\,\Omega\to\mathsf{id}\,\Omega`. Steps 6–8 of Theorem 23.4, with $`\mathsf{id}\,\Omega` in place of $`u`, show that it diverges. Under call by name, N-AppAbs gives $`\mathsf{id}\,\Omega\to_{\mathrm n}[x\mapsto\Omega]x=\Omega`, and from there every step returns $`\Omega` by Proposition 23.2. So $`\mathsf{id}\,\Omega` diverges under call by name as well. The term $`\lambda z.\Omega` is a value, hence a normal form reached in zero steps, so it diverges under neither strategy. To reach the $`\Omega` in its body one would need a congruence rule that steps inside an abstraction, such as: from $`t\to t'` conclude $`\lambda x.t\to\lambda x.t'`. With that rule $`\lambda z.\Omega` would step to itself forever.

*Further problem.* Under call by name, N-AppAbs gives $`t\to_{\mathrm n}[y\mapsto\Omega](\lambda z.y)=\lambda z.\Omega`, a value. In $`t\,\mathsf{id}` the same step happens in the operator by N-App1, giving $`(\lambda z.\Omega)\,\mathsf{id}`. Then N-AppAbs gives $`[z\mapsto\mathsf{id}]\Omega=\Omega`, since $`z` does not occur in $`\Omega`. From there the evaluation diverges. Under call by value, $`t\to t` by E-App2 over E-AppAbs, and $`t\,\mathsf{id}\to t\,\mathsf{id}` by E-App1 over that step. By the argument of steps 6–8, both diverge. So only the call-by-name evaluation of $`t` reaches a value. Returning a function and returning the result of calling it are different observations, even though both programs contain $`t`.

*Further reading · Other strategies.* TAPL §5.1 also describes full beta-reduction, in which any redex may be contracted, and normal order, which contracts the leftmost, outermost redex and also steps inside abstractions. Under full beta-reduction the term of §23.1 has two different next terms, so that relation is not deterministic. TAPL §5.1 also names call by need, a variant of call by name that evaluates an operand at most once and reuses its value.

*Further reading · The cost of copying.* Let $`A_0=\mathsf{id}` and $`A_{k+1}=\mathsf{id}\,A_k`. Under either strategy $`A_k` reaches $`\mathsf{id}` in exactly $`k` steps (induction on $`k`). Now evaluate $`(\lambda x.x\,x)\,A_k`. Call by value takes $`k` steps to evaluate the operand, then two more: $`k+2` in all. Call by name copies $`A_k` in its first step, evaluates the first copy in $`k` steps, applies the resulting $`\mathsf{id}` in one step, and evaluates the second copy in $`k` steps: $`2k+2` in all. Exercise 23.1 is the case $`k=1`. Call by need would evaluate $`A_k` once, but it needs extra rules to store and reuse a value, so its steps are not counted by these rules.

*Further reading · Evaluation contexts.* A step can be found by marking the hole in which the next redex lies. For call by name the contexts are $`\mathcal E::=\square\mid\mathcal E\,t`. For call by value they are $`\mathcal E::=\square\mid\mathcal E\,t\mid v\,\mathcal E`, where the operator in the last form is already a value. Each form other than $`\square` corresponds to one congruence rule. A step writes the term as a context whose hole holds a redex that the strategy may contract, and contracts that redex in place. Determinacy then says that each term splits in at most one way into a context and such a redex.

*Further reading · Which strategy terminates more often.* If a closed term of C.1 reaches a value under call by value, it also reaches a value under call by name, though the values may differ (Exercise 23.2). So no closed term behaves as $`u` does with the two strategies exchanged. This follows from the standardization theorem of the lambda calculus. See G. D. Plotkin, “Call-by-name, call-by-value and the λ-calculus”, _Theoretical Computer Science_ 1 (1975). This book does not prove it. Part 3 returns to call by name: the language PCF of Session 35 evaluates by name.

*Confluence and normalization.* For a chosen reduction relation, *confluence* means that whenever a term reduces in finitely many steps to each of two terms, both can reduce further, in zero or more steps, to a common term. Determinacy asks only about the uniqueness of the immediate successor. Under full beta-reduction the two distinct successors in §23.1 can both reduce to $`\lambda z.z`. This joins that particular fork. The Church–Rosser theorem establishes confluence for every fork of full beta-reduction. [Kozen’s proof, §3](https://www.cs.cornell.edu/kozen/Papers/ChurchRosser.pdf).

A term is *weakly normalizing* for a relation if some finite path reaches a normal form, and *strongly normalizing* if every reduction path is finite. Under full beta-reduction the term $`u` of Theorem 23.4 can reach $`\mathsf{id}` by contracting the outer applications, or keep reducing $`\Omega` forever. It is weakly normalizing and fails strong normalization for that relation. Under call by value the outer application must wait for its operand, so this same term has no path to a normal form.

# Sources and Formalization
%%%
tag := "ch23-notes"
number := false
%%%

Pierce, _Types and Programming Languages_ (TAPL), §5.1 compares evaluation strategies, among them call by value and call by name, and describes call by name in prose. TAPL §5.3 gives the call-by-value rules of C.1. The term $`\Omega` and the word “diverge” are from TAPL §5.2. The statement and proof of Theorem 23.4 are this book’s, as is determinacy for these rules (Theorem 23.1, Proposition 23.2). Pierce proves determinacy of one-step evaluation for a language of Boolean terms. [Source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

* *Theorem 23.1.* Formulated in this book. Corresponds to TAPL §3.5. Paper proof only ([§23.2](chapter-23/index.html#ch23-s2)).
* *Proposition 23.2.* Formulated in this book. Corresponds to TAPL §3.5. Paper proof only ([§23.2](chapter-23/index.html#ch23-s2)).
* *Theorem 23.4.* Formulated in this book. Paper proof only ([§23.3](chapter-23/index.html#ch23-s3)).
