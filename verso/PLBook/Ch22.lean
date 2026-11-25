import VersoManual

open Verso.Genre Manual

#doc (Manual) "Binding and Capture-Avoiding Substitution" =>
%%%
tag := "ch22"
file := "chapter-22"
%%%

Take the abstraction $`\lambda y.x\,y`. The occurrence of $`y` refers to its parameter. The occurrence of $`x` is free: its meaning comes from outside the term. Replace $`x` by $`y` literally and the result is $`\lambda y.y\,y`. Now both occurrences refer to the parameter. The inserted $`y`, which named something outside, has been captured. Substitution that respects binding first renames the parameter and gives $`\lambda z.y\,z`. This session defines that substitution and proves the fact about it that later sessions use: which variables are free after a substitution.

*In this session.*

* *Definitions.* Untyped lambda terms, free variables $`\mathrm{FV}`, closed terms, alpha-equivalence and the substitution $`[x\mapsto s]t` ([Lambda language card C.1](lambda-card/index.html#lambda-c1)). Occurrences, binders and their scope ([Session 1, §1.3](chapter-01/index.html#ch01-s3)).
* *New terms.* Alpha-equivalence, capture, fresh variable, capture-avoiding substitution, size of a term. [Glossary](glossary/index.html)
* *Theorem 22.3 (Free variables after substitution).* For all terms $`t,s` and every variable $`x`, if $`x\in\mathrm{FV}(t)` then $`\mathrm{FV}([x\mapsto s]t)=(\mathrm{FV}(t)\setminus\{x\})\cup\mathrm{FV}(s)`.
* *Board case.* Abstraction with renaming: $`t=\lambda y.t_1` with $`y\in\mathrm{FV}(s)`. Rename $`y` to a fresh $`z`. Lemma 22.1 shows that the renamed body has the size of $`t_1` and the same free variables apart from $`y` and $`z`. Apply the induction hypothesis to the renamed body.
* *Proof outline.* Fix $`x` and $`s`. Prove $`P(t)\coloneqq x\in\mathrm{FV}(t)\Rightarrow\mathrm{FV}([x\mapsto s]t)=(\mathrm{FV}(t)\setminus\{x\})\cup\mathrm{FV}(s)` by induction on the size of $`t`. Variable: $`t=x`. Application: the induction hypothesis for each part that contains $`x`, and Lemma 22.2 for a part that does not. Abstraction $`\lambda y.t_1`: here $`y\neq x`. If $`y\notin\mathrm{FV}(s)`, apply the hypothesis to $`t_1`. Otherwise apply it to the renamed body, which is not a subterm but has the same size as $`t_1`.
* *From Session 21.* Part 1 ends there. Its tools carry over: inference rules and derivations ([A.3](imp-card/index.html#imp-a3)), structural recursion and structural induction (Session 1), and induction on a measure, such as the height of a derivation ([Session 3, §3.1](chapter-03/index.html#ch03-s1)). What is new is binding. IMP expressions have no binders, so substitution into them ([Session 11, Definition 11.1](chapter-11/index.html#ch11-s1)) never renames anything. An abstraction binds its parameter, and substitution must sometimes rename it. In Part 2 the letters $`s,t,u` denote terms, and $`\sigma` denotes a type substitution, not a state.

# Binders and alpha-equivalence
%%%
tag := "ch22-s1"
%%%

The terms of [C.1](lambda-card/index.html#lambda-c1) are variables, abstractions $`\lambda x.t` and applications $`t_1\,t_2`. Besides $`x,y,z`, the letters $`w,a,b` also denote variables. Variables are drawn from an infinite set. An abstraction is a binder in the sense of [Session 1, §1.3](chapter-01/index.html#ch01-s3): it binds its parameter, and its scope is its body.

In $`\lambda y.x\,y` the occurrence of $`y` lies in the body of an abstraction with parameter $`y`, so it is bound. The occurrence of $`x` is free. The equations of C.1 give $`\mathrm{FV}(\lambda y.x\,y)=\{x,y\}\setminus\{y\}=\{x\}`. When nested abstractions have the same parameter, an occurrence belongs to the nearest one. In $`\lambda x.(\lambda x.x)\,y` the occurrence of $`x` belongs to the inner abstraction, the outer abstraction binds no occurrence, and the free variables are $`\{y\}`.

Binding can be read off the syntax tree. From a variable leaf, follow the path towards the root until the first abstraction whose parameter is that variable. If there is one, it binds the occurrence. If the path reaches the root first, the occurrence is free. In $`(\lambda x.x)\,x` the left leaf meets $`\lambda x` on its path. The path of the right leaf passes only the application node. The abstraction in the operator does not bind the operand, because its scope is its own body. So $`\mathrm{FV}((\lambda x.x)\,x)=\{x\}`. In general, $`\mathrm{FV}(t)` is the set of variables with at least one free occurrence in $`t`. A structural induction on $`t` checks this against the equations of C.1.

The name of a parameter does not matter, only which occurrences it binds. C.1 makes this precise. Rename the parameter of one abstraction $`\lambda y.t_1` inside a term, together with the free occurrences of $`y` in $`t_1`, to a variable that occurs nowhere in $`t_1`. Terms related by a finite sequence of such renamings and their reverses are *alpha-equivalent*. Thus $`\lambda x.\lambda y.x` and $`\lambda a.\lambda b.a` are alpha-equivalent, and $`\lambda a.\lambda b.b` is not alpha-equivalent to them. The new variable must occur nowhere in the body. Renaming $`y` to $`x` in $`\lambda y.x\,y` would give $`\lambda x.x\,x`, in which the first occurrence is no longer free. C.1 identifies alpha-equivalent terms, so from now on $`t=t'` means that $`t` and $`t'` are alpha-equivalent.

*Definition 22.1 (Fresh variable).* A variable is *fresh* for some terms and variables if it occurs nowhere in the terms, neither as an occurrence nor as a parameter, and differs from the given variables. Terms are finite and the set of variables is infinite, so for every finite list of terms and variables a fresh variable exists.

*Definition 22.2 (Size).* The *size* of a term is the number of nodes of its syntax tree:

$$`\mathrm{size}(x)=1\qquad\mathrm{size}(\lambda x.t_1)=1+\mathrm{size}(t_1)\qquad\mathrm{size}(t_1\,t_2)=1+\mathrm{size}(t_1)+\mathrm{size}(t_2)`

For example, $`\mathrm{size}(\lambda y.x\,y)=4`. Renaming $`y` to $`z` in this term gives $`\lambda z.x\,z`. The renamed body $`x\,z` has size 3, like $`x\,y`, and $`\mathrm{FV}(x\,z)\setminus\{z\}=\{x\}=\mathrm{FV}(x\,y)\setminus\{y\}`.

*Lemma 22.1 (Renaming).* Let $`t_1` be a term, let $`y` be a variable, and let $`z\neq y` be a variable that occurs nowhere in $`t_1`. Let $`t_1'` be $`t_1` with every free occurrence of $`y` replaced by $`z`. Then

$$`\mathrm{size}(t_1')=\mathrm{size}(t_1)\qquad\text{and}\qquad\mathrm{FV}(t_1')\setminus\{z\}=\mathrm{FV}(t_1)\setminus\{y\}.`

In particular, $`\lambda z.t_1'` and $`\lambda y.t_1` have the same size and the same free variables.

*Proof.* The replacement turns some variable leaves into variable leaves and leaves every other node in place. So the number of nodes is unchanged. Each leaf of $`t_1'` also has the same path to the root, with the same abstractions on it, as the corresponding leaf of $`t_1`. Take a variable $`w` other than $`y` and $`z`. Its occurrences in $`t_1` and in $`t_1'` are the same leaves with the same paths, so $`w\in\mathrm{FV}(t_1')` exactly when $`w\in\mathrm{FV}(t_1)`. The variable $`y` is not free in $`t_1'`: its free occurrences were replaced, and its other occurrences are still bound. The variable $`z` is not free in $`t_1`, because it does not occur there. So neither side of the equation contains $`y` or $`z`, and the two sides agree at every other variable. Finally, $`\mathrm{FV}(\lambda z.t_1')=\mathrm{FV}(t_1')\setminus\{z\}=\mathrm{FV}(t_1)\setminus\{y\}=\mathrm{FV}(\lambda y.t_1)`, and both abstractions have size $`1+\mathrm{size}(t_1)`. $`\square`

A renaming inside a larger term replaces one abstraction by another with the same size and the same free variables. The equations for size and for $`\mathrm{FV}` compute a term from its immediate parts. So a structural induction on the surrounding term shows that its size and its free variables do not change either. Hence alpha-equivalent terms have the same size and the same free variables, and both functions are well defined on terms identified up to alpha-equivalence.

# Capture-avoiding substitution
%%%
tag := "ch22-s2"
%%%

[Session 11, Definition 11.1](chapter-11/index.html#ch11-s1) wrote $`a[e/x]` for substitution into an IMP expression. Part 2 follows TAPL and writes $`[x\mapsto s]t` for the term obtained from $`t` by replacing the free occurrences of $`x` by $`s`. With binders, literal replacement can go wrong. Replace $`x` by $`y` in $`\lambda y.x\,y`, and the result $`\lambda y.y\,y` binds the inserted $`y`. The original term applies the outside $`x` to its argument. The result applies its argument to itself. A substitution $`[x\mapsto s]t` *captures* a variable when a free occurrence of that variable in $`s` becomes bound in the result by an abstraction of $`t`.

C.1 defines substitution so that it never captures:

$$`\begin{aligned}
[x\mapsto s]x&=s\\
[x\mapsto s]y&=y&&\text{if }y\neq x\\
[x\mapsto s](\lambda y.t_1)&=\lambda y.\,[x\mapsto s]t_1&&\text{if }y\neq x\text{ and }y\notin\mathrm{FV}(s)\\
[x\mapsto s](t_1\,t_2)&=([x\mapsto s]t_1)\,([x\mapsto s]t_2)
\end{aligned}`

When $`y=x` or $`y\in\mathrm{FV}(s)`, the third equation does not apply as it stands, and C.1 renames first. Choose $`z` fresh for $`s`, $`t_1` and $`x`. Replace $`\lambda y.t_1` by the alpha-equivalent term $`\lambda z.t_1'`, where the renamed body $`t_1'` is $`t_1` with its free occurrences of $`y` replaced by $`z`. The third equation then applies:

$$`[x\mapsto s](\lambda y.t_1)=\lambda z.\,[x\mapsto s]t_1'.`

These equations, with this renaming, define *capture-avoiding substitution*. In the opening example $`y\in\mathrm{FV}(y)`, so the parameter is renamed. Take $`z` fresh. Then $`\lambda y.x\,y=\lambda z.x\,z`, and

$$`[x\mapsto y](\lambda z.x\,z)=\lambda z.([x\mapsto y]x)\,([x\mapsto y]z)=\lambda z.y\,z.`

The inserted $`y` stays free, and $`z` still refers to the parameter. When $`y=x`, the abstraction binds every occurrence of $`x` in its body, so nothing is replaced. C.1 records $`[x\mapsto s](\lambda x.t_1)=\lambda x.t_1`, and Lemma 22.2 below proves it.

The renamed body $`t_1'` is not a subterm of $`\lambda y.t_1`, so this definition is not a structural recursion on $`t`. By Lemma 22.1, however, $`\mathrm{size}(t_1')=\mathrm{size}(t_1)<\mathrm{size}(\lambda y.t_1)`. Every recursive use of the equations is on a term of smaller size, so the computation ends. Different choices of the fresh $`z` give alpha-equivalent results. This book takes that fact from the convention of C.1 and does not prove it.

Substitution replaces all the free occurrences at once and does not look inside the inserted term. For example, $`[x\mapsto x\,y](x\,x)=(x\,y)\,(x\,y)`. The first equation returns $`s` as it is. It does not search $`s` for further occurrences of $`x`.

A longer example has two different abstractions. Let $`t=\lambda y.x\,(\lambda x.y)` and $`s=y`. Since $`y\in\mathrm{FV}(s)`, rename the outer parameter to a fresh $`w`. The occurrence of $`y` under $`\lambda x` is free in the body $`x\,(\lambda x.y)`, because that abstraction binds $`x`, not $`y`. So it is renamed too, and the renamed body is $`x\,(\lambda x.w)`. The inner abstraction binds $`x`, so $`[x\mapsto y](\lambda x.w)=\lambda x.w`, and

$$`[x\mapsto y](\lambda w.x\,(\lambda x.w))=\lambda w.y\,(\lambda x.w).`

Renaming only the parameter, to $`\lambda w.x\,(\lambda x.y)`, would be an error. The last $`y` would become free, and substitution would give $`\lambda w.y\,(\lambda x.y)`, whose last $`y` no longer refers to the parameter.

# Free variables after substitution
%%%
tag := "ch22-s3"
%%%

Compare the free variables before and after the opening substitution: $`\mathrm{FV}(\lambda y.x\,y)=\{x\}`, $`\mathrm{FV}(y)=\{y\}` and $`\mathrm{FV}(\lambda z.y\,z)=\{y\}`. The variable $`x` has gone, and the free variables of the inserted term have come in: $`\{y\}=(\{x\}\setminus\{x\})\cup\{y\}`. The longer example of §22.2 gives $`\mathrm{FV}(\lambda w.y\,(\lambda x.w))=\{y\}=(\{x\}\setminus\{x\})\cup\{y\}` in the same way. If $`x` is not free in $`t`, nothing comes in. For example, $`[x\mapsto y](\lambda x.x)=\lambda x.x` has no free variable, although $`\mathrm{FV}(y)=\{y\}`. The two situations give two statements.

*Lemma 22.2 (Absent variable).* For all terms $`t,s` and every variable $`x`, if $`x\notin\mathrm{FV}(t)` then $`[x\mapsto s]t=t`.

*Proof.* Fix $`x` and $`s`. We prove $`Q(t)\coloneqq x\notin\mathrm{FV}(t)\Rightarrow[x\mapsto s]t=t` by induction on $`\mathrm{size}(t)`, assuming $`Q(t')` for every term $`t'` with $`\mathrm{size}(t')<\mathrm{size}(t)`. Suppose $`x\notin\mathrm{FV}(t)`. If $`t` is a variable, it is not $`x`, and the second equation gives $`t`. If $`t=t_1\,t_2`, then $`x` is free in neither part, and $`Q(t_1)`, $`Q(t_2)` and the fourth equation give $`t_1\,t_2`. Let $`t=\lambda y.t_1`. If $`y\neq x` and $`y\notin\mathrm{FV}(s)`, then $`x\notin\mathrm{FV}(t_1)\setminus\{y\}` and $`x\neq y` give $`x\notin\mathrm{FV}(t_1)`, and the third equation with $`Q(t_1)` gives $`\lambda y.t_1`. Otherwise $`y=x` or $`y\in\mathrm{FV}(s)`, and substitution renames $`y` to a variable $`z` fresh for $`s`, $`t_1` and $`x`. Then $`z\neq y`, so Lemma 22.1 applies. By Lemma 22.1, $`\mathrm{FV}(t_1')\setminus\{z\}=\mathrm{FV}(t_1)\setminus\{y\}=\mathrm{FV}(t)`, which does not contain $`x`. Since $`z\neq x`, also $`x\notin\mathrm{FV}(t_1')`. Lemma 22.1 also gives $`\mathrm{size}(t_1')<\mathrm{size}(t)`. So $`Q(t_1')` gives $`[x\mapsto s](\lambda y.t_1)=\lambda z.t_1'`, which is alpha-equivalent to $`\lambda y.t_1`. $`\square`

*Theorem 22.3 (Free variables after substitution).* For all terms $`t,s` and every variable $`x`, if $`x\in\mathrm{FV}(t)` then

$$`\mathrm{FV}([x\mapsto s]t)=(\mathrm{FV}(t)\setminus\{x\})\cup\mathrm{FV}(s).`

Fix $`x` and $`s`. We prove $`P(t)` for every term $`t` by induction on $`\mathrm{size}(t)`, where

$$`P(t)\coloneqq x\in\mathrm{FV}(t)\Rightarrow\mathrm{FV}([x\mapsto s]t)=(\mathrm{FV}(t)\setminus\{x\})\cup\mathrm{FV}(s).`

The induction hypothesis (IH) for $`t` is

$$`P(t')\quad\text{for every term }t'\text{ with }\mathrm{size}(t')<\mathrm{size}(t).`

This is the principle of [Session 3, §3.1](chapter-03/index.html#ch03-s1) with size in place of height. We need it because the board case applies the hypothesis to a renamed body, which is not a subterm of $`t`. Unlike Session 3, nothing is quantified inside $`P`: every use of the hypothesis has the same $`x` and $`s`. Assume $`x\in\mathrm{FV}(t)`.

*Variable.* If $`t` is a variable $`y`, then $`x\in\{y\}` gives $`y=x`. The first equation gives $`[x\mapsto s]x=s`, and $`\mathrm{FV}(s)=(\{x\}\setminus\{x\})\cup\mathrm{FV}(s)`.

*Application.* Let $`t=t_1\,t_2`, so $`[x\mapsto s]t=([x\mapsto s]t_1)\,([x\mapsto s]t_2)`. For each part $`t_i` with $`x\in\mathrm{FV}(t_i)`, the IH for $`t_i` gives $`\mathrm{FV}([x\mapsto s]t_i)=(\mathrm{FV}(t_i)\setminus\{x\})\cup\mathrm{FV}(s)`. For each part with $`x\notin\mathrm{FV}(t_i)`, Lemma 22.2 gives $`[x\mapsto s]t_i=t_i`, so $`\mathrm{FV}([x\mapsto s]t_i)=\mathrm{FV}(t_i)\setminus\{x\}`. At least one part contains $`x`. So the union of the two sets is $`(\mathrm{FV}(t_1)\setminus\{x\})\cup(\mathrm{FV}(t_2)\setminus\{x\})\cup\mathrm{FV}(s)=(\mathrm{FV}(t)\setminus\{x\})\cup\mathrm{FV}(s)`.

*Abstraction without renaming.* Let $`t=\lambda y.t_1`. From $`x\in\mathrm{FV}(t_1)\setminus\{y\}` we get $`y\neq x` and $`x\in\mathrm{FV}(t_1)`. So renaming happens exactly when $`y\in\mathrm{FV}(s)`. Suppose $`y\notin\mathrm{FV}(s)`. The third equation, the IH for $`t_1`, and $`y\notin\mathrm{FV}(s)` give

$$`\begin{aligned}
\mathrm{FV}([x\mapsto s]t)&=\mathrm{FV}([x\mapsto s]t_1)\setminus\{y\}\\
&=((\mathrm{FV}(t_1)\setminus\{x\})\cup\mathrm{FV}(s))\setminus\{y\}\\
&=((\mathrm{FV}(t_1)\setminus\{y\})\setminus\{x\})\cup\mathrm{FV}(s).
\end{aligned}`

The right side is $`(\mathrm{FV}(t)\setminus\{x\})\cup\mathrm{FV}(s)`.

*Abstraction with renaming (board case).* Suppose $`t=\lambda y.t_1` and $`y\in\mathrm{FV}(s)`. As in the previous case, $`y\neq x` and $`x\in\mathrm{FV}(t_1)`. On the opening example, $`t_1=x\,y`, $`s=y` and the renamed body is $`x\,z`. Step 3 below reads $`\{x\}=\{x\}`, step 5 reads $`\mathrm{FV}(y\,z)=\{y,z\}=(\{x,z\}\setminus\{x\})\cup\{y\}`, and step 7 gives $`\{y\}`.

1. We must show $`\mathrm{FV}([x\mapsto s](\lambda y.t_1))=(\mathrm{FV}(\lambda y.t_1)\setminus\{x\})\cup\mathrm{FV}(s)`.
2. Choose $`z` fresh for $`s`, $`t_1` and $`x`. Let $`t_1'` be $`t_1` with its free occurrences of $`y` replaced by $`z`. Since $`y\in\mathrm{FV}(s)` and $`z` does not occur in $`s`, $`z\neq y`. C.1 gives $`[x\mapsto s](\lambda y.t_1)=\lambda z.[x\mapsto s]t_1'`, so the left side of step 1 is $`\mathrm{FV}([x\mapsto s]t_1')\setminus\{z\}`.
3. Apply Lemma 22.1 to $`t_1`, $`y` and $`z`. It gives $`\mathrm{size}(t_1')=\mathrm{size}(t_1)` and $`\mathrm{FV}(t_1')\setminus\{z\}=\mathrm{FV}(t_1)\setminus\{y\}`.
4. We have $`x\in\mathrm{FV}(t_1)\setminus\{y\}`, which equals $`\mathrm{FV}(t_1')\setminus\{z\}` by step 3. So $`x\in\mathrm{FV}(t_1')`.
5. By step 3, $`\mathrm{size}(t_1')=\mathrm{size}(t_1)<\mathrm{size}(t)`. Apply the IH to $`t_1'`. With step 4 it gives $`\mathrm{FV}([x\mapsto s]t_1')=(\mathrm{FV}(t_1')\setminus\{x\})\cup\mathrm{FV}(s)`.
6. Remove $`z` from both sides of step 5. Removing $`z` from a union removes it from each part, and the removals of $`x` and $`z` can be done in either order. Since $`z\notin\mathrm{FV}(s)`, removing $`z` does not change $`\mathrm{FV}(s)`. So $`\mathrm{FV}([x\mapsto s]t_1')\setminus\{z\}=((\mathrm{FV}(t_1')\setminus\{z\})\setminus\{x\})\cup\mathrm{FV}(s)`.
7. By step 3, the right side of step 6 is $`((\mathrm{FV}(t_1)\setminus\{y\})\setminus\{x\})\cup\mathrm{FV}(s)=(\mathrm{FV}(\lambda y.t_1)\setminus\{x\})\cup\mathrm{FV}(s)`. By step 2, the left side of step 6 is the left side of step 1. This proves step 1.

Each condition on $`z` is used. The conditions $`z\neq x` and $`z\notin\mathrm{FV}(s)` make the third equation applicable in step 2, and $`z\notin\mathrm{FV}(s)` is used again in step 6. That $`z` occurs nowhere in $`t_1` is the hypothesis of Lemma 22.1 in step 3. This completes the induction, and $`P(t)` for every $`t` is Theorem 22.3. $`\square`

*Corollary 22.4 (Closed terms).* For all terms $`t,s` and every variable $`x`, $`\mathrm{FV}([x\mapsto s]t)\subseteq(\mathrm{FV}(t)\setminus\{x\})\cup\mathrm{FV}(s)`. In particular, if $`\lambda x.t` and $`s` are closed, then $`[x\mapsto s]t` is closed.

*Proof.* If $`x\in\mathrm{FV}(t)`, Theorem 22.3 gives equality. Otherwise Lemma 22.2 gives $`\mathrm{FV}([x\mapsto s]t)=\mathrm{FV}(t)=\mathrm{FV}(t)\setminus\{x\}`. For the second claim, $`\mathrm{FV}(t)\setminus\{x\}=\mathrm{FV}(\lambda x.t)=\varnothing` and $`\mathrm{FV}(s)=\varnothing`. $`\square`

The corollary applies to the rule E-AppAbs of C.1, used from Session 23 on, which takes $`(\lambda x.t_{12})\,v_2` to $`[x\mapsto v_2]t_{12}`. If $`(\lambda x.t_{12})\,v_2` is closed, so are $`\lambda x.t_{12}` and $`v_2`, and the step gives a closed term. Theorem 22.3 speaks only about the set of free variables. It does not say that each occurrence is bound by the right abstraction. The faulty renaming at the end of §22.2 produces the right set $`\{y\}` and the wrong term.

# Exercises
%%%
tag := "ch22-s4"
number := false
%%%

*22.1.* Compute $`[x\mapsto y](\lambda y.(\lambda y.y)\,x)` and mark the free occurrences in the result. Check the result against Theorem 22.3. The outer parameter has no free occurrence in its body. Why must it still be renamed?

*22.2.* Give a term with two occurrences of $`x` such that $`[x\mapsto s]` replaces only one of them, for every $`s`.

*22.3.* Would the equation of Theorem 22.3 hold for all $`t` if the hypothesis $`x\in\mathrm{FV}(t)` were dropped? Give a counterexample, and identify the cases of the proof that use the hypothesis.

*22.4.* Let $`t=\lambda y.x\,y` and $`s=y\,z`. Suppose step 2 of the board case chose $`z` as the new parameter, although $`z\in\mathrm{FV}(s)`. Compute the result, compare its free variables with Theorem 22.3, and name the steps of the board case that use $`z\notin\mathrm{FV}(s)`.

*22.5.* Which of $`\lambda a.\lambda b.a\,b`, $`\lambda b.\lambda a.b\,a` and $`\lambda a.\lambda b.b\,a` are alpha-equivalent? Give the renamings, or explain why none exist.

*Further problem.* Let $`p=\lambda z.(x\,z)\,y`, with $`x,y,z` distinct. Compute $`[y\mapsto z]([x\mapsto y]p)` and $`[x\mapsto y]([y\mapsto z]p)`. List the free variables after each substitution and decide whether the two final terms are alpha-equivalent.

# Reading for the Seminar
%%%
tag := "ch22-s5"
number := false
%%%

*Definitions · 10 minutes.* Draw the syntax tree of $`\lambda y.x\,(\lambda x.y)`. Draw a line from each bound occurrence to its abstraction. Compute its free variables by the equations of C.1 and by the paths, and compare.

*Joint proof · 30 minutes.* One person replaces $`x` by $`y` in $`\lambda y.x\,y` literally. Another applies C.1. Compare the free variables of the two results. Then prove the board case, steps 1–7, first on this example and then in general. Say which hypothesis each step uses.

*Proof review · 20 minutes.* Redo the board case with the bad choice of Exercise 22.4 and find the steps that fail. Work Exercise 22.1 with two different fresh variables and check that the results are alpha-equivalent.

*Facilitator’s hint.* Draw the binding lines before changing any name. A line cannot cross a nearer abstraction with the same parameter. After a renaming, every line must end at the same abstraction as before.

# Solutions and Further Reading
%%%
tag := "ch22-s6"
number := false
%%%

*22.1.* The result is $`\lambda z.(\lambda y.y)\,y`. Since $`y\in\mathrm{FV}(y)`, the outer parameter is renamed to a fresh $`z`. The body $`(\lambda y.y)\,x` has no free $`y`, so the renamed body is the same term. Substitution then gives $`\lambda z.([x\mapsto y](\lambda y.y))\,y`, and Lemma 22.2 gives $`[x\mapsto y](\lambda y.y)=\lambda y.y`. The last $`y` is the only free occurrence, and $`\{y\}=(\{x\}\setminus\{x\})\cup\{y\}`. Without renaming, the result would be $`\lambda y.(\lambda y.y)\,y`. The outer abstraction would capture the inserted $`y`, and the term would be closed.

*22.2.* Take $`x\,(\lambda x.x)`. Then $`[x\mapsto s](x\,(\lambda x.x))=s\,(\lambda x.x)`. The inner abstraction binds its own occurrence of $`x`.

*22.3.* No. Take distinct $`x,y,z`, $`t=z` and $`s=y`. Then $`[x\mapsto y]z=z` has free variables $`\{z\}`, while the right side is $`\{z\}\cup\{y\}`. The variable case uses the hypothesis: $`x\in\mathrm{FV}(y)` forces $`y=x`. The application case also uses it, to know that at least one part contributes $`\mathrm{FV}(s)`, and both abstraction cases use it to obtain $`y\neq x` and $`x\in\mathrm{FV}(t_1)`.

*22.4.* Renaming $`y` to $`z` gives $`\lambda z.x\,z`, and the third equation without its side condition gives $`\lambda z.(y\,z)\,z`. Its free variables are $`\{y\}`. Theorem 22.3 predicts $`(\{x\}\setminus\{x\})\cup\{y,z\}=\{y,z\}`. The $`z` of $`s` has been captured. Steps 2 and 6 use $`z\notin\mathrm{FV}(s)`. In step 2 the third equation does not apply. In step 6, removing $`z` changes $`\mathrm{FV}(s)` from $`\{y,z\}` to $`\{y\}`, and this is exactly the lost variable. A fresh $`w` gives the correct $`\lambda w.(y\,z)\,w`.

*22.5.* The first two are alpha-equivalent. Rename $`a` to a fresh $`c`, then $`b` to $`a`, then $`c` to $`b`: $`\lambda a.\lambda b.a\,b`, $`\lambda c.\lambda b.c\,b`, $`\lambda c.\lambda a.c\,a`, $`\lambda b.\lambda a.b\,a`. Each new variable occurs nowhere in the body being renamed. In the third term the operator refers to the inner abstraction, while in the first two it refers to the outer one. Renamings keep every binding line, so the third term is not alpha-equivalent to them. All three terms are closed, so their free variables cannot tell them apart.

*Further problem.* First order. $`[x\mapsto y]p=\lambda z.(y\,z)\,y`, since $`z\neq x` and $`z\notin\mathrm{FV}(y)`. Its free variables are $`\{y\}`. In $`[y\mapsto z](\lambda z.(y\,z)\,y)` the parameter $`z` is free in the inserted term, so rename it to a fresh $`w`. The result is $`\lambda w.(z\,w)\,z`, with free variables $`\{z\}`. Second order. In $`[y\mapsto z]p` the parameter $`z` is again renamed to $`w`. The result is $`\lambda w.(x\,w)\,z`, with free variables $`\{x,z\}`. Then $`[x\mapsto y]` gives $`\lambda w.(y\,w)\,z`, with free variables $`\{y,z\}`. Alpha-equivalent terms have the same free variables (Lemma 22.1), so the two final terms are not alpha-equivalent. Each intermediate set agrees with Theorem 22.3. In the first order, the $`y` inserted by the first substitution is a target of the second. In the second order, the substitution for $`y` runs before the substitution for $`x` inserts the new $`y`.

*Further reading · Order of substitutions.* Two substitutions in sequence depend on their order even without binders. For distinct $`x,y,z`, $`[y\mapsto z]([x\mapsto y]x)=z`, whereas $`[x\mapsto y]([y\mapsto z]x)=y`. With binders there are two concerns. A later substitution may act on material inserted by an earlier one. Each abstraction on the way must not capture that material, and renaming handles this concern. The Further problem shows both.

*Further reading · Testing alpha-equivalence.* Traverse two syntax trees in parallel. The constructors must match. Each bound occurrence must refer to the corresponding abstraction on its path, and the free occurrences must have the same names. Exercise 22.5 applies this test. A nameless representation, in which each bound occurrence records how many abstractions lie between it and its own abstraction, makes alpha-equivalent terms identical. Substitution then never renames, and the question of which fresh variable to choose disappears. Pierce develops it in TAPL, chapter 6.

*Further reading · Sources.* TAPL §5.3 defines the terms, free variables and substitution of C.1, and states the convention on alpha-equivalent terms. Reynolds, _Theories of Programming Languages_, §1.4, meets the same issue under the quantifiers of predicate logic. [Session 11, further reading](chapter-11/index.html#ch11-s7) gives an example of it. [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf) [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Sources and Formalization
%%%
tag := "ch22-notes"
number := false
%%%

Terms, free variables and capture-avoiding substitution are those of Pierce, _Types and Programming Languages_ (TAPL), §5.3, as recorded in C.1. TAPL treats alpha-equivalent terms as interchangeable by convention. [Source sections](lambda-card/index.html#lambda-sources)

* *Lemma 22.1.* Formulated in this book. Paper proof only ([§22.1](chapter-22/index.html#ch22-s1)).
* *Lemma 22.2.* Formulated in this book. Paper proof only ([§22.3](chapter-22/index.html#ch22-s3)).
* *Theorem 22.3.* Formulated in this book. Paper proof only ([§22.3](chapter-22/index.html#ch22-s3)).
* *Corollary 22.4.* Formulated in this book. Paper proof only ([§22.3](chapter-22/index.html#ch22-s3)).
