import VersoManual
import PLBook.IMP.Denotation

open Verso.Genre Manual

#doc (Manual) "State Transformers and the Information Order" =>
%%%
tag := "ch08"
file := "chapter-08"
%%%

* *Definitions.* Stores and update ([A.2](imp-card/index.html#imp-a2)), expression evaluation ([A.3](imp-card/index.html#imp-a3)), commands and guard values ([A.4](imp-card/index.html#imp-a4)), the branch selected by a guard ([A.5](imp-card/index.html#imp-a5)), partial functions and their graphs ([Session 3, §3.3](chapter-03/index.html#ch03-s3)). This session adds Definitions 8.1–8.4, 8.7 and 8.9.
* *New terms.* Bottom, state transformer, strict extension, information order, least upper bound. [Glossary and label key](glossary/index.html)
* *Theorem 8.5 (Associativity of sequencing).* For all state transformers $`f,g,h`, $`h^{\dagger}\circ(g^{\dagger}\circ f)=(h^{\dagger}\circ g)^{\dagger}\circ f`. Running $`f`, then $`g`, then $`h` gives the same state transformer under either grouping.
* *Source.* The outcomes, strict extension, command meanings and information order follow John C. Reynolds, _Theories of Programming Languages_, §§2.2–2.3. Here they are applied to the commands of [A.4](imp-card/index.html#imp-a4). [Reynolds, contents](https://www.cs.cmu.edu/~jcr/tpl-toc.html)
* *Board case.* Theorem 8.5 at one store $`s`, in both cases of the first state transformer: it does not terminate ($`f(s)=\bot`), and it terminates in an intermediate store ($`f(s)=m`).
* *Proof outline.* Two state transformers are equal when they agree at every store. Fix $`s` and split on the outcome $`f(s)`. In each case apply the two equations of strict extension until both sides become the same expression. No induction is needed.
* *From Session 7.* Session 7 compared two commands through their terminating executions, one pair of stores at a time. Here each command without loops receives a single state transformer, and a claim about all executions of two commands becomes an equation between two functions.

The command `x := x + 1` produces a final store from every initial store. The command `while 0 < x do skip` returns its initial store when $`s(x)\le0` and has no terminating execution when $`s(x)>0`. We want a meaning for each command that is one function on stores, and we want the meaning of `c; d` to be computed from the meanings of `c` and `d`. Two questions follow. What does the function return when there is no final store? What does the second command do when the first returns nothing?

# Outcomes and state transformers
%%%
tag := "ch08-s1"
%%%

Let $`W` be `while 0 < x do skip`. By [A.4](imp-card/index.html#imp-a4) its guard abbreviates $`\neg(x\le0)`, so it is true exactly when $`s(x)>0`. If $`s(x)\le0`, the loop exit rule of [A.5](imp-card/index.html#imp-a5) gives $`s\vdash W\Downarrow s`. If $`s(x)>0`, there is no final store. The least-height argument of [Session 2, §2.4](chapter-02/index.html#ch02-s4) applies unchanged, because the body skip returns the same store and the guard stays true. By [Session 3, §3.3](chapter-03/index.html#ch03-s3), the executions of $`W` form the graph of a partial function on stores, defined exactly at the stores with $`s(x)\le0`.

*Definition 8.1 (Outcomes).* Let $`\bot`, read *bottom*, be an element that is not a store. Put $`\Sigma_{\bot}=\Sigma\cup\{\bot\}`. An *outcome* is an element of $`\Sigma_{\bot}`: either a store or $`\bot`. As the result of a command, $`\bot` records that there is no final store, that is, nontermination.

*Definition 8.2 (State transformer).* A *state transformer* is a total function $`f:\Sigma\to\Sigma_{\bot}`. Two state transformers $`f,g` are equal when $`f(s)=g(s)` for every store $`s`.

For $`W` above, define the state transformer $`\ell` by $`\ell(s)=s` if $`s(x)\le0` and $`\ell(s)=\bot` if $`s(x)>0`. Session 9 gives $`W` exactly this meaning. A partial function on stores and a state transformer carry the same information: the partial function is undefined at $`s` exactly when the state transformer returns $`\bot` at $`s`. The difference is that a state transformer returns a value at every store. We can pass that value to another function and split on it by cases.

# Meanings of commands
%%%
tag := "ch08-s2"
%%%

Suppose a command $`c` is followed by `y := 7`, and write $`f_c` for the state transformer of $`c` (Definition 8.4 below). If $`f_c(s)` is a store $`m`, the sequence should return $`m[y\mapsto7]`. If $`f_c(s)=\bot`, no store ever reaches the assignment, and the sequence should return $`\bot`. Ordinary function application cannot express this. The state transformer of `y := 7` accepts only stores, and $`\bot` is not a store.

*Definition 8.3 (Strict extension and sequencing).* For a state transformer $`g`, its *strict extension* $`g^{\dagger}:\Sigma_{\bot}\to\Sigma_{\bot}` is given by two equations:

$$`g^{\dagger}(\bot)=\bot,\qquad g^{\dagger}(t)=g(t)\quad\text{for every store }t.`

The word *strict* means that $`\bot` is sent to $`\bot`. The *sequencing* of $`f` followed by $`g` is the state transformer $`g^{\dagger}\circ f`. Here $`\circ` is ordinary function composition, $`(g^{\dagger}\circ f)(s)=g^{\dagger}(f(s))`. The state transformer that runs first is written on the right.

*Definition 8.4 (Meaning of a command).* For each command $`c` without loops, define its meaning $`f_c:\Sigma\to\Sigma_{\bot}` by structural recursion on $`c`. For $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`, let $`k` be the branch selected by $`B(b,s)` as in [A.5](imp-card/index.html#imp-a5).

$$`\begin{aligned}
f_{\mathsf{skip}}(s)&=s & f_{x:=e}(s)&=s[x\mapsto\mathrm{eval}(e,s)]\\
f_{c;d}&=f_d^{\dagger}\circ f_c & f_I(s)&=f_k(s)
\end{aligned}`

Each clause uses only the meanings of the immediate parts. Session 9 adds the clause for loops. The four clauses above stay as they are.

For example, take `x := 1; y := x + 3` from [Session 2, §2.3](chapter-02/index.html#ch02-s3), with $`x\ne y`. Put $`m=s[x\mapsto1]`. Then

$$`f_{x:=1;\,y:=x+3}(s)=f_{y:=x+3}^{\dagger}(m)=f_{y:=x+3}(m)=m[y\mapsto4].`

The middle step uses the second equation of strict extension, because $`m` is a store. The result is the final store $`t` of the derivation in Session 2. Now let the prefix be $`\ell` from §8.1 and let $`g` be the meaning of `y := 7`. The sequencing $`g^{\dagger}\circ\ell` returns $`s[y\mapsto7]` when $`s(x)\le0`. When $`s(x)>0` it returns $`g^{\dagger}(\bot)=\bot`, and $`g` is never applied.

# Associativity of sequencing
%%%
tag := "ch08-s3"
%%%

Let $`f=\ell`, let $`g` be the meaning of `y := 7`, and let $`h` be the meaning of `x := x - 1`. At a store with $`s(x)=0`, the grouping $`h^{\dagger}\circ(g^{\dagger}\circ f)` first forms $`g^{\dagger}(s)=s[y\mapsto7]` and then returns $`s[y\mapsto7][x\mapsto-1]`. The grouping $`(h^{\dagger}\circ g)^{\dagger}\circ f` applies $`(h^{\dagger}\circ g)^{\dagger}` to the store $`s` and returns $`h^{\dagger}(g(s))`, the same store. At a store with $`s(x)=1`, $`f(s)=\bot`, and both groupings return $`\bot` without consulting $`g` or $`h`.

*Theorem 8.5 (Associativity of sequencing).* For all state transformers $`f,g,h`,

$$`h^{\dagger}\circ(g^{\dagger}\circ f)=(h^{\dagger}\circ g)^{\dagger}\circ f.`

Both sides are state transformers. On the right, $`h^{\dagger}\circ g` maps a store to an outcome, so it is a state transformer and has a strict extension.

*Proof.* By Definition 8.2 we must show, for every store $`s`,

$$`h^{\dagger}\bigl(g^{\dagger}(f(s))\bigr)=(h^{\dagger}\circ g)^{\dagger}\bigl(f(s)\bigr).`

Fix $`s`. By Definition 8.1 the outcome $`f(s)` is either $`\bot` or a store. We consider the two cases.

*Case 1 (the first part does not terminate).* Suppose $`f(s)=\bot`.

1. The left side is $`h^{\dagger}(g^{\dagger}(\bot))`. The first equation of strict extension for $`g` gives $`g^{\dagger}(\bot)=\bot`.
2. The first equation for $`h` gives $`h^{\dagger}(\bot)=\bot`. So the left side is $`\bot`.
3. The right side is $`(h^{\dagger}\circ g)^{\dagger}(\bot)`. The first equation for the state transformer $`h^{\dagger}\circ g` gives $`\bot`.
4. Both sides equal $`\bot`.

*Case 2 (the first part terminates).* Suppose $`f(s)=m` for a store $`m`, the intermediate store.

1. The left side is $`h^{\dagger}(g^{\dagger}(m))`. The second equation of strict extension for $`g` at the store $`m` gives $`g^{\dagger}(m)=g(m)`. So the left side is $`h^{\dagger}(g(m))`.
2. The right side is $`(h^{\dagger}\circ g)^{\dagger}(m)`. The second equation for $`h^{\dagger}\circ g` at the store $`m` gives $`(h^{\dagger}\circ g)(m)`.
3. By the definition of $`\circ`, $`(h^{\dagger}\circ g)(m)=h^{\dagger}(g(m))`.
4. Both sides equal $`h^{\dagger}(g(m))`.

The two sides agree at every store, so the two state transformers are equal. $`\square`

Case 2 never asks whether $`g(m)` is a store or $`\bot`. Both sides have become the same expression $`h^{\dagger}(g(m))`, whatever its value. A presenter who also splits on $`g(m)` obtains a correct but longer proof.

The two cases check the equation $`(h^{\dagger}\circ g)^{\dagger}(r)=h^{\dagger}(g^{\dagger}(r))` for both kinds of outcome $`r`. So $`(h^{\dagger}\circ g)^{\dagger}=h^{\dagger}\circ g^{\dagger}` as functions on $`\Sigma_{\bot}`. Since ordinary composition is associative, this identity is the whole content of Theorem 8.5.

*Corollary 8.6 (Associativity of command sequencing).* For all commands $`c_1,c_2,c_3` without loops, $`f_{(c_1;c_2);c_3}=f_{c_1;(c_2;c_3)}`.

*Proof.* The sequencing clause of Definition 8.4, applied twice on each side, gives

$$`\begin{aligned}
f_{(c_1;c_2);c_3}&=f_{c_3}^{\dagger}\circ f_{c_1;c_2}=f_{c_3}^{\dagger}\circ(f_{c_2}^{\dagger}\circ f_{c_1}),\\
f_{c_1;(c_2;c_3)}&=f_{c_2;c_3}^{\dagger}\circ f_{c_1}=(f_{c_3}^{\dagger}\circ f_{c_2})^{\dagger}\circ f_{c_1}.
\end{aligned}`

Apply Theorem 8.5 with $`f=f_{c_1}`, $`g=f_{c_2}` and $`h=f_{c_3}`. $`\square`

The proof uses only the sequencing clause. Once Session 9 defines the meaning of loops, the same proof applies to all commands. The two commands are different syntax trees with the same meaning.

# The information order
%%%
tag := "ch08-s4"
%%%

Let $`f(s)=s` when $`s(x)=0` and $`f(s)=\bot` otherwise. Let $`f'(s)=s` when $`s(x)\in\{0,1\}` and $`f'(s)=\bot` otherwise. Wherever $`f` returns a store, $`f'` returns the same store, and $`f'` returns a store at more inputs. We say $`f'` is more defined than $`f`. A state transformer that returns $`s[y\mapsto s(y)+1]` at the stores with $`s(x)=0` changes a result that $`f` already gives. It is neither more nor less defined than $`f`.

*Definition 8.7 (Information order).* Let $`r,r'` range over outcomes. Define

$$`r\sqsubseteq r'\quad\text{means}\quad r=\bot\ \text{or}\ r=r'.`

Read $`r\sqsubseteq r'` as “$`r` is less defined than or equal to $`r'`”. The smaller side is the less defined one. Since $`\bot\sqsubseteq r'` for every outcome $`r'`, $`\bot` is the least outcome. A store lies below only itself, so two different stores are incomparable. For state transformers define $`f\sqsubseteq f'` when $`f(s)\sqsubseteq f'(s)` for every store $`s`. Equivalently, wherever $`f` returns a store, $`f'` returns the same store. The least state transformer returns $`\bot` at every store.

The relation is reflexive ($`r\sqsubseteq r`), antisymmetric ($`r\sqsubseteq r'` and $`r'\sqsubseteq r` imply $`r=r'`) and transitive ($`r\sqsubseteq r'` and $`r'\sqsubseteq r''` imply $`r\sqsubseteq r''`). Each property follows by asking whether the left outcome is $`\bot`. The order on state transformers has the same three properties, store by store.

Information grows upward. A more defined state transformer may replace $`\bot` by a store, but it may not change a store result. In Session 9, $`\bot` also serves as a provisional result: a finite approximation of a loop returns $`\bot` where it does not yet know the final store. Such a $`\bot` is not yet evidence of nontermination.

For example, with $`f\sqsubseteq f'` as above and $`g` the meaning of `y := 7`, the sequencing $`g^{\dagger}\circ f` returns $`s[y\mapsto7]` at the stores with $`s(x)=0`. The sequencing $`g^{\dagger}\circ f'` returns the same store there, and returns a store at the stores with $`s(x)=1` as well.

*Proposition 8.8 (Sequencing preserves the order).* If $`f\sqsubseteq f'` and $`g\sqsubseteq g'`, then $`g^{\dagger}\circ f\sqsubseteq {g'}^{\dagger}\circ f'`.

*Proof.* Fix $`s`. If $`g^{\dagger}(f(s))=\bot`, it lies below every outcome. Otherwise it is a store $`t`. Then $`f(s)` is a store $`m`, because $`g^{\dagger}(\bot)=\bot`, and $`g(m)=t`. From $`f\sqsubseteq f'` and $`f(s)=m\ne\bot` we get $`f'(s)=m`. From $`g\sqsubseteq g'` and $`g(m)=t\ne\bot` we get $`g'(m)=t`. Hence $`{g'}^{\dagger}(f'(s))=g'(m)=t`. $`\square`

A store result already produced by a sequencing survives when either part becomes more defined. Session 9 builds the meaning of a loop from a sequence of state transformers, each more defined than the previous one. Its last step needs the following facts.

*Definition 8.9 (Least upper bound).* A sequence $`r_0,r_1,r_2,\ldots` of outcomes is *increasing* if $`r_n\sqsubseteq r_{n+1}` for every $`n`. An *upper bound* of the sequence is an outcome $`r'` with $`r_n\sqsubseteq r'` for every $`n`. A *least upper bound* is an upper bound that lies below every upper bound. By antisymmetry a sequence has at most one, written $`\bigsqcup_n r_n`. The same words apply to sequences of state transformers, ordered as in Definition 8.7.

For a store $`t`, the sequence $`\bot,\bot,t,t,t,\ldots` is increasing and its least upper bound is $`t`. For different stores $`t,t'`, the sequence $`\bot,t,t',\ldots` is not increasing, because $`t\not\sqsubseteq t'`.

*Lemma 8.10 (Increasing sequences of outcomes).* Let $`r_0\sqsubseteq r_1\sqsubseteq\cdots` be an increasing sequence of outcomes. Either $`r_n=\bot` for every $`n`, and then $`\bigsqcup_n r_n=\bot`. Or there are an index $`k` and a store $`t` with $`r_n=\bot` for $`n<k` and $`r_n=t` for $`n\ge k`, and then $`\bigsqcup_n r_n=t`.

*Proof.* If every $`r_n` is $`\bot`, then $`\bot` is an upper bound and lies below every outcome. Otherwise let $`k` be the least index at which $`r_k` is a store, and put $`t=r_k`. Then $`r_n=\bot` for $`n<k`. For $`n\ge k` prove $`P(n)\coloneqq(r_n=t)` by induction on $`n`, starting at $`k`. $`P(k)` holds by the choice of $`t`. If $`P(n)` holds, then $`t=r_n\sqsubseteq r_{n+1}` and $`t\ne\bot` give $`r_{n+1}=t`. So every $`r_n` is $`\bot` or $`t`, and $`t` is an upper bound. Any upper bound $`r'` satisfies $`t=r_k\sqsubseteq r'`. Hence $`t` is the least upper bound. $`\square`

For state transformers the index $`k` can depend on the store. For each natural number $`n` let $`g_n(s)=s` when $`\lvert s(x)\rvert<n` and $`g_n(s)=\bot` otherwise. Then $`g_0` is the least state transformer and $`g_n\sqsubseteq g_{n+1}`. At a fixed store the outcomes $`g_n(s)` are $`\bot` for $`n\le\lvert s(x)\rvert` and $`s` from $`n=\lvert s(x)\rvert+1` on. By Lemma 8.10 their least upper bound is $`s`. Store by store, the least upper bound is the identity $`s\mapsto s`. No single $`g_n` equals it: at a store with $`s(x)=n`, $`g_n` still returns $`\bot`.

*Proposition 8.11 (Least upper bound of state transformers).* Every increasing sequence $`g_0\sqsubseteq g_1\sqsubseteq\cdots` of state transformers has a least upper bound, computed store by store:

$$`\Bigl(\bigsqcup_n g_n\Bigr)(s)=\bigsqcup_n g_n(s).`

*Proof.* At each store $`s`, the order on state transformers makes $`g_0(s)\sqsubseteq g_1(s)\sqsubseteq\cdots` an increasing sequence of outcomes. Lemma 8.10 gives its least upper bound. Call it $`g(s)`. Then $`g_n(s)\sqsubseteq g(s)` for every $`n` and $`s`, so $`g` is an upper bound. If $`h` is any upper bound, then $`h(s)` is an upper bound of the outcomes $`g_n(s)`, so $`g(s)\sqsubseteq h(s)` for every $`s`. Hence $`g\sqsubseteq h`. $`\square`

Session 9 defines the meaning of a loop as such a least upper bound.

# Exercises
%%%
tag := "ch08-s5"
number := false
%%%

*8.1.* An analyst proposes a different order on outcomes: $`\bot` lies below every outcome, and for stores $`t\sqsubseteq t'` when $`t(x)\le t'(x)`. Show that this order lets a more defined state transformer change a store result that is already known. Which step in the proof of Proposition 8.8 fails?

*8.2.* Prove that the meaning of skip is a unit for sequencing: $`f^{\dagger}\circ f_{\mathsf{skip}}=f` and $`f_{\mathsf{skip}}^{\dagger}\circ f=f` for every state transformer $`f`. Treat the stores where $`f` returns $`\bot` explicitly.

*8.3.* Find state transformers $`f`, $`g` and $`g'` with $`g\ne g'` but $`g^{\dagger}\circ f={g'}^{\dagger}\circ f`. State a condition on the stores where $`g` and $`g'` differ that is necessary and sufficient for this equation.

*Further problem.* Two state transformers $`f,g` need not be comparable. Characterize exactly when they have a common upper bound. In that case construct their least upper bound. Compare the criterion with Lemma 8.10, where the sequence is increasing.

# Reading for the Seminar
%%%
tag := "ch08-s6"
number := false
%%%

*Definitions · 10 minutes.* Write the types $`f:\Sigma\to\Sigma_{\bot}` and $`g^{\dagger}:\Sigma_{\bot}\to\Sigma_{\bot}` on the board. Compute the suffix `y := 7` after a terminating prefix and after a prefix that returns $`\bot`. Use the two answers to state the two equations of strict extension.

*Joint proof · 30 minutes.* Write the goal of Theorem 8.5 at one store $`s`. One participant works Case 1 and another Case 2, each naming the equation used at every step. Check that $`h^{\dagger}\circ g` is a state transformer before taking its strict extension. Derive Corollary 8.6 by unfolding Definition 8.4.

*Proof review · 20 minutes.* State Definition 8.7 and say aloud which side is less defined. Replace the prefix by a more defined state transformer and use Proposition 8.8 to decide whether an observed store result can change. Compute the least upper bound of the sequence $`g_n` in §8.4.

*Facilitator’s hint.* Fix one store and split on $`f(s)` before applying anything else. Under each expression, write what it is: a store, an outcome, or a function.

# Solutions and Further Reading
%%%
tag := "ch08-s7"
number := false
%%%

*8.1.* Fix a store $`s`. Let $`f(s)=m` with $`m(x)=2`, let $`f'(s)=m[x\mapsto3]`, and let $`f,f'` agree at every other store. The proposed order gives $`f\sqsubseteq f'`, yet the two disagree on an observable final value. Proposition 8.8 also fails. Let $`g` return its input when $`x=2` and $`\bot` otherwise. Then $`g^{\dagger}(f(s))` is a store but $`g^{\dagger}(f'(s))=\bot`. The failing step is the inference from $`f\sqsubseteq f'` and $`f(s)=m\ne\bot` to $`f'(s)=m`. Definition 8.7 makes this step valid because a store lies below only itself.

*8.2.* At a store $`s`, $`f^{\dagger}(f_{\mathsf{skip}}(s))=f^{\dagger}(s)=f(s)` by the second equation of strict extension. For the other order, if $`f(s)=\bot` then $`f_{\mathsf{skip}}^{\dagger}(\bot)=\bot=f(s)`. If $`f(s)=m` is a store, then $`f_{\mathsf{skip}}^{\dagger}(m)=f_{\mathsf{skip}}(m)=m=f(s)`.

*8.3.* Let $`f` be the meaning of `x := 0`, let $`g` be the meaning of skip, and let $`g'(s)=s` when $`s(x)=0` and $`g'(s)=\bot` otherwise. Every store returned by $`f` has $`x=0`, where $`g` and $`g'` agree. The condition is that $`g(m)=g'(m)` for every store $`m` that $`f` returns at some input. It is sufficient: at $`s`, either $`f(s)=\bot` and both sides are $`\bot`, or $`f(s)=m` and both sides are $`g(m)=g'(m)`. It is necessary: if $`f(s)=m`, the equation at $`s` reads $`g(m)=g'(m)`.

*Further problem.* Agreement is required wherever both state transformers return stores. If $`f(s)` and $`g(s)` were different stores, an upper bound at $`s` would have to lie above both, and a store lies below only itself. Conversely, assume agreement wherever both return stores. Define $`h(s)=f(s)` when $`f(s)` is a store, and $`h(s)=g(s)` otherwise. At a store where neither returns a store, $`h(s)=\bot`. Checking these cases shows $`f\sqsubseteq h` and $`g\sqsubseteq h`. For leastness take any common upper bound $`h'`. Where $`h(s)` is a store, one of $`f,g` already returns it and forces $`h'(s)=h(s)`. Where $`h(s)=\bot` the inequality holds automatically. Thus $`h\sqsubseteq h'`. In an increasing sequence this agreement is automatic. An arbitrary pair need not have it.

*Further reading · Graphs and the intermediate store.* The graph of a state transformer $`f` is the set of pairs $`(s,t)` of stores with $`f(s)=t`, as in [Session 3, §3.3](chapter-03/index.html#ch03-s3). Then $`f\sqsubseteq f'` holds exactly when the graph of $`f` is contained in the graph of $`f'`. For the sequencing $`g^{\dagger}\circ f`, expand the two equations of strict extension. If $`f(s)=\bot`, no pair $`(s,t)` is in its graph. If $`f(s)=m`, the pair is in its graph exactly when $`g(m)=t`. Combining the cases, $`(s,t)` is in the graph of $`g^{\dagger}\circ f` exactly when some store $`m` has $`(s,m)` in the graph of $`f` and $`(m,t)` in the graph of $`g`. This has the shape of the sequence rule in [A.5](imp-card/index.html#imp-a5). The pair $`f,g'` in Solution 8.3 shows that the intermediate store matters even for termination alone. Their sequencing returns a store at every input, including inputs where $`g'` alone returns $`\bot`. Intersecting the inputs where $`f` returns a store with those where $`g'` does would give the wrong answer.

*Further reading · Regrouping derivations.* The further reading of [Session 2](chapter-02/index.html#ch02-s7) regroups an execution tree for $`(c_1;c_2);c_3` by inverting it twice and reassembling the three subderivations around two intermediate stores. Corollary 8.6 states the same regrouping as an equation between functions, and its proof uses no derivations.

*Further reading · Option types.* Many programming languages have an option type, whose values are either a present value or a distinguished empty value, with an operation that applies a function only to a present value. With stores as present values and $`\bot` as the empty value, that operation is strict extension, and Theorem 8.5 is one of its standard laws.

# Sources and Formalization
%%%
tag := "ch08-notes"
number := false
%%%

* *Theorem 8.5.* Source: Reynolds §§2.2–2.3, strict extension. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Corollary 8.6.* Source: Reynolds §§2.2–2.3, the sequencing clause. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 8.8.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 8.10.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 8.11.* Formulated in this book. Checked in Lean ([IMP card references](imp-card/index.html#imp-sources)).
