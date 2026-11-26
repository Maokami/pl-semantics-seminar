import VersoManual
import PLBook.IMP.Denotation

open Verso.Genre Manual

#doc (Manual) "State Transformers and the Information Order" =>
%%%
tag := "ch08"
file := "chapter-08"
%%%

The command `x := x + 1` produces a final state from every initial state. The command `while 0 < x do skip` returns its initial state when $`\sigma(x)\le0` and has no terminating execution when $`\sigma(x)>0`. We want a meaning for each command that is one function on states, and we want the meaning of `c; d` to be computed from the meanings of `c` and `d`. Two questions follow. What does the function return when there is no final state? What does the second command do when the first returns nothing?

*In this session.*

* *Definitions.* States and update ([A.2](imp-card/index.html#imp-a2)), expression evaluation ([A.3](imp-card/index.html#imp-a3)), commands and guard values ([A.4](imp-card/index.html#imp-a4)), the branch selected by a guard ([A.5](imp-card/index.html#imp-a5)), partial functions and their graphs ([Session 3, §3.3](chapter-03/index.html#ch03-s3)). This session adds Definitions 8.1–8.4, 8.7 and 8.9.
* *New terms.* Bottom, state transformer, strict extension, information order, least upper bound. [Glossary](glossary/index.html)
* *Theorem 8.5 (Associativity of sequencing).* For all state transformers $`f,g,h`, $`h^{\dagger}\circ(g^{\dagger}\circ f)=(h^{\dagger}\circ g)^{\dagger}\circ f`. Running $`f`, then $`g`, then $`h` gives the same state transformer under either grouping.
* *Board case.* Theorem 8.5 at one state $`\sigma`, in both cases of the first state transformer: it does not terminate ($`f(\sigma)=\bot`), and it terminates in an intermediate state ($`f(\sigma)=\sigma_1`).
* *Proof outline.* Two state transformers are equal when they agree at every state. Fix $`\sigma` and split on the outcome $`f(\sigma)`. In each case apply the two equations of strict extension until both sides become the same expression. No induction is needed.
* *From Session 7.* Session 7 compared two commands through their terminating executions, one pair of states at a time. Here each command without loops receives a single state transformer, and a claim about all executions of two commands becomes an equation between two functions.

# Outcomes and state transformers
%%%
tag := "ch08-s1"
%%%

Let $`W` be `while 0 < x do skip`. By [A.4](imp-card/index.html#imp-a4) its guard abbreviates $`\neg(x\le0)`, so it is true exactly when $`\sigma(x)>0`. If $`\sigma(x)\le0`, the loop exit rule of [A.5](imp-card/index.html#imp-a5) gives $`\sigma\vdash W\Downarrow\sigma`. If $`\sigma(x)>0`, there is no final state. The least-height argument of [Session 2, §2.4](chapter-02/index.html#ch02-s4) applies unchanged, because the body skip returns the same state and the guard stays true. By [Session 3, §3.3](chapter-03/index.html#ch03-s3), the executions of $`W` form the graph of a partial function on states, defined exactly at the states with $`\sigma(x)\le0`.

*Definition 8.1 (Outcomes).* Let $`\bot`, read *bottom*, be an element that is not a state. Put $`\Sigma_{\bot}=\Sigma\cup\{\bot\}`. An *outcome* is an element of $`\Sigma_{\bot}`: either a state or $`\bot`. As the result of a command, $`\bot` records that there is no final state, that is, nontermination.

*Definition 8.2 (State transformer).* A *state transformer* is a total function $`f:\Sigma\to\Sigma_{\bot}`. Two state transformers $`f,g` are equal when $`f(\sigma)=g(\sigma)` for every state $`\sigma`.

In the *denotational semantics* of IMP the mathematical meaning, or *denotation*, of each command $`c` is a state transformer $`f_c`. A sequence uses the meanings of its two parts to compute its own meaning (§8.2). A loop must also account for the possibility of arbitrarily many iterations. [Section 9.3](chapter-09/index.html#ch09-s3) uses the information order to determine which solution of the loop equation describes execution.

For $`W` above, define the state transformer $`\ell` by $`\ell(\sigma)=\sigma` if $`\sigma(x)\le0` and $`\ell(\sigma)=\bot` if $`\sigma(x)>0`. Session 9 gives $`W` exactly this meaning. A partial function on states and a state transformer carry the same information: the partial function is undefined at $`\sigma` exactly when the state transformer returns $`\bot` at $`\sigma`. The difference is that a state transformer returns a value at every state. We can pass that value to another function and split on it by cases.

# Meanings of commands
%%%
tag := "ch08-s2"
%%%

Suppose a command $`c` is followed by `y := 7`, and write $`f_c` for the state transformer of $`c` (Definition 8.4 below). If $`f_c(\sigma)` is a state $`\sigma_1`, the sequence should return $`\sigma_1[y\mapsto7]`. If $`f_c(\sigma)=\bot`, no state ever reaches the assignment, and the sequence should return $`\bot`. Ordinary function application cannot express this. The state transformer of `y := 7` accepts only states, and $`\bot` is not a state.

*Definition 8.3 (Strict extension and sequencing).* For a state transformer $`g`, its *strict extension* $`g^{\dagger}:\Sigma_{\bot}\to\Sigma_{\bot}` is given by two equations:

$$`g^{\dagger}(\bot)=\bot,\qquad g^{\dagger}(\sigma')=g(\sigma')\quad\text{for every state }\sigma'.`

The word *strict* means that $`\bot` is sent to $`\bot`. The *sequencing* of $`f` followed by $`g` is the state transformer $`g^{\dagger}\circ f`. Here $`\circ` is ordinary function composition, $`(g^{\dagger}\circ f)(\sigma)=g^{\dagger}(f(\sigma))`. The state transformer that runs first is written on the right.

*Definition 8.4 (Meaning of a command).* For each command $`c` without loops, define its meaning $`f_c:\Sigma\to\Sigma_{\bot}` by structural recursion on $`c`. For $`I=\mathsf{if}\ b\ \mathsf{then}\ c\ \mathsf{else}\ d`, let $`k` be the branch selected by $`B(b,\sigma)` as in [A.5](imp-card/index.html#imp-a5).

$$`\begin{aligned}
f_{\mathsf{skip}}(\sigma)&=\sigma & f_{x:=e}(\sigma)&=\sigma[x\mapsto\mathrm{eval}(e,\sigma)]\\
f_{c;d}&=f_d^{\dagger}\circ f_c & f_I(\sigma)&=f_k(\sigma)
\end{aligned}`

Each clause uses only the meanings of the immediate parts. Session 9 adds the clause for loops. The four clauses above stay as they are.

For example, take `x := 1; y := x + 3` from [Session 2, §2.3](chapter-02/index.html#ch02-s3), with $`x\ne y`. Put $`\sigma_1=\sigma[x\mapsto1]`. Then

$$`f_{x:=1;\,y:=x+3}(\sigma)=f_{y:=x+3}^{\dagger}(\sigma_1)=f_{y:=x+3}(\sigma_1)=\sigma_1[y\mapsto4].`

The middle step uses the second equation of strict extension, because $`\sigma_1` is a state. The result is the final state $`\sigma'` of the derivation in Session 2. Now let the prefix be $`\ell` from §8.1 and let $`g` be the meaning of `y := 7`. The sequencing $`g^{\dagger}\circ\ell` returns $`\sigma[y\mapsto7]` when $`\sigma(x)\le0`. When $`\sigma(x)>0` it returns $`g^{\dagger}(\bot)=\bot`, and $`g` is never applied.

# Associativity of sequencing
%%%
tag := "ch08-s3"
%%%

Let $`f=\ell`, let $`g` be the meaning of `y := 7`, and let $`h` be the meaning of `x := x - 1`. At a state with $`\sigma(x)=0`, the grouping $`h^{\dagger}\circ(g^{\dagger}\circ f)` first forms $`g^{\dagger}(\sigma)=\sigma[y\mapsto7]` and then returns $`\sigma[y\mapsto7][x\mapsto-1]`. The grouping $`(h^{\dagger}\circ g)^{\dagger}\circ f` applies $`(h^{\dagger}\circ g)^{\dagger}` to the state $`\sigma` and returns $`h^{\dagger}(g(\sigma))`, the same state. At a state with $`\sigma(x)=1`, $`f(\sigma)=\bot`, and both groupings return $`\bot` without consulting $`g` or $`h`.

*Theorem 8.5 (Associativity of sequencing).* For all state transformers $`f,g,h`,

$$`h^{\dagger}\circ(g^{\dagger}\circ f)=(h^{\dagger}\circ g)^{\dagger}\circ f.`

Both sides are state transformers. On the right, $`h^{\dagger}\circ g` maps a state to an outcome, so it is a state transformer and has a strict extension.

*Proof.* By Definition 8.2 we must show, for every state $`\sigma`,

$$`h^{\dagger}\bigl(g^{\dagger}(f(\sigma))\bigr)=(h^{\dagger}\circ g)^{\dagger}\bigl(f(\sigma)\bigr).`

Fix $`\sigma`. By Definition 8.1 the outcome $`f(\sigma)` is either $`\bot` or a state. We consider the two cases.

*Case 1 (the first part does not terminate).* Suppose $`f(\sigma)=\bot`.

1. The left side is $`h^{\dagger}(g^{\dagger}(\bot))`. The first equation of strict extension for $`g` gives $`g^{\dagger}(\bot)=\bot`.
2. The first equation for $`h` gives $`h^{\dagger}(\bot)=\bot`. So the left side is $`\bot`.
3. The right side is $`(h^{\dagger}\circ g)^{\dagger}(\bot)`. The first equation for the state transformer $`h^{\dagger}\circ g` gives $`\bot`.
4. Both sides equal $`\bot`.

*Case 2 (the first part terminates).* Suppose $`f(\sigma)=\sigma_1` for a state $`\sigma_1`, the intermediate state.

1. The left side is $`h^{\dagger}(g^{\dagger}(\sigma_1))`. The second equation of strict extension for $`g` at the state $`\sigma_1` gives $`g^{\dagger}(\sigma_1)=g(\sigma_1)`. So the left side is $`h^{\dagger}(g(\sigma_1))`.
2. The right side is $`(h^{\dagger}\circ g)^{\dagger}(\sigma_1)`. The second equation for $`h^{\dagger}\circ g` at the state $`\sigma_1` gives $`(h^{\dagger}\circ g)(\sigma_1)`.
3. By the definition of $`\circ`, $`(h^{\dagger}\circ g)(\sigma_1)=h^{\dagger}(g(\sigma_1))`.
4. Both sides equal $`h^{\dagger}(g(\sigma_1))`.

The two sides agree at every state, so the two state transformers are equal. $`\square`

Case 2 never asks whether $`g(\sigma_1)` is a state or $`\bot`. Both sides have become the same expression $`h^{\dagger}(g(\sigma_1))`, whatever its value. A presenter who also splits on $`g(\sigma_1)` obtains a correct but longer proof.

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

Let $`f(\sigma)=\sigma` when $`\sigma(x)=0` and $`f(\sigma)=\bot` otherwise. Let $`f'(\sigma)=\sigma` when $`\sigma(x)\in\{0,1\}` and $`f'(\sigma)=\bot` otherwise. Wherever $`f` returns a state, $`f'` returns the same state, and $`f'` returns a state at more inputs. We say $`f'` is more defined than $`f`. A state transformer that returns $`\sigma[y\mapsto \sigma(y)+1]` at the states with $`\sigma(x)=0` changes a result that $`f` already gives. It is neither more nor less defined than $`f`.

*Definition 8.7 (Information order).* Let $`r,r'` range over outcomes. Define

$$`r\sqsubseteq r'\quad\text{means}\quad r=\bot\ \text{or}\ r=r'.`

Read $`r\sqsubseteq r'` as “$`r` is less defined than or equal to $`r'`”. The smaller side is the less defined one. Since $`\bot\sqsubseteq r'` for every outcome $`r'`, $`\bot` is the least outcome. A state lies below only itself, so two different states are incomparable. For state transformers define $`f\sqsubseteq f'` when $`f(\sigma)\sqsubseteq f'(\sigma)` for every state $`\sigma`. Equivalently, wherever $`f` returns a state, $`f'` returns the same state. The least state transformer returns $`\bot` at every state.

The relation is reflexive ($`r\sqsubseteq r`), antisymmetric ($`r\sqsubseteq r'` and $`r'\sqsubseteq r` imply $`r=r'`) and transitive ($`r\sqsubseteq r'` and $`r'\sqsubseteq r''` imply $`r\sqsubseteq r''`). Each property follows by asking whether the left outcome is $`\bot`. The order on state transformers has the same three properties, state by state.

Information grows upward. A more defined state transformer may replace $`\bot` by a state, but it may not change a state result. In Session 9, $`\bot` also serves as a provisional result: a finite approximation of a loop returns $`\bot` where it does not yet know the final state. Such a $`\bot` is not yet evidence of nontermination.

For example, with $`f\sqsubseteq f'` as above and $`g` the meaning of `y := 7`, the sequencing $`g^{\dagger}\circ f` returns $`\sigma[y\mapsto7]` at the states with $`\sigma(x)=0`. The sequencing $`g^{\dagger}\circ f'` returns the same state there, and returns a state at the states with $`\sigma(x)=1` as well.

*Proposition 8.8 (Sequencing preserves the order).* If $`f\sqsubseteq f'` and $`g\sqsubseteq g'`, then $`g^{\dagger}\circ f\sqsubseteq {g'}^{\dagger}\circ f'`.

*Proof.* Fix $`\sigma`. If $`g^{\dagger}(f(\sigma))=\bot`, it lies below every outcome. Otherwise it is a state $`\sigma'`. Then $`f(\sigma)` is a state $`\sigma_1`, because $`g^{\dagger}(\bot)=\bot`, and $`g(\sigma_1)=\sigma'`. From $`f\sqsubseteq f'` and $`f(\sigma)=\sigma_1\ne\bot` we get $`f'(\sigma)=\sigma_1`. From $`g\sqsubseteq g'` and $`g(\sigma_1)=\sigma'\ne\bot` we get $`g'(\sigma_1)=\sigma'`. Hence $`{g'}^{\dagger}(f'(\sigma))=g'(\sigma_1)=\sigma'`. $`\square`

A state result already produced by a sequencing survives when either part becomes more defined. Session 9 builds the meaning of a loop from a sequence of state transformers, each more defined than the previous one. Its last step needs the following facts.

*Definition 8.9 (Least upper bound).* A sequence $`r_0,r_1,r_2,\ldots` of outcomes is *increasing* if $`r_n\sqsubseteq r_{n+1}` for every $`n`. An *upper bound* of the sequence is an outcome $`r'` with $`r_n\sqsubseteq r'` for every $`n`. A *least upper bound* is an upper bound that lies below every upper bound. By antisymmetry a sequence has at most one, written $`\bigsqcup_n r_n`. The same words apply to sequences of state transformers, ordered as in Definition 8.7.

For a state $`\sigma'`, the sequence $`\bot,\bot,\sigma',\sigma',\sigma',\ldots` is increasing and its least upper bound is $`\sigma'`. For different states $`\sigma',\sigma''`, the sequence $`\bot,\sigma',\sigma'',\ldots` is not increasing, because $`\sigma'\not\sqsubseteq \sigma''`.

*Lemma 8.10 (Increasing sequences of outcomes).* Let $`r_0\sqsubseteq r_1\sqsubseteq\cdots` be an increasing sequence of outcomes. Either $`r_n=\bot` for every $`n`, and then $`\bigsqcup_n r_n=\bot`. Or there are an index $`k` and a state $`\sigma'` with $`r_n=\bot` for $`n<k` and $`r_n=\sigma'` for $`n\ge k`, and then $`\bigsqcup_n r_n=\sigma'`.

*Proof.* If every $`r_n` is $`\bot`, then $`\bot` is an upper bound and lies below every outcome. Otherwise let $`k` be the least index at which $`r_k` is a state, and put $`\sigma'=r_k`. Then $`r_n=\bot` for $`n<k`. For $`n\ge k` prove $`P(n)\coloneqq(r_n=\sigma')` by induction on $`n`, starting at $`k`. $`P(k)` holds by the choice of $`\sigma'`. If $`P(n)` holds, then $`\sigma'=r_n\sqsubseteq r_{n+1}` and $`\sigma'\ne\bot` give $`r_{n+1}=\sigma'`. So every $`r_n` is $`\bot` or $`\sigma'`, and $`\sigma'` is an upper bound. Any upper bound $`r'` satisfies $`\sigma'=r_k\sqsubseteq r'`. Hence $`\sigma'` is the least upper bound. $`\square`

For state transformers the index $`k` can depend on the state. For each natural number $`n` let $`g_n(\sigma)=\sigma` when $`\lvert \sigma(x)\rvert<n` and $`g_n(\sigma)=\bot` otherwise. Then $`g_0` is the least state transformer and $`g_n\sqsubseteq g_{n+1}`. At a fixed state the outcomes $`g_n(\sigma)` are $`\bot` for $`n\le\lvert \sigma(x)\rvert` and $`\sigma` from $`n=\lvert \sigma(x)\rvert+1` on. By Lemma 8.10 their least upper bound is $`\sigma`. State by state, the least upper bound is the identity $`\sigma\mapsto \sigma`. No single $`g_n` equals it: at a state with $`\sigma(x)=n`, $`g_n` still returns $`\bot`.

*Proposition 8.11 (Least upper bound of state transformers).* Every increasing sequence $`g_0\sqsubseteq g_1\sqsubseteq\cdots` of state transformers has a least upper bound, computed state by state:

$$`\Bigl(\bigsqcup_n g_n\Bigr)(\sigma)=\bigsqcup_n g_n(\sigma).`

*Proof.* At each state $`\sigma`, the order on state transformers makes $`g_0(\sigma)\sqsubseteq g_1(\sigma)\sqsubseteq\cdots` an increasing sequence of outcomes. Lemma 8.10 gives its least upper bound. Call it $`g(\sigma)`. Then $`g_n(\sigma)\sqsubseteq g(\sigma)` for every $`n` and $`\sigma`, so $`g` is an upper bound. If $`h` is any upper bound, then $`h(\sigma)` is an upper bound of the outcomes $`g_n(\sigma)`, so $`g(\sigma)\sqsubseteq h(\sigma)` for every $`\sigma`. Hence $`g\sqsubseteq h`. $`\square`

Session 9 defines the meaning of a loop as such a least upper bound.

# Exercises
%%%
tag := "ch08-s5"
number := false
%%%

*8.1.* An analyst proposes a different order on outcomes: $`\bot` lies below every outcome, and for states $`\sigma'\sqsubseteq \sigma''` when $`\sigma'(x)\le \sigma''(x)`. Show that this order lets a more defined state transformer change a state result that is already known. Which step in the proof of Proposition 8.8 fails?

*8.2.* Prove that the meaning of skip is a unit for sequencing: $`f^{\dagger}\circ f_{\mathsf{skip}}=f` and $`f_{\mathsf{skip}}^{\dagger}\circ f=f` for every state transformer $`f`. Treat the states where $`f` returns $`\bot` explicitly.

*8.3.* Find state transformers $`f`, $`g` and $`g'` with $`g\ne g'` but $`g^{\dagger}\circ f={g'}^{\dagger}\circ f`. State a condition on the states where $`g` and $`g'` differ that is necessary and sufficient for this equation.

*Further problem.* Two state transformers $`f,g` need not be comparable. Characterize exactly when they have a common upper bound. In that case construct their least upper bound. Compare the criterion with Lemma 8.10, where the sequence is increasing.

# Reading for the Seminar
%%%
tag := "ch08-s6"
number := false
%%%

*Definitions · 10 minutes.* Write the types $`f:\Sigma\to\Sigma_{\bot}` and $`g^{\dagger}:\Sigma_{\bot}\to\Sigma_{\bot}` on the board. Compute the suffix `y := 7` after a terminating prefix and after a prefix that returns $`\bot`. Use the two answers to state the two equations of strict extension.

*Joint proof · 30 minutes.* Write the goal of Theorem 8.5 at one state $`\sigma`. One participant works Case 1 and another Case 2, each naming the equation used at every step. Check that $`h^{\dagger}\circ g` is a state transformer before taking its strict extension. Derive Corollary 8.6 by unfolding Definition 8.4.

*Proof review · 20 minutes.* State Definition 8.7 and say aloud which side is less defined. Replace the prefix by a more defined state transformer and use Proposition 8.8 to decide whether an observed state result can change. Compute the least upper bound of the sequence $`g_n` in §8.4.

*Facilitator’s hint.* Fix one state and split on $`f(\sigma)` before applying anything else. Under each expression, write what it is: a state, an outcome, or a function.

# Solutions and Further Reading
%%%
tag := "ch08-s7"
number := false
%%%

*8.1.* Fix a state $`\sigma`. Let $`f(\sigma)=\sigma_1` with $`\sigma_1(x)=2`, let $`f'(\sigma)=\sigma_1[x\mapsto3]`, and let $`f,f'` agree at every other state. The proposed order gives $`f\sqsubseteq f'`, yet the two disagree on an observable final value. Proposition 8.8 also fails. Let $`g` return its input when $`x=2` and $`\bot` otherwise. Then $`g^{\dagger}(f(\sigma))` is a state but $`g^{\dagger}(f'(\sigma))=\bot`. The failing step is the inference from $`f\sqsubseteq f'` and $`f(\sigma)=\sigma_1\ne\bot` to $`f'(\sigma)=\sigma_1`. Definition 8.7 makes this step valid because a state lies below only itself.

*8.2.* At a state $`\sigma`, $`f^{\dagger}(f_{\mathsf{skip}}(\sigma))=f^{\dagger}(\sigma)=f(\sigma)` by the second equation of strict extension. For the other order, if $`f(\sigma)=\bot` then $`f_{\mathsf{skip}}^{\dagger}(\bot)=\bot=f(\sigma)`. If $`f(\sigma)=\sigma_1` is a state, then $`f_{\mathsf{skip}}^{\dagger}(\sigma_1)=f_{\mathsf{skip}}(\sigma_1)=\sigma_1=f(\sigma)`.

*8.3.* Let $`f` be the meaning of `x := 0`, let $`g` be the meaning of skip, and let $`g'(\sigma)=\sigma` when $`\sigma(x)=0` and $`g'(\sigma)=\bot` otherwise. Every state returned by $`f` has $`x=0`, where $`g` and $`g'` agree. The condition is that $`g(\sigma_1)=g'(\sigma_1)` for every state $`\sigma_1` that $`f` returns at some input. It is sufficient: at $`\sigma`, either $`f(\sigma)=\bot` and both sides are $`\bot`, or $`f(\sigma)=\sigma_1` and both sides are $`g(\sigma_1)=g'(\sigma_1)`. It is necessary: if $`f(\sigma)=\sigma_1`, the equation at $`\sigma` reads $`g(\sigma_1)=g'(\sigma_1)`.

*Further problem.* Agreement is required wherever both state transformers return states. If $`f(\sigma)` and $`g(\sigma)` were different states, an upper bound at $`\sigma` would have to lie above both, and a state lies below only itself. Conversely, assume agreement wherever both return states. Define $`h(\sigma)=f(\sigma)` when $`f(\sigma)` is a state, and $`h(\sigma)=g(\sigma)` otherwise. At a state where neither returns a state, $`h(\sigma)=\bot`. Checking these cases shows $`f\sqsubseteq h` and $`g\sqsubseteq h`. For leastness take any common upper bound $`h'`. Where $`h(\sigma)` is a state, one of $`f,g` already returns it and forces $`h'(\sigma)=h(\sigma)`. Where $`h(\sigma)=\bot` the inequality holds automatically. Thus $`h\sqsubseteq h'`. In an increasing sequence this agreement is automatic. An arbitrary pair need not have it.

*Further reading · Graphs and the intermediate state.* The graph of a state transformer $`f` is the set of pairs $`(\sigma,\sigma')` of states with $`f(\sigma)=\sigma'`, as in [Session 3, §3.3](chapter-03/index.html#ch03-s3). Then $`f\sqsubseteq f'` holds exactly when the graph of $`f` is contained in the graph of $`f'`. For the sequencing $`g^{\dagger}\circ f`, expand the two equations of strict extension. If $`f(\sigma)=\bot`, no pair $`(\sigma,\sigma')` is in its graph. If $`f(\sigma)=\sigma_1`, the pair is in its graph exactly when $`g(\sigma_1)=\sigma'`. Combining the cases, $`(\sigma,\sigma')` is in the graph of $`g^{\dagger}\circ f` exactly when some state $`\sigma_1` has $`(\sigma,\sigma_1)` in the graph of $`f` and $`(\sigma_1,\sigma')` in the graph of $`g`. This has the shape of the sequence rule in [A.5](imp-card/index.html#imp-a5). The pair $`f,g'` in Solution 8.3 shows that the intermediate state matters even for termination alone. Their sequencing returns a state at every input, including inputs where $`g'` alone returns $`\bot`. Intersecting the inputs where $`f` returns a state with those where $`g'` does would give the wrong answer.

*Further reading · Regrouping derivations.* The further reading of [Session 2](chapter-02/index.html#ch02-s7) regroups an execution tree for $`(c_1;c_2);c_3` by inverting it twice and reassembling the three subderivations around two intermediate states. Corollary 8.6 states the same regrouping as an equation between functions, and its proof uses no derivations.

*Further reading · Option types.* Many programming languages have an option type, whose values are either a present value or a distinguished empty value, with an operation that applies a function only to a present value. With states as present values and $`\bot` as the empty value, that operation is strict extension, and Theorem 8.5 is one of its standard laws.

# Sources and Formalization
%%%
tag := "ch08-notes"
number := false
%%%

The outcomes, strict extension, command meanings and information order follow John C. Reynolds, _Theories of Programming Languages_, §§2.2–2.3. Here they are applied to the commands of [A.4](imp-card/index.html#imp-a4). [Reynolds, contents](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

* *Theorem 8.5.* Source: Reynolds §§2.2–2.3, strict extension. Checked in Lean ([`sequencingAssoc`](lean/Denotation.html#sequencingAssoc) · [IMP card references](imp-card/index.html#imp-sources)).
* *Corollary 8.6.* Source: Reynolds §§2.2–2.3, the sequencing clause. Checked in Lean ([`commandSequencingAssoc`](lean/Denotation.html#commandSequencingAssoc) · [IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 8.8.* Formulated in this book. Checked in Lean ([`sequencingMono`](lean/Denotation.html#sequencingMono) · [IMP card references](imp-card/index.html#imp-sources)).
* *Lemma 8.10.* Formulated in this book. Checked in Lean ([`outcomeChainCases`](lean/Denotation.html#outcomeChainCases) · [IMP card references](imp-card/index.html#imp-sources)).
* *Proposition 8.11.* Formulated in this book. Checked in Lean ([`chainSup_isLub`](lean/Denotation.html#chainSup_isLub) · [IMP card references](imp-card/index.html#imp-sources)).
