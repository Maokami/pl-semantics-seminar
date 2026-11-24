import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Contextual Equivalence and Full Abstraction" =>
%%%
tag := "ch30"
file := "chapter-30"
%%%

[Chapter PDF](print/chapter-30.pdf) · [Session 30](seminar/index.html#week-30)

At ground type, Chapter 29 connects a concrete result of the domain calculation with an evaluation returning that value. At function type the domain also contains arguments that a source program cannot supply. Two source functions might differ on one of those arguments even when every program using them behaves identically.

*Sources.* Cambridge _Denotational Semantics_, lecture 7 and notes §8.1, especially Theorems 40–41. Read the table for parallel disjunction and the proof using two higher-order testers. We use the notes’ nondefinability and function extensionality results and work out the separating argument. [Lecture 7.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Lecture7.pdf) [Notes.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

# Observations
%%%
tag := "ch30-s1"
%%%

A *closing context* for a term of type $`A` is a well-typed expression with a hole of type $`A` whose filling yields a closed program of observable ground type. Two closed terms are contextually equivalent if every such experiment gives the same observation: for each ground value, one filled program evaluates to it exactly when the other does. Compositionality maps equal denotations to equal meanings in every context. Soundness and adequacy then give contextual equivalence. *Full abstraction* additionally requires contextual equivalence to imply equality of denotations.

The standard PCF model contains all continuous functions between the chosen domains. Write $`B` for the flat Booleans with bottom, and $`p` for parallel disjunction on two such inputs, regarded as curried. It returns true if either argument is true, false if both are false, and bottom otherwise. It is monotone since each determined output persists under a refinement of its inputs. The domain of input pairs is finite, so every increasing chain stabilizes, proving continuity. In particular $`p` belongs to the model.

A single context suffices to witness inequivalence. At type `Nat → Nat` take the two functions `λx. 0` and `λx. if zero?(x) then 0 else 0`. Every numeral argument gives zero with either operator. Choose as context the application of the hole to a divergent natural term. With the first function the application rule substitutes into the literal zero and immediately returns it. With the second function the guard demands a numeral and has no such derivation. The same ground observation, evaluation to zero, succeeds on one filling and fails on the other.

For an equivalence proof the quantifier goes the other way. If two closed terms have equal denotations, take an arbitrary closing context whose result type is Bool. Compositionality gives equal denotations of the filled programs. Suppose the first filled program returns true. Soundness identifies its denotation as true, hence so too is the denotation of the second. Adequacy turns that equality into a finite evaluation to true in the second program. Interchanging the programs gives the converse implication. Repeat with false or with a numeral in a natural-result context. This argument does not require that the original terms themselves have a ground type. The closing context supplies the observation at which adequacy can be applied.

# A semantic argument with no sequential implementation
%%%
tag := "ch30-s2"
%%%

Let $`U` be the diverging Boolean `fix (λx:Bool. x)`. The following requirements on a curried Boolean function $`f` specify three tests: true on $`\left( {\text{true},\bot} \right)`, true on $`\left( {\bot,\text{true}} \right)`, and false on $`\left( {\text{false},\text{false}} \right)`. Monotonicity forces all three ordinary Boolean pairs containing true to return true. On $`\left( {\text{false},\bot} \right)` the output must lie below both false and true by considering its two refinements, hence is bottom. The symmetric argument gives bottom on $`\left( {\bot,\text{false}} \right)`, and monotonicity then forces bottom on $`\left( {\bot,\bot} \right)`. The tests therefore characterize $`p` completely.

Theorem 40 of the notes establishes that no closed sequential PCF term denotes $`p`. Its operational difficulty is visible in the first two tests: demanding the left argument first loses the second result, demanding the right first loses the first, and returning true without inspecting either fails the third test. This intuition alone would not cover arbitrary higher-order programs and recursion. We use the nondefinability theorem for that general claim.

There is an algebraic way to see the obstruction to defining parallel disjunction. At a flat ground type call a triple of domain elements *related* if its first component is bottom, its second component is bottom, or all three components agree. Applied coordinatewise, a strict unary operation preserves the relation. If one of the first two coordinates is bottom its image remains bottom; otherwise the three inputs agree, so their images agree. A constant preserves the relation by producing an equal triple.

Extend the relation to a function type by requiring that related argument triples yield related result triples. At every type a triple with bottom in either of the first two positions is related, by induction on the result type. Thus conditionals preserve the relation too. A missing first or second guard gives bottom in that result position. Otherwise related guards agree, so all three results come from the same related branch triple. The relation also admits limits of increasing chains. At a ground type, if the first two limit components are ordinary values, both have appeared by some common finite stage. From there the three components agree. At function type use the argument test and pointwise bounds. These facts justify the recursion case by iterating related functionals from related bottoms. Variables, abstraction and application then preserve relatedness by the usual induction on typing.

Now feed two related columns `(true, ⊥, false)` and `(⊥, true, false)` to parallel disjunction coordinatewise. The output is `(true, true, false)`, which violates the ground relation. This supplies a logical-relations explanation of the nondefinability theorem used above.

Here is the finite calculation in Lean. It checks the two input columns and the failed output relation explicitly. Proving that every PCF term preserves the relation still requires the typing induction and limit argument above.

```lean
def parallelBool : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

abbrev coherentTriple (a b c : Option Bool) : Prop :=
  a = none ∨ b = none ∨ (a = b ∧ b = c)

example :
    coherentTriple (some true) none (some false) ∧
    coherentTriple none (some true) (some false) ∧
    ¬ coherentTriple (parallelBool (some true) none)
        (parallelBool none (some true))
        (parallelBool (some false) (some false)) := by decide
```

# Two definable testers
%%%
tag := "ch30-s3"
%%%

For a Boolean literal $`b`, form a closed tester $`T_{b}` that takes $`f` of type Bool to (Bool to Bool). Run the three tests in the order above, supplying the term $`U` for a bottom argument. Implement each test with a conditional. Return $`b` if the first two results are true and the third false. In every other branch evaluate $`U`. If a test itself diverges, the enclosing conditional also diverges. Thus all parts of the tester are definable in PCF.

In the model we may supply $`p` directly to the denotation of either tester. Its three answers pass the tests, so one tester returns true and the other false. The denotations of $`T_{\text{true}}` and $`T_{\text{false}}` are unequal.

Now consider an actual closed argument $`f`. If either tester applied to $`f` returned an ordinary result, all three tests would have passed. Soundness of evaluation would force the denotation of $`f` to satisfy the three equations. Section 30.2 shows that its denotation would be $`p`, contradicting Theorem 40. Both tester applications therefore give the same ground observations for every definable argument. The function extensionality theorem for PCF contextual equivalence (notes, Proposition 39) lifts this pointwise conclusion to all closing contexts. Thus the testers are contextually equivalent. This proves failure of full abstraction for the continuous-function model.

Try two definable arguments to see precisely when a tester stops. For the function always returning true, the first and second applications pass. The third application also returns true; its conditional selects divergence. For a left-to-right disjunction, the first application, on true and the divergent term, passes immediately. The next application must inspect its first argument, so its condition itself diverges. Both runs lack a final Boolean, for different immediate reasons. This illustrates why the proof quantifies over all ways a test can fail or diverge, even though a single success would settle the denotational comparison.

The two testers do return function values when evaluated alone. Their indistinguishability concerns what a closing PCF context can observe after using those values. A context can discard a tester and simply return true. Such a context certainly terminates with either filling. The assertion that both *applications* diverge at every definable argument therefore does not imply that all enclosing programs diverge. The function extensionality result invoked above takes care of contexts that discard, duplicate or pass around the supplied function. It turns agreement in those application experiments into agreement of each pair of filled contexts. The mathematical function `p` provides an additional experiment in the model, and it is precisely this extra experiment that separates the denotations.

# Exercises
%%%
tag := "ch30-s4"
number := false
%%%

1. Compute sequential left-first disjunction on the two tests involving $`U`. Which result differs from parallel disjunction?
2. If the third test were omitted, give a closed PCF argument that would distinguish the modified testers.
3. Why does comparing the testers on $`p` fail to exhibit a distinguishing *program* context?

*Further problem.* A type at which the model is fully abstract. Show that every continuous function from the flat Boolean domain to itself is denoted by a closed PCF term of type `Bool → Bool`. Count these functions. Prove that any two closed terms of that type with different denotations can be distinguished by a closing PCF context. Identify the feature of this proof that fails for the testers in §30.3.

# Reading for the Seminar
%%%
tag := "ch30-s5"
number := false
%%%

*Definitions · 10 minutes.* Complete the parallel disjunction table by ordering flat Boolean values.

*Joint proof · 30 minutes.* Compute the testers’ denotations at the semantic argument $`p`. For a closed source argument, derive a contradiction from any proposed terminating test. Identify both imported theorems.

*Proof review · 20 minutes.* Delete the third test and find a source context that now distinguishes the testers.

*Facilitator’s hint.* Keep two quantifiers visible: all continuous semantic arguments, and all closed source terms of the argument type. Nondefinability tells us exactly why these differ.

# Solutions
%%%
tag := "ch30-s6"
number := false
%%%

*1.* Left-first disjunction returns true on $`\left( {\text{true},U} \right)` without using its second argument. On $`\left( {U,\text{true}} \right)` its first guard never returns. Parallel disjunction returns true in both cases.

*2.* The curried constant-true function ignores both inputs. It passes the first two tests, so the modified testers return their respective Boolean literals on this definable argument.

*3.* An application context must supply an expression of the argument type. Nondefinability excludes any such expression with denotation $`p`. Equality of functions in the domain, in contrast, tests even arguments outside the image of source terms.

*Further problem.* If the function returns an ordinary Boolean at bottom, monotonicity forces that same Boolean at false and true. These two functions are represented by the two constant abstractions, which ignore their arguments. If the function sends bottom to bottom, its values on false and true can independently be bottom, false, or true. Each of the nine resulting strict functions is definable by `λx. if x then t else f`, choosing branches that denote the desired answers, including a diverging Boolean when required. Each assignment of this form is continuous: every increasing chain in the flat input domain stabilizes. There are thus eleven distinct functions.

For two unequal denotations choose an input at which they differ. All three possible input elements are definable by closed Boolean terms. Apply the hole to the chosen term. The two ground denotations differ, so ground soundness and adequacy distinguish the observations, including when one is bottom. Conversely, equality implies contextual equivalence by compositionality and adequacy. The separating argument for the higher-order testers in §30.3 is itself a binary function, and the required parallel disjunction lacks a PCF definition.
