import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Computational Adequacy" =>
%%%
tag := "ch29"
file := "chapter-29"
%%%

[Chapter PDF](print/chapter-29.pdf) · [Session 29](seminar/index.html#week-29) · [Session 30](seminar/index.html#week-30)

The denotation of a closed PCF term can be calculated without producing an evaluation tree. If the result of that calculation is the number two, what warrants the prediction that evaluation actually returns two? For PCF the justification uses a relation between semantic objects and terms, with a different clause at each type.

*Sources.* Cambridge _Denotational Semantics_, lectures 5–6. In the notes read Definition 27 (formal approximation), Theorem 30 (fundamental property) and Theorem 31 (adequacy), pp. 56–58. The joint proof derives Theorem 31 from the fundamental property. The general induction is illustrated here by application, abstraction and recursion. [Lectures.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/materials.html) [Notes.](https://www.cl.cam.ac.uk/teaching/2526/DenotSem/DenSem-Notes.pdf)

In §26.4 both sides of the arrow relation were values from two interpretations. Here its left side is a domain element and its right side a closed PCF term. The application argument still uses related inputs. Recursion now requires closure under limits for a fixed term.

# Ground observations
%%%
tag := "ch29-s1"
%%%

Write $`D_{A}` for the semantic domain of type $`A` and $`M(t)` for a closed term’s denotation. The ground natural domain contains bottom and each natural number. The syntax contains a numeral for each ordinary number $`n`; write $`\overline{n}` for this term. The evaluation judgment $`t \Downarrow \overline{n}` asserts that a finite evaluation tree exists. Soundness of evaluation gives the direction from that tree to the equality $`M(t) = n`; one proves it by induction on evaluation. Adequacy supplies the reverse direction at ground types.

For a closed term $`t:A` define $`d\, R_{A}\, t` by recursion on $`A`. At Nat require that for each natural $`n`, $`d = n` implies $`t \Downarrow \overline{n}`. At Bool require the corresponding implications for true and false. At an arrow $`A\rightarrow B`, relate $`f` to $`t` if for each $`a \in D_{A}` and closed $`u:A` with $`a\, R_{A}\, u`, one has $`f(a)\, R_{B}\,\left( {t\, u} \right)`. Ground bottom is related to every ground term because it asserts no ordinary result. At arrow type a function is tested on all *related pairs*. The semantic argument need not be the exact denotation of the supplied term.

For a concrete arrow-clause calculation, take the semantic identity `i` on the flat naturals and the term `I = λx:Nat. x`. Fix a semantic argument `a` and a closed operand `u` related at Nat. There are two possibilities. If `a` is a numeral `n`, the premise gives a finite derivation that `u` evaluates to the numeral for `n`. The application rule reuses that derivation for the body after substitution, giving a derivation that `I u` evaluates to the same numeral. This is the required ground relation for `i(a) = n`. If `a` is bottom, so is `i(a)`, and the result relation has no numeral obligation. In particular, a perfectly terminating term such as the numeral five can occur in a related pair whose semantic component is bottom.

Try the same argument for the semantic constant-one function and the syntactic identity. Choose `a = 2` and `u` the numeral two. The arrow clause would demand that `I u` return one. Inverting the application and numeral rules shows that its only result is two, so this pair of functions is unrelated. One failing argument test refutes the proposed relation. Establishing it requires treating an arbitrary related input pair.

# The fundamental property
%%%
tag := "ch29-s2"
%%%

Given a typing context $`\Gamma`, choose a semantic environment $`\rho` and a simultaneous substitution $`s` assigning a closed term of the proper type to each variable. They are related if $`\rho(x)\, R_{A}\, s(x)` at each entry $`x:A`. The fundamental property says that for every $`\Gamma \vdash t:B` and every such pair, $`M(t)(\rho)\, R_{B}\, t\lbrack s\rbrack`, where here $`M(t)` denotes the interpretation of an open term as a function of its environment.

At a variable this is the environment hypothesis. At application the induction hypotheses relate the operator and operand separately. Instantiating the operator’s arrow clause with the related operand gives exactly the desired result. At abstraction take any related argument pair $`a,u`. Extend $`\rho` and $`s` by this pair. The body hypothesis gives the result relation for the body with $`u` substituted. The call-by-name beta rule transfers this relation to the application of the abstraction to $`u`. At ground result type this transfer uses one more evaluation rule; at function result type test against further related arguments.

For recursion fix a closed instantiated operator term $`h` and its related semantic function $`F`. Use Scott induction with the predicate that $`d` is related to `fix h`. Bottom satisfies it by induction on result type. For a fixed term, related semantic elements are chain-closed: at a flat ground type a nonbottom result of the limit appears at a finite stage, and at a function type the argument test reduces closure to closure at the result type. If $`d` is related to `fix h`, the arrow clause for $`F` relates $`F(d)` to `h (fix h)`. The unfolding evaluation rule transfers this back to `fix h`, establishing the induction step. The course notes give the full compatibility proof for all PCF constructs.

Consider the open judgment with `f : A → B` and `x : A` and body `f x`. Fix related environments. Write `F = ρ(f)`, `a = ρ(x)`, `h = s(f)` and `u = s(x)`. The variable cases give `F R h` at the arrow type and `a R u` at the input type. Expanding the first relation introduces a universal quantifier over a semantic value and a closed term, followed by an implication. Instantiate these variables with `a` and `u`, and discharge its premise with the second relation. Its conclusion is `F(a) R (h u)` at type B. The left side is exactly the denotation of the application in `ρ`, and the right side is exactly the application after simultaneous substitution. No equality between `a` and the denotation of `u` is needed.

For the recursion case let `t = fix h` and write `a₀ = ⊥` and `aₙ₊₁ = F(aₙ)`. The induction assertion relates *each* `aₙ` to the *same* term `t`. From `aₙ R t` the arrow clause yields `F(aₙ) R (h t)`. A finite evaluation of `h t` can be made into one of `t` by adjoining the fix rule as its root. The evaluation-transfer lemma (Cambridge Lemma 35) therefore gives `aₙ₊₁ R t`. Finally the related elements for this fixed term are chain-closed (Lemma 33). At an arrow result, fix an arbitrary related input pair `e,u`. The chain evaluated at `e` is related stage by stage to the *single* term `t u`. Closure at its smaller result type and the pointwise formula for function bounds establish the required arrow clause at the limit. This is why allowing the term to change with the stage would break the argument.

# Adequacy at ground type
%%%
tag := "ch29-s3"
%%%

*Theorem 29.1.* Given a closed term $`t:\text{Nat}` and natural $`n`, if $`M(t) = n`, then $`t \Downarrow \overline{n}`. With an empty context there is a unique empty environment and substitution. Their relatedness is vacuous, so the fundamental property gives $`M(t)\, R_{\text{Nat}}\, t`. Replace the left component by $`n`. The defining ground implication now requires exactly $`t \Downarrow \overline{n}`. The Boolean argument has two possible ordinary results and uses the matching implication.

For $`K\, 1` in Chapter 28 the pointwise chain computation supplies the hypothesis at $`n = 0`. Adequacy turns that calculation into existence of an evaluation derivation. In that example we can also display the derivation explicitly, which provides a check on both accounts.

One can now classify exactly which semantic calculation warrants a conclusion about execution. Suppose the input to a semantic calculation is the closed term `t` of type Nat. If a finite approximation at some stage already reports three and the approximations increase in the flat order toward `M(t)`, every later stage and the limit also report three. Adequacy then supplies a finite derivation ending at the numeral three. This is an existence result. It gives no equality between the stage number at which a particular algorithm first discovers three and the number of inference rules in the derivation.

If the first hundred stages report bottom, no such conclusion follows. Increasing chains permit an ordinary value first to appear at stage one hundred and one. On the other hand, suppose we have proved by some independent argument that the *limit* is bottom. A hypothetical derivation to any numeral would, by soundness, identify this bottom with an ordinary natural number. Since those are distinct elements of the flat domain, no numeral derivation exists. The proof for a bottom limit therefore uses soundness in the opposite direction of the adequacy argument for an ordinary result. This distinction matters when finite approximations are computed mechanically and only the first few can be inspected.

The short proof below checks the final logical step at Nat independently of the language's implementation. The parameter `selfRelated` is the Nat instance of the fundamental property for closed terms. Supplying this parameter for PCF is precisely the mathematical work of §29.2. Bottom is represented by `none`.

```lean
def natApprox {Tm : Type} (evaluates : Tm → Nat → Prop)
    (d : Option Nat) (t : Tm) : Prop :=
  ∀ n, d = some n → evaluates t n

example {Tm : Type} (meaning : Tm → Option Nat)
    (evaluates : Tm → Nat → Prop)
    (sound : ∀ t n, evaluates t n → meaning t = some n)
    (selfRelated : ∀ t, natApprox evaluates (meaning t) t)
    (t : Tm) (n : Nat) : meaning t = some n ↔ evaluates t n :=
  ⟨selfRelated t n, sound t n⟩
```

# Exercises
%%%
tag := "ch29-s4"
number := false
%%%

1. If $`M(t) = \bot` at Nat, does the relation alone imply divergence? What additional theorem rules out a terminating natural result?
2. Show at type $`A\rightarrow B` why the bottom function is related to every closed term at that type.
3. A closed lambda may fail to terminate on some arguments. Explain why a proof that merely classifies a term as a lambda cannot establish the arrow clause.

*Further problem.* Downward closure. Fix a closed term `t : A`. Show that whenever `d R_A t` and `d′ ⊑ d`, then `d′ R_A t`. In the arrow case make explicit which expression stays fixed as you move down in the domain. Use the lemma to construct an example of a related pair `a R_Nat u` for which `a` differs from the denotation of `u`.

# Reading for the Seminar
%%%
tag := "ch29-s5"
number := false
%%%

*Session 29 · The application case.* Read §§29.1–29.2. State what it means for a semantic function and a closed function term to be related. For the open term `f x`, put the related operator pair and the related operand pair on separate lines. Instantiate the arrow clause with the operand pair to obtain the relation for the application. Check which step would be unavailable if the relation were defined only at ground types.

*Session 30 · Adequacy at Nat.* Read §§29.2–29.3. Spend the first half of the proof on fix: keep the term fixed, use Lemma 35 to transfer evaluation after unfolding, then use closure under chain suprema (Lemma 33). Spend the second half instantiating the resulting fundamental property. For a closed term, choose the empty environment and substitution. If its denotation is a number, use the ground clause to derive an evaluation returning the corresponding numeral. Apply this argument to Chapter 28’s countdown. Finish by asking how a closing context can observe a function; Chapter 30 takes up that question.

# Solutions
%%%
tag := "ch29-s6"
number := false
%%%

*1.* The relation at bottom places no obligation on $`t`. If $`t` did return a numeral, soundness of evaluation would force its denotation to equal that ordinary number, contradicting bottom.

*2.* For any related argument pair the bottom function returns bottom at $`B`. The induction hypothesis on $`B` relates this bottom to the closed application term. This meets the arrow clause.

*3.* That clause quantifies over related inputs and constrains the observed results of applications. For example the constant-zero function and a function that inspects a diverging argument may both be written as lambdas while behaving differently on that argument.

*Further problem.* Induct on the structure of `A`. At either ground type, if `d′` is bottom, its relation to `t` follows from the defining implication, whose antecedent is false for every ordinary value. Otherwise `d′` is an ordinary value. Flatness and `d′ ⊑ d` force equality, so the given relation for `d` suffices.

At type `B → C` write `f′ ⊑ f` and assume `f R t`. Choose an arbitrary related input pair `b R_B v`. The arrow clause applied to `f` gives `f(b) R_C (t v)`. Pointwise order supplies `f′(b) ⊑ f(b)`. Apply the induction hypothesis at `C` to that inequality and the *same closed application* `t v` to obtain `f′(b) R_C (t v)`. This supplies the required arrow clause for `f′`. The input pair stays fixed throughout.

For an example take `u` to be the numeral two. The value two is related to this numeral by its evaluation rule. Since bottom is below two, downward closure relates bottom to this same term even though the term denotes two.
