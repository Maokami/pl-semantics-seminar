import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Progress and Preservation for Functions" =>
%%%
tag := "ch18"
file := "chapter-18"
%%%

[Chapter PDF](print/chapter-18.pdf) · [Session 19](seminar/index.html#week-19)

The application of a function to a value disappears in a single beta step. Before that step its type follows from an application rule. Afterwards the result may be a variable, another application, or an abstraction. The substitution theorem lets us transport a typing derivation across this change of syntax.

*Sources.* Pierce, _Types and Programming Languages_, §9.3, pp. 104–107. Use the substitution result of Chapter 18. The shared proof is preservation for beta reduction, followed by progress at application. [Pierce, properties of typing.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# The closed call-by-value calculus
%%%
tag := "ch18-s1"
%%%

Use Chapter 18’s variables, annotated abstractions and applications. Include a base type Unit and a constant `unit` with that type. A value is the unit constant or an abstraction. A term is closed if it has no free variables. The expression $`\Gamma \vdash t:T` has the typing rules of Chapter 18. The empty context is written $`\varnothing`.

The evaluation rules are weak and left-to-right as in Chapter 15. A step under the operator of an application always propagates. When the operator is a value a step of the argument propagates. Finally $`\left( {\lambda x:A.b} \right)\, v\rightarrow b\left\lbrack {v/x} \right\rbrack` for a value $`v`. An abstraction does not step under its binder. The typing rules inspect the body even though evaluation stops at an abstraction.

*Inversion for applications.* Any derivation typing $`f\, a` at $`T` ends with application, since every other rule has another outer constructor. Its premises therefore give some $`A` with $`f:A\rightarrow T` and $`a:A` in the same context. A derivation of $`\lambda x:A.b` at $`A\rightarrow T` in turn has a body premise at $`T` under $`x:A`. Function types are syntax trees, so equality of two arrow types gives equality of their domains and of their codomains.

A typing derivation can inspect code that evaluation never reaches. Let the operator be `λf:Unit→Unit. unit`, and try supplying `λz:Unit. z unit`. Both expressions are values according to weak evaluation. The untyped beta rule could therefore return unit immediately. Typing the operand, however, first requires a derivation for `z unit` under `z:Unit`. Inversion of application demands an arrow type for `z`, whereas the only possible lookup returns Unit. The operand fails before any comparison of the two sides of the outer application. The typing derivation must account for the delayed body even when this particular caller discards it.

Now replace the operand with `λz:Unit. z`. Its body has a one-leaf typing derivation, and abstraction yields precisely the domain required by the operator. The two applications have the same immediate dynamic result, but only the latter falls within the hypothesis of type safety. This shows the direction of the guarantee: a successful derivation rules out a reachable stuck term. One successful execution on concrete inputs is insufficient evidence for typability, because other paths through the syntax may still have impossible premises.

# Preservation
%%%
tag := "ch18-s2"
%%%

*Theorem 19.1.* If $`\Gamma \vdash t:T` and $`t\rightarrow t'`, then $`\Gamma \vdash t':T`. Induct on the step derivation, considering any typing of its source.

In an operator step invert the application typing to obtain $`f:A\rightarrow T` and $`a:A`. Apply the induction hypothesis at the *function* type to type the new operator. Reuse the old argument typing and rebuild application. In an operand step the operator retains its type and the induction hypothesis now applies at the *domain* type. Rebuilding yields the same result type.

For beta, invert the source typing twice. The outer inversion supplies an argument type $`C`, an abstraction typing at $`C\rightarrow T`, and a typing for $`v:C`. The abstraction inversion identifies $`C = A` and types $`b:T` in $`\Gamma,x:A`, renaming $`x` fresh as needed. Substitute $`v` by Theorem 18.2 to obtain $`\Gamma \vdash b\left\lbrack {v/x} \right\rbrack:T`, exactly the target typing. The value restriction chooses when reduction is allowed. The substitution theorem itself also accepts well-typed arguments that are still computations.

For a beta step whose result is itself an abstraction, take `(λf:Unit→Unit. λy:Unit. f y) (λz:Unit. z)`. Its result type is `Unit→Unit`. Recover the particular premises needed for substitution. The left-hand abstraction was typed by first deriving $`f:\mathrm{Unit}\to\mathrm{Unit} \vdash \lambda y:\mathrm{Unit}.\,f\,y : \mathrm{Unit}\to\mathrm{Unit}`. The right-hand abstraction has a derivation in the empty context at `Unit→Unit`. In the substitution theorem of Chapter 18, set the distinguished variable to `f`, the parameter type to `Unit→Unit`, the source term to `λy:Unit. f y`, and the replacement to `λz:Unit. z`. Its conclusion types `λy:Unit. (λz:Unit. z) y` in the empty context at the original result type. Descending through the binder `y` uses the weakening established in that chapter.

The resulting expression is already a value in this weak semantics. Its body contains a redex which will become available when a caller supplies an argument. Preservation relates the types across the one step just taken, irrespective of whether the result is canonical or contains further redexes. A proof appealing to equality of the printed source and target syntax would fail even on this example, since substitution introduced an application beneath the result's lambda.

# Progress
%%%
tag := "ch18-s3"
%%%

*Canonical forms for arrows.* A closed value typed at $`A\rightarrow B` is an abstraction. Inspect the two value forms. The constant has only type Unit; an abstraction is the sole remaining form.

*Theorem 19.2.* If $`\varnothing \vdash t:T`, then $`t` is a value or $`t` takes a step. Induct on typing, restricted to closed inputs. Variables cannot be typed by lookup in the empty context. Unit and lambda are values. For an application $`f\, a`, first use progress on $`f`. An operator step lifts. Otherwise $`f` has arrow type by inversion and is a value, so canonical forms makes it an abstraction. Now use progress on $`a`. A step of $`a` lifts, and a value $`a` enables beta. The source is closed, so the subterms of an application are closed, as required. No induction hypothesis on the open body of an abstraction is used.

Together, the theorems exclude reaching a stuck term in finitely many steps from a well-typed closed term. Apply preservation along the prefix and progress at its end. Proving that every evaluation is finite would require an additional argument.

Exactly where does the empty context enter the application proof? At the top application the operator and operand both inherit the typing context unchanged. When it is empty we can invoke closed progress on either typing premise. Inside an abstraction the premise has a new variable assumption, so it cannot receive the same hypothesis. Since the outer abstraction is already a value, that recursive result is unnecessary. Thus a formal induction proof can generalize the context and state that progress follows *if the context is empty*. This produces an impossible equality with the empty map when it encounters a supposed variable lookup.

To see what fails when the hypothesis is weakened to an arbitrary well-formed context, give `f` type `Unit→Unit` and consider `f unit`. Its typing derivation is complete, yet its operator cannot take a step and cannot be recognized as an abstraction. Filling the environment by a closed substitution assigning `λz:Unit. z` to `f` changes the question. The closed instance can now reduce to unit. Thus it would also be possible to formulate progress for closed *instances* of open typed terms. That formulation requires evidence associating each free name with a suitable closed term.

We can factor the final safety argument away from the syntax. Fix a type and let the predicate `Typed` mean closed typing at that type. A finite execution is either empty or one step followed by a finite execution. The Lean proof carries typing across its first step before invoking induction on the remaining steps. Only at the endpoint does it use progress. Instantiating the two hypotheses with this chapter's theorems gives safety for this calculus.

```lean
namespace SafePrefixes
inductive Runs {α : Type} (step : α → α → Prop) : α → α → Prop where
  | refl (a) : Runs step a a
  | cons {a b c} : step a b → Runs step b c → Runs step a c

theorem endpoint {α : Type} {step : α → α → Prop}
    {Typed Value : α → Prop}
    (pres : ∀ {a b}, Typed a → step a b → Typed b)
    (prog : ∀ {a}, Typed a → Value a ∨ ∃ b, step a b)
    {a b} (path : Runs step a b) (start : Typed a) :
    Value b ∨ ∃ c, step b c := by
  induction path with
  | refl => exact prog start
  | cons first _ ih => exact ih (pres start first)
end SafePrefixes
```

*Safety and normalization.* In the pure simply typed language without general recursion, every closed well-typed term evaluates to a value. This normalization result requires an additional proof (Pierce §12.1). Progress supplies a next step for a nonvalue, and preservation lets the next state take another step; neither bounds the number of steps. In Chapter 28 we will add a typed fixed-point operator and see precisely which conclusion fails.

# Exercises
%%%
tag := "ch18-s4"
number := false
%%%

1. Assign a type to `(λf:Unit→Unit. f unit) (λz:Unit. z)` and derive both reductions. State the result type after each step.
2. Give an open well-typed application that is not a value and cannot step. Identify the precise use of closedness it evades.
3. If a new constant `bad` of type $`A\rightarrow B` were declared a value with no application rule, which line of progress would fail?

*Further problem.* Extend the language with a closed constant `loop:Unit`. Keep the original values and add `loop → loop`. Check preservation and progress, then give a closed, well-typed application whose unique evaluation runs forever under the left-to-right call-by-value rules.

# Reading for the Seminar
%%%
tag := "ch18-s5"
number := false
%%%

*Definitions · 10 minutes.* Copy the operational beta rule and the two relevant typing rules. Keep the rule conclusions visible.

*Joint proof · 30 minutes.* Start from the typing of a beta redex at an unknown result type. Recover two premises, identify its domain, and instantiate Theorem 18.2 explicitly.

*Proof review · 20 minutes.* Prove progress for an application. As a test of the conclusion, add a well-typed constant whose sole step is to itself. Does preservation still hold? Does evaluation terminate?

*Facilitator’s hint.* Ask which theorem provides a typing for the *substituted body*. Inversion only types the original body under an extra assumption.

# Solutions
%%%
tag := "ch18-s6"
number := false
%%%

*1.* The argument has type Unit to Unit, and the operator takes such a function and returns Unit. The first step gives `(λz:Unit. z) unit`, the second gives `unit`. Each whole term has type Unit.

*2.* In a context containing $`f:\text{Unit}\rightarrow\text{Unit}` the term `f unit` has type Unit. Its free operator is neither a value nor reducible. Closed progress would have excluded the operator variable case.

*3.* The canonical forms lemma for arrows is now false. Applying `bad` to a closed value of its domain gives a well-typed stuck term whenever such a value exists.

*Further problem.* The constant's only typing assigns Unit, and the target of its new rule is the very same term, so its typing derivation can be reused. The two application congruence cases still rebuild the typing from their induction hypotheses. The beta case still follows from substitution; adding the constant gives substitution one more immediate case since it contains no variables. For progress the new typing case supplies the displayed self-step. The constant is a nonvalue, so canonical forms for closed values of arrow type is unchanged. Take `(λu:Unit. unit) loop`. The body constant has type Unit in the extended context, hence the operator has type `Unit→Unit`; the operand has type Unit and application yields Unit. The sole eligible step evaluates the operand, leaving the same application. Induction on the length of any finite execution shows the program is still that nonvalue application at its end. Thus all of these preservation and progress checks are compatible with divergence.
