import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Typechecking Annotated Terms" =>
%%%
tag := "ch19"
file := "chapter-19"
%%%

[Chapter PDF](print/chapter-19.pdf) · [Session 21](seminar/index.html#week-21)

The parameter annotation in `(λx:Nat. x) 0` settles a question before the checker visits the body. It tells us what to return at the lookup of $`x`. By following the shape of each term, the checker can either construct its unique type or exhibit a failed premise.

*Sources.* Pierce, _Types and Programming Languages_, chapter 10, especially §10.3, starting p. 115. Identify the cases for variable, abstraction and application in the ML implementation. Our checker uses a named finite map for the context and adds natural and Boolean constants. [Pierce, chapter 10.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Inputs and outputs
%%%
tag := "ch19-s1"
%%%

Types are finite trees formed from Nat, Bool and the binary arrow constructor. Terms are variables, literals `0` and `true`, applications and lambdas with a parameter type. Annotations must themselves be well-formed types. A context maps names to types; an inner binding shadows its outer namesake. An output is either a type or an error. Equality testing on types compares base constructors and recursively compares the domain and codomain of arrows. Distinct base constructors are unequal.

The declarative rules are those of Chapter 18 with the two literal axioms. At an application, the premises must have types $`A\rightarrow B` and $`A` for the same $`A`. The checker below obtains $`A` by visiting the operator.

```
check(Γ, x)       = look up x in Γ, or report an unbound name
check(Γ, 0)       = Nat
check(Γ, true)    = Bool
check(Γ, λx:A.b)  = A → check(Γ[x ↦ A], b)
check(Γ, f a)     = inspect check(Γ, f)
    if it is A → B, require check(Γ, a) = A and return B
    otherwise report an invalid operator
```

Any failing recursive call propagates its error. A failed domain equality reports an argument-type error. Termination follows from recursion on proper subterms and the finite comparison of type trees.

Structural type comparison is needed even when a caller never supplies an explicit type argument. Consider an operator whose parameter annotation is `(Nat→Bool)→Nat`. A suitable operand may itself be an abstraction, so its computed type will be another constructed tree. Comparing merely the outer arrow constructor would accept both `(Nat→Bool)→Nat` and `(Bool→Nat)→Nat`. Descend first into the domains. Both are arrows; descend again to their domains, which are Nat in the first tree and Bool in the second. This single mismatch makes the entire equality false. Equality of the result branches, both Nat, cannot repair it.

An error can consequently be located quite precisely: the checker has already synthesized a type for each subterm, and the first mismatching path in their types points to the premise which cannot be satisfied. This chapter's decidable test depends on its type grammar. With aliases that abbreviate other types, an implementation would need a specified policy for expansion before comparison. With subtyping, the application premise itself changes. The exact structural equality described here is justified by the current typing rules and by the absence of such additional equations or conversion rules.

# A trace and its derivation
%%%
tag := "ch19-s2"
%%%

Start with the empty context. In the operator `λx:Nat. x`, the recursive body call sees $`x:\text{Nat}` and returns Nat. Abstraction returns

$$`\text{Nat}\rightarrow\text{Nat}`

. The literal argument returns Nat. The domain comparison succeeds, so the entire application returns Nat.

Read the same computation from the leaves as a proof. The variable premise under $`x:\text{Nat}` yields $`x:\text{Nat}`. Discharge that assumption using abstraction to type the operator. Use the zero axiom under the empty context to type the operand, then combine these two premises using application. This reconstruction explains what the returned type certifies.

Trace a term containing a genuinely free name before closing it with a lambda. In the context `u:Bool`, check `(λk:Bool→Nat. k u) (λz:Bool. 0)`. On the operator side, the checker extends the context with `k:Bool→Nat`. The inner application requires two successful lookups. The operator lookup returns `Bool→Nat`; the lookup of `u` returns Bool from the outer context. Their domain comparison succeeds, so the body returns Nat. Discharging the parameter makes the outer operator's synthesized type `(Bool→Nat)→Nat`.

The right operand is checked in the original context containing `u`. Under the local binding `z:Bool`, the zero literal synthesizes Nat. The lambda therefore synthesizes `Bool→Nat`, which matches the outer operator's domain exactly. The complete expression receives Nat. Replacing the inner operand `u` by the literal zero would instead fail the *inner* comparison, before an outer operator type could be returned. Drawing the derivation tree makes the difference between these two application nodes visible. Writing down only the final error message would hide the scope in which the failed type equality was required.

This executable fragment uses a list of parameter types as a context. Variable zero names the most recent binder. The checker either returns a type or returns `none` for an absent binding, a nonfunction operator, or an incompatible operand. The examples exercise the application and lookup branches, including an operator whose result differs from its domain.

```lean
namespace CheckingTerms
inductive Ty where
  | nat | bool | arr (a b : Ty)
  deriving DecidableEq

inductive Exp where
  | var (i : Nat) | zero | yes | lam (a : Ty) (body : Exp) | app (f x : Exp)

def check (Γ : List Ty) : Exp → Option Ty
  | .var i => Γ[i]?
  | .zero => some .nat
  | .yes => some .bool
  | .lam a body => (check (a :: Γ) body).map (.arr a)
  | .app f x => do
    let .arr a b ← check Γ f | none
    let c ← check Γ x
    if a = c then some b else none

example : check [] (.app (.lam .nat .yes) .zero) = some .bool := rfl
example : check [] (.app (.lam .nat .yes) .yes) = none := rfl
example : check [] (.lam .nat (.lam .bool (.var 1))) =
    some (.arr .nat (.arr .bool .nat)) := rfl
end CheckingTerms
```

# Correctness of the checker
%%%
tag := "ch19-s3"
%%%

*Theorem 21.1.* For every well-formed input context and term, the checker returns $`T` exactly when $`\Gamma \vdash t:T`. For soundness induct on the term with a successful output. Variable success means the lookup premise holds, and each literal return matches its axiom. At abstraction, recursive success types the body at the returned codomain in the extended context. Discharge the binding. At application success entails an operator return $`A\rightarrow T` and an argument return $`A`. By induction these are precisely the premises of application.

For completeness induct on the typing derivation. A variable lookup or literal axiom determines the same output. For abstraction the induction hypothesis computes the body’s type, so the checker constructs the conclusion arrow. In an application derivation its two premises already fix results $`A\rightarrow T` and $`A`; by induction both recursive calls return these types. Structural equality therefore succeeds and the result is $`T`. As a consequence a reported error entails that there is no typing derivation, and two derivations for the same inputs have the same result type. Both conclusions rely on having only the rules listed in §21.1.

One useful consequence of the equivalence is a principled account of negative answers. Suppose the checker rejects `f a` because it computes Nat for `f`. Assume for contradiction there is a typing derivation of the whole application. Its last rule supplies some types `A,B` and a premise typing `f` at `A→B`. Completeness applied to that premise says the same checker call returns `A→B`. A deterministic computation on a fixed input cannot return both Nat and an arrow, so the assumed derivation is impossible. This argument needs completeness: soundness alone would only explain why already accepted inputs have derivations.

Conversely, returning an arbitrary accepted type at every leaf could make a checker permissive while destroying soundness. At an abstraction one can see precisely what the soundness hypothesis must quantify over. The recursive body call runs under an extended context. Therefore structural induction on terms should keep the context and claimed output universally quantified. Fixing an empty context before induction would produce a body hypothesis about an input the algorithm never uses. The annotation at the lambda determines the extension, and the generalized hypothesis then turns that particular successful call into the body typing needed by the abstraction rule.

# Exercises
%%%
tag := "ch19-s4"
number := false
%%%

1. Trace `(λx:Nat. x) true` through the first failing test. Can a different final typing rule save it?
2. Determine the type of `λx:Nat. λx:Bool. x`. Which context is needed for the innermost lookup?
3. Extend the checker to the conditional of Chapter 17. Which induction hypotheses suffice for soundness in the new case?

*Further problem.* Suppose a checker for the annotated fragment returns the operator's *domain* whenever an application's domain comparison succeeds. Find a closed term on which it returns an incorrect type. Would tests using only applications of identity functions find the error?

# Reading for the Seminar
%%%
tag := "ch19-s5"
number := false
%%%

*Session 21 · With Chapter 22.* Start with `(λx:Nat. x) 0`. Under the binder, lookup gives the body type Nat. The abstraction therefore has type Nat → Nat, and the argument has precisely its domain type. Write the three typing rules beside the corresponding checker calls. Spend the first 20 minutes on this annotated term, then continue with the same syntax after erasing its annotation in Chapter 22.

# Solutions
%%%
tag := "ch19-s6"
number := false
%%%

*1.* The operator returns Nat to Nat. The argument returns Bool, so comparison with Nat fails. Only application could type the whole syntax; its premises cannot be obtained at a common domain.

*2.* The innermost lookup sees Bool. The result type is Nat to (Bool to Bool). The two assumptions can equivalently be given distinct fresh binder names.

*3.* Require the guard call to return Bool, compute both branch types, and return their common type when equal. The three induction hypotheses supply the guard derivation at Bool and both branch derivations at that common type.

*Further problem.* Use `(λx:Nat. true) 0`. Under `x:Nat` the checker returns Bool for the body, hence `Nat→Bool` for the abstraction. It returns Nat for the literal zero. Domain comparison succeeds, but the faulty rule now returns Nat. Inverting any declarative application typing instead requires an operator type `C→T` and an operand type `C`. Inverting the abstraction fixes `C` at Nat from the annotation and `T` at Bool from the body. The alleged typing at Nat is therefore impossible. This is a failure of soundness for accepted type *assignments* even though acceptance of this particular term at some type was appropriate. An identity application always has an operator type of the shape `A→A`. Both the correct and defective return choices then equal `A`, irrespective of how elaborate the type `A` itself is. A test needs differing domains and codomains to separate those two implementations.
