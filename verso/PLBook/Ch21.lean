import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Let-Polymorphism" =>
%%%
tag := "ch21"
file := "chapter-21"
%%%

[Chapter PDF](print/chapter-21.pdf) · [Session 22](seminar/index.html#week-22)

The identity can accept an integer in one expression and a Boolean in another. In `let id = λx. x in (id 0, id true)`, both calls occur in the same expression. If they share a single unknown parameter type, one call forces it to Nat and the other to Bool. A let-bound type scheme makes the two choices independent.

*Sources.* Pierce, _Types and Programming Languages_, §22.7, pp. 331–335. Track which variables may be generalized at a let and where fresh copies are introduced. This chapter treats a pure language; Chapter 31 revisits the rule after allocation. [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Schemes and instances
%%%
tag := "ch21-s1"
%%%

Use the finite monotypes of Chapter 20 and product types $`A \times B`. A pair has product type when its components have the indicated types. A *scheme* has the form $`\forall\alpha_{1}\ldots\alpha_{n}.T`, where $`T` is a monotype. An instance replaces the quantified variables simultaneously by monotypes, using the same replacement for every occurrence of a given variable. Free variables of the scheme remain shared with its environment. Quantifiers occur only at the front of a type scheme. A let binding can introduce such a scheme, while a lambda-bound parameter has a monotype.

A context maps names to schemes. A monotype in the context abbreviates the scheme with no quantifiers. On lookup instantiate every quantified variable with a fresh unknown, to be solved by the constraints of this occurrence. Lambda-bound parameters are entered with no quantifiers. At a pure nonrecursive let, infer and solve the right-hand side first. Apply its solution to both the context and the right-side type. Call the results $`\Gamma'` and $`T`. Generalize precisely the variables

$$`F(T) \smallsetminus F\left( \Gamma' \right),`

where $`F` takes the free type variables and forms their union over context entries. Enter the resulting scheme under the let name while inferring the body. Solving the context first ensures that any information discovered about the surrounding bindings is respected.

The placement of a quantifier changes what information is shared. Suppose the context contains a free type variable `δ` and a binding of `choose` at the scheme `∀α. α → (α × δ)`. One lookup may instantiate this scheme at Nat, yielding `Nat → (Nat × δ)`. Another may instantiate it at Bool, yielding `Bool → (Bool × δ)`. Within the first occurrence, the argument and the first component of the result must use exactly the same replacement Nat. Across both occurrences, the second component still uses the one external `δ`. Renaming `α` consistently to a fresh quantified symbol preserves these constraints, while changing `δ` in just one occurrence would change the assumptions supplied by the surrounding scope.

This distinction explains the two traversals implicit in generalization. Look first through the solved result type to find candidates for quantification. Then look through every scheme already present in the solved context, carefully ignoring names bound by those schemes. An unknown free in both places records a dependency on an outer assumption. Binding that unknown in a new scheme would sever the dependency while keeping the same printed body type. Free-variable computation over types and schemes plays the same protective role here that free-variable computation over lambda terms played in Chapter 13.

The following small scheme language has exactly one quantified slot, any number of unquantified names, arrows and products. Instantiation copies the supplied type at each use of that slot and keeps every outside name fixed. The two checked instances of the same scheme display both properties. Choosing arguments supplied by the caller here models explicit instances of a scheme; the inference algorithm may initially use fresh unknowns for these arguments.

```lean
namespace SchemeScope
inductive Mono where
  | name (i : Nat) | nat | bool | arr (a b : Mono) | prod (a b : Mono)
inductive Pattern where
  | slot | outside (i : Nat) | arr (a b : Pattern) | prod (a b : Pattern)

def inst (arg : Mono) : Pattern → Mono
  | .slot => arg
  | .outside i => .name i
  | .arr a b => .arr (inst arg a) (inst arg b)
  | .prod a b => .prod (inst arg a) (inst arg b)

def scheme := Pattern.arr .slot (.prod .slot (.outside 0))
example : inst .nat scheme = .arr .nat (.prod .nat (.name 0)) := rfl
example : inst .bool scheme = .arr .bool (.prod .bool (.name 0)) := rfl
end SchemeScope
```

# A derivation using two instances
%%%
tag := "ch21-s2"
%%%

In the empty context `λx. x` has provisional type $`\alpha\rightarrow\alpha` with no constraints. Its free variable can therefore be generalized. Bind `id` at $`\forall\alpha.\alpha\rightarrow\alpha`. The left lookup in the pair yields $`\beta\rightarrow\beta` and the right one yields $`\gamma\rightarrow\gamma`, with distinct unknowns. At `id 0` the application equation forces $`\beta = \text{Nat}` and the result is Nat. At `id true` it forces $`\gamma = \text{Bool}` and the result is Bool. Pair introduction yields $`\text{Nat} \times \text{Bool}`. At runtime the two lookups use the same pure function; instantiation is part of typing.

Under a single lambda binder in `λid. (id 0, id true)`, the two lookups share one monotype. It must equal both an arrow with domain Nat and an arrow with domain Bool. Unification of the domains fails. In this type system replacing a let by application of an unannotated lambda can change typability even when the two pure programs compute alike.

A useful intermediate example is to name an application of the identity to itself. In `let id = λx. x in let h = id id in (h 0, h true)`, the two occurrences in `id id` are separate lookups. Let their types be `α→α` and `β→β` respectively. The application equation is `α→α = (β→β)→γ`. Its most general solution sets `α = β→β` and `γ = β→β`. Thus the right-hand side for `h` has type `β→β`. The prior context gives `id` a closed scheme, so `β` is not free in that context. Generalization at the inner let gives `h` a scheme that admits both calls.

No argument in this derivation has a quantified monotype. The argument occurrence of `id` was instantiated before application, and `β→β` is an ordinary monotype containing an unresolved variable. This explains why `id id` succeeds although the monomorphic self-application `λx. x x` has no finite simple type. In the latter term both occurrences look up the very same monotype and force it to be its own function domain. At the let-bound name each occurrence instead receives a new instance of the same scheme.

# Why environment variables stay free
%%%
tag := "ch21-s3"
%%%

Consider `λy. let k = λx. y in (k 0, k true)`. Give $`y` the unknown type $`\delta`. The inner abstraction has type $`\alpha\rightarrow\delta`. The context contains free $`\delta`, so the scheme for $`k` quantifies only $`\alpha`. The argument type can vary at the two calls; both results have the same type as $`y`. The whole term has type $`\delta\rightarrow\left( {\delta \times \delta} \right)`.

If we generalized $`\delta` at the let, a caller could demand a Boolean result independently of the actual $`y`. For example imagine `λy. let k = λx. y in if k 0 then 1 else 2` applied to the number 7, using natural literals and the conditional from Chapter 16. The erroneous rule would accept this program by instantiating the local result type at Bool. Execution reaches a conditional with numeric guard 7. The correct rule propagates the Bool requirement back to $`y`, thereby rejecting the final application to 7.

Solving the context before generalization matters when an outer type variable acquires new structure during inference. Consider `λf. let h = λx. f x in (h 0, h true)`. Give the lambda-bound `f` one unknown type `δ`. In the definition of `h`, give `x` type `α` and its application result type `β`. Solving that application forces `δ = α→β`. The solved right-hand side therefore has type `α→β`, and the solved context now contains `f:α→β`.

Generalization must inspect that updated entry. Both `α` and `β` occur free in it, so neither can be generalized at `h`. The first call requires `α=Nat` and the second requires `α=Bool`; the constraints conflict. Computing context free variables from the *original* entry `f:δ` would miss both dependencies and could wrongly accept the pair. Operationally the function bound to `h` simply forwards its argument to the one supplied `f`. There is no opportunity in either call to replace that outer monomorphic function with a freshly chosen one. The solved context records exactly that fact before the body of the let is checked.

# Exercises
%%%
tag := "ch21-s4"
number := false
%%%

1. In the two-call example, instantiate the scheme twice but accidentally give both lookups the same fresh variable. Identify the contradictory equations.
2. Give the scheme for `λx. (x,y)` when $`y:\delta` is in the context. Can the two components change type independently when the bound function is reused?
3. Show why a result equal to the actual value of $`y` can safely be returned twice at the same type.

*Further problem.* Infer a scheme for `dup` in `let dup = λx. (x,x) in (dup 0, dup true)`. Could the body of the same definition typecheck at the purported scheme `∀α β. α→(α×β)`? Justify both answers from lookups.

# Reading for the Seminar
%%%
tag := "ch21-s5"
number := false
%%%

*Definitions · 10 minutes.* List the free variables in the inferred right-side type and in the surrounding context.

*Joint proof · 30 minutes.* Type the pair of identity uses, giving a different color to each instantiation. Then type the constant function returning the outer variable and recompute the generalization set.

*Proof review · 20 minutes.* Use the numeric-guard example to refute generalization of every unknown. Identify the exact lost equality between the result and the captured variable.

*Facilitator’s hint.* At a lookup, copy only the variables following the quantifier. Circle the unquantified result variable before drawing either copy.

# Solutions
%%%
tag := "ch21-s6"
number := false
%%%

*1.* The left argument imposes $`\beta = \text{Nat}` and the right imposes $`\beta = \text{Bool}`. Independent instantiation avoids this accidental identification.

*2.* The scheme is $`\forall\alpha.\alpha\rightarrow\left( {\alpha \times \delta} \right)`. The first component follows the argument type at each call. The second remains tied to the context’s $`\delta`.

*3.* Each call returns the same outer binding. If $`y:A`, each copy has type $`A`, and pair introduction permits product $`A \times A`. Quantification of the argument type of $`k` imposes no new requirement on $`A`.

*Further problem.* Inside the lambda the term context supplies one monomorphic entry `x:γ`. Both projections of the proposed result are constructed by looking up this same variable, so the pair has type `γ×γ`. Abstraction gives `γ→(γ×γ)`; the empty outer context leaves `γ` available for generalization. The two lookups of `dup` in the let body may now instantiate the scheme independently. The first call yields `Nat×Nat`, and the second yields `Bool×Bool`, so the entire pair has type `(Nat×Nat)×(Bool×Bool)`. To check the purported stronger scheme, choose Nat for its first variable and Bool for its second. Its instance would return `Nat×Bool` on zero. In the lambda body, however, the right component is again precisely `x`, and lookup assigns it Nat. Instantiation may vary a quantified variable between separate uses of the *function*, but all occurrences of that variable in the type of one use receive one consistent replacement.
