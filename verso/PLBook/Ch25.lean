import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Universal Types and System F" =>
%%%
tag := "ch23"
file := "chapter-23"
%%%

[Chapter PDF](print/chapter-23.pdf) · [Session 24](seminar/index.html#week-24)

In the let system of Chapter 23 the type chosen at a use of the identity was inferred. System F lets a programmer bind a type variable in a term and supply its argument explicitly. This gives us an expression whose own type says that its caller may choose any type.

*Sources.* Pierce, _Types and Programming Languages_, §§23.3–23.5, pp. 341–353. Follow the rules for type abstraction and application and calculate one substitution at each level. [Pierce, universal types.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Two levels of binding
%%%
tag := "ch23-s1"
%%%

Add type variables $`X` and universal types $`\forall X.T` to base types and arrows. A type context $`\Delta` records which type variables are in scope. A type is well formed when all of its free variables belong to $`\Delta`. In $`\forall X.T` the binder removes the occurrences of $`X` in its scope from the free set. Term contexts contain names assigned well-formed types.

Add the term forms $`\Lambda X.t` and $`t\lbrack A\rbrack`. The first is a *type abstraction*: it binds $`X` in type annotations and type arguments inside $`t`. The second applies a polymorphic term to a type. Ordinary $`\lambda x:A.t` still binds a term variable, and $`f\, u` still supplies a term argument. We choose all binders fresh when needed and use capture-avoiding substitution at both levels.

If $`t:T` is derivable in type context $`\Delta,X` and term context $`\Gamma`, we may derive $`\Lambda X.t:\forall X.T` under $`\Delta,\Gamma`, provided $`X` is fresh for $`\Delta` and for the types in $`\Gamma`. Conversely, if $`t:\forall X.T` and $`A` is well formed in $`\Delta`, then $`t\lbrack A\rbrack:T\left\lbrack {A/X} \right\rbrack`. An explicit type argument can itself be universal. This feature is called *impredicative instantiation*.

Consider the closed term `twice = ΛX. λf:X→X. λx:X. f (f x)`. At the innermost occurrence of `x`, the type context contains the single name `X` and the term context contains `f:X→X, x:X`. Lookup gives the operand type `X`; applying the function found by lookup at `f` yields another term of type `X`. This is exactly the domain needed for the outer application. Abstracting first over `x` yields an arrow `X→X`. Abstracting over `f` yields `(X→X)→(X→X)`. Only now is the term context empty, so type abstraction yields `∀X.(X→X)→(X→X)`.

Read the same derivation as instructions for a caller. The intermediate expression `twice[Bool]` has type `(Bool→Bool)→(Bool→Bool)`. Giving it Boolean negation leaves an ordinary Boolean endofunction, that is, a function from Bool to itself. Applying that result to true calculates two negations and returns true. Removing the type application from the explicitly typed source leaves no arrow available to the first ordinary application. Conversely, writing `twice[true]` fails before the arrow premises matter: the expression inside brackets must form a type in the caller's type context. These failures locate the two separate formation checks in a single example.

# The identity
%%%
tag := "ch23-s2"
%%%

Let $`i = \Lambda X.\left( {\lambda x:X.x} \right)`. Under type assumption $`X` and term assumption $`x:X`, lookup types the body at $`X`. Discharging $`x` gives an arrow $`X\rightarrow X` under type assumption $`X`. The term context is now empty, so discharging $`X` gives the closed typing

$$`i:\forall X.\left( {X\rightarrow X} \right).`

Instantiating with Nat replaces *both* occurrences of $`X` in the result type. Thus $`i\left\lbrack \text{Nat} \right\rbrack` has type $`\text{Nat}\rightarrow\text{Nat}`, and $`i\left\lbrack \text{Nat} \right\rbrack\, 0` has type Nat.

Operationally, type application of a type abstraction substitutes the type argument in its body. Ordinary beta reduction of an abstraction applied to a value substitutes that term value in its body. Treat type and term abstractions as values. In a left-to-right value evaluation the first step of the example is

$$`i\left\lbrack \text{Nat} \right\rbrack\, 0\rightarrow\left( {\lambda x:\text{Nat}.x} \right)\, 0.`

The second step returns zero. The first replacement changes a parameter annotation; the second replaces an occurrence of a variable used in a computation.

A polymorphic value can itself be the argument of an ordinary function. With the product types of Chapter 23, write `U = ∀X.X→X` and consider `use = λk:U. (k[Nat] 0, k[Bool] true)`. There is just one assumption for the parameter, namely `k:U`. At the first occurrence the universal elimination rule yields `k[Nat]:Nat→Nat`. At the second occurrence it yields `k[Bool]:Bool→Bool`. Arrow elimination in each component and then product formation give `use : U → (Nat × Bool)`. Notice the position of the universal quantifier inside the domain of an arrow. An ordinary lambda parameter in the let-polymorphic calculus of Chapter 23 receives a monotype, which would have to account for both uses without these two independent instantiations.

For the particular call `use i`, ordinary beta reduction first supplies the entire polymorphic identity for both occurrences of `k`. The left component then reduces to zero and the right component to true. There is no type argument to `use` itself: its parameter has a polymorphic type, while its own outermost type constructor is an arrow. The following Lean example checks the same two instantiations at one universe and computes the result of this particular call.

```lean
namespace ExplicitPoly
def useBoth (k : (α : Type) → α → α) : Nat × Bool :=
  (k Nat 0, k Bool true)

example : useBoth (fun _ x => x) = (0, true) := rfl
end ExplicitPoly
```

# Freshness and capture
%%%
tag := "ch23-s3"
%%%

Suppose an outer term variable has type $`X`. Arbitrarily generalizing that type variable while keeping the term variable in the context would permit the same supplied value to be treated as any independently chosen type. The freshness condition in the abstraction rule prevents this. It corresponds to the exclusion of context variables at let-generalization in Chapter 23.

As an example of type-level capture, consider $`T = \forall Y.\left( {X\rightarrow Y} \right)` and substitute free $`Y` for $`X`. Rename the binder to fresh $`Z` first. The result is $`\forall Z.\left( {Y\rightarrow Z} \right)`; its domain still refers to the surrounding $`Y`. The literal replacement $`\forall Y.\left( {Y\rightarrow Y} \right)` changes the domain into a bound variable and therefore describes a different type.

Substitution through a term can require the same renaming in several places. Work under the type assumption `X` and take `s = ΛY. λg:X→Y. λv:X. g v`. Its type is `∀Y.(X→Y)→X→Y`, with arrows associating to the right. We want to use a free type name `Y` from a different context as the argument replacing `X`. First change the bound name of the type abstraction to fresh `Z`. Its bound occurrences in the annotation of `g` and in the result type change together. Substitution now produces `ΛZ. λg:Y→Z. λv:Y. g v`, of type `∀Z.(Y→Z)→Y→Z` in the context containing the free `Y`.

The caller can choose Bool for the outer free type and subsequently Nat for the locally bound argument. The resulting term then accepts a function from Bool to Nat and a Boolean input. A literal replacement that captures the free name would instead accept a function from Nat to Nat and a natural input when the local argument is Nat. Checking the two instantiations therefore gives a concrete way to detect the changed dependency. In the correct substitution, the set of free type names of the resulting type is exactly the singleton containing the caller's name.

*From let to explicit type application.* In Chapter 23 the two occurrences of a let-bound identity can be instantiated independently. Write its System F value as `ΛA. λx:A. x`. Bind this value to the name `id`. The uses that inferred Nat and Bool now read `id [Nat] 0` and `id [Bool] true`. Substituting Nat for A in the first function leaves the second use free to choose Bool. In Chapter 23 generalization was restricted by the types in the surrounding context; the System F typing rule for type abstraction likewise requires its bound type variable to be fresh for that context.

# Exercises
%%%
tag := "ch23-s4"
number := false
%%%

1. Let $`U = \forall X.\left( {X\rightarrow X} \right)`. Type $`i\lbrack U\rbrack\, i` and compute its result under the given rules.
2. Type the constant function `ΛX. ΛY. λx:X. λy:Y. x`. Show the type remaining after supplying only Nat for its first argument.
3. Explain why an ordinary function application rule cannot by itself type $`i\left\lbrack \text{Bool} \right\rbrack`.

*Further problem.* In System F derive the type of `applyAt = ΛA. λk:(∀X.X→X). λa:A. k[A] a`. Compare `applyAt[Nat] i 0` and `applyAt i [Nat] 0`, understanding the second expression as first applying `applyAt` to term argument `i`.

# Reading for the Seminar
%%%
tag := "ch23-s5"
number := false
%%%

*Definitions · 10 minutes.* Mark the type and term binders in the identity and identify the scope of each.

*Joint proof · 30 minutes.* Derive its universal type and calculate the two distinct substitutions in the application to zero. Require the group to write the type after each step.

*Proof review · 20 minutes.* Make the two type arguments from the let-polymorphic identity of Session 22 explicit. Check one type substitution for capture as in §25.3.

*Facilitator’s hint.* Look at the binder removed by a step. A capital lambda discharges a type parameter, so look inside term annotations when performing that substitution.

# Solutions
%%%
tag := "ch23-s6"
number := false
%%%

*1.* The type application has type $`U\rightarrow U`. Its operand has type $`U`, so the whole term has type $`U`. First reduce the type application to $`\lambda x:U.x`, then apply it to $`i` to obtain $`i`.

*2.* Nested introduction yields $`\forall X.\forall Y.\left( {X\rightarrow\left( {Y\rightarrow X} \right)} \right)`. The first instantiation gives $`\forall Y.\left( {\text{Nat}\rightarrow\left( {Y\rightarrow\text{Nat}} \right)} \right)`. Choosing the second type and supplying the two term arguments are still pending.

*3.* That rule requires a term with an arrow type and a term argument. Here the premise is universal typing and the argument is the well-formed type Bool.

*Further problem.* Under the type assumption `A`, lookup assigns `k` the universal type and `a` the type `A`. Since `A` is well formed there, universal elimination gives `k[A]:A→A`. Term application gives `k[A] a:A`. Discharging `a`, then `k`, then the type parameter gives `∀A.(∀X.X→X)→A→A`; the outer type abstraction now has an empty term context. In the first expression, the type application yields `(∀X.X→X)→Nat→Nat`, the term application to `i` yields `Nat→Nat`, and the final term application yields Nat. Reducing the outer type redex changes the annotation on `a` and the type argument of `k` to Nat. Substitution of `i` and zero leaves `i[Nat] 0`, which returns zero. In the second expression the very first term application would require the outermost type of `applyAt` to be an arrow. It is a universal type, and the ordinary application rule cannot supply the missing type elimination.
