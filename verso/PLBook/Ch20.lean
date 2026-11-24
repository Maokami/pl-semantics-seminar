import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Constraint Generation and Unification" =>
%%%
tag := "ch20"
file := "chapter-20"
%%%

[Chapter PDF](print/chapter-20.pdf) · [Session 21](seminar/index.html#week-21)

Erase Nat from the parameter of last chapter’s identity. In `(λx. x) 0` the application still determines a type for $`x`. In `λx. x` alone, choosing Nat would discard equally valid choices. A type equation records what the surrounding term requires while allowing unresolved choices to remain variables.

*Sources.* Pierce, _Types and Programming Languages_, §§22.3–22.5, pp. 321–330, on constraint-based typing, unification and principal types. We generate fresh variables directly for unannotated binders; §22.6 explains implicit annotations. [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Equations from syntax
%%%
tag := "ch20-s1"
%%%

A provisional type is Nat, Bool, a type variable, or an arrow between provisional types. A substitution maps finitely many type variables to types and extends to types by preserving their constructors. A solution of a finite collection of equations is a substitution that makes each pair of sides identical. Fresh variables introduced at different syntax nodes are distinct and absent from the input.

Traverse the term in a context of provisional types. At a variable return its context entry with no new equations. At a literal return its base type. At $`\lambda x.b`, introduce a fresh $`\alpha`, type the body under $`x:\alpha`, and return $`\alpha\rightarrow B` with the body’s equations, where $`B` is its provisional type. At $`f\, a` collect both children’s equations, obtaining provisional types $`F` and $`A`. Introduce fresh $`\beta`, add $`F = A\rightarrow\beta`, and return $`\beta`.

*Why the equation is sufficient.* Under a solution $`S` the two child derivations of an application have types $`S(F)` and $`S(A)` by induction. The new equation ensures $`S(F) = S(A)\rightarrow S(\beta)`, exactly the premise required for an application at $`S(\beta)`. Conversely an ordinary typing fixes a domain and a result at every application and a parameter type at every binder. Assigning those types to the corresponding fresh variables satisfies the generated equations, by induction on typing. This converse allows the returned type to represent all ordinary typings of a closed term.

Generate constraints for `λf. λx. f (f x)` from the empty context. Assign the outer parameter the unknown `α` and the inner parameter `β`. The inner application looks up the very same binding for `f` that the outer application will later use. Introduce a fresh result `γ`; the inner equation is `α = β → γ`. The outer application receives this result as its argument. With a new result `δ`, its equation is `α = γ → δ`. The provisional type of the entire term is `α → (β → δ)`. Freshness applies to the result unknown at each application. Variable occurrences retrieve their parameter's existing unknown.

A solution must give the same image to the two copies of `α`. Decomposing the equality between their two required arrows yields `β = γ` and `γ = δ`. Thus each solution types the parameter as a function from some type back to itself; the entire term takes that function and returns another such function. If an implementation invented a new unknown at the second lookup of `f`, this derivation would lose the equation between the two arrows. It would incorrectly allow the single parameter to behave at unrelated types.

# Solving finite type equations
%%%
tag := "ch20-s2"
%%%

Unification searches for a *most general unifier* $`U`: every solution $`S` is obtained by applying some further substitution after $`U` on the variables of the problem. Drop an equation between identical types. Decompose an equation between arrows into domain and codomain equations. An equation between unequal rigid constructors, such as Nat and Bool, fails. Orient a variable equation as $`\alpha = T`. If the sides differ and $`\alpha` occurs in $`T`, fail the *occurs check*. Otherwise record the binding and apply it throughout the remaining equations, composing later substitutions with this one.

The elimination step preserves all solutions in factored form. Any solution must already send $`\alpha` to the image of $`T`, so it is unchanged, on this problem, by first applying the recorded binding. Conversely solving the updated equations and composing with that binding satisfies the original system. Arrow decomposition preserves solutions because finite arrow trees are equal exactly when their children are equal. Thus a successful run ending with no equations gives a most general unifier. Termination follows by ordering first the number of distinct unresolved variables, then the total size of pending equations. Elimination removes a variable, decomposition reduces size, and orientation can be performed as part of elimination.

Take the equations `α = β → γ` and `β = Nat`. After eliminating the first equation, the remaining equation still lets us choose the image of `γ` freely. Eliminating the second gives an intermediate substitution mapping `β` to Nat. To report the final solution we must also apply this substitution to the *right side* of the earlier binding, obtaining `α ↦ Nat → γ`. The unifier leaves `γ` unchanged. A later choice such as `γ ↦ Bool` then gives a particular solution by composition. Writing the two bindings side by side without recursive application or composition would leave the reported image of `α` inconsistent with its own constraints.

The linear order of elimination can change the displayed intermediate maps. Choosing `β = Nat` first already rewrites the first pending equation to `α = Nat → γ`. Both orders describe the same set of solutions. For an occurs-check failure the argument has a different shape: every finite tree has a strictly larger size when used as the domain of an arrow. The following Lean lemma makes that obstruction independent of the implementation of the unifier.

```lean
namespace FiniteTypeOccurs
inductive Tree where
  | atom
  | arr (a b : Tree)
def nodes : Tree → Nat
  | .atom => 1
  | .arr a b => nodes a + nodes b + 1
theorem noSelfDomain (a b : Tree) : a ≠ .arr a b := by
  intro h
  have impossible := congrArg nodes h
  simp only [nodes] at impossible
  omega
end FiniteTypeOccurs
```

# Principal types
%%%
tag := "ch20-s3"
%%%

The identity alone returns $`\alpha\rightarrow\alpha` with no equation. Every monomorphic instance replaces both occurrences by the same type. This is its *principal type*, a valid type pattern of which every valid type is an instance. For the application to zero, the additional equation and provisional result are

$$`\left( {\alpha\rightarrow\alpha} \right) = \left( {\text{Nat}\rightarrow\beta} \right),\quad\beta.`

Decompose to $`\alpha = \text{Nat}` and $`\alpha = \beta`. Eliminate $`\alpha` and solve $`\beta = \text{Nat}`. Applying the resulting substitution to the provisional result gives Nat. No type annotation was required.

For `λx. x x`, the same variable supplies the operator and operand, giving $`\alpha = \alpha\rightarrow\beta`. In any finite type tree the right side, after applying a proposed solution, contains the left side as a proper subtree. Its size is therefore strictly larger. This equation has no solution in our type grammar.

Principality contains two distinct claims. First the residual type pattern itself must type the original term. Second, every other typing must be obtainable by consistently instantiating its residual variables. For `λf. λx. f (f x)`, the generation trace gave the candidate `(β→β)→(β→β)`. To verify the first claim, look up `f:β→β` and `x:β`. One application types `f x` at `β`, so a second application types `f (f x)` at that same type. Discharge both variables to obtain the candidate.

For the second claim, invert an arbitrary typing derivation of this term. Let the parameter types of the two lambdas be `F` and `B`. Invert the inner application to conclude `F = B→C` for some `C`. Invert the outer application to conclude `F = C→D` for some `D`. Equality of the two arrow trees gives `B=C=D`. Thus the entire derivation has type `(B→B)→(B→B)`, precisely the instance `β ↦ B`. This argument proves principality up to renaming the residual variable. The spelling chosen for an unresolved variable makes no difference to the family of resulting finite types.

# Exercises
%%%
tag := "ch20-s4"
number := false
%%%

1. Infer the principal type of `λf. λx. f x`. Which equation identifies the type of $`f`?
2. Collect and solve the constraints for `0 true`. Compare this failure with self-application.
3. Give two distinct solutions of the identity’s constraints and explain why inferring only the first would lose information.

*Further problem.* Infer the principal type of `λx. λf. f (f x)`. Then constrain the result by demanding type `Bool→(Bool→Nat)→Nat`. Locate the first unavoidable mismatch and explain why merely typing the inner call would miss it.

# Reading for the Seminar
%%%
tag := "ch20-s5"
number := false
%%%

*Session 21 · After Chapter 19.* Keep the annotated typing derivation on the board. Erase the annotation from `(λx:Nat. x) 0` and assign a fresh type variable to the binder and another to the application result. Write the resulting arrow equation and solve it. Compare the result with the checker’s answer. For the final 15 minutes remove the application to zero: which equation disappears, and which choices for the identity’s parameter type become possible?

# Solutions
%%%
tag := "ch20-s6"
number := false
%%%

*1.* Give $`x` type $`\alpha` and the inner application result $`\beta`. The equation for $`f` is $`F = \alpha\rightarrow\beta`. The resulting type is $`\left( {\alpha\rightarrow\beta} \right)\rightarrow\left( {\alpha\rightarrow\beta} \right)`, with the right arrow corresponding to the inner lambda.

*2.* The only application equation is $`\text{Nat} = \text{Bool}\rightarrow\beta`. Distinct outer constructors cannot unify. In self-application the obstruction is an occurrence of the unknown inside its proposed solution.

*3.* Replacing $`\alpha` by Nat or by Bool gives the two corresponding identity arrows. Choosing Nat would exclude the Bool instance, whereas leaving $`\alpha` free admits both.

*Further problem.* Give `x` unknown type `α` and `f` unknown type `β`. Let `γ` be the result of `f x` and `δ` the result of the outer call. The inner application generates `β=α→γ`. The outer application uses the same context entry for `f` and generates `β=γ→δ`. Decomposing the arrow equality gives `α=γ` and `γ=δ`. Thus the principal type is `α→(α→α)→α`; conversely the two original applications type at every consistent choice of `α`. Comparing to the demanded arrow fixes `α=Bool` from the first domain and demands that the argument function return Nat. Its codomain must also equal `α`, forcing Bool to equal Nat. Equivalently, under the proposed inputs the inner call to `f` *is* well typed: applying a Boolean-to-natural function to a Boolean yields Nat. The outer call cannot feed that natural back into the Boolean domain of the one supplied function.
