import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Binding and Capture-Avoiding Substitution" =>
%%%
tag := "ch13"
file := "chapter-13"
%%%

[Chapter PDF](print/chapter-13.pdf) · [Session 14](seminar/index.html#week-14)

In the expression `λy. x y`, the first occurrence of a variable in the body obtains its value from outside the function. Replace that occurrence by `y`. If we simply write `λy. y y`, both occurrences now receive their values from the function’s caller. The substitution has changed where a name is bound.

*Sources.* Pierce, _Types and Programming Languages_, §5.3, starting p. 68, on free variables and substitution. Compute the example above before reading the abstraction clause. Compare Reynolds, _Theories of Programming Languages_, §1.4, where the same issue occurs under quantifiers. [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf) [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Terms and scope
%%%
tag := "ch13-s1"
%%%

Choose an infinite set of variable names. A term is a variable $`x`, an application $`t\, u`, or an abstraction $`\lambda x.t`. An abstraction binds occurrences of its parameter in its body. When nested abstractions use the same name, an occurrence belongs to the nearest enclosing binder with that name. Application associates to the left, and the body of a lambda extends as far right as possible. Thus `λx. f x y` means `λx. ((f x) y)`.

Write $`F(t)` for the names occurring free in $`t`. A variable has free set $`\{ x\}`. For application take the union of the two free sets. For abstraction remove the parameter from the body’s free set. In `λx. (λx. x) y`, the inner occurrence of `x` belongs to the inner binder, the outer binder has no occurrences, and $`F` contains only $`y`. A closed term has empty free set.

Renaming one binder and exactly the occurrences it binds to a fresh name preserves binding. Terms obtainable from one another by such renamings and their inverses are *alpha-equivalent*. For example, `λx. λy. x` and `λa. λb. a` are alpha-equivalent. The term `λa. λb. b` has a different binding structure.

Binding can be read off a syntax tree without computing any values. At each variable leaf, follow the path towards the root until the first abstraction whose parameter has the same name. If the path reaches the root first, record the name of that free occurrence. In `(λx. x) x` the paths from the two leaves behave differently. The left leaf encounters the lambda on the operator side. The right leaf reaches only the application node, then the root. A binder's scope consists of its body, so the binder in the operator has no authority over the argument.

This calculation gives a practical test for alpha-equivalence. Traverse two trees in parallel. Constructors must match; each bound occurrence must refer to the corresponding binder on its path, and free occurrences must have the same name. For example, `λa. λb. a b` and `λb. λa. b a` pass this test. In both bodies the operator leaf refers to the outer binder and the operand leaf to the inner one. Exchanging just the two leaves in the second body fails the test. Computing the free sets alone could not detect that change because both trees are closed.

The following function implements the free-occurrence test for one name. Application combines answers with Boolean disjunction, and a matching lambda binder blocks examination of its body for that name. The two checks differ only in whether the right occurrence is inside the lambda's scope.

```lean
namespace ScopePaths
inductive Exp where
  | var (name : Nat)
  | app (f a : Exp)
  | lam (name : Nat) (body : Exp)

def occursFree (x : Nat) : Exp → Bool
  | .var y => x == y
  | .app f a => occursFree x f || occursFree x a
  | .lam y b => x != y && occursFree x b

example : occursFree 0 (.app (.lam 0 (.var 0)) (.var 0)) = true := rfl
example : occursFree 0 (.lam 0 (.app (.var 0) (.var 0))) = false := rfl
end ScopePaths
```

# Substitution
%%%
tag := "ch13-s2"
%%%

Write $`t\left\lbrack {u/x} \right\rbrack` for replacing the free occurrences of $`x` in $`t` by $`u`. The result is determined up to alpha-equivalence. A name fresh for a list of terms is a name occurring nowhere in any of them. Finiteness of the terms and infinitude of the name supply guarantee a choice. Use the following procedure.

1. At a variable return $`u` if it is $`x` and the original variable otherwise.
2. At an application substitute independently into both children.
3. At $`\lambda y.b`, leave the abstraction alone if $`y = x` or $`x` is absent from $`F(b)`. Otherwise if $`y` is absent from $`F(u)`, retain $`y` and substitute into $`b`.
4. In the remaining case choose $`z` fresh for $`b,u,x,y`. Rename the outer binder $`y` to $`z`, replacing just its bound occurrences in $`b` to obtain $`b'`. Return $`\lambda z.\left( {b'\left\lbrack {u/x} \right\rbrack} \right)`.

Renaming a binder leaves the size of the body unchanged, so the recursive call still works on a smaller term than the original abstraction. Alternative fresh choices rename the same binder and its bound occurrences together.

Substitution is simultaneous at the selected occurrences. For example, `(x x)[x y/x]` is the application `(x y) (x y)`. Each of the two original leaves contributes one copy of the replacement. A recursive call that entered the newly inserted `x y` to look for another `x` would attempt the same replacement again. The variable clause returns its replacement immediately. This restriction both determines the mathematical operation and explains why induction on the original syntax tree suffices for an application.

Two substitutions in succession require attention to order. For distinct names `x,y,z`, start from the one-leaf tree `x`. Replacing `x` by `y` and then `y` by `z` gives `z`. Reversing these operations gives `y`, since the first replacement of `y` has no occurrence on which to act. The disagreement already occurs in a language with no binders. When proving substitution laws under lambdas, there are consequently two obligations to track: a later substitution may act on material inserted by an earlier one, and each intervening binder must preserve the free occurrences in that material. Alpha-renaming handles the latter obligation.

# A substitution under an abstraction
%%%
tag := "ch13-s3"
%%%

Take $`t = \lambda y.\left( {x\, y} \right)` and $`u = y`. The name being inserted occurs free in $`u`, and the target $`x` occurs free in the body. Choose fresh $`z`. First write $`\lambda z.\left( {x\, z} \right)`, then replace $`x` to obtain $`\lambda z.\left( {y\, z} \right)`. The occurrence to the left of the final application is free and the occurrence to its right is bound. Their roles remain distinct even if this function is later applied to another argument.

*Free-variable lemma.* If $`x \in F(t)`, then $`F\left( {t\left\lbrack {u/x} \right\rbrack} \right) = \left( {F(t) \smallsetminus \left\{ x \right\}} \right) \cup F(u)`, where $`\smallsetminus` denotes set difference. If $`x \notin F(t)`, substitution leaves the term unchanged up to alpha-equivalence. To prove the first claim, induct on term size. The variable case returns the inserted term. For an application apply the corresponding assertion to each child, taking account of a child that has no free $`x`, then take the union. For an abstraction traversed by substitution, choose its binder $`z` fresh for $`u` and distinct from $`x`. Removing $`z` from the body’s new free set removes nothing from $`F(u)`, so the displayed formula follows. The absence claim follows from the variable and application clauses and the stopping test at an abstraction.

The free-variable lemma can be used to check a longer reduction by hand. Choose distinct names and start with `(λx. λy. x (λx. y)) y`. The substitution targets the body `λy. x (λx. y)`; the new free occurrence of `y` would cross its outer binder. Rename that binder to `w`. Its bound occurrences include the occurrence inside `λx. y`, because that inner binder introduces `x`, so the new body is `λw. x (λx. w)`. Substitute the argument to obtain `λw. y (λx. w)`. The inner lambda binds its own parameter and substitution for `x` stops there.

Calculate the free set at each boundary. Before substitution, the outer abstraction's only free name is `x`. Renaming has left this set unchanged. After substitution it contains just `y`, as predicted by removing `x` and adding the free set of the operand. Renaming only the first binder token, without updating its occurrence beneath the inner lambda, would leave behind a second, unintended source of dependence on `y`. Rechecking each occurrence's path to its binder detects even errors that happen to preserve the final set of free names.

# Exercises
%%%
tag := "ch13-s4"
number := false
%%%

1. Compute `(λy. (λy. y) x)[y/x]` and mark all free occurrences in the result.
2. Give a term with two occurrences of the spelling `x` where only one is affected by substitution for $`x`.
3. Would the equality in the lemma hold for all $`t` if the hypothesis $`x \in F(t)` were dropped? Give a counterexample.

*Further problem.* Let `p = λz. (x z) y`, with all three names distinct. Calculate `(p[y/x])[z/y]` and `(p[z/y])[y/x]`. List the free names after each substitution and decide whether the final terms are alpha-equivalent.

# Reading for the Seminar
%%%
tag := "ch13-s5"
number := false
%%%

*Definitions · 10 minutes.* Mark the binding of each occurrence in the opening term.

*Joint proof · 30 minutes.* Have one reader perform textual replacement and another perform capture-avoiding substitution. Compute the free sets and then prove the abstraction case of the lemma.

*Proof review · 20 minutes.* Repeat the calculation with nested binders in Exercise 1 and with a different choice of fresh name.

*Facilitator’s hint.* Draw a line from each bound occurrence to its binder before changing any names. A line cannot cross over a nearer binder of the same name.

# Solutions
%%%
tag := "ch13-s6"
number := false
%%%

*1.* One result is `λz. (λy. y) y`. Renaming the outer binder does not enter the inner abstraction that binds its own $`y`. The final argument $`y` is the only free occurrence.

*2.* In `x (λx. x)`, replacing $`x` by $`u` gives `u (λx. x)` with the chosen term in the left position. The inner abstraction stops substitution.

*3.* Take $`t = z`, with three distinct names $`x,y,z`, and $`u = y`. Substitution returns $`z`. The proposed right side would also contain $`y`.

*Further problem.* In the first order, replacing `x` by `y` gives `λz. (y z) y`, whose free set is the singleton containing `y`. Before replacing those occurrences by the free variable `z`, rename the binder to a fresh `w`, including its bound occurrence. Substitution then gives `λw. (z w) z`, with free set containing only `z`. In the reverse order, rename the original binder before the first substitution. The intermediate expression is `λw. (x w) z`, with two free names, `x` and `z`. Replacing `x` by `y` gives `λw. (y w) z`, with free set containing `y` and `z`. Alpha-equivalence preserves free names, so the unequal final sets decide the question. The occurrence introduced by the first replacement in the first order becomes a target for the second replacement. The reverse order has already finished replacing `y` before that new occurrence is introduced.
