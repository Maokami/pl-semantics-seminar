import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Environments and Closures" =>
%%%
tag := "ch15"
file := "chapter-15"
%%%

[Chapter PDF](print/chapter-15.pdf) · [Session 16](seminar/index.html#week-16)

A function defined when $`x` has value one is called after a second binding gives $`x` value two. Substitution predicts which binding supplies the result. An evaluator that represents variables by lookups must make the same choice when it enters the function body.

*Sources.* Reynolds, _Theories of Programming Languages_, §11.2 (evaluation), followed by §§11.6–11.7 (direct denotations and dynamic binding). Follow the environment used for a free identifier and compare dynamic binding. Below we give operational rules for a pure call-by-value fragment. For a further implementation perspective, read §12.4. [Reynolds, contents and section titles.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# A lexical evaluator
%%%
tag := "ch15-s1"
%%%

Extend the lambda terms of Chapter 13 with integer literals and a binding `let x = r in b`. Its evaluation first computes $`r`, then evaluates $`b` with its $`x` bound to that value. An environment $`\rho` is a finite mapping from names to values. Updating a mapping creates an extended mapping, leaving the original available. A value is either an integer or a *closure*, a triple of a parameter, a body, and the environment in which the function was defined. In this finite, nonrecursive binding language such environments and values are built inductively.

Write $`\rho \vdash t \Downarrow v` when term $`t` evaluates in environment $`\rho` to value $`v`. The following clauses generate the finite evaluation derivations.

1. A literal evaluates to its integer. A variable $`x` evaluates to $`\rho(x)` when the name is in the domain of $`\rho`.
2. An abstraction $`\lambda x.b` evaluates to the closure $`\left\langle {x,b,\rho} \right\rangle`.
3. For `let x = r in b`, first derive $`\rho \vdash r \Downarrow w`, then derive the result for $`b` under $`\rho\left\lbrack {x\mapsto w} \right\rbrack`.
4. For $`f\, a`, evaluate $`f` in $`\rho` to a closure $`\left\langle {x,b,\eta} \right\rangle` and $`a` in $`\rho` to $`w`. Evaluate $`b` in $`\eta\left\lbrack {x\mapsto w} \right\rbrack`. The result of this last derivation is the result of the application.

The operator and argument are source subterms at the call site. The body comes from a different subterm, written at the point of definition. This accounts for the distinct environments in the last rule. A lookup of a missing name or an application of an integer supplies no corresponding successful rule.

To see why a function value contains an environment, consider `let make = λa. λb. a in (make 6) 8`. Lookup of `make` produces a closure for the outer function. Its argument evaluates to the integer six. In the saved environment extended with `a ↦ 6`, evaluation of `λb. a` produces a *new* closure. The second closure's code mentions `a`, and its saved environment now contains that integer. At this point the first application has completely finished. Returning the function transports the binding it will still need.

For the second application the operator evaluates to this inner closure and the operand to eight. Entering its body extends its saved environment with `b ↦ 8`. Lookup of `a` returns six. Notice the two separate uses of the abstraction rule in this derivation. Evaluating the inner abstraction does not evaluate its body; it saves the environment in which that body will eventually execute. Eager evaluation of arguments is consistent with deferring function bodies. Computing a function's result at definition time would fail on functions whose results depend on their as-yet-unsupplied parameters.

# Shadowing
%%%
tag := "ch15-s2"
%%%

```
let x = 1 in
let f = (λu. x) in
let x = 2 in f x
```

Starting in the empty environment, the first binding produces $`\rho_{1}` with $`x\mapsto 1`. The function definition returns $`k = \left\langle {u,x,\rho_{1}} \right\rangle`. Just before the application the environment $`\rho_{3}` maps $`f` to $`k` and $`x` to 2. The argument lookup therefore returns 2. The body environment is $`\rho_{1}\left\lbrack {u\mapsto 2} \right\rbrack`. Since $`u` and $`x` are distinct names, its lookup of $`x` returns 1. Both values of $`x` play a role in this execution.

For comparison, use the substitution evaluator with the value-let step `let x = v in b → b[v/x]` and the value-beta rule. Substituting 1 for the first $`x` changes the definition of $`f` to $`\lambda u.1`. The inner binding protects its own occurrences of $`x`. Substituting this function for $`f` and then 2 for the inner $`x` gives $`\left( {\lambda u.1} \right)\, 2`, which returns 1. The lexical closure retains exactly the binding needed to agree with this calculation.

We can separate the two lookups in the shadowing example by giving the function two results to return in succession. Within the same integer and function fragment, replace the definition with `λu. λv. u`. The argument supplied by `f x` is read in the inner let's environment, so this call constructs a closure whose environment contains `u ↦ 2`. Applying the returned closure to zero yields two. If we instead define `f` as `λu. λv. x`, its inner closure retains access to the `x ↦ 1` inherited from the point where `f` was created. Applying that result to zero yields one.

Both executions encounter the same sequence of binding constructs, and both supply two and then zero as arguments. The difference lies in one lookup at the innermost body. Its path back through the syntax reaches the parameter `u` in the first program and the original let binder of `x` in the second. Labeling these two binders before evaluating the program predicts the results. The environment rules then explain how those syntactic links are realized when the corresponding calls have already returned.

Here a closure is specialized to a single parameter and an integer result. `close` evaluates a body in the saved environment extended by the parameter. The actual operand is looked up in the caller's environment before `close` receives it. The two checks isolate the source of each lookup.

```lean
namespace SavedEnv
abbrev Env := Nat → Nat
def put (ρ : Env) (x v : Nat) : Env :=
  fun y => if y = x then v else ρ y

def close (saved : Env) (param : Nat) (body : Env → Nat) : Nat → Nat :=
  fun arg => body (put saved param arg)

def old : Env := put (fun _ => 0) 0 4
def caller : Env := put old 0 7

example : close old 1 (fun ρ => ρ 0) (caller 0) = 4 := rfl
example : close old 1 (fun ρ => ρ 1) (caller 0) = 7 := rfl
end SavedEnv
```

# Dynamic binding and closure size
%%%
tag := "ch15-s3"
%%%

If the application rule instead evaluates the body in $`\rho\left\lbrack {u\mapsto w} \right\rbrack` using the *caller’s* environment, the example returns 2. Under that rule even renaming an unrelated caller binding can affect a free lookup in a called function. Under lexical binding the binder supplying each occurrence is fixed by the nesting of the source term.

A closure may store just the bindings for the body’s free variables other than the parameter. To see why, consider a variable lookup reached during body evaluation. If its binder was introduced after the call, the evaluator extended the environment with its value. Otherwise the occurrence refers to a free name of the abstraction, whose binding survived the restriction. Formally, an induction on a finite evaluation maintains agreement on free names; closure results are compared by their code and relevant saved bindings, since entire environment records may differ. In the example $`f` needs only the old binding for $`x`.

The environment saved by a closure can retain another closure transitively. In `let x = 5 in let h = λv. x in λu. h u`, the free-name set of the final abstraction is the singleton containing `h`. A restricted environment for that abstraction therefore needs only the binding for `h`. Its value, however, is a closure whose own free-name set contains `x`. Applying the outer closure to an integer first retrieves `h`, then enters the environment attached to `h`, where lookup of `x` still yields five. Discarding all bindings except `h` from the *entire heap* would invalidate this reasoning. Restriction operates on each environment separately and retains values reachable through the entries it keeps.

This example also explains the form of an agreement statement for environments. To compare the results of two evaluators, demanding literal equality of their saved maps would distinguish a compact implementation from the full-environment implementation immediately. For integer results equality is appropriate. For function results one may instead relate closures with the same code and recursively related captured values at the free names of that code. In this nonrecursive setting the example unfolds to a single comparison of the integer five.

# Exercises
%%%
tag := "ch15-s4"
number := false
%%%

1. Change the function body in §15.2 from $`x` to $`u`. Evaluate under both binding disciplines.
2. Rename only the innermost let binder and its bound occurrence to $`z`. Give the dynamic result before and after this consistent renaming.
3. An implementation updates one mutable dictionary in place and saves a pointer to it in every function. What happens on the original example if there are no snapshots or separately allocated binding frames?

*Further problem.* Evaluate `let a=4 in let f=λp. λq. p in let a=7 in let g=f a in let a=9 in g a` with lexical environments. Give the arguments of both calls and the environment entry used by the innermost lookup.

# Reading for the Seminar
%%%
tag := "ch15-s5"
number := false
%%%

*Definitions · 10 minutes.* Write the environment after each let, keeping old environments visible.

*Joint proof · 30 minutes.* Construct the last three premises for the application, then use capture-avoiding substitution to derive the same result from the empty environment.

*Proof review · 20 minutes.* Change the body environment to the caller’s environment and try Exercise 2. Trace the lookup whose result changes.

*Facilitator’s hint.* The parameter and argument are different objects. First ask where the argument expression is written; only then ask where the body is written.

# Solutions
%%%
tag := "ch15-s6"
number := false
%%%

*1.* The argument occurrence of $`x` is found at the call site and gives 2. Both environment variants bind $`u` to that argument, so both return 2.

*2.* With the new name the call is `f z`. The argument is still 2, while under dynamic lookup the caller’s $`x` now resolves to the outer 1. Dynamic evaluation changes from 2 to 1. Lexical evaluation returns 1 both times.

*3.* Rebinding $`x` overwrites the entry visible through the saved pointer. The closure reads 2. A lexical implementation needs a way to retain the original binding, for example persistent environment frames or an explicit capture of the free value.

*Further problem.* The closure for `f` is made when the outer binding of `a` is four. At the call `f a`, the argument expression occurs under the second binding, so its lookup yields seven. Entering the body of `f` extends its definition environment with `p=7`. The body is an abstraction, and its returned closure therefore retains the entry for `p`. Bind this closure to `g`. At `g a`, the argument expression occurs under the last binding, so the value passed for `q` is nine. The body lookup for `p` now takes place in the saved environment extended with `q=9`; it returns seven. Retaining just the free entries of each abstraction would allow the environment of `f` to be empty and the environment of `g` to contain just `p=7`. In particular the first call does not need its captured binding for `a` to evaluate the separately supplied argument.
