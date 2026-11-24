import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Weakening and Typed Substitution" =>
%%%
tag := "ch17"
file := "chapter-17"
%%%

[Chapter PDF](print/chapter-17.pdf) · [Session 18](seminar/index.html#week-18)

To run a function we substitute an argument into its body. Typing knows the body under an assumption about the parameter. Once the parameter disappears, we need a typing derivation for the substituted body in the caller’s context. The only delicate step is passing beneath another binder.

*Sources.* Pierce, _Types and Programming Languages_, §§9.1–9.3, pp. 99–107. Read the application and abstraction rules before the substitution lemma. We use finite maps of names and prove the version admitting an open substituting term. [Pierce, chapter 9.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Contexts and typing
%%%
tag := "ch17-s1"
%%%

In the simply typed lambda calculus, a type is a base type or a function type $`A\rightarrow B`. The latter associates to the right. A term is a variable, a typed abstraction $`\lambda x:A.b`, or an application $`f\, a`. We may include a constant of a specified base type. A typing context $`\Gamma` is a finite mapping from distinct names to types. Write $`\Gamma,x:A` for extension by a fresh name. Terms are considered up to consistent renaming of bound variables (Chapter 13).

The judgment $`\Gamma \vdash t:A` assigns type $`A` to $`t` under those assumptions. A lookup $`\Gamma(x) = A` types a variable. If $`\Gamma,x:A \vdash b:B`, then $`\Gamma \vdash \left( {\lambda x:A.b} \right):A\rightarrow B`. If $`\Gamma \vdash f:A\rightarrow B` and $`\Gamma \vdash a:A`, then $`\Gamma \vdash f\, a:B`. A declared constant keeps its type under every context. A free variable of any typable term occurs in the context: induction on typing passes to the two children at application and removes the local parameter at abstraction.

Consider the judgment for `λf:A→B. λx:A. f x`. Start at the two leaves of the typing tree. Both occur in the context containing `f:A→B` and `x:A`. One lookup justifies the occurrence of the function and the other justifies the occurrence of its argument. Application combines these judgments in their common context to give `f x : B`. Introducing the inner abstraction discharges the assumption about `x`, giving $`f:A\to B \vdash \lambda x:A.\, f\,x : A\to B`. Introducing the outer abstraction discharges the remaining assumption. The closed result has type `(A→B)→(A→B)`.

Read the same tree downwards from its conclusion. The inner lambda introduced the assumption about `x`, so that assumption is available at both lookup leaves, even though the leaf for `f` never uses it. Consequently a typing judgment does not assert that all names in its context occur in the term. It asserts that the context supplies a consistent type for every lookup the derivation actually performs. For instance, a judgment about the open subterm `f x` needs both assumptions. Removing either one destroys a leaf of this derivation. Adding a third, fresh binding preserves both leaves. This is the distinction the weakening lemma makes precise.

# Weakening
%%%
tag := "ch17-s2"
%%%

Say $`\Gamma \subseteq \Delta` if every name in $`\Gamma` has the same binding in $`\Delta`. *Lemma 17.1.* If $`\Gamma \vdash t:A` and $`\Gamma \subseteq \Delta`, then $`\Delta \vdash t:A`. Induct on the typing derivation, allowing any such $`\Delta`. A variable keeps its lookup. At a constant the rule works in any context. At an application use both induction hypotheses and reapply the application rule. At an abstraction rename its parameter to $`z` fresh for both contexts and the body’s other names. Then $`\Gamma,z:C \subseteq \Delta,z:C`. The induction hypothesis types the body under the larger extended context, and abstraction discharges $`z:C`.

The renaming convention used here can itself be justified by relabeling a derivation: consistently replace a binder and its bound variable lookups by the fresh name, copy each unaffected lookup, and reconstruct the same application and abstraction rules. Freshness prevents any formerly distinct lookup from changing its target.

In the abstraction case of weakening, choosing a fresh name sometimes requires changing the displayed derivation. For example, start from the empty-context typing of `λy:A. y` and weaken it into the context containing `y:B`, where `A` and `B` are distinct. The premise of the original abstraction rule types its body in the one-entry context `y:A`. If we attempt to add `y:A` directly to the target context, the new entry collides with `y:B`. A finite map cannot extend both contexts by this key while retaining their original bindings.

Choose `z` fresh and use the representative `λz:A. z` of the original abstraction. Its premise uses the context `z:A`. The new premise requires `y:B, z:A`, which genuinely extends `z:A`. Apply the induction hypothesis to the lookup of `z` and discharge `z:A` again. This leaves precisely `y:B` in the conclusion. There are two different uses of the variable convention in this argument. Renaming transports a derivation to an alpha-equivalent term. Inclusion transports the new body judgment to a larger map without changing its term. Keeping these steps distinct also explains why context inclusion compares the types as well as the presence of keys.

# Substitution in context
%%%
tag := "ch17-s3"
%%%

*Theorem 17.2.* If $`\Gamma,x:A \vdash t:B` and $`\Gamma \vdash u:A`, then $`\Gamma \vdash t\left\lbrack {u/x} \right\rbrack:B`. Here $`x` is fresh for $`\Gamma` and substitution avoids capture. We induct on the first typing derivation, with the context and substituting term universally quantified.

At a variable $`y = x`, the result term is $`u` and the desired judgment is the second premise. For $`y \neq x` the original lookup already belongs to $`\Gamma`. Constants remain typed by their declarations. At application substitute independently in the two premises, retaining the original domain type, and reassemble the application.

At an abstraction choose a representative $`\lambda z:C.b` with $`z` fresh for $`\Gamma,x,u` and the body’s other names. Inverting typing gives the body judgment in $`\Gamma,x:A,z:C`. Since contexts are maps with distinct keys we may present the same map as $`\Gamma,z:C,x:A`. Weakening types $`u:A` in $`\Gamma,z:C`. Instantiate the induction hypothesis with this extended context. It gives

$$`\Gamma,z:C \vdash b\left\lbrack {u/x} \right\rbrack:D.`

Abstraction now gives the required type $`C\rightarrow D` in $`\Gamma`. The precise need for weakening is visible here: the body derivation and the argument derivation must agree on what remains in scope after removing $`x`.

Here is an instance in which the argument genuinely needs an outer assumption. Let `Γ` consist of `y:B` and `f:B→A`. Take the substituting expression to be `f y`. It has type `A` by two lookups and application. Under the extra assumption `x:A` the source body `λz:C. x` has type `C→A`. To substitute under its lambda, the induction hypothesis requests a derivation of $`\Gamma,z:C \vdash f\,y : A`. The derivation in hand concludes $`\Gamma \vdash f\,y : A`. Weakening transports both lookups to the larger map and preserves the application that joins them. Substitution in the variable body then yields $`\Gamma,z:C \vdash f\,y : A`. Discharging the binder produces $`\Gamma \vdash \lambda z:C.\,f\,y : C\to A`. A proof restricted to closed arguments could never use this example.

The Lean development below encodes each variable occurrence by a path to its binder. A path carries its type: `here` selects the newest entry and `there` passes over one entry. A term of type `Term Γ a` therefore contains evidence of its context and type in its constructors. A renaming maps each path to a path with the same type. A simultaneous substitution maps each path to a term of the same type. In `liftSub`, the new binder maps to itself. Every older variable maps to an expression which must now be weakened under that binder. This is the precise argument supplied by the named weakening lemma in the paper proof. The last declaration specializes simultaneous substitution to a single parameter. Its return type states the typing judgment needed by beta preservation.

```lean
namespace BinderProof

inductive Ty where
  | base
  | arr (a b : Ty)

inductive Var : List Ty → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

inductive Term : List Ty → Ty → Type where
  | var : Var Γ a → Term Γ a
  | lam : Term (a :: Γ) b → Term Γ (.arr a b)
  | app : Term Γ (.arr a b) → Term Γ a → Term Γ b

abbrev Ren (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Var Δ a

def liftRen (r : Ren Γ Δ) : Ren (b :: Γ) (b :: Δ)
  | _, .here => .here
  | _, .there x => .there (r x)

def rename (r : Ren Γ Δ) : Term Γ a → Term Δ a
  | .var x => .var (r x)
  | .lam t => .lam (rename (liftRen r) t)
  | .app f t => .app (rename r f) (rename r t)

def weaken (t : Term Γ a) : Term (b :: Γ) a :=
  rename (fun x => .there x) t

abbrev Sub (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Term Δ a

def liftSub (s : Sub Γ Δ) : Sub (b :: Γ) (b :: Δ)
  | _, .here => .var .here
  | _, .there x => weaken (s x)

def subst (s : Sub Γ Δ) : Term Γ a → Term Δ a
  | .var x => s x
  | .lam t => .lam (subst (liftSub s) t)
  | .app f t => .app (subst s f) (subst s t)

def replaceTop (u : Term Γ a) : Sub (a :: Γ) Γ
  | _, .here => u
  | _, .there x => .var x

def betaBody (t : Term (a :: Γ) b) (u : Term Γ a) : Term Γ b :=
  subst (replaceTop u) t

end BinderProof
```

# An open argument
%%%
tag := "ch17-s4"
%%%

Choose distinct $`x,y,z`, and set $`\Gamma` to the single binding $`y:A`. In `λy:A. x`, use alpha-renaming to separate the local binder from the free name of the argument $`u = y`. The resulting abstraction is `λz:A. y`. Its body lookup uses $`y:A` from $`\Gamma`, even after $`z:A` has been introduced. Both this term and the incorrectly captured `λy:A. y` can receive type $`A\rightarrow A`; type equality alone cannot detect a change of binding.

To distinguish two terms which both have type `A→A`, supply a context that can observe which binding they read. Instantiate the base type with Bool and supply the external value true for `y`. Apply the function to false. After capture-avoiding substitution the closed application is `(λz:Bool. true) false`. Its body does not depend on the argument, so beta reduction returns true. After the accidental capture the closed application is `(λy:Bool. y) false`, which returns false. The observation takes place in the Boolean fragment from Chapter 16. All the applications and intermediate terms have types, including the ones constructed from the incorrect substitution.

The lemma proved in this chapter constrains the result type of a specifically defined syntactic operation. It cannot serve as that operation's sole specification. For the two function bodies above, Chapter 13 supplies a second test: before closing the surrounding context, the first abstraction still has the free variable `y`, whereas the second has no free variables. The free-variable calculation detects the lost dependency before running a single step. The Boolean application subsequently shows that this syntactic difference can affect a closed program's observable result.

# Exercises
%%%
tag := "ch17-s5"
number := false
%%%

1. Type $`\left( {f\, x} \right)\left\lbrack {u/x} \right\rbrack` from $`f:A\rightarrow B` in $`\Gamma` and $`\Gamma \vdash u:A`. Indicate which premise uses the substitution hypothesis.
2. Change the local binder type to $`C` in §17.4, choosing $`C` distinct from $`A`. What goes wrong with the type of the captured result?
3. Why could the proof of weakening fail if context extension were allowed to overwrite an existing name?

*Further problem.* Prepare the beta case of Chapter 18 with an open value. Let `Γ = f:A→B`, let `V = λy:A. f y`, and consider `(λg:A→B. λf:A. g f) V`. Derive its type, take the call-by-value beta step, and instantiate Theorem 17.2 under the remaining binder. What would literal replacement do?

# Reading for the Seminar
%%%
tag := "ch17-s6"
number := false
%%%

*Definitions · 10 minutes.* Write down the domains of both maps in the substitution theorem.

*Joint proof · 30 minutes.* Derive the abstraction case from its body premise. Ask the group to name the context in which the argument must be typed immediately before induction.

*Proof review · 20 minutes.* Compute Exercise 2 with and without renaming. Mark the typing rule whose lookup changes.

*Facilitator’s hint.* Circle the binder that will still be in scope after substitution. Weakening adds exactly its assumption to the argument derivation.

# Solutions
%%%
tag := "ch17-s7"
number := false
%%%

*1.* The left variable remains $`f` by ordinary lookup. The right variable $`x` is replaced by $`u` and uses the given derivation at $`A`. Application yields $`B`.

*2.* Capture-avoiding substitution produces `λz:C. y` of type $`C\rightarrow A`. Textual capture produces `λy:C. y` of type $`C\rightarrow C`. Its body can no longer use the old $`y:A` lookup.

*3.* Overwriting $`x:A` by $`x:B` with distinct types destroys a previous typing of the term $`x`. The inclusion premise in Lemma 17.1 specifically preserves the types of existing names.

*Further problem.* Choose `w` fresh and represent the inner function as `λw:A. g w`. Under `Γ,g:A→B,w:A`, application types `g w:B`. Discharging `w` gives `A→B`, and discharging `g` gives `(A→B)→(A→B)`. Separately, lookup of `f` in `Γ,y:A` and application to `y` give $`\Gamma \vdash V : A\to B`. The source application has type `A→B`. Its operand is an abstraction, so call-by-value beta yields `λw:A. (λy:A. f y) w`. Theorem 17.2 removes `g:A→B` using the two preceding typings. In its abstraction case the new base context is `Γ,w:A`. Weakening gives $`\Gamma,w:A \vdash V : A\to B`; lookup types `w:A`, so application gives `V w:B`. Abstracting `w` recovers the source result type. Literal replacement under the original spelling would bind the argument's free `f` to a local of type `A`. Taking `A` as a base type makes the resulting application of that local to `y` untypable. The open source rules out invoking closed progress here, but preservation and Theorem 17.2 both permit this context.
