import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "References and Store Typing" =>
%%%
tag := "ch31"
file := "chapter-31"
%%%

[Chapter PDF](print/chapter-31.pdf) · [Session 32](seminar/index.html#week-32)

Two variables may contain the same address. Writing through one changes the value that a later read through the other will return. An ordinary term context records the types of the variables, but preserving types during allocation also requires a typing for the newly created address.

*Sources.* Pierce, _Types and Programming Languages_, chapter 13, especially §§13.3–13.5, pp. 159–170. Read the allocation case of preservation and note its existentially quantified extension of the store typing. Compare §22.7 before attempting Exercise 3. [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Terms, stores and locations
%%%
tag := "ch31-s1"
%%%

Extend the typed call-by-value language with `ref t` for allocation, `!t` for reading, and `t := u` for assignment returning unit. A location is a runtime value. A store $`\mu` maps allocated locations to values. The one-step judgment $`\langle t,\mu\rangle \to \langle t',\mu'\rangle` relates a term and store to their successors. Once operands are values, allocation chooses a fresh location $`l`, inserts its initial value $`v`, and returns $`l`. Reading $`l` returns $`\mu(l)` without changing the store. Assignment to $`l` replaces its contents and returns unit. The other steps evaluate operands from left to right. Locations are opaque, and fresh choices can be renamed consistently.

Use this program, taking the semicolon as a let whose unit result is discarded:

```
let r = ref 0 in let s = r in (s := 4; !r)
```

In an empty store allocation gives $`l` with $`\mu(l) = 0`. The next let binds $`s` to the same location. The assignment updates $`\mu(l)` to 4. After it returns unit, reading the first reference returns 4. A copied reference preserves identity of the location; it does not allocate a second cell.

Compare copying an address with allocating a second cell initialized from the same value. Begin with `r = ref 0` and choose `s = ref (!r)`. The read returns the integer zero. Allocation now requires an address fresh for the store already containing the cell of `r`, so the two bindings have different addresses. Writing four to `s` changes the newly allocated cell alone. Reading `r` still yields zero. Compare this trace with the aliasing program above. Immediately before the final read, the values of the two source variables have the same *types* in both programs. What distinguishes the two stores is which locations those references designate.

The choice of fresh address has a simple proof obligation. Suppose one execution called its first two locations `a,b` and another called them `c,d`, in the same allocation order. The map taking `a` to `c` and `b` to `d` is a bijection between the allocated sets. Extending this map consistently through both the term and store preserves each lookup and update in the trace. In particular it preserves the fact that two references designate the same location. This is why the integer observation at the end is independent of the allocator's particular fresh names.

# A type for each cell
%%%
tag := "ch31-s2"
%%%

A store typing $`\Sigma` maps each allocated address to the type of its *contents*. The judgment $`\Gamma\,;\,\Sigma \vdash t : A` assigns type $`A` to $`t` with variable context $`\Gamma` and store typing $`\Sigma`. When $`\Sigma(l) = A`, the term $`l` has type $`\text{Ref}\ \, A`. If $`t:A`, then `ref t` has reference type at $`A`; reading a reference at $`A` returns $`A`. Assignment requires a reference at $`A` and a value-producing expression at the same $`A`.

A closed store is well typed at $`\Sigma` if the domains agree and every value $`\mu(l)` has the type $`\Sigma(l)` when typed under the empty term context and the *whole* store typing. Using the whole mapping allows cells to contain references to other cells, even through cycles. The definition checks the finite syntax of stored values against known location types.

For a small store that genuinely needs the whole store typing, take a location `a` whose contents type is `Unit → Unit`. Store in it the closed value `λu:Unit. (!a) u`. To check the cell, type the body in the variable context extended by `u:Unit` and the fixed location context containing `a:Unit → Unit`. The location term has reference type, dereference has the declared function type, and application to `u` gives Unit. Abstraction then gives exactly the declared contents type. A direct recursive attempt to type the cell by expanding the *contents* of every encountered address would try to type this very cell again. Looking the address up in the finite store typing ends the typing derivation.

This example can arise operationally. First allocate a cell initialized with the identity on Unit, then assign to it a closure that calls the function currently stored at that address. The new value has the same contents type as the old one. Evaluating the stored closure as a value terminates immediately, while calling it can read the cell again and repeat indefinitely. The store typing says what sort of result a terminating call can deliver. It imposes no well-foundedness condition on the graph of references reached from a closure.

# Preservation under allocation
%%%
tag := "ch31-s3"
%%%

Suppose a closed well-typed configuration takes one step. The preservation statement allows some $`\Sigma'` extending $`\Sigma` without changing old bindings, such that the target term has its old type and the target store is well typed at $`\Sigma'`. To prove the allocation case, invert typing of `ref v` to obtain $`v:A`. Choose $`l` fresh for the store. Domain equality makes it fresh for $`\Sigma`. Set $`\Sigma' = \Sigma\left\lbrack {l\mapsto A} \right\rbrack`. By location typing, the returned $`l` has the required reference type under $`\Sigma'`. Weakening of location assumptions types every old stored value and $`v` under the extension. Old cells retain their required types, and the new cell contains exactly $`v:A`. The extended domains agree. This proves both parts.

In the example the store typing grows from empty to one binding $`l:\text{Nat}`. Subsequent aliasing and assignment leave that typing intact. Assignment preserves it by requiring the new value to have precisely the content type already assigned to the cell.

It helps to compare allocation with an ordinary assignment in the statement of preservation. Assume the configuration contains `a := v`, all subterms are values, and the store typing assigns contents type `A` to `a`. Inversion of the assignment typing gives a derivation for `v : A` in the old store typing. The operational result is unit and the updated store has the same domain. To check a cell `b` of the new store, split on equality with `a`. In the equal case the stored value is `v` and inversion supplied exactly the needed type. In the other case its old value and its declared type are unchanged. Thus we may choose the witness for the existential store typing to be the old typing itself.

At allocation there can be no such witness. The new address occurs as the *term returned by the step*, and its typing rule requires a lookup in the new map. Enlarging just the store of values would leave that lookup undefined. Conversely, enlarging just the type map would claim that a fresh address was available before any value had been installed. The two updates are made together. On a later dereference, membership in the type map and equality of map domains then provide exactly the premise that a value can be retrieved at the address.

The map argument in allocation can be checked separately from the typing rules. The predicate `T` below checks a value against a contents type in the *new* location context. For an old occupied cell, the store-typing weakening lemma must supply this predicate before applying the example. The local argument in fact also handles overwriting a cell, so freshness is needed elsewhere in allocation preservation.

```lean
def atLocation {A : Type} (m : Nat → Option A) (l : Nat) (a : A) :
    Nat → Option A :=
  fun i => if i = l then some a else m i

def checkedCell {V Ty : Type} (T : V → Ty → Prop) :
    Option V → Option Ty → Prop
  | none, none => True
  | some v, some t => T v t
  | _, _ => False

example {V Ty : Type} (T : V → Ty → Prop) (store : Nat → Option V)
    (types : Nat → Option Ty) (old : ∀ i, checkedCell T (store i) (types i))
    (l : Nat) (v : V) (t : Ty) (hv : T v t) :
    ∀ i, checkedCell T (atLocation store l v i) (atLocation types l t i) := by
  intro i
  by_cases h : i = l
  · simpa [atLocation, h, checkedCell] using hv
  · simpa [atLocation, h] using old i
```

The observation for allocation is the value and the resulting store up to a consistent renaming of fresh locations. Two stores with the same integer values may behave differently after a write if two variables alias the same location.

# Exercises
%%%
tag := "ch31-s4"
number := false
%%%

1. Replace `let s = r` by `let s = ref (!r)`. What does the final read return?
2. Why would preservation with the same fixed $`\Sigma` fail immediately for allocation?
3. Suppose let generalization allowed `let r = ref (λx. x)` to give $`r` scheme $`\forall X.\ \text{Ref}\ \,\left( {X\rightarrow X} \right)`. Give a bad write and read using different instances.

*Further problem.* Renaming a freshly allocated location. Suppose `ref v` can step at the same store by choosing either fresh address `a` or fresh address `b`. Compare the two successor configurations by swapping these addresses. Define the action of this swap on terms, stores and store typings. Explain why the swap fixes the initial configuration and carries one typed allocation result to the other, even when `v` contains references.

# Reading for the Seminar
%%%
tag := "ch31-s5"
number := false
%%%

*Definitions · 10 minutes.* Trace the aliasing example with a table containing one row per location.

*Joint proof · 30 minutes.* Prove both target judgments in the allocation case. Mark the weakening step for the old cells and the new value separately.

*Proof review · 20 minutes.* Use the two proposed instances of a polymorphic reference to break safety. Identify which location is shared.

*Facilitator’s hint.* The type of the location as a term includes Ref. The entry in the store typing records only the type of its contents.

# Solutions
%%%
tag := "ch31-s6"
number := false
%%%

*1.* The second allocation copies the integer zero into a fresh cell. Writing through $`s` changes the new cell, so the final read from $`r` returns zero.

*2.* A fresh address has no entry in the old typing, so the rule typing the result location cannot apply and the new store domains disagree.

*3.* Instantiate at Nat to write `λn:Nat. succ n`. Instantiate the same reference at Bool and apply the function read from it to true. Both accesses reach one allocated cell; the resulting `succ true` is stuck. Restricting generalization at effectful allocation prevents the two incompatible assumptions.

*Further problem.* Let the permutation exchange `a` and `b` and fix every other location. On terms it renames each location literal wherever it occurs, including inside an abstraction, leaving variable names and constructors intact. On stores it sends a cell with key `ℓ` and value `w` to the cell with key the renamed `ℓ` and value the renamed `w`. On a store typing it renames the keys. The type expressions of this language contain no location names.

Assume the initial term and store are well typed with matching store and type domains. Every location literal in a typed term must have a lookup in that type map, by induction on typing. The same applies to values inside cells. Neither fresh address therefore occurs anywhere in the initial configuration, so the permutation fixes it and also fixes `v`. After allocating at `a` the result term is `a` and the store adds `a ↦ v`. Renaming gives exactly result term `b` and added cell `b ↦ v`. The extended typing at `a` becomes the corresponding extension at `b`, and every location lookup used for checking the result is renamed consistently.
