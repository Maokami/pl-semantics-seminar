import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Structural Subtyping" =>
%%%
tag := "ch22"
file := "chapter-22"
%%%

[Chapter PDF](print/chapter-22.pdf) · [Session 23](seminar/index.html#week-23)

A function selecting the field `n` can use a record with both `n` and `flag`. The function’s body explains which part of its input must be present. The typing relation can express that requirement without naming a declared class for either record.

*Sources.* Pierce, _Types and Programming Languages_, §11.8 on records, then §§15.1–15.3 on subsumption, subtyping and safety. Read the typing rule for projection before trying the subtyping example. For an algorithmic presentation see §16.1. [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Records and projection
%%%
tag := "ch22-s1"
%%%

A record type lists a finite collection of distinct labels with their field types. Here labels identify fields independently of list order. A record term gives a term for each listed label. If every field term has its specified type, the complete record has the corresponding record type. If $`r` has a record type containing $`l:A`, projection `r.l` has type $`A`. Records are immutable in this chapter. At runtime a record of values is a value, and projecting from it returns the value at the chosen label.

A *subtyping judgment* $`S\mathrel{<:}T` authorizes use of a value of type $`S` wherever a value of type $`T` is expected. Read the colon following the inequality sign as part of the symbol. Subsumption extends typing with one rule: from $`\Gamma \vdash t:S` and $`S\mathrel{<:}T`, conclude $`\Gamma \vdash t:T`. This permits more than one type for a term. Subsumption is a typing step, with no new evaluation rule.

The label in a projection identifies a contract that must hold for every value of the receiver type. In context `r:{n:Nat, flag:Bool}`, projection can derive both `r.n : Nat` and `r.flag : Bool` directly. We may first subsume this very same variable to type `{n:Nat}` and then still derive the first projection. If a function parameter is declared only at that narrower type, its body can construct the first derivation but cannot recover a premise for the second. Some callers may pass a record which contains only `n`, so the missing premise reflects a real execution possibility.

This also distinguishes field order from field identity. The type describing `{flag=true, n=0}` offers the same two projections as the one for `{n=0, flag=true}`. The lookup premise refers to the label and its associated type, independently of the position where the field was printed. Distinctness of labels ensures this correspondence is functional. If a record literal could declare two different fields both named `n`, the typing and evaluation rules would need an additional convention about which occurrence a projection selects. Rejecting duplicate labels makes the stated rule unambiguous.

# Structural rules
%%%
tag := "ch22-s2"
%%%

Every type is a subtype of itself, and subtyping composes transitively. Distinct base types here have no subtyping relationship. For two record types $`S,T`, require that for *every* field $`l:A` of $`T`, the source $`S` contains the same label at some type $`B` with $`B\mathrel{<:}A`. When the common field types agree, a record may have additional fields (width). Refining the type of a common field gives depth subtyping. Selecting a field guaranteed by $`T` is then justified at $`S`, and a field value delivered with type $`B` may be used at $`A`.

For arrow types the condition is

$$`\left( {A_{1}\rightarrow B_{1}} \right)\mathrel{<:}\left( {A_{2}\rightarrow B_{2}} \right)\quad\text{if}\quad A_{2}\mathrel{<:}A_{1}\quad\text{and}\quad B_{1}\mathrel{<:}B_{2}.`

A client promises only an $`A_{2}`. We must therefore feed such a value to a function written to expect $`A_{1}`. Its result has type $`B_{1}`, which the client must be able to use at $`B_{2}`. The reversal for the domain is called *contravariance*.

For a higher-order example, let `N = {n:Nat}` and `R = {n:Nat, flag:Bool}`. An actual function of type `N→R` can be used by a client expecting a function of type `R→N`. The client will supply an `R`, which can be passed to the actual function by the width judgment `R <: N`. The actual result is an `R`, from which the client may select the promised `n` or pass it on as an `N`. In this example both subtyping premises happen to read `R <: N`. Their roles differ because the argument crosses from the client to the implementation, while the result crosses back.

The rule can be reconstructed from a typing derivation for a wrapper. Assume `f:N→R` and consider `λr:R. f r`. Inside the abstraction, subsume `r:R` to `N`, apply `f` to obtain `R`, and subsume the result to `N`. Discharging `r` gives the required type `R→N`. This wrapper exhibits the directions of both obligations with ordinary typing rules. The subtyping judgment itself permits using `f` at the new arrow type directly.

For these immutable records, hiding a field can be represented explicitly by projection to a smaller record. The adapter first hides information in the client's argument before calling the supplied function, then hides information in the returned record. Its type checks both arrow directions. The equation for observing the field follows by reducing the definitions.

```lean
namespace RecordVariance
structure Narrow where
  n : Nat
structure Rich where
  n : Nat
  flag : Bool

def forget (x : Rich) : Narrow := ⟨x.n⟩

def adapt (f : Narrow → Rich) : Rich → Narrow :=
  fun x => forget (f (forget x))

example (f : Narrow → Rich) (x : Rich) :
    (adapt f x).n = (f ⟨x.n⟩).n := rfl
end RecordVariance
```

# A complete application
%%%
tag := "ch22-s3"
%%%

Write $`N` for `{n:Nat}` and $`R` for `{n:Nat, flag:Bool}`. Let $`r` be `{n=0, flag=true}`. The literal axioms and record formation give $`r:R`. For the subtyping judgment $`R\mathrel{<:}N`, the target requests just `n`, which the source provides at Nat, and reflexivity gives the common field comparison. Subsumption gives $`r:N`.

In context $`p:N`, lookup gives $`p:N` and projection gives `p.n` type Nat. Abstraction types `λp:N. p.n` at $`N\rightarrow\text{Nat}`. Application can now use the subsumed operand, yielding Nat in the empty context. Beta reduction gives `r.n` and projection returns zero. The extra field is present in the runtime record throughout.

Reversing the record rule would let a client with only $`N` pass its record to code that reads `flag`. Applying that code to `{n=0}` would reach a missing projection. The same example rules out covariance in the domain of an arrow: a function that expects $`R` cannot in general be called with an $`N`.

The beta step in the displayed program reveals how subsumption changes a preservation proof. Before the step the source is an application at Nat. Its body projection was checked under `p:N`. For substitution we must therefore establish that the actual operand is typable at *exactly that parameter type*. The record literal's introduction yields `r:R`. The premise `R <: N` supplies a subsumption step to `r:N`. Now the substitution lemma can conclude that the substituted body `r.n` has type Nat. Separately, inspecting the literal's fields explains why the projection actually evaluates to zero. One use of the literal is through its interface in a typing derivation; the other is through its stored field in a reduction rule.

There is another typing derivation for the same application. Subtype the operator from `N→Nat` to `R→Nat` and keep the operand at its introduced type `R`. The application rule again yields Nat. Thus examining an application derivation may encounter different intermediate domains even when the evaluated term is identical. A checker that tries to guess every possible subsumption step would spend work exploring choices like these. Pierce's algorithmic account in §16.1 begins by isolating judgments about subtyping itself.

# Exercises
%%%
tag := "ch22-s4"
number := false
%%%

1. Show that $`\left( {N\rightarrow\text{Bool}} \right)\mathrel{<:}\left( {R\rightarrow\text{Bool}} \right)`. Explain what the client supplies.
2. Add a nested record field `meta` to a source and a target type so that checking their relation requires both width and depth.
3. Can we justify writable record fields by exactly the same depth rule? Use $`R\mathrel{<:}N` to give a bad write.

*Further problem.* Let `N={n:Nat}`, `R={n:Nat,flag:Bool}`, and consider the immutable object type `S={run:N→R, tag:Bool}`. Can a value at `S` be passed to a client expecting `T={run:R→N}`? Derive all premises. Can that same client read the tag through its parameter at `T`?

# Reading for the Seminar
%%%
tag := "ch22-s5"
number := false
%%%

*Definitions · 10 minutes.* Derive the type of the projection under the narrow parameter assumption.

*Joint proof · 30 minutes.* Type the two-field literal at its full type, then assemble the complete application. Mark the only subsumption required in this derivation.

*Proof review · 20 minutes.* Attempt to reverse the type comparison. Give a projection that becomes stuck, then derive the correct function-domain direction.

*Facilitator’s hint.* Begin a record comparison with the labels demanded by the target. Starting with every field of the source would reject valid width examples.

# Solutions
%%%
tag := "ch22-s6"
number := false
%%%

*1.* The source accepts any $`N`, and a client of the target promises an $`R`. Since $`R\mathrel{<:}N`, every promised argument is acceptable. The result is unchanged.

*2.* Compare `{meta:{n:Nat,flag:Bool}, tag:Bool}` to `{meta:{n:Nat}}`. Forgetting `tag` uses outer width. Comparing the shared `meta` types uses depth with an inner width comparison.

*3.* If a writable slot containing $`R` could be viewed as a slot containing $`N`, a client could store `{n=0}` through the latter view. Another client using the original view could then read the missing `flag`. Read-only fields avoid this change of representation.

*Further problem.* Record comparison begins with the labels of the *target*. Its only label is `run`, which exists in the source, and depth requires `N→R <: R→N`. The arrow-domain premise compares the expected input to the actual input, giving `R <: N`. The arrow-codomain premise compares actual output to expected output, also giving `R <: N`. Each of these is a record-width comparison: the required label `n` is present with equal type Nat. The extra source label `tag` is unconstrained. These derivations justify `S <: T` and then subsumption of a concrete value from `S` to `T`. In the client body, its parameter's lookup gives `T`, so projection of `run` yields `R→N`. Projection of `tag` would require a type guaranteeing that label. A value with only a suitable `run` can also inhabit `T`, so the public assumption cannot justify this second projection, regardless of the particular actual argument's fields.
