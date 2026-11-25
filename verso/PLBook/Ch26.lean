import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Existential Types and Abstract Data Types" =>
%%%
tag := "ch24"
file := "chapter-24"
%%%

[Chapter PDF](print/chapter-24.pdf) · [Session 25](seminar/index.html#week-25) · [Session 26](seminar/index.html#week-26)

A counter implementation provides an initial counter, a way to advance it, and a way to read it. The client needs the type of each operation and the guarantee that the three operations agree on one counter representation. The concrete representation can remain private.

*Sources.* Pierce, _Types and Programming Languages_, §§24.1–24.2, pp. 363–376. Follow the representation type from packaging to unpacking. For comparison read Reynolds, _Theories of Programming Languages_, §18.2 on existential types. The record notation below is the immutable notation of Chapter 24. [Pierce.](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf) [Reynolds.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Packaging a representation
%%%
tag := "ch24-s1"
%%%

Write $`\exists X.T` for the type of packages that consist of a well-formed witness type $`A` and an implementation value of type $`T\left\lbrack {A/X} \right\rbrack`. Introduce it by `pack [A, v] as ∃X.T`. The type annotation specifies which occurrences in the public interface are abstract. Many packages with different choices of $`A` may have exactly this public type.

Let $`T(X)` denote the record `{init:X, next:X→X, read:X→Nat}` and $`C = \exists X.T(X)`. Represent counters by Nat, take the initial value zero, `next = λn:Nat. succ n`, and `read = λn:Nat. n`. Each field has the type obtained by replacing $`X` with Nat. Record formation therefore gives $`T\left( \text{Nat} \right)` and packaging at $`C` hides the chosen witness. The witness is chosen by the implementer; in Chapter 25 a caller of a universal value chose the argument type.

There is genuine information in the ascription after `as`. Consider the concrete payload `(2,5)` with witness Nat. The types `∃X.X×Nat` and `∃X.Nat×X` are both valid ascriptions: replacing `X` by Nat in either body gives the payload type `Nat×Nat`. Yet a client of the first interface can return the second projection as a natural, observing five; a client of the second can return the first projection as a natural, observing two. In the first case the other projection has the fresh abstract type introduced by unpacking. No operation in that interface converts its result to Nat. A third ascription, `∃X.X×X`, reveals that both components have the same type while withholding the concrete identity of that type.

The counter signature exploits exactly this ability to disclose selected equalities. The result type of initialization, the argument and result of advancement, and the argument of reading all mention one bound name. The client may therefore pass a value produced by any operation returning that name to either operation accepting it. If instead the three fields were packaged using separate existential quantifiers, opening the packages would provide independent names. Even well-typed implementations that secretly chose Nat three times could no longer support this chain by the public field types alone.

# Opening a package
%%%
tag := "ch24-s2"
%%%

The term `unpack [Y,p] = q in b` first evaluates $`q` to a package. In its body it introduces a fresh abstract type name $`Y` and a term name $`p:T(Y)`. If $`q:C` and $`b:B` can be typed under these additional assumptions, the whole expression has type $`B` in the original context. The type $`B` must be well formed outside the scope of $`Y`. A type containing a free occurrence of $`Y` cannot escape this opening.

Consider `unpack [Y,p] = counter in p.read (p.next p.init)`. Projection gives `p.init` type $`Y` and `p.next` type $`Y\rightarrow Y`. Application gives another $`Y`. Projecting `p.read` and applying it yields Nat, which is well formed in the outer context. Operationally opening `pack [A,v]` substitutes $`A` for the type binder and $`v` for the module name in the body, avoiding capture. For the representation above the body calls successor on zero, then reads the resulting 1.

Two separate openings introduce different abstract type names. Even if two packages happen to contain the same representation, the typing rules alone cannot supply an equality between the fresh names. A client must keep the operations and counter values from each opening together.

A client can retain an operation after leaving the scope of the opening. Consider `unpack [Y,p] = counter in λu:Unit. p.read (p.next p.init)`, where Unit has the single value `unit`. In the body of the lambda, `p.next p.init` has type `Y` and applying `p.read` produces Nat. Introducing the unused Unit argument gives `Unit→Nat`. This result type is well formed outside the opening. Later application of the returned closure to `unit` may use the captured implementation, which shares its private representation with its captured operations. The caller receives only the resulting natural.

Changing the body to `λu:Unit. p.next p.init` changes the inferred arrow to `Unit→Y`. A free occurrence of the representation name in the codomain violates the same scope check as returning the counter directly. An interface can expose an advanced counter by packaging it again. Inside the opening, form the record with `init = p.next p.init`, `next = p.next`, and `read = p.read`. It has type `T(Y)`. Pack it using witness `Y` and ascription `C`; the result type is the closed existential type `C`. A subsequent client obtains a fresh type name on opening this new package and can read its advanced initial value.

# A second implementation
%%%
tag := "ch24-s3"
%%%

Use pairs of naturals for the witness. Store a current count in the first component and the number of advances in the second. Use $`\left( {0,0} \right)` for `init`, increment both components in `next`, and project the first in `read`. Writing $`A = \text{Nat} \times \text{Nat}`, the constructor, updater and reader again supply all fields of $`T(A)`. The same client therefore typechecks once at $`C` and computes the integer 1 using either package.

Typing a common interface alone does not assert that implementations compute equal observations. To explain this example, relate a natural $`n` and a pair $`\left( {a,b} \right)` when $`n = a`. The initial values are related, related inputs stay related after `next`, and reading related inputs gives the same natural. By induction on the number of advances, any client consisting of initialization, finitely many advances and a single read obtains the same observation from these implementations. A full representation-independence theorem for arbitrary higher-order clients requires a corresponding relation for all client types.

We can extend the induction to clients that inspect an observation before deciding whether to advance again. Let a client be a finite tree with three constructors: read the current value, advance and continue with a subtree, or inspect whether the current observation is zero and choose between two subtrees. The result of each client is a natural. For any two implementations, assume a relation on their states, a proof that advancing preserves the relation, and a proof that related states yield equal readings. Structural induction on the client tree now proves equal results from every pair of related states. In the branch case the two guards read equal naturals, hence choose corresponding subtrees. The induction hypothesis applies there to the original related states. The advance case instead needs the hypothesis at a *new* pair of states. This is why the theorem quantifies over all related starting states at each subtree.

The code states this argument for arbitrary operations. For our two packages use the relation saying that the left state equals the first component of the right state. Applying the theorem at zero and the initial pair then proves equality of observations for every client described by the three constructors.

```lean
namespace CounterClients
inductive Client where
  | read
  | next (rest : Client)
  | branchZero (yes no : Client)

def observe {S : Type} (step : S → S) (readout : S → Nat) :
    Client → S → Nat
  | .read, s => readout s
  | .next k, s => observe step readout k (step s)
  | .branchZero yes no, s =>
    if readout s = 0 then observe step readout yes s
    else observe step readout no s

theorem simulation {S T : Type} (ss : S → S) (ts : T → T)
    (sr : S → Nat) (tr : T → Nat) (R : S → T → Prop)
    (stepEq : ∀ s t, R s t → R (ss s) (ts t))
    (readEq : ∀ s t, R s t → sr s = tr t)
    (k : Client) (s : S) (t : T) (h : R s t) :
    observe ss sr k s = observe ts tr k t := by
  induction k generalizing s t with
  | read => exact readEq s t h
  | next k ih => exact ih _ _ (stepEq s t h)
  | branchZero yes no ihYes ihNo =>
    simp only [observe, readEq s t h]
    split
    · exact ihYes _ _ h
    · exact ihNo _ _ h
end CounterClients
```

# Relational parametricity for simply typed clients
%%%
tag := "ch24-client-relation"
%%%

After opening a counter, consider the client `read ((λf:X→X. f (f init)) next)`. The argument to the lambda is itself an operation on the hidden representation. With the natural counter the two applications of `f` produce 2. With the pair counter they produce (2,2). Both reads return 2. We will prove equality of observations for every client in a language that permits functions as arguments and results.

A client type is $`A ::= X \mid \mathrm{Nat} \mid A\to A`. Terms are variables, abstractions and applications, with the typing rules of Chapter 18. The counter fields are free variables with types `init:X`, `next:X→X`, and `read:X→Nat`. Fix two representation sets $`S,T` and any relation $`R\subseteq S\times T`. Write $`V_S(A)` for the interpretation of a type: $`V_S(X)=S`, $`V_S(\mathrm{Nat})=\mathbb N`, and $`V_S(A\to B)` is the set of total functions from $`V_S(A)` to $`V_S(B)`. Define $`V_T` in the same way. This language is pure and has no recursion. An environment assigns each free variable a value of its interpreted type. The denotation of a term in an environment uses lookup, function formation and function application, respectively.

Define a *logical relation* $`R_A` between $`V_S(A)` and $`V_T(A)` by induction on the type. At $`X` use $`R`. At Nat use equality. At an arrow use
$$`f\ R_{A\to B}\ g \quad\Longleftrightarrow\quad \forall x\in V_S(A),\ y\in V_T(A),\quad x\ R_A\ y\ \Longrightarrow\ f(x)\ R_B\ g(y).`
Environments are related when they assign related values to each variable at its declared type. For the counter context, these are exactly the three obligations from §26.3: related initial values, preservation by advancement, and equality after reading.

*Fundamental theorem.* For every judgment $`\Gamma\vdash e:A` and related environments $`\rho,\eta` for $`\Gamma`, the two interpretations of $`e` are related by $`R_A`. Induct on the typing derivation, allowing the environments to vary.

1. *Variable.* Lookup in the two environments gives a related pair by the hypothesis for that variable.
2. *Abstraction.* To compare the two functions denoted by $`\lambda x.u`, take any related arguments at the domain type. Extend the two environments by this pair. The new variable satisfies its relation by choice of arguments and each older variable retains its original pair. The induction hypothesis for the body in these extended environments gives the codomain relation required at the arrow.
3. *Application.* The operator hypothesis gives two functions related at the arrow type. The operand hypothesis supplies a related pair at its domain. Applying the arrow clause to this pair gives the conclusion.

*Representation independence.* Take the two implementations of §26.3 and the relation $`n\ R\ (a,b)` exactly when $`n=a`. Initialization gives $`0=0`, advancement preserves equality by successor, and the two reads return the equal first coordinates. Hence the counter environments are related. For any client of result type Nat, the fundamental theorem gives equality of its two denotations. For a function-valued result the conclusion is the arrow relation, so a client may pass that result on to a higher-order function. The observable equality follows when the whole client returns Nat.

In Lean, `Term Γ a` encodes a typing derivation. A variable position `here` selects the newest binder and `there` steps past it. `extend` therefore changes only the new binding. The proof works for any pair of representation types and any relation on them.

```lean
namespace TypedCounter

inductive Ty where
  | rep | nat | arr (a b : Ty)

def Val (S : Type) : Ty → Type
  | .rep => S
  | .nat => Nat
  | .arr a b => Val S a → Val S b

def Rel {S T : Type} (R : S → T → Prop) :
    (a : Ty) → Val S a → Val T a → Prop
  | .rep => R
  | .nat => Eq
  | .arr a b => fun f g =>
      ∀ x y, Rel R a x y → Rel R b (f x) (g y)

inductive Var : List Ty → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

inductive Term : List Ty → Ty → Type where
  | var : Var Γ a → Term Γ a
  | lam : Term (a :: Γ) b → Term Γ (.arr a b)
  | app : Term Γ (.arr a b) → Term Γ a → Term Γ b

abbrev Env (S : Type) (Γ : List Ty) :=
  ∀ {a}, Var Γ a → Val S a

def extend (ρ : Env S Γ) (x : Val S a) : Env S (a :: Γ)
  | _, .here => x
  | _, .there i => ρ i

def denote {S : Type} : Term Γ a → Env S Γ → Val S a
  | .var i, ρ => ρ i
  | .lam body, ρ => fun x => denote body (extend ρ x)
  | .app f u, ρ => denote f ρ (denote u ρ)

def EnvRel (R : S → T → Prop) (ρ : Env S Γ) (η : Env T Γ) :=
  ∀ {a} (i : Var Γ a), Rel R a (ρ i) (η i)

theorem fundamental (R : S → T → Prop) (e : Term Γ a)
    (ρ : Env S Γ) (η : Env T Γ) (h : EnvRel R ρ η) :
    Rel R a (denote e ρ) (denote e η) := by
  induction e with
  | var i => exact h i
  | app f u ihf ihu => exact ihf ρ η h _ _ (ihu ρ η h)
  | lam body ih =>
    intro x y hxy
    apply ih (extend ρ x) (extend η y)
    intro t i
    cases i with
    | here => exact hxy
    | there j => exact h j

end TypedCounter
```

*Further reading: System F.* For a closed term $`p:\forall X.\,X\to X` in pure, total System F, Reynolds’s abstraction theorem supplies preservation of every relation at every pair of instantiations. Fix a type and one value $`a`. Instantiate both sides at that type and choose the singleton relation $`\{(a,a)\}`. Preservation puts the pair of results at $`a` in this singleton, so each result equals $`a`. This corollary uses the universal-type case of the System F theorem. The Lean proof above establishes the simply typed theorem with one abstract type. [Pfenning, Representation Independence, §1.](https://www.cs.cmu.edu/`fp/courses/15814-f25/lectures/16-independence.pdf) [Pfenning, Parametricity.](https://www.cs.cmu.edu/`fp/courses/15814-f19/lectures/16-parametricity.pdf)

# Exercises
%%%
tag := "ch24-s4"
number := false
%%%

1. Is `unpack [Y,p] = counter in p.init` typable with result Nat? What if the body returns `p.read p.init`?
2. Construct an implementation at $`C` that always returns zero from `read`. Give a client distinguishing it from the first implementation.
3. Explain why using the first package’s `next` on the second package’s `init` fails when checked only from the public interfaces.

*Further problem.* Package the counter with witness Nat but represent the logical initial count by one, use successor for advancement, and use predecessor for reading. Prove agreement with the original counter for all finite clients of §26.3, including clients that branch on a reading. Is equality of machine states an invariant?

# Reading for the Seminar
%%%
tag := "ch24-s5"
number := false
%%%

*Session 25 · Opening an existential package.* Read §§26.1–26.3.

*Definitions · 10 minutes.* Write the three field types with an abstract representation, then instantiate them with Nat.

*Joint proof · 30 minutes.* Derive the client judgment under a fresh type name and check that its result type survives leaving the scope. Repeat with the pair implementation and compare the execution.

*Proof review · 20 minutes.* Prove the relation in §26.3 for one advance and one read. Explain what the common interface guarantees even for the implementation in Exercise 2.

*Facilitator’s hint.* Keep the witness chosen inside the package on one part of the board and the fresh type variable available to the client on another.

*Session 26 · Representation independence.* Read §26.4. Spend 10 minutes evaluating the higher-order client with each implementation. In 30 minutes prove the fundamental theorem, keeping the two environments on the board throughout the abstraction case. In the last 20 minutes check the three field obligations and specialize the theorem to a natural result. Replace the second reader by the constant zero function and find the failed obligation. The System F corollary is optional.

# Solutions
%%%
tag := "ch24-s6"
number := false
%%%

*1.* The first body yields $`Y`. Identifying it with Nat would require an equality hidden by the package, and returning it directly would allow $`Y` to escape. Reading it first yields Nat, which passes the scope check.

*2.* Keep the natural witness and successor, but define `read = λn:Nat. 0`. The client of §26.2 observes zero there and one with the original package. Both satisfy the three field types.

*3.* The first operation expects $`Y_{1}` and the second package supplies $`Y_{2}`. The application rule requires equal types. The two open scopes supply no equation between the distinct names.

*Further problem.* Choose the relation `R(n,m)` meaning `m=n+1`, where `n` is the original state and `m` the offset state. Initialization establishes `R(0,1)`. If `m=n+1`, then `m+1=(n+1)+1`, which proves the relation for the two successor states. For every related pair, reading the left state yields `n` and reading the right yields `pred(n+1)=n`. These are exactly the two premises of the client-tree induction. At a read leaf the result follows from reading agreement. At an advance node apply the child hypothesis at the successor pair. At a zero test both readings are equal, so the evaluation of each implementation chooses the same child and the original pair still satisfies its hypothesis. Applying the conclusion to the initial pair proves the claim for every such finite client. Equality of the stored naturals is already false at initialization. Abstract observational agreement can therefore hold even for two witnesses that happen to be the same concrete type.
