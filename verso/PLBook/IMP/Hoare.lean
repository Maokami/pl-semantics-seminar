import PLBook.IMP.Determinacy

/-! Assertions, partial and total validity, and the proof systems of Sessions 11–13. -/

namespace PLBook.IMP

def substExpr (x : ident) (e : aexp) : aexp → aexp
  | .CONST n => .CONST n
  | .VAR y => if x == y then e else .VAR y
  | .PLUS a b => .PLUS (substExpr x e a) (substExpr x e b)
  | .MINUS a b => .MINUS (substExpr x e a) (substExpr x e b)

theorem evalSubst (a e : aexp) (x : ident) (s : store) :
    aeval s (substExpr x e a) = aeval (update x (aeval s e) s) a := by
  induction a with
  | CONST => rfl
  | VAR y =>
    simp only [substExpr, aeval, update]
    split <;> rfl
  | PLUS _ _ ha hb | MINUS _ _ ha hb => simp [substExpr, aeval, ha, hb]

abbrev Assertion := store → Prop
def substAssertion (Q : Assertion) (x : ident) (e : aexp) : Assertion :=
  fun s ↦ Q (update x (aeval s e) s)
def written {j : Nat} (φ : (Fin j → Int) → Prop) (args : Fin j → aexp) : Assertion :=
  fun s ↦ φ (fun i ↦ aeval s (args i))

theorem writtenSubst {j : Nat} (φ : (Fin j → Int) → Prop) (args : Fin j → aexp)
    (x : ident) (e : aexp) :
    substAssertion (written φ args) x e = written φ (fun i ↦ substExpr x e (args i)) := by
  funext s
  simp only [substAssertion, written, evalSubst]

def Valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀ s t, P s → cexec s c t → Q t

theorem assignmentValid (Q : Assertion) (x : ident) (e : aexp) :
    Valid (substAssertion Q x e) (.ASSIGN x e) Q := by
  intro s t pre run
  exact assignmentResult run ▸ pre

/-- The second clause of Theorem 11.8, with any finite tuple of expressions. -/
theorem writtenAssignmentValid {j : Nat} (φ : (Fin j → Int) → Prop) (args : Fin j → aexp)
    (x : ident) (e : aexp) :
    Valid (written φ (fun i ↦ substExpr x e (args i))) (.ASSIGN x e) (written φ args) := by
  rw [← writtenSubst]
  exact assignmentValid _ _ _

theorem assignmentPrecondition (P Q : Assertion) (x : ident) (e : aexp) :
    Valid P (.ASSIGN x e) Q ↔ ∀ s, P s → substAssertion Q x e s := by
  constructor
  · exact fun h s pre ↦ h s _ pre .cexec_assign
  · exact fun h s t pre run ↦ assignmentValid Q x e s t (h s pre) run

theorem validSequence (left : Valid P c R) (right : Valid R d Q) : Valid P (.SEQ c d) Q := by
  intro s t pre run
  obtain ⟨m, first, second⟩ := sequenceExecution.mp run
  exact right m t (left s m pre first) second

theorem validConsequence (before : ∀ s, P' s → P s) (triple : Valid P c Q)
    (after : ∀ t, Q t → Q' t) : Valid P' c Q' :=
  fun s t pre run ↦ after t (triple s t (before s pre) run)

def guarded (P : Assertion) (b : bexp) (value : Bool) : Assertion :=
  fun s ↦ P s ∧ beval s b = value

/-- The six rules of Definition 12.2. -/
inductive Hoare : Assertion → com → Assertion → Prop where
  | skip : Hoare P .SKIP P
  | assign : Hoare (substAssertion Q x e) (.ASSIGN x e) Q
  | seq : Hoare P c R → Hoare R d Q → Hoare P (.SEQ c d) Q
  | cond : Hoare (guarded P b true) c Q → Hoare (guarded P b false) d Q →
      Hoare P (.IFTHENELSE b c d) Q
  | loop : Hoare (guarded P b true) c P → Hoare P (.WHILE b c) (guarded P b false)
  | consequence : (∀ s, P s → P₁ s) → Hoare P₁ c Q₁ → (∀ t, Q₁ t → Q t) → Hoare P c Q

private theorem loopValid (P : Assertion) (b : bexp) (c : com)
    (body : Valid (guarded P b true) c P) : Valid P (.WHILE b c) (guarded P b false) := by
  intro s t pre run
  generalize eq : com.WHILE b c = cmd at run
  induction run with
  | cexec_while_done test => cases eq; exact ⟨pre, test⟩
  | cexec_while_loop test first _ _ ih =>
    cases eq
    exact ih (body _ _ ⟨pre, test⟩ first) rfl
  | _ => cases eq

theorem hoareSound (derivation : Hoare P c Q) : Valid P c Q := by
  induction derivation with
  | skip => intro s t pre run; cases run; exact pre
  | assign => exact assignmentValid _ _ _
  | seq _ _ left right => exact validSequence left right
  | @cond P b c Q d _ _ yes no =>
    intro s t pre run
    cases run with
    | cexec_ifthenelse branch =>
      cases guard : beval s b with
      | false => exact no s t ⟨pre, guard⟩ (by simpa [guard] using branch)
      | true => exact yes s t ⟨pre, guard⟩ (by simpa [guard] using branch)
  | loop _ ih => exact loopValid _ _ _ ih
  | consequence before _ after ih => exact validConsequence before ih after

def TotalValid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀ s, P s → ∃ t, cexec s c t ∧ Q t

/-- Definition 13.2. The loop rule has one subderivation for each natural number. -/
inductive TotalHoare : Assertion → com → Assertion → Prop where
  | skip : TotalHoare P .SKIP P
  | assign : TotalHoare (substAssertion Q x e) (.ASSIGN x e) Q
  | seq : TotalHoare P c R → TotalHoare R d Q → TotalHoare P (.SEQ c d) Q
  | cond : TotalHoare (guarded P b true) c Q → TotalHoare (guarded P b false) d Q →
      TotalHoare P (.IFTHENELSE b c d) Q
  | loop (μ : store → Nat) :
      (∀ j, TotalHoare (fun s ↦ P s ∧ beval s b = true ∧ μ s = j) c
                       (fun t ↦ P t ∧ μ t < j)) →
      TotalHoare P (.WHILE b c) (guarded P b false)
  | consequence : (∀ s, P s → P₁ s) → TotalHoare P₁ c Q₁ → (∀ t, Q₁ t → Q t) → TotalHoare P c Q

private theorem totalLoopValid (P : Assertion) (b : bexp) (c : com) (μ : store → Nat)
    (body : ∀ j, TotalValid (fun s ↦ P s ∧ beval s b = true ∧ μ s = j) c
                            (fun t ↦ P t ∧ μ t < j)) :
    TotalValid P (.WHILE b c) (guarded P b false) := by
  intro s pre
  generalize eq : μ s = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    cases guard : beval s b with
    | false => exact ⟨s, .cexec_while_done guard, pre, guard⟩
    | true =>
      obtain ⟨m, first, inv, smaller⟩ := body n s ⟨pre, guard, eq⟩
      obtain ⟨t, rest, post⟩ := ih (μ m) smaller m inv rfl
      exact ⟨t, .cexec_while_loop guard first rest, post⟩

theorem totalHoareSound (derivation : TotalHoare P c Q) : TotalValid P c Q := by
  induction derivation with
  | skip => exact fun s pre ↦ ⟨s, .cexec_skip, pre⟩
  | assign => exact fun _ pre ↦ ⟨_, .cexec_assign, pre⟩
  | seq _ _ left right =>
    intro s pre
    obtain ⟨m, first, middle⟩ := left s pre
    obtain ⟨t, second, post⟩ := right m middle
    exact ⟨t, .cexec_seq first second, post⟩
  | @cond P b c Q d _ _ yes no =>
    intro s pre
    cases guard : beval s b with
    | false =>
      obtain ⟨t, run, post⟩ := no s ⟨pre, guard⟩
      exact ⟨t, ifFalse guard run, post⟩
    | true =>
      obtain ⟨t, run, post⟩ := yes s ⟨pre, guard⟩
      exact ⟨t, ifTrue guard run, post⟩
  | loop μ _ ih => exact totalLoopValid _ _ _ μ ih
  | consequence before _ after ih =>
    intro s pre
    obtain ⟨t, run, post⟩ := ih s (before s pre)
    exact ⟨t, run, after t post⟩

end PLBook.IMP
