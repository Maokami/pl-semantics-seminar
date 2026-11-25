import PLBook.IMP.Language

namespace PLBook.IMP

structure Operations (A : Type u) where
  literal : Int → A
  variableName : ident → A
  add : A → A → A
  subtract : A → A → A

def fold (ops : Operations A) : aexp → A
  | .CONST n => ops.literal n
  | .VAR x => ops.variableName x
  | .PLUS a b => ops.add (fold ops a) (fold ops b)
  | .MINUS a b => ops.subtract (fold ops a) (fold ops b)

def constructorEquations (ops : Operations A) (f : aexp → A) : Prop :=
  (∀ n, f (.CONST n) = ops.literal n) ∧
  (∀ x, f (.VAR x) = ops.variableName x) ∧
  (∀ a b, f (.PLUS a b) = ops.add (f a) (f b)) ∧
  (∀ a b, f (.MINUS a b) = ops.subtract (f a) (f b))

/-- Existence and uniqueness for the four shared constructors (Theorem 4.1). -/
theorem uniqueFold (ops : Operations A) :
    ∃ h, constructorEquations ops h ∧ ∀ g, constructorEquations ops g → g = h := by
  refine ⟨fold ops, ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩, ?_⟩
  intro g ⟨hl, hv, ha, hs⟩
  funext e
  induction e with
  | CONST n => exact hl n
  | VAR x => exact hv x
  | PLUS a b ih₁ ih₂ => simp only [ha, fold, ih₁, ih₂]
  | MINUS a b ih₁ ih₂ => simp only [hs, fold, ih₁, ih₂]

end PLBook.IMP
