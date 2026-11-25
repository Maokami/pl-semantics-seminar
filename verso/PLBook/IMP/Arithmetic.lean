import PLBook.IMP.Language

namespace PLBook.IMP

/-- The expression judgment of Definition 1.5, on the shared IMP syntax. -/
inductive Evaluates (s : store) : aexp → Int → Prop where
  | literal (n) : Evaluates s (.CONST n) n
  | lookup (x) : Evaluates s (.VAR x) (s x)
  | plus : Evaluates s e m → Evaluates s f n → Evaluates s (.PLUS e f) (m + n)
  | minus : Evaluates s e m → Evaluates s f n → Evaluates s (.MINUS e f) (m - n)

/-- Membership in the free-variable set of Definition 1.4. -/
def occurs (x : ident) : aexp → Prop
  | .CONST _ => False
  | .VAR y => x = y
  | .PLUS e f | .MINUS e f => occurs x e ∨ occurs x f

theorem coincidence (e : aexp) (s t : store) (agree : ∀ x, occurs x e → s x = t x) :
    aeval s e = aeval t e := by
  induction e with
  | CONST => rfl
  | VAR x => exact agree x rfl
  | PLUS e f he hf =>
    simp only [aeval, he (fun x h ↦ agree x (.inl h)), hf (fun x h ↦ agree x (.inr h))]
  | MINUS e f he hf =>
    simp only [aeval, he (fun x h ↦ agree x (.inl h)), hf (fun x h ↦ agree x (.inr h))]

theorem updateIrrelevant (s : store) (e : aexp) (x : ident) (n : Int) (h : ¬ occurs x e) :
    aeval (update x n s) e = aeval s e := by
  apply coincidence
  intro y hy
  have hxy : x ≠ y := fun eq ↦ h (eq ▸ hy)
  change (if (x : String) == (y : String) then n else s y) = s y
  split
  next h => exact False.elim (hxy (@eq_of_beq String _ _ x y h))
  next => rfl

theorem correspondence (s : store) (e : aexp) (n : Int) :
    Evaluates s e n ↔ aeval s e = n := by
  constructor
  · intro d
    induction d with
    | literal | lookup => rfl
    | plus _ _ he hf => simp only [aeval, he, hf]
    | minus _ _ he hf => simp only [aeval, he, hf]
  · rintro rfl
    induction e with
    | CONST n => exact .literal n
    | VAR x => exact .lookup x
    | PLUS _ _ he hf => exact .plus he hf
    | MINUS _ _ he hf => exact .minus he hf

theorem uniqueValue (s : store) (e : aexp) :
    ∃ n, Evaluates s e n ∧ ∀ m, Evaluates s e m → n = m :=
  ⟨aeval s e, (correspondence s e _).2 rfl, fun m ↦ (correspondence s e m).1⟩

end PLBook.IMP
