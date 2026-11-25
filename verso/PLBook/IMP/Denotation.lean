import PLBook.IMP.Language

/-! Reynolds's lifted-state semantics. The outcome type, strict extension, flat order,
pointwise order and finite iteration specialize Lecture/S02Order.lean to the shared IMP
states and generalize its example unfolding to arbitrary guards and body meanings. -/

namespace PLBook.IMP

abbrev Outcome := Option store
abbrev Meaning := store → Outcome

def extend (f : Meaning) : Outcome → Outcome
  | none => none
  | some s => f s

theorem sequencingAssoc (f g h : Meaning) :
    extend h ∘ (extend g ∘ f) = extend (extend h ∘ g) ∘ f := by
  funext s
  change extend h (extend g (f s)) = extend (extend h ∘ g) (f s)
  cases f s <;> rfl

def FlatLe (a b : Outcome) : Prop := a = none ∨ a = b
def MeaningLe (f g : Meaning) : Prop := ∀ s, FlatLe (f s) (g s)

private theorem flatLe_iff {a b : Outcome} :
    FlatLe a b ↔ ∀ t, a = some t → b = some t := by
  cases a with
  | none => simp [FlatLe]
  | some s => simp [FlatLe, eq_comm]

theorem intermediateStore (g h : Meaning) (s t : store) :
    extend h (g s) = some t ↔ ∃ m, g s = some m ∧ h m = some t := by
  cases g s <;> simp [extend]

theorem sequencingMono (hf : MeaningLe f f') (hg : MeaningLe g g') :
    MeaningLe (extend g ∘ f) (extend g' ∘ f') := by
  intro s
  apply flatLe_iff.mpr
  intro t ht
  obtain ⟨m, hm, hmt⟩ := (intermediateStore f g s t).mp ht
  exact (intermediateStore f' g' s t).mpr
    ⟨m, flatLe_iff.mp (hf s) m hm, flatLe_iff.mp (hg m) t hmt⟩

def unfoldLoop (b : bexp) (body rest : Meaning) (s : store) : Outcome :=
  if beval s b then extend rest (body s) else some s

def approx (b : bexp) (body : Meaning) : Nat → Meaning
  | 0 => fun _ ↦ none
  | n + 1 => unfoldLoop b body (approx b body n)

theorem unfoldMono (b : bexp) (body : Meaning) {f g : Meaning} (le : MeaningLe f g) :
    MeaningLe (unfoldLoop b body f) (unfoldLoop b body g) := by
  intro s
  cases guard : beval s b <;> simp [unfoldLoop, guard, FlatLe]
  cases body s with
  | none => exact Or.inl rfl
  | some m => exact le m

theorem approxIncreasing (b : bexp) (body : Meaning) (n : Nat) :
    MeaningLe (approx b body n) (approx b body (n + 1)) := by
  induction n with
  | zero => exact fun _ ↦ Or.inl rfl
  | succ n ih => exact unfoldMono b body ih

/-- Any defined outcome determines the supremum of an increasing flat chain. -/
noncomputable def outcomeSup (r : Nat → Outcome) : Outcome := by
  classical
  exact if h : ∃ n, r n ≠ none then r h.choose else none

noncomputable def chainSup (g : Nat → Meaning) (s : store) : Outcome :=
  outcomeSup (fun n ↦ g n s)

private theorem persists {r : Nat → Outcome} (inc : ∀ n, FlatLe (r n) (r (n+1)))
    {i j : Nat} (le : i ≤ j) {t : store} (h : r i = some t) : r j = some t := by
  induction le with
  | refl => exact h
  | step _ ih => exact flatLe_iff.mp (inc _) t ih

private theorem outcomeSup_some {r : Nat → Outcome} (inc : ∀ n, FlatLe (r n) (r (n+1)))
    (t : store) : outcomeSup r = some t ↔ ∃ n, r n = some t := by
  classical
  unfold outcomeSup
  split
  next h =>
    constructor
    · exact fun eq ↦ ⟨_, eq⟩
    · rintro ⟨n, hn⟩
      cases Nat.le_total n h.choose with
      | inl le => exact persists inc le hn
      | inr le =>
        cases eq : r h.choose with
        | none => exact (h.choose_spec eq).elim
        | some u => rw [← hn, persists inc le eq]
  next h =>
    constructor
    · intro eq; cases eq
    · rintro ⟨n, hn⟩
      exact (h ⟨n, by simp [hn]⟩).elim

theorem chainSup_some {g : Nat → Meaning} (inc : ∀ n, MeaningLe (g n) (g (n+1)))
    (s t : store) : chainSup g s = some t ↔ ∃ n, g n s = some t :=
  outcomeSup_some (fun n ↦ inc n s) t

/-- An upper bound below every upper bound, in the flat order (Definition 8.9). -/
def IsLub (r : Nat → Outcome) (a : Outcome) : Prop :=
  (∀ n, FlatLe (r n) a) ∧ ∀ u, (∀ n, FlatLe (r n) u) → FlatLe a u

private theorem outcomeSup_isLub {r : Nat → Outcome} (inc : ∀ n, FlatLe (r n) (r (n+1))) :
    IsLub r (outcomeSup r) := by
  constructor
  · exact fun n ↦ flatLe_iff.mpr fun t ht ↦ (outcomeSup_some inc t).mpr ⟨n, ht⟩
  · intro a upper
    apply flatLe_iff.mpr
    intro t ht
    obtain ⟨n, hn⟩ := (outcomeSup_some inc t).mp ht
    exact flatLe_iff.mp (upper n) t hn

/-- The first returning stage separates the two parts of a non-bottom chain (Lemma 8.10). -/
theorem outcomeChainCases (r : Nat → Outcome) (inc : ∀ n, FlatLe (r n) (r (n+1))) :
    ((∀ n, r n = none) ∧ IsLub r none) ∨
    ∃ k t, (∀ n, n < k → r n = none) ∧ (∀ n, k ≤ n → r n = some t) ∧ IsLub r (some t) := by
  classical
  have lub := outcomeSup_isLub inc
  by_cases allBottom : ∀ n, r n = none
  · have eq : outcomeSup r = none := by simp [outcomeSup, allBottom]
    exact Or.inl ⟨allBottom, eq ▸ lub⟩
  · have defined : ∃ n, r n ≠ none := Classical.not_forall.mp allBottom
    obtain ⟨n, hn⟩ := defined
    obtain ⟨k, hk, before⟩ : ∃ k, r k ≠ none ∧ ∀ i, i < k → r i = none := by
      induction n using Nat.strongRecOn with
      | ind n ih =>
        by_cases first : ∀ i, i < n → r i = none
        · exact ⟨n, hn, first⟩
        · obtain ⟨i, hi⟩ := Classical.not_forall.mp first
          by_cases lt : i < n
          · exact ih i lt (fun eq ↦ hi (fun _ ↦ eq))
          · exact (hi (fun h ↦ (lt h).elim)).elim
    cases eq : r k with
    | none => exact (hk eq).elim
    | some t =>
      have supEq := (outcomeSup_some inc t).mpr ⟨k, eq⟩
      exact Or.inr ⟨k, t, before, fun _ le ↦ persists inc le eq, supEq ▸ lub⟩

/-- The pointwise construction is the least upper bound (Proposition 8.11). -/
theorem chainSup_isLub (g : Nat → Meaning) (inc : ∀ n, MeaningLe (g n) (g (n+1))) :
    (∀ n, MeaningLe (g n) (chainSup g)) ∧
    (∀ f, (∀ n, MeaningLe (g n) f) → MeaningLe (chainSup g) f) ∧
    ∀ s, chainSup g s = outcomeSup (fun n ↦ g n s) ∧ IsLub (fun n ↦ g n s) (chainSup g s) := by
  have pointwise (s : store) := outcomeSup_isLub (fun n ↦ inc n s)
  exact ⟨fun n s ↦ (pointwise s).1 n,
    fun f upper s ↦ (pointwise s).2 (f s) (fun n ↦ upper n s),
    fun s ↦ ⟨rfl, pointwise s⟩⟩

noncomputable def loopMeaning (b : bexp) (body : Meaning) : Meaning := chainSup (approx b body)

private theorem outcomeExt {a b : Outcome} (agree : ∀ t, a = some t ↔ b = some t) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The supremum of the finite stages satisfies the unfolding equation and is least
among all solutions, for every IMP guard and body meaning (Theorem 9.5). -/
theorem loopLeastFixed (b : bexp) (body : Meaning) :
    unfoldLoop b body (loopMeaning b body) = loopMeaning b body ∧
    ∀ g, unfoldLoop b body g = g → MeaningLe (loopMeaning b body) g := by
  have atStage := chainSup_some (approxIncreasing b body)
  constructor
  · funext s
    apply outcomeExt
    intro t
    rw [show loopMeaning b body s = chainSup (approx b body) s from rfl, atStage]
    cases guard : beval s b with
    | false =>
      simp only [unfoldLoop, guard, Bool.false_eq_true, ite_false]
      constructor
      · exact fun h ↦ ⟨1, by simpa [approx, unfoldLoop, guard] using h⟩
      · rintro ⟨_ | n, h⟩
        · cases h
        · simpa [approx, unfoldLoop, guard] using h
    | true =>
      simp only [unfoldLoop, guard, ite_true]
      rw [intermediateStore]
      constructor
      · rintro ⟨m, hm, ht⟩
        obtain ⟨n, hn⟩ := (atStage m t).mp ht
        exact ⟨n+1, by simpa [approx, unfoldLoop, guard, hm, extend] using hn⟩
      · rintro ⟨_ | n, h⟩
        · cases h
        · obtain ⟨m, hm, hn⟩ := (intermediateStore body (approx b body n) s t).mp
            (by simpa [approx, unfoldLoop, guard] using h)
          exact ⟨m, hm, (atStage m t).mpr ⟨n, hn⟩⟩
  · intro g fixed
    apply (chainSup_isLub _ (approxIncreasing b body)).2.1
    intro n
    induction n with
    | zero => exact fun _ ↦ Or.inl rfl
    | succ n ih => exact fixed ▸ unfoldMono b body ih

noncomputable def denote : com → Meaning
  | .SKIP => some
  | .ASSIGN x e => fun s ↦ some (update x (aeval s e) s)
  | .SEQ c d => extend (denote d) ∘ denote c
  | .IFTHENELSE b c d => fun s ↦ if beval s b then denote c s else denote d s
  | .WHILE b c => loopMeaning b (denote c)

def LoopFree : com → Prop
  | .SKIP | .ASSIGN .. => True
  | .SEQ c d | .IFTHENELSE _ c d => LoopFree c ∧ LoopFree d
  | .WHILE .. => False

theorem commandSequencingAssoc (a b c : com) (_ : LoopFree a) (_ : LoopFree b) (_ : LoopFree c) :
    denote (.SEQ (.SEQ a b) c) = denote (.SEQ a (.SEQ b c)) :=
  sequencingAssoc (denote a) (denote b) (denote c)

/-- Theorem 9.5 for the command denotation of Definition 9.4. -/
theorem whileDenotationLeastFixed (b : bexp) (c : com) :
    unfoldLoop b (denote c) (denote (.WHILE b c)) = denote (.WHILE b c) ∧
    ∀ g, unfoldLoop b (denote c) g = g → MeaningLe (denote (.WHILE b c)) g :=
  loopLeastFixed b (denote c)

end PLBook.IMP
