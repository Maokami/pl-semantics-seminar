import PLBook.IMP.Denotation

namespace PLBook.IMP

private theorem executionDenotes (run : cexec s c t) : denote c s = some t := by
  induction run with
  | cexec_skip | cexec_assign => rfl
  | cexec_seq _ _ first second => exact (intermediateStore _ _ _ _).2 ⟨_, first, second⟩
  | @cexec_ifthenelse s b c d t _ ih =>
    cases guard : beval s b <;> simpa [denote, guard] using ih
  | cexec_while_done guard =>
    change loopMeaning _ _ _ = _
    rw [← (loopLeastFixed _ _).1]
    simp [unfoldLoop, guard]
  | cexec_while_loop guard _ _ first rest =>
    change loopMeaning _ _ _ = _
    rw [← (loopLeastFixed _ _).1]
    simpa [unfoldLoop, guard, first, extend, denote] using rest

private theorem denotesExecution (c : com) (s t : store) (h : denote c s = some t) :
    cexec s c t := by
  induction c generalizing s t with
  | SKIP => cases h; exact .cexec_skip
  | ASSIGN => cases h; exact .cexec_assign
  | SEQ c d hc hd =>
    obtain ⟨m, hm, ht⟩ := (intermediateStore _ _ _ _).1 h
    exact .cexec_seq (hc _ _ hm) (hd _ _ ht)
  | IFTHENELSE b c d hc hd =>
    apply cexec.cexec_ifthenelse
    cases guard : beval s b <;> simp_all [denote]
  | WHILE b c hc =>
    obtain ⟨n, hn⟩ := (chainSup_some (approxIncreasing b (denote c)) s t).1 h
    clear h
    induction n generalizing s t with
    | zero => cases hn
    | succ n ih =>
      cases guard : beval s b with
      | false =>
        have eq : s = t := by simpa [approx, unfoldLoop, guard] using hn
        exact eq ▸ cexec.cexec_while_done guard
      | true =>
        obtain ⟨m, hm, ht⟩ := (intermediateStore (denote c) (approx b (denote c) n) s t).1
          (by simpa [approx, unfoldLoop, guard] using hn)
        exact .cexec_while_loop guard (hc _ _ hm) (ih _ _ ht)

/-- Theorem 10.2, for the independently defined denotation, including nested loops. -/
theorem executionIffDenotation (c : com) (s t : store) :
    cexec s c t ↔ denote c s = some t :=
  ⟨executionDenotes, denotesExecution c s t⟩

theorem graphAndDivergence (c : com) :
    (fun p : store × store ↦ denote c p.1 = some p.2) =
        (fun p ↦ cexec p.1 c p.2) ∧
    ∀ s, denote c s = none ↔ ¬ ∃ t, cexec s c t := by
  constructor
  · funext p
    exact propext (executionIffDenotation c p.1 p.2).symm
  · intro s
    simp only [executionIffDenotation]
    cases denote c s <;> simp

end PLBook.IMP
