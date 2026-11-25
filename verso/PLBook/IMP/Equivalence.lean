import PLBook.IMP.Determinacy

namespace PLBook.IMP

/-- Unfolding a loop preserves exactly its terminating executions (Theorem 7.3). -/
theorem loopUnfolding (b : bexp) (c : com) (s t : store) :
    cexec s (.WHILE b c) t ↔ cexec s (.IFTHENELSE b (.SEQ c (.WHILE b c)) .SKIP) t := by
  constructor
  · intro run
    cases run with
    | cexec_while_done guard => exact ifFalse guard .cexec_skip
    | cexec_while_loop guard body rest => exact ifTrue guard (.cexec_seq body rest)
  · intro run
    cases run with
    | cexec_ifthenelse branch =>
      cases guard : beval s b with
      | false =>
        simp [guard] at branch
        cases branch
        exact .cexec_while_done guard
      | true =>
        simp [guard] at branch
        obtain ⟨_, body, rest⟩ := sequenceExecution.mp branch
        exact .cexec_while_loop guard body rest

def Equivalent (c d : com) : Prop := ∀ s t, cexec s c t ↔ cexec s d t

theorem equivalentBeforeSuffix (c d a : com) (eq : Equivalent c d) :
    Equivalent (.SEQ c a) (.SEQ d a) := by
  intro s t
  simp only [sequenceExecution, eq s]

end PLBook.IMP
