import PLBook.IMP.Language

namespace PLBook.IMP

/-- The true specialization of the single conditional execution rule. -/
theorem ifTrue (guard : beval s b = true) (branch : cexec s c t) :
    cexec s (.IFTHENELSE b c d) t :=
  .cexec_ifthenelse (by simpa [guard] using branch)

/-- The false specialization of the same rule. -/
theorem ifFalse (guard : beval s b = false) (branch : cexec s d t) :
    cexec s (.IFTHENELSE b c d) t :=
  .cexec_ifthenelse (by simpa [guard] using branch)

/-- Inversion of an assignment determines the complete final store (Lemma 3.1). -/
theorem assignmentResult (run : cexec s (.ASSIGN x a) t) : t = update x (aeval s a) s := by
  cases run
  rfl

/-- Two finite executions from the same command and store have equal final stores. -/
theorem deterministic (first : cexec s c t) (other : cexec s c u) : t = u := by
  induction first generalizing u with
  | cexec_skip => cases other; rfl
  | cexec_assign => cases other; rfl
  | cexec_seq _ _ ihLeft ihRight =>
    cases other with
    | cexec_seq left right =>
      cases ihLeft left
      exact ihRight right
  | cexec_ifthenelse _ ih =>
    cases other with
    | cexec_ifthenelse branch => exact ih branch
  | cexec_while_done guard =>
    cases other with
    | cexec_while_done => rfl
    | cexec_while_loop guard' _ _ => simp_all
  | cexec_while_loop guard _ _ ihBody ihLoop =>
    cases other with
    | cexec_while_done guard' => simp_all
    | cexec_while_loop _ body rest =>
      cases ihBody body
      exact ihLoop rest

end PLBook.IMP
