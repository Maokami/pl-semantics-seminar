import PLBook.IMP.Language

namespace PLBook.IMP

theorem progress (c : com) (s : store) :
    c = .SKIP ∨ ∃ d t, red (c,s) (d,t) := by
  induction c with
  | SKIP => exact .inl rfl
  | ASSIGN => exact .inr ⟨_, _, .red_assign _ _ _⟩
  | SEQ a b ih _ =>
    right
    rcases ih with rfl | ⟨d, t, edge⟩
    · exact ⟨_, _, .red_seq_done b s⟩
    · exact ⟨_, _, .red_seq_step a b s d t edge⟩
  | IFTHENELSE => exact .inr ⟨_, _, .red_ifthenelse _ _ _ _⟩
  | WHILE b a _ =>
    cases h : beval s b with
    | false => exact .inr ⟨_, _, .red_while_done b a s h⟩
    | true => exact .inr ⟨_, _, .red_while_loop b a s h⟩

theorem skipLoopInfinite (s : store) :
    infseq_with_function red (.WHILE .TRUE .SKIP, s) := by
  let w := com.WHILE .TRUE .SKIP
  let head := (w, s)
  let body := (com.SEQ .SKIP w, s)
  have enter : red head body := .red_while_loop _ _ _ rfl
  have repeatStep : red body head := .red_seq_done _ _
  refine ⟨fun i ↦ if i % 2 = 0 then head else body, rfl, ?_⟩
  intro i
  by_cases even : i % 2 = 0
  · have odd : (1+i) % 2 ≠ 0 := by omega
    simpa only [ite_eq_left even, ite_eq_right odd] using enter
  · have nextEven : (1+i) % 2 = 0 := by omega
    simpa only [ite_eq_left nextEven, ite_eq_right even] using repeatStep

/-- A finite sequence represented by its first edge and its tail. -/
inductive PathOfLength (R : α → α → Prop) : Nat → α → α → Prop where
  | stop : PathOfLength R 0 p p
  | next : R p q → PathOfLength R n q r → PathOfLength R (n+1) p r

theorem finiteIffLength : star R p q ↔ ∃ n, PathOfLength R n p q := by
  constructor
  · intro path
    induction path with
    | star_refl => exact ⟨0, .stop⟩
    | star_step edge _ ih =>
      obtain ⟨n, tail⟩ := ih
      exact ⟨n+1, .next edge tail⟩
  · rintro ⟨_, path⟩
    induction path with
    | stop => exact .star_refl _
    | next edge _ ih => exact .star_step edge ih

private def withSuffix (k : com) (p : com × store) := (com.SEQ p.1 k, p.2)

theorem liftLength (k : com) (path : PathOfLength red n p q) :
    PathOfLength red n (withSuffix k p) (withSuffix k q) := by
  induction path with
  | stop => exact .stop
  | next edge _ ih => exact .next (.red_seq_step _ _ _ _ _ edge) ih

private theorem appendPath (first : star R p q) (second : star R q r) : star R p r := by
  induction first with
  | star_refl => exact second
  | star_step edge _ ih => exact .star_step edge (ih second)

private theorem sequencePath (left : star red (a,s) (.SKIP,m)) (right : star red (b,m) q) :
    star red (.SEQ a b,s) q := by
  obtain ⟨n, path⟩ := finiteIffLength.mp left
  exact appendPath (finiteIffLength.mpr ⟨n, liftLength b path⟩)
    (.star_step (.red_seq_done b m) right)

private theorem pathFromExecution (d : cexec s c t) : star red (c,s) (.SKIP,t) := by
  induction d with
  | cexec_skip => exact .star_refl _
  | cexec_assign => exact .star_step (.red_assign _ _ _) (.star_refl _)
  | cexec_seq _ _ left right => exact sequencePath left right
  | cexec_ifthenelse _ ih => exact .star_step (.red_ifthenelse _ _ _ _) ih
  | cexec_while_done guard => exact .star_step (.red_while_done _ _ _ guard) (.star_refl _)
  | cexec_while_loop guard _ _ body rest =>
    exact .star_step (.red_while_loop _ _ _ guard) (sequencePath body rest)

theorem executionBeforeStep (edge : red p q) (d : cexec q.2 q.1 t) : cexec p.2 p.1 t := by
  induction edge generalizing t with
  | red_assign => cases d; exact .cexec_assign
  | red_seq_done => exact .cexec_seq .cexec_skip d
  | red_seq_step _ _ _ _ _ _ ih =>
    cases d with
    | cexec_seq left right => exact .cexec_seq (ih left) right
  | red_ifthenelse => exact .cexec_ifthenelse d
  | red_while_done _ _ _ guard => cases d; exact .cexec_while_done guard
  | red_while_loop _ _ _ guard =>
    cases d with
    | cexec_seq body rest => exact .cexec_while_loop guard body rest

private theorem executionBeforePath (path : PathOfLength red n p q) (d : cexec q.2 q.1 t) :
    cexec p.2 p.1 t := by
  induction path with
  | stop => exact d
  | next edge _ ih => exact executionBeforeStep edge (ih d)

theorem terminatingEquivalence : cexec s c t ↔ star red (c,s) (.SKIP,t) := by
  refine ⟨pathFromExecution, ?_⟩
  intro path
  obtain ⟨_, counted⟩ := finiteIffLength.mp path
  exact executionBeforePath counted .cexec_skip

end PLBook.IMP
