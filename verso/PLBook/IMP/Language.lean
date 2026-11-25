/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Authors: Wojciech Różowski (Lean port of Xavier Leroy’s course).
LGPL-2.1, see PLBook/IMP/LICENSE.md. Adapted for this edition, 2026-11-25.
Definitions from Imp.lean and Sequences.lean at a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01.
Only the namespace, layout, comments and automation attributes have changed.
-/

namespace PLBook.IMP

def ident := String deriving BEq, Repr, Hashable

inductive aexp : Type where
  | CONST (n : Int)
  | VAR (x : ident)
  | PLUS (a1 : aexp) (a2 : aexp)
  | MINUS (a1 : aexp) (s2 : aexp)

def store : Type := ident → Int

def aeval (s : store) (a : aexp) : Int :=
  match a with
  | .CONST n => n
  | .VAR x => s x
  | .PLUS a1 a2 => aeval s a1 + aeval s a2
  | .MINUS a1 a2 => aeval s a1 - aeval s a2

inductive bexp : Type where
  | TRUE
  | FALSE
  | EQUAL (a1 : aexp) (a2 : aexp)
  | LESSEQUAL (a1 : aexp) (a2 : aexp)
  | NOT (b1 : bexp)
  | AND (b1 : bexp) (b2 : bexp)

def NOTEQUAL (a1 a2 : aexp) : bexp := .NOT (.EQUAL a1 a2)

def GREATEREQUAL (a1 a2 : aexp) : bexp := .LESSEQUAL a2 a1

def GREATER (a1 a2 : aexp) : bexp := .NOT (.LESSEQUAL a1 a2)

def LESS (a1 a2 : aexp) : bexp := GREATER a2 a1

def OR (b1 b2 : bexp) : bexp := .NOT (.AND (.NOT b1) (.NOT b2))

def beval (s : store) (b : bexp) : Bool :=
  match b with
  | .TRUE => true
  | .FALSE => false
  | .EQUAL a1 a2 => aeval s a1 = aeval s a2
  | .LESSEQUAL a1 a2 => aeval s a1 <= aeval s a2
  | .NOT b1 =>  !(beval s b1)
  | .AND b1 b2 => beval s b1 && beval s b2

inductive com : Type where
  | SKIP
  | ASSIGN (x : ident) (a : aexp)
  | SEQ (c1 : com) (c2 : com)
  | IFTHENELSE (b : bexp) (c1 : com) (c2 : com)
  | WHILE (b : bexp) (c1 : com)

def update (x : ident) (v : Int) (s : store) : store :=
  fun y => if x == y then v else s y

inductive cexec : store → com → store → Prop where
  | cexec_skip :
      cexec s .SKIP s
  | cexec_assign :
      cexec s (.ASSIGN x a) (update x (aeval s a) s)
  | cexec_seq :
      cexec s c1 s' -> cexec s' c2 s'' ->
      cexec s (.SEQ c1 c2) s''
  | cexec_ifthenelse :
      cexec s (if beval s b then c1 else c2) s' ->
      cexec s (.IFTHENELSE b c1 c2) s'
  | cexec_while_done :
      beval s b = false ->
      cexec s (.WHILE b c) s
  | cexec_while_loop :
      beval s b = true -> cexec s c s' -> cexec s' (.WHILE b c) s'' ->
      cexec s (.WHILE b c) s''

inductive red : com × store → com × store → Prop where
  | red_assign : ∀ x a s,
      red (.ASSIGN x a, s) (.SKIP, update x (aeval s a) s)
  | red_seq_done : ∀ c s,
      red (.SEQ .SKIP c, s) (c, s)
  | red_seq_step : ∀ c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) →
      red (.SEQ c1 c, s1) (.SEQ c2 c, s2)
  | red_ifthenelse : ∀ b c1 c2 s,
      red (.IFTHENELSE b c1 c2, s) ((if beval s b then c1 else c2), s)
  | red_while_done : ∀ b c s,
      beval s b = false →
      red (.WHILE b c, s) (.SKIP, s)
  | red_while_loop : ∀ b c s,
      beval s b = true →
      red (.WHILE b c, s) (.SEQ c (.WHILE b c), s)

inductive star (R : α → α → Prop) : α → α → Prop where
  | star_refl : ∀ x : α, star R x x
  | star_step : ∀ {x y z}, R x y → star R y z → star R x z

def infseq_with_function (R : α → α → Prop) (a: α) : Prop :=
  ∃ f : Nat → α, f 0 = a ∧ ∀ i, R (f i) (f (1 + i))

def infseq {α} (R : α → α → Prop) : α → Prop :=
  λ x : α => ∃ y, R x y ∧ infseq R y
  coinductive_fixpoint

end PLBook.IMP
