/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Prelim
-- @axiom_system: classical
-- @importance: high

import FOL.FOL

namespace FOL.Theorems.Derived

-- ============================================================
-- Nivel 3: Conectivos Derivados
-- ============================================================

-- Introducción de la conjunción: A ⇒ B ⇒ A ∧ B
-- land A B = (A ⇒ B ⇒ ⊥) ⇒ ⊥
theorem and_intro {Γ A B} : Γ ⊢ .impl A (.impl B (land A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := B)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)

-- Eliminación de la conjunción (1): (A ∧ B) ⇒ A
theorem and_elim_left {Γ A B} : Γ ⊢ .impl (land A B) A := by
  apply Derives.intro_impl
  apply Derives.raa
  apply Derives.elim_impl (A := .impl A (.impl B ⊥))
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.intro_impl
    apply Derives.intro_impl
    apply Derives.elim_impl (A := A)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)

-- Eliminación de la conjunción (2): (A ∧ B) ⇒ B
theorem and_elim_right {Γ A B} : Γ ⊢ .impl (land A B) B := by
  apply Derives.intro_impl
  apply Derives.raa
  apply Derives.elim_impl (A := .impl A (.impl B ⊥))
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.intro_impl
    apply Derives.intro_impl
    apply Derives.elim_impl (A := B)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp; exact List.Mem.head _

-- Introducción de la disyunción (1): A ⇒ A ∨ B
-- lor A B = (A ⇒ ⊥) ⇒ B
theorem or_intro_left {Γ A B} : Γ ⊢ .impl A (lor A B) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.raa
  apply Derives.elim_impl (A := A)
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

-- Introducción de la disyunción (2): B ⇒ A ∨ B
theorem or_intro_right {Γ A B} : Γ ⊢ .impl B (lor A B) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)

-- Eliminación de la disyunción: (A ∨ B) ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
theorem or_elim {Γ A B C} : Γ ⊢ .impl (lor A B) (.impl (.impl A C) (.impl (.impl B C) C)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.raa
  apply Derives.elim_impl (A := C)
  · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.elim_impl (A := B)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
    · apply Derives.elim_impl (A := .impl A ⊥)
      · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · apply Derives.intro_impl
        apply Derives.elim_impl (A := C)
        · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
        · apply Derives.elim_impl (A := A)
          · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
          · apply Derives.hyp; exact List.Mem.head _

-- Tercio excluso: A ∨ ¬A
-- Como lor A (neg A) = (A ⇒ ⊥) ⇒ (A ⇒ ⊥), la demostración es equivalente a la identidad
theorem excluded_middle {Γ A} : Γ ⊢ lor A (neg A) := by
  apply Derives.intro_impl
  apply Derives.hyp
  exact List.Mem.head _

-- Conmutatividad de la conjunción: (A ∧ B) ⇒ (B ∧ A)
theorem and_comm {Γ A B} : Γ ⊢ .impl (land A B) (land B A) := by
  apply Derives.intro_impl
  apply Derives.elim_impl (A := A)
  · apply Derives.elim_impl (A := B)
    · exact and_intro
    · apply Derives.elim_impl (A := land A B)
      · exact and_elim_right
      · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.elim_impl (A := land A B)
    · exact and_elim_left
    · apply Derives.hyp; exact List.Mem.head _

-- Conmutatividad de la disyunción: (A ∨ B) ⇒ (B ∨ A)
theorem or_comm {Γ A B} : Γ ⊢ .impl (lor A B) (lor B A) := by
  apply Derives.intro_impl
  apply Derives.elim_impl (A := .impl B (lor B A))
  · apply Derives.elim_impl (A := .impl A (lor B A))
    · apply Derives.elim_impl (A := lor A B)
      · exact or_elim
      · apply Derives.hyp; exact List.Mem.head _
    · exact or_intro_right
  · exact or_intro_left

-- Asociatividad de la conjunción: ((A ∧ B) ∧ C) ⇒ (A ∧ (B ∧ C))
theorem and_assoc {Γ A B C} : Γ ⊢ .impl (land (land A B) C) (land A (land B C)) := by
  apply Derives.intro_impl
  apply Derives.elim_impl (A := land B C)
  · apply Derives.elim_impl (A := A)
    · exact and_intro
    · apply Derives.elim_impl (A := land A B)
      · exact and_elim_left
      · apply Derives.elim_impl (A := land (land A B) C)
        · exact and_elim_left
        · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.elim_impl (A := C)
    · apply Derives.elim_impl (A := B)
      · exact and_intro
      · apply Derives.elim_impl (A := land A B)
        · exact and_elim_right
        · apply Derives.elim_impl (A := land (land A B) C)
          · exact and_elim_left
          · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.elim_impl (A := land (land A B) C)
      · exact and_elim_right
      · apply Derives.hyp; exact List.Mem.head _

-- Asociatividad de la disyunción: ((A ∨ B) ∨ C) ⇒ (A ∨ (B ∨ C))
theorem or_assoc {Γ A B C} : Γ ⊢ .impl (lor (lor A B) C) (lor A (lor B C)) := by
  apply Derives.intro_impl
  apply Derives.elim_impl (A := .impl C (lor A (lor B C)))
  · apply Derives.elim_impl (A := .impl (lor A B) (lor A (lor B C)))
    · apply Derives.elim_impl (A := lor (lor A B) C)
      · exact or_elim
      · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.intro_impl
      apply Derives.elim_impl (A := .impl B (lor A (lor B C)))
      · apply Derives.elim_impl (A := .impl A (lor A (lor B C)))
        · apply Derives.elim_impl (A := lor A B)
          · exact or_elim
          · apply Derives.hyp; exact List.Mem.head _
        · apply Derives.intro_impl
          apply Derives.elim_impl (A := A)
          · exact or_intro_left
          · apply Derives.hyp; exact List.Mem.head _
      · apply Derives.intro_impl
        apply Derives.elim_impl (A := lor B C)
        · exact or_intro_right
        · apply Derives.elim_impl (A := B)
          · exact or_intro_left
          · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.intro_impl
    apply Derives.elim_impl (A := lor B C)
    · exact or_intro_right
    · apply Derives.elim_impl (A := C)
      · exact or_intro_right
      · apply Derives.hyp; exact List.Mem.head _

-- Ley de De Morgan (1): ¬(A ∨ B) ⇒ ¬A ∧ ¬B
theorem de_morgan_1_fwd {Γ A B} : Γ ⊢ .impl (neg (lor A B)) (land (neg A) (neg B)) := by
  apply Derives.intro_impl
  apply Derives.elim_impl (A := neg B)
  · apply Derives.elim_impl (A := neg A)
    · exact and_intro
    · apply Derives.intro_impl
      apply Derives.elim_impl (A := lor A B)
      · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
      · apply Derives.elim_impl (A := A)
        · exact or_intro_left
        · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.intro_impl
    apply Derives.elim_impl (A := lor A B)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
    · apply Derives.elim_impl (A := B)
      · exact or_intro_right
      · apply Derives.hyp; exact List.Mem.head _

-- Ley de De Morgan (1) reverso: ¬A ∧ ¬B ⇒ ¬(A ∨ B)
theorem de_morgan_1_rev {Γ A B} : Γ ⊢ .impl (land (neg A) (neg B)) (neg (lor A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := .impl B ⊥)
  · apply Derives.elim_impl (A := .impl A ⊥)
    · apply Derives.elim_impl (A := lor A B)
      · exact or_elim
      · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.elim_impl (A := land (neg A) (neg B))
      · exact and_elim_left
      · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := land (neg A) (neg B))
    · exact and_elim_right
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)

-- Ley de De Morgan (1) completa: ¬(A ∨ B) ⇔ ¬A ∧ ¬B
theorem de_morgan_1 {Γ A B} : Γ ⊢ iff (neg (lor A B)) (land (neg A) (neg B)) := by
  apply Derives.elim_impl (A := .impl (land (neg A) (neg B)) (neg (lor A B)))
  · apply Derives.elim_impl (A := .impl (neg (lor A B)) (land (neg A) (neg B)))
    · exact and_intro
    · exact de_morgan_1_fwd
  · exact de_morgan_1_rev

-- Ley de De Morgan (2): ¬(A ∧ B) ⇒ ¬A ∨ ¬B
theorem de_morgan_2_fwd {Γ A B} : Γ ⊢ .impl (neg (land A B)) (lor (neg A) (neg B)) := by
  apply Derives.intro_impl
  apply Derives.raa
  apply Derives.elim_impl (A := land A B)
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := B)
    · apply Derives.elim_impl (A := A)
      · exact and_intro
      · apply Derives.raa
        apply Derives.elim_impl (A := lor (neg A) (neg B))
        · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
        · apply Derives.elim_impl (A := neg A)
          · exact or_intro_left
          · apply Derives.intro_impl
            apply Derives.elim_impl (A := A)
            · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
            · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.raa
      apply Derives.elim_impl (A := lor (neg A) (neg B))
      · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
      · apply Derives.elim_impl (A := neg B)
        · exact or_intro_right
        · apply Derives.intro_impl
          apply Derives.elim_impl (A := B)
          · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
          · apply Derives.hyp; exact List.Mem.head _

-- Ley de De Morgan (2) reverso: ¬A ∨ ¬B ⇒ ¬(A ∧ B)
theorem de_morgan_2_rev {Γ A B} : Γ ⊢ .impl (lor (neg A) (neg B)) (neg (land A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := .impl (neg B) ⊥)
  · apply Derives.elim_impl (A := .impl (neg A) ⊥)
    · apply Derives.elim_impl (A := lor (neg A) (neg B))
      · exact or_elim
      · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
    · apply Derives.intro_impl
      apply Derives.elim_impl (A := A)
      · apply Derives.hyp; exact List.Mem.head _
      · apply Derives.elim_impl (A := land A B)
        · exact and_elim_left
        · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.intro_impl
    apply Derives.elim_impl (A := B)
    · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.elim_impl (A := land A B)
      · exact and_elim_right
      · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)

-- Ley de De Morgan (2) completa: ¬(A ∧ B) ⇔ ¬A ∨ ¬B
theorem de_morgan_2 {Γ A B} : Γ ⊢ iff (neg (land A B)) (lor (neg A) (neg B)) := by
  apply Derives.elim_impl (A := .impl (lor (neg A) (neg B)) (neg (land A B)))
  · apply Derives.elim_impl (A := .impl (neg (land A B)) (lor (neg A) (neg B)))
    · exact and_intro
    · exact de_morgan_2_fwd
  · exact de_morgan_2_rev

end FOL.Theorems.Derived

export FOL.Theorems.Derived (
  and_intro
  and_elim_left
  and_elim_right
  or_intro_left
  or_intro_right
  or_elim
  excluded_middle
  and_comm
  or_comm
  and_assoc
  or_assoc
  de_morgan_1_fwd
  de_morgan_1_rev
  de_morgan_1
  de_morgan_2_fwd
  de_morgan_2_rev
  de_morgan_2
)
