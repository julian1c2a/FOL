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

namespace FOL.Theorems.Neg

-- ============================================================
-- Nivel 2: Propiedades de la Negación
-- ============================================================

-- 5. Explosión (Ex Falso Quodlibet): ⊥ ⇒ A
theorem explosion_impl {Γ A} : Γ ⊢ .impl ⊥ A := by
  apply Derives.intro_impl
  apply Derives.raa
  apply Derives.hyp
  exact List.Mem.tail _ (List.Mem.head _)

-- 6. Doble Negación (Introducción): A ⇒ ¬(¬A)
theorem double_neg_intro {Γ A} : Γ ⊢ .impl A (neg (neg A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := A)
  · apply Derives.hyp
    exact List.Mem.head _
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)

-- 7. Doble Negación (Eliminación): ¬(¬A) ⇒ A
theorem double_neg_elim {Γ A} : Γ ⊢ .impl (neg (neg A)) A := by
  apply Derives.intro_impl
  apply Derives.raa
  apply Derives.elim_impl (A := neg A)
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.hyp
    exact List.Mem.head _

-- 8. Contrapositiva (1): (A ⇒ B) ⇒ (¬B ⇒ ¬A)
theorem contrapositive_1 {Γ A B} : Γ ⊢ .impl (.impl A B) (.impl (neg B) (neg A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := B)
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp
      exact List.Mem.head _

-- 9. Contrapositiva (2): (¬B ⇒ ¬A) ⇒ (A ⇒ B)
theorem contrapositive_2 {Γ A B} : Γ ⊢ .impl (.impl (neg B) (neg A)) (.impl A B) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.raa
  apply Derives.elim_impl (A := A)
  · apply Derives.elim_impl (A := neg B)
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp
      exact List.Mem.head _
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)

end FOL.Theorems.Neg

export FOL.Theorems.Neg (
  explosion_impl
  double_neg_intro
  double_neg_elim
  contrapositive_1
  contrapositive_2
)
