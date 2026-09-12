/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: FOLPure.FOL, FOLPure.Prelim
-- @axiom_system: none
-- @importance: high

import FOLPure.FOL
import FOLPure.Tactics

namespace FOLPure.Theorems.Impl

-- ============================================================
-- Nivel 1: Tautologías de Implicación
-- ============================================================

-- 1. Identidad: A ⇒ A
theorem id_impl {Γ A} : Γ ⊢ .impl A A := by
  apply Derives.intro_impl
  derive_hyp

-- 2. Afirmación del Consecuente (K): A ⇒ (B ⇒ A)
theorem k_impl {Γ A B} : Γ ⊢ .impl A (.impl B A) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.hyp
  exact List.Mem.tail _ (List.Mem.head _)

-- 3. Transitividad / Silogismo Hipotético: (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C))
theorem syllogism_impl {Γ A B C} : Γ ⊢ .impl (.impl A B) (.impl (.impl B C) (.impl A C)) := by
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

-- 4. Distribución de la Implicación (S): (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))
theorem s_impl {Γ A B C} : Γ ⊢ .impl (.impl A (.impl B C)) (.impl (.impl A B) (.impl A C)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := B)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp
      exact List.Mem.head _
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.head _)
    · apply Derives.hyp
      exact List.Mem.head _

end FOLPure.Theorems.Impl

export FOLPure.Theorems.Impl (
  id_impl
  k_impl
  s_impl
  syllogism_impl
)
