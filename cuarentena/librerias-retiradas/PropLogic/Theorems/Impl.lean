/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: PropLogic.PL, PropLogic.Tactics
-- @axiom_system: none
-- @importance: high

import PropLogic.PL
import PropLogic.Tactics

namespace PropLogic.Theorems.Impl

open PropLogic

-- ============================================================
-- Nivel 1: Tautologías de Implicación
-- ============================================================

theorem id_impl {Γ A} : Γ ⊢ .impl A A := by
  apply Derives.intro_impl
  derive_hyp

theorem k_impl {Γ A B} : Γ ⊢ .impl A (.impl B A) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.hyp
  exact List.Mem.tail _ (List.Mem.head _)

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

end PropLogic.Theorems.Impl

export PropLogic.Theorems.Impl (id_impl k_impl s_impl syllogism_impl)
