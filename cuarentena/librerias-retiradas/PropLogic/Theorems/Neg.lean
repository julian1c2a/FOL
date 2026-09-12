/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: PropLogic.PL
-- @axiom_system: classical
-- @importance: high

import PropLogic.PL

namespace PropLogic.Theorems.Neg

open PropLogic

-- ============================================================
-- Nivel 2: Propiedades de la Negación
-- ============================================================

theorem explosion_impl {Γ A} : Γ ⊢ .impl ⊥ A := by
  apply Derives.intro_impl
  apply Derives.bot_elim
  apply Derives.hyp
  exact List.Mem.head _

theorem derived_raa {Γ A} (h_dne : .impl (neg (neg A)) A ∈ Γ) (h : neg A :: Γ ⊢ ⊥) : Γ ⊢ A := by
  apply Derives.elim_impl (A := neg (neg A))
  · apply Derives.hyp; exact h_dne
  · apply Derives.intro_impl; exact h

theorem double_neg_intro {Γ A} : Γ ⊢ .impl A (neg (neg A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := A)
  · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)

theorem double_neg_elim {Γ A} (h_dne : .impl (neg (neg A)) A ∈ Γ) : Γ ⊢ .impl (neg (neg A)) A :=
  Derives.hyp _ _ h_dne

axiom dne {Γ : List Formula} {A : Formula} : Γ ⊢ .impl (neg (neg A)) A

theorem contrapositive_1 {Γ A B} : Γ ⊢ .impl (.impl A B) (.impl (neg B) (neg A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := B)
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp; exact List.Mem.head _

theorem contrapositive_2 {Γ A B} (h_dne : .impl (neg (neg B)) B ∈ Γ) :
    Γ ⊢ .impl (.impl (neg B) (neg A)) (.impl A B) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply derived_raa
  · exact List.Mem.tail _ (List.Mem.tail _ h_dne)
  · apply Derives.elim_impl (A := A)
    · apply Derives.elim_impl (A := neg B)
      · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)

end PropLogic.Theorems.Neg

export PropLogic.Theorems.Neg (
  explosion_impl derived_raa double_neg_intro double_neg_elim dne
  contrapositive_1 contrapositive_2
)
