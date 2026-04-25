/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Metamath.Semantics, FOL.Tactics
-- @axiom_system: classical
-- @importance: high

import FOL.FOL
import FOL.Tactics
import FOL.Metamath.Semantics

namespace FOL.Metamath.Soundness

local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- Fase 5: Teorema de Corrección (Soundness)
-- ============================================================

theorem soundness {Γ f} (h : Γ ⊢ f) : Γ ⊨ f := by
  intro D M v hΓ
  induction h with
  | hyp Γ' f' hIn =>
    exact hΓ f' hIn
  | intro_impl Γ' A B _ ih =>
    intro hA
    apply ih
    intro f' hf'
    cases hf' with
    | head _ => exact hA
    | tail _ hTail => exact hΓ f' hTail
  | elim_impl Γ' A B _ _ ih_impl ih_A =>
    exact (ih_impl hΓ) (ih_A hΓ)
  | intro_and Γ' A B _ _ ihA ihB =>
    exact ⟨ihA hΓ, ihB hΓ⟩
  | elim_and_l Γ' A B _ ih =>
    exact (ih hΓ).left
  | elim_and_r Γ' A B _ ih =>
    exact (ih hΓ).right
  | intro_or_l Γ' A B _ ih =>
    exact Or.inl (ih hΓ)
  | intro_or_r Γ' A B _ ih =>
    exact Or.inr (ih hΓ)
  | elim_or Γ' A B C _ _ _ ih_or ih_A ih_B =>
    cases ih_or hΓ with
    | inl hA =>
      apply ih_A
      intro f' hf'
      cases hf' with
      | head _ => exact hA
      | tail _ hTail => exact hΓ f' hTail
    | inr hB =>
      apply ih_B
      intro f' hf'
      cases hf' with
      | head _ => exact hB
      | tail _ hTail => exact hΓ f' hTail
  | bot_elim Γ' A _ ih =>
    have hBot := ih hΓ
    contradiction
  | weakening Γ' Γ'' f' _ hSubset ih =>
    apply ih
    intro g hg
    exact hΓ g (hSubset g hg)
  | _ =>
    -- Casos pendientes: reglas de cuantificadores (intro_forall, etc.) y rewrite_at
    sorry

end FOL.Metamath.Soundness

export FOL.Metamath.Soundness (soundness)
