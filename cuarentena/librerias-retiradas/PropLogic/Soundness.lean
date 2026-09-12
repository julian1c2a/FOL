/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: PropLogic.PL, PropLogic.Semantics, PropLogic.Tactics
-- @axiom_system: classical
-- @importance: high

import PropLogic.PL
import PropLogic.Tactics
import PropLogic.Semantics

namespace PropLogic.Metamath.Soundness

open PropLogic
open PropLogic.Metamath.Semantics

local notation:50 Γ " ⊨ " f => PropLogic.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- Teorema de Corrección (Soundness)
-- ============================================================

theorem soundness {Γ f} (h : Γ ⊢ f) : Γ ⊨ f := by
  induction h with
  | hyp Γ' f' hIn =>
    intro v hΓ
    exact hΓ f' hIn
  | intro_impl Γ' A B _ ih =>
    intro v hΓ hA
    apply ih v
    intro f' hf'
    cases hf' with
    | head _ => exact hA
    | tail _ hTail => exact hΓ f' hTail
  | elim_impl Γ' A B _ _ ih_impl ih_A =>
    intro v hΓ
    exact (ih_impl v hΓ) (ih_A v hΓ)
  | intro_and Γ' A B _ _ ihA ihB =>
    intro v hΓ
    exact ⟨ihA v hΓ, ihB v hΓ⟩
  | elim_and_l Γ' A B _ ih =>
    intro v hΓ
    exact (ih v hΓ).left
  | elim_and_r Γ' A B _ ih =>
    intro v hΓ
    exact (ih v hΓ).right
  | intro_or_l Γ' A B _ ih =>
    intro v hΓ
    exact Or.inl (ih v hΓ)
  | intro_or_r Γ' A B _ ih =>
    intro v hΓ
    exact Or.inr (ih v hΓ)
  | elim_or Γ' A B C _ _ _ ih_or ih_A ih_B =>
    intro v hΓ
    cases ih_or v hΓ with
    | inl hA =>
      apply ih_A v
      intro f' hf'
      cases hf' with
      | head _ => exact hA
      | tail _ hTail => exact hΓ f' hTail
    | inr hB =>
      apply ih_B v
      intro f' hf'
      cases hf' with
      | head _ => exact hB
      | tail _ hTail => exact hΓ f' hTail
  | bot_elim Γ' A _ ih =>
    intro v hΓ
    have hBot := ih v hΓ
    contradiction
  | weakening Γ' Γ'' f' _ hSubset ih =>
    intro v hΓ
    apply ih v
    intro g hg
    exact hΓ g (hSubset g hg)
  | rewrite_at Γ' f' f'' p sub sub' _ h_get h_rule h_replace ih =>
    intro v hΓ
    have hEvalF := ih v hΓ
    have hSubEq : ∀ w : Valuation, evalFormula w sub ↔ evalFormula w sub' :=
      fun w => rule_soundness w h_rule
    have hEquiv := replaceAt_soundness v h_get hSubEq
    exact h_replace ▸ hEquiv.mp hEvalF

end PropLogic.Metamath.Soundness

export PropLogic.Metamath.Soundness (soundness)
