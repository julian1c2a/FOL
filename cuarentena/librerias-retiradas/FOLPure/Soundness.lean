/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: FOLPure.FOL, FOLPure.Metamath.Semantics, FOLPure.Tactics
-- @axiom_system: classical
-- @importance: high

import FOLPure.FOL
import FOLPure.Tactics
import FOLPure.Semantics

namespace FOLPure.Metamath.Soundness

open FOLPure.Metamath.Semantics

local notation:50 Γ " ⊨ " f => FOLPure.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- Fase 5: Teorema de Corrección (Soundness)
-- ============================================================

theorem soundness {Γ f} (h : Γ ⊢ f) : Γ ⊨ f := by
  induction h with
  | hyp Γ' f' hIn =>
    intro D M v hΓ
    exact hΓ f' hIn
  | intro_impl Γ' A B _ ih =>
    intro D M v hΓ hA
    apply ih D M v
    intro f' hf'
    cases hf' with
    | head _ => exact hA
    | tail _ hTail => exact hΓ f' hTail
  | elim_impl Γ' A B _ _ ih_impl ih_A =>
    intro D M v hΓ
    exact (ih_impl D M v hΓ) (ih_A D M v hΓ)
  | intro_and Γ' A B _ _ ihA ihB =>
    intro D M v hΓ
    exact ⟨ihA D M v hΓ, ihB D M v hΓ⟩
  | elim_and_l Γ' A B _ ih =>
    intro D M v hΓ
    exact (ih D M v hΓ).left
  | elim_and_r Γ' A B _ ih =>
    intro D M v hΓ
    exact (ih D M v hΓ).right
  | intro_or_l Γ' A B _ ih =>
    intro D M v hΓ
    exact Or.inl (ih D M v hΓ)
  | intro_or_r Γ' A B _ ih =>
    intro D M v hΓ
    exact Or.inr (ih D M v hΓ)
  | elim_or Γ' A B C _ _ _ ih_or ih_A ih_B =>
    intro D M v hΓ
    cases ih_or D M v hΓ with
    | inl hA =>
      apply ih_A D M v
      intro f' hf'
      cases hf' with
      | head _ => exact hA
      | tail _ hTail => exact hΓ f' hTail
    | inr hB =>
      apply ih_B D M v
      intro f' hf'
      cases hf' with
      | head _ => exact hB
      | tail _ hTail => exact hΓ f' hTail
  | bot_elim Γ' A _ ih =>
    intro D M v hΓ
    have hBot := ih D M v hΓ
    contradiction
  | weakening Γ' Γ'' f' _ hSubset ih =>
    intro D M v hΓ
    apply ih D M v
    intro g hg
    exact hΓ g (hSubset g hg)
  | intro_forall Γ' A _ ih =>
    intro D M v hΓ d
    have hCtx : contextSatisfies M (shiftEnv v d) (Γ'.map (liftFormula 0)) :=
      (contextSatisfies_lift_zero M v d).mpr hΓ
    exact ih D M (shiftEnv v d) hCtx
  | elim_forall Γ' A t _ ih =>
    intro D M v hΓ
    have hForall := ih D M v hΓ
    have hEval := hForall (evalTerm M v t)
    exact (eval_substFormula_zero M v t A).mpr hEval
  | intro_ex Γ' A t _ ih =>
    intro D M v hΓ
    have hA := ih D M v hΓ
    have hEval := (eval_substFormula_zero M v t A).mp hA
    exact ⟨evalTerm M v t, hEval⟩
  | elim_ex Γ' A B _ _ ih_ex ih_B =>
    intro D M v hΓ
    have hEx := ih_ex D M v hΓ
    obtain ⟨d, hd⟩ := hEx
    have hCtx : contextSatisfies M (shiftEnv v d) (A :: Γ'.map (liftFormula 0)) := by
      intro f' hf'
      cases hf' with
      | head _ => exact hd
      | tail _ hTail => exact (contextSatisfies_lift_zero M v d).mpr hΓ f' hTail
    have hB := ih_B D M (shiftEnv v d) hCtx
    exact (eval_liftFormula_zero M v d B).mp hB
  | rewrite_at Γ' f' f'' p sub sub' _ h_get h_rule h_replace ih =>
    intro D M v hΓ
    have hEvalF := ih D M v hΓ
    have hSubEq : ∀ v', evalFormula M v' sub ↔ evalFormula M v' sub' := fun v' => rule_soundness M h_rule v'
    have hEquiv := replaceAt_soundness M v h_get hSubEq
    rw [h_replace]
    exact hEquiv.mp hEvalF

end FOLPure.Metamath.Soundness

export FOLPure.Metamath.Soundness (soundness)
