/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: FOLPure.FOL, FOLPure.Semantics, FOLPure.Soundness, FOLPure.Completeness
-- @axiom_system: classical
-- @importance: high

import FOLPure.FOL
import FOLPure.Semantics
import FOLPure.Soundness
import FOLPure.Completeness

namespace FOLPure.Metamath.Compacity

open FOLPure.Metamath.Semantics
open FOLPure.Metamath.Completeness
open FOLPure.Metamath.Soundness

-- ============================================================
-- Fase 5: Teorema de Compacidad (Compactness)
-- ============================================================

theorem consistency_of_satisfiable {S : Formula → Prop} (hSat : IsSatisfiable S) : IsConsistent S := by
  intro hBot
  obtain ⟨Γ, hΓ, hDer⟩ := hBot
  obtain ⟨D, M, v, hEval⟩ := hSat
  have hCtx : contextSatisfies M v Γ := fun f hf => hEval f (hΓ f hf)
  have hBotEval := soundness hDer D M v hCtx
  exact hBotEval

theorem compactness_theorem (S : Formula → Prop) :
    IsSatisfiable S ↔ ∀ (Γ : List Formula), (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ) := by
  apply Iff.intro
  · intro hSat Γ hSub
    obtain ⟨D, M, v, hEval⟩ := hSat
    exact ⟨D, M, v, fun f hf => hEval f (hSub f hf)⟩
  · intro hFinSat
    apply model_existence_lemma
    intro hBot
    obtain ⟨Γ, hΓ, hDer⟩ := hBot
    have hSatΓ := hFinSat Γ hΓ
    obtain ⟨D, M, v, hEvalΓ⟩ := hSatΓ
    exact soundness hDer D M v hEvalΓ

end FOLPure.Metamath.Compacity

export FOLPure.Metamath.Compacity (consistency_of_satisfiable compactness_theorem)
