/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: PropLogic.PL, PropLogic.Semantics, PropLogic.Soundness, PropLogic.Completeness
-- @axiom_system: classical
-- @importance: high

import PropLogic.PL
import PropLogic.Semantics
import PropLogic.Soundness
import PropLogic.Completeness

namespace PropLogic.Metamath.Compacity

open PropLogic.Metamath.Semantics
open PropLogic.Metamath.Completeness
open PropLogic.Metamath.Soundness

-- ============================================================
-- Teorema de Compacidad (Compactness)
-- ============================================================

theorem consistency_of_satisfiable {S : Formula → Prop} (hSat : IsSatisfiable S) : IsConsistent S := by
  intro hBot
  obtain ⟨Γ, hΓ, hDer⟩ := hBot
  obtain ⟨v, hEval⟩ := hSat
  exact soundness hDer v (fun f hf => hEval f (hΓ f hf))

theorem compactness_theorem (S : Formula → Prop) :
    IsSatisfiable S ↔ ∀ (Γ : List Formula), (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ) := by
  apply Iff.intro
  · intro ⟨v, hEval⟩ Γ hSub
    exact ⟨v, fun f hf => hEval f (hSub f hf)⟩
  · intro hFinSat
    apply model_existence_lemma
    intro hBot
    obtain ⟨Γ, hΓ, hDer⟩ := hBot
    obtain ⟨v, hEvalΓ⟩ := hFinSat Γ hΓ
    exact soundness hDer v hEvalΓ

end PropLogic.Metamath.Compacity

export PropLogic.Metamath.Compacity (consistency_of_satisfiable compactness_theorem)
