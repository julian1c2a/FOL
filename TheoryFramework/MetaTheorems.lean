/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/MetaTheorems.lean
-- Generic meta-theorems valid for any LogicSystem instance.
-- These are provable once and apply to PropLogic, FOLPure, and FOL^= automatically.

import TheoryFramework.Properties
import TheoryFramework.Relations

namespace TheoryFramework

open LogicSystem

variable {F : Type} [LogicSystem F]

-- ============================================================
-- Soundness/Completeness lifting to theories
-- ============================================================

/-- For any theory, proving and modeling coincide — lifted from the logic base. -/
theorem proves_iff_models (T : Theory F) (f : F) :
    T.proves f ↔ T.models f := by
  constructor
  · intro ⟨Γ, hΓ, hDer⟩
    exact ⟨Γ, hΓ, LogicSystem.sound hDer⟩
  · intro ⟨Γ, hΓ, hSem⟩
    exact ⟨Γ, hΓ, LogicSystem.complete hSem⟩

-- ============================================================
-- Monotonicity
-- ============================================================

/-- If T₁ ≤ T₂ (T₂ has more axioms) and T₁ proves f, then T₂ proves f. -/
theorem proves_monotone {T₁ T₂ : Theory F} (hle : T₁ ≤ T₂) {f : F}
    (hf : T₁.proves f) : T₂.proves f := by
  obtain ⟨Γ, hΓ, hDer⟩ := hf
  exact ⟨Γ, fun g hg => hle g (hΓ g hg), hDer⟩

/-- Models are also monotone (via proves_iff_models). -/
theorem models_monotone {T₁ T₂ : Theory F} (hle : T₁ ≤ T₂) {f : F}
    (hf : T₁.models f) : T₂.models f :=
  (proves_iff_models T₂ f).mp (proves_monotone hle ((proves_iff_models T₁ f).mpr hf))

-- ============================================================
-- Inconsistency propagates upward
-- ============================================================

/-- If T₁ ≤ T₂ and T₁ is inconsistent, then T₂ is also inconsistent. -/
theorem inconsistent_upward {T₁ T₂ : Theory F} (hle : T₁ ≤ T₂)
    (hIncons : ¬IsConsistent T₁) : ¬IsConsistent T₂ := by
  intro hCons
  apply hIncons
  intro hBot
  exact hCons (proves_monotone hle hBot)

/-- Contrapositive: if T₂ is consistent and T₁ ≤ T₂, T₁ is consistent. -/
theorem consistent_of_le {T₁ T₂ : Theory F} (hle : T₁ ≤ T₂)
    (hCons : IsConsistent T₂) : IsConsistent T₁ :=
  fun hBot => hCons (proves_monotone hle hBot)

-- ============================================================
-- Extension and equivalence
-- ============================================================

/-- Conservative extension implies deductive equivalence. -/
theorem equiv_of_conservative {T₁ T₂ : Theory F}
    (hCons : IsConservativeExtension T₁ T₂) : TheoryEquivalent T₁ T₂ :=
  fun f => ⟨fun h => proves_monotone hCons.left h, fun h => hCons.right f h⟩

/-- Deductive equivalence is symmetric. -/
theorem TheoryEquivalent.symm {T₁ T₂ : Theory F}
    (h : TheoryEquivalent T₁ T₂) : TheoryEquivalent T₂ T₁ :=
  fun f => (h f).symm

/-- Deductive equivalence is transitive. -/
theorem TheoryEquivalent.trans {T₁ T₂ T₃ : Theory F}
    (h₁₂ : TheoryEquivalent T₁ T₂) (h₂₃ : TheoryEquivalent T₂ T₃) :
    TheoryEquivalent T₁ T₃ :=
  fun f => (h₁₂ f).trans (h₂₃ f)

-- ============================================================
-- Empty and singleton theories
-- ============================================================

/-- Every theory extends the empty theory. -/
theorem empty_le (T : Theory F) : Theory.empty ≤ T :=
  fun _ hf => hf.elim

end TheoryFramework
