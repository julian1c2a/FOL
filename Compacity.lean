/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Semantics, FOL.Soundness, FOL.Completeness
-- @axiom_system: classical
-- @importance: high

import FOL.FOL
import FOL.Semantics
import FOL.Soundness
import FOL.Completeness

namespace FOL.Metamath.Compacity

open FOL.Metamath.Semantics
open FOL.Metamath.Completeness
open FOL.Metamath.Soundness

-- ============================================================
-- Fase 5: Teorema de Compacidad (Compactness)
-- ============================================================

-- Un conjunto de fórmulas es satisfacible si y solo si todo subconjunto finito lo es.
theorem compactness_theorem (S : Formula → Prop) :
    IsSatisfiable S ↔ ∀ (Γ : List Formula), (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ) := by
  apply Iff.intro
  · intro hSat Γ hSub
    obtain ⟨D, M, v, hEval⟩ := hSat
    use D, M, v
    intro f hf
    exact hEval f (hSub f hf)
  · -- Dirección inversa (requiere model_existence_lemma y soundness)
    sorry

end FOL.Metamath.Compacity

export FOL.Metamath.Compacity (compactness_theorem)
