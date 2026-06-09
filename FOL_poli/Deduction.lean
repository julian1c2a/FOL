/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL_poli.FOL, FOL_poli.Tactics
-- @axiom_system: classical
-- @importance: high

import FOL_poli.FOL
import FOL_poli.Tactics

namespace FOL_poli.Metamath.Deduction

-- ============================================================
-- Fase 5: Metamatemática - Teorema de Deducción
-- ============================================================

theorem deduction_theorem {Γ A B} (h : A :: Γ ⊢ B) : Γ ⊢ .impl A B := by
  apply Derives.intro_impl
  exact h

end FOL_poli.Metamath.Deduction

export FOL_poli.Metamath.Deduction (deduction_theorem)
