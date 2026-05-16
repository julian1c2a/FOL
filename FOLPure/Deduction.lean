/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: FOLPure.FOL, FOLPure.Tactics
-- @axiom_system: classical
-- @importance: high

import FOLPure.FOL
import FOLPure.Tactics

namespace FOLPure.Metamath.Deduction

-- ============================================================
-- Fase 5: Metamatemática - Teorema de Deducción
-- ============================================================

theorem deduction_theorem {Γ A B} (h : A :: Γ ⊢ B) : Γ ⊢ .impl A B := by
  apply Derives.intro_impl
  exact h

end FOLPure.Metamath.Deduction

export FOLPure.Metamath.Deduction (deduction_theorem)
