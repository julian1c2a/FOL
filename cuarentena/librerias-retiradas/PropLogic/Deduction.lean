/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Dependencies: PropLogic.PL, PropLogic.Tactics
-- @axiom_system: classical
-- @importance: high

import PropLogic.PL
import PropLogic.Tactics

namespace PropLogic.Metamath.Deduction

-- ============================================================
-- Teorema de Deducción (Proposicional)
-- ============================================================

theorem deduction_theorem {Γ A B} (h : A :: Γ ⊢ B) : Γ ⊢ .impl A B := by
  apply Derives.intro_impl
  exact h

end PropLogic.Metamath.Deduction

export PropLogic.Metamath.Deduction (deduction_theorem)
