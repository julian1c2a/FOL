/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL_poli.FOL

namespace FOL_poli.Theorems.Deduction

-- ============================================================
-- Teorema de Deducción (Opción A de la Fase 5)
-- ============================================================
-- En un sistema de Deducción Natural, el Teorema de Deducción
-- se corresponde directamente con la regla de Introducción de
-- la Implicación. Por tanto, su demostración es directa.

theorem deduction_theorem {Γ A B} (h : A :: Γ ⊢ B) : Γ ⊢ .impl A B := by
  apply Derives.intro_impl
  exact h

end FOL_poli.Theorems.Deduction