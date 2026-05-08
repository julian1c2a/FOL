/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL
import FOL.Semantics
import FOL.Soundness

namespace FOL.Theorems.Soundness
open FOL.Semantics

-- ============================================================
-- Teorema de Corrección (Soundness) - Fase 5 (Opción B)
-- ============================================================
-- Demuestra que si Γ ⊢ f (sintácticamente demostrable), 
-- entonces Γ ⊨ f (semánticamente válido).
-- Su demostración se realiza por inducción estructural sobre
-- el árbol de derivación (h : Γ ⊢ f).

theorem soundness {Γ f} (h : Γ ⊢ f) : Γ ⊨ f := 
  FOL.Metamath.Soundness.soundness h

end FOL.Theorems.Soundness