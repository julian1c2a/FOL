/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL_poli.FOL
import FOL_poli.Semantics
import FOL_poli.Soundness

namespace FOL_poli.Theorems.Soundness
open FOL_poli.Semantics

-- ============================================================
-- Teorema de Corrección (Soundness) - Fase 5 (Opción B)
-- ============================================================
-- Demuestra que si Γ ⊢ f (sintácticamente demostrable), 
-- entonces Γ ⊨ f (semánticamente válido).
-- Su demostración se realiza por inducción estructural sobre
-- el árbol de derivación (h : Γ ⊢ f).

theorem soundness {Γ f} (h : Γ ⊢ f) : Γ ⊨ f := 
  FOL_poli.Metamath.Soundness.soundness h

end FOL_poli.Theorems.Soundness