/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Prelim
-- @axiom_system: none
-- @importance: high

import FOL.FOL
-- ✏️ 2026‑11‑05 (R2‑4‑5 de la auditoría de la base de RPP, ADR‑258 de RPP): sin `import FOL.Tactics`. Se usaba una vez
-- (`derive_hyp`, en `id_impl`, ahora con `Derives.hyp` a mano), y por esta línea los 118 módulos de RPP que importan
-- `FOL.Theorems.Quantifiers` cargaban `Lean` entero (`FOL.Tactics` lo importa) sin usar ninguna táctica suya.

namespace FOL.Theorems.Impl

-- ============================================================
-- Nivel 1: Tautologías de Implicación
-- ============================================================

-- 1. Identidad: A ⇒ A
theorem id_impl {Γ A} : Γ ⊢ .impl A A := by
  apply Derives.intro_impl
  apply Derives.hyp
  exact List.Mem.head _

-- 2. Afirmación del Consecuente (K): A ⇒ (B ⇒ A)
theorem k_impl {Γ A B} : Γ ⊢ .impl A (.impl B A) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.hyp
  exact List.Mem.tail _ (List.Mem.head _)

-- 3. Transitividad / Silogismo Hipotético: (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C))
theorem syllogism_impl {Γ A B C} : Γ ⊢ .impl (.impl A B) (.impl (.impl B C) (.impl A C)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := B)
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp
      exact List.Mem.head _

-- 4. Distribución de la Implicación (S): (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))
theorem s_impl {Γ A B C} : Γ ⊢ .impl (.impl A (.impl B C)) (.impl (.impl A B) (.impl A C)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := B)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp
      exact List.Mem.head _
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.head _)
    · apply Derives.hyp
      exact List.Mem.head _

end FOL.Theorems.Impl

export FOL.Theorems.Impl (
  id_impl
  k_impl
  s_impl
  syllogism_impl
)
