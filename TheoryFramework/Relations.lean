/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Relations.lean
-- Relations between theories: extension, equivalence, conservativity, union.

import TheoryFramework.Theory

namespace TheoryFramework

open LogicSystem

variable {F : Type} [LogicSystem F]

-- ============================================================
-- Extension (partial order on theories)
-- ============================================================

/-- T₁ is a sub-theory of T₂ if every axiom of T₁ is also an axiom of T₂. -/
def TheoryExtension (T₁ T₂ : Theory F) : Prop :=
  ∀ f, T₁.axioms f → T₂.axioms f

instance : LE (Theory F) where
  le := TheoryExtension

-- Preorder is not in Lean 4 core (only Mathlib); state the laws directly.
theorem le_refl (T : Theory F) : T ≤ T :=
  fun _ h => h

theorem le_trans {T₁ T₂ T₃ : Theory F} (h₁₂ : T₁ ≤ T₂) (h₂₃ : T₂ ≤ T₃) : T₁ ≤ T₃ :=
  fun f hf => h₂₃ f (h₁₂ f hf)

-- ============================================================
-- Deductive equivalence
-- ============================================================

/-- Two theories are deductively equivalent if they prove the same formulas. -/
def TheoryEquivalent (T₁ T₂ : Theory F) : Prop :=
  ∀ f : F, T₁.proves f ↔ T₂.proves f

-- ============================================================
-- Conservative extension
-- ============================================================

/-- `T₂` is a conservative extension of `T₁` (written T₁ ≤ T₂ conservatively) if:
    - T₁ ≤ T₂ (extension of axioms), and
    - T₂ does not prove anything that T₁ cannot already prove.
    In the propositional / first-order setting without a built-in language
    distinction, this collapses to deductive equivalence over T₁.

⚠️ 2026‑10‑28 (T58, ADR‑217 de RPP): es el caso de lenguaje TOTAL, y por eso
`equiv_of_conservative` es la definición leída al revés. La conservatividad de libro es RELATIVA A UN
LENGUAJE —`T₂` puede probar fórmulas nuevas, pero ninguna nueva del lenguaje de `T₁`—: es
`IsConservativeOver`, aquí abajo, y ésta es su caso `L = todo`
(`isConservativeExtension_iff_over_all`, en `TheoryFramework/Conservativity.lean`). -/
def IsConservativeExtension (T₁ T₂ : Theory F) : Prop :=
  T₁ ≤ T₂ ∧ ∀ f : F, T₂.proves f → T₁.proves f

/-- ⭐ **Conservatividad RELATIVA A UN LENGUAJE** (2026‑10‑28, T58, ADR‑217 de RPP): `T₂` extiende `T₁`, y
toda fórmula de `L` que `T₂` prueba ya la probaba `T₁`. `L` es el lenguaje de `T₁` como predicado sobre las
fórmulas (en FOL⁼, «sus símbolos están en un conjunto dado»: `Instances.LangFormula`). Fuera de `L`, `T₂`
puede probar lo que quiera: una extensión por definición prueba la definición. Los teoremas, en
`TheoryFramework/Conservativity.lean`: el criterio semántico (`conservativeOver_of_expansion`) y, en FOL⁼, que
una extensión por definición es conservativa (`Instances.fol0_extDef_conservative`). -/
def IsConservativeOver (L : F → Prop) (T₁ T₂ : Theory F) : Prop :=
  T₁ ≤ T₂ ∧ ∀ f : F, L f → T₂.proves f → T₁.proves f

-- ============================================================
-- Theory union and intersection
-- ============================================================

/-- The union of two theories: axioms from either T₁ or T₂. -/
def TheoryUnion (T₁ T₂ : Theory F) : Theory F where
  axioms f := T₁.axioms f ∨ T₂.axioms f

/-- The intersection of two theories: axioms common to T₁ and T₂. -/
def TheoryIntersection (T₁ T₂ : Theory F) : Theory F where
  axioms f := T₁.axioms f ∧ T₂.axioms f

-- Basic monotonicity lemmas for union
-- (✏️ 2026‑10‑28, T58: `_` en vez de `f`, que no se usaba: los cuatro avisos de la auditoría.)
theorem le_union_left (T₁ T₂ : Theory F) : T₁ ≤ TheoryUnion T₁ T₂ :=
  fun _ hf => Or.inl hf

theorem le_union_right (T₁ T₂ : Theory F) : T₂ ≤ TheoryUnion T₁ T₂ :=
  fun _ hf => Or.inr hf

theorem intersection_le_left (T₁ T₂ : Theory F) : TheoryIntersection T₁ T₂ ≤ T₁ :=
  fun _ ⟨h, _⟩ => h

theorem intersection_le_right (T₁ T₂ : Theory F) : TheoryIntersection T₁ T₂ ≤ T₂ :=
  fun _ ⟨_, h⟩ => h

end TheoryFramework
