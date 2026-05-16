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
    distinction, this collapses to deductive equivalence over T₁. -/
def IsConservativeExtension (T₁ T₂ : Theory F) : Prop :=
  T₁ ≤ T₂ ∧ ∀ f : F, T₂.proves f → T₁.proves f

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
theorem le_union_left (T₁ T₂ : Theory F) : T₁ ≤ TheoryUnion T₁ T₂ :=
  fun f hf => Or.inl hf

theorem le_union_right (T₁ T₂ : Theory F) : T₂ ≤ TheoryUnion T₁ T₂ :=
  fun f hf => Or.inr hf

theorem intersection_le_left (T₁ T₂ : Theory F) : TheoryIntersection T₁ T₂ ≤ T₁ :=
  fun f ⟨h, _⟩ => h

theorem intersection_le_right (T₁ T₂ : Theory F) : TheoryIntersection T₁ T₂ ≤ T₂ :=
  fun f ⟨_, h⟩ => h

end TheoryFramework
