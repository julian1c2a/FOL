/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Theory.lean
-- The Theory structure and its fundamental proof/model relations.

import TheoryFramework.Logic

namespace TheoryFramework

open LogicSystem

-- ============================================================
-- Theory
-- ============================================================

/-- A theory over a logic `F` is a set of extra-logical axioms. -/
structure Theory (F : Type) [LogicSystem F] where
  axioms : F → Prop

namespace Theory

variable {F : Type} [LogicSystem F]

/-- A theory proves `f` if some finite subset of its axioms derives `f`. -/
def proves (T : Theory F) (f : F) : Prop :=
  DerivesSet T.axioms f

/-- A theory models `f` if some finite subset of its axioms semantically entails `f`. -/
def models (T : Theory F) (f : F) : Prop :=
  EntailsSet T.axioms f

/-- The empty theory (no extra axioms). -/
def empty : Theory F where
  axioms _ := False

/-- A theory containing exactly the formulas in a list. -/
def fromList (Γ : List F) : Theory F where
  axioms f := f ∈ Γ

/-- A theory containing a single axiom. -/
def singleton (f : F) : Theory F where
  axioms g := g = f

end Theory

end TheoryFramework
