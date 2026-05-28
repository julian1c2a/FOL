/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Properties.lean
-- Meta-logical properties that a theory may or may not satisfy.

import TheoryFramework.Theory

namespace TheoryFramework

open LogicSystem

variable {F : Type} [LogicSystem F]

-- ============================================================
-- Consistency
-- ============================================================

/-- A theory is consistent if it does not prove absurdity. -/
def IsConsistent (T : Theory F) : Prop :=
  ¬T.proves (LogicSystem.bottom)

/-- A formula set is consistent if the theory it generates is consistent. -/
def SetIsConsistent (S : F → Prop) : Prop :=
  IsConsistent { axioms := S }

-- ============================================================
-- Syntactic completeness
-- ============================================================

/-- A theory is syntactically complete (decides every formula) if for every `f`,
    it either proves `f` or proves its negation `¬f`. -/
def IsSyntacticallyComplete (T : Theory F) : Prop :=
  ∀ f : F, T.proves f ∨ T.proves (LogicSystem.neg f)

-- ============================================================
-- Axiom independence
-- ============================================================

/-- Axiom `ax` is redundant in `T` if it is derivable from the remaining axioms. -/
def IsAxiomRedundant (T : Theory F) (ax : F) : Prop :=
  T.axioms ax ∧
  DerivesSet (fun f => T.axioms f ∧ f ≠ ax) ax

/-- A theory is irredundant if none of its axioms is derivable from the rest. -/
def IsIrredundant (T : Theory F) : Prop :=
  ∀ ax : F, T.axioms ax → ¬IsAxiomRedundant T ax

-- ============================================================
-- Maximal consistency
-- ============================================================

/-- A theory is maximal consistent if it is consistent and adding any new formula
    that it does not prove would make it inconsistent. -/
def IsMaximalConsistent (T : Theory F) : Prop :=
  IsConsistent T ∧
  ∀ f : F, ¬T.proves f →
    ¬IsConsistent { axioms := fun g => T.axioms g ∨ g = f }

end TheoryFramework
