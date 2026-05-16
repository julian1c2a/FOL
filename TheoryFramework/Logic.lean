/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Logic.lean
-- Abstract interface for logical systems.
-- Any logic satisfying this typeclass can host theories evaluated by this framework.

namespace TheoryFramework

-- ============================================================
-- Typeclass LogicSystem
-- ============================================================

/-- An abstract logical system over formula type `F`.

Fields:
- `derives`         : syntactic entailment (proof relation)
- `bottom`          : the absurdity / false formula
- `neg`             : negation (derived connective, typically `f → ⊥`)
- `semanticEntails` : semantic entailment (truth in all valuations/models)
- `sound`           : every derivable formula is semantically valid
- `complete`        : every semantically valid formula is derivable

The types of `sound` and `complete` are symmetric, so the logic is
both sound and (strongly) complete.  The valuation/model type is hidden
inside `semanticEntails`; the framework never needs to inspect it.
-/
class LogicSystem (F : Type) where
  derives         : List F → F → Prop
  bottom          : F
  neg             : F → F
  semanticEntails : List F → F → Prop
  sound    : ∀ {Γ : List F} {f : F}, derives Γ f → semanticEntails Γ f
  complete : ∀ {Γ : List F} {f : F}, semanticEntails Γ f → derives Γ f

-- Shorthand notation (local to framework files)
namespace LogicSystem

variable {F : Type} [LogicSystem F]

/-- Derives from a set: there exists a finite list Γ ⊆ S with `Γ ⊢ f`. -/
def DerivesSet (S : F → Prop) (f : F) : Prop :=
  ∃ Γ : List F, (∀ g ∈ Γ, S g) ∧ LogicSystem.derives Γ f

/-- Semantic entailment from a set: there exists a finite list Γ ⊆ S with `Γ ⊨ f`. -/
def EntailsSet (S : F → Prop) (f : F) : Prop :=
  ∃ Γ : List F, (∀ g ∈ Γ, S g) ∧ LogicSystem.semanticEntails Γ f

end LogicSystem

end TheoryFramework
