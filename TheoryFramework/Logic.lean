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

⚠️⚠️ **CORRECCIÓN 2026‑09‑12 (A‑6): `sound` y `complete` ERAN CAMPOS DE ESTA CLASE, y no
deben serlo.**

Ser un sistema lógico **no incluye** ser sólido ni completo: son **propiedades** que un
sistema puede tener o no. Al exigirlos como campos, el marco **POSTULABA la solidez de cada
instancia** — y para `FOL` ese campo es **indemostrable**: `soundness` es FALSO en presencia
de `FOL/MetaRules.lean` (ver `cuarentena/README.md`). La instancia `folSystem` lo rellenaba
con ese teorema, y se autodescribía «fully complete and verified».

⇒ Ahora la solidez y la completitud viven en **clases aparte** (`SoundLogic`,
`CompleteLogic`), y todo lo que dependa de ellas es **explícitamente condicional** — que es
lo que siempre fue.
-/
class LogicSystem (F : Type) where
  derives         : List F → F → Prop
  bottom          : F
  neg             : F → F
  semanticEntails : List F → F → Prop

/-- **Solidez** — una PROPIEDAD, no parte de «ser un sistema lógico».

⛔ `FOL` **no puede habitarla**: con las meta‑reglas de `FOL/MetaRules.lean`, un testigo de
este campo demuestra `False` (`cuarentena/Inconsistencia.lean`, compilado). El único cálculo
del ecosistema del que se ha probado la solidez es `Prf₀`
(`../ROBINSON_PlusPlus/sondeos/AnclaSoundness.lean`). -/
class SoundLogic (F : Type) [LogicSystem F] : Prop where
  sound : ∀ {Γ : List F} {f : F},
    LogicSystem.derives Γ f → LogicSystem.semanticEntails Γ f

/-- **Completitud (fuerte)** — una PROPIEDAD, no parte de «ser un sistema lógico».

⛔ **Corrección 2026‑09‑18 (ADR‑072)**: la nota que había aquí —«`FOL/Completeness.lean`
prueba `completeness` apoyándose en **cinco `axiom`**»— era **falsa por partida doble** y ésta
era su **tercera** aparición en el repo: ese fichero **no existe**, y `cuarentena/Completeness.lean`
tiene **UN** `axiom`. 🏁 Hoy la completitud de FOL⁼ es **`FOL.Canonical0.completeness₀`**, con
**cero axiomas del proyecto** (ADR‑041) — pero sobre **`Derives₀`**, no sobre el `Derives` que
instancia `folSystem`, así que **no paga esta clase**. Ver `TheoryFramework/Instances/FOL.lean`. -/
class CompleteLogic (F : Type) [LogicSystem F] : Prop where
  complete : ∀ {Γ : List F} {f : F},
    LogicSystem.semanticEntails Γ f → LogicSystem.derives Γ f

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
