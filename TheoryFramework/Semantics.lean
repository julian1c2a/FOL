/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Semantics.lean
-- Las interpretaciones de una lógica, la consecuencia semántica DESDE UN CONJUNTO, la compacidad y la completitud
-- fuerte.

import TheoryFramework.Properties

/-!
# `TheoryFramework/Semantics.lean` — modelos, compacidad y completitud fuerte (T58, ADR‑217 de RPP)

Hasta el 2026‑10‑28 el marco sólo tenía `semanticEntails : List F → F → Prop`, la consecuencia desde una lista
FINITA de premisas. Con eso, `Theory.models` —«alguna parte finita de los axiomas implica `f`»— no es la
consecuencia semántica de una teoría sino su versión finita, y `CompleteLogic`, que se llamaba «completitud
(fuerte)», es la completitud para premisas finitas. Lo que faltaba para decir lo otro:

* `ModelSemantics F`: las interpretaciones (`Interp`) y la satisfacción (`sat`), compatibles con `semanticEntails`.
* `Sat S` (S tiene modelo) y `Conseq S f` (todo modelo de S satisface `f`): la consecuencia desde un CONJUNTO.
* `Theory.entails` y `Theory.HasModel`.
* `CompactLogic`: lo que se sigue de un conjunto se sigue de una parte finita; `SatCompact`, la forma de libro (todo
  conjunto finitamente satisfacible es satisfacible). Las dos son equivalentes con la negación clásica
  (`satCompact_of_compact`, `compact_of_satCompact`).
* `Theory.models_iff_entails`: `models` ES la consecuencia semántica cuando la lógica es compacta.
* `Theory.proves_of_entails`: la **completitud fuerte** = la de premisas finitas + la compacidad. Y al revés,
  `compact_of_strongComplete`: con la solidez, la compacidad es exactamente lo que le falta a la una para ser la otra.
* `consistent_iff_hasModel`: una teoría es consistente si y sólo si tiene modelo.

La instancia de FOL⁼, en `TheoryFramework/Instances/FOLModels.lean`.

📏 Sin axiomas, salvo los que piden la lógica clásica: `satCompact_of_compact`, `compact_of_satCompact` y
`consistent_iff_hasModel` (un `byContradiction`, y en la segunda además un `filter` con decisión clásica).
-/

namespace TheoryFramework

open LogicSystem

/-- Una semántica de MODELOS para `F`: las interpretaciones y cuándo una interpretación satisface una fórmula.

`entails_iff` la ata a `semanticEntails`: la consecuencia desde una lista es «todo modelo de la lista satisface
la conclusión». `Interp` vive en `Type 1` para que quepan las estructuras de primer orden (un dominio `D : Type`
más la estructura y la valuación); una semántica de `Type` se sube con `ULift`. -/
class ModelSemantics (F : Type) [LogicSystem F] where
  Interp : Type 1
  sat : Interp → F → Prop
  entails_iff : ∀ (Γ : List F) (f : F),
    LogicSystem.semanticEntails Γ f ↔ ∀ I : Interp, (∀ g, g ∈ Γ → sat I g) → sat I f

namespace ModelSemantics

variable {F : Type} [LogicSystem F] [ModelSemantics F]

/-- `I` satisface TODO `S`. -/
def SatisfiesSet (I : Interp (F := F)) (S : F → Prop) : Prop :=
  ∀ g, S g → sat I g

/-- `S` es SATISFACIBLE: alguna interpretación lo satisface entero. -/
def Sat (S : F → Prop) : Prop :=
  ∃ I : Interp (F := F), SatisfiesSet I S

/-- Consecuencia semántica DESDE UN CONJUNTO (de verdad): todo modelo de `S` satisface `f`. -/
def Conseq (S : F → Prop) (f : F) : Prop :=
  ∀ I : Interp (F := F), SatisfiesSet I S → sat I f

/-- Lo que se sigue de una parte finita se sigue del conjunto. (La vuelta es la compacidad.) -/
theorem conseq_of_entailsSet {S : F → Prop} {f : F} (h : EntailsSet S f) : Conseq S f := by
  obtain ⟨Γ, hΓ, hE⟩ := h
  intro I hI
  exact (entails_iff Γ f).mp hE I (fun g hg => hI g (hΓ g hg))

end ModelSemantics

open ModelSemantics

namespace Theory

variable {F : Type} [LogicSystem F] [ModelSemantics F]

/-- ⭐ La consecuencia semántica de una teoría: todo modelo de sus axiomas —de TODOS— satisface `f`. No es
`Theory.models`, que pide una parte finita; coinciden si la lógica es compacta (`models_iff_entails`). -/
def entails (T : Theory F) (f : F) : Prop :=
  Conseq T.axioms f

/-- La teoría tiene MODELO. -/
def HasModel (T : Theory F) : Prop :=
  Sat T.axioms

end Theory

-- ============================================================
-- Compacidad
-- ============================================================

/-- **Compacidad** — una PROPIEDAD, como la solidez y la completitud: lo que se sigue de un conjunto se sigue de
una parte FINITA. Es la forma que piden los teoremas sobre teorías; la de libro es `SatCompact`. -/
class CompactLogic (F : Type) [LogicSystem F] [ModelSemantics F] : Prop where
  compact : ∀ {S : F → Prop} {f : F}, Conseq S f → EntailsSet S f

/-- La compacidad de libro: todo conjunto FINITAMENTE satisfacible es satisfacible. -/
def SatCompact (F : Type) [LogicSystem F] [ModelSemantics F] : Prop :=
  ∀ S : F → Prop, (∀ Γ : List F, (∀ g, g ∈ Γ → S g) → Sat (fun g => g ∈ Γ)) → Sat S

variable {F : Type} [LogicSystem F] [ModelSemantics F]

/-- La compacidad de consecuencia da la de libro, si `bottom` no tiene modelo. -/
theorem satCompact_of_compact [CompactLogic F]
    (hbot : ∀ I : ModelSemantics.Interp (F := F), ¬ sat I (LogicSystem.bottom : F)) : SatCompact F := by
  intro S hfin
  refine Classical.byContradiction fun hno => ?_
  have hc : Conseq S (LogicSystem.bottom : F) := fun I hI => absurd ⟨I, hI⟩ hno
  obtain ⟨Γ, hΓ, hE⟩ := CompactLogic.compact hc
  obtain ⟨I, hI⟩ := hfin Γ hΓ
  exact hbot I ((entails_iff Γ _).mp hE I hI)

/-- Y la de libro da la de consecuencia, si la negación es la clásica: `S ⊨ f` si y sólo si `S ∪ {¬f}` no tiene
modelo, y una parte finita de `S ∪ {¬f}` sin modelo da una parte finita de `S` que implica `f`. -/
theorem compact_of_satCompact
    (hneg : ∀ (I : ModelSemantics.Interp (F := F)) (f : F), sat I (LogicSystem.neg f) ↔ ¬ sat I f)
    (hsc : SatCompact F) : CompactLogic F := by
  refine ⟨fun {S} {f} hc => ?_⟩
  classical
  refine Classical.byContradiction fun hno => ?_
  -- `S ∪ {¬f}` es finitamente satisfacible: si una parte finita `Γ` no lo fuera, la parte de `Γ` que está en `S`
  -- implicaría `f`.
  have hfin : ∀ Γ : List F, (∀ g, g ∈ Γ → (S g ∨ g = LogicSystem.neg f)) → Sat (fun g => g ∈ Γ) := by
    intro Γ hΓ
    refine Classical.byContradiction fun hns => hno ?_
    refine ⟨Γ.filter (fun g => decide (S g)), fun g hg => of_decide_eq_true (List.mem_filter.mp hg).2, ?_⟩
    rw [entails_iff]
    intro I hI
    refine Classical.byContradiction fun hf => hns ⟨I, fun g hg => ?_⟩
    rcases hΓ g hg with hS | hEq
    · exact hI g (List.mem_filter.mpr ⟨hg, decide_eq_true hS⟩)
    · rw [hEq]
      exact (hneg I f).mpr hf
  obtain ⟨I, hI⟩ := hsc (fun g => S g ∨ g = LogicSystem.neg f) hfin
  exact (hneg I f).mp (hI _ (Or.inr rfl)) (hc I (fun g hg => hI g (Or.inl hg)))

-- ============================================================
-- Las teorías: consecuencia, solidez y completitud FUERTE
-- ============================================================

namespace Theory

/-- La consecuencia finita es consecuencia. -/
theorem entails_of_models {T : Theory F} {f : F} (h : T.models f) : T.entails f :=
  conseq_of_entailsSet h

/-- Y con la compacidad, al revés. -/
theorem models_of_entails [CompactLogic F] {T : Theory F} {f : F} (h : T.entails f) : T.models f :=
  CompactLogic.compact h

/-- ⭐ `Theory.models` es la consecuencia semántica de la teoría si la lógica es compacta. -/
theorem models_iff_entails [CompactLogic F] (T : Theory F) (f : F) : T.models f ↔ T.entails f :=
  ⟨entails_of_models, models_of_entails⟩

/-- **Solidez para teorías**: lo que una teoría prueba es consecuencia semántica de sus axiomas. -/
theorem entails_of_proves [SoundLogic F] {T : Theory F} {f : F} (h : T.proves f) : T.entails f := by
  obtain ⟨Γ, hΓ, hD⟩ := h
  exact conseq_of_entailsSet ⟨Γ, hΓ, SoundLogic.sound hD⟩

/-- 🏁 **COMPLETITUD FUERTE**: lo que se sigue de los axiomas de una teoría —de todos, infinitos si lo son— se
prueba en ella. Es la completitud de premisas finitas (`CompleteLogic`) más la compacidad. -/
theorem proves_of_entails [CompleteLogic F] [CompactLogic F] {T : Theory F} {f : F} (h : T.entails f) :
    T.proves f := by
  obtain ⟨Γ, hΓ, hE⟩ := CompactLogic.compact h
  exact ⟨Γ, hΓ, CompleteLogic.complete hE⟩

/-- Probar y ser consecuencia semántica, lo mismo. -/
theorem proves_iff_entails [SoundLogic F] [CompleteLogic F] [CompactLogic F] (T : Theory F) (f : F) :
    T.proves f ↔ T.entails f :=
  ⟨entails_of_proves, proves_of_entails⟩

end Theory

/-- ⭐ **La compacidad es exactamente la diferencia**: en una lógica sólida y fuertemente completa, la compacidad
es un TEOREMA (las pruebas son finitas). Con `Theory.proves_of_entails`: para una lógica sólida y completa en
premisas finitas, ser compacta y ser fuertemente completa son lo mismo. -/
theorem compact_of_strongComplete [SoundLogic F]
    (h : ∀ (T : Theory F) (f : F), T.entails f → T.proves f) : CompactLogic F := by
  refine ⟨fun {S} {f} hc => ?_⟩
  obtain ⟨Γ, hΓ, hD⟩ := h { axioms := S } f hc
  exact ⟨Γ, hΓ, SoundLogic.sound hD⟩

/-- 🏁 **EXISTENCIA DE MODELO**: en una lógica sólida, completa y compacta (y con `bottom` sin modelos), una teoría
es consistente si y sólo si tiene modelo. -/
theorem consistent_iff_hasModel [SoundLogic F] [CompleteLogic F] [CompactLogic F]
    (hbot : ∀ I : ModelSemantics.Interp (F := F), ¬ sat I (LogicSystem.bottom : F)) (T : Theory F) :
    IsConsistent T ↔ T.HasModel := by
  constructor
  · intro hc
    refine Classical.byContradiction fun hno => hc ?_
    exact Theory.proves_of_entails (fun I hI => absurd ⟨I, hI⟩ hno)
  · intro ⟨I, hI⟩ hp
    exact hbot I (Theory.entails_of_proves hp I hI)

end TheoryFramework
