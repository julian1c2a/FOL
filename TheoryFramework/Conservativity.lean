/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Conservativity.lean
-- La conservatividad relativa a un lenguaje: sus propiedades y el criterio semántico.

import TheoryFramework.Semantics
import TheoryFramework.MetaTheorems

/-!
# `TheoryFramework/Conservativity.lean` — conservatividad relativa a un lenguaje (T58, ADR‑217 de RPP)

`IsConservativeExtension` (`TheoryFramework/Relations.lean`) no tiene lenguaje: pide que `T₂` no pruebe NADA que
`T₁` no pruebe, y entonces `equiv_of_conservative` es su definición leída al revés. La de libro es
`IsConservativeOver L T₁ T₂`: ninguna fórmula NUEVA del lenguaje `L`. Aquí:

* `isConservativeExtension_iff_over_all`: la vieja es la de lenguaje total.
* `refl`, `trans`, `mono` (un lenguaje menor), `proves_iff` (sobre `L`, las dos teorías prueban lo mismo) y
  `consistent` (si `bottom` está en `L`, una extensión conservativa de una teoría consistente es consistente).
* 🏁 `conservativeOver_of_expansion`, el **criterio semántico**: si todo modelo de `T₁` es equivalente, en las
  fórmulas de `L`, a un modelo de `T₂`, entonces `T₂` es conservativa sobre `T₁` en `L`. Pide solidez,
  completitud y compacidad: es la completitud FUERTE la que lo hace funcionar (`T₁` puede ser infinita).

En FOL⁼, con «las fórmulas cuyos símbolos están en un conjunto» y las EXPANSIONES de un modelo, y su aplicación —una
extensión por definición es conservativa—: `TheoryFramework/Instances/FOLModels.lean`.
-/

namespace TheoryFramework

open LogicSystem ModelSemantics

variable {F : Type} [LogicSystem F]

/-- La conservatividad sin lenguaje es la de lenguaje TOTAL. -/
theorem isConservativeExtension_iff_over_all (T₁ T₂ : Theory F) :
    IsConservativeExtension T₁ T₂ ↔ IsConservativeOver (fun _ => True) T₁ T₂ :=
  ⟨fun ⟨hle, hc⟩ => ⟨hle, fun f _ => hc f⟩, fun ⟨hle, hc⟩ => ⟨hle, fun f => hc f trivial⟩⟩

namespace IsConservativeOver

variable {L L' : F → Prop} {T₁ T₂ T₃ : Theory F}

theorem refl (L : F → Prop) (T : Theory F) : IsConservativeOver L T T :=
  ⟨le_refl T, fun _ _ h => h⟩

theorem trans (h₁₂ : IsConservativeOver L T₁ T₂) (h₂₃ : IsConservativeOver L T₂ T₃) :
    IsConservativeOver L T₁ T₃ :=
  ⟨le_trans h₁₂.1 h₂₃.1, fun f hf h => h₁₂.2 f hf (h₂₃.2 f hf h)⟩

/-- Conservativa sobre un lenguaje, conservativa sobre uno menor. -/
theorem mono (hL : ∀ f, L' f → L f) (h : IsConservativeOver L T₁ T₂) : IsConservativeOver L' T₁ T₂ :=
  ⟨h.1, fun f hf => h.2 f (hL f hf)⟩

/-- Sobre las fórmulas de `L`, las dos teorías prueban lo mismo. -/
theorem proves_iff (h : IsConservativeOver L T₁ T₂) {f : F} (hf : L f) : T₁.proves f ↔ T₂.proves f :=
  ⟨proves_monotone h.1, h.2 f hf⟩

/-- Una extensión conservativa (sobre un lenguaje que tiene `bottom`) de una teoría consistente es consistente. -/
theorem consistent (h : IsConservativeOver L T₁ T₂) (hbot : L LogicSystem.bottom) (hc : IsConsistent T₁) :
    IsConsistent T₂ :=
  fun hp => hc (h.2 _ hbot hp)

end IsConservativeOver

/-- 🏁 **EL CRITERIO SEMÁNTICO DE CONSERVATIVIDAD.** Si `T₁ ≤ T₂` y cada modelo `I` de `T₁` tiene un modelo `J`
de `T₂` que no satisface ninguna fórmula de `L` que `I` no satisfaga, entonces `T₂` es conservativa sobre `T₁` en
`L`. (En FOL⁼, `J` es una EXPANSIÓN de `I`: el mismo dominio y los símbolos de `L` sin tocar.) -/
theorem conservativeOver_of_expansion [ModelSemantics F] [SoundLogic F] [CompleteLogic F] [CompactLogic F]
    {L : F → Prop} {T₁ T₂ : Theory F} (hle : T₁ ≤ T₂)
    (hexp : ∀ I : ModelSemantics.Interp (F := F), SatisfiesSet I T₁.axioms →
      ∃ J : ModelSemantics.Interp (F := F), SatisfiesSet J T₂.axioms ∧ ∀ f, L f → sat J f → sat I f) :
    IsConservativeOver L T₁ T₂ := by
  refine ⟨hle, fun f hf hp => Theory.proves_of_entails fun I hI => ?_⟩
  obtain ⟨J, hJ, hag⟩ := hexp I hI
  exact hag f hf (Theory.entails_of_proves hp J hJ)

end TheoryFramework
