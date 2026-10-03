/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Instances/FOL.lean
-- La instancia `LogicSystem Formula` sobre `Derives₀`, con solidez y completitud (2026‑09‑27).

import TheoryFramework.MetaTheorems
import FOL.Canonical0

/-!
# `FOL⁼` y `LogicSystem` — la instancia sobre **`Derives₀`** (desde el 2026‑09‑27)

    fol0System            : LogicSystem Formula      -- derives := (· ⊢₀ ·), semanticEntails := satisfies
    fol0Sound             : SoundLogic Formula       -- = derives0_soundness
    fol0Complete          : CompleteLogic Formula    -- = completeness₀
    fol0_proves_iff_models : T.proves f ↔ T.models f  -- = TheoryFramework.proves_iff_models

🏁 **Decisión del propietario (D7, 2026‑09‑27)**: se declara la instancia sobre `Derives₀` —la
opción (a) que este fichero dejaba escrita desde el 2026‑09‑18 (ADR‑072)— y con ella
`proves_iff_models`, el metateorema de `TheoryFramework`, **se aplica por fin a FOL⁼**. Estaba
medida en la auditoría de constructividad (unas 20 líneas).

## La historia, en corto

* Hasta el 2026‑09‑12 este fichero declaraba una instancia *«fully complete and verified»* que
  rellenaba `sound`/`complete` con `FOL.Metamath.Soundness.soundness` (que se tuvo por FALSA:
  con las meta‑reglas en el entorno, cualquier testigo suyo daba `False`; ✏️ 2026‑10‑03: lo falso
  era `raa`, ADR‑115 de RPP) y con una completitud que se apoyaba en un `axiom`. Y **no entraba
  en ningún build**: la `lean_lib` no tenía `globs`.
* El 2026‑09‑23 se retiró `folSystem`, que declaraba `derives := Derives` —el cálculo con las
  meta‑reglas— y que por eso, se dijo, no podía llevar ni `SoundLogic` (inhabitable) ni
  `CompleteLogic` (`completeness₀` es de `Derives₀`: otro cálculo). ✏️ 2026‑10‑03: `SoundLogic` era
  habitable, y `CompleteLogic` también (`derives0_to_derives ∘ completeness₀`, los dos en el árbol
  desde el 2026‑09‑16); lo inconsistente era el entorno. La vía quedó cerrada con su mapa de vuelta escrito.
* El 2026‑09‑27 se toma ese mapa: la instancia se declara sobre **`Derives₀`**, y entonces
  `SoundLogic` la paga `derives0_soundness` y `CompleteLogic` la paga `completeness₀`.

`Derives` sigue **sin instancia propia**. ✏️ 2026‑10‑03: aquí se decía «y es correcto: su solidez es
falsa». Podría tenerla —y podía desde el 2026‑09‑16, salvo por el entorno inconsistente que FOL
deshizo al borrar `FOL/MetaRules.lean` (ADR‑115 de RPP)—: la solidez es
`FOL.Inconsistencia.derives_soundness`, y la completitud sale de `completeness₀` con
`derives0_to_derives`—, pero no hace falta: el sujeto de FOL⁼ es `Derives₀`, y la tiene.

## 📏 Footprint

`fol0System`: **ningún axioma** (es la firma). `fol0Sound`, `fol0Complete` y
`fol0_proves_iff_models`: `[propext, Classical.choice, Quot.sound]` (auditoría de constructividad,
2026‑09‑27):

* `fol0Sound` lo toma de `derives0_soundness`, la semántica de Tarski en `Prop`: los constructores
  clásicos de `Derives₀` (`dne_rule`, `dne_schema`, `forall_not_ex_not`) se validan con
  `byContradiction`. Con este enunciado es **inevitable**: la solidez implica `¬¬P → P` (medido).
* `fol0Complete` lo toma de `completeness₀`: el lema de la verdad sobre un maximal ARBITRARIO
  (los `max_cons_*` de la frontera y el propio `truth_lemma₀` implican `¬¬P → P`, medido) y el
  `byContradiction` final, que tiene la
  forma del principio de Markov: que sea inevitable para el enunciado es HIPÓTESIS.
* `fol0_proves_iff_models` usa las dos.

⚠️ Ninguno es el `if IsConsistent₀` de Lindenbaum, que ya no existe (desde el 2026‑09‑27 la etapa no
decide su condición): `lindenbaum_lemma₀` es `[propext, Quot.sound]`.
-/

namespace TheoryFramework.Instances

open FOL.Metamath.Semantics

/-- ⭐ **`Derives₀` como sistema lógico**: la firma. -/
instance fol0System : LogicSystem Formula where
  derives         := fun Γ f => Γ ⊢₀ f
  bottom          := Formula.bottom
  neg             := neg
  semanticEntails := fun Γ f => satisfies Γ f

/-- **Solidez**: la paga `derives0_soundness`. -/
instance fol0Sound : SoundLogic Formula :=
  ⟨fun h => FOL.Metamath.Soundness0.derives0_soundness h⟩

/-- **Completitud (fuerte)**: la paga `completeness₀`. -/
instance fol0Complete : CompleteLogic Formula :=
  ⟨fun h => FOL.Canonical0.completeness₀ h⟩

/-- 🏁 **El metateorema del marco, aplicado a FOL⁼**: para cualquier teoría, derivar y ser
consecuencia semántica son lo mismo (`Theory.models`: consecuencia de una parte FINITA de los
axiomas, `EntailsSet`). -/
theorem fol0_proves_iff_models (T : Theory Formula) (f : Formula) : T.proves f ↔ T.models f :=
  TheoryFramework.proves_iff_models T f

end TheoryFramework.Instances

#print axioms TheoryFramework.Instances.fol0System
#print axioms TheoryFramework.Instances.fol0Sound
#print axioms TheoryFramework.Instances.fol0Complete
#print axioms TheoryFramework.Instances.fol0_proves_iff_models
