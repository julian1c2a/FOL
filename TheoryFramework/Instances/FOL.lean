/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Instances/FOL.lean
-- Instancia `LogicSystem` para la lógica de primer orden con igualdad (FOL⁼).

import TheoryFramework.Logic
import FOL.FOL
import FOL.Semantics

/-!
# `FOL⁼` como `LogicSystem` — y **sólo** como `LogicSystem`

## ⚠️ Qué decía este fichero antes del 2026‑09‑12, y por qué era falso

Su cabecera decía literalmente *«This instance is fully complete and verified»*, y rellenaba
los campos `sound` y `complete` de la vieja `LogicSystem` con

    sound    := @FOL.Metamath.Soundness.soundness
    complete := @FOL.Metamath.Completeness.completeness

Tres cosas estaban mal a la vez, y **ninguna la veía nadie** porque el módulo era **huérfano**:
la `lean_lib` no llevaba `globs`, así que sólo se compilaba lo que el barrel alcanzaba, y este
fichero **no entraba en ningún build**.

1. ⛔ **`FOL.Metamath.Soundness` ya no existe**: `soundness` está en `cuarentena/` desde el
   2026‑09‑11, porque **es FALSO** — con las meta‑reglas de `FOL/MetaRules.lean`, cualquier
   testigo suyo demuestra `False` sin hipótesis (`cuarentena/Inconsistencia.lean`, compilado,
   footprint `[propext, FOL.MetaRules.raa]`).
2. ⚠️ `completeness` existe, pero se apoya en **cinco `axiom`** de `FOL/Completeness.lean`
   introducidos en un commit titulado «100% sorry‑free». Ver `AXIOMS.md`.
3. ⛔ Y el fallo de fondo: **`sound` no debía ser un campo de `LogicSystem`** (A‑6). El marco
   estaba **postulando la solidez de toda instancia**.

## Lo que se declara hoy

**Sólo el núcleo**: `derives`, `bottom`, `neg`, `semanticEntails`. Eso es lo que `FOL⁼` **es**.

⛔ **NO se declara `SoundLogic Formula`, y no es un olvido: es INHABITABLE.** Declararla exigiría
un testigo de `Γ ⊢ f → Γ ⊨ f`, que es exactamente lo que demuestra `False`. Si algún día las
meta‑reglas dejan de habitar `Derives` ([ADR‑025](../../cuarentena/README.md) §8), la instancia
pasará a ser demostrable y **entonces** se declara.

⬜ **`CompleteLogic Formula` tampoco se declara**, pero por otra razón: es **decisión pendiente**
(D‑3) — hay que adjudicar antes si los cinco axiomas de `Completeness.lean` son aceptables.

⇒ En consecuencia, `proves_iff_models` **no se aplica a `FOL⁼`**. Correcto: nunca se le pudo
aplicar; lo que había era una instancia que lo fingía.
-/

namespace TheoryFramework.Instances

open FOL
open FOL.Metamath.Semantics

/-- **`FOL⁼` como sistema lógico** — el núcleo y nada más.
    `Formula`, `Derives` y `neg` viven en la raíz (`FOL/FOL.lean` no abre `namespace`). -/
instance folSystem : LogicSystem Formula where
  derives         := fun Γ f => Derives Γ f
  bottom          := .bottom
  neg             := neg
  semanticEntails := FOL.Metamath.Semantics.satisfies

end TheoryFramework.Instances
