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
2. ⚠️ ~~`completeness` existe, pero se apoya en **cinco `axiom`** de `FOL/Completeness.lean`~~
   — ⛔ **DOS COSAS FALSAS, corregidas el 2026‑09‑18 (ADR‑072)**: `FOL/Completeness.lean`
   **no existe**, y `cuarentena/Completeness.lean` tiene **UN** `axiom`
   (`henkin_extension_lemma`), no cinco (ADR‑030/031 retiraron los otros cuatro).
   🏁 Y hoy hay algo mejor: **`FOL.Canonical0.completeness₀`** — completitud de FOL⁼ con
   **cero axiomas del proyecto** (ADR‑041).
3. ⛔ Y el fallo de fondo: **`sound` no debía ser un campo de `LogicSystem`** (A‑6). El marco
   estaba **postulando la solidez de toda instancia**.

## Lo que se declara hoy

**Sólo el núcleo**: `derives`, `bottom`, `neg`, `semanticEntails`. Eso es lo que `FOL⁼` **es**.

⛔ **NO se declara `SoundLogic Formula`, y no es un olvido: es INHABITABLE.** Declararla exigiría
un testigo de `Γ ⊢ f → Γ ⊨ f`, que es exactamente lo que demuestra `False`. Si algún día las
meta‑reglas dejan de habitar `Derives` ([ADR‑025](../../cuarentena/README.md) §8), la instancia
pasará a ser demostrable y **entonces** se declara.

⬜ **`CompleteLogic Formula` tampoco se declara, y la deuda SIGUE VIGENTE** — pero su razón
de 2026‑09‑12 («adjudicar antes si los cinco axiomas de `Completeness.lean` son aceptables»)
**ya no es la buena**, porque ni hay cinco axiomas ni existe ese fichero.

⛔ **La razón de verdad, medida el 2026‑09‑18 (ADR‑072)**: `folSystem` declara
`derives := fun Γ f => Derives Γ f` — el cálculo **CONTAMINADO**—, mientras que
`completeness₀` se prueba sobre **`Derives₀`**. ⇒ **`completeness₀` NO paga
`CompleteLogic Formula`**: son dos cálculos distintos.
🔑 *Una deuda puede sobrevivir a la desaparición de su motivo; comprobar que el motivo sigue
en pie es parte de comprobar la deuda.*

⭐ Las dos salidas, y hay que elegir con ADR: (a) declarar una segunda instancia
`LogicSystem Formula` sobre `Derives₀` y colgar de ella `CompleteLogic`; o (b) dejarlo sin
declarar y decir por qué, que es lo que hace este fichero hoy.

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
