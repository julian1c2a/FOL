/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- TheoryFramework/Instances/FOL.lean
-- Por qué NO hay instancia `LogicSystem` para FOL⁼ (`folSystem`, retirada el 2026‑09‑23).

import TheoryFramework.Logic
import FOL.FOL
import FOL.Semantics

/-!
# `FOL⁼` y `LogicSystem` — por qué **no** hay instancia (desde el 2026‑09‑23)

## ⚠️ Qué decía este fichero antes del 2026‑09‑12, y por qué era falso

Su cabecera decía literalmente *«This instance is fully complete and verified»*, y rellenaba
los campos `sound` y `complete` de la vieja `LogicSystem` con

    sound    := @FOL.Metamath.Soundness.soundness
    complete := @FOL.Metamath.Completeness.completeness

Tres cosas estaban mal a la vez, y **ninguna la veía nadie** porque el módulo era **huérfano**:
la `lean_lib` no llevaba `globs`, así que sólo se compilaba lo que el barrel alcanzaba, y este
fichero **no entraba en ningún build**.

1. ⛔ **`FOL.Metamath.Soundness` ya no existe**: `soundness` se apartó a `cuarentena/` el
   2026‑09‑11 (y se borró el 2026‑09‑23) porque **es FALSO** — con las meta‑reglas de `FOL/MetaRules.lean`, cualquier
   testigo suyo demuestra `False` sin hipótesis (`FOL/Inconsistencia.lean`, compilado,
   footprint `[propext, FOL.MetaRules.raa]`).
2. ⚠️ ~~`completeness` existe, pero se apoya en **cinco `axiom`** de `FOL/Completeness.lean`~~
   — ⛔ **DOS COSAS FALSAS, corregidas el 2026‑09‑18 (ADR‑072)**: `FOL/Completeness.lean`
   **no existe**, y `cuarentena/Completeness.lean` (borrado el 2026‑09‑23) tenía **UN** `axiom`
   (`henkin_extension_lemma`), no cinco (ADR‑030/031 retiraron los otros cuatro).
   🏁 Y hoy hay algo mejor: **`FOL.Canonical0.completeness₀`** — completitud de FOL⁼ con
   **cero axiomas del proyecto** (ADR‑041).
3. ⛔ Y el fallo de fondo: **`sound` no debía ser un campo de `LogicSystem`** (A‑6). El marco
   estaba **postulando la solidez de toda instancia**.

## Lo que se declara hoy

**Nada**: `folSystem`, que declaraba sólo el núcleo (`derives`, `bottom`, `neg`, `semanticEntails`), se retiró el 2026‑09‑23 (ver abajo).

⛔ **NO se declara `SoundLogic Formula`, y no es un olvido: es INHABITABLE.** Declararla exigiría
un testigo de `Γ ⊢ f → Γ ⊨ f`, que es exactamente lo que demuestra `False`. Si algún día las
meta‑reglas dejan de habitar `Derives` ([ADR‑025](../../cuarentena/README.md) §8), la instancia
pasará a ser demostrable y **entonces** se declara.

⬜ **`CompleteLogic Formula` tampoco se declara, y la deuda SIGUE VIGENTE** — pero su razón
de 2026‑09‑12 («adjudicar antes si los cinco axiomas de `Completeness.lean` son aceptables»)
**ya no es la buena**, porque ni hay cinco axiomas ni existe ese fichero.

⛔ **La razón de verdad, medida el 2026‑09‑18 (ADR‑072)**: `folSystem` declaraba
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

-- ⛔⛔⛔ **LA VÍA DE `TheoryFramework` QUEDA CERRADA — 2026‑09‑23, decisión del propietario.**
--
-- 📐 **Lo medido**: retirada `folSystem`, esta librería (6 módulos, 456 l.) queda **sin
-- ningún habitante y sin ningún consumidor**. `proves_iff_models` (`MetaTheorems.lean`) pide
-- `[SoundLogic F]` y `[CompleteLogic F]`, y **no existe ninguna instancia de ninguna de las dos**.
--
-- ⚠️ Es exactamente la forma que mandó `FOLPure`, `PropLogic` y `FOL_poli` a cuarentena
-- (`cuarentena/README.md` §7) — con **una diferencia que importa**: aquéllas estaban
-- **declaradas y nunca compiladas**, y ésta **sí se compila** y la vigilan los controles. Por eso
-- se queda donde está en vez de irse a cuarentena.
--
-- ⭐ **Y se queda a propósito**, no por inercia: el marco está bien planteado y la única razón
-- de que esté vacío es que su instancia apuntaba al cálculo equivocado. Si el camino vuelve por
-- aquí —y la vía de vuelta está escrita abajo— lo que hay que hacer es **una** declaración,
-- no reconstruir nada.
--
-- 🔑 *Una vía que se cierra con su mapa de vuelta escrito no es una vía perdida; una que se
-- borra, sí.*
--

-- ⛔⛔ **`folSystem` RETIRADA el 2026‑09‑23** (decisión del propietario, cierre de FOL).
--
-- Declaraba `derives := fun Γ f => Derives Γ f` — el cálculo **CONTAMINADO** —, y por eso
-- `SoundLogic Formula` era INHABITABLE y `CompleteLogic Formula` **no** la pagaba
-- `completeness₀`: son dos cálculos distintos (ADR‑072).
--
-- 📐 **Lo que decidió retirarla es una MEDICIÓN**: `folSystem` se declaraba **una vez** y
-- **no la consumía nadie en código** — las otras tres apariciones del nombre en el árbol eran
-- prosa. Una instancia sin consumidores que además apunta al cálculo equivocado no es un
-- puente: es una afirmación sobre el sujeto equivocado.
--
-- ⚠️ **Este módulo se queda, y a propósito**: lo que vale de él es la cabecera de arriba, que
-- explica **por qué no hay instancia** y qué haría falta para que la hubiera. Borrarlo dejaría
-- la pregunta sin respuesta escrita, que es como la deuda sobrevivió a su propio motivo.
--
-- ⬜ **Para reabrirlo**: declarar `LogicSystem Formula` sobre **`Derives₀`**. Entonces
-- `SoundLogic` la paga `derives0_soundness` y `CompleteLogic` la paga `completeness₀`, y
-- `proves_iff_models` deja de ser inusable. Es la opción (a) de la cabecera.

end TheoryFramework.Instances
