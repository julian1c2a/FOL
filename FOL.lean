/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.Core
import FOL.Semantics
import FOL.Enumeration
import FOL.Derives0
import FOL.Soundness0
import FOL.Rename
import FOL.Eigenvariable
import FOL.Lift0
import FOL.Henkin0
import FOL.Fresh0
import FOL.HenkinLimit0
import FOL.Eq0
import FOL.Lindenbaum0
import FOL.Canonical0
import FOL.DecEq
import FOL.Propositional0
import FOL.Herbrand0
import FOL.Derives1
import FOL.Derives2
import FOL.Sequent0

/-!
# `FOL` — el barrel completo: núcleo **más** capa semántica

⭐ **D-4 (2026‑09‑12): este barrel se PARTIÓ.**

* **`FOL.Core`** — sintaxis, derivación, tácticas y teoremas lógicos. Es **exactamente** lo que
  ROBINSON_PlusPlus importa (medido: nueve módulos; nunca importa este barrel).
* **`FOL`** (este fichero) — `FOL.Core` **más** `Semantics`, `Enumeration` y `Derives0`.

⭐⭐ **`FOL.Derives0` entró el 2026‑09‑14** — es el **Paso 0** de
`../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md`: `Derives₀`, los 21 constructores de
`Derives` **menos la ω‑regla** y **sin los cuatro axiomas de `MetaRules`**, con **cero
habitantes‑axioma** ⇒ **se puede inducir sobre él** (M‑11 no aplica). Más el encaje
`derives0_to_derives : Γ ⊢₀ f → Γ ⊢ f`, que es **él mismo** una inducción sobre `Derives₀` y por
tanto la prueba de que el paso funciona. ⚠️ **No toca a ROBINSON_PlusPlus**: es un objeto nuevo, y
este barrel RPP no lo importa.

🏁🏁 **`FOL.Soundness0`, el mismo día (Paso 1)** — y es lo que el repo no tenía:
`derives0_soundness : Γ ⊢₀ f → Γ ⊨ f`, **demostrada**, y con ella
**`derives0_consistent : ¬ ([] ⊢₀ ⊥)`** —la primera consistencia de un cálculo de FOL⁼ aquí— y
⭐⭐ **`derives0_not_complete`**: `Derives₀` **no decide toda fórmula**, que es exactamente la
patología de la que `Derives` sí padece. ⛔ Recuérdese que **la solidez de `Derives` es FALSA**
(`cuarentena/Inconsistencia.lean`).

⭐ **`FOL.Rename`, también el 2026‑09‑14**: `derives0_rename` — `Derives₀` respeta el renombrado
de símbolos de función, footprint **`[propext, Quot.sound]`** (ni `Classical.choice`). Es la pieza
que la **extensión de Henkin** necesitaba y que sobre `Derives` estaba prohibida por M‑11.

⭐⭐ **`FOL.Eigenvariable`, la otra mitad**: `derives0_gen_fresh` — de `Γ ⊢₀ φ` con la constante
`c` **fresca en el contexto** se concluye `Γ ⊢₀ ∀ (absFormula c 0 φ)`. Footprint
**`[propext, Quot.sound]`**. ⚠️ Ésta **sí** toca los índices de De Bruijn, así que sus
conmutaciones llevan hipótesis de nivel (`j ≤ k`, `v ≤ k`) — de ahí que costara más que el
renombrado.

⭐ **`FOL.Lift0`** — `derives0_lift`, el debilitamiento bajo levantamiento, y con él
`derives0_ex_forall_neg_absurd` (`∃A` y `∀¬A` se contradicen). Lo descubrió el ensamblaje: en un
cálculo finitario esa contradicción pasa por `elim_ex`, cuya premisa vive en el contexto levantado.

⭐⭐ **`FOL.Henkin0`** — **`henkin_step_consistent`**: añadir el testigo de Henkin con una constante
fresca **preserva la consistencia**. Es donde paga `derives0_gen_fresh`, y es la parte
**matemática** del ensamblaje. ⬜ Falta la iteración ω y el **suministro de constantes frescas**,
que es combinatoria de nombres y pasa por `String`.

⭐ **`FOL.Enumeration` entró el 2026‑09‑13**: construye `natToFormula : Nat → Formula` y su
sobreyectividad, **cero axiomas**. Es lo que retira `formula_enum` y `formula_enum_surj` de
`cuarentena/Completeness.lean` (5 → 3 axiomas). Está aquí, y no en `FOL.Core`, porque
ROBINSON_PlusPlus no lo necesita; pero sí **dentro de un `@[default_target]`**, que es la
diferencia entre código verificado y código huérfano.

Antes, `import FOL` arrastraba también `Completeness`, y con él **cinco axiomas** que el
consumidor no usaba.

## 🗑️ Lo que este barrel NO importa, y por qué

| módulo | desde | razón |
|---|---|---|
| `FOL.Soundness` | 2026‑09‑11 | ⛔ **su teorema es FALSO**: con `raa` demuestra `False` sin hipótesis |
| `FOL.Compacity` | 2026‑09‑11 | su prueba pasaba por `soundness` ⇒ **vacua** |
| `FOL.Completeness` | 2026‑09‑12 | 702 líneas y **5 axiomas**, con **cero consumidores reales**. ⭐⭐ **Desde el 2026‑09‑13 es UNO**: la enumerabilidad la construye `FOL.Enumeration` y las dos congruencias de la igualdad son teoremas (`FOL/Theorems/Eq.lean`). ⛔ Sigue en cuarentena: `henkin_extension_lemma` no está pagado, y con él `completeness` no está demostrado |

Los tres están en `cuarentena/`, con su explicación en `cuarentena/README.md`.
-/

-- ⛔⛔ NO REGENERAR CON `gen-root.bash`: está PROHIBIDO (A-7). Sobrescribiría este
-- fichero entero, borrando los avisos de abajo y metiendo tres módulos huérfanos con
-- declaraciones duplicadas. Ver la cabecera de `gen-root.bash`.

