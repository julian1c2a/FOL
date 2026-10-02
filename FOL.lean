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
import FOL.Inconsistencia
import FOL.Rename
import FOL.Eigenvariable
import FOL.Lift0
import FOL.Henkin0
import FOL.Fresh0
import FOL.HenkinLimit0
import FOL.Eq0
import FOL.Lindenbaum0
import FOL.Canonical0
import FOL.SymClasses
import FOL.DecEq
import FOL.Propositional0
import FOL.Herbrand0
import FOL.Derives1
import FOL.Derives2
import FOL.Sequent0
import FOL.SequentSound0
import FOL.NDtoLK0
import FOL.Hauptsatz0
import FOL.Inversion0
import FOL.Finitary0
import FOL.Compacity0
import FOL.HerbrandBlock0
import FOL.Skolem0
import FOL.Prenex0
import FOL.PrenexNF0
import FOL.SkolemN0
import FOL.SkolemNF0
import FOL.Craig0
import FOL.Interpolation0
import FOL.QFDecide0
import FOL.BlockExtraction0
import FOL.SkolemHerbrand0

/-!
# `FOL` — el barrel completo: núcleo **más** capa semántica

⭐ **D-4 (2026‑09‑12): este barrel se PARTIÓ.**

* **`FOL.Core`** — sintaxis, derivación, tácticas y teoremas lógicos. Es **exactamente** lo que
  ROBINSON_PlusPlus importa (medido el 2026‑10‑02: ocho módulos —eran nueve con `FOL.MetaRules`,
  🗑️ borrado con ADR‑115 de RPP—; nunca importa este barrel).
* **`FOL`** (este fichero) — `FOL.Core` **más** `Semantics`, `Enumeration` y **toda la capa `₀`** (`Derives0` … `SkolemHerbrand0`: la lista son los `import` de arriba).

⭐⭐ **`FOL.Derives0` entró el 2026‑09‑14** — es el **Paso 0** de
`../ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md`: `Derives₀`, los constructores de
`Derives` **menos la ω‑regla** (21 de 22), con **cero habitantes‑axioma** ⇒ **se puede inducir
sobre él**. Aquel día `Derives` cargaba además los cuatro axiomas de `MetaRules`, y M‑11 prohibía
inducir sobre él; 🗑️ los cuatro, refutables, se borraron con `FOL/MetaRules.lean` el 2026‑10‑02
(ADR‑115 de RPP), y desde entonces M‑11 tampoco aplica a `Derives`. Más el encaje
`derives0_to_derives : Γ ⊢₀ f → Γ ⊢ f`, que es **él mismo** una inducción sobre `Derives₀` y por
tanto la prueba de que el paso funciona. ⚠️ **No toca a ROBINSON_PlusPlus**: es un objeto nuevo, y
este barrel RPP no lo importa.

🏁🏁 **`FOL.Soundness0`, el mismo día (Paso 1)** — y es lo que el repo no tenía:
`derives0_soundness : Γ ⊢₀ f → Γ ⊨ f`, **demostrada**, y con ella
**`derives0_consistent : ¬ ([] ⊢₀ ⊥)`** —la primera consistencia de un cálculo de FOL⁼ aquí— y
⭐⭐ **`derives0_not_complete`**: `Derives₀` **no decide toda fórmula**, que es exactamente la
patología de la que `Derives` padecía mientras `raa` estuvo postulado sobre él (hasta ADR‑115 de
RPP). ⛔ Del 2026‑09‑11 al 2026‑10‑02 se leyó que **la solidez de `Derives` era FALSA**
(`FOL/Inconsistencia.lean`, en el build desde el 2026-09-23). Era al revés: lo falso era `raa`.
🗑️ Borrado `FOL/MetaRules.lean` (ADR‑115 de RPP), esa solidez es un teorema del mismo módulo,
reescrito (`FOL.Inconsistencia.derives_soundness`), y `Derives` tampoco decide toda fórmula
(`derives_not_P`, `derives_not_negP`).

⭐ **`FOL.Rename`, también el 2026‑09‑14**: `derives0_rename` — `Derives₀` respeta el renombrado
de símbolos de función, footprint **`[propext, Quot.sound]`** (ni `Classical.choice`). Es la pieza
que la **extensión de Henkin** necesitaba y que sobre `Derives` estaba prohibida por M‑11 (hasta
ADR‑115 de RPP).

⭐⭐ **`FOL.Eigenvariable`, la otra mitad**: `derives0_gen_fresh` — de `Γ ⊢₀ φ` con la constante
`c` **fresca en el contexto** se concluye `Γ ⊢₀ ∀ (absFormula c 0 φ)`. Footprint
**`[propext, Quot.sound]`**. ⚠️ Ésta **sí** toca los índices de De Bruijn, así que sus
conmutaciones llevan hipótesis de nivel (`j ≤ k`, `v ≤ k`) — de ahí que costara más que el
renombrado.

⭐ **`FOL.Lift0`** — `derives0_lift`, el debilitamiento bajo levantamiento, y con él
`derives0_ex_forall_neg_absurd` (`∃A` y `∀¬A` se contradicen). Lo descubrió el ensamblaje: en un
cálculo finitario esa contradicción pasa por `elim_ex`, cuya premisa vive en el contexto levantado.

⭐⭐ **`FOL.Henkin0`** — **`henkin_step_consistent₀`**: añadir el testigo de Henkin con una constante
fresca **preserva la consistencia**. Es donde paga `derives0_gen_fresh`, y es la parte
**matemática** del ensamblaje. 🏁 La iteración ω y el **suministro de constantes frescas** los
pagan `FOL.HenkinLimit0` (`henLimit_consistent₀`, `henLimit_witness`) y `FOL.Fresh0` (`exists_fresh`).
⭐ Desde el 2026‑09‑27 (auditoría de constructividad, `auditoria/constructividad-2026-09-27/`) la
construcción entera va **sin `Classical.choice`**: `Rename`, `Eigenvariable`, `Henkin0`, `Fresh0`,
`HenkinLimit0` y `Lindenbaum0` hasta `henkin_completion₀` miden `[propext, Quot.sound]` o menos.
En `Lindenbaum0` sólo quedan `max_cons_contains` y `max_cons_impl`, que ya son lema de la verdad.
Lo clásico de la completitud está en ese lema, sobre un maximal arbitrario, en la semántica de
Tarski en `Prop` y en el `byContradiction` final de `completeness₀` (cabecera de
`FOL/Canonical0.lean`).

⭐ **`FOL.Enumeration` entró el 2026‑09‑13**: construye `natToFormula : Nat → Formula` y su
sobreyectividad, **cero axiomas**. Es lo que retira `formula_enum` y `formula_enum_surj` de
`cuarentena/Completeness.lean` (5 → 3 axiomas; ese fichero se **borró** el 2026-09-23). Está aquí, y no en `FOL.Core`, porque
ROBINSON_PlusPlus no lo necesita; pero sí **dentro de un `@[default_target]`**, que es la
diferencia entre código verificado y código huérfano.

Antes, `import FOL` arrastraba también `Completeness`, y con él **cinco axiomas** que el
consumidor no usaba.

## 🗑️ Lo que este barrel NO importa, y por qué

| módulo | desde | razón |
|---|---|---|
| `FOL.Soundness` | 2026‑09‑11 | ⛔ se leyó que **su teorema era FALSO**: con `raa` postulado demostraba `False` sin hipótesis. Era al revés: lo falso era `raa`. 🗑️ Borrado `FOL/MetaRules.lean` (ADR‑115 de RPP, 2026‑10‑02), su enunciado es un teorema: `FOL.Inconsistencia.derives_soundness` |
| `FOL.Compacity` | 2026‑09‑11 | su prueba pasaba por `soundness` ⇒ se declaró **vacua** (razón de entonces, que ya no vale: ese enunciado es hoy un teorema, ADR‑115 de RPP) |
| `FOL.Completeness` | 2026‑09‑12 | 702 líneas y **5 axiomas**, con **cero consumidores reales**. ⭐⭐ **Desde el 2026‑09‑13 es UNO**: la enumerabilidad la construye `FOL.Enumeration` y las dos congruencias de la igualdad son teoremas (`FOL/Theorems/Eq.lean`). ⛔ **Borrado el 2026-09-23**: lo supera `FOL.Canonical0.completeness₀`, con cero axiomas del proyecto |

Los tres se **borraron** el 2026-09-23 (la cuarentena se vació de código); el porqué sigue en `cuarentena/README.md`. Sus sujetos, reparados sobre `Derives₀`: `FOL.Soundness0`, `FOL.Compacity0` y `FOL.Canonical0`.
-/

-- ⛔⛔ NO REGENERAR CON `gen-root.bash`: está PROHIBIDO (A-7). Sobrescribiría este
-- fichero entero, borrando los avisos de abajo y metiendo tres módulos huérfanos con
-- declaraciones duplicadas. Ver la cabecera de `gen-root.bash`.

