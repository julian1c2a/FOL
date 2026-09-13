/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.Core
import FOL.Semantics
import FOL.Enumeration

/-!
# `FOL` — el barrel completo: núcleo **más** capa semántica

⭐ **D-4 (2026‑09‑12): este barrel se PARTIÓ.**

* **`FOL.Core`** — sintaxis, derivación, tácticas y teoremas lógicos. Es **exactamente** lo que
  ROBINSON_PlusPlus importa (medido: nueve módulos; nunca importa este barrel).
* **`FOL`** (este fichero) — `FOL.Core` **más** `Semantics` **más** `Enumeration`.

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
| `FOL.Completeness` | 2026‑09‑12 | 702 líneas y **5 axiomas**, con **cero consumidores reales**. ⭐ **Desde el 2026‑09‑13 son TRES**: `formula_enum` y `formula_enum_surj` ya **no se postulan**, los construye `FOL.Enumeration`. Sigue en cuarentena: `henkin_extension_lemma` no está pagado |

Los tres están en `cuarentena/`, con su explicación en `cuarentena/README.md`.
-/

-- ⛔⛔ NO REGENERAR CON `gen-root.bash`: está PROHIBIDO (A-7). Sobrescribiría este
-- fichero entero, borrando los avisos de abajo y metiendo tres módulos huérfanos con
-- declaraciones duplicadas. Ver la cabecera de `gen-root.bash`.

