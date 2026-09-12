/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.Core
import FOL.Semantics

/-!
# `FOL` — el barrel completo: núcleo **más** capa semántica

⭐ **D-4 (2026‑09‑12): este barrel se PARTIÓ.**

* **`FOL.Core`** — sintaxis, derivación, tácticas y teoremas lógicos. Es **exactamente** lo que
  ROBINSON_PlusPlus importa (medido: nueve módulos; nunca importa este barrel).
* **`FOL`** (este fichero) — `FOL.Core` **más** `Semantics`.

Antes, `import FOL` arrastraba también `Completeness`, y con él **cinco axiomas** que el
consumidor no usaba.

## 🗑️ Lo que este barrel NO importa, y por qué

| módulo | desde | razón |
|---|---|---|
| `FOL.Soundness` | 2026‑09‑11 | ⛔ **su teorema es FALSO**: con `raa` demuestra `False` sin hipótesis |
| `FOL.Compacity` | 2026‑09‑11 | su prueba pasaba por `soundness` ⇒ **vacua** |
| `FOL.Completeness` | 2026‑09‑12 | 702 líneas y **5 de los 13 axiomas** del repo, con **cero consumidores reales**. Dos de ellos (`formula_enum`, `formula_enum_surj`) son **construibles** |

Los tres están en `cuarentena/`, con su explicación en `cuarentena/README.md`.
-/

-- ⛔⛔ NO REGENERAR CON `gen-root.bash`: está PROHIBIDO (A-7). Sobrescribiría este
-- fichero entero, borrando los avisos de abajo y metiendo tres módulos huérfanos con
-- declaraciones duplicadas. Ver la cabecera de `gen-root.bash`.

