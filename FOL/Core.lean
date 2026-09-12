/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL
import FOL.MetaRules
import FOL.Tactics
import FOL.Deduction
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Theorems.Eq

/-!
# `FOL.Core` — el núcleo sintáctico, y **exactamente** lo que ROBINSON_PlusPlus usa

Creado el **2026‑09‑12** (decisión **D‑4** de `doc/AUDITORIA-FOL-2026-09-12.md`).

**Medido**: ROBINSON_PlusPlus importa **nueve** módulos de FOL, y son justo éstos. Nunca importa
el barrel raíz. Antes, `import FOL` arrastraba además `Semantics` y `Completeness` —y con
`Completeness`, **cinco axiomas** que el consumidor no usaba.

⇒ **`FOL.Core` = sintaxis + derivación + tácticas + teoremas lógicos.**
   **`FOL` = `FOL.Core` + la capa semántica** (`Semantics`).

⚠️ `MetaRules` **está aquí**, y es deliberado: ROBINSON_PlusPlus lo usa en 336 sitios. Pero
conviene saber lo que trae: son las cuatro reglas con **premisa‑FUNCIÓN** (`imp_intro`, `raa`,
`or_elim`, `ex_elim`), que son las que hacen `⊢` **sintácticamente completo** y por tanto **no
r.e.** — ver `../ROBINSON_PlusPlus/Meta/OmegaStrength.lean` y la regla **M‑11**.
-/

