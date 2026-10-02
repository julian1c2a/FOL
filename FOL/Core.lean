/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL
import FOL.Tactics
import FOL.Deduction
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Theorems.Eq

/-!
# `FOL.Core` — el núcleo sintáctico

Creado el **2026‑09‑12** (decisión **D‑4** de `doc/AUDITORIA-FOL-2026-09-12.md`).

**Medido entonces**: ROBINSON_PlusPlus importaba **nueve** módulos de FOL, y eran justo éstos (más
`MetaRules`). Nunca importa el barrel raíz. Antes, `import FOL` arrastraba además `Semantics` y
`Completeness` —y con `Completeness`, **cinco axiomas** que el consumidor no usaba.

⇒ **`FOL.Core` = sintaxis + derivación + tácticas + teoremas lógicos.**
   **`FOL` = `FOL.Core` + la capa semántica** (`Semantics`) y los cálculos `Derives₀`/`LK`.

🗑️ **2026‑10‑02 · `MetaRules` YA NO ESTÁ AQUÍ, ni en ninguna parte.** Estaba «deliberadamente» porque
ROBINSON_PlusPlus lo usaba en 336 sitios. Eran las cuatro reglas con **premisa‑FUNCIÓN** (`imp_intro`,
`raa`, `or_elim`, `ex_elim`), y sus enunciados son **refutables sin usarlas** (`FOL/Inconsistencia.lean`
§3): Lean + cualquiera de ellas demostraba `False`. RPP retiró su capa `⊢` (su ADR‑115) y FOL retiró
`FOL/MetaRules.lean` el mismo día. Sin ellas, `Derives` es `Derives₀` más `gen_rule`, que es admisible
(`FOL.Inconsistencia.derives_to_derives0`), y es sólido (`derives_soundness`).
-/
