# FOL Ecosystem — Formalización de Lógica en Lean 4

> # ⛔⛔ AVISO DE ESTADO — 2026-09-26, retocado el 2026-10-02 (reescrito: el del 2026-09-12 había quedado FALSO). LEER ANTES QUE NADA
>
> **Este documento estaba fechado en mayo de 2026 y publicaba como hitos demostrados cosas que
> hoy están medidas FALSAS.** Se corrigen abajo las afirmaciones concretas; el resto del texto
> **no se ha reescrito** y debe leerse con esta advertencia delante.
>
> | lo que decía | lo medido |
> |---|---|
> | «Teorema de Corrección (Soundness): `Γ ⊢ A → Γ ⊨ A`» ✅ | 🏁 **Sí, sobre `Derives₀`** (2026-09-14): `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f` (`FOL/Soundness0.lean`), y con ella `derives0_consistent`. 🏁 **Y sobre `Derives`**, el enunciado de la columna izquierda, desde el 2026-10-02: `derives_soundness : Γ ⊢ f → Γ ⊨ f` (`FOL/Inconsistencia.lean` §1), porque sin meta‑reglas `Derives` se traduce a `Derives₀` (`derives_to_derives0`: `gen_rule` es admisible). Hasta ese día esta celda decía que la de `Derives` era «FALSA en presencia de `FOL/MetaRules.lean`»: lo falso era `raa` (`raa_refutable`, §3), y el módulo se borró (ADR‑115 de RPP) |
> | «Compacidad» ✅ | 🏁 `compactness`, `loewenheim_skolem_down` y el modelo infinito `infinite_model_of_large`, en `FOL/Compacity0.lean`. El `Compacity.lean` vacuo **se borró** el 2026-09-23 |
> | «Completitud» ✅ / «1 sorry» | 🏁 `completeness₀ : Γ ⊨ f → Γ ⊢₀ f` (`FOL/Canonical0.lean`, 2026-09-16), con **cero axiomas del proyecto**: `[propext, Classical.choice, Quot.sound]`. Ese `Classical.choice` viene del lema de la verdad sobre un maximal arbitrario (`max_cons_*`) y del `byContradiction` final de `completeness₀`; **no** del `if` de `Lindenbaum0`, que ya no decide nada (`lindenbaum_lemma₀` es `[propext, Quot.sound]`). Hasta el 2026-09-27 esta celda decía que era «el WKL de `Lindenbaum0`» (ADR-041): refutado, ADR-110 y `AXIOMS.md` §4. `Completeness.lean` y su último postulado, `henkin_extension_lemma`, **se borraron** el 2026-09-23. Ver **`AXIOMS.md`** |
> | «4 `lean_lib`, ~43 módulos, 1 sorry, v4.28.0» | **2 `lean_lib`** (`FOL`, `TheoryFramework`) · **0 `axiom`**: los cuatro de `FOL/MetaRules.lean` (`imp_intro`, `raa`, `or_elim`, `ex_elim`), refutables sin usarlos (`FOL/Inconsistencia.lean` §3), se borraron con el módulo el 2026-10-02 (ADR‑115 de RPP). Esta celda decía «4 `axiom`, los de `MetaRules` que el kernel obliga»: el kernel sólo impedía que fueran constructores (premisa‑función, ocurrencia no positiva), no obligaba a tenerlos · **0 sorry** · **v4.31.0**. `FOLPure`, `PropLogic` y `FOL_poli` **retiradas** el 2026-09-12 a `cuarentena/librerias-retiradas/` |
>
> ⭐ **Los seis teoremas del cierre (T1 a T6, 2026-09-23 y 2026-09-26) están en el árbol**, sobre `Derives₀`; el catálogo, en `CURRENT-STATUS-PROJECT.md` («Estado vigente») y `REFERENCE.md` §6. ⛔ Y lo que NO hay: la propiedad de disyunción para `Derives₀` es **FALSA** (`derives0_no_disjunction_property`).
> (Este aviso decía que «lo único sólido MEDIDO» era `prf0_soundness`, en RPP: dejó de serlo el 2026-09-14.)
> ✅ **2026-10-03 · deuda saldada**: los cinco módulos 🧊 que conservaban el texto anterior al borrado de `FOL/MetaRules.lean` (`Soundness0`, `Canonical0`, `Compacity0`, `Rename`, `TheoryFramework/Instances/FOL`) se descongelaron con autorización del propietario, se corrigieron sólo sus comentarios y se volvieron a congelar: `NEXT-STEPS.md`.
>
> **Fuentes:** `cuarentena/README.md` · `AXIOMS.md` ·
> `../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md` · ADR‑114 y ADR‑115 de `../ROBINSON_PlusPlus/DECISIONS.md` (2026-10-02)

[![Lean 4](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Sorries](https://img.shields.io/badge/sorries-0-brightgreen)](CURRENT-STATUS-PROJECT.md)

> **Status**: Ver [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) para detalles completos.

Dos librerías Lean 4 en el build (`FOL`, `TheoryFramework`), construidas desde cero sin dependencias de Mathlib; las otras dos de esta tabla se retiraron el 2026-09-12:

| Librería | Descripción | Sorries |
|----------|-------------|---------|
| `FOL` | Lógica de Primer Orden **con** igualdad (FOL^=) | 0 |
| ~~`FOLPure`~~ | 🗑️ retirada (`cuarentena/librerias-retiradas/`) | — |
| ~~`PropLogic`~~ | 🗑️ retirada (`cuarentena/librerias-retiradas/`) | — |
| `TheoryFramework` | Marco genérico de teorías — instancia **`fol0System`, sobre `Derives₀`**, desde el 2026-09-27 (`folSystem`, sobre `Derives`, se retiró el 2026-09-23) | 0 |

## Description

Este ecosistema formaliza la sintaxis, semántica y metamatemática de la Lógica Clásica en múltiples capas, con el objetivo de proporcionar una base rigurosa para la fundamentación de la matemática.

**Características principales:**

- **Sintaxis De Bruijn**: Índices de De Bruijn en fórmulas y términos, evitando la captura de variables en cuantificadores.
- **Deducción Natural**: Sistema extendido con reglas de reescritura local (`rewrite_at`) y eliminación de la doble negación (`dne_rule`, `dne_schema`: lógica clásica; la versión objeto de `raa` es `derives0_raa` (`intro_impl` con conclusión `⊥`: de `A :: Γ ⊢₀ ⊥`, `Γ ⊢₀ ¬A`); la reducción al absurdo clásica (de `¬A :: Γ ⊢ ⊥`, `Γ ⊢ A`) es `intro_impl` seguido de `dne_rule`). La meta‑regla `raa` —un `axiom` de `FOL/MetaRules.lean`, con premisa‑función— se borró el 2026-10-02 por refutable (ADR‑115 de RPP).
- **Automatización**: Tácticas `derive_hyp`, `derive_weaken`, `derive_rewrite` via `MetaM`.
- **Semántica Tarskiana**: Modelos, evaluación de fórmulas, satisfacción `Γ ⊨ f`.
- **Marco Genérico**: `class LogicSystem (F : Type)` con metateoremas reutilizables; desde el 2026-09-27, instanciado para FOL⁼ sobre `Derives₀` (`TheoryFramework/Instances/FOL.lean`: `fol0System`, con solidez y completitud).

**Hitos Metamatemáticos:**

1. Teorema de Deducción.
2. 🏁 **Teorema de Corrección** sobre `Derives₀` (`derives0_soundness`), y sobre `Derives` desde el 2026-10-02, sin meta‑reglas (`derives_soundness`, vía `derives_to_derives0`; ADR‑115 de RPP). Hasta ese día este hito decía que la de `Derives` era «FALSA con `MetaRules`»: lo falso eran las meta‑reglas, refutadas en `FOL/Inconsistencia.lean` §3, y `FOL/MetaRules.lean` se borró.
3. Construcción de Henkin + Lema de Lindenbaum (`henkin_completion₀`, `lindenbaum_lemma₀`): sin `Classical.choice` desde el 2026-09-27, `[propext, Quot.sound]`.
4. 🏁 **Teorema de Completitud** sobre `Derives₀`: `completeness₀ : Γ ⊨ f → Γ ⊢₀ f`, cero axiomas del proyecto; y su forma de Henkin, `model_existence_iff₀`. Su `Classical.choice` es el del lema de la verdad sobre un maximal arbitrario (`max_cons_*`) y el de su `byContradiction` final (auditoría de constructividad del 2026-09-27: `AXIOMS.md` §4).
5. 🏁 **Compacidad** (`compactness`), **Löwenheim–Skolem descendente** y el **modelo infinito por compacidad** (`infinite_model_of_large`: numerable e infinito).
6. Hauptsatz (`hauptsatz₀`), Herbrand, Craig, Skolem y forma prenexa; el fragmento sin cuantificadores caracterizado (`derives0_qf_iff`) y DECIDIDO (`decideDerives0QF`); decisor proposicional (`ptautCheck_iff`); inversión de `LK₀`. Catálogo: `REFERENCE.md` §6. Y los metateoremas genéricos de `LogicSystem` se aplican a FOL⁼: `fol0_proves_iff_models` (desde el 2026-09-27; entre el 2026-09-23 y esa fecha el marco no tuvo instancias).

## Modules — ⚠️ HISTÓRICO (2026-05-16): el catálogo vigente es `REFERENCE.md` §6

### `FOL` — FOL con Igualdad

| Module | Namespace | Status |
|--------|-----------|--------|
| `Prelim.lean` | top-level | ✅ |
| `FOL.lean` | top-level | ✅ |
| `Tactics.lean` | top-level | ✅ |
| `Deduction.lean` | `FOL.Metamath.Deduction` | ✅ |
| `Semantics.lean` | `FOL.Metamath.Semantics` | ✅ |
| ~~`Soundness.lean`~~ | — | ⛔ **CUARENTENA**: su teorema se tuvo por FALSO (con `raa` postulado, cualquier testigo suyo daba `False`). ✏️ Desde el 2026-10-02 (`FOL/MetaRules.lean` borrado, ADR‑115 de RPP) su enunciado es un teorema, `derives_soundness`: lo falso era `raa` |
| `Completeness.lean` | `FOL.Metamath.Completeness` | ⚠️ **0 sorry, 1 `axiom`** — eran 5 |
| ~~`Compacity.lean`~~ | — | ⛔ **CUARENTENA**: vacuo |
| `Theorems/Impl.lean`, `Neg.lean`, `Derived.lean`, `Quantifiers.lean`, `Eq.lean` | — | ✅ |

### `FOLPure` / `PropLogic` — estructura análoga, 0 sorries

### `TheoryFramework`

| Module | Purpose |
|--------|---------|
| `Logic.lean` | `class LogicSystem (F : Type)` |
| `Theory.lean` | `structure Theory F`, `proves`, `models` |
| `Properties.lean` | `IsConsistent`, `IsSyntacticallyComplete`, … |
| `Relations.lean` | `LE`, `TheoryEquivalent`, `IsConservativeExtension`, … |
| `MetaTheorems.lean` | `proves_iff_models`, `proves_monotone`, … |
| `Instances/` | Instancias para PropLogic, FOLPure, FOL |

## Project Structure — ⚠️ HISTÓRICO (2026-05-16): ver `REFERENCE.md` §6

```text
repo/
├── FOL/                     # FOL^= con igualdad
│   ├── FOL.lean             # Sintaxis + Derives (incl. eq, refl, subst)
│   ├── Tactics.lean
│   ├── Deduction.lean
│   ├── Semantics.lean
│   ├── Soundness.lean
│   ├── Completeness.lean    # ⚠️ hoy en `cuarentena/`: cero sorry y un postulado
│   │                        #    (`henkin_extension_lemma`) — histórico este árbol
│   ├── Compacity.lean
│   └── Theorems/
├── FOLPure/                 # FOL sin igualdad — 0 sorries
│   └── [misma estructura]
├── PropLogic/               # Lógica proposicional — 0 sorries
│   └── [estructura análoga]
├── TheoryFramework/         # Marco genérico
│   ├── Logic.lean
│   ├── Theory.lean
│   ├── Properties.lean
│   ├── Relations.lean
│   ├── MetaTheorems.lean
│   └── Instances/
├── FOL.lean                 # Barrel FOL^=
├── FOLPure.lean             # Barrel FOLPure
├── PropLogic.lean           # Barrel PropLogic
└── TheoryFramework.lean     # Barrel TheoryFramework
```

## Installation — ⛔ FOL NO se construye desde FOL (M-3): `lake build "@FOL/FOL" "@FOL/TheoryFramework"` desde la raíz de `../ROBINSON_PlusPlus`; lo de abajo es de 2026-05-16

```bash
git clone https://github.com/julian1c2a/ProjectName.git
cd ProjectName
lake build
```

Para construir una sola librería:

```bash
lake build FOLPure
lake build PropLogic
lake build TheoryFramework
```

Para usar una instancia concreta del TheoryFramework:

```lean
import TheoryFramework.Instances.FOL   -- el barril `TheoryFramework` no importa las instancias
-- `fol0System : LogicSystem Formula` sobre `Derives₀` (desde el 2026-09-27), con `fol0Sound` y `fol0Complete`
-- ⛔ HISTÓRICO: `Instances/FOLPure` y `Instances/PropLogic` ya no existen
```

## Requirements

- **Lean 4**: v4.31.0 (`lean-toolchain`)
- **Lake**: incluido con Lean 4
- Sin dependencias de Mathlib.

## Development Workflow

```bash
make build      # ⛔ es `lake build` DESDE FOL: prohibido por M-3 (ver Installation); el Makefile no lo impide
make build-all  # TODAS las librerias del lakefile, explicitamente
make sorry      # check-sorry.bash
make axioms     # check-axioms.bash  ← el censo de `axiom` (A-1)
make status     # locked files + sorry + axiom status
bash new-module.bash ModuleName
```

> ### ⛔ `make root` / `bash gen-root.bash` están **PROHIBIDOS** (2026‑09‑12, A‑7)
>
> Sobrescriben el barrel entero: **borrarían el aviso de cuarentena** de `FOL.lean` y
> **meterían tres módulos huérfanos con declaraciones duplicadas**, uno de los cuales
> redefine `derive_hyp`/`derive_weaken`, de `FOL.Tactics`, que ROBINSON_PlusPlus importaba **22 veces**
> el 2026‑09‑12 (9 el 2026‑10‑02, medido en RPP `b1dedd1`, tras retirar su capa `⊢`: ADR‑115 de RPP).
> Tan prohibido como `cd FOL && lake build`. La cabecera de `gen-root.bash` dice qué
> haría falta para levantar la prohibición.

> Ver [WORKFLOW.md](WORKFLOW.md) para el flujo completo.

## Documentation

| Document | Purpose |
|----------|---------|
| [WORKFLOW.md](WORKFLOW.md) | ⭐ Flujo de desarrollo completo |
| [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) | Estado actual y métricas |
| [NEXT-STEPS.md](NEXT-STEPS.md) | Fases de desarrollo planificadas |
| [PLANNING.md](PLANNING.md) | Hoja de ruta estratégica |
| [REFERENCE.md](REFERENCE.md) | Referencia técnica de definiciones y teoremas |
| [AI-GUIDE.md](AI-GUIDE.md) | Guía de convenciones y estándares |
| [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) | Convenciones de nombres Mathlib-style |
| [CHANGELOG.md](CHANGELOG.md) | Historial de cambios |
| [DEPENDENCIES.md](DEPENDENCIES.md) | Diagramas de dependencias |
| [DECISIONS.md](DECISIONS.md) | Architectural Decision Records |
| [THOUGHTS.md](THOUGHTS.md) | Diario de diseño |

## Naming Conventions

Este proyecto sigue las [convenciones de Mathlib4](https://leanprover-community.github.io/contribute/naming.html).

| Entity | Convention | Example |
|--------|------------|---------|
| Module | `UpperCamelCase` | `CoreAxioms.lean` |
| Namespace | `UpperCamelCase` | `FOL.Metamath.Soundness` |
| Type / Prop predicate | `UpperCamelCase` | `IsConsistent`, `IsFun` |
| Function / value def | `lowerCamelCase` | `neg`, `satisfies` |
| Theorem | `subject_predicate` | `proves_iff_models` |

## License

MIT License. Ver [LICENSE](LICENSE).

## Author

Julián Calderón Almendros

## Credits

### AI Tools

- Claude (Anthropic) — vía GitHub Copilot CLI

---

**Author**: Julián Calderón Almendros
**Last updated:** 2026-10-03 — la deuda de los cinco módulos 🧊 con textos falsos, SALDADA (`thaw` autorizado, sólo comentarios, re‑congelados). Antes, 2026-10-02 — 🗑️ `FOL/MetaRules.lean` borrado (ADR‑115 de RPP): aviso (la solidez de `Derives` es un teorema, 0 `axiom`, la deuda de cinco módulos 🧊), «Deducción Natural» (sin `raa`), hito 2, la fila histórica de `Soundness.lean` y las importaciones de `FOL.Tactics` desde RPP. Antes (2026-09-27): la auditoría de constructividad y D1–D8: aviso (la tesis del WKL, rectificada), la instancia de `TheoryFramework` y los hitos 3, 4 y 6. Antes, el mismo día: el decisor del fragmento sin cuantificadores; renombres de la regla de subíndices (P2). Antes (2026-09-26): aviso, insignias, librerías, hitos y cabeceras HISTÓRICO corregidos; el resto del cuerpo es de 2026-05-16.
