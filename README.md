# FOL Ecosystem — Formalización de Lógica en Lean 4

> # ⛔⛔ AVISO DE ESTADO — 2026-09-26 (reescrito: el del 2026-09-12 había quedado FALSO). LEER ANTES QUE NADA
>
> **Este documento estaba fechado en mayo de 2026 y publicaba como hitos demostrados cosas que
> hoy están medidas FALSAS.** Se corrigen abajo las afirmaciones concretas; el resto del texto
> **no se ha reescrito** y debe leerse con esta advertencia delante.
>
> | lo que decía | lo medido |
> |---|---|
> | «Teorema de Corrección (Soundness): `Γ ⊢ A → Γ ⊨ A`» ✅ | 🏁 **Sí, sobre `Derives₀`** (2026-09-14): `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f` (`FOL/Soundness0.lean`), y con ella `derives0_consistent`. ⛔ La de **`Derives`** sigue siendo **FALSA** en presencia de `FOL/MetaRules.lean`: `FOL/Inconsistencia.lean`, hoy **en el build** |
> | «Compacidad» ✅ | 🏁 `compactness₀`, `loewenheim_skolem_down` y el modelo infinito `infinite_model_of_large`, en `FOL/Compacity0.lean`. El `Compacity.lean` vacuo **se borró** el 2026-09-23 |
> | «Completitud» ✅ / «1 sorry» | 🏁 `completeness₀ : Γ ⊨ f → Γ ⊢₀ f` (`FOL/Canonical0.lean`, 2026-09-16), con **cero axiomas del proyecto**: `[propext, Classical.choice, Quot.sound]`, y ese `Classical.choice` es el WKL de `Lindenbaum0` (ADR-041). `Completeness.lean` y su último postulado, `henkin_extension_lemma`, **se borraron** el 2026-09-23. Ver **`AXIOMS.md`** |
> | «4 `lean_lib`, ~43 módulos, 1 sorry, v4.28.0» | **2 `lean_lib`** (`FOL`, `TheoryFramework`) · **4 `axiom`**, los de `MetaRules` que el kernel obliga, y ninguno más fuera de las librerías retiradas · **0 sorry** · **v4.31.0**. `FOLPure`, `PropLogic` y `FOL_poli` **retiradas** el 2026-09-12 a `cuarentena/librerias-retiradas/` |
>
> ⭐ **Los seis teoremas del cierre (T1 a T6, 2026-09-23 y 2026-09-26) están en el árbol**, sobre `Derives₀`; el catálogo, en `CURRENT-STATUS-PROJECT.md` («Estado vigente») y `REFERENCE.md` §6. ⛔ Y lo que NO hay: la propiedad de disyunción para `Derives₀` es **FALSA** (`derives0_no_disjunction_property`).
> (Este aviso decía que «lo único sólido MEDIDO» era `prf0_soundness`, en RPP: dejó de serlo el 2026-09-14.)
>
> **Fuentes:** `cuarentena/README.md` · `AXIOMS.md` ·
> `../ROBINSON_PlusPlus/doc/AUDITORIA-FOL-2026-09-12.md`

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
| `TheoryFramework` | Marco genérico de teorías — ⛔ **sin instancias** desde el 2026-09-23 (`folSystem` retirada) | 0 |

## Description

Este ecosistema formaliza la sintaxis, semántica y metamatemática de la Lógica Clásica en múltiples capas, con el objetivo de proporcionar una base rigurosa para la fundamentación de la matemática.

**Características principales:**

- **Sintaxis De Bruijn**: Índices de De Bruijn en fórmulas y términos, evitando la captura de variables en cuantificadores.
- **Deducción Natural**: Sistema extendido con reglas de reescritura local y RAA (lógica clásica).
- **Automatización**: Tácticas `derive_hyp`, `derive_weaken`, `derive_rewrite` via `MetaM`.
- **Semántica Tarskiana**: Modelos, evaluación de fórmulas, satisfacción `Γ ⊨ f`.
- **Marco Genérico**: `class LogicSystem (F : Type)` con metateoremas reutilizables — ⛔ sin instancias desde el 2026-09-23.

**Hitos Metamatemáticos:**

1. Teorema de Deducción.
2. 🏁 **Teorema de Corrección** sobre `Derives₀` (`derives0_soundness`). ⛔ La de `Derives` es FALSA con `MetaRules`: ver el aviso.
3. Construcción de Henkin + Lema de Lindenbaum.
4. 🏁 **Teorema de Completitud** sobre `Derives₀`: `completeness₀ : Γ ⊨ f → Γ ⊢₀ f`, cero axiomas del proyecto; y su forma de Henkin, `model_existence_iff`.
5. 🏁 **Compacidad** (`compactness₀`), **Löwenheim–Skolem descendente** y el **modelo infinito por compacidad** (`infinite_model_of_large`: numerable e infinito).
6. Hauptsatz (`hauptsatz`), Herbrand, Craig, Skolem y forma prenexa; el fragmento sin cuantificadores caracterizado (`derives0_qf_iff`); decisor proposicional (`ptautCheck_iff`); inversión de `LK₀`. Catálogo: `REFERENCE.md` §6. ⛔ Los metateoremas genéricos sobre `LogicSystem` siguen en el build, pero el marco **no tiene instancias** desde el 2026-09-23.

## Modules — ⚠️ HISTÓRICO (2026-05-16): el catálogo vigente es `REFERENCE.md` §6

### `FOL` — FOL con Igualdad

| Module | Namespace | Status |
|--------|-----------|--------|
| `Prelim.lean` | top-level | ✅ |
| `FOL.lean` | top-level | ✅ |
| `Tactics.lean` | top-level | ✅ |
| `Deduction.lean` | `FOL.Metamath.Deduction` | ✅ |
| `Semantics.lean` | `FOL.Metamath.Semantics` | ✅ |
| ~~`Soundness.lean`~~ | — | ⛔ **CUARENTENA**: su teorema es FALSO |
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
import TheoryFramework
-- ⛔ HISTÓRICO: `Instances/FOLPure` y `Instances/PropLogic` ya no existen, e `Instances/FOL` no declara ninguna instancia desde el 2026-09-23
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
> redefine `derive_hyp`/`derive_weaken` que ROBINSON_PlusPlus importa **22 veces**.
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
**Last updated:** 2026-09-26 — aviso, insignias, librerías, hitos y cabeceras HISTÓRICO corregidos; el resto del cuerpo es de 2026-05-16.
