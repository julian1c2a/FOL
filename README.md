# FOL Ecosystem — Formalización de Lógica en Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Sorries](https://img.shields.io/badge/sorries-1%20(expected)-yellow)](CURRENT-STATUS-PROJECT.md)

> **Status**: Ver [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) para detalles completos.

Cuatro librerías Lean 4 en un mismo repositorio, construidas desde cero sin dependencias de Mathlib:

| Librería | Descripción | Sorries |
|----------|-------------|---------|
| `FOL` | Lógica de Primer Orden **con** igualdad (FOL^=) | 1 (esperado) |
| `FOLPure` | Lógica de Primer Orden **sin** igualdad | 0 |
| `PropLogic` | Lógica proposicional (subconjunto sin cuantificadores) | 0 |
| `TheoryFramework` | Marco genérico de teorías sobre cualquiera de las tres lógicas | 0 |

## Description

Este ecosistema formaliza la sintaxis, semántica y metamatemática de la Lógica Clásica en múltiples capas, con el objetivo de proporcionar una base rigurosa para la fundamentación de la matemática.

**Características principales:**

- **Sintaxis De Bruijn**: Índices de De Bruijn en fórmulas y términos, evitando la captura de variables en cuantificadores.
- **Deducción Natural**: Sistema extendido con reglas de reescritura local y RAA (lógica clásica).
- **Automatización**: Tácticas `derive_hyp`, `derive_weaken`, `derive_rewrite` via `MetaM`.
- **Semántica Tarskiana**: Modelos, evaluación de fórmulas, satisfacción `Γ ⊨ f`.
- **Marco Genérico**: `class LogicSystem (F : Type)` que abstrae las tres lógicas con metateorémas reutilizables.

**Hitos Metamatemáticos:**

1. Teorema de Deducción.
2. **Teorema de Corrección** (Soundness): `Γ ⊢ A → Γ ⊨ A`.
3. Construcción de Henkin + Lema de Lindenbaum.
4. **Teorema de Completitud de Gödel**: `Γ ⊨ A → Γ ⊢ A` (FOL, FOLPure, PropLogic).
5. **Teorema de Compacidad Semántica**.
6. Metateorémas genéricos sobre cualquier `LogicSystem`: monotonía de pruebas, preservación de inconsistencia, extensiones conservativas.

## Modules

### `FOL` — FOL con Igualdad

| Module | Namespace | Status |
|--------|-----------|--------|
| `Prelim.lean` | top-level | ✅ |
| `FOL.lean` | top-level | ✅ |
| `Tactics.lean` | top-level | ✅ |
| `Deduction.lean` | `FOL.Metamath.Deduction` | ✅ |
| `Semantics.lean` | `FOL.Metamath.Semantics` | ✅ |
| `Soundness.lean` | `FOL.Metamath.Soundness` | ✅ |
| `Completeness.lean` | `FOL.Metamath.Completeness` | ⚠️ 1 sorry |
| `Compacity.lean` | `FOL.Metamath.Compacity` | ✅ |
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

## Project Structure

```text
repo/
├── FOL/                     # FOL^= con igualdad
│   ├── FOL.lean             # Sintaxis + Derives (incl. eq, refl, subst)
│   ├── Tactics.lean
│   ├── Deduction.lean
│   ├── Semantics.lean
│   ├── Soundness.lean
│   ├── Completeness.lean    # ⚠️ 1 sorry (eq/Henkin)
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

## Installation

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
import TheoryFramework.Instances.FOLPure  -- o PropLogic / FOL (no mezclar)
```

## Requirements

- **Lean 4**: v4.28.0 o posterior
- **Lake**: incluido con Lean 4
- Sin dependencias de Mathlib.

## Development Workflow

```bash
make build      # lake build
make sorry      # check-sorry.bash
make status     # locked files + sorry status
bash new-module.bash ModuleName
bash gen-root.bash
```

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
*Last updated: 2026-05-16*
