# ProjectName

[![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Coverage](https://img.shields.io/badge/proofs-100%25%20complete-brightgreen)](CURRENT-STATUS-PROJECT.md)

> **Status**: See [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) for complete details

Una implementación formal de la **Lógica de Primer Orden (FOL)** en Lean 4, construida completamente desde cero sin dependencias de Mathlib.

## Description

Este proyecto formaliza la sintaxis, semántica y metamatemática de la Lógica de Primer Orden clásica. El objetivo ha sido proporcionar una base rigurosa, computacionalmente clara y matemática del comportamiento del razonamiento lógico formal.

**Características principales:**

- **Sintaxis Rigurosa**: Implementación de fórmulas y términos mediante índices de De Bruijn, resolviendo elegantemente el problema de la captura de variables en cuantificadores ($\forall, \exists$).
- **Sistema Deductivo**: Formalización de un sistema de Deducción Natural extendido con reglas de reescritura locales.
- **Automatización (Metaprogramación)**: Desarrollo de tácticas (`derive_hyp`, `derive_weaken`, `derive_rewrite`) utilizando el framework `MetaM` de Lean 4 para agilizar demostraciones.
- **Semántica Tarskiana**: Definición precisa de Modelos, funciones de evaluación y la noción de satisfacción lógica ($\Gamma \models f$).

**Hitos Metamatemáticos Demostrados:**

1. Tautologías clásicas y equivalencias (Doble Negación, De Morgan, Dualidad de Cuantificadores).
2. **Teorema de Deducción**.
3. **Teorema de Corrección (Soundness)**: $\Gamma \vdash A \implies \Gamma \models A$.
4. **Construcción de Henkin y Lema de Lindenbaum**.
5. **Teorema de Completitud de Gödel (para FOL y FOL con Igualdad)**: $\Gamma \models A \implies \Gamma \vdash A$.
6. **Teorema de Compacidad Semántica**.

## Modules

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Prelim.lean` | `top-level` | `Init.Classical` | ✅ Complete |
| `FOL.lean` | `top-level` | `Prelim.lean` | ✅ Complete |
| `Tactics.lean` | `top-level` | `FOL.lean` | ✅ Complete |
| `Deduction.lean` | `FOL.Metamath.Deduction` | `FOL.lean`, `Tactics.lean` | ✅ Complete |
| `Semantics.lean` | `FOL.Metamath.Semantics` | `FOL.lean` | ✅ Complete |
| `Soundness.lean` | `FOL.Metamath.Soundness` | `Semantics.lean`, `Tactics.lean` | ✅ Complete |
| `Completeness.lean` | `FOL.Metamath.Completeness` | `Semantics.lean`, `Deduction.lean` | ✅ Complete |
| `Compacity.lean` | `FOL.Metamath.Compacity` | `Completeness.lean`, `Soundness.lean` | ✅ Complete |
| `Theorems/Eq.lean` | `FOL.Theorems.Eq` | `FOL.FOL` | ✅ Complete |

## Project Structure

```text
FOL/
├── Prelim.lean              # Preliminary definitions
├── FOL.lean                 # Syntax, De Bruijn, and Natural Deduction
├── Tactics.lean             # Metaprogramming macros
├── Deduction.lean           # Deduction Theorem
├── Semantics.lean           # Semantic evaluation & Models
├── Soundness.lean           # Soundness Theorem
├── Completeness.lean        # Gödel's Completeness Theorem & Henkin construction
├── Compacity.lean           # Compactness & Consistency Theorems
└── Theorems/                # Logical equivalences, tautologies, and rules
    ├── Impl.lean
    ├── Neg.lean
    ├── Derived.lean
    ├── Quantifiers.lean
    └── Eq.lean
```

> As the project grows, organize modules into thematic subdirectories.
> See AI-GUIDE.md §22 for the directory organization protocol.

## Installation

```bash
git clone https://github.com/julian1c2a/ProjectName.git
cd ProjectName
lake build
```

## Requirements

- **Lean 4**: v4.28.0 or later
- **Lake**: Included with Lean 4

## Development Workflow

```bash
# Initialize lock system (first time only)
bash git-lock.bash init

# Create a new module (supports subdirectories)
bash new-module.bash ModuleName
bash new-module.bash Topic/SubModule

# Build
make build

# Check for sorry
make sorry

# Show locked files and sorry status
make status

# Regenerate root import file
bash gen-root.bash
```

> See [WORKFLOW.md](WORKFLOW.md) for the complete development workflow.

## Documentation

| Document | Purpose |
|----------|---------|
| [WORKFLOW.md](WORKFLOW.md) | ⭐ **Complete development workflow** (start here after setup) |
| [REFERENCE.md](REFERENCE.md) | Technical reference for all definitions and theorems |
| [AI-GUIDE.md](AI-GUIDE.md) | Documentation standards, naming conventions, and AI assistant guide |
| [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) | Full Mathlib-style naming dictionary and formation rules |
| [CHANGELOG.md](CHANGELOG.md) | Change history |
| [DEPENDENCIES.md](DEPENDENCIES.md) | Module dependency diagrams |
| [DECISIONS.md](DECISIONS.md) | Architectural Decision Records (ADR) |
| [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) | Current project status and metrics |
| [NEXT-STEPS.md](NEXT-STEPS.md) | Planned development phases |
| [THOUGHTS.md](THOUGHTS.md) | Design journal and ideas |

## Naming Conventions

This project follows [Mathlib4 naming conventions](https://leanprover-community.github.io/contribute/naming.html).
See [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) for the full reference.

**Quick summary:**

| Entity | Convention | Example |
|--------|------------|---------|
| Module | `UpperCamelCase` | `CoreAxioms.lean` |
| Namespace | `UpperCamelCase` | `ProjectName.Topic` |
| Type / Prop predicate | `UpperCamelCase` | `IsSet`, `IsFun` |
| Function / value def | `lowerCamelCase` | `powerset`, `dom` |
| Axiom | `TAG_ShortName` | `ZF_Ext`, `MK_Pair` |
| Theorem | `subject_predicate` | `mem_pair_iff` |

## License

This project is under the MIT License. See [LICENSE](LICENSE) for details.

## Author

Julián Calderón Almendros

## Credits

### Educational Resources

- [add resources here]

### Bibliographic References

- [add references here]

### AI Tools

- Claude Code AI (Anthropic)

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-04-25 21:30*
