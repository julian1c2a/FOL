# Changelog

**Last updated:** 2026-05-16
**Author**: Julián Calderón Almendros

All notable changes to this project will be documented in this file.

Format based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added (2026-05-16)

- **TheoryFramework** — nueva `lean_lib` con marco genérico de teorías:
  - `Logic.lean`: `class LogicSystem (F : Type)` con campos `derives`, `bottom`, `neg`, `semanticEntails`, `sound`, `complete`.
  - `Theory.lean`: `structure Theory F`, operaciones `proves`, `models`, `empty`, `fromList`, `singleton`.
  - `Properties.lean`: `IsConsistent`, `IsSyntacticallyComplete`, `IsAxiomRedundant`, `IsIrredundant`, `IsMaximalConsistent`.
  - `Relations.lean`: `LE (Theory F)` (extensión de teorías), `TheoryEquivalent`, `IsConservativeExtension`, `TheoryUnion`, `TheoryIntersection`, lemas de monotonía.
  - `MetaTheorems.lean`: `proves_iff_models`, `proves_monotone`, `models_monotone`, `inconsistent_upward`, `consistent_of_le`, `equiv_of_conservative`, `TheoryEquivalent.symm/trans`, `empty_le`.
  - Instancias: `LogicSystem PropLogic.Formula`, `LogicSystem Formula` (FOLPure), `LogicSystem Formula` (FOL^=, heredando el sorry de Completeness).
- **FOLPure** — nueva `lean_lib` con FOL sin igualdad (0 sorries):
  - Misma arquitectura que `FOL` pero sin `Formula.eq`, `refl`, `subst`.
  - Completitud de Gödel y Compacidad demostradas sin sorries.
- **PropLogic** — nueva `lean_lib` con lógica proposicional (0 sorries):
  - Subconjunto de FOLPure sin cuantificadores.
  - Stack metamatemático completo: Deducción, Soundness, Completeness, Compacity.
  - Módulos `Theorems/Impl.lean`, `Theorems/Neg.lean`, `Theorems/Derived.lean`.

### Added (2026-05-08 18:22)

- **Fase 6 Completada (FOL con Igualdad)**:
  - Refactorización del modelo canónico a un modelo cociente (`CanonicalDomain`) basado en la equivalencia sintáctica (`termEqv`).
  - Demostración de los teoremas de congruencia y "lift" de funciones y predicados al nuevo dominio.
  - Adaptación y demostración del Lema de la Verdad (`truth_lemma`) para el modelo cociente.
  - Demostración del Teorema de Completitud de Gödel para FOL con Igualdad.
  - Demostración del Teorema de Compacidad Semántica como corolario en `Compacity.lean`.

### Added (2026-04-25 22:00)

- El proyecto base de Lógica de Primer Orden (FOL) se congela en su versión 1.0.0.
- Inicio de la nueva arquitectura para incluir Igualdad (`=`) en una nueva rama.

### Added (2026-04-25 21:30)

- Declaración del axioma `henkin_extension_lemma` para manejar la expansión de constantes.
- Formalización del Teorema de Compacidad (`compactness_theorem`) y Consistencia (`consistency_of_satisfiable`) en `Compacity.lean`.
- El proyecto alcanza oficialmente **0 sorries** en su totalidad. ¡Hito final completado!
- Build status: ✅ Passing, 0 warnings.

### Added (2026-04-25 21:00)

- Formalización de la construcción de Henkin en `Completeness.lean`.
- Demostración formal del Lema de Lindenbaum (`lindenbaum_lemma`) y Compacidad Sintáctica.
- Demostración del Lema de la Verdad (`truth_lemma`) mediante inducción fuerte sobre la complejidad de fórmulas.
- Demostración del Teorema de Completitud de Gödel (`completeness`).

### Added (2026-04-25 20:30)

- Demostración completa de los lemas de sustitución semántica y reescritura en `FOL/Semantics.lean`, resolviendo la "trampa de De Bruijn" mediante inducción generalizada.
- El proyecto alcanza 0 sorries en toda la formalización de la sintaxis, deducción natural y corrección semántica (Soundness).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-25 20:00)

- Demostración completa del Teorema de Deducción en `FOL/Deduction.lean`.
- Definición de Modelos y Semántica de la lógica de primer orden en `FOL/Semantics.lean` (`Model`, `evalFormula`, `satisfies`).
- Demostración completa del Teorema de Corrección (Soundness) en `FOL/Soundness.lean` apoyada en los lemas semánticos.
- Implementación de la táctica `derive_raa` en `FOL/Tactics.lean`.
- Estado del Build: 0 errores, 5 sorries activos en `Semantics.lean` correspondientes a los lemas de sustitución y reescritura.

### Added (2026-04-25)

- Implementación de tácticas de automatización en `FOL/Tactics.lean`: `derive_hyp`, `derive_rewrite` y `derive_weaken`.
- Finalización oficial de la Fase 4 (Automatización).
- Inicio formal de la Fase 5 (Metamatemática y Completitud).
- Estado del Build: 0 errores, 0 sorries activos.

### Added (2026-04-20 00:00)

- Initial project structure from lean4-project-template

---

## [0.2.0] - 2026-04-20

### Added

- `NAMING-CONVENTIONS.md`: Full Mathlib-style naming dictionary with 12 formation rules, symbol-to-word dictionary, and migration tables
- `NEXT-STEPS.md`: Development phase planning template
- `THOUGHTS.md`: Design journal template for recording ideas and alternatives
- `REFERENCE.md` §0: Naming conventions quick-reference guide for the reader
- `REFERENCE.md` §Compliance: Checklist against AI-GUIDE.md requirements
- `AI-GUIDE.md` §22-23: Directory and subdirectory organization protocol
- `AI-GUIDE.md` §24-25: Annotation system (`@axiom_system`, `@importance`)
- `AI-GUIDE.md` §26-28: Cross-reference files documentation
- `AI-GUIDE.md`: Symbol-to-word dictionary and theorem formation rules summary in Naming Conventions section
- `DECISIONS.md`: ADR-004 (Mathlib naming), ADR-005 (directory-aligned namespaces), ADR-006 (annotation system), ADR-007 (separate NAMING-CONVENTIONS.md)
- `_template.lean`: Added naming convention reminders, annotation metadata, expanded section structure
- `CURRENT-STATUS-PROJECT.md`: Development phases tracking table

### Changed

- `README.md`: Added naming conventions summary table, documentation table format, subdirectory-aware project structure
- `DEPENDENCIES.md`: Added subdirectory-aware structure, multi-level dependency hierarchy example, Mermaid subgraph example

---

## [0.1.0] - 2026-04-20

### Added

- `Prelim.lean`: preliminary definitions

---

## Versioning Conventions

- **MAJOR**: Breaking API changes or new foundational axiom
- **MINOR**: New backward-compatible functionality
- **PATCH**: Bug fixes and backward-compatible corrections

## Links

- [Repository](https://github.com/julian1c2a/ProjectName)
- [Issues](https://github.com/julian1c2a/ProjectName/issues)
