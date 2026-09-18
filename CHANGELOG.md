# Changelog

**Last updated:** 2026-09-18
**Author**: Julián Calderón Almendros

> ⛔⛔ **ESTE FICHERO ESTUVO CONGELADO EN 2026-05-16 CON 115 COMMITS DETRÁS**, y no fue un
> descuido inocuo: el control `[E]` de `check-doc-sync.bash` usaba **la entrada más reciente de
> este CHANGELOG como referencia** para juzgar si los titulares de los demás documentos se habían
> quedado atrás. Con la referencia congelada, ningún documento podía estar «por detrás» de ella
> ⇒ **el control aprobaba siempre** (ADR-072).
> 🔑 *Un diario que nadie escribe no es sólo un diario vacío: es una referencia falsa para
> todo lo que se apoye en él.*
> ⚠️ Las entradas de abajo, del 2026-09-11 en adelante, se han reconstruido desde `git log` y
> desde las ADR de `../ROBINSON_PlusPlus/DECISIONS.md`. Son un **ÍNDICE de lo que aterrizó**, no
> un inventario exhaustivo de los 115 commits; la fuente de verdad de cada pieza es su ADR.

All notable changes to this project will be documented in this file.

Format based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added (2026-09-18) — el tipo de los SÍMBOLOS pasa a ser un PARÁMETRO

- **ADR-068** — `TermG (S : Type)` / `FormulaG (S : Type)` en `FOL/FOL.lean`, con
  `abbrev Term := TermG String` y `abbrev Formula := FormulaG String`, más los `export` de
  constructores y `injEq` y **tres shims** (`Term.noConfusion`, `Formula.noConfusion`,
  `Formula.ex.inj`): para un inductivo CON parámetro, Lean 4.31 genera el `noConfusion`
  **heterogéneo** y **no** genera `Ctor.inj`. Coste medido: **3 ficheros**, 147 footprints
  idénticos.
- **ADR-069** — la **capa de operaciones** genérica en `Sym`: `neg`/`top`/`iff`, `lift*`,
  `subst*`, `getAt?`/`replaceAt`, más `occurs*`/`abs*` (`Eigenvariable`) y `rename*` (`Rename`).
  Nuevo módulo **`FOL/SymClasses.lean`** con las clases `FreshSym` y `EnumSym` y la instancia
  `FreshSym (List Char)`; las de `String` viven donde viven sus pruebas.
  ⛔ `Derives` y `LocalRule` se dejan en `String` — decisión, no olvido.
- **ADR-071** — `Derives₀` y `LocalRule` genéricos, con el parámetro **implícito** para que la
  notación `⊢₀` sobreviva. Dos firmas, cero errores en los 22 ficheros consumidores.
  ⛔ Rectifica ADR-069: `LocalRule` sigue a `Derives₀`, no a `Derives`.
- **ADR-072** — el control `[E]` de `check-doc-sync.bash`, **rearmado**: la referencia deja de ser
  este fichero y pasa a calcularse por documento (`git log -1` del propio documento), con tabla
  de deuda declarada y rotura en los dos sentidos.

### Added (2026-09-17) — el HAUPTSATZ, el catálogo clásico y la forma normal de Skolem

- **ADR-050/051/052** — `FOL/Hauptsatz0.lean`: **`hauptsatz : CutAdm`**, `cut_elimination`,
  `herbrand_extraction` y **`herbrand`** ya incondicional. `[propext, Quot.sound]`.
- **ADR-053…056** — el catálogo clásico: `derives0_consistent_fin` (consistencia **sin**
  `Classical.choice`), `compactness₀`, `loewenheim_skolem_down`, `derives0_exBlock_of_cert`,
  `henkin_conservative`.
- **ADR-057…060** — la capa **prenexa** (`Prenex0`, `PrenexNF0`) y **Skolem** (`Skolem0`,
  `SkolemN0`), incluido el axioma bajo un prefijo `∀ⁿ`.
- **ADR-061** — FOL adopta `check-doc-sync.bash`; en su primera ejecución encuentra nueve cosas.
- **CI** — FOL vuelve a tener CI: no la tenía desde mayo, y las dos veces que había corrido
  **falló en 0 s**. El gate de `sorry` pasa a ser **bloqueante**.

### Added (2026-09-16) — COMPLETITUD, y la vía H

- **ADR-039/040/041** — `FOL/Canonical0.lean`: **`completeness₀ : Γ ⊨ f → Γ ⊢₀ f`** y
  `derives0_complete_iff`, con **cero axiomas del proyecto**. La no-finitud queda en **una línea**
  Π⁰₁ (el `if IsConsistent₀` de `LindenbaumStep`): es el **WKL**.
- **ADR-042…049** — la vía H: `Derives₁`, `Derives₂`, el certificado de Herbrand,
  `LK₀`/`LKc`, `ndToLK`, y la solidez del cálculo de secuentes.

### Added (2026-09-14) — `Derives₀`, y con él una metateoría que significa algo

- **ADR-033** — **`Derives₀`**: los 21 constructores **sin la ω-regla ni los cuatro
  habitantes-axioma** ⇒ se puede inducir sobre él (M-11 no aplica).
- **ADR-034…037** — `derives0_soundness` (el repo tiene por fin un cálculo de FOL⁼ **sólido**),
  el renombrado y su recíproca, el paso de **eigenvariable**, y `henkin_step_consistent`.

### Added (2026-09-13) — la Completitud, de cinco axiomas a uno

- **ADR-030** — la enumerabilidad de `Formula` deja de ser un postulado (`FOL/Enumeration.lean`).
- **ADR-031** — las dos congruencias de la igualdad, demostradas.
- **ADR-032** — `henkin_extension_lemma` **medido**: sale, y **por eso no se paga**; queda
  protegido por `check-axioms.bash`, que rompe **también si el contador baja a 0**.

### Changed (2026-09-12) — la cuarentena, los axiomas y la doctrina

- FOL pasa de **13 a 4** `axiom`, y los cuatro son los que el kernel obliga.
- Se retiran tres librerías, entra `TheoryFramework`, y `git-lock` deja de proteger lo que no era.

### Removed (2026-09-11) — ⛔ `soundness` era FALSO

- `soundness : Γ ⊢ f → Γ ⊨ f` **no es demostrable porque no es verdad**, y junto con `raa`
  demostraba **`False` sin hipótesis**. Evidencia compilada en `cuarentena/Inconsistencia.lean`.
  De aquí sale **M-11**: *un `axiom` que HABITA un inductivo prohibe demostrar nada sobre él por
  INDUCCIÓN*. ⚠️ Y `gen` **no** es la ω-regla — su docstring lo decía y era falso.

### Changed (2026-05-28 … 2026-07-12) — lo que hubo entre medias

- `subst_lift_cancel_formula` era un **`axiom` FALSO**; pasa a teorema en su forma restringida
  verdadera (2026-06-23), y la corrección se propaga a `FOLPure`/`FOL_poli` en septiembre.
- Conmutaciones De Bruijn en `Theorems/Eq.lean`, meta-reglas ω en `MetaRules.lean`, `dne`,
  semantica polimórfica, modelo cociente para FOL⁼.
- Toolchain a **Lean v4.31.0** (2026-07-04) y plantilla unificada de gobernanza (2026-07-12).

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
