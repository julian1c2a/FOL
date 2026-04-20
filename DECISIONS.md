# Design Decisions — ProjectName

**Last updated:** 2026-04-20 00:00
**Author**: Julián Calderón Almendros

Architectural Decision Records (ADR) for this project.
Each entry records *what* was decided and *why*, for future reference.

---

## ADR-001: No Mathlib dependency

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: This project does not depend on Mathlib.

**Rationale**: [Explain why — e.g., educational goals, performance, avoiding API churn, etc.]

**Consequences**: All necessary infrastructure (ExistsUnique, etc.) must be built from scratch.

---

## ADR-002: autoImplicit = false

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: `moreServerArgs := #["-DautoImplicit=false"]` is set in `lakefile.lean`.

**Rationale**: Explicit type annotations prevent accidental universe polymorphism issues and make code easier to read and maintain.

**Consequences**: All variables must be explicitly declared or annotated.

---

## ADR-003: File locking system

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: Use `git-lock.bash` + `locked_files.txt` + pre-commit hook to prevent accidental edits to completed modules.

**Rationale**: Lean 4 proofs are fragile — small changes to completed modules can break dependent proofs. The locking system makes this explicit.

**Consequences**: Workflow requires locking/unlocking files. See AI-GUIDE.md §20.

---

## ADR-004: Mathlib naming conventions

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: All identifiers follow Mathlib4 naming conventions as documented in NAMING-CONVENTIONS.md.

**Rationale**: Consistency with the broader Lean 4 ecosystem. Makes theorems discoverable by name pattern (`mem_X_iff`, `subject_predicate`). Facilitates future Mathlib integration if desired.

**Consequences**: Existing names may need migration. See NAMING-CONVENTIONS.md for the full dictionary and 12 formation rules. REFERENCE.md §0 provides a quick reference.

---

## ADR-005: Directory-aligned namespaces

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: Each subdirectory corresponds to a sub-namespace: `ProjectName/Foo/Bar.lean` → `namespace ProjectName.Foo.Bar`.

**Rationale**: Clear 1:1 mapping between file system and namespace hierarchy. Reduces confusion about where definitions live. Scales well as the project grows.

**Consequences**: `new-module.bash` must handle subdirectory creation. `gen-root.bash` must scan recursively.

---

## ADR-006: Annotation system in REFERENCE.md

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: REFERENCE.md entries include `@axiom_system` and `@importance` annotations.

**Rationale**: Helps AI assistants prioritize which modules/theorems to load for context. Provides quick classification without reading module code.

**Consequences**: Annotations must be maintained when modules are updated. See AI-GUIDE.md §24-25.

---

## ADR-007: Separate NAMING-CONVENTIONS.md file

**Date**: 2026-04-20
**Status**: Accepted

**Decision**: Naming conventions live in a dedicated NAMING-CONVENTIONS.md file, with a summary in AI-GUIDE.md and REFERENCE.md §0.

**Rationale**: The full naming dictionary with 12 rules and migration tables is too large for AI-GUIDE.md alone. A separate file allows detailed examples without bloating the main guide.

**Consequences**: Three places reference naming: NAMING-CONVENTIONS.md (canonical), AI-GUIDE.md (summary), REFERENCE.md §0 (reader guide). All must be kept in sync.

---

## Template for new decisions

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]
