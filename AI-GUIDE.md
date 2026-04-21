# AI Assistant Guide — Documentation Standards

**Last updated:** 2026-04-20 00:00
**Author**: Julián Calderón Almendros

This document establishes requirements and standards for technical documentation of this Lean 4 project.

> **This file is the first document an AI assistant should read.**
> It defines the project's documentation protocol, naming conventions,
> file locking policy, and compliance checklist. Read it fully before
> touching any `.lean` file or documentation.

---

## Requirements for REFERENCE.md

### (0.) **This documentation is technical, not user-facing.** It is a reference for AI assistants and experienced Lean 4 developers. Clear, precise, complete — but not pedagogical

### (1.) **Lean modules**: List all `.lean` files in both root and subdirectories, with location, namespace, dependencies, and documentation status

### (2.) **Module dependencies**: Each module must clearly document which modules it depends on, and which modules depend on it. Critical for AI navigation without loading the full project

### (3.) **Namespaces and their relationships**: Namespaces are not necessarily equal to modules. Document which namespaces exist, which modules they belong to, and how they relate

### (4.) **Introduced definitions**: For each module and namespace, document all definitions with location, dependencies, mathematical notation, and Lean 4 signature

#### (4.1.) **How to document definitions**: Include the Lean 4 signature plus mathematical notation (no explanations — the audience is mathematicians and Lean 4 experts). Include module, namespace, and dependencies

#### (4.2.) **Computability**: Indicate whether the definition is computable or noncomputable, and whether it has a boolean counterpart, and if it is decidable or not

#### (4.3.) **Well-foundedness**: Indicate whether the definition includes a termination proof (*terminated by*)

#### (4.4.) **Notation**: Record introduced notation: infix/prefix/other, symbols used, priorities, so it can be used correctly in proofs and documentation

### (5.) **Introduced axioms and their references**: Each axiom must document its location (module, namespace, declaration order) and relationship to definitions

### (6.) For **axioms** and **definitions**, provide

#### (6.1.) **Mathematical notation** (not Lean code) for human readability. No explanations — mathematical language suffices

#### (6.2.) **Lean 4 signature** for correct usage in proofs and constructions

#### (6.3.) **Dependencies** required to build the definition or axiom

### (7.) Main theorems **without proof of any kind**, with reference to location (module, namespace, declaration order)

#### (7.1.) **Mathematical notation** (not Lean code)

#### (7.2.) **Lean 4 signature**

#### (7.3.) **Dependencies** required to prove the theorem

### (8.) **Nothing unproven goes in REFERENCE.md** — no pending theorems, no TODOs in this file. Only what is already proven or constructed in `.lean` files

### (9.) **Update REFERENCE.md each time you load a `.lean` file** and find something new. Record the date and the last modification date of the `.lean` file for traceability

### (10.) **REFERENCE.md must be self-sufficient** — enough to write new modules or documentation without loading the full project. This file **REFERENCE.md** is the primary purpose of the file for AI assistants

### (11.) **When reading a `.lean` file, add or verify its REFERENCE.md header comment** reminding the reader to project the file

### (12.) **"Projecting" a `.lean` file into REFERENCE.md** means updating REFERENCE.md with all relevant information proven or constructed in that file, following the points above

### (13.) **Relevant information** means all non-private definitions, notations, axioms, theorems, and any other content necessary to understand the project, use it as reference, or build further proofs

### (14.) **Everything exportable in a `.lean` module must be projected into REFERENCE.md** and must appear in the module's export block

---

## Timestamps

### (15.) All technical documentation files must include timestamps in `YYYY-MM-DD HH:MM` format (ISO 8601 abbreviated)

Applied to: REFERENCE.md, CHANGELOG.md, DEPENDENCIES.md, CURRENT-STATUS-PROJECT.md, and any technical summary file.

Purpose: Track how outdated a file is relative to REFERENCE.md, even within a single work session.

---

## Authorship and License

### (16.) All principal documentation files (README.md, REFERENCE.md, CURRENT-STATUS-PROJECT.md) must clearly state the author

### (17.) Credits visible in README.md: educational resources, bibliographic references, AI tools used

### (18.) License: MIT. Indicated in LICENSE, README.md, CURRENT-STATUS-PROJECT.md footer, and README.md badge

### (19.) **All `.lean` files must include a copyright header** before any `import`

```lean
/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
```

Placement: lines 1–5 of every `.lean` file, no exceptions (including the root module).

---

## File Locking System

`git-lock.bash` implements two levels of write protection.

### Protection levels

| Level | Command | Reversible | Purpose |
| ------- | --------- | ---------- | ------- |
| **Lock** | `lock` / `unlock` | Yes | One-file-at-a-time during development |
| **Freeze** | `freeze` / `thaw --confirm` | Emergency only | Module completed — immutable forever |

Tracking files:

- `locked_files.txt` — all locked files (lock + freeze)
- `frozen_files.txt` — permanently frozen modules only

### (20.) Session locking protocol

At most one `.lean` file unlocked at any time.

```bash
bash git-lock.bash lock   ProjectName/Module.lean   # temporary lock
bash git-lock.bash unlock ProjectName/Module.lean   # temporary unlock
bash git-lock.bash list                             # show all locked and frozen files
bash git-lock.bash init                             # install/reinstall pre-commit hook
```

Session protocol:

1. **Session start**: Run `list`. Lock all files except the target.
2. **Switching files**: Lock the current file **before** unlocking the next.
3. **Session end**: Lock **all** modified `.lean` files. Commit `locked_files.txt`.
4. **Pre-commit hook**: Blocks commits touching locked or frozen files.

Violation: If more than one file is unlocked, lock all and restart with the correct file.

### (21.) Module freeze protocol — immutable completed modules

When a module reaches ✅ Complete status in REFERENCE.md, it must be **frozen**.
A frozen module is permanently immutable: it cannot be unlocked, only extended.

```bash
bash git-lock.bash freeze ProjectName/Module.lean   # mark as permanently frozen
bash git-lock.bash list                              # shows [frozen] vs [locked]
```

**Attempting to unlock a frozen module is blocked** with a message pointing to
the extension protocol. The pre-commit hook also blocks any staged changes to
frozen files, distinguishing them from ordinary locked files.

**Emergency only** — thawing a frozen module:

```bash
bash git-lock.bash thaw ProjectName/Module.lean --confirm
```

The `--confirm` flag is required. After thawing, update REFERENCE.md status
and document the reason for reopening the module.

#### Extension protocol for frozen modules

When a frozen module `Foo.lean` needs new content:

1. Create `FooExt.lean` in the same directory.

2. Import the frozen module and reopen its namespace:

   ```lean
   /-
   Copyright (c) YYYY. All rights reserved.
   Author: Julián Calderón Almendros
   License: MIT
   -/
   import ProjectName.Foo

   namespace ProjectName   -- same namespace as Foo.lean
   -- new definitions and theorems here
   end ProjectName
   ```

3. Add `FooExt.lean` to `ProjectName.lean` (root import) and to REFERENCE.md.

4. `Foo.lean` remains frozen and untouched.

**Naming rule** (see NC-1): extension files follow `UpperCamelCase`:

| Base module | Extension |
| ----------- | --------- |
| `Prelim.lean` | `PrelimExt.lean` |
| `CoreAxioms.lean` | `CoreAxiomsExt.lean` |
| `Ordinals.lean` | `OrdinalsArithmetic.lean` (content-named preferred) |

Content-named extensions (`OrdinalsArithmetic.lean`, `OrdinalsLimit.lean`) are
preferred over numbered ones (`OrdinalsExt1.lean`) when the topic is clear.

#### REFERENCE.md status codes with freeze

| Code | Meaning |
| ---- | ------- |
| ✅ Complete | Fully projected. May still be locked (temporary). |
| 🧊 Frozen | Permanently frozen. Extensions only via `*Ext.lean`. |
| 🔶 Partial | Documented partially. |
| 🔄 In progress | Actively being developed. |
| ❌ Pending | Not yet started. |

A module transitions: 🔄 → 🔶 → ✅ → 🧊. The 🧊 state is final.

---

## Available Scripts

| Script | Purpose |
| ------ | ------- |
| `bash git-lock.bash lock/unlock <file>` | Temporary file lock |
| `bash git-lock.bash freeze <file>` | Permanent module freeze |
| `bash git-lock.bash thaw <file> --confirm` | Emergency unfreeze |
| `bash git-lock.bash list` | Show locked and frozen files |
| `bash git-lock.bash init` | Install/reinstall pre-commit hook |
| `bash new-module.bash ModuleName` | Create new module from template |
| `bash gen-root.bash` | Regenerate root import file |
| `bash check-sorry.bash` | Find all sorry statements |
| `bash update-toolchain.bash v4.x.x` | Update Lean toolchain with build verification |
| `make help` | Show all Makefile targets |

---

## Naming Conventions

These rules apply to all `.lean` files in this project. Names are in **English**.
The scheme follows Mathlib4 conventions.

> **A separate file `NAMING-CONVENTIONS.md`** contains extended examples,
> detailed rules (12 formation rules), a symbol-to-word dictionary, and
> migration tables. That file is the canonical reference for renaming.
> The summary below is kept in sync with it.

---

### Symbol-to-Word Dictionary (quick reference)

| Symbol | Name | | Symbol | Name | | Symbol | Name |
|--------|------|---|--------|------|---|--------|------|
| ∈ | `mem` | | ∪ | `union` | | + | `add` |
| ∉ | `not_mem` | | ∩ | `inter` | | * | `mul` |
| ⊆ | `subset` | | ⋃ | `sUnion` | | - | `sub`/`neg` |
| ⊂ | `ssubset` | | ⋂ | `sInter` | | / | `div` |
| 𝒫 | `powerset` | | \ | `sdiff` | | ^ | `pow` |
| σ | `succ` | | △ | `symmDiff` | | ∣ | `dvd` |
| ∅ | `empty` | | ᶜ | `compl` | | ≤ | `le` |
| = | `eq` | | ⟂ | `disjoint` | | < | `lt` |
| ≠ | `ne` | | ↔ | `iff` | | 0 | `zero` |
| ¬ | `not` | | → | `of` | | 1 | `one` |

### Theorem Name Formation Rules (summary)

1. **Conclusion first, hypotheses with `_of_`**: `c_of_a_of_b` — conclusion goes first, then `_of_hypothesis`
2. **Biconditionals carry `_iff`**: `mem_powerset_iff` (∈ 𝒫 ↔ ⊆)
3. **Use `.mp`/`.mpr` instead of `_wc` suffixes**: `inter_eq_empty_iff_disjoint.mp`
4. **Algebraic properties → axiomatic suffix**: `union_comm`, `inter_assoc`, `subset_refl`
5. **Predicates as prefix, operations in infix order**: `isNat_zero` (not `zero_is_nat`)
6. **Standard abbreviations**: `pos` (> 0), `neg` (< 0), `nonpos` (≤ 0), `nonneg` (≥ 0)
7. **`Is` prefix for Prop definitions**: `def IsNat` (UpperCamelCase); in theorem names → `lowerCamelCase`: `isNat_zero`
8. **Functions/constructors**: `lowerCamelCase` — `powerset`, `union`, `sep`, `comp`
9. **Specification pattern**: `mem_X_iff` — `mem_succ_iff`, `mem_inter_iff`, `mem_union_iff`
10. **Uniqueness/existence**: `inter_unique`, `powerset_unique`
11. **Lateral variants**: `_left`/`_right` — `subset_union_left`, `union_inter_distrib_left`
12. **Named theorems**: proper names kept as-is — `cantor_no_surjection`, `cantor_schroeder_bernstein`

### Standard Axiomatic Suffixes

| Suffix | Meaning | | Suffix | Meaning |
|--------|---------|---|--------|---------|
| `_comm` | commutativity | | `_self` | op with itself |
| `_assoc` | associativity | | `_left`/`_right` | lateral variant |
| `_refl` | reflexivity | | `_cancel` | cancellation |
| `_trans` | transitivity | | `_mono` | monotonicity |
| `_antisymm` | antisymmetry | | `_inj` | injectivity (iff) |
| `_symm` | symmetry | | `_injective` | injectivity (pred) |
| `_irrefl` | irreflexivity | | `_surjective` | surjectivity |

---

### (NC-1) Modules (`.lean` files)

`UpperCamelCase`. Named after mathematical content, not technical role.

| Pattern | Example |
| ------- | ------- |
| `UpperCamelCase.lean` | `Prelim.lean`, `CoreAxioms.lean`, `Ordinals.lean` |

- Root entry point: `ProjectName.lean` — imports only, no definitions.
- Template: `_template.lean` — underscore prefix marks non-imported utility files.
- Extension of frozen module: `FooExt.lean` — imports `Foo.lean`, reopens its namespace.
- Content-named extensions preferred: `OrdinalsArithmetic.lean` over `OrdinalsExt1.lean`.

---

### (NC-2) Namespaces

`UpperCamelCase`. Mirror the module file hierarchy.

| Level | Pattern | Example |
| ----- | ------- | ------- |
| Root | `ProjectName` | `namespace ProjectName` |
| Sub | `ProjectName.Topic` | `namespace ProjectName.Ordinals` |

- One namespace per module as a rule.
- Do not create sub-namespaces solely for grouping within a file — use `section` instead.
- `private` declarations do not need their own namespace.

---

### (NC-3) Types and Prop-predicates (`def` returning `Type` or `Prop`)

`UpperCamelCase`. Matches Mathlib's convention for `IsEmpty`, `IsClosed`, `Finset`, etc.

| Kind | Example |
| ---- | ------- |
| Sort/Type | `Class`, `Ordinal` |
| Prop predicate | `IsSet`, `IsEmpty`, `IsFun` |

---

### (NC-4) Functions and term-level definitions (`def` returning a value)

`lowerCamelCase`.

| Kind | Example |
| ---- | ------- |
| Constructor | `oPair`, `succ` |
| Accessor | `dom`, `img`, `fst`, `snd` |

---

### (NC-5) Axioms

Prefix `PROJ_` (replace with a short project-specific uppercase tag) + `UpperCamelCase` descriptor.
The prefix signals axiomatic (unproven) status and distinguishes axioms from theorems at a glance.

| Pattern | Example (project tag `MK`) |
| ------- | -------------------------- |
| `TAG_ShortName` | `MK_Ext`, `MK_Found`, `MK_Pair` |
| `TAG_Compound` | `MK_GlobalChoice`, `MK_CAC` |

Rules:

- Tag always uppercase, followed immediately by the descriptor (no extra underscores).
- Choose short, stable descriptors: `Ext`, `Found`, `Pair`, `Union`, `Pow`, `Inf`, `Comp`, `Repl`.
- Keep the tag consistent across the whole project.

---

### (NC-6) Exportable theorems and lemmas

Follow Mathlib4's **subject\_predicate** pattern, all `lowerCamelCase` with underscores.

```text
[subject]_[predicate]
[subject]_[predicate]_[object]
[subject]_[predicate]_of_[hypothesis]
```

Standard suffixes:

| Suffix | Meaning | Example |
| ------ | ------- | ------- |
| `_iff` | biconditional | `mem_pair_iff` |
| `_eq` | equality | `empty_eq` |
| `_of_` | follows from | `isSet_of_mem` |
| `_mem` | membership | `pair_mem` |
| `_subset` | inclusion | `inter_subset_left` |
| `_ne` | inequality | `succ_ne_empty` |
| `_unique` | uniqueness | `empty_unique` |
| `_exists` | existence | `pair_exists` |

---

### (NC-7) Private and auxiliary declarations

Use the `private` keyword. Optionally append `_aux` for intermediate steps.

```lean
private lemma foo_of_bar_aux : … := …
private def witnessFor_aux : … := …
```

- `_aux` suffix is optional but recommended when the lemma is a stepping stone within a proof.
- Never export `_aux` names.

---

### (NC-8) Notations

Document every introduced notation in REFERENCE.md §5 with: symbol, priority, scope, expansion.

Rules:

- Prefer `local notation` inside namespaces to avoid global pollution.
- Follow Mathlib Unicode conventions where a standard symbol exists (∈, ⊆, ∅, ⟨⟩).
- Custom symbols must be declared `local` unless they are the project's primary notation
  and will never conflict with Mathlib imports.
- Priority: follow Lean 4 defaults (50 for relations, 65 for arithmetic operators).

---

### (NC-9) Section names

`UpperCamelCase`, descriptive.

```lean
section Extensionality
section PairingLemmas
section FoundationConsequences
```

---

### (NC-10) Summary table

| Entity | Convention | Example |
| ------ | ---------- | ------- |
| Module (`.lean` file) | `UpperCamelCase` | `CoreAxioms.lean` |
| Namespace | `UpperCamelCase` | `ProjectName`, `ProjectName.Ordinals` |
| Type / Prop predicate | `UpperCamelCase` | `IsSet`, `IsFun` |
| Function / value def | `lowerCamelCase` | `oPair`, `dom` |
| Axiom | `TAG_ShortName` | `MK_Ext`, `ZF_Sep` |
| Exportable theorem | `subject_predicate` | `mem_pair_iff` |
| Private / auxiliary | `private` + optional `_aux` | `private lemma foo_aux` |
| Section | `UpperCamelCase` | `section Pairing` |
| Notation | `local notation` preferred | `local notation:50 …` |

---

## Compliance

Verify that REFERENCE.md, `.lean` files, and documentation files comply with all points
(0–21), export/glob rules (23, 30–33), and naming conventions (NC-1–NC-10) before
considering documentation complete and up to date.

---

## Directory Structure and Subdirectories

### (22.) Module organization by subdirectory

As the project grows, organize modules into **thematic subdirectories** inside `ProjectName/`.
Each subdirectory groups related modules and corresponds to a sub-namespace.

Example structure:

```
ProjectName/
├── Prelim.lean               # Level 0: foundations
├── _template.lean            # Template (not imported)
├── Core/
│   └── Basic.lean            # ProjectName.Core.Basic
├── Axiom/
│   ├── Extension.lean        # ProjectName.Axiom.Extension
│   └── Pairing.lean          # ProjectName.Axiom.Pairing
├── Nat/
│   ├── Basic.lean            # ProjectName.Nat.Basic
│   ├── Add.lean              # ProjectName.Nat.Add
│   └── Mul.lean              # ProjectName.Nat.Mul
└── BoolAlg/
    ├── Basic.lean             # ProjectName.BoolAlg.Basic
    └── Complete.lean          # ProjectName.BoolAlg.Complete
```

Rules:

- Subdirectory names: `UpperCamelCase`, matching the sub-namespace.
- Each subdirectory may have a `Basic.lean` for foundational definitions of that area.
- `new-module.bash` supports paths: `bash new-module.bash Nat/Add` creates `ProjectName/Nat/Add.lean`.
- `gen-root.bash` automatically scans subdirectories.
- Namespace mirrors path: `ProjectName/Nat/Add.lean` → `namespace ProjectName.Nat.Add`.

### (23.) Barrel modules (mandatory for subdirectories)

Every subdirectory containing 2 or more `.lean` modules **MUST** have a barrel file.
The barrel file:

- Sits at the same level as the directory, named `DirName.lean` (e.g., `Operations.lean` for `Operations/`).
- Imports ALL production sub-modules in the directory (excludes `test_*.lean` and `Test*.lean`).
- Contains NO definitions, theorems, or proofs — only `import` statements and an optional header comment.
- Serves as the **single import point** for the subdirectory.

```lean
-- ProjectName/Operations.lean (barrel file)
import ProjectName.Operations.Union
import ProjectName.Operations.Intersection
import ProjectName.Operations.Setminus
-- ... all production modules in Operations/
```

The root barrel file (`ProjectName.lean`) **prefers barrel imports** over individual
sub-modules when a barrel exists:

```lean
-- ProjectName.lean (root barrel)
import ProjectName.CList          -- barrel for CList/
import ProjectName.Operations     -- barrel for Operations/
import ProjectName.Axioms         -- barrel for Axioms/
import ProjectName.HFSets         -- top-level module (no barrel needed)
import ProjectName.Notation       -- top-level module
```

`gen-root.bash` detects barrel files and emits the barrel import instead of listing
each sub-module individually.

---

## Export/Glob Architecture

### (30.) Export blocks in leaf modules

Every production module (not barrels, not test files) **MUST** end with an `export` block
that lists all public (non-private) definitions, theorems, lemmas, and instances from the
module's namespace. This makes declarations available to importers without requiring
`open Namespace`.

**Pattern:**

```lean
namespace MyNamespace

def myDef : Type := ...

theorem myTheorem : ... := ...

end MyNamespace

-- Export: all public declarations from this module
export MyNamespace (myDef myTheorem)
```

**Rules:**

1. The `export` statement goes AFTER `end namespace`, at the top level of the file.
2. List ALL non-private `def`, `theorem`, `lemma`, `instance` names.
3. Do NOT export `private` declarations, `_aux` helpers, or intermediate lemmas prefixed with `private`.
4. Keep the export list **sorted alphabetically** within each namespace.
5. If a module contributes to multiple namespaces, use one `export` per namespace.
6. `notation`, `macro`, `syntax` are NOT listed in `export` — they propagate automatically on `import`.

**Effect:** After `import ProjectName.Axioms.Union`, downstream code can write
`mem_union` directly instead of `MyNamespace.mem_union`.

### (31.) Export block maintenance

- **Adding** a new public declaration requires adding it to the `export` block.
- **Renaming** a declaration requires updating the `export` block.
- **Deleting** a public declaration requires removing it from the `export` block.
- When **projecting** a module to REFERENCE.md (§14), verify the export list matches.
- The export list is the **canonical list** of a module's public API.

### (32.) Barrel files and exports

Barrel files (`DirName.lean`) do **not** add their own `export` blocks — the leaf modules
handle their own exports. The barrel file's sole job is aggregation via `import`.

However, a barrel file **may** include a top-level comment cataloguing the public API:

```lean
-- ProjectName/Operations.lean
-- Public API: union, inter, setminus, pair, powerset, symDiff, orderedPair,
--             sep, sUnion, dom, range, comp, image, ...
import ProjectName.Operations.Union
import ProjectName.Operations.Intersection
-- ...
```

### (33.) Template compliance

The `_template.lean` file must reflect the export pattern. Section 4 ("Exports") in the
template shows the `export` block after `end namespace`. New modules created by
`new-module.bash` inherit this structure.

---

## Annotation System for REFERENCE.md

### (24.) Module-level annotations

Each module entry in REFERENCE.md §3 may include the following metadata:

```markdown
**@axiom_system**: `ZFC` | `Peano` | `BoolAlg` | `none`
**@importance**: `foundational` | `high` | `medium` | `low`
```

- `@axiom_system`: Which formal system the module primarily belongs to.
- `@importance`: How critical the module is to the project's dependency chain.

### (25.) Theorem-level annotations

Individual theorems or definitions in REFERENCE.md may be annotated:

```markdown
**@importance**: `high` | `medium` | `low`
```

- `high`: Used by 3+ other modules, or is a key axiom/definition.
- `medium`: Used by 1–2 other modules.
- `low`: Internal utility, only used within its own module.

Purpose: Helps AI assistants prioritize which theorems to load for context.

---

## Cross-Reference Files

### (26.) NAMING-CONVENTIONS.md

A standalone file with the full naming dictionary, 12 formation rules,
migration tables, and detailed examples. Canonical reference for renaming.
Updated whenever naming conventions evolve.

### (27.) NEXT-STEPS.md

A living document tracking planned development phases. Each phase includes:

- Name and objective
- List of modules to create/modify
- Dependencies on prior phases
- Estimated complexity (simple/medium/complex)

### (28.) THOUGHTS.md

An informal design journal for recording ideas, alternatives considered,
open questions, and future directions. Not normative — purely exploratory.
Useful for AI context on "why" decisions were made.

### (29.) Commands

A set of high-level instructions that trigger a predefined multi-step workflow.
Commands are addressed to the AI assistant and named using a short verb phrase.
Each command is defined in this section (§29) with its exact steps.

> To invoke a command, write its name in the chat, e.g.: **`actualiza doc`**

---

## Commands

### `actualiza doc`

**Purpose**: Full documentation pass — synchronize all living documentation files
with the current state of the codebase after a development session.

**Steps** (execute in order):

1. **Run the build** and record the result:
   - `lake build` — note the number of jobs, errors, sorry count, and any warnings.

2. **Read the current state** of these files (to diff against later):
   - `NEXT-STEPS.md` — current sorry table and phase status.
   - `CHANGELOG.md` — latest entry date.
   - `CURRENT-STATUS-PROJECT.md` — build snapshot and module status table.
   - `AI-GUIDE.md` — directory structure block inside § 22.

3. **Identify what changed** since the last documentation update:
   - Which sorries were closed (compare `check-sorry.bash` output vs NEXT-STEPS.md table).
   - Which new theorems, definitions, or modules were added.
   - Which modules changed status (🔄 → 🔶 → ✅ → 🧊).
   - Current build numbers (jobs, errors, sorry count).

4. **Update `CHANGELOG.md`**:
   - Add a new `### Added (YYYY-MM-DD)` block under `## [Unreleased]`.
   - List every closed sorry, new declaration, and structural change.
   - Include build stats: jobs, errors, sorry count, warnings.
   - Follow the existing entry format (bullet points grouped by module).

5. **Update `NEXT-STEPS.md`**:
   - Update `**Last updated:**` timestamp.
   - Update § 1 "Estado Actual" snapshot: build status, error count, sorry count.
   - Update § 1.1 "Completado recientemente": move closed items here.
   - Update § 1.2 "Sorries vigentes": remove closed sorries; update line numbers for open ones.
   - Update priority sections if the next objective changed.

6. **Update `CURRENT-STATUS-PROJECT.md`**:
   - Update `**Last updated:**` timestamp.
   - Update build snapshot block: date, jobs, errors, sorry count.
   - Update the module status table: mark newly completed modules ✅ or 🧊.

7. **Update `AI-GUIDE.md` § 22 directory structure block** (if modules were added/removed):
   - Update the tree listing.
   - Update the sorry count annotations (e.g., `[ 3 sorry ]` → `[ 2 sorry ]`).
   - Update the "Current structure" date.

8. **Update `REFERENCE.md`** for every `.lean` file modified in the session:
   - Project new public declarations following rules §1–§14.
   - Update module status codes.
   - Add timestamps.

9. **Verify consistency**:
   - Sorry count in NEXT-STEPS.md = sorry count in CHANGELOG.md = `check-sorry.bash` output.
   - All new public declarations appear in their module's `export` block.
   - REFERENCE.md timestamps are newer than the `.lean` file timestamps for modified modules.

10. **Report a brief summary** to the user:
    - Sorries closed this session.
    - New declarations added.
    - Files updated.
    - Remaining sorries and their location.

**Files touched by this command** (in order of update):
`CHANGELOG.md` → `NEXT-STEPS.md` → `CURRENT-STATUS-PROJECT.md` → `AI-GUIDE.md` → `REFERENCE.md`

**Note**: Steps 4–8 may be done in parallel when changes are independent across modules.
Never overwrite content from prior sessions — only prepend new entries or update
clearly demarcated snapshot blocks.

---

### `dame situación`

**Purpose**: Instant read-only status report. No files are modified. Gives a complete,
structured picture of the project's current state in a single response.

**Steps** (all read-only, execute in parallel where possible):

1. **Run `check-sorry.bash`** — get the current sorry count and file locations.
2. **Run `lake build`** — confirm 0 errors; record job count and warning count.
3. **Read `NEXT-STEPS.md` § 1.2** — get the canonical sorry table (names + lines).
4. **Read `CURRENT-STATUS-PROJECT.md`** — get the module status table.
5. **Read `CHANGELOG.md`** — get the most recent entry to know what changed last.

**Output format** (always in this order):

```
## Situación — YYYY-MM-DD

### Build
- Jobs: N  |  Errores: 0  |  Sorries activos: N  |  Warnings: N

### Sorries vigentes
| Archivo | Línea | Teorema | Estrategia |
|---------|-------|---------|------------|
| ...     | ...   | ...     | ...        |

### Último cambio documentado
- Fecha: YYYY-MM-DD
- Resumen: <primera línea del último bloque CHANGELOG>

### Módulos con estado incompleto
| Módulo | Estado | Bloqueado por |
|--------|--------|---------------|
| ...    | ...    | ...           |

### Próximo objetivo
<Extraído de NEXT-STEPS.md § 2>
```

**Files read** (none modified):
`check-sorry.bash` output → `NEXT-STEPS.md` → `CURRENT-STATUS-PROJECT.md` → `CHANGELOG.md`

---

### `proyecta`

**Purpose**: Extract all new or modified non-private definitions, notations, axioms, and theorems from the currently locked or modified `.lean` files and project them into `REFERENCE.md`.

**Steps** (execute in order):

1. **Identify modified modules**: Identify all `.lean` files that have been modified during the current session (or that the user explicitly indicates).
2. **Extract public symbols**: For each modified file, extract its full `export` block.
3. **Draft the projection**: Translate each exported symbol into its mathematical notation and Lean 4 signature as described in rules §4 to §7. Note its dependencies.
4. **Update `REFERENCE.md`**: Locate the module's section in `REFERENCE.md`. Insert the newly extracted symbols in the correct subsections. Update the module's modification timestamp in `REFERENCE.md`.
5. **Verify**: Ensure every symbol in the `export` block now appears in `REFERENCE.md` and no private symbols are exposed.

**Files touched by this command**: `REFERENCE.md`

---

### `guarda y sube`

**Purpose**: Automate the standard workflow for safely saving work, committing it, pushing it to the remote repository, and resetting the locks for the next task.

**Steps** (execute in order):

1. **Verify build**: Ensure the project compiles by running `lake build`.
2. **Unlock files**: Run `bash git-lock.bash unlock <file>` for all currently locked `.lean` files.
3. **Stage changes**: Run `git add .` to stage all modified files (including documentation, scripts, and code).
4. **Commit**: Run `git commit -m "<Summary of changes>"` using the standard commit format based on the session's work. Propose the commit message to the user or generate it autonomously based on the changes if confident.
5. **Push**: Run `git push` to upload the changes to the current branch.
6. **Relock files**: Run `bash git-lock.bash lock <file>` on the active files you were working on to resume the session safely.

**Files touched by this command**: git state, `locked_files.txt` (via `git-lock.bash`)
