# Development Workflow

**Author**: Your Name
*Last updated: 2026-10-20* — Part 4: `update-toolchain.bash`, retired here (T42, ADR-176 of RPP). Before: 2026-04-20.

Complete guide for using this template — from initial setup to active development.

---

## Part 1: Starting a New Project

### Step 1 — Clone the template

```bash
git clone https://github.com/julian1c2a/lean4-project-template MyProject
cd MyProject
```

### Step 2 — Run setup

```bash
bash setup.bash MyProject "Your Full Name" your-github-username
```

This single command:

- Renames `ProjectName/` → `MyProject/` and `ProjectName.lean` → `MyProject.lean`
- Replaces all occurrences of `ProjectName`, `Your Name`, `julian1c2a` in every file
- Updates copyright year to the current year
- Commits the result

### Step 3 — Install the git hook

```bash
bash git-lock.bash init
```

This installs the pre-commit hook that:

- Blocks commits that touch locked `.lean` files
- Warns about `sorry` statements in staged files

> **Note**: Run this once per machine/clone. The hook lives in `.git/hooks/` which is not versioned.

> **Do NOT run `git init` or `lake init`.**
>
> - `git init` is already done by `git clone` — running it again would reinitialize the repo and break the commit history.
> - `lake init` would overwrite `lakefile.lean` with a bare default, losing the template configuration (`autoImplicit=false`, `globs`, commented dependencies).
>
> If you activate a dependency in `lakefile.lean`, run `lake update` (not `lake init`) to fetch it:
>
> ```bash
> # After uncommenting a require block in lakefile.lean:
> lake update   # downloads and registers the external package
> lake build    # verify it compiles
> ```

### Step 4 — Create the GitHub repository and push

```bash
# Option A: with gh CLI
gh repo create MyProject --public --source=. --push

# Option B: manually
# Create repo on github.com, then:
git remote add origin https://github.com/julian1c2a/MyProject.git
git push -u origin master
```

### Step 5 — Customize

Edit these files before starting development:

| File | What to update |
|------|----------------|
| `README.md` | Project description, module table |
| `lakefile.lean` | Add external dependencies; uncomment `globs` if desired |
| `DECISIONS.md` | Add project-specific design decisions |
| `NAMING-CONVENTIONS.md` | Customize domain-specific naming rules and examples |
| `NEXT-STEPS.md` | Define initial development phases |
| `THOUGHTS.md` | Record design philosophy and initial decisions |
| `LICENSE` | Verify author name and year |

---

## Part 2: Daily Development Workflow

### Starting a work session

```bash
# 1. Check which files are unlocked
bash git-lock.bash list

# If more than one file is unlocked from a previous session, lock all:
# bash git-lock.bash lock MyProject/SomeModule.lean

# 2. Check current sorry status
make sorry
```

### Creating a new module

Create `FOL/ModuleName.lean` (or `FOL/Topic/ModuleName.lean`, or under `TheoryFramework/`) by hand and import it
from its barrel (`FOL.lean`, `FOL/Core.lean` or `TheoryFramework.lean`), which is curated by hand. The lakefile's
`globs := #[.andSubmodules …]` compile every file in both directories, and `[L]` of `check-doc-sync.bash` fails if a
file is not in the import closure of the roots (`cierre-imports.bash`) or not in git.
(2026-10-18, T15 and ADR-163 of RPP: `make new` / `new-module.bash`, which needed a missing `_template.lean`, and
`gen-root.bash`, PROHIBITED since A-7, were retired.)

Then edit the generated file. When done:

```bash
bash git-lock.bash lock MyProject/ModuleName.lean
```

### Editing an existing module

```bash
# 1. Unlock the file
bash git-lock.bash unlock MyProject/ModuleName.lean

# 2. Edit...

# 3. Lock when done
bash git-lock.bash lock MyProject/ModuleName.lean
```

### The one-file rule

> **At most one `.lean` file may be unlocked at any time.**

If you need to switch to a different file mid-session:

```bash
bash git-lock.bash lock MyProject/CurrentModule.lean
bash git-lock.bash unlock MyProject/NextModule.lean
```

### Building

```bash
make build          # compile full project
make rebuild        # clean + compile
```

### Checking proofs

```bash
make sorry          # list all sorry in project
make status         # lock status + sorry count
```

---

## Part 3: Commit Protocol

### Before committing

```bash
# 1. Verify only the intended files are unlocked
bash git-lock.bash list

# 2. Check for sorry
make sorry

# 3. Update REFERENCE.md
#    Project modified .lean files → REFERENCE.md
#    (See AI-GUIDE.md §12)
```

### Committing

```bash
# Stage specific files (avoid git add -A to prevent accidents)
git add MyProject/ModuleName.lean REFERENCE.md CHANGELOG.md

git commit -m "feat: add ModuleName with N definitions and M theorems"
```

### After committing — lock all modified .lean files

```bash
bash git-lock.bash lock MyProject/ModuleName.lean

# Commit the updated locked_files.txt
git add locked_files.txt
git commit -m "chore: lock ModuleName after completion"
```

### Ending a session

```bash
# Lock ALL modified .lean files
bash git-lock.bash list   # verify none remain unlocked

git push origin master
```

---

## Part 4: Updating the Lean Toolchain

```bash
# ⛔ Retired here (2026-10-20, T42, ADR-176 of RPP): it built FOL from this directory (M-3) and committed on its own.
# The pair (RPP, FOL) is probed together, from the root of ROBINSON_PlusPlus, in separate worktrees, never committing:
cd ../ROBINSON_PlusPlus && bash update-toolchain.bash [vX.Y.Z]

# A bump, if decided, is done by hand with an ADR, in both repos (M-12: FOL first).
```

---

## Part 5: The Root Module

The barrels are curated by hand. (2026-10-18, T15 and ADR-163 of RPP: `gen-root.bash`, which rewrote `MyProject.lean`
with the full import list and erased its comments, was retired; it had been PROHIBITED here since A-7.) `[L]` of
`check-doc-sync.bash` says whether every file is reachable from the roots.

---

## Part 6: AI Assistant Sessions (Claude Code / Aider)

When starting a session with an AI assistant:

1. **Point to AI-GUIDE.md** — the AI reads this first
2. **Point to REFERENCE.md** — the AI uses this instead of loading all `.lean` files
3. **Remind the one-file rule** — unlock only the target module
4. **At session end** — AI locks all modified files and updates `REFERENCE.md`, `CHANGELOG.md`

Key commands to tell the AI:

```
bash git-lock.bash list             # what is currently unlocked?
bash git-lock.bash unlock File.lean # unlock for editing
bash git-lock.bash lock File.lean   # lock after completion
make sorry                          # any sorry left?
```

---

## Quick Reference

```bash
bash setup.bash Name "Author" user   # initialize new project
bash git-lock.bash init              # install git hook (once per clone)
bash git-lock.bash list              # show locked files
bash git-lock.bash lock File.lean    # lock a file
bash git-lock.bash unlock File.lean  # unlock a file
make build                           # compile
make sorry                           # check for sorry
make status                          # lock + sorry status
# toolchain: cd ../ROBINSON_PlusPlus && bash update-toolchain.bash [vX.Y.Z]   (probe, no commit)
```
n.bash vX.Y.Z    # update Lean version
```
