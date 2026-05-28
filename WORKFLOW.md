# Development Workflow

**Author**: Your Name
*Last updated: 2026-04-20*

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

```bash
# Creates MyProject/ModuleName.lean from _template.lean
# and adds the import to MyProject.lean
make new NAME=ModuleName

# For nested modules:
make new NAME=Algebra/Ring
```

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
# Try a new version — automatically builds and commits on success
bash update-toolchain.bash v4.29.0

# On failure it restores the previous version automatically
```

---

## Part 5: Regenerating the Root Module

If you add/remove modules manually without using `new-module.bash`:

```bash
bash gen-root.bash
```

This scans `MyProject/` for all `.lean` files (excluding `_template.lean`) and rewrites `MyProject.lean` with the full import list.

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
make new NAME=Module                 # create new module
make build                           # compile
make sorry                           # check for sorry
make status                          # lock + sorry status
bash gen-root.bash                   # regenerate root imports
bash update-toolchain.bash vX.Y.Z    # update Lean version
```
n.bash vX.Y.Z    # update Lean version
```
