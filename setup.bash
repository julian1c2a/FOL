#!/bin/bash
# setup.bash — Initialize a new project from this template
#
# Usage:
#   bash setup.bash ProjectName "Author Name"
#   bash setup.bash ProjectName "Author Name" "github-username"
#
# What it does:
#   1. Renames ProjectName/ directory and ProjectName.lean
#   2. Replaces all "ProjectName" occurrences in all files
#   3. Replaces "Your Name" with the provided author name
#   4. Replaces github.com/your-username with actual username (optional)
#   5. Updates copyright year to current year
#   6. Makes an initial commit with the new project name

set -e

# ── Arguments ────────────────────────────────────────────────────────────────

if [ $# -lt 2 ]; then
    echo "Usage: bash setup.bash ProjectName \"Author Name\" [github-username]"
    echo ""
    echo "Example:"
    echo "  bash setup.bash IntegerTheory \"Julián Calderón Almendros\" julian1c2a"
    exit 1
fi

NEW_NAME="$1"
AUTHOR="$2"
GH_USER="${3:-your-username}"
YEAR=$(date +%Y)
OLD_NAME="MyProject"

# Validate: project name must be a valid Lean identifier
if ! echo "$NEW_NAME" | grep -qE '^[A-Za-z][A-Za-z0-9_]*$'; then
    echo "Error: '$NEW_NAME' is not a valid Lean identifier."
    echo "  Use only letters, digits, underscores. Must start with a letter."
    exit 1
fi

if [ "$NEW_NAME" = "$OLD_NAME" ]; then
    echo "Error: New name must differ from 'ProjectName'."
    exit 1
fi

echo "Setting up project: $NEW_NAME"
echo "Author:             $AUTHOR"
echo "GitHub user:        $GH_USER"
echo "Year:               $YEAR"
echo ""

# ── Step 1: Rename directory and root file ────────────────────────────────────

if [ -d "$OLD_NAME" ]; then
    mv "$OLD_NAME" "$NEW_NAME"
    echo "✅ Renamed directory: $OLD_NAME/ → $NEW_NAME/"
fi

if [ -f "${OLD_NAME}.lean" ]; then
    mv "${OLD_NAME}.lean" "${NEW_NAME}.lean"
    echo "✅ Renamed file: ${OLD_NAME}.lean → ${NEW_NAME}.lean"
fi

# ── Step 2: Replace text in all files ────────────────────────────────────────

# Files to process: all text files excluding .git/, .lake/, binaries
TEXT_FILES=$(find . \
    ! -path './.git/*' \
    ! -path './.lake/*' \
    ! -name '*.olean' \
    ! -name '*.ilean' \
    ! -name '*.trace' \
    -type f | sort)

echo ""
echo "Replacing text in files..."

for FILE in $TEXT_FILES; do
    # Skip binary files
    if ! file "$FILE" | grep -qE 'text|empty'; then
        continue
    fi

    CHANGED=false

    # Replace ProjectName → NewName
    if grep -qF "$OLD_NAME" "$FILE" 2>/dev/null; then
        sed -i "s/${OLD_NAME}/${NEW_NAME}/g" "$FILE"
        CHANGED=true
    fi

    # Replace "Your Name" → Author
    if grep -qF "Your Name" "$FILE" 2>/dev/null; then
        sed -i "s/Your Name/${AUTHOR}/g" "$FILE"
        CHANGED=true
    fi

    # Replace "your-username" → GH_USER
    if grep -qF "your-username" "$FILE" 2>/dev/null; then
        sed -i "s/your-username/${GH_USER}/g" "$FILE"
        CHANGED=true
    fi

    # Replace copyright year 2025 → current year (only in .lean and .md files)
    if [[ "$FILE" == *.lean || "$FILE" == *.md ]] && grep -qF "Copyright (c) 2025" "$FILE" 2>/dev/null; then
        sed -i "s/Copyright (c) 2025/Copyright (c) ${YEAR}/g" "$FILE"
        CHANGED=true
    fi

    # Replace "2025-01-01 00:00" timestamps → today
    TODAY=$(date +%Y-%m-%d)
    if grep -qF "2025-01-01 00:00" "$FILE" 2>/dev/null; then
        sed -i "s/2025-01-01 00:00/${TODAY} 00:00/g" "$FILE"
        CHANGED=true
    fi

    if [ "$CHANGED" = true ]; then
        echo "   ✏️  $FILE"
    fi
done

# ── Step 3: Update git config ─────────────────────────────────────────────────

echo ""
git config user.name "$AUTHOR"
echo "✅ git user.name set to: $AUTHOR"

# ── Step 4: Commit the setup ──────────────────────────────────────────────────

echo ""
echo "Creating setup commit..."
git add -A
git commit -m "chore: initialize project as '${NEW_NAME}' by ${AUTHOR}

Renamed from lean4-project-template:
- ProjectName → ${NEW_NAME}
- Author: ${AUTHOR}
- GitHub: ${GH_USER}

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>"

echo ""
echo "✅ Project '${NEW_NAME}' is ready."
echo ""
echo "Next steps:"
echo "  1. Edit README.md — fill in the project description"
echo "  2. Edit lakefile.lean — add dependencies if needed"
echo "  3. Run: bash git-lock.bash init   (re-install hook for this session)"
echo "  4. Run: make new NAME=FirstModule"
echo "  5. Push: git remote add origin https://github.com/${GH_USER}/${NEW_NAME}.git"
echo "           git push -u origin master"
