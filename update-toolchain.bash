#!/bin/bash
# update-toolchain.bash — Update lean-toolchain to a new version and verify build
#
# Usage:
#   bash update-toolchain.bash v4.29.0
#   bash update-toolchain.bash v4.29.0-rc1
#
# On success: commits the updated lean-toolchain file.
# On failure: restores the previous version.

set -e

if [ $# -eq 0 ]; then
    echo "Usage: bash update-toolchain.bash v4.28.0"
    echo "Current toolchain: $(cat lean-toolchain)"
    exit 1
fi

NEW_VERSION="leanprover/lean4:$1"
OLD_VERSION=$(cat lean-toolchain)

echo "Updating toolchain: $OLD_VERSION → $NEW_VERSION"
echo "$NEW_VERSION" > lean-toolchain

echo "Running lake build..."
if lake build; then
    echo ""
    echo "✅ Build passed with $NEW_VERSION"
    git add lean-toolchain
    git commit -m "chore: update lean toolchain to $1"
    echo "✅ Committed lean-toolchain update."
else
    echo ""
    echo "❌ Build failed. Restoring previous toolchain: $OLD_VERSION"
    echo "$OLD_VERSION" > lean-toolchain
    exit 1
fi
