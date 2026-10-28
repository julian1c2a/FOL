#!/bin/bash
# guarda_y_bloquea.bash — commitea un fichero BLOQUEADO sin tocar la lista, y lo vuelve a bloquear (T52, ADR-201).
#
# Uso, tras desbloquearlo y editarlo (`bash git-lock.bash unlock <fichero>`):
#   bash guarda_y_bloquea.bash <fichero> "<mensaje del commit>"
#
# Hace el protocolo de los bloqueados: comprueba que <fichero> está bloqueado en la lista COMMITEADA y desbloqueado en
# el árbol; añade SÓLO <fichero> al índice (avisa de lo que ya hubiera en él, que entra en el commit); commitea con
# <mensaje>; lo vuelve a bloquear; y restaura `locked_files.txt` tal como estaba commiteado (con su orden). No hace
# push: `master` está protegido, y se sube por una rama `ci/…` (AI-GUIDE). Un CONGELADO, no: pide un thaw del
# propietario, y el gancho de `git-lock.bash` lo rechazaría.
# ✏️ 2026-10-28 (T52, ADR-201): hasta hoy desbloqueaba la lista entera, hacía `git add .` (todo el árbol), commit y push
# directo a la rama actual, sin ningún control; en RPP, además, no hay nada bloqueado.

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

if [ $# -lt 2 ]; then
  echo "Uso: bash guarda_y_bloquea.bash <fichero> \"<mensaje del commit>\""
  exit 1
fi
FILE="$1"
MSG="$2"

if [ -f frozen_files.txt ] && tr -d '\r' < frozen_files.txt | grep -qxF "$FILE"; then
  echo "⛔ $FILE está CONGELADO: sólo con un thaw del propietario."
  exit 1
fi
if ! git show HEAD:locked_files.txt 2>/dev/null | tr -d '\r' | grep -qxF "$FILE"; then
  echo "⛔ $FILE no está bloqueado en la lista commiteada: para un fichero libre, git add y git commit sin más."
  exit 1
fi
if tr -d '\r' < locked_files.txt | grep -qxF "$FILE"; then
  echo "⛔ $FILE sigue bloqueado en el árbol: desbloquéalo antes de editarlo (bash git-lock.bash unlock $FILE)."
  exit 1
fi

YA=$(git diff --cached --name-only | grep -vxF "$FILE" | grep -vxF locked_files.txt || true)
if [ -n "$YA" ]; then
  echo "⚠️  el índice ya tiene otros cambios, y entran en el commit:"
  printf '%s\n' "$YA" | sed 's/^/      /'
fi
# la lista del árbol (sin <fichero>) no entra en el commit
git reset -q -- locked_files.txt
git add -- "$FILE" || exit 1
git commit -m "$MSG" || exit 1
bash git-lock.bash lock "$FILE" || exit 1
git checkout -- locked_files.txt
if git diff --quiet -- locked_files.txt; then
  echo "✅ commiteado y vuelto a bloquear: $FILE (la lista, la commiteada)."
else
  echo "⚠️  locked_files.txt no ha quedado como la commiteada: revísalo."
  exit 1
fi
