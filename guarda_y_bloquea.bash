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

# ⭐ 2026-11-04 (R3-5-14 de la ronda 3, ADR-255 de RPP): el AUTOTEST. «Probado con el fallo puesto» no tenía artefacto:
# ahora, en un repositorio de prueba (una copia de este script, un git-lock.bash mínimo, un bloqueado B y un congelado
# C), tiene que rechazar C, rechazar B con C ya en el índice, y commitear B y volver a bloquearlo sin él. En la CI.
if [ "${1:-}" = "--autotest" ]; then
  T=$(mktemp -d)
  trap 'rm -rf "$T"' EXIT
  cp "$0" "$T/guarda_y_bloquea.bash"
  printf '%s\n' '#!/bin/bash' '[ "$1" = lock ] && printf "%s\n" "$2" >> locked_files.txt' > "$T/git-lock.bash"
  ( cd "$T" || exit 2
    git init -q . && git config user.name autotest && git config user.email autotest@example.invalid
    git config core.hooksPath .sin-ganchos && git config core.autocrlf false
    printf 'C.txt\n' > frozen_files.txt; printf 'B.txt\n' > locked_files.txt; echo b > B.txt; echo c > C.txt
    git add . && git commit -qm base
    : > locked_files.txt; echo b2 > B.txt; echo c2 > C.txt
    F=0
    ANTES=$(git rev-parse HEAD)
    bash guarda_y_bloquea.bash C.txt "m" > salida1.txt 2>&1 && { echo "  ✗ commiteó el congelado C"; F=1; }
    git add C.txt
    bash guarda_y_bloquea.bash B.txt "m" > salida2.txt 2>&1 && { echo "  ✗ commiteó con el congelado C en el índice"; F=1; }
    grep -q CONGELADO salida2.txt || { echo "  ✗ no dijo por qué rechazó B con C en el índice"; F=1; }
    [ "$(git rev-parse HEAD)" = "$ANTES" ] || { echo "  ✗ HEAD se movió con un rechazo"; F=1; }
    git reset -q -- C.txt
    bash guarda_y_bloquea.bash B.txt "m" > salida3.txt 2>&1 || { echo "  ✗ no commiteó B, que sí podía:"; cat salida3.txt; F=1; }
    [ "$(git diff --name-only HEAD~1 HEAD 2>/dev/null)" = "B.txt" ] || { echo "  ✗ el commit no es sólo B.txt"; F=1; }
    tr -d '\r' < locked_files.txt | grep -qxF B.txt || { echo "  ✗ B no quedó bloqueado"; F=1; }
    exit $F )
  if [ $? = 0 ]; then
    echo "✅ autotest de guarda_y_bloquea.bash: rechaza el congelado, también si ya está en el índice, y commitea el bloqueado."
    exit 0
  fi
  echo "❌ autotest de guarda_y_bloquea.bash."
  exit 1
fi

if [ $# -lt 2 ]; then
  echo "Uso: bash guarda_y_bloquea.bash <fichero> \"<mensaje del commit>\""
  exit 1
fi
FILE="$1"
MSG="$2"

# los congelados: los de la lista commiteada y los de la del árbol
CONGELADOS=$( { git show HEAD:frozen_files.txt 2>/dev/null; [ -f frozen_files.txt ] && cat frozen_files.txt; } \
  | tr -d '\r' | grep . | sort -u)
if printf '%s\n' "$CONGELADOS" | grep -qxF "$FILE"; then
  echo "⛔ $FILE está CONGELADO: sólo con un thaw del propietario."
  exit 1
fi
# ✏️ 2026-11-04 (R3-3-09 de la ronda 3, ADR-255 de RPP): y ninguno en el ÍNDICE. Sólo miraba el fichero recibido, y un
# congelado ya añadido entraba en el commit (lo pararía el gancho de git-lock.bash, si está activo en el clon)
EN_INDICE=$(git diff --cached --name-only | grep -xF -f <(printf '%s\n' "$CONGELADOS" | grep . ; echo '//nada//') || true)
if [ -n "$EN_INDICE" ]; then
  echo "⛔ el índice ya tiene un CONGELADO, que entraría en el commit: $(printf '%s ' $EN_INDICE)(git reset -- <fichero>)."
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
