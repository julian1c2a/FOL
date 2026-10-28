#!/bin/bash
# check-congelados.bash — ningún cambio toca un módulo CONGELADO sin su thaw (R3-4-01 de la ronda 3, ADR-212 de RPP).
#
# El gancho de `git-lock.bash` lo impide en local, si está instalado y si lee bien las listas (hasta el 2026-10-28 no
# las leía: con `core.autocrlf` estaban en CRLF y no casaba ninguna entrada). Esto lo comprueba en la CI, contra la
# base: un fichero que cambia entre BASE y HEAD y está en el `frozen_files.txt` de BASE tiene que haber salido de la
# lista en ALGÚN commit de BASE..HEAD (el thaw, que autoriza el propietario y queda en la historia); si no, ROJO.
#
# Uso: bash check-congelados.bash [BASE]      (por defecto, B_BASE_REF; si está vacío, refs/remotes/origin/master)
# ⭐ Con AUTOTEST: una base con dos congelados, A y B, y tres cambios, A, B y C, donde B sale de la lista en un commit
#    intermedio: tiene que salir exactamente A. Si no, el control no mide, y lo dice.
export PATH="/usr/bin:$PATH"
set -uo pipefail
cd "$(dirname "$0")" || exit 2

lista() { tr -d '\r' | grep -v '^[[:space:]]*#' | sed '/^[[:space:]]*$/d'; }

# revisa CONG_BASE CAMBIADOS SIGUE_EN_TODOS → los congelados que cambian sin thaw. SIGUE_EN_TODOS f responde 0 si f
# sigue en la lista de TODOS los commits de BASE..HEAD (si salió en alguno, hubo thaw).
revisa() {
  local base="$1" cambiados="$2" sigue="$3" f
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    printf '%s\n' "$base" | grep -Fqx -- "$f" || continue
    "$sigue" "$f" && printf '%s\n' "$f"
  done <<< "$cambiados"
}
auto_sigue() { [ "$1" != "B" ]; }   # en el autotest, B sale de la lista en un commit intermedio
AUTO=$(revisa "$(printf 'A\nB\n')" "$(printf 'A\nB\nC\n')" auto_sigue | tr '\n' ' ')
if [ "$AUTO" != "A " ]; then
  echo "❌ NO PUDE MEDIR: el autotest da «$AUTO» y debía dar «A »."
  exit 2
fi

BASE="${1:-${B_BASE_REF:-}}"
[ -n "$BASE" ] || BASE=refs/remotes/origin/master
if ! git rev-parse -q --verify "$BASE^{commit}" > /dev/null; then
  echo "❌ NO PUDE MEDIR: no encuentro la base «$BASE» (¿un clon superficial?)."
  exit 2
fi
if ! git cat-file -e "$BASE:frozen_files.txt" 2> /dev/null; then
  echo "❌ NO PUDE MEDIR: la base $(git rev-parse --short "$BASE") no tiene frozen_files.txt."
  exit 2
fi
CONG_BASE=$(git show "$BASE:frozen_files.txt" | lista)
CAMBIADOS=$(git diff --name-only --no-renames "$BASE" HEAD)
COMMITS=$(git rev-list "$BASE..HEAD")
sigue_en_todos() {
  local c
  for c in $COMMITS; do
    git cat-file -e "$c:frozen_files.txt" 2> /dev/null || return 1
    git show "$c:frozen_files.txt" | lista | grep -Fqx -- "$1" || return 1
  done
  return 0
}
MAL=$(revisa "$CONG_BASE" "$CAMBIADOS" sigue_en_todos)
NB=$(printf '%s\n' "$CONG_BASE" | grep -c .)
NC=$(printf '%s\n' "$CAMBIADOS" | grep -c .)
if [ -n "$MAL" ]; then
  echo "❌ cambian módulos CONGELADOS sin thaw (siguen en frozen_files.txt en todos los commits desde la base):"
  printf '%s\n' "$MAL" | sed 's/^/      /'
  exit 1
fi
echo "✓ ningún congelado cambia sin su thaw ($NB congelados en la base $(git rev-parse --short "$BASE"); $NC ficheros cambiados; autotest: «A»)"
