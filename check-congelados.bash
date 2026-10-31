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
# ✏️ 2026-10-31 (T14, ADR-234 de RPP): y (b), cada THAW de BASE..HEAD (un commit que saca una entrada de
#    frozen_files.txt) cita en su mensaje el ADR de RPP que lo autoriza, «ADR-NNN de RPP» (THAW_RE, la misma que
#    .githooks/commit-msg: check-gancho.bash lo comprueba). Que ese ADR exista y recoja la decisión del propietario lo
#    comprueba la CI de RPP (scripts/thaws-fol.bash), que tiene DECISIONS.md. Con su autotest de cuatro mensajes.
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

# (b) el mensaje de un thaw cita su ADR de RPP. ⚠️ Sin tubería a `grep -q` del texto del commit: con pipefail, un
# productor que muere de SIGPIPE daría FALSO (la 23.ª causa de los controles que no comprueban nada).
THAW_RE='ADR(-|‑)[0-9]+(( y |, )ADR(-|‑)[0-9]+)* de RPP'
cita_adr() { local t; t=$(grep -v '^#' <<< "$1"); grep -qE "$THAW_RE" <<< "$t"; }
AUTO_B=""
for m in "Thaw autorizado de siete congelados (ADR-227 y ADR-229 de RPP): los 19 nombres" \
         "re-freeze de los siete descongelados" \
         "SequentSound0: thaw autorizado, las tres localizaciones del WKL rectificadas (D2)" \
         "Thaw autorizado (ADR‑116 de RPP)"; do
  if cita_adr "$m"; then AUTO_B="${AUTO_B}s"; else AUTO_B="${AUTO_B}n"; fi
done
if [ "$AUTO_B" != "snns" ]; then
  echo "❌ NO PUDE MEDIR (b): el autotest de los mensajes da «$AUTO_B» y debía dar «snns»."
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
# (b) los thaws de BASE..HEAD, con su ADR de RPP en el mensaje
THAWS=0
SIN_ADR=""
for c in $COMMITS; do
  git cat-file -e "$c^" 2> /dev/null || continue
  QUITA=$(git diff --no-renames --unified=0 "$c^" "$c" -- frozen_files.txt | tr -d '\r' | grep '^-[^-]' || true)
  [ -n "$QUITA" ] || continue
  THAWS=$((THAWS + 1))
  if ! cita_adr "$(git log -1 --format=%B "$c")"; then
    SIN_ADR="$SIN_ADR$(git log -1 --format='%h %s' "$c" | cut -c1-110)"$'\n'
  fi
done
FALLO=0
if [ -n "$MAL" ]; then
  echo "❌ cambian módulos CONGELADOS sin thaw (siguen en frozen_files.txt en todos los commits desde la base):"
  printf '%s\n' "$MAL" | sed 's/^/      /'
  FALLO=1
fi
if [ -n "$SIN_ADR" ]; then
  echo "❌ thaws que no citan el ADR de RPP que los autoriza («ADR-NNN de RPP» en el mensaje):"
  printf '%s' "$SIN_ADR" | sed 's/^/      /'
  FALLO=1
fi
[ "$FALLO" = "0" ] || exit 1
echo "✓ ningún congelado cambia sin su thaw ($NB congelados en la base $(git rev-parse --short "$BASE"); $NC ficheros cambiados; autotest: «A»)"
echo "✓ thaws desde la base: $THAWS, y todos citan su ADR de RPP (autotest de los mensajes: «snns»)"
