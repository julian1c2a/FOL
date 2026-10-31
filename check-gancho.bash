#!/bin/bash
# check-gancho.bash — los ganchos VERSIONADOS (.githooks/) hacen lo que dicen, probados en un repositorio de juguete
# (T14, ADR-234 de RPP).
#
# Desde ADR-234 el gancho que corre en un clon es el fichero versionado (`bash git-lock.bash init` pone
# `core.hooksPath = .githooks`). Este script lo PRUEBA: crea un repositorio temporal con un congelado (A.lean), un
# bloqueado (B.lean) y uno libre (C.lean), con las listas en CRLF (como las deja core.autocrlf en Windows: R3-4-01),
# activa los ganchos por `core.hooksPath`, y comprueba siete casos:
#   1. tocar el congelado            → RECHAZADO (pre-commit)
#   2. tocar el bloqueado            → RECHAZADO (pre-commit)
#   3. renombrar el congelado (mv)   → RECHAZADO (pre-commit, por --no-renames)
#   4. tocar el libre                → ACEPTADO
#   5. un thaw sin citar un ADR      → RECHAZADO (commit-msg)
#   6. el mismo thaw, con «ADR-NNN de RPP» en el mensaje → ACEPTADO
#   7. el re-freeze (la entrada vuelve a la lista) → ACEPTADO (commit-msg sólo mira lo que SALE)
# y que THAW_RE es la misma en .githooks/commit-msg y en check-congelados.bash.
# Sale con 0 si los siete casos dan lo esperado, con 1 si alguno no, y con 2 si no puede medir.
export PATH="/usr/bin:$PATH"
set -uo pipefail
cd "$(dirname "$0")" || exit 2
RAIZ=$(pwd)

for h in .githooks/pre-commit .githooks/commit-msg; do
  [ -f "$h" ] || { echo "❌ NO PUDE MEDIR: falta $h"; exit 2; }
done
command -v git > /dev/null || { echo "❌ NO PUDE MEDIR: no hay git"; exit 2; }

RE_HOOK=$(grep -m1 "^THAW_RE=" .githooks/commit-msg)
RE_CONG=$(grep -m1 "^THAW_RE=" check-congelados.bash)
if [ -z "$RE_HOOK" ] || [ "$RE_HOOK" != "$RE_CONG" ]; then
  echo "❌ THAW_RE distinta: commit-msg «$RE_HOOK», check-congelados.bash «$RE_CONG»"
  exit 1
fi

T=$(mktemp -d) || exit 2
trap 'rm -rf "$T"' EXIT
cd "$T" || exit 2
git init -q . || { echo "❌ NO PUDE MEDIR: git init"; exit 2; }
git config user.email prueba@example.invalid
git config user.name prueba
git config core.autocrlf false
mkdir .githooks
cp "$RAIZ/.githooks/pre-commit" "$RAIZ/.githooks/commit-msg" .githooks/
chmod +x .githooks/pre-commit .githooks/commit-msg
printf 'A.lean\r\n' > frozen_files.txt
printf 'A.lean\r\nB.lean\r\n' > locked_files.txt
for f in A B C; do echo "-- $f" > "$f.lean"; done
git add -A && git commit -q -m "base" --no-verify || { echo "❌ NO PUDE MEDIR: el commit base"; exit 2; }
git config core.hooksPath .githooks

FALLO=0
caso() {   # caso <n> <esperado: acepta|rechaza> <descripción> — con lo preparado en el índice; mensaje en $MSG
  local n=$1 esp=$2 d=$3 got
  if git commit -q -m "$MSG" > "$T/salida.$n" 2>&1; then got=acepta; else got=rechaza; fi
  if [ "$got" = "$esp" ]; then
    printf '  ✓ %s. %-38s %s\n' "$n" "$d" "$got"
  else
    printf '  ✗ %s. %-38s %s (esperado: %s)\n' "$n" "$d" "$got" "$esp"
    sed 's/^/        /' "$T/salida.$n"
    FALLO=1
  fi
  git reset -q --hard HEAD > /dev/null 2>&1
}

MSG="toca A";             echo "-- cambio" >> A.lean; git add A.lean;             caso 1 rechaza "tocar el congelado"
MSG="toca B";             echo "-- cambio" >> B.lean; git add B.lean;             caso 2 rechaza "tocar el bloqueado"
MSG="renombra A";         git mv A.lean A2.lean;                                   caso 3 rechaza "renombrar el congelado"
MSG="toca C";             echo "-- cambio" >> C.lean; git add C.lean;             caso 4 acepta  "tocar el libre"
MSG="thaw de A, sin ADR"; printf '' > frozen_files.txt; printf 'B.lean\r\n' > locked_files.txt
                          echo "-- cambio" >> A.lean; git add -A;                  caso 5 rechaza "un thaw sin citar el ADR"
MSG="Thaw autorizado de A (ADR-999 de RPP)"
                          printf '' > frozen_files.txt; printf 'B.lean\r\n' > locked_files.txt
                          echo "-- cambio" >> A.lean; git add -A;                  caso 6 acepta  "el thaw, citando su ADR de RPP"
MSG="re-freeze de A";     printf 'A.lean\r\n' > frozen_files.txt; printf 'A.lean\r\nB.lean\r\n' > locked_files.txt
                          git add -A;                                              caso 7 acepta  "el re-freeze"

if [ "$FALLO" = "0" ]; then
  echo "✓ los ganchos versionados hacen lo que dicen: 7 de 7 casos (listas en CRLF; activos por core.hooksPath)"
  exit 0
fi
echo "❌ los ganchos versionados NO hacen lo que dicen"
exit 1
