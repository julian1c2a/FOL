#!/bin/bash
# check-sorry.bash — Find all sorry statements in .lean files
#
# ⚠️ Cuenta `sorry` como TOKEN DE CÓDIGO, no como cadena de texto. Antes de buscar,
#    ELIMINA los comentarios de Lean (`--` de línea y `/- … -/` de bloque, anidados,
#    lo que incluye los docstrings `/-- … -/`) y los literales de cadena.
#
#    Sin eso el control MIENTE, y mucho: este proyecto declara «cero `sorry`» en
#    decenas de docstrings y anota «(sorry pendiente)» junto a varios axiomas, así que
#    la versión ingenua (`grep -c 'sorry'`) daba «101 sorry en 87 ficheros» donde hay 0,
#    y la versión que sólo excluye backticks seguía dando 15. Se arregla la
#    HERRAMIENTA, nunca la cifra.
#
#    Los números de línea que se imprimen son los del fichero ORIGINAL.
#
# Usage:
#   bash check-sorry.bash           # check all .lean files
#   bash check-sorry.bash staged    # check only staged files (for CI)
#   bash check-sorry.bash Module    # check files matching pattern

set -e

# ═══ PATH HIGIÉNICO ═════════════════════════════════════════════════════════
# ⚠️ No es paranoia: es un fallo MEDIDO el 2026-09-09. Lanzado desde PowerShell (o desde
# cualquier consola de Windows), `bash` hereda el PATH de Windows, y en esta máquina eso
# hace que `head` resuelva a C:/msys64/ucrt64/bin/head.exe — que no es el `head` de
# coreutils, sino el HEAD de Quantum ESPRESSO — y que `grep` sea otro build que rechaza
# las expresiones de este script («warning: ? at start of expression»).
#
# El resultado era el peor posible: los CUATRO controles [A] salían VACÍOS y el script
# imprimía «✅ DOCUMENTACIÓN SINCRONIZADA» sin haber comprobado absolutamente nada.
# Se antepone el /usr/bin de MSYS2, que es contra el que están escritos estos scripts.
[ -d /usr/bin ] && export PATH="/usr/bin:/bin:$PATH"

MODE="${1:-all}"
TOTAL=0
FILES_WITH_SORRY=0

if [ "$MODE" = "staged" ]; then
    LEAN_FILES=$(git diff --cached --name-only | grep '\.lean$' || true)
elif [ "$MODE" = "all" ]; then
    LEAN_FILES=$(find . -name "*.lean" ! -name "_template.lean" ! -path "./.lake/*" | sort)
else
    LEAN_FILES=$(find . -name "*${MODE}*.lean" ! -path "./.lake/*" | sort)
fi

if [ -z "$LEAN_FILES" ]; then
    echo "No .lean files found."
    exit 0
fi

# ── Despojador de comentarios y cadenas ──────────────────────────────────────
# Vive en `strip-lean.awk` (2026-10-03): una definición delicada vive en UN sitio, y la usan
# también `check-doc-sync.bash` [A] y [B] y `check-axioms.bash`.
# Emite UNA línea por cada línea de entrada (los números de línea siguen siendo los del original)
# sin comentarios (`--`, `/- … -/` anidados, docstrings) ni literales (cadenas y caracteres).
# ⚠️ Se ejecuta con `LC_ALL=C`: despoja por BYTES (en otro locale se niega, y la prueba de humo lo dice).
STRIP_AWK="$(cd "$(dirname "$0")" && pwd)/strip-lean.awk"
[ -f "$STRIP_AWK" ] || { echo "⚠️  SIN MEDIR — falta $STRIP_AWK"; exit 2; }
STRIP () { LC_ALL=C awk -f "$STRIP_AWK" "$@"; }
# ⛔ 2026-10-03 (ADR-116): `admit` es `sorry`, `stop` es `repeat sorry` y `sorryAx` es el propio axioma
# (Init/Tactics.lean del core); el patrón sólo casaba `sorry` y los tres daban verde.
# (un literal de nombre, `` `sorryAx ``, no es un uso: se excluye la comilla invertida delante; el
# nombre calificado `_root_.sorryAx` sí lo es — 2026-10-04, segunda revisión)
SORRY_RE='(^|[^A-Za-z0-9_'"'"'.`])(_root_\.)?(sorry|sorryAx|admit|stop)([^A-Za-z0-9_'"'"'!?]|$)'
# ── PRUEBA DE HUMO del despojador (2026-10-03, ADR-116; ampliada el 2026-10-04) ─────────────
# Si `strip-lean.awk` falla (un error de sintaxis en una edición, un awk incompatible, un locale que
# no es C), sin esto el control daba «✅ No sorry found.» con `sorry` reales: la salida vacía de un
# awk roto pasa por limpia. Entrada fija con TRECE `sorry` reales —uno por cada construcción que
# alguna versión del despojador leyó mal, en las dos revisiones adversariales— y siete falsos: si no
# salen exactamente trece, NO se mide.
SMOKE=$(STRIP <<'EOF' | grep -cE "$SORRY_RE" || true
-- sorry
"sorry" -- una cadena
/- sorry -/ sorry -- 1
('"', sorry) -- 2: '"' es un carácter, no abre cadena
s!"v {(sorry : Nat)}" -- 3: el código de una interpolación
theorem «a--b» : True := sorry -- 4: «…» es opaco
/-/- x -/ sorry -- 5: `/-` consume tres caracteres
r#"sorry"# -- una cadena en bruto
"uno
sorry dos" -- una cadena de dos líneas
by admit -- 6
throwError "x {(sorry : Nat)}" -- 7: throwError interpola
#eval !"{".isEmpty -- `!"…"` es el not de una cadena normal: su `{` no abre nada
sorry -- 8
s!"a {s!"b {(sorry : Nat)} c"} d" -- 9: interpolaciones anidadas
⟨'«', "»", sorry⟩ -- 10: un carácter tras un símbolo no ASCII
⟨r"\", sorry⟩ -- 11: una cadena en bruto tras un símbolo no ASCII
exact/- c -/sorry -- 12: un comentario es espacio
_root_.sorryAx Nat -- 13
(`sorryAx, h₀', Γ') -- un literal de nombre y dos primas
EOF
)
if [ "$SMOKE" != "13" ]; then
  echo "⚠️  SIN MEDIR — strip-lean.awk no pasa su prueba de humo ($SMOKE de 13 \`sorry\`)."
  exit 2
fi

echo "=== sorry report ==="
while IFS= read -r FILE; do
    [ -z "$FILE" ] && continue
    [ ! -f "$FILE" ] && continue
    HITS=$(STRIP "$FILE" | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
    [ -z "$HITS" ] && continue
    COUNT=$(printf '%s\n' "$HITS" | grep -c . || true)
    echo ""
    echo "📄 $FILE ($COUNT sorry)"
    while IFS= read -r LN; do
        [ -z "$LN" ] && continue
        printf '   %s:%s\n' "$LN" "$(sed -n "${LN}p" "$FILE")"
    done <<< "$HITS"
    TOTAL=$((TOTAL + COUNT))
    FILES_WITH_SORRY=$((FILES_WITH_SORRY + 1))
done <<< "$LEAN_FILES"

echo ""
if [ "$TOTAL" -eq 0 ]; then
    echo "✅ No sorry found."
else
    echo "⚠️  Total: $TOTAL sorry in $FILES_WITH_SORRY file(s)."
    exit 1
fi
