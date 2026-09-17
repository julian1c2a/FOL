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
# Emite UNA línea de salida por cada línea de entrada (así los números de línea
# siguen siendo los del original) con el contenido de comentarios y de literales
# de cadena sustituido por nada. Los bloques `/- … -/` ANIDAN en Lean, por eso se
# lleva un contador de profundidad y no un booleano.
STRIP='
BEGIN { depth = 0 }
{
  line = $0; out = ""; i = 1; n = length(line)
  while (i <= n) {
    two = substr(line, i, 2)
    if (depth > 0) {
      if (two == "-/") { depth--; i += 2; continue }
      if (two == "/-") { depth++; i += 2; continue }
      i++; continue
    }
    if (two == "/-") { depth++; i += 2; continue }
    if (two == "--") { break }
    c = substr(line, i, 1)
    if (c == "\"") {
      i++
      while (i <= n) {
        c2 = substr(line, i, 1)
        if (c2 == "\\") { i += 2; continue }
        if (c2 == "\"") { i++; break }
        i++
      }
      out = out " "; continue
    }
    out = out c; i++
  }
  print out
}
'
SORRY_RE='(^|[^a-zA-Z_])sorry([^a-zA-Z_]|$)'

echo "=== sorry report ==="
while IFS= read -r FILE; do
    [ -z "$FILE" ] && continue
    [ ! -f "$FILE" ] && continue
    HITS=$(awk "$STRIP" "$FILE" 2>/dev/null | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
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
