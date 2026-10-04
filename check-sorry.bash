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

# ⛔ 2026-10-04 (cuarta revisión de ADR-116): el script se sitúa en SU directorio, como los demás
# controles; antes medía donde lo lanzaran (y desde un directorio sin `.lean` salía en verde).
cd "$(dirname "$0")" || exit 2

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
# ── PRUEBA DE HUMO del despojador (2026-10-03, ADR-116; ampliada en cada revisión) ─────────────────
# Si `strip-lean.awk` falla (un error de sintaxis en una edición, un awk incompatible, un locale que
# no es C), sin esto el control daba «✅ No sorry found.» con `sorry` reales: la salida vacía de un
# awk roto pasa por limpia. Entrada fija con 39 `sorry` reales —uno por cada construcción que alguna
# versión del despojador leyó mal, en las cuatro revisiones adversariales— y señuelos; y aparte una
# línea con CRLF. ⛔ Se compara el CONJUNTO de líneas con `sorry`, no la cuenta (cuarta revisión): con
# la cuenta, un despojador que perdía un `sorry` real y hacía contar un señuelo daba la misma cifra.
SMOKE=$(STRIP <<'EOF' | grep -nE "$SORRY_RE" | cut -d: -f1 | tr '\n' ' ' || true
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
def b := !s!"{(sorry : Nat)}".isEmpty -- 14: el not de una interpolada
def N := { x : Int //-x > 0 }
sorry -- 15: `//` es un token, y lo que le sigue no abre comentario
def u := p |>.r"\"" sorry "x" -- 16: tras `|>.`, `r` es un identificador y su cadena es normal
def g := f '
'"' "
sorry -- 17: un carácter que es un salto de línea literal
def w := φs! "{sorry}" -- `φs!` es UN identificador: su cadena es normal
theorem t18 (p q : Prop) (hp : p) : p \/-- la izquierda
  q := Or.inl sorry -- 18: `\/` es un token
def m : IO Int := do
  let x <-- sorry -- 19: `<-` es un token
  return x
def u := f `r"\"" sorry "x" -- 20: tras la comilla invertida, `r` es un identificador
def U := Nat ⊕'"'" = "x"
theorem t21 : True := sorry -- 21: `⊕'` es un token
def k := 0...s!"{(sorry : Nat)}".length -- 22: `..` + `s!`
  throwErrorAt stx[0] "b {(sorry : Nat)}" -- 23: throwErrorAt x[…]
  throwErrorAt (← getRef) "c {(sorry : Nat)}" -- 24: throwErrorAt (…)
def pl : IO Unit := println! "v {(sorry : Nat)}" -- 25
def dt : Nat := dbg_trace "v {(sorry : Nat)}"; 0 -- 26
  trace[Meta.debug] "x {(sorry : Nat)}" -- 27
  Macro.trace[foo] "z {(sorry : Nat)}" -- 28
  logInfo m!"m {(sorry : Nat)}" -- 29
  let s := f!"f {(sorry : Nat)}" -- 30
  throwNamedError
    lean.foo "a {(sorry : Nat)}" -- 31
  logNamedErrorAt stx
    lean.foo "a {(sorry : Nat)}" -- 32
/- a /- b -/ "c -/
theorem t33 : True := sorry -- 33: los comentarios anidan
/- sorry -/
def r := r#"a "b"#
theorem t34 : True := sorry -- 34: la cadena en bruto acaba en `"#`
/- Says "hi -/
theorem t35 : True := sorry -- 35: una comilla dentro de un comentario
def q := p.1'"'
theorem t36 : True := sorry -- 36: tras `p.1`, `'"'` es un carácter
def f (args : Array Syntax) : MetaM Unit := throwErrorAt args[0]! "falta {(sorry : Nat)}" -- 37: throwErrorAt x[i]!
def f2 (a b : Nat) : Nat := a <<<-- "
  b
theorem t38 : True := sorry -- 38: `<<<` es un token, y lo de detrás un comentario
def nb := s!"{({a := 1} : P).a} y" -- llaves anidadas dentro de una interpolación
theorem t39 : True := sorry -- 39: detrás de las llaves anidadas
def w2 := x₁throwError "{sorry}" -- `x₁throwError` es UN identificador: su cadena es normal
EOF
)
SMOKE_ESPERADO="3 4 5 6 7 11 12 14 15 16 17 18 19 21 23 24 27 30 32 34 36 37 38 39 40 41 42 43 44 45 47 49 51 54 56 58 59 62 64 "
SMOKE_CRLF=$(printf 'throwErrorAt\r\n  stx "a {(sorry : Nat)}"\r\n' | STRIP | grep -cE "$SORRY_RE" || true)
if [ "$SMOKE" != "$SMOKE_ESPERADO" ] || [ "$SMOKE_CRLF" != "1" ]; then
  echo "⚠️  SIN MEDIR — strip-lean.awk no pasa su prueba de humo."
  echo "    líneas con sorry: «$SMOKE»"
  echo "    esperadas:        «$SMOKE_ESPERADO»   (con CRLF: $SMOKE_CRLF de 1)"
  exit 2
fi

MODE="${1:-all}"
TOTAL=0
FILES_WITH_SORRY=0

if [ "$MODE" = "staged" ]; then
    # (el ÍNDICE, no el árbol: se despoja `git show :FICHERO`, y sólo lo añadido o cambiado)
    LEAN_FILES=$(git diff --cached --name-only --diff-filter=ACM | grep '\.lean$' || true)
elif [ "$MODE" = "all" ]; then
    # (sin `_rpp/` —el clon de RPP que hace la CI de FOL— ni `Probe/` —local de RPP, fuera de git—: el
    #  alcance es el mismo en local que en la CI; 2026-10-04, tercera revisión de ADR-116)
    LEAN_FILES=$(find . -name "*.lean" ! -name "_template.lean" ! -path "./.lake/*" ! -path "./_rpp/*" ! -path "./Probe/*" | sort)
else
    LEAN_FILES=$(find . -name "*${MODE}*.lean" ! -path "./.lake/*" | sort)
fi

if [ -z "$LEAN_FILES" ]; then
    # en modo all, no encontrar ningún `.lean` es no haber medido (cuarta revisión): antes, «No .lean files
    # found.» y salida 0, sin pasar siquiera por el autotest
    if [ "$MODE" = "all" ]; then echo "⚠️  SIN MEDIR — ningún .lean en $(pwd)"; exit 2; fi
    echo "No .lean files found."
    exit 0
fi


echo "=== sorry report ==="
while IFS= read -r FILE; do
    [ -z "$FILE" ] && continue
    [ "$MODE" != "staged" ] && [ ! -f "$FILE" ] && continue
    if [ "$MODE" = "staged" ]; then
        CONTENIDO=$(git show ":$FILE" 2>/dev/null || true)
        HITS=$(printf '%s\n' "$CONTENIDO" | STRIP | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
    else
        HITS=$(STRIP "$FILE" | grep -nE "$SORRY_RE" | cut -d: -f1 || true)
    fi
    [ -z "$HITS" ] && continue
    COUNT=$(printf '%s\n' "$HITS" | grep -c . || true)
    echo ""
    echo "📄 $FILE ($COUNT sorry)"
    while IFS= read -r LN; do
        [ -z "$LN" ] && continue
        if [ "$MODE" = "staged" ]; then
            printf '   %s:%s\n' "$LN" "$(printf '%s\n' "$CONTENIDO" | sed -n "${LN}p")"
        else
            printf '   %s:%s\n' "$LN" "$(sed -n "${LN}p" "$FILE")"
        fi
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
