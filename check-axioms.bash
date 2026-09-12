#!/usr/bin/env bash
# check-axioms.bash — cuenta los `axiom` de Lean por librería y ROMPE si no cuadran
# con lo escrito en AXIOMS.md.
#
# ⛔ POR QUÉ EXISTE (2026-09-12, A-1): este repo NO tenía ningún control que contara
# `axiom`. `check-sorry.bash` daba VERDE con 28 axiomas en el árbol, y el censo se movió
# de 34 a 28 y luego a 13 sin que nada lo registrara. Un `sorry` es visible; un `axiom` no.
#
# ⚠️ El caso que lo motiva: `FOL/Completeness.lean` sustituyó un `sorry` por CINCO `axiom`
# en un commit titulado «100% sorry-free».
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

ESPERADO_FOL=4
ESPERADO_TF=0

echo "════ AXIOMAS DE LEAN, por librería ════"
FAIL=0
for lib in FOL TheoryFramework; do
  [ -d "$lib" ] || continue
  N=$(grep -rhE '^axiom ' "$lib"/ --include=*.lean 2>/dev/null | wc -l | tr -d ' ')
  case "$lib" in
    FOL)             ESP=$ESPERADO_FOL ;;
    TheoryFramework) ESP=$ESPERADO_TF  ;;
  esac
  if [ "$N" = "$ESP" ]; then
    printf "  ✓ %-18s %2s axiom\n" "$lib" "$N"
  else
    printf "  ✗ %-18s %2s axiom — AXIOMS.md dice %s\n" "$lib" "$N" "$ESP"
    FAIL=1
  fi
done

echo
echo "════ ¿los cita AXIOMS.md? ════"
if [ ! -f AXIOMS.md ]; then
  echo "  ✗ NO EXISTE AXIOMS.md"; FAIL=1
else
  FALTAN=0
  while IFS= read -r NOMBRE; do
    [ -n "$NOMBRE" ] || continue
    grep -q "\`$NOMBRE\`" AXIOMS.md || { echo "  ✗ \`$NOMBRE\` no aparece en AXIOMS.md"; FALTAN=1; }
  done <<< "$(grep -rhE '^axiom ' FOL/ TheoryFramework/ --include=*.lean 2>/dev/null \
              | sed -E 's/^axiom +([A-Za-z_][A-Za-z0-9_'\'']*).*/\1/' | sort -u)"
  [ "$FALTAN" = "0" ] && echo "  ✓ todos los axiomas del árbol están documentados"
  [ "$FALTAN" = "1" ] && FAIL=1
fi

echo
echo "════ librerías RETIRADAS: no deben estar en el lakefile ════"
RET=0
for l in FOLPure PropLogic FOL_poli; do
  if grep -q "lean_lib «$l»" lakefile.lean 2>/dev/null; then
    echo "  ✗ $l sigue declarada en el lakefile (se retiró el 2026-09-12)"; RET=1
  fi
done
[ "$RET" = "0" ] && echo "  ✓ ninguna librería retirada está en el build"
[ "$RET" = "1" ] && FAIL=1

echo
if [ "$FAIL" = "0" ]; then
  echo "✅ CENSO DE AXIOMAS CORRECTO."
else
  echo "❌ EL CENSO NO CUADRA — actualizar AXIOMS.md (y sus cifras esperadas en este script)."
fi
exit "$FAIL"
