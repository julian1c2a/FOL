#!/bin/bash
# check-indice.bash — el ÍNDICE de las constantes de FOL y de TheoryFramework (L5-11 y ADR-254 de RPP).
#
# ⛔ POR QUÉ EXISTE. «Antes de construir, buscar» se repetía en seis ADR de RPP (L5-11, ronda 1 de la auditoría de la
# base): se volvía a construir lo que ya estaba, porque no había dónde buscarlo salvo con grep sobre el texto, que no ve
# el nombre completo que da un `namespace` ni el enunciado que elabora Lean. La decisión del propietario (2026-11-04):
# un índice (nombre, módulo, enunciado) de todas las constantes de RPP y FOL, regenerado y comprobado en cada run. Éste
# es el de FOL; el de RPP, `../ROBINSON_PlusPlus/doc/indice.tsv`, lo genera el check-indice.bash de RPP, que mide además
# lo que nadie usa de FOL (`../ROBINSON_PlusPlus/doc/control/fol-sin-uso.tsv`, B-5 de la auditoría de FOL del
# 2026-09-12): para eso hace falta RPP.
#
# QUÉ ESCRIBE. Del entorno de Lean —un fichero generado que importa CADA módulo de FOL y de TheoryFramework—, cada
# constante DECLARADA: con rango de declaración en su fuente y que Lean no genere (ni recursores, ni `casesOn`, ni
# `match_N`, ni ecuaciones, ni `injEq`, ni `ctorElim`…: las reglas de `Lean.isAutoDeclOrPrivate_Internal`, de
# Lean/AutoDecl.lean, salvo que una privada cuenta por su nombre de usuario), en `doc/indice.tsv`, una por línea:
# «nombre · clase · módulo · enunciado», el enunciado como lo imprime Lean con los nombres COMPLETOS (`pp.fullNames`: no
# depende de los `open` ni de los `export`), en una línea. El código Lean es el del check-indice.bash de RPP, sin la
# medida de uso.
#
# ⭐ La tabla se compara con lo que se GENERA, línea a línea: cualquier diferencia es rojo. Se rehace con `--rehacer` en
# el mismo commit que cambia una declaración (como DEPENDENCIES.md con gen-dependencies.py y el §6 de REFERENCE.md con
# gen-reference.py, que da los nombres por módulo pero no los enunciados).
#
# 🔑 CALIBRACIÓN (feedback de los controles que no comprueban nada de RPP): el fichero generado declara seis
# constantes de prueba —un teorema, otro que lo usa, una privada, un inductivo con dos constructores, una función por
# casos sobre él y una recursiva—; el control exige ver en el índice exactamente esas ocho declaraciones (con los dos
# constructores) y sus enunciados (ni el recursor, ni `casesOn`, ni `match_1`, ni `injEq`), que el filtro de las
# generadas quite él solo las de prueba sin rango (la falta de rango es un segundo filtro, y sin esto no se le vería
# fallar al primero), y que se generen al menos cuatro constantes más. Si el censo no corre o no llega al final (la
# línea FIN), es rojo.
#
# 🔧 En local, con RPP construido al lado: el entorno se carga desde la raíz de RPP, que es donde se construye FOL (M-3,
# ADR-205 de RPP); en la CI de FOL, desde FOL, que acaba de construirse ahí. `lake` en el PATH (PowerShell, o un bash
# con él).
#
#   bash check-indice.bash            # genera y compara con doc/indice.tsv
#   bash check-indice.bash --rehacer  # además, la reescribe con lo generado
#
# Para buscar antes de construir: `grep -i 'patrón' doc/indice.tsv ../ROBINSON_PlusPlus/doc/indice.tsv`.

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

INDICE=doc/indice.tsv
REHACER=0
[ "${1:-}" = "--rehacer" ] && REHACER=1
SIBLING="${RPP_DIR:-../ROBINSON_PlusPlus}"

echo "════ EL ÍNDICE DE LAS CONSTANTES DE FOL Y DE TheoryFramework ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell. Un control que no se ejecuta NO es un control."
  exit 2
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
# (Lean es un programa de Windows en la máquina de desarrollo: las rutas que lee, en su forma; en Linux, tal cual)
win() { cygpath -m "$1" 2>/dev/null || printf '%s' "$1"; }
LEANFILE="$TMP/Indice.lean"
MODS="$TMP/modulos.txt"
{ find FOL TheoryFramework -name '*.lean' ; echo FOL.lean ; echo TheoryFramework.lean ; } \
  | sed -e 's/\.lean$//' -e 's|/|.|g' | LC_ALL=C sort -u > "$MODS"
NMODS=$(grep -c . "$MODS")
if [ "$NMODS" -lt 50 ]; then
  echo "  ❌ sólo $NMODS módulos: la lista de ficheros no se pudo leer."
  exit 1
fi
{
  echo "import Lean"
  sed 's/^/import /' "$MODS"
  cat <<'EOF'
open Lean Meta

namespace IndiceCalib
-- la calibración: el índice tiene que ver estas ocho declaraciones (con los dos constructores), y no lo que Lean
-- genera con ellas
theorem calibT (n : Nat) : n + 0 = n := rfl
theorem calibU : 3 + 0 = 3 := calibT 3
private def calibP : Nat := 1
inductive CalibI where
  | uno
  | dos (n : Nat)
def calibM : CalibI → Nat
  | .uno => 0
  | .dos n => n
def calibR : Nat → Nat
  | 0 => 0
  | n + 1 => calibR n
end IndiceCalib

def indiceRaiz (m : Name) : Option String :=
  let r := m.getRoot.toString
  if r == "FOL" then some "FOL" else if r == "TheoryFramework" then some "TF" else none

/-- ¿la genera Lean? Las reglas de `Lean.isAutoDeclOrPrivate_Internal` (Lean/AutoDecl.lean), salvo que una privada
    cuenta por su nombre de usuario: aquélla las da todas por generadas. -/
partial def indiceGenerada (env : Environment) (d : Name) : Bool :=
  let u := (privateToUserName? d).getD d
  if isPrivateName d && u.isAnonymous then false
  else if d.hasMacroScopes || u.isInternal || isReservedName env d then true
  else match d with
    | .str n s =>
      indiceGenerada env n || s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "unsafe_"
        || s.startsWith "grind_"
        || (env.isConstructor n && ["injEq", "inj", "sizeOf_spec", "elim", "noConfusion"].contains s)
        || (match env.find? n with
            | some (.inductInfo _) =>
              s.startsWith "brecOn_" || s.startsWith "below_"
                || ["casesOn", "recOn", "brecOn", "below", "ndrec", "ndrecOn", "noConfusionType", "noConfusion",
                    "ofNat", "toCtorIdx", "ctorIdx", "ctorElim", "ctorElimType"].contains s
                || (isSubobjectField? env n (.mkSimple s)).isSome
            | _ => false)
    | _ => false

/-- el enunciado en una línea: los saltos y los tabuladores, espacios; los espacios seguidos, uno -/
def indiceLinea (s : String) : String := Id.run do
  let mut out := ""
  let mut esp := false
  for ch in s.toList do
    let ch := if ch == '\n' || ch == '\t' || ch == '\r' then ' ' else ch
    if ch == ' ' then
      unless esp do out := out.push ' '
      esp := true
    else
      out := out.push ch
      esp := false
  return out

#eval show MetaM Unit from do
  let env ← getEnv
  let some rutaI ← IO.getEnv "INDICE_FOL" | throwError "falta INDICE_FOL"
  let repoDe (c : Name) : Option (String × String) := match env.getModuleIdxFor? c with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      (indiceRaiz m).map (fun r => (r, m.toString))
    | none => if (`IndiceCalib).isPrefixOf ((privateToUserName? c).getD c) then some ("CALIB", "_calibracion") else none
  let mut indice : Array String := #[]
  let mut calib : Array String := #[]
  let mut nDecl : Std.HashMap String Nat := {}
  let mut nGen : Std.HashMap String Nat := {}
  let mut sinRango : Array Name := #[]
  let mut nCortados := 0
  for (c, ci) in env.constants.toList do
    let some (repo, modulo) := repoDe c | continue
    let gen := (match ci with | .recInfo _ | .quotInfo _ => true | _ => false)
      || isAuxRecursor env c || isNoConfusion env c || isRecCore env c || isMatcherCore env c || indiceGenerada env c
    if gen then
      nGen := nGen.insert repo ((nGen.getD repo 0) + 1)
      continue
    if (← findDeclarationRanges? c).isNone then
      sinRango := sinRango.push c
      continue
    let u := (privateToUserName? c).getD c
    let esMeta := match ci.type.getAppFn.constName? with
      | some h => h.getRoot == `Lean
      | none => false
    let clase := match ci with
      | .thmInfo _ => "teorema"
      | .axiomInfo _ => "axioma"
      | .opaqueInfo _ => "opaca"
      | .ctorInfo _ => "constructor"
      | .inductInfo _ => if isClass env c then "clase" else if isStructure env c then "estructura" else "inductivo"
      | .defnInfo _ =>
        if isInstanceCore env c then "instancia"
        else if (env.getProjectionFnInfo? c).isSome then "campo"
        else if esMeta then "meta" else "def"
      | _ => "otra"
    let clase := if isPrivateName c then clase ++ "·privada" else clase
    nDecl := nDecl.insert repo ((nDecl.getD repo 0) + 1)
    let f ← withOptions (fun o => pp.fullNames.set o true) (ppExpr ci.type)
    let mut txt := indiceLinea (f.pretty 100000)
    -- (un enunciado de más de 4000 caracteres se corta, y lo dice)
    if txt.length > 4000 then
      nCortados := nCortados + 1
      txt := String.ofList (txt.toList.take 4000) ++ s!" …[+{txt.length - 4000}]"
    let fila := s!"{u}\t{clase}\t{modulo}\t{txt}"
    if repo == "CALIB" then calib := calib.push s!"CALIB\tI\t{fila}" else indice := indice.push fila
  IO.FS.writeFile rutaI ("\n".intercalate indice.toList ++ "\n")
  for l in calib do IO.println l
  for r in ["FOL", "TF", "CALIB"] do
    IO.println s!"TOTAL\t{r}\t{nDecl.getD r 0}\t{nGen.getD r 0}"
  IO.println s!"SINRANGO\t{sinRango.size}\t{" ".intercalate ((sinRango.toList.map toString).take 10)}"
  -- (las de prueba que no tienen rango tiene que verlas generadas el primer filtro: si no, no se le ve fallar)
  let calibSinRango := sinRango.filter (fun c => (`IndiceCalib).isPrefixOf ((privateToUserName? c).getD c))
  IO.println s!"SINRANGOCALIB\t{calibSinRango.size}\t{" ".intercalate (calibSinRango.toList.map toString)}"
  IO.println s!"CORTADOS\t{nCortados}"
  IO.println "FIN"
EOF
} > "$LEANFILE"

GEN_I="$TMP/indice.tsv"
T0=$(date +%s)
RC=1
if [ -d "$SIBLING/ROBINSON_PlusPlus" ] && [ -d "$SIBLING/.lake/build" ]; then
  SALIDA=$(cd "$SIBLING" && INDICE_FOL="$(win "$TMP/indice.crudo")" lake env lean "$(win "$LEANFILE")" 2>&1)
  RC=$?
elif [ -n "${CI:-}" ]; then
  SALIDA=$(INDICE_FOL="$(win "$TMP/indice.crudo")" lake env lean "$(win "$LEANFILE")" 2>&1)
  RC=$?
else
  echo "  ❌ NO PUEDO MEDIR: sin RPP construido al lado ($SIBLING) ni la CI, no cargo el entorno de Lean (M-3)."
  exit 1
fi
T1=$(date +%s)
FAIL=0
# (sin tubería hacia `grep -q`: con pipefail, el SIGPIPE de printf la daría por fallida)
if [ "$RC" != "0" ] || ! grep -qx 'FIN' <<< "$SALIDA"; then
  echo "  ❌ el censo no llegó al final (lake env lean salió con $RC):"
  printf '%s\n' "$SALIDA" | grep -v '^CALIB' | head -20 | sed 's/^/      /'
  exit 1
fi
echo "  censo: $NMODS módulos, $((T1 - T0)) s"
tr -d '\r' < "$TMP/indice.crudo" | grep . | LC_ALL=C sort > "$GEN_I"

# la calibración: el índice, exactamente estas siete (con su enunciado)
CAL_I=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "CALIB" && $2 == "I" { print $3 "\t" $4 "\t" $6 }' | LC_ALL=C sort)
ESP_I=$(LC_ALL=C sort <<'EOF'
IndiceCalib.CalibI	inductivo	Type
IndiceCalib.CalibI.dos	constructor	Nat → IndiceCalib.CalibI
IndiceCalib.CalibI.uno	constructor	IndiceCalib.CalibI
IndiceCalib.calibM	def	IndiceCalib.CalibI → Nat
IndiceCalib.calibP	def·privada	Nat
IndiceCalib.calibR	def	Nat → Nat
IndiceCalib.calibT	teorema	∀ (n : Nat), n + 0 = n
IndiceCalib.calibU	teorema	3 + 0 = 3
EOF
)
if [ "$CAL_I" = "$ESP_I" ]; then
  echo "  ✓ calibración del índice: las ocho declaraciones de prueba (dos constructores), con su enunciado, y nada más"
else
  echo "  ❌ calibración del índice: no ve exactamente las declaraciones de prueba —no comprueba lo que dice—:"
  diff <(printf '%s\n' "$ESP_I") <(printf '%s\n' "$CAL_I") | sed 's/^/      /'
  FAIL=1
fi
SRCAL=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "SINRANGOCALIB" { print $2 "\t" $3 }')
if [ "${SRCAL%%	*}" != "0" ]; then
  echo "  ❌ calibración: de las de prueba, éstas sólo las quitó la falta de rango, no el filtro de las generadas:"
  echo "     ${SRCAL#*	}"
  FAIL=1
fi
GENCAL=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "TOTAL" && $2 == "CALIB" { print $4 }')
if [ "${GENCAL:-0}" -lt 4 ]; then
  echo "  ❌ calibración: sólo ${GENCAL:-0} constantes generadas con las de prueba (el recursor, casesOn, match_1…):"
  echo "     el filtro no las ve."
  FAIL=1
fi
printf '%s\n' "$SALIDA" | awk -F'\t' '
  $1 == "TOTAL" && $2 != "CALIB" { printf "  %-4s %5d declaradas (%5d generadas, fuera)\n", $2, $3, $4 }
  $1 == "SINRANGO" { printf "  %d constantes sin rango de declaración (generadas), fuera: %s\n", $2, $3 }
  $1 == "CORTADOS" && $2 > 0 { printf "  %d enunciados de más de 4000 caracteres, cortados (lo dice la línea)\n", $2 }'

if [ "$REHACER" = "1" ]; then
  {
    echo "# doc/indice.tsv — el ÍNDICE de las constantes DECLARADAS de FOL y de TheoryFramework (sin las que genera Lean):"
    echo "# nombre, clase, módulo y enunciado, como lo imprime Lean con los nombres completos, en una línea. Lo genera y lo"
    echo "# compara, en cada run de la CI, check-indice.bash (L5-11 y ADR-254 de RPP); se rehace con"
    echo "# «bash check-indice.bash --rehacer» en el commit que cambia una declaración. Las de RPP, en"
    echo "# ../ROBINSON_PlusPlus/doc/indice.tsv. Para buscar antes de construir:"
    echo "#   grep -i 'patrón' doc/indice.tsv ../ROBINSON_PlusPlus/doc/indice.tsv"
    echo "# nombre	clase	módulo	enunciado"
    cat "$GEN_I"
  } > "$INDICE"
  echo "  ✏️  $INDICE ($(grep -c . "$GEN_I") líneas), rehecha."
fi

if [ ! -f "$INDICE" ]; then
  echo "  ❌ no existe $INDICE."
  FAIL=1
else
  DECL="$TMP/declarado.tsv"
  grep -v '^#' "$INDICE" | tr -d '\r' | grep . | LC_ALL=C sort > "$DECL"
  NUEVAS=$(LC_ALL=C comm -13 "$DECL" "$GEN_I")
  IDAS=$(LC_ALL=C comm -23 "$DECL" "$GEN_I")
  if [ -z "$NUEVAS" ] && [ -z "$IDAS" ]; then
    echo "  ✓ $INDICE: $(grep -c . "$DECL") líneas, las que se generan"
  else
    echo "  ❌ $INDICE NO es lo que se genera ($(printf '%s\n' "$NUEVAS" | grep -c .) de más en lo generado,"
    echo "     $(printf '%s\n' "$IDAS" | grep -c .) de menos): «bash check-indice.bash --rehacer»"
    printf '%s\n' "$NUEVAS" | grep . | head -15 | cut -c1-200 | sed 's/^/      + /'
    printf '%s\n' "$IDAS" | grep . | head -15 | cut -c1-200 | sed 's/^/      - /'
    FAIL=1
  fi
fi

if [ "$FAIL" = "0" ]; then
  echo "✅ EL ÍNDICE DE FOL Y DE TheoryFramework, AL DÍA."
else
  echo "❌ EL ÍNDICE DE FOL Y DE TheoryFramework NO CUADRA (o la calibración falló)."
  exit 1
fi
