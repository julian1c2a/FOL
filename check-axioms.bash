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
#
# ⭐ 2026-10-02 (ADR-115 de RPP): 4 → 0. Los cuatro de `FOL/MetaRules.lean` (`imp_intro`, `raa`,
# `or_elim`, `ex_elim`) eran REFUTABLES sin usarlos (`FOL/Inconsistencia.lean` §3) y se borraron con
# el módulo. Un `axiom` sobre `Derives` puede ser refutable con el propio recursor, y eso es lo que pasó.
#
# ⛔⛔ 2026-10-03 (ADR-116 de RPP): HASTA HOY ESTE CONTROL ERA UN GREP de `^axiom `, y no veía
# `private`/`protected`/`@[…] axiom`, uno sangrado, ni uno en los barrels `FOL.lean` y
# `TheoryFramework.lean` — y un patrón más ancho casaba con los ejemplos de los docstrings
# (`Enumeration.lean` cita dos `axiom` de la vieja `Completeness` en un bloque de código). Ahora:
#   (1) el censo de las dos librerías del build se mide en el ENTORNO de Lean (`lake env lean`
#       sobre un fichero que importa `FOL` y todo `TheoryFramework`): cuenta cada `axiomInfo`
#       cuyo módulo es de FOL o de TheoryFramework, se declare como se declare;
#   (2) el grep queda como CONTRASTE, sobre el código SIN comentarios ni cadenas
#       (`strip-lean.awk`, el mismo despojador que `check-sorry.bash`) y con todas las formas de
#       declaración; si el grep y el entorno no dan lo mismo, ROMPE (un `axiom` en un módulo que el
#       build no compila, o uno que el grep no sabe leer);
#   (3) la cuarentena, que no se compila, se sigue midiendo por grep, ya sin comentarios.
# ⭐ 2026-10-04 (ADR-116, segunda revisión): ya que el entorno está cargado, se censa también el
# `sorry` en él: toda constante de FOL o de TheoryFramework cuyo tipo o valor nombra `sorryAx`. Es el
# contraste de `check-sorry.bash`, que lee texto: aquí no hay forma de escribirlo que no se vea.
# 🔧 EJECUTAR DESDE POWERSHELL (desde Bash, `lake` no está en el PATH — y el script lo DICE).
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

ESPERADO_FOL=0
ESPERADO_TF=0

# ⭐ 2026-09-13: la CUARENTENA también se cuenta. Motivo: `cuarentena/Completeness.lean` bajó de
# 5 a 3 y luego a 1 axioma (2026-09-13: la enumeración de fórmulas, y los dos `termEqv_*_congr`),
# y la cifra quedó escrita en SEIS documentos sin que NADA la comprobara. Un número escrito y no
# medido se pudre.
# ⚠️ NO incluye `cuarentena/librerias-retiradas/` (15 axiomas): son librerías MUERTAS, fuera del
# lakefile, y su cifra no es una promesa de nadie.
ESPERADO_CUAR=0

STRIP_AWK="$PWD/strip-lean.awk"
if [ ! -f "$STRIP_AWK" ]; then
  echo "  ⚠️  SIN MEDIR — falta $STRIP_AWK"; exit 2
fi
# (despoja por BYTES: con `LC_ALL=C`, y en otro locale se niega — la prueba de humo de abajo lo ve)
STRIP () { LC_ALL=C awk -f "$STRIP_AWK" "$@"; }
# Una declaración de `axiom`, sobre el código YA SIN comentarios ni cadenas: con sangría, con
# atributos y con modificadores.
AX_RE='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|unsafe|partial)[[:space:]]+)*axiom[[:space:]]+[^[:space:]:({]+'

# grep_axiomas FICHERO… → una línea «fichero:línea:nombre» por axioma declarado.
# ⛔ 2026-10-04 (tercera revisión de ADR-116 de RPP): se busca el TOKEN `axiom` en todo el código despojado,
# no sólo a principio de línea (`open Nat in axiom x`, `def t := 0 axiom x`); si el nombre va en la línea
# siguiente, sale «?». En modo byte (LC_ALL=C), como el despojador.
# ⛔ Y desde la cuarta revisión: la frontera excluye la comilla invertida (`` `axiom `` es un literal de
# nombre) y los bytes de continuación UTF-8 (`αaxiom` es UN identificador); el nombre puede ser `«…»`; el
# sed se ANCLA a la frontera (con `.*` voraz, `axiom my_axiom` salía «?»); y los ficheros se pasan de uno en
# uno, nunca partidos por espacios («cuarentena/X - copia.lean» se saltaba en silencio). Un argumento que
# no es un fichero es SIN MEDIR.
AX_TOK="(^|[^A-Za-z0-9_'.«\`"$'\x80-\xbf'"])axiom([[:space:]]+(«[^»]*»|[^[:space:]:({«]+)|«[^»]*»|[[:space:]]*\$)"
grep_axiomas () {
  local f
  for f in "$@"; do
    [ -f "$f" ] || { echo "SIN-MEDIR:$f"; continue; }
    STRIP "$f" | { LC_ALL=C grep -noE "$AX_TOK" || true; } \
      | LC_ALL=C sed -E "s|^([0-9]+):[^A-Za-z0-9_]?axiom[[:space:]]*(«[^»]*»\|[^[:space:]:({«]*).*|$f:\1:\2|; s|:\$|:?|"
  done
}
lean_de () { find "$@" -name '*.lean' ! -path '*/.lake/*' 2>/dev/null | sort; }
# grep_lista DIR… → grep_axiomas de cada `.lean` de los directorios, leídos por LÍNEAS (con espacios, bien)
grep_lista () { lean_de "$@" | while IFS= read -r f; do grep_axiomas "$f"; done; }

# PRUEBA DE HUMO (ADR-116): con un despojador roto, el contraste y la cuarentena daban «0» sin medir.
# Entrada fija: seis `axiom` reales (con sangría y modificador, con atributo, tras `open … in`, con
# «axiom» DENTRO del nombre, con el nombre en la línea siguiente —sale «?»— y con nombre `«…»`) y seis
# falsos (docstring, comentario, cadena, un identificador que empieza por `axiom`, un literal de nombre y
# un identificador que ACABA en `axiom` tras una letra griega). Si no salen exactamente esos, NO se mide.
HUMO_F=$(mktemp)
printf '%s\n' '/-- axiom falso1 : X -/' '-- axiom falso2 : X' 'def s := "axiom falso3 : X"' \
       '  private axiom real1 : True' '@[simp] axiom real2 : True' 'open Nat in axiom real3 : True' \
       'def axiomInfo := 0' 'axiom real_axiom : True' 'axiom' '  real4 : True' 'def k := `axiom' \
       'def αaxiom : Nat := 1' 'axiom«real5» : True' > "$HUMO_F"
HUMO=$(grep_axiomas "$HUMO_F" | sed 's/.*://' | tr '\n' ' ')
rm -f "$HUMO_F"
if [ "$HUMO" != "real1 real2 real3 real_axiom ? «real5» " ]; then
  echo "  ⚠️  SIN MEDIR — strip-lean.awk o el patrón de \`axiom\` no pasan su prueba de humo («$HUMO»)."
  exit 2
fi

FAIL=0

# ── 1 · El censo del BUILD, medido en el ENTORNO ─────────────────────────────────────────────
echo "════ AXIOMAS DE LEAN, por librería — medidos en el ENTORNO de Lean ════"
if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell."
  echo "      Lánzalo desde PowerShell. Un control que no se ejecuta NO es un control."
  exit 2
fi
# ⚠️ ÁMBITO (ADR-116): el entorno lee los `.olean` que haya; la cifra es la del ÚLTIMO build, y se dice
# de cuándo es. (Se probó a comprobar la frescura por fechas y daba falsos «caducados»: tras cambiar de
# rama, git toca ficheros que Lake no recompila porque el contenido es el mismo.) En la CI el build es
# siempre nuevo, y el contraste con el grep mira el árbol ACTUAL. El barrel `TheoryFramework.lean` no se
# importa: el build no lo compila (`globs := .submodules`).
ULTIMO=$(ls -t .lake/build/lib/lean/FOL.olean .lake/build/lib/lean/FOL/*.olean .lake/build/lib/lean/TheoryFramework/*.olean 2>/dev/null | head -1)
BUILD_FECHA=$([ -n "$ULTIMO" ] && date -r "$ULTIMO" '+%Y-%m-%d %H:%M' 2>/dev/null || echo '¿?')
TMP=$(mktemp -d)
LEANFILE="$TMP/Axiomas.lean"
{
  echo "import Lean"
  echo "import FOL"
  for f in $(lean_de TheoryFramework); do
    m="${f%.lean}"; echo "import ${m//\//.}"
  done
  cat <<'LEANEOF'
open Lean

run_cmd do
  let env ← Lean.getEnv
  let mut nFOL := 0
  let mut nTF := 0
  -- los tres axiomas de Lean que el proyecto acepta; cualquier OTRO axioma ajeno que use una constante
  -- nuestra (`sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, …) es @TRUST
  let estandar : NameSet := ((({} : NameSet).insert ``propext).insert ``Classical.choice).insert ``Quot.sound
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      let lib := if (`FOL).isPrefixOf m then "FOL" else if (`TheoryFramework).isPrefixOf m then "TF" else ""
      if lib == "FOL" then nFOL := nFOL + 1
      if lib == "TF" then nTF := nTF + 1
      if lib != "" then
        if ci matches .axiomInfo _ then logInfo m!"@AX {lib} {n}"
        -- tipo y valor, también el de un teorema (`getUsedConstantsAsSet` lee con `allowOpaque`)
        let usadas := ci.getUsedConstantsAsSet
        if usadas.contains ``sorryAx then logInfo m!"@SORRY {lib} {n}"
        for u in usadas do
          if let some (.axiomInfo _) := env.find? u then
            if !estandar.contains u && u != ``sorryAx then
              match env.getModuleIdxFor? u with
              | some j =>
                let mu := env.header.moduleNames[j.toNat]!
                if !((`FOL).isPrefixOf mu || (`TheoryFramework).isPrefixOf mu) then logInfo m!"@TRUST {lib} {n} {u}"
              | none => logInfo m!"@TRUST {lib} {n} {u}"
        if (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n then logInfo m!"@NATIVO {lib} {n}"
    | none => pure ()
  logInfo m!"@CONST {nFOL} {nTF}"
  -- ¿alguna librería cargada que ningún censo mira? (una nueva, importada por FOL, quedaría fuera)
  for m in env.header.moduleNames do
    if !([`Init, `Std, `Lean, `Lake, `FOL, `TheoryFramework].contains m.getRoot) then logInfo m!"@AJENO {m}"
  logInfo m!"@FIN {env.header.moduleNames.size}"
LEANEOF
} > "$LEANFILE"
SALIDA=$(lake env lean "$LEANFILE" 2>&1)
RC=$?
rm -rf "$TMP"
PLANA=$(printf '%s' "$SALIDA" | tr '\n' ' ' | tr -s ' ')
# (`logInfo` en un `run_cmd` sale como «@FIN N» a secas, o con «…: info: » delante según la versión)
MODS=$(printf '%s\n' "$SALIDA" | grep -oE "(^|info: )@FIN [0-9]+" | grep -oE "[0-9]+$" | head -1)
if [ "$RC" != "0" ] || [ -z "$MODS" ] || [ "$MODS" -le 0 ] 2>/dev/null \
   || printf '%s\n' "$SALIDA" | grep -qE ": error"; then
  echo "  ❌ NO PUDE MEDIR: 'lake env lean' no llegó al final (código $RC). ¿Está construido el árbol?"
  printf '%s\n' "$SALIDA" | grep -m3 -E "error" | sed 's/^/      /' | cut -c1-160
  echo "      (construir antes: desde ../ROBINSON_PlusPlus, lake build \"@FOL/FOL\" \"@FOL/TheoryFramework\")"
  exit 1
fi
ENV_FOL=$(printf '%s' "$PLANA" | grep -oE "@AX FOL [^ ]+" | sed 's/@AX FOL //' | sort -u)
ENV_TF=$(printf '%s' "$PLANA" | grep -oE "@AX TF [^ ]+" | sed 's/@AX TF //' | sort -u)
GREP_FOL=$(grep_axiomas FOL.lean; grep_lista FOL)
GREP_TF=$(grep_axiomas TheoryFramework.lean; grep_lista TheoryFramework)
cuenta () { printf '%s\n' "$1" | sed '/^$/d' | wc -l | tr -d ' '; }
for lib in FOL TheoryFramework; do
  case "$lib" in
    FOL)             ESP=$ESPERADO_FOL; E="$ENV_FOL"; G="$GREP_FOL" ;;
    TheoryFramework) ESP=$ESPERADO_TF;  E="$ENV_TF";  G="$GREP_TF"  ;;
  esac
  NE=$(cuenta "$E"); NG=$(cuenta "$G")
  if [ "$NE" = "$ESP" ]; then
    printf "  ✓ %-18s %2s axiom en el entorno\n" "$lib" "$NE"
  else
    printf "  ✗ %-18s %2s axiom en el entorno — AXIOMS.md dice %s\n" "$lib" "$NE" "$ESP"
    printf '%s\n' "$E" | sed '/^$/d' | head -10 | sed 's/^/      · /'
    FAIL=1
  fi
  if [ "$NG" != "$NE" ]; then
    printf "  ✗ %-18s el grep sin comentarios ve %s y el entorno %s: no cuadran\n" "$lib" "$NG" "$NE"
    printf '%s\n' "$G" | sed '/^$/d' | head -10 | sed 's/^/      · /'
    echo "      ⇒ o hay un \`axiom\` en un módulo que el build no compila, o una forma que el grep no lee."
    FAIL=1
  fi
done
echo "      (entorno de Lean: $MODS módulos cargados, core incluido, del build de $BUILD_FECHA; contraste: grep sobre el código sin comentarios)"

# ── 1bis · `sorry` en el ENTORNO ─────────────────────────────────────────────────────────────
echo
echo "════ sorry EN EL ENTORNO (constantes cuyo tipo o valor nombra sorryAx) ════"
CONSTS=$(printf '%s' "$PLANA" | grep -oE "@CONST [0-9]+ [0-9]+" | head -1)
NCF=$(printf '%s' "$CONSTS" | awk '{print $2}'); NCT=$(printf '%s' "$CONSTS" | awk '{print $3}')
ENV_SORRY=$(printf '%s' "$PLANA" | grep -oE "@SORRY (FOL|TF) [^ ]+" | sed 's/@SORRY //' | sort -u)
if [ -z "$NCF" ] || [ -z "$NCT" ] || [ "$NCF" -le 0 ] || [ "$NCT" -le 0 ]; then
  echo "  ❌ NO PUDE MEDIR: el censo no vio constantes de FOL ($NCF) o de TheoryFramework ($NCT)."
  FAIL=1
elif [ "$(cuenta "$ENV_SORRY")" = "0" ]; then
  echo "  ✓ ninguna usa sorryAx  (de $NCF constantes de FOL y $NCT de TheoryFramework)"
else
  echo "  ✗ $(cuenta "$ENV_SORRY") constante(s) usan sorryAx:"
  printf '%s\n' "$ENV_SORRY" | sed '/^$/d' | head -10 | sed 's/^/      · /'
  FAIL=1
fi

# ── 1ter · CONFIANZA y código NATIVO en el ENTORNO (cuarta revisión de ADR-116 de RPP) ─────────
# El censo de `sorry` sólo miraba `sorryAx`: una constante que use `Lean.ofReduceBool` (confiar en el
# compilador, y con `implemented_by` el compilador puede «demostrar» `False`) pasaba por limpia.
echo
echo "════ CONFIANZA (axiomas del core fuera de los tres de Lean) · NATIVO (implemented_by / extern) · AJENO ════"
TRUST=$(printf '%s' "$PLANA" | grep -oE "@TRUST (FOL|TF) [^ ]+ [^ ]+" | sed 's/@TRUST //' | sort -u)
NATIVO=$(printf '%s' "$PLANA" | grep -oE "@NATIVO (FOL|TF) [^ ]+" | sed 's/@NATIVO //' | sort -u)
AJENO=$(printf '%s' "$PLANA" | grep -oE "@AJENO [^ ]+" | sed 's/@AJENO //' | sort -u)
for par in "TRUST|constante(s) usan un axioma de confianza" "NATIVO|constante(s) con implemented_by o extern" "AJENO|módulo(s) de una librería que ningún censo mira"; do
  var="${par%%|*}"; txt="${par#*|}"
  val="${!var}"
  if [ -z "$val" ]; then
    printf "  ✓ %-8s ninguno\n" "$var"
  else
    printf "  ✗ %-8s %s %s:\n" "$var" "$(cuenta "$val")" "$txt"
    printf '%s\n' "$val" | head -10 | sed 's/^/      · /'
    FAIL=1
  fi
done

# ── 2 · La CUARENTENA, que no se compila: por grep, sin comentarios ──────────────────────────
echo
echo "════ CUARENTENA (fuera del build, pero con cifra publicada) ════"
if [ -d cuarentena ]; then
  TODO_C=$(grep_lista cuarentena)
  RET_C=$(grep_lista cuarentena/librerias-retiradas)
  NC=$(( $(cuenta "$TODO_C") - $(cuenta "$RET_C") ))
  NR=$(cuenta "$RET_C")
  if [ "$NC" = "$ESPERADO_CUAR" ]; then
    printf "  ✓ %-18s %2s axiom  (+%s en librerias-retiradas, muertas)\n" "cuarentena" "$NC" "$NR"
  else
    printf "  ✗ %-18s %2s axiom — este script dice %s\n" "cuarentena" "$NC" "$ESPERADO_CUAR"
    FAIL=1
  fi
else
  echo "  · sin cuarentena/"
fi

# ── 3 · ¿Los cita AXIOMS.md? ─────────────────────────────────────────────────────────────────
echo
echo "════ ¿los cita AXIOMS.md? ════"
if [ ! -f AXIOMS.md ]; then
  echo "  ✗ NO EXISTE AXIOMS.md"; FAIL=1
else
  FALTAN=0
  NOMBRES=$( { printf '%s\n' "$ENV_FOL" "$ENV_TF" | sed 's/.*\.//'; \
               printf '%s\n' "$GREP_FOL" "$GREP_TF" | sed 's/.*://; s/.*\.//'; } | sed '/^$/d' | sort -u)
  while IFS= read -r NOMBRE; do
    [ -n "$NOMBRE" ] || continue
    grep -q "\`$NOMBRE\`" AXIOMS.md || { echo "  ✗ \`$NOMBRE\` no aparece en AXIOMS.md"; FALTAN=1; }
  done <<< "$NOMBRES"
  [ "$FALTAN" = "0" ] && echo "  ✓ todos los axiomas del árbol están documentados"
  [ "$FALTAN" = "1" ] && FAIL=1
fi

echo
echo "════ librerías RETIRADAS: no deben estar en el lakefile ════"
RET=0
for l in FOLPure PropLogic FOL_poli; do
  # (con «» o sin ellas: `lean_lib FOLPure where` también es Lake válido — cuarta revisión)
  if grep -qE "lean_lib[[:space:]]+«?$l»?([[:space:]]|$)" lakefile.lean 2>/dev/null; then
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
