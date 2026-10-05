#!/bin/bash
# check-doc-sync.bash — detecta documentación DESINCRONIZADA del código real.
#
# 📌 PORTADO DESDE ROBINSON_PlusPlus el 2026-09-17 (ADR-061 de RPP). Nace de dos fallos
# reales, ambos caros (AI-GUIDE.md §27 de RPP, memoria `feedback-doc-audit-traps`):
#
#   1. Los documentos de estado se actualizan por su BANNER y no por su CUERPO.
#   2. Se citan como vigentes símbolos que YA NO EXISTEN en el código.
#
# ⭐ Y en FOL no era hipotético: el simulacro previo a adoptarlo encontró TRES desfases
# vivos desde mayo de 2026 («1 sorry (eq/Henkin)» en dos árboles de directorios y
# «✅ Complete (1 sorry pendiente)» en la tabla de fases) que ningún control veía, porque
# hasta hoy NADIE miraba los documentos de FOL — ni los de FOL ni los de RPP.
#
# [A], [C] y [D] son OBJETIVOS y rompen el check. [A2], [B] y [E] son AVISOS que piden
# juicio: hay menciones legítimas de símbolos inexistentes y cifras históricas.
#
# ⛔⛔ ESTE SCRIPT **NO EJECUTA `lake build`**, y no es un olvido — es la regla M-3 del
# proyecto: FOL **no se construye desde FOL** (mezcla oleans con los que ROBINSON_PlusPlus
# genera al compilarlo como dependencia, y produce «incompatible header»). La cifra de jobs
# de FOL la mide y la publica RPP, que sí puede construirlo. Aquí, por tanto, NO hay control
# [A] de jobs, y `--quick` se conserva sólo por compatibilidad de invocación.
#
# Uso:
#   bash check-doc-sync.bash            # comprobación completa
#   bash check-doc-sync.bash --fix-hint # además, sugiere el sed de cada corrección
#
# Salida: 0 si todo cuadra, 1 si hay desincronización.

set -uo pipefail
cd "$(dirname "$0")"

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

QUICK=0
HINT=0
for a in "$@"; do
  case "$a" in
    --quick)     QUICK=1 ;;
    --fix-hint)  HINT=1 ;;
    -h|--help)   sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "opción desconocida: $a" >&2; exit 2 ;;
  esac
done

# ─── 1. VERDAD DEL CÓDIGO ────────────────────────────────────────────────────
# El árbol de FOL son DOS `lean_lib` (`FOL` y `TheoryFramework`) más `FOL/Theorems/`.
CORE=$(ls FOL/*.lean 2>/dev/null | wc -l)
THEO=$(ls FOL/Theorems/*.lean 2>/dev/null | wc -l)
TFW=$(ls TheoryFramework/*.lean TheoryFramework/**/*.lean 2>/dev/null | sort -u | wc -l)
ACTIVE=$((CORE + THEO + TFW))
QUAR=$(ls cuarentena/*.lean 2>/dev/null | wc -l)
# ⚠️ Sin `bc`: no está instalado en Git Bash ni, por defecto, en el runner de CI, y
# `paste -sd+ | bc` fallaba en silencio dejando la cifra VACÍA. `wc -l` sobre las
# líneas que casan cuenta lo mismo y no depende de nada.
# ⛔ 2026-10-03 (ADR-116): antes era `grep "^axiom "`, ciego a `private`/`@[…]`/sangrados y crédulo con
# los docstrings. Ahora es el mismo patrón que `check-axioms.bash` (de FOL), sobre el código sin
# comentarios (`strip-lean.awk`). El censo autoritativo, por entorno, es el de `check-axioms.bash`.
# ⛔⛔ 2026-10-04 (ADR-116 de RPP, segunda revisión): y la primera versión de esa línea daba SIEMPRE 0.
# Donde iba la continuación de línea había un `\n` LITERAL (la cadena de herramientas se comió la
# barra al escribirla): `find` recibía «\n» como un camino más y fallaba, y el `|| true` del final
# se tragaba el fallo. Como el árbol tiene de verdad 0 `axiom`, la cifra cuadraba con los documentos
# y nadie lo vio: un `axiom` nuevo habría dado VERDE. Ahora la cuenta es una función que DEVUELVE su
# fallo, y antes de medir el árbol mide un fixture con TRES `axiom` reales y cinco señuelos: si no
# salen 3, no se mide (y no medir es rojo). El alcance incluye ya el barrel `TheoryFramework.lean`.
# 🔑 *Un `|| true` al final de una tubería convierte «no he podido medir» en «cero».*
# ⛔ Y desde la tercera revisión (2026-10-04): (1) se cuenta el TOKEN `axiom` en todo el código
# despojado, no sólo a principio de línea —`open Nat in axiom x`, `def t := 0 axiom x` o el nombre en la
# línea siguiente son declaraciones que el patrón anclado no veía; en código, `axiom` sólo declara—;
# (2) el fixture EJERCE el despojador: señuelos que empiezan línea DENTRO de un docstring, de una
# cadena de dos líneas y de un comentario anidado (el patrón anclado de antes los rechazaba aunque no
# se despojara nada), y `axiom` reales detrás de una comilla escapada, de `'"'`, de una interpolación y
# de una cadena en bruto: si el despojador falla en cualquiera, la cifra no sale.
# (cuarta revisión: la frontera excluye la comilla invertida —`` `axiom `` es un literal de nombre— y los
#  bytes de continuación UTF-8 —`αaxiom` es UN identificador—, y tras `axiom` vale también `«`; el fixture
#  tiene hoy NUEVE `axiom` reales, y si no salen 9 no se mide)
AX_TOK="(^|[^A-Za-z0-9_'.«\`"$'\x80-\xbf'"])axiom([[:space:]«]|$)"
cuenta_axiomas () {   # $@ = caminos; imprime la cifra, o nada y estado 2 si no ha podido medir
  local p n
  for p in "$@"; do [ -e "$p" ] || return 2; done
  [ -n "$(find "$@" -name '*.lean' ! -path '*/.lake/*' -print -quit)" ] || return 2
  n=$(find "$@" -name '*.lean' ! -path '*/.lake/*' -print0 \
        | xargs -0 env LC_ALL=C awk -f strip-lean.awk \
        | { LC_ALL=C grep -oE "$AX_TOK" || [ $? -eq 1 ]; } | wc -l) || return 2
  printf '%s\n' "$n" | tr -d ' '
}
AX_FIX=$(mktemp -d)
cat > "$AX_FIX/Fixture.lean" <<'EOF'
/-- un docstring
axiom senuelo1 : True
-/
axiom real1 : True
-- axiom senuelo2 : True
  @[simp] private axiom real2 : True
def s := "una cadena de dos líneas
axiom senuelo3 : True"
/-- doc -/ axiom real3 : True
/- /- anidado -/
axiom senuelo4 : True -/
def q := "comilla: \"" axiom real4 : True
def c := '"' axiom real5 : True
def i := s!"{1}" axiom real6 : True
def r := r#"x"# axiom real7 : True
open Nat in axiom real8 : True
axiom«real9» : True
theorem u : True := trivial -- axiom senuelo5
def k := `axiom
def αaxiom : Nat := 1
EOF
AXIOMS=""
if [ "$(cuenta_axiomas "$AX_FIX" || true)" = "9" ]; then
  AXIOMS=$(cuenta_axiomas FOL/ TheoryFramework/ FOL.lean TheoryFramework.lean || true)
fi
rm -rf "$AX_FIX"
AXIOMS_MISSING=0
[ -n "$AXIOMS" ] || AXIOMS_MISSING=1
# ⚠️ El conteo de `sorry` se DELEGA en check-sorry.bash y no se reimplementa aquí: qué
# cuenta como `sorry` (token de código, fuera de comentarios y de literales) es una
# definición delicada, y tenerla en dos sitios garantiza que se separen.
# ⚠️⚠️ Esta extracción estuvo ROTA POR DOS SITIOS A LA VEZ hasta el 2026‑09‑11:
#   (1) el reemplazo del `sed` era un BYTE DE CONTROL 0x01 en lugar de la
#       retro‑referencia (backslash‑uno), así que de casar habría escrito un SOH
#       donde va un número. ⭐ Y NO fue una errata: escribir esa
#       secuencia a través de la cadena de herramientas la CONVIERTE en 0x01 — se
#       reprodujo sola al arreglarlo. Por eso aquí no se usa ninguna retro‑referencia:
#       se extrae con `grep -oE | grep -oE`, como ya se hacía con JOBS;
#   (2) el patrón sólo cubría la rama «⚠️  Total: N sorry», y con CERO sorry
#       `check-sorry.bash` imprime «✅ No sorry found.» ⇒ el `sed` NO casaba NUNCA y la
#       línea siguiente fijaba SORRY=0 POR DEFECTO.
# ⇒ El «0 sorry» de todos los banners se comparaba contra una CONSTANTE, no contra una
# medición: [A] habría dado verde con el árbol lleno de `sorry`. Es la sexta causa de
# [[feedback-controles-que-no-comprueban]], y la única que estaba en el propio control.
# Ahora se leen LAS DOS ramas y, si no aparece ninguna, se AVISA (§27.1).
SORRY_OUT=$(bash check-sorry.bash 2>/dev/null || true)
SORRY_MISSING=0
# ⛔ 2026-10-04 (tercera revisión): se leen las LÍNEAS DE RESUMEN, enteras. check-sorry reimprime cada
# línea fuente con `sorry`, y una que contuviera «No sorry found» hacía SORRY=0 con un `sorry` real.
if printf '%s\n' "$SORRY_OUT" | LC_ALL=C grep -qxF '✅ No sorry found.'; then
  SORRY=0
elif printf '%s\n' "$SORRY_OUT" | LC_ALL=C grep -qE '^⚠️  Total: [0-9]+ sorry in '; then
  SORRY=$(printf '%s\n' "$SORRY_OUT" | LC_ALL=C grep -oE '^⚠️  Total: [0-9]+' | grep -oE '[0-9]+$' | head -1)
else
  SORRY=0
  SORRY_MISSING=1
fi

# ⛔ M-3: aquí NO se ejecuta `lake build`. Ver la cabecera. `JOBS` queda vacío a propósito
# y el control [A] de jobs no existe en esta copia — lo hace RPP, que sí construye FOL.
JOBS=""
LAKE_MISSING=0

echo "════ VERDAD DEL CÓDIGO ════"
printf "  módulos activos : %s  (FOL/ %s + FOL/Theorems/ %s + TheoryFramework/ %s)\n" "$ACTIVE" "$CORE" "$THEO" "$TFW"
printf "  cuarentena      : %s\n" "$QUAR"
printf "  axiom de Lean   : %s\n" "$AXIOMS"
printf "  sorry           : %s\n" "$SORRY"
echo "  build jobs      : no se mide aquí (M-3: FOL no se construye desde FOL)"
[ "$SORRY_MISSING" = "1" ] && echo "  ⚠️  sorry         : SIN MEDIR — check-sorry.bash no dijo ni 'No sorry found' ni 'Total: N sorry'."
[ "$AXIOMS_MISSING" = "1" ] && echo "  ⚠️  axiom de Lean : SIN MEDIR — el autotest de cuenta_axiomas no dio 9 (¿strip-lean.awk, LC_ALL?)."
echo

# Documentos AUTORITATIVOS: los que describen el ESTADO ACTUAL y por tanto deben cuadrar.
# Quedan fuera, y con razón, los de diario, diseño e historia (CHANGELOG, GODEL-*-DESIGN,
# PLAN-*, THOUGHTS, MINIMAL-AXIOMS…): sus cifras y símbolos son históricos POR DISEÑO.
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md NEXT-STEPS.md AI-GUIDE.md"
AUTHORITATIVE="$AUTHORITATIVE cuarentena/README.md"
DOCS="$AUTHORITATIVE"
FAIL=0

# ⚠️ SI NO SE PUEDE MEDIR, ES ROJO (añadido el 2026-09-17, medido en PeanoRF).
# Hasta hoy `LAKE_MISSING`/`SORRY_MISSING` sólo IMPRIMÍAN «SIN MEDIR» y el script seguía y
# salía con 0: anunciaba verde sobre cifras que nadie había comprobado. En PeanoRF eso
# llegó a empujar un commit con el check en rojo, creyéndolo verde.
# 🔑 Un control tiene TRES resultados —pasa, falla, NO HE PODIDO COMPROBARLO— y colapsar
# el tercero en el primero es lo que lo convierte en decoración. El único verde sin medida
# es el que se pide a mano con `--quick`, y ése se anuncia como tal.
if [ "$SORRY_MISSING" != "0" ] || [ "$AXIOMS_MISSING" != "0" ]; then
  FAIL=1
fi

# ─── 2. CIFRAS OBSOLETAS ─────────────────────────────────────────────────────
# CHANGELOG.md se excluye: es un diario, sus cifras son históricas por diseño.
# Las líneas marcadas como históricas también (fecha ISO al principio, o marcador).
echo "════ [A] CIFRAS ════"
A_FAIL=0
# ALCANCE: sólo la REGIÓN DE CABECERA (primeras 100 líneas) de cada doc autoritativo.
# Ahí viven el banner y las tablas resumen — lo que AFIRMA el estado actual. Más abajo
# están los registros de logros, donde «93 jobs» es historia correcta, no un error.
# Esta acotación es la que hace utilizable el control: sin ella, los diarios de
# `NEXT-STEPS.md` disparan una docena de falsos positivos y nadie vuelve a mirarlo.
HEADREGION=$(mktemp)
: > "$HEADREGION"
for d in $DOCS; do
  [ -e "$d" ] || continue
  head -100 "$d" | sed "s|^|$d:|" >> "$HEADREGION"
done

# ⚠️ Los patrones se pasan SIEMPRE entre comillas SIMPLES: un backtick dentro de
#    comillas dobles lo ejecuta bash como sustitución de comando y el patrón queda roto.
check_num () {   # $1 = regex con grupo numérico   $2 = valor correcto   $3 = etiqueta
  local pat="$1" good="$2" label="$3" hits
  # Se descartan: menciones históricas, aproximaciones (~40), rangos (40-50) y ejemplos.
    # ⭐ AÑADIDO al portar a FOL (2026-09-17): una cifra DENTRO de «comillas latinas» es una
  # CITA, no una afirmación. Los avisos de estado de FOL usan el formato
  # «lo que decía | lo medido», y sin esta exclusión los CUATRO daban falso positivo
  # citando textualmente el error que la propia fila está corrigiendo.
  # 🔑 Una cifra entrecomillada la está diciendo OTRO; el control mira lo que el doc AFIRMA.
hits=$(grep -nE "$pat" "$HEADREGION" 2>/dev/null          | grep -viE "hist[oó]rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|20[0-9]{2}-[0-9]{2}-[0-9]{2}|~|p\. ej|ejemplo|umbral|[0-9]+-[0-9]+|«[^»]*[0-9]" || true)
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local n; n=$(echo "$line" | grep -oE "$pat" | grep -oE "[0-9]+" | head -1)
    if [ -n "$n" ] && [ "$n" != "$good" ]; then
      echo "  ✗ $label: dice $n, real $good"
      echo "      ${line:0:150}"
      A_FAIL=1
    fi
  done <<< "$hits"
  # ⚠️ Un patrón sin ninguna aparición NO está comprobando nada, y da verde. Es el peor
  # resultado posible para un control cuyo cometido es que no te fibres de los docs: por eso
  # se avisa en vez de callar. Si sale este aviso, o el fraseo del doc cambió, o el patrón
  # está mal — en los dos casos hay que tocar algo.
  [ -z "$hits" ] && echo "  ⚠️  $label: la frase no aparece en ningún doc autoritativo — control VACÍO"
  return 0
}
check_num "[0-9]+ módulos activos" "$ACTIVE" "módulos activos"
check_num "[0-9]+ (módulos )?en \`cuarentena/\`" "$QUAR" "cuarentena"
[ -n "$AXIOMS" ] && check_num '[0-9]+ `?axiom`? de Lean' "$AXIOMS" "axiom de Lean"
check_num '[0-9]+ sorrys?' "$SORRY" "sorry"
rm -f "$HEADREGION"
[ "$A_FAIL" = "0" ] && echo "  ✓ sin cifras obsoletas" || FAIL=1

# ─── 2bis. CIFRAS EN EL **CUERPO** ───────────────────────────────────────────
# ⭐ Añadido el 2026-09-10h, y lo pidió una auditoría externa (`doc/book/AUDITORIA-2026-09-10.md`
# §5 y R3), que midió la causa raíz de la deriva documental del proyecto:
#
#     «check-doc-sync.bash:108 — ALCANCE: sólo la REGIÓN DE CABECERA (primeras 100 líneas).
#      Eso explica el patrón entero. El commit 50e8864 pudo declarar la sincronía en verde con
#      ocho contradicciones vivas a partir de la línea 218. No es que nadie mire: es que el
#      control mira sólo el banner, y el banner es justamente la parte que sí se actualiza.
#      Auditar el banner es auditar lo que ya está bien.»
#
# ⚠️ Y la acotación NO era un descuido: sin ella, los diarios de `NEXT-STEPS.md` disparan una
# docena de falsos positivos y el control deja de usarse. Así que el cuerpo entra como **AVISO**,
# igual que [B]: se ve, pide juicio, y no rompe. Lo que rompe sigue siendo la cabecera.
echo ""
echo "════ [A2] CIFRAS EN EL CUERPO — AVISO, requiere juicio ════"
BODYREGION=$(mktemp)
: > "$BODYREGION"
for d in $DOCS; do
  [ -e "$d" ] || continue
  tail -n +101 "$d" | sed "s|^|$d:|" >> "$BODYREGION"
done

A2_HITS=0
warn_num () {   # $1 = regex con grupo numérico   $2 = valor correcto   $3 = etiqueta
  local pat="$1" good="$2" label="$3" hits
  hits=$(grep -nE "$pat" "$BODYREGION" 2>/dev/null          | grep -viE "hist[oó]rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|retirad|20[0-9]{2}-[0-9]{2}-[0-9]{2}|20[0-9]{2}‑[0-9]{2}‑[0-9]{2}|~|p\. ej|ejemplo|umbral|[0-9]+-[0-9]+|«[^»]*[0-9]" || true)
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local n; n=$(echo "$line" | grep -oE "$pat" | grep -oE "[0-9]+" | head -1)
    if [ -n "$n" ] && [ "$n" != "$good" ]; then
      echo "  ⚠️  $label: dice $n, real $good"
      echo "      ${line:0:150}"
      A2_HITS=$((A2_HITS+1))
    fi
  done <<< "$hits"
  return 0
}
warn_num "[0-9]+ módulos activos" "$ACTIVE" "módulos activos"
[ -n "$AXIOMS" ] && warn_num '[0-9]+ `?axiom`? de Lean' "$AXIOMS" "axiom de Lean"
warn_num '[0-9]+ sorrys?' "$SORRY" "sorry"
rm -f "$BODYREGION"
if [ "$A2_HITS" = "0" ]; then
  echo "  ✓ el cuerpo tampoco tiene cifras obsoletas"
else
  echo "  ⚠️  $A2_HITS línea(s) en el CUERPO con cifras que no cuadran."
  echo "      ¿es una afirmación de estado ACTUAL (⇒ corregir) o un registro histórico"
  echo "      sin marcar (⇒ marcarlo: fecha ISO, «previo», «era», «histórico»)?"
fi

echo ""
echo "════ [E] FRESCURA DEL TITULAR — ROJO (objetivo: lo decide git) ════"
# ⭐ Añadido el 2026-09-11 por la auditoría (hallazgo F-2): [A] comprueba las CIFRAS del banner
# y [D] que EXISTA una marca de tiempo, pero nadie comprobaba que la marca fuera CIERTA.
#
# ⛔⛔ REARMADO EL 2026-09-18 (auditoría A3, ADR-072). Estaba desarmado por TRES vías y daba
# verde sin comprobar nada:
#   1. La referencia era la entrada más reciente de CHANGELOG.md — un documento que un HUMANO
#      tiene que actualizar. Congelado en 2026-05-16 con **111 commits** detrás, `NEWEST` se
#      quedaba viejo y NINGÚN doc podía estar «por detrás»: aprobaba siempre.
#   2. `E_HITS` no tocaba `FAIL` en ninguna rama, ni en la de «control VACÍO».
#   3. Leía la fecha con `head -12`, y `**Last updated:**` vive en la línea 22-38 ⇒ medía la
#      fecha de OTRA cosa (el aviso histórico de la cabecera).
#
# 🔑 *Un control cuya REFERENCIA es un documento que alguien tiene que mantener se pudre con
# él. La referencia tiene que CALCULARSE.* Aquí se calcula, y por documento: la fecha del
# ÚLTIMO COMMIT QUE TOCÓ ESE DOCUMENTO, que no se puede quedar vieja.
#
# ⚠️ LA TABLA DE DEUDA, y por qué existe: al rearmarlo, la medición dio 21 defectos en 24
# documentos — deuda ANTERIOR, acumulada mientras el control estaba ciego. Ponerlo en rojo de
# golpe habría dejado el repo en rojo indefinidamente; callarla habría sido volver al verde
# falso. Se declara, como en `check-warnings.bash` (ADR-065), y el control **ROMPE EN LOS DOS
# SENTIDOS**: si un doc NO declarado falla, rojo; y si un doc declarado ya está bien, también
# rojo — *la deuda se saldó, quítala de la tabla*. Así la cifra sólo puede BAJAR.
read -r -d '' E_DEUDA <<'EOF'
DECISIONS.md
AI-GUIDE.md
cuarentena/README.md
EOF

# ⛔ GUARDA DEL CLON SUPERFICIAL (2026-09-18, ADR-072). En `--depth 1`, `git log -1 -- <f>`
# devuelve HEAD para TODOS los ficheros ⇒ este control mediría basura y la CI se pondría roja
# con falsos positivos. Pasó: la primera ejecución en CI. No se calla, se ROMPE diciendo qué
# hacer. 🔑 *Un control que depende de la historia de git mide OTRA COSA bajo un clon
# superficial, y la diferencia no se ve en local.*
if [ "$(git rev-parse --is-shallow-repository 2>/dev/null)" = "true" ]; then
  echo "  ❌ CLON SUPERFICIAL: \`git log\` no tiene historia, este control no puede medir."
  echo "      Arreglo: \`fetch-depth: 0\` en el paso de checkout del workflow."
  FAIL=1
fi
E_BAD=0      # documentos que fallan y NO estaban declarados
E_SALDADA=0  # documentos declarados que ya están bien ⇒ hay que quitarlos de la tabla
E_DECL=0     # deuda declarada que sigue vigente
for d in $DOCS; do
  [ -e "$d" ] || continue
  GIT_DATE=$(git log -1 --format=%ad --date=short -- "$d" 2>/dev/null)
  LU=$(grep -m1 -iE "^\*\*Last updated" "$d" 2>/dev/null \
       | grep -ohE "20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}" | sed "s/‑/-/g" | head -1)
  EN_TABLA=0
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    [ "$t" = "$d" ] && EN_TABLA=1
  done <<< "$E_DEUDA"

  ESTADO="ok"
  MOTIVO=""
  if [ -z "$LU" ]; then
    ESTADO="mal"; MOTIVO="sin marca \`**Last updated:**\`"
  elif [ -z "$GIT_DATE" ]; then
    ESTADO="mal"; MOTIVO="sin historia en git"
  elif [ "$LU" \< "$GIT_DATE" ]; then
    ESTADO="mal"; MOTIVO="la marca dice $LU y el último commit que lo tocó es $GIT_DATE"
  fi

  if [ "$ESTADO" = "mal" ] && [ "$EN_TABLA" = "0" ]; then
    echo "  ❌ $d: $MOTIVO"
    E_BAD=$((E_BAD+1))
  elif [ "$ESTADO" = "mal" ]; then
    E_DECL=$((E_DECL+1))
  elif [ "$EN_TABLA" = "1" ]; then
    echo "  ❌ $d: la deuda ESTÁ SALDADA — quítalo de la tabla E_DEUDA de este script."
    E_SALDADA=$((E_SALDADA+1))
  fi
done
echo "  deuda declarada: $E_DECL   ·   sin declarar: $E_BAD   ·   saldadas sin quitar: $E_SALDADA"
if [ "$E_BAD" = "0" ] && [ "$E_SALDADA" = "0" ]; then
  echo "  ✓ ninguna marca de tiempo miente fuera de la deuda declarada"
else
  echo "      ⚠️ El titular es una FRASE: [A] no lo ve. Al actualizar la marca, comprobar que lo"
  echo "      que el titular AFIRMA sigue siendo cierto, no sólo que sus cifras cuadren."
  FAIL=1
fi

# ─── 3. SÍMBOLOS MUERTOS ─────────────────────────────────────────────────────
# Un símbolo está MUERTO si se cita en un doc AUTORITATIVO pero ninguna declaración
# del árbol activo se llama así.
#
# Dos calibraciones aprendidas al estrenar este control (2026-08-23):
#   * Sólo se miran los docs AUTORITATIVOS (los que describen el estado actual). Los
#     de diseño e historia — MINIMAL-AXIOMS, THOUGHTS, GODEL-*-DESIGN, PLAN-* — citan
#     por diseño cosas que ya no están, y marcarlos sería ruido.
#   * (✏️ 2026-10-03, ADR-116 de RPP: REVOCADA.) Se comparaba por PREFIJO («la prosa abrevia»), y
#     eso absolvía a todo nombre que empezara como uno vivo. Hoy se casa el nombre EXACTO, y una
#     familia se cita con `_` final (`ax_C3_`): ver (2) más abajo.
echo
echo "════ [B] SÍMBOLOS MUERTOS — AVISO, requiere juicio ════"
echo "   (no rompe el check: hay menciones legítimas en secciones de diseño e historia.)"
B_FAIL=0
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md NEXT-STEPS.md AI-GUIDE.md"
AUTHORITATIVE="$AUTHORITATIVE cuarentena/README.md"
# Marcadores que hacen LEGÍTIMA la mención de un símbolo inexistente:
#   (a) se declara retirado;  (b) es hipotético/propuesto/descartado;  (c) va en una
#   entrada fechada (histórico por diseño).
DEAD_MARKER='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|F7a|histórico|ANTERIORES|🗑️|muert|Aquí vivía|tampoco existe|inexistente|desapareci|ya no son|se borró'
DEAD_MARKER="$DEAD_MARKER"'|propuest|candidat|hipot(e|é)tic|har(i|í)a falta|si se |habr(i|í)a que|añadir |descartad|no existe|NO EXISTE|sin materializar|20[0-9][0-9]-[0-9][0-9]-[0-9][0-9]'
#   (d) es un OBJETIVO declarado, no una afirmación de que ya está.
DEAD_MARKER="$DEAD_MARKER"'|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la'
DECLS=$(mktemp)
# El árbol de declaraciones incluye `cuarentena/`: esos símbolos EXISTEN (están fuera
# del build, no borrados), y los docs los discuten con razón.
# ⚠️ Se incluye `../ROBINSON_PlusPlus/` por si los docs de FOL citan símbolos VIVOS de RPP con
# los prefijos de [B]. Medido el 2026‑10‑02: hoy no citan ninguno (cero `prf_`/`goedel_`; los
# cuatro `ax_` citados están retirados), y el alcance sólo hace pasar por vivo a
# `ax_list_induction` —retirado por ADR‑115 de RPP— por dos causas: [B] no salta comentarios
# (`sondeos/` de RPP lo nombra como `axiom ax_list_induction` en la prosa de un docstring) y casa por
# PREFIJO (`ax_list_induction_refutable`; la prosa abrevia). 🔑 Un control con el alcance
# equivocado no comprueba: INVENTA.
# ⚠️⚠️ Y si el hermano NO está, se DICE. Sin él [B] daría por muertos los símbolos VIVOS de RPP
# que los docs de FOL citaran, y un aviso que siempre sale es un aviso que nadie lee.
# 🔑 Un control tiene TRES resultados — pasa, falla, NO HE PODIDO COMPROBARLO — y el tercero
# se anuncia, no se colapsa en el primero.
# ⭐ `RPP_DIR` permite apuntar al hermano desde donde esté: en la CI, `actions/checkout`
# no admite un `path:` fuera del workspace, así que RPP se clona DENTRO y se pasa aquí.
SIBLING="${RPP_DIR:-../ROBINSON_PlusPlus}"
# ⛔ 2026-10-04 (tercera revisión): el hermano se reconoce por su CONTENIDO. `actions/checkout` crea el
# directorio y hace `git init` ANTES de traer nada, y si falla no lo borra: con `[ -d "$SIBLING" ]`, un
# checkout fallido daba «NO PUDE MEDIR» (rojo) en vez de alcance reducido.
SIBLING_OK=0
[ -d "$SIBLING/ROBINSON_PlusPlus" ] && SIBLING_OK=1
if [ "$SIBLING_OK" = "1" ]; then
  # El alcance de RPP es su árbol ACTIVO —la librería y su cuarentena—, no sus sondeos ni `Probe/`
  # (que en local existe y en el clon `_rpp` de la CI no): ADR-116.
  SCOPE="FOL/ TheoryFramework/ FOL.lean cuarentena/ $SIBLING/ROBINSON_PlusPlus/ $SIBLING/ROBINSON_PlusPlus.lean $SIBLING/cuarentena/"
else
  SCOPE="FOL/ TheoryFramework/ FOL.lean cuarentena/"
  echo "  ⚠️  ALCANCE REDUCIDO: no está ../ROBINSON_PlusPlus ⇒ los símbolos VIVOS de RPP que estos"
  echo "      docs citaran saldrían aquí como MUERTOS. No es un hallazgo: es un hueco."
fi
# ⛔⛔ 2026-10-03 (ADR-116 de RPP): dos defectos de este bloque, medidos. (1) Las declaraciones se
# sacaban del texto ENTERO, comentarios incluidos: un nombre que sólo aparece en prosa (p. ej. el
# «axiom ax_list_induction» de un docstring de RPP) pasaba por VIVO. Ahora salen del código SIN
# comentarios ni cadenas (`strip-lean.awk`), y con todas las palabras clave de declaración.
# (2) Se casaba por PREFIJO («la prosa abrevia»): `ax_list_induction` pasaba por vivo porque existe
# `ax_list_induction_refutable`, y `d3_prf` porque existe `d3_prf_real`. Ahora se casa el nombre
# EXACTO; la abreviatura de una FAMILIA se escribe con `_` final (`prf_tc_`), y sólo ésa casa por
# prefijo. 🔑 *Un control que casa por prefijo absuelve a todo nombre que empiece igual que uno vivo.*
# (3) 2026-10-03, v2 (revisión adversarial): el NOMBRE se toma entero (`prf_foo₀`, `Prf.prf_bar`: antes
# se cortaba en el primer carácter no ASCII o en el primer `.`) y se guarda también su último
# componente; el ALCANCE es explícito (antes entraban `auditoria/`, las librerías muertas y, en local,
# `Probe/`, que la CI no tiene); y si la lista sale vacía o sin un nombre que existe seguro, NO se mide.
# (4) 2026-10-04, segunda revisión (ADR-116 de RPP): (a) las CITAS se leen enteras también:
# calificadas (`Foo.ax_bar`, que vale por su último componente) y con caracteres no ASCII (`prf_zz₀`);
# antes el patrón se paraba en el `.` o en el subíndice y esas citas no las miraba nadie; (b) `def
# prf_univ.{u}` declara `prf_univ` (antes, `prf_univ.` y un nombre vacío); (c) una sola pasada de awk
# sobre los documentos, y los marcadores por BYTES (un acento va con `(e|é)`: en modo byte un corchete
# casa UN byte); (d) el control positivo es por NOMBRE: con el umbral de 1000 declaraciones, FOL sin
# el hermano (990) daba «NO PUDE MEDIR» — y además seguía y decía «✓».
# ⚠️ Lo que NO ve: los constructores y los campos de estructura no son declaraciones de primer nivel,
# así que citar uno sale como MUERTO — falso aviso, nunca falso verde; se arregla citando el tipo.
DECL_RE="(^|[^A-Za-z0-9_'.])(theorem|lemma|def|abbrev|axiom|opaque|instance|structure|inductive|class) +[^[:space:]:({[]+"
NOMBRES='{n = $NF; sub(/[.]$/, "", n); if (n == "") next; print n; k = n; sub(/.*[.]/, "", k); if (k != n && k != "") print k}'
B_SALIDA=$(mktemp)
find $SCOPE -name '*.lean' ! -path '*/.lake/*' ! -path '*/librerias-retiradas/*' -print0 2>/dev/null \
  | xargs -0 env LC_ALL=C awk -f strip-lean.awk | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C sort -u > "$DECLS"
B_MEDIDO=1
B_SUELO=500; B_TESTIGOS="derives0_soundness"
[ "$SIBLING_OK" = "1" ] && { B_SUELO=1000; B_TESTIGOS="derives0_soundness goedel_first_prf"; }
B_FALTA=""
for w in $B_TESTIGOS; do grep -qxF "$w" "$DECLS" || B_FALTA="$B_FALTA $w"; done
if [ "$(wc -l < "$DECLS" | tr -d ' ')" -lt "$B_SUELO" ] || [ -n "$B_FALTA" ]; then
  echo "  ❌ NO PUDE MEDIR [B]: $(wc -l < "$DECLS" | tr -d ' ') declaraciones (suelo $B_SUELO), y faltan:${B_FALTA:- ninguna} (¿strip-lean.awk?)."
  FAIL=1; B_FAIL=1; B_MEDIDO=0
fi
B_DOCS=""
for d in $AUTHORITATIVE; do [ -f "$d" ] && B_DOCS="$B_DOCS $d"; done
if [ "$B_MEDIDO" = "1" ]; then
  LC_ALL=C awk -v MARK="$DEAD_MARKER" '
    BEGIN { CAND = "`([A-Z][A-Za-z0-9_]*[.])*(prf_|pcc_|goedel_|godel|d[123]_|repr_|ax_)([A-Za-z0-9_'"'"'!?]|[\303-\337][\200-\277]|\342(\202|\204|\205|\261)[\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])+`" }
    FILENAME == ARGV[1] { vivo[$0] = 1; next }
    {
      s = $0
      # un carácter de nombre: ASCII, o en UTF-8 una letra (2 bytes), un subíndice, un letterlike, ⱼ,
      # el griego extendido o el alfabeto matemático — NO la puntuación general (`1‑3`, `a–b`, `…`)
      while (match(s, CAND)) {
        t = substr(s, RSTART + 1, RLENGTH - 2); s = substr(s, RSTART + RLENGTH)
        k = t; sub(/^([A-Z][A-Za-z0-9_]*[.])*/, "", k)
        # los axiomas objeto son snake_case: `ax_UpperCamel` es un PLACEHOLDER de convención
        # de nombres (`ax_TagDescriptor`), no un símbolo
        if (k ~ /^ax_[A-Z]/) continue
        if ((t in vivo) || (k in vivo)) continue
        if (k ~ /_$/) {
          if (!(k in fam)) { fam[k] = 0; for (v in vivo) if (index(v, k) == 1) { fam[k] = 1; break } }
          if (fam[k]) continue
        }
        # el marcador se mira en la línea con las CITAS en blanco: un nombre muerto que contenga un
        # marcador (`prf_x_muerto`, `ax_medir`) no puede eximirse a sí mismo (tercera revisión)
        l = $0; gsub(CAND, "``", l)
        if (l ~ MARK) continue
        print k "|" t "|" FILENAME ":" FNR ":" $0
      }
    }' "$DECLS" $B_DOCS > "$B_SALIDA"
  cut -d'|' -f1 "$B_SALIDA" | LC_ALL=C sort -u | while IFS= read -r k; do
    echo "  ✗ \`$k\` no existe en el árbol activo, y se cita sin marcar como retirado:"
    awk -F'|' -v k="$k" '$1 == k' "$B_SALIDA" | head -2 | cut -d'|' -f3- | sed 's/^/      /' | cut -c1-140
  done
  [ -s "$B_SALIDA" ] && B_FAIL=1
fi
rm -f "$DECLS" "$B_SALIDA"
# [B] NO marca FAIL: es un aviso. [A], [C] y [D] sí son objetivos y sí lo marcan (y «NO PUDE MEDIR»
# también: un control que no ha medido no avisa de nada).
# Razón: un control que grita lobo se acaba ignorando, y ése era justo el fallo que
# este script existe para evitar.
if [ "$B_MEDIDO" = "0" ]; then
  echo "  ❌ [B] SIN MEDIR"
elif [ "$B_FAIL" = "0" ]; then
  echo "  ✓ ningún símbolo muerto citado como vigente"
else
  echo "  ⚠️  revisar los de arriba: ¿es una afirmación de que YA ESTÁ, o una mención histórica/planificada?"
fi

# ─── 4. PROYECCIÓN: ¿está cada módulo en el catálogo? ────────────────────────
echo
echo "════ [C] PROYECCIÓN (AI-GUIDE §1/§14) ════"
C_FAIL=0
# ⚠ Se comprueba contra §6 (Exports), que es lo que AI-GUIDE §14 exige de verdad: no basta
# con que el nombre aparezca en la tabla de módulos.
# ⚠ Frontera de palabra OBLIGATORIA, y la RUTA y no el basename:
#   • con `grep -F "Eq.lean"` el módulo `Theorems/Eq.lean` daba VERDE porque "Eq.lean" es
#     subcadena de "DecEq.lean";
#   • con el basename, `Deduction.lean` y `Theorems/Deduction.lean` eran el MISMO control,
#     y una sola entrada absolvía a los dos.
# 🔑 Un control que casa por subcadena no comprueba: ABSUELVE.
if [ -f REFERENCE.md ]; then
  FOLEXP=$(sed -n '/^## 6\. Exports/,/^## 7\./p' REFERENCE.md)
  for f in FOL/*.lean FOL/Theorems/*.lean; do
    [ -e "$f" ] || continue
    m=${f#FOL/}; m=${m%.lean}
    [ "$m" = "FOL" ] && continue
    case "$m" in
      */*) PAT="(^|[^A-Za-z0-9_])$m\.lean" ;;
      *)   PAT="(^|[^A-Za-z0-9_/])$m\.lean" ;;
    esac
    if ! printf '%s' "$FOLEXP" | grep -qE "$PAT"; then
      echo "  ✗ FOL/$m NO está proyectado en REFERENCE.md §6 (AI-GUIDE §14)"
      C_FAIL=1
    fi
  done
else
  echo "  ⚠️  no hay REFERENCE.md — control VACÍO"
fi
# ⛔⛔ `TheoryFramework` va con la MISMA vara que `FOL/`: contra §6 y por RUTA con frontera
# de palabra. Con el `basename` que tenía RPP, CUATRO de sus seis módulos daban VERDE por
# SUBCADENA (`Logic`, `Theory`, `Properties` y `FOL` aparecen sueltos por todo REFERENCE.md)
# estando los SEIS sin proyectar. Es la novena causa otra vez: casar por subcadena ABSUELVE.
if [ -f REFERENCE.md ]; then
  for f in TheoryFramework/*.lean TheoryFramework/Instances/*.lean; do
    [ -e "$f" ] || continue
    if ! printf '%s' "$FOLEXP" | grep -qE "(^|[^A-Za-z0-9_])$f"; then
      echo "  ✗ $f NO está proyectado en REFERENCE.md §6 (AI-GUIDE §14)"
      C_FAIL=1
    fi
  done
fi
for f in cuarentena/*.lean; do
  [ -e "$f" ] || continue
  m=$(basename "$f" .lean)
  grep -q "$m" cuarentena/README.md 2>/dev/null || { echo "  ✗ $m (cuarentena) sin listar en su README"; C_FAIL=1; }
done
[ "$C_FAIL" = "0" ] && echo "  ✓ todo módulo aparece en su catálogo" || FAIL=1

# ─── 5. MARCAS DE TIEMPO (AI-GUIDE §22: YYYY-MM-DD HH:MM) ───────────────────
echo
echo "════ [D] MARCAS DE TIEMPO ════"
D_FAIL=0
for f in REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md; do
  [ -e "$f" ] || continue
  grep -qE '\*\*(Last updated|Última actualización):\*\*' "$f" \
    || { echo "  ✗ $f sin marca de tiempo"; D_FAIL=1; }
done
[ "$D_FAIL" = "0" ] && echo "  ✓ todos los docs técnicos llevan marca de tiempo" || FAIL=1

# ─── [F] ARTEFACTOS HUÉRFANOS ───────────────────────────────────────────────
# ⛔⛔ AÑADIDO EL 2026‑09‑12, y por un fallo REAL de la víspera.
#
# El 2026‑09‑11 se puso `FOL/Soundness.lean` en cuarentena porque su teorema se tuvo por FALSO
# (con `raa` en el entorno daba `False` sin hipótesis; ✏️ 2026‑10‑02: lo falso era `raa`, que se
# borró con `FOL/MetaRules.lean` — ADR‑115 de RPP). Se movió el fuente, se quitó del barrel,
# se reconstruyó el árbol y dio VERDE. Pero `lake` NO recoge la basura: el
# `.olean` COMPILADO se quedó, `import FOL.Soundness` SEGUÍA RESOLVIENDO desde él, y
# `False` se demostraba al día siguiente exactamente igual.
#
# 🔑 La lección: **retirar el FUENTE no retira el MÓDULO**. Un `.olean` sin `.lean` es un
# módulo fantasma — importable, invisible al build y sin fuente que auditar.
#
# Este bloque ROMPE: no hay ningún caso legítimo de `.olean` sin fuente.
echo
echo "════ [F] ARTEFACTOS HUÉRFANOS (.olean sin fuente) ════"
F_FAIL=0
for ROOT in "."; do
  LAKEDIR="$ROOT/.lake/build/lib/lean"
  [ -d "$LAKEDIR" ] || continue
  while IFS= read -r O; do
    [ -n "$O" ] || continue
    REL="${O#$LAKEDIR/}"
    SRC="$ROOT/${REL%.olean}.lean"
    if [ ! -f "$SRC" ]; then
      echo "  ✗ módulo FANTASMA: ${REL%.olean} — hay .olean pero NO hay fuente"
      echo "      $O"
      F_FAIL=1
    fi
  done <<< "$(find "$LAKEDIR" -name '*.olean' 2>/dev/null)"
done
if [ "$F_FAIL" = "0" ]; then
  echo "  ✓ ningún .olean sin fuente"
else
  echo "  ⚠️  un .olean sin fuente SIGUE SIENDO IMPORTABLE. Bórralo:"
  echo "      rm -f <ruta>.olean <ruta>.olean.hash <ruta>.ilean <ruta>.ilean.hash <ruta>.trace"
  FAIL=1
fi

# ─── [G] DEUDAS ENUNCIADAS QUE YA ESTÁN PAGADAS ─────────────────────────
# ⛔ POR QUÉ EXISTE (2026-09-18, auditoría A1, ADR-072): ningún control miraba lo que un
# docstring de módulo **AFIRMA QUE FALTA**. [E] mira la FECHA del titular, no lo que dice.
# Medido en el barrido: de 24 líneas con ⬜ en 16 módulos, **19 anunciaban una deuda ya
# pagada**, más ≥7 afirmaciones falsas sin ⬜. Casos: `Sequent0` titulaba el Hauptsatz como
# «LA ÚNICA DEUDA QUE QUEDA» **tres veces** con `hauptsatz` ya probado; `Skolem0` decía
# «⬜ MEDIDO que no existe nada de eso» del prefijo ∀ⁿ con `SkolemN0` entero al lado — y la
# falsedad iba etiquetada **MEDIDO**.
#
# 🔑 Lo que hace esto comprobable A MÁQUINA es que el idioma del proyecto es exacto: *una
# deuda se ENUNCIA como `Prop`, nunca se postula*, y se paga con `theorem X : ESA_PROP := …`.
# No hay que leer prosa: se compara un nombre con otro.
#
# ⚠️ El testigo tiene que ser INCONDICIONAL. `herbrandExtraction_of (hcut) (htr)` no paga
# nada: es el CONSUMIDOR. Por eso el patrón exige `: NOMBRE :=` sin binders delante — sin esa
# restricción el control daría rojo el día que se escribe el consumidor, o sea siempre.
# ⛔ Y NO entra el aviso «un párrafo ⬜ cita un nombre ya declarado»: medido, acierta 2 de 11
# (`Skolem0` cita `shiftEnv`/`exBlock` justo para decir «esto SÍ está, lo otro no»).
# 🔑 *Un control que grita lobo se deja de mirar.*
echo ""
echo "════ [G] DEUDAS ENUNCIADAS QUE YA TIENEN TESTIGO — ROJO ════"
GSRC="FOL TheoryFramework"
GDEBT="⬜|DEUDA|[Nn]o está hecha|[Nn]o está hecho|NO se paga aquí|[Nn]o existe nada"
# ⭐ La exóneración: si la MISMA cabecera dice que está pagada, no hay nada que cazar.
# ⚠️ No debilita el control: [G.1] sólo mira deudas cuyo testigo YA EXISTE, luego escribir
# «PAGADA» ahí es escribir la verdad. Lo que caza es «dice ABIERTA y está CERRADA».
GPAID="PAGADA|PAGADO|RESUELTA|RESUELTO|SALDADA|SALDADO|🏁"
G_FAIL=0
GPROPS=$(mktemp)
grep -rnE "^def +[A-Za-z_][A-Za-z0-9_'₀₁₂ⁿ]* *: *Prop" $GSRC --include=*.lean > "$GPROPS" 2>/dev/null
while IFS= read -r gp; do
  [ -z "$gp" ] && continue
  GF=${gp%%:*}; grest=${gp#*:}; GL=${grest%%:*}
  GNAME=$(printf '%s' "$grest" | sed 's/^[0-9]*://' | awk '{print $2}')
  [ -z "$GNAME" ] && continue
  # El docstring INMEDIATAMENTE anterior, delimitado por `-/` y NO por línea en blanco:
  # ⚠️ medido — un docstring largo lleva blancos DENTRO, y cortando ahí se pierde justo la
  # línea del ⬜ (le pasaba a `Herbrand0.lean:268`, que quedaba fuera por dos líneas).
  gi=$((GL-1)); GBLK=""
  while [ "$gi" -gt 0 ]; do
    gln=$(sed -n "${gi}p" "$GF")
    case "$gln" in *"-/"*) [ -n "$GBLK" ] && break ;; esac
    GBLK="$gln
$GBLK"; gi=$((gi-1))
    [ $((GL-gi)) -gt 40 ] && break
  done
  printf '%s' "$GBLK" | grep -qE "$GDEBT" || continue
  printf '%s' "$GBLK" | grep -qE "$GPAID" && continue
  GWIT=$(grep -rnE "^theorem +[A-Za-z_][A-Za-z0-9_'₀₁₂ⁿ]* *: *$GNAME *:=" $GSRC --include=*.lean 2>/dev/null | head -1)
  if [ -n "$GWIT" ]; then
    echo "  ❌ $GF:$GL — \`$GNAME\` se anuncia como DEUDA y YA TIENE TESTIGO INCONDICIONAL:"
    echo "        $(printf '%s' "$GWIT" | cut -c1-130)"
    G_FAIL=1
  fi
done < "$GPROPS"
rm -f "$GPROPS"
if [ "$G_FAIL" = "0" ]; then
  echo "  ✓ ninguna deuda enunciada tiene ya testigo incondicional"
else
  echo "      ⚠️ La deuda está PAGADA y la cabecera sigue anunciándola abierta. Corregir la"
  echo "      CABECERA, no el teorema. 🔑 Un módulo que dice que algo falta se vuelve a construir."
  FAIL=1
fi

# ─── [G.2] CENSO DE MARCADORES DE DEUDA — trinquete en los DOS sentidos ───
# ⛔ POR QUÉ EXISTE (2026-09-23): [G.1] tiene un hueco MEDIDO. Sólo lee el docstring **pegado
# a un `def X : Prop`** y sólo acepta como pago un `theorem X : X :=`. ⇒ no ve dos clases
# enteras, y el 2026-09-23 las dos estaban pobladas:
#   (a) la ⬜ que vive en la **cabecera `/-! … -/` del módulo**, que no cuelga de ningún `Prop`;
#   (b) la deuda que paga **otro módulo entero** (`PrenexNF0` pagaba `Prenex0`; `SkolemN0`
#       pagaba `Skolem0`; `Canonical0` pagaba `Lindenbaum0`; `Eigenvariable` pagaba `Rename`).
# Medido ese día: **23 marcadores, 9 de ellos anunciando abierto algo probado al lado**, con
# [G.1] en VERDE. Es el mismo recuento que ADR-072 hizo al crear [G.1] — 19 de 24 —, o sea que
# el problema **vuelve a crecer** en cuanto no hay trinquete.
#
# 🔑 Lo que [G.2] automatiza NO es «la deuda tiene testigo» (eso es [G.1]): es
# **«la deuda ha sido MIRADA y CLASIFICADA»**. No juzga; obliga a que alguien haya juzgado.
#
# ⚠️ Rompe en los DOS sentidos, como [B] y [E]:
#   * marcador SIN declarar        ⇒ ROJO (clasifícalo)
#   * fila declarada que ya NO casa ⇒ ROJO (quítala: la deuda se pagó o el texto cambió)
#   * ancla que casa DOS veces      ⇒ ROJO (ambigua; no vale absolver por subcadena)
# 🔑 *Un contador exacto rompe también hacia abajo.*
#
# Las cuatro clases:
#   ABIERTA   — deuda real y viva. La nota dice qué falta.
#   DIFERIDA  — se puede hacer y se decidió NO hacerlo ahora. La nota dice por qué.
#   OFERTA    — no es deuda: una alternativa ofrecida al propietario.
#   HISTORIAL — el marcador CITA una deuda pasada (entre «» o tachada). La nota dice quién la pagó.
echo ""
echo "════ [G.2] CENSO DE MARCADORES DE DEUDA — ROJO ════"
G2SRC="FOL TheoryFramework"
# ⚠️ 2026-09-26: + «no está(n) medido/a(s)». La forma larga se le escapaba a «[Nn]o medido» y la
# revisión adversarial de T4/T6 encontró dos casos NUEVOS, míos, que ningún control veía.
G2PAT="⬜|DEUDA|[Nn]o está hecha|[Nn]o está hecho|NO se paga aquí|[Nn]o existe nada|ÚNICA DEUDA|[Nn]o medido|[Nn]o está medid[oa]|[Nn]o están medid[oa]s"
G2_FAIL=0
G2TAB=$(mktemp); G2CUR=$(mktemp)

# ── LA TABLA ──  fichero § ancla (subcadena ÚNICA en ese fichero) § clase § nota
cat > "$G2TAB" <<'G2EOF'
FOL/Derives1.lean§Esta sección se titulaba§HISTORIAL§H3 la paga `Hauptsatz0.cut_elimination₀`
FOL/Derives2.lean§Se titulaba§HISTORIAL§H3 la paga `Hauptsatz0.hauptsatz₀`
FOL/Herbrand0.lean§Esta cabecera decía§HISTORIAL§H3 la paga `Hauptsatz0.herbrand_extraction₀`
FOL/HerbrandBlock0.lean§ya decía «PAGADA» mientras esta línea§HISTORIAL§la paga `BlockExtraction0.herbrand_extraction_block₀`
FOL/Prenex0.lean§~~Lo que falta para la forma normal~~§HISTORIAL§la paga `FOL.PrenexNF0` (y refuta su estimación)
FOL/Prenex0.lean§Estimado ~200 l., riesgo medio§HISTORIAL§la estimación que `PrenexNF0` refutó
FOL/Rename.lean§~~Lo que esto NO es todavía~~§HISTORIAL§la paga `Eigenvariable.derives0_gen_fresh`
FOL/Sequent0.lean§LA ÚNICA DEUDA QUE QUEDA§HISTORIAL§`CutElim₀` la paga `Hauptsatz0.cut_elimination₀`
FOL/Skolem0.lean§la falsedad iba etiquetada§HISTORIAL§la paga `SkolemN0.skolem_conservative_n₀`
FOL/Skolem0.lean§~~Lo que falta: el axioma bajo un PREFIJO§HISTORIAL§la paga `SkolemN0`
FOL/Skolem0.lean§**MEDIDO que no existe nada de eso**§HISTORIAL§`envPush` resultó no hacer falta
FOL/Skolem0.lean§~200 l., riesgo **medio**, y el riesgo§HISTORIAL§la estimación que `SkolemN0` refutó
G2EOF

grep -rnE "$G2PAT" $G2SRC --include=*.lean 2>/dev/null > "$G2CUR"
G2N=$(wc -l < "$G2CUR" | tr -d ' ')
G2D=$(grep -c . "$G2TAB" | tr -d ' ')

# (i) cada fila declarada casa EXACTAMENTE una vez
while IFS= read -r g2row; do
  [ -z "$g2row" ] && continue
  g2f=$(printf '%s' "$g2row" | awk -F'§' '{print $1}')
  g2a=$(printf '%s' "$g2row" | awk -F'§' '{print $2}')
  g2c=$(printf '%s' "$g2row" | awk -F'§' '{print $3}')
  g2hits=$(grep -F -- "$g2a" "$G2CUR" | grep -c "^$g2f:" | tr -d ' ')
  if [ "$g2hits" = "0" ]; then
    echo "  ❌ $g2f — la fila declarada ($g2c) YA NO CASA con ningún marcador:"
    echo "        ancla: $g2a"
    echo "        ⇒ o la deuda se pagó (quita la fila) o el texto cambió (ajusta el ancla)."
    G2_FAIL=1
  elif [ "$g2hits" != "1" ]; then
    echo "  ❌ $g2f — ancla AMBIGUA ($g2hits marcadores): $g2a"
    echo "        ⇒ casar por subcadena ABSUELVE si el ancla no es única. Afínala."
    G2_FAIL=1
  fi
done < "$G2TAB"

# (ii) ningún marcador sin declarar  — y el recuento tiene que CUADRAR
if [ "$G2N" != "$G2D" ]; then
  echo "  ❌ marcadores en el árbol: $G2N · filas declaradas: $G2D"
  while IFS= read -r g2l; do
    [ -z "$g2l" ] && continue
    g2lf=${g2l%%:*}
    g2found=0
    while IFS= read -r g2row; do
      [ -z "$g2row" ] && continue
      g2f=$(printf '%s' "$g2row" | awk -F'§' '{print $1}')
      [ "$g2f" = "$g2lf" ] || continue
      g2a=$(printf '%s' "$g2row" | awk -F'§' '{print $2}')
      case "$g2l" in *"$g2a"*) g2found=1; break ;; esac
    done < "$G2TAB"
    [ "$g2found" = "0" ] && echo "        SIN DECLARAR → $(printf '%s' "$g2l" | cut -c1-118)"
  done < "$G2CUR"
  G2_FAIL=1
fi

rm -f "$G2TAB" "$G2CUR"
if [ "$G2_FAIL" = "0" ]; then
  echo "  ✓ los $G2N marcadores de deuda están TODOS clasificados"
else
  echo "      ⚠️ Un marcador sin clasificar es una deuda que nadie ha mirado. Clásificalo en"
  echo "      la TABLA de [G.2] como ABIERTA / DIFERIDA / OFERTA / HISTORIAL, con su nota."
  echo "      🔑 [G.1] comprueba que la deuda tiene TESTIGO; [G.2], que ha sido MIRADA."
  FAIL=1
fi

# ─── RESUMEN ────────────────────────────────────────────────────────────────
echo
if [ "$FAIL" = "0" ]; then
  echo "✅ DOCUMENTACIÓN SINCRONIZADA."
else
  echo "❌ HAY DESINCRONIZACIÓN — corregir ANTES de commitear."
  if [ "$HINT" = "1" ]; then
    echo
    echo "Sugerencias de sed (revisar antes de aplicar):"
    echo "  sed -i -E 's/[0-9]+ módulos activos/$ACTIVE módulos activos/g' *.md"
  fi
  echo
  echo "⚠️  Recordatorio: NO basta con arreglar el banner. Comprobar también el CUERPO"
  echo "    (tablas resumen, §Próximos pasos, notas de auditoría antiguas)."
fi
exit "$FAIL"
