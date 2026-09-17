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
AXIOMS=$(grep -rhE "^axiom " FOL/ TheoryFramework/ --include=*.lean 2>/dev/null | wc -l)
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
if printf '%s' "$SORRY_OUT" | grep -q 'No sorry found'; then
  SORRY=0
elif printf '%s' "$SORRY_OUT" | grep -qE 'Total: [0-9]+ sorry'; then
  SORRY=$(printf '%s' "$SORRY_OUT" | grep -oE 'Total: [0-9]+ sorry' | grep -oE '[0-9]+' | head -1)
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
printf "  sorry           : %s
" "$SORRY"
echo "  build jobs      : no se mide aquí (M-3: FOL no se construye desde FOL)"
[ "$SORRY_MISSING" = "1" ] && echo "  ⚠️  sorry         : SIN MEDIR — check-sorry.bash no dijo ni 'No sorry found' ni 'Total: N sorry'."
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
if [ "$SORRY_MISSING" != "0" ]; then
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
check_num '[0-9]+ `?axiom`? de Lean' "$AXIOMS" "axiom de Lean"
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
warn_num '[0-9]+ `?axiom`? de Lean' "$AXIOMS" "axiom de Lean"
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
echo "════ [E] FRESCURA DEL TITULAR — AVISO, requiere juicio ════"
# ⭐ Añadido el 2026-09-11 por la auditoría (hallazgo F-2). El control [A] comprueba las
# CIFRAS del banner y [D] que exista una marca de tiempo, pero NADIE comprobaba la FRASE.
# Resultado medido: SEIS documentos autoritativos compartían el mismo titular del 2026-09-09
# —«C3: 5 de 7 reflectores · D3 a DOS obligaciones»— con las cifras de abajo ya al día.
# C3 se cerró el 10e y D3 se probó el 10g. El titular estaba duplicado ⇒ el error se multiplicó
# por seis, y ningún control lo veía porque no es un número.
#
# La heurística: la fecha del TITULAR de cada doc autoritativo no debería ser anterior a la
# entrada más reciente del CHANGELOG. Si lo es, o el titular se quedó atrás o falta marcarlo.
NEWEST=$(grep -ohE "20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}" CHANGELOG.md 2>/dev/null | sed "s/‑/-/g" | sort -r | head -1)
E_HITS=0
if [ -n "$NEWEST" ]; then
  for d in $DOCS; do
    [ -e "$d" ] || continue
    HEAD_DATE=$(head -12 "$d" | grep -ohE "20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}" | sed "s/‑/-/g" | sort -r | head -1)
    [ -z "$HEAD_DATE" ] && continue
    if [ "$HEAD_DATE" \< "$NEWEST" ]; then
      echo "  ⚠️  $d: titular fechado $HEAD_DATE, y el CHANGELOG llega a $NEWEST"
      echo "      $(head -12 "$d" | grep -m1 -E "ESTADO REAL|^\*\*Estado |^> \*\*Estado " | cut -c1-120)"
      E_HITS=$((E_HITS+1))
    fi
  done
  if [ "$E_HITS" = "0" ]; then
    echo "  ✓ ningún titular se ha quedado atrás del CHANGELOG ($NEWEST)"
  else
    echo "  ⚠️  $E_HITS titular(es) por detrás del CHANGELOG."
    echo "      ⚠️ El titular es una FRASE: [A] no lo ve. Comprobar que lo que AFIRMA sigue"
    echo "      siendo cierto, no sólo que sus cifras cuadren."
  fi
else
  echo "  ⚠️  no pude leer la fecha más reciente del CHANGELOG — control VACÍO"
fi

# ─── 3. SÍMBOLOS MUERTOS ─────────────────────────────────────────────────────
# Un símbolo está MUERTO si se cita en un doc AUTORITATIVO pero ninguna declaración
# del árbol activo empieza por él.
#
# Dos calibraciones aprendidas al estrenar este control (2026-08-23):
#   * Sólo se miran los docs AUTORITATIVOS (los que describen el estado actual). Los
#     de diseño e historia — MINIMAL-AXIOMS, THOUGHTS, GODEL-*-DESIGN, PLAN-* — citan
#     por diseño cosas que ya no están, y marcarlos sería ruido.
#   * Se compara por PREFIJO, no por igualdad: la prosa abrevia (`ax_C3` por
#     `ax_C3_concat_assoc`, `ax_lineWF` por `ax_lineWF_c1`), y eso es legítimo.
#     Un símbolo de verdad muerto (`goedel_first_real'`, `prf_tc_cons'`) no prefija nada.
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
DEAD_MARKER="$DEAD_MARKER"'|propuest|candidat|hipot[eé]tic|har[ií]a falta|si se |habr[ií]a que|añadir |descartad|no existe|NO EXISTE|sin materializar|20[0-9]{2}-[0-9]{2}-[0-9]{2}'
#   (d) es un OBJETIVO declarado, no una afirmación de que ya está.
DEAD_MARKER="$DEAD_MARKER"'|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la'
DECLS=$(mktemp)
# El árbol de declaraciones incluye `cuarentena/`: esos símbolos EXISTEN (están fuera
# del build, no borrados), y los docs los discuten con razón.
# ⚠️ Se incluye `../ROBINSON_PlusPlus/`: los docs de FOL citan con razón símbolos de RPP
# (p. ej. los tres `axiom` de Lean que `cuarentena/README.md` contabiliza), y sin ese
# alcance [B] los daría por muertos. 🔑 Un control con el alcance equivocado no comprueba:
# INVENTA.
# ⚠️⚠️ Y si el hermano NO está, se DICE. Sin él [B] da por muertos los símbolos de RPP que
# los docs de FOL citan con razón, y un aviso que siempre sale es un aviso que nadie lee.
# 🔑 Un control tiene TRES resultados — pasa, falla, NO HE PODIDO COMPROBARLO — y el tercero
# se anuncia, no se colapsa en el primero.
# ⭐ `RPP_DIR` permite apuntar al hermano desde donde esté: en la CI, `actions/checkout`
# no admite un `path:` fuera del workspace, así que RPP se clona DENTRO y se pasa aquí.
SIBLING="${RPP_DIR:-../ROBINSON_PlusPlus}"
if [ -d "$SIBLING" ]; then
  SCOPE="FOL/ TheoryFramework/ cuarentena/ $SIBLING/"
else
  SCOPE="FOL/ TheoryFramework/ cuarentena/"
  echo "  ⚠️  ALCANCE REDUCIDO: no está ../ROBINSON_PlusPlus ⇒ los símbolos de RPP que estos"
  echo "      docs citan con razón saldrán aquí como MUERTOS. No es un hallazgo: es un hueco."
fi
grep -rhoE "(theorem|def|abbrev|axiom|noncomputable def) +[A-Za-z_][A-Za-z0-9_']*"      $SCOPE --include=*.lean 2>/dev/null      | awk '{print $NF}' | sort -u > "$DECLS"
CANDS=$(grep -rhoE '`(prf_|pcc_|goedel_|godel|d[123]_|repr_|ax_)[A-Za-z0-9_'"'"']+`' $AUTHORITATIVE 2>/dev/null         | tr -d '`' | sort -u)
for sym in $CANDS; do
  # los axiomas objeto son snake_case: `ax_UpperCamel` es un PLACEHOLDER de convención
  # de nombres (`ax_TagDescriptor`), no un símbolo. Se ignora.
  case "$sym" in ax_[A-Z]*) continue ;; esac
  # vivo si ALGUNA declaración empieza por el símbolo (la prosa abrevia)
  grep -qE "^${sym}" "$DECLS" && continue
  bad=$(grep -rn "\`${sym}\`" $AUTHORITATIVE 2>/dev/null | grep -vE "$DEAD_MARKER" || true)
  if [ -n "$bad" ]; then
    echo "  ✗ \`$sym\` no existe en el árbol activo, y se cita sin marcar como retirado:"
    echo "$bad" | head -2 | sed 's/^/      /' | cut -c1-140
    B_FAIL=1
  fi
done
rm -f "$DECLS"
# [B] NO marca FAIL: es un aviso. [A], [C] y [D] sí son objetivos y sí lo marcan.
# Razón: un control que grita lobo se acaba ignorando, y ése era justo el fallo que
# este script existe para evitar.
[ "$B_FAIL" = "0" ] && echo "  ✓ ningún símbolo muerto citado como vigente"                     || echo "  ⚠️  revisar los de arriba: ¿es una afirmación de que YA ESTÁ, o una mención histórica/planificada?"

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
# El 2026‑09‑11 se puso `FOL/Soundness.lean` en cuarentena porque su teorema es FALSO
# (con `raa` demuestra `False` sin hipótesis). Se movió el fuente, se quitó del barrel,
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
