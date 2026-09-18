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
DEPENDENCIES.md
DECISIONS.md
README.md
AXIOMS.md
NEXT-STEPS.md
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
