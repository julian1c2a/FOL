# b-control.bash — el control [B] de check-doc-sync.bash (T04, ADR-166): autotest, ejecución, deuda por cita y techo.
# ⛔ Este fichero es IDÉNTICO, byte a byte, en ROBINSON_PlusPlus y en FOL (check-doc-sync.bash de RPP lo comprueba),
# como b-citas.awk. Lo propio de cada repo (de dónde salen las entradas, qué documentos) lo pone quien lo carga.
#
# Lo carga (`source`) check-doc-sync.bash con estas variables ya puestas:
#   B_DECLS B_ENV B_SOND B_MOD B_RUT   las entradas de b-citas.awk (ficheros); DECL_RE y NOMBRES, como en [B];
#   B_GITS      los repos cuya historia da los nombres que el proyecto declaró alguna vez (`. ../FOL`): del PRIMERO, el
#               propio, su HEAD, sus etiquetas y lo que aún no está en git (lo que verá su CI tras el commit); de los
#               demás, su HEAD y sus etiquetas (lo que ve la CI: nunca un `stash` ni una rama local);
#   B_DOCS_LISTA  los documentos (todos tienen que existir: uno que desaparece no puede bajar la deuda en silencio);
#   B_DEUDA_MODO (0, 1 --b-deuda, 2 --b-deuda-inicial, 3 --b-deuda-rehacer);
#   B_SUBE_ADR  vacío, o el ADR que deja subir entradas concretas; y las funciones b_adr_existe ADR y b_adr_texto ADR
#               (dice si existe; imprime su texto: tiene que NOMBRAR cada clave que sube).
# Deja B_FAIL (1 si rompe) y B_MEDIDO (0 si no pudo medir), e imprime lo que encuentra.
#
# 🔑 EL TRINQUETE. Una cita muerta de más que la tabla es rojo; una de menos, también, hasta que `--b-deuda` baje la
# tabla. Y la tabla tiene TECHO, que se calcula en cada ejecución REHACIENDO su historia en git desde que se creó (por
# la línea de primeros padres), versión a versión:
#   · una versión sólo puede quedarse en lo que dejó la anterior, o bajar (una entrada ausente cuenta 0);
#   · donde cambia el núcleo (b-citas.awk), puede subir lo que el núcleo NUEVO ve de más que el VIEJO sobre los
#     documentos de esa versión, con las entradas de hoy: máx(0, nuevo − viejo), y nada más;
#   · lo que una versión sube sin cabida NO CUENTA para las siguientes: no se blanquea con un commit intermedio que la
#     CI no vio, ni con un comentario en el núcleo, ni borrando la tabla y creándola otra vez.
# El techo del árbol es la última versión legítima, más lo que vea de más su núcleo si cambia. Subir una entrada sin
# eso pide un ADR que la nombre (B_SUBE_ADR, que exime las claves que nombra mientras siga puesto). Si un núcleo viejo
# no lee las mismas entradas (otra interfaz: no lee la sexta), la versión que lo cambia se toma tal cual y la historia
# empieza ahí: lo dice la línea «historia de la tabla», y lo tiene que decir su ADR. Si un núcleo FALLA con las entradas
# de hoy, esa versión no sube nada: romperlo en un commit intermedio no blanquea el siguiente.
# La tabla vive en la misma ruta en los dos repos, y se fija AQUÍ: con otra ruta, su historia empezaría de cero.
B_TABLA=doc/control/b-deuda.tsv
B_FAIL=0; B_MEDIDO=1; B_TAB=$(printf '\t')
B_AUTO=$(mktemp -d); B_CIT=$(mktemp); B_ACT=$(mktemp); B_TECHO=$(mktemp); B_HIST=$(mktemp); B_LEG=$(mktemp)
for d in $B_DOCS_LISTA; do
  [ -f "$d" ] || { echo "  ❌ falta el documento $d: uno que desaparece no puede llevarse su deuda en silencio."; B_FAIL=1; }
done
B_DOCS=""; for d in $B_DOCS_LISTA; do [ -f "$d" ] && B_DOCS="$B_DOCS $d"; done
# ⭐ AUTOTEST de salida EXACTA: una cita de cada clase —viva por cada vía; muerta pese a un marcador lejano, de otra
# celda, una fecha, su propio nombre, un verbo corriente, «hace falta», un comentario HTML, un homónimo de Lean, su forma
# o su posición dentro de la cita— y las reglas de CommonMark. Si no da exactamente lo esperado, no se mide.
printf '%s\n' vivo_ok > "$B_AUTO/vivos"
printf 'Lean.Name\tL\nimp_intro\tL\nCoreM.run\tL\nStd.Bounded.LE\tL\nLean.Expr.getUsedConstants\tL\nQuot.sound\tL\nROBINSON_PlusPlus.X.Prf.listInd\tP\nROBINSON_PlusPlus.X.SinWTs.vivo_ok\tP\nautoImplicit\tO\nInit.Classical\tM\n#mi_orden\tT\n' > "$B_AUTO/env"
printf '%s\n' 'solo_en_sondeo|sondeos/Sondeo.lean' > "$B_AUTO/sond"
printf '%s\n' ROBINSON_PlusPlus.Meta.Rosser Meta.Rosser Rosser > "$B_AUTO/mod"
printf '%s\n' ROBINSON_PlusPlus/Meta/Rosser.lean sondeos/Sondeo.lean doc/registro/x.txt archivo/tag-1 'archivo/tag-1:sondeos/Viejo.lean' \
  check-doc-sync.bash '=cuarentena/retiradas/Viejo.lean' > "$B_AUTO/rut"
printf '%s\n' raa Bounded > "$B_AUTO/hist"
B_RELLENO=$(printf '%0110d' 0 | tr 0 x)
printf '%s\n' \
  '`vivo_ok`, `Lean.Name`, `listInd`, `Prf.listInd`, `CoreM`, `getUsedConstants`, `autoImplicit`, `Init.Classical`, `Rosser`.' \
  '`Meta/Rosser.lean:12‑20`, `doc/registro`, `archivo/tag-1`, `archivo/tag-1:sondeos/Viejo.lean`, `Meta/*.lean`, `@vivo_ok`.' \
  '`bash check-doc-sync.bash --b-deuda`, `vivo_ok.mp`, `[propext, Quot.sound]` y `Build completed (1 jobs)`.' \
  'La orden `#mi_orden` corre en el build; `#orden_muerta`, no.' \
  'El `muerto_a`, retirado.' \
  "El \`muerto_b\` $B_RELLENO retirado." \
  '| `muerto_c` | retirado |' \
  '2026-10-18: `muerto_d`.' \
  '`T_UNIVERSO`, `simp`, `f9941dc`, `hPsiId`, `ax21`, `ax_TagDescriptor`, `Prop` y `h.symm`.' \
  '`solo_en_sondeo`, en `Sondeo.lean`.' \
  '`solo_en_sondeo` sin nombrar su fichero.' \
  '`Meta/NoExiste.lean`, `archivo/tag-1:sondeos/Nada.lean`, `Viejo.lean` y la familia `muerto_e_`.' \
  '`muerto_retirado_g`.' \
  '`imp_intro`, `teorema_borrado.mk`, `raa`, `Bounded`, `Borrado.vivo_ok` y `SinWTs.prf_borrado`.' \
  '`muerto_h` lo necesita; el borrador de `muerto_i`; `muerto_j` <!-- falta --> y `muerto_k` hace falta.' \
  'La base `[propext,' 'gen, muerto_l]` y `muerto_m`.' \
  '```bash orden``` en línea: `muerto_n`.' \
  '`theorem muerto_o (h : P) : Q` y `#print axioms muerto_p`.' \
  '- un acento suelto: ` sin cerrar' '- `muerto_q` en el ítem siguiente.' \
  'El marcador `<!--` es texto; `` muerto_r `` y \` y `muerto_s`.' \
  '````md' '```' '`muerto_dentro`' '````' \
  '~~~' '`muerto_tilde`' '~~~' \
  '> ```' '> `muerto_cita`' '> ```' \
  '```' '`muerto_tras_valla_abierta`' > "$B_AUTO/doc.md"
B_AUTO_SAL=$(LC_ALL=C awk -f b-citas.awk "$B_AUTO/vivos" "$B_AUTO/env" "$B_AUTO/sond" "$B_AUTO/mod" "$B_AUTO/rut" \
  "$B_AUTO/hist" "$B_AUTO/doc.md" | cut -d'|' -f1,2 | sed 's%^V|.*/doc[.]md:%V|doc.md:%' | LC_ALL=C sort | tr '\n' ';')
B_AUTO_ESP="B2|Meta/NoExiste.lean;B2|Viejo.lean;B2|archivo/tag-1:sondeos/Nada.lean;B|Borrado.vivo_ok;B|Bounded;B|SinWTs.prf_borrado;B|imp_intro;B|muerto_b;B|muerto_c;B|muerto_d;B|muerto_e_;B|muerto_h;B|muerto_i;B|muerto_j;B|muerto_k;B|muerto_l;B|muerto_m;B|muerto_n;B|muerto_o;B|muerto_p;B|muerto_q;B|muerto_r;B|muerto_retirado_g;B|muerto_s;B|orden_muerta;B|raa;B|solo_en_sondeo;B|teorema_borrado.mk;V|doc.md:33;"
if [ "$B_AUTO_SAL" != "$B_AUTO_ESP" ]; then
  echo "  ❌ NO PUDE MEDIR [B]: el autotest de b-citas.awk no da lo esperado; da: $B_AUTO_SAL"
  B_FAIL=1; B_MEDIDO=0
fi
# HIST: los nombres que el proyecto declaró ALGUNA VEZ y los módulos que tuvo, de la historia de git (completa: las CI
# clonan con fetch-depth 0). Un nombre de aquí no se exime por su forma, ni lo absuelve un homónimo de Lean. Se mira lo
# que mira la CI —HEAD y las etiquetas, no `--all`: un `stash` o una rama local darían en local otra deuda— y, del repo
# propio, también lo que aún no está en git, que su CI verá tras el commit. De los diffs sólo cuentan las líneas que
# EMPIEZAN por una declaración (tras sus atributos y modificadores): «class instance» o «theorem that» en un comentario
# meterían palabras sueltas (`instance`, `list`, `for`), que perderían su exención (medido el 2026-10-18: sin anclar,
# 76 nombres de más en RPP y FOL, casi todos palabras de comentarios).
B_DECL_LINEA='^[+-][[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)[[:space:]]+)*(theorem|lemma|def|abbrev|axiom|opaque|instance|structure|inductive|class)[[:space:]]+[^[:space:]:({[]'
if [ "$B_MEDIDO" = "1" ]; then
  B_PROPIO=1
  for g in $B_GITS; do
    { git -C "$g" log HEAD --tags -p --format= -- '*.lean'
      if [ "$B_PROPIO" = "1" ]; then
        git -C "$g" diff HEAD -- '*.lean'
        git -C "$g" ls-files -o --exclude-standard -- '*.lean' | while IFS= read -r f; do sed 's/^/+/' "$g/$f"; done
      fi; } 2>/dev/null | LC_ALL=C grep -E "$B_DECL_LINEA" | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES"
    { git -C "$g" log HEAD --tags --name-only --format= -- '*.lean'
      if [ "$B_PROPIO" = "1" ]; then git -C "$g" ls-files -co --exclude-standard -- '*.lean'; fi; } 2>/dev/null \
      | sed 's|.*/||; s|[.]lean$||'
    B_PROPIO=0
  done | grep . | LC_ALL=C sort -u > "$B_HIST"
  if [ "$(wc -l < "$B_HIST" | tr -d ' ')" -lt 1000 ] || ! grep -qxF raa "$B_HIST"; then
    echo "  ❌ NO PUDE MEDIR [B]: la historia de git no da los nombres de siempre (¿un clon superficial?)."
    B_FAIL=1; B_MEDIDO=0
  fi
fi
if [ "$B_MEDIDO" = "1" ]; then
  if ! LC_ALL=C awk -f b-citas.awk "$B_DECLS" "$B_ENV" "$B_SOND" "$B_MOD" "$B_RUT" "$B_HIST" $B_DOCS > "$B_CIT"; then
    echo "  ❌ NO PUDE MEDIR [B]: b-citas.awk falló."
    B_FAIL=1; B_MEDIDO=0
  elif grep -q '^V|' "$B_CIT"; then
    echo "  ❌ NO PUDE MEDIR [B]: un documento acaba con una valla o un comentario ABIERTO, y el resto no se ha mirado:"
    grep '^V|' "$B_CIT" | sed 's/^V|/      /'
    B_FAIL=1; B_MEDIDO=0
  fi
fi
b_cuenta() {   # stdin: la salida de b-citas.awk → «clase<TAB>clave<TAB>documento<TAB>citas», ordenado
  LC_ALL=C awk -F'|' '$1 == "B" || $1 == "B2" { d = $4; sub(/:[0-9]+$/, "", d); n[$1 "\t" $2 "\t" d]++ }
    END { for (k in n) print k "\t" n[k] }' | LC_ALL=C sort
}
if [ "$B_MEDIDO" = "1" ]; then
  b_cuenta < "$B_CIT" > "$B_ACT"
  # ¿cambia el núcleo en el árbol? (--b-deuda-rehacer sólo vale entonces)
  B_NUCLEO_CAMBIA=0
  git ls-files --error-unmatch b-citas.awk > /dev/null 2>&1 || B_NUCLEO_CAMBIA=1
  git diff --quiet HEAD -- b-citas.awk 2>/dev/null || B_NUCLEO_CAMBIA=1
  B_CAB="# $B_TABLA — la deuda POR CITA de [B] (check-doc-sync.bash; T04, ADR-166 de RPP).
# Una línea por (clase, clave, documento): cuántas citas muertas tiene. B, un identificador; B2, una ruta.
# Una cita muerta de más es rojo; una de menos, también, hasta bajar la tabla: bash check-doc-sync.bash --b-deuda.
# El techo de cada entrada sale de rehacer en git la historia de esta tabla: sólo baja, salvo lo que un cambio de
# b-citas.awk vea de más. Se arregla en el DOCUMENTO: la cita, o un marcador de estado («retirado», «archivado»,
# «propuesto», «falta»…) a 100 bytes o menos, en la misma celda.
# clase${B_TAB}clave${B_TAB}documento${B_TAB}citas"
  if [ "$B_DEUDA_MODO" = "2" ] || [ "$B_DEUDA_MODO" = "3" ]; then
    if [ "$B_FAIL" = "1" ]; then
      echo "  ❌ no reescribo la tabla con [B] en rojo (¿falta un documento?)."
    elif [ "$B_DEUDA_MODO" = "2" ] && [ -e "$B_TABLA" ]; then
      echo "  ❌ --b-deuda-inicial: $B_TABLA ya existe; la tabla sólo baja (--b-deuda), o se rehace con el núcleo."
      B_FAIL=1
    elif [ "$B_DEUDA_MODO" = "3" ] && [ "$B_NUCLEO_CAMBIA" = "0" ]; then
      echo "  ❌ --b-deuda-rehacer: b-citas.awk no cambia en este árbol; la tabla sólo baja."
      B_FAIL=1
    else
      mkdir -p "$(dirname "$B_TABLA")"
      { printf '%s\n' "$B_CAB"; cat "$B_ACT"; } > "$B_TABLA"
      echo "  ✓ la tabla, escrita de nuevo: $(grep -vc '^#' "$B_TABLA") entradas"
    fi
  fi
  B_TAB_HOY=$(grep -v '^#' "$B_TABLA" 2>/dev/null | tr -d '\r' | LC_ALL=C sort)
  if [ "$B_DEUDA_MODO" = "1" ]; then
    B_SUBEN=$(LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { if ($0 != "") t[$1 "\t" $2 "\t" $3] = $4; next }
      { k = $1 "\t" $2 "\t" $3; if (!(k in t) || $4 + 0 > t[k] + 0) print }' <(printf '%s\n' "$B_TAB_HOY") "$B_ACT")
    if [ "$B_FAIL" = "1" ]; then
      echo "  ❌ --b-deuda: no bajo la tabla con [B] en rojo (¿falta un documento?)."
    elif [ -n "$B_SUBEN" ]; then
      echo "  ❌ --b-deuda NO baja la tabla: estas entradas suben o son nuevas (arréglalas en el documento o márcalas):"
      printf '%s\n' "$B_SUBEN" | head -20 | sed 's/^/      /'
      B_FAIL=1
    else
      B_DESAP=$(LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { if ($0 != "") h[$1 "\t" $2 "\t" $3] = 1; next }
        $0 != "" { k = $1 "\t" $2 "\t" $3; if (!(k in h)) print }' "$B_ACT" <(printf '%s\n' "$B_TAB_HOY"))
      { printf '%s\n' "$B_CAB"; cat "$B_ACT"; } > "$B_TABLA"
      B_TAB_HOY=$(grep -v '^#' "$B_TABLA" | tr -d '\r' | LC_ALL=C sort)
      echo "  ✓ --b-deuda: la tabla baja a $(grep -vc '^#' "$B_TABLA") entradas; salen del todo $(printf '%s\n' "$B_DESAP" | grep -c .):"
      printf '%s\n' "$B_DESAP" | grep . | head -10 | sed 's/^/      /'
    fi
  fi
  # una tabla con una entrada repetida o mal formada no se compara: es rojo
  B_MAL=$(printf '%s\n' "$B_TAB_HOY" | LC_ALL=C awk -F'\t' '$0 == "" { next } NF != 4 || $4 !~ /^[1-9][0-9]*$/ { print; next }
    { k = $1 "\t" $2 "\t" $3; if (k in v) print; v[k] = 1 }')
  if [ -n "$B_MAL" ]; then
    echo "  ❌ $B_TABLA tiene entradas repetidas o mal formadas (cuatro campos; las citas, un entero positivo):"
    printf '%s\n' "$B_MAL" | head -5 | sed 's/^/      /'
    B_FAIL=1
  fi
  # una de más (o nueva) es rojo; una de menos, también: hay que bajar la tabla
  B_DIF=$(LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { if ($0 != "") t[$1 "\t" $2 "\t" $3] = $4; next }
      { k = $1 "\t" $2 "\t" $3; h[k] = $4; if (!(k in t)) print "N\t" k "\t" $4
        else if ($4 + 0 > t[k] + 0) print "S\t" k "\t" $4 "\t" t[k]; else if ($4 + 0 < t[k] + 0) print "B\t" k "\t" $4 "\t" t[k] }
      END { for (k in t) if (!(k in h)) print "B\t" k "\t0\t" t[k] }' <(printf '%s\n' "$B_TAB_HOY") "$B_ACT")
  printf '%s\n' "$B_DIF" | grep -E "^(N|S)$B_TAB" | while IFS=$'\t' read -r tipo c k d n m; do
    [ -n "$c" ] || continue
    if [ "$tipo" = "N" ]; then echo "  ❌ $c \`$k\` no existe y se cita sin marcar, en $d ($n) — cita muerta NUEVA:"
    else echo "  ❌ $c \`$k\`: $n citas muertas en $d, y la tabla dice $m — una de más:"; fi
    LC_ALL=C awk -F'|' -v c="$c" -v k="$k" -v d="$d" '$1 == c && $2 == k && index($4, d ":") == 1 { print "      " $4 }' "$B_CIT" | head -3
  done
  printf '%s\n' "$B_DIF" | grep -qE "^(N|S)$B_TAB" && B_FAIL=1
  B_NBAJA=$(printf '%s\n' "$B_DIF" | grep -c "^B$B_TAB" || true)
  if [ "$B_NBAJA" -gt 0 ]; then
    echo "  ❌ $B_NBAJA entradas de $B_TABLA tienen MENOS citas muertas que las que dice la tabla (deuda saldada):"
    printf '%s\n' "$B_DIF" | grep "^B$B_TAB" | head -5 | sed "s/^B$B_TAB/      /"
    echo "      baja la tabla con: bash check-doc-sync.bash --b-deuda"
    B_FAIL=1
  fi
  # el TECHO: la historia de la tabla, REHECHA desde que se creó (ver la cabecera)
  B_TECHO_OK=1
  b_abs() { case "$1" in /*) printf '%s' "$1" ;; *) printf '%s/%s' "$(pwd)" "$1" ;; esac; }
  b_version() {   # $1 = commit → su tabla, sin la cabecera; una entrada repetida cuenta por la menor
    git show "$1:$B_TABLA" 2>/dev/null | tr -d '\r' | LC_ALL=C awk -F'\t' '!/^#/ && NF >= 4 { k = $1 "\t" $2 "\t" $3
      if (!(k in m) || $4 + 0 < m[k]) m[k] = $4 + 0 } END { for (k in m) print k "\t" m[k] }'
  }
  b_corre() {   # $1 = núcleo  $2 = directorio de los documentos  $3… = los documentos → su cuenta; sale con 1 si falla
    local nuc=$1 dir=$2; shift 2
    ( cd "$dir" && LC_ALL=C awk -f "$nuc" "$B_DECLS_A" "$B_ENV_A" "$B_SOND_A" "$B_MOD_A" "$B_RUT_A" "$B_HIST" "$@" ) \
      > "$B_AUTO/salida" 2>/dev/null || return 1
    b_cuenta < "$B_AUTO/salida"
  }
  b_de_mas() {   # $1 = núcleo viejo  $2 = núcleo nuevo  $3 = commit de los documentos, o vacío (los del árbol)
                 # → lo que el nuevo ve de más que el viejo, por entrada. Sale con 2 si el viejo no lee las mismas
                 # entradas (otra interfaz: no lee la sexta), y con 1 si uno de los dos falla con las de hoy
    grep -q 'ARGV\[6\]' "$1" || return 2
    local dir=. docs=$B_DOCS d
    if [ -n "$3" ]; then
      dir=$B_AUTO/docs; rm -rf "$dir"; mkdir -p "$dir"; docs=""
      for d in $B_DOCS; do
        git cat-file -e "$3:$d" 2>/dev/null || continue
        mkdir -p "$dir/$(dirname "$d")"; git show "$3:$d" > "$dir/$d"; docs="$docs $d"
      done
    fi
    b_corre "$1" "$dir" $docs > "$B_AUTO/viejo.tsv" || return 1
    b_corre "$2" "$dir" $docs > "$B_AUTO/nuevo.tsv" || return 1
    LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { v[$1 "\t" $2 "\t" $3] = $4; next }
      { d = $4 - v[$1 "\t" $2 "\t" $3]; if (d > 0) print $1 "\t" $2 "\t" $3 "\t" d }' "$B_AUTO/viejo.tsv" "$B_AUTO/nuevo.tsv"
  }
  b_suma() {   # $1, $2 = tablas → su suma, por entrada
    LC_ALL=C awk -F'\t' 'NF >= 4 { c[$1 "\t" $2 "\t" $3] += $4 } END { for (k in c) print k "\t" c[k] }' "$1" "$2"
  }
  b_minimo() {   # $1 = el tope  $2 = la tabla de una versión → lo legítimo: por entrada de la versión, el menor de los
                 # dos; cuántas entradas pasaban del tope, a $B_AUTO/sin-cabida
    LC_ALL=C awk -F'\t' -v sc="$B_AUTO/sin-cabida" 'FILENAME == ARGV[1] { c[$1 "\t" $2 "\t" $3] = $4; next }
      NF >= 4 { k = $1 "\t" $2 "\t" $3; m = $4 + 0; t = (k in c) ? c[k] + 0 : 0; if (t < m) { m = t; n++ }
        if (m > 0) print k "\t" m }
      END { print n + 0 > sc }' "$1" "$2"
  }
  B_SEQ=$(git log --first-parent --reverse --format=%H -- "$B_TABLA" b-citas.awk 2>/dev/null)
  B_C0=""
  for c in $B_SEQ; do git cat-file -e "$c:$B_TABLA" 2>/dev/null && { B_C0=$c; break; }; done
  if [ -z "$B_C0" ]; then
    echo "  ⚠️  $B_TABLA no está en git: es la tabla que se crea, y no se compara con nada."
    B_TECHO_OK=0
  else
    B_DECLS_A=$(b_abs "$B_DECLS"); B_ENV_A=$(b_abs "$B_ENV"); B_SOND_A=$(b_abs "$B_SOND"); B_MOD_A=$(b_abs "$B_MOD")
    B_RUT_A=$(b_abs "$B_RUT")
    b_version "$B_C0" > "$B_LEG"
    B_NUC=$B_C0; B_NV=1; B_NN=0; B_NSC=0; B_NF=0; B_RAIZ=""; B_TRAS=0
    for c in $B_SEQ; do
      if [ "$B_TRAS" = "0" ]; then [ "$c" = "$B_C0" ] && B_TRAS=1; continue; fi
      B_NV=$((B_NV + 1))
      cp "$B_LEG" "$B_AUTO/tope.tsv"
      if [ "$(git rev-parse -q --verify "$c:b-citas.awk")" != "$(git rev-parse -q --verify "$B_NUC:b-citas.awk")" ]; then
        B_NN=$((B_NN + 1))
        git show "$B_NUC:b-citas.awk" > "$B_AUTO/viejo.awk" 2>/dev/null; git show "$c:b-citas.awk" > "$B_AUTO/nuevo.awk" 2>/dev/null
        b_de_mas "$B_AUTO/viejo.awk" "$B_AUTO/nuevo.awk" "$c" > "$B_AUTO/de-mas.tsv"; B_R=$?
        if [ "$B_R" = "0" ]; then b_suma "$B_LEG" "$B_AUTO/de-mas.tsv" > "$B_AUTO/tope.tsv"
        # otra interfaz: la versión se toma tal cual, y la historia empieza ahí
        elif [ "$B_R" = "2" ]; then b_version "$c" > "$B_AUTO/tope.tsv"; B_RAIZ=$c
        # un núcleo que falla con las entradas de hoy no deja subir nada (si no, romperlo en un commit intermedio
        # blanquearía la tabla del siguiente)
        else B_NF=$((B_NF + 1)); fi
      fi
      b_version "$c" > "$B_AUTO/version.tsv"
      b_minimo "$B_AUTO/tope.tsv" "$B_AUTO/version.tsv" > "$B_LEG"
      B_NSC=$((B_NSC + $(cat "$B_AUTO/sin-cabida")))
      B_NUC=$c
    done
    # el árbol: lo legítimo, más lo que vea de más su núcleo si cambia
    cp "$B_LEG" "$B_TECHO"
    if [ "$B_NUCLEO_CAMBIA" = "1" ]; then
      git show "$B_NUC:b-citas.awk" > "$B_AUTO/viejo.awk" 2>/dev/null
      b_de_mas "$B_AUTO/viejo.awk" "$(b_abs b-citas.awk)" "" > "$B_AUTO/de-mas.tsv"; B_R=$?
      if [ "$B_R" = "0" ]; then b_suma "$B_LEG" "$B_AUTO/de-mas.tsv" > "$B_TECHO"
      elif [ "$B_R" = "2" ]; then
        echo "  ⚠️  el núcleo de $(git rev-parse --short "$B_NUC") lee otras entradas que el del árbol: la tabla se rehace sin comparar (lo tiene que decir su ADR)."
        B_TECHO_OK=0
      else
        echo "  ⚠️  el núcleo de $(git rev-parse --short "$B_NUC") falla con las entradas de hoy: la tabla no puede subir."
      fi
    fi
    B_TXT_NF=""; [ "$B_NF" -gt 0 ] && B_TXT_NF="; en $B_NF falla un núcleo, y no sube nada"
    echo "  historia de la tabla: $B_NV versiones desde $(git rev-parse --short "$B_C0"), $B_NN con otro núcleo${B_RAIZ:+ (la de $(git rev-parse --short "$B_RAIZ"), con otra interfaz, se toma tal cual)}$B_TXT_NF; $B_NSC entradas subieron sin cabida y no cuentan"
  fi
  if [ "$B_TECHO_OK" = "1" ]; then
    B_SOBRE=$(LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { t[$1 "\t" $2 "\t" $3] = $4; next }
        $0 != "" { k = $1 "\t" $2 "\t" $3; if (!(k in t) || $4 + 0 > t[k] + 0) print }' "$B_TECHO" <(printf '%s\n' "$B_TAB_HOY"))
    if [ -n "$B_SOBRE" ]; then
      B_SIN_ADR=$B_SOBRE
      if [ -n "$B_SUBE_ADR" ] && b_adr_existe "$B_SUBE_ADR"; then
        B_TXT_ADR=$(b_adr_texto "$B_SUBE_ADR")
        B_SIN_ADR=$(printf '%s\n' "$B_SOBRE" | while IFS=$'\t' read -r c k d n; do
          printf '%s' "$B_TXT_ADR" | grep -qF -- "$k" || printf '%s\t%s\t%s\t%s\n' "$c" "$k" "$d" "$n"; done)
        [ -z "$B_SIN_ADR" ] && echo "  ⚠️  $(printf '%s\n' "$B_SOBRE" | grep -c .) entradas sobre su techo, y $B_SUBE_ADR las nombra todas."
      fi
      if [ -n "$B_SIN_ADR" ]; then
        echo "  ❌ la tabla tiene entradas por ENCIMA de su techo (sólo baja; subirla pide un ADR que las nombre):"
        printf '%s\n' "$B_SIN_ADR" | head -5 | sed 's/^/      /'
        B_FAIL=1
      fi
    fi
  fi
  B_NT=$(printf '%s\n' "$B_TAB_HOY" | grep -c . || true)
  B_NC=$(printf '%s\n' "$B_TAB_HOY" | awk -F'\t' '{ s += $4 } END { print s + 0 }')
  echo "  deuda declarada: $B_NC citas muertas en $B_NT entradas (clase, clave, documento) de $B_TABLA; hoy, $(grep -c '^B' "$B_CIT")"
else
  echo "  deuda declarada: SIN MEDIR"
fi
rm -rf "$B_AUTO" "$B_CIT" "$B_ACT" "$B_TECHO" "$B_HIST" "$B_LEG"
