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
#   B_BASE_REF  la BASE VERIFICADA: lo último que la CI aprobó (por omisión `refs/remotes/origin/master`; la CI de FOL
#               pasa el commit de antes de un push a master);
#   B_SUBE_ADR  vacío, o el ADR que deja subir entradas concretas; y las funciones b_adr_texto ADR (su texto en el árbol)
#               y b_adr_texto_base ADR (su texto en la base, vacío si no está): el ADR tiene que ser NUEVO respecto de la
#               base y nombrar cada entrada que sube entera, «`clave` · documento · citas».
# Deja B_FAIL (1 si rompe) y B_MEDIDO (0 si no pudo medir), e imprime lo que encuentra.
#
# 🔑 EL TRINQUETE. Una cita muerta de más que la tabla es rojo; una de menos, también, hasta que `--b-deuda` baje la
# tabla. Y la tabla tiene TECHO: la tabla de la BASE VERIFICADA (por omisión `refs/remotes/origin/master`, con su nombre
# entero), que tiene que ser antepasado de HEAD y tener la tabla si tiene el núcleo. Nada de lo que pasó entre la base y
# HEAD cuenta (ni un commit intermedio, ni una fusión, ni un núcleo debilitado y restaurado).
#   · Un cambio del NÚCLEO (b-citas.awk distinto del de la base) va SOLO: los documentos de la lista no pueden cambiar
#     respecto de la base. Entonces el techo es máx(0, base + nuevo − viejo) entrada a entrada, con el núcleo del árbol
#     (nuevo) y el de la base (viejo) sobre los MISMOS documentos, en el mismo directorio aparte y con las entradas de
#     hoy: lo que el núcleo nuevo deja de ver BAJA el techo. Si el de la base no lee las entradas, falla o deja una valla
#     abierta, no sube nada. Sólo se ejecutan esos dos núcleos.
#   · Un documento con deuda en la base no sale de la lista, ni sigue en git fuera de ella, ni se renombra fuera; si se
#     renombra dentro, su deuda va con él.
#   · Subir una entrada fuera de eso pide un ADR NUEVO (que no está en la base) que nombre cada entrada entera:
#     «`clave` · documento · citas» (B_SUBE_ADR); una vez en la base, su tabla ya es el techo.
# (Antes, ADR-166: el techo rehacía la historia de la tabla, y la tercera revisión lo subió con la CI en verde; la cuarta,
# sobre la primera versión de la base verificada, encontró más: ADR-167.)
# La tabla vive en la misma ruta en los dos repos, y se fija AQUÍ.
B_TABLA=doc/control/b-deuda.tsv
B_FAIL=0; B_MEDIDO=1; B_TAB=$(printf '\t')
# (un objeto reemplazado con `git replace` no engaña a git en local)
export GIT_NO_REPLACE_OBJECTS=1
B_AUTO=$(mktemp -d); B_CIT=$(mktemp); B_ACT=$(mktemp); B_TECHO=$(mktemp); B_HIST=$(mktemp)
for d in $B_DOCS_LISTA; do
  [ -f "$d" ] || { echo "  ❌ falta el documento $d: uno que desaparece no puede llevarse su deuda en silencio."; B_FAIL=1; }
done
B_DOCS=""; for d in $B_DOCS_LISTA; do [ -f "$d" ] && B_DOCS="$B_DOCS $d"; done
# ⭐ AUTOTEST de salida EXACTA: una cita de cada clase —viva por cada vía; muerta pese a un marcador lejano, de otra
# celda, una fecha, su propio nombre, un verbo corriente, «hace falta», un comentario HTML, un homónimo de Lean, su forma
# o su posición dentro de la cita; un marcador de la cita VECINA, uno negado o dentro de una ruta; una familia por glob,
# una abreviatura con barra, una prima, un alias y un directorio que ya no existe— y las reglas de CommonMark. Si no da
# exactamente lo esperado, no se mide.
printf '%s\n' vivo_ok vivo_fam_uno "vivo_prima'" > "$B_AUTO/vivos"
printf 'Lean.Name\tL\nimp_intro\tL\nCoreM.run\tL\nStd.Bounded.LE\tL\nLean.Expr.getUsedConstants\tL\nQuot.sound\tL\nROBINSON_PlusPlus.X.Prf.listInd\tP\nROBINSON_PlusPlus.X.SinWTs.vivo_ok\tP\nautoImplicit\tO\nInit.Classical\tM\n#mi_orden\tT\nROBINSON_PlusPlus.X.Alias.campo_alias\tP\tA\nStd.DirViejo.x\tL\n' > "$B_AUTO/env"
printf '%s\n' 'solo_en_sondeo|sondeos/Sondeo.lean' > "$B_AUTO/sond"
printf '%s\n' ROBINSON_PlusPlus.Meta.Rosser Meta.Rosser Rosser > "$B_AUTO/mod"
printf '%s\n' ROBINSON_PlusPlus/Meta/Rosser.lean sondeos/Sondeo.lean doc/registro/x.txt archivo/tag-1 'archivo/tag-1:sondeos/Viejo.lean' \
  check-doc-sync.bash '=cuarentena/retiradas/Viejo.lean' Makefile > "$B_AUTO/rut"
printf '%s\n' raa Bounded /DirViejo > "$B_AUTO/hist"
B_RELLENO=$(printf '%0110d' 0 | tr 0 x)
printf '%s\n' \
  '`vivo_ok`, `Lean.Name`, `listInd`, `Prf.listInd`, `CoreM`, `getUsedConstants`, `autoImplicit`, `Init.Classical`, `Rosser`.' \
  '`Meta/Rosser.lean:12‑20`, `doc/registro`, `archivo/tag-1`, `archivo/tag-1:sondeos/Viejo.lean`, `Meta/*.lean`, `@vivo_ok`, `Makefile`.' \
  '`bash check-doc-sync.bash --b-deuda`, `vivo_ok.mp`, `[propext, Quot.sound]` y `Build completed (1 jobs)`.' \
  'La orden `#mi_orden` corre en el build; `#orden_muerta`, no.' \
  '`muerto_t` toma `muerto_u` … falta `muerto_v`.' \
  '`muerto_w1`, `muerto_w2` y `muerto_w3` (retirados).' \
  '`muerto_x` no está retirado.' \
  '`muerto_y` en cuarentena/librerias-retiradas/ y en https://x/retiradas.' \
  "\`vivo_fam_*\` y \`muerto_fam_*\`; \`muerto_ab/vivo_ok\`; \`exact vivo_prima'\` y \`exact muerto_prima'\`." \
  '`Alias.campo_alias`, pero `campo_alias` a secas; `DirViejo`.' \
  '`muerto_z4` no se ha retirado; `muerto_z5` no es código muerto. La propuesta usa `muerto_z6`; por falta de `muerto_z7`.' \
  'Retirado: nada. `muerto_z8` vive. Usa `muerto_z9` (`muerto_y0`, renombrado). `muerto_y1` retirado `muerto_y2`.' \
  '`axiom` y `⊢`, retirados con esa capa: `muerto_w4`, `muerto_w5`. `muerto_w6` como hipótesis, también retirado. `muerto_w7` vive.' \
  '`Muerto.cosa.*`, `Lean.*`, `Viejo*.lean`, `Meta/Ros*.lean`, `ROBINSON_PlusPlus/Meta/Order` y `vivo_fam_uno/dos`.' \
  "En \`C:\\msys64\\\` con \`muerto_z3\`." \
  '- ```lean' '  ejemplo' '  ```' '`muerto_z1` tras la valla de un ítem.' \
  '' 'Un <!-- suelto.' '' '`muerto_z2` tras el comentario suelto.' '' 'Fin -->.' \
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
B_AUTO_ESP="B2|Meta/NoExiste.lean;B2|ROBINSON_PlusPlus/Meta/Order;B2|Viejo*.lean;B2|Viejo.lean;B2|archivo/tag-1:sondeos/Nada.lean;B|Borrado.vivo_ok;B|Bounded;B|DirViejo;B|Muerto.cosa.*;B|SinWTs.prf_borrado;B|campo_alias;B|imp_intro;B|muerto_ab;B|muerto_b;B|muerto_c;B|muerto_d;B|muerto_e_;B|muerto_fam_*;B|muerto_h;B|muerto_i;B|muerto_j;B|muerto_k;B|muerto_l;B|muerto_m;B|muerto_n;B|muerto_o;B|muerto_p;B|muerto_prima';B|muerto_q;B|muerto_r;B|muerto_retirado_g;B|muerto_s;B|muerto_t;B|muerto_u;B|muerto_w7;B|muerto_x;B|muerto_y;B|muerto_y1;B|muerto_y2;B|muerto_z1;B|muerto_z2;B|muerto_z3;B|muerto_z4;B|muerto_z5;B|muerto_z6;B|muerto_z7;B|muerto_z8;B|muerto_z9;B|orden_muerta;B|raa;B|solo_en_sondeo;B|teorema_borrado.mk;B|vivo_fam_dos;V|doc.md:54;"
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
# Los directorios que tuvo un `.lean` entran como «/X» (a ésos sólo no los absuelve un homónimo de Lean), y las palabras
# clave que «class inductive» dejaría como nombre, no.
if [ "$B_MEDIDO" = "1" ]; then
  for g in $B_GITS; do
    if [ "$(git -C "$g" rev-parse --is-shallow-repository 2>/dev/null)" != "false" ]; then
      echo "  ❌ NO PUDE MEDIR [B]: $g es un clon SUPERFICIAL (o no es un repo): su historia no da los nombres de siempre."
      B_FAIL=1; B_MEDIDO=0
    fi
  done
fi
if [ "$B_MEDIDO" = "1" ]; then
  B_PROPIO=1
  for g in $B_GITS; do
    { git -C "$g" log HEAD --tags -p --format= -- '*.lean'
      if [ "$B_PROPIO" = "1" ]; then
        git -C "$g" diff HEAD -- '*.lean'
        git -C "$g" ls-files -o --exclude-standard -- '*.lean' | while IFS= read -r f; do sed 's/^/+/' "$g/$f"; done
      fi; } 2>/dev/null | LC_ALL=C grep -E "$B_DECL_LINEA" | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" \
      | LC_ALL=C grep -vxE 'inductive|structure|class|instance|where|extends|deriving|theorem|lemma|def|abbrev|axiom|opaque'
    { git -C "$g" log HEAD --tags --name-only --format= -- '*.lean'
      if [ "$B_PROPIO" = "1" ]; then git -C "$g" ls-files -co --exclude-standard -- '*.lean'; fi; } 2>/dev/null \
      | LC_ALL=C awk -F/ 'NF { b = $NF; sub(/[.]lean$/, "", b); print b; for (i = 1; i < NF; i++) print "/" $i }'
    B_PROPIO=0
  done | grep . | LC_ALL=C sort -u > "$B_HIST"
  if [ "$(grep -vc '^/' "$B_HIST")" -lt 1000 ] || ! grep -qxF raa "$B_HIST"; then
    echo "  ❌ NO PUDE MEDIR [B]: la historia de git no da los nombres de siempre."
    B_FAIL=1; B_MEDIDO=0
  fi
fi
# La medición se hace en un directorio aparte con COPIAS de los documentos (y sólo eso), con las rutas de siempre: el
# núcleo del árbol mide igual aquí que cuando se le compara con el de la base (ADR-167: un núcleo que distinguiera las
# dos mediciones podría darse crédito), y con un tiempo límite.
b_abs() { case "$1" in /*) printf '%s' "$1" ;; *) printf '%s/%s' "$(pwd)" "$1" ;; esac; }
if [ "$B_MEDIDO" = "1" ]; then
  B_DECLS_A=$(b_abs "$B_DECLS"); B_ENV_A=$(b_abs "$B_ENV"); B_SOND_A=$(b_abs "$B_SOND"); B_MOD_A=$(b_abs "$B_MOD")
  B_RUT_A=$(b_abs "$B_RUT"); B_NUC_A=$(b_abs b-citas.awk)
  B_DIR=$B_AUTO/docs; mkdir -p "$B_DIR"
  for d in $B_DOCS; do mkdir -p "$B_DIR/$(dirname "$d")"; tr -d '\r' < "$d" > "$B_DIR/$d"; done
  if ! ( cd "$B_DIR" && LC_ALL=C timeout 600 awk -f "$B_NUC_A" "$B_DECLS_A" "$B_ENV_A" "$B_SOND_A" "$B_MOD_A" "$B_RUT_A" \
         "$B_HIST" $B_DOCS ) > "$B_CIT"; then
    echo "  ❌ NO PUDE MEDIR [B]: b-citas.awk falló (o tardó más de diez minutos)."
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
  # la BASE VERIFICADA: lo último que la CI aprobó; tiene que existir y ser antepasado de HEAD. Por omisión, la rama
  # remota con su nombre ENTERO (`refs/remotes/origin/master`): una etiqueta llamada `origin/master` le ganaría a la
  # forma corta (la cuarta revisión lo midió)
  B_BASE_REF=${B_BASE_REF:-refs/remotes/origin/master}
  case "$B_BASE_REF" in 0000000*) B_BASE_REF=refs/remotes/origin/master ;; esac
  B_BASE=$(git rev-parse -q --verify "$B_BASE_REF^{commit}" 2>/dev/null)
  B_BASE_OK=1
  if [ -z "$B_BASE" ]; then
    echo "  ❌ no hay BASE VERIFICADA ($B_BASE_REF): sin ella la tabla no tiene techo (¿falta un git fetch?)."
    B_FAIL=1; B_BASE_OK=0
  elif ! git merge-base --is-ancestor "$B_BASE" HEAD 2>/dev/null; then
    echo "  ❌ HEAD no desciende de la base verificada ($B_BASE_REF, $(git rev-parse --short "$B_BASE")): rebase sobre ella."
    B_FAIL=1; B_BASE_OK=0
  elif [ "$B_BASE" = "$(git rev-parse HEAD)" ] && git diff --quiet HEAD -- "$B_TABLA" b-citas.awk $B_DOCS 2>/dev/null; then
    echo "  ℹ️  la base verificada es HEAD: el techo es la tabla de HEAD, y aquí no compara nada nuevo."
  fi
  b_base_tiene() { [ "$B_BASE_OK" = "1" ] && git cat-file -e "$B_BASE:$1" 2>/dev/null; }
  # ¿es el núcleo del árbol otro que el de la base? (--b-deuda-rehacer sólo vale entonces)
  B_NUCLEO_CAMBIA=1
  if b_base_tiene b-citas.awk && cmp -s <(git show "$B_BASE:b-citas.awk" | tr -d '\r') <(tr -d '\r' < b-citas.awk); then
    B_NUCLEO_CAMBIA=0
  fi
  # la base TIENE que tener la tabla si tiene el núcleo: si no, la tabla se ha movido o borrado (falla en cerrado)
  if [ "$B_BASE_OK" = "1" ] && b_base_tiene b-citas.awk && ! b_base_tiene "$B_TABLA"; then
    echo "  ❌ la base verificada tiene b-citas.awk y no tiene $B_TABLA: la tabla no puede cambiar de sitio ni nacer otra vez."
    B_FAIL=1
  fi
  # un documento con deuda en la base no sale de la lista si sigue en git, ni RENOMBRADO fuera de ella: su deuda no se
  # va en silencio. Renombrado dentro de la lista, su deuda lo sigue (B_AUTO/renombres: «viejo<TAB>nuevo»)
  : > "$B_AUTO/renombres"
  if b_base_tiene "$B_TABLA"; then
    git diff -M --name-status "$B_BASE" 2>/dev/null | LC_ALL=C awk -F'\t' '$1 ~ /^R/ { print $2 "\t" $3 }' > "$B_AUTO/movidos"
    B_FUERA=$(git show "$B_BASE:$B_TABLA" | tr -d '\r' | LC_ALL=C awk -F'\t' '!/^#/ && NF >= 4 { print $3 }' | LC_ALL=C sort -u \
      | while IFS= read -r d; do
          case " $B_DOCS_LISTA " in *" $d "*) continue ;; esac
          if git ls-files --error-unmatch "$d" > /dev/null 2>&1; then printf '%s (sigue en git)\n' "$d"; continue; fi
          n=$(LC_ALL=C awk -F'\t' -v d="$d" '$1 == d { print $2; exit }' "$B_AUTO/movidos")
          [ -z "$n" ] && continue
          case " $B_DOCS_LISTA " in
            *" $n "*) printf '%s\t%s\n' "$d" "$n" >> "$B_AUTO/renombres" ;;
            *) printf '%s (renombrado a %s, fuera de la lista)\n' "$d" "$n" ;;
          esac
        done)
    if [ -n "$B_FUERA" ]; then
      echo "  ❌ documentos con deuda en la base salen de la lista (con su deuda, en silencio):"
      printf '%s\n' "$B_FUERA" | head -5 | sed 's/^/      /'
      B_FAIL=1
    fi
  fi
  # un cambio del NÚCLEO va solo: con él, los documentos de la lista no pueden cambiar respecto de la base (súbelos en
  # otro push). Así su crédito se mide sobre los mismos documentos que la deuda, y el núcleo no puede distinguir las
  # dos mediciones (ADR-167)
  if [ "$B_BASE_OK" = "1" ] && [ "$B_NUCLEO_CAMBIA" = "1" ] && b_base_tiene b-citas.awk; then
    B_CAMBIAN=""
    for d in $B_DOCS; do
      if ! b_base_tiene "$d" || ! cmp -s <(git show "$B_BASE:$d" | tr -d '\r') "$B_DIR/$d"; then B_CAMBIAN="$B_CAMBIAN $d"; fi
    done
    if [ -n "$B_CAMBIAN" ]; then
      echo "  ❌ b-citas.awk cambia respecto de la base, y también estos documentos de la lista (un cambio del núcleo va solo):"
      printf '%s\n' $B_CAMBIAN | head -5 | sed 's/^/      /'
      B_FAIL=1
    fi
  fi
  B_CAB="# $B_TABLA — la deuda POR CITA de [B] (check-doc-sync.bash; T04, ADR-166 y ADR-167 de RPP).
# Una línea por (clase, clave, documento): cuántas citas muertas tiene. B, un identificador; B2, una ruta.
# Una cita muerta de más es rojo; una de menos, también, hasta bajar la tabla: bash check-doc-sync.bash --b-deuda.
# El techo de cada entrada es esta tabla en la base verificada (master): sólo baja, salvo lo que un cambio de
# b-citas.awk vea de más sobre los documentos de la base. Se arregla en el DOCUMENTO: la cita, o un marcador de estado
# («retirado», «archivado», «propuesto», «falta»…) a su lado, a 100 bytes o menos, en la misma celda.
# clase${B_TAB}clave${B_TAB}documento${B_TAB}citas"
  if [ "$B_DEUDA_MODO" = "2" ] || [ "$B_DEUDA_MODO" = "3" ]; then
    if [ "$B_FAIL" = "1" ]; then
      echo "  ❌ no reescribo la tabla con [B] en rojo (¿falta un documento?)."
    elif [ "$B_DEUDA_MODO" = "2" ] && [ -e "$B_TABLA" ]; then
      echo "  ❌ --b-deuda-inicial: $B_TABLA ya existe; la tabla sólo baja (--b-deuda), o se rehace con el núcleo."
      B_FAIL=1
    elif [ "$B_DEUDA_MODO" = "3" ] && [ "$B_NUCLEO_CAMBIA" = "0" ]; then
      echo "  ❌ --b-deuda-rehacer: b-citas.awk es el de la base verificada; la tabla sólo baja."
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
  # el TECHO: la tabla de la base verificada (con la deuda de un documento renombrado, en su ruta nueva) y, si el núcleo
  # cambia, más lo que el del árbol ve DE MÁS O DE MENOS que el de la base sobre los mismos documentos, que son los de
  # la base (ver arriba): techo = máx(0, base + nuevo − viejo), entrada a entrada (ver la cabecera)
  B_TECHO_OK=1
  b_version() {   # $1 = commit → su tabla, sin la cabecera; una entrada repetida cuenta por la menor
    git show "$1:$B_TABLA" 2>/dev/null | tr -d '\r' | LC_ALL=C awk -F'\t' '!/^#/ && NF >= 4 { k = $1 "\t" $2 "\t" $3
      if (!(k in m) || $4 + 0 < m[k]) m[k] = $4 + 0 } END { for (k in m) print k "\t" m[k] }'
  }
  if [ "$B_BASE_OK" != "1" ]; then
    B_TECHO_OK=0
  elif ! b_base_tiene "$B_TABLA"; then
    # (con el núcleo en la base, ya es rojo, arriba; sin él, es la tabla que se crea)
    b_base_tiene b-citas.awk \
      || echo "  ⚠️  la base verificada ($(git rev-parse --short "$B_BASE")) no tiene ni la tabla ni el núcleo: es la que se crea, y no se compara con nada."
    B_TECHO_OK=0
  else
    b_version "$B_BASE" > "$B_AUTO/base.tsv"
    LC_ALL=C awk -F'\t' -v OFS='\t' 'FILENAME == ARGV[1] { r[$1] = $2; next } ($3 in r) { $3 = r[$3] } { print }' \
      "$B_AUTO/renombres" "$B_AUTO/base.tsv" > "$B_TECHO"
    B_TXT_TECHO="la tabla de la base verificada, $(git rev-parse --short "$B_BASE") ($B_BASE_REF)"
    if [ "$B_NUCLEO_CAMBIA" = "1" ]; then
      git show "$B_BASE:b-citas.awk" > "$B_AUTO/viejo.awk" 2>/dev/null
      if ! grep -q 'ARGV\[6\]' "$B_AUTO/viejo.awk" \
         || ! ( cd "$B_DIR" && LC_ALL=C timeout 600 awk -f "$B_AUTO/viejo.awk" "$B_DECLS_A" "$B_ENV_A" "$B_SOND_A" "$B_MOD_A" \
                "$B_RUT_A" "$B_HIST" $B_DOCS ) > "$B_AUTO/viejo.out" 2>/dev/null || grep -q '^V|' "$B_AUTO/viejo.out"; then
        echo "  ⚠️  el núcleo de la base no lee las entradas de hoy, falla o no mide los documentos: la tabla no puede subir."
      else
        b_cuenta < "$B_AUTO/viejo.out" > "$B_AUTO/viejo.tsv"
        LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { c[$1 "\t" $2 "\t" $3] += $4; next }
            FILENAME == ARGV[2] { c[$1 "\t" $2 "\t" $3] -= $4; d[$1 "\t" $2 "\t" $3] -= $4; next }
            { c[$1 "\t" $2 "\t" $3] += $4; d[$1 "\t" $2 "\t" $3] += $4 }
            END { for (k in c) if (c[k] > 0) print k "\t" c[k]
                  for (k in d) { if (d[k] > 0) { ns++; s += d[k] } else if (d[k] < 0) { nb++; b -= d[k] } }
                  printf "%d entradas y %d citas de más, %d entradas y %d citas de menos\n", ns, s, nb, b > "/dev/stderr" }' \
          "$B_TECHO" "$B_AUTO/viejo.tsv" "$B_ACT" > "$B_AUTO/techo.tsv" 2> "$B_AUTO/delta.txt" && cp "$B_AUTO/techo.tsv" "$B_TECHO"
        B_TXT_TECHO="$B_TXT_TECHO, más lo que el núcleo del árbol ve de más o de menos que el suyo: $(cat "$B_AUTO/delta.txt")"
      fi
    fi
    echo "  techo: $B_TXT_TECHO"
  fi
  if [ "$B_TECHO_OK" = "1" ]; then
    B_SOBRE=$(LC_ALL=C awk -F'\t' 'FILENAME == ARGV[1] { t[$1 "\t" $2 "\t" $3] = $4; next }
        $0 != "" { k = $1 "\t" $2 "\t" $3; if (!(k in t) || $4 + 0 > t[k] + 0) print }' "$B_TECHO" <(printf '%s\n' "$B_TAB_HOY"))
    if [ -n "$B_SOBRE" ]; then
      B_SIN_ADR=$B_SOBRE
      if [ -n "$B_SUBE_ADR" ]; then
        B_TXT_ADR=$(b_adr_texto "$B_SUBE_ADR")
        if [ -z "$B_TXT_ADR" ]; then
          echo "  ❌ B_SUBE_ADR=$B_SUBE_ADR: ese ADR no existe."
        elif [ -n "$(b_adr_texto_base "$B_SUBE_ADR")" ]; then
          echo "  ❌ B_SUBE_ADR=$B_SUBE_ADR ya está en la base verificada: un ADR deja subir la tabla UNA vez, en el commit que lo trae."
        else
          # (cada entrada, ENTERA: «`clave` · documento · citas», con las citas que la tabla le da)
          B_SIN_ADR=$(printf '%s\n' "$B_SOBRE" | while IFS=$'\t' read -r c k d n; do
            printf '%s' "$B_TXT_ADR" | grep -qF -- "\`$k\` · $d · $n" || printf '%s\t%s\t%s\t%s\n' "$c" "$k" "$d" "$n"; done)
          [ -z "$B_SIN_ADR" ] && echo "  ⚠️  $(printf '%s\n' "$B_SOBRE" | grep -c .) entradas sobre su techo, y $B_SUBE_ADR, nuevo, nombra cada una."
        fi
      fi
      if [ -n "$B_SIN_ADR" ]; then
        echo "  ❌ la tabla tiene entradas por ENCIMA de su techo (sólo baja; subirla pide un ADR nuevo que nombre cada una: «\`clave\` · documento · citas»):"
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
rm -rf "$B_AUTO" "$B_CIT" "$B_ACT" "$B_TECHO" "$B_HIST"
