# b-citas.awk — las citas MUERTAS de los documentos: el núcleo de [B] de check-doc-sync.bash (T04, ADR-166).
# ⛔ Este fichero es IDÉNTICO, byte a byte, en ROBINSON_PlusPlus y en FOL, y check-doc-sync.bash de RPP lo comprueba.
#
# Uso: LC_ALL=C awk -f b-citas.awk VIVOS ENV SONDEOS MODULOS RUTAS HIST DOC1.md [DOC2.md …]
#   VIVOS    un nombre declarado por línea (el nombre entero y su último componente), del proyecto y de cuarentena/;
#   ENV      «nombre<TAB>clase»: P (constante del proyecto), L (constante de Lean), O (opción), M (módulo de Lean), T (una
#            orden: un token del analizador que empieza por «#», como `#print` o `#pureza_titulares`);
#   SONDEOS  «nombre|fichero» por cada declaración de un sondeo (también de los archivados: «etiqueta:sondeos/X.lean»);
#   MODULOS  los módulos que existen (el cierre de las librerías, sondeos/ y scripts/), con puntos, y cada tramo de ellos;
#   RUTAS    los ficheros versionados de RPP y de FOL (y con el repo delante), las etiquetas de git y «etiqueta:ruta»;
#            una línea que empieza por «=» entra sólo entera, sin sus sufijos (las copias retiradas de cuarentena/);
#   HIST     los nombres que el proyecto declaró ALGUNA VEZ y los módulos que tuvo (de la historia de git de los dos repos).
# Emite, por cada cita no absuelta, «B|clave|cita|fichero:línea» (un identificador) o «B2|ruta|cita|fichero:línea» (un
# fichero que no existe); y «V|fichero:línea» por cada valla de código o comentario HTML que queda ABIERTO al acabar un
# documento (el resto del documento no se ha mirado: quien llama lo da por NO MEDIDO).
#
# QUÉ ES UNA CITA. Lo que va entre comillas invertidas en la prosa, con las reglas de CommonMark: fuera de las vallas
# (``` y ~~~, también dentro de una cita `>`; una línea que empieza por ``` y lleva otra comilla detrás es código EN
# LÍNEA), fuera de los comentarios HTML que no están dentro de una cita, con tiras de n comillas, sin las comillas
# escapadas (\`), con un espacio menos a cada lado, y siguiendo en la línea siguiente del mismo párrafo si no se cierra
# (no a través de un ítem de lista nuevo ni de una línea `>` vacía).
# De una cita se miran sus PIEZAS: la cita entera si es un identificador o una ruta; si no (una firma, una lista de
# axiomas, `exact nombre h`), cada palabra suya con forma de declaración (`_`, `.`, `'` o camelCase).
#   · un IDENTIFICADOR cuenta si tiene 3 caracteres o más y no es una palabra sola en minúsculas (`simp`), ni MAYÚSCULAS
#     de script (`T_UNIVERSO`), ni un hash (`f9941dc`), ni una hipótesis (`hPsiId`), ni la abreviatura o el patrón de
#     un axioma (`ax21`, `ax_TagDescriptor`). ⛔ Salvo que esté en HIST: un nombre que el proyecto declaró alguna vez no
#     se exime por su forma (`raa` murió con su regla, y sus citas saltan);
#   · una RUTA: con `/` o con una extensión conocida; `etiqueta:ruta`; con `*` (cuenta su directorio).
# QUÉ LA HACE VIVA. Un identificador sin punto: está en VIVOS, o es un componente del nombre de una constante del
# PROYECTO (un constructor, un campo, un espacio de nombres), un módulo, una opción o vocabulario; o, si el proyecto no
# lo declaró nunca, de Lean: un componente en Mayúscula (`CoreM`) o el último componente en camelCase (`getUsedConstants`).
# Con punto: el nombre entero de una constante, un espacio de nombres, un sufijo de dos o tres componentes de una
# constante (`Prf.listInd`, `Expr.hash`) o un módulo; o un campo sobre algo vivo (`foo.mp`, `Prf.rec`). Un homónimo de
# Lean (`imp_intro`, `Bounded`) NO absuelve a un nombre que el proyecto declaró. Una FAMILIA (acaba en `_`) vive si algún
# nombre vivo empieza así. Una ruta: es un sufijo de un fichero, un directorio, una etiqueta o una «etiqueta:ruta». Una
# orden (`#pureza_titulares`, `#print`): un token del analizador (T); si no lo es, se mira su nombre sin la «#».
# QUÉ LA ABSUELVE. Un MARCADOR de ESTADO (retirado, borrado, archivado, propuesto, candidato, hipotético, descartado,
# muerto, histórico, «falta», «pendiente», «por construir», «no existe»…), palabra entera, a 100 bytes o menos de la
# cita, sin cruzar una celda de tabla, sobre la línea con las citas en blanco; o, si la declara un sondeo, que la línea
# nombre ese sondeo (`sondeos/X` o `X.lean`). ⛔ La fecha NO es un marcador, ni los verbos corrientes («necesita»,
# «pide», «exige», «abierta», «hace falta»): una cita muerta seguida de «hace falta» no está marcada.
BEGIN {
  W = 100
  L = "([A-Za-z_]|[\303-\337][\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])"
  C = "([A-Za-z0-9_'!?]|[\303-\337][\200-\277]|\342(\202|\204|\205|\261)[\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])"
  IDENT = "^" L C "*([.]" L C "*)*$"
  PALABRA = L C "*([.]" L C "*)*"
  EXT = "[.](lean|md|bash|sh|py|awk|ps1|txt|json|yml|yaml|tsv|csv|olean|tex|pdf|htm|html|toml)$"
  NOLETRA = "(^|[^a-z\200-\377])"
  FINP = "([^a-z\200-\377]|$)"
  # cada palabra entera, con sus terminaciones: «borrador» no es «borrado», ni «faltaban» es «falta»
  MARK = NOLETRA "((retirad|borrad|eliminad|archivad|descartad|propuest|candidat|hipot(e|\303\251)tic|hist(o|\303\263)ric|muert|desaparecid|obsolet|renombrad|sustituid|reemplazad)(o|a|os|as)"
  MARK = MARK "|legacy|inexistentes?|faltan?|pendientes?|sin materializar|sin medir|no existen?|ya no existen?|tampoco existen?"
  MARK = MARK "|se (borr|retir|elimin|archiv|descart)(o|\303\263|aron)|desapareci(o|\303\263)"
  MARK = MARK "|aqu(i|\303\255) viv(i|\303\255)a|habr(i|\303\255)a que|por (construir|hacer|medir|escribir|demostrar|decidir|probar))" FINP
  MARK = MARK "|\342\217\263|\360\237\227\221"
  # «hace falta» (y sus formas) es «se necesita»: no marca nada
  HACERFALTA = NOLETRA "(hace|hac(i|\303\255)a|hacen|hac(i|\303\255)an|hizo|haciendo|har(a|\303\241)|har(i|\303\255)an?|haga|hagan|hubiera hecho) falta" FINP
  nv = split("Prop Type Sort lean_lib leanOptions globs andSubmodules submodules default_target moreServerArgs", vz, " ")
  for (i = 1; i <= nv; i++) VOCAB[vz[i]] = 1
}
FILENAME == ARGV[1] { vivo[$0] = 1; next }
FILENAME == ARGV[2] {
  if ($0 == "") next
  split($0, e2, "\t"); n0 = e2[1]; c0 = e2[2]
  if (c0 == "O") { opcion[n0] = 1; next }
  if (c0 == "T") { orden[n0] = 1; next }
  if (c0 == "M") { modulo[n0] = 1; next }
  entero[n0] = 1
  nc = split(n0, cz, ".")
  if (nc >= 2) suf[cz[nc - 1] "." cz[nc]] = 1
  if (nc >= 3) suf[cz[nc - 2] "." cz[nc - 1] "." cz[nc]] = 1
  for (i = 1; i <= nc; i++) { if (c0 == "P") p1[cz[i]] = 1; else l1[cz[i]] = 1 }
  if (c0 != "P") l1ult[cz[nc]] = 1
  u = n0; while (sub(/[.][^.]*$/, "", u)) { if (u in espacio) break; espacio[u] = 1 }
  next
}
FILENAME == ARGV[3] { p = index($0, "|"); k = substr($0, 1, p - 1); sond[k] = sond[k] "|" substr($0, p + 1); next }
FILENAME == ARGV[4] { modulo[$0] = 1; next }
# cada ruta entra con todos sus sufijos de fichero y de directorio: los documentos citan `Meta/Rosser.lean` (desde la
# librería), `FOL/Semantics.lean` (desde FOL) o `Rosser.lean` a secas; «etiqueta:ruta» y las de «=» entran tal cual
FILENAME == ARGV[5] {
  if (substr($0, 1, 1) == "=") { ruta[substr($0, 2)] = 1; next }
  if (index($0, ":")) { ruta[$0] = 1; next }
  n = split($0, pz, "/"); acc = ""
  for (i = n; i >= 1; i--) { acc = (acc == "") ? pz[i] : pz[i] "/" acc; ruta[acc] = 1 }
  d = ""; for (i = 1; i < n; i++) { d = (d == "") ? pz[i] : d "/" pz[i]; dd = d
    while (1) { ruta[dd] = 1; if (!sub(/^[^\/]*\//, "", dd)) break } }
  next
}
FILENAME == ARGV[6] { hist[$0] = 1; next }
# ── los documentos ──
FNR == 1 { cierra_doc(); doc = FILENAME; valla = 0; vq = 0; abierta = 0; html = 0 }
{
  x = $0
  # la cita `>` (para las vallas dentro de una cita)
  q = x; cita_md = 0; while (sub(/^ {0,3}> ?/, "", q)) cita_md = 1
  if (valla) {
    if (vq && !cita_md) { valla = 0 }
    else {
      if (q ~ ("^ {0,3}" vchar vchar vchar) && cierra_valla(q)) valla = 0
      next
    }
  }
  if (!html && q ~ /^ {0,3}(```|~~~)/) {
    r = q; sub(/^ */, "", r); vchar = substr(r, 1, 1)
    match(r, (vchar == "`") ? "^`+" : "^~+"); vlen = RLENGTH; info = substr(r, vlen + 1)
    if (!(vchar == "`" && index(info, "`"))) { valla = 1; vq = cita_md; vlin = FNR; abierta = 0; next }
  }
  # un comentario HTML que viene de la línea anterior: hasta su cierre, no es prosa
  if (html) { p = index(x, "-->"); if (!p) next; x = sprintf("%" (p + 2) "s", "") substr(x, p + 3); html = 0 }
  # las comillas escapadas (\`) son texto
  gsub(/\\`/, "  ", x)
  # una cita no sigue a través de un párrafo nuevo, una tabla, un título, un ítem de lista nuevo o una línea `>` vacía
  if (x ~ /^[ \t]*$/ || x ~ /^\|/ || x ~ /^#/ || x ~ /^[ \t]*([-*+]|[0-9]+[.)])[ \t]/ || x ~ /^ {0,3}>[ \t]*$/) abierta = 0
  # una cita de UNA comilla que viene de la línea anterior: hasta su comilla de cierre, es código; se mira entera al
  # cerrarse
  pendiente_t = ""
  if (abierta) {
    p = cierre1(x, 1)
    if (!p) { pend = pend " " x; next }
    pendiente_t = pend " " substr(x, 1, p - 1); pendiente_fin = p
    x = sprintf("%" p "s", "") substr(x, p + 1); abierta = 0
  }
  # las citas, y los comentarios HTML que quedan FUERA de ellas
  escanea(x)
  while ((p = html_fuera(x)) > 0) {
    e = index(substr(x, p + 4), "-->")
    if (e) { x = substr(x, 1, p - 1) sprintf("%" (e + 6) "s", "") substr(x, p + e + 6) }
    else { x = substr(x, 1, p - 1); html = 1; hlin = FNR }
    escanea(x)
  }
  # la línea con cada cita en BLANCO, del mismo largo: la ventana del marcador se corta de aquí
  lb = ""; pos = 1
  for (i = 1; i <= ns; i++) { lb = lb substr(x, pos, sini[i] - pos) sprintf("%" (sfin[i] - sini[i] + 1) "s", ""); pos = sfin[i] + 1 }
  if (abre1) { lb = lb substr(x, pos, abre1 - pos) sprintf("%" (length(x) - abre1 + 1) "s", ""); abierta = 1; pend = substr(x, abre1 + 1) }
  else lb = lb substr(x, pos)
  xs = x
  if (pendiente_t != "") { ini = 1; fin = pendiente_fin; piezas(pendiente_t) }
  for (i = 1; i <= ns; i++) { ini = sini[i]; fin = sfin[i]; piezas(scont[i]) }
}
END { cierra_doc() }
function cierra_doc() {
  if (doc != "" && valla) print "V|" doc ":" vlin
  if (doc != "" && html) print "V|" doc ":" hlin
  valla = 0; html = 0
}
function cierra_valla(r,   z) { z = r; sub(/^ */, "", z); match(z, (vchar == "`") ? "^`+" : "^~+")
  return (RLENGTH >= vlen && substr(z, RLENGTH + 1) ~ /^[ \t]*$/) }
# la primera tira de exactamente UNA comilla desde la posición i (0 si no hay)
function cierre1(x, i,   p, j) {
  while ((p = index(substr(x, i), "`")) > 0) {
    p = i + p - 1; j = p; while (substr(x, j, 1) == "`") j++
    if (j - p == 1) return p
    i = j
  }
  return 0
}
# las citas de la línea: sini, sfin (las comillas de los extremos) y scont, ns de ellas; abre1, la posición de una
# comilla sola sin cierre (la cita sigue en la línea siguiente), o 0. Una tira de n ≥ 2 sin cierre es texto.
function escanea(x,   i, p, j, n, k, m, hay, c) {
  ns = 0; abre1 = 0; i = 1
  while ((p = index(substr(x, i), "`")) > 0) {
    p = i + p - 1; j = p; while (substr(x, j, 1) == "`") j++
    n = j - p; k = j; hay = 0
    while ((m = index(substr(x, k), "`")) > 0) {
      m = k + m - 1; k = m; while (substr(x, k, 1) == "`") k++
      if (k - m == n) { hay = 1; break }
    }
    if (hay) {
      c = substr(x, j, m - j)
      if (c ~ /^ / && c ~ / $/ && c ~ /[^ ]/) c = substr(c, 2, length(c) - 2)
      ns++; sini[ns] = p; sfin[ns] = k - 1; scont[ns] = c; i = k
    }
    else { if (n == 1) { abre1 = p; return } ; i = j }
  }
}
# la primera «<!--» fuera de las citas (0 si no hay)
function html_fuera(x,   p, d, i, dentro) {
  d = 0
  while ((p = index(substr(x, d + 1), "<!--")) > 0) {
    p = d + p; dentro = 0
    for (i = 1; i <= ns; i++) if (p >= sini[i] && p <= sfin[i]) dentro = 1
    if (abre1 && p >= abre1) dentro = 1
    if (!dentro) return p
    d = p
  }
  return 0
}
# las piezas de una cita: la cita entera si es un identificador o una ruta; si no, sus palabras con forma de declaración
function piezas(t,   u, w, cab, nt, tz, it) {
  gsub(/\342\200\221|\342\200\223/, "-", t)
  if (t ~ /:[0-9][0-9,:-]*$/) sub(/:[0-9][0-9,:-]*$/, "", t)
  if (t ~ /^[A-Za-z0-9_.\/*-]+(:[A-Za-z0-9_.\/*-]+)?$/ && (t ~ /\// || t ~ EXT || t ~ /\*/ || t ~ /:/)) { examina(t, 0); return }
  cab = t; sub(/^@/, "", cab); sub(/[.]$/, "", cab)
  if (cab ~ IDENT) { examina(cab, 0); return }
  # por palabras separadas por blancos: una ruta entera (`check-doc-sync.bash`) se mira como ruta; lo demás, por sus
  # nombres con forma de declaración
  nt = split(t, tz, /[ \t]+/)
  for (it = 1; it <= nt; it++) {
    u = tz[it]; sub(/^[[({"'@]+/, "", u); sub(/[])},;:."']+$/, "", u)
    # una orden (`#pureza_titulares`) vive si el analizador la conoce; si no, se mira su nombre
    if (substr(u, 1, 1) == "#") { if (u in orden) continue; sub(/^#+/, "", u) }
    if (u ~ /^[A-Za-z0-9_.\/*-]+$/ && (u ~ /\// || u ~ EXT)) { examina(u, 1); continue }
    while (match(u, PALABRA)) {
      w = substr(u, RSTART, RLENGTH); u = substr(u, RSTART + RLENGTH)
      sub(/[.]$/, "", w)
      if (w ~ /[_.']|[a-z][A-Z]/) examina(w, 1)
    }
  }
}
function examina(t, enpieza,   r, k, k2, clase, pre) {
  if (t ~ /^[A-Za-z0-9_.\/*-]+:[A-Za-z0-9_.\/*-]+$/) {
    # «etiqueta:ruta» (`archivo/sondeos-2026-10:sondeos/X.lean`)
    if (t in ruta) return
    clase = "B2"; k = t
  } else if (t ~ /^[A-Za-z0-9_.\/*-]+$/ && (t ~ /\// || t ~ EXT || t ~ /\*/) && !(t !~ EXT && t !~ /\*/ && t ~ /_[^\/]*$/)) {
    # (sin extensión y con `_` en el último tramo, `prf_x_left/right` abrevia dos nombres: no es una ruta)
    r = t; sub(/^(\.\.?\/)+/, "", r)
    if (index(r, "*")) { r = substr(r, 1, index(r, "*") - 1); sub(/[^\/]*$/, "", r) }
    sub(/\/$/, "", r)
    if (r !~ /[A-Za-z0-9]/ || r ~ /^[.][A-Za-z]+$/) return
    if ((r in ruta) || ((r ".lean") in ruta)) return
    clase = "B2"; k = t
  } else {
    if (t !~ IDENT) return
    # una variable de una o dos letras nunca cuenta; las demás formas exentas, sólo si el proyecto no las declaró
    if (length(t) < 3) return
    if (exenta(t) && !(t in hist)) return
    # una variable local con un campo (`h.symm`, `hcon.elim`) no es un nombre: su primer componente tiene forma exenta
    if (index(t, ".")) { pre = t; sub(/[.].*$/, "", pre); if (length(pre) < 3 || (exenta(pre) && !(pre in hist))) return }
    clase = "B"
    k = t; sub(/^([A-Z][A-Za-z0-9_]*[.])*/, "", k)
    if (vive(t)) return
    if (k ~ /_$/) {
      if (!(k in fam)) { fam[k] = 0; for (v in vivo) if (index(v, k) == 1) { fam[k] = 1; break } }
      if (fam[k]) return
    }
  }
  # el marcador, en la ventana [ini − W, fin + W] de la línea en blanco, sin cruzar un `|`, en minúsculas
  a = ini - W; if (a < 1) a = 1
  izq = substr(lb, a, ini - a); der = substr(lb, fin + 1, W)
  q2 = 0; while ((p = index(substr(izq, q2 + 1), "|")) > 0) q2 += p
  if (q2 > 0) izq = substr(izq, q2 + 1)
  p = index(der, "|"); if (p > 0) der = substr(der, 1, p - 1)
  ventana = tolower(izq " " der); gsub(HACERFALTA, " ", ventana)
  if (ventana ~ MARK) return
  if (clase == "B" && (k in sond) && nombra_sondeo(k)) return
  print clase "|" t "|" t "|" FILENAME ":" FNR
}
# ¿vive el identificador t? (sin el marcador ni el sondeo)
function vive(t,   k2, pre) {
  if (t in vivo) return 1
  if (index(t, ".")) {
    if ((t in entero) || (t in espacio) || (t in suf) || (t in modulo)) return 1
    # un campo sobre un TÉRMINO vivo: `foo.mp`, `prf_x.trans` (el prefijo empieza en minúscula). Sobre un espacio de
    # nombres o un tipo (`SinWTs.prf_borrado`) no: eso es un nombre calificado, y tiene que ser una constante
    k2 = t; sub(/.*[.]/, "", k2); pre = t; sub(/[.][^.]*$/, "", pre)
    if (pre ~ /^[a-z_]/ && k2 ~ /^[a-z0-9_]/ && vive(pre)) return 1
    return 0
  }
  if ((t in p1) || (t in modulo) || (t in opcion) || (t in VOCAB)) return 1
  # un nombre que el proyecto declaró alguna vez sólo lo absuelve el proyecto: un homónimo de Lean no basta
  if (t in hist) return 0
  if (t ~ /^[A-Z]/ && (t in l1)) return 1
  if (t ~ /^[a-z_][A-Za-z0-9_']*[A-Z]/ && (t in l1ult)) return 1
  return 0
}
# las formas exentas (si el nombre no se declaró nunca)
function exenta(t) {
  return (t ~ /^[a-z]+$/ || t ~ /^[A-Z0-9_]+$/ || t ~ /^[0-9a-f]+$/ \
    || t ~ /^_?h[A-Z0-9_]/ || t ~ /^_?h[a-z][A-Z_]/ || t ~ /^ax[0-9]+[a-z]?$/ || t ~ /^ax_[A-Z][A-Za-z]*$/)
}
# ¿nombra la línea (sin sus comentarios HTML) un sondeo que declara `k`? (`sondeos/X`, o `X.lean`)
function nombra_sondeo(k,   nf, fs, i, f, b) {
  nf = split(substr(sond[k], 2), fs, "|")
  for (i = 1; i <= nf; i++) {
    f = fs[i]; sub(/^.*:/, "", f); sub(/[.]lean$/, "", f); b = f; sub(/.*\//, "", b)
    if (match(xs, f "([^A-Za-z0-9_]|$)")) return 1
    if (match(xs, "(^|[^A-Za-z0-9_/])" b "[.]lean")) return 1
  }
  return 0
}
