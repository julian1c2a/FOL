# b-citas.awk — las citas MUERTAS de los documentos: el núcleo de [B] de check-doc-sync.bash (T04 y ADR‑166 de RPP).
#
# Uso: LC_ALL=C awk -v MARK=ERE -v W=N -f b-citas.awk VIVOS ENV SONDEOS MODULOS RUTAS DOC1.md [DOC2.md …]
#   VIVOS    un nombre declarado por línea (el nombre entero y su último componente), del proyecto y de cuarentena/;
#   ENV      «nombre<TAB>P|L» por constante del entorno de Lean (P si es del proyecto); puede estar vacío;
#   SONDEOS  «nombre|fichero» por cada declaración de un sondeo;
#   MODULOS  los módulos que existen: su ruta con puntos y cada sufijo de ella (`ROBINSON_PlusPlus.Meta.Rosser`,
#            `Meta.Rosser`, `Rosser`);
#   RUTAS    los ficheros que existen, con su ruta desde la raíz de cada repo (`ROBINSON_PlusPlus/Meta/Rosser.lean`), y
#            las etiquetas de git (`archivo/t66-2026-10-18`): una ruta viva es un sufijo de una de ellas.
# Emite, por cada cita no absuelta, «B|clave|cita|fichero:línea» (un identificador) o «B2|ruta|cita|fichero:línea» (un
# fichero que no existe).
#
# QUÉ ES UNA CITA. Lo que va entre comillas invertidas, `X`, fuera de los bloques de código (```), si X es:
#   · un IDENTIFICADOR con forma de declaración: letras, cifras, `_`, `'`, `!`, `?`, subíndices y letras no ASCII, con
#     componentes separados por puntos; de 3 caracteres o más; y que no sea una palabra sola en minúsculas (`simp`,
#     `axiom`: palabras clave y tácticas), ni MAYÚSCULAS con `_` (`T_UNIVERSO`: variables de los scripts), ni un hash de
#     commit (`f9941dc`). Ésas son las tres formas que una declaración del proyecto no tiene (salvo una declaración de
#     una palabra en minúsculas, como `consistencia`: hueco declarado, la vigila [T] si es titular);
#   · una RUTA: con `/` o acabada en una extensión de fichero conocida.
# QUÉ LA HACE VIVA. Un identificador: su nombre entero o su último componente está en VIVOS; o el nombre entero en ENV;
# o el último componente es el de una constante del PROYECTO en ENV (constructores, campos); o es un MÓDULO; o es una
# FAMILIA (acaba en `_`) y algún nombre vivo empieza así. Una ruta: es un sufijo (de fichero o de directorio) de una
# ruta que existe en RPP o en FOL, sin los `../` del principio.
# QUÉ LA ABSUELVE. Un MARCADOR (MARK) a W bytes o menos de la cita, sin cruzar una celda de tabla (`|`), con las citas en
# blanco (un nombre muerto no se absuelve a sí mismo); o, si la declaran sondeos, que la línea nombre uno de ellos.
# ⛔ La fecha NO es un marcador desde ADR‑166 de RPP: una línea fechada no dice que lo que cita esté retirado.
# El CÓDIGO es el de ../ROBINSON_PlusPlus/b-citas.awk (cambian sólo los comentarios), y RPP lo comprueba.
BEGIN {
  L = "([A-Za-z_]|[\303-\337][\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])"
  C = "([A-Za-z0-9_'!?]|[\303-\337][\200-\277]|\342(\202|\204|\205|\261)[\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])"
  IDENT = "^" L C "*([.]" L C "*)*$"
  EXT = "[.](lean|md|bash|sh|py|awk|ps1|txt|json|yml|yaml|tsv|csv|olean|tex|pdf|htm|html|toml)$"
  # lo que se cita y no es una constante: las clases de Lean y el vocabulario del lakefile
  nv = split("Prop Type Sort lean_lib leanOptions globs andSubmodules submodules default_target moreServerArgs", vz, " ")
  for (i = 1; i <= nv; i++) VOCAB[vz[i]] = 1
}
FILENAME == ARGV[1] { vivo[$0] = 1; next }
FILENAME == ARGV[2] { if ($0 == "") next; split($0, e2, "\t"); env[e2[1]] = 1
                      # de una constante del proyecto, cada componente de su nombre (un constructor, un campo, un
                      # espacio de nombres: `listInd`, `SinWTs`) y cada prefijo (`FOL.Metamath.Semantics`)
                      if (e2[2] == "P") { nc = split(e2[1], cz, "."); for (i = 1; i <= nc; i++) ult[cz[i]] = 1 }
                      # y, de toda constante, sus espacios de nombres (`Classical`, `Lean.Meta`)
                      u = e2[1]; while (sub(/[.][^.]*$/, "", u)) { if (u in env) break; env[u] = 1 }
                      next }
FILENAME == ARGV[3] { p = index($0, "|"); k = substr($0, 1, p - 1); sond[k] = sond[k] "|" substr($0, p + 1); next }
FILENAME == ARGV[4] { modulo[$0] = 1; next }
# cada ruta que existe entra con todos sus sufijos de fichero y de directorio: los documentos citan `Meta/Rosser.lean`
# (desde la librería), `FOL/Semantics.lean` (desde FOL) o `Rosser.lean` a secas
FILENAME == ARGV[5] { n = split($0, pz, "/"); acc = ""
                      for (i = n; i >= 1; i--) { acc = (acc == "") ? pz[i] : pz[i] "/" acc; ruta[acc] = 1 }
                      d = ""; for (i = 1; i < n; i++) { d = (d == "") ? pz[i] : d "/" pz[i]; dd = d
                        while (1) { ruta[dd] = 1; if (!sub(/^[^\/]*\//, "", dd)) break } }
                      next }
FNR == 1 { fence = 0 }
/^[ \t]*```/ { fence = !fence; next }
fence { next }
{
  s = $0; off = 0
  # la línea con cada cita en BLANCO, del mismo largo: la ventana del marcador se corta de aquí, así que ni el nombre de
  # una cita (`prf_x_muerto`) ni un `|` dentro de una cita cuentan
  lb = ""; x = $0
  while (match(x, /`[^`]+`/)) { lb = lb substr(x, 1, RSTART - 1) sprintf("%" RLENGTH "s", ""); x = substr(x, RSTART + RLENGTH) }
  lb = lb x
  while (match(s, /`[^`]+`/)) {
    t = substr(s, RSTART + 1, RLENGTH - 2); ini = off + RSTART; fin = off + RSTART + RLENGTH - 1
    off = fin; s = substr(s, RSTART + RLENGTH)
    clase = ""
    # una ruta con su línea (`GodelTwoPrf.lean:161`, `check-doc-sync.bash:533-536`) se mira sin la línea
    if (t ~ /:[0-9][0-9,:-]*$/) sub(/:[0-9][0-9,:-]*$/, "", t)
    if (t ~ /^[A-Za-z0-9_.\/-]+$/ && (t ~ /\// || t ~ EXT) && !(t !~ EXT && t ~ /_[^\/]*$/)) {
      # (sin extensión y con `_` en el último tramo, `prf_x_left/right` abrevia dos nombres: no es una ruta)
      clase = "B2"
      r = t; sub(/^(\.\.?\/)+/, "", r); sub(/\/$/, "", r)
      if (r !~ /[A-Za-z0-9]/ || r ~ /^[.]/) continue
      if ((r in ruta) || ((r ".lean") in ruta)) continue
      k = t
    } else if (t ~ IDENT) {
      # las formas que una declaración del proyecto no tiene: palabras sueltas en minúsculas, MAYÚSCULAS_DE_SCRIPT,
      # hashes de commit, hipótesis de una prueba (`hPsiId`, `hwP`, `_hE`) y la abreviatura de un axioma (`ax21`)
      if (length(t) < 3 || t ~ /^[a-z]+$/ || t ~ /^[A-Z0-9_]+$/ || t ~ /^[0-9a-f]+$/) continue
      if (t ~ /^_?h[A-Z0-9_]/ || t ~ /^_?h[a-z][A-Z_]/ || t ~ /^ax[0-9]+[a-z]?$/) continue
      if (t in VOCAB) continue
      clase = "B"
      k = t; sub(/^([A-Z][A-Za-z0-9_]*[.])*/, "", k)
      if (k ~ /^ax_[A-Z]/) continue
      k2 = t; sub(/.*[.]/, "", k2)
      if ((t in vivo) || (k in vivo) || (t in env) || (k in ult) || (k2 in ult) || (t in modulo)) continue
      if (k ~ /_$/) {
        if (!(k in fam)) { fam[k] = 0; for (v in vivo) if (index(v, k) == 1) { fam[k] = 1; break } }
        if (fam[k]) continue
      }
    } else continue
    # el marcador, en la ventana [ini − W, fin + W] de la línea en blanco, sin cruzar un `|`
    a = ini - W; if (a < 1) a = 1
    izq = substr(lb, a, ini - a); der = substr(lb, fin + 1, W)
    q = 0; while ((p = index(substr(izq, q + 1), "|")) > 0) q += p
    if (q > 0) izq = substr(izq, q + 1)
    p = index(der, "|"); if (p > 0) der = substr(der, 1, p - 1)
    if ((izq " " der) ~ MARK) continue
    if (clase == "B" && (k in sond)) {
      nf = split(substr(sond[k], 2), fs, "|"); ex = 0
      for (q2 = 1; q2 <= nf; q2++) { bb = fs[q2]; sub(/[.]lean$/, "", bb); if (match($0, bb "([^A-Za-z0-9_]|$)")) ex = 1 }
      if (ex) continue
    }
    print clase "|" k "|" t "|" FILENAME ":" FNR
  }
}
