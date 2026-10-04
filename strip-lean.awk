# strip-lean.awk — despoja un fichero de Lean de comentarios y literales (cadenas y caracteres).
#
# Emite UNA línea de salida por cada línea de entrada (los números de línea siguen siendo los del
# original) con el contenido de los comentarios —`--` de línea y `/- … -/` de bloque, docstrings
# `/-- … -/` y `/-! … -/` incluidos— y de los literales sustituido por nada: un literal o un
# comentario de bloque dejan UN espacio (para Lean un comentario es espacio: `exact/- c -/sorry`
# son dos tokens). El CÓDIGO se conserva, también el de dentro de las interpolaciones.
#
# 🔑 Una definición delicada vive en UN sitio: la usan `check-sorry.bash`, `check-axioms.bash` y
# los bloques [A] y [B] de `check-doc-sync.bash`. El CÓDIGO es idéntico al de
# `../ROBINSON_PlusPlus/strip-lean.awk` (sólo cambian estas líneas de cabecera), y
# `check-doc-sync.bash` de RPP lo comprueba.
#
# ⛔ SE EJECUTA CON `LC_ALL=C` (trabaja por BYTES y decodifica el UTF-8 a mano): así hace lo mismo
# con gawk que con mawk y en cualquier locale. Si no está en modo byte, sale con 2 sin emitir nada,
# y el autotest de quien lo llama da «SIN MEDIR».
#
# Sigue al lexer de Lean v4.31.0 (`Lean/Parser/Basic.lean`, `StrInterpolation.lean`,
# `Init/Meta/Defs.lean`), comparado con un lexer de referencia escrito función a función:
#   · comentarios de bloque anidados; `/-` consume TRES caracteres, como Lean (`/-/- x -/` cierra en
#     el primer `-/`; `/--/ … -/` es un docstring);
#   · cadenas normales de varias líneas, con escapes y saltos `\`+fin de línea;
#   · cadenas en bruto `r"…"`, `r#"…"#` (sin escapes; terminan en `"` + las mismas `#`);
#   · literales de carácter (`'a'`, `'α'`, `'"'`, `'\x41'`, `'α'`) en todo comienzo de token, y
#     la prima de un identificador (`Γ'`, `h₀'`) no lo es: las clases `isIdFirst`/`isIdRest` del core;
#   · cadenas INTERPOLADAS: lo son sólo tras los tokens que las admiten en el core —`s!` `m!` `f!`
#     `println!` `throwError` `throwErrorAt t` `dbg_trace` `trace[…]` `Macro.trace[…]`
#     `trace_goal[…]` `report…Issue!` y las variantes `…Named…`—, con espacio en medio o no; `!"…"`
#     (el `not` booleano) es una cadena normal. Se anidan: una pila de contextos.
#   · identificadores `«…»`, opacos aunque contengan `--`, `/-` o `"` (y aunque ocupen varias líneas).
# ⚠️ Lo que NO sigue: una macro PROPIA que tome `interpolatedStr(term)` (su cadena se lee como normal),
# y el término de `throwErrorAt` se reconoce si es un token o un paréntesis sin paréntesis dentro.
#
# Historia: v1 (2026-10-03, ADR-116 de RPP); v2 el mismo día, tras una revisión adversarial con siete
# construcciones mal leídas; v3 tras la segunda ronda (interpolación por token, pila de contextos,
# modo byte, comentario = espacio). Los casos están en el autotest de `check-sorry.bash`.
#
# Uso: LC_ALL=C awk -f strip-lean.awk FICHERO.lean [MÁS.lean …] — con varios ficheros, el estado se
# reinicia en cada uno (`FNR == 1`): un comentario o una cadena sin cerrar no contamina al siguiente.
function reinicia() { depth = 0; instr = 0; raw = -1; guil = 0; sp = 0; tb = "" }
# Longitud en bytes del carácter UTF-8 cuyo primer byte es c (un byte suelto cuenta como uno).
function lenu(c,   o) { o = ord[c]; return (o < 192) ? 1 : (o < 224) ? 2 : (o < 240) ? 3 : 4 }
# Punto de código de un carácter UTF-8 de 2 a 4 bytes.
function cpde(ch,   m, v, q) {
  m = length(ch); v = ord[substr(ch, 1, 1)] - ((m == 2) ? 192 : (m == 3) ? 224 : 240)
  for (q = 2; q <= m; q++) v = v * 64 + ord[substr(ch, q, 1)] - 128
  return v
}
# `isLetterLike` y `isSubScriptAlnum` de Init/Meta/Defs.lean (sólo puntos de código ≥ 128).
function letra(cp) {
  return (cp >= 945 && cp <= 969 && cp != 955) || (cp >= 913 && cp <= 937 && cp != 928 && cp != 931) \
      || (cp >= 970 && cp <= 1019) || (cp >= 7936 && cp <= 8190) || (cp >= 8448 && cp <= 8527) \
      || (cp >= 119964 && cp <= 120223) || (cp >= 192 && cp <= 255 && cp != 215 && cp != 247) \
      || (cp >= 256 && cp <= 383)
}
function subind(cp) {
  return (cp >= 8320 && cp <= 8329) || (cp >= 8336 && cp <= 8348) || (cp >= 7522 && cp <= 7530) || cp == 11388
}
# ¿La cadena que empieza aquí es INTERPOLADA? Lo decide el token anterior (t = código anterior, sin
# los espacios del final; cada literal deja en t una `"`, y la entrada a una interpolación una `{`).
function esinterp(t) {
  return t ~ /(^|[^A-Za-z0-9_'!?.])([smf]|println|reportIssue|reportDbgIssue|reportEMatchIssue)!$/ \
      || t ~ /(^|[^A-Za-z0-9_'!?.])(throwError|dbg_trace)$/ \
      || t ~ /(^|[^A-Za-z0-9_'!?.])(Macro[.])?trace(_goal)?\[[^]]*\]$/ \
      || t ~ /(^|[^A-Za-z0-9_'!?.])throwErrorAt[ \t]+([(][^()]*[)]|[^ \t()"]+)$/ \
      || t ~ /(^|[^A-Za-z0-9_'!?.])(throwNamedError|logNamedError|logNamedWarning)[ \t]+[^ \t"]+$/ \
      || t ~ /(^|[^A-Za-z0-9_'!?.])(throwNamedErrorAt|logNamedErrorAt|logNamedWarningAt)[ \t]+([(][^()]*[)]|[^ \t()"]+)[ \t]+[^ \t"]+$/
}
BEGIN {
  for (k = 1; k < 256; k++) ord[sprintf("%c", k)] = k
  if (length("«") != 2 || length(sprintf("%c", 200)) != 1) {
    print "strip-lean.awk: hace falta LC_ALL=C (despoja por BYTES); no se ha leído nada" > "/dev/stderr"
    exit 2
  }
  for (k = 48; k <= 57; k++) { idr[sprintf("%c", k)] = 1 }
  for (k = 65; k <= 90; k++) { idf[sprintf("%c", k)] = 1; idr[sprintf("%c", k)] = 1 }
  for (k = 97; k <= 122; k++) { idf[sprintf("%c", k)] = 1; idr[sprintf("%c", k)] = 1 }
  idf["_"] = 1; idr["_"] = 1; idr["'"] = 1; idr["!"] = 1; idr["?"] = 1
  G1 = "«"; G2 = "»"; SIGMA = "Σ"; POR = "×"
  reinicia()
}
FNR == 1 { reinicia() }
{
  line = $0; out = ""; i = 1; n = length(line); inid = 0; lastc = ""
  while (i <= n) {
    c = substr(line, i, 1)
    # 1 · dentro de un comentario de bloque (anidan)
    if (depth > 0) {
      two = substr(line, i, 2)
      if (two == "-/") { depth--; i += 2; continue }
      if (two == "/-") { depth++; i += 2; continue }
      i++; continue
    }
    # 2 · dentro de una cadena en bruto: termina en `"` seguida de `raw` almohadillas
    if (raw >= 0) {
      if (c == "\"" && substr(line, i + 1, raw) == hashes) { i += 1 + raw; raw = -1; continue }
      i++; continue
    }
    # 3 · dentro de una cadena normal (puede venir de la línea anterior)
    if (instr) {
      if (c == "\\") { i += 2; continue }
      if (c == "\"") instr = 0
      i++; continue
    }
    # 4 · dentro de un identificador `«…»`: se copia tal cual
    if (guil) {
      if (substr(line, i, 2) == G2) { guil = 0; out = out G2; tb = tb G2; i += 2; inid = 0; lastc = G2; continue }
      out = out c; tb = tb c; i++; continue
    }
    # 5 · en el tramo literal de una cadena interpolada: `{` abre código, `"` la cierra
    if (sp > 0 && st[sp] == "I") {
      if (c == "\\") { i += 2; continue }
      if (c == "\"") { sp--; i++; continue }
      if (c == "{") { sp++; st[sp] = "C"; br[sp] = 0; out = out " "; tb = tb "{"; inid = 0; lastc = ""; i++ }
      else i++
      continue
    }
    # 6 · CÓDIGO: el del fichero o el de una interpolación (que acaba en su `}`)
    if (sp > 0) {
      if (c == "{") br[sp]++
      else if (c == "}") {
        if (br[sp] == 0) { sp--; out = out " "; tb = tb "}"; inid = 0; lastc = ""; i++; continue }
        br[sp]--
      }
    }
    two = substr(line, i, 2)
    if (two == "/-") { depth = 1; i += (i + 2 <= n) ? 3 : 2; out = out " "; tb = tb " "; inid = 0; lastc = ""; continue }
    if (two == "--") break
    if (two == G1) { guil = 1; out = out G1; tb = tb G1; i += 2; continue }
    # cadena en bruto: `r` al COMIENZO de un token, `#`… y `"`
    if (c == "r" && !inid) {
      k = i + 1; h = 0
      while (substr(line, k, 1) == "#") { h++; k++ }
      if (substr(line, k, 1) == "\"") {
        raw = h; hashes = ""; for (q = 0; q < h; q++) hashes = hashes "#"
        out = out " "; tb = tb "\""; inid = 0; lastc = ""; i = k + 1; continue
      }
    }
    # literal de carácter: `'` al comienzo de un token (no tras `Σ` `×` `]` `#`, que forman `Σ'`…)
    if (c == "'" && !inid && lastc != "]" && lastc != "#" && lastc != SIGMA && lastc != POR) {
      d = substr(line, i + 1, 1)
      if (d == "\\") {
        e = substr(line, i + 2, 1); m = (e == "x") ? 4 : (e == "u") ? 6 : 2
      } else if (d != "" && d != "'") {
        m = lenu(d)
      } else m = -1
      if (m > 0 && substr(line, i + 1 + m, 1) == "'") {
        out = out " "; tb = tb "\""; inid = 0; lastc = ""; i += m + 2; continue
      }
    }
    if (c == "\"") {
      t = tb; sub(/[ \t\r]+$/, "", t)
      if (esinterp(t)) { sp++; st[sp] = "I" } else instr = 1
      out = out " "; tb = tb "\""; inid = 0; lastc = ""; i++; continue
    }
    # un carácter de código, entero (1 a 4 bytes)
    if (ord[c] < 128) {
      out = out c; tb = tb c; i++
      inid = inid ? (idr[c] || c == ".") : idf[c]; lastc = c
    } else {
      m = lenu(c); ch = substr(line, i, m); out = out ch; tb = tb ch; i += m
      cp = (m > 1) ? cpde(ch) : 0
      inid = inid ? (letra(cp) || subind(cp)) : letra(cp); lastc = ch
    }
  }
  print out
  tb = tb " "
  if (length(tb) > 240) tb = substr(tb, length(tb) - 159)
}
