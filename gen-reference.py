# -*- coding: utf-8 -*-
"""Regenera el §6 de REFERENCE.md («Exports») desde las declaraciones reales de FOL y de TheoryFramework.

Uso:  python3 gen-reference.py            (reescribe el bloque generado de REFERENCE.md)
      python3 gen-reference.py --check    (sale con 1 si el bloque no es lo que se generaría)

Nació el 2026-11-02 (T56, ADR-245 de RPP). El §6 escrito a mano describía cuatro módulos borrados (`Prelim`,
`Soundness`, `Completeness`, `Compacity`) y el registro de un quinto (`MetaRules`), y sus entradas se añadían a mano y
fuera de orden: un catálogo de lo que exporta cada módulo que se escribe a mano se pudre con el árbol, como el
DEPENDENCIES.md de julio. Éste se CALCULA de las fuentes, y la CI comprueba con `--check` que lo versionado es lo que se
generaría. El texto viejo, con lo que explicaba, está en el apéndice R de REFERENCE.md, como registro.

Qué cuenta como declaración: las órdenes `theorem`, `lemma`, `def`, `abbrev`, `instance` (con nombre), `structure`,
`inductive`, `class` (y `class inductive`), `opaque` y `axiom` que empiezan una línea de CÓDIGO (sin comentarios ni
cadenas), con su nombre completo según los `namespace` abiertos; las `private`, fuera. No cuenta lo que Lean genera
(proyecciones, constructores, recursores, ecuaciones) ni las órdenes de sintaxis (`macro`, `syntax`, `elab`,
`notation`): de ésas se da el número. El dominio, el de `gen-dependencies.py`: todos los `.lean` de `FOL/` y de
`TheoryFramework/`, lo que compilan los `globs` del lakefile.
"""
import io, os, re, sys

ROOT = os.path.dirname(os.path.abspath(__file__))
os.chdir(ROOT)
REF = 'REFERENCE.md'
INI = '<!-- §6 GENERADO por `python3 gen-reference.py`: no se edita a mano (T56) -->'
FIN = '<!-- FIN DEL §6 GENERADO -->'

def rd(p):
    return io.open(p, encoding='utf-8').read()

files = sorted(os.path.join(d, f).replace(os.sep, '/') for top in ('FOL', 'TheoryFramework')
               for d, _, fs in os.walk(top) for f in fs if f.endswith('.lean'))

def codigo(src):
    """el fuente con los comentarios (de línea, de bloque anidados y docstrings) y las cadenas en blanco; los saltos de
    línea se conservan"""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith('/-', i):
                depth += 1; out.append('  '); i += 2; continue
            if src.startswith('-/', i):
                depth -= 1; out.append('  '); i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if src.startswith('/-', i):
            depth = 1; out.append('  '); i += 2; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append('"' + ' ' * (min(j, n) - i - 1) + '"'); i = j + 1; continue
        if c == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'.!?₀₁₂₃₄₅₆₇₈₉")):
            m = re.match(r"'(\\.[^']*|[^'\\])'", src[i:])
            if m:   # un carácter literal (`'"'` no abre una cadena)
                out.append(' ' * len(m.group(0))); i += len(m.group(0)); continue
        out.append(c); i += 1
    return ''.join(out)

MODS = r'(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(' + MODS + r')(theorem|lemma|def|abbrev|instance|structure|inductive|'
                  r'class\s+inductive|class|opaque|axiom)\b(.*)$')
SINTAXIS = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:local|scoped)\s+)?(macro|macro_rules|syntax|elab|elab_rules|'
                      r'notation|infixl|infixr|infix|prefix|postfix)\b')
NOMBRE = re.compile(r'^\s*(?:\(priority\s*:=\s*[^)]*\)\s*)?([^\s:(\[{⦃.]+(?:\.[^\s:(\[{⦃.]+)*)')

def declaraciones(src):
    pila = []      # ('ns', partes) | ('sec',) | ('mut',)
    decls, sint = [], 0
    for linea in codigo(src).split('\n'):
        m = re.match(r'^\s*namespace\s+(\S+)', linea)
        if m:
            pila.append(('ns', m.group(1).split('.'))); continue
        if re.match(r'^\s*(?:noncomputable\s+)?section\b', linea):
            pila.append(('sec',)); continue
        if re.match(r'^\s*mutual\s*$', linea):
            pila.append(('mut',)); continue
        m = re.match(r'^\s*end(?:\s+(\S+))?\s*$', linea)
        if m:
            if pila:
                pila.pop()
            continue
        if SINTAXIS.match(linea):
            sint += 1; continue
        m = DECL.match(linea)
        if not m:
            continue
        mods, kind, resto = m.group(1), re.sub(r'\s+', ' ', m.group(2)), m.group(3)
        if 'private' in mods.split():
            continue
        mn = NOMBRE.match(resto)
        if not mn:
            continue   # una instancia sin nombre
        nombre = re.sub(r'\.\{[^}]*\}$', '', mn.group(1))
        if kind == 'instance' and nombre.startswith(('(', '[', '{')):
            continue
        if nombre.startswith('_root_.'):
            completo = nombre[len('_root_.'):]
        else:
            ns = [p for e in pila if e[0] == 'ns' for p in e[1]]
            completo = '.'.join(ns + [nombre])
        decls.append((kind, completo, ns_de(pila), nombre))
    return decls, sint

def ns_de(pila):
    return '.'.join(p for e in pila if e[0] == 'ns' for p in e[1])

CLASE = {'theorem': 'teoremas', 'lemma': 'teoremas', 'def': 'definiciones', 'abbrev': 'definiciones',
         'opaque': 'definiciones', 'instance': 'instancias', 'structure': 'tipos', 'inductive': 'tipos',
         'class': 'tipos', 'class inductive': 'tipos', 'axiom': 'axiomas'}
ORDEN = ['tipos', 'definiciones', 'instancias', 'teoremas', 'axiomas']

def etiqueta(f):
    # la forma que busca [C] de check-doc-sync.bash: la ruta bajo `FOL/` para los de FOL (`Lindenbaum0.lean`,
    # `Theorems/Eq.lean`) y la entera para los de TheoryFramework
    return f[len('FOL/'):] if f.startswith('FOL/') else f

def genera():
    out = [INI, '', '> Generado de las fuentes (T56, ADR‑245 de RPP): por cada módulo de las dos `lean_lib`, sus declaraciones',
           '> públicas, agrupadas por espacio de nombres y por clase. No dice qué demuestra cada una (eso, §3 y',
           '> `CURRENT-STATUS-PROJECT.md`) ni su footprint (`../ROBINSON_PlusPlus/check-footprints.bash`). Para regenerarlo:',
           '> `python3 gen-reference.py`; la CI de FOL comprueba con `--check` que está al día.', '']
    total = {k: 0 for k in ORDEN}
    nsint = 0
    cuerpo = []
    for k, f in enumerate(files, 1):
        mod = f[:-5].replace('/', '.')
        decls, sint = declaraciones(rd(f))
        nsint += sint
        cuerpo.append(f'### 6.{k} · `{etiqueta(f)}` — `{mod}`')
        cuerpo.append('')
        if not decls:
            cuerpo.append('Sin declaraciones públicas' + (f' ({sint} órdenes de sintaxis).' if sint else '.'))
            cuerpo.append('')
            continue
        por_ns = {}
        for kind, completo, ns, nombre in decls:
            por_ns.setdefault(ns, {}).setdefault(CLASE[kind], []).append(completo[len(ns) + 1:] if ns else completo)
            total[CLASE[kind]] += 1
        for ns in sorted(por_ns, key=lambda x: (x != '', x)):
            cab = f'En `{ns}`' if ns else 'En la raíz'
            partes = []
            for c in ORDEN:
                if c in por_ns[ns]:
                    nombres = sorted(set(por_ns[ns][c]), key=lambda x: (x.lower(), x))
                    partes.append(f'*{c}* ({len(nombres)}): ' + ', '.join(f'`{x}`' for x in nombres))
            cuerpo.append(f'* {cab} — ' + ' · '.join(partes) + '.')
        if sint:
            cuerpo.append(f'* Y {sint} órdenes de sintaxis (`macro`, `syntax`, `elab`, `notation`…).')
        cuerpo.append('')
    n = sum(total.values())
    out.append(f'**{len(files)} módulos** (`FOL/` {sum(1 for f in files if f.startswith("FOL/"))} + '
               f'`TheoryFramework/` {sum(1 for f in files if f.startswith("TheoryFramework/"))}), **{n} declaraciones '
               f'públicas**: ' + ', '.join(f'{total[c]} {c}' for c in ORDEN if total[c]) +
               (f'; y {nsint} órdenes de sintaxis.' if nsint else '.'))
    out.append('')
    out.extend(cuerpo)
    out.append(FIN)
    return '\n'.join(out)

crudo = io.open(REF, encoding='utf-8', newline='').read()
crlf = '\r\n' in crudo
ref = crudo.replace('\r\n', '\n')
if INI not in ref or FIN not in ref:
    raise SystemExit(f'{REF} no tiene el bloque generado (entre «{INI}» y «{FIN}»)')
a, b = ref.index(INI), ref.index(FIN) + len(FIN)
nuevo = ref[:a] + genera() + ref[b:]
if '--check' in sys.argv:
    if nuevo != ref:
        print('REFERENCE.md §6 NO está al día: python3 gen-reference.py')
        sys.exit(1)
    print('REFERENCE.md §6 al día')
    sys.exit(0)
io.open(REF, 'w', encoding='utf-8', newline='').write(nuevo.replace('\n', '\r\n') if crlf else nuevo)
print(f'REFERENCE.md §6: {len(files)} módulos')
