# -*- coding: utf-8 -*-
"""Regenera DEPENDENCIES.md desde las líneas `import` reales de FOL.

Uso:  py gen-dependencies.py            (escribe DEPENDENCIES.md)
      py gen-dependencies.py --check    (sale con 1 si DEPENDENCIES.md no es lo que se generaría)

Nació el 2026-09-26: el DEPENDENCIES.md a mano llevaba desde julio describiendo un árbol que ya no
existía (cinco lean_lib, tres nodos borrados, ninguno de la capa ₀). Un grafo que se escribe a mano
se pudre con el árbol; éste se CALCULA.
"""
import io, os, re, sys, glob, datetime

ROOT = os.path.dirname(os.path.abspath(__file__))
os.chdir(ROOT)

def rd(p):
    return io.open(p, encoding='utf-8').read()

PATTERNS = ('FOL/*.lean', 'FOL/Theorems/*.lean', 'TheoryFramework/*.lean', 'TheoryFramework/Instances/*.lean')
files = sorted({f.replace(os.sep, '/') for pat in PATTERNS for f in glob.glob(pat)})

def mod(path):
    return path[:-5].replace('/', '.')

mods = [mod(f) for f in files]
MODSET = set(mods)
imports = {}
lean_imports = {}
for f in files:
    src = rd(f)
    imps = re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)', src, re.M)
    imports[mod(f)] = sorted(i for i in imps if i in MODSET)
    lean_imports[mod(f)] = sorted(i for i in imps if i not in MODSET)

imported_by = {m: [] for m in mods}
for m, deps in imports.items():
    for d in deps:
        imported_by[d].append(m)

# nivel = longitud del camino de imports más largo hasta una raíz
level = {}
def lv(m, stack=()):
    if m in level:
        return level[m]
    if m in stack:
        raise SystemExit('ciclo de imports en ' + ' -> '.join(stack + (m,)))
    level[m] = 0 if not imports[m] else 1 + max(lv(d, stack + (m,)) for d in imports[m])
    return level[m]
for m in mods:
    lv(m)

barrels = {}
for b in ('FOL.lean', 'TheoryFramework.lean'):
    if os.path.exists(b):
        barrels[b] = re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)', rd(b), re.M)
compiled = set()
def close(ms):
    st = list(ms)
    while st:
        x = st.pop()
        if x in compiled or x not in MODSET:
            continue
        compiled.add(x)
        st.extend(imports[x])
close(barrels.get('FOL.lean', []))
close([m for m in mods if m.startswith('TheoryFramework.')])   # globs del lean_lib TheoryFramework

n_edges = sum(len(v) for v in imports.values())
n_fol = sum(1 for f in files if f.startswith('FOL/') and not f.startswith('FOL/Theorems/'))
n_thm = sum(1 for f in files if f.startswith('FOL/Theorems/'))
n_tf = sum(1 for f in files if f.startswith('TheoryFramework/'))
today = datetime.date.today().isoformat() if '--date' not in sys.argv else sys.argv[sys.argv.index('--date') + 1]

def short(m):
    if m == 'FOL.FOL':
        return 'FOL.FOL'
    return m.replace('TheoryFramework.', 'TF.').replace('FOL.Theorems.', 'Thm.').replace('FOL.', '')

out = []
w = out.append
w('# Diagrama de Dependencias — FOL')
w('')
w(f'**Last updated:** {today} — GENERADO por `py gen-dependencies.py` desde las líneas `import`; no se edita a mano.')
w('**Autor**: Julián Calderón Almendros')
w('')
w('> ⚠️ Este fichero se **calcula**. Para actualizarlo: `py gen-dependencies.py`; para comprobar que')
w('> está al día: `py gen-dependencies.py --check`. El DEPENDENCIES.md escrito a mano (2026-07-12) se')
w('> sustituyó el 2026-09-26: describía cinco `lean_lib`, tres nodos borrados y ninguno de la capa ₀.')
w('')
w('## Cifras')
w('')
w(f'* **{len(mods)} módulos** (`FOL/` {n_fol} + `FOL/Theorems/` {n_thm} + `TheoryFramework/` {n_tf}), '
  f'**{n_edges} aristas** `import` entre ellos, profundidad máxima **{max(level.values())}**.')
w('* 2 `lean_lib`: `FOL` (raíz: el barril `FOL.lean`, sin globs) y `TheoryFramework` (globs `.submodules`).')
nc = sorted(set(mods) - compiled)
w(f'* Módulos que NINGÚN build alcanza: {", ".join("`" + m + "`" for m in nc) if nc else "ninguno"}.')
ext = sorted({i for v in lean_imports.values() for i in v})
w(f'* Imports externos a FOL: {", ".join("`" + i + "`" for i in ext) if ext else "ninguno"} '
  f'(FOL no tiene `require`: no depende de nada más allá de sí mismo).')
w('')
w('## Por niveles (camino de imports más largo hasta una raíz)')
w('')
for L in range(max(level.values()) + 1):
    ms = sorted(m for m in mods if level[m] == L)
    w(f'* **{L}** — ' + ', '.join('`' + short(m) + '`' for m in ms))
w('')
w('## Grafo')
w('')
w('```mermaid')
w('graph BT')
for m in sorted(mods):
    for d in imports[m]:
        w(f'    {short(m).replace(".", "_")}["{short(m)}"] --> {short(d).replace(".", "_")}["{short(d)}"]')
for m in sorted(mods):
    if not imports[m] and not imported_by[m]:
        w(f'    {short(m).replace(".", "_")}["{short(m)}"]')
w('```')
w('')
w('## Tabla')
w('')
w('| módulo | nivel | importa | lo importan |')
w('|---|---|---|---|')
for m in sorted(mods, key=lambda x: (level[x], x)):
    imp = ', '.join('`' + short(d) + '`' for d in imports[m]) or '—'
    if lean_imports[m]:
        imp += ' · externo: ' + ', '.join('`' + i + '`' for i in lean_imports[m])
    by = ', '.join('`' + short(d) + '`' for d in sorted(imported_by[m])) or '—'
    w(f'| `{m}` | {level[m]} | {imp} | {by} |')
w('')
w('## Barriles')
w('')
for b, imps in barrels.items():
    w(f'* `{b}` importa {len(imps)} módulos.')
w('')
text = '\n'.join(out) + '\n'

if '--check' in sys.argv:
    cur = rd('DEPENDENCIES.md') if os.path.exists('DEPENDENCIES.md') else ''
    strip = lambda s: re.sub(r'^\*\*Last updated:\*\*.*$', '', s, flags=re.M)
    if strip(cur) != strip(text):
        print('DEPENDENCIES.md NO está al día: py gen-dependencies.py')
        sys.exit(1)
    print('DEPENDENCIES.md al día')
    sys.exit(0)
io.open('DEPENDENCIES.md', 'w', encoding='utf-8', newline='\n').write(text)
print(f'DEPENDENCIES.md: {len(mods)} módulos, {n_edges} aristas, profundidad {max(level.values())}')
