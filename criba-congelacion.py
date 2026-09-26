# -*- coding: utf-8 -*-
"""Criba de CONGELACION de FOL — los criterios MEDIBLES (1: marcadores; 3: cadena entrante de
PeanoRF, cierre transitivo; 4: footprint declarado y modulo compilado). SOLO LECTURA.

Traida al repo el 2026-09-26 desde el scratchpad (una medicion cuyo artefacto vive en un scratchpad
se evapora). Los criterios 2 (decision pendiente) y 5 (hogar de un resultado del catalogo) piden
juicio: este script NO los decide. Su salida es una CRIBA, no un permiso de `freeze`: la del
2026-09-26 dio 16 candidatos y la refutacion adversarial objeto 13 (ver NEXT-STEPS.md).
Uso:  py criba-congelacion.py   (desde la raiz de FOL; RPP y PeanoRF como directorios hermanos)
"""
import io, os, re, glob, sys
sys.stdout.reconfigure(encoding='utf-8')

FOL = os.path.dirname(os.path.abspath(__file__)).replace(os.sep, '/') + '/'
RPP = FOL + '../ROBINSON_PlusPlus/'
PRF = FOL + '../Peano-from-ROB-n-FOL/PeanoRF/'

def rd(p):
    return io.open(p, encoding='utf-8', errors='replace').read()

mods = sorted(set(
    os.path.relpath(f, FOL).replace('\\', '/')
    for pat in ('FOL/*.lean', 'FOL/Theorems/*.lean', 'TheoryFramework/*.lean',
                'TheoryFramework/Instances/*.lean')
    for f in glob.glob(FOL + pat)))

def modname(path):   # FOL/Theorems/Eq.lean -> FOL.Theorems.Eq
    return path[:-5].replace('/', '.')
def modpath(name):
    return name.replace('.', '/') + '.lean'

imports = {}
for m in mods:
    imports[m] = [modpath(x) for x in re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)', rd(FOL + m), re.M)
                  if x.startswith('FOL.') or x.startswith('TheoryFramework.')]

def closure(starts):
    seen, st = set(), list(starts)
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x)
        st.extend(imports.get(x, []))
    return seen

# ── compilacion: barril FOL.lean (lean_lib FOL, sin globs) + TheoryFramework (globs .submodules)
barrel = [modpath(x) for x in re.findall(r'^\s*import\s+(FOL\.[A-Za-z0-9_.]+)', rd(FOL + 'FOL.lean'), re.M)]
compiled = closure(barrel) | set(m for m in mods if m.startswith('TheoryFramework/'))
tfbarrel = [modpath(x) for x in re.findall(r'^\s*import\s+(TheoryFramework\.[A-Za-z0-9_.]+)', rd(FOL + 'TheoryFramework.lean'), re.M)]

# ── criterio 1: [G.2]
ctrl = rd(FOL + 'check-doc-sync.bash')
tab = re.search(r"cat > \"\$G2TAB\" <<'G2EOF'\n(.*?)\nG2EOF", ctrl, re.S).group(1)
g2 = {}
for row in tab.splitlines():
    f, a, c, n = row.split('\u00a7')
    g2.setdefault(f, []).append((c, a, n))

# ── criterio 4: #print axioms y filas
TABLA = re.search(r"read -r -d '' TABLA <<'EOF'\n(.*?)\nEOF", rd(RPP + 'check-footprints.bash'), re.S).group(1)
rows = [l.split('|')[0] for l in TABLA.splitlines() if l.strip()]
root_map = {
    'Derives\u2080.rec': 'FOL/Derives0.lean', 'derives0_to_derives': 'FOL/Derives0.lean',
    'derives0_raa': 'FOL/Derives0.lean', 'Derives\u2081.rec': 'FOL/Derives1.lean',
    'Derives\u2082.rec': 'FOL/Derives2.lean', 'LK\u2080.rec': 'FOL/Sequent0.lean',
    'LKh.rec': 'FOL/Hauptsatz0.lean', 'instDecidableEqFormula': 'FOL/DecEq.lean',
    'liftFormula': 'FOL/FOL.lean', 'neg': 'FOL/FOL.lean', 'substFormula': 'FOL/FOL.lean',
    'top': 'FOL/FOL.lean', 'FOL.derive_atom_congr': 'FOL/Theorems/Eq.lean',
    'FOL.derive_eq_func_congr': 'FOL/Theorems/Eq.lean', 'FOL.substTerm_liftTerm': 'FOL/Theorems/Eq.lean',
    'FOL.instFreshSymListChar': 'FOL/SymClasses.lean',
}
ns_map = {'FOL.Metamath.Enumeration.': 'FOL/Enumeration.lean',
          'FOL.Metamath.Semantics.': 'FOL/Semantics.lean',
          'FOL.Metamath.Soundness0.': 'FOL/Soundness0.lean'}
rowmod, unmapped = {}, []
for r in rows:
    if r.startswith('ROBINSON_PlusPlus.'): continue
    home = root_map.get(r)
    if not home:
        for p, h in ns_map.items():
            if r.startswith(p): home = h
    if not home:
        mm = re.match(r'FOL\.([A-Za-z0-9]+)\.', r)
        if mm and ('FOL/' + mm.group(1) + '.lean') in mods: home = 'FOL/' + mm.group(1) + '.lean'
    if home: rowmod.setdefault(home, []).append(r)
    else: unmapped.append(r)
prints = {m: re.findall(r'^\s*#print\s+axioms\s+(\S+)', rd(FOL + m), re.M) for m in mods}

# ── criterio 3: cadena entrante de PeanoRF (los 7)
SEVEN = ['Subst', 'DerivesI', 'SubstDerives', 'Consistency', 'Eq', 'Collapse', 'Slash']
direct_fol, via_prelim = set(), set()
for s in SEVEN:
    src = rd(PRF + 'Calculus/' + s + '.lean')
    for imp in re.findall(r'^\s*import\s+(FOL\.[A-Za-z0-9_.]+)', src, re.M):
        direct_fol.add(modpath(imp))
    if re.search(r'^\s*import\s+PeanoRF\.Prelim', src, re.M):
        for imp in re.findall(r'^\s*import\s+(FOL\.[A-Za-z0-9_.]+)', rd(PRF + 'Prelim.lean'), re.M):
            via_prelim.add(modpath(imp))
chain_direct = closure(direct_fol | {'FOL/FOL.lean'})   # Subst -> import FOL.FOL tras el re-apuntado
chain_prelim = closure(via_prelim) - chain_direct

print('modulos activos:', len(mods), '| compilados:', len(compiled & set(mods)))
print('NO compilados:', sorted(set(mods) - compiled))
print('TF en el barril TheoryFramework.lean:', tfbarrel)
print('filas FOL sin modulo asignado:', unmapped)
print('imports FOL directos de los 7:', sorted(direct_fol))
print('imports FOL via Prelim:', sorted(via_prelim))
print('cierre (directo + FOL.FOL):', len(chain_direct), sorted(chain_direct))
print('cierre SOLO via Prelim (extra):', len(chain_prelim), sorted(chain_prelim))
print()
for m in mods:
    pr = prints[m]; rw = rowmod.get(m, [])
    notrow = [p for p in pr if p not in rw]
    marks = [c for c, a, n in g2.get(m, []) if c in ('ABIERTA', 'DIFERIDA')]
    tags = []
    if marks: tags.append('C1:' + '+'.join(marks))
    if m in chain_direct: tags.append('C3:cadena')
    elif m in chain_prelim: tags.append('C3:solo-Prelim')
    if m not in compiled: tags.append('C4:NO-compila')
    if not pr: tags.append('C4:sin#print')
    if not rw: tags.append('C4:sin-filas')
    if notrow: tags.append('C4:print-sin-fila=' + ','.join(notrow))
    print('%-36s print=%-2d filas=%-2d %s' % (m, len(pr), len(rw), ' '.join(tags) or 'OK(1,3,4)'))
