# -*- coding: utf-8 -*-
import io, sys, re, collections
sys.stdout.reconfigure(encoding='utf-8')
D = 'C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/'
edges = [l.rstrip('\n').split('\t') for l in io.open(D + 'choice_edges.tsv', encoding='utf-8')][1:]
G = collections.defaultdict(set); EXT = collections.defaultdict(set)
for m, n, d, md, isf in edges:
    if isf == 'true': G[n].add(d)
    else: EXT[n].add(d)
front = set(EXT)  # FOL nodes using external choice directly
def norm(n):
    n = re.sub(r'\.(_f|_sunfold|_unfold|eq_\d+|eq_def|_unsafe_rec)$', '', n)
    return n
tit = []
for l in io.open(D + 'origenes_titulares.txt', encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    m, n, o = l.rstrip('\n').split('\t')
    tit.append((m, n, set(x.strip() for x in o.split(';'))))
def origins(n, dead, deadedges):
    seen = set(); st = [n]; res = set()
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x)
        if norm(x) in dead: continue
        if x in front: res.add(norm(x))
        for y in G.get(x, ()):
            if (norm(x), norm(y)) in deadedges: continue
            st.append(y)
    return res
BND = {'FOL.HenkinLimit0.bnd', 'FOL.HenkinLimit0.bnd_spec'}
INV_USERS = {'FOL.Fresh0.derivesSet0_shift_inv', 'FOL.Rename.derives0_rename_conservative'}
FRESH = {'FOL.Fresh0.cst_ne_shift', 'FOL.Fresh0.cst_zero_ne', 'FOL.Fresh0.cst_bound_sym'}
# who uses invOf directly?
print('usuarios directos de invOf/invOf_spec:', sorted({norm(n) for n in G if G[n] & {'FOL.Rename.invOf','FOL.Rename.invOf_spec'}}))
print('usuarios directos de bnd/bnd_spec:', sorted({norm(n) for n in G if G[n] & BND}))
scen = {
 'base': (set(), set()),
 'A (bndC)': (BND, set()),
 'B (locInv)': (INV_USERS, set()),
 'A+B': (BND | INV_USERS, set()),
 'A+B+anexoFresh0': (BND | INV_USERS | FRESH, set()),
}
rows = []
for m, n, o in tit:
    r = {k: origins(n, dead, de) for k, (dead, de) in scen.items()}
    rows.append((m, n, o, r))
# check base reproduces origenes file
bad = [(n) for m, n, o, r in rows if {norm(x) for x in o} != r['base']]
print('base != origenes_titulares:', len(bad), bad[:5])
for k in scen:
    free = [n for m, n, o, r in rows if not r[k]]
    print(f'\n== {k}: titulares SIN choice: {len(free)}')
    for n in free: print('   ', n)
print('\n== titulares cuyo conjunto de origenes contiene bnd/bnd_spec/invOf/invOf_spec:')
for m, n, o, r in rows:
    hit = o & (BND | {'FOL.Rename.invOf', 'FOL.Rename.invOf_spec'})
    if hit:
        print(f'  {n}: base {len(r["base"])} -> A+B {len(r["A+B"])} ; invOf sigue: {"FOL.Rename.invOf" in r["A+B"]} ; resto A+B: {sorted(r["A+B"])[:6]}{"..." if len(r["A+B"])>6 else ""}')
print('\n== detalle de titulares con pocos origenes tras A+B (<=4):')
for m, n, o, r in rows:
    if len(r['A+B']) <= 4 and (o & (BND | {'FOL.Rename.invOf'})):
        print('  ', n, '->', sorted(r['A+B']), '| con anexo:', sorted(r['A+B+anexoFresh0']))
print('\n== diferencias base vs fichero de origenes:')
for m, n, o, r in rows:
    on = {norm(x) for x in o}
    if on != r['base']:
        print('  ', n, ' solo-sim:', sorted(r['base'] - on), ' solo-fichero:', sorted(on - r['base']))
print('\n== por escenario, titulares pequeños:')
for m, n, o, r in rows:
    if n.split('.')[-1] in ('henLimit_witness','henLimit_consistent₀','hen_consistent','henkin_completion₀','infinite_model_of_large','countable_infinite_of_infinite','infinite_model_of_large_fresh'):
        for k in scen: print('  ', n, '|', k, '|', len(r[k]), sorted(r[k]) if len(r[k])<5 else '')
print('\n== conteo de titulares que pierden AL MENOS un origen, por escenario:')
for k in scen:
    c=[n for m,n,o,r in rows if r[k] < r['base']]
    print('  ', k, len(c))
