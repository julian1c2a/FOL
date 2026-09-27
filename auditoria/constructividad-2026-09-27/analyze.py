# -*- coding: utf-8 -*-
import io, sys, re, collections, json
sys.stdout.reconfigure(encoding='utf-8')
import os
D = (sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'actual')).replace(os.sep, '/') + '/'
rows = [l.rstrip('\n').split('\t') for l in io.open(D + 'decls.tsv', encoding='utf-8')][1:]
edges = [l.rstrip('\n').split('\t') for l in io.open(D + 'choice_edges.tsv', encoding='utf-8')][1:]

def internal(n):
    # nombres generados: match_, proof_, eq_, _private, _cstage, _sunfold, _unfold, brecOn, below, etc.
    parts = n.split('.')
    return any(p.startswith('_') or re.match(r'^(match_|proof_|eq_\d|eq_def|sizeOf_spec|brecOn|below|binductionOn|ibelow|casesOn|recOn|noConfusion|noConfusionType|ctorIdx|ctorElim|inj|injEq|rec|mk\.inj|_)', p) for p in parts[1:]) or '._' in n

mods = collections.Counter(r[0] for r in rows)
print('modulos:', len(mods))
AX = collections.Counter()
bymod = collections.defaultdict(lambda: collections.Counter())
choice_user = []
proj_ax = []
nonc = []
for m, n, k, nc, axs in rows:
    s = frozenset(a for a in axs.split(',') if a)
    key = ('choice' if 'Classical.choice' in s else '') + ('+MetaRules' if any(a.startswith('FOL.MetaRules') for a in s) else '')
    cls = ','.join(sorted(s)) if s else '(ninguno)'
    AX[cls] += 1
    if not internal(n):
        bymod[m]['total'] += 1
        if 'Classical.choice' in s: bymod[m]['choice'] += 1
        if any(a.startswith('FOL.MetaRules') for a in s): bymod[m]['metarules'] += 1
        if not s: bymod[m]['cero'] += 1
    if nc == 'true': nonc.append((m, n, k, axs))
    if k == 'axiom': proj_ax.append((m, n))
print('\nclases de footprint (todas las constantes, incl. generadas):')
for c, v in AX.most_common(): print(f'  {v:5d}  {c}')
print('\naxiomas declarados en FOL:', proj_ax)
print('\nnoncomputable:', len(nonc))
for x in nonc: print('  ', x)
# fuentes externas de choice
ext = collections.defaultdict(set)
folsrc = collections.defaultdict(set)
for m, n, d, md, isf in edges:
    if isf == 'false':
        ext[d].add(n)
print('\nFUENTES EXTERNAS de Classical.choice (constante externa usada directamente -> nº de constantes FOL que la usan):')
for d, s in sorted(ext.items(), key=lambda x: -len(x[1])):
    print(f'  {len(s):4d}  {d}')
# por modulo
print('\npor modulo (sin generadas): total / con choice / con MetaRules / sin axiomas')
for m in sorted(bymod):
    c = bymod[m]
    print(f'  {m:40s} {c["total"]:4d} {c["choice"]:4d} {c["metarules"]:4d} {c["cero"]:4d}')
