# -*- coding: utf-8 -*-
import io, sys, re, collections
sys.stdout.reconfigure(encoding='utf-8')
D = 'C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/'
rows = [l.rstrip('\n').split('\t') for l in io.open(D + 'decls.tsv', encoding='utf-8')][1:]
edges = [l.rstrip('\n').split('\t') for l in io.open(D + 'choice_edges.tsv', encoding='utf-8')][1:]
ax = {r[1]: r[4] for r in rows}
# tabla
txt = io.open('E:/dropbox/github/lean4/ROBINSON_PlusPlus/check-footprints.bash', encoding='utf-8').read()
m = re.search(r"read -r -d '' TABLA <<'EOF'\n(.*?)\nEOF", txt, re.S)
tit = [l.split('|')[0] for l in m.group(1).splitlines() if '|' in l]
tit = [t for t in tit if t in ax]
choice_tit = [t for t in tit if 'Classical.choice' in ax[t]]
print('titulares con fila y en FOL:', len(tit), ' con choice:', len(choice_tit))
succ = collections.defaultdict(set); extsrc = collections.defaultdict(set)
for mod, n, d, md, isf in edges:
    if isf == 'true': succ[n].add(d)
    else: extsrc[n].add(d)
def reach(t):
    seen = set(); st = [t]
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(succ[x])
    return seen
def base(n):
    # colapsa nombres generados al padre
    n = re.sub(r'\._(f|sunfold|unfold|unsafe_rec)$', '', n)
    n = re.sub(r'\.(eq_\d+|eq_def|match_\d+(_\d+)?)$', '', n)
    return n
TARGET = {'FOL.Henkin0.henkin_step_consistent₀', 'FOL.Lindenbaum0.derivesSet0_intro_impl'}
out = []
for t in choice_tit:
    R = reach(t)
    fr = sorted({base(x) for x in R if extsrc[x]})
    rest = [f for f in fr if f not in TARGET]
    lose = [f for f in fr if f in TARGET]
    out.append((t, fr, lose, rest))
print('\n== titulares que tienen algun origen en TARGET ==')
for t, fr, lose, rest in out:
    if lose:
        print(t, '| pierde:', ','.join(x.split('.')[-1] for x in lose), '| quedan', len(rest), ':', ','.join(x.split('.')[-1] for x in rest) if len(rest) < 6 else '...')
print('\n== quedarian SIN choice ==')
for t, fr, lose, rest in out:
    if lose and not rest: print('  ', t)
# comparacion con origenes_titulares.txt
old = {}
for l in io.open(D + 'origenes_titulares.txt', encoding='utf-8'):
    if l.startswith('#'): continue
    p = l.rstrip('\n').split('\t'); old[p[1]] = set(p[2].split('; '))
print('\n== discrepancias con origenes_titulares.txt ==')
for t, fr, lose, rest in out:
    o = old.get(t)
    if o is None: print('  falta en viejo:', t); continue
    if set(fr) != o:
        print('  ', t, ' nuevo-viejo:', set(fr) - o, ' viejo-nuevo:', o - set(fr))
