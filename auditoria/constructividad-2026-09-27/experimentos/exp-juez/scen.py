# -*- coding: utf-8 -*-
import io, sys, re, collections
sys.stdout.reconfigure(encoding='utf-8')
D = 'C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/'
rows = [l.rstrip('\n').split('\t') for l in io.open(D + 'decls.tsv', encoding='utf-8')][1:]
edges = [l.rstrip('\n').split('\t') for l in io.open(D + 'choice_edges.tsv', encoding='utf-8')][1:]
ax = {r[1]: r[4] for r in rows}
mod = {r[1]: r[0] for r in rows}
txt = io.open('E:/dropbox/github/lean4/ROBINSON_PlusPlus/check-footprints.bash', encoding='utf-8').read()
m = re.search(r"read -r -d '' TABLA <<'EOF'\n(.*?)\nEOF", txt, re.S)
tabrows = [l.split('|') for l in m.group(1).splitlines() if '|' in l]
tit_all = [t[0] for t in tabrows]
tit = [t for t in tit_all if t in ax]
choice_tit = [t for t in tit if 'Classical.choice' in ax[t]]
print('filas en TABLA:', len(tit_all), ' de FOL/TF (en decls):', len(tit), ' con choice:', len(choice_tit))
succ0 = collections.defaultdict(set); ext0 = collections.defaultdict(set)
for md, n, d, mdd, isf in edges:
    (succ0[n] if isf == 'true' else ext0[n]).add(d)
def base(n):
    n = re.sub(r'\._(f|sunfold|unfold|unsafe_rec)$', '', n)
    n = re.sub(r'\.(eq_\d+|eq_def|match_\d+(_\d+)?)$', '', n)
    return n
def reach(t, succ):
    seen = set(); st = [t]
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(succ[x])
    return seen
def origins(t, succ, ext):
    return sorted({base(x) for x in reach(t, succ) if ext[x]})
# corrected origins (includes self)
orig = {t: origins(t, succ0, ext0) for t in choice_tit}
old = {}
for l in io.open(D + 'origenes_titulares.txt', encoding='utf-8'):
    if l.startswith('#'): continue
    p = l.rstrip('\n').split('\t'); old[p[1]] = set(p[2].split('; '))
print('\n== diferencias con origenes_titulares.txt (corregido - viejo) ==')
for t in choice_tit:
    d1 = set(orig[t]) - old.get(t, set()); d2 = old.get(t, set()) - set(orig[t])
    if d1 or d2: print('  ', t, '+', sorted(d1), '-', sorted(d2))
# fixed point: which constants have choice under modified graph
def choice_set(succ, ext):
    has = {n for n in set(succ) | set(ext) if ext[n]}
    # predecessor propagation
    pred = collections.defaultdict(set)
    for n, ds in succ.items():
        for d in ds: pred[d].add(n)
    st = list(has)
    while st:
        x = st.pop()
        for p in pred[x]:
            if p not in has:
                has.add(p); st.append(p)
    return has
allchoice = {n for n, a in ax.items() if 'Classical.choice' in a}
base_has = choice_set(succ0, ext0)
print('\nconstantes FOL con choice (decls):', len(allchoice), ' reproducidas por el grafo:', len(base_has & allchoice), ' extra en grafo:', len(base_has - allchoice))
def apply(steps):
    succ = collections.defaultdict(set, {k: set(v) for k, v in succ0.items()})
    ext = collections.defaultdict(set, {k: set(v) for k, v in ext0.items()})
    for kind, *args in steps:
        if kind == 'clean':          # reproof sin choice: sin fuentes externas ni aristas con choice
            for n in args:
                for k in list(succ):
                    if base(k) == n: succ[k] = set()
                for k in list(ext):
                    if base(k) == n: ext[k] = set()
        elif kind == 'cut':          # quitar arista n -> d
            n, d = args
            for k in list(succ):
                if base(k) == n: succ[k] = {x for x in succ[k] if base(x) != d}
        elif kind == 'set':          # fijar aristas
            n, ds = args
            for k in list(succ):
                if base(k) == n: succ[k] = set()
            for k in list(ext):
                if base(k) == n: ext[k] = set()
            succ[n] = set(ds)
    return succ, ext
F='FOL.'
A = [('clean', F+'Fresh0.cst_zero_ne'), ('clean', F+'Fresh0.cst_ne_shift'), ('clean', F+'Fresh0.cst_bound_sym'),
     ('clean', F+'Metamath.Enumeration.natToString_surj'), ('clean', F+'Henkin0.henkin_step_consistent₀'),
     ('clean', F+'Lindenbaum0.derivesSet0_intro_impl'), ('clean', F+'HenkinLimit0.bnd'), ('clean', F+'HenkinLimit0.bnd_spec'),
     ('clean', F+'substTerm_subst_comm_succ')]
B = [('clean', F+'Fresh0.derivesSet0_shift_inv'), ('clean', F+'Rename.derives0_rename_conservative')]
C = [('clean', F+'Lindenbaum0.LindenbaumStep'), ('clean', F+'Lindenbaum0.lindenbaum_step_consistent'),
     ('clean', F+'Lindenbaum0.lindenbaum_step_subset'), ('clean', F+'Lindenbaum0.LindenbaumLimit'),
     ('clean', F+'Lindenbaum0.lindenbaum_limit_bound'), ('clean', F+'Lindenbaum0.lindenbaum_step_mono'),
     ('set', F+'Lindenbaum0.lindenbaum_lemma₀', [F+'Metamath.Enumeration.natToFormula_surj'])]
Q = [('cut', n, F+'Canonical0.quotientOut') for n in [F+'Canonical0.canonicalModel', F+'Canonical0.truth_lemma_lt', F+'Canonical0.evalTerm_canonical', F+'Canonical0.pointwiseEqv_out_mk']] + \
    [('cut', F+'Canonical0.pointwiseEqv_out_mk', F+'Canonical0.quotientOut_eq')]
T = [('clean', F+'Canonical0.derives0_em'), ('clean', F+'Canonical0.derives0_peirce'),
     ('clean', F+'Inconsistencia.derives0_no_disjunction_property'), ('clean', F+'Skolem0.henkin_conservative₀')]
scen = {'S1 (A: pruebas locales, mismos enunciados)': A, 'S2 (A+B: locInv, descongela Rename)': A+B,
        'S3 (A+B+C+Q: Lindenbaum impredicativo y cociente por listas)': A+B+C+Q,
        'S4 (S3 + titulares reprobados: em, peirce, no_disjunction, henkin_conservative)': A+B+C+Q+T}
prev = set()
for name, st in scen.items():
    succ, ext = apply(st)
    has = choice_set(succ, ext)
    freed = [t for t in choice_tit if t not in has]
    print(f'\n== {name}: constantes FOL con choice {len(has & allchoice)} de {len(allchoice)}; titulares libres {len(freed)} de {len(choice_tit)}')
    for t in freed:
        print('   ' + ('  ' if t in prev else '+ ') + t)
    prev = set(freed)
    last = (succ, ext, has)
succ, ext, has = last
print('\n== IRREDUCIBLES tras S4: titular -> origenes que le quedan ==')
for t in choice_tit:
    if t in has:
        print('  ', t, '<-', ', '.join(x.replace('FOL.','') for x in origins(t, succ, ext)))
# lista de origenes corregidos para el informe
print('\n== ORIGENES CORREGIDOS (n) ==')
for t in choice_tit:
    print('  ', t, len(orig[t]))
# que titulares contamina cada entrada
print('\n== ENTRADA -> titulares que contamina (corregido) ==')
contam = collections.defaultdict(list)
for t in choice_tit:
    for o in orig[t]: contam[o].append(t)
for o in sorted(contam, key=lambda x: -len(contam[x])):
    print(f'  {len(contam[o]):3d} {o}')

print('\n== listas de titulares por entrada (pequenas y medianas) ==')
for o in sorted(contam, key=lambda x: -len(contam[x])):
    ts = [t.replace('FOL.','').replace('Metamath.','') for t in contam[o]]
    print(f'  {o.replace("FOL.","")} ({len(ts)}): ' + ', '.join(ts))

print('\n== ESCENARIO FINAL (S4 + henkin_completion₀ por límite cerrado + gemelos ADR-061) ==')
H = [('clean', F+'Lindenbaum0.henkin_completion₀')]
G = [('clean', F+'Metamath.Soundness0.derives0_consistent'), ('clean', F+'Metamath.Soundness0.derives0_not_complete'),
     ('clean', F+'SequentSound0.lk0_not_empty'), ('clean', F+'SequentSound0.lk0_to_derives0'), ('clean', F+'SequentSound0.lk0_to_derives2')]
for name, st in {'S5 = S4 + henkin_completion₀': A+B+C+Q+T+H, 'S6 = S5 + gemelos (ADR-061)': A+B+C+Q+T+H+G}.items():
    succ, ext = apply(st)
    has = choice_set(succ, ext)
    freed = [t for t in choice_tit if t not in has]
    print(f'{name}: constantes con choice {len(has & allchoice)} de {len(allchoice)}; titulares libres {len(freed)}; quedan {len(choice_tit)-len(freed)}')
    if name.startswith('S6'):
        print('  QUEDAN:')
        for t in choice_tit:
            if t in has: print('    ', t)
        mods = collections.Counter(mod[n] for n in has & allchoice)
        print('  modulos con choice:', len(mods), dict(mods))
