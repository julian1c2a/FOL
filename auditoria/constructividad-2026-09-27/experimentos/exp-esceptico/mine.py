# -*- coding: utf-8 -*-
# Recalculo independiente: ¿que titulares/constantes quedan con choice en cada escenario?
import io, sys, re, collections
sys.stdout.reconfigure(encoding='utf-8')
D='C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/'
rows=[l.rstrip('\n').split('\t') for l in io.open(D+'decls.tsv',encoding='utf-8')][1:]
ax={r[1]:r[4] for r in rows}; mod={r[1]:r[0] for r in rows}
E=[l.rstrip('\n').split('\t') for l in io.open(D+'choice_edges.tsv',encoding='utf-8')][1:]
fol=collections.defaultdict(set); ext=collections.defaultdict(set)
for m,n,d,md,f in E:
    (fol if f=='true' else ext)[n].add(d)
txt=io.open('E:/dropbox/github/lean4/ROBINSON_PlusPlus/check-footprints.bash',encoding='utf-8').read()
tab=re.search(r"read -r -d '' TABLA <<'EOF'\n(.*?)\nEOF",txt,re.S).group(1)
tit=[l.split('|')[0] for l in tab.splitlines() if '|' in l]
titF=[t for t in tit if t in ax]
ch={n for n,a in ax.items() if 'Classical.choice' in a}
titC=[t for t in titF if t in ch]
print('titulares fila:',len(tit),'FOL:',len(titF),'con choice:',len(titC))
def grp(n):  # agrupa auxiliares
    n=re.sub(r'\._(f|sunfold|unfold|unsafe_rec|proof_\d+)$','',n)
    n=re.sub(r'\.(eq_\d+|eq_def|match_\d+(_\d+)?)$','',n)
    return n
def compute(clean=set(), removed=set()):
    # clean: grupos cuya prueba se rehace sin choice (sin aristas ni fuentes)
    # removed: grupos que desaparecen (no cuentan, y sus usuarios pierden la arista)
    has=set()
    nodes=set(fol)|set(ext)|ch
    memo={}
    sys.setrecursionlimit(100000)
    def h(n,stack=()):
        if n in memo: return memo[n]
        g=grp(n)
        if g in clean or g in removed: memo[n]=False; return False
        memo[n]=None
        r=bool(ext[n]) or any(h(d) for d in fol[n] if memo.get(d) is not False and (memo.get(d) or h(d)))
        memo[n]=r; return r
    res={n for n in ch if h(n) and grp(n) not in removed}
    return res
F='FOL.'
A={F+'Fresh0.cst_zero_ne',F+'Fresh0.cst_ne_shift',F+'Fresh0.cst_bound_sym',F+'Metamath.Enumeration.natToString_surj',
   F+'Henkin0.henkin_step_consistent₀',F+'Lindenbaum0.derivesSet0_intro_impl',F+'HenkinLimit0.bnd',F+'HenkinLimit0.bnd_spec',
   F+'substTerm_subst_comm_succ'}
B={F+'Fresh0.derivesSet0_shift_inv',F+'Rename.derives0_rename_conservative'}
C={F+'Lindenbaum0.LindenbaumStep',F+'Lindenbaum0.lindenbaum_step_consistent',F+'Lindenbaum0.lindenbaum_step_subset',
   F+'Lindenbaum0.lindenbaum_lemma₀',F+'Lindenbaum0.henkin_completion₀'}
T={F+'Canonical0.derives0_em',F+'Canonical0.derives0_peirce',F+'Inconsistencia.derives0_no_disjunction_property',F+'Skolem0.henkin_conservative₀'}
G={F+'Metamath.Soundness0.derives0_consistent',F+'Metamath.Soundness0.derives0_not_complete',F+'SequentSound0.lk0_not_empty',
   F+'SequentSound0.lk0_to_derives0',F+'SequentSound0.lk0_to_derives2'}
Qrem={F+'Canonical0.quotientOut',F+'Canonical0.quotientOut_eq',F+'Canonical0.pointwiseEqv_out_mk'}
def rep(name,clean,removed=set()):
    r=compute(clean,removed)
    free=[t for t in titC if t not in r]
    print(f'{name}: constantes con choice {len(r)}; titulares libres {len(free)}; quedan {len(titC)-len(free)}')
    return r,free
rep('base',set())
rA,fA=rep('A',A)
rep('A+B',A|B)
rep('A+B+C (sin Q)',A|B|C)
rep('A+B+C+Q (Q = retirar quotientOut, _eq, pointwiseEqv_out_mk)',A|B|C,Qrem)
rep('A+B+C+T',A|B|C|T)
rep('A+B+C+T+G',A|B|C|T|G)
r,f=rep('A+B+C+T+G+Q',A|B|C|T|G,Qrem)
rep('A+C (sin descongelar Rename)',A|C)
rep('A+C+T (sin Rename; sin tocar congelados)',A|C|T)
print('modulos:',collections.Counter(mod[n] for n in r))
print('--- con unshiftC (inversa global de shift sin choice; exp-esceptico/U2.lean) ---')
Bu={F+'Fresh0.derivesSet0_shift_inv',F+'Compacity0.hasLargeModels_shift'}
rep('A+Bu (sin descongelar Rename)',A|Bu)
rep('A+Bu+C',A|Bu|C)
rep('A+Bu+C+T',A|Bu|C|T)
rep('A+Bu+C+T+G',A|Bu|C|T|G)
rep('A+Bu+B+C+T+G',A|Bu|B|C|T|G)
rem=Qrem|{F+'Rename.invOf',F+'Rename.invOf_spec'}
r,f=rep('A+Bu+B+C+T+G, retirando quotientOut/_eq/pointwiseEqv_out_mk e invOf/invOf_spec',A|Bu|B|C|T|G,rem)
print(collections.Counter(mod[n] for n in r))
for t in titC:
    if t in r and ('infinite_model_of_large' in t or 'countable_infinite' in t): print('  sigue con choice (por completitud):',t)
