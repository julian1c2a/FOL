import io, sys, collections
sys.stdout.reconfigure(encoding='utf-8')
D='C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/'
rows=[l.rstrip('\n').split('\t') for l in io.open(D+'decls.tsv',encoding='utf-8')][1:]
by=collections.defaultdict(list)
for m,n,k,nc,a in rows:
    if 'Classical.choice' in a: by[m].append((n,k,a))
for m in sorted(by):
    print('==',m,len(by[m]))
    for n,k,a in sorted(by[m]): print('   ',k,n,'|',a)
