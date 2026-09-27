import io, sys
sys.stdout.reconfigure(encoding='utf-8')
D='C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/'
rows=[l.rstrip('\n').split('\t') for l in io.open(D+'decls.tsv',encoding='utf-8')][1:]
q=sys.argv[1:]
for m,n,k,nc,a in rows:
    for x in q:
        if n==x or n.endswith('.'+x):
            print(f'{m}\t{n}\t{k}\tnc={nc}\t[{a}]')
