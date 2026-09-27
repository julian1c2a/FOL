import json, io, sys
sys.stdout.reconfigure(encoding='utf-8')
D='C:/msys64/tmp/claude/e--dropbox-github-lean4-FOL/dc390825-7a17-4693-bf72-7a68c475e9c7/scratchpad/audit/'
E=json.load(io.open(D+'exp-juez/edits_juez.json',encoding='utf-8'))
print(type(E), len(E))
if isinstance(E,dict): E=E.get('ediciones',E)
R='E:/dropbox/github/lean4/FOL/'
from collections import Counter
perfile=Counter()
for i,e in enumerate(E):
    f=e['fichero']; b=e['buscar']
    try: t=io.open(R+f,encoding='utf-8').read()
    except Exception as ex: print(i,f,'NO EXISTE',ex); continue
    n=t.count(b)
    perfile[f]+=1
    print(f'{i:2d} {f:35s} ocurrencias={n}')
print(perfile, sum(perfile.values()))
