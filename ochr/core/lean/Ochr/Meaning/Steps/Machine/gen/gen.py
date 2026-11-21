import re, json
src=open('/home/charlielidbury/repos/ochre-machine/ochr/core/lean/Ochr/Machine.lean').read().split('\n')
# the mutual block: the `mutual` after line 700 and the last `end` at column 0
start=next(i for i,l in enumerate(src) if l.startswith('mutual') and i>700)+1
end=max(i for i,l in enumerate(src) if l.strip()=='end' and i>start)+1
defs=[]
i=start-1
while i<end:
    l=src[i]
    if l.startswith('def '):
        sig=l; j=i
        while True:
            # stop when we see ' : M' return type at depth 0 followed by ':=' or a line starting with '|'
            if re.search(r'\)\s*:\s*\n?\s*M\b|:\s*M\b',sig) and (':=' in sig or (j+1<len(src) and src[j+1].strip().startswith('|'))): break
            j+=1; sig+=' '+src[j].strip()
        defs.append(sig)
    i+=1
def groups(s):
    # s after name; parse top-level (...) groups until ' : M'
    out=[];depth=0;cur='';k=0
    while k<len(s):
        c=s[k]
        if c=='(' :
            if depth==0: cur=''
            else: cur+=c
            depth+=1
        elif c==')':
            depth-=1
            if depth==0: out.append(cur)
            else: cur+=c
        elif depth==0 and s[k:k+1]==':' : break
        else:
            if depth>0: cur+=c
        k+=1
    return out
res=[]
for d in defs:
    m=re.match(r'def (\S+)\s*(.*)',d)
    name=m.group(1); rest=m.group(2)
    params=[]
    for g in groups(rest):
        g=re.sub(r':=.*$','',g).strip()
        names,ty=g.split(':',1)
        for nm in names.split():
            params.append((nm.strip(),ty.strip()))
    # positional list-pattern functions (convList/convTList)
    if name in ('convList','convTList'):
        ty='List Value' if name=='convList' else 'List Term'
        params.append(('as',ty)); params.append(('bs',ty))
    res.append((name,params))
json.dump(res,open('sigs.json','w'))
for n,p in res: print(n,[x[0] for x in p])
