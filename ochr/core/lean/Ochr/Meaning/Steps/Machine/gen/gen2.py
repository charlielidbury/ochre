import json
res=json.load(open('sigs.json'))
HYP={
 'fieldTele': {'val':'(hval : ∀ i v, GrowsIn tb (val i v))'},
 'splitArmsThenClose': {'arms':'(harms : ∀ a ∈ arms, GrowsIn tb a.1)'},
 'joinDrop': {'run':'(hrun : GrowsIn tb run)'},
 'joinEnds': {'run':'(hrun : GrowsIn tb run)'},
 'joinCont': {'k':'(hk : ∀ r R, GrowsIn tb (k r R))'},
 'checkTail': {'k':'(hk : ∀ r R, GrowsIn tb (k r R))'},
 'checkTailAt': {'k':'(hk : ∀ r R, GrowsIn tb (k r R))'},
 'closeBlock': {'arms':'(harms : ∀ a ∈ arms, GrowsIn tb a.setup ∧ ∀ r, GrowsIn tb (a.body r))'},
}
def ren(x): return {'self':'self'}.get(x,x)
def binders(name,params):
    out=[]
    for nm,ty in params:
        if nm=='fuel': continue
        out.append(f'({ren(nm)} : {ty})')
        if name in HYP and nm in HYP[name]: out.append(HYP[name][nm])
    return out
def call(name,params,fuel):
    args=[ren(nm) if nm!='fuel' else fuel for nm,_ in params]
    return f'Ochr.{name} '+' '.join(f'({a})' if ' ' in a else a for a in args)
fields=[]
for name,params in res:
    if name in ('joinLogged','lentInFields'): continue
    b=binders(name,params)
    q = ("∀ "+" ".join(b)+", ") if b else ""
    fields.append(f'  {name} : {q}GrowsIn tb ({call(name,params,"nf")})')
fields.append('  joinContRet : ∀ (mt : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)),\n    RetOk tb (Ochr.joinCont nf mt k) (fun k\' => ∀ r R, GrowsIn tb (k\' r R))')
open('fields.lean','w').write('\n'.join(fields)+'\n')
# step lemma stubs
stubs={}
for name,params in res:
    if name in ('joinLogged','lentInFields'): continue
    b=binders(name,params)
    names=[]
    for x in b:
        nm=x[1:].split(':')[0].strip()
        names.append(nm)
    q = ("∀ "+" ".join(b)+", ") if b else ""
    it = ("intro "+" ".join(names)+"\n  ") if b else ""
    stubs[name]=(f'theorem step_{name.replace("?","Q")} (ih : MachineGrows tb nf) :\n    {q}GrowsIn tb ({call(name,params,"(nf + 1)")}) := by\n  {it}unfold Ochr.{name}; grows_go ih\n',
                 f'theorem zero_{name.replace("?","Q")} :\n    {q}GrowsIn tb ({call(name,params,"0")}) := by\n  {it}unfold Ochr.{name}; grows_go\n')
json.dump(stubs,open('stubs.json','w'))
print(len(fields))
