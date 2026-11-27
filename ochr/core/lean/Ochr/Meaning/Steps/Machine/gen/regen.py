import json,re,subprocess
D='/home/charlielidbury/repos/ochre-machine/ochr/core/lean/Ochr/Meaning/Steps/Machine/'
src=open('/home/charlielidbury/repos/ochre-machine/ochr/core/lean/Ochr/Machine.lean').read().split('\n')
def body(name):
    i=next(k for k,l in enumerate(src) if l.startswith(f'def {name} '))
    j=next(k for k in range(i,len(src)) if "let fuel' + 1 := fuel" in src[k])
    e=next(k for k in range(j,len(src)) if src[k].startswith('termination_by'))
    lines=[re.sub(r"\bfuel'",'n',l) for l in src[j+1:e]]
    lines=[l for l in lines if not l.strip().startswith('--')]
    lines=[re.sub(r'\s+--.*$','',l) if ' -- ' in l and '"' not in l.split(' -- ')[1] else l for l in lines]
    return '\n'.join('    '+l for l in lines)
groups=[
 ('StepSubst','substitution and normal forms','substV,substT,substEnv,nfSealed'),
 ('StepBorrow','borrows ([End], [Access], [Repack])','endBorrow,lentUnknown,repackCheck,repackAt,bodyReturns,endAll,obsResult,endTopLoan,accessPath,accessInside,accessNeutralHead'),
 ('StepPlace',"reads, borrows, assignments, drops, a place's type",'openWrite,readPlace,copyRead,borrowPlace,assignPlace,dropTopBind,endLoansOfTopBind,dropValue,endLoansOfTopTemp,popFrame,placeType?,placeType,natPlace,projIn,projMatch,depFieldType'),
 ('StepTypes',"values' types, fields, captures",'packedErr,convVal,valType?,valType,sealedType?,fieldDeclType,fieldTele,fieldTypes,fieldTypesOf,fieldsGeneric,fieldTypeAt,indValType?,bindDataFields,piSort,evalType,capture'),
 ('StepConv','the comparison','conv,convList,convTList,convPi,convT,convFn,convFnRun'),
 ('StepEval','evaluation','mkEqM,rewriteGoal,expectTy,eval,evalAt,jMotiveAt,evalCore,lentProofAssign,evalTInd,evalParams,checkParams,evalCtor'),
 ('StepCall','calls','unknownLent,lentLeafCheck,stmtCallee,evalCall,argHint,funType?,funType,callType,declCallType,forceHint,paramTypes,bindTy?,endBorrowArgs,runBody,runBodyCore,callFn,closeCall'),
 ('StepMatch','matches, refinement, generalisation','refine,evalMatch,natScrutinee,generalizeNeutral,sealedResultType?,renormAll,renormV,renormT,splitThenClose,splitArmsThenClose,ctorRefinement,scrutType,evalMatchByType,evalMatchInd,etaInPlace,etaPlace,movedPlace'),
 ('StepJoin','the join and stuck blocks','staticJoin,joinDrop,joinCont,joinEnds,blockEntry,entryAccess,dropAtJoin,blockCaptures,closeBlock'),
 ('StepTail','observations, Id, tail position, [Fix]','observe,idType,stuckScrutinee,findSplit,generalizeFound,splitTarget,checkTail,checkTailAt,checkFix'),
]
res=json.load(open('sigs.json'))
names=[n for n,_ in res if n not in ('joinLogged','lentInFields')]
listed=[x for g in groups for x in g[2].split(',')]
missing=set(names)-set(listed); extra=set(listed)-set(names)
assert not missing and not extra, (missing,extra)
stubs=json.load(open('stubs.json'))
for fname,title,ns in groups:
    out=[f'''import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: {title}

Each function at fuel `nf + 1`, its body walked by `grows_go ih` (the induction hypothesis at `nf`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {{tb : Tab}} {{nf : Nat}}
''']
    for nm in ns.split(','):
        st=stubs[nm][0]
        if nm=='evalType':
            out.append('''/-- `evalType` at `n + 1` (its equation lemmas time out when generated: the fuel's match sits under
`inStatement`; at `n + 1` the unfolding is `rfl`). -/
theorem evalType_succ (n : Nat) (t : Term) : Ochr.evalType (n + 1) t = inStatement (do
'''+body('evalType')+') := rfl\n')
            st=st.replace('unfold Ochr.evalType; grows_go ih','rw [evalType_succ]; grows_go ih')
        if nm=='observe':
            out.append('''/-- `observe` at `n + 1` (as `evalType_succ`: the fuel's match sits under `inStatement`). -/
theorem observe_succ (n : Nat) (typed : Bool) (t : Term) (A : Value) (W : List Pos)
    (refs : List (Place × Value × Value)) (consumed : List Place) :
    Ochr.observe (n + 1) typed t A W refs consumed = inStatement (do
'''+body('observe')+') := rfl\n')
            st=st.replace('unfold Ochr.observe; grows_go ih','rw [observe_succ]; grows_go ih')
        if nm == 'callFn':
            # main's D135 (`underCheck`) doubled the match on the head: 4,000,000 times out (lead31)
            st='set_option maxHeartbeats 16000000 in\n'+st
        elif nm == 'evalCore':
            st='set_option maxHeartbeats 4000000 in\n'+st
        out.append(st)
    out.append('end Ochr.Meaning.Steps.Machine\n')
    open(D+fname+'.lean','w').write('\n'.join(out))
# zero
out=['''import Ochr.Meaning.Steps.Machine.IH

/-!
# The base of the induction for the machine's block: every function at fuel `0`

Each is out of fuel at once, or (`convList`, `convTList`) answers an empty list without running.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab}
''']
for n in names:
    z=stubs[n][1]
    if n=='evalType':
        z=z.replace('unfold Ochr.evalType; grows_go','have e : Ochr.evalType 0 t = inStatement (exhausted "out of fuel") := rfl\n  rw [e]; grows_go')
    if n=='observe':
        z=z.replace('unfold Ochr.observe; grows_go','have e : Ochr.observe 0 typed t A W refs consumed = inStatement (exhausted "out of fuel") := rfl\n  rw [e]; grows_go')
    out.append(z)
out.append('end Ochr.Meaning.Steps.Machine\n')
open(D+'Zero.lean','w').write('\n'.join(out))
# All
def q(n): return n.replace('?','Q')
a=open(D+'All.lean').read()
i=a.index('theorem machineGrows_zero : MachineGrows tb 0 where\n')
j=a.index('/-- **Every function of the machine')
mid='theorem machineGrows_zero : MachineGrows tb 0 where\n'+'\n'.join(f'  {n} := zero_{q(n)}' for n in names)+'\n  joinContRet := retOk_joinCont_zero\n\n'
mid+='theorem machineGrows_succ (nf : Nat) (ih : MachineGrows tb nf) : MachineGrows tb (nf + 1) where\n'+'\n'.join(f'  {n} := step_{q(n)} ih' for n in names)+'\n  joinContRet := retOk_joinCont nf ih\n\n'
a=a[:i]+mid+a[j:]
a=a.replace('import Ochr.Meaning.Steps.Machine.StepPending\n','import Ochr.Meaning.Steps.Machine.StepConv\n')
open(D+'All.lean','w').write(a)
print('ok')
