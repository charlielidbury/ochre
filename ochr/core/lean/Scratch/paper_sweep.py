#!/usr/bin/env python3
"""Regenerate Scratch/PaperSweep.lean from the paper: every fenced program in §1, §2, §8 and the
appendix, transliterated only as the checker's surface needs (`def`, curried binders, `Type₀`
→ `Type`, a `λ` bound by `let` parenthesised), plus the inline fragments (kept by hand below).
Usage: python3 Scratch/paper_sweep.py > Scratch/PaperSweep.lean && lake env lean Scratch/PaperSweep.lean
Every block should print "n/n as expected"; the expected verdicts are the paper's claims."""
import re, sys
import os
P=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','paper','sections')+'/'
def blocks(f):
    ls=open(P+f).read().split('\n'); out=[]; cur=None
    for i,l in enumerate(ls,1):
        if l.strip().startswith('```'):
            if cur is None: cur=(i,[])
            else: out.append(cur); cur=None
            continue
        if cur is not None: cur[1].append(l)
    return out
def split_defs(lines):
    defs=[]; cur=None
    for l in lines:
        if re.match(r"^\s{0,2}(inductive\s|[A-Z]\w*'?(\(| :))",l):
            cur=[l]; defs.append(cur)
        elif cur is not None and l.strip(): cur.append(l)
    return defs
def split_top(s):
    parts=[]; d=0; cur=''
    for ch in s:
        if ch in '([{⟨': d+=1
        if ch in ')]}⟩': d-=1
        if ch==',' and d==0: parts.append(cur); cur=''
        else: cur+=ch
    parts.append(cur); return [p.strip() for p in parts if p.strip()]
def translit(text):
    text=' '.join(text.split())
    if text.startswith('inductive'): return text.replace('Type₀','Type')
    m0=re.match(r"^([A-Z]\w*'?) :",text)
    if m0: return ('def '+text).replace('Type₀','Type')
    m=re.match(r"^([A-Z]\w*'?)\(",text)
    name=m.group(1); i=m.end(); d=1; j=i
    while d: 
        if text[j] in '([': d+=1
        elif text[j] in ')]': d-=1
        j+=1
    binders=split_top(text[i:j-1]); rest=text[j:]
    bs=[]
    for b in binders:
        ns,_,ty=b.partition(':')
        for n in ns.split(','): bs.append(f'({n.strip()} : {ty.strip()})')
    return (f'def {name} '+' '.join(bs)+rest).replace('Type₀','Type')
REJECT={'Clear','BoomL','LieB','BoomB','LieH','BoomH','Bad','L','Bad4','Esc','Bad5','IsL','Irr','Boom','Impred','PolyId','SelfApp'}
def defs(f):
    out=[]
    for ln,b in blocks(f):
        for d in split_defs(b):
            t=translit('\n'.join(d))
            m=re.match(r'(def|inductive) (\w+\'?)',t)
            if not m or '≡' in t: continue
            out.append((m.group(2),t,f'{f}:{ln}'))
    return out
def emit(name, uses, items, rename={}):
    print(f'ochr {name}{" uses "+uses if uses else ""} {{')
    for n,t,loc in items:
        if n in rename: t=t.replace(f'def {n} ',f'def {rename[n]} ',1); n=rename[n]
        if n=='Clear': t+=' := refl'
        t=t.replace('let h = λ(x : &Nat) : U(n) => (*x := S Z; V(n)); let c','let h = (λ(x : &Nat) : U(n) => (*x := S Z; V(n))); let c')
        print(f'  -- {loc}')
        print('  '+('reject ' if n in REJECT else '')+t)
    print('}')
    print(f'#eval IO.println (run "{name}" {name}).show')
S2=[d for d in defs('intro.typ')+defs('overview.typ')]
seen=set(); S2u=[]
for d in S2:
    if d[0] in seen: continue
    seen.add(d[0]); S2u.append(d)
trees={'InsertM','Insert','SizeInsert'}
print('import Ochr.Examples.«17HashMap»\nimport Ochr.Examples.«16Arrays»\nopen Ochr Ochr.Test')
emit('SweepS2','',[d for d in S2u if d[0] not in trees|{'Clear'}])
print('''ochr SweepTrees uses Std {
  -- not printed: the tree, `Lt`, `Size`, `AddMS`/`AddS` as in InPlaceTrees
  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)
  def Lt (a : Word) (b : Word) : Bool by a := match a { Zero => match b { Zero => false, Succ _ => true }, Succ a' => match b { Zero => false, Succ b' => Lt(a', b') } }
  def AddMS (x : &Nat) (y : Nat) : Id Unit (AddM(x, S y)) (AddM(&*x, y); *x := S *x) by x := match *x { Z => refl, S p => AddMS(&p, y) }
  def AddS (x : Nat) (y : Nat) : Id Nat (Add(x, S y)) (S (Add(x, y))) := AddMS(&x, y)
  def Size (t : Tree) : Nat by t := match t { Leaf => 0, Node(l, v, r) => S (Add(Size(l), Size(r))) }''')
for n,t,loc in S2u:
    if n in trees: print(f'  -- {loc}\n  {t}')
print('}\n#eval IO.println (run "SweepTrees" SweepTrees).show')
emit('SweepClear','Std',[d for d in S2u if d[0]=='Clear'])
emit('SweepHM','Std, HashMap, HashMapLookup',defs('impl.typ')[:1],{'InsertFindOther':'InsertFindOtherP'})
emit('SweepQS','Quicksort',defs('impl.typ')[1:],{'QSCorrect':'QSCorrectP'})
A=defs('appendix.typ')
emit('SweepApp1','',[d for d in A if d[0] not in {'Or','IsL','Irr','Boom'}])
emit('SweepApp2','Std',[d for d in A if d[0] in {'Or','IsL','Irr','Boom'}])
print('''-- inline fragments, verbatim inside the smallest program that runs them
ochr SweepInline uses Std, Fixtures {
  -- meta.typ:70 (naturality), at an abstract `n` and at 0, 1
  reject def PickEarly (n : Nat) (a : Nat) (b : Nat) : Unit := let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  def PickEarly0 (a : Nat) (b : Nat) : Unit := let n = 0; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  def PickEarly1 (a : Nat) (b : Nat) : Unit := let n = 1; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }
  -- eval.typ §4.3 closure fragments
  def CapCopy (x : &Nat) : Nat := let n = clone(*x); let f = (λ(y : Nat) : Nat => clone(n)); f(0)
  def TwiceMZeroFrag (x : &Nat) : Unit := let g = (λ(z : &Nat) : Unit => AddM(z, 0)); g(x)
  -- appendix note 27
  def CapS (x : &Nat) : Nat := AddM(&*x, 1); let n = clone(*x); let f = (λ(y : Nat) : Nat => clone(n)); f(0)
  -- typing.typ intro, obs.typ §5
  def LetZ (x : Nat) : Nat := let z = (let y = &x; *y := 2; x); let h : Id Nat z 2 = refl; z
  def WriteNeq (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : Nat := match e {}
  reject def OwnedLocal (x : Nat) : Id Unit (x := 6) () := refl
  -- appendix notes 6, 7, 11, [Close]'s row
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def PickY (x : &Nat) (y : &Nat) : &Nat := y
  def PF (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : False := e
  reject def QF (g : Π(n : Nat). &Nat) : False := PF(g(5), refl)
  reject def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }
  reject def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()
}
#eval IO.println (run "SweepInline" SweepInline).show
-- appendix note 11's `G`, with `&` read from the declared type switched off
ochr SweepG uses Std {
  def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }
  def G (n : Nat) (a : Nat) : Unit := let r = F(n, &a); let b = a; let r2 = r; ()
  reject def UseG : Unit := G(0, 5)
}
#eval IO.println (run "SweepG" SweepG { refTop := false }).show
''')
