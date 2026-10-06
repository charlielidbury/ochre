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
        t=t.replace('let h = λ(x : &Nat) : U(n) => (*x := S(Z); V(n)); let c','let h = (λ(x : &Nat) : U(n) => (*x := S(Z); V(n))); let c')
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
print("ochr SweepTrees uses Std {\n  -- not printed: the tree, `Lt`, `Size`, `AddMS`/`AddS` as in InPlaceTrees\n  inductive Tree := Leaf | Node(l : Tree, v : Word, r : Tree)\n  def Lt (a : Word) (b : Word) : Bool by a := match a { Zero => match b { Zero => false, Succ _ => true }, Succ a' => match b { Zero => false, Succ b' => Lt(a', b') } }\n  def AddMS (x : &Nat) (y : Nat) : Id(Unit, AddM(x, S(y)), AddM(&*x, y); *x := S(*x)) by x := match *x { Z => refl, S p => AddMS(&p, y) }\n  def AddS (x : Nat) (y : Nat) : Id(Nat, Add(x, S(y)), S(Add(x, y))) := AddMS(&x, y)\n  def Size (t : Tree) : Nat by t := match t { Leaf => 0, Node(l, v, r) => S(Add(Size(l), Size(r))) }")
for n,t,loc in S2u:
    if n in trees: print(f'  -- {loc}\n  {t}')
print('}\n#eval IO.println (run "SweepTrees" SweepTrees).show')
emit('SweepClear','Std',[d for d in S2u if d[0]=='Clear'])
emit('SweepHM','Std, HashMap, HashMapLookup',defs('impl.typ')[:1],{'InsertFindOther':'InsertFindOtherP'})
emit('SweepQS','Quicksort',defs('impl.typ')[1:],{'QSCorrect':'QSCorrectP'})
A=defs('appendix.typ')
emit('SweepApp1','',[d for d in A if d[0] not in {'Or','IsL','Irr','Boom'}])
emit('SweepApp2','Std',[d for d in A if d[0] in {'Or','IsL','Irr','Boom'}])
print("-- inline fragments, verbatim inside the smallest program that runs them\nochr SweepInline uses Std, Fixtures {\n  -- meta.typ:70 (naturality), at an abstract `n` and at 0, 1\n  reject def PickEarly (n : Nat) (a : Nat) (b : Nat) : Unit := let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }\n  def PickEarly0 (a : Nat) (b : Nat) : Unit := let n = 0; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }\n  def PickEarly1 (a : Nat) (b : Nat) : Unit := let n = 1; let r = Pick(clone(n), &a, &b); let z = b; match n { Z => *r := 5, S _ => () }\n  -- eval.typ §4.3 closure fragments\n  def CapCopy (x : &Nat) : Nat := let n = clone(*x); let f = (λ(y : Nat) : Nat => clone(n)); f(0)\n  def TwiceMZeroFrag (x : &Nat) : Unit := let g = (λ(z : &Nat) : Unit => AddM(z, 0)); g(x)\n  -- appendix note 27\n  def CapS (x : &Nat) : Nat := AddM(&*x, 1); let n = clone(*x); let f = (λ(y : Nat) : Nat => clone(n)); f(0)\n  -- typing.typ intro, obs.typ §5\n  def LetZ (x : Nat) : Nat := let z = (let y = &x; *y := 2; x); let h : Id(Nat, z, 2) = refl; z\n  def WriteNeq (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : Nat := match e {}\n  reject def OwnedLocal (x : Nat) : Id(Unit, x := 6, ()) := refl\n  -- appendix notes 6, 7, 11, [Close]'s row\n  def PickX (x : &Nat) (y : &Nat) : &Nat := x\n  def PickY (x : &Nat) (y : &Nat) : &Nat := y\n  def PF (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e\n  reject def QF (g : Π(n : Nat). &Nat) : False := PF(g(5), refl)\n  reject def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }\n  -- D66: `&A` for `A : Type₀` is well formed; a type variable in `Type₁` is not\n  def SwapT (A : Type) (x : &A) (y : &A) : Unit := ()\n  reject def SwapT1 (A : Type₁) (x : &A) (y : &A) : Unit := ()\n}\n#eval IO.println (run \"SweepInline\" SweepInline).show\n-- dependent fields (appendix, impl §8.3): the growable vector and the arm assigning its two\n-- fields in either order\nochr SweepDep uses ArrayBench {\n  inductive Vec (E : Type) := MkVec(n : Word, items : Array(E, n))\n  def Two : Array(Word, W(2)) := [Zero, Succ(Zero)]\n  def SetTwo (v : &Vec(Word)) : Unit := match *v { MkVec(n, items) => (n := W(2); items := Two) }\n  def SetTwoRev (v : &Vec(Word)) : Unit := match *v { MkVec(n, items) => (items := Two; n := W(2)) }\n}\n-- appendix A.4.8, nesting: `NBox` is accepted, `Bad` nested in it is not, and a field that is\n-- a Π at the generic fields is rejected already\nochr SweepNest uses Std {\n  inductive Void : Type\n  def IsSucc (n : Word) : Prop := match n { Zero => False, Succ(_) => True }\n  def NegIf (n : Word) (A : Type) : Type := match n { Zero => Unit, Succ(m) => Π(x : A). Void }\n  inductive NBox (A : Type) := MkNBox(n : Word, f : NegIf(n, A), h : IsSucc(n))\n  reject inductive Bad := MkBad(b : NBox(Bad))\n  def Neg (A : Type) : Type := Π(x : A). Void\n  reject inductive NegBox (A : Type) := MkNegBox(f : Neg(A))\n}\n#eval IO.println (run \"SweepNest\" SweepNest).show\n#guard ((run \"SweepNest\" SweepNest { k4Nest := false }).rows.map (fun r => r.verdict matches .accepted)) == [true, true, true, true, true, true, false]\n#eval IO.println (run \"SweepDep\" SweepDep).show\n-- the typed-fragment appendix (tf.typ): Bad2 as printed and the claims around it. Since D67\n-- (overwriting a borrow keeps the reborrows behind it) an assignment's [Access] leaves a\n-- reborrow behind the old borrow alone, so the reborrow-and-replace idiom (Trav) and the\n-- Pick variants are accepted on both paths\nochr SweepTF uses Std, Fixtures {\n  def Bad2 (n : Nat) (b : Nat) (x : &Nat) : Unit := let a = 0; x := Pick(n, &a, &b); let z = b; ()\n  def Bad2Run : Unit := (let y = 7; Bad2(0, 5, &y))\n  def Bad4 (x : &Nat) (a : Nat) : Unit := (x := TailM(&a); match a { Z => (), S _ => () })\n  def Bad4Run : Unit := (let c = 0; Bad4(&c, 1))\n  reject def RetLocal (x : &Nat) : &Nat := (let a = 0; &a)\n  reject def IdLet (a : Nat) : Id(Nat, let z = a; a, a) := refl\n  reject def LetCode (a : Nat) : Nat := let z = a; a\n  def AssignPick (n : Nat) (b : Nat) (x : &Nat) : Unit := (x := Pick(n, &*x, &b); *x := 5)\n  def AssignPick1 (b : Nat) (c : Nat) : Unit := (let x = &c; let n = 1; x := Pick(n, &*x, &b); *x := 5)\n  def AssignPickDrop (n : Nat) (b : Nat) (x : &Nat) : Unit := (x := Pick(n, &*x, &b); ())\n  def ReborrowPick (n : Nat) (a : Nat) (b : Nat) (c : Nat) : Unit := (let x = Pick(n, &a, &b); let y = &*x; x := &c; *y := 0)\n  def ReborrowPick0 (a : Nat) (b : Nat) (c : Nat) : Unit := (let n = 0; let x = Pick(n, &a, &b); let y = &*x; x := &c; *y := 0)\n  def Trav (x : &Nat) : Unit := match *x { Z => (), S p => (x := &p; *x := 0) }\n}\n#eval IO.println (run \"SweepTF\" SweepTF).show\n-- appendix note 11's `G`. The ochr command checks under the default configuration, where\n-- `F` is rejected ([D48]); the note's point is with `&` read from the declared type switched\n-- off (`refTop`), where `F` and `G` are accepted and `UseG` is not\nochr SweepG uses Std {\n  reject def F (n : Nat) (x : &Nat) : (match n { Z => &Nat, S _ => Nat }) := match n { Z => x, S _ => 0 }\n  reject def G (n : Nat) (a : Nat) : Unit := let r = F(n, &a); let b = a; let r2 = r; ()\n  reject def UseG : Unit := G(0, 5)\n}\n#eval IO.println (run \"SweepG\" SweepG).show\n#guard ((run \"SweepG\" SweepG { refTop := false }).rows.map (fun r => r.verdict matches .accepted)) == [true, true, false]\n")
