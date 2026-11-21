#!/usr/bin/env python3
"""Generator of D119's differential table, `ReturnedBorrows.SplitJoin` and `SplitJoinInd`: for
each shape a generic definition (`…g`, the split at the generic call, path 3), one inline twin per
constructor (`…i<C>`, the scrutinee a let-bound known constructor, path 1) and one closed call per
constructor (`…c<C>`, a call's run of the body, path 2), with its value asserted by `refl`
(`…c<C>_v`). The nested shapes `F`/`F2` and the `Id`/proof shapes `E`/`I` are written by hand
(`MANUAL1`, `MANUAL2`), and so is `M`, a tail match as a lambda's body. `python3 gen.py` prints the blocks' rows and the guard's table
(`splitJoinTable`, with `F`, `F2`, `M`, `E`, `I` added by hand)."""
import sys

N = ['Z', 'S(Z)']
def nat(tag):  # constructor suffixes
    return {'Z': 'Z', 'S(Z)': 'S', 'S(S(Z))': 'S'}[tag]

# shape: id, scrutinee (name, type, ctors [(suffix, value)]), params, result type (fn of ctor value or n),
# body, call (fn ctor -> (type, term)), values
S = []
def shape(id, ps, R, body, ctors, call, vals, scrut=('n', 'Nat'), inline=None, block=1):
    S.append(dict(id=id, ps=ps, R=R, body=body, ctors=ctors, call=call, vals=vals, scrut=scrut, inline=inline, block=block))

def dataCall(id, args):
    return lambda k: (None, f'{id}g({k}{", " if args else ""}{args})')

NZS = [('Z', 'Z'), ('S', 'S(Z)')]
# A: the lead's example
shape('A', '', lambda k: 'Nat', 'match n { Z => Z, S m => m }', [('Z', 'Z'), ('S', 'S(S(Z))')],
      dataCall('A', ''), {'Z': 'Z', 'S': 'S(Z)'})
# B: arms that move different parts
shape('B', '(p : Nat × Nat)', lambda k: 'Nat', 'match n { Z => p.0, S _ => p.1 }', NZS,
      dataCall('B', '(1, 2)'), {'Z': '1', 'S': '2'})
shape('B2', '(p : Nat × Nat)', lambda k: 'Nat × Nat', 'match n { Z => (let a = p.0; (a, Z)), S _ => p }', NZS,
      dataCall('B2', '(1, 2)'), {'Z': '(1, 0)', 'S': '(1, 2)'})
shape('B3', '(p : Nat × Nat)', lambda k: 'Nat × Nat',
      'match n { Z => (let a = p.0; p.0 := S(a); p), S _ => (let b = p.1; (Z, b)) }', NZS,
      dataCall('B3', '(1, 2)'), {'Z': '(2, 2)', 'S': '(0, 2)'})
# C: a dependent return type that mentions the matched parameter
shape('C', '(x : Nat)', lambda k: f'TF({k})', 'match n { Z => x, S m => () }', NZS,
      dataCall('C', '5'), {'Z': '5', 'S': '()'})
# D: a result that is a borrow passed in by a parameter
def brCall(id, pre, args):
    return lambda k: ('Nat', f'({pre} let r = {id}g({k}, {args}); clone(*r))')
for id, ps, body, pre in [
    ('D', '(x : &Nat) (y : &Nat)', 'match n { Z => x, S _ => y }', 'let a = 1;'),
    ('D2', '(x : &Nat) (y : &Nat)', 'match n { Z => &*x, S _ => (let q = x; y) }', 'let a = 1;'),
    ('D3', '(x : &Nat) (y : &Nat)', '(let r = x; match n { Z => r, S _ => y })', 'let a = 1;'),
    ('D4', '(x : &(Nat × Nat)) (y : &Nat)', 'match n { Z => &(*x).0, S _ => (let q = x; y) }', 'let a = (1, 3);'),
    ('D5', '(x : &(Nat × Nat)) (y : &Nat)', '(let r = &(*x).1; match n { Z => &(*x).0, S _ => (*r := Z; y) })', 'let a = (1, 3);'),
    ('D6', '(x : &Nat) (y : &Nat)', '(let r = &*x; match n { Z => r, S _ => (let q = x; y) })', 'let a = 1;'),
]:
    shape(id, ps, lambda k: '&Nat', body, NZS, brCall(id, pre + ' let b = 2;', '&a, &b'), {'Z': '1', 'S': '2'})
# F: nested tail matches: by hand (MANUAL1), the calls fixing both scrutinees
# G: a tail match under `let` and under `;`
shape('G', '(a : Nat)', lambda k: 'Nat', '(let b = a; match n { Z => b, S _ => Z })', NZS,
      dataCall('G', '4'), {'Z': '4', 'S': '0'})
shape('G2', '(a : Nat) (x : &Nat)', lambda k: 'Nat', '(*x := Z; match n { Z => a, S _ => Z })', NZS,
      lambda k: ('Nat', f'(let c = 1; G2g({k}, 4, &c))'), {'Z': '4', 'S': '0'})
shape('G3', '(a : Nat)', lambda k: 'Nat', '(let r = &a; match n { Z => (*r := S(Z); Z), S _ => a })', NZS,
      dataCall('G3', '4'), {'Z': '0', 'S': '4'})
shape('G4', '(a : Nat)', lambda k: 'Nat', '(let r = &a; match n { Z => (let q = r; Z), S _ => a })', NZS,
      dataCall('G4', '4'), {'Z': '0', 'S': '4'})
shape('G5', '(x : &Nat) (a : Nat)', lambda k: 'Nat', '(let r = &*x; match n { Z => (let q = x; a), S _ => (*r := a; Z) })', NZS,
      lambda k: ('Nat', f'(let c = 1; let k = G5g({k}, &c, 7); clone(c))'), {'Z': '1', 'S': '7'})
shape('G6', '(x : &Nat) (a : Nat)', lambda k: 'Nat', '(let r = x; match n { Z => (*r := a; Z), S _ => (let q = r; a) })', NZS,
      lambda k: ('Nat', f'(let c = 1; let k = G6g({k}, &c, 7); clone(c))'), {'Z': '7', 'S': '1'})
shape('G7', '(a : Nat)', lambda k: 'Nat', '(let r = &a; let s = &*r; match n { Z => (*s := 5; Z), S _ => (let q = r; a) })', NZS,
      dataCall('G7', '4'), {'Z': '0', 'S': '4'})
# H: `matchInd` with fields, with a borrowed scrutinee, and with a dependent field
CH = [('L', 'L(S(Z))'), ('R', 'R(S(Z))')]
shape('H', '(a : Nat)', lambda k: 'Nat', 'match c { L(u) => u, R(v) => a }', CH,
      dataCall('H', '5'), {'L': '1', 'R': '5'}, scrut=('c', 'Ch'), block=2)
shape('H1', '(a : Nat)', lambda k: 'Nat', 'match *c { L(u) => clone(u), R(v) => a }', CH,
      lambda k: ('Nat', f'(let c0 = {k}; H1g(&c0, 5))'), {'L': '1', 'R': '5'}, scrut=('c', '&Ch'), block=2)
shape('H2', '(a : Nat)', lambda k: 'Unit', 'match *c { L(u) => (u := a; ()), R(v) => () }', CH,
      lambda k: ('Ch', f'(let c0 = {k}; H2g(&c0, 5); c0)'), {'L': 'L(5)', 'R': 'R(1)'}, scrut=('c', '&Ch'), block=2)
DV = [('N', 'DNil'), ('C', 'DCons(S(Z), MkNBox[S(Z)](3))')]
shape('H3', '(a : Nat)', lambda k: 'Nat', 'match t { DNil => a, DCons(k, b) => k }', DV,
      dataCall('H3', '4'), {'N': '4', 'C': '1'}, scrut=('t', 'DV'), block=2)
shape('H4', '(a : Nat)', lambda k: 'Nat', 'match t { DNil => a, DCons(k, b) => match b { MkNBox(v) => v } }', DV,
      dataCall('H4', '4'), {'N': '4', 'C': '3'}, scrut=('t', 'DV'), block=2)
shape('H5', '(a : Nat)', lambda k: 'Nat', 'match *t { DNil => a, DCons(k, b) => clone(k) }', DV,
      lambda k: ('Nat', f'(let t0 = {k}; H5g(&t0, 4))'), {'N': '4', 'C': '1'}, scrut=('t', '&DV'), block=2)
shape('H6', '(a : Nat)', lambda k: 'Unit', 'match *t { DNil => (let q = a; ()), DCons(k, b) => (k := a; b := MkNBox[clone(k)](Z); ()) }', DV,
      lambda k: ('DV', f'(let t0 = {k}; H6g(&t0, 4); t0)'), {'N': 'DNil', 'C': 'DCons(4, MkNBox[4](0))'}, scrut=('t', '&DV'), block=2)
# K: a closure in an arm captures a variable
shape('K', '(a : Nat)', lambda k: 'Nat → Nat', 'match n { Z => λ(k : Nat) : Nat => clone(a), S _ => λ(k : Nat) : Nat => k }', NZS,
      lambda k: ('Nat', f'(let f = Kg({k}, 4); f(2))'), {'Z': '4', 'S': '2'}, block=2)
shape('K2', '(a : Nat) (b : Nat)', lambda k: 'Nat × (Nat → Nat)',
      'match n { Z => (b, λ(k : Nat) : Nat => clone(a)), S _ => (a, λ(k : Nat) : Nat => k) }', NZS,
      lambda k: ('Nat', f'(let p = K2g({k}, 4, 5); clone(p.0))'), {'Z': '5', 'S': '4'}, block=2)
# J: a stuck program as the scrutinee, generalised then split
shape('J', '(a : Nat)', lambda k: 'Nat', '(let m = J1(n); match m { Z => a, S _ => Z })', NZS,
      dataCall('J', '5'), {'Z': '5', 'S': '0'}, block=2)

def gen():
    out = {1: [], 2: []}
    table = []
    for s in S:
        o = out[s['block']]
        sv, st = s['scrut']
        sid = s['id']
        o.append(f"  def {sid}g ({sv} : {st}) {s['ps']} : {s['R'](sv)} := {s['body']}".replace('  :', ' :').replace(')  ', ') '))
        inl = []
        for (suf, kv) in s['ctors']:
            if st.startswith('&'):
                pre = f'let {sv}0 = {kv}; let {sv} = &{sv}0;'
            else:
                pre = f'let {sv} = {kv};'
            ps = s['ps'] if s['ps'] else '(u : Unit)'
            o.append(f"  def {sid}i{suf} {ps} : {s['R'](kv)} := ({pre} {s['body']})")
            inl.append(f'{sid}i{suf}')
        calls = []
        if s['call'] is not None:
            for (suf, kv) in s['ctors']:
                T, term = s['call'](kv)
                T = T or s['R'](kv)
                o.append(f"  def {sid}c{suf} : {T} := {term}")
                o.append(f"  def {sid}c{suf}_v : Eq({T}, {sid}c{suf}, {s['vals'][suf]}) := refl")
                calls.append((f'{sid}i{suf}', f'{sid}c{suf}'))
        table.append((f'{sid}g', inl, calls))
    return out, table

MANUAL1 = '''  def Fg (n : Nat) (k : Nat) (a : Nat) (b : Nat) : Nat := match n { Z => match k { Z => a, S _ => b }, S _ => Z }
  def FiZ (k : Nat) (a : Nat) (b : Nat) : Nat := (let n = Z; match n { Z => match k { Z => a, S _ => b }, S _ => Z })
  def FiS (k : Nat) (a : Nat) (b : Nat) : Nat := (let n = S(Z); match n { Z => match k { Z => a, S _ => b }, S _ => Z })
  def FcZZ : Nat := Fg(Z, Z, 1, 2)
  def FcZZ_v : Eq(Nat, FcZZ, 1) := refl
  def FcZS : Nat := Fg(Z, S(Z), 1, 2)
  def FcZS_v : Eq(Nat, FcZS, 2) := refl
  def FcSZ : Nat := Fg(S(Z), Z, 1, 2)
  def FcSZ_v : Eq(Nat, FcSZ, 0) := refl
  def F2g (n : Nat) (k : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => match k { Z => x, S _ => &*y }, S _ => (let q = x; y) }
  def F2iZ (k : Nat) (x : &Nat) (y : &Nat) : &Nat := (let n = Z; match n { Z => match k { Z => x, S _ => &*y }, S _ => (let q = x; y) })
  def F2iS (k : Nat) (x : &Nat) (y : &Nat) : &Nat := (let n = S(Z); match n { Z => match k { Z => x, S _ => &*y }, S _ => (let q = x; y) })
  def F2cZZ : Nat := (let a = 1; let b = 2; let r = F2g(Z, Z, &a, &b); clone(*r))
  def F2cZZ_v : Eq(Nat, F2cZZ, 1) := refl
  def F2cZS : Nat := (let a = 1; let b = 2; let r = F2g(Z, S(Z), &a, &b); clone(*r))
  def F2cZS_v : Eq(Nat, F2cZS, 2) := refl
  def F2cSZ : Nat := (let a = 1; let b = 2; let r = F2g(S(Z), Z, &a, &b); clone(*r))
  def F2cSZ_v : Eq(Nat, F2cSZ, 2) := refl
  def Mg (u : Unit) : Nat → Nat := λ(n : Nat) : Nat => match n { Z => Z, S m => m }
  def MiZ (u : Unit) : Nat → Nat := λ(k : Nat) : Nat => (let n = Z; match n { Z => Z, S m => m })
  def MiS (u : Unit) : Nat → Nat := λ(k : Nat) : Nat => (let n = S(S(Z)); match n { Z => Z, S m => m })
  def McZ : Nat := (let f = Mg(()); f(Z))
  def McZ_v : Eq(Nat, McZ, Z) := refl
  def McS : Nat := (let f = Mg(()); f(S(S(Z))))
  def McS_v : Eq(Nat, McS, S(Z)) := refl'''
MANUAL2 = '''  def MovesAt (n : Nat) (x : Nat) : Prop := Id(Unit, (let r = &x; match n { Z => (let y = x; ()), S _ => () }), (let r = &x; let y = x; ()))
  def Eg (n : Nat) (x : Nat) : MovesAt(n, x) := match n { Z => refl, S _ => (let q = x; refl) }
  def EiZ (x : Nat) : MovesAt(Z, x) := (let n = Z; match n { Z => refl, S _ => (let q = x; refl) })
  def EiS (x : Nat) : MovesAt(S(Z), x) := (let n = S(Z); match n { Z => refl, S _ => (let q = x; refl) })
  def EcS : MovesAt(S(Z), 3) := Eg(S(Z), 3)
  def Ig (h : Or2(True, True)) (x : Nat) : True := match h { Inl(a) => (let q = x; a), Inr(b) => b }
  def IiL (x : Nat) : True := (let h = Inl[True, True](I); match h { Inl(a) => (let q = x; a), Inr(b) => b })
  def IiR (x : Nat) : True := (let h = Inr[True, True](I); match h { Inl(a) => (let q = x; a), Inr(b) => b })
  def IcL : True := Ig(Inl[True, True](I), 3)
  def IcR : True := Ig(Inr[True, True](I), 3)'''

if __name__ == '__main__':
    out, table = gen()
    print('--- SplitJoin (after `def TF`)')
    print('\n'.join(out[1]))
    print(MANUAL1)
    print('--- SplitJoinInd (after `Ch`, `NBox`, `DV`, `Or2`, `J1`)')
    print('\n'.join(out[2]))
    print(MANUAL2)
    print('--- table')
    for g, inl, calls in table:
        print(g, inl, calls)
