#!/usr/bin/env python3
"""D129 hunt: a match nested in an arm that has already moved part of a place of a type with two
constructors (`x : B2`, `x.n` moved), then the other part (`m`) read. Generic against instance.
usage: gen129.py [block]"""
import sys
moves = {
    "Let": "let y = n;",
    "Call": "let y = UseL(n);",
    "Fld": "let y = LBox(n);",
    "Seq": "let y = (Z; n);",
}
inners = {
    "NK": ("let w = match Z { Z => Z, S(j) => Z, };", False),
    "NU": ("let w = match k { Z => Z, S(j) => Z, };", False),
    "IK": ("let w = match LN { LN => Z, LC(h) => Z, };", False),
    "IU": ("let w = match l { LN => Z, LC(h) => Z, };", False),
    "No": ("let w = Z;", False),
    "NT": ("match k { Z => m, S(j) => m, }", True),
    "IT": ("match l { LN => m, LC(h) => m, }", True),
}
rows = []
for mk, mv in moves.items():
    for ik, (inner, tail) in inners.items():
        body = f"({mv} {inner})" if tail else f"({mv} {inner} m)"
        nm = f"R{mk}{ik}"
        arm = f"match x {{ A0(n, m) => {body}, A1 => LN, }}"
        rows.append(f"def {nm}I (k : Nat) (l : L) : L := (let x = A0(LN, LC(3)); {arm})")
        rows.append(f"def {nm}IV : Eq(L, {nm}I(Z, LN), LC(3)) := refl")
        rows.append(f"def {nm}G (x : B2) (k : Nat) (l : L) : L := {arm}")
        rows.append(f"def {nm}GZ : Eq(L, {nm}G(A0(LN, LC(3)), Z, LN), LC(3)) := refl")
        rows.append(f"def {nm}GS : Eq(L, {nm}G(A0(LN, LC(4)), S(Z), LC(1)), LC(4)) := refl")
# the reverse question: an arm of the inner match moves the rest (`m`) of the partly moved `x`
rev = {
    # the inner arm that moves m is taken (k = Z) or not (S): after it m is moved either way (the join)
    "Mv": ("let w = match k { Z => (let z = m; Z), S(j) => Z, };", "LN"),
    # and a read of m after it: rejected on every path
    "MvR": ("let w = match k { Z => (let z = m; Z), S(j) => Z, };", "m"),
    # the inner arm that moves m is never taken (known scrutinee): the join still drops m
    "MvK": ("let w = match Z { Z => Z, S(j) => (let z = m; Z), };", "m"),
    # the inner arm refills the moved part: the join drops it where another arm leaves it moved
    "Rf": ("let w = match k { Z => (n := LN; Z), S(j) => Z, };", "m"),
    # the same at a known scrutinee: the arm runs, refills `n`, and the join drops it again (another
    # arm leaves it moved); the other part is read after it, and the refilled one is not readable
    "RfK": ("let w = match Z { Z => (n := LN; Z), S(j) => Z, };", "m"),
    "RfKn": ("let w = match Z { Z => (n := LN; Z), S(j) => Z, };", "n"),
}
for rk, (inner, end) in rev.items():
    nm = f"V{rk}"
    arm = f"match x {{ A0(n, m) => (let y = n; {inner} {end}), A1 => LN, }}"
    rows.append(f"def {nm}I (k : Nat) : L := (let x = A0(LN, LC(3)); {arm})")
    rows.append(f"def {nm}IV : Eq(L, {nm}I(Z), { {'LN': 'LN', 'm': 'LC(3)', 'n': 'LN'}[end] }) := refl")
    rows.append(f"def {nm}G (x : B2) (k : Nat) : L := {arm}")
    rows.append(f"def {nm}GZ : Eq(L, {nm}G(A0(LN, LC(3)), Z), { {'LN': 'LN', 'm': 'LC(3)', 'n': 'LN'}[end] }) := refl")
    rows.append(f"def {nm}GS : Eq(L, {nm}G(A0(LN, LC(3)), S(Z)), { {'LN': 'LN', 'm': 'LC(3)', 'n': 'LN'}[end] }) := refl")
# a deeper part: x.n.h, through n : L2 (two constructors)
rows.append("def DI (k : Nat) : L := (let x = A2(LC2(LC(5)), LC(3)); match x { A2(n, m) => match n { LN2 => m, LC2(h) => (let y = h; let w = match k { Z => Z, S(j) => Z, }; m), }, A3 => LN, })")
rows.append("def DIV : Eq(L, DI(Z), LC(3)) := refl")
rows.append("def DG (x : B3) (k : Nat) : L := match x { A2(n, m) => match n { LN2 => m, LC2(h) => (let y = h; let w = match k { Z => Z, S(j) => Z, }; m), }, A3 => LN, }")
rows.append("def DGZ : Eq(L, DG(A2(LC2(LC(5)), LC(3)), Z), LC(3)) := refl")
head = [
    "inductive L := LN | LC(h : Nat)",
    "inductive B2 := A0(n : L, m : L) | A1",
    "inductive LB := LBox(l : L)",
    "inductive L2 := LN2 | LC2(h : L)",
    "inductive B3 := A2(n : L2, m : L) | A3",
    "def UseL (l : L) : Nat := 0",
    "-- the lead's four",
    "def ok1 : L := (let x = A0(LN, LC(3)); match x { A0(n, m) => (let y = n; m), A1 => LN, })",
    "def f3 : L := (let x = A0(LN, LC(3)); match x { A0(n, m) => (let y = n; let w = match Z { Z => Z, S(j) => Z, }; m), A1 => LN, })",
    "def f (x : B2) (k : Nat) : L := match x { A0(n, m) => (let y = n; let w = match k { Z => Z, S(j) => Z, }; m), A1 => LN, }",
    "def callF : L := f(A0(LN, LC(3)), Z)",
    "def callFV : Eq(L, callF, LC(3)) := refl",
]
out = head + rows
# rejected after D129, on every path (the reverse question), with their messages
rejects = {
    "VMv": "[Read] x was partly moved out (D53)",
    "VMvR": "[Read] x was partly moved out (D53)",
    "VMvK": "no such place x.m: its path does not exist in ⊥",
    "VRf": "[Borrow] x.n was moved out (borrowing ⊥)",
    "VRfKn": "[Read] x.n was moved out or its borrow ended (reading ⊥)",
}
def rejectMsg(name):
    for k, m in rejects.items():
        if name in (k + "I", k + "G"): return m
        if name in (k + "IV",): return f"unknown constant {k}I"
        if name in (k + "GZ", k + "GS"): return f"unknown constant {k}G"
    return None
if len(sys.argv) > 1 and sys.argv[1] == "block":
    lines = []
    guard = []
    for r in out:
        if r.startswith("def "):
            name = r.split()[1]
            m = rejectMsg(name)
            if m is not None:
                lines.append("reject " + r)
                guard.append(f'  ("{name}", "{m}")')
                continue
        lines.append(r)
    print("\n".join("  " + r for r in lines))
    print("#GUARD")
    print(",\n".join(guard))
else:
    print("import Ochr.Examples.Registry\nopen Ochr Ochr.Test\n\nochr Hunt129 uses Nats {")
    print("\n".join("  " + r for r in out))
    print("}")
print(f"-- rows {sum(1 for r in out if r.startswith('def ') or r.startswith('inductive '))}", file=sys.stderr)
