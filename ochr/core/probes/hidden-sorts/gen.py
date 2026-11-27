#!/usr/bin/env python3
"""D131: a binding a typed run makes agrees with its stored type and its value. Generates the
asserted block `HiddenSorts` (lean/Ochr/Examples/Universes.lean) and its guard.

A sort hidden from the declared-type readers (`PropF(x)` with `PropF (n : Nat) : Type₁ := Prop`, an
ascription `(Prop : Type₁)`, a constant `PC : Type₁ := Prop`, a call under `;` or `let`, a match
whose arms disagree), and `Prop` written as itself as the control, by each binder of a typed run:
a `let` of a `J` whose motive's codomain is the hidden sort (a proof read as data), the same
captured by a closure, a `let` annotated with the hidden sort and a `let` of a call returning at it
(a type read as data), a parameter and a λ's parameter at it, and a `J` whose type is STUCK on the
hidden sort while its value is already `⋆` (read in a match, captured, read twice). Each a generic
function `G…(k)` reading the binding in one arm of a match on `k` and again after the join (D131's
`V1`); with the sort hidden each is rejected (D131), with it written each is accepted, with its
instance `C…` and a generic caller `H…`. The forms whose generic function typing rejects already
(the match form under `J`, the annotation and the call) are left out.

usage: python3 gen.py > block.txt"""

hidden = [
    ("Call", "PropF({x})"),
    ("Asc", "(Prop : Type₁)"),
    ("Const", "PC"),
    ("Seq", "((); PropF({x}))"),
    ("Let", "(let z = 0; PropF({x}))"),
    ("Match", "match {x} {{ Z => Prop, S(m) => PropF(m) }}"),
    ("Plain", "Prop"),
]

def v1(y):
    return f"match k {{ Z => (let z = {y}; ()), S(j) => () }}; let w = {y}; ()"

rows, helpers, guards = [], [], []
for (hn, h) in hidden:
    hx, hk, hnn = h.format(x="x"), h.format(x="k"), h.format(x="n")
    j = f"J(Nat, Z, Z, (λ(x : Nat) : {hx} => ⊤), refl, refl)"
    jS = f"J(Nat, Z, k, (λ(x : Nat) : {hx} => match x {{ Z => ⊤, S(m) => ⊤ }}), e, refl)"
    fam = [
        ("J", "(k : Nat)", f"(let y = {j}; {v1('y')})", "Z", "y is a proof"),
        ("Cap", "(k : Nat)", f"(let y = {j}; let g = (λ(u : Unit) : Unit => (let a = y; u)); match k {{ Z => g(()), S(j) => () }}; let w = y; ())", "Z", "y is a proof"),
        ("Ann", "(k : Nat)", f"(let y : {hk} = ⊤; {v1('y')})", "Z", "y is a type"),
        ("Ret", "(k : Nat)", f"(let y = GH{hn}(k); {v1('y')})", "Z", "y is a type"),
        ("Par", f"(k : Nat) (P : {hk})", f"({v1('P')})", "Z, ⊤", "z is a type" if hn == "Match" else "P is a type"),
        ("Lam", "(k : Nat)", f"(let f = (λ(P : {hk}) : Unit => ({v1('P')})); f(⊤))", "Z", "z is a type" if hn == "Match" else "P is a type"),
        ("SJ", "(k : Nat) (e : Eq(Nat, Z, k))", f"(let y = {jS}; {v1('y')})", "Z, refl", "y holds a proof"),
        ("SCap", "(k : Nat) (e : Eq(Nat, Z, k))", f"(let y = {jS}; let g = (λ(u : Unit) : Unit => (let a = y; u)); match k {{ Z => g(()), S(j) => () }}; let w = y; ())", "Z, refl", "y holds a proof"),
        ("SMove", "(k : Nat) (e : Eq(Nat, Z, k))", f"(let y = {jS}; let a = y; let b = y; ())", "Z, refl", "y holds a proof"),
    ]
    if hn != "Match":
        helpers.append(f"  def GH{hn} (n : Nat) : {hnn} := ⊤")
    for (f, ps, body, inst, msg) in fam:
        if hn == "Match" and f in ("J", "Cap", "Ann", "Ret"):
            continue
        n = f + hn
        args = ", ".join(p.split(" : ")[0].lstrip("(") for p in ps.split(") ("))
        if hn == "Plain":
            rows.append(f"  def G{n} {ps} : Unit := {body}")
            rows.append(f"  def C{n} : Unit := G{n}({inst})")
            rows.append(f"  def H{n} {ps} : Unit := G{n}({args})")
        else:
            rows.append(f"  reject def G{n} {ps} : Unit := {body}")
            guards.append((f"G{n}", f"[D131] {msg}"))

print("ochr HiddenSorts {")
print("  def PropF (n : Nat) : Type₁ := Prop")
print("  def PC : Type₁ := Prop")
print("\n".join(helpers))
print("  -- the proof lane's example (`FitProofCE.V1`), and its control with the codomain written `Prop`")
print("  reject def V1 (k : Nat) : Unit := (let y = J(Nat, Z, Z, λ(x : Nat) : PropF(x) => ⊤, refl, refl); match k { Z => (let z = y; ()), S(j) => (), }; let w = y; ())")
print("  def V3 (k : Nat) : Unit := (let y = J(Nat, Z, Z, λ(x : Nat) : Prop => ⊤, refl, refl); match k { Z => (let z = y; ()), S(j) => (), }; let w = y; ())")
print("  def V4 : Unit := V3(Z)")
print("\n".join(rows))
print("}")
print()
guards.insert(0, ("V1", "[D131] y is a proof"))
print("#guard (run \"HiddenSorts\" HiddenSorts).rejectedWith [")
print(",\n".join(f"  (\"{n}\", \"{m}\")" for (n, m) in guards) + "]")
