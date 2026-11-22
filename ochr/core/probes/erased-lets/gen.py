#!/usr/bin/env python3
"""D132: an untyped `let` of an erased call (returning a type, a proposition, a function type or a
proof), by every way the binding's type is later read. Generates the asserted block `ErasedLets`
(lean/Ochr/Examples/Functions.lean). Each row: a generic function `G…(n)` (checked typed), a closed
call of it by `refl` (`C…`: its body runs untyped at n = 1) and a generic caller `H…(n) := G…(n)`
(its body runs untyped at an unknown n, where `TS(n)` closes off). Every row is accepted.
`TS`'s annotated uses are left out: `let z : TS(n) = 3` is rejected at the generic `n` already.

usage: python3 gen.py > block.txt"""

helpers = r"""
  def TF (n : Nat) : Type := Nat
  def PF (n : Nat) : Prop := Eq(Nat, n, n)
  def FT (n : Nat) : Type := Π(x : Nat). Nat
  def TS (n : Nat) : Type := match n { Z => Nat, S(m) => Nat }
  def lem (n : Nat) : Eq(Nat, n, n) := refl
  inductive IsZ (n : Nat) : Prop := MkZ(h : Eq(Nat, n, n))
  def lemZ (n : Nat) : IsZ(n) := MkZ[n](refl)
  def useTy (A : Type) : Nat := 3
  def useProp (P : Prop) : Nat := 3
  def useP (n : Nat) (h : Eq(Nat, n, n)) : Nat := 3
  def useZ (n : Nat) (h : IsZ(n)) : Nat := 3
  inductive WP (n : Nat) := MkWP(p : Eq(Nat, n, n))
"""

# right-hand sides: (name, kind, term); kind: ty (a type of data), prop (a proposition), fn (a
# function type), pf (a proof of Eq), pz (a proof of IsZ)
rhs = [
    ("TF", "ty", "TF(n)"),
    ("TS", "ty", "TS(n)"),
    ("Clo", "ty", "(let F = (λ(m : Nat) : Type => Nat); F(n))"),
    ("CloL", "ty", None),            # the closure bound first, the let's right-hand side a call of it
    ("PF", "prop", "PF(n)"),
    ("FT", "fn", "FT(n)"),
    ("Lem", "pf", "lem(n)"),
    ("LemZ", "pz", "lemZ(n)"),
    # controls: not a bare call, so not deferred today
    ("SeqTF", "ty", "((); TF(n))"),
    ("AscTF", "ty", "(TF(n) : Type)"),
    ("SeqLem", "pf", "((); lem(n))"),
]

uses = {
    "ty": [("Ann", "let z : X = 3; 3"), ("Arg", "useTy(X)"), ("Clone", "let c = clone(X); 3"),
           ("Copy", "let y = X; 3"), ("Pi", "let f : (Π(a : X). X) = (λ(a : X) : X => a); 3"),
           ("Ret", "(let z : X = 3; z)"), ("Cap", "let g = (λ(m : Nat) : Nat => (let q : X = m; q)); g(3)")],
    "prop": [("Ann", "let z : X = refl; 3"), ("Arg", "useProp(X)"), ("Clone", "let c = clone(X); 3"),
             ("Copy", "let y = X; 3")],
    "fn": [("Ann", "let z : X = (λ(x : Nat) : Nat => x); 3"), ("Arg", "useTy(X)"), ("App", "let f : X = (λ(x : Nat) : Nat => x); f(3)"),
           ("Copy", "let y = X; 3")],
    "pf": [("Ann", "let k : Eq(Nat, n, n) = X; 3"), ("Arg", "useP(n, X)"), ("Clone", "let c = clone(X); 3"),
           ("FieldP", "let w = MkWP[n](X); 3"),
           ("J", "J(Nat, n, n, (λ(x : Nat) : Type => Nat), X, 3)"), ("Copy", "let y = X; 3"),
           ("Asc", "let k = (X : Eq(Nat, n, n)); 3"), ("Cap", "let g = (λ(m : Nat) : Nat => (let q = X; m)); g(3)")],
    "pz": [("Match", "match X { MkZ(e) => 3 }"), ("Cap", "let g = (λ(m : Nat) : Nat => (let q = X; m)); g(3)"), ("Arg", "useZ(n, X)"), ("Clone", "let c = clone(X); 3"),
           ("Copy", "let y = X; 3")],
}

rows = []
for (rn, kind, t) in rhs:
    for (un, use) in uses[kind]:
        if rn == "TS" and un in ("Ann", "Ret", "Cap"):
            continue
        nm = f"{rn}{un}"
        if rn == "CloL":
            body = f"(let F = (λ(m : Nat) : Type => Nat); let X = F(n); {use})"
        else:
            body = f"(let X = {t}; {use})"
        rows.append(f"  def G{nm} (n : Nat) : Nat := {body}")
        rows.append(f"  def C{nm} : Eq(Nat, G{nm}(1), 3) := refl")
        rows.append(f"  def H{nm} (n : Nat) : Nat := G{nm}(n)")

print("ochr ErasedLets uses Nats {" + helpers + "\n".join(rows) + "\n}")
