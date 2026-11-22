#!/usr/bin/env python3
"""D125's hunt, and the generator of the asserted table `CaseSplits.SplitCallable`.

Every form the check of a body (`checkTailAt`) accepts at the end of a data-valued function: a
split in both forms (`split f in u`, and the braces form), bare, under a `let`, under a `;`, in the
arms of a match on a number, on a value of an inductive type, on a known constructor, on a proof
(by type), on a value of a type with one constructor (a destructuring `let`), and on a stuck call
(generalised); a match on the call with no split (`Plain`); and a call of a function ending in a
split (`Call`). Each shape `S<shape>` is called at a known argument (`K`, with its values by `refl`,
`KV` and `KU`), at an unknown argument inside another function, where the body runs (`U`, the split
call computes) or the call closes off (`S`, re-run at closed instances `SV`, `SU`), and through a
closure: a lambda ending in the form, called (`C`, `CV`), a lambda calling it passed to a
higher-order function (`H`, `HU`), and the function itself passed (`G`, for one parameter).

    python3 gen.py hunt old   # the hunt as run on main (D61's braces spelling), a whole file
    python3 gen.py hunt new   # the same with D126's spelling, a whole file
    python3 gen.py block      # the rows of the asserted block (D126's spelling)

On main every generic definition was accepted and every call of a split rejected ("split: only in
tail position"); `Plain` was callable everywhere.
"""
import sys

ARMS = "{ T => 1, F => (), }"
IN = f"split IsZ in match IsZ(n) {ARMS}"


def rows(mode):
    BR = f"split IsZ {ARMS}" if mode == "old" else f"split IsZ(n) {ARMS}"
    # (name, parameters after n, the extra arguments of a call, body)
    shapes = [
        ("In", "", "", IN),
        ("Br", "", "", BR),
        ("Bare", "", "", "split IsZ in Gm(n)"),
        ("LetIn", "", "", f"(let a = 0; {IN})"),
        ("LetBr", "", "", f"(let a = 0; {BR})"),
        ("SeqIn", "", "", f"((); {IN})"),
        ("SeqBr", "", "", f"((); {BR})"),
        ("NatIn", " (k : Nat)", ", Z", f"match k {{ Z => {IN}, S(j) => {IN}, }}"),
        ("NatBr", " (k : Nat)", ", Z", f"match k {{ Z => {BR}, S(j) => {BR}, }}"),
        ("IndIn", " (c : B)", ", T", f"match c {{ T => {IN}, F => {IN}, }}"),
        ("IndBr", " (c : B)", ", T", f"match c {{ T => {BR}, F => {BR}, }}"),
        ("KnownIn", "", "", f"(let c = F; match c {{ T => {IN}, F => {IN}, }})"),
        ("KnownBr", "", "", f"(let c = F; match c {{ T => {BR}, F => {BR}, }})"),
        ("ProofIn", " (h : And(⊤, ⊤))", ", ⟨refl, refl⟩", f"match h {{ Intro(a, b) => {IN}, }}"),
        ("ProofBr", " (h : And(⊤, ⊤))", ", ⟨refl, refl⟩", f"match h {{ Intro(a, b) => {BR}, }}"),
        ("OneIn", " (p : Pair(Nat, Nat))", ", (0, 0)", f"(let (x, y) = p; {IN})"),
        ("OneBr", " (p : Pair(Nat, Nat))", ", (0, 0)", f"(let (x, y) = p; {BR})"),
        ("SealIn", " (k : Nat)", ", Z", f"match IsZ(k) {{ T => {IN}, F => {IN}, }}"),
        ("SealBr", " (k : Nat)", ", Z", f"match IsZ(k) {{ T => {BR}, F => {BR}, }}"),
        ("Plain", "", "", f"match IsZ(n) {ARMS}"),
        ("Call", "", "", "SIn(n)"),
    ]
    out = [
        "inductive B := T | F",
        "def IsZ (n : Nat) : B := match n { Z => T, S(m) => F, }",
        "def V (b : B) : Type := match b { T => Nat, F => Unit, }",
        f"def Gm (n : Nat) : V(IsZ(n)) := match IsZ(n) {ARMS}",
        "def AppZ (f : Π(n : Nat). V(IsZ(n))) : Nat := f(Z)",
        "def AppS (f : Π(n : Nat). V(IsZ(n))) (m : Nat) : Unit := f(S(m))",
    ]
    for (nm, ps, xs, body) in shapes:
        f = "S" + nm
        lam = f"(λ(n : Nat){ps} : V(IsZ(n)) => ({body}))"
        out += [
            f"def {f} (n : Nat){ps} : V(IsZ(n)) := {body}",
            f"def {f}K : Nat := {f}(Z{xs})",
            f"def {f}KV : Eq(Nat, {f}(Z{xs}), 1) := refl",
            f"def {f}KU : Eq(Unit, {f}(S(Z){xs}), ()) := refl",
            f"def {f}U (m : Nat) : Unit := {f}(S(m){xs})",
            f"def {f}S (m : Nat) : V(IsZ(m)) := {f}(m{xs})",
            f"def {f}SV : Eq(Nat, {f}S(Z), 1) := refl",
            f"def {f}SU : Eq(Unit, {f}S(S(Z)), ()) := refl",
            f"def {f}C : Nat := (let c = {lam}; c(Z{xs}))",
            f"def {f}CV : Eq(Nat, (let c = {lam}; c(Z{xs})), 1) := refl",
            f"def {f}H : Eq(Nat, AppZ(λ(n : Nat) : V(IsZ(n)) => {f}(n{xs})), 1) := refl",
            f"def {f}HU (m : Nat) : Eq(Unit, AppS(λ(n : Nat) : V(IsZ(n)) => {f}(n{xs}), m), ()) := refl",
        ]
        if ps == "":
            out.append(f"def {f}G : Eq(Nat, AppZ({f}), 1) := refl")
    return out


if __name__ == "__main__":
    if sys.argv[1] == "hunt":
        print("import Ochr.Examples.Registry\nopen Ochr Ochr.Test\n")
        print("ochr Hunt125 uses Nats {")
        print("\n".join("  " + r for r in rows(sys.argv[2])))
        print("}")
    else:
        print("\n".join("  " + r for r in rows("new")))
