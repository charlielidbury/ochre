#!/usr/bin/env python3
"""D128: a parameter of an inductive declaration whose declared type reads as a sort is written as a
sort. Generates the asserted block `WrittenSorts` (lean/Ochr/Examples/Fording.lean) and its guard.

Every spelling of a parameter type that `typeDecl` reads as a sort without its being one (a `let`, a
`;`, a `let` naming the sort, a match whose arms all return it, on a parameter, on a literal or
through a `let`), at each sort (`Prop`, `Type`, `Type₁`), twice: with a field `x : B` that reads the
parameter as a type (`…F`) and with none (`…N`). Each is rejected (D128) and sits beside its twin
written as the sort (`…W`), which keeps its verdict. Then the spellings that read as a value, not a
sort (an ascription, a call, a constant, a type function, an earlier parameter, a match whose arms
disagree): a value parameter, accepted with no field and rejected by D55 as a field's type, as before.

usage: python3 gen.py > block.txt   (the block, then the guard; pasted into Fording.lean)"""

SORTS = [("p", "Prop", "Type₁"), ("t", "Type", "Type₁"), ("u", "Type₁", "Type₂")]

# reads as the sort: (shape, leading parameters, written type of B)
def sorty(S):
    return [
        ("Let", "(A : Type)", f"(let z = A; {S})"),
        ("Let0", "", f"(let z = 0; {S})"),
        ("LetN", "(A : Type)", f"(let z = A; let w = z; {S})"),
        ("Seq", "", f"((); {S})"),
        ("SeqA", "(A : Type)", f"(A; {S})"),
        ("LetS", "", f"(let T = {S}; T)"),
        ("LetSA", "(A : Type)", f"(let T = {S}; let z = A; T)"),
        ("MatchL", "", f"match 0 {{ Z => {S}, S(m) => {S} }}"),
        ("MatchN", "(n : Nat)", f"match n {{ Z => {S}, S(m) => {S} }}"),
        ("MatchW", "(w : Word)", f"match w {{ Zero => {S}, Succ(v) => {S} }}"),
        ("LetM", "(n : Nat)", f"(let z = n; match z {{ Z => {S}, S(m) => {S} }})"),
        ("MatchLet", "(n : Nat)", f"match n {{ Z => (let w = n; {S}), S(m) => {S} }}"),
        ("LetMatchS", "(n : Nat)", f"(let T = {S}; match n {{ Z => T, S(m) => T }})"),
    ]

# reads as a value: (shape, leading parameters, written type of B, helper declarations)
def valuey(S, S1, s):
    return [
        ("Asc", "", f"({S} : {S1})", []),
        ("Call", "", f"WSF{s}(())", [f"def WSF{s} (u : Unit) : {S1} := {S}"]),
        ("Const", "", f"WSC{s}", [f"def WSC{s} : {S1} := {S}"]),
        ("IdFn", "", f"WSI{s}({S})", [f"def WSI{s} (X : {S1}) : {S1} := X"]),
        ("Param", f"(U : {S1})", "U", []),
    ]

D128 = "[D128] the parameter B of {n} is declared at "
D55 = "[D55] B is written where a type is expected, but its declared type is not a sort"
LEVEL = "field x of Mk{n}: its type must be in Prop or Type"

rows, guards = [], []

def ind(rej, n, pre, B, field):
    ps = (pre + " " if pre else "") + f"(B : {B})"
    fs = f"Mk{n}(x : B)" if field else f"Mk{n}"
    rows.append(f"  {'reject ' if rej else ''}inductive {n} {ps} := {fs}")

# the proof lane's counterexample, verbatim, and a nested use of it
rows.append("  -- the proof lane's counterexample (`FactsCE.dTL`), and the same parameter nested in a list")
ind(True, "TL", "(A : Type)", "(let z = A; Type)", True); guards.append(("TL", D128.format(n="TL")))
ind(False, "TLW", "(A : Type)", "Type", True)
rows.append("  reject inductive TLL (A : Type) (B : (let z = A; Type)) := MkTLL(x : List(B))")
guards.append(("TLL", D128.format(n="TLL")))
rows.append("  inductive TLLW (A : Type) (B : Type) := MkTLLW(x : List(B))")

for (s, S, S1) in SORTS:
    rows.append(f"  -- reads as {S}: rejected, beside the same declaration with B written as {S}")
    for (shape, pre, B) in sorty(S):
        for use in ("F", "N"):
            n = f"{shape}{s}{use}"
            ind(True, n, pre, B, use == "F"); guards.append((n, D128.format(n=n)))
            w = n + "W"
            # a field of type B : Type₁ is above Type (unchanged by D128)
            rej = (S == "Type₁" and use == "F")
            ind(rej, w, pre, S, use == "F")
            if rej: guards.append((w, LEVEL.format(n=w)))
    rows.append(f"  -- reads as a value of {S1}, not as a sort: a value parameter, as before (no field may have it as its type)")
    for (shape, pre, B, helpers) in valuey(S, S1, s):
        for h in helpers:
            rows.append("  " + h)
        for use in ("F", "N"):
            n = f"{shape}{s}{use}"
            ind(use == "F", n, pre, B, use == "F")
            if use == "F": guards.append((n, D55))

rows.append("  -- arms that disagree (Type, Prop) read as neither: a value parameter")
ind(True, "MatchMixF", "(n : Nat)", "match n { Z => Type, S(m) => Prop }", True); guards.append(("MatchMixF", D55))
ind(False, "MatchMixN", "(n : Nat)", "match n { Z => Type, S(m) => Prop }", False)

print("ochr WrittenSorts uses Lists {")
print("\n".join(rows))
print("}")
print()
print("#guard (run \"WrittenSorts\" WrittenSorts).rejectedWith [")
print(",\n".join(f"  (\"{n}\", \"{m}\")" for (n, m) in guards) + "]")
