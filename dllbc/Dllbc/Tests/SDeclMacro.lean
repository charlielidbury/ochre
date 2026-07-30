import Dllbc.DeclMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.S5Bound
import Dllbc.Tests.S17Spec
-- NOTE: the quicksort crown round-trip lives in `SDeclMacroCrown.lean`, the only
-- file importing `S19Partition`. Importing S19 here would force a from-scratch
-- S19 re-elaboration (the ~39-minute quicksort audit) because the worktree's
-- pre-seeded `.lake` trace is not accepted by lake — see the report. Keeping this
-- file S19-free makes the macro's round-trip suite build in seconds.

/-!
# `decl{ … }` round-trip suite — surface Decls equal the hand-built corpus

Each `example` below re-expresses a corpus `Decl` in the `decl{ }` surface and
asserts BEq-equality with the hand-built original. Equality (not
re-verification) is the correctness criterion: if the surface builds the *same*
`Decl` value, it inherits that Decl's `checkFnOk` proof for free. The corpus
Decls are IMPORTED (cache-warm); nothing here re-elaborates them, so even the
39-minute quicksort audit is never paid — we compare structure, not re-check.

## Before / after — the ugliness this macro removes

SUBJECT (illustrative): the code block below quotes the hand-built raw-constructor
"old way" purely to CONTRAST it with the surface — it is documentation of what the
macro removes, not live raw-Term machinery.

`quicksort`'s signature, hand-built (S19Partition.lean):

```
{ name := "quicksort", retType := .const "Unit",
  telescope := [("v", .borrowT listNatT listNatT), ("fuel", natT), ("lo", natT), ("cnt", natT),
    ("hbnd", LeT (addTmH (V 2 "lo") (V 3 "cnt")) (lenT dv))],
  body := …,
  back := some (sortRangeLT2 (V 1 "fuel") (V 2 "lo") (V 3 "cnt") dv) }
```

the same signature in the surface:

```
decl{ fn quicksort (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat,
                    hbnd : Le (add lo cnt) (len *v)) -> Unit
      back = sortRangeL fuel lo cnt (*v)
      = %(…body…) }
```

The `hbnd` line — the positional `V 2 "lo"` / `V 3 "cnt"` ids, the `addTmH`/`lenT`
plumbing, the `dv` for `*v` — collapses to `hbnd : Le (add lo cnt) (len *v)`, and
the `back` reads as the pure spec it is.

## Coverage map

Fully surface (header + telescope + retType + back + BODY, exact BEq):
  * `throughOk` — borrow-returning, `back = λ (r : List Nat). r`, body `{ b }`.
  * `swapSN`    — Unit-returning, `back = swapL i j *v`, Le-typed telescope over
                  `len *v`, full runtime body (the ids match `dllbcWith`'s).
  * `vecPush`   — the Σ-paired borrow type `&mut (Σ (l : Nat). VecF Nat l)`.
  * `pushList`  — the §4.1 take-and-rebuild.

Surface signature, BODY spliced via the `= %term` escape hatch (the body is laden
with pure proof terms outside the runtime `dllb` grammar — see the report):
  * `nthS`      — borrow-returning, Le-typed telescope, `back = λ (r). set i r *v`.
  * `quicksort` — THE CROWN: the `hbnd` telescope + `back = sortRangeL …`.
-/

open Dllbc
open Dllbc.Tests.S5Bound (vecFT)
open Dllbc.StdLemmas (swapL set sortRangeL)

-- `Decl` has no `deriving BEq`; the round-trip assertions need one.
deriving instance BEq for Dllbc.Decl

namespace Dllbc.Tests.SDeclMacro

/-! ## throughOk — borrow-returning with an identity backward spec (full surface) -/

def throughOk' : Decl :=
  decl{ fn through (b : &mut List Nat) -> &mut List Nat
        back = λ (r : List Nat). r
        { b } }

example : (throughOk' == Dllbc.Tests.S17Spec.throughOk) = true := by native_decide

/-! ## swapSN — Unit + back = swapL i j *v, Le telescope over `len *v` (full surface) -/

def swapS' : Decl :=
  decl{ fn swapS (v : &mut List Nat, i : Nat, j : Nat,
                  pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Unit
        back = swapL i j (*v)
        { let pr = nth2(v, i, j, pij, p2);
          match pr { Pair(ei, ej) => {
            let t = *ei;
            *ei := *ej;
            *ej := t;
            () } } } }

example : (swapS' == Dllbc.Tests.S17Spec.swapSN) = true := by native_decide

/-! ## vecPush — the Σ-paired borrow type (full surface) -/

def vecPush' : Decl :=
  decl{ fn push (e : Nat, v : &mut (Σ (l : Nat) → vecFT Nat l)) -> Unit
        { match v { Pair(l, xs) => { *xs := Pair(e, *xs); *l := S(*l); () } } } }

example : (vecPush' == Dllbc.Tests.S5Bound.vecPush) = true := by native_decide

/-! ## pushList — §4.1 take-and-rebuild (full surface) -/

def pushList' : Decl :=
  decl{ fn push (e : Nat, v : &mut List Nat) -> Unit
        { let tail = *v;
          *v := Cons(e, tail);
          () } }

example : (pushList' == Dllbc.Tests.S5Bound.pushList) = true := by native_decide

/-! ## nthS — borrow-returning, `back = λ (r). set i r *v` (signature surface,
    body spliced). The body's `Nil` branch is `botElim Unit p`, an ex-falso return
    outside the runtime `dllb` grammar, so it rides the `= %term` escape hatch. The
    Le-typed telescope over `len *v` and the backward spec are still full surface —
    and the back is the crisp check that a runtime var (`i`) under the λ is NOT
    de Bruijn-shifted (it stays `.var ⟨1,"i"⟩` while the surrendered `r` is pvar 0). -/

def nth' : Decl :=
  decl{ fn nth [v] (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat
        back = λ (r : Nat). set i r (*v)
        = %(Dllbc.Tests.S17Spec.nthS.body) }

example : (nth' == Dllbc.Tests.S17Spec.nthS) = true := by native_decide

/-! ## The `↝` snapshot-obligation borrow type (§5.1) — the one type-position form
    no corpus Decl in the round-trip set exercises, checked here against hand-built
    `Term`s.

    `&mut (s : τ ~> S)` binds the entry snapshot `s` as pure var 0 in `S` (the
    `borrowT`/`seedTelescope` convention); `&mut (τ ~> S)` is the same with `S`
    ignoring `s` (`S` weakened, so `substPure 0 σ` at seed time recovers it).
    checkFn is never run — only the produced telescope type is inspected. -/

def snapBinderDecl : Decl :=
  decl{ fn f (b : &mut (s : Nat ~> Id Nat s s)) -> Unit { () } }

-- `s` is pure var 0 inside `S = Id Nat s s`; the deref audit will owe `Id Nat σ σ`.
example : (snapBinderDecl.telescope.head!.2 ==
    Dllbc.Term.borrowT (.const "Nat") (.idT (.const "Nat") (.pvar 0) (.pvar 0))) = true := by
  native_decide

def snapIgnoreDecl : Decl :=
  decl{ fn f (b : &mut (Nat ~> Bool)) -> Unit { () } }

-- `S = Bool` ignores the snapshot; weakened, and `Bool` is closed, so the owed
-- type produced is just `Bool`.
example : (snapIgnoreDecl.telescope.head!.2 ==
    Dllbc.Term.borrowT (.const "Nat") (.const "Bool")) = true := by native_decide

end Dllbc.Tests.SDeclMacro
