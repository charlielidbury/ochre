import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff

/-!
# §17 test suite — declared backward specs (spec group-ends)

The sound reincarnation of the `constrained` wire removed in M8: unsound then
because INFERRED from a signature (`through` and `advance` share one), sound now
because DECLARED on the function and CHECKED against its body. A borrow-returning
function may carry `Decl.back` — a pure function from the issued borrows'
surrendered values to the captured borrow's release value. Two consequences:

* **Callee check**: at return, the captured borrow's payload with the issued
  markers replaced by fresh hole variables — the suspension tree with holes IS
  the backward function the body implements — must convert with the declared
  spec applied to those holes. A spec that lies about the body is rejected.
* **Caller side**: on group end, each captured loan releases the COMPUTED value
  (the spec applied to the surrendered values) instead of a fresh existential.
  Precision recovered soundly — the M8 arc completed.

A spec-less call behaves exactly as before (opaque, a fresh existential); nothing
regresses (see the M9 `through`/`choose` in S7Group, still opaque).
-/

open Dllbc

namespace Dllbc.Tests.S17Spec

/-! ## `through` with a declared identity spec — the M8 arc closed -/

-- `through (b) = b`, `back (r) = r`: the release IS the surrendered value.
def throughOk : Decl :=
  decl{ fn through (b : &mut List Nat) -> &mut List Nat
        back = λ (r : List Nat). r
        { b } }
example : checkFnOk throughOk = true := by native_decide

-- The caller now recovers the WRITTEN value, not a fresh existential: after
-- `*r := Cons(9, Nil)` and demanding the owner, `y = Cons(9, Nil)`. Contrast the
-- spec-less `through` in S7Group, whose `y` is a fresh σ (§6.2 precision loss).
def caller : Decl :=
  decl{ fn caller () -> Unit {
    let x = Cons(1, Nil); let b = &mut x;
    let r = through(b);
    *r := Cons(9, Nil);
    let y = x;
    () } }
def vlist9 : Val := .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "Z" []]]]]]]]]], .ctor "Nil" []]
example : (match runFn [throughOk, caller] caller with
  | [.ok env] => env.lookup "y" == some vlist9
  | _ => false) = true := by native_decide

/-! ## A lying spec is rejected -/

-- `through (b) = b` but `back (r) = Cons(1, Nil)` — claims a constant release the
-- body does not implement. The callee check converts the body's tree (`#0`, the
-- hole) against the spec's `Cons(1, Nil)` and fails.
def throughLie : Decl :=
  decl{ fn through (b : &mut List Nat) -> &mut List Nat
        back = λ (r : List Nat). Cons(1, Nil)
        { b } }
example : checkFnErr throughLie "does not match the body" = true := by native_decide

/-! ## Spec-less stays opaque (no regression) -/

-- Same body, no `back`: the caller's recovery is a fresh existential (a `sym`),
-- exactly as in M9 — the spec-carrying end is opt-in.
def throughOpaque : Decl :=
  decl{ fn through (b : &mut List Nat) -> &mut List Nat { b } }
example : (match runFn [throughOpaque, { caller with name := "c2" }] { caller with name := "c2" } with
  | [.ok env] => match env.lookup "y" with | some (.sym _) => true | _ => false
  | _ => false) = true := by native_decide

/-! ## The real spec-carrying swap: nth2's backward spec composes through swapS

    Backward specs compose along the call chain — LLBC's synthesized backward
    functions, here as CHECKED declarations. `nth`'s spec is `set i r s`; `nth2`'s
    is `set i r₁ (set j r₂ s)` (composing `nth`'s); `swapS`'s is `swapL i j s`
    (composing `nth2`'s, with no surrendered args since it returns Unit). The
    payoff: a caller of `swapS` recovers the EXACT swapped list in CHECKING mode
    — precision restored soundly, and at ZERO unpack lines (the value arrives
    directly, no Σ to open — beating M16's ~2). -/

open Dllbc.StdLemmas (set swapL)

def nthS : Decl :=
  decl{ fn nth [v] (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat
        back = λ (r : Nat). set i r (*v)
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match i {
              Z => &mut *hd,
              S(k) => nth(&mut *tl, k, p)
            }
        } } }

def nth2S : Decl :=
  decl{ fn nth2 [v] (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Σ (x : &mut Nat) → &mut Nat
        back = λ (r1 : Nat). λ (r2 : Nat). set i r1 (set j r2 (*v))
        { match v {
            Nil => botElim Unit p2,
            Cons(hd, tl) => match i {
              Z => match j {
                Z => botElim Unit pij,
                S(jjv) => Pair(&mut *hd, nth(&mut *tl, jjv, p2))
              },
              S(k) => match j {
                Z => botElim Unit pij,
                S(jj2) => nth2(&mut *tl, k, jj2, pij, p2)
              }
            }
        } } }

def swapSN : Decl :=
  decl{ fn swapS (v : &mut List Nat, i : Nat, j : Nat,
                  pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Unit
        back = swapL i j (*v)
        { let pr = nth2(v, i, j, pij, p2);
          match pr { Pair(ei, ej) => {
            let t = *ei;
            *ei := *ej;
            *ej := t;
            () } } } }

example : checkFnOk nthS = true := by native_decide
example : checkFnOk nth2S ([nthS, nth2S]) = true := by native_decide
example : checkFnOk swapSN ([nthS, nth2S, swapSN]) = true := by native_decide

-- The caller recovers [3,2,1] PRECISELY in checking mode (no unpack lines).
def spcBody : Term := dllbcWith [] {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &mut x;
  swapS(b, 0, 2, (), ());
  let y = x;
  () }
def spcCaller : Decl := decl{ fn spc () -> Unit = %spcBody }
def vlist321 : Val := .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "Z" []]]],
  .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "Z" []]], .ctor "Cons" [.ctor "S" [.ctor "Z" []], .ctor "Nil" []]]]
example : (match runFn [nthS, nth2S, swapSN, spcCaller] spcCaller with
  | [.ok env] => env.lookup "y" == some vlist321
  | _ => false) = true := by native_decide
-- Checking-mode precise recovery AGREES with the executing-mode run (differential).
example : (match Dllbc.Tests.S9Diff.runExec [nthS, nth2S, swapSN] spcBody with
  | .ok env => env.lookup "y" == some vlist321
  | .error _ => false) = true := by native_decide

end Dllbc.Tests.S17Spec
