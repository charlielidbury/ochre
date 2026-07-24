import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
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

def listNatT : Term := .app (.const "List") (.const "Nat")

/-! ## `through` with a declared identity spec — the M8 arc closed -/

-- `through (b) = b`, `back (r) = r`: the release IS the surrendered value.
def throughOk : Decl :=
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { b },
    back := some (.lam listNatT (.pvar 0)) }
example : checkFnOk throughOk = true := by native_decide

-- The caller now recovers the WRITTEN value, not a fresh existential: after
-- `*r := Cons(9, Nil)` and demanding the owner, `y = Cons(9, Nil)`. Contrast the
-- spec-less `through` in S7Group, whose `y` is a fresh σ (§6.2 precision loss).
def caller : Decl :=
  { name := "caller", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
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
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { b },
    back := some (.lam listNatT (.ctorApp "Cons" [.ctorApp "S" [.ctorApp "Z" []], .ctorApp "Nil" []])) }
example : checkFnErr throughLie "does not match the body" = true := by native_decide

/-! ## Spec-less stays opaque (no regression) -/

-- Same body, no `back`: the caller's recovery is a fresh existential (a `sym`),
-- exactly as in M9 — the spec-carrying end is opt-in.
def throughOpaque : Decl :=
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { b } }
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

def natT : Term := .const "Nat"
def mutNat : Term := .borrowT natT natT
def tS (t : Term) : Term := .ctorApp "S" [t]
def LeT (a b : Term) : Term := Std.LeT a b
def lenT (l : Term) : Term := Std.lenT l
def setT (k v l : Term) : Term := .app (.app (.app StdLemmas.set k) v) l
def bE (x : Term) : Term := .app (.app (.const "botElim") (.const "Unit")) x
def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def rb (x : Var) : Term := .borrow (.deref (.var x))
def pairMut : Term := .sigmaT mutNat mutNat

def nthS : Decl :=
  { name := "nth", retType := mutNat,
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("p", LeT (tS (V 1 "i")) (lenT (.deref (V 0 "v"))))],
    body := .matchE ⟨0, "v"⟩ [ .mk "Nil" [] (bE (V 2 "p")),
      .mk "Cons" [⟨3, "hd"⟩, ⟨4, "tl"⟩] (.matchE ⟨1, "i"⟩ [ .mk "Z" [] (rb ⟨3, "hd"⟩),
        .mk "S" [⟨5, "k"⟩] (.call "nth" [rb ⟨4, "tl"⟩, V 5 "k", V 2 "p"]) ]) ],
    back := some (.lam natT (setT (V 1 "i") (.pvar 0) (.deref (V 0 "v")))) }

def nth2S : Decl :=
  { name := "nth2", retType := pairMut,
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("j", natT),
      ("pij", LeT (tS (V 1 "i")) (V 2 "j")), ("p2", LeT (tS (V 2 "j")) (lenT (.deref (V 0 "v"))))],
    body := .matchE ⟨0, "v"⟩ [ .mk "Nil" [] (bE (V 4 "p2")),
      .mk "Cons" [⟨5, "hd"⟩, ⟨6, "tl"⟩] (.matchE ⟨1, "i"⟩ [
        .mk "Z" [] (.matchE ⟨2, "j"⟩ [ .mk "Z" [] (bE (V 3 "pij")),
          .mk "S" [⟨7, "jjv"⟩] (.ctorApp "Pair" [rb ⟨5, "hd"⟩, .call "nth" [rb ⟨6, "tl"⟩, V 7 "jjv", V 4 "p2"]]) ]),
        .mk "S" [⟨8, "k"⟩] (.matchE ⟨2, "j"⟩ [ .mk "Z" [] (bE (V 3 "pij")),
          .mk "S" [⟨9, "jj2"⟩] (.call "nth2" [rb ⟨6, "tl"⟩, V 8 "k", V 9 "jj2", V 3 "pij", V 4 "p2"]) ]) ]) ],
    back := some (.lam natT (.lam natT (setT (V 1 "i") (.pvar 1) (setT (V 2 "j") (.pvar 0) (.deref (V 0 "v")))))) }

def swapSN : Decl :=
  { name := "swapS", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("j", natT),
      ("pij", LeT (tS (V 1 "i")) (V 2 "j")), ("p2", LeT (tS (V 2 "j")) (lenT (.deref (V 0 "v"))))],
    body := .letIn ⟨5, "pr"⟩ (.call "nth2" [V 0 "v", V 1 "i", V 2 "j", V 3 "pij", V 4 "p2"])
      (.matchE ⟨5, "pr"⟩ [ .mk "Pair" [⟨6, "ei"⟩, ⟨7, "ej"⟩]
        (.letIn ⟨8, "t"⟩ (.deref (V 6 "ei"))
          (.assign (.deref (V 6 "ei")) (.deref (V 7 "ej"))
            (.assign (.deref (V 7 "ej")) (V 8 "t") .unit))) ]),
    back := some (.app (.app (.app StdLemmas.swapL (V 1 "i")) (V 2 "j")) (.deref (V 0 "v"))) }

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
def spcCaller : Decl := { name := "spc", retType := .const "Unit", telescope := [], body := spcBody }
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
