import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# Stage-0 viability probe for the pin (12-design §10)

THE GATE, per the design doc: "verify that the `Nth` `S(k)` branch's conversion in
§2.3 actually goes through definitionally on `SetNth`'s real corpus definition …
before stage 1, not after stage 4." The corpus's list update is `StdLemmas.Set`
(the doc's `SetNth`), which recurses on the index FIRST.

The claim, at the audit's own level of symbolism: in the `S(k)` branch every
participant is a σ (the match refined `i := S σk`, `v`'s payload to
`Cons σh σtl`), so the conversion the discharge runs is

    Set (S σk) σr (Cons σh σtl)   ≡?   Cons σh (Set σk σr σtl)

with all four atoms NEUTRAL. If that is definitional (the recursor ι-steps on the
`S` head and the `Cons` head without needing σk), the pin needs no bridging
equations and stage 5 is viable. σ's are `pvar`s with reserved names; plain
`pvar`s convert by the same rule, so the probe uses ordinary names.

Also probed here, because stage 5's design leans on each:
  * the `Z` leg;
  * the read-only law's derivation leg `Set i (NthL i s) s ≡ s` — expected
    DEFINITIONAL at concrete `i`/`s` and STUCK at symbolic ones (the test file's
    "states it both ways");
  * inertness of the `@res` marker (the kernel form `*res` will elaborate to):
    it must ride through `Pure.nf` as a neutral spine and through `readC`
    without a reflection error.

NOT imported by `Dllbc.lean` — a scratch module, built directly.
-/

open Dllbc

namespace Dllbc.Tests.PinProbe

open Dllbc.StdLemmas

def pk : Term := .pvar "k"
def pr : Term := .pvar "r"
def ph : Term := .pvar "h"
def pt : Term := .pvar "t"
def ps : Term := .pvar "s"
def pi' : Term := .pvar "i"

/-! ## THE GATE: the `S(k)` leg, all atoms neutral -/

def lhsS : Term := prog{ Set (S %pk) %pr (Cons %ph %pt) }
def rhsS : Term := prog{ Cons %ph (Set %pk %pr %pt) }
example : Pure.convert 2000 lhsS rhsS = true := by native_decide

/-! ## The `Z` leg -/

def lhsZ : Term := prog{ Set Z %pr (Cons %ph %pt) }
def rhsZ : Term := prog{ Cons %pr %pt }
example : Pure.convert 2000 lhsZ rhsZ = true := by native_decide

/-! ## The read-only derivation leg, both ways -/

-- Concrete index and list: definitional.
def roConc1 : Term := prog{ Set 1 (NthL 1 (Cons 1 (Cons 2 (Cons 3 Nil)))) (Cons 1 (Cons 2 (Cons 3 Nil))) }
def roConc2 : Term := prog{ Cons 1 (Cons 2 (Cons 3 Nil)) }
example : Pure.convert 2000 roConc1 roConc2 = true := by native_decide

-- Symbolic index and list: stuck (an induction, not a conversion).
def roSym1 : Term := prog{ Set %pi' (NthL %pi' %ps) %ps }
example : Pure.convert 2000 roSym1 ps = false := by native_decide

/-! ## The `@res` marker is inert -/

def resM : Term := .app (.const "@res") (.ctorApp "Z" [])

def lhsRes : Term := prog{ Set (S Z) %resM (Cons %ph %pt) }
def rhsRes : Term := prog{ Cons %ph (Set Z %resM %pt) }
example : Pure.convert 2000 lhsRes rhsRes = true := by native_decide

-- …and distinct positions do NOT convert (the marker is a name, not a wildcard).
def resM1 : Term := .app (.const "@res") (.ctorApp "S" [.ctorApp "Z" []])
example : Pure.convert 2000 resM resM1 = false := by native_decide

-- readC passes the marker through (no reflection error), so a pin can be stored
-- and re-read wherever owed types already are.
def rcOk (tm : Term) : Bool :=
  match (readC 8000 tm).run (seedPure [] []) with
  | .ok _ _ => true
  | .error _ _ => false

example : rcOk lhsRes = true := by native_decide

/-! ## Classification probes (D1's one-slot rule) — A MEASURED FINDING

    The obvious classifier — `hasTypeT rhs Type` — is WRONG on this kernel, and
    the probe measured it rather than assuming it: `hasTypeT` has universe arms
    for `.pi`/`.sigmaT`/`.idT`/`.type` and NONE for a bare type constant or a
    neutral type application, so `Nat : Type` and `List Nat : Type` both throw
    ("cannot type value/neutral") and a chk-wrapper reads `false`. Under that
    classifier the corpus's `&mut (s : Bool ~> Nat)` would silently become a PIN.

    So D1's kind classification must be a dedicated type-recognizer
    (`isOwedTypeT`, stage 5): whnf, then type-former head / type-constant head /
    `List`/`Array` spine / σ whose `sctx` type is `Type` ⇒ owed-type claim;
    anything else ⇒ pin. The two assertions below pin the finding that forced it. -/

def chkT (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

-- Σ-types DO inhabit the universe by `hasTypeT`…
example : chkT prog{ Σ (l : List Nat). Id Nat (Len l) (Len (Cons 1 Nil)) } prog{ Type }
  = true := by native_decide
-- …but a bare type constant and a neutral type application do NOT (the finding).
example : chkT prog{ Nat } prog{ Type } = false := by native_decide
example : chkT prog{ List Nat } prog{ Type } = false := by native_decide
-- Pin-shaped terms are not types under any reading.
example : chkT prog{ Set (S Z) 9 (Cons 1 (Cons 2 Nil)) } prog{ Type } = false := by native_decide
example : chkT prog{ Cons 1 Nil } prog{ Type } = false := by native_decide

/-! ## Stage-5 smoke: the mechanism end to end (kept as the probe's record) -/

def why (t : Term) : String :=
  match checkProgram t prog{ Unit } with
  | .ok _ => "ACCEPTED"
  | .error e => e

def tails (t : Term) : String :=
  match tailEnvs t with
  | [.ok env] => String.intercalate ", " (env.map (fun kv => s!"{kv.1} ↦ {kv.2.pretty}"))
  | [.error e] => s!"ERR {e}"
  | rs => s!"{rs.length} paths"

def throughPinP : Term := prog{
  fn ThroughP (b : &mut (s : List Nat ~> *res)) -> &mut List Nat { b }; () }

def throughPinCallerP : Term := prog{
  fn ThroughP (b : &mut (s : List Nat ~> *res)) -> &mut List Nat { b };
  let x = Cons(1, Nil); let b = &m x;
  let r = ThroughP(b);
  *r := Cons(9, Nil);
  let y = x;
  () }

#eval IO.println (why throughPinP)
#eval IO.println (tails throughPinCallerP)

def withNthPinP (rest : Term) : Term := prog{
  fn NthPin [i] (i : Nat, v : &mut (s : List Nat ~> Set i (*res) s), p : Le (S i) (Len *v)) -> &mut Nat {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &m *hd,
        S(k) => NthPin(k, &m *tl, p)
      }
    } };
  %rest }

#eval IO.println (why (withNthPinP prog{ () }))
#eval IO.println (tails (withNthPinP prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = NthPin(1, b, ());
  *r := 9;
  let y = x;
  () }))

def withGetROP (rest : Term) : Term := prog{
  fn GetRO [i] (i : Nat, v : &mut (s : List Nat ~> s), p : Le (S i) (Len *v)) -> &mut (t : Nat ~> t) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &m *hd,
        S(k) => GetRO(k, &m *tl, p)
      }
    } };
  %rest }

#eval IO.println (why (withGetROP prog{ () }))
#eval IO.println (tails (withGetROP prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = GetRO(1, b, ());
  let T = *r;
  let y = x;
  () }))
#eval IO.println (why (withGetROP prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = GetRO(1, b, ());
  *r := 9;
  let y = x;
  () }))

end Dllbc.Tests.PinProbe
