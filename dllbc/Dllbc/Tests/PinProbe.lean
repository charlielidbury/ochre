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

/-! ## Residual (a) smoke: pins over CARVED ARRAYS — the toy pack GetMut -/

/-- OpaqueFill's `AllK7`, copied: every KEY is 7, values unread. -/
def AllK7 : Term := prog{
  λ (M : Nat). λ (A : Array M (Σ (k : Nat). Nat)).
    arrRec (Σ (k : Nat). Nat)
      (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Type)
      Unit
      (λ (K : Nat). λ (H : Σ (k : Nat). Nat). λ (T : Array K (Σ (k : Nat). Nat)).
        λ (Ih : Type).
          (elim H return (λ (Hm : Σ (k : Nat). Nat). Type) {
            Pair (K2) (V2) => Id Nat K2 7 }) × Ih)
      M A }

/-- The toy's array update: replace cell `I`'s VALUE component, keeping its key —
    index-first (list-style), destructuring the array by the cons view. -/
def AVSetT : Term := prog{
  λ (I : Nat). λ (V : Nat).
    elim I return (λ (Z0 : Nat). Π (N : Nat) → Π (A : Array N (Σ (k : Nat). Nat)) → Array N (Σ (k : Nat). Nat)) {
      Z => λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
        arrRec (Σ (k : Nat). Nat)
          (λ (M : Nat). λ (Az : Array M (Σ (k : Nat). Nat)). Array M (Σ (k : Nat). Nat))
          %(Term.ctorApp "Arr" [])
          (λ (M : Nat). λ (X : Σ (k : Nat). Nat). λ (XS : Array M (Σ (k : Nat). Nat)).
            λ (Ih : Array M (Σ (k : Nat). Nat)).
              acons M (elim X return (λ (Xz : Σ (k : Nat). Nat). Σ (k : Nat). Nat) {
                Pair (Kx) (Vx) => Pair Kx V }) XS)
          N A,
      S (I2) Rec => λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
        arrRec (Σ (k : Nat). Nat)
          (λ (M : Nat). λ (Az : Array M (Σ (k : Nat). Nat)). Array M (Σ (k : Nat). Nat))
          %(Term.ctorApp "Arr" [])
          (λ (M : Nat). λ (X : Σ (k : Nat). Nat). λ (XS : Array M (Σ (k : Nat). Nat)).
            λ (Ih : Array M (Σ (k : Nat). Nat)).
              acons M X (Rec M XS))
          N A } }

/-- The pack-level update at extent 2: value-cell `I` of the pack's array. -/
def PVSet2T : Term := prog{
  λ (I : Nat). λ (V : Nat). λ (P : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). %AllK7 2 a).
    elim P return (λ (Pz : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). %AllK7 2 a).
                     Σ0 (a : Array 2 (Σ (k : Nat). Nat)). %AllK7 2 a) {
      Pair (A) (H) => Pair ((%AVSetT) I V 2 A) H } }

def PVSet3T : Term := prog{
  λ (I : Nat). λ (V : Nat). λ (P : Σ0 (a : Array 3 (Σ (k : Nat). Nat)). %AllK7 3 a).
    elim P return (λ (Pz : Σ0 (a : Array 3 (Σ (k : Nat). Nat)). %AllK7 3 a).
                     Σ0 (a : Array 3 (Σ (k : Nat). Nat)). %AllK7 3 a) {
      Pair (A) (H) => Pair ((%AVSetT) I V 3 A) H } }

/-- Index 0 (the `gmVal2` carve), pinned. -/
def gmPin2at0 : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). %AllK7 2 a ~> (%PVSet2T) 0 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-- Index 1 (the `gmValMin` carve), pinned — the body OPENS cell 0 first, which
    is what exposes the prefix the index-first update computes past. -/
def gmPin2at1 : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). %AllK7 2 a ~> (%PVSet2T) 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e = &m (*a)[1];
        match e { Pair(kk, vv) => &m *vv } } } } } };
  () }

/-- Index 2 (the `gmValMid`/`gmValLast` carve), extent 3, cells 0 and 1 opened. -/
def gmPin3at2 : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 3 (Σ (k : Nat). Nat)). %AllK7 3 a ~> (%PVSet3T) 2 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e1 = &m (*a)[1];
        match e1 { Pair(k1, v1) => {
          let e = &m (*a)[2];
          match e { Pair(kk, vv) => &m *vv } } } } } } } };
  () }

/-- The NEGATIVE control: same pin, but the KEY escapes. The fill puts the exit
    in the key position and the pin puts it in the value position; no convert. -/
def gmPinKey2at1 : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). %AllK7 2 a ~> (%PVSet2T) 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e = &m (*a)[1];
        match e { Pair(kk, vv) => &m *kk } } } } } };
  () }

/-- …and the UNOPENED-prefix probe: gmValMin's exact body with only the pin
    added. Whether this closes is the measured boundary of the mechanism. -/
def gmPin2at1blind : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). %AllK7 2 a ~> (%PVSet2T) 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

#eval IO.println (why gmPin2at0)
#eval IO.println (why gmPin2at1)
#eval IO.println (why gmPin3at2)
#eval IO.println (why gmPinKey2at1)
#eval IO.println (why gmPin2at1blind)

/-! ## Residual (b) smoke: D9 — the cursor says WHERE it points -/

/-- Evidence alone (no pin): `Σ (r : &mut Nat). Id Nat (*r) (NthL i (old *v))`. -/
def withNthEv (rest : Term) : Term := prog{
  fn NthEv [i] (i : Nat, v : &mut List Nat, p : Le (S i) (Len *v))
      -> Σ (r : &mut Nat). Id Nat (*r) (NthL i (old *v)) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => Pair(&m *hd, Refl),
        S(k) => NthEv(k, &m *tl, p)
      }
    } };
  %rest }

#eval IO.println (why (withNthEv prog{ () }))

/-- Pin AND evidence: the derived read-only's missing half. -/
def withNthPinEv (rest : Term) : Term := prog{
  fn NthPinEv [i] (i : Nat, v : &mut (s : List Nat ~> Set i (*res) s), p : Le (S i) (Len *v))
      -> Σ (r : &mut Nat). Id Nat (*r) (NthL i (old *v)) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => Pair(&m *hd, Refl),
        S(k) => NthPinEv(k, &m *tl, p)
      }
    } };
  %rest }

#eval IO.println (why (withNthPinEv prog{ () }))

-- The derived read-only, COMPLETED: match the evidence, and the release computes
-- to the entry list exactly.
#eval IO.println (tails (withNthPinEv prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let pr = NthPinEv(1, b, ());
  match pr { Pair(r, h) => {
    match h { Refl => {
      let T = *r;
      let y = x;
      () } } } } }))

-- THE TWO-CALL ROUND-TRIP CHAIN: call, write, call again — the caller DERIVES
-- what the second borrow holds.
#eval IO.println (tails (withNthPinEv prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let pr = NthPinEv(1, b, ());
  match pr { Pair(r, h) => {
    *r := 9;
    let b2 = &m x;
    let pr2 = NthPinEv(1, b2, ());
    match pr2 { Pair(r2, h2) => {
      match h2 { Refl => {
        let T = *r2;
        let y = x;
        () } } } } } } }))

-- Negative: a body returning evidence about the WRONG position.
#eval IO.println (why (prog{
  fn BadEv (i : Nat, v : &mut List Nat, p : Le (S i) (Len *v)) -> Σ (r : &mut Nat). Id Nat (*r) (NthL 1 (old *v)) {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => Pair(&m *hd, Refl)
    } };
  () }))

-- S27Mixed movement probes (D9)
#eval IO.println (why (prog{
  fn HeadLie (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : &mut Nat). Id Nat Z (S Z)
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&m *hd, Refl) } };
  () }))
#eval IO.println (why (prog{
  fn HeadTrue (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : &mut Nat). Id Nat Z Z
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&m *hd, Refl) } };
  () }))
#eval IO.println (why (prog{
  let F = (λ(v : &mut List Nat) { match v { Nil => (), Cons(hd, tl) => Pair(&m *hd, Refl) } }
           : %(prog{ Π (v : &mut List Nat) → Σ (x : &mut Nat). Id Nat Z (S Z) }));
  () }))

end Dllbc.Tests.PinProbe
