import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# HmProbeOpt — a viability probe for the hashmap flagship

Three independent capability questions, answered by construction:

  * **O1** — an `Option` encoding as `Σ (b : Bool) → OptP b T`, since the kernel's
    `ctorSig` basis is fixed (Unit/Bool/Nat/List/Σ/Array/Id) and has no `Option`.
  * **O2** — building an `Array n T` full of a constant at a SYMBOLIC `n`, which
    `new_with_capacity` needs and which the `Arr` literal cannot do (its field
    telescope exists only at a concrete length).
  * **O3** — type parameters: where `Type`-genericity is and is not available.

Probe file, not a suite: failures are recorded verbatim rather than fixed.
-/

open Dllbc

namespace Dllbc.Tests.HmProbeOpt

/-- Type-check a closed term against a closed type in the pure seed (as §23/§24/§25). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- The same, but keeping the error message — a probe wants the verbatim text. -/
def chkLMsg (tm ty : Term) : String :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => s!"ok {r}"
  | .error e _ => s!"error {e}"

def pv (t : Term) : Term := Pure.nf 4000 t

/-! ## O1 — the `Σ (Bool)` Option

    `OptP : Bool → Type → Type` is an ordinary type-VALUED comptime fn, in the
    `Std.SortedFn`/`BoundFn` style: a `boolRec` whose motive is `Type`. -/

def OptP : Term := prog{
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }

/-- `Opt T = Σ (b : Bool) → OptP b T` — the tag is RUNTIME data (lowercase `b`),
    which is what makes `match o { Pair(b, p) => match b { … } }` a runtime match. -/
def OptT (t : Term) : Term := prog{ Σ (b : Bool) → OptP b %t }

def optNat : Term := OptT prog{ Nat }

-- Does the payload type compute?
#eval (pv prog{ OptP True Nat }).pretty
#eval (pv prog{ OptP False Nat }).pretty
#eval optNat.pretty

/-! ### O1(a) — constructing both shapes -/

example : chkL prog{ Pair(True, 5) } optNat = true := by native_decide
example : chkL prog{ Pair(False, unit) } optNat = true := by native_decide

-- …and the encoding is NOT vacuous: the payload must match the tag.
example : chkL prog{ Pair(True, unit) } optNat = false := by native_decide
example : chkL prog{ Pair(False, 5) } optNat = false := by native_decide

/-! ### O1(b) — a `fn` RETURNING an `Opt Nat`, both branches -/

-- The constant `Some`.
def mkSomeP : Term := prog{
  fn MkSome (n : Nat) -> (Σ (b : Bool) → OptP b Nat) { Pair(True, n) };
  () }
example : progOk mkSomeP = true := by native_decide

-- The constant `None`.
def mkNoneP : Term := prog{
  fn MkNone () -> (Σ (b : Bool) → OptP b Nat) { Pair(False, unit) };
  () }
example : progOk mkNoneP = true := by native_decide

-- BOTH branches from one body: `pred`, which is `None` at zero.
def predOptP : Term := prog{
  fn PredOpt (n : Nat) -> (Σ (b : Bool) → OptP b Nat) {
    match n { Z => Pair(False, unit), S(m) => Pair(True, m) } };
  () }
example : progOk predOptP = true := by native_decide

/-- Check a program and keep the message. -/
def chkProg (t : Term) : String :=
  match checkProgram t prog{ Unit } with | .ok _ => "ACCEPTED" | .error e => "REJECTED: " ++ e

-- The wrong payload in one branch is REJECTED.
#eval chkProg prog{
    fn PredOpt (n : Nat) -> (Σ (b : Bool) → OptP b Nat) {
      match n { Z => Pair(False, unit), S(m) => Pair(True, unit) } };
    () }

/-! ### O1(c) — MATCHING an `Opt Nat`: does the payload's type refine?

    `p`'s type at branch entry is `OptP σb Nat` — a STUCK `boolRec`. The `True`
    arm must see it become `Nat` and the `False` arm `Unit`. -/

-- (c1) The match itself, with no payload use at all.
#eval chkProg prog{
  fn IsSome (o : &mut (Σ (b : Bool) → OptP b Nat)) -> Bool {
    match o { Pair(bb, p) => match bb { True => True, False => False } } };
  () }

-- (c2) THE REFINEMENT TEST, take-and-refill: `let x = *p` gives `x : OptP True Nat`,
-- and `S(x)` needs that to BE `Nat`. The `False` arm refills with `unit`, which
-- needs `OptP False Nat` to be `Unit`.
#eval chkProg prog{
  fn BumpOpt (o : &mut (Σ (b : Bool) → OptP b Nat)) -> Unit {
    match o { Pair(bb, p) => match bb {
      True => { let x = *p; *p := S(x); () },
      False => { let u = *p; *p := unit; () } } } };
  () }

-- (c3) …and the refinement is not vacuous: refilling the `True` arm with `unit`
-- must FAIL.
#eval chkProg prog{
  fn BumpOpt (o : &mut (Σ (b : Bool) → OptP b Nat)) -> Unit {
    match o { Pair(bb, p) => match bb {
      True => { let x = *p; *p := unit; () },
      False => { let u = *p; *p := unit; () } } } };
  () }

-- (c4) WRITING the tag — the `vecPush` shape, and the operation an insert does:
-- set the tag to `True` and the payload to a `Nat`, both in place.
#eval chkProg prog{
  fn SetSome (n : Nat, o : &mut (Σ (b : Bool) → OptP b Nat)) -> Unit {
    match o { Pair(bb, p) => { *bb := True; *p := n; () } } };
  () }

-- (c5) THE MONEY TEST for this encoding: write the payload and FORGET the tag.
#eval chkProg prog{
  fn SetSome (n : Nat, o : &mut (Σ (b : Bool) → OptP b Nat)) -> Unit {
    match o { Pair(bb, p) => { *p := n; () } } };
  () }

-- (c6) The reverse: set the tag to `False` and the payload to `unit`.
#eval chkProg prog{
  fn SetNone (o : &mut (Σ (b : Bool) → OptP b Nat)) -> Unit {
    match o { Pair(bb, p) => { *bb := False; *p := unit; () } } };
  () }

-- (c7) Can the payload be RETURNED? (`unwrap_or` — the natural reader.)
#eval chkProg prog{
  fn UnwrapOr (d : Nat, o : &mut (Σ (b : Bool) → OptP b Nat)) -> Nat {
    match o { Pair(bb, p) => match bb { True => *p, False => d } } };
  () }

-- (c8) …and with an OWNED `Opt` parameter (`*p` peeled a σ, so drop the peel).
#eval chkProg prog{
  fn UnwrapOr (d : Nat, o : (Σ (b : Bool) → OptP b Nat)) -> Nat {
    match o { Pair(bb, p) => match bb { True => p, False => d } } };
  () }

-- (c9) The `get`-shaped reader: peel the payload, PUT IT BACK, and return a fresh
-- `Opt` built from it. (Whether a `Nat` may be used after being written back is
-- the question this one really asks.)
#eval chkProg prog{
  fn CloneOpt (o : &mut (Σ (b : Bool) → OptP b Nat)) -> (Σ (b : Bool) → OptP b Nat) {
    match o { Pair(bb, p) => match bb {
      True => { let x = *p; *p := x; Pair(True, x) },
      False => { let u = *p; *p := unit; Pair(False, unit) } } } };
  () }

/-! ### O1(d) — `Id` at the `Opt` type -/

example : chkL prog{ Refl }
  prog{ Id (Σ (b : Bool) → OptP b Nat) Pair(True, 5) Pair(True, 5) } = true := by native_decide
example : chkL prog{ Refl }
  prog{ Id (Σ (b : Bool) → OptP b Nat) Pair(True, 5) Pair(True, 6) } = false := by native_decide
example : chkL prog{ Refl }
  prog{ Id (Σ (b : Bool) → OptP b Nat) Pair(False, unit) Pair(False, unit) } = true := by
  native_decide
-- A `Some` is not a `None`.
example : chkL prog{ Refl }
  prog{ Id (Σ (b : Bool) → OptP b Nat) Pair(True, 5) Pair(False, unit) } = false := by
  native_decide

/-! ## O2 — building an `Array n T` at a SYMBOLIC `n`

    `ctorSig "Arr"` has a field telescope only at a CONCRETE length ("one cannot
    write an array literal of unknown length"), so the literal cannot do this. The
    recursive builder can — if its `acons` spine converts against the rigid
    `Array (S m) T`. -/

/-- `MkSlots : Π n. Array n (List Nat)` — `n` empty buckets. -/
def MkSlotsFn : Term := prog{
  λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm (List Nat)) {
    Z => Arr(),
    S (M) Rec => acons M Nil Rec } }
def MkSlotsTy : Term := prog{ Π (N : Nat) → Array N (List Nat) }

-- (a) Does the comptime definition CHECK at its Π type?
#eval chkLMsg MkSlotsFn MkSlotsTy

-- (b) Does it COMPUTE to a flat `Arr(…)` at a concrete length?
#eval (pv prog{ MkSlotsFn 0 }).pretty
#eval (pv prog{ MkSlotsFn 3 }).pretty

-- (c) …and does the computed value check against its own concrete array type?
#eval chkLMsg prog{ MkSlotsFn 3 } prog{ Array 3 (List Nat) }

-- (d) η-expanded: the spine STUCK under a binder, which is the shape a symbolic
--     length gives.
def MkSlotsAtN : Term := prog{ λ (N : Nat). MkSlotsFn N }
#eval chkLMsg MkSlotsAtN MkSlotsTy

end Dllbc.Tests.HmProbeOpt
