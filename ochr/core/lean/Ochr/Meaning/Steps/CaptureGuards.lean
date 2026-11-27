import Ochr.Meaning.Steps.DataBoxGuards

/-!
# A function value with a capture, pinned (lead21, 2026-11-22; compiled, not kernel-checked; docs/31 D149)

Every `#guard` runs the checker. `Const (n : Nat) : Π(m : Nat). Nat := λ(m : Nat) : Nat => n` is REJECTED ([D53]: a
closure's body moves a captured value out, and a closure may run again), so the smallest accepted program is the
body `clone(n)`. Pinned: the core body (`fix _ (m : Nat) : Nat := clone(#2)`: in the closure's frame
`[κ, _, m]`, `#2` is the capture); the lambda's body checked at its own generic call (`κ ↦ σ0` a capture,
`_ ↦` the closure itself MARKED with the [Rec] uid `1`, `m ↦ σ2`); the closure value `.clo [σ0] t [(.other, Nat)]`
(the capture BY MOVE: `n ↦ ⊥` after, its reading `.other` at `Nat` in `rd`), at the type `Π(m : Nat). Nat` with the
same capture; the caller `let f = Const(1); f(Z)` is `1`.
-/

open Ochr.Test

ochr CaptureProbe {
  reject def Const0 (n : Nat) : (Π(m : Nat). Nat) := (λ(m : Nat) : Nat => n)
  def Const (n : Nat) : (Π(m : Nat). Nat) := (λ(m : Nat) : Nat => clone(n))
  def UseK : Nat := let f = Const(1); f(Z)
}

namespace Ochr.Meaning.Steps.Form.Capture.Guards

open Ochr Ochr.Meaning
open Ochr.Meaning.Steps.Form.ParGuards (bodyOf)
open Ochr.Meaning.Steps.Form.ColumnBox.Guards (lines)

-- `Const0` rejected, `Const` and `UseK` accepted (the block's expectations)
#guard (Ochr.Test.runWith none "CaptureProbe" CaptureProbe {} (located := false)).allAsExpected

/-- The lambda, as the surface resolves it. -/
def lam : Term := .fix ⟨"_"⟩ [⟨"m"⟩] [.nat] .nat none (.prim "clone" [.place (.var 2)])
#guard (bodyOf CaptureProbe "Const").exact lam

/-- The states the checker records at the located terms' exits in `Const`'s check, with their values. -/
def exits : List (Value × MState) :=
  let r := Ochr.Test.runWith none "CaptureProbe" CaptureProbe { recordStates := true } (located := true)
  match r.rows.find? (·.name == "Const") with
  | some row => row.trace.toList.filterMap fun
      | .state _ true (some (v, _)) st => some (v, st)
      | _ => none
  | none => []

-- the lambda's body at its generic call: the capture `κ ↦ σ0` (a capture), the closure's own binding marked with the
-- fresh mark `1` its check took (main's D136 as amended: a local function is not recursive, but marked), `m ↦ σ2`;
-- its value `σ0`
#guard exits.any fun (v, st) => v.exact (.abs 0) && st.env.size == 2 && st.env[1]!.binds.size == 3 &&
  st.env[1]!.binds[0]!.cap && (st.env[1]!.binds[0]!.val).exact (.abs 0) &&
  st.env[1]!.binds[1]!.recUid == some 1 && st.env[1]!.binds[1]!.hint.name == "_" &&
  (st.env[1]!.binds[2]!.val).exact (.abs 2)
-- the closure value: one capture, `σ0`, BY MOVE (`n ↦ ⊥` after), read `.other` at `Nat`
#guard exits.any fun (v, st) => (match v with
  | .clo [c] t [(d, T)] => c.exact (.abs 0) && t.exact lam && d == .other && T.exact .tNat
  | _ => false) && st.env.size == 2 && st.env[1]!.binds.size == 2 && (st.env[1]!.binds[1]!.val).exact .bot
-- the caller
#guard (lines CaptureProbe "UseK").contains "[Return] UseK is defined as it: 1 : Nat, with 0 place(s) held by borrow"

end Ochr.Meaning.Steps.Form.Capture.Guards
