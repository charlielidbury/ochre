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

end Dllbc.Tests.HmProbeOpt
