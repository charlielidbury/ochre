import Ochr.Meaning.Steps.CallStep

/-!
# Regressions: the call step's clauses asked at EVERY state (lead43, 2026-11-28; docs/31 D253)

Before D253 the derivation of the step for a call of a global (`callFnGW_of_facts`, `callRanSimG_of`,
`callAcceptedFF_of`, `callInPlace_of`) assumed `∀ st, AcceptedGlobalG K st` and `∀ Δ st, FixEqG { K with Δ := Δ } st`.
A state may hold ANY code under a global's name, so the every-state forms assert a clause of every code whatsoever:
- `everyState_accepted_forces`: any two codes under one name (not the one under check) would have the same function
  type `piTG`. FALSE at every context: `fix g (n : Nat) : Nat := Z` and `fix g (n : Nat) : Unit := ()` have the
  function types `Π(n : Nat). Nat` and `Π(n : Nat). Unit`.
- `everyState_fixEq_forces`: every code would satisfy the fixpoint equation. FALSE at every context: for
  `fix f (n : Nat) : Nat by n := f(n)`, `GG` at `0` is stage 1, the body with its own binding the stage-0 closure at the
  weakened type, which returns the fill `()`; the right side binds the closure of `GG` at the true type, `err` since
  `GG` is not good, and its call fails.
Ruled (D253): the three clauses are `GlobalsOk`'s (`fixEq`, `accepted`, `retKind`), asked of the state's own globals.
-/

namespace Ochr.Meaning.Steps.Form.Master.EveryStateCE

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- A state holding one global `g` with the code `t`. -/
def stOf (g : String) (t : Term) : MState := { globals := [{ name := g, ty := .bot, fn? := some t, val := .gfn g }] }

theorem find_stOf (g : String) (t : Term) :
    (stOf g t).globals.find? (·.name == g) = some { name := g, ty := .bot, fn? := some t, val := .gfn g } := by
  simp [stOf]

/-- **REGRESSION**: the every-state form of `AcceptedGlobalG` forces any two codes under one name to have the same
function type (false: `Π(n : Nat). Nat` against `Π(n : Nat). Unit`). -/
theorem everyState_accepted_forces (K : RunCtx) (h : ∀ st, AcceptedGlobalG K st) (g : String)
    (hcur : K.cur.map (·.1) ≠ some g) (self₁ self₂ : Hint) (hs₁ hs₂ : List Hint) (ds₁ ds₂ : List Term) (c₁ c₂ : Term)
    (dec₁ dec₂ : Option Nat) (b₁ b₂ : Term) (Δ : Nat → TyS) (ρ : Assignment) (φ : Future) :
    piTG { K with Δ := Δ } ρ φ hs₁ ds₁ c₁ = piTG { K with Δ := Δ } ρ φ hs₂ ds₂ c₂ := by
  have h1 := (h (stOf g (.fix self₁ hs₁ ds₁ c₁ dec₁ b₁)) g _ self₁ hs₁ ds₁ c₁ dec₁ b₁ (find_stOf _ _) hcur rfl Δ ρ φ).2.1
  have h2 := (h (stOf g (.fix self₂ hs₂ ds₂ c₂ dec₂ b₂)) g _ self₂ hs₂ ds₂ c₂ dec₂ b₂ (find_stOf _ _) hcur rfl Δ ρ φ).2.1
  exact h1.symm.trans h2

/-- **REGRESSION**: the every-state form of `FixEqG` asserts the fixpoint equation of every code whatsoever (false at
`fix f (n : Nat) : Nat by n := f(n)`, by reading: the left side returns the fill, the right side fails). -/
theorem everyState_fixEq_forces (K : RunCtx) (h : ∀ st, FixEqG K st) (g : String) (hcur : K.cur.map (·.1) ≠ some g)
    (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) (ρ : Assignment)
    (φ : Future) (args : List Sem) (ha : DomMembers K.dm.read (psG K ρ φ ds) args) :
    GG K ρ φ hs ds c dec body args =
      fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) (piTG K ρ φ hs ds c) 0 body
        (selfG K ρ φ hs ds c dec body) args :=
  h (stOf g (.fix self hs ds c dec body)) g _ self hs ds c dec body (find_stOf _ _) hcur rfl ρ φ args ha

end Ochr.Meaning.Steps.Form.Master.EveryStateCE
