import Ochr.Meaning.Steps.FormTail
import Ochr.Meaning.Steps.ParGuards

/-!
# The column `P`: the states of the split, and the checker fact it assumes (lead16, 2026-11-21; docs/31 D131)

`def P (n : Nat) : Nat := match n { Z => Z, S m => m }`; its core body is `match #0 { Z => Z, S _ => #0.0 }`
(`ParGuards.bodyP`, asserted there to be what the surface resolves to). `checkFix` checks the body once, in
tail position (`checkTail`), from the generic state: frame 0 empty, frame 1 holding `P ↦ .gfn "P"` at
`Π(n : Nat). Nat`, marked, then `n ↦ σ0` at `Nat` (`stP`, the kernel `ColumnI.stI` has for `I`, the name and
the global `P`'s). The scrutinee holds the unknown `σ0`, so the match SPLITS (`checkTailAt`'s `.matchNat`,
`.abs σ` case): two worlds, each arm's end dropping what the join names (main's D119: `joinCont`), then the
continuation `k` at the leaf.

The states, pinned by running the checker (`Steps/SplitGuards.lean`):
- world `σ0 := Z`: the refinement puts `Z` at `n` and records `0 := Z`; the arm `Z` reads nothing; the join
  drops `n` (`n ↦ ⊥`); `k` runs on `Z` at `Nat` from `leafZ`;
- world `σ0 := S(σ1)`: a fresh unknown `σ1 : Nat` (read `.other`), the refinement puts `S(σ1)` at `n` and
  records `0 := S(σ1)`; the arm reads the place `n.0`, MOVING it (`n ↦ S(⊥)`, the value `σ1` at `Nat`); the
  join drops `n` (`n ↦ ⊥`); `k` runs on `σ1` at `Nat` from `leafS`;
- after both worlds the snapshot is back (`n ↦ σ0`, no refinement), the counters and the fresh unknown's type
  kept (`endP`).
The fresh unknown is `σ1` only when world `Z`'s continuation names no unknown and issues no label: a world's
exit keeps the counters (`Env.exitWorld`), so a continuation that makes an unknown in world `Z` moves world
`S`'s fresh unknown up (guarded). Hence the condition `KeepsAtZ` on `k`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnP

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI selfTy selfSem)

/-- `P`'s body. -/
abbrev bodyP : Term := ParGuards.bodyP

/-- `P`'s `fix` term. -/
def fixP : Term := .fix ⟨"P"⟩ [⟨"n"⟩] [.nat] .nat none bodyP

/-- `P`'s global, as `checkDef` pushes it before checking the body. -/
def gP : GDef := { name := "P", ty := piNat, fn? := some fixP, val := .gfn "P" }

/-- The function's binding of itself, marked (`recUid`). -/
def selfP : Binding := { hint := ⟨"P"⟩, ty := some piNat, val := .gfn "P", decl := .pi .other, recUid := some 0 }

/-- The parameter's binding after the join's drop. -/
def nBot : Binding := { nB with val := .bot }

/-- The kernel of the body's start state. -/
def stP : MState :=
  { env := #[{}, { binds := #[selfP, nB] }], globals := [gP], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other],
    goal := some .tNat }

/-- The frames at a leaf: `n` dropped by the join. -/
def envBot : Env := #[{}, { binds := #[selfP, nBot] }]

/-- The kernel at world `Z`'s leaf: `n` dropped by the join, the refinement `σ0 := Z` recorded. -/
def leafZ : MState :=
  { env := envBot, globals := [gP], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some .tNat,
    refs := [(0, .zero)] }

/-- The kernel at world `S`'s leaf: the fresh unknown `σ1 : Nat`, the refinement `σ0 := S(σ1)` recorded, `n`
dropped by the join. -/
def leafS : MState :=
  { env := envBot, globals := [gP], nextAbs := 2, absTy := #[.tNat, .tNat], absDecl := #[.other, .other],
    goal := some .tNat, refs := [(0, .succ (.abs 1))] }

/-- The kernel after the split: the snapshot back, the fresh unknown's type kept. -/
def endP : MState :=
  { env := #[{}, { binds := #[selfP, nB] }], globals := [gP], nextAbs := 2, absTy := #[.tNat, .tNat],
    absDecl := #[.other, .other], goal := some .tNat }

/-- The globals: `P` means its stage-0 closure (the weakened `Π(n : Nat). Unit`, as for `I`). -/
noncomputable def CP (R : DataRead) (φ : Future) : CodeMeaning :=
  { global := fun n => if n = "P" then (selfSem R φ, .plain (selfTy R)) else (.el0 Nat 0, .plain TyM.nat),
    sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- Δ at the start: `σ0` is a number. -/
def ΔP : Nat → TyS := fun σ => if σ = 0 then .plain TyM.nat else .plain TyM.err

/-- Δ in world `S`: `σ0` and the fresh `σ1` are numbers. -/
def ΔPS : Nat → TyS := fun σ => if σ < 2 then .plain TyM.nat else .plain TyM.err

/-- The run's context while `P`'s body is checked, at the unknowns' types `Δ`. -/
noncomputable def KP (dm : DataModel) (D : Decisions) (φ : Future) (Δ : Nat → TyS) : RunCtx :=
  { dm := dm, Γ := [], C := CP dm.read φ, D := D, Δ := Δ, cur := some ("P", 0) }

/-! ## The fact about the checker -/

/-- **World `Z`'s continuation keeps the counters a world's exit keeps**: run on `Z` at `Nat` from a state with
`leafZ`'s kernel, `k` names no new unknown, changes no unknown's type or reading, and issues no label. -/
def KeepsAtZ (k : Value → Value → M Unit) : Prop :=
  ∀ (st st' : MState) (bh : Nat), Kern leafZ st → Runs (k .zero .tNat) st bh () st' →
    st'.nextAbs = st.nextAbs ∧ st'.absTy = st.absTy ∧ st'.absDecl = st.absDecl ∧ st'.nextLoan = st.nextLoan

/-- **The checker's split at `P`'s body** (a fact about the checker alone; the machine lane's to prove): where
`checkTail` of `P`'s body succeeds from a state with `stP`'s kernel in the plain mode, with no handed-down
reading, with a continuation `k` that keeps the counters in world `Z`, it ran `k` at two leaves, one per world:
on `Z` at `Nat` from a state with the kernel `leafZ`, and on `σ1` at `Nat` from a state with the kernel `leafS`.
Guarded in `Steps/SplitGuards.lean` (the leaves' kernels, the order, the entry conditions). -/
def SplitPInv : Prop :=
  ∀ (fuel : Nat) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat),
    Kern stP st → Mode st → st.tailDecl = none → KeepsAtZ k →
    Runs (Ochr.checkTail fuel bodyP k) st bh () st' →
    (∃ stl bk stk, Kern leafZ stl ∧ Runs (k .zero .tNat) stl bk () stk) ∧
    (∃ stl bk stk, Kern leafS stl ∧ Runs (k (.abs 1) .tNat) stl bk () stk)

end Ochr.Meaning.Steps.Form.ColumnP
