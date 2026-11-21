import Ochr.Meaning.Steps.SplitP

/-!
# The first recursive function, column `R`: its states and the checker facts it assumes (lead17, 2026-11-21; docs/31 D134)

`def R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }`, the smallest function the checker accepts
that calls itself (without `by n` it is rejected: "[Rec] R calls itself but declares no decreasing
parameter"). Its core body is `match #0 { Z => Z, S _ => #1(#0.0) }`: `#1` is the function's binding of itself
(after the parameter), the call's argument the place `n.0` (`bodyR`; the surface resolves to exactly this,
asserted in `Steps/RecGuards.lean`). `checkFix` checks it once, in tail position, from the generic state: frame 0
empty, frame 1 holding `R ↦ .gfn "R"` at `Π(n : Nat). Nat`, MARKED (`recUid = some 0`), then `n ↦ σ0` at `Nat`
(`stR`, `P`'s `stP` with `R`'s name and global, whose `fix` term carries `by n`: `dec = some 0`), with one [Rec]
context (`fn = .gfn R`, `uid = 0`, the entry `σ0`, the decreasing candidate `0`).

What the checker does (pinned in `Steps/RecGuards.lean`): the match SPLITS as `P`'s does. World `Z`: `n ↦ Z`, the
record `0 := Z`, the arm `Z`, the join drops `n`, `k` runs on `Z : Nat` at `leafZR`. World `S`: the fresh
`σ1 : Nat`, `n ↦ S(σ1)`, the record `0 := S(σ1)`; the arm is the CALL `R(n.0)`: the head is read in place (the
function's binding of itself, not consumed); the argument's read moves `n.0` (`n ↦ S(⊥)`), giving `σ1 : Nat`;
[Call-type] gives `Nat`; [Rec] (`recCheck`, typed runs only, before the callee runs) finds the context by the
head binding's mark and keeps the candidate `0` because the argument `σ1` is a strict subterm of the entry
`σ0` as the records expand it (`S(σ1)`), and otherwise rejects; then the callee's body runs UNTYPED on `σ1`, its
match on the unknown is stuck, and the call CLOSES OFF: the value is the sealed program `⌈R(σ1)⌉`
(`.sealed (.call (.val (.gfn "R")) [.val (.abs 1)] true)`), at `Nat`, with no new unknown and no label. The join
drops `n`; `k` runs on `⌈R(σ1)⌉ : Nat` at `leafSR`. After both worlds the snapshot is back (`endR`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnR

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB)

/-- `R`'s body: `match #0 { Z => Z, S _ => #1(#0.0) }`. -/
def bodyR : Term := .matchNat (.var 0) .zero (.call (.place (.var 1)) [.place (.proj 0 (.var 0))] false)

/-- The arm of world `S`: the recursive call `R(n.0)`. -/
def callR : Term := .call (.place (.var 1)) [.place (.proj 0 (.var 0))] false

/-- `R`'s `fix` term: decreasing on its parameter. -/
def fixR : Term := .fix ⟨"R"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyR

/-- `R` as a core definition. -/
def defR : Def := { name := "R", hs := [⟨"n"⟩], doms := [.nat], cod := .nat, dec := some 0, body := bodyR }

/-- `R`'s global, as `checkDef` pushes it before checking the body. -/
def gR : GDef := { name := "R", ty := piNat, fn? := some fixR, val := .gfn "R" }

/-- The function's binding of itself, marked (`recUid`). -/
def selfR : Binding := { hint := ⟨"R"⟩, ty := some piNat, val := .gfn "R", decl := .pi .other, recUid := some 0 }

/-- The parameter's binding after the join's drop. -/
def nBot : Binding := { nB with val := .bot }

/-- The kernel of the body's start state. -/
def stR : MState :=
  { env := #[{}, { binds := #[selfR, nB] }], globals := [gR], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other],
    goal := some .tNat }

/-- The [Rec] context `checkFix` pushes for `R`: the entry `σ0`, the candidate `0`. -/
def rcR : RecCtx := { fn := .gfn "R", entries := #[some 0], cands := [0], uid := 0 }

/-- The body's full start state, in `checkFix`'s mode. -/
def stRm : MState := { stR with typing := true, recStack := [rcR], nextRecUid := 1 }

/-- The frames at a leaf: `n` dropped by the join. -/
def envBot : Env := #[{}, { binds := #[selfR, nBot] }]

/-- The kernel at world `Z`'s leaf. -/
def leafZR : MState :=
  { env := envBot, globals := [gR], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some .tNat,
    refs := [(0, .zero)] }

/-- The kernel at world `S`'s arm start: the fresh `σ1 : Nat`, `n ↦ S(σ1)`, the record `0 := S(σ1)`. -/
def armSR : MState :=
  { env := #[{}, { binds := #[selfR, { nB with val := .succ (.abs 1) }] }], globals := [gR], nextAbs := 2,
    absTy := #[.tNat, .tNat], absDecl := #[.other, .other], goal := some .tNat, refs := [(0, .succ (.abs 1))] }

/-- The kernel after the call, before the join's drop: `n.0` moved. -/
def armSR' : MState :=
  { armSR with env := #[{}, { binds := #[selfR, { nB with val := .succ .bot }] }] }

/-- The kernel at world `S`'s leaf: `n` dropped by the join. -/
def leafSR : MState :=
  { env := envBot, globals := [gR], nextAbs := 2, absTy := #[.tNat, .tNat], absDecl := #[.other, .other],
    goal := some .tNat, refs := [(0, .succ (.abs 1))] }

/-- The kernel after the split: the snapshot back, the fresh unknown's type kept. -/
def endR : MState :=
  { env := #[{}, { binds := #[selfR, nB] }], globals := [gR], nextAbs := 2, absTy := #[.tNat, .tNat],
    absDecl := #[.other, .other], goal := some .tNat }

/-- The sealed program the recursive call closes off to: `⌈R(σ1)⌉`. -/
def sealR : Term := .call (.val (.gfn "R")) [.val (.abs 1)] true

/-- The value of the recursive call. -/
def vR : Value := .sealed sealR

/-! ## The facts about the checker -/

/-- **World `Z`'s continuation keeps the counters a world's exit keeps** (`ColumnP.KeepsAtZ` at `R`'s leaf): run on
`Z` at `Nat` from a state with `leafZR`'s kernel, `k` names no new unknown, changes no unknown's type or reading, and
issues no label. -/
def KeepsAtZR (k : Value → Value → M Unit) : Prop :=
  ∀ (st st' : MState) (bh : Nat), Kern leafZR st → Runs (k .zero .tNat) st bh () st' →
    st'.nextAbs = st.nextAbs ∧ st'.absTy = st.absTy ∧ st'.absDecl = st.absDecl ∧ st'.nextLoan = st.nextLoan

/-- **The checker's split at `R`'s body** (a fact about the checker alone; the machine lane's to prove): where
`checkTail` of `R`'s body succeeds from a state with `stR`'s kernel in the plain mode, with no handed-down reading,
with a continuation `k` that keeps the counters in world `Z`, it ran `k` at two leaves, one per world: on `Z` at `Nat`
from a state with the kernel `leafZR`, and on the sealed call `⌈R(σ1)⌉` at `Nat` from a state with the kernel `leafSR`.
`ColumnP.SplitPInv` with world `S`'s arm the recursive call, which closes off (the callee's body is stuck at its match
on `σ1`). Nothing is asked of the [Rec] context: where the run succeeds, the leaves are these whether or not the
recursion check ran (guarded in `Steps/RecGuards.lean`: the leaves, the order, the entry conditions, a run with no
[Rec] context). -/
def SplitRInv : Prop :=
  ∀ (fuel : Nat) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat),
    Kern stR st → Mode st → st.tailDecl = none → KeepsAtZR k →
    Runs (Ochr.checkTail fuel bodyR k) st bh () st' →
    (∃ stl bk stk, Kern leafZR stl ∧ Runs (k .zero .tNat) stl bk () stk) ∧
    (∃ stl bk stk, Kern leafSR stl ∧ Runs (k vR .tNat) stl bk () stk)

/-- **The checker's acceptance of `R`, inverted down to its body's check** (a fact about the checker, assumed; the
machine lane's to prove): where `checkDef defR` succeeds from the empty state, `checkFix` ran `checkTail` of the body
(with its return check as the continuation) from a state with `stR`'s kernel, in the plain mode, with no handed-down
reading, and that continuation keeps the counters in world `Z` (`ColumnP.FixRunP` for `R`; guarded by `checkDef
defR`'s trace in `Steps/RecGuards.lean`). -/
def FixRunR : Prop :=
  ∀ (fuel : Nat) (st₁ : MState), Runs (checkDef defR) {} fuel () st₁ →
    ∃ (n : Nat) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat),
      Kern stR st ∧ Mode st ∧ st.tailDecl = none ∧ KeepsAtZR k ∧ Runs (Ochr.checkTail n bodyR k) st bh () st'

end Ochr.Meaning.Steps.Form.ColumnR
