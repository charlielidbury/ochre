import Ochr.Meaning.Steps.FormTail
import Ochr.Meaning.Steps.ParGuards

/-!
# The first data type that is not `Nat`: the column `Not`, its states and the checker fact it assumes (lead21, 2026-11-22; docs/31 D147)

```
inductive B := T | F
def Not(b : B) : B := match b { T => F, F => T }
```
The core body is `match #0 { T => F, F => T }` (`bodyNot`; asserted in `Steps/DataGuards.lean` to be what the
surface resolves to). `checkFix` checks it once, in tail position (`checkTail`), from the generic state: frame 0
empty, frame 1 holding `Not ↦ .gfn "Not"` at `Π(b : B). B` read `.pi (.ind B [])`, marked, then `b ↦ σ0` at `B`
read `.ind B []`; the unknown `σ0 : B` itself read `.other` (its frozen reading, `absDecl`); the declaration `B`
in the state's declarations (`inds`, as `checkInd` stores it: sort `1`, no parameter, two constructors with no
field); the goal `B` (`stNot`). The scrutinee holds `σ0` and `B` has two constructors, so the match SPLITS
(`checkTailAt`'s `.matchInd`, `.abs σ` case, D119): one world per constructor, in order.

The states, pinned by running the checker (`Steps/DataGuards.lean`):
- world `σ0 := T`: `ctorRefinement` gives `T` (no field, so no fresh unknown), `refine` puts it at `b` and records
  `0 := T`; the arm `F` is a constructor value, `F : B`; no arm moves anything, so the join drops nothing
  (`joinCont` hands back `k` itself); `k` runs on `F` at `B` from `leafT` (`b ↦ T`);
- world `σ0 := F`: the same with the constructors swapped; `k` runs on `T` at `B` from `leafF`;
- after both worlds the snapshot is back: exactly `stNot`'s kernel (nothing was made).
A world's exit keeps the counters, so a continuation that names an unknown in world `T` changes the counters world
`F`'s leaf has (guarded): hence `KeepsAtT`, as `KeepsAtZ` for `P`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnNot

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- `inductive B := T | F`, as `checkInd` stores it. -/
def declB : IndDecl := { name := "B", ctors := [("T", []), ("F", [])] }

/-- The type `B`. -/
def tyB : Value := .tInd "B" []

/-- The constructor values `T` and `F`, as `ctorRefinement` and `evalCtor` build them. -/
def vT : Value := .ind "B" 0 ⟨"T"⟩ [] []
def vF : Value := .ind "B" 1 ⟨"F"⟩ [] []

/-- `Not`'s body: `match #0 { T => F, F => T }`. -/
def bodyNot : Term :=
  .matchInd (.var 0) "B" [(⟨"T"⟩, .ctor "B" 1 ⟨"F"⟩ [] []), (⟨"F"⟩, .ctor "B" 0 ⟨"T"⟩ [] [])]

/-- `Π(b : B). B`, as the checker stores it. -/
def piB : Value := .tPi [] (.pi [⟨"b"⟩] [.tind "B" []] (.tind "B" [])) []

/-- `Not`'s `fix` term. -/
def fixNot : Term := .fix ⟨"Not"⟩ [⟨"b"⟩] [.tind "B" []] (.tind "B" []) none bodyNot

/-- `Not`'s global, as `checkDef` pushes it before checking the body. -/
def gNot : GDef := { name := "Not", ty := piB, fn? := some fixNot, val := .gfn "Not" }

/-- The function's binding of itself, marked (`recUid`). -/
def selfNot : Binding :=
  { hint := ⟨"Not"⟩, ty := some piB, val := .gfn "Not", decl := .pi (.ind "B" []), recUid := some 0 }

/-- The parameter's binding, holding `v`. -/
def bB (v : Value) : Binding := { hint := ⟨"b"⟩, ty := some tyB, val := v, decl := .ind "B" [] }

/-- The frames with `b ↦ v`. -/
def envB (v : Value) : Env := #[{}, { binds := #[selfNot, bB v] }]

/-- The kernel of the body's start state. -/
def stNot : MState :=
  { env := envB (.abs 0), globals := [gNot], inds := [declB], nextAbs := 1, absTy := #[tyB], absDecl := #[.other],
    goal := some tyB }

/-- The kernel at world `T`'s leaf: `b ↦ T`, the refinement `σ0 := T` recorded; nothing dropped. -/
def leafT : MState := { stNot with env := envB vT, refs := [(0, vT)] }

/-- The kernel at world `F`'s leaf. -/
def leafF : MState := { stNot with env := envB vF, refs := [(0, vF)] }

/-! ## The fact about the checker -/

/-- **World `T`'s continuation keeps the counters a world's exit keeps**: run on `F` at `B` from a state with
`leafT`'s kernel, `k` names no new unknown, changes no unknown's type or reading, and issues no label. -/
def KeepsAtT (k : Value → Value → M Unit) : Prop :=
  ∀ (st st' : MState) (bh : Nat), Kern leafT st → Runs (k vF tyB) st bh () st' →
    st'.nextAbs = st.nextAbs ∧ st'.absTy = st.absTy ∧ st'.absDecl = st.absDecl ∧ st'.nextLoan = st.nextLoan

/-- **The checker's split at `Not`'s body** (a fact about the checker alone; the machine lane's to prove): where
`checkTail` of `Not`'s body succeeds from a state with `stNot`'s kernel in the plain mode, with no handed-down
reading, with a continuation `k` that keeps the counters in world `T`, it ran `k` at two leaves, one per world: on
`F` at `B` from a state with the kernel `leafT`, and on `T` at `B` from a state with the kernel `leafF`. Guarded in
`Steps/DataGuards.lean` (the leaves' kernels, the order, the end state, the entry conditions). -/
def SplitNotInv : Prop :=
  ∀ (fuel : Nat) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat),
    Kern stNot st → Mode st → st.tailDecl = none → KeepsAtT k →
    Runs (Ochr.checkTail fuel bodyNot k) st bh () st' →
    (∃ stl bk stk, Kern leafT stl ∧ Runs (k vF tyB) stl bk () stk) ∧
    (∃ stl bk stk, Kern leafF stl ∧ Runs (k vT tyB) stl bk () stk)

end Ochr.Meaning.Steps.Form.ColumnNot
