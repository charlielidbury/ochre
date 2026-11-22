import Ochr.Meaning.Steps.FormTail
import Ochr.Meaning.Steps.ParGuards

/-!
# A data type with a field: the columns `Wrap` and `Unbox`, their states and the checker facts they assume (lead21, 2026-11-22; docs/31 D148)

```
inductive Box := MkBox(n : Nat)
def Wrap(n : Nat) : Box := MkBox(n)
def Unbox(b : Box) : Nat := match b { MkBox(n) => n }
```
Core bodies: `MkBox(#0)` (`bodyWrap`, a constructor taking its argument) and `match #0 { MkBox => #0.n }` (`bodyUnbox`,
the field read out of the matched value as the place `b.n`, a field of constructor `0` of `Box`). Each is checked
by `checkTail` from its generic state; `Unbox` alone with `Box` (no `Wrap` in Σ), so its start state has one global.

The states, pinned by running the checker (`Steps/DataBoxGuards.lean`):
- `Wrap`: from `stWrap` (`n ↦ σ0 : Nat`, the goal `Box`), `checkTail`'s general case runs the constructor's typed
  `eval` at the goal: the field's read MOVES `n` (`n ↦ ⊥`), the value `MkBox(σ0) : Box`; `k` runs on it from
  `endWrap`. One leaf.
- `Unbox`: from `stUnbox` (`b ↦ σ0 : Box` read `.ind Box []`, the goal `Nat`), `checkTailAt`'s `.matchInd` on `σ0` of
  a ONE-constructor type does not split (D93): `etaInPlace` makes a fresh `σ1 : Nat` (read `.other`), refines
  `σ0 := MkBox(σ1)` in place (`b ↦ MkBox(σ1)`, recorded in `refs` AND in `etaRefs`), and runs the match again on the
  constructor: its one arm, with no join (one constructor); the arm's read of the place `b.n` MOVES it
  (`b ↦ MkBox(⊥)`), the value `σ1 : Nat`; `k` runs on it from `leafUnbox`. One leaf, and nothing is undone after it
  (no world): the refinement, the record and the partial move stay.
-/

namespace Ochr.Meaning.Steps.Form.ColumnBox

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- `inductive Box := MkBox(n : Nat)`, as `checkInd` stores it. -/
def declBox : IndDecl := { name := "Box", ctors := [("MkBox", [("n", .nat)])] }

/-- The type `Box`. -/
def tyBox : Value := .tInd "Box" []

/-- The constructor value `MkBox(v)`. -/
def mkBox (v : Value) : Value := .ind "Box" 0 ⟨"MkBox"⟩ [] [v]

/-- The field `n` of `MkBox`, as a pattern variable names it. -/
def fieldN : FieldRef := ⟨"Box", 0, 0, "n"⟩

/-- `Wrap`'s body: `MkBox(#0)`. -/
def bodyWrap : Term := .ctor "Box" 0 ⟨"MkBox"⟩ [] [.place (.var 0)]

/-- `Unbox`'s body: `match #0 { MkBox => #0.n }`. -/
def bodyUnbox : Term := .matchInd (.var 0) "Box" [(⟨"MkBox"⟩, .place (.field fieldN (.var 0)))]

/-- The functions' types, as the checker stores them. -/
def piWrap : Value := .tPi [] (.pi [⟨"n"⟩] [.nat] (.tind "Box" [])) []
def piUnbox : Value := .tPi [] (.pi [⟨"b"⟩] [.tind "Box" []] .nat) []

def fixWrap : Term := .fix ⟨"Wrap"⟩ [⟨"n"⟩] [.nat] (.tind "Box" []) none bodyWrap
def fixUnbox : Term := .fix ⟨"Unbox"⟩ [⟨"b"⟩] [.tind "Box" []] .nat none bodyUnbox

def gWrap : GDef := { name := "Wrap", ty := piWrap, fn? := some fixWrap, val := .gfn "Wrap" }
def gUnbox : GDef := { name := "Unbox", ty := piUnbox, fn? := some fixUnbox, val := .gfn "Unbox" }

/-- The functions' bindings of themselves, marked. `Wrap`'s is read `.pi (.ind Box [])`, `Unbox`'s `.pi .other`. -/
def selfWrap : Binding :=
  { hint := ⟨"Wrap"⟩, ty := some piWrap, val := .gfn "Wrap", decl := .pi (.ind "Box" []), recUid := some 0 }
def selfUnbox : Binding :=
  { hint := ⟨"Unbox"⟩, ty := some piUnbox, val := .gfn "Unbox", decl := .pi .other, recUid := some 0 }

/-- The parameters' bindings. -/
def nW (v : Value) : Binding := { hint := ⟨"n"⟩, ty := some .tNat, val := v, decl := .other }
def bX (v : Value) : Binding := { hint := ⟨"b"⟩, ty := some tyBox, val := v, decl := .ind "Box" [] }

def envW (v : Value) : Env := #[{}, { binds := #[selfWrap, nW v] }]
def envU (v : Value) : Env := #[{}, { binds := #[selfUnbox, bX v] }]

/-- The kernel of `Wrap`'s body's start state. -/
def stWrap : MState :=
  { env := envW (.abs 0), globals := [gWrap], inds := [declBox], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other],
    goal := some tyBox }

/-- The kernel at `Wrap`'s one leaf: `n` moved. -/
def endWrap : MState := { stWrap with env := envW .bot }

/-- The kernel of `Unbox`'s body's start state. -/
def stUnbox : MState :=
  { env := envU (.abs 0), globals := [gUnbox], inds := [declBox], nextAbs := 1, absTy := #[tyBox], absDecl := #[.other],
    goal := some .tNat }

/-- The kernel at `Unbox`'s one leaf: the fresh `σ1 : Nat`, `σ0 := MkBox(σ1)` recorded as a refinement and as η, the
field moved out (`b ↦ MkBox(⊥)`). -/
def leafUnbox : MState :=
  { stUnbox with
    env := envU (mkBox .bot), nextAbs := 2, absTy := #[tyBox, .tNat], absDecl := #[.other, .other],
    refs := [(0, mkBox (.abs 1))], etaRefs := [(0, mkBox (.abs 1))] }

/-! ## The facts about the checker -/

/-- **The checker at `Wrap`'s body** (a fact about the checker alone): where `checkTail` of `MkBox(#0)` succeeds from
a state with `stWrap`'s kernel in the plain mode with no handed-down reading, it ran `k` on `MkBox(σ0)` at `Box` from a
state with the kernel `endWrap`. Guarded in `Steps/DataBoxGuards.lean`. -/
def WrapInv : Prop :=
  ∀ (fuel : Nat) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat),
    Kern stWrap st → Mode st → st.tailDecl = none →
    Runs (Ochr.checkTail fuel bodyWrap k) st bh () st' →
    ∃ stl bk stk, Kern endWrap stl ∧ Runs (k (mkBox (.abs 0)) tyBox) stl bk () stk

/-- **The checker at `Unbox`'s body** (a fact about the checker alone): where `checkTail` of
`match #0 { MkBox => #0.n }` succeeds from a state with `stUnbox`'s kernel in the plain mode with no handed-down
reading, it ran `k` on `σ1` at `Nat` from a state with the kernel `leafUnbox`. Guarded in `Steps/DataBoxGuards.lean`. -/
def UnboxInv : Prop :=
  ∀ (fuel : Nat) (k : Value → Value → M Unit) (st st' : MState) (bh : Nat),
    Kern stUnbox st → Mode st → st.tailDecl = none →
    Runs (Ochr.checkTail fuel bodyUnbox k) st bh () st' →
    ∃ stl bk stk, Kern leafUnbox stl ∧ Runs (k (.abs 1) .tNat) stl bk () stk

end Ochr.Meaning.Steps.Form.ColumnBox
