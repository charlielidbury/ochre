import Ochr.Meaning.Steps.ColumnP

/-!
# The first block the checker closes off, column `Q`: its states and the checker fact it assumes (lead18, 2026-11-21; docs/31 D137)

`def Q (n : Nat) : Nat := S(match n { Z => Z, S m => m })` in core terms: `S(match #0 { Z => Z, S _ => #0.0 })`
(`bodyQ`; the match is `P`'s body, `matchQ`). The match is the argument of `S`, not the end of the body, so the
checker cannot split there: its scrutinee holds the unknown `σ0`, the match is stuck, and the checker CLOSES IT OFF
([Split] for a non-tail match, `Machine.splitThenClose`, then [Block], `Machine.closeBlock`).

What the checker does (pinned in `Steps/BlockGuards.lean`, every `#guard` runs it), from `Q`'s start state (`stQ`:
`stP` with `Q`'s name and global):
- the block's captures, computed from syntax and declared types before anything runs (`blockCaptures`, K1): `n`, by
  MOVE (the arm `S _` moves `n.0`, so the static join moves `n`); the [Entry] accesses them (a no-op here);
- both arms are checked, each in its own world (`enterWorld`/`inWorld`): world `Z` (`σ0 := Z`, the arm `Z : Nat`),
  world `S` (a fresh `σ1 : Nat`, `σ0 := S(σ1)`, the arm's read moves `n.0`, `σ1 : Nat`); each arm's return is
  checked (`bodyReturns`); the worlds' refinements and moves are undone at their exits, but the counters are KEPT
  (`exitWorld`): after the block `σ1 : Nat` is still in the table of unknowns, named by nothing;
- the block's type is the arms' common type, `Nat`;
- the block is the anonymous closure `anonQ = fix _ (n : Nat) : Nat := match #0 { Z => Z, S _ => #0.0 }` (its body is
  the match with the capture renumbered to its parameter, here `matchQ` itself), called UNTYPED on the captured place
  `n`: the argument's read moves `n` (`n ↦ ⊥`) and gives `σ0`; the callee's body runs untyped and its match on `σ0` is
  stuck, so the call closes off: the value is the sealed program `⌈anonQ(σ0)⌉` (`vQ`), at `Nat`;
- no new unknown besides world `S`'s `σ1`, no label, no refinement left; the state after is `endQ`
  (`n ↦ ⊥`, the table of unknowns `[Nat, Nat]`).
In `clone`'s mode (`copying`) the block's argument read COPIES `n` (`n ↦ σ0` after); the plain mode is assumed
(`Mode`). An untyped run of the match fails (stuck, `stuckOn`): the enclosing call closes off instead.
-/

namespace Ochr.Meaning.Steps.Form.ColumnQ

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI selfTy selfSem)
open Ochr.Meaning.Steps.Form.ColumnP (nBot)

/-- The match: `P`'s body, `match #0 { Z => Z, S _ => #0.0 }`. -/
abbrev matchQ : Term := ParGuards.bodyP

/-- `Q`'s body: `S(match #0 { Z => Z, S _ => #0.0 })`. -/
def bodyQ : Term := .succ matchQ

/-- `Q`'s `fix` term. -/
def fixQ : Term := .fix ⟨"Q"⟩ [⟨"n"⟩] [.nat] .nat none bodyQ

/-- `Q` as a core definition. -/
def defQ : Def := { name := "Q", hs := [⟨"n"⟩], doms := [.nat], cod := .nat, body := bodyQ }

/-- `Q`'s global, as `checkDef` pushes it before checking the body. -/
def gQ : GDef := { name := "Q", ty := piNat, fn? := some fixQ, val := .gfn "Q" }

/-- The function's binding of itself, marked (`recUid`). -/
def selfQ : Binding := { hint := ⟨"Q"⟩, ty := some piNat, val := .gfn "Q", decl := .pi .other, recUid := some 0 }

/-- The kernel of the body's start state. -/
def stQ : MState :=
  { env := #[{}, { binds := #[selfQ, nB] }], globals := [gQ], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other],
    goal := some .tNat }

/-- The kernel after the block (and after the body): `n` moved by the block's call, world `S`'s `σ1 : Nat` kept in
the table, no refinement. -/
def endQ : MState :=
  { env := #[{}, { binds := #[selfQ, nBot] }], globals := [gQ], nextAbs := 2, absTy := #[.tNat, .tNat],
    absDecl := #[.other, .other], goal := some .tNat }

/-- The block's code: the anonymous function of the captured `n` (`closeBlock`'s `anon`), its body the match with
the capture renumbered to the parameter (`matchQ` itself), its domain and codomain the place's type and the arms'. -/
def anonFix : Term := .fix ⟨"_"⟩ [⟨"n"⟩] [.val .tNat] (.val .tNat) none matchQ

/-- The block as a closure value: no capture of its own, its parameter read `.other` at `Nat`. -/
def anonQ : Value := .clo [] anonFix [(.other, .tNat)]

/-- The sealed program the block closes off to: the block called on `σ0`. -/
def sealQ : Term := .call (.val anonQ) [.val (.abs 0)] true

/-- The block's value on main's checker, `⌈anonQ(σ0)⌉` (a closure applied; not what the experimental checker makes). -/
def vQClo : Value := .sealed sealQ

/-- **The block's text** (exp-block-text, `spine-exp-block`): its one cell `n` holding `σ0` at `Nat` (read `.other`, not a
proof), then the match over it, of type `Nat`: `⌈let n = σ0; match n { Z => 0, S _ => n.0 }⌉`. -/
def textQ : Term := .block [(⟨"n"⟩, .val (.abs 0))] [(.other, .tNat)] [false] .tNat matchQ

/-- The block's value on the experimental checker: its sealed text. -/
def vQ : Value := .sealed textQ

/-! ## The context -/

/-- The globals while `Q`'s body is checked: `Q` means its stage-0 closure (as `P`, `ColumnP.CP`). -/
noncomputable def CQ (R : DataRead) (φ : Future) : CodeMeaning :=
  { global := fun n => if n = "Q" then (selfSem R φ, .plain (selfTy R)) else (.el0 Nat 0, .plain TyM.nat),
    sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- The run's context while `Q`'s body is checked, at the unknowns' types `Δ`. -/
noncomputable def KQ (dm : DataModel) (D : Decisions) (φ : Future) (Δ : Nat → TyS) : RunCtx :=
  { dm := dm, Γ := [], C := CQ dm.read φ, D := D, Δ := Δ, cur := some ("Q", 0) }

/-! ## The facts about the checker -/

/-- **The checker closes `Q`'s match off** (a fact about the checker alone; the machine lane's to prove): every
successful TYPED `eval` of the match from a state with `stQ`'s kernel, in the plain mode, not in tail position, with no
handed-down reading, returns the sealed block's text `⌈let n = σ0; match n {…}⌉` (`vQ`; on main `⌈anonQ(σ0)⌉`) at `Nat` and ends with `endQ`'s kernel (`n` moved, world
`S`'s `σ1 : Nat` kept in the table). Guarded in `Steps/BlockGuards.lean` (the value, the type, the end kernel at
every hint and tail flag; the captures; the worlds; the entry conditions). -/
def BlockQInv : Prop :=
  ∀ (n : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
    Kern stQ st → Mode st → st.tailNext = false → st.tailDecl = none →
    Runs (Ochr.eval n true matchQ hint) st bh (v, T?) st' →
    v = vQ ∧ T? = some .tNat ∧ Kern endQ st'

/-- **The checker's acceptance of `Q`, inverted down to its body's run** (a fact about the checker, assumed; the
machine lane's to prove; `ColumnI.FixRunI` for `Q`): where `checkDef defQ` succeeds from the empty state, `checkFix`
ran the body's typed `eval` (the general case of `checkTail`: `S(…)` is no form it splits on) from a state with
`stQ`'s kernel, in the plain mode, with no handed-down reading. Guarded by `checkDef defQ`'s trace in
`Steps/BlockGuards.lean`. -/
def FixRunQ : Prop :=
  ∀ (fuel : Nat) (st₁ : MState), Runs (checkDef defQ) {} fuel () st₁ →
    ∃ (n : Nat) (hc : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
      Kern stQ st ∧ Mode st ∧ st.tailDecl = none ∧ Runs (Ochr.eval n true bodyQ hc) st bh (v, T?) st'

end Ochr.Meaning.Steps.Form.ColumnQ
