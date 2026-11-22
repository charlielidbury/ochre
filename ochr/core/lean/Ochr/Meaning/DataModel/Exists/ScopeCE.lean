import Ochr.Meaning.DataModel.Exists.KnotCE
import Ochr.Meaning.DataModel.CtorMem

/-!
# Weakening in the declaration list needs a scope invariant (exists8, the lead's ruling (a))

The reference run reads the declaration list `K.Γ` not only at the names a term mentions: reading a
field of a constructor value whose content is a tree of ANOTHER declaration than the field's shape
names (a strong update's tree, D112) looks that tree's declaration up by the name the tree carries
(`DataModel.readTy`'s `ownTy`, through `Sem.stepField` and `Sem.follow`). So the run of a term that
names no declaration at all can differ between a declaration list and an extension of it, when the
state holds a tree whose name only the extension declares.

The smallest instance (`run_differs`): the lists `[]` and `[L]`; the state one binding `x : M` holding
`MkM(t)` where `M`'s record makes its field a `N`, and `t` is a tree of `L` (`MkL`); the term `x.0`.
Under `[]` the read fails (`ownTy` finds no `L`); under `[L]` it reads `t` at `L`'s type. The state
names `L`, which `[]` does not declare: it is outside the scope invariant (`Γ1`'s names only), which
is therefore necessary.
-/

namespace Ochr.Meaning.DataModel.Exists.ScopeCE

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

def declL : IndDecl := { name := "L", ctors := [("MkL", [])] }
def declN : IndDecl := { name := "N", ctors := [("MkN", [])] }
def declM : IndDecl := { name := "M", ctors := [("MkM", [("x", .tind "N" [])])] }

/-- `M`'s record: its field is an `N`. -/
def recM : Rec
  | [(0, 0, [])] => .data declN
  | _ => .none
/-- `L`'s record: nothing to keep. -/
def recL : Rec := fun _ => .none

/-- A tree of `L`. -/
def tL : Sem := .dat "L" recL 0 []
/-- `MkM(t)` with `t` a tree of `L` where the shape says `N`. -/
def vM : Sem := .dat "M" recM 0 [tL]

theorem follow_nil (dm : DataModel) :
    Sem.follow dm [] (.plain (dm.rawTy declM recM)) vM [.proj 0] = none := by
  simp [Sem.follow, Sem.step, Sem.stepField, vM, tL, DataModel.rawTy, Code0.dataCode?, declM, DataModel.readTy,
    DataModel.sig, uSig, uShape, recM, kindKey, projIdx, DataModel.ownTy, declN, Sem.asNat_dat, TyS.plain, TyM.dataCode?]

theorem follow_L (dm : DataModel) :
    Sem.follow dm [declL] (.plain (dm.rawTy declM recM)) vM [.proj 0] = some (tL, .plain (dm.rawTy declL recL)) := by
  simp [Sem.follow, Sem.step, Sem.stepField, vM, tL, DataModel.rawTy, Code0.dataCode?, declM, DataModel.readTy,
    DataModel.sig, uSig, uShape, recM, kindKey, projIdx, DataModel.ownTy, declN, declL, Sem.asNat_dat, TyS.plain, TyM.dataCode?]

/-! ## The run of `x.0` -/

/-- The binding `x : M` holding `vM`. -/
noncomputable def bx (dm : DataModel) : SBinding := { ty := .plain (dm.rawTy declM recM), val := fun _ => vM, decl := .other }
/-- One frame, the binding `x`. -/
noncomputable def sx (dm : DataModel) : SState := stateOf 0 [bx dm]
/-- The place `x.0`. -/
def px : Place := .proj 0 (.var 0)

theorem sx_shape (dm : DataModel) : (sx dm).shape = fun _ => none := rfl

theorem sx_live (dm : DataModel) : (sx dm).liveLabels = [] := by
  have h0 : ∀ l : List Pos, List.filterMap (fun _ : Pos => (none : Option Nat)) l = [] := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  simp [SState.liveLabels, sx_shape, h0]

theorem contentOf_px (K : RunCtx) (φ : Future) :
    contentOf K φ px (sx K.dm) = (Sem.follow K.dm K.Γ (.plain (K.dm.rawTy declM recM)) vM [.proj 0]).map
      fun vt => ((vt.1, { vt.2 with label := none }, .bind 0 0, [.proj 0]), sx K.dm) := by
  have hacc : ∀ pos hit, (sx K.dm).access pos hit = sx K.dm := fun pos hit => Attack.access_noShape _ (sx_shape _) pos hit
  have htf : (sx K.dm).typedFuture φ = φ := by funext l; simp [SState.typedFuture, sx_live]
  have hv : (sx K.dm).varPos 0 = some (.bind 0 0) := by simp [sx, SState.varPos, stateOf, SState.topIdx]
  have hty : (sx K.dm).tyAt (.bind 0 0) = .plain (K.dm.rawTy declM recM) := by simp [sx, SState.tyAt, stateOf, bx]
  have hval : (sx K.dm).valAt (.bind 0 0) φ = vM := by simp [sx, SState.valAt, stateOf, bx]
  simp only [contentOf, resolve, px, Place.steps, hacc, htf, hv, Option.map_some, hty, hval, List.nil_append]
  cases Sem.follow K.dm K.Γ (TyS.plain (K.dm.rawTy declM recM)) vM [Step.proj 0] <;> rfl

theorem tL_mem (dm : DataModel) : tL ∈ₛ[dm.read] dm.rawTy declL recL := by
  have h := dm.ctorR_mem declL recL 0 [] rfl (by decide) rfl (fun i f hf => by simp at hf)
    (fun c i e hc hi _ => by
      have : c = 0 := by simp [declL] at hc; omega
      subst this; simp [declL, DataLib.arity] at hi)
  have e1 : DataModel.ctorR declL recL 0 [] = tL := rfl
  have e2 : dm.tyR declL recL = dm.rawTy declL recL := by simp [DataModel.tyR, DataModel.rawTy, declL]
  rwa [e1, e2] at h

/-- **Under the list `[]` the read of `x.0` fails**: `ownTy` finds no `L`. -/
theorem run_nil (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (hΓ : K.Γ = [])
    (hD : ∀ sc t, K.D.flags sc t = (false, false)) : runT K ρ φ tl h (.place px) (sx K.dm) = none := by
  have hc : contentOf K φ px (sx K.dm) = none := by rw [contentOf_px, hΓ, follow_nil]; rfl
  simp only [runT]
  rw [hD]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false,
    SM.guarded_of (Strict.Witness.contentOk_noLive (sx_live K.dm) px)]
  simp [readPlace, hc, bind, Option.bind]

/-- **Under the list `[L]` it reads `t` at `L`'s type** (a copy). -/
theorem run_L (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (hΓ : K.Γ = [declL])
    (hD : ∀ sc t, K.D.flags sc t = (false, false)) (hcp : K.D.copy (K.D.placeDecl (scopeOf (sx K.dm)) px) = true) :
    runT K ρ φ tl h (.place px) (sx K.dm) = some ((tL, .plain (K.dm.rawTy declL recL)), sx K.dm) := by
  have hc : contentOf K φ px (sx K.dm) = some ((tL, .plain (K.dm.rawTy declL recL), .bind 0 0, [.proj 0]), sx K.dm) := by
    rw [contentOf_px, hΓ, follow_L]; rfl
  have hw : tL.whole := by simp [tL, Sem.whole]
  have hg : ReadGood K.dm.read (K.dm.rawTy declL recL) tL := .inl (tL_mem K.dm)
  simp only [runT]
  rw [hD]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false,
    SM.guarded_of (Strict.Witness.contentOk_noLive (sx_live K.dm) px), hcp]
  simp only [readPlace, hc, bind, Option.bind]
  rw [if_neg (fun hn => hn hw), if_neg (fun hn => hn hg)]
  rfl

/-- **The run of a term naming no declaration differs between `[]` and its extension `[L]`**, at a
state holding a tree of `L` (outside the scope of `[]`). -/
theorem run_differs (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS)
    (hD : ∀ sc t, K.D.flags sc t = (false, false)) (hcp : K.D.copy (K.D.placeDecl (scopeOf (sx K.dm)) px) = true) :
    runT { K with Γ := [] } ρ φ tl h (.place px) (sx K.dm) = none ∧
      runT { K with Γ := [declL] } ρ φ tl h (.place px) (sx K.dm) = some ((tL, .plain (K.dm.rawTy declL recL)), sx K.dm) :=
  ⟨run_nil { K with Γ := [] } ρ φ tl h rfl hD, run_L { K with Γ := [declL] } ρ φ tl h rfl hD hcp⟩

end Ochr.Meaning.DataModel.Exists.ScopeCE
