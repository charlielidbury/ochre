import Ochr.Meaning.Strict.WitnessLet
import Ochr.Meaning.DataModel.CtorMem

/-!
# The typed checker's hints on the two probes of docs/31 D119

The reference hands a sub-term an expected type exactly where the TYPED checker does (D119). Two
programs, with the checker's verdicts (probed on the checker, 2026-11-21):

    inductive Opt (A : Type) := None | Some(v : A)
    def SetNone (p : &Opt(Nat)) : Unit := (*p := None)                       -- accepted
    def UseIt : Opt(Nat) := (let x = Some(1); (SetNone(&x); x))              -- accepted
    def TailNone : Opt(Nat) := (let y = Z; None)                             -- rejected

- `TailNone`: the typed checker hands a `let`'s tail no hint, so the bare `None` has no record and it
  rejects ("cannot infer the parameter A"). The reference fails there too (`tailNone_none`), at any
  outer hint: the strict constructor with no record fails.
- `UseIt`: its check runs `SetNone`'s body in place, where the UNTYPED checker hands `None` no hint
  (it checks nothing there). The reference hands it the place's type, as the typed checker does, so
  the in-place run of the body succeeds (`setNone_inPlace`), at `SetNone`'s frame above `UseIt`'s
  (`x` lent to the borrow `0`, `p` its holder). Had the reference followed the untyped checker it
  would fail (`runT_noneT_noHint`): the reason D119 follows the checker that checks.
-/

namespace Ochr.Meaning.Strict.Witness

open Ochr Ochr.Meaning Ochr.Meaning.Strict
open Classical

/-- `Opt(A) := None | Some(v : A)`. -/
def optD : IndDecl := { name := "Opt", params := [(⟨"A"⟩, .sort 1)], ctors := [("None", []), ("Some", [("v", .place (.var 0))])] }

/-- A bare `None`: no parameter written, no field. -/
def noneT (x : Hint) : Term := .ctor "Opt" 0 x [] []

section Generic
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **With no hint, the bare `None` fails**: no parameter written, no hint naming `Opt`, no field to
solve `A`, so no record (`ctorOut … none`). -/
theorem runT_noneT_noHint (hfl : ∀ sc t, K.D.flags sc t = (false, false))
    (hΓ : K.Γ.find? (·.name == "Opt") = some optD) (tl : Bool) (x : Hint) (s : SState) :
    runT K ρ φ tl (.plain TyM.err) (noneT x) s = none := by
  rw [noneT, runT]
  show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _
  rw [hfl]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [hΓ]
  have hd : (TyS.plain TyM.err).data = none := rfl
  simp [runParams, runFields, optD, ctorOut, SM.strictS, SM.fail, hd, pure, bind]

/-- **`TailNone` fails at every hint** (the checker rejects it): the `let`'s tail runs with no hint. -/
theorem tailNone_none (hfl : ∀ sc t, K.D.flags sc t = (false, false))
    (hΓ : K.Γ.find? (·.name == "Opt") = some optD) (tl : Bool) (hint : TyS) (y x : Hint) (s : SState) :
    runT K ρ φ tl hint (.letIn y .zero (noneT x)) s = none := by
  rw [runT]
  show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _
  rw [hfl]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  have hz : runT K ρ φ false (.plain TyM.err) .zero s = some ((.el0 Nat 0, .plain TyM.nat), s) := by
    rw [runT]; rfl
  simp only [Bind.bind, hz, Option.bind_some, runT_noneT_noHint hfl hΓ, Option.bind_none]

end Generic

section InPlace
variable (dm : DataModel) (r : Rec)

/-- The context: `Opt` declared, nothing erased, nothing invalidated. -/
def KO : RunCtx := { Kw dm [] with Γ := [optD] }

/-- `SetNone`'s frame above `UseIt`'s, as `callFrame` pushes it: `x : Opt(Nat)` (frame 0) lent at its
root to the borrow `0`; `self` and `p : &Opt(Nat)` (frame 1), `p` the borrow's holder with content
`c`. -/
def sN (c : Sem) : SState where
  env := [{ binds := [{ ty := .plain (dm.tyR optD r), val := fun ψ => ψ 0 }] }, { binds := [{ ty := .plain TyM.err, val := fun _ => .moved }, { ty := { (TyS.plain (dm.tyR optD r)) with label := some 0 }, val := fun _ => c }] }]
  shape := fun p => if p = .bind 1 1 then some 0 else none
  nextLoan := 1
  lent := fun l => if l = 0 then [⟨.bind 0 0, [], false⟩] else []
  heldTy := fun _ => dm.tyR optD r
  heldMem := fun _ => c

/-- `*p`. -/
def pDeref : Place := .deref (.var 0)

theorem resolve_sN (c : Sem) : resolve (sN dm r c) pDeref = some (.bind 1 1, [.deref]) := rfl

theorem reached_sN (c : Sem) (hit : List Step → Bool) (l : Nat) : (sN dm r c).reached (.bind 1 1) hit l = false := by
  unfold SState.reached; by_cases h : l = 0 <;> simp [sN, h]

theorem contentOf_sN (c : Sem) : contentOf (KO dm) φw pDeref (sN dm r c) =
    some ((c, { ({ (TyS.plain (dm.tyR optD r)) with label := some 0 } : TyS) with label := none }, .bind 1 1, [.deref]), sN dm r c) := by
  unfold contentOf
  rw [resolve_sN]
  dsimp only
  rw [access_unreached (reached_sN dm r c _)]
  rfl

/-- **The bare `None` at the place's type runs**: the hint names `Opt` at `r`, so it is built there
and is a member (`ctorR_mem`). -/
theorem run_noneT_hint (hok : dm.RecLeafOk optD r) (ρ : Assignment) (x : Hint) (T : TyS) (hT : T.m = dm.tyR optD r)
    (s : SState) :
    runT (KO dm) ρ φw false T (noneT x) s = some ((DataModel.ctorR optD r 0 [], .plain (dm.tyR optD r)), s) := by
  rw [noneT]
  have hdata : T.data = some ("Opt", r) := by
    unfold TyS.data; rw [hT]; simp [DataModel.tyR, optD, TyM.dataRec?]
  have hmem : DataModel.ctorR optD r 0 [] ∈ₛ[dm.read] dm.tyR optD r :=
    dm.ctorR_mem optD r 0 [] rfl (by decide) rfl (fun i f h => by simp at h) hok
  rw [runT]
  show SM.erasedIf (false, false) _ s = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  have hΓ : (KO dm).Γ.find? (·.name == "Opt") = some optD := rfl
  rw [hΓ]
  simp [runParams, runFields, hdata, ctorOut, SM.strictS, pure, bind, hmem, optD]
  exact ⟨hmem, rfl⟩

theorem placeTy_sN (c : Sem) : placeTy (KO dm) φw pDeref (sN dm r c) = .plain (dm.tyR optD r) := by
  unfold placeTy; rw [contentOf_sN]; rfl

theorem assignOk_sN (c : Sem) : AssignOk (KO dm) φw pDeref (sN dm r c) := by
  unfold AssignOk; rw [resolve_sN]
  exact ⟨fun _ => accessOkF_unreached (Γ := [optD]) (reached_sN dm r c _), fun h => by cases h⟩

/-- **`SetNone`'s body runs in place** (`*p := None`, the frame `sN` above `UseIt`'s): the bare `None`
is handed the place's type (D119: the typed checker's discipline at an assignment), built at `Opt`'s
record and a member; the write through `*` is whole. Under the untyped checker's discipline the
right-hand side would have no hint and fail (`runT_noneT_noHint`). -/
theorem setNone_inPlace (hok : dm.RecLeafOk optD r) (ρ : Assignment) (tl : Bool) (hint : TyS) (x : Hint) (c : Sem) :
    ∃ s', runT (KO dm) ρ φw tl hint (.assign pDeref (noneT x)) (sN dm r c) = some ((.el0 Unit (), .plain TyM.unit), s') := by
  have hmem : DataModel.ctorR optD r 0 [] ∈ₛ[dm.read] dm.tyR optD r :=
    dm.ctorR_mem optD r 0 [] rfl (by decide) rfl (fun i f h => by simp at h) hok
  rw [runT]
  show ∃ s', SM.erasedIf (false, false) _ _ = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [show (noneT x).assignHinted = true from rfl, if_pos rfl, contentOf_sN]
  dsimp only
  rw [run_noneT_hint dm r hok ρ x _ rfl]
  simp only [Bind.bind, Option.bind_some]
  rw [placeTy_sN, if_pos ⟨hmem, fun _ h => by cases h⟩, SM.guarded_of (assignOk_sN dm r c)]
  unfold assignAt
  rw [resolve_sN]
  simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
  rw [access_unreached (reached_sN dm r c _)]
  unfold setContent
  rw [if_pos (fun ψ _ => by rw [Sem.updAt_deref', Sem.updAt_nil']; rfl)]
  dsimp only
  rw [if_pos ⟨trivial, .inr (.inl rfl)⟩]
  exact ⟨_, rfl⟩

end InPlace

end Ochr.Meaning.Strict.Witness
