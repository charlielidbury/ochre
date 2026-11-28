import Ochr.Meaning.Steps.TopFix

/-!
# `FixMeanAt` reduced: the round trip of codes is definitional; what remains is `PartsRun` (lead44; docs/31 D257)

lead43 read `FixMeanAt` (a function's recorded meaning is its guarded fixpoint's closure, a member of its stored type) as
a fact about the model alone. It is not. `defMeaning` gives the function the TYPE its stored Π-type means, and that
meaning is the run of the Π-term at the forming state, which is `err` unless every domain and the codomain have a level
at every tuple of members (`PiOk`). That clause, `PartsRun`, is (II) at `checkFix`'s own evaluations of the parameter
types and the codomain, then (I): a mixed fact.

Here, kernel-checked: `FixMeanAt` from `PartsRun`, the code being closed (`freeVars = []`, a resolution fact), and the
table's proof flag on the fix term agreeing with its sort (both decisions read the codomain's declared sort). The round
trip of codes (lead39's open sub-fact: the stored Π-type's code is the one the fix term's domains and codomain run to)
needs no lemma: both are the same `runDoms`/`codOf` at `formG`.
-/

namespace Ochr.Meaning.Steps.Form.Top

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master

/-- **The stored Π-type's meaning is the `.pi` term's run at the forming state**: `piTyAt` at the parts when they run
(`PiOk`). -/
theorem globalTyS_tPi (K : RunCtx) (hs : List Hint) (ds : List Term) (c : Term)
    (hok : PiOk K.dm.read (psG K (fun _ => .err) noFuture ds) [] (outG K (fun _ => .err) noFuture ds c)) :
    globalTyS (fun _ => .err) K (.tPi [] (.pi hs ds c) []) =
      .plain (piTyAt K.dm.read (lG K hs ds c) (psG K (fun _ => .err) noFuture ds) (outG K (fun _ => .err) noFuture ds c)) := by
  unfold globalTyS Value.tyS
  rw [meanV_eq_mean]
  have h1 : meanV K (fun _ => .err) (fun _ => .err) (.plain .err) (.tPi [] (.pi hs ds c) []) =
      (match run K (fun _ => .err) (fun _ => .err) (.plain .err) (.pi hs ds c) (stateOf 0 []) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err) := by
    classical
    show (if CapsOk K.dm.read (capsVals K (fun _ => .err) (fun _ => .err) []) (capsTys K (fun _ => .err) (fun _ => .err) []) then
        match run K (fun _ => .err) (fun _ => .err) (.plain .err) (.pi hs ds c)
          (stateOf 0 (capsState (capsVals K (fun _ => .err) (fun _ => .err) []) (capsTys K (fun _ => .err) (fun _ => .err) []))) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err
      else .ty TyM.err) = _
    rw [capsVals, capsTys, if_pos (show CapsOk K.dm.read [] [] from trivial)]
    rfl
  have hok' : PiOk K.dm.read (runDoms K (fun _ => .err) (fun _ => .err) (stateOf 0 []) ds) []
      (codOf K (fun _ => .err) (fun _ => .err) (stateOf 0 []) (bindsOf K (fun _ => .err) (fun _ => .err) (stateOf 0 []) ds)
        (ds.map Term.isRefTy) c) := hok
  rw [h1, run, run_pi_def, if_pos hok']
  rfl

/-- A strict test that passes. -/
theorem strictS_some (R : DataRead) (x : Sem × TyS) (s : SState) (h : x.1 ∈ₛ[R] x.2.m) :
    SM.strictS R (fun s' => some (x, s')) s = some (x, s) := by
  simp only [SM.strictS, if_pos h]

/-- **`FixMeanAt` from `PartsRun`** (kernel-checked; standard axioms): a function's recorded meaning is a member of its
stored type, given the parts of that type running at every member tuple (`PartsRun`, `PiOk`: (II) at `checkFix`'s
evaluations of the parameter types and the codomain, then (I)), the code closed (a resolution fact), and the table's proof
flag on the fix term only at sort `0` (both decisions read the codomain's declared sort). -/
theorem fixMeanAt_of (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (P : ProgState) (d : Def) (st' : MState)
    (hd : d.doms ≠ [])
    (hclosed : (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body).freeVars = [])
    (hparts : PiOk dm.read (psG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.doms) []
      (outG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.doms d.cod))
    (hflag : ((P.ctx dm D Γ st').D.flags (scopeOf (emptyState 0)) (.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body)).2 = true →
      lG (P.ctx dm D Γ st') d.hs d.doms d.cod = 0) :
    FixMeanAt dm D Γ P d st' := by
  intro hmem
  have hA := globalTyS_tPi (P.ctx dm D Γ st') d.hs d.doms d.cod hparts
  have hcap : capOrder (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) = [] := by
    unfold capOrder; rw [hclosed]; rfl
  have hne : d.doms.isEmpty = false := by
    cases h : d.doms with
    | nil => exact absurd h hd
    | cons _ _ => rfl
  unfold defMeaning
  have hfm : fixMoves (P.ctx dm D Γ st') (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) (emptyState 0) = emptyState 0 := by
    unfold fixMoves; rw [hcap]; rfl
  have he0 : (emptyState 0 : SState) = stateOf 0 [] := rfl
  rw [hne, if_neg Bool.false_ne_true, run, run_fix_def, hcap, hfm, hA]
  simp only [FoldOk, if_true, he0]
  simp only [psG, outG, lG, GG, formG, fbG] at hmem hflag
  rw [he0] at hflag
  generalize hfl : (P.ctx dm D Γ st').D.flags (scopeOf (stateOf 0 [])) (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) = fl at hflag ⊢
  obtain ⟨b1, b2⟩ := fl
  rw [strictS_some]
  · cases b2 with
    | false =>
      cases b1
      · exact ⟨_, rfl, hmem⟩
      · exact ⟨_, rfl, hmem⟩
    | true =>
      have hl : lG (P.ctx dm D Γ st') d.hs d.doms d.cod = 0 := hflag rfl
      have hl' : (P.ctx dm D Γ st').D.piSort (scopeOf (stateOf 0 [])) (Term.pi d.hs d.doms d.cod) = 0 := hl
      simp only [SM.erasedIf, if_true, hl', closureAt]
      refine ⟨_, rfl, ?_⟩
      have h0 := hmem
      simp only [hl', closureAt] at h0
      show Sem.proof ∈ₛ[dm.read] piTyAt dm.read (lG (P.ctx dm D Γ st') d.hs d.doms d.cod) _ _
      rw [hl]
      exact h0
  · exact hmem
end Ochr.Meaning.Steps.Form.Top
