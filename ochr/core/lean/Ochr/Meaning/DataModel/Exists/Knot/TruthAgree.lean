import Ochr.Meaning.DataModel.Exists.Knot.TruthMono
import Ochr.Meaning.DataModel.Exists.Knot.Steady

/-!
# Truth first, part 4: the field types are the run's (exists7)

At the truth record `R = truthRec (truthP)`, `d`'s code at any arguments is the proposition its truth
predicate gives there (`uTyR_truthRec`, the fixed point). So the actual run of a field type, at the
model with `d`'s records set to `R`, reads `d(ā)` as the interpreter `semP` does, and agrees with it
along the spine (`semP_run`, as `semT_run` for the knot). The steady nodes agree by the knot's argument,
now for any spec (`Steady.steadyAt_spec`: frame locality and the model congruence).
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Classical

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat} {R : List Sem → Rec} {T : List Sem → Prop}
variable {ps : List Sem} {A F : SState} {P : Nat → Prop}

mutual
/-- **Along the spine the run's value is the truth interpreter's**, at a frame `A` whose parameter
bindings hold the parameters, given that `d`'s code at `R` is `T`'s proposition and that every steady
node's run there is its canonical value at `F`. -/
theorem semP_run (hT : ∀ a, uTyR d (R a) = TyM.prop (T a))
    (hAs : A.shape = fun _ => none)
    (hpar : ∀ v, v < d.params.length → ∃ pos, A.varPos v = some pos ∧ A.valAt pos noFuture = ps.getD (d.params.length - 1 - v) .err)
    (hst : ∀ t h r s', Steady d c t → (∀ v ∈ t.freeVars, P v) →
      runT { K with dm := setRec K.dm d R } ρ noFuture false h t A = some (r, s') → r.1 = valOf K ρ F h t) :
    ∀ {t : Term}, PSpine K.Γ d c t → (∀ v ∈ t.freeVars, P v) → ∀ h r s',
      runT { K with dm := setRec K.dm d R } ρ noFuture false h t A = some (r, s') → r.1 = semP K ρ d T ps F h t
  | _, .nat, hP, h, r, s', hr => by
    rw [hst _ h r s' (steady_nat d c) hP hr, semP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .unit, hP, h, r, s', hr => by
    rw [hst _ h r s' (steady_unit d c) hP hr, semP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .call _ _ _ hs, hP, h, r, s', hr => by
    rw [hst _ h r s' hs hP hr, semP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .eq _ _ _ hs, hP, h, r, s', hr => by
    rw [hst _ h r s' hs hP hr, semP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .param v hv, _, h, r, s', hr => by
    obtain ⟨pos, hpos, hval⟩ := hpar v hv
    rw [RunLemmas.runT_var _ _ _ _ _ _ _ hAs pos hpos hr, hval, semP_var K ρ d T ps F h v hv]
  | _, .tind n as M hM hargs, hP, h, r, s', hr => by
    obtain ⟨M', psM, hM', hps, -, hr1, -⟩ := RunLemmas.runT_tind _ _ _ _ _ _ _ _ hr
    have hMM : M' = M := by rw [show K.Γ = ({ K with dm := setRec K.dm d R } : RunCtx).Γ from rfl, hM'] at hM; cases hM; rfl
    subst hMM
    rw [hr1, semP_tind, hM]
    have := itpArgsP_run hT hAs hpar hst hargs (fun a ha v hv => hP v (mem_freeVars_tind ha hv)) [] psM A hps
    simp only [DataModel.tyM, setRec_recFor K d R, tyR_eq_uTyR, this, recFor]
    by_cases hMd : M' = d
    · subst hMd; simp only [if_true, hT]
    · simp only [if_neg hMd]

theorem itpArgsP_run (hT : ∀ a, uTyR d (R a) = TyM.prop (T a))
    (hAs : A.shape = fun _ => none)
    (hpar : ∀ v, v < d.params.length → ∃ pos, A.varPos v = some pos ∧ A.valAt pos noFuture = ps.getD (d.params.length - 1 - v) .err)
    (hst : ∀ t h r s', Steady d c t → (∀ v ∈ t.freeVars, P v) →
      runT { K with dm := setRec K.dm d R } ρ noFuture false h t A = some (r, s') → r.1 = valOf K ρ F h t) :
    ∀ {M : IndDecl} {j : Nat} {pre as : List Term}, PSpineArgs K.Γ d c M j pre as → (∀ a ∈ as, ∀ v ∈ a.freeVars, P v) →
      ∀ (vs psM : List Sem) (s' : SState), runParams { K with dm := setRec K.dm d R } ρ noFuture M j vs as A = some (psM, s') →
        psM = itpArgsP K ρ d T ps F M j vs as
  | _, _, _, _, .nil _ _ _, _, vs, psM, s', h => by
    simp only [runParams, pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, itpArgsP_nil]
  | _, _, _, _, .type M j pre a as hty ha _ _ hrest, hP, vs, psM, s', h => by
    obtain ⟨v, T', s₁, rest, hv, hrest', rfl⟩ := runParams_cons _ _ _ _ _ _ _ _ _ h
    have e1 : v = argSemP K ρ d T ps F M j vs a := by
      rw [argSemP_eq, if_pos hty]
      exact semP_run hT hAs hpar hst ha (hP a (List.mem_cons_self ..)) _ _ _ hv
    rw [itpArgsP_cons, ← e1, itpArgsP_run hT hAs hpar hst hrest (fun b hb => hP b (List.mem_cons_of_mem _ hb)) _ _ _ hrest']
  | _, _, _, _, .value M j pre a as hty ha hrest, hP, vs, psM, s', h => by
    obtain ⟨v, T', s₁, rest, hv, hrest', rfl⟩ := runParams_cons _ _ _ _ _ _ _ _ _ h
    have e1 : v = argSemP K ρ d T ps F M j vs a := by
      rw [argSemP_eq, if_neg (by simp [hty])]
      exact hst _ _ _ _ ha (hP a (List.mem_cons_self ..)) hv
    rw [itpArgsP_cons, ← e1, itpArgsP_run hT hAs hpar hst hrest (fun b hb => hP b (List.mem_cons_of_mem _ hb)) _ _ _ hrest']
end

end

/-- **The truth record agrees with the run, given the steady nodes.** -/
theorem truth_agree (K : RunCtx) (ρ : Assignment) (d : IndDecl) (G : TruthHyp K d)
    (hst : SteadyAtS K ρ d (truthSpec K ρ d (truthP K ρ d))) :
    ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
      ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
      (∀ j (hj : j < e.length), e[j] ∈ₛ[K.dm.read]
        (setRec K.dm d (truthRec K ρ d (truthP K ρ d))).fieldTy d ps c j (e.take j)) →
      e.length = i → fieldTerm d c i = some FT →
      run { K with dm := setRec K.dm d (truthRec K ρ d (truthP K ρ d)) } ρ noFuture (.plain (TyM.univ 1)) FT
        (teleFrame (setRec K.dm d (truthRec K ρ d (truthP K ρ d))) K.D d ps c e) = some (r, s') →
        r.1.asTy = (ftyP K ρ d (truthP K ρ d) ps c i (projIdx d c (e.map Sem.small))).mean := by
  intro ps c i e FT r s' hl hty hfit hei hFT hrun
  unfold run at hrun
  have hsem := semP_run (P := fun v => v ∈ FT.freeVars) (F := canFrame K d ps c i (projIdx d c (e.map Sem.small))
      fun j => if _h : j < i then
        shapeTyP (shapeOf (ftyP K ρ d (truthP K ρ d) ps c j ((projIdx d c (e.map Sem.small)).take j))) else TyM.err)
    (uTyR_truthRec G) rfl (teleFrame_param _ _ d ps c e hl)
    (fun t h r s' hts htv htr => hst ps c i e FT hl hty hfit hei hFT t h r s' hts htv htr)
    (G.hspine c i FT hFT) (fun v hv => hv) _ r s' hrun
  rw [ftyP_eq, hFT]
  dsimp only
  cases G.hspine c i FT hFT with
  | tind n as M hM hargs =>
    rw [semP_tind, hM] at hsem
    rw [itpP_tind, hM]
    by_cases hMd : M = d
    · subst hMd; simp only [if_true] at hsem ⊢; rw [hsem]; rfl
    · simp only [if_neg hMd] at hsem ⊢; rw [hsem]; rfl
  | _ =>
    rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), hsem]
    rfl

end Ochr.Meaning.DataModel.Exists.Knot
