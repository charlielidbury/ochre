import Ochr.Meaning.Steps.ParBody
import Ochr.Meaning.Steps.CallGuards

/-!
# The callee's body, run UNTYPED in place: the step in the form (lead15, 2026-11-21; docs/31 D127)

At a call of a known function the checker runs the callee's body untyped, in a frame pushed on the
caller's, the parameter LAZILY typed (`ty = none`, its type deferred to the Π-type at the arguments;
`Steps/CallGuards.lean`). This file states the step for `I`'s body `S(#0)` there, in the form
(`Column.EvalSim` at `typed = false`), and proves it: the first untyped run and the first lazily typed
binding the form meets.

What fits as the form stands: `eval_sim`'s untyped hypothesis (`hok`, the strict run succeeds) is not
used: the strict run of `S(#0)` from a related state succeeds by itself (the read is a member of
`Nat` by the relation, whose type for the lazily typed binding is its deferred type through
`codeMeaning.paramTy`, `Env.hintAt`); the read in an untyped run returns NO type, and `Out`'s type
conjunct asks nothing then; `S` returns `Nat`. Nothing in `Sim`/`Out` had to change.

Assumes one fact about the checker, `BodyLazyInv` (stated here, `#guard`ed), and `InvNumA`.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

namespace CallBody

/-- **The untyped run of `I`'s body from a callee frame** (a fact about the checker alone, assumed; the
machine lane's): where `#0` resolves to a binding holding a closed numeral whose type is DEFERRED
(`ty = none`: the callee's parameter as `runBodyCore` binds it), every successful UNTYPED `eval` of
`S(#0)` (in the plain mode, no reading handed down) returns `S` of the numeral at `Nat`; it is quiet
and keeps the invariant up to the read, which copies or moves `#0` as the aligned copy decision says.
The read itself returns no type (`Steps/CallGuards.lean`); `S` gives `Nat`. `VarNumAInv` does not cover
the read: it asks `b.ty.isSome`. -/
def BodyLazyInv : Prop :=
  ∀ (n : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value) (f j : Nat)
    (b : Binding) (D : Decisions),
    Mode st → st.tailDecl = none → ckVarPos st.env 0 = some (.bind f j) →
    st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.val.Num → b.ty = none → DecTab D st' →
    Runs (Ochr.eval n false bodyI hint) st bh (v, T?) st' →
    v = .succ b.val ∧ T? = some .tNat ∧ ∃ st₁, Quiet st st₁ ∧ KeepsInv st st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var 0)) = true → Kern st₁ st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var 0)) = false →
        Kern { st₁ with env := Env.setAtE st₁.env (.bind f j) .bot } st')

namespace Guards

open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk)
open CallGuards (stCJ calleeOk)

/-- `stCJ` with the parameter holding `w`. -/
def withArg (w : Value) : MState :=
  { stCJ with env := stCJ.env.set! 1 { binds := #[stCJ.env[1]!.binds[0]!, { stCJ.env[1]!.binds[1]! with val := w }] } }

-- at `Z` (`J`) and `S(Z)` (`J2`), with any hint, in tail position or not: `S` of the numeral at `Nat`,
-- the parameter moved (the copy decision at `.other` is false), nothing else changed
#guard [Value.zero, .succ .zero].all fun w => [none, some .tNat].all fun h => [true, false].all fun tl =>
  let st := { withArg w with tailNext := tl }
  isOk (Ochr.eval 100 false bodyI h) st 100000 &&
  outVal (Ochr.eval 100 false bodyI h) st 100000 == (.succ w, some .tNat) &&
  calleeOk (outSt (Ochr.eval 100 false bodyI h) st 100000) .bot
-- the read alone returns no type
#guard (outVal (Ochr.evalCore 100 false (.place (.var 0)) none) (withArg (.succ .zero)) 100000).2.isNone

end Guards

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The callee's state as the step needs it: `#0` resolves to a binding holding a closed numeral, its
type deferred, read `Nat` by the context (`Env.hintAt` through `codeMeaning.paramTy`); the top frame
reads `R`; no reading handed down. -/
def LazyNum (K : RunCtx) (ρ : Assignment) (R : List DeclInfo) (st : MState) : Prop :=
  (∃ f j b, ckVarPos st.env 0 = some (.bind f j) ∧ st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧
    b.val.Num ∧ b.ty = none ∧ (Env.hintAt K.dm K.M K.Γ ρ st.env (.bind f j)).m = TyM.nat) ∧
  DecideScope.topReadings st = R ∧ st.tailDecl = none

theorem num_mean {v : Value} (h : v.Num) : ∃ m : Nat, ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS),
    meanV K ρ φ hint v = .el0 Nat m := by
  induction h with
  | zero => exact ⟨0, fun _ _ _ _ => rfl⟩
  | succ _ ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, fun K ρ φ hint => ?_⟩
    show (meanV K ρ φ (.plain TyM.nat) _).succ = _
    rw [hm, Sem.succ, Sem.asNat_el0]

/-- **The untyped body step in place, in the form** (`EvalSim` at `typed = false`): from a callee state
whose parameter is lazily typed and holds a closed numeral read `Nat` by the context, and every
reference state related to it and good, the strict run of `S(#0)` succeeds with `S` of the numeral,
at `Nat`, and the states after (the parameter moved or kept, as the aligned copy decision says) are
related, with `Pre` again. The untyped hypothesis `hok` is not used. Assumes `BodyLazyInv` (checker)
and `InvNumA` (checker, read and judged true). -/
theorem bodyLazy_sim (hB : BodyLazyInv) (hN : InvNumA) {R : List DeclInfo} (hd : ParDecI K.D R) :
    ∀ n, EvalSim K ρ φ n bodyI (LazyNum K ρ R) (· = false) := by
  intro n st st' typed hint v T? s π ⟨⟨f, j, b, hpos, hb, hbv, hty, htyK⟩, hR, htd⟩ htyp hm _ hp hr _ _ _ _ hfl _ hD bh h
  subst htyp
  obtain ⟨rfl, rfl, st₁, hq, hki, hcopy, hmove⟩ := hB n hint st st' bh v T? f j b K.D hm htd hpos hb hbv hty hD h
  have hres : resolve s (.var 0) = some (.bind f j, []) := rel_resolve_ck K ρ φ st s π (.var 0) _ hr hpos
  have hvb : valAt st.env (.bind f j) = b.val := by
    rw [valAt_bind_eq]; rcases hfr : st.env[f]? with _ | fr
    · rw [hfr] at hb; cases hb
    · rw [hfr] at hb; simp only [Option.bind_some] at hb; simp [hb]
  have hns : ∀ l, (valAt st.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by
    rw [hvb]; exact hbv.sitesOf l _ []
  have hacc : s.access (.bind f j) (dataHit []) = s := access_noSites (rel_noSites_at hr hns)
  obtain ⟨m, hmv⟩ := num_mean hbv
  have hval : s.valAt (.bind f j) (s.typedFuture φ) = .el0 Nat m := by
    rw [← hr.sim.1 (s.typedFuture φ) ⟨relF_typedFuture φ s, hr.typedFuture_typed φ⟩ (.bind f j) (by simp [IsTemp])]
    show Env.mean K.dm K.M K.Γ ρ _ st.env (.bind f j) = _
    simp only [Env.mean, hb]; exact (meanV_eq_mean K ρ _ _ _).trans (hmv _ _ _ _)
  obtain ⟨hposS, htyS⟩ := rel_bind_ty hr hb (by simp [Binding.piTyped, hty])
  have htyN : (s.tyAt (.bind f j)).m = TyM.nat := by rw [htyS]; exact htyK
  have hshS : s.shape (.bind f j) = none := by
    rcases e : s.shape (.bind f j) with _ | l'
    · rfl
    · obtain ⟨l, h1, -⟩ := hr.sim.2.2.1 (.bind f j) l' (by simp [IsTemp]) e
      have : Env.shape st.env (.bind f j) = some l := h1
      simp only [Env.shape, hvb] at this
      split at this
      · rename_i w heq; exact absurd heq (hbv.not_borrow _ _)
      · cases this
  have hsc : scopeOf s = R := by rw [scopeOf_rel hr, hR]
  have hco : contentOf K φ (.var 0) s = some ((.el0 Nat m, s.tyAt (.bind f j), .bind f j, []), s) := by
    unfold contentOf; rw [hres]; simp only; rw [hacc]; simp [Sem.follow, hval]
  have hrg : ReadGood K.dm.read (s.tyAt (.bind f j)).m (.el0 Nat m) := .inl (by rw [htyN]; exact ⟨m, rfl⟩)
  have hrun0 : runT K ρ φ false (.plain TyM.nat) (.place (.var 0)) s =
      readPlace K φ (.var 0) (K.D.copy (K.D.placeDecl R (.var 0))) s := by
    have hcok : ContentOk K φ (.var 0) s := by
      unfold ContentOk; rw [hres]; exact accessOk_noSites (rel_noSites_at hr hns)
    rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hsc, hd.1]
    show SM.guarded _ _ s = _; unfold SM.guarded; rw [if_pos hcok]
  have hwhole : (Sem.el0 Nat m).whole := by simp [Sem.whole]
  have hbody : ∀ s₁ : SState, readPlace K φ (.var 0) (K.D.copy (K.D.placeDecl R (.var 0))) s =
      some ((.el0 Nat m, { s.tyAt (.bind f j) with label := none }), s₁) →
      runT K ρ φ st.tailNext (hintM K ρ hint) bodyI s = some ((.el0 Nat (m + 1), .plain TyM.nat), s₁) := by
    intro s₁ hrd
    unfold bodyI
    rw [runT_succ _ _ _ s hfl]
    have hb' : (runT K ρ φ false (.plain TyM.nat) (.place (.var 0)) >>= fun x : Res => match x with
        | (v, _) => (pure (v.succ, TyS.plain TyM.nat) : SM Res)) s = some (((Sem.el0 Nat m).succ, .plain TyM.nat), s₁) := by
      simp only [Bind.bind]; rw [hrun0, hrd]; rfl
    unfold SM.strictS
    rw [hb']
    have hsu : (Sem.el0 Nat m).succ = .el0 Nat (m + 1) := by rw [Sem.succ, Sem.asNat_el0]
    have hc : (Sem.el0 Nat m).succ ∈ₛ[K.dm.read] (TyS.plain TyM.nat).m := by rw [hsu]; exact ⟨m + 1, rfl⟩
    dsimp only; rw [if_pos hc, hsu]
  have hlab : ∀ l, st.Occurs l → l < st.nextLoan := hp.labels
  have hr₁ : Rel K ρ φ π st₁ s := hr.of_quiet hq hlab
  have ha₁ : Asg K ρ st₁.norm := Asg.of_quiet hq hp.asg hp.inv.wf6
  have hb₁ : st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
    rw [← lookup_erase, ← hq.env, lookup_erase]; exact hb
  have hvb₁ : valAt st₁.env (.bind f j) = b.val := by rw [← valAt_erase, ← hq.env, valAt_erase]; exact hvb
  have hsN : (Value.succ b.val).Num := .succ hbv
  have hNA : ∀ st₂ : MState, NumAt st₂ (Value.succ b.val) := fun st₂ =>
    ⟨hsN.numA, fun σ h' => by rw [hsN.hasAbs σ] at h'; cases h'⟩
  have hvR : ∀ σ, (Value.succ b.val).hasAbs σ = true → st₁.norm.Refd σ := fun σ h' => by
    rw [hsN.hasAbs σ] at h'; cases h'
  have hmean : ∀ ψ, meanV K ρ ψ (.plain TyM.nat) (Value.succ b.val) = .el0 Nat (m + 1) := fun ψ => by
    show (meanV K ρ ψ (.plain TyM.nat) b.val).succ = _
    rw [hmv, Sem.succ, Sem.asNat_el0]
  cases hc : K.D.copy (K.D.placeDecl R (.var 0))
  · -- a move: `⊥` at the binding
    have hk := hmove (by rw [hR]; exact hc)
    have hst : readPlace K φ (.var 0) false s = some ((.el0 Nat m, { s.tyAt (.bind f j) with label := none }),
        s.setAt (.bind f j) fun φ' =>
          (Sem.updAt K.dm K.Γ (s.tyAt (.bind f j)) (fun _ => .moved) [] (s.valAt (.bind f j) φ')).getD .err) := by
      have hset : setContent K φ (.bind f j) [] .moved s = some (⟨⟩, s.setAt (.bind f j) fun φ' =>
          (Sem.updAt K.dm K.Γ (s.tyAt (.bind f j)) (fun _ => .moved) [] (s.valAt (.bind f j) φ')).getD .err) := by
        unfold setContent; rw [if_pos (by intro ψ _; rfl)]
      unfold readPlace
      rw [hco]
      simp only [hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_nil,
        hshS, hset, bind, Option.bind]
      rfl
    have hwf1 : WF1 st₁.env := by
      rw [← wf1_erase, ← hq.env, wf1_erase]; exact (wf1_erase st.env).mp hp.inv.1
    have hpos₁ : Pos.bind f j ∈ allPos st₁.env := (lookup_pos hb₁).1
    have hRb := botWrite_rel K ρ φ st₁ s π f j [] .bot hr₁ hwf1 hpos₁ hposS
      (by rw [Value.updAt])
      (fun _ => by
        simp only [Env.shape, hvb₁]
        split
        · rename_i w heq; exact absurd heq (hbv.not_borrow _ _)
        · rfl)
      (fun l _ x hx hxp => by
        have := mem_sitesOf_at hx hxp
        rw [hvb₁, hbv.sitesOf] at this; simp at this)
      ⟨by rw [hvb₁]; exact hbv.anyAtom rfl (fun _ => rfl), by rw [hvb₁]; exact hbv.anyAtom rfl (fun _ => rfl)⟩
      (fun _ => by rw [NatAlong]; trivial)
    have hRm : ∀ σ', ({ st₁ with env := Env.setAtE st₁.env (.bind f j) .bot } : MState).norm.Refd σ' →
        st₁.norm.Refd σ' := by
      refine refd_sub rfl rfl rfl rfl ?_ ?_ ?_
      · intro w hw σ' hσ'
        rcases mem_values_setAtE hw with rfl | hw'
        · cases hσ'
        · exact ⟨w, hw', hσ'⟩
      · intro f' i' b' T σ' hb' hT hσ'
        obtain ⟨b'', hb'', hty'', -⟩ := lookup_setAtE hb'
        exact .ty f' i' b'' T (by rw [show st₁.norm.env = st₁.env.erase from rfl, lookup_erase]; exact hb'')
          (by rw [hty'']; exact hT) hσ'
      · intro f' i' b' P ws j' σ' hb' hl hσ'
        obtain ⟨b'', hb'', -, hlz''⟩ := lookup_setAtE hb'
        exact .lazyTy f' i' b'' P ws j' (by rw [show st₁.norm.env = st₁.env.erase from rfl, lookup_erase]; exact hb'')
          (by rw [hlz'']; exact hl) hσ'
    have hinv : Inv K.D K.Γ (st'.withTempT (.succ b.val) (some .tNat)).norm := by
      have h₁ : Inv K.D K.Γ st₁.norm := hki K.D K.Γ hp.inv
      refine hN.push K.D K.Γ st' _ _ (hNA st') ?_
      rw [← hk.norm]
      exact hN.setBot K.D K.Γ st₁ f j (by rw [hvb₁]; exact hbv.numA) h₁
    refine ⟨ρ, K.Δ, π, _, _, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, hbody _ (by rw [hc]; exact hst), hmean _,
      fun T hT => by cases hT; exact strAgree_tNat, rfl, ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · exact ha₁.of_refd hk.absTy.symm hk.neutrals.symm hk.etaRefs.symm hk.refs.symm hk.goal.symm
          (refd_withTempT_to hk.absTy.symm (fun σ' h' => hRm σ' (by rw [hk.norm]; exact h')) hvR)
    · exact rel_withTempT_inertA (hRb.of_kern hk) hsN.inert.toA _
  · -- a copy: nothing changes
    have hk := hcopy (by rw [hR]; exact hc)
    have hst : readPlace K φ (.var 0) true s = some ((.el0 Nat m, { s.tyAt (.bind f j) with label := none }), s) := by
      unfold readPlace
      rw [hco]
      simp only [hwhole, hrg, not_true_eq_false, if_false, if_true, bind, Option.bind]
    have hinv : Inv K.D K.Γ (st'.withTempT (.succ b.val) (some .tNat)).norm := by
      refine hN.push K.D K.Γ st' _ _ (hNA st') ?_
      rw [← hk.norm]; exact hki K.D K.Γ hp.inv
    refine ⟨ρ, K.Δ, π, _, s, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, hbody _ (by rw [hc]; exact hst), hmean _,
      fun T hT => by cases hT; exact strAgree_tNat, rfl, ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · exact ha₁.of_refd hk.absTy.symm hk.neutrals.symm hk.etaRefs.symm hk.refs.symm hk.goal.symm
          (refd_withTempT_to hk.absTy.symm (fun σ' h' => by rw [← hk.norm] at h'; exact h') hvR)
    · exact rel_withTempT_inertA (hr₁.of_kern hk) hsN.inert.toA _

end

end CallBody

end Ochr.Meaning.Steps.Form
