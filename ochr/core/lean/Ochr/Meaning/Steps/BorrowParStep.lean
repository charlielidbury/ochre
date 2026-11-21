import Ochr.Meaning.Steps.BorrowParRun
import Ochr.Meaning.Steps.ParRead

/-!
# `W`'s body step in the form (lead19, 2026-11-21; docs/31 D142)

`def W (r : &Nat) : Nat := clone(*r)`. The step: from every reference state related to a checker state with `stW`'s
kernel (and good), the reference's run of `clone(*r)` simulates the checker's typed `eval` (`Sim`, `Steps/Form.lean`).

Where the borrow parameter's label is used. The checker's `r ↦ borrow₀ σ0` means `σ0`'s number (a borrow means its
content); on the reference side `r`'s position holds the argument, labelled `π 0`. The read of `*r` resolves to `r`'s
position through `*`; its [Access] ends the live labels with a site there, and there are none: the only live label is
`π 0`, whose one site is the cell in frame 0 on both sides (`Rel.sites`, D138). The content is read at the TYPED future
(`SState.typedFuture`: each live label its record), and `r`'s meaning does not read label `π 0` at all (it is the
content itself), so the record is not consulted by this step: `clone(*r)` reads `ρ σ0`. The state is unchanged on both
sides: `clone` reads in place, and `r` keeps the borrow.

Assumes 2 facts about the checker: `BodyWInv` (the body's typed `eval`: value `σ0`, type `Nat`, end kernel `stW`) and
`InvNumA` (its `push`: the invariant survives pushing an unknown of type `Nat` as the value in flight). No model fact.
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

theorem lookup_stW_r {st : MState} (hk : Kern stW st) :
    st.env[1]?.bind (fun fr : Frame => fr.binds[1]?) = some (rB (.borrow 0 (.abs 0))) := by
  rw [← lookup_erase, ← hk.env, lookup_erase]; rfl

theorem ckVarPos_stW {st : MState} (hk : Kern stW st) : ckVarPos st.env 0 = some (.bind 1 1) := by
  rw [← ckVarPos_erase, ← hk.env, ckVarPos_erase]; rfl

theorem valAt_stW_r {st : MState} (hk : Kern stW st) : valAt st.env (.bind 1 1) = .borrow 0 (.abs 0) := by
  rw [← valAt_erase, ← hk.env, valAt_erase]; rfl

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **`W`'s body, simulated** (`Sim`): for every checker run of `clone(*r)`'s typed `eval` from a state with `stW`'s
kernel, plain mode, no handed-down reading, at decisions that classify the body as neither a statement nor a proof,
every related good reference state runs `clone(*r)` to the number `ρ σ0` at `Nat`, unchanged, related again with `σ0`
in flight. ASSUMES 2 facts about the checker, `BodyWInv` and `InvNumA`; no model fact. -/
theorem body_simW (hB : BodyWInv) (hN : InvNumA) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat}
    {v : Value} {T? : Option Value} (hk : Kern stW st) (hm : Mode st) (htd : st.tailDecl = none)
    (hfl : K.D.flags (DecideScope.topReadings st) bodyW = (false, false))
    (h : Runs (Ochr.eval n true bodyW hint) st bh (v, T?) st') :
    Sim K ρ φ st st' (runT K ρ φ st.tailNext (hintM K ρ hint) bodyW) v T? := by
  obtain ⟨rfl, rfl, hk'⟩ := hB n hint st st' bh v T? hk hm htd h
  have hkk : Kern st st' := hk.symm.trans hk'
  intro s π hp hr _
  have hb := lookup_stW_r hk
  have hvb := valAt_stW_r hk
  have hres : resolve s (.deref (.var 0)) = some (.bind 1 1, [.deref]) :=
    rel_resolve_ck K ρ φ st s π (.deref (.var 0)) _ hr (ckVarPos_stW hk)
  have hns : ∀ l, (valAt st.env (.bind 1 1)).sitesOf l (.bind 1 1) [] = [] := fun l => by
    rw [hvb]; simp [Value.sitesOf]
  have hacc : s.access (.bind 1 1) (dataHit [.deref]) = s := access_noSites (rel_noSites_at hr hns)
  have hposA : Pos.bind 1 1 ∈ allPos st.env := (lookup_pos hb).1
  have hσT : st.absTy[0]? = some .tNat := by rw [← hk.absTy]; rfl
  have hRσ : st.norm.Refd 0 := .val (.borrow 0 (.abs 0)) (by
    show _ ∈ Env.values st.env.erase
    rw [values_erase]; exact List.mem_map.mpr ⟨_, hposA, hvb⟩) (by
      simp only [Value.hasAbs, Value.anyAtom]
      first | rfl | simp [BEq.beq, Value.beq] | (unfold BEq.beq; simp [Value.beq]))
  obtain ⟨m, hmρ⟩ := asg_abs_nat hp.asg hRσ hσT
  have hval : s.valAt (.bind 1 1) (s.typedFuture φ) = .el0 Nat m := by
    rw [← hr.sim.1 (s.typedFuture φ) ⟨relF_typedFuture φ s, hr.typedFuture_typed φ⟩ (.bind 1 1) (by simp [IsTemp])]
    show Env.mean K.dm K.M K.Γ ρ _ st.env (.bind 1 1) = _
    simp only [Env.mean, hb, rB, Value.mean]; exact hmρ
  obtain ⟨-, htyS⟩ := rel_bind_ty hr hb (by rfl)
  have htyN : (s.tyAt (.bind 1 1)).m = TyM.nat := by
    rw [htyS]; simp only [Env.hintAt, hb, rB]; rfl
  have hsc : scopeOf s = DecideScope.topReadings st := scopeOf_rel hr
  have hco : contentOf K φ (.deref (.var 0)) s = some ((.el0 Nat m, { s.tyAt (.bind 1 1) with label := none }, .bind 1 1, [.deref]), s) := by
    unfold contentOf; rw [hres]; simp only; rw [hacc]; simp [Sem.follow, Sem.step, hval]
  have hrg : ReadGood K.dm.read ({ s.tyAt (.bind 1 1) with label := none } : TyS).m (.el0 Nat m) :=
    .inl (by show _ ∈ₛ[_] (s.tyAt (.bind 1 1)).m; rw [htyN]; exact ⟨m, rfl⟩)
  have hwhole : (Sem.el0 Nat m).whole := by simp [Sem.whole]
  have hst : readPlace K φ (.deref (.var 0)) true s =
      some ((.el0 Nat m, { s.tyAt (.bind 1 1) with label := none }), s) := by
    unfold readPlace
    rw [hco]
    simp only [hwhole, hrg, not_true_eq_false, if_false, if_true, bind, Option.bind]
  have hrun : runT K ρ φ st.tailNext (hintM K ρ hint) bodyW s = some ((.el0 Nat m, { s.tyAt (.bind 1 1) with label := none }), s) := by
    have hcok : ContentOk K φ (.deref (.var 0)) s := by
      unfold ContentOk; rw [hres]; exact accessOk_noSites (rel_noSites_at hr hns)
    have hfl' : K.D.flags (scopeOf s) (.prim "clone" [.place (.deref (.var 0))]) = (false, false) := by rw [hsc]; exact hfl
    rw [bodyW, runT]
    show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _
    rw [hfl']
    show SM.guarded _ _ s = _
    unfold SM.guarded; rw [if_pos hcok]; exact hst
  have hNA : NumAt st' (.abs 0) := ⟨.abs 0, fun σ' h' => by rw [abs_hasAbs_eq h', ← hkk.absTy]; exact hσT⟩
  have hinv : Inv K.D K.Γ (st'.withTempT (.abs 0) (some .tNat)).norm := by
    refine hN.push K.D K.Γ st' _ _ hNA ?_
    rw [← hkk.norm]; exact hp.inv
  refine ⟨ρ, K.Δ, π, _, s, ⟨by rw [← hkk.absTy]; exact Nat.le_refl _, by rw [← hkk.nextLoan]; exact Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩,
    hrun, hmρ.symm ▸ rfl, fun T e => ?_, rfl, ?_, ?_⟩
  · cases e; show _ = (s.tyAt (.bind 1 1)).m; rw [htyN]; rfl
  · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
    · show st'.inds = st.inds; rw [← hkk.inds]
    · show st'.globals = st.globals; rw [← hkk.globals]
    · exact hp.asg.of_refd hkk.absTy.symm hkk.neutrals.symm hkk.etaRefs.symm hkk.refs.symm hkk.goal.symm
        (refd_withTempT_to hkk.absTy.symm (fun σ' h' => by rw [← hkk.norm] at h'; exact h')
          (fun σ' h' => by rw [abs_hasAbs_eq h']; exact hRσ))
  · exact rel_withTempT_inertA (hr.of_kern hkk) (abs_inertA 0) _

end

end Ochr.Meaning.Steps.Form.ColumnW
