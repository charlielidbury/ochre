import Ochr.Meaning.Steps.ParFacts

/-!
# The read of a parameter: a variable holding an unknown of type `Nat` (lead13)

`I`'s body `S(n)` reads `n ↦ σ₀`, an unknown (the checker moves it: `n ↦ ⊥` after). `varAbs_core` is
`ColumnRead.var_core` for a binding holding `.abs σ` at `Nat`, `σ` of type `Nat` in Δ: the strict read
returns `ρ σ`, a member of `Nat` by the typed assignment. It assumes `VarNumAInv` and `InvNumA`.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- An unknown in flight names only itself. A state with it parked names what the state did, and the
unknown. -/
theorem refd_withTempT_to {st st₀ : MState} {v : Value} {T? : Option Value} (ha : st.absTy = st₀.absTy)
    (hb : ∀ σ, st.norm.Refd σ → st₀.norm.Refd σ) (hv : ∀ σ, v.hasAbs σ = true → st₀.norm.Refd σ) :
    ∀ σ, (st.withTempT v T?).norm.Refd σ → st₀.norm.Refd σ := by
  intro σ h
  induction h with
  | val w hw hab =>
    rcases values_withTempT_norm st v T? w hw with hw | rfl
    · exact hb _ (.val w hw hab)
    · exact hv _ hab
  | ty f i b T hb' hT hab =>
    rw [binds_withTempT_norm] at hb'
    exact hb _ (.ty f i b T hb' hT hab)
  | lazyTy f i b P ws j hb' hT hab =>
    rw [binds_withTempT_norm] at hb'
    exact hb _ (.lazyTy f i b P ws j hb' hT hab)
  | goal G hG hab => exact hb _ (.goal G hG hab)
  | neutral n σ' hn hab => exact hb _ (.neutral n σ' hn hab)
  | eta σ' w he hab => exact hb _ (.eta σ' w he hab)
  | dep σ' T _ hT hab ih =>
    refine .dep σ' T ih ?_ hab
    have : (st.withTempT v T?).norm.absTy = st₀.norm.absTy := ha
    rw [← this]; exact hT

theorem abs_hasAbs (σ : Nat) : (Value.abs σ).hasAbs σ = true := by
  simp only [Value.hasAbs, Value.anyAtom]
  first | rfl | simp [BEq.beq, Value.beq] | (unfold BEq.beq; simp [Value.beq])

theorem abs_hasAbs_eq {σ σ' : Nat} (h : (Value.abs σ).hasAbs σ' = true) : σ' = σ := by
  simp only [Value.hasAbs, Value.anyAtom] at h
  first | (simp [BEq.beq, Value.beq] at h; omega) | (unfold BEq.beq at h; simp [Value.beq] at h; omega)

theorem abs_inertA (σ : Nat) : (Value.abs σ).InertA :=
  ⟨fun P _ _ _ _ ha => by simp [Value.anyAtom, ha σ], fun _ => rfl, fun _ _ _ => by simp [Value.sitesOf], rfl⟩

/-- A variable holding an unknown of type `Nat`, itself stored at `Nat`. -/
def AbsVar (i : Nat) (st : MState) : Prop :=
  ∃ f j b σ, ckVarPos st.env i = some (.bind f j) ∧ st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧
    b.val = .abs σ ∧ b.ty = some .tNat ∧ st.absTy[σ]? = some .tNat

theorem AbsVar.of_kern {i : Nat} {st st' : MState} (hk : Kern st st') (h : AbsVar i st) : AbsVar i st' := by
  obtain ⟨f, j, b, σ, h1, h2, h3, h4, h5⟩ := h
  refine ⟨f, j, b, σ, ?_, ?_, h3, h4, by rw [← hk.absTy]; exact h5⟩
  · rw [← ckVarPos_erase, ← hk.env, ckVarPos_erase]; exact h1
  · rw [← lookup_erase, ← hk.env, lookup_erase]; exact h2

/-- The typed assignment gives an unknown of type `Nat` that the state names a number. -/
theorem asg_abs_nat {K : RunCtx} {ρ : Assignment} {st : MState} (ha : Asg K ρ st.norm) {σ : Nat}
    (hR : st.norm.Refd σ) (hT : st.absTy[σ]? = some .tNat) : ∃ m, ρ σ = .el0 Nat m := by
  have hlt : σ < st.norm.absTy.size := by
    show σ < st.absTy.size
    rcases Nat.lt_or_ge σ st.absTy.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hT; cases hT
  have hm := ha.asg.mem σ hR hlt
  have e : MState.absTyM K.dm K.M K.Γ ρ st.norm σ = TyM.nat := by
    unfold MState.absTyM; rw [show st.norm.absTy[σ]? = some .tNat from hT]; rfl
  rw [e] at hm
  obtain ⟨m, hm⟩ := hm
  exact ⟨m, hm.symm⟩

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The read of a variable holding an unknown of type `Nat`** (`ColumnRead.var_core` with `.abs σ`
for a number): the strict read returns `ρ σ`, a number by the typed assignment, at the binding's
type; the checker's value means it; the states after are related. -/
theorem varAbs_core (hV : VarNumAInv) (hN : InvNumA) {n i : Nat} :
    CoreSim K ρ φ (n + 1) (.place (.var i)) (AbsVar i) := by
  intro st st' typed hint v T? s π ⟨f, j, b, σ, hpos, hb, hbv, hty, hσT⟩ _ hm htn _ _ hp hr hS hv hab hnh hfl hok hD bh h
  obtain ⟨rfl, hT, -, hm', st₁, hq, hki, hcopy, hmove⟩ :=
    hV n typed i hint st st' bh v T? f j b K.D hm hpos hb (by rw [hbv]; exact .abs σ) (by rw [hty]; rfl) hD h
  have hres : resolve s (.var i) = some (.bind f j, []) := rel_resolve_ck K ρ φ st s π (.var i) _ hr hpos
  have hvb : valAt st.env (.bind f j) = b.val := by
    rw [valAt_bind_eq]; rcases hfr : st.env[f]? with _ | fr
    · rw [hfr] at hb; cases hb
    · rw [hfr] at hb; simp only [Option.bind_some] at hb; simp [hb]
  have hns : ∀ l, (valAt st.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by
    rw [hvb, hbv]; simp [Value.sitesOf]
  have hacc : s.access (.bind f j) (dataHit []) = s := access_noSites (rel_noSites_at hr hns)
  have hposA : Pos.bind f j ∈ allPos st.env := (lookup_pos hb).1
  have hRσ : st.norm.Refd σ := .val (.abs σ) (by
    show _ ∈ Env.values st.env.erase
    rw [values_erase]; exact List.mem_map.mpr ⟨_, hposA, by rw [hvb, hbv]⟩) (abs_hasAbs σ)
  obtain ⟨m, hmρ⟩ := asg_abs_nat hp.asg hRσ hσT
  have hval : s.valAt (.bind f j) (s.typedFuture φ) = .el0 Nat m := by
    rw [← hr.sim.1 (s.typedFuture φ) ⟨relF_typedFuture φ s, hr.typedFuture_typed φ⟩ (.bind f j) (by simp [IsTemp])]
    show Env.mean K.dm K.M K.Γ ρ _ st.env (.bind f j) = _
    simp only [Env.mean, hb]; rw [hbv]; exact hmρ
  obtain ⟨hposS, htyS⟩ := rel_bind_ty hr hb
  have htyN : (s.tyAt (.bind f j)).m = TyM.nat := by
    rw [htyS]; simp only [Env.hintAt, hb, hty]; rfl
  have hshS : s.shape (.bind f j) = none := by
    rcases e : s.shape (.bind f j) with _ | l'
    · rfl
    · obtain ⟨l, h1, -⟩ := hr.sim.2.2.1 (.bind f j) l' (by simp [IsTemp]) e
      have : Env.shape st.env (.bind f j) = some l := h1
      simp only [Env.shape, hvb, hbv] at this
      cases this
  have hsc : scopeOf s = DecideScope.topReadings st := scopeOf_rel hr
  have hco : contentOf K φ (.var i) s = some ((.el0 Nat m, s.tyAt (.bind f j), .bind f j, []), s) := by
    unfold contentOf; rw [hres]; simp only; rw [hacc]; simp [Sem.follow, hval]
  have hrg : ReadGood K.dm.read (s.tyAt (.bind f j)).m (.el0 Nat m) := .inl (by rw [htyN]; exact ⟨m, rfl⟩)
  have hrun : runT K ρ φ st.curTail (hintM K ρ hint) (.place (.var i)) s =
      readPlace K φ (.var i) (K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var i))) s := by
    have hcok : ContentOk K φ (.var i) s := by
      unfold ContentOk; rw [hres]; exact accessOk_noSites (rel_noSites_at hr hns)
    rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl, hsc]
    show SM.guarded _ _ s = _; unfold SM.guarded; rw [if_pos hcok]
  have hwhole : (Sem.el0 Nat m).whole := by simp [Sem.whole]
  have hlab : ∀ l, st.Occurs l → l < st.nextLoan := hp.labels
  have hr₁ : Rel K ρ φ π st₁ s := hr.of_quiet hq hlab
  have ha₁ : Asg K ρ st₁.norm := Asg.of_quiet hq hp.asg hp.inv.wf6
  have hσlt : σ < st.absTy.size := by
    rcases Nat.lt_or_ge σ st.absTy.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hσT; cases hσT
  have hσT₁ : st₁.absTy[σ]? = some .tNat := by rw [hq.absTy σ hσlt]; exact hσT
  have hb₁ : st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
    rw [← lookup_erase, ← hq.env, lookup_erase]; exact hb
  have hvb₁ : valAt st₁.env (.bind f j) = b.val := by rw [← valAt_erase, ← hq.env, valAt_erase]; exact hvb
  have hRσ₁ : st₁.norm.Refd σ := .val (.abs σ) (by
    show _ ∈ Env.values st₁.env.erase
    rw [values_erase]; exact List.mem_map.mpr ⟨_, (lookup_pos hb₁).1, by rw [hvb₁, hbv]⟩) (abs_hasAbs σ)
  have hmeanV : ∀ ψ hint', meanV K ρ ψ hint' b.val = .el0 Nat m := fun ψ hint' => by rw [hbv]; exact hmρ
  have hagree : ∀ T, T? = some T → StrAgree K ρ T { s.tyAt (.bind f j) with label := none } := by
    intro T e
    have := hT T e; rw [hty] at this; cases this
    show _ = (s.tyAt (.bind f j)).m; rw [htyN]; rfl
  have hheld : Value.heldLabel b.val = none := by rw [hbv]; rfl
  have hinA : b.val.InertA := by rw [hbv]; exact abs_inertA σ
  have hNA : ∀ st₂ : MState, st₂.absTy = st₁.absTy → NumAt st₂ b.val := fun st₂ he =>
    ⟨by rw [hbv]; exact .abs σ, fun σ' h' => by rw [hbv] at h'; rw [abs_hasAbs_eq h', he]; exact hσT₁⟩
  have hvR : ∀ σ', b.val.hasAbs σ' = true → st₁.norm.Refd σ' := fun σ' h' => by
    rw [hbv] at h'; rw [abs_hasAbs_eq h']; exact hRσ₁
  cases hc : K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var i))
  · -- a move: `⊥` at the binding
    have hk := hmove hc
    have hst : readPlace K φ (.var i) false s = some ((.el0 Nat m, { s.tyAt (.bind f j) with label := none }),
        s.setAt (.bind f j) fun φ' =>
          (Sem.updAt K.dm K.Γ (s.tyAt (.bind f j)) (fun _ => .moved) [] (s.valAt (.bind f j) φ')).getD .err) := by
      have hset : setContent K φ (.bind f j) [] .moved s = some (⟨⟩, s.setAt (.bind f j) fun φ' =>
          (Sem.updAt K.dm K.Γ (s.tyAt (.bind f j)) (fun _ => .moved) [] (s.valAt (.bind f j) φ')).getD .err) := by
        unfold setContent; rw [if_pos (by intro ψ _; rfl)]
      unfold readPlace
      rw [hco]
      simp only [Option.bind_some, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_nil,
        hshS, hset, bind, Option.bind]
      rfl
    have hwf1 : WF1 st₁.env := by
      rw [← wf1_erase, ← hq.env, wf1_erase]; exact (wf1_erase st.env).mp hp.inv.1
    have hpos₁ : Pos.bind f j ∈ allPos st₁.env := (lookup_pos hb₁).1
    have hR := botWrite_rel K ρ φ st₁ s π f j [] .bot hr₁ hwf1 hpos₁ hposS
      (by rw [Value.updAt])
      (fun _ => by simp only [Env.shape, hvb₁, hbv])
      (fun l _ x hx hxp => by
        have := mem_sitesOf_at hx hxp
        rw [hvb₁, hbv] at this; simp [Value.sitesOf] at this)
      ⟨by rw [hvb₁, hbv]; rfl, by rw [hvb₁, hbv]; rfl⟩
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
    have hinv : Inv K.D K.Γ (st'.withTempT b.val T?).norm := by
      have h₁ : Inv K.D K.Γ st₁.norm := hki K.D K.Γ hp.inv
      refine hN.push K.D K.Γ st' _ _ (hNA st' hk.absTy.symm) ?_
      rw [← hk.norm]
      exact hN.setBot K.D K.Γ st₁ f j (by rw [hvb₁, hbv]; exact .abs σ) h₁
    refine ⟨ρ, K.Δ, π, _, _, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, by rw [hrun, hc]; exact hst, hmeanV _ _, hagree,
      by simp [hheld], ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · exact ha₁.of_refd hk.absTy.symm hk.neutrals.symm hk.etaRefs.symm hk.refs.symm hk.goal.symm
          (refd_withTempT_to hk.absTy.symm (fun σ' h' => hRm σ' (by rw [hk.norm]; exact h')) hvR)
    · exact rel_withTempT_inertA (hR.of_kern hk) hinA T?
  · -- a copy: nothing changes
    have hk := hcopy hc
    have hst : readPlace K φ (.var i) true s = some ((.el0 Nat m, { s.tyAt (.bind f j) with label := none }), s) := by
      unfold readPlace
      rw [hco]
      simp only [hwhole, hrg, not_true_eq_false, if_false, if_true, bind, Option.bind]
    have hinv : Inv K.D K.Γ (st'.withTempT b.val T?).norm := by
      refine hN.push K.D K.Γ st' _ _ (hNA st' hk.absTy.symm) ?_
      rw [← hk.norm]; exact hki K.D K.Γ hp.inv
    refine ⟨ρ, K.Δ, π, _, s, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, by rw [hrun, hc]; exact hst, hmeanV _ _, hagree,
      by simp [hheld], ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · exact ha₁.of_refd hk.absTy.symm hk.neutrals.symm hk.etaRefs.symm hk.refs.symm hk.goal.symm
          (refd_withTempT_to hk.absTy.symm (fun σ' h' => by rw [← hk.norm] at h'; exact h') hvR)
    · exact rel_withTempT_inertA (hr₁.of_kern hk) hinA T?

end

end Ochr.Meaning.Steps.Form
