import Ochr.Meaning.Steps.Column
import Ochr.Meaning.Steps.DropOne
import Ochr.Meaning.Steps.BotWriteRel

/-!
# The column: the read of a variable holding a number (lead7)

`x`, a variable bound to a number at `Nat`, read whole: the checker's [Read] (its [Repack] and access
quiet, a copy or a move by the aligned copy decision) against the strict run's `.place` clause
(`readPlace`: the access, the strict test that the value read is a member of the binding's type, a
copy or a move). Proved for a number in a binding stored at `Nat` (`NumVar`); the general read needs
[Repack]'s soundness (`RepackSound`, stated, for its own owner) for the strict test, and the access
step for a place something is lent at.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-- A number means a number, whatever it is read through. -/
theorem _root_.Ochr.Value.Num.vmean {v : Value} (hv : v.Num) :
    ∃ m : Nat, ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint v = .el0 Nat m := by
  induction hv with
  | zero => exact ⟨0, fun _ _ _ _ _ _ => rfl⟩
  | succ _ ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, fun dm C Γ ρ φ hint => ?_⟩
    show (Value.mean dm C Γ ρ φ (.plain TyM.nat) _).succ = _
    rw [hm, Sem.succ, Sem.asNat_el0]

/-- [Access] at a position no live label is lent at is the identity. -/
theorem access_noSites {s : SState} {pos : Pos} {hit : List Step → Bool}
    (h : ∀ l ∈ s.liveLabels, ∀ x ∈ s.lent l, x.pos ≠ pos) : s.access pos hit = s := by
  have hstep : (s.liveLabels.filter (s.reached pos hit)).foldl SState.endLabel s = s := by
    rw [List.filter_eq_nil_iff.mpr]
    · rfl
    intro l hl
    simp only [SState.reached, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro x hx hpos
    exact absurd hpos (h l hl x hx)
  unfold SState.access
  dsimp only
  generalize List.range s.liveLabels.length = L
  induction L with
  | nil => rfl
  | cons _ L ih => rw [List.foldl_cons, hstep, ih]

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **No reference label is lent at a position whose checker value has no site**, at related states. -/
theorem rel_noSites_at {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s) {pos : Pos}
    (hns : ∀ l, (valAt st.env pos).sitesOf l pos [] = []) : ∀ l ∈ s.liveLabels, ∀ x ∈ s.lent l, x.pos ≠ pos := by
  intro l' hl' x hx hxp
  obtain ⟨l, hl, rfl⟩ := rel_live_ref K ρ φ st s π hr hl'
  have hx' := (hr.sites l hl x).mp hx
  have := mem_sitesOf_at hx' hxp
  rw [hns] at this; cases this

/-- **The reference's binding is the checker's**: a binding of the checker's state is a position of the
reference's, at a type of the same code as the checker's stored type. -/
theorem rel_bind_ty {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s) {f j : Nat} {b : Binding}
    (hb : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    Pos.bind f j ∈ s.positions ∧ (s.tyAt (.bind f j)).m = (Env.hintAt K.dm K.M K.Γ ρ st.env (.bind f j)).m := by
  have hsk := hr.skel
  have e := congrArg (fun L => L[f]?.bind fun l => l[j]?) hsk
  simp only [List.getElem?_map, Option.bind_map, Function.comp_def, List.getElem?_map] at e
  rcases hfr : st.env[f]? with _ | fr
  · rw [hfr] at hb; cases hb
  rw [hfr] at hb
  simp only [Option.bind_some] at hb
  have hsl : (SM' K ρ st).env[f]?.bind (fun sf : SFrame => sf.binds[j]?) =
      some { ty := Env.hintAt K.dm K.M K.Γ ρ st.env (.bind f j),
             val := fun ψ => Env.mean K.dm K.M K.Γ ρ ψ st.env (.bind f j), decl := b.decl } := by
    simp only [SM', MState.sstate, List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList, hfr,
      Option.map_some, Option.bind_some, Nat.zero_add, hb]
  have e' : ((SM' K ρ st).env[f]?.bind (fun sf : SFrame => sf.binds[j]?)).map bindSkel =
      (s.env[f]?.bind (fun sf : SFrame => sf.binds[j]?)).map bindSkel := by
    cases h1 : (SM' K ρ st).env[f]? <;> cases h2 : s.env[f]? <;> simp_all
  rw [hsl] at e'
  rcases hs : s.env[f]?.bind (fun sf : SFrame => sf.binds[j]?) with _ | sb
  · rw [hs] at e'; cases e'
  rw [hs] at e'
  simp only [Option.map_some, Option.some.injEq, bindSkel, Prod.mk.injEq] at e'
  refine ⟨(SState.mem_positions s _).mpr (by simp [SState.lookup, hs]), ?_⟩
  show (match s.env[f]?.bind (·.binds[j]?) with | some b => b.ty | none => .plain TyM.err).m = _
  rw [hs]; exact e'.1.symm

end

/-! ## Helpers about the checker's environment -/

theorem lookup_erase (env : Env) (f j : Nat) :
    env.erase[f]?.bind (fun fr : Frame => fr.binds[j]?) = env[f]?.bind (fun fr : Frame => fr.binds[j]?) := by
  rw [Env.erase_get?]; cases env[f]? <;> rfl

theorem ckVarPos_erase (env : Env) (i : Nat) : ckVarPos env.erase i = ckVarPos env i := by
  simp only [ckVarPos, Env.erase_size, binds_erase]

theorem wf1_erase (env : Env) : WF1 env.erase ↔ WF1 env := by
  simp only [WF1, allPos_erase, valAt_erase, shape_erase]

/-- A variable of the top frame bound to a number stored at `Nat`. -/
def NumVar (i : Nat) (st : MState) : Prop :=
  ∃ f j b, ckVarPos st.env i = some (.bind f j) ∧ st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧
    b.val.Num ∧ b.ty = some .tNat

theorem NumVar.of_erase {i : Nat} {st st' : MState} (he : st.env.erase = st'.env.erase) (h : NumVar i st) :
    NumVar i st' := by
  obtain ⟨f, j, b, h1, h2, h3, h4⟩ := h
  refine ⟨f, j, b, ?_, ?_, h3, h4⟩
  · rw [← ckVarPos_erase, ← he, ckVarPos_erase]; exact h1
  · rw [← lookup_erase, ← he, lookup_erase]; exact h2

theorem NumVar.of_kern {i : Nat} {st st' : MState} (hk : Kern st st') (h : NumVar i st) : NumVar i st' :=
  h.of_erase hk.env

theorem mem_values_setAtE {env : Env} {p : Pos} {v w : Value} (hw : w ∈ Env.values (Env.setAtE env p v)) :
    w = v ∨ w ∈ Env.values env := by
  simp only [Env.values, allPos_setAtE, List.mem_map] at hw ⊢
  obtain ⟨q, hq, rfl⟩ := hw
  by_cases e : q = p
  · subst e
    left
    rcases q with ⟨f, i⟩ | ⟨f, i⟩
    · obtain ⟨fr, b, hf, hi⟩ := mem_allPos_bind env f i hq
      exact valAt_setAtE_bind env f i v fr b hf hi
    · obtain ⟨fr, hf, hi⟩ := mem_allPos_temp env f i hq
      exact valAt_setAtE_temp env f i v fr hf hi
  · exact .inr ⟨q, hq, (valAt_setAtE_other env p q v e).symm⟩


theorem lookup_setAtE {env : Env} {p : Pos} {v : Value} {f i : Nat} {b : Binding}
    (h : (Env.setAtE env p v)[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b) :
    ∃ b', env[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b' ∧ b'.ty = b.ty ∧ b'.lazyTy = b.lazyTy := by
  cases p with
  | bind f' i' =>
    simp only [Env.setAtE, Array.getElem?_modify] at h
    by_cases hf : f' = f
    · subst hf
      rcases hfr : env[f']? with _ | fr
      · rw [hfr] at h; simp at h
      · rw [hfr] at h
        simp only [if_true, Option.map_some, Option.bind_some, Array.getElem?_modify] at h
        by_cases hi : i' = i
        · subst hi; simp only [if_true] at h
          rcases hb : fr.binds[i']? with _ | b'
          · rw [hb] at h; simp at h
          · rw [hb] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
            exact ⟨b', by simp [hfr, hb], rfl, rfl⟩
        · simp only [hi, if_false] at h; exact ⟨b, by simp [hfr, h], rfl, rfl⟩
    · simp only [hf, if_false] at h; exact ⟨b, h, rfl, rfl⟩
  | temp f' i' =>
    simp only [Env.setAtE, Array.getElem?_modify] at h
    by_cases hf : f' = f
    · subst hf
      rcases hfr : env[f']? with _ | fr
      · rw [hfr] at h; simp at h
      · rw [hfr] at h; simp only [if_true, Option.map_some, Option.bind_some] at h
        exact ⟨b, by simp [hfr, h], rfl, rfl⟩
    · simp only [hf, if_false] at h; exact ⟨b, h, rfl, rfl⟩

/-! ## The read -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem num_heldLabel {v : Value} (hv : v.Num) : Value.heldLabel v = none := by cases hv <;> rfl

/-- The checker's meaning of a binding holding a number, at its stored type, at any future. -/
theorem mean_numVar {st : MState} {f j : Nat} {b : Binding}
    (hb : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) {m : Nat}
    (hm : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint b.val = .el0 Nat m) (ψ : Future) :
    Env.mean K.dm K.M K.Γ ρ ψ st.env (.bind f j) = .el0 Nat m := by
  simp only [Env.mean, hb]; exact hm _ _ _ _ _ _

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The read of a variable holding a number stored at `Nat`, at `evalCore`.** -/
theorem var_core (hV : VarNumInv) (hIC : InvCore) {n i : Nat} : CoreSim K ρ φ (n + 1) (.place (.var i)) (NumVar i) := by
  intro st st' typed hint v T? s π ⟨f, j, b, hpos, hb, hnum, hty⟩ _ hm htn hp hr hS hv hab hnh hfl hok hD bh h
  obtain ⟨rfl, hT, -, hm', st₁, hq, hcopy, hmove⟩ := hV n typed i hint st st' bh v T? f j b K.D hm hpos hb hnum hD h
  have hres : resolve s (.var i) = some (.bind f j, []) := rel_resolve_ck K ρ φ st s π (.var i) _ hr hpos
  have hvb : valAt st.env (.bind f j) = b.val := by
    rw [valAt_bind_eq]; rcases hfr : st.env[f]? with _ | fr
    · rw [hfr] at hb; cases hb
    · rw [hfr] at hb; simp only [Option.bind_some] at hb; simp [hb]
  have hns : ∀ l, (valAt st.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by rw [hvb]; exact hnum.sitesOf l _ _
  have hacc : s.access (.bind f j) (dataHit []) = s := access_noSites (rel_noSites_at hr hns)
  obtain ⟨m, hmv⟩ := hnum.vmean
  have hval : s.valAt (.bind f j) (s.typedFuture φ) = .el0 Nat m := by
    rw [← hr.sim.1 (s.typedFuture φ) ⟨relF_typedFuture φ s, hr.typedFuture_typed φ⟩ (.bind f j) (by simp [IsTemp])]
    exact mean_numVar hb hmv _
  obtain ⟨hposS, htyS⟩ := rel_bind_ty hr hb
  have htyN : (s.tyAt (.bind f j)).m = TyM.nat := by
    rw [htyS]; simp only [Env.hintAt, hb, hty]; rfl
  have hshS : s.shape (.bind f j) = none := by
    rcases e : s.shape (.bind f j) with _ | l'
    · rfl
    · obtain ⟨l, h1, -⟩ := hr.sim.2.2.1 (.bind f j) l' (by simp [IsTemp]) e
      have : Env.shape st.env (.bind f j) = some l := h1
      simp only [Env.shape, hvb] at this
      revert this
      generalize b.val = w at hnum
      cases hnum <;> simp
  have hsc : scopeOf s = DecideScope.topReadings st := scopeOf_rel hr
  have hco : contentOf K φ (.var i) s = some ((.el0 Nat m, s.tyAt (.bind f j), .bind f j, []), s) := by
    unfold contentOf; rw [hres]; simp only; rw [hacc]; simp [Sem.follow, hval]
  have hrg : ReadGood K.dm.read (s.tyAt (.bind f j)).m (.el0 Nat m) := .inl (by rw [htyN]; exact ⟨m, rfl⟩)
  have hrun : runT K ρ φ st.curTail (hintM K ρ hint) (.place (.var i)) s =
      readPlace K φ (.var i) (K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var i))) s := by
    rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl, hsc]; rfl
  have hwhole : (Sem.el0 Nat m).whole := by simp [Sem.whole]
  have hlab : ∀ l, st.Occurs l → l < st.nextLoan := hp.labels
  have hr₁ : Rel K ρ φ π st₁ s := hr.of_quiet hq hlab
  have ha₁ : Asg K ρ st₁.norm := Asg.of_quiet hq hp.asg hp.inv.wf6
  have hinv := hIC (n + 1) typed (.place (.var i)) hint st st' bh b.val T? K.D K.Γ hp.inv hD h
  have hmeanV : ∀ ψ hint', meanV K ρ ψ hint' b.val = .el0 Nat m := fun ψ hint' => by
    rw [← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  have hagree : ∀ T, T? = some T → StrAgree K ρ T { s.tyAt (.bind f j) with label := none } := by
    intro T e
    have := hT T e; rw [hty] at this; cases this
    show _ = (s.tyAt (.bind f j)).m; rw [htyN]; rfl
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
    have hb₁ : st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
      rw [← lookup_erase, ← hq.env, lookup_erase]; exact hb
    have hvb₁ : valAt st₁.env (.bind f j) = b.val := by rw [← valAt_erase, ← hq.env, valAt_erase]; exact hvb
    have hwf1 : WF1 st₁.env := by
      rw [← wf1_erase, ← hq.env, wf1_erase]; exact (wf1_erase st.env).mp hp.inv.1
    have hpos₁ : Pos.bind f j ∈ allPos st₁.env := by
      rcases hfr : st₁.env[f]? with _ | fr
      · rw [hfr] at hb₁; cases hb₁
      · rw [hfr] at hb₁; exact bind_mem_allPos st₁.env f j fr b hfr hb₁
    have hR := botWrite_rel K ρ φ st₁ s π f j [] .bot hr₁ hwf1 hpos₁ hposS
      (by rw [Value.updAt])
      (fun _ => by simp only [Env.shape, hvb₁]; generalize b.val = w at hnum; cases hnum <;> rfl)
      (fun l _ x hx hxp => by
        have := mem_sitesOf_at hx hxp
        rw [hvb₁, hnum.sitesOf] at this; cases this)
      ⟨by rw [hvb₁]; exact hnum.anyAtom rfl fun _ => rfl, by rw [hvb₁]; exact hnum.anyAtom rfl fun _ => rfl⟩
      (fun _ => by rw [NatAlong]; trivial)
    have hA : Asg K ρ ({ st₁ with env := Env.setAtE st₁.env (.bind f j) .bot } : MState).norm := by
      refine ha₁.of_refd rfl rfl rfl rfl rfl (refd_sub rfl rfl rfl rfl ?_ ?_ ?_)
      · intro w hw σ hσ
        rcases mem_values_setAtE hw with rfl | hw'
        · cases hσ
        · exact ⟨w, hw', hσ⟩
      · intro f' i' b' T σ hb' hT hσ
        obtain ⟨b'', hb'', hty'', -⟩ := lookup_setAtE hb'
        exact .ty f' i' b'' T (by rw [show st₁.norm.env = st₁.env.erase from rfl, lookup_erase]; exact hb'')
          (by rw [hty'']; exact hT) hσ
      · intro f' i' b' P ws j' σ hb' hl hσ
        obtain ⟨b'', hb'', -, hlz''⟩ := lookup_setAtE hb'
        exact .lazyTy f' i' b'' P ws j' (by rw [show st₁.norm.env = st₁.env.erase from rfl, lookup_erase]; exact hb'')
          (by rw [hlz'']; exact hl) hσ
    refine ⟨ρ, K.Δ, π, _, _, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, by rw [hrun, hc]; exact hst, hmeanV _ _, hagree,
      by simp [num_heldLabel hnum], ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · have : Asg K ρ st'.norm := by rw [← hk.norm]; exact hA
        exact asg_withTempT_num this hnum T?
    · exact rel_withTempT_num (hR.of_kern hk) hnum T?
  · -- a copy: nothing changes
    have hk := hcopy hc
    have hst : readPlace K φ (.var i) true s = some ((.el0 Nat m, { s.tyAt (.bind f j) with label := none }), s) := by
      unfold readPlace
      rw [hco]
      simp only [hwhole, hrg, not_true_eq_false, if_false, if_true, bind, Option.bind]
    refine ⟨ρ, K.Δ, π, _, s, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, by rw [hrun, hc]; exact hst, hmeanV _ _, hagree,
      by simp [num_heldLabel hnum], ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · have : Asg K ρ st'.norm := by rw [← hk.norm]; exact ha₁
        exact asg_withTempT_num this hnum T?
    · exact rel_withTempT_num (hr₁.of_kern hk) hnum T?

end

end Ochr.Meaning.Steps.Form
