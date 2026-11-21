import Ochr.Meaning.Steps.FragMachine

/-!
# The fragment: the read of a LENT number variable (lead10)

`x` (the `i`-th variable, a number binding) holds `loan_l`; its borrow `borrow_l c` is held at a
binding `y`; other borrows may be live. The checker's read ends `l` (`VarLentInv`: `y ↦ ⊥`, `x ↦ c`)
and copies or moves `c`; the reference's read ends `π l` by its [Access] (`access_one`, strict by
`end_ok`) and reads `c`'s meaning at the place. The relation across the end is `rel_end`; the read
after it is the column's read of a number variable (`var_core`), at the states after the end.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-- **A read of a lent number variable**: the `i`-th variable is a binding at `.bind f j` stored at
`Nat` and read `.other`, holding `loan_l`, whose borrow `borrow_l c` is held at the binding
`.bind f' j'`; every position holds a fragment value (`FEnd`); every loan in the environment is live
(the checker's D111). -/
def LentVar (i : Nat) (st : MState) : Prop :=
  ∃ f j b f' j' l c, ckVarPos st.env i = some (.bind f j) ∧
    st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧ b.ty = some .tNat ∧ b.decl = .other ∧
    FEnd st.env (.bind f j) (.bind f' j') l c ∧
    ∀ q ∈ allPos st.env, ∀ m, valAt st.env q = .loan m → liveLoan st.env m = true

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The assignment's facts survive a write of a value holding no unknown. -/
theorem asg_setAtE_noAbs {st : MState} {p : Pos} {v : Value} (hv : ∀ σ, v.hasAbs σ = false)
    (ha : Asg K ρ st.norm) : Asg K ρ ({ st with env := Env.setAtE st.env p v } : MState).norm := by
  refine ha.of_refd rfl rfl rfl rfl rfl (refd_sub rfl rfl rfl rfl ?_ ?_ ?_)
  · intro w hw σ hσ
    rcases Form.mem_values_setAtE hw with rfl | hw'
    · rw [hv σ] at hσ; cases hσ
    · exact ⟨w, hw', hσ⟩
  · intro f' i' b' T σ hb' hT hσ
    obtain ⟨b'', hb'', hty'', -⟩ := lookup_setAtE hb'
    exact .ty f' i' b'' T (by rw [show st.norm.env = st.env.erase from rfl, lookup_erase]; exact hb'')
      (by rw [hty'']; exact hT) hσ
  · intro f' i' b' P ws j' σ hb' hl hσ
    obtain ⟨b'', hb'', -, hlz''⟩ := lookup_setAtE hb'
    exact .lazyTy f' i' b'' P ws j' (by rw [show st.norm.env = st.env.erase from rfl, lookup_erase]; exact hb'')
      (by rw [hlz'']; exact hl) hσ

theorem asg_endE {st : MState} {px ph : Pos} {c : Value} (hc : c.Num) (ha : Asg K ρ st.norm) :
    Asg K ρ ({ st with env := endE st.env px ph c } : MState).norm :=
  asg_setAtE_noAbs (st := { st with env := Env.setAtE st.env ph .bot }) hc.hasAbs
    (asg_setAtE_noAbs (fun _ => rfl) ha)

/-- The reference's [Access] of the lent variable ends exactly its label. -/
theorem lent_access {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s) {f j f' j' l : Nat} {c : Value} (he : FEnd st.env (.bind f j) (.bind f' j') l c)
    {r : Pos} (hrs : s.shape r = some (π l)) (hr' : r = .bind f' j') :
    s.access (.bind f j) (dataHit []) = s.endAt (π l) r ∧
      (EndOk K φ s (π l) → AccessOk K φ s (.bind f j) (dataHit [])) := by
  have hliveL := he.liveL
  have hsite : ∀ l' x, liveLoan st.env l' = true → x ∈ s.lent (π l') → valAt st.env x.pos = .loan l' :=
    fun l' x hl hx => (he.mem_sitesOf ((hr.sites l' hl x).mp hx)).2
  refine access_one hS.uniq hrs (hr.holders r _ hrs) ?_ ?_ ?_
  · -- `π l` is lent at `x`'s root
    unfold SState.reached
    refine List.any_eq_true.mpr ⟨⟨.bind f j, [], false⟩, (hr.sites l hliveL _).mpr ?_, by simp [dataHit]⟩
    unfold Env.sitesOf
    refine List.mem_flatMap.mpr ⟨.bind f j, he.hpx, ?_⟩
    rw [he.x]; simp [Value.sitesOf]
  · intro z hz hreach
    obtain ⟨l', hl', rfl⟩ := rel_live_ref K ρ φ st s π hr hz
    unfold SState.reached at hreach
    obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp hreach
    have hxpos : x.pos = .bind f j := by simpa using (Bool.and_eq_true _ _).mp hxp |>.1
    have := hsite l' x hl' hx
    rw [hxpos, he.x] at this
    cases this; rfl
  · intro z hz hne x hx e
    obtain ⟨l', hl', rfl⟩ := rel_live_ref K ρ φ st s π hr hz
    have := hsite l' x hl' hx
    rw [e, hr', he.y] at this
    cases this

/-- **The read of a lent number variable, at `evalCore`** (`LentVar`). The strict run's [Access]
ends `π l` and is strict (`end_ok`); the value read is `c`, read through the future at the holder's
content; then the read copies or moves as the aligned decision says, as `var_core`. Assumes the
facts about the checker `VarLentInv` (the run), `InvEnd` (the invariant across the end) and the
column's `InvSteps`. -/
theorem readLent_core (hV : VarLentInv) (hIE : InvEnd) (hI : InvSteps) (hPL : PlaceLocal K.D) {n i : Nat} :
    CoreSim K ρ φ (n + 1) (.place (.var i)) (LentVar i) := by
  intro st st' typed hint v T? s π hP _ hm htn _ _ hp hr hS hv hab hnh hfl hok hD bh h
  obtain ⟨f, j, b, f', j', l, c, hpos, hb, hty, hdo, he, hlv⟩ := hP
  obtain ⟨hvc, hT, -, hm', st₁, hq, hki, hcopy, hmove⟩ :=
    hV n typed i hint st st' bh v T? f j b f' j' l c K.D hm hpos hb hty he hD h
  subst hvc
  -- the checker's state after the [Repack]: the same values
  have hvE : ∀ q, valAt st₁.env q = valAt st.env q := fun q => by rw [← valAt_erase, ← hq.env, valAt_erase]
  have haE : allPos st₁.env = allPos st.env := by rw [← allPos_erase, ← hq.env, allPos_erase]
  have hlE : ∀ m, liveLoan st₁.env m = liveLoan st.env m := fun m => by
    unfold liveLoan findBorrow; rw [haE]; simp only [hvE]
  have he₁ : FEnd st₁.env (.bind f j) (.bind f' j') l v := he.of_erase hq.env
  have hlv₁ : ∀ q ∈ allPos st₁.env, ∀ m, valAt st₁.env q = .loan m → liveLoan st₁.env m = true :=
    fun q hq' m hm₁ => by rw [hlE]; exact hlv q (haE ▸ hq') m (by rw [← hvE]; exact hm₁)
  have hlab : ∀ l, st.Occurs l → l < st.nextLoan := hp.labels
  have hr₁ : Rel K ρ φ π st₁ s := hr.of_quiet hq hlab
  have ha₁ : Asg K ρ st₁.norm := Asg.of_quiet hq hp.asg hp.inv.wf6
  -- the end, on both sides
  obtain ⟨r, cM, hhold, hrs, hrph, -, -, hcM, -⟩ := end_holder hr₁ hS he₁
  have hrr : r = .bind f' j' := hrph f' j' rfl
  obtain ⟨r₂, hhold₂, hrE⟩ := rel_end hr₁ hS he₁ hlv₁
  have hr₂ : r = r₂ := by rw [hhold] at hhold₂; exact Option.some.inj hhold₂
  subst hr₂
  have hend := end_ok hr₁ hS he₁
  obtain ⟨hacc, haok⟩ := lent_access hr₁ hS he₁ hrs hrr
  have hSt : Strict.SGood K.dm K.Γ φ (s.endAt (π l) r) := Strict.endAt_sgood hS hhold hend
  -- the checker's invariant and assignment after the end
  have hinv₂ : Inv K.D K.Γ ({ st₁ with env := endE st₁.env (.bind f j) (.bind f' j') v } : MState).norm :=
    hIE K.D K.Γ st₁ _ _ l v hPL he₁ (fun f₀ j₀ e b₀ hb₀ => by
      cases e; rw [← lookup_erase, ← hq.env, lookup_erase, hb] at hb₀; cases hb₀; exact hdo)
      (hki K.D K.Γ hp.inv)
  have ha₂ : Asg K ρ ({ st₁ with env := endE st₁.env (.bind f j) (.bind f' j') v } : MState).norm := asg_endE he.c ha₁
  -- the reference reads `c`'s meaning at `x`, after the access
  obtain ⟨m, hmv⟩ := he.c.vmean
  have hres : resolve s (.var i) = some (.bind f j, []) := rel_resolve_ck K ρ φ st s π (.var i) _ hr hpos
  have hxpos₂ : Pos.bind f j ∈ allPos (endE st₁.env (.bind f j) (.bind f' j') v) := by rw [FEnd.allPos_endE, haE]; exact he.hpx
  have hvx₂ : valAt (endE st₁.env (.bind f j) (.bind f' j') v) (.bind f j) = v := by rw [he₁.valAt_endE, if_pos rfl]
  have hval : (s.endAt (π l) r).valAt (.bind f j) ((s.endAt (π l) r).typedFuture φ) = .el0 Nat m := by
    rw [← hrE.sim.1 _ ⟨relF_typedFuture φ _, hrE.typedFuture_typed φ⟩ (.bind f j) (by simp [IsTemp])]
    show Env.mean K.dm K.M K.Γ ρ _ (endE st₁.env (.bind f j) (.bind f' j') v) (.bind f j) = _
    rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ hxpos₂, hvx₂]; exact hmv _ _ _ _ _ _
  have hb₁ : st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
    rw [← lookup_erase, ← hq.env, lookup_erase]; exact hb
  obtain ⟨hposS, htyS₀⟩ := rel_bind_ty hr₁ hb₁
  have htyN : (s.tyAt (.bind f j)).m = TyM.nat := by rw [htyS₀]; simp only [Env.hintAt, hb₁, hty]; rfl
  have hsc : scopeOf s = DecideScope.topReadings st := scopeOf_rel hr
  have hco : contentOf K φ (.var i) s =
      some ((.el0 Nat m, s.tyAt (.bind f j), .bind f j, []), s.endAt (π l) r) := by
    unfold contentOf; rw [hres]; simp only; rw [hacc, hval]; simp [Sem.follow, endAt_tyAt']
  have hrg : ReadGood K.dm.read (s.tyAt (.bind f j)).m (.el0 Nat m) := .inl (by rw [htyN]; exact ⟨m, rfl⟩)
  have hrun : runT K ρ φ st.curTail (hintM K ρ hint) (.place (.var i)) s =
      readPlace K φ (.var i) (K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var i))) s := by
    have hcok : ContentOk K φ (.var i) s := by unfold ContentOk; rw [hres]; exact haok hend
    rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl, hsc]
    show SM.guarded _ _ s = _; unfold SM.guarded; rw [if_pos hcok]
  have hwhole : (Sem.el0 Nat m).whole := by simp [Sem.whole]
  have hinv : Inv K.D K.Γ (st'.withTempT v T?).norm := by
    refine hI.pushInert K.D K.Γ st' _ _ (.inl he.c) ?_
    cases hc : K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var i))
    · rw [← (hmove hc).norm]
      exact hI.setBot K.D K.Γ ({ st₁ with env := endE st₁.env (.bind f j) (.bind f' j') v } : MState) f j
        (by show (valAt (endE st₁.env (.bind f j) (.bind f' j') v) (.bind f j)).Num; rw [hvx₂]; exact he.c) hinv₂
    · rw [← (hcopy hc).norm]; exact hinv₂
  have hmeanV : ∀ ψ hint', meanV K ρ ψ hint' v = .el0 Nat m := fun ψ hint' => by
    rw [← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  have hagree : ∀ T, T? = some T → StrAgree K ρ T { s.tyAt (.bind f j) with label := none } := by
    intro T e
    obtain rfl := hT T e
    show _ = (s.tyAt (.bind f j)).m; rw [htyN]; rfl
  cases hc : K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var i))
  · -- a move: `⊥` at the binding, on both sides, after the end
    have hk := hmove hc
    have hshT : (s.endAt (π l) r).shape (.bind f j) = none := by
      rw [SState.endAt_shape]; simp only
      rw [if_neg (fun e => he.ne (by rw [← hrr, ← e]))]
      rcases e : s.shape (.bind f j) with _ | l'
      · rfl
      · obtain ⟨l₀, h1, -⟩ := hr₁.sim.2.2.1 (.bind f j) l' (by simp [IsTemp]) e
        have : Env.shape st₁.env (.bind f j) = some l₀ := h1
        rw [shape_eq_shapeOf, he₁.x] at this; cases this
    have hst : readPlace K φ (.var i) false s = some ((.el0 Nat m, { s.tyAt (.bind f j) with label := none }),
        (s.endAt (π l) r).setAt (.bind f j) fun φ' =>
          (Sem.updAt K.dm K.Γ ((s.endAt (π l) r).tyAt (.bind f j)) (fun _ => .moved) []
            ((s.endAt (π l) r).valAt (.bind f j) φ')).getD .err) := by
      have hset : setContent K φ (.bind f j) [] .moved (s.endAt (π l) r) = some (⟨⟩,
          (s.endAt (π l) r).setAt (.bind f j) fun φ' =>
            (Sem.updAt K.dm K.Γ ((s.endAt (π l) r).tyAt (.bind f j)) (fun _ => .moved) []
              ((s.endAt (π l) r).valAt (.bind f j) φ')).getD .err) := by
        unfold setContent; rw [if_pos (by intro ψ _; rfl)]
      unfold readPlace
      rw [hco]
      simp only [Option.bind_some, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_nil,
        hshT, hset, bind, Option.bind]
      rfl
    have hwf1 : WF1 (endE st₁.env (.bind f j) (.bind f' j') v) := (wf1_erase _).mp hinv₂.1
    have hR := botWrite_rel K ρ φ ({ st₁ with env := endE st₁.env (.bind f j) (.bind f' j') v } : MState)
      (s.endAt (π l) r) π f j [] .bot hrE hwf1 hxpos₂ (by rw [SState.endAt_positions]; exact hposS)
      (by rw [Value.updAt])
      (fun _ => by simp only [Env.shape, hvx₂]; generalize v = w at he; cases he.c <;> rfl)
      (fun l' _ x hx hxp => by
        have := mem_sitesOf_at hx hxp
        rw [hvx₂, he.c.sitesOf] at this; cases this)
      ⟨by rw [hvx₂]; exact he.c.anyAtom rfl fun _ => rfl, by rw [hvx₂]; exact he.c.anyAtom rfl fun _ => rfl⟩
      (fun _ => by rw [NatAlong]; trivial)
    refine ⟨ρ, K.Δ, π, _, _, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, by rw [hrun, hc]; exact hst, hmeanV _ _, hagree,
      by simp [num_heldLabel he.c], ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · have : Asg K ρ st'.norm := by rw [← hk.norm]; exact asg_setAtE_noAbs (fun _ => rfl) ha₂
        exact asg_withTempT_num this he.c T?
    · exact rel_withTempT_num (hR.of_kern hk) he.c T?
  · -- a copy: the state after the end
    have hk := hcopy hc
    have hst : readPlace K φ (.var i) true s =
        some ((.el0 Nat m, { s.tyAt (.bind f j) with label := none }), s.endAt (π l) r) := by
      unfold readPlace
      rw [hco]
      simp only [hwhole, hrg, not_true_eq_false, if_false, if_true, bind, Option.bind]
    refine ⟨ρ, K.Δ, π, _, _, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, by rw [hrun, hc]; exact hst, hmeanV _ _, hagree,
      by simp [num_heldLabel he.c], ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · have : Asg K ρ st'.norm := by rw [← hk.norm]; exact ha₂
        exact asg_withTempT_num this he.c T?
    · exact rel_withTempT_num (hrE.of_kern hk) he.c T?

end

end Ochr.Meaning.Steps.Form
