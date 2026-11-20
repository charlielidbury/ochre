import Ochr.Meaning.Steps.DropRuns

/-!
# `dropOne_step` assembled where the place exists (docs/31 D30; task C)

The main case of the drop of one place: the place exists in the checker's state, so `movedPlace`
returns it (`movedPlace_exists'`), and `dropAtJoin`'s four cases (`runs_dropAtJoin_inv`) meet the
reference's `joinDropOne`, the shortest lent prefix accessed whole and then `dropAt`. The assembly
is proved from named obligations, the open ones `sorry`'d below or in `Steps/DropOne.lean`, and the
induction hypothesis's [Access] and [End] statements.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem lentPrefix_nil (s : SState) (pos : Pos) : lentPrefix s pos [] = none := rfl

theorem accessLentPrefix_nil (s : SState) (pos : Pos) : accessLentPrefix pos [] s = s := by
  simp [accessLentPrefix, lentPrefix_nil]

/-- **A borrow is found only at a root** ((WF1): a borrow is the whole value of its position). Open:
by induction on the path; not written. -/
theorem follow_borrow_root {env : Env} {pos : Pos} {ss : List Step} {l : Nat} {w : Value}
    (hwf : WF1 env) (hp : pos ∈ allPos env) (h : (valAt env pos).follow ss = some (.borrow l w)) :
    ss = [] := by
  sorry

/-- **The holder of a borrow the drop ends is not `moved` or `⋆` in the reference** (its content is
whole: the checker's [End] rejects a borrow whose content is partly moved out, D53; and no proof is
borrowed, D66). Open: not tried. -/
theorem holder_follow (st : MState) (s : SState) (π : Nat → Nat) (pos : Pos) (l : Nat) (w : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hv : valAt st.env pos = .borrow l w) :
    ∃ x T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) [] = some (x, T) ∧
      x ≠ .proof ∧ x ≠ .moved := by
  sorry

/-- **The reference's drop of a data place is its access then its write** (`dropAt`'s last clause):
the place is not missing, `moved` or `⋆` after the lent prefix's access, it is not a holder at a
root, and it is not a copy. Open: from `content_follow` after the prefix access; not written. -/
theorem dropAt_data (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hv : (valAt st.env pos).follow q.steps.2 = some v) (hb : ∀ l w, v ≠ .borrow l w) (hbot : v ≠ .bot)
    (hproof : v ≠ .proof) (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false) :
    let s₀ := accessLentPrefix pos q.steps.2 s
    let s₁ := s₀.access pos (dataHit q.steps.2)
    dropAt K φ q pos q.steps.2 s₀ = s₁.setAt pos fun φ' =>
      (Sem.updAt K.dm K.Γ (s₁.tyAt pos) (fun _ => .moved) q.steps.2 (s₁.valAt pos φ')).getD .err := by
  sorry

/-- **What the write of `⊥` needs, at the drop** (`botWrite_rel`'s hypotheses after the access and
the log): the place is at a binding of the reference's positions, the value records its parameters
with no sealed program, the path is one it has, a whole root written is not a holder or a type
value, and the access cleared the place. Open: from (WF10), [Close]'s programs being top-hint-free
(`mean_updAt_bot_sealed` for the sealed case), `GrainOk`, the copy decision, `access_clears`. -/
theorem botWrite_hyps (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos) (v' : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hck : ckVarPos st.env q.steps.1 = some pos) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hv : Value.updAt (fun _ => .bot) q.steps.2 (valAt st.env pos) = some v')
    (hclear : ∀ l, liveLoan st.env l = true → ∀ x ∈ Env.sitesOf st.env l, x.pos = pos →
      dataHit q.steps.2 x.path = false) :
    ∃ f i, pos = .bind f i ∧ Pos.bind f i ∈ allPos st.env ∧ Pos.bind f i ∈ s.positions ∧
      (q.steps.2 = [] → Env.shape st.env pos = none) ∧
      (q.steps.2 = [] → (∀ c t rd, valAt st.env pos ≠ .tPi c t rd) ∧ ∀ n a, valAt st.env pos ≠ .tInd n a) ∧
      RecPlain K.Γ (valAt st.env pos) ∧ ∀ ψ, NatAlong K.dm K.M K.Γ ρ ψ q.steps.2 (valAt st.env pos) := by
  sorry

/-- **`Good` after the write of `⊥`** (L3's other half): membership by `MovedOf` (a part moved out
of a member), and every clause of well-formedness survives removing a part. Open: not tried. -/
theorem botWrite_good (st : MState) (pos : Pos) (steps : List Step) (v' : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hv : Value.updAt (fun _ => .bot) steps (valAt st.env pos) = some v') :
    Good K.dm K.M K.Γ ρ { st with env := Env.setAtE st.env pos v' } := by
  sorry

theorem ckVarPos_mem {env : Env} {i : Nat} {pos : Pos} (h : ckVarPos env i = some pos) : pos ∈ allPos env := by
  unfold ckVarPos at h
  split at h
  · rename_i hi
    simp only [Option.some.injEq] at h
    subst h
    have hne : env.size ≠ 0 := by
      intro h0
      have hd : env[env.size - 1]! = (default : Frame) := by simp [h0]
      rw [hd] at hi
      have : (default : Frame).binds.size = 0 := rfl
      omega
    have hf : env[env.size - 1]? = some env[env.size - 1]! := by
      rw [Array.getElem?_eq_getElem (by omega), getElem!_pos env (env.size - 1) (by omega)]
    generalize hfr : env[env.size - 1]! = fr at hi hf
    have hb : fr.binds[fr.binds.size - 1 - i]? = some fr.binds[fr.binds.size - 1 - i]! := by
      rw [Array.getElem?_eq_getElem (by omega), getElem!_pos _ _ (by omega)]
    exact bind_mem_allPos env _ _ _ _ hf hb
  · cases h

/-- A borrow held at a position of Ω is live. -/
theorem liveLoan_of_holder {env : Env} {pos : Pos} {l : Nat} {w : Value} (hp : pos ∈ allPos env)
    (h : valAt env pos = .borrow l w) : liveLoan env l = true := by
  unfold liveLoan findBorrow
  rw [Option.isSome_iff_exists]
  have : ((allPos env).find? fun p => (valAt env p).holdsBorrow l).isSome := by
    rw [List.find?_isSome]
    exact ⟨pos, hp, by simp [h, Value.holdsBorrow]⟩
  rwa [Option.isSome_iff_exists] at this

theorem resolve_of_declsOf {s s' : SState} (h : declsOf s = declsOf s') (q : Place) : resolve s q = resolve s' q := by
  have hl : s.env.map (fun fr => fr.binds.length) = s'.env.map (fun fr => fr.binds.length) := by
    have := congrArg (List.map List.length) h
    simpa [declsOf, List.map_map, Function.comp_def] using this
  have hlen : s.env.length = s'.env.length := by simpa using congrArg List.length hl
  have hlast : (s.env.getLast?).map (fun fr => fr.binds.length) = (s'.env.getLast?).map (fun fr => fr.binds.length) := by
    rw [← List.getLast?_map, ← List.getLast?_map, hl]
  simp only [resolve, SState.varPos, SState.topIdx, hlen]
  rcases e : s.env.getLast? with _ | fr <;> rcases e' : s'.env.getLast? with _ | fr' <;>
    simp_all

theorem declsOf_accessLentPrefix (s : SState) (pos : Pos) (steps : List Step) :
    declsOf (accessLentPrefix pos steps s) = declsOf s := by
  unfold accessLentPrefix
  split
  · exact declsOf_access _ _ _
  · rfl

/-- **The checker's access keeps its run context** (it ends borrows: no unknown, global or
declaration changes). Open: not tried. -/
theorem access_ctx (fuel : Nat) (st st' : MState) (q : Place) (b : Nat) (hctx : CtxOk K ρ st)
    (h : Runs (do Ochr.accessPath fuel q; Ochr.accessInside fuel q) st b () st') : CtxOk K ρ st' := by
  sorry

/-- **The drop of one place where the place exists** (`dropOne_step`'s main case), assembled from
the named obligations and the induction hypothesis's [Access] and [End]: missing, `⊥` or `⋆` (both
sides do nothing); a borrow at a root (both end it); a copy (excluded: the join moves no copy);
data (both access, then write `⊥`/`moved`). -/
theorem dropOne_exists (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel)
    (st st' : MState) (q : Place) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (pos : Pos) (w : Value) (hck : ckVarPos st.env q.steps.1 = some pos)
    (hw : (valAt st.env pos).follow q.steps.2 = some w)
    (b : Nat) (h : Runs (Ochr.dropAtJoin (fuel + 1) q) st b () st') :
    Rel K ρ φ π st' (joinDropOne K φ s q) ∧ Good K.dm K.M K.Γ ρ st' := by
  have hres := rel_resolve_ck K ρ φ st s π q pos hs hck
  have hj : joinDropOne K φ s q = dropAt K φ q pos q.steps.2 (accessLentPrefix pos q.steps.2 s) := by
    simp [joinDropOne, hres]
  rw [hj]
  have hp := ckVarPos_mem hck
  obtain ⟨pos', hck', hcases⟩ := runs_dropAtJoin_inv h
  rw [hck] at hck'
  cases hck'
  rcases hcases with ⟨hno, hst⟩ | ⟨l, w', hbw, st₁, b₁, b₂, hlog, hend⟩ | ⟨v, hv, b₁, hcr⟩ |
      ⟨v, hv, hb, hbot, hproof, st₁, st₂, st₃, b₁, b₂, b₃, b₄, hcr, hacc, hlog, hset⟩
  · -- missing, ⊥ or ⋆: both do nothing
    rw [hst]
    rcases hno with hn | hn
    · rw [hw] at hn; cases hn
    have hlp := lentPrefix_none_of_noop K ρ φ st s π q pos hg hs hres hn
    have hpre : accessLentPrefix pos q.steps.2 s = s := by simp [accessLentPrefix, hlp]
    rw [hpre]
    obtain ⟨cbot, cproof, -⟩ := content_follow K ρ φ st s π q pos hg hs hres
    rcases hn with hn | hn
    · obtain ⟨T, hT⟩ := cbot.mp hn
      unfold dropAt; rw [hT]; exact ⟨hs, hg⟩
    · obtain ⟨T, hT⟩ := cproof.mp hn
      unfold dropAt; rw [hT]; exact ⟨hs, hg⟩
  · -- a borrow at a root: both end it
    have hsteps := follow_borrow_root hg.2.2.1 hp hbw
    have hval : valAt st.env pos = .borrow l w' := by
      rw [hsteps] at hbw; simpa [Value.follow] using hbw
    obtain ⟨hs₁, hg₁, hctx₁, henv₁⟩ := logEffect_rel K ρ φ st st₁ s π q "moves" b₁ hg hctx hs hlog
    have hl : liveLoan st₁.env l = true := by rw [henv₁]; exact liveLoan_of_holder hp hval
    obtain ⟨hs', hg'⟩ := (ih K ρ φ).endBorrow_step st₁ st' l s π hg₁ hctx₁ hs₁ hl b₂ hend
    have hsh : s.shape pos = some (π l) := by
      have hpt : ¬ IsTemp pos := by
        rcases pos with ⟨f, i⟩ | ⟨f, i⟩
        · simp [IsTemp]
        · unfold ckVarPos at hck; split at hck <;> cases hck
      exact hs.sim.2.1 pos l hpt (by show Env.shape st.env pos = some l; rw [shape_eq_shapeOf, hval]; rfl)
    rw [hsteps, accessLentPrefix_nil]
    obtain ⟨x, T, hT, hxp, hxm⟩ := holder_follow K ρ φ st s π pos l w' hg hs hval
    have hd : dropAt K φ q pos [] s = s.endLabel (π l) := by
      unfold dropAt
      rw [hT]
      cases x <;> simp_all
    rw [hd]
    exact ⟨hs', hg'⟩
  · -- a copy: excluded
    obtain ⟨-, hc⟩ := copyRead_aligned K ρ φ fuel st st' s π q true b₁ hctx hs hcr
    rw [hcopy] at hc; cases hc
  · -- data: both access, then write
    obtain ⟨hst₁, -⟩ := copyRead_aligned K ρ φ fuel st st₁ s π q false b₁ hctx hs hcr
    rw [hst₁] at hacc
    obtain ⟨hs₂, hg₂⟩ := (ih K ρ φ).access_step st st₂ q pos false s π hg hctx hs hres b₂ hacc
    simp only [Bool.false_and, Bool.false_eq_true, if_false] at hs₂
    have hs₂' := (lentPrefix_absorbed K ρ φ st st₂ s π pos q.steps.2 hg hs).mpr hs₂
    have hctx₂ := access_ctx K ρ fuel st st₂ q b₂ hctx hacc
    obtain ⟨hs₃, hg₃, hctx₃, henv₃⟩ := logEffect_rel K ρ φ st₂ st₃ _ π q "moves" b₃ hg₂ hctx₂ hs₂' hlog
    have hdecl : declsOf ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2)) = declsOf s := by
      rw [declsOf_access, declsOf_accessLentPrefix]
    have hres₁ : resolve ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2)) q =
        some (pos, q.steps.2) := by rw [resolve_of_declsOf hdecl]; exact hres
    obtain ⟨pos'', v', hck'', hupd, hst'⟩ := runs_setPlace_inv hset
    have hpp : pos'' = pos := by
      have := rel_resolve_ck K ρ φ st₃ _ π q pos'' hs₃ hck''
      rw [hres₁] at this
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact this.1.symm
    rw [hpp] at hck'' hupd hst'
    have hclear₂ := access_clears fuel st st₂ q pos b₂ hck hacc
    have hclear₃ : ∀ l, liveLoan st₃.env l = true → ∀ x ∈ Env.sitesOf st₃.env l, x.pos = pos →
        dataHit q.steps.2 x.path = false := by rw [henv₃]; exact hclear₂
    have hgrain₁ : GrainOk K.D K.Γ (scopeOf ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2))) q := by
      rw [scopeOf_of_declsOf hdecl]; exact hgrain
    obtain ⟨f, i, hposfi, hpb, hsp, hroot, htype, hplain, hnat⟩ :=
      botWrite_hyps K ρ φ st₃ _ π q pos v' hg₃ hs₃ hres₁ hck'' hgrain₁ hupd hclear₃
    subst hposfi
    have hrel := botWrite_rel K ρ φ st₃ _ π f i q.steps.2 v' hs₃ hg₃.2.2.1 hpb hsp hupd hroot htype hclear₃ hplain hnat
    rw [dropAt_data K ρ φ st s π q (.bind f i) v hg hs hres hv hb hbot hproof hcopy, hst']
    exact ⟨hrel, botWrite_good K ρ st₃ (.bind f i) q.steps.2 v' hg₃ hupd⟩

/-- **The checker's drop of one place keeps the run context and creates no unknown** (`dropAtJoin`
ends a borrow, accesses and writes: no unknown, global or declaration changes). Open: not tried. -/
theorem dropAtJoin_ctx (fuel : Nat) (st st' : MState) (q : Place) (b : Nat) (hctx : CtxOk K ρ st)
    (h : Runs (Ochr.dropAtJoin (fuel + 1) q) st b () st') :
    CtxOk K ρ st' ∧ st.absTy.size ≤ st'.absTy.size := by
  sorry

/-- **The drop of one place where the place does not exist** (`movedPlace`'s other branches: a
filled parent accessed whole, an unknown or a sealed program of a one-constructor type refined,
and the exits), with the extended context. Open: the branch lemmas `movedPlace_fill`,
`movedPlace_eta`, `movedPlace_sealed`, `movedPlace_exit` in `Steps/DropOne.lean`, then the drop
of the place they return (`dropOne_exists` once it exists). -/
theorem dropOne_missing (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel)
    (st st' : MState) (q : Place) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (hnex : ¬ ∃ pos w, ckVarPos st.env q.steps.1 = some pos ∧ (valAt st.env pos).follow q.steps.2 = some w)
    (bh : Nat) (h : Runs (do Ochr.dropAtJoin (fuel + 1) (← Ochr.movedPlace (fuel + 1) q)) st bh () st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), st.absTy.size ≤ st'.absTy.size ∧
      (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧
      Rel { K with Δ := Δ' } ρ' φ π st' (joinDropOne K φ s q) ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' := by
  sorry

theorem runCtx_with_self (K : RunCtx) : ({ K with Δ := K.Δ } : RunCtx) = K := by cases K; rfl

/-- **`dropOne_step`, assembled**: where the place exists, `dropOne_exists`; where it does not,
`dropOne_missing`. -/
theorem dropOne_step_asm (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) :
    dropOne_step_stmt K ρ φ (fuel + 1) := by
  intro st st' q s π hg hctx hs hgrain hcopy bh h
  by_cases hex : ∃ pos w, ckVarPos st.env q.steps.1 = some pos ∧ (valAt st.env pos).follow q.steps.2 = some w
  · obtain ⟨pos, w, hck, hw⟩ := hex
    obtain ⟨q', st₁, b₁, hmp, hdj⟩ := Runs.bind_inv h
    obtain ⟨hq', hst₁⟩ := movedPlace_exists' fuel hck hw hmp
    rw [hq', hst₁] at hdj
    obtain ⟨hrel, hgood⟩ := dropOne_exists K ρ φ fuel ih st st' q s π hg hctx hs hgrain hcopy pos w hck hw b₁ hdj
    obtain ⟨hctx', hsize⟩ := dropAtJoin_ctx K ρ fuel st st' q b₁ hctx hdj
    refine ⟨ρ, K.Δ, hsize, fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩ <;> rw [runCtx_with_self K]
    · exact hctx'
    · exact hrel
    · exact hgood
  · exact dropOne_missing K ρ φ fuel ih st st' q s π hg hctx hs hgrain hcopy hex bh h

/-! ## `refine` in the simulation form, reduced -/

/-- **`substEnv` of an unknown by a refinement it means, in the simulation form**: every position
means the same (the substitution lemma for unknowns, the analogue of `meanV_substLoan` and
`run_substLoan`, with [Seal]'s re-run of a changed sealed program meaning the same), the shape,
sites and labels are untouched (a refinement holds no loan), and `Good` and the context are kept.
Open: the analogue of `RunSubst.lean` for unknowns is not written. -/
theorem substEnv_abs_sim (fuel : Nat) (st st' : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hσ : ∀ ψ H, ρ σ = meanV K ρ ψ H r)
    (h : Runs (Ochr.substEnv fuel (.abs σ) r true) st b () st') :
    Rel K ρ φ π st' s ∧ Good K.dm K.M K.Γ ρ st' ∧ CtxOk K ρ st' := by
  sorry

/-- Recording a refinement changes nothing the relation reads (it reads Ω and the counter). -/
theorem rel_refs (st : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π { st with refs := (σ, r) :: st.refs } s := ⟨hs.1, hs.2, hs.3, hs.4, hs.5⟩

/-- **Recording a refinement keeps `Good` and the context** where the assignment makes the
refinement true (the relation's half is `rel_refs`). Open: `Good`'s path conditions. -/
theorem refs_sim (st : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hσ : ∀ ψ H, ρ σ = meanV K ρ ψ H r) :
    Rel K ρ φ π { st with refs := (σ, r) :: st.refs } s ∧ Good K.dm K.M K.Γ ρ { st with refs := (σ, r) :: st.refs } ∧
      CtxOk K ρ { st with refs := (σ, r) :: st.refs } := by
  sorry

/-- **The re-normalisation after a refinement keeps the relation** (`renormAll`: every sealed
program the refined unknown's records mention re-runs, meaning the same, [Seal]). Open. -/
theorem renormAll_sim (fuel : Nat) (st st' : MState) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.renormAll fuel) st b () st') :
    Rel K ρ φ π st' s ∧ Good K.dm K.M K.Γ ρ st' ∧ CtxOk K ρ st' := by
  sorry

/-- **`refine` in the simulation form**, assembled: the substitution, the record, the
re-normalisation. The refinement means `ρ σ` at every future and hint (it holds no loan and
records its parameters). -/
theorem refine_sim' (fuel : Nat) (st st' : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hσ : ∀ ψ H, ρ σ = meanV K ρ ψ H r)
    (h : Runs (Ochr.refine (fuel + 1) σ r) st b () st') :
    Rel K ρ φ π st' s ∧ Good K.dm K.M K.Γ ρ st' ∧ CtxOk K ρ st' := by
  unfold Ochr.refine at h
  obtain ⟨_, st₁, b₁, hsub, h1⟩ := Runs.bind_inv h
  obtain ⟨hs₁, hg₁, hctx₁⟩ := substEnv_abs_sim K ρ φ fuel st st₁ σ r s π b hg hctx hs hσ hsub
  obtain ⟨_, st₂, b₂, hmod, h2⟩ := Runs.bind_inv h1
  obtain ⟨L, left, log, hmod⟩ := hmod
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at hmod
  obtain ⟨⟨-, hst₂⟩, -⟩ := hmod
  obtain ⟨hs₂, hg₂, hctx₂⟩ := refs_sim K ρ φ st₁ σ r s π hg₁ hctx₁ hs₁ hσ
  rw [hst₂] at hs₂ hg₂ hctx₂
  obtain ⟨g, st₃, b₃, hget, h3⟩ := Runs.bind_inv h2
  obtain ⟨L, left, log, hget⟩ := hget
  simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at hget
  obtain ⟨⟨hg3, hst3⟩, -⟩ := hget
  rw [← hst3, ← hg3] at h3
  split at h3
  · exact renormAll_sim K ρ φ fuel st₂ st' s π b₃ hg₂ hctx₂ hs₂ h3
  · obtain ⟨L, left, log, h3⟩ := h3
    simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h3
    rw [← h3.1.2]
    exact ⟨hs₂, hg₂, hctx₂⟩

end

end Ochr.Meaning.Steps
