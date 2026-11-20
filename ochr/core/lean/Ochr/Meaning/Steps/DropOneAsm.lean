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

/-- **A borrow is found only at a root** ((WF1): a borrow is the whole value of its position, never
inside another value, and nothing below a borrow's content holds one). -/
theorem follow_borrow_root {env : Env} {pos : Pos} {ss : List Step} {l : Nat} {w : Value}
    (hwf : WF1 env) (hp : pos ∈ allPos env) (h : (valAt env pos).follow ss = some (.borrow l w)) :
    ss = [] := by
  cases ss with
  | nil => rfl
  | cons s₁ ss' =>
    exfalso
    have hb : (Value.borrow l w).hasBorrow = true := by simp [Value.hasBorrow, Value.anyAtom]
    have hwf1 := hwf.1 pos hp
    cases hv : valAt env pos with
    | borrow m w' =>
      rw [hv] at hwf1 h
      cases s₁ with
      | deref =>
        simp only [Value.follow, stepV, Option.bind_some] at h
        exact hwf1 (anyAtom_of_follow ss' w' _ h hb)
      | proj _ | field _ => simp [Value.follow, stepV] at h
    | _ => rw [hv] at hwf1 h; exact hwf1 (anyAtom_of_follow _ _ _ h hb)

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

/-- **The checker's access keeps its run context** (it ends borrows: no global or declaration
changes). An end of a borrow of a dependent type may keep an unknown nothing names (`repackCheck`,
docs/31 D35, measured): `DeltaOk` asks nothing of it. `Good` is needed: a state that already
names the counter would have the kept unknown named, with `K.Δ` free there. Open: not tried. -/
theorem access_ctx (fuel : Nat) (st st' : MState) (q : Place) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
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
  rcases hcases with ⟨hno, hst⟩ | ⟨l, w', hbw, st₁, b₁, b₂, hlog, hend⟩ | ⟨v, hv, -, -, b₁, hcr⟩ |
      ⟨v, hv, hb, hbot, hproof, st₁, st₂, st₃, b₁, b₂, b₃, b₄, hcr, hacc, hlog, hset⟩
  · -- missing, ⊥ or ⋆: both do nothing
    rw [hst]
    rcases hno with hn | hn
    · rw [hw] at hn; cases hn
    have hlp : lentPrefix s pos q.steps.2 = none := by
      rcases hn with hn | hn
      · exact lentPrefix_none_of_noop K ρ φ st s π q pos hg hs hres hn
      · exact lentPrefix_none_of_proof K ρ φ st s π q pos hg hs hres hcopy hn
    have hpre : accessLentPrefix pos q.steps.2 s = s := by simp [accessLentPrefix, hlp]
    rw [hpre]
    obtain ⟨cbot, cproof⟩ := content_follow K ρ φ st s π q pos hg hs hres
    rcases hn with hn | hn
    · obtain ⟨T, hT⟩ := cbot hn
      unfold dropAt; rw [hT]; exact ⟨hs, hg⟩
    · obtain ⟨T, hT⟩ := cproof hn
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
    have hs₂' := (lentPrefix_absorbed K ρ φ st st₂ s π pos q.steps.2 v hg hs hp hv).mpr hs₂
    have hctx₂ := access_ctx K ρ fuel st st₂ q b₂ hg hctx hacc
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
theorem dropAtJoin_ctx (fuel : Nat) (st st' : MState) (q : Place) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (h : Runs (Ochr.dropAtJoin (fuel + 1) q) st b () st') :
    CtxOk K ρ st' ∧ st.absTy.size ≤ st'.absTy.size := by
  sorry

theorem runCtx_with_self (K : RunCtx) : ({ K with Δ := K.Δ } : RunCtx) = K := by cases K; rfl

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
    Rel K ρ φ π st' s ∧ Good K.dm K.M K.Γ ρ st' ∧ CtxOk K ρ st' ∧ st.absTy.size ≤ st'.absTy.size := by
  sorry

/-- Recording a refinement changes nothing the relation reads (it reads Ω and the counter). -/
theorem rel_refs (st : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π { st with refs := (σ, r) :: st.refs } s := ⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6⟩

theorem mem_of_lookup {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: rest, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      have e : a = k := by simpa using hk
      subst e
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- (WF6): an η record names only typed unknowns. -/
theorem Good.eta_bound {C : CodeMeaning} {ρ : Assignment} {st : MState} (hg : Good K.dm C K.Γ ρ st)
    {σ : Nat} {r : Value} (h : (σ, r) ∈ st.etaRefs) :
    σ < st.absTy.size ∧ ∀ τ, r.hasAbs τ = true → τ < st.absTy.size :=
  ⟨hg.2.2.2.2.2.2.1.1 σ (.eta σ r h (.inl rfl)), fun τ hτ => hg.2.2.2.2.2.2.1.1 τ (.eta σ r h (.inr hτ))⟩

/-- **Recording a refinement keeps `Good` and the context** where the assignment makes the
refinement true: the record is `TypedAssignment.refs`'s path condition (`hσ` at the closed future
and `σ`'s type), it names typed unknowns only ((WF6), `hb`), and nothing else reads `refs` (the
relation's half is `rel_refs`). -/
theorem refs_sim (st : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hσ : ∀ ψ H, ρ σ = meanV K ρ ψ H r)
    (hb : σ < st.absTy.size ∧ ∀ τ, r.hasAbs τ = true → τ < st.absTy.size) :
    Rel K ρ φ π { st with refs := (σ, r) :: st.refs } s ∧ Good K.dm K.M K.Γ ρ { st with refs := (σ, r) :: st.refs } ∧
      CtxOk K ρ { st with refs := (σ, r) :: st.refs } := by
  obtain ⟨ta, mem, wf⟩ := hg
  have hrefd : ∀ τ, ({ st with refs := (σ, r) :: st.refs } : MState).Refd τ → st.Refd τ :=
    fun τ h => refd_of_same (st := st) (st' := { st with refs := (σ, r) :: st.refs }) rfl rfl rfl rfl rfl h
  have w6 := wf.2.2.2.2.1
  refine ⟨rel_refs K ρ φ st σ r s π hs, ⟨⟨fun τ hr hlt => ta.mem τ (hrefd τ hr) hlt, ta.neutral, ta.eta, ?_⟩,
    ⟨mem.pos, fun τ hr hlt => mem.absTy τ (hrefd τ hr) hlt, mem.goal⟩,
    ⟨wf.1, wf.2.1, wf.2.2.1, wf.2.2.2.1,
      ⟨fun τ hr => w6.1 τ (hrefd τ hr), w6.2.1, fun τ v hv => (List.mem_cons.mp hv).elim
        (fun h => by simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hb)
        (fun h => w6.2.2.1 τ v h), w6.2.2.2⟩, wf.2.2.2.2.2⟩⟩,
    ⟨hctx.1, hctx.2, fun τ hr hlt => hctx.3 τ (hrefd τ hr) hlt, hctx.4, ⟨hctx.5.1, hctx.5.2, hctx.5.3, hctx.5.4⟩,
      hctx.6.of_sameDec rfl rfl, hctx.7.of_sameDec rfl rfl rfl⟩⟩
  intro τ v hv
  rcases List.mem_cons.mp hv with h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hσ (fun _ => .err) (.plain (MState.absTyM K.dm K.M K.Γ ρ st τ))]
    exact (meanV_eq_mean_aux K ρ (fun _ => .err) _ v).symm
  · exact ta.refs τ v h

/-- **The re-normalisation after a refinement keeps the relation** (`renormAll`: every sealed
program the refined unknown's records mention re-runs, meaning the same, [Seal]). Open. -/
theorem renormAll_sim (fuel : Nat) (st st' : MState) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.renormAll fuel) st b () st') :
    Rel K ρ φ π st' s ∧ Good K.dm K.M K.Γ ρ st' ∧ CtxOk K ρ st' ∧ st.absTy.size ≤ st'.absTy.size := by
  sorry

/-- **`refine` in the simulation form**, assembled: the substitution, the record, the
re-normalisation. The refinement means `ρ σ` at every future and hint (it holds no loan and
records its parameters). -/
theorem refine_sim' (fuel : Nat) (st st' : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hσ : ∀ ψ H, ρ σ = meanV K ρ ψ H r)
    (hb : σ < st.absTy.size ∧ ∀ τ, r.hasAbs τ = true → τ < st.absTy.size)
    (h : Runs (Ochr.refine (fuel + 1) σ r) st b () st') :
    Rel K ρ φ π st' s ∧ Good K.dm K.M K.Γ ρ st' ∧ CtxOk K ρ st' ∧ st.absTy.size ≤ st'.absTy.size := by
  unfold Ochr.refine at h
  obtain ⟨_, st₁, b₁, hsub, h1⟩ := Runs.bind_inv h
  obtain ⟨hs₁, hg₁, hctx₁, hsz₁⟩ := substEnv_abs_sim K ρ φ fuel st st₁ σ r s π b hg hctx hs hσ hsub
  obtain ⟨_, st₂, b₂, hmod, h2⟩ := Runs.bind_inv h1
  obtain ⟨L, left, log, hmod⟩ := hmod
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at hmod
  obtain ⟨⟨-, hst₂⟩, -⟩ := hmod
  obtain ⟨hs₂, hg₂, hctx₂⟩ := refs_sim K ρ φ st₁ σ r s π hg₁ hctx₁ hs₁ hσ
    ⟨Nat.lt_of_lt_of_le hb.1 hsz₁, fun τ hτ => Nat.lt_of_lt_of_le (hb.2 τ hτ) hsz₁⟩
  rw [hst₂] at hs₂ hg₂ hctx₂
  have hsz₂ : st.absTy.size ≤ st₂.absTy.size := by rw [← hst₂]; exact hsz₁
  obtain ⟨g, st₃, b₃, hget, h3⟩ := Runs.bind_inv h2
  obtain ⟨L, left, log, hget⟩ := hget
  simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at hget
  obtain ⟨⟨hg3, hst3⟩, -⟩ := hget
  rw [← hst3, ← hg3] at h3
  split at h3
  · obtain ⟨a, b', c, d⟩ := renormAll_sim K ρ φ fuel st₂ st' s π b₃ hg₂ hctx₂ hs₂ h3
    exact ⟨a, b', c, Nat.le_trans hsz₂ d⟩
  · obtain ⟨L, left, log, h3⟩ := h3
    simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h3
    rw [← h3.1.2]
    exact ⟨hs₂, hg₂, hctx₂, hsz₂⟩

/-! ## `generalizeNeutral` in the simulation form, reduced -/

/-- What the generalisation needs of the type `placeType` gives the new unknown (`T`, the type of
the place holding the program `n`): a type of the state (its unknowns typed), of some level,
holding no loan, a borrow type only at its top; `n`'s unknowns typed too, and `n` a member of `T`. -/
structure GenTy (st : MState) (T n : Value) : Prop where
  abs : ∀ τ, T.hasAbs τ = true → τ < st.absTy.size
  nabs : ∀ τ, n.hasAbs τ = true → τ < st.absTy.size
  loanFree : ∀ l, T.hasLoan l = false
  refOk : T.refMisplaced = false
  level : (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T).level.isSome
  mem : meanV K ρ (fun _ => .err) (.plain (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T)) n ∈ₛ
    Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T

/-- **`placeType` in the simulation form.** The field and parameter types it evaluates run on
private copies (`inStatement`, `privately`), so Ω is the snapshot's (`Rel.private_copy` is the
relation's half); the unknowns and records the copies keep (D37) are given values and types by an
extension; and the type returned is a `GenTy` for the place's sealed, loan-free content (a member
of the place's type, by membership at the place's position and the typing of a path). Open. -/
theorem placeType_sim (fuel : Nat) (st st₁ : MState) (p : Place) (n T : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hn : ckContent st.env p = some n) (hsealed : ∃ t, n = .sealed t) (hfree : ∀ l, n.hasLoan l = false)
    (h : Runs (Ochr.placeType fuel p) st b T st₁) :
    ∃ (ρ₁ : Assignment) (Δ₁ : Nat → TyS), (∀ τ, τ < st.absTy.size → ρ₁ τ = ρ τ ∧ Δ₁ τ = K.Δ τ) ∧
      st₁.env = st.env ∧ st.absTy.size ≤ st₁.absTy.size ∧
      CtxOk { K with Δ := Δ₁ } ρ₁ st₁ ∧ Rel { K with Δ := Δ₁ } ρ₁ φ π st₁ s ∧
      Good K.dm ({ K with Δ := Δ₁ } : RunCtx).M K.Γ ρ₁ st₁ ∧ GenTy { K with Δ := Δ₁ } ρ₁ st₁ T n := by
  sorry

/-- `freshAbs` names the unknown by the counter and pushes its type. -/
theorem runs_freshAbs_inv {T : Value} {st st' : MState} {b σ : Nat} (h : Runs (Ochr.freshAbs T) st b σ st') :
    σ = st.nextAbs ∧ st' = { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T } := by
  obtain ⟨L, left, log, h⟩ := h
  simp only [Ochr.freshAbs, runMachineL_bind, runMachineL_get, runMachineL_set, runMachineL_pure,
    Prod.mk.injEq, Outcome.ok.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm⟩

/-- `trace` writes the log only. -/
theorem runs_trace_inv {m : Unit → String} {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (Ochr.trace m) st b u st') : st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  unfold Ochr.trace at h
  simp only [runMachineL_bind, runMachineL_get] at h
  split at h <;> simp_all [runMachineL_modifyThe_log, runMachineL_pure]

/-- (WF6): the counter of unknowns is the number typed. -/
theorem Good.absTy_size {C : CodeMeaning} {ρ : Assignment} {st : MState} (hg : Good K.dm C K.Γ ρ st) :
    st.absTy.size = st.nextAbs :=
  hg.2.2.2.2.2.2.1.2.2.2.1

/-- **A fresh unknown of a well-formed type** (`freshAbs`). Nothing in the state names it yet, so
under any value for it, with its type added to Δ, the relation, `Good`, the context and the
`GenTy` are kept, and the program and its type read the same (neither holds the new unknown).
Open: needs that a meaning reads the assignment and Δ only at the unknowns the value holds (the
assignment's analogue of `RunCongr.meanV_congrE`, not written). -/
theorem freshAbs_sim (st : MState) (T n : Value) (s : SState) (π : Nat → Nat) (v : Sem)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s) (hT : GenTy K ρ st T n) :
    ∃ Δ' : Nat → TyS, (∀ τ, τ < st.absTy.size → Δ' τ = K.Δ τ) ∧
      CtxOk { K with Δ := Δ' } (ρ.ext st.nextAbs v) { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T } ∧
      Rel { K with Δ := Δ' } (ρ.ext st.nextAbs v) φ π { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T } s ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ (ρ.ext st.nextAbs v)
        { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T } ∧
      GenTy { K with Δ := Δ' } (ρ.ext st.nextAbs v) { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T } T n ∧
      meanV { K with Δ := Δ' } (ρ.ext st.nextAbs v) (fun _ => .err)
          (.plain (Value.tyM K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ (ρ.ext st.nextAbs v) (fun _ => .err) T)) n =
        meanV K ρ (fun _ => .err) (.plain (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T)) n := by
  sorry

/-- **`substEnv` of a sealed program by an unknown that means it, then the record `n := σ`.** Every
position means the same (the substitution lemma, a program replaced by an unknown: the converse of
`substEnv_abs_sim`, with [Seal]'s re-run of a changed sealed program meaning the same), the types
of the unknowns mean the same, and the record is the path condition the assignment already meets
(`hσ`); `Good` and the context are kept. Open: the substitution lemma is not written. -/
theorem substEnv_neutral_sim (fuel : Nat) (st st' : MState) (p : Place) (n T : Value) (σ : Nat) (s : SState)
    (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hn : ckContent st.env p = some n) (hsealed : ∃ t, n = .sealed t) (hfree : ∀ l, n.hasLoan l = false)
    (hT : GenTy K ρ st T n) (hσT : st.absTy[σ]? = some T) (hσn : n.hasAbs σ = false)
    (hσ : ρ σ = meanV K ρ (fun _ => .err) (.plain (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T)) n)
    (h : Runs (Ochr.substEnv fuel n (.abs σ) true) st b () st') :
    Rel K ρ φ π st' s ∧ Good K.dm K.M K.Γ ρ { st' with neutrals := (n, σ) :: st'.neutrals } ∧
      CtxOk K ρ { st' with neutrals := (n, σ) :: st'.neutrals } ∧ st.absTy.size ≤ st'.absTy.size := by
  sorry

/-- Recording a generalisation changes nothing the relation reads. -/
theorem rel_neutrals (st : MState) (x : List (Value × Nat)) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π { st with neutrals := x } s := ⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6⟩

/-- **`generalizeNeutral` in the simulation form, with an extended context**, assembled: the
place's type, the fresh unknown, the substitution and the record. The sealed program `n` at `p`
becomes a fresh unknown `σ` with the record `n := σ`; under an assignment extended by `σ := ⟦n⟧`
(read at `σ`'s type) and Δ by `σ`'s type, and at the unknowns `placeType`'s private copies keep,
the states stay related to the same reference state. `n` is `p`'s content, a sealed program
holding no loan, as at both callers; without the first the statement was false
(`Regress/GenNeutralContent.lean`). The extension is existential, as in every step that creates
unknowns: `placeType`'s copies keep their unknowns and records (D37), which must be given values. -/
theorem generalizeNeutral_sim (fuel : Nat) (st st' : MState) (p : Place) (n : Value) (σ : Nat) (s : SState)
    (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hn : ckContent st.env p = some n) (hsealed : ∃ t, n = .sealed t) (hfree : ∀ l, n.hasLoan l = false)
    (h : Runs (Ochr.generalizeNeutral fuel p n) st b σ st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ τ, τ < st.absTy.size → ρ' τ = ρ τ ∧ Δ' τ = K.Δ τ) ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π st' s ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' ∧ st.absTy.size ≤ st'.absTy.size := by
  cases fuel with
  | zero =>
    obtain ⟨L, left, log, h⟩ := h
    simp [Ochr.generalizeNeutral, runMachineL_exhausted] at h
  | succ fuel =>
  unfold Ochr.generalizeNeutral at h
  obtain ⟨T, st₁, b₁, hpt, h1⟩ := Runs.bind_inv h
  obtain ⟨ρ₁, Δ₁, hext₁, henv₁, hsz₁, hctx₁, hs₁, hg₁, hT₁⟩ :=
    placeType_sim K ρ φ fuel st st₁ p n T s π b hg hctx hs hn hsealed hfree hpt
  have hn₁ : ckContent st₁.env p = some n := by rw [henv₁]; exact hn
  obtain ⟨σ', st₂, b₂, hfa, h2⟩ := Runs.bind_inv h1
  obtain ⟨rfl, rfl⟩ := runs_freshAbs_inv hfa
  let v := meanV { K with Δ := Δ₁ } ρ₁ (fun _ => .err)
    (.plain (Value.tyM K.dm ({ K with Δ := Δ₁ } : RunCtx).M K.Γ ρ₁ (fun _ => .err) T)) n
  obtain ⟨Δ₂, hext₂, hctx₂, hs₂, hg₂, hT₂, hv⟩ :=
    freshAbs_sim { K with Δ := Δ₁ } ρ₁ φ st₁ T n s π v hg₁ hctx₁ hs₁ hT₁
  have hsize₁ : st₁.absTy.size = st₁.nextAbs := Good.absTy_size { K with Δ := Δ₁ } hg₁
  obtain ⟨u, st₃, b₃, htr, h3⟩ := Runs.bind_inv h2
  have hst₃ := runs_trace_inv htr
  subst hst₃
  obtain ⟨u', st₄, b₄, hsub, h4⟩ := Runs.bind_inv h3
  have hσT : ({ st₁ with nextAbs := st₁.nextAbs + 1, absTy := st₁.absTy.push T } : MState).absTy[st₁.nextAbs]? = some T := by
    simp only [← hsize₁, Array.getElem?_push_size]
  have hσn : n.hasAbs st₁.nextAbs = false := by
    cases e : n.hasAbs st₁.nextAbs
    · rfl
    · have := hT₁.nabs _ e; omega
  have hσ : (ρ₁.ext st₁.nextAbs v) st₁.nextAbs = meanV { K with Δ := Δ₂ } (ρ₁.ext st₁.nextAbs v) (fun _ => .err)
      (.plain (Value.tyM K.dm ({ K with Δ := Δ₂ } : RunCtx).M K.Γ (ρ₁.ext st₁.nextAbs v) (fun _ => .err) T)) n := by
    simp only [Assignment.ext, if_pos rfl]; exact hv.symm
  obtain ⟨hs₄, hg₄, hctx₄, hsz₄⟩ := substEnv_neutral_sim { K with Δ := Δ₂ } (ρ₁.ext st₁.nextAbs v) φ fuel _ st₄ p n T
    st₁.nextAbs s π b₃ hg₂ hctx₂ hs₂ hn₁ hsealed hfree hT₂ hσT hσn hσ hsub
  obtain ⟨L, left, log, h4⟩ := h4
  simp only [runMachineL_bind, runMachineL_modify, runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h4
  obtain ⟨⟨-, rfl⟩, -⟩ := h4
  have hpush : st₁.absTy.size ≤ (st₁.absTy.push T).size := by simp
  refine ⟨ρ₁.ext st₁.nextAbs v, Δ₂, fun τ hτ => ?_, hctx₄, rel_neutrals { K with Δ := Δ₂ } _ φ st₄ _ s π hs₄, hg₄,
    Nat.le_trans hsz₁ (Nat.le_trans hpush hsz₄)⟩
  have hτ₁ : τ < st₁.absTy.size := Nat.lt_of_lt_of_le hτ hsz₁
  have hne : τ ≠ st₁.nextAbs := by omega
  refine ⟨?_, ?_⟩
  · simp only [Assignment.ext, if_neg hne]; exact (hext₁ τ hτ).1
  · rw [hext₂ τ hτ₁]; exact (hext₁ τ hτ).2

end

end Ochr.Meaning.Steps
