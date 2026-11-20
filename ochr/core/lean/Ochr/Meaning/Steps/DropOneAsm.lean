import Ochr.Meaning.Steps.DropRuns
import Ochr.Meaning.Steps.BotWriteGood
import Ochr.Meaning.Steps.Slice.Shapes

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

/-- **The reference's drop of a data place is its access then its write** (`dropAt`'s last clause):
where the place is no holder at a root, it is no copy, and the write can be made at the typed
future after the access. PROVED. (Restated with `dropAt`, the slice: it asked the reading after the
access to exist and not be `⋆`, the test `dropAt` no longer makes.) -/
theorem dropAt_data (s : SState) (q : Place) (pos : Pos) (steps : List Step)
    (hns : steps = [] → s.shape pos = none)
    (hupd : ∃ y, Sem.updAt K.dm K.Γ ((s.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps
      ((s.access pos (dataHit steps)).valAt pos ((s.access pos (dataHit steps)).typedFuture φ)) = some y)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false) :
    dropAt K φ q pos steps s = (s.access pos (dataHit steps)).setAt pos fun φ' =>
      (Sem.updAt K.dm K.Γ ((s.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps
        ((s.access pos (dataHit steps)).valAt pos φ')).getD .err := by
  obtain ⟨y, hy⟩ := hupd
  unfold dropAt
  split
  · next h2 => rw [hns rfl] at h2; cases h2
  · dsimp only
    simp only [hcopy, Bool.false_eq_true, if_false]
    rw [hy]

/-- **Nothing is lent at a root holding `⋆`** (`⋆` holds no loan, mark or sealed program). -/
theorem clear_of_proof_root {env : Env} {pos : Pos} (hproof : valAt env pos = .proof) :
    ∀ l, ∀ x ∈ Env.sitesOf env l, x.pos ≠ pos := by
  intro l x hx hxp
  simp only [Env.sitesOf, List.mem_flatMap] at hx
  obtain ⟨p, -, hxv⟩ := hx
  have hpp : x.pos = p := (sitesOf_prefix l p [] _ x hxv).1
  rw [hxp] at hpp; subst hpp
  rw [hproof] at hxv
  simp [Value.sitesOf] at hxv

/-- A write along a path finds the path. -/
theorem follow_of_updAt (f : Value → Value) (ss : List Step) (v v' : Value)
    (h : Value.updAt f ss v = some v') : ∃ c, v.follow ss = some c := by
  fun_induction Value.updAt f ss v generalizing v' with
  | case1 v => exact ⟨v, rfl⟩
  | case2 ss l w hne ih =>
    obtain ⟨w', hw', -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c, hc⟩ := ih w' hw'
    cases ss with
    | nil => exact absurd rfl hne
    | cons x ss => exact ⟨c, by simpa [Value.follow, stepV] using hc⟩
  | case3 ss l w ih =>
    obtain ⟨w', hw', -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c, hc⟩ := ih w' hw'
    exact ⟨c, by simpa [Value.follow, stepV] using hc⟩
  | case4 ss w ih =>
    obtain ⟨w', hw', -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c, hc⟩ := ih w' hw'
    exact ⟨c, by simpa [Value.follow, stepV] using hc⟩
  | case5 =>
    rename_i hi ih
    obtain ⟨w', hw', -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c, hc⟩ := ih w' hw'
    exact ⟨c, by simp [Value.follow, stepV, hi, hc]⟩
  | case6 => simp_all
  | case7 =>
    rename_i hi ih
    obtain ⟨w', hw', -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c, hc⟩ := ih w' hw'
    refine ⟨c, ?_⟩
    simp only [Value.follow, stepV]
    rw [dite_eq_ite] at hi
    rw [hi]
    simpa using hc
  | case8 => simp_all
  | case9 => simp_all

/-- A place with no steps is a variable. -/
theorem place_eq_var_of_nil {q : Place} (h : q.steps.2 = []) : q = .var q.steps.1 := by
  cases q with
  | var i => rfl
  | deref p | proj _ p | field _ p => simp [Place.steps] at h

/-- **What the write of `⊥` needs, at the drop** (`botWrite_rel`'s hypotheses after the access and
the log): the place is at a binding of the reference's positions, a whole root written is not a
holder (the reference's root is none, `hns`), the value records its parameters (WF10) and holds no
sealed program whose tail reads the hint ((WF16); docs/31 D45: first, no sealed program at all,
false of a value with a closed-off call in a field), and the path conditions of the write hold
along the place (`natAlong_grain`: the typing of places at every prefix). PROVED (docs/31 D47).
(Until D59 a whole root written also had to hold no type value, through (Ty): the binding's
structure was read off the value it held.) -/
theorem botWrite_hyps (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos) (v' : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hsh : ShapeFacts K.D K.Γ st) (hs : Rel K ρ φ π st s)
    (hck : ckVarPos st.env q.steps.1 = some pos) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hns : q.steps.2 = [] → s.shape pos = none)
    (hv : Value.updAt (fun _ => .bot) q.steps.2 (valAt st.env pos) = some v') :
    ∃ f i, pos = .bind f i ∧ Pos.bind f i ∈ allPos st.env ∧ Pos.bind f i ∈ s.positions ∧
      (q.steps.2 = [] → Env.shape st.env pos = none) ∧
      ((valAt st.env pos).anyAtom (Value.bareCtor K.Γ) = false ∧
        (valAt st.env pos).anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false) ∧
      ∀ ψ, NatAlong K.dm K.M K.Γ ρ ψ q.steps.2 (valAt st.env pos) := by
  have hp := ckVarPos_mem hck
  have hsc := rel_scopeOf K ρ φ hs
  have hgr : GrainOk K.D K.Γ (DecideScope.topReadings st) q := by rw [← hsc]; exact hgrain
  have hmem : valAt st.env pos ∈ Env.values st.env := List.mem_map.mpr ⟨pos, hp, rfl⟩
  have hres := rel_resolve_ck K ρ φ st s π q pos hs hck
  have hsp : pos ∈ s.positions := by
    simp only [resolve] at hres
    obtain ⟨pos', hvp, he⟩ := Option.map_eq_some_iff.mp hres
    simp only [Prod.mk.injEq] at he; rw [← he.1]; exact varPos_mem hvp
  have hbind : ∃ f i, pos = .bind f i := by
    unfold ckVarPos at hck; split at hck
    · simp only [Option.some.injEq] at hck; exact ⟨_, _, hck.symm⟩
    · cases hck
  obtain ⟨f, i, rfl⟩ := hbind
  refine ⟨f, i, rfl, hp, hsp, ?_, ⟨hg.2.2.2.2.2.2.2.2.2.2.1 _ hmem, hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ hmem⟩, ?_⟩
  · intro he
    cases hsh : Env.shape st.env (.bind f i) with
    | none => rfl
    | some l =>
      have := hs.sim.2.1 (.bind f i) l (by simp [IsTemp]) hsh
      rw [hns he] at this; cases this
  · intro ψ
    refine natAlong_grain K ρ hsh ψ (fun _ => .bot) q.steps.2 (.var q.steps.1) _
      (grainOk_of_steps (by rw [jdExtend_steps]; simp [Place.steps]) hgr) ?_ (by rw [hv]; rfl)
    unfold ckContent; simp [Place.steps, hck, Value.follow]

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

theorem runCtx_with_self (K : RunCtx) : ({ K with Δ := K.Δ } : RunCtx) = K := by cases K; rfl

theorem runCtx_with_self' (K : RunCtx) : ({ K with Δ := K.Δ } : RunCtx) = K := by cases K; rfl

/-- **A value naming only old unknowns means the same under an extension** of the assignment and
`Δ` (leaf; `AssignCongr.meanV_congrA` for the assignment, and `Δ` read only at the unknowns a value
holds). The decisions are not extended since the slice's change of form (main's decision,
2026-11-20), so the decisions' half of this lemma is gone. -/
theorem meanV_ext {n : Nat} {ρ' : Assignment} {Δ' : Nat → TyS} (v : Value) (ψ : Future) (hint : TyS)
    (hv : ∀ σ, v.hasAbs σ = true → σ < n) (ha : ∀ σ, σ < n → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) :
    meanV { K with Δ := Δ' } ρ' ψ hint v = meanV K ρ ψ hint v := by
  sorry

/-- From `st` (related to some reference state under `K`, `ρ`) to `st'`, related to `s'` under an
assignment and a `Δ` extended at the unknowns created (docs/31 D71's rule), with `Good` and the
context kept; the decisions are the context's, fixed for the run (main's decision 2026-11-20). -/
structure Ext (π : Nat → Nat) (st st' : MState) (s' : SState) (ρ' : Assignment) (Δ' : Nat → TyS) : Prop where
  size : st.absTy.size ≤ st'.absTy.size
  agree : ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ
  ctx : CtxOk { K with Δ := Δ' } ρ' st'
  rel : Rel { K with Δ := Δ' } ρ' φ π st' s'
  good : Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st'

theorem Ext.refl {π : Nat → Nat} {st : MState} {s : SState} (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hs : Rel K ρ φ π st s) : Ext K ρ φ π st st s ρ K.Δ :=
  ⟨Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, by rw [runCtx_with_self K]; exact hctx,
    by rw [runCtx_with_self K]; exact hs, by rw [runCtx_with_self K]; exact hg⟩

theorem Ext.trans {π : Nat → Nat} {st st₁ st₂ : MState} {s₁ s₂ : SState} {ρ₁ ρ₂ : Assignment} {Δ₁ Δ₂ : Nat → TyS}
    (h₁ : Ext K ρ φ π st st₁ s₁ ρ₁ Δ₁) (h₂ : Ext { K with Δ := Δ₁ } ρ₁ φ π st₁ st₂ s₂ ρ₂ Δ₂) :
    Ext K ρ φ π st st₂ s₂ ρ₂ Δ₂ where
  size := Nat.le_trans h₁.size h₂.size
  agree σ hσ := by
    obtain ⟨a, b⟩ := h₂.agree σ (Nat.lt_of_lt_of_le hσ h₁.size)
    obtain ⟨c, d⟩ := h₁.agree σ hσ
    exact ⟨a.trans c, b.trans d⟩
  ctx := h₂.ctx
  rel := h₂.rel
  good := h₂.good

/-- The same state, the reference state replaced by one the checker's is also related to. -/
theorem Ext.with_rel {π : Nat → Nat} {st st' : MState} {s' s'' : SState} {ρ' : Assignment} {Δ' : Nat → TyS} (h : Ext K ρ φ π st st' s' ρ' Δ') (hr : Rel { K with Δ := Δ' } ρ' φ π st' s'') :
    Ext K ρ φ π st st' s'' ρ' Δ' :=
  ⟨h.size, h.agree, h.ctx, hr, h.good⟩

/-- A step's conclusion in the induction hypothesis's form (`ExtOk` and the relation), as an `Ext`. -/
theorem Ext.of_extOk {π : Nat → Nat} {st st' : MState} {s' : SState} {ρ' : Assignment} {Δ' : Nat → TyS} (hsz : st.absTy.size ≤ st'.absTy.size) (he : ExtOk K ρ st st' ρ' Δ')
    (hr : Rel { K with Δ := Δ' } ρ' φ π st' s') : Ext K ρ φ π st st' s' ρ' Δ' :=
  ⟨hsz, he.1, he.2.1, hr, he.2.2⟩

/-- The same state, related to another reference state, as an extension by nothing. -/
theorem Ext.same {π : Nat → Nat} {st : MState} {s' : SState} (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hs' : Rel K ρ φ π st s') : Ext K ρ φ π st st s' ρ K.Δ :=
  ⟨Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, by rw [runCtx_with_self K]; exact hctx,
    by rw [runCtx_with_self K]; exact hs', by rw [runCtx_with_self K]; exact hg⟩

/-- **The context after the drop's write of `⊥`** (leaf; it replaces the old `dropAtJoin_ctx`, whose
other parts are now the induction hypothesis's [Access] and [End] in the extended form). The write
changes one place's content to `⊥`: the declarations, globals and tables are the state's, `Δ` asks
of no new unknown (the write names none), the decisions are aligned after it (`hD`, the tables), and
`ShapeFacts` hold of a `⊥` part. What is open is the block's captures at the new state, whose entry
set the write changes (main's item 4: measured on recorded states first, not proved). -/
theorem ctx_botWrite (st : MState) (pos : Pos) (steps : List Step) (v' : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hv : Value.updAt (fun _ => .bot) steps (valAt st.env pos) = some v')
    (hD : DecTab K.D { st with env := Env.setAtE st.env pos v' }) :
    CtxOk K ρ { st with env := Env.setAtE st.env pos v' } := by
  sorry

/-- **The drop of one place where the place exists** (`dropOne_step`'s main case), assembled from
the named obligations and the induction hypothesis's [Access] and [End]: missing, `⊥` or `⋆` (both
sides do nothing); a borrow at a root (both end it); a copy (excluded: the join moves no copy);
data (both access, then write `⊥`/`moved`). In the extended form (main's item 3): the access and
the end extend the context, and the context after the write is `ctx_botWrite`. -/
theorem dropOne_exists (fuel : Nat) (ih : StepsIHBelow fuel)
    (st st' : MState) (q : Place) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (pos : Pos) (w : Value) (hck : ckVarPos st.env q.steps.1 = some pos)
    (hw : (valAt st.env pos).follow q.steps.2 = some w) (hD : DecTab K.D st')
    (b : Nat) (h : Runs (Ochr.dropAtJoin (fuel + 1) q) st b () st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), Ext K ρ φ π st st' (joinDropOne K φ s q) ρ' Δ' := by
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
  · -- missing, ⊥ or ⋆: the checker does nothing
    rw [hst]
    refine ⟨ρ, K.Δ, Ext.same K ρ φ hg hctx ?_⟩
    rcases hno with hn | hn
    · rw [hw] at hn; cases hn
    have hpt : ¬ IsTemp pos := by
      rcases pos with ⟨f, i⟩ | ⟨f, i⟩
      · simp [IsTemp]
      · unfold ckVarPos at hck; split at hck <;> cases hck
    rcases hn with hn | hn
    rotate_left
    · -- `⋆` at a place at the join's grain: a copy ((C⋆), true since main's D100), which the join
      -- does not drop
      exfalso
      have h := hctx.shapes.proofCopy q (by rw [← rel_scopeOf K ρ φ hs]; exact hgrain)
        (by unfold ckContent; simp [hck, hn])
      rw [← rel_scopeOf K ρ φ hs, hcopy] at h
      cases h
    -- `⊥`: a root holding it is no holder, in the reference either (`SimEq`'s holders)
    have hnb : q.steps.2 = [] → s.shape pos = none := by
      intro he
      cases hsp : s.shape pos with
      | none => rfl
      | some l' =>
        obtain ⟨l, hl, -⟩ := hs.sim.2.2.1 pos l' hpt hsp
        have hl' : Env.shape st.env pos = some l := hl
        have hn' := hn
        rw [he] at hn'; simp only [Value.follow, Option.some.injEq] at hn'
        rw [shape_eq_shapeOf, hn'] at hl'
        simp [shapeOf] at hl'
    have hlp : lentPrefix s pos q.steps.2 = none := lentPrefix_none_of_noop K ρ φ st s π q pos hg hs hres hn
    have hpre : accessLentPrefix pos q.steps.2 s = s := by simp [accessLentPrefix, hlp]
    rw [hpre]
    -- the reference's access of a place holding `⊥` ends nothing: nothing is lent over, at or under
    -- a `⊥` (`clear_of_bot`)
    have hclr := clear_of_bot hg.2.2.1 hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hn
    have hacc : s.access pos (dataHit q.steps.2) = s := by
      apply SState.access_of_unreached
      intro y hy
      obtain ⟨l, hl, rfl⟩ := rel_live_ref K ρ φ st s π hs hy
      unfold SState.reached
      rw [List.any_eq_false]
      intro x hx hpx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpx
      rw [hclr l hl x ((hs.sites l hl x).mp hx) hpx.1] at hpx
      exact Bool.false_ne_true hpx.2
    unfold dropAt
    split
    · next l h1 h2 => rw [hnb h1] at h2; cases h2
    · dsimp only
      rw [hacc]
      simp only [hcopy, Bool.false_eq_true, if_false]
      split
      · -- the write cannot be made (the path passes through a moved part): nothing
        exact hs
      · -- a place already moved: the reference writes `moved` over `moved`, which changes nothing
        -- the relation reads (docs/31 D52)
        have hself := updAt_bot_self q.steps.2 _ hn
        obtain ⟨f, i, hposfi, hpb, hsp, hroot, hplain, hnat⟩ :=
          botWrite_hyps K ρ φ st s π q pos _ hg hctx.shapes hs hck hgrain hnb hself
        subst hposfi
        have hrel := botWrite_rel K ρ φ st s π f i q.steps.2 _ hs hg.2.2.1 hpb hsp hself hroot
          (fun l hl x hx hxp => hclr l hl x hx hxp) hplain hnat
        rw [setAtE_self_bind st.env f i hpb] at hrel
        exact hrel
  · -- a borrow at a root: both end it
    have hsteps := follow_borrow_root hg.2.2.1 hp hbw
    have hval : valAt st.env pos = .borrow l w' := by
      rw [hsteps] at hbw; simpa [Value.follow] using hbw
    obtain ⟨hs₁, hg₁, hctx₁, henv₁⟩ := logEffect_rel K ρ φ st st₁ s π q "moves" b₁ hg hctx hs hlog
    obtain ⟨X₁, hX₁⟩ := runs_logEffect_inv hlog
    have hsz₁ : st.absTy.size ≤ st₁.absTy.size := by rw [hX₁]; exact Nat.le_refl _
    have hl : liveLoan st₁.env l = true := by rw [henv₁]; exact liveLoan_of_holder hp hval
    obtain ⟨hsz', ρ₂, Δ₂, e₂, hs'⟩ := (ih.at K ρ φ).endBorrow_step st₁ st' l s π hg₁ hctx₁ hs₁ hl hD b₂ hend
    have hsh : s.shape pos = some (π l) := by
      have hpt : ¬ IsTemp pos := by
        rcases pos with ⟨f, i⟩ | ⟨f, i⟩
        · simp [IsTemp]
        · unfold ckVarPos at hck; split at hck <;> cases hck
      exact hs.sim.2.1 pos l hpt (by show Env.shape st.env pos = some l; rw [shape_eq_shapeOf, hval]; rfl)
    rw [hsteps, accessLentPrefix_nil]
    have hd : dropAt K φ q pos [] s = s.endLabel (π l) := by
      unfold dropAt; rw [hsh]
    rw [hd]
    exact ⟨ρ₂, Δ₂, Nat.le_trans hsz₁ hsz', fun σ hσ => e₂.1 σ (Nat.lt_of_lt_of_le hσ hsz₁), e₂.2.1, hs', e₂.2.2⟩
  · -- a copy: excluded
    obtain ⟨-, hc⟩ := copyRead_aligned K ρ φ fuel st st' s π q true b₁ hctx hs hcr
    rw [hcopy] at hc; cases hc
  · -- data: both access, then write
    obtain ⟨hst₁, -⟩ := copyRead_aligned K ρ φ fuel st st₁ s π q false b₁ hctx hs hcr
    rw [hst₁] at hacc
    have hD₂ : DecTab K.D st₂ :=
      hD.back ((hlog.grows (grows_logEffect _ _)).trans (hset.grows (grows_setPlace _ _)))
    obtain ⟨hsz₂, ρ₂, Δ₂, e₂, hs₂⟩ := (ih.at K ρ φ).access_step st st₂ q pos false s π hg hctx hs hres hD₂ b₂ hacc
    simp only [Bool.false_and, Bool.false_eq_true, if_false] at hs₂
    have hs₂' : Rel { K with Δ := Δ₂ } ρ₂ φ π st₂ ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2)) := by
      rw [lentPrefix_absorbed_eq K ρ φ st s π pos q.steps.2 v hg hs hp hv]; exact hs₂
    obtain ⟨hs₃, hg₃, hctx₃, henv₃⟩ := logEffect_rel { K with Δ := Δ₂ } ρ₂ φ st₂ st₃ _ π q "moves" b₃ e₂.2.2 e₂.2.1 hs₂' hlog
    have hsh₃ := hctx₃.shapes
    obtain ⟨X₃, hX₃⟩ := runs_logEffect_inv hlog
    have hdecl : declsOf ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2)) = declsOf s := by
      rw [declsOf_access, declsOf_accessLentPrefix]
    have hres₁ : resolve ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2)) q =
        some (pos, q.steps.2) := by rw [resolve_of_declsOf hdecl]; exact hres
    obtain ⟨pos'', v', hck'', hupd, hst'⟩ := runs_setPlace_inv hset
    have hpp : pos'' = pos := by
      have := rel_resolve_ck { K with Δ := Δ₂ } ρ₂ φ st₃ _ π q pos'' hs₃ hck''
      rw [hres₁] at this
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact this.1.symm
    rw [hpp] at hck'' hupd hst'
    have hclear₂ := access_clears { K with Δ := Δ₂ } ρ₂ φ st₂ (accessLentPrefix pos q.steps.2 s) π pos q.steps.2 e₂.2.2 hs₂'
    have hclear₃ : ∀ l, liveLoan st₃.env l = true → ∀ x ∈ Env.sitesOf st₃.env l, x.pos = pos →
        dataHit q.steps.2 x.path = false := by rw [henv₃]; exact hclear₂
    have hgrain₁ : GrainOk K.D K.Γ (scopeOf ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2))) q := by
      rw [scopeOf_of_declsOf hdecl]; exact hgrain
    have hcopy₁ : K.D.copy (K.D.placeDecl (scopeOf ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2))) q) = false := by
      rw [scopeOf_of_declsOf hdecl]; exact hcopy
    have hns : q.steps.2 = [] → s.shape pos = none := by
      intro he
      have hpt : ¬ IsTemp pos := by
        rcases pos with ⟨f, i⟩ | ⟨f, i⟩
        · simp [IsTemp]
        · unfold ckVarPos at hck; split at hck <;> cases hck
      cases hsh : s.shape pos with
      | none => rfl
      | some l' =>
        obtain ⟨l, hl, -⟩ := hs.sim.2.2.1 pos l' hpt hsh
        have hl' : Env.shape st.env pos = some l := hl
        rw [he] at hv; simp only [Value.follow, Option.some.injEq] at hv
        rw [shape_eq_shapeOf, hv] at hl'
        cases v <;> simp [shapeOf] at hl'
        exact absurd rfl (hb _ _)
    have hns₀ : q.steps.2 = [] → (accessLentPrefix pos q.steps.2 s).shape pos = none := by
      intro he
      cases hsh : (accessLentPrefix pos q.steps.2 s).shape pos with
      | none => rfl
      | some l =>
        have := (shapeSub_accessLentPrefix pos q.steps.2 s).1 pos l hsh
        rw [hns he] at this; cases this
    have hns₁ : q.steps.2 = [] → ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2)).shape pos = none := by
      intro he
      cases hsh : ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2)).shape pos with
      | none => rfl
      | some l =>
        have := (SState.shapeSub_access _ pos _).1 pos l hsh
        rw [hns₀ he] at this; cases this
    have hcopy₀ : K.D.copy (K.D.placeDecl (scopeOf (accessLentPrefix pos q.steps.2 s)) q) = false := by
      rw [scopeOf_of_declsOf (declsOf_accessLentPrefix s pos q.steps.2)]; exact hcopy
    obtain ⟨f, i, hposfi, hpb, hsp, hroot, hplain, hnat⟩ :=
      botWrite_hyps { K with Δ := Δ₂ } ρ₂ φ st₃ _ π q pos v' hg₃ hsh₃ hs₃ hck'' hgrain₁ hns₁ hupd
    subst hposfi
    have hrel := botWrite_rel { K with Δ := Δ₂ } ρ₂ φ st₃ _ π f i q.steps.2 v' hs₃ hg₃.2.2.1 hpb hsp hupd hroot hclear₃ hplain hnat
    -- the reference's write can be made: its reading of the position after its access is the
    -- meaning of the checker's value there (the relation, at the typed future), and writing `⊥`
    -- commutes with the meaning along a place at the grain (`mean_updAt_botS`, L2)
    have hupdR : ∃ y, Sem.updAt K.dm K.Γ (((accessLentPrefix (.bind f i) q.steps.2 s).access (.bind f i)
        (dataHit q.steps.2)).tyAt (.bind f i)) (fun _ => .moved) q.steps.2
        (((accessLentPrefix (.bind f i) q.steps.2 s).access (.bind f i) (dataHit q.steps.2)).valAt (.bind f i)
          (((accessLentPrefix (.bind f i) q.steps.2 s).access (.bind f i) (dataHit q.steps.2)).typedFuture φ)) =
        some y := by
      have hval : ((accessLentPrefix (.bind f i) q.steps.2 s).access (.bind f i) (dataHit q.steps.2)).valAt (.bind f i)
          (((accessLentPrefix (.bind f i) q.steps.2 s).access (.bind f i) (dataHit q.steps.2)).typedFuture φ) =
          Env.mean K.dm ({ K with Δ := Δ₂ } : RunCtx).M K.Γ ρ₂
            (fun l => ((accessLentPrefix (.bind f i) q.steps.2 s).access (.bind f i) (dataHit q.steps.2)).typedFuture φ (π l))
            st₃.env (.bind f i) :=
        (hs₃.sim.1 _ ⟨relF_typedFuture φ _, hs₃.typedFuture_typed φ⟩ (.bind f i) (by simp [IsTemp])).symm
      obtain ⟨H, hH⟩ := envMean_ck K.dm ({ K with Δ := Δ₂ } : RunCtx).M K.Γ ρ₂
        (fun l => ((accessLentPrefix (.bind f i) q.steps.2 s).access (.bind f i) (dataHit q.steps.2)).typedFuture φ (π l)) hck''
      rw [hval, hH]
      exact ⟨_, mean_updAt_botS { K with Δ := Δ₂ } ρ₂ _ q.steps.2 H _ _ v' hupd hplain.1 hplain.2 (hnat _)⟩
    rw [dropAt_data K φ _ q (.bind f i) q.steps.2 hns₀ hupdR hcopy₀]
    have hsz : st.absTy.size ≤ st'.absTy.size := by rw [hst', hX₃]; exact hsz₂
    rw [hst'] at hD hsz ⊢
    exact ⟨ρ₂, Δ₂, hsz, e₂.1,
      ctx_botWrite { K with Δ := Δ₂ } ρ₂ st₃ (.bind f i) q.steps.2 v' hg₃ hctx₃ hupd hD, hrel,
      botWrite_good { K with Δ := Δ₂ } ρ₂ st₃ (.bind f i) q.steps.2 v' hg₃ hpb hupd hroot hclear₃ hplain hnat⟩

/-! ## Records of refinements (the steps `refine` and `generalizeNeutral` are the induction
hypothesis's fields `refine_step` and `generalizeNeutral_step`) -/

/-- Recording a refinement changes nothing the relation reads (it reads Ω and the counter). -/
theorem rel_refs (st : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π { st with refs := (σ, r) :: st.refs } s := ⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7⟩

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
    ⟨hctx.inds, hctx.covers, hctx.faithful, fun τ hr hlt => hctx.delta τ (hrefd τ hr) hlt, hctx.noLabel,
      hctx.globals.of_globals rfl, hctx.dec.of_sameDec rfl rfl, hctx.shapes.of_sameDec rfl rfl rfl rfl⟩⟩
  intro τ v hv
  rcases List.mem_cons.mp hv with h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hσ (fun _ => .err) (.plain (MState.absTyM K.dm K.M K.Γ ρ st τ))]
    exact (meanV_eq_mean_aux K ρ (fun _ => .err) _ v).symm
  · exact ta.refs τ v h

/-! ## Generalisation helpers -/

/-- What the generalisation needs of the type `placeType` gives the new unknown (`T`, the type of
the place holding the program `n`): a type of the state (its unknowns typed), of some level,
holding no loan, a borrow type only at its top; `n`'s unknowns typed too, and `n` a member of `T`. -/
structure GenTy (st : MState) (T n : Value) : Prop where
  abs : ∀ τ, T.hasAbs τ = true → τ < st.absTy.size
  nabs : ∀ τ, n.hasAbs τ = true → τ < st.absTy.size
  loanFree : ∀ l, T.hasLoan l = false
  refOk : T.refMisplaced = false
  level : (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T).level.isSome
  mem : meanV K ρ (fun _ => .err) (.plain (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T)) n ∈ₛ[K.dm.read]
    Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T

/-- `freshAbs` names the unknown by the counter and pushes its type and its frozen reading (D96). -/
theorem runs_freshAbs_inv {T : Value} {d : DeclInfo} {st st' : MState} {b σ : Nat} (h : Runs (Ochr.freshAbs T d) st b σ st') :
    σ = st.nextAbs ∧ st' = { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T, absDecl := st.absDecl.push d } := by
  obtain ⟨L, left, log, h⟩ := h
  simp only [Ochr.freshAbs, runMachineL_bind, runMachineL_get, runMachineL_set, runMachineL_pure,
    Prod.mk.injEq, Outcome.ok.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm⟩

/-- **A decision's run leaves the state as it was** (main's D95: the decision procedures write no
cache; they set `liveScope` only inside `withLive`, which restores it). Here for `valTypeDecl`, the
reading `freshAbsR` freezes (D96); the same fact is `copyRead_aligned`'s "state unchanged". PROVED:
an induction over `Decide.lean`'s mutual block, the shape of `DecideScope.decideSim`
(`Slice.decideKeep`). -/
theorem runs_valTypeDecl_keep {fuel : Nat} {T : Value} {st st' : MState} {b : Nat} {d : DeclInfo}
    (h : Runs (Ochr.valTypeDecl fuel T) st b d st') : st' = st :=
  Slice.runs_valTypeDecl_keep' h

/-- `freshAbsR` (D96): the unknown's reading is read off its type, then frozen by `freshAbs`. -/
theorem runs_freshAbsR_inv {fuel : Nat} {T : Value} {st st' : MState} {b σ : Nat}
    (h : Runs (Ochr.freshAbsR fuel T) st b σ st') :
    ∃ d, σ = st.nextAbs ∧
      st' = { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T, absDecl := st.absDecl.push d } := by
  cases fuel with
  | zero =>
    obtain ⟨L, left, log, h⟩ := h
    simp [Ochr.freshAbsR, runMachineL_exhausted] at h
  | succ fuel =>
    unfold Ochr.freshAbsR at h
    obtain ⟨d, st₁, b₁, hd, h1⟩ := Runs.bind_inv h
    have e := runs_valTypeDecl_keep hd
    subst e
    exact ⟨d, runs_freshAbs_inv h1⟩

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

/-- Recording a generalisation changes nothing the relation reads. -/
theorem rel_neutrals (st : MState) (x : List (Value × Nat)) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π { st with neutrals := x } s := ⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7⟩

end

end Ochr.Meaning.Steps
