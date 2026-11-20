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

/-- **The reference's drop of a data place is its access then its write** (`dropAt`'s last clause,
under the lead's (B), docs/31 D52, reading after the access, D54): where the place is no holder at
a root, its reading after the access exists and is not `⋆`, and it is no copy. PROVED. -/
theorem dropAt_data (s : SState) (q : Place) (pos : Pos) (steps : List Step)
    (hns : steps = [] → s.shape pos = none)
    (hread : ∃ x T, Sem.follow K.dm K.Γ ((s.access pos (dataHit steps)).tyAt pos)
      ((s.access pos (dataHit steps)).valAt pos ((s.access pos (dataHit steps)).typedFuture φ)) steps =
        some (x, T) ∧ x ≠ .proof)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false) :
    dropAt K φ q pos steps s = (s.access pos (dataHit steps)).setAt pos fun φ' =>
      (Sem.updAt K.dm K.Γ ((s.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps
        ((s.access pos (dataHit steps)).valAt pos φ')).getD .err := by
  obtain ⟨x, T, hf, hx⟩ := hread
  unfold dropAt
  split
  · next h2 => rw [hns rfl] at h2; cases h2
  · dsimp only
    rw [hf]
    split
    · next h => simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 hx
    · next h => cases h
    · simp only [hcopy, Bool.false_eq_true, if_false]

/-- **After the checker's access, a root of a non-copy reading that held data holds no `⋆`**, read
after the induction hypothesis's [Access]: the states before and after related to the reference's
before and after its own access, `Good` and the typing of places at both (with (D⋆)). A variable of
a non-copy reading holding data (no `⋆`, `⊥` or borrow) is of a type whose values are not proofs,
so what the access puts there is not `⋆` either (below a variable (C⋆) gives it). Restated for the
slice from a bare fact about the checker's run of the access (whose re-runs of sealed programs it
would have had to follow through the interpreter); for the lead to review. Open. -/
theorem access_root_not_proof (st st₂ : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hck : ckVarPos st.env q.steps.1 = some pos) (hnil : q.steps.2 = []) (hv : valAt st.env pos = v)
    (hb : ∀ l w, v ≠ .borrow l w) (hbot : v ≠ .bot) (hproof : v ≠ .proof)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (hg₂ : Good K.dm K.M K.Γ ρ st₂) (hsh₂ : ShapeFacts K.D K.Γ st₂)
    (hs₂ : Rel K ρ φ π st₂ ((accessLentPrefix pos q.steps.2 s).access pos (dataHit q.steps.2))) :
    valAt st₂.env pos ≠ .proof := by
  sorry

/-- **The reference reads no data of a non-copy place as `⋆`**: at a related state, the meaning of
what the checker holds at a place of a non-copy reading, other than `⋆`, is not `⋆`. By membership
(`Good`) and the typing of places, the meaning is a member of the place's type; `⋆` is a member of
a proposition only, and a place declared a proposition is a copy (`declCopy`: `.prop`); a borrow
of a proposition is no copy, but the checker holds `⋆` there (P5, the `⋆` excluded here). Open: not
tried. -/
theorem dataMean_ne_proof (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hsh : ShapeFacts K.D K.Γ st) (hs : Rel K ρ φ π st s)
    (hck : ckVarPos st.env q.steps.1 = some pos) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (hv : (valAt st.env pos).follow q.steps.2 = some v) (hproof : v ≠ .proof) (H : TyS) :
    Value.mean K.dm K.M K.Γ ρ (fun l => s.typedFuture φ (π l)) H v ≠ .proof := by
  sorry

/-- **The reference's reading of a data place at a related state** exists and is not `⋆`
(`followMean`: it is the meaning of the checker's value, which is not `⋆`, `dataMean_ne_proof`).
PROVED from `dataMean_ne_proof`. -/
theorem dataRead (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hsh : ShapeFacts K.D K.Γ st) (hs : Rel K ρ φ π st s)
    (hck : ckVarPos st.env q.steps.1 = some pos) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (hv : (valAt st.env pos).follow q.steps.2 = some v) (hproof : v ≠ .proof) :
    ∃ x T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.typedFuture φ)) q.steps.2 = some (x, T) ∧
      x ≠ .proof := by
  have hgr : GrainOk K.D K.Γ (DecideScope.topReadings st) q := by rw [← rel_scopeOf K ρ φ hs]; exact hgrain
  have hpt : ¬ IsTemp pos := by
    rcases pos with ⟨f, i⟩ | ⟨f, i⟩
    · simp [IsTemp]
    · unfold ckVarPos at hck; split at hck <;> cases hck
  have hrel : RelF φ s (s.typedFuture φ) := relF_typedFuture φ s
  have hval : s.valAt pos (s.typedFuture φ) =
      Env.mean K.dm K.M K.Γ ρ (fun l => s.typedFuture φ (π l)) st.env pos := (hs.sim.1 _ ⟨hrel, hs.typedFuture_typed φ⟩ pos hpt).symm
  obtain ⟨s', T', h1, h2⟩ := followMean K ρ hsh hg (fun l => s.typedFuture φ (π l)) pos q hgr hck v
    (by unfold ckContent; simp [hck, hv]) (s.tyAt pos)
  rw [hval]
  refine ⟨s', T', h1, ?_⟩
  rcases h2 with ⟨-, rfl⟩ | ⟨H, rfl⟩
  · exact absurd rfl hproof
  · exact dataMean_ne_proof K ρ φ st s π q pos v hg hsh hs hck hgrain hcopy hv hproof H

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

theorem runCtx_with_self' (K : RunCtx) : ({ K with Δ := K.Δ, D := K.D } : RunCtx) = K := by cases K; rfl

/-- **A value naming only old unknowns means the same under an extension** (leaf;
`AssignCongr.meanV_congrA` for the assignment, `DecExtend.meanV_congrD` for the decisions, and `Δ`
read only at the unknowns a value holds). -/
theorem meanV_ext {n : Nat} {ρ' : Assignment} {Δ' : Nat → TyS} {D' : Decisions} (v : Value) (ψ : Future) (hint : TyS)
    (hv : ∀ σ, v.hasAbs σ = true → σ < n) (ha : ∀ σ, σ < n → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ)
    (hd : K.D.AgreeOld n D') :
    meanV { K with Δ := Δ', D := D' } ρ' ψ hint v = meanV K ρ ψ hint v := by
  sorry

/-- From `st` (related to some reference state under `K`, `ρ`) to `st'`, related to `s'` under an
assignment, a `Δ` and decisions extended at the unknowns created (docs/31 D71's rule: the decisions
agree with the old ones on inputs naming only old unknowns), with `Good` and the context kept. -/
structure Ext (π : Nat → Nat) (st st' : MState) (s' : SState) (ρ' : Assignment) (Δ' : Nat → TyS)
    (D' : Decisions) : Prop where
  size : st.absTy.size ≤ st'.absTy.size
  agree : ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ
  dec : K.D.AgreeOld st.absTy.size D'
  ctx : CtxOk { K with Δ := Δ', D := D' } ρ' st'
  rel : Rel { K with Δ := Δ', D := D' } ρ' φ π st' s'
  good : Good K.dm ({ K with Δ := Δ', D := D' } : RunCtx).M K.Γ ρ' st'

theorem Ext.refl {π : Nat → Nat} {st : MState} {s : SState} (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hs : Rel K ρ φ π st s) : Ext K ρ φ π st st s ρ K.Δ K.D :=
  ⟨Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, Decisions.AgreeOld.refl _ _, by rw [runCtx_with_self' K]; exact hctx,
    by rw [runCtx_with_self' K]; exact hs, by rw [runCtx_with_self' K]; exact hg⟩

theorem Ext.trans {π : Nat → Nat} {st st₁ st₂ : MState} {s₁ s₂ : SState} {ρ₁ ρ₂ : Assignment} {Δ₁ Δ₂ : Nat → TyS}
    {D₁ D₂ : Decisions}
    (h₁ : Ext K ρ φ π st st₁ s₁ ρ₁ Δ₁ D₁) (h₂ : Ext { K with Δ := Δ₁, D := D₁ } ρ₁ φ π st₁ st₂ s₂ ρ₂ Δ₂ D₂) :
    Ext K ρ φ π st st₂ s₂ ρ₂ Δ₂ D₂ where
  size := Nat.le_trans h₁.size h₂.size
  agree σ hσ := by
    obtain ⟨a, b⟩ := h₂.agree σ (Nat.lt_of_lt_of_le hσ h₁.size)
    obtain ⟨c, d⟩ := h₁.agree σ hσ
    exact ⟨a.trans c, b.trans d⟩
  dec := Decisions.AgreeOld.trans h₁.dec h₂.dec h₁.size
  ctx := h₂.ctx
  rel := h₂.rel
  good := h₂.good

/-- The same state, the reference state replaced by one the checker's is also related to. -/
theorem Ext.with_rel {π : Nat → Nat} {st st' : MState} {s' s'' : SState} {ρ' : Assignment} {Δ' : Nat → TyS}
    {D' : Decisions} (h : Ext K ρ φ π st st' s' ρ' Δ' D') (hr : Rel { K with Δ := Δ', D := D' } ρ' φ π st' s'') :
    Ext K ρ φ π st st' s'' ρ' Δ' D' :=
  ⟨h.size, h.agree, h.dec, h.ctx, hr, h.good⟩

/-- **The checker's access keeps its run context** (it ends borrows: no global or declaration
changes). An end of a borrow of a dependent type may keep an unknown nothing names (`repackCheck`,
docs/31 D35, measured): `DeltaOk` asks nothing of it. `Good` is needed: a state that already
names the counter would have the kept unknown named, with `K.Δ` free there.

FALSE as stated (the slice, docs/31 D57 (1)): an access can grow the table of unknowns (ending a
borrow of a dependent type runs `repackCheck`, whose `lentUnknown` makes one with a frozen reading;
D35's measured ends), and then `CtxOk.dec` asks the fixed `K.D` to be the checker's on inputs naming
the new unknown (`declOf` of `.val (.abs σ)` reads `absDecl[σ]`), which `CtxOk K ρ st` leaves free
since the checker's run on them fails before the access. The drop of one place no longer uses it
(it reads the typing of places after the access from the induction hypothesis's [Access]);
`movedPlace_step`'s filled-parent branch still does, and waits on the statement form for steps that
grow the table (the spine lead's).

RESTATED (docs/31 D76, D78): [Repack]'s new unknown is used for the check only, named by nothing in
Ω, so the assignment and `Δ` stay; the decisions are extended (`D'`, agreeing on old inputs), and
the relation and `Good` the access left under `K` carry over to the extended context. -/
theorem access_ctx (fuel : Nat) (st st' : MState) (q : Place) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (h : Runs (do Ochr.accessPath fuel q; Ochr.accessInside fuel q) st b () st')
    {s' : SState} {π : Nat → Nat} (hs' : Rel K ρ φ π st' s') (hg' : Good K.dm K.M K.Γ ρ st') :
    ∃ D' : Decisions, Ext K ρ φ π st st' s' ρ K.Δ D' := by
  sorry

/-- **The drop of one place where the place exists** (`dropOne_step`'s main case), assembled from
the named obligations and the induction hypothesis's [Access] and [End]: missing, `⊥` or `⋆` (both
sides do nothing); a borrow at a root (both end it); a copy (excluded: the join moves no copy);
data (both access, then write `⊥`/`moved`). -/
theorem dropOne_exists (fuel : Nat) (ih : StepsIHBelow fuel)
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
    have hpt : ¬ IsTemp pos := by
      rcases pos with ⟨f, i⟩ | ⟨f, i⟩
      · simp [IsTemp]
      · unfold ckVarPos at hck; split at hck <;> cases hck
    -- a root holding `⊥` or `⋆` is no holder, in the reference either (`SimEq`'s holders)
    have hnb : ∀ c, (valAt st.env pos).follow q.steps.2 = some c → (c = .bot ∨ c = .proof) →
        q.steps.2 = [] → s.shape pos = none := by
      intro c hc hcp he
      cases hsp : s.shape pos with
      | none => rfl
      | some l' =>
        obtain ⟨l, hl, -⟩ := hs.sim.2.2.1 pos l' hpt hsp
        have hl' : Env.shape st.env pos = some l := hl
        rw [he] at hc; simp only [Value.follow, Option.some.injEq] at hc
        rw [shape_eq_shapeOf, hc] at hl'
        rcases hcp with rfl | rfl <;> simp [shapeOf] at hl'
    have hlp : lentPrefix s pos q.steps.2 = none := by
      rcases hn with hn | hn
      · exact lentPrefix_none_of_noop K ρ φ st s π q pos hg hs hres hn
      · exact lentPrefix_none_of_proof K ρ φ st s π q pos hctx hs hck hcopy hn
    have hpre : accessLentPrefix pos q.steps.2 s = s := by simp [accessLentPrefix, hlp]
    rw [hpre]
    obtain ⟨c, hn, hcb⟩ : ∃ c, (valAt st.env pos).follow q.steps.2 = some c ∧ (c = .bot ∨ c = .proof) := by
      rcases hn with hn | hn
      · exact ⟨_, hn, .inl rfl⟩
      · exact ⟨_, hn, .inr rfl⟩
    -- the reference's access of a place holding `⊥` or `⋆` ends nothing: nothing is lent over,
    -- at or under a `⊥` (`clear_of_bot`); a `⋆` below a variable is a copy ((C⋆)), excluded, and at
    -- a root nothing is lent at all (`clear_of_proof_root`)
    have hclr : ∀ l, liveLoan st.env l = true → ∀ x ∈ Env.sitesOf st.env l, x.pos = pos →
        dataHit q.steps.2 x.path = false := by
      rcases hcb with rfl | rfl
      · exact clear_of_bot hg.2.2.1 hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hn
      · by_cases hne : q.steps.2 = []
        · rw [hne] at hn
          simp only [Value.follow, Option.some.injEq] at hn
          intro l _ x hx hxp
          exact absurd hxp (clear_of_proof_root hn l x hx)
        · have h := hctx.shapes.proofCopy q hne (by unfold ckContent; simp [hck, hn])
          rw [← rel_scopeOf K ρ φ hs, hcopy] at h
          cases h
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
    obtain ⟨x, T, hT, hx⟩ := content_follow K ρ φ st s π q pos hg hctx hs hck hgrain c hn hcb
    unfold dropAt
    split
    · next l h1 h2 => rw [hnb _ hn hcb h1] at h2; cases h2
    · dsimp only
      rw [hacc, hT]
      rcases hx with rfl | ⟨rfl, rfl⟩
      · exact ⟨hs, hg⟩
      · -- a place already moved: the reference accesses it, which ends nothing, and writes `moved`
        -- over `moved`, which changes nothing the relation reads (docs/31 D52)
        simp only [hcopy, Bool.false_eq_true, if_false]
        have hclr := clear_of_bot hg.2.2.1 hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hn
        have hself := updAt_bot_self q.steps.2 _ hn
        obtain ⟨f, i, hposfi, hpb, hsp, hroot, hplain, hnat⟩ :=
          botWrite_hyps K ρ φ st s π q pos _ hg hctx.shapes hs hck hgrain (fun he => hnb _ hn (.inl rfl) he) hself
        subst hposfi
        have hrel := botWrite_rel K ρ φ st s π f i q.steps.2 _ hs hg.2.2.1 hpb hsp hself hroot
          (fun l hl x hx hxp => hclr l hl x hx hxp) hplain hnat
        rw [setAtE_self_bind st.env f i hpb] at hrel
        exact ⟨hrel, hg⟩
  · -- a borrow at a root: both end it
    have hsteps := follow_borrow_root hg.2.2.1 hp hbw
    have hval : valAt st.env pos = .borrow l w' := by
      rw [hsteps] at hbw; simpa [Value.follow] using hbw
    obtain ⟨hs₁, hg₁, hctx₁, henv₁⟩ := logEffect_rel K ρ φ st st₁ s π q "moves" b₁ hg hctx hs hlog
    have hl : liveLoan st₁.env l = true := by rw [henv₁]; exact liveLoan_of_holder hp hval
    obtain ⟨hs', hg'⟩ := (ih.at K ρ φ).endBorrow_step st₁ st' l s π hg₁ hctx₁ hs₁ hl b₂ hend
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
    exact ⟨hs', hg'⟩
  · -- a copy: excluded
    obtain ⟨-, hc⟩ := copyRead_aligned K ρ φ fuel st st' s π q true b₁ hctx hs hcr
    rw [hcopy] at hc; cases hc
  · -- data: both access, then write
    obtain ⟨hst₁, -⟩ := copyRead_aligned K ρ φ fuel st st₁ s π q false b₁ hctx hs hcr
    rw [hst₁] at hacc
    obtain ⟨hs₂, hg₂, hsh₂⟩ := (ih.at K ρ φ).access_step st st₂ q pos false s π hg hctx hs hres b₂ hacc
    simp only [Bool.false_and, Bool.false_eq_true, if_false] at hs₂
    have hs₂' := (lentPrefix_absorbed K ρ φ st st₂ s π pos q.steps.2 v hg hs hp hv).mpr hs₂
    obtain ⟨hs₃, hg₃, hsh₃, henv₃⟩ := Slice.logEffect_rel_shapes K ρ φ st₂ st₃ _ π q "moves" b₃ hg₂ hsh₂ hs₂' hlog
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
    have hclear₂ := access_clears K ρ φ st₂ (accessLentPrefix pos q.steps.2 s) π pos q.steps.2 hg₂ hs₂'
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
    -- the reference's reading after its access: at the checker's state after its access, the place
    -- holds data the access did not make `⋆`, which the reference does not read as `⋆`
    obtain ⟨v₃, hv₃⟩ := follow_of_updAt _ _ _ _ hupd
    have hproof₃ : v₃ ≠ .proof := by
      rintro rfl
      by_cases hne : q.steps.2 = []
      · have hv' := hv
        rw [hne] at hv₃ hv'
        simp only [Value.follow, Option.some.injEq] at hv₃ hv'
        exact access_root_not_proof K ρ φ st st₂ s π q pos v hg hctx hs hck hne hv' hb hbot hproof hcopy
          hg₂ hsh₂ hs₂' (by rw [← henv₃]; exact hv₃)
      · have h := hsh₃.proofCopy q hne (by unfold ckContent; simp [hck'', hv₃])
        rw [← rel_scopeOf K ρ φ hs₃, hcopy₁] at h
        cases h
    have hread := dataRead K ρ φ st₃ _ π q pos v₃ hg₃ hsh₃ hs₃ hck'' hgrain₁ hcopy₁ hv₃ hproof₃
    have hcopy₀ : K.D.copy (K.D.placeDecl (scopeOf (accessLentPrefix pos q.steps.2 s)) q) = false := by
      rw [scopeOf_of_declsOf (declsOf_accessLentPrefix s pos q.steps.2)]; exact hcopy
    obtain ⟨f, i, hposfi, hpb, hsp, hroot, hplain, hnat⟩ :=
      botWrite_hyps K ρ φ st₃ _ π q pos v' hg₃ hsh₃ hs₃ hck'' hgrain₁ hns₁ hupd
    subst hposfi
    have hrel := botWrite_rel K ρ φ st₃ _ π f i q.steps.2 v' hs₃ hg₃.2.2.1 hpb hsp hupd hroot hclear₃ hplain hnat
    rw [dropAt_data K φ _ q (.bind f i) q.steps.2 hns₀ hread hcopy₀, hst']
    exact ⟨hrel, botWrite_good K ρ st₃ (.bind f i) q.steps.2 v' hg₃ hpb hupd hroot hclear₃ hplain hnat⟩

/-- **The checker's drop of one place keeps the run context** (`dropAtJoin` ends a borrow, accesses
and writes: no global or declaration changes, and no unknown is NAMED, but an end's [Repack] may make
one for its check, as [Access] does: `access_ctx`). Restated with the decisions extended (docs/31
D78; as first stated, the context unchanged, it was false for the reason `access_ctx` was), the
relation and `Good` the drop left under `K` carried over. Open: not tried. -/
theorem dropAtJoin_ctx (fuel : Nat) (st st' : MState) (q : Place) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (h : Runs (Ochr.dropAtJoin (fuel + 1) q) st b () st')
    {s' : SState} {π : Nat → Nat} (hs' : Rel K ρ φ π st' s') (hg' : Good K.dm K.M K.Γ ρ st') :
    ∃ D' : Decisions, Ext K ρ φ π st st' s' ρ K.Δ D' := by
  sorry


/-! ## `refine` in the simulation form, reduced -/

/-- **`substEnv` of an unknown by a refinement it means, in the simulation form**: every position
means the same (the substitution lemma for unknowns, the analogue of `meanV_substLoan` and
`run_substLoan`, with [Seal]'s re-run of a changed sealed program meaning the same), the shape,
sites and labels are untouched (a refinement holds no loan), and `Good` and the context are kept
under an extension (the re-runs keep unknowns: docs/31 D76; as first stated, under the same context,
false for that reason). Open: the substitution lemma for unknowns is `SubstAbs.lean`'s. -/
theorem substEnv_abs_sim (fuel : Nat) (st st' : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hσ : ∀ ψ H, ρ σ = meanV K ρ ψ H r)
    (h : Runs (Ochr.substEnv fuel (.abs σ) r true) st b () st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (D' : Decisions), Ext K ρ φ π st st' s ρ' Δ' D' := by
  sorry

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
    ⟨hctx.1, hctx.2, fun τ hr hlt => hctx.3 τ (hrefd τ hr) hlt, hctx.4, hctx.5.of_globals rfl,
      hctx.6.of_sameDec rfl rfl, hctx.7.of_sameDec rfl rfl rfl rfl⟩⟩
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
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (D' : Decisions), Ext K ρ φ π st st' s ρ' Δ' D' := by
  sorry

/-- **`refine` in the simulation form**, assembled: the substitution, the record, the
re-normalisation. The refinement means `ρ σ` at every future and hint (it holds no loan and
records its parameters). -/
theorem refine_sim' (fuel : Nat) (st st' : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hσ : ∀ ψ H, ρ σ = meanV K ρ ψ H r)
    (hb : σ < st.absTy.size ∧ ∀ τ, r.hasAbs τ = true → τ < st.absTy.size)
    (h : Runs (Ochr.refine (fuel + 1) σ r) st b () st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (D' : Decisions), Ext K ρ φ π st st' s ρ' Δ' D' := by
  unfold Ochr.refine at h
  obtain ⟨_, st₁, b₁, hsub, h1⟩ := Runs.bind_inv h
  obtain ⟨ρ₁, Δ₁, D₁, E₁⟩ := substEnv_abs_sim K ρ φ fuel st st₁ σ r s π b hg hctx hs hσ hsub
  obtain ⟨_, st₂, b₂, hmod, h2⟩ := Runs.bind_inv h1
  obtain ⟨L, left, log, hmod⟩ := hmod
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at hmod
  obtain ⟨⟨-, hst₂⟩, -⟩ := hmod
  have hσ₁ : ∀ ψ H, ρ₁ σ = meanV { K with Δ := Δ₁, D := D₁ } ρ₁ ψ H r := fun ψ H => by
    rw [meanV_ext K ρ r ψ H hb.2 E₁.agree E₁.dec, (E₁.agree σ hb.1).1]; exact hσ ψ H
  obtain ⟨hs₂, hg₂, hctx₂⟩ := refs_sim { K with Δ := Δ₁, D := D₁ } ρ₁ φ st₁ σ r s π E₁.good E₁.ctx E₁.rel hσ₁
    ⟨Nat.lt_of_lt_of_le hb.1 E₁.size, fun τ hτ => Nat.lt_of_lt_of_le (hb.2 τ hτ) E₁.size⟩
  rw [hst₂] at hs₂ hg₂ hctx₂
  have E₂ : Ext K ρ φ π st st₂ s ρ₁ Δ₁ D₁ :=
    ⟨by rw [← hst₂]; exact E₁.size, E₁.agree, E₁.dec, hctx₂, hs₂, hg₂⟩
  obtain ⟨g, st₃, b₃, hget, h3⟩ := Runs.bind_inv h2
  obtain ⟨L, left, log, hget⟩ := hget
  simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at hget
  obtain ⟨⟨hg3, hst3⟩, -⟩ := hget
  rw [← hst3, ← hg3] at h3
  split at h3
  · obtain ⟨ρ₃, Δ₃, D₃, E₃⟩ := renormAll_sim { K with Δ := Δ₁, D := D₁ } ρ₁ φ fuel st₂ st' s π b₃ hg₂ hctx₂ hs₂ h3
    exact ⟨ρ₃, Δ₃, D₃, E₂.trans K ρ φ E₃⟩
  · obtain ⟨L, left, log, h3⟩ := h3
    simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h3
    rw [← h3.1.2]
    exact ⟨ρ₁, Δ₁, D₁, E₂⟩

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
  mem : meanV K ρ (fun _ => .err) (.plain (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T)) n ∈ₛ[K.dm.read]
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
    ∃ (ρ₁ : Assignment) (Δ₁ : Nat → TyS) (D₁ : Decisions), Ext K ρ φ π st st₁ s ρ₁ Δ₁ D₁ ∧
      st₁.env = st.env ∧ GenTy { K with Δ := Δ₁, D := D₁ } ρ₁ st₁ T n := by
  sorry

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

/-- **A fresh unknown of a well-formed type** (`freshAbs`). Nothing in the state names it yet, so
under any value for it, with its type added to Δ, the relation, `Good`, the context and the
`GenTy` are kept, and the program and its type read the same (neither holds the new unknown).
Open: needs that a meaning reads the assignment and Δ only at the unknowns the value holds (the
assignment's analogue of `RunCongr.meanV_congrE`, not written). -/
theorem freshAbs_sim (st : MState) (T n : Value) (d : DeclInfo) (s : SState) (π : Nat → Nat) (v : Sem)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s) (hT : GenTy K ρ st T n) :
    ∃ (Δ' : Nat → TyS) (D' : Decisions),
      Ext K ρ φ π st { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T, absDecl := st.absDecl.push d } s
        (ρ.ext st.nextAbs v) Δ' D' ∧
      GenTy { K with Δ := Δ', D := D' } (ρ.ext st.nextAbs v)
        { st with nextAbs := st.nextAbs + 1, absTy := st.absTy.push T, absDecl := st.absDecl.push d } T n ∧
      meanV { K with Δ := Δ', D := D' } (ρ.ext st.nextAbs v) (fun _ => .err)
          (.plain (Value.tyM K.dm ({ K with Δ := Δ', D := D' } : RunCtx).M K.Γ (ρ.ext st.nextAbs v) (fun _ => .err) T)) n =
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
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (D' : Decisions),
      Ext K ρ φ π st { st' with neutrals := (n, σ) :: st'.neutrals } s ρ' Δ' D' := by
  sorry

/-- Recording a generalisation changes nothing the relation reads. -/
theorem rel_neutrals (st : MState) (x : List (Value × Nat)) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π { st with neutrals := x } s := ⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7⟩

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
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (D' : Decisions), Ext K ρ φ π st st' s ρ' Δ' D' := by
  cases fuel with
  | zero =>
    obtain ⟨L, left, log, h⟩ := h
    simp [Ochr.generalizeNeutral, runMachineL_exhausted] at h
  | succ fuel =>
  unfold Ochr.generalizeNeutral at h
  obtain ⟨T, st₁, b₁, hpt, h1⟩ := Runs.bind_inv h
  obtain ⟨ρ₁, Δ₁, D₁, E₁, henv₁, hT₁⟩ :=
    placeType_sim K ρ φ fuel st st₁ p n T s π b hg hctx hs hn hsealed hfree hpt
  have hn₁ : ckContent st₁.env p = some n := by rw [henv₁]; exact hn
  obtain ⟨σ', st₂, b₂, hfa, h2⟩ := Runs.bind_inv h1
  obtain ⟨dσ, rfl, rfl⟩ := runs_freshAbsR_inv hfa
  let v := meanV { K with Δ := Δ₁, D := D₁ } ρ₁ (fun _ => .err)
    (.plain (Value.tyM K.dm ({ K with Δ := Δ₁, D := D₁ } : RunCtx).M K.Γ ρ₁ (fun _ => .err) T)) n
  obtain ⟨Δ₂, D₂, E₂, hT₂, hv⟩ :=
    freshAbs_sim { K with Δ := Δ₁, D := D₁ } ρ₁ φ st₁ T n dσ s π v E₁.good E₁.ctx E₁.rel hT₁
  have hsize₁ : st₁.absTy.size = st₁.nextAbs := Good.absTy_size { K with Δ := Δ₁, D := D₁ } E₁.good
  obtain ⟨u, st₃, b₃, htr, h3⟩ := Runs.bind_inv h2
  have hst₃ := runs_trace_inv htr
  subst hst₃
  obtain ⟨u', st₄, b₄, hsub, h4⟩ := Runs.bind_inv h3
  have hσT : ({ st₁ with nextAbs := st₁.nextAbs + 1, absTy := st₁.absTy.push T, absDecl := st₁.absDecl.push dσ } : MState).absTy[st₁.nextAbs]? = some T := by
    simp only [← hsize₁, Array.getElem?_push_size]
  have hσn : n.hasAbs st₁.nextAbs = false := by
    cases e : n.hasAbs st₁.nextAbs
    · rfl
    · have := hT₁.nabs _ e; omega
  have hσ : (ρ₁.ext st₁.nextAbs v) st₁.nextAbs = meanV { K with Δ := Δ₂, D := D₂ } (ρ₁.ext st₁.nextAbs v) (fun _ => .err)
      (.plain (Value.tyM K.dm ({ K with Δ := Δ₂, D := D₂ } : RunCtx).M K.Γ (ρ₁.ext st₁.nextAbs v) (fun _ => .err) T)) n := by
    simp only [Assignment.ext, if_pos rfl]; exact hv.symm
  obtain ⟨ρ₃, Δ₃, D₃, E₃⟩ := substEnv_neutral_sim { K with Δ := Δ₂, D := D₂ } (ρ₁.ext st₁.nextAbs v) φ fuel _ st₄ p n T
    st₁.nextAbs s π b₃ E₂.good E₂.ctx E₂.rel hn₁ hsealed hfree hT₂ hσT hσn hσ hsub
  obtain ⟨L, left, log, h4⟩ := h4
  simp only [runMachineL_bind, runMachineL_modify, runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h4
  obtain ⟨⟨-, rfl⟩, -⟩ := h4
  exact ⟨ρ₃, Δ₃, D₃, E₁.trans K ρ φ (E₂.trans _ _ φ E₃)⟩

end

end Ochr.Meaning.Steps
