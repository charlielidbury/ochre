import Ochr.Meaning.Steps.JoinNoop
import Ochr.Meaning.Steps.EqJAsm
import Ochr.Meaning.Steps.Slice.UpdAt

/-!
# `movedPlace` in the simulation form, and the drop of a place that does not exist (D84; task C)

`Machine.movedPlace` re-roots a place the join drops when it does not exist in the checker's state:
it re-roots the parent first (recursively), then accesses a filled parent whole, η-refines an
unknown of a one-constructor type, or generalises a sealed program of one, and asks again. Since
main's D94 its last part (`mpFinal`) returns the place if it exists now, a prefix holding `⊥` or
`⋆` (whose drop does nothing), and otherwise rejects the definition, which is no run, so nothing is
left to prove there (docs/31 D51; the exit lemmas that read the typing of places went). The reference never
re-roots: its state holds meanings, where the place exists, and it accesses the shortest lent
prefix whole before the drop (`accessLentPrefix`).

`movedPlace_step` proves the induction hypothesis's field `movedPlace_step_stmt` at `fuel + 1`
from the hypothesis at `fuel` (whose `movedPlace_step` covers the recursive calls), following the
checker's code branch by branch; each branch's semantic content is a named obligation below,
`sorry`'d where open. The assembly of `dropOne_step` is here, on top of it.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

/-- `Machine.movedPlace` after the parent is found, a copy of its code (the two are tied by
`movedPlace_succ_eq`, which is `rfl`: a change to the checker's function breaks the build here). -/
def mpTail (fuel : Nat) (q p : Place) : M Place := do
  let p ← Ochr.movedPlace fuel p
  if !(Ochr.fillHoles (← get).env (← Ochr.content p)).isEmpty then
    Ochr.accessPath fuel p; Ochr.accessInside fuel p
    if !(Ochr.fillHoles (← get).env (← Ochr.content p)).isEmpty then return p
    return ← Ochr.movedPlace fuel q
  match ← Ochr.content p with
  | .abs σ =>
    match ← Ochr.absType σ with
    | .tInd n ps =>
      let d ← Ochr.lookupInd n
      if d.ctors.length == 1 then
        discard (Ochr.etaInPlace fuel σ d ps)
        return ← Ochr.movedPlace fuel q
    | _ => pure ()
  | n@(.sealed _) =>
    if let some (.tInd tn _) ← Ochr.placeType? fuel p then
      if (← Ochr.lookupInd tn).ctors.length == 1 then
        match ← Ochr.recordedNeutral n with
        | some r => Ochr.substEnv fuel n r true
        | none => discard (Ochr.generalizeNeutral fuel p n)
        return ← Ochr.movedPlace fuel q
  | _ => pure ()
  if (← Ochr.content? q).isSome then return q
  match ← Ochr.content p with
  | .bot | .proof => pure p
  | v =>
    let why := match v with
      | .abs _ => "an unknown of a type with several constructors"
      | .sealed _ => "a stuck program of a type with several constructors"
      | .ind .. => match q with
        | .deref _ => "a constructor value, which is not a borrow"
        | _ => "a constructor value without that field"
      | _ => match q with
        | .deref _ => "a value that is not a borrow"
        | _ => "a value without that field"
    Ochr.err s!"[Join] an arm of the match moves {← Ochr.ppPlace q}, which does not exist: {← Ochr.ppPlace p} holds {why} ({v})"

/-- `movedPlace`'s last part (D94): the place if it exists now, a prefix holding `⊥` or `⋆` for a
no-op, and otherwise the definition is rejected. -/
def mpFinal (q p : Place) : M Place := do
  if (← Ochr.content? q).isSome then return q
  match ← Ochr.content p with
  | .bot | .proof => pure p
  | v =>
    let why := match v with
      | .abs _ => "an unknown of a type with several constructors"
      | .sealed _ => "a stuck program of a type with several constructors"
      | .ind .. => match q with
        | .deref _ => "a constructor value, which is not a borrow"
        | _ => "a constructor value without that field"
      | _ => match q with
        | .deref _ => "a value that is not a borrow"
        | _ => "a value without that field"
    Ochr.err s!"[Join] an arm of the match moves {← Ochr.ppPlace q}, which does not exist: {← Ochr.ppPlace p} holds {why} ({v})"

/-- `mpTail` with each fall-through to the last part written out (`mpTail_eq`, by `rfl`). -/
def mpTail' (fuel : Nat) (q p : Place) : M Place := do
  let p ← Ochr.movedPlace fuel p
  if !(Ochr.fillHoles (← get).env (← Ochr.content p)).isEmpty then
    Ochr.accessPath fuel p; Ochr.accessInside fuel p
    if !(Ochr.fillHoles (← get).env (← Ochr.content p)).isEmpty then return p
    return ← Ochr.movedPlace fuel q
  match ← Ochr.content p with
  | .abs σ =>
    match ← Ochr.absType σ with
    | .tInd n ps =>
      let d ← Ochr.lookupInd n
      if d.ctors.length == 1 then
        discard (Ochr.etaInPlace fuel σ d ps)
        Ochr.movedPlace fuel q
      else mpFinal q p
    | _ => mpFinal q p
  | n@(.sealed _) =>
    match ← Ochr.placeType? fuel p with
    | some (.tInd tn _) =>
      if (← Ochr.lookupInd tn).ctors.length == 1 then
        match ← Ochr.recordedNeutral n with
        | some r => Ochr.substEnv fuel n r true
        | none => discard (Ochr.generalizeNeutral fuel p n)
        Ochr.movedPlace fuel q
      else mpFinal q p
    | _ => mpFinal q p
  | _ => mpFinal q p

set_option maxHeartbeats 2000000 in
theorem mpTail_eq (fuel : Nat) (q p : Place) : mpTail fuel q p = mpTail' fuel q p := rfl

set_option maxHeartbeats 2000000 in
theorem movedPlace_succ_eq (fuel : Nat) (q : Place) :
    Ochr.movedPlace (fuel + 1) q = (do
      if (← Ochr.content? q).isSome then return q
      match parentOf q with
      | some p => mpTail fuel q p
      | none => pure q) := by
  rw [Ochr.movedPlace.eq_def]
  cases q <;> rfl

/-! ## Small inversions -/

/-- `content` reads the place and changes nothing. -/
theorem runs_content_inv {p : Place} {st st' : MState} {b : Nat} {v : Value}
    (h : Runs (Ochr.content p) st b v st') : st' = st ∧ ckContent st.env p = some v := by
  unfold Ochr.content at h
  rcases hq : p.steps with ⟨i, ss⟩
  rw [hq] at h
  obtain ⟨pos, st₁, b₁, hv, h2⟩ := Runs.bind_inv h
  obtain ⟨rfl, hpos⟩ := runs_varPos_inv hv
  obtain ⟨w, st₂, b₂, hg, h3⟩ := Runs.bind_inv h2
  obtain ⟨rfl, rfl⟩ := runs_getAt_inv hg
  split at h3
  · rename_i w' hw
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h3
    exact ⟨rfl, by simp [ckContent, hq, hpos, hw]⟩
  · obtain ⟨_, st₃, b₃, -, h4⟩ := Runs.bind_inv h3
    exact (runs_err_false h4).elim

theorem runs_absType_inv {σ : Nat} {st st' : MState} {b : Nat} {T : Value}
    (h : Runs (Ochr.absType σ) st b T st') : st' = st ∧ st.absTy[σ]? = some T := by
  unfold Ochr.absType at h
  obtain ⟨x, st₁, b₁, hg, h2⟩ := Runs.bind_inv h
  obtain ⟨rfl, rfl⟩ := runs_get_inv hg
  split at h2
  · rename_i T' hT
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h2
    exact ⟨rfl, hT⟩
  · exact (runs_err_false h2).elim

theorem runs_mapM_keep {α β : Type} (f : α → M β)
    (hf : ∀ x st b y st', Runs (f x) st b y st' → st' = st) :
    ∀ (xs : List α) {st st' : MState} {b : Nat} {ys : List β}, Runs (xs.mapM f) st b ys st' → st' = st
  | [], st, st', b, ys, h => by
    rw [List.mapM_nil] at h
    exact (runs_pure_inv h).2
  | x :: xs, st, st', b, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    obtain ⟨ys', st₂, b₂, h3, h4⟩ := Runs.bind_inv h2
    rw [(runs_pure_inv h4).2, runs_mapM_keep f hf xs h3, hf x st b y st₁ h1]

/-- `expandRefsF` computes a value and changes nothing. -/
theorem runs_expandRefsF_keep (refs : List (Nat × Value)) :
    ∀ (fuel : Nat) (v : Value) {st st' : MState} {b : Nat} {w : Value},
      Runs (Ochr.expandRefsF refs fuel v) st b w st' → st' = st
  | 0, v, st, st', b, w, h => by
    obtain ⟨L, left, log, h⟩ := h
    simp [Ochr.expandRefsF, runMachineL_exhausted] at h
  | fuel + 1, v, st, st', b, w, h => by
    rw [Ochr.expandRefsF.eq_def] at h
    cases v with
    | abs σ =>
      dsimp only at h
      split at h
      · exact runs_expandRefsF_keep refs fuel _ h
      · exact (runs_pure_inv h).2
    | succ v =>
      dsimp only at h
      obtain ⟨y, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
      rw [(runs_pure_inv h2).2]
      exact runs_expandRefsF_keep refs fuel _ h1
    | ind t c hh ps fs =>
      dsimp only at h
      obtain ⟨ys, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
      rw [(runs_pure_inv h2).2]
      exact runs_mapM_keep _ (fun x _ _ _ _ hx => runs_expandRefsF_keep refs fuel x hx) _ h1
    | _ => exact (runs_pure_inv h).2

/-- `neutralLookup` (main's D108: a record is found by `Value.exact`) reads the records and changes
nothing. -/
theorem runs_neutralLookup_inv {v : Value} {st st' : MState} {b : Nat} {o : Option Nat}
    (h : Runs (Ochr.neutralLookup v) st b o st') :
    st' = st ∧ o = (st.neutrals.find? (·.1.exact v)).map (·.2) := by
  unfold Ochr.neutralLookup at h
  obtain ⟨x, st₁, b₁, hg, h2⟩ := Runs.bind_inv h
  obtain ⟨hx, hst₁⟩ := runs_get_inv hg
  subst x; subst st₁
  obtain ⟨ho, hst⟩ := runs_pure_inv h2
  exact ⟨hst, ho⟩

/-- `recordedNeutral` reads the records and changes nothing. -/
theorem runs_recordedNeutral_inv {v : Value} {st st' : MState} {b : Nat} {o : Option Value}
    (h : Runs (Ochr.recordedNeutral v) st b o st') : st' = st := by
  unfold Ochr.recordedNeutral at h
  split at h
  · obtain ⟨x, st₁, b₁, hg, h2⟩ := Runs.bind_inv h
    obtain ⟨hst₁, -⟩ := runs_neutralLookup_inv hg
    subst st₁
    split at h2
    · obtain ⟨y, st₂, b₂, hg', h3⟩ := Runs.bind_inv h2
      obtain ⟨hy, hst₂⟩ := runs_get_inv hg'
      subst y; subst st₂
      obtain ⟨w, st₃, b₃, hex, h4⟩ := Runs.bind_inv h3
      rw [(runs_pure_inv h4).2]
      unfold Ochr.expandRefs at hex
      obtain ⟨n, st₄, b₄, hfl, h5⟩ := Runs.bind_inv hex
      have e : st₄ = st := by
        obtain ⟨L, left, log, hfl⟩ := hfl
        have e0 : runMachineL Ochr.fuelLeft st b₂ L = (.ok b₂ st, b₂, L) := rfl
        rw [e0] at hfl
        simp only [Prod.mk.injEq, Outcome.ok.injEq] at hfl
        exact hfl.1.2.symm
      subst st₄
      exact runs_expandRefsF_keep _ _ _ h5
    · exact (runs_pure_inv h2).2
  · exact (runs_pure_inv h).2

theorem runs_discard_inv {α : Type} {x : M α} {st st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (discard x) st b u st') : ∃ a, Runs x st b a st' := by
  have e : (discard x : M PUnit) = x >>= fun _ => pure PUnit.unit := by
    simp only [discard, Functor.mapConst, Function.comp_def]
    rfl
  rw [e] at h
  obtain ⟨a, st₁, b₁, hx, h2⟩ := Runs.bind_inv h
  obtain ⟨-, rfl⟩ := runs_pure_inv h2
  exact ⟨a, hx⟩

theorem Runs.bind_assoc_inv {α β γ : Type} {x : M α} {y : α → M β} {k : β → M γ} {st st' : MState} {b : Nat} {c : γ}
    (h : Runs (x >>= fun a => y a >>= k) st b c st') :
    ∃ v st₁ b₁, Runs (x >>= y) st b v st₁ ∧ Runs (k v) st₁ b₁ c st' := by
  rw [← bind_assoc] at h
  exact Runs.bind_inv h

/-! ## Places and their parents -/

theorem resolve_parent {s : SState} {q p : Place} {pos : Pos} (hpar : parentOf q = some p)
    (h : resolve s q = some (pos, q.steps.2)) : resolve s p = some (pos, p.steps.2) := by
  obtain ⟨x, hx, -⟩ := steps_parent hpar
  unfold resolve at h ⊢
  rw [hx] at h
  rcases hv : s.varPos p.steps.1 with _ | pos'
  · simp [hv] at h
  · simp only [hv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, trivial⟩

theorem lentPrefix_snoc (s : SState) (pos : Pos) (steps : List Step) (x : Step) (ψ : List Step)
    (h : lentPrefix s pos steps = some ψ) : lentPrefix s pos (steps ++ [x]) = some ψ := by
  unfold lentPrefix at h ⊢
  have e : (List.range (steps ++ [x]).length).map (steps ++ [x]).take =
      (List.range steps.length).map steps.take ++ [steps] := by
    rw [List.length_append, List.length_singleton, List.range_succ, List.map_append, List.map_singleton,
      List.take_left' rfl]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    exact List.take_append_of_le_length (Nat.le_of_lt hi)
  rw [e, List.find?_append, h]
  rfl

/-- The reference's state after the parent's re-rooting, read for the place. -/
theorem alp_parent {s s₁ : SState} {q p : Place} {pos : Pos} (hpar : parentOf q = some p)
    (h : s₁ = s ∨ s₁ = accessLentPrefix pos p.steps.2 s) : s₁ = s ∨ s₁ = accessLentPrefix pos q.steps.2 s := by
  obtain ⟨x, hx, -⟩ := steps_parent hpar
  rcases h with rfl | rfl
  · exact .inl rfl
  · unfold accessLentPrefix
    rcases hl : lentPrefix s pos p.steps.2 with _ | ψ
    · exact .inl rfl
    · right
      rw [hx, lentPrefix_snoc s pos _ x ψ hl]

/-! ## A run with an extended context -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem runCtx_with_with (Δ₁ Δ₂ : Nat → TyS) :
    ({ ({ K with Δ := Δ₁ } : RunCtx) with Δ := Δ₂ } : RunCtx) = { K with Δ := Δ₂ } := rfl

end

/-! ## The branches' obligations -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **Above a filled parent the lent prefix exists, at or above it**: the parent holds a fill
over a live borrow, so that borrow (or one whose mark the path passes, holding it) has a site at
the parent's path or above it, and the related reference state has the same sites for the same
live labels. PROVED (the checker's site found by `site_of_fillHole`, compared step by step, read as
the reference's erased key, `KeyBridge`'s free direction). -/
theorem lentPrefix_some_of_fill (st : MState) (s : SState) (π : Nat → Nat) (q p : Place) (pos : Pos) (c : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpar : parentOf q = some p)
    (hpos : resolve s q = some (pos, q.steps.2)) (hc : ckContent st.env p = some c)
    (hfill : Ochr.fillHoles st.env c ≠ []) :
    ∃ ψ, lentPrefix s pos q.steps.2 = some ψ ∧ pathKey ψ <+: pathKey p.steps.2 := by
  -- the parent's position
  unfold ckContent at hc
  obtain ⟨pos', hck, hfol⟩ := Option.bind_eq_some_iff.mp hc
  have hpos' := rel_resolve_ck K ρ φ st s π p pos' hs hck
  rw [resolve_parent hpar hpos] at hpos'
  simp only [Option.some.injEq, Prod.mk.injEq] at hpos'
  obtain ⟨rfl, -⟩ := hpos'
  have hp := ckVarPos_mem hck
  -- a live hole of the fill, and its site at or above the parent
  obtain ⟨l, hl⟩ : ∃ l, l ∈ Ochr.fillHoles st.env c := by
    cases e : Ochr.fillHoles st.env c with
    | nil => exact absurd e hfill
    | cons l _ => exact ⟨l, List.mem_cons_self ..⟩
  have hlive : liveLoan st.env l = true := (mem_liveLoansIn_inv (fillHoles_sub st.env c l hl)).2
  obtain ⟨x, hx, ψ₁, hxp, hk⟩ := site_of_fillHole st.env l pos (valAt st.env pos) [] p.steps.2 c hfol hl
  simp only [List.nil_append] at hxp
  have hxs : x ∈ s.lent (π l) := (hs.sites l hlive x).mpr (mem_env_sitesOf hp hx)
  have hxpos : x.pos = pos := (sitesOf_prefix l pos [] _ x hx).1
  have hπl := rel_live_ref' K ρ φ st s π hg hs hlive
  -- the predicate holds at the prefix of the parent's path of the site's length
  obtain ⟨xs, hxs', -⟩ := steps_parent hpar
  have hq2 : q.steps.2 = p.steps.2 ++ [xs] := by rw [hxs']
  let n := ψ₁.length
  have hn : n ≤ p.steps.2.length := by
    have := hk.length_le; simp only [walkKey, List.length_map] at this; exact this
  have hkey : pathKey (q.steps.2.take n) = pathKey ψ₁ := by
    rw [hq2, List.take_append_of_le_length hn]
    have := List.prefix_iff_eq_take.mp hk
    simp only [walkKey, List.length_map] at this
    rw [← List.map_take] at this
    -- the checker's positional key, read as the reference's (`KeyBridge`, the free direction)
    exact pathKey_eq_of_walkKey (by simp only [walkKey]; exact this.symm)
  have hPn : s.liveLabels.any (s.reached pos fun ψ' => pathKey ψ' == pathKey (q.steps.2.take n)) = true := by
    rw [List.any_eq_true]
    refine ⟨π l, hπl, ?_⟩
    unfold SState.reached
    rw [List.any_eq_true]
    exact ⟨x, hxs, by simp [hxpos, hxp, hkey]⟩
  have hsome : (lentPrefix s pos q.steps.2).isSome := by
    unfold lentPrefix
    rw [List.find?_isSome]
    refine ⟨q.steps.2.take n, List.mem_map.mpr ⟨n, List.mem_range.mpr (by rw [hq2]; simp; omega), rfl⟩, hPn⟩
  obtain ⟨ψ, hψ⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨j, hj, rfl, hmin⟩ := lentPrefix_spec hψ
  refine ⟨q.steps.2.take j, hψ, ?_⟩
  have hjn : j ≤ n := by
    rcases Nat.lt_or_ge n j with h | h
    · rw [hmin n h] at hPn; cases hPn
    · exact h
  rw [hq2, List.take_append_of_le_length (Nat.le_trans hjn hn)]
  exact (List.take_prefix _ _).filterMap _

/-- **A filled parent accessed whole is the lent prefix accessed whole** (`movedPlace`'s fill
branch against the reference's `accessLentPrefix`). The lent prefix is the parent's path or above
it (`lentPrefix_some_of_fill`); at the parent's own path the two accesses are one; above it, the
access of the parent ends what the access of the prefix ends (`SState.access_absorb`, under
`lentPrefix_absorbInv`: no live site above the prefix, its minimality; only the prefix's borrow at
or below it, as a fill, (WF12)). Assembled. -/
theorem fillPrefix_eq (st : MState) (s : SState) (π : Nat → Nat) (q p : Place) (pos : Pos) (c : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpar : parentOf q = some p)
    (hpos : resolve s q = some (pos, q.steps.2)) (hc : ckContent st.env p = some c)
    (hfill : Ochr.fillHoles st.env c ≠ []) :
    accessLentPrefix pos q.steps.2 s = s.access pos (dataHit p.steps.2) := by
  obtain ⟨ψ, hl, hψp⟩ := lentPrefix_some_of_fill K ρ φ st s π q p pos c hg hs hpar hpos hc hfill
  unfold ckContent at hc
  obtain ⟨pos', hck, hfol⟩ := Option.bind_eq_some_iff.mp hc
  have hpos' := rel_resolve_ck K ρ φ st s π p pos' hs hck
  rw [resolve_parent hpar hpos] at hpos'
  simp only [Option.some.injEq, Prod.mk.injEq] at hpos'
  obtain ⟨rfl, -⟩ := hpos'
  have hp := ckVarPos_mem hck
  unfold accessLentPrefix
  rw [hl]
  simp only
  by_cases hk : pathKey ψ = pathKey p.steps.2
  · rw [dataHit_congr hk]
  · have hI := lentPrefix_absorbInv K ρ φ st s π pos q.steps.2 p.steps.2 ψ c hg hs hp hl hfol hψp hk
    exact SState.access_absorb hI hψp

/-- `accessInside` stops where the place's content holds no live loan. -/
theorem accessInside_final (p : Place) : ∀ (fuel : Nat) {st st' : MState} {b : Nat} {u : Unit},
    Runs (Ochr.accessInside fuel p false) st b u st' →
      ∃ v, ckContent st'.env p = some v ∧ liveLoansIn st'.env v = []
  | 0, st, st', b, u, h => by
    obtain ⟨L, left, log, h⟩ := h
    simp [Ochr.accessInside, runMachineL_exhausted] at h
  | fuel + 1, st, st', b, u, h => by
    unfold Ochr.accessInside at h
    obtain ⟨v, st₁, b₁, hc, h1⟩ := Runs.bind_inv h
    obtain ⟨hst₁, hcv⟩ := runs_content_inv hc
    subst st₁
    obtain ⟨x, st₂, b₂, hg, h2⟩ := Runs.bind_inv h1
    obtain ⟨hx, hst₂⟩ := runs_get_inv hg
    subst x; subst st₂
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    have hk : ∀ {b₃ : Nat}, Runs (match liveLoansIn st.env v with
        | l :: _ => do Ochr.endTopLoan fuel l "accessInside" (some p); Ochr.accessInside fuel p
        | [] => pure ()) st b₃ u st' → ∃ v, ckContent st'.env p = some v ∧ liveLoansIn st'.env v = [] := by
      intro b₃ h3
      split at h3
      · obtain ⟨u₂, st₄, b₄, he, h4⟩ := Runs.bind_inv h3
        exact accessInside_final p fuel h4
      · rename_i hnil
        rw [(runs_pure_inv h3).2]
        exact ⟨v, hcv, hnil⟩
    split at h2
    · exact hk h2
    · obtain ⟨u₁, st₃, b₃, hf, h3⟩ := Runs.bind_inv h2
      rw [runs_fire_inv hf] at h3
      exact hk h3

/-- **After the checker's access of a place (path and inside), its content holds no live hole**:
`accessInside` stops only where the content holds no live loan, and a fill's holes are live loans
of it (`fillHoles_sub`). -/
theorem fillAccess_clears (fuel : Nat) (st st' : MState) (p : Place) (b : Nat) (c : Value)
    (h : Runs (do Ochr.accessPath fuel p; Ochr.accessInside fuel p) st b () st')
    (hc : ckContent st'.env p = some c) : Ochr.fillHoles st'.env c = [] := by
  obtain ⟨u, st₁, b₁, -, h2⟩ := Runs.bind_inv h
  obtain ⟨v, hv, hnil⟩ := accessInside_final p fuel h2
  rw [hc] at hv
  cases hv
  cases e : Ochr.fillHoles st'.env c with
  | nil => rfl
  | cons l ls =>
    have := fillHoles_sub st'.env c l (by rw [e]; exact List.mem_cons_self ..)
    rw [hnil] at this
    cases this

/-- The checker's access forgets no unknown (its ends substitute, and a sealed program they re-run
keeps the types its copy created). True by inspection: every write of the table is a push
(`freshAbs`), an in-place rewrite (`Env.mapState`) or a restore that keeps the new entries
(`restoreKeep`); a proof is an induction over the interpreter, not attempted by the lead's
decision. Swept (docs/31 D58): 358,141 accesses of a top-frame variable from the suite's recorded
states and 25,451 ends, none shrinking the table or a record list (none of the accesses grew it);
along each run, 68,120 consecutive recorded states, none shrinking it. Open. -/
theorem access_absTy (fuel : Nat) (st st' : MState) (p : Place) (b : Nat)
    (h : Runs (do Ochr.accessPath fuel p; Ochr.accessInside fuel p) st b () st') :
    st.absTy.size ≤ st'.absTy.size := by
  sorry

/-- **A recorded η-refinement means the unknown** (D68: the same fields in every private copy).
`Good`'s path condition for the record gives `ρ σ = ⟦r⟧` at the unknown's type and the constant
future; the record holds no loan ((WF11)), so it means the same at every future (`meanV_congr`), and
it is top-hint-free ((Hη)), so at every hint (`meanV_hintIndep`). PROVED (docs/31 D55). -/
theorem etaRecorded_sim (st : MState) (σ : Nat) (r : Value) (hg : Good K.dm K.M K.Γ ρ st)
    (hctx : CtxOk K ρ st) (hr : st.etaRefs.lookup σ = some r) : ∀ ψ H, ρ σ = meanV K ρ ψ H r := by
  intro ψ H
  have hm := mem_of_lookup hr
  rw [hg.1.eta σ r hm, meanV_eq_mean_aux K ρ (fun _ => .err) _ r]
  have h11 : WF11 st := hg.2.2.2.2.2.2.2.2.2.2.2.1
  rw [meanV_congr K ρ (fun _ => .err) ψ _ r hctx.noLabel fun l hl => by
    have := h11.2.2.2.2 σ r hm l
    rw [Value.hasLoan_of_hasLoanM hl] at this; cases this]
  exact meanV_hintIndep K ρ ψ r (hctx.shapes.etaHint σ r hm) _ H

/-- **A fresh η-refinement of an unknown of a one-constructor type, recorded** (`ctorRefinement`,
then the record `σ := r`): under the assignment extended at the fresh field unknowns by the
fields of `ρ σ` (a member of a one-constructor type is that constructor: D32 reads its fields
off the value) and `Δ` by their types, the refinement means `ρ σ`, and the relation (the reference
is untouched), `Good` (the record is the path condition just met) and the context are kept. Open. -/
theorem etaFresh_sim (fuel : Nat) (st st' : MState) (p : Place) (σ : Nat) (n : String) (ps : List Value)
    (d : IndDecl) (r : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hp : ckContent st.env p = some (.abs σ)) (hT : st.absTy[σ]? = some (.tInd n ps))
    (hd : st.inds.find? (·.name == n) = some d) (h1 : d.ctors.length = 1)
    (h : Runs (Ochr.ctorRefinement fuel d ps 0) st b r st')
    (hD : DecTab K.D { st' with etaRefs := (σ, r) :: st'.etaRefs }) :
    ∃ ρ' Δ', Ext K ρ φ π st { st' with etaRefs := (σ, r) :: st'.etaRefs } s ρ' Δ' ∧
      ∀ ψ H, ρ' σ = meanV { K with Δ := Δ' } ρ' ψ H r := by
  sorry

/-- **`placeType?` in the simulation form** (its field and parameter types run on private copies:
Ω is the snapshot's, and what the copies keep is assigned by an extension). Assembled: the induction
hypothesis's `placeTypeQ_step` (a private computation) and `Rel.kept`. -/
theorem placeTypeQ_sim (fuel : Nat) (ih : StepsIHBelow fuel) (st st' : MState) (p : Place) (T? : Option Value)
    (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.placeType? fuel p) st b T? st') (hD : DecTab K.D st') :
    ∃ ρ' Δ', Ext K ρ φ π st st' s ρ' Δ' ∧ st'.env = st.env := by
  obtain ⟨hk, ρ', Δ', e⟩ := (ih.at K ρ φ).placeTypeQ_step st st' p T? hg hctx hD b h
  exact ⟨ρ', Δ', ⟨hk.2.2.2.2.1, e.1, e.2.1, Rel.kept K ρ φ hg hctx hs hk e, e.2.2⟩, hk.1⟩

/-- **A sealed program this world already generalised: its record's value means it**
(`recordedNeutral`): `Good`'s path condition for the record `n := σ` makes `σ`, refined by the
refinements made since (`expandRefs`), mean `⟦n⟧`; the value names typed unknowns and holds no loan
((WF6), (WF11)). Open. -/
theorem recordedNeutral_ok (st : MState) (n r : Value) (b' : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hr : Runs (Ochr.recordedNeutral n) st b' (some r) st) : NeutralOk K ρ st n r := by
  sorry

/-- The record read back and substituted (assembled: `recordedNeutral_ok`, then the induction
hypothesis's `substEnv_neutral_step`). -/
theorem recorded_sim (fuel : Nat) (ih : StepsIHBelow fuel) (st st' : MState) (n r : Value) (s : SState)
    (π : Nat → Nat) (b b' : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hr : Runs (Ochr.recordedNeutral n) st b' (some r) st)
    (h : Runs (Ochr.substEnv fuel n r true) st b () st') (hD : DecTab K.D st') :
    ∃ ρ' Δ', Ext K ρ φ π st st' s ρ' Δ' := by
  obtain ⟨hsh, ρ', Δ', e, hrel⟩ := (ih.at K ρ φ).substEnv_neutral_step st st' n r hg hctx s π hs
    (recordedNeutral_ok K ρ st n r b' hg hctx hr) hD b h
  exact ⟨ρ', Δ', Ext.of_extOk K ρ φ hsh.2.2.2.1 e hrel⟩

/-- **A sealed program in Ω with no live hole holds no loan at all**: a loan it holds (outside a
recorded reading, (WF15)) is in its list of loans, so it is live ((L), [End] substitutes a loan
everywhere its borrow ends), so it is a live hole, and there is none. PROVED (docs/31 D46). -/
theorem sealed_loanFree (st : MState) (p : Place) (t : Term) (hg : Good K.dm K.M K.Γ ρ st)
    (hctx : CtxOk K ρ st)
    (hp : ckContent st.env p = some (.sealed t)) (hfill : Ochr.fillHoles st.env (.sealed t) = []) :
    ∀ l, (Value.sealed t).hasLoan l = false := by
  intro l
  cases h : (Value.sealed t).hasLoan l
  · rfl
  · exfalso
    obtain ⟨root, hroot, hf⟩ := ckContent_root hp
    have h15 : WF15 st.env := hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hrd : (Value.sealed t).anyAtom (rdHasLoan l) = false := by
      have hr := h15 root hroot l
      rw [← rdHasLoan_eq] at hr
      cases e : (Value.sealed t).anyAtom (rdHasLoan l)
      · rfl
      · have := anyAtom_of_follow _ _ _ hf e
        rw [hr] at this; cases this
    have hmem := mem_loans_of_hasLoan hrd h
    have hlive := hctx.shapes.loans root hroot l (loans_of_follow _ _ _ hf hmem)
    have hin := mem_liveLoansIn hmem hlive
    simp only [Ochr.fillHoles] at hfill
    rw [hfill] at hin; cases hin


/-- **A recorded η refinement is one `refine_step` accepts** (`RefineOk`): it means its unknown
(given), names typed unknowns ((WF6)), not its own ((Hη≠), `ShapeFacts.etaNoSelf`), and holds no
loan ((WF11)). -/
theorem etaRefineOk (st : MState) (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) {σ : Nat} {r : Value}
    (h : (σ, r) ∈ st.etaRefs) (hσ : ∀ ψ H, ρ σ = meanV K ρ ψ H r) : RefineOk K ρ st σ r :=
  have h11 : WF11 st := hg.2.2.2.2.2.2.2.2.2.2.2.1
  ⟨hσ, (Good.eta_bound K hg h).1, (Good.eta_bound K hg h).2, hctx.shapes.etaNoSelf σ r h,
    fun l => h11.2.2.2.2 σ r h l⟩

/-- **An unknown of a one-constructor type refined in place** (`Machine.etaInPlace`, D68, D93:
`movedPlace`'s η branch, a one-constructor match on an unknown, a block's capture): this world's
recorded refinement (`etaRecorded_sim`) or a fresh one, recorded (`etaFresh_sim`), then the
substitution (the induction hypothesis's `refine_step`, at a record `etaRefineOk` shows it
accepts). The reference is untouched; the assignment and Δ are extended at the fresh fields.
Assembled: no `sorry` beyond `etaFresh_sim`. -/
theorem etaInPlace_sim (fuel : Nat) (ih : StepsIHBelow fuel) (st st' : MState) (p : Place) (σ : Nat) (n : String) (ps : List Value)
    (d : IndDecl) (r : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hp : ckContent st.env p = some (.abs σ)) (hT : st.absTy[σ]? = some (.tInd n ps))
    (hd : st.inds.find? (·.name == n) = some d) (h1 : d.ctors.length = 1)
    (h : Runs (Ochr.etaInPlace fuel σ d ps) st b r st') (hD : DecTab K.D st') :
    ∃ ρ' Δ', Ext K ρ φ π st st' s ρ' Δ' := by
  rcases fuel with _ | f
  · obtain ⟨L, left, log, h⟩ := h
    simp [Ochr.etaInPlace, runMachineL_exhausted] at h
  rw [Ochr.etaInPlace] at h
  obtain ⟨x, st₇, b₇, hget, h7⟩ := Runs.bind_inv h
  obtain ⟨hx, hst₇⟩ := runs_get_inv hget
  subst x; subst st₇
  dsimp only at h7
  split at h7
  · -- the recorded refinement
    rename_i r₀ hr
    obtain ⟨r', st₈, b₈, hpr, h8⟩ := Runs.bind_inv h7
    obtain ⟨hrr, hst₈⟩ := runs_pure_inv hpr
    subst r'; subst st₈
    obtain ⟨u, st₉, b₉, hrf, h9⟩ := Runs.bind_inv h8
    obtain ⟨-, hst⟩ := runs_pure_inv h9
    subst hst
    have hσ := etaRecorded_sim K ρ st σ r₀ hg hctx hr
    rcases f with _ | f
    · obtain ⟨L, left, log, hrf⟩ := hrf
      simp [Ochr.refine, runMachineL_exhausted] at hrf
    obtain ⟨hsh, ρ', Δ', he, hrel⟩ := (ih (f + 1) (by omega) K ρ φ).refine_step st st' σ r₀ hg hctx s π hs
      (etaRefineOk K ρ st hg hctx (mem_of_lookup hr) hσ) hD _ hrf
    exact ⟨ρ', Δ', Ext.of_extOk K ρ φ hsh.2.2.2.1 he hrel⟩
  · -- a fresh refinement, recorded
    obtain ⟨r₀, st₈, b₈, hcr, h8⟩ := Runs.bind_inv h7
    obtain ⟨u, st₉, b₉, hmod, h9⟩ := Runs.bind_inv h8
    obtain ⟨L, left, log, hmod⟩ := hmod
    simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at hmod
    obtain ⟨⟨-, hst₉⟩, -⟩ := hmod
    subst st₉
    obtain ⟨r', st₁₀, b₁₀, hpr, h10⟩ := Runs.bind_inv h9
    obtain ⟨hrr, hst₁₀⟩ := runs_pure_inv hpr
    subst r'; subst st₁₀
    obtain ⟨u', st₁₁, b₁₁, hrf, h11⟩ := Runs.bind_inv h10
    obtain ⟨-, hst⟩ := runs_pure_inv h11
    subst hst
    obtain ⟨ρ₂, Δ₂, E₂, hσ⟩ := etaFresh_sim K ρ φ f st st₈ p σ n ps d r₀ s π _ hg hctx hs hp hT hd h1 hcr
      (hD.of_rest (grows_refine _ _ _) hrf)
    rcases f with _ | f
    · obtain ⟨L, left, log, hrf⟩ := hrf
      simp [Ochr.refine, runMachineL_exhausted] at hrf
    obtain ⟨hsh, ρ₃, Δ₃, he, hrel⟩ := (ih (f + 1) (by omega) { K with Δ := Δ₂ } ρ₂ φ).refine_step
      _ st' σ r₀ E₂.good E₂.ctx s π E₂.rel
      (etaRefineOk { K with Δ := Δ₂ } ρ₂ _ E₂.good E₂.ctx List.mem_cons_self hσ) hD _ hrf
    exact ⟨ρ₃, Δ₃, E₂.trans K ρ φ (Ext.of_extOk _ _ φ hsh.2.2.2.1 he hrel)⟩


/-- **A stuck block's captures made places** (`Machine.etaPlace`, D93 rule 3: after the block's
entry and before its arms, each capture's prefix that is an unknown, or a sealed program, of a
one-constructor type is refined in place, refusing a fill over a live borrow). The reference never
forms a block and never refines: in the simulation form the reference state is untouched and the
assignment and Δ are extended at the fields named, as `movedPlace`'s branches are (the same steps:
`etaInPlace_sim`, `placeTypeQ_sim`, `recorded_sim`, `generalizeNeutral_step`). Needed by the block's
statement (`closeBlock_step_stmt`). Open: an induction on the fuel along `etaPlace`'s recursion, as
`movedPlace_step` is assembled; not written. -/
theorem etaPlace_sim (fuel : Nat) (st st' : MState) (q : Place) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.etaPlace fuel q) st b () st') (hD : DecTab K.D st') :
    ∃ ρ' Δ', Ext K ρ φ π st st' s ρ' Δ' := by
  sorry

end

/-! ## The last part (D94) and the lent prefix -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **`movedPlace`'s last part (D94)**: it changes nothing, and returns the place where it exists
or a prefix holding `⊥` or `⋆`; anything else is the [Join] rejection, which is no run. -/
theorem mpFinal_inv {q p q' : Place} {st st' : MState} {b : Nat} (h : Runs (mpFinal q p) st b q' st') :
    st' = st ∧ ((q' = q ∧ ∃ w, ckContent st.env q = some w) ∨
      (q' = p ∧ (ckContent st.env p = some .bot ∨ ckContent st.env p = some .proof))) := by
  unfold mpFinal at h
  obtain ⟨o, st₁, b₁, hc, h⟩ := Runs.bind_inv h
  obtain ⟨rfl, pos, hpos, rfl⟩ := runs_content?_inv hc
  split at h
  · rename_i hsome
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨rfl, .inl ⟨rfl, w, by unfold ckContent; rw [hpos, Option.bind_some]; exact hw⟩⟩
  · obtain ⟨v, st₂, b₂, hcv, h2⟩ := Runs.bind_inv h
    obtain ⟨rfl, hv⟩ := runs_content_inv hcv
    split at h2
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h2; exact ⟨rfl, .inr ⟨rfl, .inl hv⟩⟩
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h2; exact ⟨rfl, .inr ⟨rfl, .inr hv⟩⟩
    · obtain ⟨s1, st₃, b₃, -, h3⟩ := Runs.bind_inv h2
      obtain ⟨s2, st₄, b₄, -, h4⟩ := Runs.bind_inv h3
      exact (runs_err_false h4).elim

/-- **After the shortest lent prefix is accessed whole, no strict prefix of the path is lent**:
every strict prefix of the path is a prefix of the accessed one or extends it, so a site there is
one the access reaches, and after the access no live label has one (`SState.access_post`, the
access's fixpoint). Proved for every reference state. -/
theorem alp_idem (pos : Pos) (steps : List Step) (s : SState) :
    accessLentPrefix pos steps (accessLentPrefix pos steps s) = accessLentPrefix pos steps s := by
  unfold accessLentPrefix
  rcases hl : lentPrefix s pos steps with _ | ψ
  · simp only [hl]
  · simp only
    have hψ : ψ ∈ (List.range steps.length).map steps.take := List.mem_of_find?_eq_some hl
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
    have hnone : lentPrefix (s.access pos (dataHit (steps.take j))) pos steps = none := by
      unfold lentPrefix
      apply List.find?_eq_none.mpr
      intro ψ' hψ' hany
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ'
      obtain ⟨y, hy, hr⟩ := List.any_eq_true.mp hany
      have hpost := SState.access_post s pos (dataHit (steps.take j)) y hy
      rw [← Bool.not_eq_true] at hpost
      apply hpost
      unfold SState.reached at hr ⊢
      obtain ⟨x, hx, hxr⟩ := List.any_eq_true.mp hr
      refine List.any_eq_true.mpr ⟨x, hx, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxr ⊢
      refine ⟨hxr.1, ?_⟩
      unfold dataHit
      rw [hxr.2]
      simp only [Bool.or_eq_true, List.isPrefixOf_iff_prefix]
      rcases Nat.le_total i j with h | h
      · exact .inl (pathKey_take_prefix steps h)
      · exact .inr (pathKey_take_prefix steps h)
    rw [hnone]


end

/-! ## `movedPlace`, branch by branch -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem resolve_alp {s s₁ : SState} {pos : Pos} {steps : List Step} (h : s₁ = s ∨ s₁ = accessLentPrefix pos steps s)
    (r : Place) : resolve s₁ r = resolve s r := by
  rcases h with rfl | rfl
  · rfl
  · exact resolve_of_declsOf (declsOf_accessLentPrefix s pos steps) r

theorem scopeOf_alp {s s₁ : SState} {pos : Pos} {steps : List Step} (h : s₁ = s ∨ s₁ = accessLentPrefix pos steps s) :
    scopeOf s₁ = scopeOf s := by
  rcases h with rfl | rfl
  · rfl
  · exact scopeOf_of_declsOf (declsOf_accessLentPrefix s pos steps)

/-- The reference's state after an access of the lent prefix, again: the same. -/
theorem alp_again {s s₁ s₂ : SState} {pos : Pos} {steps : List Step}
    (hidem : accessLentPrefix pos steps (accessLentPrefix pos steps s) = accessLentPrefix pos steps s)
    (h₁ : s₁ = s ∨ s₁ = accessLentPrefix pos steps s)
    (h₂ : s₂ = s₁ ∨ s₂ = accessLentPrefix pos steps s₁) : s₂ = s ∨ s₂ = accessLentPrefix pos steps s := by
  rcases h₂ with rfl | rfl
  · exact h₁
  · rcases h₁ with rfl | rfl
    · exact .inr rfl
    · exact .inr hidem

/-- `movedPlace`'s last part only reads (it extends no table). -/
theorem grows_mpFinal (q p : Place) : GrowsM (mpFinal q p) := by
  unfold mpFinal
  grows_go

/-- **`movedPlace` after the parent is found**, in the simulation form. -/
theorem mpTail_sim (fuel : Nat) (ih : StepsIHBelow fuel)
    (st st' : MState) (q p q' : Place) (pos : Pos) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s q = some (pos, q.steps.2)) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hpar : parentOf q = some p) (hq : ckContent st.env q = none) (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (mpTail fuel q p) st bh q' st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (s' : SState), (s' = s ∨ s' = accessLentPrefix pos q.steps.2 s) ∧
      Ext K ρ φ π st st' s' ρ' Δ' ∧ MPOut st' q q' := by
  rw [mpTail_eq] at h
  unfold mpTail' at h
  obtain ⟨p', st₁, b₁, hmp, h⟩ := Runs.bind_inv h
  have hD₁ : DecTab K.D st₁ := hD.of_rest (by grows_go; all_goals exact grows_mpFinal _ _) h
  obtain ⟨ρ₁, Δ₁, s₁, hsz₁, hag₁, hs₁or, hctx₁, hrel₁, hg₁, hout₁⟩ :=
    (ih.at K ρ φ).movedPlace_step st st₁ p p' pos s π hg hctx hs (resolve_parent hpar hpos) (grain_parent hpar hgrain)
      hD₁ bh hmp
  have hs₁q := alp_parent hpar hs₁or
  have hidem := alp_idem pos q.steps.2 s
  have E₁ : Ext K ρ φ π st st₁ s₁ ρ₁ Δ₁ := ⟨hsz₁, hag₁, hctx₁, hrel₁, hg₁⟩
  obtain ⟨x, st₂, b₂, hget, h2⟩ := Runs.bind_inv h
  obtain ⟨hx, hst₂⟩ := runs_get_inv hget
  subst x; subst st₂
  obtain ⟨c, st₃, b₃, hcont, h3⟩ := Runs.bind_inv h2
  obtain ⟨hst₃, hc⟩ := runs_content_inv hcont
  subst st₃
  obtain ⟨xs, hxs, -⟩ := steps_parent hpar
  have hq1 : q.steps.1 = p.steps.1 := by rw [hxs]
  have hq2 : q.steps.2 = p.steps.2 ++ [xs] := by rw [hxs]
  rcases hout₁ with ⟨hpp, w, hw⟩ | ⟨hroot, hpre, hbt⟩
  · subst p'
    rw [hc] at hw
    cases hw
    split at h3
    · -- the parent holds a fill: accessed whole, then the place asked again
      rename_i hfill
      have hfill' : Ochr.fillHoles st₁.env c ≠ [] := by simpa using hfill
      obtain ⟨u, st₄, b₄, hacc, h4⟩ := Runs.bind_assoc_inv h3
      have hres₁ : resolve s₁ p = some (pos, p.steps.2) := by
        rw [resolve_alp hs₁q]; exact resolve_parent hpar hpos
      have hD₄ : DecTab K.D st₄ := hD.of_rest (by grows_go; all_goals exact grows_mpFinal _ _) h4
      obtain ⟨hsz₄, ρ₄, Δ₄, e₄, hrel₄⟩ := (ih.at { K with Δ := Δ₁ } ρ₁ φ).access_step st₁ st₄ p pos false s₁ π hg₁ hctx₁
        hrel₁ hres₁ hD₄ b₃ hacc
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hrel₄
      rw [← fillPrefix_eq { K with Δ := Δ₁ } ρ₁ φ st₁ s₁ π q p pos c hg₁ hrel₁ hpar
        (by rw [resolve_alp hs₁q]; exact hpos) hc hfill'] at hrel₄
      have E₂ := Ext.of_extOk { K with Δ := Δ₁ } ρ₁ φ hsz₄ e₄ hrel₄
      obtain ⟨x, st₅, b₅, hget, h5⟩ := Runs.bind_inv h4
      obtain ⟨hx, hst₅⟩ := runs_get_inv hget
      subst x; subst st₅
      obtain ⟨c₂, st₆, b₆, hcont, h6⟩ := Runs.bind_inv h5
      obtain ⟨hst₆, hc₂⟩ := runs_content_inv hcont
      subst st₆
      have hclr := fillAccess_clears fuel st₁ st₄ p b₃ c₂ hacc hc₂
      simp only [hclr, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h6
      have hs₂q := alp_again hidem hs₁q (.inr rfl)
      obtain ⟨ρ₃, Δ₃, s₃, hsz₃, hag₃, hs₃or, hctx₃, hrel₃, hg₃, hout₃⟩ :=
        (ih.at { K with Δ := Δ₄ } ρ₄ φ).movedPlace_step st₄ st' q q' pos (accessLentPrefix pos q.steps.2 s₁) π
          E₂.good E₂.ctx E₂.rel (by rw [resolve_alp hs₂q]; exact hpos)
          (by rw [scopeOf_alp hs₂q]; exact hgrain) hD b₆ h6
      have E₃ : Ext { K with Δ := Δ₄ } ρ₄ φ π st₄ st' s₃ ρ₃ Δ₃ := ⟨hsz₃, hag₃, hctx₃, hrel₃, hg₃⟩
      exact ⟨ρ₃, Δ₃, s₃, alp_again hidem hs₂q hs₃or, (E₁.trans K ρ φ E₂).trans K ρ φ E₃, hout₃⟩
    · -- no fill: the parent's content decides
      rename_i hnf
      have hfill : Ochr.fillHoles st₁.env c = [] := by simpa using hnf
      obtain ⟨c', st₄, b₄, hcont', h4⟩ := Runs.bind_inv h3
      obtain ⟨hst₄, hc'⟩ := runs_content_inv hcont'
      subst st₄
      rw [hc] at hc'
      cases hc'
      have hgr₁ : GrainOk K.D K.Γ (scopeOf s₁) q := by rw [scopeOf_alp hs₁q]; exact hgrain
      have hpos₁ : resolve s₁ q = some (pos, q.steps.2) := by rw [resolve_alp hs₁q]; exact hpos
      have hfinal : ∀ {st₅ : MState} {b₅ : Nat} {ρ₂ : Assignment} {Δ₂ : Nat → TyS},
          Ext K ρ φ π st st₅ s₁ ρ₂ Δ₂ → Runs (mpFinal q p) st₅ b₅ q' st' →
          ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (s' : SState), (s' = s ∨ s' = accessLentPrefix pos q.steps.2 s) ∧
            Ext K ρ φ π st st' s' ρ' Δ' ∧ MPOut st' q q' := by
        intro st₅ b₅ ρ₂ Δ₂ E h5
        obtain ⟨rfl, hout⟩ := mpFinal_inv h5
        refine ⟨ρ₂, Δ₂, s₁, hs₁q, E, ?_⟩
        rcases hout with h | ⟨rfl, h⟩
        · exact .inl h
        · exact .inr ⟨hq1.symm, by rw [hq2]; exact List.prefix_append _ _, h⟩
      split at h4
      · -- an unknown: of a one-constructor type, η-refined, then the place asked again
        rename_i σ
        obtain ⟨T, st₅, b₅, habsT, h5⟩ := Runs.bind_inv h4
        obtain ⟨hst₅, hT⟩ := runs_absType_inv habsT
        subst st₅
        split at h5
        · rename_i n ps
          obtain ⟨d, st₆, b₆, hlk, h6⟩ := Runs.bind_inv h5
          obtain ⟨hst₆, hd⟩ := runs_lookupInd_inv hlk
          subst st₆
          split at h6
          · rename_i h1
            have h1' : d.ctors.length = 1 := by simpa using h1
            obtain ⟨u, st₇, b₇, hdis, h7⟩ := Runs.bind_inv h6
            obtain ⟨r, heta⟩ := runs_discard_inv hdis
            obtain ⟨ρ₂, Δ₂, E₂⟩ := etaInPlace_sim { K with Δ := Δ₁ } ρ₁ φ fuel ih st₁ st₇ p σ n ps d r s₁ π b₆
              hg₁ hctx₁ hrel₁ hc hT hd h1' heta (hD.of_rest (grows_movedPlace _ _) h7)
            obtain ⟨ρ₄, Δ₄, s₄, hsz₄, hag₄, hs₄or, hctx₄, hrel₄, hg₄, hout₄⟩ :=
              (ih.at { K with Δ := Δ₂ } ρ₂ φ).movedPlace_step st₇ st' q q' pos s₁ π E₂.good E₂.ctx E₂.rel hpos₁
                hgr₁ hD b₇ h7
            have E₄ : Ext { K with Δ := Δ₂ } ρ₂ φ π st₇ st' s₄ ρ₄ Δ₄ := ⟨hsz₄, hag₄, hctx₄, hrel₄, hg₄⟩
            exact ⟨ρ₄, Δ₄, s₄, alp_again hidem hs₁q hs₄or, E₁.trans K ρ φ (E₂.trans _ _ φ E₄), hout₄⟩
          · exact hfinal E₁ h6
        · exact hfinal E₁ h5
      · -- a sealed program: of a one-constructor computed type, generalised (or its record), then
        -- the place asked again
        rename_i t
        obtain ⟨T?, st₅, b₅, hpt, h5⟩ := Runs.bind_inv h4
        obtain ⟨ρ₂, Δ₂, E₂, henv₅⟩ := placeTypeQ_sim { K with Δ := Δ₁ } ρ₁ φ fuel ih st₁ st₅ p T? s₁ π b₄ hg₁ hctx₁ hrel₁ hpt
          (hD.of_rest (by grows_go; all_goals exact grows_mpFinal _ _) h5)
        have E₁₂ := E₁.trans K ρ φ E₂
        split at h5
        · rename_i tn args
          obtain ⟨d, st₆, b₆, hlk, h6⟩ := Runs.bind_inv h5
          obtain ⟨hst₆, hd⟩ := runs_lookupInd_inv hlk
          subst st₆
          split at h6
          · obtain ⟨o, st₇, b₇, hrn, h7⟩ := Runs.bind_inv h6
            have hst₇ := runs_recordedNeutral_inv hrn
            subst st₇
            have hc₅ : ckContent st₅.env p = some (.sealed t) := by rw [henv₅]; exact hc
            split at h7
            · -- generalised before in this world: its record's value
              rename_i r
              obtain ⟨u, st₈, b₈, hsub, h8⟩ := Runs.bind_inv h7
              obtain ⟨ρ₃, Δ₃, E₃⟩ := recorded_sim { K with Δ := Δ₂ } ρ₂ φ fuel ih st₅ st₈ (.sealed t) r s₁ π b₇ b₆
                E₂.good E₂.ctx E₂.rel hrn hsub (hD.of_rest (grows_movedPlace _ _) h8)
              obtain ⟨ρ₄, Δ₄, s₄, hsz₄, hag₄, hs₄or, hctx₄, hrel₄, hg₄, hout₄⟩ :=
                (ih.at { K with Δ := Δ₃ } ρ₃ φ).movedPlace_step st₈ st' q q' pos s₁ π E₃.good E₃.ctx E₃.rel hpos₁
                  hgr₁ hD b₈ h8
              have E₄ : Ext { K with Δ := Δ₃ } ρ₃ φ π st₈ st' s₄ ρ₄ Δ₄ := ⟨hsz₄, hag₄, hctx₄, hrel₄, hg₄⟩
              exact ⟨ρ₄, Δ₄, s₄, alp_again hidem hs₁q hs₄or,
                E₁.trans K ρ φ (E₂.trans _ _ φ (E₃.trans _ _ φ E₄)), hout₄⟩
            · -- generalised here (D34)
              obtain ⟨u, st₈, b₈, hdisc, h8⟩ := Runs.bind_inv h7
              obtain ⟨σ, hgen⟩ := runs_discard_inv hdisc
              have hfill₅ : Ochr.fillHoles st₅.env (.sealed t) = [] := by rw [henv₅]; exact hfill
              have hfree := sealed_loanFree { K with Δ := Δ₂ } ρ₂ st₅ p t E₂.good E₂.ctx hc₅ hfill₅
              obtain ⟨hsh₃, ρ₃, Δ₃, he₃, hrel₃, -⟩ :=
                (ih.at { K with Δ := Δ₂ } ρ₂ φ).generalizeNeutral_step st₅ st₈ p (.sealed t) σ
                  E₂.good E₂.ctx s₁ π E₂.rel hc₅ ⟨t, rfl⟩ hfree (hD.of_rest (grows_movedPlace _ _) h8) b₇ hgen
              have E₃ := Ext.of_extOk { K with Δ := Δ₂ } ρ₂ φ hsh₃.2.2.2.1 he₃ hrel₃
              obtain ⟨ρ₄, Δ₄, s₄, hsz₄, hag₄, hs₄or, hctx₄, hrel₄, hg₄, hout₄⟩ :=
                (ih.at { K with Δ := Δ₃ } ρ₃ φ).movedPlace_step st₈ st' q q' pos s₁ π E₃.good E₃.ctx E₃.rel hpos₁
                  hgr₁ hD b₈ h8
              have E₄ : Ext { K with Δ := Δ₃ } ρ₃ φ π st₈ st' s₄ ρ₄ Δ₄ := ⟨hsz₄, hag₄, hctx₄, hrel₄, hg₄⟩
              exact ⟨ρ₄, Δ₄, s₄, alp_again hidem hs₁q hs₄or,
                E₁.trans K ρ φ (E₂.trans _ _ φ (E₃.trans _ _ φ E₄)), hout₄⟩
          · exact hfinal E₁₂ h6
        · exact hfinal E₁₂ h5
      · -- any other content: the last part
        exact hfinal E₁ h4
  · -- the parent re-rooted to a prefix holding `⊥` or `⋆`: the last part, from that prefix
    have hcv : c = .bot ∨ c = .proof := by
      rcases hbt with hb | hb <;> rw [hc] at hb <;> cases hb <;> simp
    have hfill : Ochr.fillHoles st₁.env c = [] := by rcases hcv with rfl | rfl <;> rfl
    simp only [hfill, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h3
    obtain ⟨c', st₄, b₄, hcont', h4⟩ := Runs.bind_inv h3
    obtain ⟨hst₄, hc'⟩ := runs_content_inv hcont'
    subst st₄
    rw [hc] at hc'
    cases hc'
    have h4' : Runs (mpFinal q p') st₁ b₄ q' st' := by rcases hcv with rfl | rfl <;> exact h4
    obtain ⟨rfl, hout⟩ := mpFinal_inv h4'
    refine ⟨ρ₁, Δ₁, s₁, hs₁q, E₁, ?_⟩
    rcases hout with h | ⟨rfl, h⟩
    · exact .inl h
    · exact .inr ⟨by rw [hroot, hq1], by rw [hq2]; exact hpre.trans (List.prefix_append _ _), h⟩
end

/-! ## `movedPlace` and the drop of one place, assembled -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **`movedPlace` in the simulation form** (the induction hypothesis's field at `fuel + 1`): where
the place exists it is returned and nothing changes; otherwise `mpTail_sim`. -/
theorem movedPlace_step (fuel : Nat) (ih : StepsIHBelow fuel) :
    movedPlace_step_stmt K ρ φ (fuel + 1) := by
  intro st st' q q' pos s π hg hctx hs hpos hgrain hD bh h
  rw [movedPlace_succ_eq] at h
  obtain ⟨o, st₀, b₀, hc, h⟩ := Runs.bind_inv h
  obtain ⟨hst₀, pos₀, hck₀, ho⟩ := runs_content?_inv hc
  subst st₀; subst o
  have hres₀ := rel_resolve_ck K ρ φ st s π q pos₀ hs hck₀
  rw [hpos] at hres₀
  simp only [Option.some.injEq, Prod.mk.injEq] at hres₀
  obtain ⟨hpp, -⟩ := hres₀
  subst pos₀
  cases hf : (valAt st.env pos).follow q.steps.2 with
  | some w =>
    rw [hf] at h
    simp only [Option.isSome_some, ↓reduceIte] at h
    obtain ⟨hq', hst'⟩ := runs_pure_inv h
    subst q'; subst st'
    refine ⟨ρ, K.Δ, s, Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, .inl rfl, ?_, ?_, ?_,
      .inl ⟨rfl, w, ?_⟩⟩
    · rw [runCtx_with_self K]; exact hctx
    · rw [runCtx_with_self K]; exact hs
    · rw [runCtx_with_self K]; exact hg
    · simp [ckContent, hck₀, hf]
  | none =>
    rw [hf] at h
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
    have hq : ckContent st.env q = none := by simp [ckContent, hck₀, hf]
    rcases hpar : parentOf q with _ | p
    · cases q with
      | var i => simp [Place.steps, Value.follow] at hf
      | _ => simp [parentOf] at hpar
    · rw [hpar] at h
      obtain ⟨ρ', Δ', s', hs', E, hout⟩ := mpTail_sim K ρ φ fuel ih st st' q p q' pos s π hg hctx hs hpos hgrain hpar hq
        hD b₀ h
      exact ⟨ρ', Δ', s', E.size, E.agree, hs', E.ctx, E.rel, E.good, hout⟩

/-- The reference's drop of a place from the state after the lent prefix's access is its drop. -/
theorem joinDropOne_alp {s s₁ : SState} {q : Place} {pos : Pos} (hpos : resolve s q = some (pos, q.steps.2))
    (hidem : accessLentPrefix pos q.steps.2 (accessLentPrefix pos q.steps.2 s) = accessLentPrefix pos q.steps.2 s)
    (h : s₁ = s ∨ s₁ = accessLentPrefix pos q.steps.2 s) : joinDropOne K φ s₁ q = joinDropOne K φ s q := by
  rcases h with rfl | rfl
  · rfl
  · have hpos₁ : resolve (accessLentPrefix pos q.steps.2 s) q = some (pos, q.steps.2) := by
      rw [resolve_alp (.inr rfl)]; exact hpos
    simp only [joinDropOne, hpos₁, hpos, hidem]

/-- **Where the checker re-rooted to a prefix holding `⊥` or `⋆`, the reference's drop keeps the
relation** (docs/31 D56): nothing is lent over, at or under the prefix (`clear_of_bot`; a `⋆` at a
root lends nothing, and none strictly below a variable is above a dropped place,
`not_below_proof`), so neither access ends anything; the place reads through the prefix (`⋆`
along any path, `moved` along `*`s only, nothing otherwise), and where it reads `moved` the write
of `moved` along it is the write along the prefix, over a moved part. PROVED from
`grain_deref_not_proof`. -/
theorem joinDropOne_noop (st : MState) (s s₁ : SState) (π : Nat → Nat) (q q' : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s₁)
    (hs₁ : s₁ = s ∨ s₁ = accessLentPrefix pos q.steps.2 s)
    (hpos : resolve s q = some (pos, q.steps.2)) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (hpre : q'.steps.1 = q.steps.1 ∧ q'.steps.2 <+: q.steps.2)
    (hq' : ckContent st.env q' = some .bot ∨ ckContent st.env q' = some .proof) :
    Rel K ρ φ π st (joinDropOne K φ s q) := by
  rw [← joinDropOne_alp K φ hpos (alp_idem pos q.steps.2 s) hs₁]
  have hres₁ : resolve s₁ q = some (pos, q.steps.2) := by rw [resolve_alp hs₁]; exact hpos
  have hgr₁ : GrainOk K.D K.Γ (scopeOf s₁) q := by rw [scopeOf_alp hs₁]; exact hgrain
  have hcp₁ : K.D.copy (K.D.placeDecl (scopeOf s₁) q) = false := by rw [scopeOf_alp hs₁]; exact hcopy
  obtain ⟨c, hc, hcb⟩ : ∃ c, ckContent st.env q' = some c ∧ (c = .bot ∨ c = .proof) := by
    rcases hq' with h | h
    · exact ⟨_, h, .inl rfl⟩
    · exact ⟨_, h, .inr rfl⟩
  obtain ⟨pos', hck', hf'⟩ := Option.bind_eq_some_iff.mp hc
  have hpp : pos' = pos := by
    have := rel_resolve_ck K ρ φ st s₁ π q pos' hs (by rw [← hpre.1]; exact hck')
    rw [hres₁] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1.symm
  subst hpp
  have hgr' : GrainOk K.D K.Γ (scopeOf s₁) q' := grain_prefix hgr₁ hpre.1 hpre.2
  have hpt : ¬ IsTemp pos' := by
    rcases pos' with ⟨f, i⟩ | ⟨f, i⟩
    · simp [IsTemp]
    · unfold ckVarPos at hck'; split at hck' <;> cases hck'
  -- `⋆` at the prefix: excluded, the place at or below it is a copy or the join derefs a proof
  -- (`not_below_proof`)
  rcases hcb with rfl | rfl
  rotate_left
  · exact (not_below_proof K ρ φ st s₁ π q q' hg hctx hs hgr₁ hcp₁ hpre.1 hpre.2 hc).elim
  -- `⊥` at the prefix: nothing is lent comparable with it (`clear_of_bot`)
  have hclr : ∀ l, liveLoan st.env l = true → ∀ x ∈ Env.sitesOf st.env l, x.pos = pos' →
      dataHit q'.steps.2 x.path = false := clear_of_bot hg.2.2.1 hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hf'
  have hun := unreached_of_clear K ρ φ hs pos' (dataHit q'.steps.2) hclr
  have hlp : accessLentPrefix pos' q.steps.2 s₁ = s₁ := by
    simp [accessLentPrefix, lentPrefix_none_of_unreached hpre.2 hun]
  have hacc : s₁.access pos' (dataHit q.steps.2) = s₁ := by
    refine SState.access_of_unreached _ _ _ fun y hy => ?_
    have h0 := hun y hy
    unfold SState.reached at h0 ⊢
    rw [List.any_eq_false] at h0 ⊢
    intro x hx hxr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hxr
    exact h0 x hx (by simp [hxr.1, dataHit_of_prefix hpre.2 hxr.2])
  -- a root holding `⊥` is no holder
  have hnb' : q'.steps.2 = [] → s₁.shape pos' = none := by
    intro he
    have hv0 := hf'
    rw [he] at hv0; simp only [Value.follow, Option.some.injEq] at hv0
    cases hsp : s₁.shape pos' with
    | none => rfl
    | some l' =>
      obtain ⟨l, hl, -⟩ := hs.sim.2.2.1 pos' l' hpt hsp
      have hl' : Env.shape st.env pos' = some l := hl
      rw [shape_eq_shapeOf, hv0] at hl'
      simp [shapeOf] at hl'
  obtain ⟨rest, hrest⟩ := hpre.2
  have hnb : q.steps.2 = [] → s₁.shape pos' = none := fun he =>
    hnb' (List.append_eq_nil_iff.mp (hrest.trans he)).1
  -- the reference reads `moved` at the prefix (the checker's `⊥` there, `followMean`)
  have hgrT : GrainOk K.D K.Γ (DecideScope.topReadings st) q' := by rw [← rel_scopeOf K ρ φ hs]; exact hgr'
  have hval : s₁.valAt pos' (s₁.typedFuture φ) =
      Env.mean K.dm K.M K.Γ ρ (fun l => s₁.typedFuture φ (π l)) st.env pos' :=
    (hs.sim.1 _ ⟨relF_typedFuture φ s₁, hs.typedFuture_typed φ⟩ pos' hpt).symm
  obtain ⟨x, T₁, hT, hx⟩ := followMean K ρ hctx.shapes hg (fun l => s₁.typedFuture φ (π l)) pos' q' hgrT hck'
    .bot hc (s₁.tyAt pos')
  have hxm : x = .moved := by
    rcases hx with ⟨-, h⟩ | ⟨H, rfl⟩
    · cases h
    · simp [Value.mean]
  rw [← hval, hxm] at hT
  unfold joinDropOne
  rw [hres₁]
  dsimp only
  rw [hlp]
  unfold dropAt
  split
  · next l h1 h2 => rw [hnb h1] at h2; cases h2
  · dsimp only
    rw [hacc]
    simp only [hcp₁, Bool.false_eq_true, if_false]
    by_cases hd : ∀ x ∈ rest, x = .deref
    · -- through `*`s only: the write at the place is the write at the prefix, `moved` over `moved`
      rw [← hrest]
      simp only [sem_updAt_append_derefs K.dm K.Γ _ rest hd]
      split
      · exact hs
      · have hself := updAt_bot_self q'.steps.2 _ hf'
        obtain ⟨f, i, hposfi, hpb, hsp, hroot, hplain, hnat⟩ :=
          botWrite_hyps K ρ φ st s₁ π q' pos' _ hg hctx.shapes hs hck' hgr' hnb' hself
        subst hposfi
        have hrel := botWrite_rel K ρ φ st s₁ π f i q'.steps.2 _ hs hg.2.2.1 hpb hsp hself hroot
          (fun l hl x hx hxp => hclr l hl x hx hxp) hplain hnat
        rw [setAtE_self_bind st.env f i hpb] at hrel
        exact hrel
    · -- through the moved prefix by a field step: the write cannot be made, nothing is done
      obtain ⟨y, hy, hyd⟩ : ∃ y ∈ rest, y ≠ .deref :=
        Classical.byContradiction fun hne => hd fun y hy => Classical.byContradiction fun h => hne ⟨y, hy, h⟩
      have hnone := Slice.updAt_append_none K.dm K.Γ (fun _ => Sem.moved) q'.steps.2 _ _ _ T₁ rest hT
        (Slice.updAt_moved_none K.dm K.Γ (fun _ => Sem.moved) rest T₁ ⟨y, hy, hyd⟩)
      rw [← hrest, hnone]
      exact hs

/-- **`dropOne_step`, assembled** (the drop of one place, D84): `movedPlace` in the simulation form
(`movedPlace_step`), then where the place exists the drop of an existing place (`dropOne_exists`)
from the reference state after the re-rooting, and where it re-rooted to a prefix holding `⊥` or
`⋆` nothing on either side (`joinDropOne_noop`). -/
theorem dropOne_step_asm (fuel : Nat) (ih : StepsIHBelow fuel) :
    dropOne_step_stmt K ρ φ (fuel + 1) := by
  intro st st' q s π hg hctx hs hgrain hcopy hD bh h
  obtain ⟨q', st₁, b₁, hmp, hdj⟩ := Runs.bind_inv h
  have hmp' := hmp
  rw [movedPlace_succ_eq] at hmp'
  obtain ⟨o, st₀, b₀, hc, -⟩ := Runs.bind_inv hmp'
  obtain ⟨-, pos, hck, -⟩ := runs_content?_inv hc
  have hpos := rel_resolve_ck K ρ φ st s π q pos hs hck
  obtain ⟨ρ₁, Δ₁, s₁, hsz₁, hag₁, hs₁or, hctx₁, hrel₁, hg₁, hout⟩ :=
    movedPlace_step K ρ φ fuel ih st st₁ q q' pos s π hg hctx hs hpos hgrain
      (hD.of_rest (grows_dropAtJoin _ _) hdj) bh hmp
  rcases hout with ⟨hqq, w, hw⟩ | ⟨hroot, hpre, hbt⟩
  · subst q'
    unfold ckContent at hw
    obtain ⟨pos', hck', hw'⟩ := Option.bind_eq_some_iff.mp hw
    have hgr₁ : GrainOk K.D K.Γ (scopeOf s₁) q := by rw [scopeOf_alp hs₁or]; exact hgrain
    have hcp₁ : K.D.copy (K.D.placeDecl (scopeOf s₁) q) = false := by
      rw [scopeOf_alp hs₁or]; exact hcopy
    obtain ⟨ρ₂, Δ₂, E₂⟩ := dropOne_exists { K with Δ := Δ₁ } ρ₁ φ fuel ih st₁ st' q s₁ π hg₁ hctx₁ hrel₁ hgr₁ hcp₁
      pos' w hck' hw' hD b₁ hdj
    have hrel₂ := E₂.rel
    rw [joinDropOne_alp { K with Δ := Δ₁ } φ hpos (alp_idem pos q.steps.2 s) hs₁or] at hrel₂
    exact ⟨ρ₂, Δ₂, Nat.le_trans hsz₁ E₂.size,
      fun σ hσ => ⟨((E₂.agree σ (Nat.lt_of_lt_of_le hσ hsz₁)).1).trans (hag₁ σ hσ).1,
        ((E₂.agree σ (Nat.lt_of_lt_of_le hσ hsz₁)).2).trans (hag₁ σ hσ).2⟩, E₂.ctx, hrel₂, E₂.good⟩
  · have hj := joinDropOne_noop { K with Δ := Δ₁ } ρ₁ φ st₁ s s₁ π q q' pos hg₁ hctx₁ hrel₁ hs₁or hpos
      hgrain hcopy ⟨hroot, hpre⟩ hbt
    obtain ⟨pos', hck', hcases⟩ := runs_dropAtJoin_inv hdj
    have hv : (valAt st₁.env pos').follow q'.steps.2 = some .bot ∨ (valAt st₁.env pos').follow q'.steps.2 = some .proof := by
      unfold ckContent at hbt; rw [hck'] at hbt; simpa using hbt
    -- the re-rooted place does not hold `⋆`: it is a prefix of `q`, which is at the join's grain
    -- and not a copy (`not_below_proof`). Since main's D102 the checker's drop sends a place's own
    -- `⋆` to the copy decision, so this is what excludes the copy and data cases there.
    have hvb : (valAt st₁.env pos').follow q'.steps.2 = some .bot := by
      rcases hv with e | e
      · exact e
      · exfalso
        refine not_below_proof { K with Δ := Δ₁ } ρ₁ φ st₁ s₁ π q q' hg₁ hctx₁ hrel₁
          (by rw [scopeOf_alp hs₁or]; exact hgrain) (by rw [scopeOf_alp hs₁or]; exact hcopy) hroot hpre ?_
        unfold ckContent; rw [hck']; simpa using e
    have hst' : st' = st₁ := by
      rcases hcases with ⟨-, h⟩ | ⟨l, w, hbw, -⟩ | ⟨v, hv', hb, -, -⟩ | ⟨v, hv', -, hb, -, -⟩
      · exact h
      · rw [hvb] at hbw; cases hbw
      · rw [hvb] at hv'; cases hv'; exact absurd rfl hb
      · rw [hvb] at hv'; cases hv'; exact absurd rfl hb
    subst hst'
    exact ⟨ρ₁, Δ₁, hsz₁, hag₁, hctx₁, hj, hg₁⟩

end

end Ochr.Meaning.Steps
