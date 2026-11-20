import Ochr.Meaning.Steps.DropOneAsm

/-!
# `movedPlace` in the simulation form, and the drop of a place that does not exist (D84; task C)

`Machine.movedPlace` re-roots a place the join drops when it does not exist in the checker's state:
it re-roots the parent first (recursively), then accesses a filled parent whole, η-refines an
unknown of a one-constructor type, or generalises a sealed program of one, and asks again; any
other parent is returned (it holds `⊥` or `⋆`, and its drop does nothing). The reference never
re-roots: its state holds meanings, where the place exists, and it accesses the shortest lent
prefix whole before the drop (`accessLentPrefix`).

`movedPlace_step` proves the induction hypothesis's field `movedPlace_step_stmt` at `fuel + 1`
from the hypothesis at `fuel` (whose `movedPlace_step` covers the recursive calls), following the
checker's code branch by branch; each branch's semantic content is a named obligation below,
`sorry`'d where open. The assembly of `dropOne_step` is here, on top of it.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

/-- A place's parent (`Machine.movedPlace`'s local `parent`). -/
def parentOf : Place → Option Place
  | .deref p | .proj _ p | .field _ p => some p
  | .var _ => none

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
        let r ← match (← get).etaRefs.lookup σ with
          | some r => pure r
          | none => do
            let r ← Ochr.ctorRefinement fuel d ps 0
            modify fun s => { s with etaRefs := (σ, r) :: s.etaRefs }
            pure r
        Ochr.refine fuel σ r
        Ochr.movedPlace fuel q
      else pure p
    | _ => pure p
  | n@(.sealed _) =>
    match ← Ochr.placeType? fuel p with
    | some (.tInd tn _) =>
      if (← Ochr.lookupInd tn).ctors.length == 1 then
        match ← Ochr.recordedNeutral n with
        | some r => Ochr.substEnv fuel n r true
        | none => discard (Ochr.generalizeNeutral fuel p n)
        Ochr.movedPlace fuel q
      else pure p
    | _ => pure p
  | _ => pure p

theorem movedPlace_succ_eq (fuel : Nat) (q : Place) :
    Ochr.movedPlace (fuel + 1) q = (do
      if (← Ochr.content? q).isSome then return q
      match parentOf q with
      | some p => mpTail fuel q p
      | none => pure q) := by
  rw [Ochr.movedPlace]
  cases q <;> rfl

/-! ## Small inversions -/

theorem runs_get_inv {st st' x : MState} {b : Nat} (h : Runs (get : M MState) st b x st') : x = st ∧ st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_get, Prod.mk.injEq, Outcome.ok.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm⟩

theorem runs_pure_inv {α : Type} {a a' : α} {st st' : MState} {b : Nat} (h : Runs (pure a : M α) st b a' st') :
    a' = a ∧ st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm⟩

theorem runs_err_false {α : Type} {m : String} {a : α} {st st' : MState} {b : Nat}
    (h : Runs (err m : M α) st b a st') : False := by
  obtain ⟨L, left, log, h⟩ := h
  simp [runMachineL_err] at h

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

theorem runs_lookupInd_inv {n : String} {st st' : MState} {b : Nat} {d : IndDecl}
    (h : Runs (Ochr.lookupInd n) st b d st') : st' = st ∧ st.inds.find? (·.name == n) = some d := by
  unfold Ochr.lookupInd at h
  obtain ⟨x, st₁, b₁, hg, h2⟩ := Runs.bind_inv h
  obtain ⟨rfl, rfl⟩ := runs_get_inv hg
  split at h2
  · rename_i d' hd
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h2
    exact ⟨rfl, hd⟩
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

/-- `recordedNeutral` reads the records and changes nothing. -/
theorem runs_recordedNeutral_inv {v : Value} {st st' : MState} {b : Nat} {o : Option Value}
    (h : Runs (Ochr.recordedNeutral v) st b o st') : st' = st := by
  unfold Ochr.recordedNeutral at h
  split at h
  · obtain ⟨x, st₁, b₁, hg, h2⟩ := Runs.bind_inv h
    obtain ⟨hx, hst₁⟩ := runs_get_inv hg
    subst x; subst st₁
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

theorem steps_parent {q p : Place} (h : parentOf q = some p) :
    ∃ x, q.steps = (p.steps.1, p.steps.2 ++ [x]) ∧ ((x = .deref) ∨ (∃ i, x = .proj i) ∨ ∃ g, x = .field g) := by
  cases q with
  | var i => simp [parentOf] at h
  | deref p' =>
    simp only [parentOf, Option.some.injEq] at h; subst h
    exact ⟨.deref, by simp only [Place.steps], .inl rfl⟩
  | proj j p' =>
    simp only [parentOf, Option.some.injEq] at h; subst h
    exact ⟨.proj j, by simp only [Place.steps], .inr (.inl ⟨j, rfl⟩)⟩
  | field g p' =>
    simp only [parentOf, Option.some.injEq] at h; subst h
    exact ⟨.field g, by simp only [Place.steps], .inr (.inr ⟨g, rfl⟩)⟩

theorem resolve_parent {s : SState} {q p : Place} {pos : Pos} (hpar : parentOf q = some p)
    (h : resolve s q = some (pos, q.steps.2)) : resolve s p = some (pos, p.steps.2) := by
  obtain ⟨x, hx, -⟩ := steps_parent hpar
  unfold resolve at h ⊢
  rw [hx] at h
  rcases hv : s.varPos p.steps.1 with _ | pos'
  · simp [hv] at h
  · simp only [hv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, trivial⟩

theorem grain_parent {D : Decisions} {Γ : List IndDecl} {sc : List DeclInfo} {q p : Place}
    (hpar : parentOf q = some p) (h : GrainOk D Γ sc q) : GrainOk D Γ sc p := by
  obtain ⟨x, hx, -⟩ := steps_parent hpar
  intro p' ⟨h1, st, rest, hst, h2⟩
  apply h p'
  refine ⟨by rw [h1, hx], st, rest ++ [x], hst, ?_⟩
  rw [hx]; simp [h2]

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

/-- From `st` (related to some reference state under `K`, `ρ`) to `st'`, related to `s'` under an
assignment and a `Δ` extended at the unknowns created, with `Good` and the context kept. -/
structure Ext (π : Nat → Nat) (st st' : MState) (s' : SState) (ρ' : Assignment) (Δ' : Nat → TyS) : Prop where
  size : st.absTy.size ≤ st'.absTy.size
  agree : ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ
  ctx : CtxOk { K with Δ := Δ' } ρ' st'
  rel : Rel { K with Δ := Δ' } ρ' φ π st' s'
  good : Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st'

theorem Ext.refl {π : Nat → Nat} {st : MState} {s : SState} (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hs : Rel K ρ φ π st s) : Ext K ρ φ π st st s ρ K.Δ :=
  ⟨Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, by rw [runCtx_with_self K]; exact hctx, by rw [runCtx_with_self K]; exact hs,
    by rw [runCtx_with_self K]; exact hg⟩

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
theorem Ext.with_rel {π : Nat → Nat} {st st' : MState} {s' s'' : SState} {ρ' : Assignment} {Δ' : Nat → TyS}
    (h : Ext K ρ φ π st st' s' ρ' Δ') (hr : Rel { K with Δ := Δ' } ρ' φ π st' s'') : Ext K ρ φ π st st' s'' ρ' Δ' :=
  ⟨h.size, h.agree, h.ctx, hr, h.good⟩

end

/-! ## The branches' obligations -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **A filled parent accessed whole is the lent prefix accessed whole** (`movedPlace`'s fill
branch against the reference's `accessLentPrefix`). The parent holds a fill over a live borrow, so
its path is lent and the shortest lent prefix is it or above it; a borrow the reference's access of
that prefix ends and the checker's access of the parent (its path and inside) does not would be
lent strictly under a fill and not at or above it, which (WF12) excludes. Open: the argument of
`lentPrefix_absorbed`, with the fill at the parent. -/
theorem fillPrefix_absorbed (st st' : MState) (s : SState) (π : Nat → Nat) (q p : Place) (pos : Pos) (c : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpar : parentOf q = some p)
    (hpos : resolve s q = some (pos, q.steps.2)) (hc : ckContent st.env p = some c)
    (hfill : Ochr.fillHoles st.env c ≠ [])
    (hs' : Rel K ρ φ π st' (s.access pos (dataHit p.steps.2))) :
    Rel K ρ φ π st' (accessLentPrefix pos q.steps.2 s) := by
  sorry

/-- After the checker's access of a place (path and inside), its content holds no live hole
(`accessInside` ends every live loan inside it, and a fill's holes are among them). Open. -/
theorem fillAccess_clears (fuel : Nat) (st st' : MState) (p : Place) (b : Nat) (c : Value)
    (h : Runs (do Ochr.accessPath fuel p; Ochr.accessInside fuel p) st b () st')
    (hc : ckContent st'.env p = some c) : Ochr.fillHoles st'.env c = [] := by
  sorry

/-- The checker's access creates no unknown and forgets none (its ends substitute, and a sealed
program they re-run keeps the types its copy created). Open. -/
theorem access_absTy (fuel : Nat) (st st' : MState) (p : Place) (b : Nat)
    (h : Runs (do Ochr.accessPath fuel p; Ochr.accessInside fuel p) st b () st') :
    st.absTy.size ≤ st'.absTy.size := by
  sorry

/-- **A recorded η-refinement means the unknown** (D68: the same fields in every private copy).
`Good`'s path condition for the record gives `ρ σ = ⟦r⟧` at the unknown's type and the closed
future; the refinement is a constructor of fresh unknowns, which holds no loan and records its
parameters, so it means the same at every future and hint. Open. -/
theorem etaRecorded_sim (st : MState) (σ : Nat) (r : Value) (hg : Good K.dm K.M K.Γ ρ st)
    (hr : st.etaRefs.lookup σ = some r) : ∀ ψ H, ρ σ = meanV K ρ ψ H r := by
  sorry

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
    (h : Runs (Ochr.ctorRefinement fuel d ps 0) st b r st') :
    ∃ ρ' Δ', Ext K ρ φ π st { st' with etaRefs := (σ, r) :: st'.etaRefs } s ρ' Δ' ∧
      ∀ ψ H, ρ' σ = meanV { K with Δ := Δ' } ρ' ψ H r := by
  sorry

/-- **`placeType?` in the simulation form** (its field and parameter types run on private copies:
Ω is the snapshot's, and what the copies keep is assigned by an extension; `placeType_sim` is the
form with the typing of the result). Open. -/
theorem placeTypeQ_sim (fuel : Nat) (st st' : MState) (p : Place) (T? : Option Value) (s : SState)
    (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.placeType? fuel p) st b T? st') :
    ∃ ρ' Δ', Ext K ρ φ π st st' s ρ' Δ' ∧ st'.env = st.env := by
  sorry

/-- **A sealed program this world already generalised is its record's value** (`recordedNeutral`,
then `substEnv`): `Good`'s path condition for the record `n := σ` makes `σ`, refined by the
refinements made since (`expandRefs`), mean `⟦n⟧`, so the substitution changes no meaning (the
substitution lemma, as `substEnv_neutral_sim`). Open. -/
theorem recorded_sim (fuel : Nat) (st st' : MState) (n r : Value) (s : SState) (π : Nat → Nat) (b b' : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hr : Runs (Ochr.recordedNeutral n) st b' (some r) st)
    (h : Runs (Ochr.substEnv fuel n r true) st b () st') : Ext K ρ φ π st st' s ρ K.Δ := by
  sorry

/-- A sealed program in Ω with no live hole holds no loan at all: [End] substitutes a loan
everywhere its borrow ends, so a loan in Ω is live. Not a clause of `Good` yet ((WF2) is about the
loans outside sealed programs); a fact read off the checker. Open. -/
theorem sealed_loanFree (st : MState) (p : Place) (t : Term) (hg : Good K.dm K.M K.Γ ρ st)
    (hp : ckContent st.env p = some (.sealed t)) (hfill : Ochr.fillHoles st.env (.sealed t) = []) :
    ∀ l, (Value.sealed t).hasLoan l = false := by
  sorry

/-- **`movedPlace` of the parent leaves the place missing** when it returns the parent itself: if
the parent existed, nothing changed (`movedPlace_exists'`); if not, it holds a fresh field of a
refinement, an unknown or `⋆` (`fieldsGeneric`; no field is a borrow, (WF8)), which has no field
and no content. Open: needs the typing of a refinement's fields. -/
theorem movedPlace_keeps_missing (fuel : Nat) (st st' : MState) (q p : Place) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hpar : parentOf q = some p) (hq : ckContent st.env q = none)
    (h : Runs (Ochr.movedPlace fuel p) st b p st') (hp : ∃ w, ckContent st'.env p = some w) :
    ckContent st'.env q = none := by
  sorry

end

/-! ## The exits -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **An unknown at the parent has a one-constructor type** (the exit of the unknown branch does
not happen): the place's field step is through a place whose declared type is an inductive with
one constructor (`GrainOk`), and an unknown's type is its place's declared type; through a borrow
step the parent would be an unknown of a borrow type, which no unknown has (a generic borrow is
`borrow_ℓ σ`, `genericValue`). Open: needs both couplings as facts of the state. -/
theorem exit_abs (st : MState) (s : SState) (π : Nat → Nat) (q p : Place) (σ : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpar : parentOf q = some p)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hp : ckContent st.env p = some (.abs σ)) :
    ∃ n ps d, st.absTy[σ]? = some (.tInd n ps) ∧ st.inds.find? (·.name == n) = some d ∧ d.ctors.length = 1 := by
  sorry

/-- **A sealed program at the parent has a one-constructor declared type** (the exit of the sealed
branch does not happen). Through a field step, `GrainOk` gives it (`placeType?` reads the declared
type). Through a borrow step the parent would hold a bare sealed program of a borrow type, which
`GrainOk` does not exclude; but a place of a borrow type holds a borrow (`borrow_k ⌈…⌉`: a call
returning a borrow closes off to one, `closeCall`'s `.ref` kind; a generic borrow is
`borrow_ℓ σ`), `⊥` or a loan, never a bare sealed program: an invariant to state. Open. -/
theorem exit_sealed (fuel : Nat) (st st' : MState) (s : SState) (π : Nat → Nat) (q p : Place) (t : Term)
    (T? : Option Value) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpar : parentOf q = some p)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hp : ckContent st.env p = some (.sealed t))
    (hfill : Ochr.fillHoles st.env (.sealed t) = [])
    (h : Runs (Ochr.placeType? fuel p) st b T? st') :
    ∃ tn args d, T? = some (.tInd tn args) ∧ st'.inds.find? (·.name == tn) = some d ∧ d.ctors.length = 1 := by
  sorry

/-- **Any other parent holds `⊥` or `⋆`** (`movedPlace`'s last exit): the place is missing and its
parent holds no fill, unknown or sealed program, so (by membership at the parent's declared type)
it holds no constructor, number or borrow the step would go into. Open. -/
theorem exit_other (st : MState) (s : SState) (π : Nat → Nat) (q p : Place) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpar : parentOf q = some p)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hp : ckContent st.env p = some v)
    (hq : ckContent st.env q = none) (hfill : Ochr.fillHoles st.env v = [])
    (habs : ∀ σ, v ≠ .abs σ) (hsealed : ∀ t, v ≠ .sealed t) : v = .bot ∨ v = .proof := by
  sorry

/-- After the shortest lent prefix is accessed whole, no strict prefix of the path is lent: the
access ends, to a fixpoint, what is lent at or under that prefix, sites re-rooted by its ends
included (`relend` re-roots a site to one of the ended label's, which is at or under the prefix or
off the path), and nothing above it was lent; an ended label keeps no site, so each label is
ended at most once and the access's rounds (one per live label) reach the fixpoint. Stated under
the relation and `Good`, which the proof may need about the reference's holders; not known to be
false without them. Open. -/
theorem alp_idem (st : MState) (s : SState) (π : Nat → Nat) (pos : Pos) (steps : List Step)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) :
    accessLentPrefix pos steps (accessLentPrefix pos steps s) = accessLentPrefix pos steps s := by
  sorry

/-- **Where the checker re-rooted to a prefix holding `⊥` or `⋆`, the reference's drop does
nothing either**: no live fill is above a moved or proof part (`lentPrefix_none_of_noop`), so the
lent prefix's access does nothing, and the reference's place reads `moved` or `proof` or is
missing (`Sem.follow` through a moved or proof part). Open. -/
theorem joinDropOne_noop (st : MState) (s s₁ : SState) (π : Nat → Nat) (q q' : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s₁) (hs₁ : s₁ = s ∨ s₁ = accessLentPrefix pos q.steps.2 s)
    (hpos : resolve s q = some (pos, q.steps.2)) (hpre : q'.steps.1 = q.steps.1 ∧ q'.steps.2 <+: q.steps.2)
    (hq' : ckContent st.env q' = some .bot ∨ ckContent st.env q' = some .proof) :
    joinDropOne K φ s q = s₁ := by
  sorry

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

/-- **`movedPlace` after the parent is found**, in the simulation form. -/
theorem mpTail_sim (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel)
    (st st' : MState) (q p q' : Place) (pos : Pos) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s q = some (pos, q.steps.2)) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hpar : parentOf q = some p) (hq : ckContent st.env q = none)
    (bh : Nat) (h : Runs (mpTail fuel q p) st bh q' st') :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (s' : SState), (s' = s ∨ s' = accessLentPrefix pos q.steps.2 s) ∧
      Ext K ρ φ π st st' s' ρ' Δ' ∧ MPOut st' q q' := by
  unfold mpTail at h
  obtain ⟨p', st₁, b₁, hmp, h⟩ := Runs.bind_inv h
  obtain ⟨ρ₁, Δ₁, s₁, hsz₁, hag₁, hs₁or, hctx₁, hrel₁, hg₁, hout₁⟩ :=
    (ih K ρ φ).movedPlace_step st st₁ p p' pos s π hg hctx hs (resolve_parent hpar hpos) (grain_parent hpar hgrain) bh hmp
  have hs₁q := alp_parent hpar hs₁or
  have hidem := alp_idem K ρ φ st s π pos q.steps.2 hg hs
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
      obtain ⟨hrel₄, hg₄⟩ := (ih { K with Δ := Δ₁ } ρ₁ φ).access_step st₁ st₄ p pos false s₁ π hg₁ hctx₁ hrel₁ hres₁ b₃ hacc
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hrel₄
      have hrel₄' := fillPrefix_absorbed { K with Δ := Δ₁ } ρ₁ φ st₁ st₄ s₁ π q p pos c hg₁ hrel₁ hpar
        (by rw [resolve_alp hs₁q]; exact hpos) hc hfill' hrel₄
      have hctx₄ := access_ctx { K with Δ := Δ₁ } ρ₁ fuel st₁ st₄ p b₃ hctx₁ hacc
      have hsz₄ := access_absTy fuel st₁ st₄ p b₃ hacc
      have E₂ : Ext { K with Δ := Δ₁ } ρ₁ φ π st₁ st₄ (accessLentPrefix pos q.steps.2 s₁) ρ₁ Δ₁ :=
        ⟨hsz₄, fun _ _ => ⟨rfl, rfl⟩, hctx₄, hrel₄', hg₄⟩
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
        (ih { K with Δ := Δ₁ } ρ₁ φ).movedPlace_step st₄ st' q q' pos (accessLentPrefix pos q.steps.2 s₁) π hg₄ hctx₄
          hrel₄' (by rw [resolve_alp hs₂q]; exact hpos) (by rw [scopeOf_alp hs₂q]; exact hgrain) b₆ h6
      have E₃ : Ext { K with Δ := Δ₁ } ρ₁ φ π st₄ st' s₃ ρ₃ Δ₃ := ⟨hsz₃, hag₃, hctx₃, hrel₃, hg₃⟩
      exact ⟨ρ₃, Δ₃, s₃, alp_again hidem hs₂q hs₃or, (E₁.trans K ρ φ E₂).trans K ρ φ E₃, hout₃⟩
    · -- no fill: the parent's content decides
      rename_i hnf
      have hfill : Ochr.fillHoles st₁.env c = [] := by simpa using hnf
      obtain ⟨c', st₄, b₄, hcont', h4⟩ := Runs.bind_inv h3
      obtain ⟨hst₄, hc'⟩ := runs_content_inv hcont'
      subst st₄
      rw [hc] at hc'
      cases hc'
      have hq₁ : ckContent st₁.env q = none :=
        movedPlace_keeps_missing K ρ fuel st st₁ q p bh hg hpar hq hmp ⟨c, hc⟩
      have hgr₁ : GrainOk K.D K.Γ (scopeOf s₁) q := by rw [scopeOf_alp hs₁q]; exact hgrain
      have hpos₁ : resolve s₁ q = some (pos, q.steps.2) := by rw [resolve_alp hs₁q]; exact hpos
      split at h4
      · -- an unknown: of a one-constructor type, η-refined, then the place asked again
        rename_i σ
        obtain ⟨T, st₅, b₅, habsT, h5⟩ := Runs.bind_inv h4
        obtain ⟨hst₅, hT⟩ := runs_absType_inv habsT
        subst st₅
        obtain ⟨n, ps, d, hTn, hd, h1⟩ := exit_abs { K with Δ := Δ₁ } ρ₁ φ st₁ s₁ π q p σ hg₁ hrel₁ hpar hgr₁ hc
        rw [hTn] at hT
        cases hT
        obtain ⟨d', st₆, b₆, hlk, h6⟩ := Runs.bind_inv h5
        obtain ⟨hst₆, hd'⟩ := runs_lookupInd_inv hlk
        subst st₆
        rw [hd] at hd'
        cases hd'
        simp only [h1, BEq.rfl, ↓reduceIte] at h6
        obtain ⟨x, st₇, b₇, hget, h7⟩ := Runs.bind_inv h6
        obtain ⟨hx, hst₇⟩ := runs_get_inv hget
        subst x; subst st₇
        split at h7
        · -- the recorded refinement
          rename_i r hr
          obtain ⟨r', st₈, b₈, hpr, h8⟩ := Runs.bind_inv h7
          obtain ⟨hrr, hst₈⟩ := runs_pure_inv hpr
          subst r'; subst st₈
          obtain ⟨u, st₉, b₉, hrf, h9⟩ := Runs.bind_inv h8
          have hσ := etaRecorded_sim { K with Δ := Δ₁ } ρ₁ st₁ σ r hg₁ hr
          rcases fuel with _ | f
          · obtain ⟨L, left, log, hrf⟩ := hrf
            simp [Ochr.refine, runMachineL_exhausted] at hrf
          obtain ⟨hs₉, hg₉, hctx₉, hsz₉⟩ := refine_sim' { K with Δ := Δ₁ } ρ₁ φ f st₁ st₉ σ r s₁ π b₈ hg₁ hctx₁ hrel₁ hσ hrf
          have E₂ : Ext { K with Δ := Δ₁ } ρ₁ φ π st₁ st₉ s₁ ρ₁ Δ₁ := ⟨hsz₉, fun _ _ => ⟨rfl, rfl⟩, hctx₉, hs₉, hg₉⟩
          obtain ⟨ρ₃, Δ₃, s₃, hsz₃, hag₃, hs₃or, hctx₃, hrel₃, hg₃, hout₃⟩ :=
            (ih { K with Δ := Δ₁ } ρ₁ φ).movedPlace_step st₉ st' q q' pos s₁ π hg₉ hctx₉ hs₉ hpos₁ hgr₁ b₉ h9
          have E₃ : Ext { K with Δ := Δ₁ } ρ₁ φ π st₉ st' s₃ ρ₃ Δ₃ := ⟨hsz₃, hag₃, hctx₃, hrel₃, hg₃⟩
          exact ⟨ρ₃, Δ₃, s₃, alp_again hidem hs₁q hs₃or, E₁.trans K ρ φ (E₂.trans _ _ φ E₃), hout₃⟩
        · -- a fresh refinement, recorded
          obtain ⟨r, st₈, b₈, hcr, h8⟩ := Runs.bind_inv h7
          obtain ⟨u, st₉, b₉, hmod, h9⟩ := Runs.bind_inv h8
          obtain ⟨L, left, log, hmod⟩ := hmod
          simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at hmod
          obtain ⟨⟨-, hst₉⟩, -⟩ := hmod
          subst st₉
          obtain ⟨r', st₁₀, b₁₀, hpr, h10⟩ := Runs.bind_inv h9
          obtain ⟨hrr, hst₁₀⟩ := runs_pure_inv hpr
          subst r'; subst st₁₀
          obtain ⟨u', st₁₁, b₁₁, hrf, h11⟩ := Runs.bind_inv h10
          obtain ⟨ρ₂, Δ₂, E₂, hσ⟩ := etaFresh_sim { K with Δ := Δ₁ } ρ₁ φ fuel st₁ st₈ p σ n ps d r s₁ π b₇
            hg₁ hctx₁ hrel₁ hc hTn hd h1 hcr
          rcases fuel with _ | f
          · obtain ⟨L, left, log, hrf⟩ := hrf
            simp [Ochr.refine, runMachineL_exhausted] at hrf
          obtain ⟨hs₁₁, hg₁₁, hctx₁₁, hsz₁₁⟩ := refine_sim' { K with Δ := Δ₂ } ρ₂ φ f _ st₁₁ σ r s₁ π b₁₀
            E₂.good E₂.ctx E₂.rel hσ hrf
          have E₃ : Ext { K with Δ := Δ₂ } ρ₂ φ π _ st₁₁ s₁ ρ₂ Δ₂ := ⟨hsz₁₁, fun _ _ => ⟨rfl, rfl⟩, hctx₁₁, hs₁₁, hg₁₁⟩
          obtain ⟨ρ₄, Δ₄, s₄, hsz₄, hag₄, hs₄or, hctx₄, hrel₄, hg₄, hout₄⟩ :=
            (ih { K with Δ := Δ₂ } ρ₂ φ).movedPlace_step st₁₁ st' q q' pos s₁ π hg₁₁ hctx₁₁ hs₁₁ hpos₁ hgr₁ b₁₁ h11
          have E₄ : Ext { K with Δ := Δ₂ } ρ₂ φ π st₁₁ st' s₄ ρ₄ Δ₄ := ⟨hsz₄, hag₄, hctx₄, hrel₄, hg₄⟩
          exact ⟨ρ₄, Δ₄, s₄, alp_again hidem hs₁q hs₄or,
            E₁.trans K ρ φ (E₂.trans _ _ φ (E₃.trans _ _ φ E₄)), hout₄⟩
      · -- a sealed program: of a one-constructor declared type, generalised (or its record), then
        -- the place asked again
        rename_i t
        obtain ⟨T?, st₅, b₅, hpt, h5⟩ := Runs.bind_inv h4
        obtain ⟨tn, args, d, hT?, hd, h1⟩ := exit_sealed { K with Δ := Δ₁ } ρ₁ φ fuel st₁ st₅ s₁ π q p t T? b₄
          hg₁ hrel₁ hpar hgr₁ hc hfill hpt
        obtain ⟨ρ₂, Δ₂, E₂, henv₅⟩ := placeTypeQ_sim { K with Δ := Δ₁ } ρ₁ φ fuel st₁ st₅ p T? s₁ π b₄ hg₁ hctx₁ hrel₁ hpt
        subst T?
        obtain ⟨d', st₆, b₆, hlk, h6⟩ := Runs.bind_inv h5
        obtain ⟨hst₆, hd'⟩ := runs_lookupInd_inv hlk
        subst st₆
        rw [hd] at hd'
        cases hd'
        simp only [h1, BEq.rfl, ↓reduceIte] at h6
        obtain ⟨o, st₇, b₇, hrn, h7⟩ := Runs.bind_inv h6
        have hst₇ := runs_recordedNeutral_inv hrn
        subst st₇
        have hc₅ : ckContent st₅.env p = some (.sealed t) := by rw [henv₅]; exact hc
        split at h7
        · -- generalised before in this world: its record's value
          rename_i r
          obtain ⟨u, st₈, b₈, hsub, h8⟩ := Runs.bind_inv h7
          have E₃ := recorded_sim { K with Δ := Δ₂ } ρ₂ φ fuel st₅ st₈ (.sealed t) r s₁ π b₇ b₆ E₂.good E₂.ctx E₂.rel
            hrn hsub
          obtain ⟨ρ₄, Δ₄, s₄, hsz₄, hag₄, hs₄or, hctx₄, hrel₄, hg₄, hout₄⟩ :=
            (ih { K with Δ := Δ₂ } ρ₂ φ).movedPlace_step st₈ st' q q' pos s₁ π E₃.good E₃.ctx E₃.rel hpos₁ hgr₁ b₈ h8
          have E₄ : Ext { K with Δ := Δ₂ } ρ₂ φ π st₈ st' s₄ ρ₄ Δ₄ := ⟨hsz₄, hag₄, hctx₄, hrel₄, hg₄⟩
          exact ⟨ρ₄, Δ₄, s₄, alp_again hidem hs₁q hs₄or,
            E₁.trans K ρ φ (E₂.trans _ _ φ (E₃.trans _ _ φ E₄)), hout₄⟩
        · -- generalised here (D34)
          obtain ⟨u, st₈, b₈, hdisc, h8⟩ := Runs.bind_inv h7
          obtain ⟨σ, hgen⟩ := runs_discard_inv hdisc
          have hfill₅ : Ochr.fillHoles st₅.env (.sealed t) = [] := by rw [henv₅]; exact hfill
          have hfree := sealed_loanFree { K with Δ := Δ₂ } ρ₂ st₅ p t E₂.good hc₅ hfill₅
          obtain ⟨ρ₃, Δ₃, hag₃, hctx₃, hrel₃, hg₃, hsz₃⟩ := generalizeNeutral_sim { K with Δ := Δ₂ } ρ₂ φ fuel st₅ st₈ p
            (.sealed t) σ s₁ π b₇ E₂.good E₂.ctx E₂.rel hc₅ ⟨t, rfl⟩ hfree hgen
          have E₃ : Ext { K with Δ := Δ₂ } ρ₂ φ π st₅ st₈ s₁ ρ₃ Δ₃ := ⟨hsz₃, hag₃, hctx₃, hrel₃, hg₃⟩
          obtain ⟨ρ₄, Δ₄, s₄, hsz₄, hag₄, hs₄or, hctx₄, hrel₄, hg₄, hout₄⟩ :=
            (ih { K with Δ := Δ₃ } ρ₃ φ).movedPlace_step st₈ st' q q' pos s₁ π hg₃ hctx₃ hrel₃ hpos₁ hgr₁ b₈ h8
          have E₄ : Ext { K with Δ := Δ₃ } ρ₃ φ π st₈ st' s₄ ρ₄ Δ₄ := ⟨hsz₄, hag₄, hctx₄, hrel₄, hg₄⟩
          exact ⟨ρ₄, Δ₄, s₄, alp_again hidem hs₁q hs₄or,
            E₁.trans K ρ φ (E₂.trans _ _ φ (E₃.trans _ _ φ E₄)), hout₄⟩
      · -- any other content: `⊥` or `⋆`, re-rooted to the parent
        rename_i habs hsea
        have hcv := exit_other { K with Δ := Δ₁ } ρ₁ φ st₁ s₁ π q p c hg₁ hrel₁ hpar hgr₁ hc hq₁ hfill
          (fun σ e => habs σ e) (fun t e => hsea t e)
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h4
        refine ⟨ρ₁, Δ₁, s₁, hs₁q, E₁, .inr ⟨hq1.symm, by rw [hq2]; exact List.prefix_append _ _, ?_⟩⟩
        rw [hc]; simpa using hcv
  · -- the parent re-rooted to a prefix holding `⊥` or `⋆`: so does the place
    have hcv : c = .bot ∨ c = .proof := by
      rcases hbt with hb | hb <;> rw [hc] at hb <;> cases hb <;> simp
    have hfill : Ochr.fillHoles st₁.env c = [] := by rcases hcv with rfl | rfl <;> rfl
    simp only [hfill, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h3
    obtain ⟨c', st₄, b₄, hcont', h4⟩ := Runs.bind_inv h3
    obtain ⟨hst₄, hc'⟩ := runs_content_inv hcont'
    subst st₄
    rw [hc] at hc'
    cases hc'
    have hout : MPOut st₁ q p' :=
      .inr ⟨by rw [hroot, hq1], by rw [hq2]; exact hpre.trans (List.prefix_append _ _), by rw [hc]; simpa using hcv⟩
    rcases hcv with rfl | rfl
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h4
      exact ⟨ρ₁, Δ₁, s₁, hs₁q, E₁, hout⟩
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h4
      exact ⟨ρ₁, Δ₁, s₁, hs₁q, E₁, hout⟩

end

/-! ## `movedPlace` and the drop of one place, assembled -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **`movedPlace` in the simulation form** (the induction hypothesis's field at `fuel + 1`): where
the place exists it is returned and nothing changes; otherwise `mpTail_sim`. -/
theorem movedPlace_step (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) :
    movedPlace_step_stmt K ρ φ (fuel + 1) := by
  intro st st' q q' pos s π hg hctx hs hpos hgrain bh h
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
    refine ⟨ρ, K.Δ, s, Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩, .inl rfl, ?_, ?_, ?_, .inl ⟨rfl, w, ?_⟩⟩
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
      obtain ⟨ρ', Δ', s', hs', E, hout⟩ := mpTail_sim K ρ φ fuel ih st st' q p q' pos s π hg hctx hs hpos hgrain hpar hq b₀ h
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

/-- **`dropOne_step`, assembled** (the drop of one place, D84): `movedPlace` in the simulation form
(`movedPlace_step`), then where the place exists the drop of an existing place (`dropOne_exists`)
from the reference state after the re-rooting, and where it re-rooted to a prefix holding `⊥` or
`⋆` nothing on either side (`joinDropOne_noop`). -/
theorem dropOne_step_asm (fuel : Nat) (ih : ∀ K' ρ φ, StepsIH K' ρ φ fuel) :
    dropOne_step_stmt K ρ φ (fuel + 1) := by
  intro st st' q s π hg hctx hs hgrain hcopy bh h
  obtain ⟨q', st₁, b₁, hmp, hdj⟩ := Runs.bind_inv h
  have hmp' := hmp
  rw [movedPlace_succ_eq] at hmp'
  obtain ⟨o, st₀, b₀, hc, -⟩ := Runs.bind_inv hmp'
  obtain ⟨-, pos, hck, -⟩ := runs_content?_inv hc
  have hpos := rel_resolve_ck K ρ φ st s π q pos hs hck
  obtain ⟨ρ₁, Δ₁, s₁, hsz₁, hag₁, hs₁or, hctx₁, hrel₁, hg₁, hout⟩ :=
    movedPlace_step K ρ φ fuel ih st st₁ q q' pos s π hg hctx hs hpos hgrain bh hmp
  rcases hout with ⟨hqq, w, hw⟩ | ⟨hroot, hpre, hbt⟩
  · subst q'
    unfold ckContent at hw
    obtain ⟨pos', hck', hw'⟩ := Option.bind_eq_some_iff.mp hw
    have hgr₁ : GrainOk K.D K.Γ (scopeOf s₁) q := by rw [scopeOf_alp hs₁or]; exact hgrain
    have hcp₁ : K.D.copy (K.D.placeDecl (scopeOf s₁) q) = false := by rw [scopeOf_alp hs₁or]; exact hcopy
    obtain ⟨hrel, hgood⟩ := dropOne_exists { K with Δ := Δ₁ } ρ₁ φ fuel ih st₁ st' q s₁ π hg₁ hctx₁ hrel₁ hgr₁ hcp₁
      pos' w hck' hw' b₁ hdj
    obtain ⟨hctx', hsize⟩ := dropAtJoin_ctx { K with Δ := Δ₁ } ρ₁ fuel st₁ st' q b₁ hctx₁ hdj
    rw [joinDropOne_alp { K with Δ := Δ₁ } φ hpos (alp_idem K ρ φ st s π pos q.steps.2 hg hs) hs₁or] at hrel
    exact ⟨ρ₁, Δ₁, Nat.le_trans hsz₁ hsize, hag₁, hctx', hrel, hgood⟩
  · have hj := joinDropOne_noop { K with Δ := Δ₁ } ρ₁ φ st₁ s s₁ π q q' pos hg₁ hrel₁ hs₁or hpos ⟨hroot, hpre⟩ hbt
    obtain ⟨pos', hck', hcases⟩ := runs_dropAtJoin_inv hdj
    have hv : (valAt st₁.env pos').follow q'.steps.2 = some .bot ∨ (valAt st₁.env pos').follow q'.steps.2 = some .proof := by
      unfold ckContent at hbt; rw [hck'] at hbt; simpa using hbt
    have hst' : st' = st₁ := by
      rcases hcases with ⟨-, h⟩ | ⟨l, w, hbw, -⟩ | ⟨v, hv', hb, hp, -⟩ | ⟨v, hv', -, hb, hp, -⟩
      · exact h
      · rcases hv with e | e <;> rw [e] at hbw <;> cases hbw
      · rcases hv with e | e <;> rw [e] at hv' <;> cases hv'
        · exact absurd rfl hb
        · exact absurd rfl hp
      · rcases hv with e | e <;> rw [e] at hv' <;> cases hv'
        · exact absurd rfl hb
        · exact absurd rfl hp
    subst hst'
    refine ⟨ρ₁, Δ₁, hsz₁, hag₁, hctx₁, ?_, hg₁⟩
    have hj' : joinDropOne K φ s q = s₁ := hj
    rw [hj']; exact hrel₁

end

end Ochr.Meaning.Steps
