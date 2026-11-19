import Ochr.Meaning.Steps.JoinDropLib
import Ochr.Meaning.BotWrite
import Ochr.Meaning.SitesWrite
import Ochr.Meaning.RelendComm

/-!
# The drop of one place at the join: what `dropOne_step` rests on (docs/31 D30, D31; task C)

`dropOne_step` (`Steps/Match.lean`) is the checker's `movedPlace` then `dropAtJoin` against the
reference's `joinDropOne` (the shortest lent prefix accessed whole, then `dropAt`). Its obligations
are stated here, each a named Lean statement; the open ones are `sorry`'d, with what was tried. In
the order the team lead set (model risk first):

1. L2, writing `⊥` at a path commutes with the meaning: PROVED for a value that records its
   parameters and holds no sealed program (`mean_updAt_bot`, `BotWrite.lean`); open for a sealed
   sibling (`mean_updAt_bot_sealed`). Attacking it found D31 (the reference decoded data by its
   carrier), fixed; it rests on (WF13), a new clause of `Good`.
2. L3, the write keeps the relation (`botWrite_step`), from L2, (WF13) through `dataOn_of_wf13`,
   and the access having ended every borrow lent at, over or under the place (`access_clears`).
3. The commutation of ends on sites: PROVED (`relend_comm`, `RelendComm.lean`), when every site
   at either holder is inside its content and the two are not lent at each other's holders; it is
   used inside the [Access] statement, an induction-hypothesis field.
4. The checker's place and the reference's: `rel_resolve` (through `Rel.skel`).
5. `refine` and `generalizeNeutral` in the simulation form with an extended context
   (`refine_sim`, `generalizeNeutral_sim`).
6. `movedPlace`'s branches, last: the place exists (`movedPlace_exists`, proved), the lent prefix
   absorbed by the access at an instance ((WF12), `lentPrefix_absorbed`), a filled parent accessed
   whole (`movedPlace_fill`), an unknown of a one-constructor type (`movedPlace_eta`), a sealed
   program of one (`movedPlace_sealed`), and the other exits (`movedPlace_exit`).
Smaller: the copy decision (`copyRead_aligned`), what the checker's content and the reference's
`Sem.follow` say of a missing, moved or proof place (`content_follow`), `logEffect` changes nothing
the relation reads (`logEffect_rel`).
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

/-- A run of `x >>= g` is a run of `x`, then a run of `g` at its result. -/
theorem Runs.bind_inv {α β : Type} {x : M α} {g : α → M β} {st st' : MState} {b : Nat} {y : β}
    (h : Runs (x >>= g) st b y st') : ∃ a st₁ b₁, Runs x st b a st₁ ∧ Runs (g a) st₁ b₁ y st' := by
  obtain ⟨L, left, log, h⟩ := h
  rw [runMachineL_bind] at h
  rcases e : runMachineL x st b L with ⟨o, b₁, L₁⟩
  rw [e] at h
  rcases o with ⟨a, st₁⟩ | f | m
  · exact ⟨a, st₁, b₁, ⟨L, b₁, L₁, e⟩, ⟨L₁, left, log, h⟩⟩
  · cases h
  · cases h

/-- The checker's position of de Bruijn variable `i` (`Machine.varPos`, as a function). -/
def ckVarPos (env : Env) (i : Nat) : Option Pos :=
  if i < env[env.size - 1]!.binds.size then some (.bind (env.size - 1) (env[env.size - 1]!.binds.size - 1 - i))
  else none

theorem runs_varPos_inv {i : Nat} {st st' : MState} {b : Nat} {pos : Pos}
    (h : Runs (Ochr.varPos i) st b pos st') : st' = st ∧ ckVarPos st.env i = some pos := by
  obtain ⟨L, left, log, h⟩ := h
  simp only [Ochr.varPos, Ochr.topIdx, runMachineL_bind, runMachineL_get, runMachineL_pure] at h
  unfold ckVarPos
  split at h
  · rename_i hi
    simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    simp [hi]
  · simp [runMachineL_err] at h

/-- **The checker's write at a place**: at the variable's position, the value written at the path. -/
theorem runs_setPlace_inv {q : Place} {new : Value} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.setPlace q new) st b () st') :
    ∃ pos v', ckVarPos st.env q.steps.1 = some pos ∧ (valAt st.env pos).updAt (fun _ => new) q.steps.2 = some v' ∧
      st' = { st with env := Env.setAtE st.env pos v' } := by
  unfold Ochr.setPlace at h
  obtain ⟨pos, st₁, b₁, hv, h⟩ := Runs.bind_inv h
  obtain ⟨hst, hpos⟩ := runs_varPos_inv hv
  rw [hst] at h
  obtain ⟨v, st₂, b₂, hg, h⟩ := Runs.bind_inv h
  have hv2 : st₂ = st ∧ v = valAt st.env pos := by
    obtain ⟨L, left, log, hg⟩ := hg
    cases pos <;> simp only [Ochr.getAt, runMachineL_bind, runMachineL_get, runMachineL_pure, Prod.mk.injEq,
      Outcome.ok.injEq] at hg <;> exact ⟨hg.1.2.symm, by rw [← hg.1.1]; rfl⟩
  obtain ⟨hst2, hvv⟩ := hv2
  rw [hst2, hvv] at h
  split at h
  · rename_i v' hv'
    obtain ⟨L, left, log, h⟩ := h
    refine ⟨pos, v', hpos, hv', ?_⟩
    cases pos <;> simp only [Ochr.setAt, Ochr.modifyFrame, runMachineL_modify, Prod.mk.injEq,
      Outcome.ok.injEq] at h <;> exact h.1.2.symm
  · obtain ⟨_, _, _, _, h⟩ := Runs.bind_inv h
    obtain ⟨L, left, log, h⟩ := h
    simp [runMachineL_err] at h

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The frames of related states have the same numbers of bindings (`Rel.skel`). -/
theorem rel_frames {st : MState} {s : SState} {π : Nat → Nat} (hs : Rel K ρ φ π st s) :
    s.env.length = st.env.size ∧
      ∀ f : Nat, (s.env[f]?.map fun fr : SFrame => fr.binds.length) = (st.env[f]?.map fun fr : Frame => fr.binds.size) := by
  have hk := hs.skel
  have hl := congrArg List.length hk
  simp only [List.length_map] at hl
  have hlen : (SM' K ρ st).env.length = st.env.size := by simp [SM', MState.sstate]
  refine ⟨by omega, fun f => ?_⟩
  have hf := congrArg (fun l => (l[f]?).map List.length) hk
  simp only [List.getElem?_map, Option.map_map] at hf
  have e1 : ((SM' K ρ st).env[f]?.map fun fr : SFrame => fr.binds.length) = (st.env[f]?.map fun fr : Frame => fr.binds.size) := by
    simp only [SM', MState.sstate, List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Array.getElem?_toList]
    rcases st.env[f]? with _ | fr
    · rfl
    · simp [Function.comp_def]
  rw [← e1]
  have := hf.symm
  simpa [Function.comp_def] using this

/-- **(4) The checker's place is the reference's.** At related states a variable's position in the
checker (`varPos`, the top frame's bindings counted from the top) is the reference's (`resolve`):
the two have the same frames and bindings (`Rel.skel`). -/
theorem rel_resolve (st st₁ : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos) (b : Nat)
    (hs : Rel K ρ φ π st s) (h : Runs (Ochr.varPos q.steps.1) st b pos st₁) :
    st₁ = st ∧ resolve s q = some (pos, q.steps.2) := by
  obtain ⟨hst, hpos⟩ := runs_varPos_inv h
  refine ⟨hst, ?_⟩
  obtain ⟨hlen, hfr⟩ := rel_frames K ρ φ hs
  unfold ckVarPos at hpos
  split at hpos
  · rename_i hi
    simp only [Option.some.injEq] at hpos
    subst hpos
    have hne : st.env.size ≠ 0 := by
      intro h0
      have hd : st.env[st.env.size - 1]! = (default : Frame) := by
        simp [h0]
      rw [hd] at hi
      have : (default : Frame).binds.size = 0 := rfl
      omega
    have htop := hfr (st.env.size - 1)
    rcases e : s.env.getLast? with _ | fr
    · rw [List.getLast?_eq_none_iff] at e; simp [e] at hlen; omega
    · have hfr' : s.env[s.env.length - 1]? = some fr := by
        rw [List.getLast?_eq_getElem?] at e; exact e
      rw [hlen] at hfr'
      rw [hfr'] at htop
      have hsz : fr.binds.length = st.env[st.env.size - 1]!.binds.size := by
        have : st.env[st.env.size - 1]? = some st.env[st.env.size - 1]! := by
          rw [Array.getElem?_eq_getElem (by omega), getElem!_pos st.env (st.env.size - 1) (by omega)]
        rw [this] at htop; simpa using htop
      simp only [resolve, SState.varPos, e, SState.topIdx, hlen, hsz, hi, ↓reduceIte, Option.map_some]
  · cases hpos

/-- **(1') L2 with sealed siblings.** `mean_updAt_bot` for a value some field of which off the path
is a sealed program that is top-hint-free (`Value.topHintFree`: [Close]'s programs, `HintIndep`),
at the run's code meaning (`meanV_hintIndep`). Open: the proof is `mean_updAt_bot`'s with
`meanV_hintIndep` in place of `mean_hintFree`; not yet written. -/
theorem mean_updAt_bot_sealed (H : TyS) (steps : List Step) (v v' : Value)
    (h : Value.updAt (fun _ => .bot) steps v = some v')
    (hb : v.anyAtom (Value.bareCtor K.Γ) = false)
    (hs : v.anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false)
    (hd : DataOn K.dm K.M K.Γ ρ φ H steps v) :
    Sem.updAt K.dm K.Γ H (fun _ => .moved) steps (Value.mean K.dm K.M K.Γ ρ φ H v) =
      some (Value.mean K.dm K.M K.Γ ρ φ H v') := by
  sorry

/-- **(WF13) gives the path's data agreement**, at a path that enters one constructor (marks,
`*` and `S` aside): the value at a binding agrees there with the reference's type of the binding
(`Rel.skel` makes it the checker's hint), at every future. As first stated, along any path where
the earlier fields are whole (`WholeAlong`), it was REFUTED by an accepted program
(`Regress/OpenWriteDep.lean`, `OWK`: an index rewritten whole, then a read into the dependent
field, which the reference decodes at the new index's parameters); deeper paths are D32's question.
Open: not tried. -/
theorem dataOn_of_wf13 (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (ψ : Future) (hone : (q.steps.2.filter fun st => st.key.isSome).length ≤ 1) :
    DataOn K.dm K.M K.Γ ρ ψ (s.tyAt pos) q.steps.2 (valAt st.env pos) := by
  sorry

/-- **The checker's access clears the place**: after `accessPath q; accessInside q`, no live borrow
has a site at, over or under the place (`dataHit`): the path holds no live loan, mark or sealed
program (`firstLiveLoanOnPath` is `none`) and the content none inside (`liveLoansIn` is empty).
Open: not tried yet; a fact about the checker's two loops' exits. -/
theorem access_clears (fuel : Nat) (st st' : MState) (q : Place) (pos : Pos) (b b' : Nat)
    (hpos : Runs (Ochr.varPos q.steps.1) st' b' pos st')
    (h : Runs (do Ochr.accessPath fuel q; Ochr.accessInside fuel q) st b () st') :
    ∀ l, liveLoan st'.env l = true → ∀ x ∈ Env.sitesOf st'.env l, x.pos = pos →
      dataHit q.steps.2 x.path = false := by
  sorry

/-- **(2) L3: the write of `⊥` keeps the relation.** After the access (`access_clears`), the
checker's `setPlace q ⊥` and the reference's write of `moved` at the same path (`dropAt`'s last
clause) give related states: the meanings by L2 at every compared future (`dataOn_of_wf13`), the
holders unchanged (a field, or a root holding no borrow), and every live borrow's sites unchanged
(none is at, over or under the place). `Good` is kept: membership by `MovedOf` (a part moved out of
a member), and every clause survives removing a part. Open: not tried beyond L2. -/
theorem botWrite_step (st st' : MState) (q : Place) (pos : Pos) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s q = some (pos, q.steps.2))
    (hroot : q.steps.2 = [] → Env.shape st.env pos = none)
    (hclear : ∀ l, liveLoan st.env l = true → ∀ x ∈ Env.sitesOf st.env l, x.pos = pos →
      dataHit q.steps.2 x.path = false)
    (hplain : RecPlain K.Γ (valAt st.env pos) ∨
      (valAt st.env pos).anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false)
    (h : Runs (Ochr.setPlace q .bot) st b () st') :
    Rel K ρ φ π st' (s.setAt pos fun φ' =>
      (Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => .moved) q.steps.2 (s.valAt pos φ')).getD .err) ∧
    Good K.dm K.M K.Γ ρ st' := by
  sorry

/-- **(5) `refine` in the simulation form.** Under an assignment that already makes the
refinement true (`ρ σ` is the meaning of `r`, read at `σ`'s type; the new unknowns of `r` given
their values), the checker's substitution of `r` for `σ` keeps the relation with the same
reference state: the reference never refines, and every position means the same. Open: the
old order form (`refine_step_stmt`, Below) is the template; not restated in full yet. -/
theorem refine_sim (fuel : Nat) (st st' : MState) (σ : Nat) (r : Value) (s : SState) (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hσ : ρ σ = meanV K ρ φ (.plain (MState.absTyM K.dm K.M K.Γ ρ st σ)) r)
    (h : Runs (Ochr.refine fuel σ r) st b () st') :
    Rel K ρ φ π st' s ∧ Good K.dm K.M K.Γ ρ st' := by
  sorry

/-- **(5) `generalizeNeutral` in the simulation form, with an extended context.** The sealed
program `n` at `p` becomes a fresh unknown `σ` with the record `n := σ`; under the assignment
extended by `σ := ⟦n⟧` (read at `σ`'s type) and `Δ` by `σ`'s type, the states stay related to the
same reference state. Open: the old `Exact` form (`generalizeNeutral_step_stmt`) is the template. -/
theorem generalizeNeutral_sim (fuel : Nat) (st st' : MState) (p : Place) (n : Value) (σ : Nat) (s : SState)
    (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.generalizeNeutral fuel p n) st b σ st') :
    let ρ' := ρ.ext σ (meanV K ρ φ (.plain (MState.absTyM K.dm K.M K.Γ ρ st' σ)) n)
    ∃ Δ' : Nat → TyS, (∀ τ, τ < st.absTy.size → Δ' τ = K.Δ τ) ∧ CtxOk { K with Δ := Δ' } ρ' st' ∧
      Rel { K with Δ := Δ' } ρ' φ π st' s ∧ Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' := by
  sorry

/-- **(6) The place exists**: `movedPlace` returns it and changes nothing. Open: monad plumbing
(`content?`'s run is `varPos` and a pure `follow`); not written. -/
theorem movedPlace_exists (fuel : Nat) (st st₁ : MState) (q q' : Place) (pos : Pos) (w : Value) (b b' : Nat)
    (hpos : Runs (Ochr.varPos q.steps.1) st b' pos st) (hw : (valAt st.env pos).follow q.steps.2 = some w)
    (h : Runs (Ochr.movedPlace (fuel + 1) q) st b q' st₁) : q' = q ∧ st₁ = st := by
  sorry

/-- **(6) The lent prefix, absorbed at an instance.** Where the place exists under a fill (a mark,
transparent to the checker's path), the checker accesses the path to the place only, the
reference first the shortest lent prefix whole; by (WF12) every borrow the prefix access ends is
one the place's access ends, and by `relend_comm` the order does not matter. Open: not tried. -/
theorem lentPrefix_absorbed (st st' : MState) (s : SState) (π : Nat → Nat) (pos : Pos) (steps : List Step)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π st' ((accessLentPrefix pos steps s).access pos (dataHit steps)) ↔
      Rel K ρ φ π st' (s.access pos (dataHit steps)) := by
  sorry

/-- **(6) No lent prefix where the drop does nothing.** Where the checker's place is `⊥` or `⋆`
(its drop does nothing), no live borrow is lent at a strict prefix of it, so the reference's
prefix access does nothing either: [Borrow] rejects a partly moved place, and a move under a fill
reaches the fill first and ends it. A fact read off the checker, to be a clause beside (WF12).
Open: not tried. -/
theorem lentPrefix_none_of_noop (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hnoop : (valAt st.env pos).follow q.steps.2 = some .bot ∨ (valAt st.env pos).follow q.steps.2 = some .proof) :
    lentPrefix s pos q.steps.2 = none := by
  sorry

/-- **(6) A filled parent accessed whole.** Where the place does not exist because a strict prefix
holds a fill over a live borrow (a sealed program over its hole: the generic call), `movedPlace`
accesses that prefix whole (`accessPath`, `accessInside`) and re-roots; the reference accesses the
shortest lent prefix whole. They end the same borrows ((WF12): the fill is the shortest lent prefix's
or above it), and afterwards the place exists or is a no-op on both sides. Open: not tried. -/
theorem movedPlace_fill (fuel : Nat) (st st₁ : MState) (q q' : Place) (pos : Pos) (s : SState) (π : Nat → Nat)
    (b : Nat) (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s q = some (pos, q.steps.2)) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hnone : (valAt st.env pos).follow q.steps.2 = none)
    (h : Runs (Ochr.movedPlace (fuel + 1) q) st b q' st₁) :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      CtxOk { K with Δ := Δ' } ρ' st₁ ∧ Rel { K with Δ := Δ' } ρ' φ π st₁ (accessLentPrefix pos q.steps.2 s) ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st₁ ∧
      (q' = q ∨ ((valAt st₁.env pos).follow q'.steps.2 = some .bot ∨ (valAt st₁.env pos).follow q'.steps.2 = some .proof)) := by
  sorry

/-- **(6) An unknown of a one-constructor type, η-refined** (D68): where a strict prefix `p` of the
place holds an unknown `σ` (and no fill is above it), `movedPlace` η-refines `σ` (`ctorRefinement`
creates the field unknowns, or `etaRefs` gives the recorded ones; `refine` substitutes) and the
place then exists. Under `ρ` extended by the fields of `ρ σ` (decoded by its type's name, D31) and
`Δ` by their types, the states stay related to the same reference state (`refine_sim`), which never
refines. `GrainOk` must give that `σ`'s type is the declared one-constructor type (the coupling with
`absType`). Open: not tried. -/
theorem movedPlace_eta (fuel : Nat) (st st₁ : MState) (q q' p : Place) (pos : Pos) (σ : Nat) (s : SState)
    (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s q = some (pos, q.steps.2)) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hpre : p.steps.2 <+: q.steps.2) (hσ : (valAt st.env pos).follow p.steps.2 = some (.abs σ))
    (h : Runs (Ochr.movedPlace (fuel + 1) q) st b q' st₁) :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ τ, τ < st.absTy.size → ρ' τ = ρ τ ∧ Δ' τ = K.Δ τ) ∧
      CtxOk { K with Δ := Δ' } ρ' st₁ ∧ Rel { K with Δ := Δ' } ρ' φ π st₁ s ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st₁ ∧ q' = q := by
  sorry

/-- **(6) A sealed program of a one-constructor type, generalised then η-refined** (D84): where a
strict prefix holds a sealed program that is not a fill over a live borrow, `movedPlace`
generalises it (`generalizeNeutral`, or `substEnv` of the recorded unknown) and η-refines the
unknown (`movedPlace_eta`); the reference reads the program's meaning directly. Under the
extended context the states stay related to the same reference state (`generalizeNeutral_sim`).
`GrainOk` must give that the prefix's declared type has one constructor (`placeType?`). Open: not
tried. -/
theorem movedPlace_sealed (fuel : Nat) (st st₁ : MState) (q q' p : Place) (pos : Pos) (t : Term) (s : SState)
    (π : Nat → Nat) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s q = some (pos, q.steps.2)) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hpre : p.steps.2 <+: q.steps.2) (ht : (valAt st.env pos).follow p.steps.2 = some (.sealed t))
    (hnofill : fillHoles st.env (.sealed t) = [])
    (h : Runs (Ochr.movedPlace (fuel + 1) q) st b q' st₁) :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ τ, τ < st.absTy.size → ρ' τ = ρ τ ∧ Δ' τ = K.Δ τ) ∧
      CtxOk { K with Δ := Δ' } ρ' st₁ ∧ Rel { K with Δ := Δ' } ρ' φ π st₁ s ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st₁ ∧ q' = q := by
  sorry

/-- **(6) The other exits of `movedPlace`**: a prefix that is `⊥`, `⋆`, or otherwise has no field
(not a one-constructor unknown or sealed program, excluded by `GrainOk`'s coupling): the checker
re-roots to it and its drop does nothing; the reference's `Sem.follow` fails or reads `moved` or
`proof`, and it does nothing either. Open: not tried. -/
theorem movedPlace_exit (st : MState) (s : SState) (π : Nat → Nat) (q p : Place) (pos : Pos)
    (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hp : (valAt st.env pos).follow p.steps.2 = some .bot ∨ (valAt st.env pos).follow p.steps.2 = some .proof)
    (hpre : p.steps.2 <+: q.steps.2) :
    Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = none ∨
      (∃ T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = some (.moved, T)) ∨
      (∃ T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = some (.proof, T)) := by
  sorry

/-- **What the checker's content and the reference's `follow` say of the dropped place**, after the
access: missing, `⊥`, `⋆` and a borrow on one side are the same on the other (L4: a proof in Ω is
`⋆`; the relation's readings at the closed future). Open: not tried. -/
theorem content_follow (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2)) :
    ((valAt st.env pos).follow q.steps.2 = some .bot ↔
      ∃ T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = some (.moved, T)) ∧
    ((valAt st.env pos).follow q.steps.2 = some .proof ↔
      ∃ T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = some (.proof, T)) ∧
    ((valAt st.env pos).follow q.steps.2 = none ↔
      Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = none) := by
  sorry

/-- **The copy decision is aligned**: the checker's `copyRead` is the reference's declared reading
of the place (the decisions are the checker's `Decide`, `CtxOk`). Open: not tried. -/
theorem copyRead_aligned (fuel : Nat) (st st₁ : MState) (s : SState) (π : Nat → Nat) (q : Place) (c : Bool) (b : Nat)
    (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s) (h : Runs (Ochr.copyRead fuel q) st b c st₁) :
    st₁ = st ∧ c = K.D.copy (K.D.placeDecl (scopeOf s) q) := by
  sorry

/-- **`logEffect` changes nothing the relation or `Good` reads** (it writes `placeLog` only).
Open: not tried. -/
theorem logEffect_rel (st st₁ : MState) (s : SState) (π : Nat → Nat) (q : Place) (k : String) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (h : Runs (Ochr.logEffect q k) st b () st₁) :
    Rel K ρ φ π st₁ s ∧ Good K.dm K.M K.Γ ρ st₁ := by
  sorry

end

end Ochr.Meaning.Steps
