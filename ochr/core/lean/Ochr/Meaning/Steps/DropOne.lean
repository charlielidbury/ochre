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
   carrier) and then the partial-move and open-value faults; since D32 a constructor value
   describes itself, and L2 asks nothing of the hint.
2. L3, the write keeps the relation (`botWrite_step`), from L2 and the access having ended every
   borrow lent at, over or under the place (`access_clears`).
3. The commutation of ends on sites: PROVED (`relend_comm`, `RelendComm.lean`), when every site
   at either holder is inside its content and the two are not lent at each other's holders; it is
   used inside the [Access] statement, an induction-hypothesis field.
4. The checker's place and the reference's: `rel_resolve` (through `Rel.skel`).
5. `refine` and `generalizeNeutral` in the simulation form with an extended context
   (`refine_sim`; both are assembled from smaller obligations in `Steps/DropOneAsm.lean`,
   `refine_sim'` and `generalizeNeutral_sim`).
6. `movedPlace`'s branches, last: the place exists (`movedPlace_exists'`, PROVED in `Steps/DropRuns.lean`), the lent prefix
   absorbed by the access at an instance ((WF12), `lentPrefix_absorbed`); the other branches (a
   filled parent accessed whole, an unknown or a sealed program of a one-constructor type refined,
   the exits) are `movedPlace_step`, an induction-hypothesis field proved branch by branch in
   `Steps/MovedPlace.lean`.
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
theorem rel_resolve_ck (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hs : Rel K ρ φ π st s) (hpos : ckVarPos st.env q.steps.1 = some pos) :
    resolve s q = some (pos, q.steps.2) := by
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

/-- **(4) The checker's place is the reference's**, from a run of `varPos`. -/
theorem rel_resolve (st st₁ : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos) (b : Nat)
    (hs : Rel K ρ φ π st s) (h : Runs (Ochr.varPos q.steps.1) st b pos st₁) :
    st₁ = st ∧ resolve s q = some (pos, q.steps.2) := by
  obtain ⟨hst, hpos⟩ := runs_varPos_inv h
  exact ⟨hst, rel_resolve_ck K ρ φ st s π q pos hs hpos⟩

/-- **(1') L2 with sealed siblings.** `mean_updAt_bot` for a value some field of which off the path
is a sealed program that is top-hint-free (`Value.topHintFree`: [Close]'s programs, `HintIndep`),
at the run's code meaning (`meanV_hintIndep`). Open: the proof is `mean_updAt_bot`'s with
`meanV_hintIndep` in place of `mean_hintFree`; not yet written. -/
theorem mean_updAt_bot_sealed (H : TyS) (steps : List Step) (v v' : Value)
    (h : Value.updAt (fun _ => .bot) steps v = some v')
    (hb : v.anyAtom (Value.bareCtor K.Γ) = false)
    (hs : v.anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false)
    (hd : NatAlong K.dm K.M K.Γ ρ φ steps v) :
    Sem.updAt K.dm K.Γ H (fun _ => .moved) steps (Value.mean K.dm K.M K.Γ ρ φ H v) =
      some (Value.mean K.dm K.M K.Γ ρ φ H v') := by
  sorry

/-- **The checker's access clears the place**: after `accessPath q; accessInside q`, no live borrow
has a site at, over or under the place (`dataHit`): the path holds no live loan, mark or sealed
program (`firstLiveLoanOnPath` is `none`) and the content none inside (`liveLoansIn` is empty).
Open: not tried yet; a fact about the checker's two loops' exits. -/
theorem access_clears (fuel : Nat) (st st' : MState) (q : Place) (pos : Pos) (b : Nat)
    (hpos : ckVarPos st.env q.steps.1 = some pos)
    (h : Runs (do Ochr.accessPath fuel q; Ochr.accessInside fuel q) st b () st') :
    ∀ l, liveLoan st'.env l = true → ∀ x ∈ Env.sitesOf st'.env l, x.pos = pos →
      dataHit q.steps.2 x.path = false := by
  sorry

/-- **(2) L3: the write of `⊥` keeps the relation.** After the access (`access_clears`), the
checker's `setPlace q ⊥` and the reference's write of `moved` at the same path (`dropAt`'s last
clause) give related states: the meanings by L2 at every compared future, the
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

/-- **(6) The lent prefix, absorbed at an instance.** Where the place exists under a fill (a mark,
transparent to the checker's path), the checker accesses the path to the place only, the
reference first the shortest lent prefix whole; by (WF12) every borrow the prefix access ends is
one the place's access ends, and by `relend_comm` the order does not matter. Open: not tried. -/
theorem lentPrefix_absorbed (st st' : MState) (s : SState) (π : Nat → Nat) (pos : Pos) (steps : List Step)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π st' ((accessLentPrefix pos steps s).access pos (dataHit steps)) ↔
      Rel K ρ φ π st' (s.access pos (dataHit steps)) := by
  sorry

/-- **(6) No lent prefix above a moved part.** Where the checker's place is `⊥` (its drop does
nothing), no live borrow is lent at a strict prefix of it, so the reference's prefix access does
nothing either: [Borrow] rejects a partly moved place, and a move under a fill reaches the fill
first and ends it. A fact read off the checker; the sweep (`lake exe sweep`) found no violation
(32 suite states with a moved part beside a live fill). Open: not tried.

As first written it also covered a `⋆` part, which the sweep refuted: a place lent whole keeps its
proof field under the mark (`MkC(n, h)` lent by `Get(&c)`, state `c = lent_2 MkC(loan_2, ⋆)`,
19 states). The `⋆` case is `lentPrefix_none_of_proof`, at the places the join drops. -/
theorem lentPrefix_none_of_noop (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hnoop : (valAt st.env pos).follow q.steps.2 = some .bot) :
    lentPrefix s pos q.steps.2 = none := by
  sorry

/-- **(6) No lent prefix above a proof part the join drops.** A place the join drops is not of a
copy type (`hcopy`), and a proposition is one, so the sweep's proof fields under a mark are never
dropped; a non-copy place holds `⋆` only as a data field of a proof. Whether the join can drop
such a field under a live fill is untested. If it can, the checker's two paths end different
borrows: at the generic call the place is missing under the sealed fill and `movedPlace` accesses
the parent whole, at an instance the mark is transparent and the drop of `⋆` does nothing; the
reference, which accesses the lent prefix, matches the generic call, and this statement would be
a checker finding (D90: a borrow ends alike on every path). Open: a probe is owed. -/
theorem lentPrefix_none_of_proof (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (hproof : (valAt st.env pos).follow q.steps.2 = some .proof) :
    lentPrefix s pos q.steps.2 = none := by
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
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.logEffect q k) st b () st₁) :
    Rel K ρ φ π st₁ s ∧ Good K.dm K.M K.Γ ρ st₁ ∧ CtxOk K ρ st₁ ∧ st₁.env = st.env := by
  sorry

end

end Ochr.Meaning.Steps
