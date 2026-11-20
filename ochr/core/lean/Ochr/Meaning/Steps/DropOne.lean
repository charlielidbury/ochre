import Ochr.Meaning.Steps.JoinDropLib
import Ochr.Meaning.BotWrite
import Ochr.Meaning.SitesWrite
import Ochr.Meaning.RelendComm
import Ochr.Meaning.AccessAbsorb
import Ochr.Meaning.SitesFollow

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
2. L3, the write keeps the relation (`botWrite_rel`, PROVED, and `botWrite_good`), from L2 and the access having ended every
   borrow lent at, over or under the place (`access_clears`).
3. The commutation of ends on sites: PROVED (`relend_comm`, `RelendComm.lean`), when every site
   at either holder is inside its content and the two are not lent at each other's holders; it is
   used inside the [Access] statement, an induction-hypothesis field.
4. The checker's place and the reference's: `rel_resolve` (through `Rel.skel`).
5. `refine` and `generalizeNeutral` in the simulation form with an extended context
   (both assembled from smaller obligations in `Steps/DropOneAsm.lean`, `refine_sim'` and
   `generalizeNeutral_sim`; the first forms, unused, are deleted).
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

/-- **A live label of the reference is the renaming of a live label of the checker** (`SimEq`'s
holders both ways: a reference holder's label renames a checker holder's). -/
theorem rel_live_ref (st : MState) (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) {m : Nat}
    (hm : m ∈ s.liveLabels) : ∃ l, liveLoan st.env l = true ∧ π l = m := by
  obtain ⟨p, -, hsh⟩ := (SState.mem_liveLabels s m).mp hm
  cases p with
  | bind f i =>
    obtain ⟨l, hl, hπ⟩ := hs.sim.2.2.1 (.bind f i) m (by simp [IsTemp]) hsh
    exact ⟨l, liveLoan_of_shape (p := .bind f i) hl, hπ⟩
  | temp f j =>
    obtain ⟨i, l, hl, hπ⟩ := hs.sim.2.2.2.2 f j m hsh
    exact ⟨l, liveLoan_of_shape (p := .temp f i) hl, hπ⟩

/-- **(6) At the lent prefix above an existing place, only that prefix's borrow, as a fill**: a
live borrow with a site at or below the lent prefix has a fill exactly there. The prefix's own site
is a fill, not a loan (a place exists below it, and nothing exists below a loan); and (WF12) leaves
no other live borrow at or below a live fill. The second half of `SState.AbsorbInv`; the first is
the prefix's minimality (`lentPrefix_above`). Open: the correspondence between the checker's sites
(`Value.sitesOf`) and its paths (`Value.follow`) at one position, and between the live labels of
related states (`SimEq`'s holders, `Rel.sites`). -/
theorem lentPrefix_fill (st : MState) (s : SState) (π : Nat → Nat) (pos : Pos) (steps ss ψ : List Step) (w : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hp : pos ∈ allPos st.env)
    (hl : lentPrefix s pos steps = some ψ) (hw : (valAt st.env pos).follow ss = some w)
    (hlt : pathKey ψ <+: pathKey ss) (hne : pathKey ψ ≠ pathKey ss) :
    ∀ m ∈ s.liveLabels, ∀ x ∈ s.lent m, x.pos = pos → pathKey ψ <+: pathKey x.path →
      ∃ y ∈ s.lent m, y.pos = pos ∧ pathKey y.path = pathKey ψ ∧ y.fill = true := by
  intro m hm x hx hxp hK
  have hP : s.liveLabels.any (s.reached pos fun ψ' => pathKey ψ' == pathKey ψ) = true := by
    unfold lentPrefix at hl
    exact List.find?_some (p := fun ψ => s.liveLabels.any (s.reached pos fun ψ' => pathKey ψ' == pathKey ψ)) hl
  obtain ⟨k, hk, hkr⟩ := List.any_eq_true.mp hP
  unfold SState.reached at hkr
  obtain ⟨z, hz, hzr⟩ := List.any_eq_true.mp hkr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hzr
  obtain ⟨k₀, hk₀, rfl⟩ := rel_live_ref K ρ φ st s π hs hk
  obtain ⟨l₀, hl₀, rfl⟩ := rel_live_ref K ρ φ st s π hs hm
  have hz' : z ∈ Env.sitesOf st.env k₀ := (hs.sites k₀ hk₀ z).mp hz
  have hx' : x ∈ Env.sitesOf st.env l₀ := (hs.sites l₀ hl₀ x).mp hx
  have hzf : z.fill = true := by
    cases hzfill : z.fill
    · exfalso
      obtain ⟨ψ₀, hzpath, hb⟩ := loanSite_blocks k₀ pos [] (valAt st.env pos) z (mem_sitesOf_at hz' hzr.1) hzfill
      simp only [List.nil_append] at hzpath
      rw [hzpath] at hzr
      have := hb ss (hzr.2 ▸ hlt) (hzr.2 ▸ hne)
      rw [hw] at this; cases this
    · rfl
  by_cases hkl : k₀ = l₀
  · subst hkl
    exact ⟨z, hz, hzr.1, hzr.2, hzf⟩
  · exfalso
    have h12 : WF12 st.env := hg.2.2.2.2.2.2.2.2.2.2.2.2
    have := h12 k₀ l₀ hk₀ hl₀ hkl z hz' hzf x hx' (hxp.trans hzr.1.symm)
    rw [hzr.2] at this
    have hpre : (pathKey ψ).isPrefixOf (pathKey x.path) = true := List.isPrefixOf_iff_prefix.mpr hK
    rw [hpre] at this; cases this

/-- The sites at the lent prefix of a path above an existing place are as the absorption needs. -/
theorem lentPrefix_absorbInv (st : MState) (s : SState) (π : Nat → Nat) (pos : Pos) (steps ss ψ : List Step) (w : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hp : pos ∈ allPos st.env)
    (hl : lentPrefix s pos steps = some ψ) (hw : (valAt st.env pos).follow ss = some w)
    (hlt : pathKey ψ <+: pathKey ss) (hne : pathKey ψ ≠ pathKey ss) : s.AbsorbInv pos (pathKey ψ) :=
  ⟨lentPrefix_above hl, lentPrefix_fill K ρ φ st s π pos steps ss ψ w hg hs hp hl hw hlt hne⟩

theorem dataHit_congr {ψ₁ ψ₂ : List Step} (h : pathKey ψ₁ = pathKey ψ₂) : dataHit ψ₁ = dataHit ψ₂ := by
  funext x; simp [dataHit, h]

/-- **(6) The lent prefix, absorbed at an instance.** Where the place exists under a fill (a mark,
transparent to the checker's path), the checker accesses the path to the place only, the
reference first the shortest lent prefix whole; the two end the same borrows
(`SState.access_absorb`, under `lentPrefix_absorbInv`), and accessing twice is accessing once.
Assembled; it rests on `lentPrefix_fill`. -/
theorem lentPrefix_absorbed (st st' : MState) (s : SState) (π : Nat → Nat) (pos : Pos) (steps : List Step) (w : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hp : pos ∈ allPos st.env)
    (hw : (valAt st.env pos).follow steps = some w) :
    Rel K ρ φ π st' ((accessLentPrefix pos steps s).access pos (dataHit steps)) ↔
      Rel K ρ φ π st' (s.access pos (dataHit steps)) := by
  have e : (accessLentPrefix pos steps s).access pos (dataHit steps) = s.access pos (dataHit steps) := by
    unfold accessLentPrefix
    rcases hl : lentPrefix s pos steps with _ | ψ
    · rfl
    · simp only
      obtain ⟨j, hj, hψ, -⟩ := lentPrefix_spec hl
      have hlt : pathKey ψ <+: pathKey steps := by
        rw [hψ]; simp only [pathKey, List.map_take]; exact List.take_prefix _ _
      have hne : pathKey ψ ≠ pathKey steps := by
        intro h
        have := congrArg List.length h
        simp [pathKey, hψ] at this
        omega
      have hI := lentPrefix_absorbInv K ρ φ st s π pos steps steps ψ w hg hs hp hl hw hlt hne
      rw [SState.access_absorb hI hlt, SState.access_access]
  rw [e]

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
a checker finding (D90: a borrow ends alike on every path). Probed (2026-11-21): a data field of a
proof cannot be read at a data position, so no arm moves one: a match on a proof returning data is
rejected ([D45]: not a subsingleton) and a projection from data into its proof field is rejected
([D81]: name it with a match, which is then on a proof); a read inside a proof is erased, and the
join's move list skips erased terms (`Decide.jdMoves`). Open: no proof; the premise did not arise. -/
theorem lentPrefix_none_of_proof (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (hproof : (valAt st.env pos).follow q.steps.2 = some .proof) :
    lentPrefix s pos q.steps.2 = none := by
  sorry

/-- **What the checker's content says of the reference's `follow`** at the dropped place, after
the access: a `⊥` reads `moved`, a `⋆` reads `proof` (L4: a proof in Ω is `⋆`; the relation's
readings at the closed future). As first stated it also claimed the converses and that a place
missing on one side is missing on the other; that is false under a sealed program or an unknown,
whose meaning has the field the checker cannot follow (the case `movedPlace` refines), and it was
never used, so it is removed. Open: not tried. -/
theorem content_follow (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2)) :
    ((valAt st.env pos).follow q.steps.2 = some .bot →
      ∃ T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = some (.moved, T)) ∧
    ((valAt st.env pos).follow q.steps.2 = some .proof →
      ∃ T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = some (.proof, T)) := by
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
