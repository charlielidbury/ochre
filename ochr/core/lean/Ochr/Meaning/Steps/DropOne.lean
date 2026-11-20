import Ochr.Meaning.Steps.JoinDropLib
import Ochr.Meaning.BotWrite
import Ochr.Meaning.SitesWrite
import Ochr.Meaning.RelendComm
import Ochr.Meaning.AccessAbsorb
import Ochr.Meaning.SitesFollow
import Ochr.Meaning.Steps.PlaceTyping

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

/-- A loop whose body never changes the state leaves it as it was. -/
theorem runs_forIn_keep' {α β : Type} (body : α → β → M (ForInStep β))
    (hb : ∀ x c st b r st', Runs (body x c) st b r st' → st' = st) :
    ∀ (xs : List α) (c : β) {st st' : MState} {b : Nat} {u : β}, Runs (forIn xs c body) st b u st' → st' = st
  | [], c, st, st', b, u, h => by
    rw [List.forIn_nil] at h
    exact (runs_pure_inv h).2
  | x :: xs, c, st, st', b, u, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    have e1 := hb x c st b r st₁ h1
    subst e1
    cases r with
    | done c' => exact (runs_pure_inv h2).2
    | yield c' => exact runs_forIn_keep' body hb xs c' h2

mutual
/-- `loanPath` reads the value and the declarations and changes nothing. -/
theorem runs_loanPath_keep (l : Nat) : ∀ (v : Value) {st st' : MState} {b : Nat} {o : Option (List Step)},
    Runs (Ochr.loanPath v l) st b o st' → st' = st
  | .loan m, _, _, _, _, h => by unfold Ochr.loanPath at h; exact (runs_pure_inv h).2
  | .gloan m w, _, _, _, _, h => by unfold Ochr.loanPath at h; exact runs_loanPath_keep l w h
  | .succ w, _, _, _, _, h | .borrow _ w, _, _, _, _, h => by
    unfold Ochr.loanPath at h
    obtain ⟨o', st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    rw [(runs_pure_inv h2).2]; exact runs_loanPath_keep l w h1
  | .ind t c hh ps fs, _, _, _, _, h => by
    unfold Ochr.loanPath at h
    obtain ⟨d, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    rw [runs_loanPathFields_keep l t c _ 0 fs h2]
    exact (runs_lookupInd_inv h1).1
  | .zero, _, _, _, _, h | .unit, _, _, _, _, h | .gfn _, _, _, _, _, h | .clo .., _, _, _, _, h
  | .bot, _, _, _, _, h | .abs _, _, _, _, _, h | .sealed _, _, _, _, _, h | .proof, _, _, _, _, h
  | .tNat, _, _, _, _, h | .tUnit, _, _, _, _, h | .tEq .., _, _, _, _, h | .tRef _, _, _, _, _, h
  | .tPi .., _, _, _, _, h | .sort _, _, _, _, _, h | .tInd .., _, _, _, _, h => by
    unfold Ochr.loanPath at h; exact (runs_pure_inv h).2

theorem runs_loanPathFields_keep (l : Nat) (t : String) (c : Nat) (names : List String) :
    ∀ (i : Nat) (ws : List Value) {st st' : MState} {b : Nat} {o : Option (List Step)},
      Runs (Ochr.loanPathFields t c names l i ws) st b o st' → st' = st
  | _, [], _, _, _, _, h => by unfold Ochr.loanPathFields at h; exact (runs_pure_inv h).2
  | i, w :: ws, _, _, _, _, h => by
    unfold Ochr.loanPathFields at h
    obtain ⟨o', st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    have e1 := runs_loanPath_keep l w h1
    subst e1
    split at h2
    · exact (runs_pure_inv h2).2
    · exact runs_loanPathFields_keep l t c names (i + 1) ws h2
end

/-- `throughLocalBorrow` reads the frame and changes nothing. -/
theorem runs_throughLocalBorrow_keep {f i : Nat} {p : Place} {st st' : MState} {b : Nat}
    {o : Option (Nat × List Step)} (h : Runs (Ochr.throughLocalBorrow f i p) st b o st') : st' = st := by
  unfold Ochr.throughLocalBorrow at h
  split at h
  rename_i fst ss _
  split at h
  · obtain ⟨x, st₁, b₁, hg, h1⟩ := Runs.bind_inv h
    obtain ⟨hx, hst₁⟩ := runs_get_inv hg
    subst x; subst st₁
    split at h1
    · obtain ⟨x, st₂, b₂, hg', h2⟩ := Runs.bind_inv h1
      obtain ⟨hx', hst₂⟩ := runs_get_inv hg'
      subst x; subst st₂
      obtain ⟨r, st₃, b₃, hl, h3⟩ := Runs.bind_inv h2
      have e3 : st₃ = st := by
        rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hl
        refine runs_forIn_keep' _ (fun j c st₀ b₀ r₀ st₀' hb => ?_) _ _ hl
        obtain ⟨o₀, st₄, b₄, h4, h5⟩ := Runs.bind_inv hb
        have := runs_loanPath_keep _ _ h4
        subst this
        split at h5 <;> exact (runs_pure_inv h5).2
      subst e3
      dsimp only at h3
      split at h3 <;> exact (runs_pure_inv h3).2
    · exact (runs_pure_inv h1).2
  · exact (runs_pure_inv h).2

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

theorem anyAtomList_mem {P : Value → Bool} : ∀ {fs : List Value}, Value.anyAtomList P fs = false →
    ∀ x ∈ fs, x.anyAtom P = false
  | [], _, x, hx => by cases hx
  | y :: ys, h, x, hx => by
    simp only [Value.anyAtomList, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact anyAtomList_mem h.2 x hx

/-- No bare constructor and no sealed program with a hint-reading tail, anywhere: top-hint-free. -/
theorem topHintFree_of (Γ : List IndDecl) : ∀ (x : Value), x.anyAtom (Value.bareCtor Γ) = false →
    x.anyAtom (fun a => a.isSealed && !a.topHintFree Γ) = false → x.topHintFree Γ = true
  | .borrow l w, hb, hs => by
    rw [Value.anyAtom] at hb hs; simp only [Bool.or_eq_false_iff] at hb hs
    simp only [Value.topHintFree]; exact topHintFree_of Γ w hb.2 hs.2
  | .gloan l w, hb, hs => by
    rw [Value.anyAtom] at hb hs; simp only [Bool.or_eq_false_iff] at hb hs
    simp only [Value.topHintFree]; exact topHintFree_of Γ w hb.2 hs.2
  | .sealed t, _, hs => by
    rw [Value.anyAtom] at hs; simp only [Bool.or_eq_false_iff] at hs
    have := hs.1; simp only [Value.isSealed, Bool.true_and, Bool.not_eq_false'] at this; exact this
  | .ind ty c h ps fs, hb, _ => by
    rw [Value.anyAtom] at hb; simp only [Bool.or_eq_false_iff] at hb
    have := hb.1
    cases ps with
    | nil =>
      simp only [Value.bareCtor] at this
      simp only [Value.topHintFree]
      cases e : List.find? (fun x => x.name == ty) Γ <;> simp_all
    | cons _ _ => simp [Value.topHintFree]
  | .zero, _, _ | .succ _, _, _ | .unit, _, _ | .gfn _, _, _ | .clo .., _, _ | .loan _, _, _ | .bot, _, _
  | .abs _, _, _ | .proof, _, _ | .tNat, _, _ | .tUnit, _, _ | .tEq .., _, _ | .tRef _, _, _ | .tPi .., _, _
  | .sort _, _, _ | .tInd .., _, _ => by simp [Value.topHintFree]

/-- Under the run's code meaning, such a value means the same at every hint (`meanV_hintIndep`). -/
theorem meanK_hintFree (x : Value) (hb : x.anyAtom (Value.bareCtor K.Γ) = false)
    (hs : x.anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false) (h h' : TyS) :
    Value.mean K.dm K.M K.Γ ρ φ h x = Value.mean K.dm K.M K.Γ ρ φ h' x := by
  rw [meanV_eq_mean K ρ φ h x, meanV_eq_mean K ρ φ h' x]
  exact meanV_hintIndep K ρ φ x (topHintFree_of K.Γ x hb hs) h h'

/-- **(1') L2 with sealed siblings**, at every reading type `T` of the write: `mean_updAt_bot` for a
value with no bare constructor and no sealed program whose tail reads the hint (`Value.topHintFree`:
[Close]'s programs, `HintIndep`), under the run's code meaning. The proof is `mean_updAt_bot`'s
with `meanV_hintIndep` (`meanK_hintFree`) in place of `mean_hintFree` for the later fields, which
are typed at the earlier ones. -/
theorem mean_updAt_botS : ∀ (steps : List Step) (H T : TyS) (v v' : Value),
    Value.updAt (fun _ => .bot) steps v = some v' →
    v.anyAtom (Value.bareCtor K.Γ) = false → v.anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false →
    NatAlong K.dm K.M K.Γ ρ φ steps v →
    Sem.updAt K.dm K.Γ T (fun _ => .moved) steps (Value.mean K.dm K.M K.Γ ρ φ H v) =
      some (Value.mean K.dm K.M K.Γ ρ φ H v')
  | [], H, T, v, v', h, _, _, _ => by
    simp only [Value.updAt, Option.some.injEq] at h
    subst h
    simp only [Sem.updAt_nil', Value.mean]
  | st :: ss, H, T, v, v', h, hb, hs, hd => by
    cases v with
    | gloan l w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      have hd' : NatAlong K.dm K.M K.Γ ρ φ (st :: ss) w := by cases st <;> simpa [NatAlong] using hd
      rw [Value.anyAtom] at hb hs; simp only [Bool.or_eq_false_iff] at hb hs
      simp only [Value.mean]
      exact mean_updAt_botS (st :: ss) H T w w' hw' hb.2 hs.2 hd'
    | borrow l w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        have hd' : NatAlong K.dm K.M K.Γ ρ φ ss w := by simpa [NatAlong] using hd
        rw [Value.anyAtom] at hb hs; simp only [Bool.or_eq_false_iff] at hb hs
        simp only [Value.mean, Sem.updAt_deref']
        exact mean_updAt_botS ss H T w w' hw' hb.2 hs.2 hd'
      | proj i => simp [Value.updAt] at h
      | field g => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨⟨n, hn⟩, hd'⟩ : (∃ n, (Value.mean K.dm K.M K.Γ ρ φ (.plain (.ty0 Nat)) w).asNat = some n) ∧
              NatAlong K.dm K.M K.Γ ρ φ ss w := by simpa [NatAlong] using hd
          rw [Value.anyAtom] at hb hs; simp only [Bool.or_eq_false_iff] at hb hs
          have IH := mean_updAt_botS ss (.plain (.ty0 Nat)) (.plain (.ty0 Nat)) w w' hw' hb.2 hs.2 hd'
          rw [Sem.asNat_some hn] at IH
          simp only [Value.mean, Sem.asNat_some hn, Sem.succ_el0]
          rw [Sem.updAt_nat' K.dm K.Γ T _ ss _ n (Sem.asNat_el0 (n + 1)), IH, Option.map_some]
        | succ i => simp [Value.updAt] at h
      | deref => simp [Value.updAt] at h
      | field g => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      obtain ⟨hst, w, w', hw, hw', rfl⟩ := updAt_ind_inv h
      obtain ⟨d, hf, hsort, hnat, hrec⟩ : ∃ d, K.Γ.find? (·.name == ty) = some d ∧ d.sort ≠ 0 ∧ d.name ≠ "Nat" ∧
          ∀ w, fs[st.fieldIdx]? = some w → NatAlong K.dm K.M K.Γ ρ φ ss w := by
        cases st with
        | deref => exact absurd rfl hst
        | proj i => simpa only [NatAlong] using hd
        | field g => simpa only [NatAlong] using hd
      rw [Value.anyAtom] at hb hs; simp only [Bool.or_eq_false_iff] at hb hs
      have hbare := hb.1
      have hbare' : Value.bareCtor K.Γ (.ind ty c hh ps (fs.set st.fieldIdx w')) = false := by
        cases ps <;> simp only [Value.bareCtor] at hbare ⊢ <;> exact hbare
      have hfb := anyAtomList_mem hb.2.2
      have hfs := anyAtomList_mem hs.2.2
      have HF : ∀ x ∈ fs, ∀ h h', Value.mean K.dm K.M K.Γ ρ φ h x = Value.mean K.dm K.M K.Γ ρ φ h' x :=
        fun x hx => meanK_hintFree K ρ φ x (hfb x hx) (hfs x hx)
      have hi : st.fieldIdx < fs.length := (List.getElem?_eq_some_iff.mp hw).1
      have hget := meanFields_getElem? K.dm K.M K.Γ ρ φ d (Value.meanParams K.dm K.M K.Γ ρ φ d 0 [] ps) c fs 0 [] st.fieldIdx w hw
      have hset := meanFields_setH K.dm K.M K.Γ ρ φ d (Value.meanParams K.dm K.M K.Γ ρ φ d 0 [] ps) c fs 0 [] st.fieldIdx w' hi HF
      simp only [Nat.zero_add, List.nil_append] at hget hset
      have hwm := List.mem_of_getElem? hw
      have IH := mean_updAt_botS ss (fieldHint K.dm d (Value.meanParams K.dm K.M K.Γ ρ φ d 0 [] ps) c st.fieldIdx
        ((Value.meanFields K.dm K.M K.Γ ρ φ d (Value.meanParams K.dm K.M K.Γ ρ φ d 0 [] ps) c 0 [] fs).take st.fieldIdx))
        T w w' hw' (hfb w hwm) (hfs w hwm) (hrec w hw)
      rw [mean_ind K.dm K.M K.Γ ρ φ hf hbare hsort, mean_ind K.dm K.M K.Γ ρ φ hf hbare' hsort, hset]
      obtain ⟨el, hel⟩ := Ochr.Meaning.ctorM_dat K.dm d (Value.meanParams K.dm K.M K.Γ ρ φ d 0 [] ps) c
        (Value.meanFields K.dm K.M K.Γ ρ φ d (Value.meanParams K.dm K.M K.Γ ρ φ d 0 [] ps) c 0 [] fs)
      rw [hel, Sem.updAt_dat' K.dm K.Γ T _ st ss hst hnat hget, IH, Option.map_some, reDat_eq K.dm K.Γ hf]
    | _ => simp [Value.updAt] at h
termination_by steps _ _ v => (steps.length, sizeOf v)

/-- **(1') L2 with sealed siblings** (`mean_updAt_botS` at `T = H`). PROVED (docs/31 D45). -/
theorem mean_updAt_bot_sealed (H : TyS) (steps : List Step) (v v' : Value)
    (h : Value.updAt (fun _ => .bot) steps v = some v')
    (hb : v.anyAtom (Value.bareCtor K.Γ) = false)
    (hs : v.anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false)
    (hd : NatAlong K.dm K.M K.Γ ρ φ steps v) :
    Sem.updAt K.dm K.Γ H (fun _ => .moved) steps (Value.mean K.dm K.M K.Γ ρ φ H v) =
      some (Value.mean K.dm K.M K.Γ ρ φ H v') :=
  mean_updAt_botS K ρ φ steps H H v v' h hb hs hd

/-- **A live label of the checker is live in the reference**: under (WF1) its holder holds it
whole, so the position has its shape; `SimEq` gives the reference a holder of its renaming (a
temporary's at some index), and the reference holds borrows only at its positions (`Rel.holders`). -/
theorem rel_live_ref' (st : MState) (s : SState) (π : Nat → Nat) (hg : Good K.dm K.M K.Γ ρ st)
    (hs : Rel K ρ φ π st s) {l : Nat} (hl : liveLoan st.env l = true) : π l ∈ s.liveLabels := by
  unfold liveLoan at hl
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp hl
  have hmem := mem_allPos_of_find st.env l p₀ hp₀
  have hhold : (valAt st.env p₀).holdsBorrow l = true := by
    unfold findBorrow at hp₀; exact List.find?_some (p := fun p => (valAt st.env p).holdsBorrow l) hp₀
  have hsh : Env.shape st.env p₀ = some l := by
    have hwf1 := hg.2.2.1.1 p₀ hmem
    cases hv : valAt st.env p₀ with
    | borrow m w =>
      rw [hv] at hwf1 hhold
      simp only [Value.holdsBorrow, Bool.or_eq_true, beq_iff_eq] at hhold
      rcases hhold with rfl | hw
      · simp [Env.shape, hv]
      · exact absurd (hasBorrow_of_holdsBorrow l w hw) hwf1
    | succ w =>
      rw [hv] at hwf1 hhold
      simp only [Value.holdsBorrow] at hhold
      exact absurd (hasBorrow_of_holdsBorrow l (.succ w) (by simpa [Value.holdsBorrow] using hhold)) hwf1
    | _ => rw [hv] at hhold; simp [Value.holdsBorrow] at hhold
  rw [SState.mem_liveLabels]
  cases p₀ with
  | bind f i =>
    have := hs.sim.2.1 (.bind f i) l (by simp [IsTemp]) hsh
    exact ⟨_, hs.holders _ _ this, this⟩
  | temp f i =>
    obtain ⟨j, hj, -⟩ := hs.sim.2.2.2.1 f i l hsh
    exact ⟨_, hs.holders _ _ hj, hj⟩

/-- **The checker's access clears the place**: after it, no live borrow has a site at, over or
under the place (`dataHit`). Read through the relation, where the reference's access is at its
fixpoint (`SState.access_post`): the related reference state is an access of the same position and
path, the live labels correspond (`rel_live_ref'`) and so do their sites (`Rel.sites`). PROVED
(docs/31 D48); as first stated it was about the checker's two loops' exits, which needs a frame
lemma for [End] (what an end leaves untouched). -/
theorem access_clears (st : MState) (s : SState) (π : Nat → Nat) (pos : Pos) (steps : List Step)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st (s.access pos (dataHit steps))) :
    ∀ l, liveLoan st.env l = true → ∀ x ∈ Env.sitesOf st.env l, x.pos = pos →
      dataHit steps x.path = false := by
  intro l hl x hx hxp
  cases e : dataHit steps x.path
  · rfl
  · exfalso
    have hlive := rel_live_ref' K ρ φ st _ π hg hs hl
    have hxs := (hs.sites l hl x).mpr hx
    have hpost := SState.access_post s pos (dataHit steps) (π l) hlive
    unfold SState.reached at hpost
    rw [List.any_eq_false] at hpost
    exact hpost x hxs (by simp [hxp, e])

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
  have h12 : WF12 st.env := hg.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpre : (pathKey z.path).isPrefixOf (pathKey x.path) = true := by
    rw [hzr.2]; exact List.isPrefixOf_iff_prefix.mpr hK
  obtain ⟨z', hz', hz'p, hz'k, hz'f⟩ := h12 k₀ l₀ hk₀ hl₀ z hz' hzf x hx' (hxp.trans hzr.1.symm) hpre
  refine ⟨z', (hs.sites l₀ hl₀ z').mpr hz', hz'p.trans hzr.1, hz'k.trans hzr.2, hz'f⟩

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
first and ends it. PROVED from (WF14) (docs/31 D43), the clause read off the checker and swept
(`lake exe sweep`'s clause (iii), at every `⊥` part of every position), through the relation's live
labels (`rel_live_ref`) and sites.

As first written it also covered a `⋆` part, which the sweep refuted: a place lent whole keeps its
proof field under the mark (`MkC(n, h)` lent by `Get(&c)`, state `c = lent_2 MkC(loan_2, ⋆)`,
19 states). The `⋆` case is `lentPrefix_none_of_proof`, at the places the join drops. -/
theorem lentPrefix_none_of_noop (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hnoop : (valAt st.env pos).follow q.steps.2 = some .bot) :
    lentPrefix s pos q.steps.2 = none := by
  have h14 : WF14 st.env := hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold lentPrefix
  rw [List.find?_eq_none]
  intro ψ hψ hP
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hψ
  obtain ⟨m, hm, hr⟩ := List.any_eq_true.mp hP
  obtain ⟨l, hl, rfl⟩ := rel_live_ref K ρ φ st s π hs hm
  unfold SState.reached at hr
  obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxp
  exact h14 pos q.steps.2 hnoop l hl x ((hs.sites l hl x).mp hx) hxp.1 k (List.mem_range.mp hk) hxp.2

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

/-- The closed future changes only the live labels. -/
theorem closedFuture_nonlive (s : SState) (φ : Future) {l : Nat} (hl : l ∉ s.liveLabels) :
    s.closedFuture φ l = φ l := by
  have hpass : ∀ ψ : Future, s.cfPass ψ l = ψ l := by
    intro ψ
    unfold SState.cfPass
    have : ∀ (ls : List Nat) (ψ : Future), l ∉ ls → (ls.foldl (fun ψ l' =>
        match s.holderOf l' with
        | some r => ψ.upd l' (s.valAt r ψ)
        | none => ψ) ψ) l = ψ l := by
      intro ls
      induction ls with
      | nil => intro ψ _; rfl
      | cons a t ih =>
        intro ψ hn
        simp only [List.foldl_cons]
        rw [ih _ (fun h => hn (List.mem_cons_of_mem _ h))]
        have hne : l ≠ a := fun e => hn (e ▸ List.mem_cons_self ..)
        cases hh : s.holderOf a <;> simp [Future.upd, hne]
    exact this _ ψ hl
  rw [SState.closedFuture_eq]
  generalize List.range s.liveLabels.length = rs
  induction rs generalizing φ with
  | nil => rfl
  | cons a t ih => simp only [List.foldl_cons]; rw [ih, hpass]

/-- **What the checker's content says of the reference's `follow`** at the dropped place: a `⊥`
or a `⋆` reads `moved` or `⋆` (a place inside a proof reads `⋆` whatever the checker holds there).
PROVED (docs/31 D44) from the checker's typing of places along the join's grain (`followMean`):
the reference's reading of a place at the grain is the meaning of the checker's value there, or `⋆`.
As first stated it asked `moved` exactly of a `⊥`, false inside a value of a `Prop`-sorted type
(whose meaning is `⋆` whatever its fields hold), where the reference's drop does nothing too; it
also lacked the grain and the typing, without which a step of the reference's reading need not be
the checker's (a constructor of an undeclared type means `err`). -/
theorem content_follow (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hck : ckVarPos st.env q.steps.1 = some pos) (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (c : Value)
    (hc : (valAt st.env pos).follow q.steps.2 = some c) (hcb : c = .bot ∨ c = .proof) :
    ∃ x T, Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos (s.closedFuture φ)) q.steps.2 = some (x, T) ∧
      (x = .moved ∨ x = .proof) := by
  have hgr : GrainOk K.D K.Γ (DecideScope.topReadings st) q := by rw [← rel_scopeOf K ρ φ hs]; exact hgrain
  have hpt : ¬ IsTemp pos := by
    rcases pos with ⟨f, i⟩ | ⟨f, i⟩
    · simp [IsTemp]
    · unfold ckVarPos at hck; split at hck <;> cases hck
  have hrel : RelF φ s (s.closedFuture φ) := fun l hl => closedFuture_nonlive s φ hl
  have hval : s.valAt pos (s.closedFuture φ) =
      Env.mean K.dm K.M K.Γ ρ (fun l => s.closedFuture φ (π l)) st.env pos := (hs.sim.1 _ hrel pos hpt).symm
  obtain ⟨s', T', h1, h2⟩ := followMean K ρ hctx hg (fun l => s.closedFuture φ (π l)) pos q hgr hck c
    (by unfold ckContent; simp [hck, hc]) (s.tyAt pos)
  rw [hval]
  refine ⟨s', T', h1, ?_⟩
  rcases h2 with rfl | ⟨H, rfl⟩
  · exact .inr rfl
  · rcases hcb with rfl | rfl
    · exact .inl (by simp [Value.mean])
    · exact .inr (by simp [Value.mean])

/-- **The copy decision is aligned**: the checker's `copyRead` is the reference's declared reading
of the place (the decisions are the checker's `Decide`, `CtxOk`). Open: not tried. -/
theorem copyRead_aligned (fuel : Nat) (st st₁ : MState) (s : SState) (π : Nat → Nat) (q : Place) (c : Bool) (b : Nat)
    (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s) (h : Runs (Ochr.copyRead fuel q) st b c st₁) :
    st₁ = st ∧ c = K.D.copy (K.D.placeDecl (scopeOf s) q) := by
  sorry

/-- `logEffect` appends to `placeLog` and changes nothing else. -/
theorem runs_logEffect_inv {q : Place} {k : String} {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (Ochr.logEffect q k) st b u st') : ∃ X, st' = { st with placeLog := X } := by
  unfold Ochr.logEffect at h
  obtain ⟨pos, st₁, b₁, hv, h1⟩ := Runs.bind_inv h
  obtain ⟨hst₁, -⟩ := runs_varPos_inv hv
  subst st₁
  split at h1
  · split at h1
    · obtain ⟨u₁, st₂, b₂, hm, h2⟩ := Runs.bind_inv h1
      obtain ⟨L, left, log, hm⟩ := hm
      simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at hm
      obtain ⟨⟨-, hst₂⟩, -⟩ := hm
      subst st₂
      obtain ⟨o, st₃, b₃, ht, h3⟩ := Runs.bind_inv h2
      have := runs_throughLocalBorrow_keep ht
      subst st₃
      split at h3
      · obtain ⟨L, left, log, h3⟩ := h3
        simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at h3
        exact ⟨_, h3.1.2.symm⟩
      · exact ⟨_, (runs_pure_inv h3).2⟩
    · exact ⟨st.placeLog, (runs_pure_inv h1).2⟩
  · exact ⟨st.placeLog, (runs_pure_inv h1).2⟩

/-- Being referenced reads the values, stored types, goal, records and types of unknowns only. -/
theorem refd_of_same {st st' : MState} (henv : st'.env = st.env) (hgoal : st'.goal = st.goal)
    (hn : st'.neutrals = st.neutrals) (he : st'.etaRefs = st.etaRefs) (ha : st'.absTy = st.absTy) {σ : Nat}
    (h : st'.Refd σ) : st.Refd σ := by
  induction h with
  | val v hv h => exact .val v (henv ▸ hv) h
  | ty f i b T hb hT h => exact .ty f i b T (henv ▸ hb) hT h
  | lazyTy f i b P ws j hb hT h => exact .lazyTy f i b P ws j (henv ▸ hb) hT h
  | goal G hG h => exact .goal G (hgoal ▸ hG) h
  | neutral n σ' hn' h => exact .neutral n σ' (hn ▸ hn') h
  | eta σ' v he' h => exact .eta σ' v (he ▸ he') h
  | dep σ' T _ hT h ih => exact .dep σ' T ih (ha ▸ hT) h

/-- **`logEffect` changes nothing the relation or `Good` reads** (it writes `placeLog` only,
`runs_logEffect_inv`; `throughLocalBorrow` and `loanPath` only read). -/
theorem logEffect_rel (st st₁ : MState) (s : SState) (π : Nat → Nat) (q : Place) (k : String) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.logEffect q k) st b () st₁) :
    Rel K ρ φ π st₁ s ∧ Good K.dm K.M K.Γ ρ st₁ ∧ CtxOk K ρ st₁ ∧ st₁.env = st.env := by
  obtain ⟨X, rfl⟩ := runs_logEffect_inv h
  obtain ⟨ta, mem, wf⟩ := hg
  have hrefd : ∀ τ, ({ st with placeLog := X } : MState).Refd τ → st.Refd τ :=
    fun τ h => refd_of_same (st := st) (st' := { st with placeLog := X }) rfl rfl rfl rfl rfl h
  exact ⟨⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6⟩,
    ⟨⟨fun τ hr hlt => ta.mem τ (hrefd τ hr) hlt, ta.neutral, ta.eta, ta.refs⟩,
     ⟨mem.pos, fun τ hr hlt => mem.absTy τ (hrefd τ hr) hlt, mem.goal⟩,
     ⟨wf.1, wf.2.1, wf.2.2.1, wf.2.2.2.1, ⟨fun τ hr => wf.2.2.2.2.1.1 τ (hrefd τ hr), wf.2.2.2.2.1.2⟩,
      wf.2.2.2.2.2⟩⟩,
    ⟨hctx.1, hctx.2, fun τ hr hlt => hctx.3 τ (hrefd τ hr) hlt, hctx.4, ⟨hctx.5.1, hctx.5.2, hctx.5.3, hctx.5.4⟩,
      hctx.6.of_sameDec rfl rfl, hctx.7.of_sameDec rfl rfl rfl⟩, rfl⟩

end

end Ochr.Meaning.Steps
