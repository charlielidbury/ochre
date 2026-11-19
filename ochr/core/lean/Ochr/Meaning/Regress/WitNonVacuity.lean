import Ochr.Meaning.Steps.Sim
import Ochr.Meaning.RunPres
import Ochr.Meaning.Regress.EarlyUnpinned
import Ochr.Meaning.Regress.CondDep

/-!
# The loan witness checked both ways (built)

docs/31 D27 (fourth lead, 2026-11-19). A clause of `Rel` that is never checked on a state it must
exclude, or on a state it must hold at, is how the earlier forms of the relation went wrong. So:

* **It excludes the unpinned state** (`not_related`). The checker holds the constant `Z` at `x`
  and the borrow of label `1` at `hk`, and has ended label `0` early (`hl ↦ ⊥`). The reference's
  `x` means `EarlyUnpinned.f₁ 0 1 c` (it reads label `1` where label `0` reads `err`). No
  renaming and no list of early ends relate them: label `1` is held by the checker, so it is not
  early-ended, and the reference's [Access] of `x` would end it, where the checker's ends nothing
  (its `x` holds no loan).
* **It holds at the reachable form of D27's example 1** (`wit_example1`). The checker has ended
  label `0` (`j`) early and holds at `x` the fill with its content substituted, still holding the
  loan of label `1` (`m`), whose borrow `hm` holds; the reference's `x` means
  `CondDep.fx 0 1 c`, which reads `1` only where `0` holds `0`. The witness holds with `E = [0]`:
  the reference can end only `0` and `1`, and the checker's access of `x` ends `1`.

Checking the second on its first statement found a fault of the clause: it ranged over every
place, including the places into the sealed fill, whose meaning the reference follows and the
checker cannot reach. `Wit` now ranges over the places whose path reaches content in the
checker's state (`pathReaches`).
-/

namespace Ochr.Meaning.Regress.WitNonVacuity
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-! ## Shapes after a list of ends -/

/-- After ends, a position's shape is what it was, or forgotten. -/
theorem foldl_endLabel_shape : ∀ (E : List Nat) (s : SState) (p : Pos),
    (E.foldl SState.endLabel s).shape p = none ∨ (E.foldl SState.endLabel s).shape p = s.shape p
  | [], s, p => .inr rfl
  | l :: E, s, p => by
    simp only [List.foldl_cons]
    rcases foldl_endLabel_shape E (s.endLabel l) p with h | h
    · exact .inl h
    · rw [h]
      cases e : s.holderOf l with
      | none => rw [SState.endLabel_of_none e]; exact .inr rfl
      | some r =>
        rw [SState.endLabel_eq e, SState.endAt_shape]
        by_cases hp : p = r
        · simp [hp]
        · simp [hp]

theorem foldl_endLabel_positions : ∀ (E : List Nat) (s : SState),
    (E.foldl SState.endLabel s).positions = s.positions
  | [], _ => rfl
  | l :: E, s => by
    simp only [List.foldl_cons]
    rw [foldl_endLabel_positions E (s.endLabel l), endLabel_positions]

/-! ## The unpinned state is not related -/

/-- The checker's state: `x ↦ Z`, `hk ↦ borrow₁ Z` (label `1` live), `hl ↦ ⊥` (label `0` ended). -/
def stU : MState := { env := #[{ binds := #[
  { hint := ⟨"x"⟩, ty := some .tNat, val := .zero },
  { hint := ⟨"hk"⟩, ty := some (.tRef .tNat), val := .borrow 1 .zero },
  { hint := ⟨"hl"⟩, ty := some (.tRef .tNat), val := .bot }] }], nextLoan := 2 }

/-- The reference's state: `x` means `f₁ 0 1 c`; `hk` holds label `1`, `hl` label `0`. -/
noncomputable def sU (c : Sem) : SState :=
  { env := [{ binds := [
      { ty := .plain .err, val := EarlyUnpinned.f₁ 0 1 c },
      { ty := .plain .err, val := fun _ => .el0 Nat 0 },
      { ty := .plain .err, val := fun _ => .el0 Nat 1 }] }],
    shape := fun p => if p = .bind 0 1 then some 1 else if p = .bind 0 2 then some 0 else none,
    nextLoan := 2 }

theorem sU_positions (c : Sem) : (sU c).positions = [.bind 0 0, .bind 0 1, .bind 0 2] := by
  rw [SState.positions_eq]; rfl

theorem sU_valAt0 (c : Sem) : (sU c).valAt (.bind 0 0) = EarlyUnpinned.f₁ 0 1 c := rfl

/-- The whole observation at the empty path: the content with its type. -/
theorem obs_whole (K : RunCtx) (T : TyM) (x : Sem) : obsAt K T [] wholeOb x = .ctor "" 0 [x, .ty T] := rfl

/-- The checker's access of `x` ends nothing: `Z` holds no loan. -/
theorem accLoans_x (n : Nat) : accLoans stU.env n (valAt stU.env (.bind 0 0)) [] = [] := by
  rcases n with _ | _ | n <;> rfl

/-- **The unpinned state is not related, under any renaming**: the witness excludes it. -/
theorem not_related (K : RunCtx) (ρ : Assignment) (φ : Future) (c : Sem) (π : Nat → Nat) :
    ¬ Rel K ρ φ π stU (sU c) := by
  intro hr
  obtain ⟨E, hsim, hw⟩ := hr.early
  -- the checker holds label `1` at `hk`, so the reference still holds `π 1` there after the ends
  have hsh := hsim.2.1 (.bind 0 1) 1 (by simp [IsTemp]) rfl
  have hπ : π 1 = 1 := by
    rcases foldl_endLabel_shape E (sU c) (.bind 0 1) with h | h
    · rw [h] at hsh; cases hsh
    · rw [h] at hsh; simp [sU] at hsh; exact hsh.symm
  -- so label `1` is live after the ends, hence not early-ended
  have hlive : (E.foldl SState.endLabel (sU c)).Live 1 := by
    rw [SState.live_iff]
    exact ⟨.bind 0 1, by rw [foldl_endLabel_positions, sU_positions]; simp, hsh.trans (by rw [hπ])⟩
  have hnE : 1 ∉ E := by
    intro hE
    have hcount := SState.holders_foldl_endLabel 1 E (sU c)
    have h1 : (sU c).holders 1 = 1 := by
      unfold SState.holders; rw [sU_positions]; simp [sU]
    have hc : 0 < E.count 1 := List.count_pos_iff.mpr hE
    rw [SState.live_iff_holders] at hlive
    omega
  -- the reference's access of `x` would end label `1`, which the checker's does not
  have hdep : ReachDep (sU c) (.bind 0 0) (obsAt K ((sU c).tyAt (.bind 0 0)).m [] wholeOb) 1 := by
    refine .direct ?_ ?_
    · rw [SState.live_iff]; exact ⟨.bind 0 1, by rw [sU_positions]; simp, by simp [sU]⟩
    · refine ⟨fun _ => .err, .proof, ?_⟩
      rw [sU_valAt0, obs_whole, obs_whole]
      unfold EarlyUnpinned.f₁
      rw [Future.upd_other _ _ (by decide : (0 : Nat) ≠ 1), Future.upd_same]
      simp
  obtain ⟨l', _, hmem⟩ := hw (.var 2) (.bind 0 0) [] rfl (by decide) 1 hdep hnE
  rw [accLoans_x] at hmem
  cases hmem

/-! ## The witness holds at the reachable form of D27's example 1

The checker has ended label `0` (`j`) early: its holder `hj` is `⊥` and the fill at `x` has its
content substituted, which still holds the loan of label `1` (`m`), whose borrow `hm` holds. The
fill is `⌈loan₁⌉` here: what the witness reads of it is its loans. The reference has not ended
`0`; its `x` means `CondDep.fx 0 1 c` (the unknown callee's backward function at the content
`(ψ 0, ψ 1)`), its `hm` holds `1` and its `hj` holds `0`. -/

def stE : MState := { env := #[{ binds := #[
  { hint := ⟨"x"⟩, ty := some .tNat, val := .sealed (.val (.loan 1)) },
  { hint := ⟨"hm"⟩, ty := some (.tRef .tNat), val := .borrow 1 .zero },
  { hint := ⟨"hj"⟩, ty := some (.tRef .tNat), val := .bot }] }], nextLoan := 2 }

noncomputable def sE (c n : Nat) : SState :=
  { env := [{ binds := [
      { ty := .plain .err, val := CondDep.fx 0 1 c },
      { ty := .plain .err, val := fun _ => .el0 Nat 0 },
      { ty := .plain .err, val := fun _ => .el0 Nat (n + 1) }] }],
    shape := fun p => if p = .bind 0 1 then some 1 else if p = .bind 0 2 then some 0 else none,
    nextLoan := 2 }

theorem sE_valAt0 (c n : Nat) : (sE c n).valAt (.bind 0 0) = CondDep.fx 0 1 c := rfl

/-- Every position but `x` reads no future. -/
theorem sE_const (c n : Nat) (p : Pos) (hp : p ≠ .bind 0 0) (ψ ψ' : Future) :
    (sE c n).valAt p ψ = (sE c n).valAt p ψ' := by
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | f
    · rcases i with _ | _ | _ | i
      · exact absurd rfl hp
      · rfl
      · rfl
      · rfl
    · rfl
  · rcases f with _ | f <;> rfl

/-- Every position reads at most labels `0` and `1`. -/
theorem sE_FT (c n : Nat) (p : Pos) : FT (fun y => y = 0 ∨ y = 1) ((sE c n).valAt p) := by
  by_cases hp : p = .bind 0 0
  · subst hp
    rw [sE_valAt0]
    intro ψ ψ' h
    unfold CondDep.fx
    rw [h 0 (.inl rfl), h 1 (.inr rfl)]
  · exact fun ψ ψ' _ => sE_const c n p hp ψ ψ'

/-- The checker's access of `x` (the whole fill) ends label `1`. -/
theorem allPos_stE : allPos stE.env = [.bind 0 0, .bind 0 1, .bind 0 2] := by
  rw [allPos_eq]; rfl

theorem liveLoan_stE : liveLoan stE.env 1 = true := by
  unfold liveLoan findBorrow; rw [allPos_stE]; rfl

theorem accLoans_fill : 1 ∈ accLoans stE.env ((allPos stE.env).length + 1) (valAt stE.env (.bind 0 0)) [] := by
  rw [allPos_stE]
  show 1 ∈ accLoans stE.env 4 (.sealed (.val (.loan 1))) []
  simp [accLoans, loanOnPath, Value.follow, insideLoans, liveLoansIn, Value.loans, Term.loans, liveLoan_stE]

/-- No path into the fill reaches content: the checker cannot follow a sealed program. -/
theorem pathReaches_fill (st : Step) (ss : List Step) (k : Nat) :
    pathReaches stE.env k (valAt stE.env (.bind 0 0)) (st :: ss) = false := by
  rcases k with _ | k
  · rfl
  · cases st with
    | proj i => rcases i with _ | i <;> rfl
    | _ => rfl

/-- **The witness holds**, with label `0` early-ended: whatever the reference's access ends other
than `0` is `1`, and the checker's access of the one place whose path reaches content and whose
meaning reads the future, `x` itself, ends `1`. -/
theorem wit_example1 (K : RunCtx) (c n : Nat) : Wit K id [0] stE.env (sE c n) := by
  intro q pos steps _ hreach m hr hm
  have hm1 : m = 1 := by
    rcases reachDep_FT (sE_FT c n) hr with h | h
    · exact absurd (by rw [h]; exact List.mem_singleton_self 0) hm
    · exact h
  subst hm1
  refine ⟨1, rfl, ?_⟩
  by_cases hpos : pos = .bind 0 0
  · subst hpos
    cases steps with
    | nil => exact accLoans_fill
    | cons st ss => rw [pathReaches_fill] at hreach; cases hreach
  · exfalso
    have hd : ∀ {o : Sem → Sem} {l : Nat}, ¬ (sE c n).obsDep pos o l := by
      rintro o l ⟨ψ, x, hne⟩
      exact hne (by rw [sE_const c n pos hpos ψ (ψ.upd l x)])
    cases hr with
    | direct _ hd' => exact hd hd'
    | via _ hd' _ => exact hd hd'

end Ochr.Meaning.Regress.WitNonVacuity
