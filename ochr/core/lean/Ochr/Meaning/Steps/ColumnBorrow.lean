import Ochr.Meaning.Steps.ColumnWrite

/-!
# The borrow column: `&x` (lead8)

The first step that makes a LIVE label: `&x`, in a typed run, where `x` is a top-frame variable bound
at `Nat` to a number and nothing is lent at it. The checker (`BorrowNumInv`) leaves `x ↦ loan_lc`
and returns `borrow_lc v` at `&Nat` with `lc` its label counter; the strict run (`borrowPlace`)
leaves `x` reading its fresh label `lr` (the reference's counter), parks the borrow in a temporary
of the top frame, records the content `⟦v⟧` as the label's member and `x` as its one site. The
renaming is extended at the new label, `π[lc ↦ lr]` (`Out`'s label conjunct), and the relation is
compared at the futures of the state after, which may give `lr` any whole member: the positions
from before read no label at or above the reference's counter (`SGood.indep_fresh`), and the
checker's read only labels that occur, which the relation renames below it (`Rel.fresh`).

* `lendState`: the reference state `borrowPlace` leaves, at a root with nothing lent.
* the new temporary's position, value and shape (`pushTemp`, `pushTempShaped`).
* `rel_lend`: the relation after the borrow, under `π[lc ↦ lr]`, the borrow in flight counted.
* `borrow_core`: the step, in (II)'s form.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-! ## A temporary pushed on the reference's top frame -/

namespace SStateB

/-- The position the next temporary of the top frame takes. -/
def newTemp (s : SState) (fr : SFrame) : Pos := .temp s.topIdx fr.temps.length

theorem top_of_last {s : SState} {fr : SFrame} (h : s.env.getLast? = some fr) : s.env[s.topIdx]? = some fr := by
  rw [List.getLast?_eq_getElem?] at h; simpa [SState.topIdx] using h

theorem lookup_pushTemp (s : SState) (v : SVal) {fr : SFrame} (hfr : s.env.getLast? = some fr) (q : Pos) :
    (s.pushTemp v).lookup q = if q = newTemp s fr then some v else s.lookup q := by
  have ht := top_of_last hfr
  cases q with
  | bind f i =>
    rw [if_neg (by simp [newTemp])]
    simp only [SState.lookup, SState.pushTemp, List.getElem?_modify]
    split <;> cases s.env[f]? <;> simp
  | temp f i =>
    simp only [SState.lookup, SState.pushTemp, List.getElem?_modify, newTemp, Pos.temp.injEq]
    by_cases hf : s.topIdx = f
    · subst hf
      rw [ht]
      by_cases hi : i = fr.temps.length
      · subst hi; simp
      · rcases Nat.lt_or_ge i fr.temps.length with h | h
        · simp [hi, List.getElem?_append_left h]
        · have h1 : (fr.temps ++ [v])[i]? = none := List.getElem?_eq_none (by simp; omega)
          have h2 : fr.temps[i]? = none := List.getElem?_eq_none h
          simp [hi, h1, h2]
    · simp [hf]
      intro e; exact absurd e.symm hf

theorem valAt_pushTemp' (s : SState) (v : SVal) {fr : SFrame} (hfr : s.env.getLast? = some fr) (q : Pos) :
    (s.pushTemp v).valAt q = if q = newTemp s fr then v else s.valAt q := by
  rw [SState.valAt_eq, SState.valAt_eq, lookup_pushTemp s v hfr]
  split <;> rfl

theorem mem_positions_pushTemp' (s : SState) (v : SVal) {fr : SFrame} (hfr : s.env.getLast? = some fr) (q : Pos) :
    q ∈ (s.pushTemp v).positions ↔ q = newTemp s fr ∨ q ∈ s.positions := by
  rw [SState.mem_positions, SState.mem_positions, lookup_pushTemp s v hfr]
  split <;> simp_all

theorem newTemp_not_mem (s : SState) {fr : SFrame} (hfr : s.env.getLast? = some fr) : newTemp s fr ∉ s.positions := by
  rw [SState.mem_positions]
  simp [SState.lookup, newTemp, top_of_last hfr]

theorem shape_pushTempShaped (s : SState) (v : SVal) (l : Nat) {fr : SFrame} (hfr : s.env.getLast? = some fr)
    (q : Pos) : (s.pushTempShaped v l).shape q = if q = newTemp s fr then some l else s.shape q := by
  unfold SState.pushTempShaped
  dsimp only
  rw [SState.pushTemp_getLast, hfr]
  simp only [Option.map_some, SState.pushTemp_topIdx, List.length_append, List.length_singleton,
    Nat.add_sub_cancel, newTemp]
  rfl

theorem valAt_pushTempShaped' (s : SState) (v : SVal) (l : Nat) {fr : SFrame} (hfr : s.env.getLast? = some fr)
    (q : Pos) : (s.pushTempShaped v l).valAt q = if q = newTemp s fr then v else s.valAt q := by
  rw [SState.valAt_pushTempShaped, valAt_pushTemp' s v hfr]

theorem mem_positions_pushTempShaped (s : SState) (v : SVal) (l : Nat) {fr : SFrame}
    (hfr : s.env.getLast? = some fr) (q : Pos) :
    q ∈ (s.pushTempShaped v l).positions ↔ q = newTemp s fr ∨ q ∈ s.positions := by
  rw [SState.positions_pushTempShaped, mem_positions_pushTemp' s v hfr]

/-- `setAt` at a binding leaves the last frame's temporaries. -/
theorem getLast_setAt_bind (s : SState) (f j : Nat) (g : SVal) {fr : SFrame} (hfr : s.env.getLast? = some fr) :
    ∃ fr', (s.setAt (.bind f j) g).env.getLast? = some fr' ∧ fr'.temps = fr.temps := by
  simp only [SState.setAt]
  rw [List.getLast?_eq_getElem?, List.length_modify, List.getElem?_modify]
  rw [List.getLast?_eq_getElem?] at hfr
  rw [hfr]
  split
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

theorem topIdx_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).topIdx = s.topIdx := by
  cases p <;> simp [SState.setAt, SState.topIdx]

end SStateB

open SStateB

section
variable {K : RunCtx} {φ : Future}

/-- **The reference state `borrowPlace` leaves at a root with nothing lent**: the counter one up,
the place reading the fresh label's final content, the borrow parked in a temporary holding the
content `a`, the place its one site (a loan), the label's type the place's and its member `a`. -/
noncomputable def lendState (s : SState) (pos : Pos) (a : Sem) : SState :=
  ((((({ s with nextLoan := s.nextLoan + 1 } : SState).setAt pos fun φ' => φ' s.nextLoan).pushTempShaped
    (fun _ => a) s.nextLoan).setLent s.nextLoan [⟨pos, [], false⟩]).setHeldTy s.nextLoan (s.tyAt pos).m).setHeldMem
    s.nextLoan a

/-- **`borrowPlace` at a root with nothing lent.** -/
theorem borrowPlace_root {s : SState} {i : Nat} {pos : Pos} (hres : resolve s (.var i) = some (pos, []))
    (hacc : s.access pos (dataHit []) = s) {a : Sem} (hval : s.valAt pos (s.typedFuture φ) = a) (hw : a.whole) :
    borrowPlace K φ (.var i) s = some ((a, { s.tyAt pos with label := some s.nextLoan }), lendState s pos a) := by
  unfold borrowPlace contentOf
  rw [hres]; simp only; rw [hacc, hval]
  simp [Sem.follow, hw, SState.freshLoan, lendState]
  rfl

variable {s : SState} {f j : Nat} {a : Sem} {frs : SFrame} (hfr : s.env.getLast? = some frs)
  (hpos : Pos.bind f j ∈ s.positions)
include hfr

/-- The new temporary's position. -/
abbrev ntR (s : SState) (frs : SFrame) : Pos := .temp s.topIdx frs.temps.length

theorem lend_last : ∃ fr', ((({ s with nextLoan := s.nextLoan + 1 } : SState).setAt (.bind f j)
    fun φ' => φ' s.nextLoan).env.getLast? = some fr' ∧ fr'.temps = frs.temps) :=
  getLast_setAt_bind ({ s with nextLoan := s.nextLoan + 1 } : SState) f j (fun φ' => φ' s.nextLoan) hfr

omit hfr in
theorem lend_newTemp {fr' : SFrame} (h : fr'.temps = frs.temps) :
    newTemp ((({ s with nextLoan := s.nextLoan + 1 } : SState).setAt (.bind f j) fun φ' => φ' s.nextLoan)) fr' =
      ntR s frs := by
  simp only [newTemp, topIdx_setAt, h]; rfl

theorem lend_mem_positions (q : Pos) :
    q ∈ (lendState s (.bind f j) a).positions ↔ q = ntR s frs ∨ q ∈ s.positions := by
  obtain ⟨fr', h1, h2⟩ := lend_last (f := f) (j := j) hfr
  simp only [lendState, SState.setHeldMem_positions, SState.setHeldTy_positions, SState.setLent_positions]
  rw [mem_positions_pushTempShaped _ _ _ h1, lend_newTemp h2, SState.positions_setAt]
  rfl

theorem lend_shape (q : Pos) :
    (lendState s (.bind f j) a).shape q = if q = ntR s frs then some s.nextLoan else s.shape q := by
  obtain ⟨fr', h1, h2⟩ := lend_last (f := f) (j := j) hfr
  simp only [lendState, SState.setHeldMem_shape, SState.setHeldTy_shape, SState.setLent_shape]
  rw [shape_pushTempShaped _ _ _ h1, lend_newTemp h2, SState.shape_setAt]

include hpos in
theorem lend_valAt (q : Pos) :
    (lendState s (.bind f j) a).valAt q =
      if q = ntR s frs then (fun _ => a) else if q = .bind f j then (fun φ' => φ' s.nextLoan) else s.valAt q := by
  obtain ⟨fr', h1, h2⟩ := lend_last (f := f) (j := j) hfr
  simp only [lendState, SState.setHeldMem_valAt, SState.setHeldTy_valAt, SState.setLent_valAt]
  rw [valAt_pushTempShaped' _ _ _ h1, lend_newTemp h2]
  split
  · rfl
  · split
    · next h => subst h; exact valAt_setAt_self _ _ _ hpos
    · next h => exact SState.valAt_setAt_ne _ _ _ _ (Ne.symm h)

omit hfr in
theorem lend_tyAt (q : Pos) : (lendState s (.bind f j) a).tyAt q = s.tyAt q := by
  simp only [lendState, SState.setHeldMem_tyAt, SState.setHeldTy_tyAt, SState.setLent_tyAt]
  rw [Strict.tyAt_pushTempShaped, Steps.tyAt_setAt]; rfl

end

section
variable {K : RunCtx} {ρ : Assignment}

/-! ## The checker's environment after the borrow: `x ↦ loan_lc`, `borrow_lc w` in flight -/

section
variable {E : Env} {f j : Nat} {fr : Frame}

theorem top_setAtE (hfr : E[E.size - 1]? = some fr) (v : Value) :
    ∃ fr', (Env.setAtE E (.bind f j) v)[(Env.setAtE E (.bind f j) v).size - 1]? = some fr' ∧ fr'.temps = fr.temps := by
  simp only [Env.setAtE, Array.size_modify, Array.getElem?_modify, hfr]
  split <;> exact ⟨_, rfl, rfl⟩

/-- The new temporary's position on the checker's side. -/
abbrev ntC (E : Env) (fr : Frame) : Pos := .temp (E.size - 1) fr.temps.size

variable (hfr : E[E.size - 1]? = some fr) (hx : Pos.bind f j ∈ allPos E)
include hfr

theorem lendE_pos (lc : Nat) (w : Value) :
    allPos (Env.pushTempE (Env.setAtE E (.bind f j) (.loan lc)) (.borrow lc w)) = allPos E ++ [ntC E fr] := by
  obtain ⟨fr', h1, h2⟩ := top_setAtE (f := f) (j := j) hfr (.loan lc)
  have hne : 0 < (Env.setAtE E (.bind f j) (.loan lc)).size := by
    rcases Nat.eq_zero_or_pos (Env.setAtE E (.bind f j) (.loan lc)).size with h | h
    · rw [Array.getElem?_eq_none (by omega)] at h1; cases h1
    · exact h
  rw [allPos_pushTempE _ _ fr' h1 hne, allPos_setAtE, h2]
  simp [Env.setAtE]

include hx in
theorem lendE_valAt (lc : Nat) (w : Value) (q : Pos) :
    valAt (Env.pushTempE (Env.setAtE E (.bind f j) (.loan lc)) (.borrow lc w)) q =
      if q = ntC E fr then .borrow lc w else if q = .bind f j then .loan lc else valAt E q := by
  obtain ⟨fr', h1, h2⟩ := top_setAtE (f := f) (j := j) hfr (.loan lc)
  have hs : (Env.setAtE E (.bind f j) (.loan lc)).size = E.size := by simp [Env.setAtE]
  have hn : ntC E fr = .temp ((Env.setAtE E (.bind f j) (.loan lc)).size - 1) fr'.temps.size := by
    simp [ntC, hs, h2]
  split
  · next h => rw [h, hn]; exact valAt_pushTempE_new _ _ fr' h1
  · next h =>
    have hq : q ≠ .temp ((Env.setAtE E (.bind f j) (.loan lc)).size - 1) fr'.temps.size := by rw [← hn]; exact h
    have e1 : valAt (Env.pushTempE (Env.setAtE E (.bind f j) (.loan lc)) (.borrow lc w)) q =
        valAt (Env.setAtE E (.bind f j) (.loan lc)) q := by
      cases q with
      | bind f' i' => exact valAt_pushTempE_bind _ _ f' i'
      | temp f' i' => exact valAt_pushTempE_old _ _ fr' h1 f' i' hq
    rw [e1]
    split
    · next h' => rw [h']; exact valAt_setAtE_self _ hx
    · next h' => exact valAt_setAtE_other _ _ _ _ h'

theorem lendE_mean (lc : Nat) (w : Value) (χ : Future) {q : Pos} (hq : q ≠ ntC E fr) (hqx : q ≠ .bind f j) :
    Env.mean K.dm K.M K.Γ ρ χ (Env.pushTempE (Env.setAtE E (.bind f j) (.loan lc)) (.borrow lc w)) q =
      Env.mean K.dm K.M K.Γ ρ χ E q := by
  obtain ⟨fr', h1, h2⟩ := top_setAtE (f := f) (j := j) hfr (.loan lc)
  have hs : (Env.setAtE E (.bind f j) (.loan lc)).size = E.size := by simp [Env.setAtE]
  rw [mean_pushTempE_other K.dm K.M K.Γ ρ _ _ fr' h1 q χ (by rw [hs, h2]; exact hq),
    mean_setAtE_other K.dm K.M K.Γ ρ E _ q _ χ hqx]

end

end

/-! ## The relation after the borrow -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- A binding's meaning reads the future only at the loans its value holds. -/
theorem mean_congr_bind (hK : ∀ n, (K.C.global n).2.label = none) {env : Env} {f i : Nat} {χ χ' : Future}
    (h : Pos.bind f i ∈ allPos env → ∀ l, (valAt env (.bind f i)).hasLoanM l = true → χ l = χ' l) :
    Env.mean K.dm K.M K.Γ ρ χ env (.bind f i) = Env.mean K.dm K.M K.Γ ρ χ' env (.bind f i) := by
  by_cases hp : Pos.bind f i ∈ allPos env
  · rw [mean_eq_valAt K.dm K.M K.Γ ρ χ env _ hp, mean_eq_valAt K.dm K.M K.Γ ρ χ' env _ hp, meanV_eq_mean,
      meanV_eq_mean]
    exact meanV_congr K ρ χ χ' _ _ hK (h hp)
  · have e : env[f]?.bind (fun fr : Frame => fr.binds[i]?) = none := by
      rcases e1 : env[f]? with _ | fr
      · rfl
      · simp only [Option.bind_some]
        rcases e2 : fr.binds[i]? with _ | b
        · rfl
        · exact absurd (bind_mem_allPos env f i fr b e1 e2) hp
    simp only [Env.mean, e]

theorem occurs_of_hasLoanM {st : MState} {p : Pos} (hp : p ∈ allPos st.env) {l : Nat}
    (h : (valAt st.env p).hasLoanM l = true) : st.Occurs l :=
  ⟨_, List.mem_map_of_mem hp, Value.anyAtom_mono (fun a ha => by simp [ha]) _ h⟩

theorem loan_beq_loan {a b : Nat} (h : (Value.loan a == Value.loan b) = true) : a = b := by
  have h' : (a == b) = true := h
  exact beq_iff_eq.mp h'

theorem borrow_beq_loan {a b : Nat} {w : Value} : (Value.borrow a w == Value.loan b) = false := rfl

/-- The renaming extended at one label. -/
def renameAt (π : Nat → Nat) (lc lr : Nat) : Nat → Nat := fun l => if l = lc then lr else π l

theorem skel_pushTempShaped (s : SState) (v : SVal) (l : Nat) :
    (s.pushTempShaped v l).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel) := by
  have h : (s.pushTemp v).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel) := by
    simp only [SState.pushTemp]
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_map, List.getElem?_modify]
    split <;> cases s.env[k]? <;> rfl
  unfold SState.pushTempShaped; dsimp only; split <;> exact h

theorem skel_lend (s : SState) (pos : Pos) (a : Sem) :
    (lendState s pos a).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel) := by
  simp only [lendState, SState.setHeldMem_env, SState.setHeldTy_env, SState.setLent_env]
  rw [skel_pushTempShaped, skel_setAt]

theorem lend_nextLoan (s : SState) (pos : Pos) (a : Sem) : (lendState s pos a).nextLoan = s.nextLoan + 1 := by
  simp only [lendState, SState.setHeldMem_nextLoan, SState.setHeldTy_nextLoan, SState.setLent_nextLoan]
  rw [SState.nextLoan_pushTempShaped, SState.nextLoan_setAt']

theorem lend_lent (s : SState) (pos : Pos) (a : Sem) :
    (lendState s pos a).lent s.nextLoan = [⟨pos, [], false⟩] := by
  simp [lendState, SState.setHeldMem, SState.setHeldTy, SState.setLent]

theorem lend_heldMem (s : SState) (pos : Pos) (a : Sem) : (lendState s pos a).heldMem s.nextLoan = a := by
  simp [lendState, SState.setHeldMem]

theorem lend_heldTy (s : SState) (pos : Pos) (a : Sem) : (lendState s pos a).heldTy s.nextLoan = (s.tyAt pos).m := by
  simp [lendState, SState.setHeldMem, SState.setHeldTy]

/-- The checker's environment after `&x`: `x ↦ loan_lc`, `borrow_lc w` in flight. -/
abbrev lendE (E : Env) (x : Pos) (lc : Nat) (w : Value) : Env := Env.pushTempE (Env.setAtE E x (.loan lc)) (.borrow lc w)

/-- **The relation after `&x`** (`x` a binding holding a number, nothing live): the checker's `x`
holds `loan_lc` and `borrow_lc w` is in flight; the reference is `borrowPlace`'s state; the renaming
sends `lc` to the reference's fresh label. -/
theorem rel_lend (hK : ∀ n, (K.C.global n).2.label = none) {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) (hS : Strict.SGood K.dm K.Γ φ s) (hlab : ∀ l, st.Occurs l → l < st.nextLoan)
    (hnl : ∀ l, liveLoan st.env l = false)
    (hfs : ∀ q ∈ allPos st.env, (valAt st.env q).sitesOf st.nextLoan q [] = [])
    {fr : Frame} (hfr : st.env[st.env.size - 1]? = some fr) {f j : Nat}
    {b : Binding} (hlk : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) (hnum : b.val.Num) {m : Nat}
    (hmv : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint b.val = .el0 Nat m)
    (hTy : (s.tyAt (.bind f j)).m = TyM.nat) :
    Rel K ρ φ (renameAt π st.nextLoan s.nextLoan)
      { st with env := lendE st.env (.bind f j) st.nextLoan b.val, nextLoan := st.nextLoan + 1 }
      (lendState s (.bind f j) (.el0 Nat m)) := by
  -- the reference's top frame
  obtain ⟨frs, hfrs, htop, -⟩ := skel_align K ρ st s hr.skel fr hfr
  have hlast : s.env.getLast? = some frs := by
    rw [List.getLast?_eq_getElem?]; simpa [SState.topIdx] using hfrs
  -- `x`
  obtain ⟨fr₀, e₀, hb₀⟩ : ∃ fr₀, st.env[f]? = some fr₀ ∧ fr₀.binds[j]? = some b := by
    rcases e : st.env[f]? with _ | fr₀
    · rw [e] at hlk; cases hlk
    · rw [e] at hlk; simp only [Option.bind_some] at hlk; exact ⟨fr₀, rfl, hlk⟩
  have hx : Pos.bind f j ∈ allPos st.env := bind_mem_allPos _ f j fr₀ b e₀ hb₀
  have hxv : valAt st.env (.bind f j) = b.val := by
    rw [valAt_bind_eq, e₀, Option.getD_some, hb₀, Option.getD_some]
  have hxs : Pos.bind f j ∈ s.positions := (rel_bind_ty hr hlk).1
  have hntx : ntC st.env fr ≠ .bind f j := by simp [ntC]
  have hntE : ntC st.env fr ∉ allPos st.env := fun h => by
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ h
    rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
  -- nothing live on either side before
  have hnoS : ∀ l, ¬ s.Live l := fun l hl => by
    obtain ⟨l₀, h₀, -⟩ := rel_live_ref K ρ φ st s π hr hl
    rw [hnl] at h₀; cases h₀
  have hshS : ∀ q, s.shape q = none := fun q => by
    rcases e : s.shape q with _ | l
    · rfl
    · exact absurd ((SState.live_iff s l).mpr ⟨q, hr.holders q l e, e⟩) (hnoS l)
  have hnoB : ∀ q l, q ∈ allPos st.env → (valAt st.env q).holdsBorrow l = false := fun q l hq => by
    cases e : (valAt st.env q).holdsBorrow l with
    | false => rfl
    | true =>
      have : liveLoan st.env l = true := by
        unfold liveLoan findBorrow
        exact List.find?_isSome.mpr ⟨q, hq, e⟩
      rw [hnl] at this; cases this
  -- the checker's side after
  have hpos2 := lendE_pos (f := f) (j := j) hfr st.nextLoan b.val
  have hval2 := lendE_valAt (f := f) (j := j) hfr hx st.nextLoan b.val
  have hsh2 : ∀ q, Env.shape (lendE st.env (.bind f j) st.nextLoan b.val) q =
      if q = ntC st.env fr then some st.nextLoan else none := fun q => by
    rw [shape_eq_shapeOf, hval2]
    split
    · rfl
    · split
      · rfl
      · rcases e : shapeOf (valAt st.env q) with _ | l
        · rfl
        · exfalso
          have hq : q ∈ allPos st.env := mem_allPos_of_shape (l := l) (by rw [shape_eq_shapeOf]; exact e)
          have : (valAt st.env q).holdsBorrow l = true := by
            generalize valAt st.env q = v at e
            cases v <;> simp [shapeOf] at e
            subst e; simp [Value.holdsBorrow]
          rw [hnoB q l hq] at this; cases this
  -- the reference's side after
  have hsh' : ∀ q, (lendState s (.bind f j) (.el0 Nat m)).shape q = if q = ntR s frs then some s.nextLoan else none :=
    fun q => by rw [lend_shape hlast, hshS]
  have hlive' : ∀ l, (lendState s (.bind f j) (.el0 Nat m)).Live l ↔ l = s.nextLoan := fun l => by
    rw [SState.live_iff]
    constructor
    · rintro ⟨q, -, hq⟩; rw [hsh'] at hq; split at hq <;> cases hq; rfl
    · rintro rfl; exact ⟨ntR s frs, (lend_mem_positions hlast _).mpr (.inl rfl), by rw [hsh']; simp⟩
  have hval' := lend_valAt (a := .el0 Nat m) hlast hxs
  -- the futures the relation compares at, after: `φ` but at the new label
  have hF : ∀ ψ, RelF φ (lendState s (.bind f j) (.el0 Nat m)) ψ → ψ = φ.upd s.nextLoan (ψ s.nextLoan) := fun ψ h => by
    funext l
    by_cases e : l = s.nextLoan
    · subst e; simp [Future.upd]
    · rw [h l (fun h' => e ((hlive' l).mp h'))]; simp [Future.upd, e]
  have hlt : ∀ l, st.Occurs l → π l < s.nextLoan := fun l h => hr.fresh l (hlab l h) h
  have hπold : ∀ l, st.Occurs l → renameAt π st.nextLoan s.nextLoan l = π l := fun l h => by
    simp [renameAt, Nat.ne_of_lt (hlab l h)]
  have hπnew : renameAt π st.nextLoan s.nextLoan st.nextLoan = s.nextLoan := by simp [renameAt]
  -- occurrences after
  have hocc : ∀ l, ({ st with env := lendE st.env (.bind f j) st.nextLoan b.val, nextLoan := st.nextLoan + 1 } : MState).Occurs l → l = st.nextLoan ∨ st.Occurs l := by
    rintro l ⟨v, hv, ha⟩
    simp only [Env.values, hpos2, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_map, List.mem_singleton] at hv
    rcases hv with ⟨q, hq, rfl⟩ | rfl
    · rw [hval2, if_neg (show q ≠ ntC st.env fr from fun e => hntE (by rw [← e]; exact hq))] at ha
      split at ha
      · left
        simp only [Value.anyAtom, Bool.or_false] at ha
        revert ha
        cases hd : (st.nextLoan == l)
        · have : (Value.loan st.nextLoan == Value.loan l) = false := hd
          simp [this]
        · intro _; exact (beq_iff_eq.mp hd).symm
      · exact .inr ⟨_, List.mem_map_of_mem hq, ha⟩
    · rw [hval2, if_pos rfl] at ha
      simp only [Value.anyAtom, Bool.or_eq_true, borrow_beq_loan, Bool.false_or] at ha
      rcases ha with ha | ha
      · exact .inl (beq_iff_eq.mp ha).symm
      · rw [hnum.inert.anyAtom _ (by rfl) (by rfl) (fun _ => by rfl)] at ha; cases ha
  have hntE2 : ntC st.env fr ∈ allPos (lendE st.env (.bind f j) st.nextLoan b.val) := by
    rw [hpos2]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hxE2 : Pos.bind f j ∈ allPos (lendE st.env (.bind f j) st.nextLoan b.val) := by
    rw [hpos2]; exact List.mem_append_left _ hx
  have hlive2 : ∀ l, liveLoan (lendE st.env (.bind f j) st.nextLoan b.val) l = true → l = st.nextLoan := by
    intro l hl
    unfold liveLoan findBorrow at hl
    obtain ⟨p, hp, hb⟩ := List.find?_isSome.mp hl
    rw [hval2] at hb
    split at hb
    · simp only [Value.holdsBorrow, Bool.or_eq_true, beq_iff_eq, hnum.holdsBorrow] at hb
      rcases hb with hb | hb
      · exact hb.symm
      · cases hb
    · split at hb
      · simp [Value.holdsBorrow] at hb
      · next h1 h2 =>
        have hp' : p ∈ allPos st.env := by
          rw [hpos2, List.mem_append, List.mem_singleton] at hp; exact hp.resolve_right h1
        rw [hnoB p l hp'] at hb; cases hb
  have hmeanX : ∀ χ : Future,
      Env.mean K.dm K.M K.Γ ρ χ (lendE st.env (.bind f j) st.nextLoan b.val) (.bind f j) = χ st.nextLoan := by
    intro χ
    rw [mean_eq_valAt K.dm K.M K.Γ ρ χ _ _ hxE2, hval2, if_neg hntx.symm, if_pos rfl]; rfl
  have hmeanN : ∀ χ : Future,
      Env.mean K.dm K.M K.Γ ρ χ (lendE st.env (.bind f j) st.nextLoan b.val) (ntC st.env fr) = .el0 Nat m := by
    intro χ
    rw [mean_eq_valAt K.dm K.M K.Γ ρ χ _ _ hntE2, hval2, if_pos rfl]; exact hmv _ _ _ _ _ _
  have htopf : ∀ f' : Nat, f' = st.env.size - 1 → f' = s.topIdx := fun f' h => by rw [htop]; exact h
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun p q l hp hq => ?_⟩
  · -- skel
    have h1 := skel_pushTempE K ρ ({ st with env := Env.setAtE st.env (.bind f j) (.loan st.nextLoan), nextLoan := st.nextLoan + 1 } : MState) (.borrow st.nextLoan b.val)
    have h2 := skel_setAtE K ρ ({ st with nextLoan := st.nextLoan + 1 } : MState) f j (.loan st.nextLoan)
    have h3 : (SM' K ρ ({ st with nextLoan := st.nextLoan + 1 } : MState)).env.map (fun fr => fr.binds.map bindSkel) =
        (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) := rfl
    exact h1.trans (h2.trans (h3.trans (hr.skel.trans (skel_lend s _ _).symm)))
  · -- fresh
    intro l _ ho
    rw [lend_nextLoan]
    rcases hocc l ho with rfl | h
    · rw [hπnew]; exact Nat.lt_succ_self _
    · rw [hπold l h]; exact Nat.lt_succ_of_lt (hlt l h)
  · -- the bindings mean the same
    intro ψ hψ p hp
    cases p with
    | temp => exact absurd trivial hp
    | bind f' i' =>
      have hψe := hF ψ hψ.1
      show Env.mean K.dm K.M K.Γ ρ _ (lendE st.env (.bind f j) st.nextLoan b.val) (.bind f' i') = _
      rw [hval']
      by_cases hpx : Pos.bind f' i' = .bind f j
      · rw [hpx, hmeanX, if_neg (by simp [ntR]), if_pos rfl, hπnew]
      · rw [if_neg (by simp [ntR]), if_neg hpx, lendE_mean (f := f) (j := j) hfr _ _ _ (by simp [ntC]) hpx]
        have hc : Env.mean K.dm K.M K.Γ ρ (fun l => ψ (renameAt π st.nextLoan s.nextLoan l)) st.env (.bind f' i') =
            Env.mean K.dm K.M K.Γ ρ (fun l => φ (π l)) st.env (.bind f' i') := by
          apply mean_congr_bind hK
          intro hp' l hl
          have ho := occurs_of_hasLoanM hp' hl
          show ψ _ = φ _
          rw [hπold l ho, hψe]
          simp [Future.upd, Nat.ne_of_lt (hlt l ho)]
        have h0 : Env.mean K.dm K.M K.Γ ρ (fun l => φ (π l)) st.env (.bind f' i') = s.valAt (.bind f' i') φ :=
          hr.sim.1 φ ⟨fun _ _ => rfl, fun l hl => absurd hl (hnoS l)⟩ _ hp
        rw [hc, h0, hψe]
        exact (hS.indep_fresh _ (Nat.le_refl _) φ _).symm
  · -- the checker's bindings hold no borrow
    intro p l hp h
    have h' : Env.shape (lendE st.env (.bind f j) st.nextLoan b.val) p = some l := h
    rw [hsh2, if_neg (fun e => hp (by rw [e]; exact trivial))] at h'; cases h'
  · -- the reference's bindings hold no borrow
    intro p l' hp h
    rw [hsh', if_neg (fun e => hp (by rw [e]; exact trivial))] at h; cases h
  · -- the borrow in flight, on both sides
    intro f' i l h
    have h' : Env.shape (lendE st.env (.bind f j) st.nextLoan b.val) (.temp f' i) = some l := h
    rw [hsh2] at h'
    split at h'
    · next he =>
      cases h'
      have hf' : f' = st.env.size - 1 := by simp [ntC] at he; exact he.1
      refine ⟨frs.temps.length, ?_, fun ψ _ => ?_⟩
      · rw [hsh', if_pos (by simp [ntR, htopf f' hf']), hπnew]
      · show Env.mean K.dm K.M K.Γ ρ _ (lendE st.env (.bind f j) st.nextLoan b.val) (.temp f' i) = _
        rw [he, hmeanN, hval', if_pos (by simp [ntR, htopf f' hf'])]
    · cases h'
  · intro f' j' l' h
    rw [hsh'] at h
    split at h
    · next he =>
      cases h
      have hf' : f' = s.topIdx := by simp [ntR] at he; exact he.1
      refine ⟨fr.temps.size, st.nextLoan, ?_, hπnew⟩
      show Env.shape (lendE st.env (.bind f j) st.nextLoan b.val) _ = _
      rw [hsh2, if_pos (by simp [ntC, hf', htop])]
    · cases h
  · -- one live label on each side
    intro l l' hl hl' _
    rw [hlive2 l hl, hlive2 l' hl']
  · -- it is lent at `x`, as a loan, on both sides
    intro l hl x'
    obtain rfl := hlive2 l hl
    rw [hπnew, lend_lent]
    simp only [List.mem_singleton, Env.sitesOf, List.mem_flatMap]
    constructor
    · rintro rfl
      refine ⟨.bind f j, hxE2, ?_⟩
      rw [hval2, if_neg hntx.symm, if_pos rfl]; simp [Value.sitesOf]
    · rintro ⟨p, hp, hx'⟩
      rw [hval2] at hx'
      split at hx'
      · simp [Value.sitesOf, hnum.sitesOf] at hx'
      · split at hx'
        · next h1 h2 => subst h2; simpa [Value.sitesOf] using hx'
        · next h1 h2 =>
          have hp' : p ∈ allPos st.env := by
            rw [hpos2, List.mem_append, List.mem_singleton] at hp; exact hp.resolve_right h1
          rw [hfs p hp'] at hx'; cases hx'
  · -- the reference holds its borrows at its positions
    intro p l h
    rw [hsh'] at h
    split at h
    · next he => exact (lend_mem_positions hlast p).mpr (.inl he)
    · cases h
  · -- the new label's record is the borrowed content, a whole member of `Nat`
    intro l hl
    obtain rfl := (hlive' l).mp hl
    obtain ⟨r, hr'⟩ := SState.holderOf_of_live hl
    have hrs := (SState.holderOf_spec hr').2
    rw [hsh'] at hrs
    have hrn : r = ntR s frs := by split at hrs; assumption; cases hrs
    rw [lend_heldMem]
    refine ⟨by simp [Sem.whole], ?_⟩
    unfold holderTy; rw [hr', hrn]
    show Sem.el0 Nat m ∈ₛ[K.dm.read] (lendState s (.bind f j) (.el0 Nat m)).heldTy s.nextLoan
    rw [lend_heldTy, hTy]; exact ⟨m, rfl⟩
  · -- one holder: the new temporary
    rw [hsh'] at hp hq
    split at hp
    · split at hq
      · next h1 h2 => rw [h1, h2]
      · cases hq
    · cases hp

end

/-! ## The step: `&x` at `evalCore` -/

theorem refd_withTempT_noAbs {st : MState} {v : Value} (hv : ∀ σ, v.hasAbs σ = false) (T? : Option Value) :
    ∀ σ, (st.withTempT v T?).norm.Refd σ → st.norm.Refd σ := by
  intro σ h
  induction h with
  | val w hw hab =>
    rcases values_withTempT_norm st v T? w hw with hw | rfl
    · exact .val w hw hab
    · rw [hv] at hab; cases hab
  | ty f i b T hb hT hab =>
    rw [binds_withTempT_norm] at hb
    exact .ty f i b T hb hT hab
  | lazyTy f i b P ws j hb hT hab =>
    rw [binds_withTempT_norm] at hb
    exact .lazyTy f i b P ws j hb hT hab
  | goal G hG hab => exact .goal G hG hab
  | neutral n σ' hn hab => exact .neutral n σ' hn hab
  | eta σ' w he hab => exact .eta σ' w he hab
  | dep σ' T _ hT hab ih => exact .dep σ' T ih hT hab

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The borrow clause of the strict run, where the aligned table does not erase it. -/
theorem runT_borrow (tl : Bool) (hint : TyS) (p : Place) (s : SState)
    (hfl : K.D.flags (scopeOf s) (.borrow p) = (false, false)) :
    runT K ρ φ tl hint (.borrow p) s =
      match SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s with
      | some (r, s₁) =>
        if InvalidateOk K φ p s₁ ∧ lentOk K φ p (invalidate K φ p s₁) then some (r, invalidate K φ p s₁) else none
      | none => none := by
  rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl]; rfl

theorem lentOk_var (i : Nat) (s : SState) : lentOk K φ (.var i) s := by
  unfold lentOk resolve
  simp only [Place.steps]
  cases s.varPos i <;> simp

/-- **The precondition of `&x`**: `x` a top-frame variable bound at `Nat` to a number; no live borrow
anywhere; no site of a label at or above the counter. -/
def BorrowPre (i : Nat) (st : MState) : Prop :=
  NumVar i st ∧ (∀ l, liveLoan st.env l = false) ∧
    ∀ q ∈ allPos st.env, ∀ l, st.nextLoan ≤ l → (valAt st.env q).sitesOf l q [] = []

/-- **`&x` at `evalCore`**, for `x` a top-frame variable bound at `Nat` to a number, nothing live
(`BorrowPre`). The strict run's tests pass: the access ends nothing; the content, the number, is a
member of `Nat`; the invalidation is empty; the write is at a root. The renaming is extended at the
new label, and the result's label is the checker's, renamed. -/
theorem borrow_core (hB : BorrowNumInv) (hIC : InvCore) {n i : Nat} {P : MState → Prop}
    (hP : ∀ st, P st → BorrowPre i st) (hinv : ∀ sc, K.D.invalidated sc (.var i) = []) :
    CoreSim K ρ φ (n + 1) (.borrow (.var i)) P (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd _ hp hr hS hv hab hnh hfl _ hD bh h
  subst hty
  obtain ⟨⟨f, j, b, hpos, hlk, hnum, htyb⟩, hnl, hfs⟩ := hP st hPst
  obtain ⟨-, st₁, hq, rfl, rfl, hk⟩ := hB n i hint st st' bh v T? f j b K.D hm hpos hlk hnum htyb hD h
  -- the checker's state after the quiet step: the same Ω up to temporaries' types
  have hlk₁ : st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
    rw [← lookup_erase, ← hq.env, lookup_erase]; exact hlk
  have hnl₁ : ∀ l, liveLoan st₁.env l = false := fun l => by
    rw [← liveLoan_erase, ← hq.env, liveLoan_erase]; exact hnl l
  have hfs₁ : ∀ q ∈ allPos st₁.env, (valAt st₁.env q).sitesOf st₁.nextLoan q [] = [] := fun q hq' => by
    rw [← allPos_erase, ← hq.env, allPos_erase] at hq'
    rw [← valAt_erase, ← hq.env, valAt_erase]
    exact hfs q hq' _ hq.nextLoan
  have hocc₁ : ∀ l, st₁.Occurs l ↔ st.Occurs l := fun l =>
    (occurs_erase st₁ l).symm.trans ((occurs_of_env (st := { st with env := st.env.erase })
      (st' := { st₁ with env := st₁.env.erase }) hq.env.symm l).trans (occurs_erase st l))
  have hlab₁ : ∀ l, st₁.Occurs l → l < st₁.nextLoan := fun l h' =>
    Nat.lt_of_lt_of_le (hp.labels l ((hocc₁ l).mp h')) hq.nextLoan
  obtain ⟨fr, hfr⟩ : ∃ fr, st₁.env[st₁.env.size - 1]? = some fr := by
    have : 0 < st₁.env.size := by
      rcases e : st₁.env[f]? with _ | fr₀
      · rw [e] at hlk₁; cases hlk₁
      · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp e).1
    exact ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  have hr₁ : Rel K ρ φ π st₁ s := hr.of_quiet hq hp.labels
  -- `x` on the reference's side: the same position, at `Nat`, meaning the number, nothing lent there
  obtain ⟨m, hmv⟩ := hnum.vmean
  have hTy : (s.tyAt (.bind f j)).m = TyM.nat := by
    rw [(rel_bind_ty hr hlk).2]; simp only [Env.hintAt, hlk, htyb]; rfl
  have hres : resolve s (.var i) = some (.bind f j, []) := rel_resolve_ck K ρ φ st s π (.var i) _ hr hpos
  have hns : ∀ l, (valAt st.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by
    have : valAt st.env (.bind f j) = b.val := by
      rw [valAt_bind_eq]; rcases e : st.env[f]? with _ | fr₀
      · rw [e] at hlk; cases hlk
      · rw [e] at hlk; simp only [Option.bind_some] at hlk; simp [e, hlk]
    rw [this]; exact hnum.sitesOf l _ _
  have hacc : s.access (.bind f j) (dataHit []) = s := access_noSites (rel_noSites_at hr hns)
  have haok : AccessOk K φ s (.bind f j) (dataHit []) := accessOk_noSites (rel_noSites_at hr hns)
  have hval : s.valAt (.bind f j) (s.typedFuture φ) = .el0 Nat m := by
    rw [← hr.sim.1 _ ⟨relF_typedFuture φ s, hr.typedFuture_typed φ⟩ (.bind f j) (by simp [IsTemp])]
    exact mean_numVar hlk hmv _
  -- the reference's run
  have hbp := borrowPlace_root (K := K) (φ := φ) hres hacc hval (by simp [Sem.whole])
  have hxr : runT K ρ φ st.curTail (hintM K ρ hint) (.borrow (.var i)) s =
      some ((.el0 Nat m, { s.tyAt (.bind f j) with label := some s.nextLoan }), lendState s (.bind f j) (.el0 Nat m)) := by
    rw [runT_borrow _ _ _ s hfl]
    have hg : SM.guarded (ContentOk K φ (.var i)) (borrowPlace K φ (.var i)) s =
        some ((.el0 Nat m, { s.tyAt (.bind f j) with label := some s.nextLoan }), lendState s (.bind f j) (.el0 Nat m)) := by
      rw [SM.guarded_of (by unfold ContentOk; rw [hres]; exact haok), hbp]
    have hst : SM.strictS K.dm.read (SM.guarded (ContentOk K φ (.var i)) (borrowPlace K φ (.var i))) s =
        some ((.el0 Nat m, { s.tyAt (.bind f j) with label := some s.nextLoan }), lendState s (.bind f j) (.el0 Nat m)) := by
      unfold SM.strictS; rw [hg]; simp only; rw [if_pos (by show Sem.el0 Nat m ∈ₛ[K.dm.read] (s.tyAt (.bind f j)).m; rw [hTy]; exact ⟨m, rfl⟩)]
    rw [hst]
    simp only
    have hi : invalidate K φ (.var i) (lendState s (.bind f j) (.el0 Nat m)) = lendState s (.bind f j) (.el0 Nat m) := by
      unfold invalidate; rw [hinv]; rfl
    rw [hi, if_pos ⟨by unfold InvalidateOk; rw [hinv]; trivial, lentOk_var i _⟩]
  -- the relation after
  have hR := rel_lend hp.ctx.noLabel hr₁ hS hlab₁ hnl₁ hfs₁ hfr hlk₁ hnum hmv hTy
  have hbAbs : ∀ σ, (Value.borrow st₁.nextLoan b.val).hasAbs σ = false := fun σ => by
    show ((Value.borrow st₁.nextLoan b.val == Value.abs σ) || b.val.anyAtom (· == .abs σ)) = false
    rw [show (Value.borrow st₁.nextLoan b.val == Value.abs σ) = false from rfl]
    exact hnum.hasAbs σ
  refine ⟨ρ, K.Δ, renameAt π st₁.nextLoan s.nextLoan, _, _, ⟨?_, ?_, fun _ _ => ⟨rfl, rfl⟩, ?_⟩, hxr, ?_,
    fun T hT => ?_, ?_, ?_, ?_⟩
  · rw [← hk.absTy]; exact hq.absSize
  · rw [← hk.nextLoan]; exact Nat.le_succ_of_le hq.nextLoan
  · intro l hl
    have : l ≠ st₁.nextLoan := Nat.ne_of_lt (Nat.lt_of_lt_of_le hl hq.nextLoan)
    simp [renameAt, this]
  · show meanV _ ρ _ _ (Value.borrow st₁.nextLoan b.val) = .el0 Nat m
    rw [← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  · cases hT
    show _ = (s.tyAt (.bind f j)).m
    rw [hTy]; rfl
  · simp [Value.heldLabel, renameAt]
  · refine ⟨hp.ctx.of_eq ?_ ?_, ?_, ?_⟩
    · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
    · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
    · exact hIC (n + 1) true _ hint st st' bh _ _ K.D K.Γ (.borrow i) hp.inv hD h
    · have hA₁ : Asg K ρ st₁.norm := Asg.of_quiet hq hp.asg hp.inv.wf6
      have hX : Asg K ρ (({ st₁ with env := Env.setAtE st₁.env (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } : MState).withTempT (.borrow st₁.nextLoan b.val) (some (.tRef .tNat))).norm := by
        refine hA₁.of_refd rfl rfl rfl rfl rfl fun σ hσ => ?_
        have h1 := refd_withTempT_noAbs (st := ({ st₁ with env := Env.setAtE st₁.env (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } : MState)) hbAbs _ σ hσ
        refine refd_sub (st := st₁) (st' := ({ st₁ with env := Env.setAtE st₁.env (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } : MState)) rfl rfl rfl rfl ?_ ?_ ?_ σ h1
        · intro w' hw' σ' hσ'
          rcases mem_values_setAtE hw' with rfl | hw''
          · exact absurd hσ' (by rw [show (Value.loan st₁.nextLoan).hasAbs σ' = false from rfl]; simp)
          · exact ⟨w', hw'', hσ'⟩
        · intro f' i' b' T σ' hb' hT hσ'
          obtain ⟨b'', hb'', hty'', -⟩ := lookup_setAtE hb'
          exact .ty f' i' b'' T (by rw [show st₁.norm.env = st₁.env.erase from rfl, lookup_erase]; exact hb'')
            (by rw [hty'']; exact hT) hσ'
        · intro f' i' b' P ws j' σ' hb' hl hσ'
          obtain ⟨b'', hb'', -, hlz''⟩ := lookup_setAtE hb'
          exact .lazyTy f' i' b'' P ws j' (by rw [show st₁.norm.env = st₁.env.erase from rfl, lookup_erase]; exact hb'')
            (by rw [hlz'']; exact hl) hσ'
      rw [(hk.withTempT _ _).norm] at hX
      exact hX
  · have h1 := Rel.of_kern (kern_withTemp ({ st₁ with env := Env.setAtE st₁.env (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } : MState) (.borrow st₁.nextLoan b.val) (some (.tRef .tNat))) hR
    exact Rel.of_kern (hk.withTempT _ _) h1

end

end Ochr.Meaning.Steps.Form
