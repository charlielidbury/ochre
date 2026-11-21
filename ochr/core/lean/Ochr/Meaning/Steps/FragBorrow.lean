import Ochr.Meaning.Steps.FragPush
import Ochr.Meaning.Steps.ColumnBorrow

/-!
# `&x` in the fragment (lead12)

`ColumnBorrow.rel_lend` related the states after `&x` where no borrow was live anywhere (`hnl`).
Here the same with other borrows live (`rel_lendG`): every other label keeps its holder, its sites
and its record; liveness and the holders' types are compared through `SState.Uniq`, as
`FragPush.rel_pushBind_borrowG` does. Then the case `&x` of the fragment (`borF_core`): `x` a number
(`BorrowNumInv`), lent (`BorrowLentInv`: the end, `FragEnd.rel_end`, then the lend), or moved
(`BorrowBotInv`: the run fails).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical
open SStateB

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- A position's meaning reads the future only at the loans its value holds (`mean_congr_bind` at any
position of the environment). -/
theorem mean_congr_pos (hK : ∀ n, (K.C.global n).2.label = none) {env : Env} {q : Pos} (hq : q ∈ allPos env)
    {χ χ' : Future} (h : ∀ l, (valAt env q).hasLoanM l = true → χ l = χ' l) :
    Env.mean K.dm K.M K.Γ ρ χ env q = Env.mean K.dm K.M K.Γ ρ χ' env q := by
  rw [mean_eq_valAt K.dm K.M K.Γ ρ χ env _ hq, mean_eq_valAt K.dm K.M K.Γ ρ χ' env _ hq, meanV_eq_mean,
    meanV_eq_mean]
  exact meanV_congr K ρ χ χ' _ _ hK h

theorem lent_pushTempShaped (s : SState) (v : SVal) (l : Nat) : (s.pushTempShaped v l).lent = s.lent := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem lend_lent_ne (s : SState) (pos : Pos) (a : Sem) {L : Nat} (hL : L ≠ s.nextLoan) :
    (lendState s pos a).lent L = s.lent L := by
  simp only [lendState, SState.setHeldMem, SState.setHeldTy, SState.setLent, if_neg hL]
  rw [lent_pushTempShaped, SState.lent_setAt]

theorem lend_heldMem_ne (s : SState) (pos : Pos) (a : Sem) {L : Nat} (hL : L ≠ s.nextLoan) :
    (lendState s pos a).heldMem L = s.heldMem L := by
  simp only [lendState, SState.setHeldMem, SState.setHeldTy, SState.setLent, if_neg hL, Strict.heldMem_pushTempShaped,
    Strict.heldMem_setAt]

theorem lend_heldTy_ne (s : SState) (pos : Pos) (a : Sem) {L : Nat} (hL : L ≠ s.nextLoan) :
    (lendState s pos a).heldTy L = s.heldTy L := by
  simp only [lendState, SState.setHeldMem, SState.setHeldTy, SState.setLent, if_neg hL, Strict.heldTy_pushTempShaped,
    Strict.heldTy_setAt]

/-- **The relation after `&x`, other borrows live** (`ColumnBorrow.rel_lend` without its `hnl`): the
checker's `x` (a binding holding a number) holds `loan_lc` and `borrow_lc w` is in flight; the reference
is `borrowPlace`'s state; the renaming sends `lc` to the reference's fresh label. Every other label
keeps its holder (compared through `SState.Uniq`), its sites and its record. -/
theorem rel_lendG (hK : ∀ n, (K.C.global n).2.label = none) {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) (hS : Strict.SGood K.dm K.Γ φ s) (hlab : ∀ l, st.Occurs l → l < st.nextLoan)
    (hoccL : ∀ l, liveLoan st.env l = true → st.Occurs l)
    (hfs : ∀ q ∈ allPos st.env, (valAt st.env q).sitesOf st.nextLoan q [] = [])
    {fr : Frame} (hfr : st.env[st.env.size - 1]? = some fr) {f j : Nat} {w : Value}
    (hx : Pos.bind f j ∈ allPos st.env) (hxv : valAt st.env (.bind f j) = w) (hxs : Pos.bind f j ∈ s.positions)
    (hnum : w.Num) {m : Nat}
    (hmv : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint w = .el0 Nat m)
    (hTy : (s.tyAt (.bind f j)).m = TyM.nat) :
    Rel K ρ φ (renameAt π st.nextLoan s.nextLoan)
      { st with env := lendE st.env (.bind f j) st.nextLoan w, nextLoan := st.nextLoan + 1 }
      (lendState s (.bind f j) (.el0 Nat m)) := by
  obtain ⟨frs, hfrs, htop, -⟩ := skel_align K ρ st s hr.skel fr hfr
  have hlast : s.env.getLast? = some frs := by
    rw [List.getLast?_eq_getElem?]; simpa [SState.topIdx] using hfrs
  have hntx : ntC st.env fr ≠ .bind f j := by simp [ntC]
  have hntE : ntC st.env fr ∉ allPos st.env := fun h => by
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ h
    rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
  have hntS : ntR s frs ∉ s.positions := newTemp_not_mem s hlast
  have huniq : s.Uniq := hS.uniq
  have hliveS : ∀ L, s.Live L → L < s.nextLoan := fun L h => hS.live_lt h
  have hliveC : ∀ l, liveLoan st.env l = true → l < st.nextLoan := fun l h => hlab l (hoccL l h)
  have hlt : ∀ l, st.Occurs l → π l < s.nextLoan := fun l h => hr.fresh l (hlab l h) h
  have hπold : ∀ l, l < st.nextLoan → renameAt π st.nextLoan s.nextLoan l = π l := fun l h => by
    simp [renameAt, Nat.ne_of_lt h]
  have hπnew : renameAt π st.nextLoan s.nextLoan st.nextLoan = s.nextLoan := by simp [renameAt]
  have htopf : ∀ f' : Nat, f' = st.env.size - 1 → f' = s.topIdx := fun f' h => by rw [htop]; exact h
  -- the checker's side after
  have hpos2 := lendE_pos (f := f) (j := j) hfr st.nextLoan w
  have hval2 := lendE_valAt (f := f) (j := j) hfr hx st.nextLoan w
  have hsh2 : ∀ q, Env.shape (lendE st.env (.bind f j) st.nextLoan w) q =
      if q = ntC st.env fr then some st.nextLoan else Env.shape st.env q := fun q => by
    rw [shape_eq_shapeOf, hval2, shape_eq_shapeOf]
    split
    · rfl
    · split
      · next h => rw [h, hxv]; clear hmv hxv; cases hnum <;> rfl
      · rfl
  obtain ⟨fr', hfr', -⟩ := top_setAtE (f := f) (j := j) hfr (.loan st.nextLoan)
  have hsz : (Env.setAtE st.env (.bind f j) (.loan st.nextLoan)).size = st.env.size := by simp [Env.setAtE]
  have hne : 0 < st.env.size := by
    rcases Nat.eq_zero_or_pos st.env.size with h | h
    · rw [Array.getElem?_eq_none (by omega)] at hfr; cases hfr
    · exact h
  have hlive2 : ∀ l, liveLoan (lendE st.env (.bind f j) st.nextLoan w) l = true ↔
      l = st.nextLoan ∨ liveLoan st.env l = true := fun l => by
    show liveLoan (Env.pushTempE (Env.setAtE st.env (.bind f j) (.loan st.nextLoan)) (.borrow st.nextLoan w)) l = true ↔ _
    rw [liveLoan_pushTempE_bor hfr' (by rw [hsz]; exact hne) hnum l,
      liveLoan_setAtE hx (fun l' => by rw [hxv, hnum.holdsBorrow]; rfl) l]
  have hxE2 : Pos.bind f j ∈ allPos (lendE st.env (.bind f j) st.nextLoan w) := by
    rw [hpos2]; exact List.mem_append_left _ hx
  have hntE2 : ntC st.env fr ∈ allPos (lendE st.env (.bind f j) st.nextLoan w) := by
    rw [hpos2]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hmeanX : ∀ χ : Future,
      Env.mean K.dm K.M K.Γ ρ χ (lendE st.env (.bind f j) st.nextLoan w) (.bind f j) = χ st.nextLoan := by
    intro χ
    rw [mean_eq_valAt K.dm K.M K.Γ ρ χ _ _ hxE2, hval2, if_neg hntx.symm, if_pos rfl]; rfl
  have hmeanN : ∀ χ : Future,
      Env.mean K.dm K.M K.Γ ρ χ (lendE st.env (.bind f j) st.nextLoan w) (ntC st.env fr) = .el0 Nat m := by
    intro χ
    rw [mean_eq_valAt K.dm K.M K.Γ ρ χ _ _ hntE2, hval2, if_pos rfl]; exact hmv _ _ _ _ _ _
  -- the reference's side after: the new label held at the new temporary, every other holder kept
  have hsh' : ∀ q, (lendState s (.bind f j) (.el0 Nat m)).shape q =
      if q = ntR s frs then some s.nextLoan else s.shape q := fun q => lend_shape (f := f) (j := j) hlast q
  have hpos' : ∀ q, q ∈ (lendState s (.bind f j) (.el0 Nat m)).positions ↔ q = ntR s frs ∨ q ∈ s.positions :=
    fun q => lend_mem_positions (f := f) (j := j) hlast q
  have hnewS : ¬ s.Live s.nextLoan := fun h => Nat.lt_irrefl _ (hliveS _ h)
  have hlive' : ∀ L, (lendState s (.bind f j) (.el0 Nat m)).Live L ↔ L = s.nextLoan ∨ s.Live L := fun L => by
    rw [SState.live_iff, SState.live_iff]
    constructor
    · rintro ⟨q, -, hsq⟩
      rw [hsh'] at hsq
      split at hsq
      · cases hsq; exact .inl rfl
      · exact .inr ⟨q, hr.holders q L hsq, hsq⟩
    · rintro (rfl | ⟨q, hq, hsq⟩)
      · exact ⟨ntR s frs, (hpos' _).mpr (.inl rfl), by rw [hsh']; simp⟩
      · refine ⟨q, (hpos' q).mpr (.inr hq), ?_⟩
        rw [hsh', if_neg (fun (e : q = ntR s frs) => hntS (e ▸ hq))]; exact hsq
  have hholdX : ∀ L, s.Live L → holderTy (lendState s (.bind f j) (.el0 Nat m)) L = holderTy s L := by
    intro L hL
    have hLn : L ≠ s.nextLoan := Nat.ne_of_lt (hliveS L hL)
    obtain ⟨r, hr₀⟩ := SState.holderOf_of_live ((hlive' L).mpr (.inr hL))
    have hrs := (SState.holderOf_spec hr₀).2
    rw [hsh'] at hrs
    have hr1 : r ≠ ntR s frs := fun e => by rw [if_pos e] at hrs; exact hLn (Option.some.inj hrs).symm
    rw [if_neg hr1] at hrs
    obtain ⟨r', hr₀'⟩ := SState.holderOf_of_live hL
    obtain rfl := huniq r r' L hrs (SState.holderOf_spec hr₀').2
    unfold holderTy; rw [hr₀, hr₀']
    cases r with
    | bind f' i' => exact congrArg TyS.m (lend_tyAt (s := s) (f := f) (j := j) (a := .el0 Nat m) _)
    | temp f' i' => exact lend_heldTy_ne s _ _ hLn
  -- the futures the relation compares at, after, pulled back to the old ones
  have hF : ∀ ψ, (RelF φ (lendState s (.bind f j) (.el0 Nat m)) ψ ∧
      TypedLive K (lendState s (.bind f j) (.el0 Nat m)) ψ) →
      RelF φ s (ψ.upd s.nextLoan (φ s.nextLoan)) ∧ TypedLive K s (ψ.upd s.nextLoan (φ s.nextLoan)) := by
    rintro ψ ⟨h1, h2⟩
    refine ⟨fun L hL => ?_, fun L hL => ?_⟩
    · by_cases e : L = s.nextLoan
      · subst e; simp [Future.upd]
      · rw [show (ψ.upd s.nextLoan (φ s.nextLoan)) L = ψ L by simp [Future.upd, e]]
        exact h1 L (fun h => ((hlive' L).mp h).elim e hL)
    · have hLn : L ≠ s.nextLoan := Nat.ne_of_lt (hliveS L hL)
      rw [show (ψ.upd s.nextLoan (φ s.nextLoan)) L = ψ L by simp [Future.upd, hLn], ← hholdX L hL]
      exact h2 L ((hlive' L).mpr (.inr hL))
  have hmeanOld : ∀ (ψ : Future) q, q ∈ allPos st.env → q ≠ .bind f j →
      Env.mean K.dm K.M K.Γ ρ (fun l => ψ (renameAt π st.nextLoan s.nextLoan l)) (lendE st.env (.bind f j) st.nextLoan w) q =
      Env.mean K.dm K.M K.Γ ρ (fun l => ψ.upd s.nextLoan (φ s.nextLoan) (π l)) st.env q := by
    intro ψ q hq hqx
    rw [lendE_mean (K := K) (ρ := ρ) (f := f) (j := j) hfr _ _ _ (fun (e : q = ntC st.env fr) => hntE (e ▸ hq)) hqx]
    apply mean_congr_pos hK hq
    intro l hl
    have ho := occurs_of_hasLoanM hq hl
    show ψ _ = _
    rw [hπold l (hlab l ho)]
    simp [Future.upd, Nat.ne_of_lt (hlt l ho)]
  have hvalOld : ∀ (ψ : Future) q, q ≠ ntR s frs → q ≠ .bind f j →
      (lendState s (.bind f j) (.el0 Nat m)).valAt q ψ = s.valAt q (ψ.upd s.nextLoan (φ s.nextLoan)) := by
    intro ψ q h1 h2
    rw [lend_valAt (a := .el0 Nat m) hlast hxs, if_neg h1, if_neg h2, hS.indep_fresh q (Nat.le_refl _) ψ]
  -- occurrences after
  have hocc : ∀ l, ({ st with env := lendE st.env (.bind f j) st.nextLoan w, nextLoan := st.nextLoan + 1 } : MState).Occurs l → l = st.nextLoan ∨ st.Occurs l := by
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
      · rw [hnum.inert.anyAtom _ (by rfl) (by rfl) (by rfl) (fun _ => by rfl)] at ha; cases ha
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- skel
    have h1 := skel_pushTempE K ρ ({ st with env := Env.setAtE st.env (.bind f j) (.loan st.nextLoan), nextLoan := st.nextLoan + 1 } : MState) (.borrow st.nextLoan w)
    have h2 := skel_setAtE K ρ ({ st with nextLoan := st.nextLoan + 1 } : MState) f j (.loan st.nextLoan)
    have h3 : (SM' K ρ ({ st with nextLoan := st.nextLoan + 1 } : MState)).env.map (fun fr => fr.binds.map bindSkel) =
        (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) := rfl
    exact h1.trans (h2.trans (h3.trans (hr.skel.trans (skel_lend s _ _).symm)))
  · -- fresh
    intro l _ ho
    rw [lend_nextLoan]
    rcases hocc l ho with rfl | h
    · rw [hπnew]; exact Nat.lt_succ_self _
    · rw [hπold l (hlab l h)]; exact Nat.lt_succ_of_lt (hlt l h)
  · -- the bindings mean the same
    intro ψ hψ p hp
    cases p with
    | temp => exact absurd trivial hp
    | bind f' i' =>
      show Env.mean K.dm K.M K.Γ ρ _ (lendE st.env (.bind f j) st.nextLoan w) (.bind f' i') = _
      by_cases hpx : Pos.bind f' i' = .bind f j
      · rw [lend_valAt (a := .el0 Nat m) hlast hxs, hpx, hmeanX, if_neg (by simp [ntR]), if_pos rfl, hπnew]
      · rw [hvalOld ψ _ (by simp [ntR]) hpx, lendE_mean (K := K) (ρ := ρ) (f := f) (j := j) hfr _ _ _ (by simp [ntC]) hpx,
          mean_congr_bind hK (χ' := fun l => ψ.upd s.nextLoan (φ s.nextLoan) (π l)) (fun hp' l hl => by
            have ho := occurs_of_hasLoanM hp' hl
            show ψ _ = _
            rw [hπold l (hlab l ho)]
            simp [Future.upd, Nat.ne_of_lt (hlt l ho)])]
        exact hr.sim.1 _ (hF ψ hψ) _ hp
  · -- the checker's holders at bindings are the reference's
    intro p l hp h
    have h' : Env.shape (lendE st.env (.bind f j) st.nextLoan w) p = some l := h
    rw [hsh2, if_neg (fun e => hp (by rw [e]; exact trivial))] at h'
    rw [hπold l (hliveC l (FEnd.liveLoan_of_shape h')), hsh', if_neg (fun e => hp (by rw [e]; exact trivial))]
    exact hr.sim.2.1 p l hp h'
  · -- the reference's holders at bindings are the checker's
    intro p L hp h
    rw [hsh', if_neg (fun e => hp (by rw [e]; exact trivial))] at h
    obtain ⟨l, h1, h2⟩ := hr.sim.2.2.1 p L hp h
    have h1' : Env.shape st.env p = some l := h1
    refine ⟨l, ?_, ?_⟩
    · show Env.shape (lendE st.env (.bind f j) st.nextLoan w) p = some l
      rw [hsh2, if_neg (fun e => hp (by rw [e]; exact trivial))]; exact h1'
    · rw [hπold l (hliveC l (FEnd.liveLoan_of_shape h1'))]; exact h2
  · -- the checker's temporaries holding a borrow
    intro f' i l h
    have h' : Env.shape (lendE st.env (.bind f j) st.nextLoan w) (.temp f' i) = some l := h
    rw [hsh2] at h'
    split at h'
    · next he =>
      cases h'
      have hf' : f' = st.env.size - 1 := by simp [ntC] at he; exact he.1
      refine ⟨frs.temps.length, ?_, fun ψ _ => ?_⟩
      · rw [hsh', if_pos (by simp [ntR, htopf f' hf']), hπnew]
      · show Env.mean K.dm K.M K.Γ ρ _ (lendE st.env (.bind f j) st.nextLoan w) (.temp f' i) = _
        rw [he, hmeanN, lend_valAt (a := .el0 Nat m) hlast hxs, if_pos (by simp [ntR, htopf f' hf'])]
    · have hq := mem_allPos_of_shape h'
      have hl : l < st.nextLoan := hliveC l (FEnd.liveLoan_of_shape h')
      obtain ⟨j', hj, hjv⟩ := hr.sim.2.2.2.1 f' i l h'
      have hjn : Pos.temp f' j' ≠ ntR s frs := fun e => hntS (e ▸ hr.holders _ _ hj)
      refine ⟨j', ?_, fun ψ hψ => ?_⟩
      · rw [hsh', if_neg hjn, hπold l hl]; exact hj
      · show Env.mean K.dm K.M K.Γ ρ _ (lendE st.env (.bind f j) st.nextLoan w) (.temp f' i) = _
        rw [hmeanOld ψ _ hq (by simp), hvalOld ψ _ hjn (by simp)]
        exact hjv _ (hF ψ hψ)
  · -- the reference's temporaries holding a borrow
    intro f' j' L h
    rw [hsh'] at h
    split at h
    · next he =>
      cases h
      have hf' : f' = s.topIdx := by simp [ntR] at he; exact he.1
      refine ⟨fr.temps.size, st.nextLoan, ?_, hπnew⟩
      show Env.shape (lendE st.env (.bind f j) st.nextLoan w) _ = _
      rw [hsh2, if_pos (by simp [ntC, hf', htop])]
    · obtain ⟨i, l, h1, h2⟩ := hr.sim.2.2.2.2 f' j' L h
      have h1' : Env.shape st.env (.temp f' i) = some l := h1
      have hq := mem_allPos_of_shape h1'
      refine ⟨i, l, ?_, ?_⟩
      · show Env.shape (lendE st.env (.bind f j) st.nextLoan w) _ = _
        rw [hsh2, if_neg (fun (e : Pos.temp f' i = ntC st.env fr) => hntE (e ▸ hq))]; exact h1'
      · rw [hπold l (hliveC l (FEnd.liveLoan_of_shape h1'))]; exact h2
  · -- the renaming is one to one: the new label goes to the reference's fresh one
    intro l l' hl hl' e
    rcases (hlive2 l).mp hl with rfl | h1 <;> rcases (hlive2 l').mp hl' with rfl | h2
    · rfl
    · rw [hπnew, hπold l' (hliveC l' h2)] at e
      exact absurd e (Nat.ne_of_gt (hlt l' (hoccL l' h2)))
    · rw [hπnew, hπold l (hliveC l h1)] at e
      exact absurd e (Nat.ne_of_lt (hlt l (hoccL l h1)))
    · rw [hπold l (hliveC l h1), hπold l' (hliveC l' h2)] at e
      exact hr.inj l l' h1 h2 e
  · -- the sites
    intro l hl x'
    rcases (hlive2 l).mp hl with rfl | hl1
    · rw [hπnew, lend_lent]
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
    · have hln : l ≠ st.nextLoan := Nat.ne_of_lt (hliveC l hl1)
      rw [hπold l (hliveC l hl1), lend_lent_ne s _ _ (Nat.ne_of_lt (hlt l (hoccL l hl1))), hr.sites l hl1 x']
      simp only [Env.sitesOf, List.mem_flatMap]
      constructor
      · rintro ⟨p, hp, hx'⟩
        refine ⟨p, by rw [hpos2]; exact List.mem_append_left _ hp, ?_⟩
        rw [hval2, if_neg (fun (e : p = ntC st.env fr) => hntE (e ▸ hp))]
        split
        · next he => subst he; rw [hxv, hnum.sitesOf] at hx'; cases hx'
        · exact hx'
      · rintro ⟨p, hp, hx'⟩
        rw [hval2] at hx'
        split at hx'
        · simp [Value.sitesOf, hnum.sitesOf] at hx'
        · split at hx'
          · simp [Value.sitesOf, hln, Ne.symm hln] at hx'
          · next h1 h2 =>
            have hp' : p ∈ allPos st.env := by
              rw [hpos2, List.mem_append, List.mem_singleton] at hp; exact hp.resolve_right h1
            exact ⟨p, hp', hx'⟩
  · -- the reference holds its borrows at its positions
    intro p L h
    rw [hsh'] at h
    split at h
    · next he => exact (hpos' p).mpr (.inl he)
    · exact (hpos' p).mpr (.inr (hr.holders p L h))
  · -- the records: the new label's is the borrowed number; every other kept
    intro L hL
    rcases (hlive' L).mp hL with rfl | hL1
    · obtain ⟨r, hr'⟩ := SState.holderOf_of_live hL
      have hrs := (SState.holderOf_spec hr').2
      rw [hsh'] at hrs
      have hrn : r = ntR s frs := by
        split at hrs
        · assumption
        · exact absurd ((SState.live_iff s _).mpr ⟨r, hr.holders r _ hrs, hrs⟩) hnewS
      rw [lend_heldMem]
      refine ⟨by simp [Sem.whole], ?_⟩
      unfold holderTy; rw [hr', hrn]
      show Sem.el0 Nat m ∈ₛ[K.dm.read] (lendState s (.bind f j) (.el0 Nat m)).heldTy s.nextLoan
      rw [lend_heldTy, hTy]; exact ⟨m, rfl⟩
    · have hLn : L ≠ s.nextLoan := Nat.ne_of_lt (hliveS L hL1)
      rw [lend_heldMem_ne s _ _ hLn, hholdX L hL1]
      exact hr.records L hL1

/-- **`borrowPlace` at a root whose access leaves `s₁`** (`ColumnBorrow.borrowPlace_root` where the
access may end borrows). -/
theorem borrowPlace_rootA {s s₁ : SState} {i : Nat} {pos : Pos} (hres : resolve s (.var i) = some (pos, []))
    (hacc : s.access pos (dataHit []) = s₁) {a : Sem} (hval : s₁.valAt pos (s₁.typedFuture φ) = a) (hw : a.whole) :
    borrowPlace K φ (.var i) s = some ((a, { s₁.tyAt pos with label := some s₁.nextLoan }), lendState s₁ pos a) := by
  unfold borrowPlace contentOf
  rw [hres]; simp only; rw [hacc, hval]
  simp [Sem.follow, hw, SState.freshLoan, lendState]
  rfl

/-- In a fragment environment a live label occurs. -/
theorem occurs_of_liveLoan_fval {st : MState} (hv : ∀ q ∈ allPos st.env, FVal (valAt st.env q)) {l : Nat}
    (hl : liveLoan st.env l = true) : st.Occurs l := by
  unfold liveLoan findBorrow at hl
  obtain ⟨p, hp, h⟩ := List.find?_isSome.mp hl
  obtain ⟨w, e⟩ := (FVal.holdsBorrow (hv p hp) l).mp h
  exact ⟨_, List.mem_map_of_mem hp, by rw [e]; simp [Value.anyAtom]⟩

/-- In a fragment environment whose labels lie below the counter, nothing is lent at the counter. -/
theorem sitesNext_fval {st : MState} (hv : ∀ q ∈ allPos st.env, FVal (valAt st.env q))
    (hlab : ∀ l, st.Occurs l → l < st.nextLoan) : ∀ q ∈ allPos st.env, (valAt st.env q).sitesOf st.nextLoan q [] = [] := by
  intro q hq
  rw [FVal.sitesOf (hv q hq)]
  split
  · next e =>
    have : st.Occurs st.nextLoan := occurs_of_hasLoanM hq ((FVal.hasLoanM (hv q hq) _).mpr e)
    exact absurd (hlab _ this) (Nat.lt_irrefl _)
  · rfl

/-- **The tail of `&x`**, shared by `x` a number and `x` lent: after a quiet stretch (`st₁`) and the
access (the checker's environment `E₂`, the reference's state `s₂`, related), `x` (a binding stored at
`Nat` holding the number `c`) is lent at the counter on both sides (`rel_lendG`). -/
theorem lend_out (hILG : InvLendG) (hPL : PlaceLocal K.D) (hInv : ∀ sc p, K.D.invalidated sc p = [])
    {st st₁ st' : MState} {E₂ : Env} {s s₂ : SState} {π : Nat → Nat} {tl : Bool} {hint : Option Value}
    {i f j : Nat} {c : Value}
    (hp : Pre K ρ st) (hq : Quiet st st₁) (hr₂ : Rel K ρ φ π { st₁ with env := E₂ } s₂)
    (hS₂ : Strict.SGood K.dm K.Γ φ s₂) (hlab₂ : ∀ l, ({ st₁ with env := E₂ } : MState).Occurs l → l < st₁.nextLoan)
    (hvals₂ : ∀ q ∈ allPos E₂, FVal (valAt E₂ q))
    (htemps₂ : ∀ f' i', Pos.temp f' i' ∈ allPos E₂ → (valAt E₂ (.temp f' i')).Num ∨ valAt E₂ (.temp f' i') = .unit)
    (hne₂ : 0 < E₂.size)
    (hinv₂ : Inv K.D K.Γ ({ st₁ with env := E₂ } : MState).norm) (ha₂ : Asg K ρ ({ st₁ with env := E₂ } : MState).norm)
    (hx₂ : Pos.bind f j ∈ allPos E₂) (hxv₂ : valAt E₂ (.bind f j) = c) (hc : c.Num)
    (hxty : ∀ b, E₂[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.ty = some .tNat ∧ b.decl = .other)
    (hxs₂ : Pos.bind f j ∈ s₂.positions) (hTy : (s₂.tyAt (.bind f j)).m = TyM.nat)
    (hres : resolve s (.var i) = some (.bind f j, [])) (hacc : s.access (.bind f j) (dataHit []) = s₂)
    (haok : AccessOk K φ s (.bind f j) (dataHit [])) (hfl : K.D.flags (scopeOf s) (.borrow (.var i)) = (false, false))
    (hk : Kern { st₁ with env := Env.setAtE E₂ (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } st') :
    Out K ρ φ π st st' s (runT K ρ φ tl (hintM K ρ hint) (.borrow (.var i))) (.borrow st₁.nextLoan c)
      (some (.tRef .tNat)) := by
  obtain ⟨m, hmv⟩ := hc.vmean
  -- the reference's run
  have hval : s₂.valAt (.bind f j) (s₂.typedFuture φ) = .el0 Nat m := by
    rw [← hr₂.sim.1 _ ⟨relF_typedFuture φ s₂, hr₂.typedFuture_typed φ⟩ (.bind f j) (by simp [IsTemp])]
    show Env.mean K.dm K.M K.Γ ρ _ E₂ (.bind f j) = _
    rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ hx₂, hxv₂]; exact hmv _ _ _ _ _ _
  have hbp := borrowPlace_rootA (K := K) (φ := φ) hres hacc hval (by simp [Sem.whole])
  have hxr : runT K ρ φ tl (hintM K ρ hint) (.borrow (.var i)) s =
      some ((.el0 Nat m, { s₂.tyAt (.bind f j) with label := some s₂.nextLoan }), lendState s₂ (.bind f j) (.el0 Nat m)) := by
    rw [runT_borrow _ _ _ s hfl]
    have hg : SM.guarded (ContentOk K φ (.var i)) (borrowPlace K φ (.var i)) s =
        some ((.el0 Nat m, { s₂.tyAt (.bind f j) with label := some s₂.nextLoan }), lendState s₂ (.bind f j) (.el0 Nat m)) := by
      rw [SM.guarded_of (by unfold ContentOk; rw [hres]; exact haok), hbp]
    have hst : SM.strictS K.dm.read (SM.guarded (ContentOk K φ (.var i)) (borrowPlace K φ (.var i))) s =
        some ((.el0 Nat m, { s₂.tyAt (.bind f j) with label := some s₂.nextLoan }), lendState s₂ (.bind f j) (.el0 Nat m)) := by
      unfold SM.strictS; rw [hg]; simp only
      rw [if_pos (by show Sem.el0 Nat m ∈ₛ[K.dm.read] (s₂.tyAt (.bind f j)).m; rw [hTy]; exact ⟨m, rfl⟩)]
    rw [hst]
    simp only
    have hi : invalidate K φ (.var i) (lendState s₂ (.bind f j) (.el0 Nat m)) = lendState s₂ (.bind f j) (.el0 Nat m) := by
      unfold invalidate; rw [hInv]; rfl
    rw [hi, if_pos ⟨by unfold InvalidateOk; rw [hInv]; trivial, lentOk_var i _⟩]
  -- the relation after
  obtain ⟨fr, hfr⟩ : ∃ fr, E₂[E₂.size - 1]? = some fr := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  have hR := rel_lendG (st := { st₁ with env := E₂ }) hp.ctx.noLabel hr₂ hS₂ hlab₂
    (fun l hl => occurs_of_liveLoan_fval hvals₂ hl) (sitesNext_fval hvals₂ hlab₂) hfr hx₂ hxv₂ hxs₂ hc hmv hTy
  have hbAbs : ∀ σ, (Value.borrow st₁.nextLoan c).hasAbs σ = false := fun σ => by
    show ((Value.borrow st₁.nextLoan c == Value.abs σ) || c.anyAtom (· == .abs σ)) = false
    rw [show (Value.borrow st₁.nextLoan c == Value.abs σ) = false from rfl]
    exact hc.hasAbs σ
  refine ⟨ρ, K.Δ, renameAt π st₁.nextLoan s₂.nextLoan, _, _, ⟨?_, ?_, fun _ _ => ⟨rfl, rfl⟩, ?_⟩, hxr, ?_,
    fun T hT => ?_, ?_, ?_, ?_⟩
  · rw [← hk.absTy]; exact hq.absSize
  · rw [← hk.nextLoan]; exact Nat.le_succ_of_le hq.nextLoan
  · intro l hl
    have : l ≠ st₁.nextLoan := Nat.ne_of_lt (Nat.lt_of_lt_of_le hl hq.nextLoan)
    simp [renameAt, this]
  · show meanV _ ρ _ _ (Value.borrow st₁.nextLoan c) = .el0 Nat m
    rw [← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  · cases hT
    show _ = (s₂.tyAt (.bind f j)).m
    rw [hTy]; rfl
  · simp [Value.heldLabel, renameAt]
  · refine ⟨hp.ctx.of_eq ?_ ?_, ?_, ?_⟩
    · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
    · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
    · rw [← (hk.withTempT _ _).norm]
      have := hILG K.D K.Γ ({ st₁ with env := E₂ } : MState) f j (some (.tRef .tNat)) hPL hx₂ (by rw [hxv₂]; exact hc)
        hxty hvals₂ htemps₂ hinv₂
      rw [hxv₂] at this; exact this
    · have hX : Asg K ρ (({ st₁ with env := Env.setAtE E₂ (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } : MState).withTempT (.borrow st₁.nextLoan c) (some (.tRef .tNat))).norm := by
        refine ha₂.of_refd rfl rfl rfl rfl rfl fun σ hσ => ?_
        have h1 := refd_withTempT_noAbs (st := ({ st₁ with env := Env.setAtE E₂ (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } : MState)) hbAbs _ σ hσ
        refine refd_sub (st := ({ st₁ with env := E₂ } : MState)) (st' := ({ st₁ with env := Env.setAtE E₂ (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } : MState)) rfl rfl rfl rfl ?_ ?_ ?_ σ h1
        · intro w' hw' σ' hσ'
          rcases mem_values_setAtE hw' with rfl | hw''
          · exact absurd hσ' (by rw [show (Value.loan st₁.nextLoan).hasAbs σ' = false from rfl]; simp)
          · exact ⟨w', hw'', hσ'⟩
        · intro f' i' b' T σ' hb' hT hσ'
          obtain ⟨b'', hb'', hty'', -⟩ := lookup_setAtE hb'
          exact .ty f' i' b'' T (by rw [show ({ st₁ with env := E₂ } : MState).norm.env = E₂.erase from rfl, lookup_erase]; exact hb'')
            (by rw [hty'']; exact hT) hσ'
        · intro f' i' b' P ws j' σ' hb' hl hσ'
          obtain ⟨b'', hb'', -, hlz''⟩ := lookup_setAtE hb'
          exact .lazyTy f' i' b'' P ws j' (by rw [show ({ st₁ with env := E₂ } : MState).norm.env = E₂.erase from rfl, lookup_erase]; exact hb'')
            (by rw [hlz'']; exact hl) hσ'
      rw [(hk.withTempT _ _).norm] at hX
      exact hX
  · have h1 := Rel.of_kern (kern_withTemp ({ st₁ with env := Env.setAtE E₂ (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } : MState) (.borrow st₁.nextLoan c) (some (.tRef .tNat))) hR
    exact Rel.of_kern (hk.withTempT _ _) h1

/-- A write keeps every binding's stored type and reading (`lookup_setAtE` with the reading). -/
theorem lookup_setAtE_decl {env : Env} {p : Pos} {v : Value} {f i : Nat} {b : Binding}
    (h : (Env.setAtE env p v)[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b) :
    ∃ b', env[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b' ∧ b'.ty = b.ty ∧ b'.decl = b.decl := by
  cases p with
  | bind f' i' =>
    simp only [Env.setAtE, Array.getElem?_modify] at h
    by_cases hf : f' = f
    · subst hf
      rcases hfr : env[f']? with _ | fr
      · rw [hfr] at h; simp at h
      · rw [hfr] at h
        simp only [if_true, Option.map_some, Option.bind_some, Array.getElem?_modify] at h
        by_cases hi : i' = i
        · subst hi; simp only [if_true] at h
          rcases hb : fr.binds[i']? with _ | b'
          · rw [hb] at h; simp at h
          · rw [hb] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
            exact ⟨b', by simp [hfr, hb], rfl, rfl⟩
        · simp only [hi, if_false] at h; exact ⟨b, by simp [hfr, h], rfl, rfl⟩
    · simp only [hf, if_false] at h; exact ⟨b, h, rfl, rfl⟩
  | temp f' i' =>
    simp only [Env.setAtE, Array.getElem?_modify] at h
    by_cases hf : f' = f
    · subst hf
      rcases hfr : env[f']? with _ | fr
      · rw [hfr] at h; simp at h
      · rw [hfr] at h; simp only [if_true, Option.map_some, Option.bind_some] at h
        exact ⟨b, by simp [hfr, h], rfl, rfl⟩
    · simp only [hf, if_false] at h; exact ⟨b, h, rfl, rfl⟩

/-- The checker's `x` of the fragment is stored at `Nat` and read `.other`. -/
theorem FSt.natVar {Γ : List FT} {st : MState} (hP : FSt Γ st) {i f j : Nat} (hi : Γ[i]? = some .nat)
    (hpos : ckVarPos st.env i = some (.bind f j)) :
    ∀ b, st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.ty = some .tNat ∧ b.decl = .other := by
  intro b hb
  obtain ⟨f₀, j₀, b₀, hck₀, hb₀, hty₀, hrd₀, -⟩ := hP.top i .nat hi
  rw [hpos] at hck₀; cases hck₀
  rw [hb] at hb₀; cases hb₀
  exact ⟨hty₀, hrd₀⟩

/-- **`&x` of the fragment, at `evalCore`** (`x` a number variable of the top frame): `x` holds a
number (`BorrowNumInv`: nothing ends), is lent (`BorrowLentInv`: the access ends its borrow, `rel_end`
and `lent_access`, then the lend), or was moved (`BorrowBotInv`: the run fails). The lend is
`lend_out` (`rel_lendG`: other borrows stay live). Assumes the facts about the checker
`BorrowNumInv`, `BorrowLentInv`, `BorrowBotInv`, `InvEnd`, `InvLendG` and of the table `PlaceLocal`,
an empty invalidation. -/
theorem borF_core (hB : BorrowNumInv) (hBL : BorrowLentInv) (hBB : BorrowBotInv) (hIE : InvEnd) (hILG : InvLendG)
    (hPL : PlaceLocal K.D) (hInv : ∀ sc p, K.D.invalidated sc p = []) {n i : Nat} {Γ : List FT}
    (hi : Γ[i]? = some .nat) : CoreSim K ρ φ (n + 1) (.borrow (.var i)) (FSt Γ) (· = true) := by
  intro st st' typed hint v T? s π hP hty hm htn htd hcd hp hr hS hv hab hnh hfl hok hD bh h
  subst hty
  have hlab : ∀ l, st.Occurs l → l < st.nextLoan := hp.labels
  rcases hP.var_cases hi with ⟨f, j, b, hpos, hlk, hnum, htyb⟩ | hL | ⟨f, j, b, hpos, hlk, hbot, htyb⟩
  · -- `x` holds a number: nothing ends
    obtain ⟨-, st₁, hq, hki, rfl, rfl, hk⟩ := hB n i hint st st' bh v T? f j b K.D hm hpos hlk hnum htyb hD h
    have hlk₁ : st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
      rw [← lookup_erase, ← hq.env, lookup_erase]; exact hlk
    have hP₁ : FSt Γ st₁ := hP.of_erase hq.env
    have hocc₁ : ∀ l, st₁.Occurs l ↔ st.Occurs l := fun l =>
      (occurs_erase st₁ l).symm.trans ((occurs_of_env (st := { st with env := st.env.erase })
        (st' := { st₁ with env := st₁.env.erase }) hq.env.symm l).trans (occurs_erase st l))
    have hlab₁ : ∀ l, st₁.Occurs l → l < st₁.nextLoan := fun l h' =>
      Nat.lt_of_lt_of_le (hlab l ((hocc₁ l).mp h')) hq.nextLoan
    have hr₁ : Rel K ρ φ π st₁ s := hr.of_quiet hq hlab
    obtain ⟨hx, hxv⟩ := lookup_pos hlk₁
    have hres : resolve s (.var i) = some (.bind f j, []) := rel_resolve_ck K ρ φ st s π (.var i) _ hr hpos
    have hns : ∀ l, (valAt st.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by
      rw [(lookup_pos hlk).2]; exact hnum.sitesOf l _ _
    have hacc : s.access (.bind f j) (dataHit []) = s := access_noSites (rel_noSites_at hr hns)
    have haok : AccessOk K φ s (.bind f j) (dataHit []) := accessOk_noSites (rel_noSites_at hr hns)
    have hTy : (s.tyAt (.bind f j)).m = TyM.nat := by
      rw [(rel_bind_ty hr hlk).2]; simp only [Env.hintAt, hlk, htyb]; rfl
    have hpos₁ : ckVarPos st₁.env i = some (.bind f j) := by rw [← ckVarPos_erase, ← hq.env, ckVarPos_erase]; exact hpos
    exact lend_out (E₂ := st₁.env) hILG hPL hInv hp hq hr₁ hS hlab₁ hP₁.vals hP₁.temps hP₁.frame
      (hki K.D K.Γ hp.inv) (Asg.of_quiet hq hp.asg hp.inv.wf6) hx hxv hnum (hP₁.natVar hi hpos₁)
      (rel_bind_ty hr hlk).1 hTy hres hacc haok hfl hk
  · -- `x` lent: the access ends its borrow, then the lend
    obtain ⟨f, j, b, f', j', l, c, hpos, hb, htyb, hdo, he, hlv⟩ := hL
    obtain ⟨-, st₁, hq, hki, rfl, rfl, hk⟩ := hBL n i hint st st' bh v T? f j b f' j' l c K.D hm hpos hb htyb he hD h
    have hvE : ∀ q, valAt st₁.env q = valAt st.env q := fun q => by rw [← valAt_erase, ← hq.env, valAt_erase]
    have haE : allPos st₁.env = allPos st.env := by rw [← allPos_erase, ← hq.env, allPos_erase]
    have hlE : ∀ m, liveLoan st₁.env m = liveLoan st.env m := fun m => by
      unfold liveLoan findBorrow; rw [haE]; simp only [hvE]
    have hP₁ : FSt Γ st₁ := hP.of_erase hq.env
    have he₁ : FEnd st₁.env (.bind f j) (.bind f' j') l c := he.of_erase hq.env
    have hlv₁ : ∀ q ∈ allPos st₁.env, ∀ m, valAt st₁.env q = .loan m → liveLoan st₁.env m = true :=
      fun q hq' m hm₁ => by rw [hlE]; exact hlv q (haE ▸ hq') m (by rw [← hvE]; exact hm₁)
    have hocc₁ : ∀ l, st₁.Occurs l ↔ st.Occurs l := fun l =>
      (occurs_erase st₁ l).symm.trans ((occurs_of_env (st := { st with env := st.env.erase })
        (st' := { st₁ with env := st₁.env.erase }) hq.env.symm l).trans (occurs_erase st l))
    have hr₁ : Rel K ρ φ π st₁ s := hr.of_quiet hq hlab
    have ha₁ : Asg K ρ st₁.norm := Asg.of_quiet hq hp.asg hp.inv.wf6
    -- the end, on both sides
    obtain ⟨r, cM, hhold, hrs, hrph, -, -, -, -⟩ := end_holder hr₁ hS he₁
    have hrr : r = .bind f' j' := hrph f' j' rfl
    obtain ⟨r₂, hhold₂, hrE⟩ := rel_end hr₁ hS he₁ hlv₁
    have hr₂ : r = r₂ := by rw [hhold] at hhold₂; exact Option.some.inj hhold₂
    subst hr₂
    have hend := end_ok hr₁ hS he₁
    obtain ⟨hacc, haok⟩ := lent_access hr₁ hS he₁ hrs hrr
    have hSt : Strict.SGood K.dm K.Γ φ (s.endAt (π l) r) := Strict.endAt_sgood hS hhold hend
    have hinv₂ : Inv K.D K.Γ ({ st₁ with env := (endE st₁.env (.bind f j) (.bind f' j') c) } : MState).norm :=
      hIE K.D K.Γ st₁ _ _ l c hPL he₁ (fun f₀ j₀ e b₀ hb₀ => by
        cases e; rw [← lookup_erase, ← hq.env, lookup_erase, hb] at hb₀; cases hb₀; exact hdo)
        (hki K.D K.Γ hp.inv)
    have hres : resolve s (.var i) = some (.bind f j, []) := rel_resolve_ck K ρ φ st s π (.var i) _ hr hpos
    have hb₁ : st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
      rw [← lookup_erase, ← hq.env, lookup_erase]; exact hb
    obtain ⟨hposS, htyS₀⟩ := rel_bind_ty hr₁ hb₁
    have htyN : ((s.endAt (π l) r).tyAt (.bind f j)).m = TyM.nat := by
      rw [endAt_tyAt', htyS₀]; simp only [Env.hintAt, hb₁, htyb]; rfl
    have hvals₂ := he₁.vals_endE
    have htemps₂ : ∀ f₀ i₀, Pos.temp f₀ i₀ ∈ allPos (endE st₁.env (.bind f j) (.bind f' j') c) → (valAt (endE st₁.env (.bind f j) (.bind f' j') c) (.temp f₀ i₀)).Num ∨ valAt (endE st₁.env (.bind f j) (.bind f' j') c) (.temp f₀ i₀) = .unit := by
      intro f₀ i₀ hq₀
      rw [he₁.valAt_endE, if_neg (by simp), if_neg (by simp)]
      rw [FEnd.allPos_endE] at hq₀
      exact hP₁.temps f₀ i₀ hq₀
    have hsz : (endE st₁.env (.bind f j) (.bind f' j') c).size = st₁.env.size := by simp [endE, Env.setAtE]
    have hxty : ∀ b', (endE st₁.env (.bind f j) (.bind f' j') c)[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b' → b'.ty = some .tNat ∧ b'.decl = .other := by
      intro b' hb'
      obtain ⟨b₂, hb₂, ht₂, hd₂⟩ := lookup_setAtE_decl hb'
      obtain ⟨b₃, hb₃, ht₃, hd₃⟩ := lookup_setAtE_decl hb₂
      rw [hb₁] at hb₃; cases hb₃
      exact ⟨by rw [← ht₂, ← ht₃]; exact htyb, by rw [← hd₂, ← hd₃]; exact hdo⟩
    exact lend_out (E₂ := (endE st₁.env (.bind f j) (.bind f' j') c)) hILG hPL hInv hp hq hrE hSt
      (fun l' h' => Nat.lt_of_lt_of_le (hlab l' ((hocc₁ l').mp (he₁.occurs_endE (st := st₁) rfl h'))) hq.nextLoan)
      hvals₂ htemps₂ (by rw [hsz]; exact hP₁.frame) hinv₂ (asg_endE he.c ha₁)
      (by rw [FEnd.allPos_endE]; exact he₁.hpx) (by rw [he₁.valAt_endE, if_pos rfl]) he.c hxty
      (by rw [SState.endAt_positions]; exact hposS) htyN hres hacc (haok hend) hfl hk
  · exact absurd h (hBB n i hint st st' bh v T? f j b hpos hlk hbot htyb)

end

end Ochr.Meaning.Steps.Form
