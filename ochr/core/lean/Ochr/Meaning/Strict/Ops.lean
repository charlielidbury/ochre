import Ochr.Meaning.Strict.Good

/-!
# The state operations keep the invariant

Each operation the strict run performs on the model state, shown to keep `SGood`: a whole write of a
binding (`sgood_setAt_const`), an end (`endAt_sgood`), [Access] (`access_sgood`), and below them the
facts they share. (There is no read clause to keep since the dependent-values unit: reads are strict,
`Run.ReadGood`, so the data layer's read hypothesis `MemReads` is gone.)
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

/-- On `⊥`, a read gives `⊥` or nothing. -/
theorem follow_moved' (dm : DataModel) (Γ : List IndDecl) : ∀ (T : TyS) (steps : List Step) (x : Sem) (U : TyS),
    Sem.follow dm Γ T .moved steps = some (x, U) → x = .moved
  | _, [], _, _, h => by simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  | T, st :: sts, x, U, h => by
    simp only [Sem.follow] at h
    cases st with
    | deref => exact follow_moved' dm Γ T sts x U (by simpa [Sem.step] using h)
    | proj i =>
      cases i with
      | zero => simp [Sem.step, Sem.asNat, Sem.as, Sem.stepField] at h
      | succ i => simp [Sem.step, Sem.stepField] at h
    | field g => simp [Sem.step, Sem.stepField] at h

theorem Future.upd_comm (ψ : Future) {a b : Nat} (h : a ≠ b) (x y : Sem) :
    (ψ.upd a x).upd b y = (ψ.upd b y).upd a x := by
  funext l
  simp only [Future.upd]
  by_cases ha : l = a <;> by_cases hb : l = b <;> simp_all

section
variable {dm : DataModel} {Γ : List IndDecl} {φ : Future}

theorem liveLabels_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).liveLabels = s.liveLabels := by
  unfold SState.liveLabels; rw [SState.positions_setAt, SState.shape_setAt]

theorem heldTy_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).heldTy = s.heldTy := by
  cases p <;> rfl

theorem heldMem_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).heldMem = s.heldMem := by
  cases p <;> rfl

theorem nextLoan_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).nextLoan = s.nextLoan := by
  cases p <;> rfl

theorem typedF_setAt {s : SState} {p : Pos} {g : SVal} {ψ : Future} :
    TypedF dm Γ φ (s.setAt p g) ψ ↔ TypedF dm Γ φ s ψ := by
  unfold TypedF; rw [liveLabels_setAt, heldTy_setAt]

/-- A holder's meaning does not read its own label (from the label order). -/
theorem SGood.holderIndep {s : SState} (hs : SGood dm Γ φ s) {p : Pos} {l : Nat}
    (hl : s.shape p = some l) : Indep l (s.valAt p) := by
  obtain ⟨-, h2, hsa⟩ := hs.acyc
  refine (h2 p l (hsa p l hl).1 hl).indep ?_
  rintro (⟨-, hn⟩ | ⟨-, hlt⟩)
  · exact hn ((SState.live_iff s l).2 ⟨p, (hsa p l hl).1, hl⟩)
  · exact Nat.lt_irrefl l hlt

/-- No position reads a label at or above the counter. -/
theorem SGood.indep_fresh {s : SState} (hs : SGood dm Γ φ s) (p : Pos) {l : Nat} (hl : s.nextLoan ≤ l) :
    Indep l (s.valAt p) := by
  intro ψ x
  by_cases h : s.valAt p (ψ.upd l x) = s.valAt p ψ
  · exact h
  · exact absurd (hs.fresh p l ⟨ψ, x, fun e => h e.symm⟩) (Nat.not_lt.mpr hl)

theorem SGood.live_lt {s : SState} (hs : SGood dm Γ φ s) {l : Nat} (hl : l ∈ s.liveLabels) : l < s.nextLoan := by
  obtain ⟨p, -, hp⟩ := (SState.live_iff s l).1 hl
  exact (hs.acyc.2.2 p l hp).2

/-- A binding not among the positions has the error type. -/
theorem tyAt_of_not_mem {s : SState} {f i : Nat} (hn : Pos.bind f i ∉ s.positions) :
    s.tyAt (.bind f i) = .plain TyM.err := by
  rw [SState.mem_positions] at hn
  simp only [SState.lookup, Option.isSome_iff_exists, not_exists] at hn
  simp only [SState.tyAt]
  cases hb : s.env[f]?.bind (·.binds[i]?) with
  | none => rfl
  | some b => exact absurd (by rw [Option.map_eq_some_iff]; exact ⟨b, hb, rfl⟩) (hn _)

/-- A binding's meaning after a write of a constant there. -/
theorem valAt_setAt_const {s : SState} {pos : Pos} (hpos : pos ∈ s.positions) (v : Sem) (q : Pos) (ψ : Future) :
    (s.setAt pos fun _ => v).valAt q ψ = if q = pos then v else s.valAt q ψ := by
  split
  · rename_i hq; subst hq; rw [valAt_setAt_self s _ _ hpos]
  · rename_i hq; rw [SState.valAt_setAt_ne s _ _ q (Ne.symm hq)]

/-- **A binding written whole with a member of its stored type** (an assignment's write at a root or
through a borrow, `*r := v`, writes the holder's content whole) keeps the invariant: where the binding
holds a borrow, its stored type is the label's content type (`holderTy`), so the value is a member of
that too. -/
theorem sgood_setAt_const {s : SState} {f i : Nat} {v : Sem} (hs : SGood dm Γ φ s)
    (hv : v ∈ₛ[dm.read] (s.tyAt (.bind f i)).m) : SGood dm Γ φ (s.setAt (.bind f i) fun _ => v) := by
  have hpos : Pos.bind f i ∈ s.positions := by
    by_cases hn : Pos.bind f i ∈ s.positions
    · exact hn
    exfalso
    rw [tyAt_of_not_mem hn] at hv
    exact DataModel.err_mem_false _ v hv
  have hval := valAt_setAt_const hpos v
  refine ⟨fun ψ hψ f' i' hpi => ?_, fun ψ hψ p l hl => ?_, ?_, fun f' i' l hl => ?_, ?_, ?_⟩
  · rw [typedF_setAt] at hψ
    show GoodVal _ _ ((s.setAt _ _).valAt _ ψ) ((s.setAt _ _).tyAt _).m
    rw [hval, tyAt_setAt]
    split
    · rename_i hq; rw [hq]; exact goodVal_of_mem dm.read_wholeFields Γ hv
    · exact hs.bind ψ hψ f' i' (by rwa [SState.positions_setAt] at hpi)
  · rw [typedF_setAt] at hψ
    rw [SState.shape_setAt] at hl
    rw [hval, heldTy_setAt]
    split
    · rename_i hq; subst hq
      rw [← hs.holderTy f i l hl]
      exact .mem hv
    · exact hs.holder ψ hψ p l hl
  · rw [liveLabels_setAt, heldTy_setAt, heldMem_setAt]; exact hs.held
  · rw [SState.shape_setAt] at hl; rw [tyAt_setAt, heldTy_setAt]; exact hs.holderTy f' i' l hl
  · exact SState.setAt_rinv hs.acyc _ _ (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  · exact SState.readsBelow_setAt hs.fresh _ _ (fun l ⟨_, _, h⟩ => absurd rfl h)

/-- **A position rewritten pointwise** (`fun φ' => g (old φ')`: a write at a path, `setContent`) keeps
the invariant where, at every typed future, the new value is good at the position's types. -/
theorem sgood_setAt_comp {s : SState} {p : Pos} (g : Sem → Sem) (hs : SGood dm Γ φ s) (hp : p ∈ s.positions)
    (hb : ∀ ψ, TypedF dm Γ φ s ψ → ∀ f i, p = .bind f i → GoodVal dm Γ (g (s.valAt p ψ)) (s.tyAt p).m)
    (hh : ∀ ψ, TypedF dm Γ φ s ψ → ∀ l, s.shape p = some l → PMem dm Γ (g (s.valAt p ψ)) (s.heldTy l)) :
    SGood dm Γ φ (s.setAt p fun φ' => g (s.valAt p φ')) := by
  have hval : ∀ q ψ, (s.setAt p fun φ' => g (s.valAt p φ')).valAt q ψ =
      if q = p then g (s.valAt p ψ) else s.valAt q ψ := by
    intro q ψ; split
    · rename_i hq; subst hq; rw [valAt_setAt_self s _ _ hp]
    · rename_i hq; rw [SState.valAt_setAt_ne s _ _ q (Ne.symm hq)]
  refine ⟨fun ψ hψ f' i' hpi => ?_, fun ψ hψ q l hl => ?_, ?_, fun f' i' l hl => ?_, ?_, ?_⟩
  · rw [typedF_setAt] at hψ
    show GoodVal _ _ ((s.setAt _ _).valAt _ ψ) ((s.setAt _ _).tyAt _).m
    rw [hval, tyAt_setAt]
    split
    · rename_i hq; rw [hq]; exact hb ψ hψ f' i' hq.symm
    · exact hs.bind ψ hψ f' i' (by rwa [SState.positions_setAt] at hpi)
  · rw [typedF_setAt] at hψ
    rw [SState.shape_setAt] at hl
    rw [hval, heldTy_setAt]
    split
    · rename_i hq; subst hq; exact hh ψ hψ l hl
    · exact hs.holder ψ hψ q l hl
  · rw [liveLabels_setAt, heldTy_setAt, heldMem_setAt]; exact hs.held
  · rw [SState.shape_setAt] at hl; rw [tyAt_setAt, heldTy_setAt]; exact hs.holderTy f' i' l hl
  · exact SState.setAt_rinv hs.acyc p _ ((hs.acyc.1 p).comp g)
      (fun x hx => (hs.acyc.2.1 p x (hs.acyc.2.2 p x hx).1 hx).comp g)
  · exact SState.readsBelow_setAt hs.fresh _ _ (fun l h => hs.fresh p l (SVal.dependsOn_comp h))

/-- **A position written with a constant that is an open member of its types** (a member, or
`⊥`: a write of a member, a move out of a whole position) keeps the invariant: at a binding the value
is an open member of its stored type, at a holder of its label's content type. -/
theorem sgood_setAt_pmem {s : SState} {p : Pos} {v : Sem} (hs : SGood dm Γ φ s)
    (hp : p ∈ s.positions) (hb : ∀ f i, p = .bind f i → PMem dm Γ v (s.tyAt p).m)
    (hh : ∀ l, s.shape p = some l → PMem dm Γ v (s.heldTy l)) :
    SGood dm Γ φ (s.setAt p fun _ => v) := by
  have hval := valAt_setAt_const hp v
  refine ⟨fun ψ hψ f' i' hpi => ?_, fun ψ hψ q l hl => ?_, ?_, fun f' i' l hl => ?_, ?_, ?_⟩
  · rw [typedF_setAt] at hψ
    show GoodVal _ _ ((s.setAt _ _).valAt _ ψ) ((s.setAt _ _).tyAt _).m
    rw [hval, tyAt_setAt]
    split
    · rename_i hq; subst hq; exact .inl (hb f' i' rfl).pmem
    · exact hs.bind ψ hψ f' i' (by rwa [SState.positions_setAt] at hpi)
  · rw [typedF_setAt] at hψ
    rw [SState.shape_setAt] at hl
    rw [hval, heldTy_setAt]
    split
    · rename_i hq; subst hq; exact hh l hl
    · exact hs.holder ψ hψ q l hl
  · rw [liveLabels_setAt, heldTy_setAt, heldMem_setAt]; exact hs.held
  · rw [SState.shape_setAt] at hl; rw [tyAt_setAt, heldTy_setAt]; exact hs.holderTy f' i' l hl
  · exact SState.setAt_rinv hs.acyc _ _ (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  · exact SState.readsBelow_setAt hs.fresh _ _ (fun l ⟨_, _, h⟩ => absurd rfl h)

/-- **An end keeps the invariant** (`endAt`: the holder `r` of `l` reads `⊥`, every other position its
old meaning at `ψ := ψ'.upd l (r's content at ψ')`). That `ψ` is typed for the state before: it agrees
with `φ` off the live labels before (they include `l`), at `l` it is `r`'s content, an open
member of `heldTy l` (`holder`, at `ψ'` with `l` set to its record, which `r` does not read), and
elsewhere it is `ψ'`. Why the typed futures give a live label an OPEN member: a borrow may
end with parts of its content moved out (D53 (h)), and its lenders then read those parts moved. -/
theorem endAt_sgood {s : SState} {l : Nat} {r : Pos} (hs : SGood dm Γ φ s) (hh : s.holderOf l = some r) :
    SGood dm Γ φ (s.endAt l r) := by
  have hr : s.shape r = some l := (SState.holderOf_spec hh).2
  have hlive : l ∈ s.liveLabels := (SState.live_iff s l).2 ⟨r, (SState.holderOf_spec hh).1, hr⟩
  have hTy : ∀ q, (s.endAt l r).tyAt q = s.tyAt q := fun q => by unfold SState.endAt; rw [tyAt_mapVals]; rfl
  have hHT : (s.endAt l r).heldTy = s.heldTy := rfl
  have hHM : (s.endAt l r).heldMem = s.heldMem := rfl
  have hNL : (s.endAt l r).nextLoan = s.nextLoan := rfl
  -- a future typed after the end, read before it
  have key : ∀ ψ', TypedF dm Γ φ (s.endAt l r) ψ' → TypedF dm Γ φ s (ψ'.upd l (s.valAt r ψ')) := by
    rintro ψ' ⟨hag, hψ'⟩
    have hag' : ∀ y, y ∉ s.liveLabels → ψ' y = φ y := fun y hy =>
      hag y (fun h => hy (SState.endAt_live h))
    refine ⟨fun y hy => ?_, fun l' hl' => ?_⟩
    · have hne : y ≠ l := fun e => hy (e ▸ hlive)
      rw [Future.upd_other _ _ hne]; exact hag' y hy
    by_cases e : l' = l
    · subst e
      rw [Future.upd_same]
      have hm : s.heldMem l' ∈ₛ[dm.read] s.heldTy l' := hs.held l' hl'
      have ht : TypedF dm Γ φ s (ψ'.upd l' (s.heldMem l')) := by
        refine ⟨fun y hy => ?_, fun y hy => ?_⟩
        · have hne : y ≠ l' := fun e => hy (e ▸ hl')
          rw [Future.upd_other _ _ hne]; exact hag' y hy
        by_cases ey : y = l'
        · subst ey; rw [Future.upd_same]; exact hm
        · rw [Future.upd_other _ _ ey]
          have := hψ' y (SState.live_endAt hr hy ey); rwa [hHT] at this
      -- PROBE (A): the holder's content is an OPEN member of `heldTy` (`hs.holder`); a typed future
      -- now needs a MEMBER: the strict end
      sorry
    · rw [Future.upd_other _ _ e]
      have := hψ' l' (SState.live_endAt hr hl' e); rwa [hHT] at this
  refine ⟨fun ψ' hψ' f i hpi => ?_, fun ψ' hψ' p l'' hl'' => ?_, fun l' hl' => ?_, fun f i l' hl' => ?_, ?_,
    ?_⟩
  · show GoodVal _ _ ((s.endAt l r).valAt _ ψ') ((s.endAt l r).tyAt _).m
    rw [hTy]
    have hp : Pos.bind f i ∈ s.positions := by rwa [SState.endAt_positions] at hpi
    rw [SState.endAt_valAt s l r _ hp]
    split
    · exact .inl (.moved _)
    · exact hs.bind _ (key ψ' hψ') f i hp
  · rw [SState.endAt_shape] at hl''
    simp only at hl''
    split at hl''
    · cases hl''
    · rename_i hpr
      have hp : p ∈ s.positions := (hs.acyc.2.2 p l'' hl'').1
      rw [SState.endAt_valAt s l r _ hp]
      dsimp only
      rw [if_neg hpr, hHT]
      exact hs.holder _ (key ψ' hψ') p l'' hl''
  · rw [hHT, hHM]; exact hs.held l' (SState.endAt_live hl')
  · rw [SState.endAt_shape] at hl'
    simp only at hl'
    split at hl'
    · cases hl'
    · rw [hTy, hHT]; exact hs.holderTy f i l' hl'
  · have := SState.endLabel_rinv hs.acyc l
    rwa [SState.endLabel_eq hh] at this
  · have := SState.readsBelow_endLabel hs.fresh l
    rwa [SState.endLabel_eq hh] at this

theorem endLabel_sgood {s : SState} (hs : SGood dm Γ φ s) (l : Nat) : SGood dm Γ φ (s.endLabel l) := by
  cases h : s.holderOf l with
  | none => rw [SState.endLabel_of_none h]; exact hs
  | some r => rw [SState.endLabel_eq h]; exact endAt_sgood hs h

theorem foldl_endLabel_sgood : ∀ (ls : List Nat) {s : SState}, SGood dm Γ φ s → SGood dm Γ φ (ls.foldl SState.endLabel s)
  | [], _, h => h
  | l :: ls, _, h => foldl_endLabel_sgood ls (endLabel_sgood h l)

/-- **[Access] keeps the invariant**: a fold of ends. -/
theorem access_sgood {s : SState} (hs : SGood dm Γ φ s) (p : Pos) (hit : List Step → Bool) :
    SGood dm Γ φ (s.access p hit) := by
  rw [SState.access_eq, SState.foldl_range_iterR]
  generalize s.liveLabels.length = k
  induction k with
  | zero => exact hs
  | succ k ih => exact foldl_endLabel_sgood _ ih

end

end Ochr.Meaning.Strict
