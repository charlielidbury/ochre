import Ochr.Meaning.Strict.RunS
import Ochr.Meaning.RunPresInd

/-!
# The fundamental lemma's statement (prototype)

**The invariant** (`SGood`, in terms of `SState` alone): under every TYPED future (`TypedF`: each
live label ends at a possibly partly moved member of the content type recorded for it when it was
made, `heldTy`; partly moved, because a borrow may end with parts of its content moved out, D53 (h),
and its lenders then read those parts moved),
- every binding holds a (possibly partly moved) member of its stored type, or is at the error type
  (`GoodRes`: no type known, nothing owed);
- every holder of a borrow holds a (possibly partly moved) member of its label's content type;
- each live label's record (`heldMem`, read by `typedFuture`) is a member of its content type;
- a binding that holds a borrow is stored at its label's content type;
- the labels are ordered as `RunPresInd`'s invariant orders them (`SState.RInv`, at every label:
  a holder of `x` reads no live label `≤ x`): what an end needs, since the lenders then read the
  holder's content, which must not read the label being ended (`holderIndep`), and what keeps that
  true after the end (no cycle of holders reading each other's labels).

A temporary has no stored type in `SState`; the reference's temporaries are only borrow holders
(typed by their label, `holder`) and a closure frame's cells (read at the future, owing nothing).

**The fundamental lemma** (`Fund`): from a good state, a successful strict run returns a good result
(a member of the type it returns, or at `err`) and leaves a good state. A proof's run (`SM.erasedS`)
returns `⋆` at a proposition, so its membership is the proposition's truth (`erasedS_true`).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable (R : DataRead) (Γ : List IndDecl)

/-- A result is good: a (partly moved) member of its type, or at the error type. -/
def GoodRes (r : Res) : Prop := DataModel.pmem R Γ r.1 r.2.m ∨ r.2.m = TyM.err

/-- A future typed at a state: each live label ends at a (partly moved) member of its recorded
content type. Every future `Membership`'s `TypedFuture` admits is one (a member is a partly moved
member), so the invariant at these futures gives it at those. -/
def TypedF (s : SState) (ψ : Future) : Prop := ∀ l ∈ s.liveLabels, DataModel.pmem R Γ (ψ l) (s.heldTy l)

/-- **The model-side invariant.** -/
structure SGood (s : SState) : Prop where
  /-- every binding holds a good value at its stored type, under every typed future -/
  bind : ∀ ψ, TypedF R Γ s ψ → ∀ f i, GoodRes R Γ (s.valAt (.bind f i) ψ, s.tyAt (.bind f i))
  /-- every holder holds a (partly moved) member of its label's content type -/
  holder : ∀ ψ, TypedF R Γ s ψ → ∀ p l, s.shape p = some l → DataModel.pmem R Γ (s.valAt p ψ) (s.heldTy l)
  /-- each live label's record is a member of its content type (so `typedFuture` is typed) -/
  held : ∀ l ∈ s.liveLabels, s.heldMem l ∈ₛ[R] s.heldTy l
  /-- a binding holding a borrow is stored at its label's content type -/
  holderTy : ∀ f i l, s.shape (.bind f i) = some l → (s.tyAt (.bind f i)).m = s.heldTy l
  /-- the labels are ordered (`RunPresInd`'s invariant, at every label) -/
  acyc : SState.RInv (fun _ => True) s

/-- A run keeps the invariant. -/
def StatePres {α : Type 3} (x : SM α) : Prop := ∀ s s' r, SGood R Γ s → x s = some (r, s') → SGood R Γ s'

/-- **The fundamental lemma at one run**: from a good state, a successful run returns a good result
and leaves a good state. -/
def FundAt (x : SM Res) : Prop :=
  ∀ s s' r, SGood R Γ s → x s = some (r, s') → GoodRes R Γ r ∧ SGood R Γ s'

theorem FundAt.pres {x : SM Res} (h : FundAt R Γ x) : StatePres R Γ x :=
  fun s s' r hs hx => (h s s' r hs hx).2

end

/-- **The fundamental lemma at a term**: every strict run of it, at every hint and tail flag. -/
def Fund (K : RunCtx) (ρ : Assignment) (φ : Future) (t : Term) : Prop :=
  ∀ tl hint, FundAt K.dm.read K.Γ (runS K ρ φ tl hint t)

/-! ## Members are whole; a proof's membership -/

section
variable {R : DataRead}

theorem enc0_whole (hR : R.WholeFields) : ∀ {A : Type} (c : Code0 A) (a : A), (c.enc R a).whole
  | _, .prop _, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]
  | _, .nat, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]
  | _, .unit, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]
  | _, .data d r A, a => hR d r A a
  | _, .pi _ _, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]
  | _, .err, a => nomatch a

theorem enc1_whole (hR : R.WholeFields) : ∀ {A : Type 1} (c : Code1 A) (a : A), (c.enc R a).whole
  | _, .lift _ c, a => enc0_whole hR c a.down
  | _, .univ0, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]
  | _, .univ1, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]
  | _, .pi _ _, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]

theorem enc2_whole (hR : R.WholeFields) : ∀ {A : Type 2} (c : Code2 A) (a : A), (c.enc R a).whole
  | _, .lift _ c, a => enc1_whole hR c a.down
  | _, .univ2, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]
  | _, .pi _ _, _ => by simp [Code0.enc, Code1.enc, Code2.enc, Sem.whole]

/-- **A member is whole** (where the reading gives whole fields, as the data model's does). -/
theorem mem_whole (hR : R.WholeFields) {v : Sem} {T : TyM} (h : v ∈ₛ[R] T) : v.whole := by
  cases T with
  | t0 A c => obtain ⟨a, rfl⟩ := h; exact enc0_whole hR c a
  | t1 A c => obtain ⟨a, rfl⟩ := h; exact enc1_whole hR c a
  | t2 A c => obtain ⟨a, rfl⟩ := h; exact enc2_whole hR c a

theorem goodRes_of_mem (hR : R.WholeFields) (Γ : List IndDecl) {r : Res} (h : r.1 ∈ₛ[R] r.2.m) :
    GoodRes R Γ r :=
  .inl (DataModel.pmem_of_mem R Γ (mem_whole hR h) h)

/-- `MovedOf` below `⋆` is `⋆` itself. -/
theorem movedOf_proof {Γ : List IndDecl} {t : Sem} (h : DataModel.MovedOf Γ .proof t) : t = .proof := by
  cases h
  rfl

/-- **A partly moved member that is `⋆` is a member**: no part of a proof is moved. -/
theorem mem_of_pmem_proof {Γ : List IndDecl} {T : TyM} (h : DataModel.pmem R Γ .proof T) : Sem.proof ∈ₛ[R] T := by
  rcases h with h | ⟨t, _, hm, ht | ho⟩
  · cases h
  · rw [movedOf_proof hm] at ht; exact ht
  · rw [movedOf_proof hm] at ho
    cases T with
    | t0 A c => cases c <;> exact ho.elim
    | t1 _ _ => exact ho.elim
    | t2 _ _ => exact ho.elim

end

end Ochr.Meaning.Strict

/-! ## State operations: types are kept -/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

theorem tyAt_mapVals (s : SState) (g : Pos → SVal → SVal) (q : Pos) : (s.mapVals g).tyAt q = s.tyAt q := by
  cases q with
  | temp => rfl
  | bind f i =>
    simp only [SState.mapVals, SState.tyAt, List.getElem?_map, List.getElem?_zipIdx]
    cases s.env[f]? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, Option.bind_some, List.getElem?_map, List.getElem?_zipIdx]
      cases fr.binds[i]? <;> rfl

theorem tyAt_setAt (s : SState) (p : Pos) (g : SVal) (q : Pos) : (s.setAt p g).tyAt q = s.tyAt q := by
  cases q with
  | temp => rfl
  | bind f' i' =>
    cases p with
    | bind f i =>
      simp only [SState.setAt, SState.tyAt, List.getElem?_modify]
      cases hfr : s.env[f']? with
      | none => rfl
      | some fr =>
        by_cases hf : f = f'
        · simp only [Option.map_eq_map, Option.map_some, hf, if_true, Option.bind_some, List.getElem?_modify]
          cases fr.binds[i']? with
          | none => rfl
          | some b => simp only [Option.map_eq_map, Option.map_some]; split <;> rfl
        · simp only [Option.map_eq_map, Option.map_some, hf, if_false, Option.bind_some]
    | temp f i =>
      simp only [SState.setAt, SState.tyAt, List.getElem?_modify]
      cases hfr : s.env[f']? with
      | none => rfl
      | some fr =>
        by_cases hf : f = f' <;> simp only [Option.map_eq_map, Option.map_some, hf, if_true, if_false, Option.bind_some]

theorem tyAt_endLabel (s : SState) (l : Nat) (q : Pos) : (s.endLabel l).tyAt q = s.tyAt q := by
  unfold SState.endLabel
  split
  · rw [tyAt_mapVals]; rfl
  · rfl

theorem tyAt_foldl_endLabel : ∀ (ls : List Nat) (s : SState) (q : Pos), (ls.foldl SState.endLabel s).tyAt q = s.tyAt q
  | [], _, _ => rfl
  | l :: ls, s, q => by rw [List.foldl_cons, tyAt_foldl_endLabel ls, tyAt_endLabel]

/-- [Access] keeps every stored type (it ends borrows, which rewrites meanings only). -/
theorem tyAt_access (s : SState) (p : Pos) (hit : List Step → Bool) (q : Pos) : (s.access p hit).tyAt q = s.tyAt q := by
  unfold SState.access
  generalize List.range s.liveLabels.length = ns
  induction ns generalizing s with
  | nil => rfl
  | cons n ns ih => rw [List.foldl_cons, ih, tyAt_foldl_endLabel]

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {R : DataRead} {Γ : List IndDecl}

theorem liveLabels_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).liveLabels = s.liveLabels := by
  unfold SState.liveLabels; rw [SState.positions_setAt, SState.shape_setAt]

theorem heldTy_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).heldTy = s.heldTy := by
  cases p <;> rfl

theorem heldMem_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).heldMem = s.heldMem := by
  cases p <;> rfl

theorem typedF_setAt {s : SState} {p : Pos} {g : SVal} {ψ : Future} :
    TypedF R Γ (s.setAt p g) ψ ↔ TypedF R Γ s ψ := by
  unfold TypedF; rw [liveLabels_setAt, heldTy_setAt]

/-- **A binding written whole with a member of its stored type** (an assignment's write through a
borrow, `*r := v`, writes the holder's content whole) keeps the invariant: where the binding holds a
borrow, its stored type is the label's content type (`holderTy`), so the value is a member of that too. -/
theorem sgood_setAt_const (hR : R.WholeFields) {s : SState} {f i : Nat} {v : Sem} (hs : SGood R Γ s)
    (hv : v ∈ₛ[R] (s.tyAt (.bind f i)).m) : SGood R Γ (s.setAt (.bind f i) fun _ => v) := by
  have hpos : Pos.bind f i ∈ s.positions := by
    by_cases hn : Pos.bind f i ∈ s.positions
    · exact hn
    exfalso
    have e : s.tyAt (.bind f i) = .plain TyM.err := by
      rw [SState.mem_positions] at hn
      simp only [SState.lookup, Option.isSome_iff_exists, not_exists] at hn
      simp only [SState.tyAt]
      cases hb : s.env[f]?.bind (·.binds[i]?) with
      | none => rfl
      | some b => exact absurd (by rw [Option.map_eq_some_iff]; exact ⟨b, hb, rfl⟩) (hn _)
    rw [e] at hv
    exact DataModel.err_mem_false R v hv
  have hval : ∀ q ψ, (s.setAt (.bind f i) fun _ => v).valAt q ψ = if q = .bind f i then v else s.valAt q ψ := by
    intro q ψ
    split
    · subst q; rw [valAt_setAt_self s _ _ hpos]
    · rename_i hq; rw [SState.valAt_setAt_ne s _ _ q (Ne.symm hq)]
  refine ⟨fun ψ hψ f' i' => ?_, fun ψ hψ p l hl => ?_, ?_, fun f' i' l hl => ?_, ?_⟩
  · rw [typedF_setAt] at hψ
    show GoodRes R Γ ((s.setAt _ _).valAt _ ψ, (s.setAt _ _).tyAt _)
    rw [hval, tyAt_setAt]
    split
    · rename_i hq; rw [hq]; exact goodRes_of_mem hR Γ hv
    · exact hs.bind ψ hψ f' i'
  · rw [typedF_setAt] at hψ
    rw [SState.shape_setAt] at hl
    rw [hval]
    split
    · rename_i hq; subst hq
      rw [heldTy_setAt, ← hs.holderTy f i l hl]
      exact DataModel.pmem_of_mem R Γ (mem_whole hR hv) hv
    · rw [heldTy_setAt]; exact hs.holder ψ hψ p l hl
  · rw [liveLabels_setAt, heldTy_setAt, heldMem_setAt]; exact hs.held
  · rw [SState.shape_setAt] at hl; rw [tyAt_setAt, heldTy_setAt]; exact hs.holderTy f' i' l hl
  · refine SState.setAt_rinv hs.acyc _ _ (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

end

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

/-- A holder's meaning does not read its own label (from the label order). -/
theorem SGood.holderIndep {R : DataRead} {Γ : List IndDecl} {s : SState} (hs : SGood R Γ s) {p : Pos} {l : Nat}
    (hl : s.shape p = some l) : Indep l (s.valAt p) := by
  obtain ⟨-, h2, hsa⟩ := hs.acyc
  refine (h2 p l (hsa p l hl).1 hl).indep ?_
  rintro (⟨-, hn⟩ | ⟨-, hlt⟩)
  · exact hn ((SState.live_iff s l).2 ⟨p, (hsa p l hl).1, hl⟩)
  · exact Nat.lt_irrefl l hlt

end Ochr.Meaning.Strict

namespace Ochr.Meaning.Strict
open Ochr.Meaning

/-- **An end keeps the invariant** (`endAt`: the holder `r` of `l` reads `⊥`, every other position its
old meaning at `ψ := ψ'.upd l (r's content at ψ')`). That `ψ` is typed for the state before: at `l`,
`r`'s content is a partly moved member of `heldTy l` (`holder`, at `ψ'` with `l` set to its record,
which `r` does not read, `holderIndep`), and elsewhere it is `ψ'`, whose live labels the end kept.
This is why the typed futures give a live label a PARTLY moved member: a borrow may end with parts of
its content moved out (D53 (h)), and its lenders then read those parts moved. -/
theorem endAt_sgood {R : DataRead} {Γ : List IndDecl} (hR : R.WholeFields) {s : SState} {l : Nat} {r : Pos}
    (hs : SGood R Γ s) (hh : s.holderOf l = some r) : SGood R Γ (s.endAt l r) := by
  have hr : s.shape r = some l := (SState.holderOf_spec hh).2
  have hTy : ∀ q, (s.endAt l r).tyAt q = s.tyAt q := fun q => by unfold SState.endAt; rw [tyAt_mapVals]; rfl
  have hHT : (s.endAt l r).heldTy = s.heldTy := rfl
  have hHM : (s.endAt l r).heldMem = s.heldMem := rfl
  -- a future typed after the end, read before it
  have key : ∀ ψ', TypedF R Γ (s.endAt l r) ψ' → TypedF R Γ s (ψ'.upd l (s.valAt r ψ')) := by
    intro ψ' hψ' l' hl'
    by_cases e : l' = l
    · subst e
      rw [Future.upd_same]
      have hm : DataModel.pmem R Γ (s.heldMem l') (s.heldTy l') := DataModel.pmem_of_mem R Γ (mem_whole hR (hs.held l' hl')) (hs.held l' hl')
      have ht : TypedF R Γ s (ψ'.upd l' (s.heldMem l')) := by
        intro y hy
        by_cases ey : y = l'
        · subst ey; rw [Future.upd_same]; exact hm
        · rw [Future.upd_other _ _ ey]
          have := hψ' y (SState.live_endAt hr hy ey); rwa [hHT] at this
      have := hs.holder _ ht r l' hr
      rwa [hs.holderIndep hr ψ' (s.heldMem l')] at this
    · rw [Future.upd_other _ _ e]
      have := hψ' l' (SState.live_endAt hr hl' e); rwa [hHT] at this
  refine ⟨fun ψ' hψ' f i => ?_, fun ψ' hψ' p l'' hl'' => ?_, fun l' hl' => ?_, fun f i l' hl' => ?_, ?_⟩
  · show GoodRes R Γ ((s.endAt l r).valAt _ ψ', (s.endAt l r).tyAt _)
    rw [hTy]
    by_cases hp : Pos.bind f i ∈ s.positions
    · rw [SState.endAt_valAt s l r _ hp]
      split
      · exact .inl (.inl rfl)
      · exact hs.bind _ (key ψ' hψ') f i
    · rw [SState.endAt_valAt_not_mem s l r _ hp]
      have := hs.bind _ (key ψ' hψ') f i
      rwa [SState.valAt_of_not_mem s _ hp] at this ⊢
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

theorem endLabel_sgood {R : DataRead} {Γ : List IndDecl} (hR : R.WholeFields) {s : SState} (hs : SGood R Γ s)
    (l : Nat) : SGood R Γ (s.endLabel l) := by
  cases h : s.holderOf l with
  | none => rw [SState.endLabel_of_none h]; exact hs
  | some r =>
    rw [SState.endLabel_eq h]
    exact endAt_sgood hR hs h

theorem foldl_endLabel_sgood {R : DataRead} {Γ : List IndDecl} (hR : R.WholeFields) :
    ∀ (ls : List Nat) {s : SState}, SGood R Γ s → SGood R Γ (ls.foldl SState.endLabel s)
  | [], _, h => h
  | l :: ls, _, h => foldl_endLabel_sgood hR ls (endLabel_sgood hR h l)

/-- **[Access] keeps the invariant**: a fold of ends. -/
theorem access_sgood {R : DataRead} {Γ : List IndDecl} (hR : R.WholeFields) {s : SState} (hs : SGood R Γ s)
    (p : Pos) (hit : List Step → Bool) : SGood R Γ (s.access p hit) := by
  rw [SState.access_eq, SState.foldl_range_iterR]
  generalize s.liveLabels.length = k
  induction k with
  | zero => exact hs
  | succ k ih => exact foldl_endLabel_sgood hR _ ih

end Ochr.Meaning.Strict
