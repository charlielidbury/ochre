import Ochr.Meaning.Strict.RunS
import Ochr.Meaning.RunPresInd

/-!
# The fundamental lemma's statement

**The invariant** (`SGood dm Γ φ s`, in terms of `SState` alone), at every TYPED future `ψ` of the
state (`TypedF`: `ψ` agrees with the run's future `φ` off the live labels, as the relation compares
states, and gives each live label a possibly partly moved member of the content type recorded for it
when it was made, `heldTy`; partly moved, because a borrow may end with parts of its content moved
out, D53 (h), and its lenders then read those parts moved):
- `bind`: every binding holds a (possibly partly moved) member of its stored type, or is at the error
  type (`GoodRes`: no type known, nothing owed);
- `holder`: every holder of a borrow holds a (possibly partly moved) member of its label's content type;
- `held`: each live label's record (`heldMem`, read by `typedFuture`) is a member of its content type;
- `holderTy`: a binding that holds a borrow is stored at its label's content type;
- `acyc`: the labels are ordered as `RunPresInd`'s invariant orders them (`SState.RInv`: a holder of
  `x` reads no live label `≤ x`), what an end needs (`holderIndep`) and keeps;
- `fresh`: no position reads a label at or above the counter (a new borrow's lender reads a future
  that agrees with the old state's only off it);
- `read`: **the read clause** (`ReadOk`, named on its own: the dependent-values area): every path a
  read can follow from a binding to a whole value gives a member of the type the read gives it.

The reference's temporaries are only borrow holders (typed by their label, `holder`) and a closure
frame's cells (read at the future, owing nothing).

**The fundamental lemma** (`Fund`): from a good state, a successful strict run returns a good result
(a member of the type it returns, or at `err`) whose label, if any, records its type (`LabOk`), and
leaves a good state. A proof's run (`SM.erasedS`) returns `⋆` at a proposition, so its
membership is the proposition's truth (`erasedS_true`).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

/-- A result is good: a whole member of its type, or `⊥`, or a type value at the error type (a type
the bounded model has no universe for, e.g. `Type₁` as a value, whose type `Type₂` means `err`). Only a
TYPE VALUE may sit at `err`: a value at `err` with fields would have them read at real types. -/
def GoodRes (R : DataRead) (r : Res) : Prop :=
  r.1 ∈ₛ[R] r.2.m ∨ r.1 = .moved ∨ (r.2.m = TyM.err ∧ ∃ T, r.1 = .ty T)

/-- A partly moved MEMBER: `⊥`, or a whole member with parts moved out (`pmem` without its `OpenIn`
disjunct: what a live label's final content and a holder's content are). -/
def PMem (R : DataRead) (Γ : List IndDecl) (v : Sem) (T : TyM) : Prop :=
  v = .moved ∨ ∃ t, t.whole ∧ DataModel.MovedOf Γ v t ∧ t ∈ₛ[R] T

theorem PMem.pmem {R : DataRead} {Γ : List IndDecl} {v : Sem} {T : TyM} (h : PMem R Γ v T) : DataModel.pmem R Γ v T := by
  rcases h with h | ⟨t, hw, hm, ht⟩
  · exact .inl h
  · exact .inr ⟨t, hw, hm, .inl ht⟩

/-- A binding's value is good: a (partly moved) member of its stored type, or a type value at `err`. -/
def GoodVal (R : DataRead) (Γ : List IndDecl) (v : Sem) (T : TyM) : Prop :=
  DataModel.pmem R Γ v T ∨ (T = TyM.err ∧ ∃ U, v = .ty U)

section
variable (dm : DataModel) (Γ : List IndDecl) (φ : Future)

/-- A future typed at a state: it agrees with the run's future off the live labels, and gives each
live label a (partly moved) member of its recorded content type. -/
def TypedF (s : SState) (ψ : Future) : Prop :=
  (∀ l, l ∉ s.liveLabels → ψ l = φ l) ∧ ∀ l ∈ s.liveLabels, PMem dm.read Γ (ψ l) (s.heldTy l)

/-- **THE READ CLAUSE** (what the lemma's read case consumes; the dependent-values area): at every
typed future, every path a read can follow from a binding, to a whole value, gives a member of the
type the read gives it (`Sem.follow`: a constructor field by its own record, any other field at its
declaration's type at the current earlier fields), or the type is `err`. At the empty path it says a
binding's whole value is a member of its stored type, so a value OPEN in its type (`pmem`'s `OpenIn`)
breaks it at the root. -/
def ReadOk (s : SState) : Prop :=
  ∀ ψ, TypedF dm Γ φ s ψ → ∀ f i steps x U,
    Sem.follow dm Γ (s.tyAt (.bind f i)) (s.valAt (.bind f i) ψ) steps = some (x, U) → x.whole →
      x ∈ₛ[dm.read] U.m ∨ U.m = TyM.err

/-- **The model-side invariant.** -/
structure SGood (s : SState) : Prop where
  bind : ∀ ψ, TypedF dm Γ φ s ψ → ∀ f i, Pos.bind f i ∈ s.positions →
    GoodVal dm.read Γ (s.valAt (.bind f i) ψ) (s.tyAt (.bind f i)).m
  holder : ∀ ψ, TypedF dm Γ φ s ψ → ∀ p l, s.shape p = some l → PMem dm.read Γ (s.valAt p ψ) (s.heldTy l)
  held : ∀ l ∈ s.liveLabels, s.heldMem l ∈ₛ[dm.read] s.heldTy l
  holderTy : ∀ f i l, s.shape (.bind f i) = some l → (s.tyAt (.bind f i)).m = s.heldTy l
  acyc : SState.RInv (fun _ => True) s
  fresh : s.ReadsBelow
  read : ReadOk dm Γ φ s

/-- A result's label, if any, records the result's type as its content type, and a member as its
record (the label may have ended: a borrow of a binding the result outlived; binding the result makes
it live again, at that record). -/
def LabOk (s : SState) (r : Res) : Prop :=
  ∀ l, r.2.label = some l → s.heldTy l = r.2.m ∧ s.heldMem l ∈ₛ[dm.read] s.heldTy l

/-- A run keeps the invariant. -/
def StatePres {α : Type 3} (x : SM α) : Prop := ∀ s s' r, SGood dm Γ φ s → x s = some (r, s') → SGood dm Γ φ s'

/-- **The fundamental lemma at one run**. -/
def FundAt (x : SM Res) : Prop :=
  ∀ s s' r, SGood dm Γ φ s → x s = some (r, s') → GoodRes dm.read r ∧ LabOk dm s' r ∧ SGood dm Γ φ s'

theorem FundAt.pres {x : SM Res} (h : FundAt dm Γ φ x) : StatePres dm Γ φ x :=
  fun s s' r hs hx => (h s s' r hs hx).2.2

end

/-- **The fundamental lemma at a term**: every strict run of it, at every hint and tail flag. -/
def Fund (K : RunCtx) (ρ : Assignment) (φ : Future) (t : Term) : Prop :=
  ∀ tl hint, FundAt K.dm K.Γ φ (runS K ρ φ tl hint t)

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

theorem goodVal_of_mem (hR : R.WholeFields) (Γ : List IndDecl) {v : Sem} {T : TyM} (h : v ∈ₛ[R] T) :
    GoodVal R Γ v T :=
  .inl (DataModel.pmem_of_mem R Γ (mem_whole hR h) h)

/-- A good result is a good value. -/
theorem GoodRes.val (hR : R.WholeFields) (Γ : List IndDecl) {r : Res} (h : GoodRes R r) : GoodVal R Γ r.1 r.2.m := by
  rcases h with h | h | h
  · exact goodVal_of_mem hR Γ h
  · rw [h]; exact .inl (.inl rfl)
  · exact .inr h

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

