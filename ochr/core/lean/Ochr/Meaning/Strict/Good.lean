import Ochr.Meaning.ApplyMem
import Ochr.Meaning.RunPresInd

/-!
# The fundamental lemma's statement

**The invariant** (`SGood dm Γ φ s`, in terms of `SState` alone), at every TYPED future `ψ` of the
state (`TypedF`: `ψ` agrees with the run's future `φ` off the live labels, as the relation compares
states, and gives each live label an open member (`DataModel.OMem`) of the content type recorded for
it when it was made, `heldTy`; open, because a borrow may end with parts of its content moved out,
D53 (h), and its lenders then read those parts moved):
- `bind`: every binding holds an open member of its stored type, or is at the error type (`GoodRes`:
  no type known, nothing owed);
- `holder`: every holder of a borrow holds an open member of its label's content type;
- `held`: each live label's record (`heldMem`, read by `typedFuture`) is a member of its content type;
- `holderTy`: a binding that holds a borrow is stored at its label's content type;
- `acyc`: the labels are ordered as `RunPresInd`'s invariant orders them (`SState.RInv`: a holder of
  `x` reads no live label `≤ x`), what an end needs (`holderIndep`) and keeps;
- `fresh`: no position reads a label at or above the counter (a new borrow's lender reads a future
  that agrees with the old state's only off it);
- (no read clause since the dependent-values unit: a read is strict, `Run.ReadGood`, and the
  positions hold OPEN members, `DataModel.OMem`, which a read need not give whole.)

The reference's temporaries are only borrow holders (typed by their label, `holder`) and a closure
frame's cells (read at the future, owing nothing).

**The fundamental lemma** (`Fund`): from a good state, a successful strict run returns a good result
(a member of the type it returns, or at `err`) whose label, if any, records its type (`LabOk`) and is live or read
by no position (`LoU`, as `RunPresInd` has it), and leaves a good state. A proof's run (`SM.erasedIf`) returns `⋆` at a proposition, so its
membership is the proposition's truth (`erasedS_true`).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

/-- A value with no data inside: a type value or `⋆`. Only such a value may sit at the error type: a
value at `err` with fields would have them read at real types. -/
def NoData (v : Sem) : Prop := (∃ T, v = .ty T) ∨ v = .proof

/-- A result is good: a whole member of its type, or `⊥`, or a value with no data at the error type
(a type the bounded model has no universe for, e.g. `Type₁` as a value, whose type `Type₂` means `err`;
a field of `⋆`, which a read types `err`). -/
def GoodRes (R : DataRead) (r : Res) : Prop :=
  r.1 ∈ₛ[R] r.2.m ∨ r.1 = .moved ∨ (r.2.m = TyM.err ∧ NoData r.1)

/-- What a live label's final content and a holder's content are: an OPEN member (`DataModel.OMem`,
the dependent-values unit; it was a partly moved member, which reads wrong types once an index is
moved, `ReadProto.not_memReads_dep`). -/
def PMem (dm : DataModel) (Γ : List IndDecl) (v : Sem) (T : TyM) : Prop := dm.pmem Γ v T

theorem PMem.pmem {dm : DataModel} {Γ : List IndDecl} {v : Sem} {T : TyM} (h : PMem dm Γ v T) : dm.pmem Γ v T := h

/-- A binding's value is good: an open member of its stored type, or a type value at `err`. -/
def GoodVal (dm : DataModel) (Γ : List IndDecl) (v : Sem) (T : TyM) : Prop :=
  dm.pmem Γ v T ∨ (T = TyM.err ∧ NoData v)

section
variable (dm : DataModel) (Γ : List IndDecl) (φ : Future)

/-- A future typed at a state: it agrees with the run's future off the live labels, and gives each
live label an open member of its recorded content type. -/
def TypedF (s : SState) (ψ : Future) : Prop :=
  (∀ l, l ∉ s.liveLabels → ψ l = φ l) ∧ ∀ l ∈ s.liveLabels, PMem dm Γ (ψ l) (s.heldTy l)

/-- **The model-side invariant.** -/
structure SGood (s : SState) : Prop where
  bind : ∀ ψ, TypedF dm Γ φ s ψ → ∀ f i, Pos.bind f i ∈ s.positions →
    GoodVal dm Γ (s.valAt (.bind f i) ψ) (s.tyAt (.bind f i)).m
  holder : ∀ ψ, TypedF dm Γ φ s ψ → ∀ p l, s.shape p = some l → PMem dm Γ (s.valAt p ψ) (s.heldTy l)
  held : ∀ l ∈ s.liveLabels, s.heldMem l ∈ₛ[dm.read] s.heldTy l
  holderTy : ∀ f i l, s.shape (.bind f i) = some l → (s.tyAt (.bind f i)).m = s.heldTy l
  acyc : SState.RInv (fun _ => True) s
  fresh : s.ReadsBelow

/-- A result's label, if any, records the result's type as its content type, and a member as its
record (the label may have ended: a borrow of a binding the result outlived; binding the result makes
it live again, at that record). -/
def LabOk (s : SState) (r : Res) : Prop :=
  ∀ l, r.2.label = some l → s.heldTy l = r.2.m ∧ s.heldMem l ∈ₛ[dm.read] s.heldTy l

/-- A run keeps the invariant. -/
def StatePres {α : Type 3} (x : SM α) : Prop := ∀ s s' r, SGood dm Γ φ s → x s = some (r, s') → SGood dm Γ φ s'

/-- **The fundamental lemma at one run**. -/
def FundAt (x : SM Res) : Prop :=
  ∀ s s' r, SGood dm Γ φ s → x s = some (r, s') →
    GoodRes dm.read r ∧ LabOk dm s' r ∧ LoU s' r.2.label ∧ SGood dm Γ φ s'

theorem FundAt.pres {x : SM Res} (h : FundAt dm Γ φ x) : StatePres dm Γ φ x :=
  fun s s' r hs hx => (h s s' r hs hx).2.2.2

end

/-- **The fundamental lemma at a term**: every strict run of it, at every hint and tail flag. -/
def Fund (K : RunCtx) (ρ : Assignment) (φ : Future) (t : Term) : Prop :=
  ∀ tl hint, FundAt K.dm K.Γ φ (runT K ρ φ tl hint t)

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

theorem goodVal_of_mem {dm : DataModel} (_hR : dm.read.WholeFields) (Γ : List IndDecl) {v : Sem} {T : TyM}
    (h : v ∈ₛ[dm.read] T) : GoodVal dm Γ v T :=
  .inl (.mem h)

/-- A good result is a good value. -/
theorem GoodRes.val {dm : DataModel} (hR : dm.read.WholeFields) (Γ : List IndDecl) {r : Res}
    (h : GoodRes dm.read r) : GoodVal dm Γ r.1 r.2.m := by
  rcases h with h | h | h
  · exact goodVal_of_mem hR Γ h
  · rw [h]; exact .inl (.moved _)
  · exact .inr h

/-- `MovedOf` below `⋆` is `⋆` itself. -/
theorem movedOf_proof {Γ : List IndDecl} {t : Sem} (h : DataModel.MovedOf Γ .proof t) : t = .proof := by
  cases h
  rfl

/-- **An open member that is `⋆` is a member**: no part of a proof is moved or open. -/
theorem mem_of_pmem_proof {dm : DataModel} {Γ : List IndDecl} {T : TyM} (h : dm.pmem Γ .proof T) :
    Sem.proof ∈ₛ[dm.read] T := by
  cases h with
  | mem h => exact h

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

/-- **A named fact the simulation may use (the checker's rule, D98; D53 for a parameter's borrow at
the function's end): no borrow ends over moved-out content.** On a reference state related to a state
the checker reaches, the holder of a label about to end holds a WHOLE value at every typed future. The
fundamental lemma does not need it (its typed futures give live labels open members, and
`endAt_sgood` holds without it); the simulation may use it where it wants an ended borrow's content
whole (e.g. to relate the reference's lenders after an end to the checker's, at whole-member
futures). Not proved here: it is a fact about the checker, to be read off `Machine` by the simulation
side. -/
def EndWhole (dm : DataModel) (Γ : List IndDecl) (φ : Future) (s : SState) (l : Nat) : Prop :=
  ∀ r, s.holderOf l = some r → ∀ ψ, TypedF dm Γ φ s ψ → (s.valAt r ψ).whole

end Ochr.Meaning.Strict
