import Ochr.Meaning.Steps.Sim
import Ochr.Meaning.Apply

/-!
# The records: where a label is made (docs/31 D68)

The relation's records clause (`Rel.records`) asks each live label's record to be a whole member of
its holder's content type, so that the future a place is read at (`SState.typedFuture`) is typed.
Records and held types are written once, where a label is made, and a binding holder's stored type
is the held type; so the only obligation with content is the record's membership where a label is
made. Labels are made at three places of the run:
- `borrowPlace`: the record is the content borrowed, read at the typed future after the access,
  held at the type `contentOf` read it at (`borrowPlace_record`, proved). Its membership is
  `borrowPlace_record_mem` (open): it uses the checker's [Borrow] and [Repack] (below).
- `callOf`'s `.ref` row: the record is the forward value `L.enc c fwd`, held at `L.toTy c`
  (`callOfL_record`, proved). It is a member by the encoding (`enc_mem_lvl0/1/2`, proved: nothing
  on the checker's side), and whole when the data model's reading gives whole fields
  (`DataRead.WholeFields`, `enc_whole_lvl0/1/2`, proved from it): a fact about the model, owed
  where the reading is fixed, beside `genericModel`'s coherence `hR`.
- a closure frame's borrow parameter (`bodyAt`, `fixStep`): the argument, decoded at the
  parameter's code by `applyFnL`, so a member of its type. This frame is the closure's meaning's
  run, which no checker state is related to, so the records clause is not asked of it; its record
  matters only to `callOf_inPlace`, where the argument is the caller's borrow and its record the
  caller's.
-/

namespace Ochr.Meaning.Steps
open Ochr Ochr.Meaning

/-- A label's record is a whole member of its holder's content type. -/
def RecordOK (K : RunCtx) (s : SState) (l : Nat) : Prop :=
  (s.heldMem l).whole ∧ s.heldMem l ∈ₛ[K.dm.read] holderTy s l

/-- **The record a borrow makes**: the content it borrowed, whole by `borrowPlace`'s own check, with
the type `contentOf` read it at as its held type. -/
theorem borrowPlace_record (K : RunCtx) (φ : Future) (p : Place) {s s' : SState} {r : Res}
    (h : borrowPlace K φ p s = some (r, s')) :
    ∃ T pos steps s₁, contentOf K φ p s = some ((r.1, T, pos, steps), s₁) ∧ r.2.label = some s₁.nextLoan ∧
      s'.heldMem s₁.nextLoan = r.1 ∧ s'.heldTy s₁.nextLoan = T.m ∧ r.1.whole := by
  unfold borrowPlace at h
  cases hc : contentOf K φ p s with
  | none => rw [hc] at h; cases h
  | some x =>
    obtain ⟨⟨c, T, pos, steps⟩, s₁⟩ := x
    simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
    · rename_i hw
      simp only [Option.some.injEq] at h
      cases h
      refine ⟨T, pos, steps, s₁, rfl, rfl, ?_, ?_, Classical.not_not.mp hw⟩
      · simp [SState.setHeldMem, SState.freshLoan]
      · simp [SState.setHeldMem, SState.setHeldTy, SState.freshLoan]

/-- **The record a borrow makes is a member** (open). At a state related to the checker's, when the
checker's [Borrow] of `p` succeeds, the content the reference's `borrowPlace` records is a member of
the type it is held at. What it uses on the checker's side:
- the reference's content is the meaning of the checker's content of the place, at the typed future
  (`Rel.sim`; after the access the content holds no live loan, so the future does not matter,
  `meanV_congr`), and the reference's type is the checker's place type (the place's grain);
- a WHOLE place: the content is a member of the declared type by the checker's `Membership` at the
  position. It is whole because [Borrow] rejects a partly moved place and [Repack] rejects a whole
  borrow of an open value ("*v is borrowed whole, but it is open", `Regress/RecordSites`);
- a FIELD: the parent is a partial member (`PMem`: a whole member with parts moved out), so the
  field's content is a field of a member's element, a member of its field type at that element's
  earlier fields (the data model's `pack_isSome` with `pack_fields`). `contentOf` reads a field at
  its content's own type (`contentTyS`: a constructor value is typed by what it describes, D29
  point 5 e), except a number, read at the declaration's field type at the earlier fields; a field
  borrowed whole is not open (the [Repack] check above, on the field). -/
theorem borrowPlace_record_mem (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (fuel : Nat)
    (st st' : MState) (s : SState) (p : Place) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (bh : Nat) (hc : Runs (Ochr.borrowPlace fuel p) st bh v st')
    {r : Res} {s' : SState} (h : borrowPlace K φ p s = some (r, s')) :
    ∃ T pos steps s₁, contentOf K φ p s = some ((r.1, T, pos, steps), s₁) ∧ r.1 ∈ₛ[K.dm.read] T.m := by
  sorry

/-! ### The record a borrow-returning call makes -/

/-- The data model's reading gives whole fields: what makes an encoding whole. -/
def _root_.Ochr.Meaning.DataRead.WholeFields (R : DataRead) : Prop :=
  ∀ d ps A a, ∀ f ∈ (R d ps A a).2, Sem.whole f

theorem enc_whole_lvl0 {R : DataRead} (hR : R.WholeFields) : ∀ {A : Type} (c : Code0 A) (a : A),
    ((lvl0 R).enc c a).whole
  | _, .prop _, _ => by simp [Code0.enc, Sem.whole]
  | _, .nat, _ => by simp [Code0.enc, Sem.whole]
  | _, .unit, _ => by simp [Code0.enc, Sem.whole]
  | _, .data d ps A, a => by simpa [Code0.enc, Sem.whole] using hR d _ A a
  | _, .pi _ _, _ => by simp [Code0.enc, Sem.whole]
  | _, .err, x => nomatch x

theorem enc_whole_lvl1 {R : DataRead} (hR : R.WholeFields) : ∀ {A : Type 1} (c : Code1 A) (a : A),
    ((lvl1 R).enc c a).whole
  | _, .lift _ c, a => by simpa [Code1.enc] using enc_whole_lvl0 hR c a.down
  | _, .univ0, _ => by simp [Code1.enc, Sem.whole]
  | _, .univ1, _ => by simp [Code1.enc, Sem.whole]
  | _, .pi _ _, _ => by simp [Code1.enc, Sem.whole]

theorem enc_whole_lvl2 {R : DataRead} (hR : R.WholeFields) : ∀ {A : Type 2} (c : Code2 A) (a : A),
    ((lvl2 R).enc c a).whole
  | _, .lift _ c, a => by simpa [Code2.enc] using enc_whole_lvl1 hR c a.down
  | _, .univ2, _ => by simp [Code2.enc, Sem.whole]
  | _, .pi _ _, _ => by simp [Code2.enc, Sem.whole]

/-- An encoding is a member of its code's type, at each level. -/
theorem enc_mem_lvl0 (R : DataRead) {A : Type} (c : Code0 A) (a : A) :
    (lvl0 R).enc c a ∈ₛ[R] (lvl0 R).toTy c := ⟨a, rfl⟩

theorem enc_mem_lvl1 (R : DataRead) : ∀ {A : Type 1} (c : Code1 A) (a : A),
    (lvl1 R).enc c a ∈ₛ[R] (lvl1 R).toTy c
  | _, .lift _ _, a => ⟨a.down, rfl⟩
  | _, .univ0, a => ⟨a, rfl⟩
  | _, .univ1, a => ⟨a, rfl⟩
  | _, .pi _ _, a => ⟨a, rfl⟩

theorem enc_mem_lvl2 (R : DataRead) : ∀ {A : Type 2} (c : Code2 A) (a : A),
    (lvl2 R).enc c a ∈ₛ[R] (lvl2 R).toTy c
  | _, .lift _ c, a => enc_mem_lvl1 R c a.down
  | _, .univ2, a => ⟨a, rfl⟩
  | _, .pi _ _, a => ⟨a, rfl⟩

/-- **The record a borrow-returning call makes**: the forward value, held at the result's code. -/
theorem callOfL_record.{u} (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} {res : Res} (h : callOfL Lv t fv args s = some (res, s'))
    {U : Type u} {c : Lv.Code U} {fwd : U} {back : U → List Sem}
    (happ : applyFnL Lv t fv (args.map (·.1)) = some (.ref U c fwd back)) :
    ∃ k, res.2.label = some k ∧ s'.heldMem k = Lv.enc c fwd ∧ s'.heldTy k = Lv.toTy c := by
  unfold callOfL at h
  dsimp only at h
  rw [happ] at h
  simp only [SState.freshLoan, Option.some.injEq] at h
  cases h
  exact ⟨_, rfl, by simp [SState.setHeldMem], by simp [SState.setHeldMem, SState.setHeldTy]⟩

end Ochr.Meaning.Steps
