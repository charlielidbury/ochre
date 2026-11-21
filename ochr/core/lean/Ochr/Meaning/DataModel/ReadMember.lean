import Ochr.Meaning.Places

/-!
# Reading along a path: the read lemma (route (c), 2026-11-21)

A read types a field by the type it starts at and the value's own record (`DataModel.readTy`,
`Places.Sem.stepField`), never by a declaration looked up by name. `follow_good`: every read of a
member of ANY data code gives a member of the type the read gives it (or `⋆` or a type value at
`err`), with no hypothesis. It replaces `follow_below_member` (a meaning BELOW a member, under the
coherence `ReadCoherent`), whose by-name read was false off the program's declarations
(`Strict/MemReadsCE`) and whose partly moved form is false under any read typing
(`Strict/ReadProto.not_typed_below`: a field typed at a moved index). `ShapeCanon`, `ReadCoherent`
and `TyIn` stay as the data model's faithfulness notions (the simulation's side).
-/

namespace Ochr.Meaning.DataModel

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

/-- A shape is canonical: a leaf's code is not a data code over the model's own carrier (a data code
over a foreign carrier is an ordinary leaf, docs/34 §18), a data field's declaration is not
`Prop`-sorted, a proof field's is. -/
def ShapeCanon (dm : DataModel) : Shape → Prop
  | .leaf B c => ∀ d r, c.dataCode? = some (d, r) → B ≠ dm.car d r
  | .sub d _ => d.sort ≠ 0
  | .prf d _ => d.sort = 0

/-- **What reading along paths needs of the data model and `Γ`**, on a set `P` of declarations and
records closed under the data and proof fields of the signature. -/
structure ReadCoherent (dm : DataModel) (Γ : List IndDecl) (P : IndDecl → Rec → Prop) : Prop where
  closed : ∀ d r c i e d' r', P d r →
    (dm.sig.shape d r c i e = .sub d' r' ∨ dm.sig.shape d r c i e = .prf d' r') → P d' r'
  found : ∀ d r, P d r → Γ.find? (·.name == d.name) = some d
  notNat : ∀ d r, P d r → d.name ≠ "Nat"
  canon : ∀ d r c i e, P d r → ShapeCanon dm (dm.sig.shape d r c i e)

/-- The fields of a member fit their shapes at the earlier fields, one by one. -/
theorem fitsM_get (S : Sig) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (n i : Nat) (e : List Small) (fs : List Sem), FitsM S d r c i n e fs →
      ∀ (j : Nat) (f : Sem), fs[j]? = some f → FitsOneM S (S.shape d r c (i + j) (e ++ (fs.take j).map Sem.small)) f
  | 0, _, _, fs, h, j, f, hf => by
    have : fs = [] := h
    subst this; simp at hf
  | n + 1, i, e, fs, ⟨f0, fs', hfs, h1, h2⟩, j, f, hf => by
    subst hfs
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      simpa using h1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hf
      have := fitsM_get S d r c n (i + 1) (e ++ [f0.small]) fs' h2 j f hf
      rw [show i + (j + 1) = i + 1 + j by omega]
      simpa [List.take_succ_cons] using this

variable (dm : DataModel)

/-- A member of a data type at any level is a member of its declaration at its record, which the
tree records. -/
theorem mem_dat_inv {T : TyM} {n : String} {r : Rec} {c : Nat} {gs : List Sem}
    (h : Sem.dat n r c gs ∈ₛ[dm.read] T) :
    ∃ d, T.dataCode? = some (d, r) ∧ dm.Mem d r (.dat n r c gs) ∧ d.name = n := by
  have key : ∀ (d : IndDecl) (r' : Rec) (A : Type) (a : A), dm.read.read d r' A a = .dat n r c gs →
      r' = r ∧ dm.Mem d r (.dat n r c gs) ∧ d.name = n := by
    intro d r' A a ha
    change dm.readFn d r' A a = _ at ha
    unfold readFn at ha
    split at ha
    · have hm : dm.Mem d r' (.dat n r c gs) := (dm.mem_iff_meanC d r' _).2 ⟨_, ha⟩
      obtain ⟨_, _, he, _⟩ := (DataLib.mem_iff dm.sig d r' _).1 hm
      simp only [Sem.dat.injEq] at he
      obtain ⟨hn, hr, -⟩ := he
      subst hr
      exact ⟨rfl, hm, hn.symm⟩
    · cases ha
  cases T with
  | t0 A c0 =>
    obtain ⟨a, ha⟩ := h
    cases c0 with
    | data d r' A =>
      obtain ⟨rfl, hm, hn⟩ := key d r' A a ha
      exact ⟨d, rfl, hm, hn⟩
    | prop _ => cases ha
    | nat => cases ha
    | unit => cases ha
    | pi _ _ => cases ha
    | err => exact a.elim
  | t1 A c1 =>
    obtain ⟨a, ha⟩ := h
    cases c1 with
    | lift A' c0 =>
      cases c0 with
      | data d r' A =>
        obtain ⟨rfl, hm, hn⟩ := key d r' _ a.down ha
        exact ⟨d, rfl, hm, hn⟩
      | prop _ => cases ha
      | nat => cases ha
      | unit => cases ha
      | pi _ _ => cases ha
      | err => exact a.down.elim
    | univ0 => cases ha
    | univ1 => cases ha
    | pi _ _ => cases ha
  | t2 A c2 =>
    obtain ⟨a, ha⟩ := h
    cases c2 with
    | lift A' c1 =>
      cases c1 with
      | lift A'' c0 =>
        cases c0 with
        | data d r' A =>
          obtain ⟨rfl, hm, hn⟩ := key d r' _ a.down.down ha
          exact ⟨d, rfl, hm, hn⟩
        | prop _ => cases ha
        | nat => cases ha
        | unit => cases ha
        | pi _ _ => cases ha
        | err => exact a.down.down.elim
      | univ0 => cases ha
      | univ1 => cases ha
      | pi _ _ => cases ha
    | univ2 => cases ha
    | pi _ _ => cases ha

variable {dm} {Γ : List IndDecl} {P : IndDecl → Rec → Prop}

/-- A type all of whose data codes that have a constructor value as a member are in `P` (a data
code over a foreign carrier, a leaf's, has only tagged elements: docs/34 §18). -/
def TyIn (dm : DataModel) (P : IndDecl → Rec → Prop) (U : TyM) : Prop :=
  ∀ d r n c gs, Sem.dat n r c gs ∈ₛ[dm.read] U → U.dataCode? = some (d, r) → P d r

theorem encLeaf_not_dat : ∀ {B : Type} (c : Code0 B) (b : B) (n : String) (r : Rec) (c' : Nat) (fs : List Sem),
    encLeaf c b ≠ .dat n r c' fs
  | _, .prop _, _, _, _, _, _ => by simp [encLeaf]
  | _, .nat, _, _, _, _, _ => by simp [encLeaf]
  | _, .unit, _, _, _, _, _ => by simp [encLeaf]
  | _, .pi _ _, _, _, _, _, _ => by simp [encLeaf]
  | _, .data _ _ _, _, _, _, _, _ => by simp [encLeaf]
  | _, .err, b, _, _, _, _ => nomatch b

theorem movedOfList_get : ∀ {fs gs : List Sem}, MovedOfList Γ fs gs → ∀ (i : Nat) (f : Sem), fs[i]? = some f →
    ∃ g, gs[i]? = some g ∧ MovedOf Γ f g
  | [], [], .nil, _, _, h => by simp at h
  | _ :: _, _ :: _, .cons h1 h2, 0, f, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact ⟨_, rfl, h1⟩
  | _ :: _, _ :: _, .cons _ h2, i + 1, f, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact movedOfList_get h2 i f h

theorem movedOfList_refl : ∀ (fs : List Sem), MovedOfList Γ fs fs
  | [] => .nil
  | f :: fs => .cons (.refl f) (movedOfList_refl fs)

/-! ## The read lemma (route (c): the read typed by the type and the value's record, no hypothesis) -/

/-- What a read gives: a member of its type, or `⋆` or a type value at `err`. -/
def GoodAt (dm : DataModel) (T : TyS) (w : Sem) : Prop :=
  w ∈ₛ[dm.read] T.m ∨ (T.m = TyM.err ∧ ((∃ X, w = .ty X) ∨ w = .proof))

theorem stepField_good {T U : TyS} {c i : Nat} {w x : Sem} (hw : GoodAt dm T w)
    (h : Sem.stepField dm T c i w = some (x, U)) : GoodAt dm U x := by
  unfold Sem.stepField at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, .inr rfl⟩
  · rename_i n r c' fs
    split at h
    · rename_i d r₀ hdc
      split at h
      · rename_i hcond
        obtain ⟨hn, rfl⟩ := hcond
        split at h
        · rename_i f hf
          cases hU : dm.readTy d r c' i (fs.take i) f with
          | none => rw [hU] at h; cases h
          | some U' =>
            rw [hU] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rcases hw with hm | ⟨-, ⟨X, hX⟩ | hX⟩
            · obtain ⟨d₁, hdc₁, hmem, -⟩ := mem_dat_inv dm hm
              rw [hdc] at hdc₁
              simp only [Option.some.injEq, Prod.mk.injEq] at hdc₁
              obtain ⟨rfl, -⟩ := hdc₁
              subst hn
              obtain ⟨⟨c₂, hc₂⟩, fs₂, he, hfits⟩ := (DataLib.mem_iff dm.sig d r _).1 hmem
              simp only [Sem.dat.injEq, true_and] at he
              obtain ⟨hc, rfl⟩ := he
              subst hc
              have hfit := fitsM_get dm.sig d r c' _ 0 [] fs hfits i f hf
              simp only [Nat.zero_add, List.nil_append] at hfit
              rw [dm.readTy_fit hfit] at hU
              exact .inl (dm.fits_readTy hfit hU)
            · cases hX
            · cases hX
        · cases h
      · cases h
    · cases h
  · cases h

theorem step_good {T U : TyS} {st : Step} {w x : Sem} (hw : GoodAt dm T w)
    (h : Sem.step dm Γ T st w = some (x, U)) : GoodAt dm U x := by
  cases st with
  | deref =>
    simp only [Sem.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hw
  | proj i =>
    cases i with
    | zero =>
      simp only [Sem.step] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inl ⟨_, rfl⟩
      · cases h
      · split at h
        · rename_i hT _
          rcases hw with hm | ⟨-, ⟨X, hX⟩ | hX⟩
          · obtain ⟨d₁, hdc, -, -⟩ := mem_dat_inv dm hm
            rw [hT] at hdc; cases hdc
          · cases hX
          · cases hX
        · exact stepField_good hw h
    | succ i => exact stepField_good hw h
  | field g =>
    simp only [Sem.step] at h
    split at h
    · split at h
      · exact stepField_good hw h
      · cases h
    · exact stepField_good hw h

/-- **The read lemma, with no hypothesis**: every read path of a value good at a type (a member, or
no data at `err`) gives a value good at the type the read gives it. Every read of a MEMBER of ANY
data code (declared by the program or not, at any record) gives a member of its type, or `⋆` or a
type value at `err` (`Strict/MemReadsCE`: the by-name read failed exactly here). -/
theorem follow_good : ∀ (steps : List Step) {T U : TyS} {w x : Sem}, GoodAt dm T w →
    Sem.follow dm Γ T w steps = some (x, U) → GoodAt dm U x
  | [], T, U, w, x, hw, h => by
    simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hw
  | st :: sts, T, U, w, x, hw, h => by
    simp only [Sem.follow] at h
    cases hs : Sem.step dm Γ T st w with
    | none => rw [hs] at h; cases h
    | some p =>
      obtain ⟨w', T'⟩ := p
      rw [hs] at h
      exact follow_good sts (step_good hw hs) h

end Ochr.Meaning.DataModel
