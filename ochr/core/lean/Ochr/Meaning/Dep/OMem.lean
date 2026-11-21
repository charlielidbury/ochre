import Ochr.Meaning.Dep.Records
import Ochr.Meaning.DataModel.ReadMember

/-!
# Open membership, field by field, read off records (kernel-checked on cases)

The replacement for partial membership's `OpenIn` disjunct (`DataModel.pmem`), after D112 (main
`f7e46755`: a dependent field that cannot be typed by its content, a leaf, is invalidated by an
index write and checked when assigned; only a tree is typed by what it holds). The type of a
field comes from the parent's TYPE, its declaration and record (`dm.sig.shape d r c i`), never
from a lookup of the value's name, except for a tree that an [Open] strong update stored, which
carries only its name and record. A value `s` is an open member of `T` (`OMem`) when it is
- `moved`;
- a partly moved member: below (`MovedOf`) a whole member of `T` (`member`); or
- a tree of `T`'s declaration and record (`T = tyR d r`, a data sort) whose fields are each
  (`OField`): moved; a partly moved member of the declared shape at SOME completion of the
  earlier fields (`fits`: a leaf, which D112 keeps at its declared type, or a closed tree); a tree
  of the declaration the parent's record names there, open at its own record (`sub`); or a tree
  of a declaration found by name, open at its own type (`byContent`: what a strong update stored).
No whole open value need lie above it (`Records.below_no_member`: `MkV(0, Only(⋆))` and
`MkVM(0, ⊥)` lie below no whole member, and with a field whose type is empty at the current index
no whole value of any kind need lie above a partly moved one), so the notion is structural.

Checked: closed is member (`closed_iff_mem`); a partly moved member is an open member (`OMem.member`, by construction); the reachable
states of `Records` are open members (`omem_belowAt`, `omem_belowMovedAt`); the junk value
`OpenIn` admits is not (`not_omem_junk`); a field of an open value is moved, a partly moved member
of its declared shape's type, or an open member of the type its own tree names (`field_cases`).
-/

namespace Ochr.Meaning.Dep

open Ochr Ochr.Meaning Ochr.Meaning.DataModel Ochr.Meaning.DataLib

mutual
/-- **Open membership** (records, not names, except for a tree stored by content). -/
inductive OMem (dm : DataModel) (Γ : List IndDecl) : Sem → TyM → Prop
  | moved (T : TyM) : OMem dm Γ .moved T
  | member {s : Sem} {T : TyM} (t : Sem) : t.whole → MovedOf Γ s t → t ∈ₛ[dm.read] T → OMem dm Γ s T
  | dat {d : IndDecl} {r : Rec} {c : Nat} {fs : List Sem} :
      d.sort ≠ 0 → c < d.ctors.length → fs.length = arity d c →
      (∀ (i : Nat) (f : Sem), fs[i]? = some f → OField dm Γ d r c i (fs.take i) f) →
      OMem dm Γ (.dat d.name r c fs) (dm.tyR d r)

/-- One field of an open value: by the parent's declaration `d` and record `r`. -/
inductive OField (dm : DataModel) (Γ : List IndDecl) : IndDecl → Rec → Nat → Nat → List Sem → Sem → Prop
  | moved {d r c i e} : OField dm Γ d r c i e .moved
  | fits {d r c i e f} (e' : List Sem) (t : Sem) : MovedOfList Γ e e' → t.whole → MovedOf Γ f t →
      FitsOneM dm.sig (dm.sig.shape d r c i (e'.map Sem.small)) t → OField dm Γ d r c i e f
  | sub {d r c i e} {d' : IndDecl} {r' : Rec} {c' : Nat} {gs : List Sem} (e' : List Sem) (r'' : Rec) :
      MovedOfList Γ e e' → dm.sig.shape d r c i (e'.map Sem.small) = .sub d' r'' →
      OMem dm Γ (.dat d'.name r' c' gs) (dm.tyR d' r') → OField dm Γ d r c i e (.dat d'.name r' c' gs)
  | byContent {d r c i e} {d' : IndDecl} {r' : Rec} {c' : Nat} {gs : List Sem} :
      Γ.find? (·.name == d'.name) = some d' →
      OMem dm Γ (.dat d'.name r' c' gs) (dm.tyR d' r') → OField dm Γ d r c i e (.dat d'.name r' c' gs)
end

/-- **A partly moved member is an open member** (partial membership's member disjunct). -/
theorem omem_of_pmem_member {dm : DataModel} {Γ : List IndDecl} {s t : Sem} {T : TyM}
    (hw : t.whole) (hm : MovedOf Γ s t) (ht : t ∈ₛ[dm.read] T) : OMem dm Γ s T :=
  .member t hw hm ht

/-- A value CLOSED at `tyR d r`: a tree of `d` at `r` each of whose fields fits its declared shape
at the current earlier fields (none moved, none typed by content). [Repack] checks closedness. -/
def Closed (dm : DataModel) (d : IndDecl) (r : Rec) (s : Sem) : Prop :=
  ∃ c fs, s = .dat d.name r c fs ∧ c < d.ctors.length ∧ FitsM dm.sig d r c 0 (arity d c) [] fs

/-- **Closed is member** (at a data sort): the definition of membership, field by field. -/
theorem closed_iff_mem (dm : DataModel) (d : IndDecl) (r : Rec) (hd : d.sort ≠ 0) (s : Sem) :
    Closed dm d r s ↔ s ∈ₛ[dm.read] dm.tyR d r := by
  have hs : (d.sort == 0) = false := by simpa using hd
  rw [DataModel.mem_tyR dm d r hs, DataModel.Mem, mem_iff]
  constructor
  · rintro ⟨c, fs, rfl, hc, hf⟩; exact ⟨⟨c, hc⟩, fs, rfl, hf⟩
  · rintro ⟨⟨c, hc⟩, fs, rfl, hf⟩; exact ⟨c, fs, rfl, hc, hf⟩

/-- **The read clause, one step**: a field of a value open at its declaration's type is moved, a
partly moved member of its declared shape at a completion of the earlier fields, or an open
member of the type its own tree names (the parent's record's declaration, or one found by name). -/
theorem field_cases {dm : DataModel} {Γ : List IndDecl} {d : IndDecl} {r : Rec} {c i : Nat}
    {e : List Sem} {f : Sem} (h : OField dm Γ d r c i e f) :
    f = .moved ∨
    (∃ e' t, MovedOfList Γ e e' ∧ t.whole ∧ MovedOf Γ f t ∧ FitsOneM dm.sig (dm.sig.shape d r c i (e'.map Sem.small)) t) ∨
    (∃ (d' : IndDecl) (r' : Rec) (c' : Nat) (gs : List Sem), f = .dat d'.name r' c' gs ∧ OMem dm Γ f (dm.tyR d' r')) := by
  cases h with
  | moved => exact .inl rfl
  | fits e' t he hw hm hf => exact .inr (.inl ⟨e', t, he, hw, hm, hf⟩)
  | sub _ _ _ _ ho => exact .inr (.inr ⟨_, _, _, _, rfl, ho⟩)
  | byContent _ ho => exact .inr (.inr ⟨_, _, _, _, rfl, ho⟩)

namespace OMemCases

open Ochr.Meaning.DataModel.Program Ochr.Meaning.Dep.Records


theorem onlyOne_mem : onlyOne ∈ₛ[dmP.read] dmP.tyR fin1D (fin1Rec (.el Nat 1)) := by
  refine (DataModel.mem_tyR dmP fin1D _ rfl _).2 ?_
  refine mem_intro fin1D _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem leaf_n : OField dmP progDecls vD vR 0 0 [] (.el0 Nat 0) :=
  .fits [] (.el0 Nat 0) .nil (by simp [Sem.whole]) (.refl _) ⟨0, rfl⟩

theorem shape_x0 : dmP.sig.shape vD vR 0 1 ([Sem.el0 Nat 0].map Sem.small) = .sub fin1D (fin1Rec (.el Nat 0)) := rfl

/-- **`BelowAt`'s value is an open member** (whole, open, below no whole member). -/
theorem omem_belowAt : OMem dmP progDecls (.dat "V" vR 0 [.el0 Nat 0, onlyOne]) (dmP.tyR vD vR) := by
  refine OMem.dat (d := vD) (by decide) (by decide) rfl ?_
  intro i f hf
  match i, hf with
  | 0, hf => simp only [List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf; exact leaf_n
  | 1, hf =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf
    exact OField.sub (d' := fin1D) [.el0 Nat 0] _ (.cons (.refl _) .nil) shape_x0
      (.member _ (by simp [Sem.whole]) (.refl _) onlyOne_mem)
  | _ + 2, hf => simp at hf

/-- **`BelowMovedAt`'s value (its field moved out) is an open member.** -/
theorem omem_belowMovedAt : OMem dmP progDecls (.dat "V" vR 0 [.el0 Nat 0, .moved]) (dmP.tyR vD vR) := by
  refine OMem.dat (d := vD) (by decide) (by decide) rfl ?_
  intro i f hf
  match i, hf with
  | 0, hf => simp only [List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf; exact leaf_n
  | 1, hf =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf
    exact .moved
  | _ + 2, hf => simp at hf

theorem not_mem_fin1_unit : ¬ dmP.Mem fin1D (fin1Rec (.el Nat 0)) (.el0 Unit ()) := by
  intro hm
  obtain ⟨_, _, he, _⟩ := (mem_iff S fin1D _ _).1 hm
  cases he

theorem tyR_dataCode (dm : DataModel) (d : IndDecl) (r : Rec) (hd : d.sort ≠ 0) :
    (dm.tyR d r).dataCode? = some (d, r) := by
  have : (d.sort == 0) = false := by simpa using hd
  simp [DataModel.tyR, this, TyM.dataCode?, Code0.dataCode?]

/-- **The junk value `OpenIn` admits is no open member**: the unit value in `x`, whose type at the
index `0` is `Fin1(0)` by the record, fits no case (and nothing whole of `V` lies above it). -/
theorem not_omem_junk : ¬ OMem dmP progDecls (.dat "V" vR 0 [.el0 Nat 0, .el0 Unit ()]) (dmP.tyR vD vR) := by
  have key2 : ∀ d r c i e f, OField dmP progDecls d r c i e f → d = vD → r = vR → c = 0 → i = 1 →
      e = [.el0 Nat 0] → f = .el0 Unit () → False := by
    intro d r c i e f hof hd hr hc hi he hf
    cases hof with
    | moved => cases hf
    | sub _ _ _ _ _ => cases hf
    | byContent _ _ => cases hf
    | fits e' t hl hw hm hfit =>
      subst hd hr hc hi he hf
      rw [movedOf_el0_inv hm _ _ rfl] at hfit
      cases hl with
      | cons h0 hnil =>
        cases hnil
        rw [movedOf_el0_inv h0 _ _ rfl, shape_x0] at hfit
        exact not_mem_fin1_unit hfit
  have key : ∀ s T, OMem dmP progDecls s T → s = .dat "V" vR 0 [.el0 Nat 0, .el0 Unit ()] →
      T = dmP.tyR vD vR → False := by
    intro s T h hs hT
    cases h with
    | moved => cases hs
    | member t _ hm ht =>
      subst hs hT
      exact Records.below_no_member progDecls _ t hm ht
    | @dat d r c fs hsort _ _ hfs =>
      have hdc := congrArg TyM.dataCode? hT
      rw [tyR_dataCode dmP d r hsort, tyR_dataCode dmP vD vR (by decide)] at hdc
      simp only [Option.some.injEq, Prod.mk.injEq] at hdc
      obtain ⟨rfl, rfl⟩ := hdc
      simp only [Sem.dat.injEq] at hs
      obtain ⟨_, -, rfl, rfl⟩ := hs
      exact key2 _ _ _ _ _ _ (hfs 1 (.el0 Unit ()) rfl) rfl rfl rfl rfl rfl rfl
  exact fun h => key _ _ h rfl rfl

end OMemCases

end Ochr.Meaning.Dep



