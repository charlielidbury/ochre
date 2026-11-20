import Ochr.Meaning.Dep.Records
import Ochr.Meaning.DataModel.ReadMember

/-!
# Membership of an opened, partly moved value, field by field (a candidate; kernel-checked on cases)

The candidate to replace partial membership's `OpenIn` disjunct (`DataModel.pmem`), under the
route where every dependent field that holds a leaf (a number, the unit, a function, a proof) is
invalidated by a write to its index and checked when assigned, so that a leaf is always of its
declared type at the earlier fields (`Dep/HANDOFF.md`, route B). A value is `moved`, a whole
member, or a tree of the type's declaration and record whose fields are each:
- moved;
- a tree, open-member of the type its own name and record give it (by content: the type the
  checker's `depFieldType` gives a field that does not fit its declared type);
- a leaf that is a member of its declared field type at SOME completion of the earlier fields (the
  earlier fields as they were before parts of them were moved out; when they are whole it is the
  type the read gives).
No whole member need lie above it: `MkV(0, Only(⋆))` has none (`Records.below_no_member`).
Checked here: it holds of the two reachable states of `Records` (`BelowAt`, `BelowMovedAt`) and
fails of the junk value `OpenIn` admits (`Records.open_admits_any`).
-/

namespace Ochr.Meaning.Dep

open Ochr Ochr.Meaning Ochr.Meaning.DataModel Ochr.Meaning.DataLib

mutual
/-- **Open membership** (candidate). -/
inductive OMem (dm : DataModel) (Γ : List IndDecl) : Sem → TyM → Prop
  | moved (T : TyM) : OMem dm Γ .moved T
  | mem {s : Sem} {T : TyM} : s ∈ₛ[dm.read] T → OMem dm Γ s T
  | dat {d : IndDecl} {r : Rec} {c : Nat} {fs : List Sem} :
      Γ.find? (·.name == d.name) = some d → d.sort ≠ 0 → c < d.ctors.length → fs.length = arity d c →
      (∀ (i : Nat) (f : Sem), fs[i]? = some f → OField dm Γ d r c i (fs.take i) f) →
      OMem dm Γ (.dat d.name r c fs) (dm.tyR d r)

/-- One field of an open value (candidate). -/
inductive OField (dm : DataModel) (Γ : List IndDecl) : IndDecl → Rec → Nat → Nat → List Sem → Sem → Prop
  | moved {d r c i e} : OField dm Γ d r c i e .moved
  | tree {d r c i e} {n : String} {r' : Rec} {c' : Nat} {gs : List Sem} {d' : IndDecl} :
      Γ.find? (·.name == n) = some d' → OMem dm Γ (.dat n r' c' gs) (dm.tyR d' r') →
      OField dm Γ d r c i e (.dat n r' c' gs)
  | leaf {d r c i e} {f : Sem} : (∀ n r' c' gs, f ≠ .dat n r' c' gs) →
      (∃ e', MovedOfList Γ e e' ∧ f ∈ₛ[dm.read] dm.fieldTyR d r c i e') →
      OField dm Γ d r c i e f
end


namespace OMemCases

open Ochr.Meaning.DataModel.Program Ochr.Meaning.Dep.Records

theorem find_V : progDecls.find? (·.name == vD.name) = some vD := rfl
theorem find_Fin1 : progDecls.find? (·.name == "Fin1") = some fin1D := rfl
theorem fieldTy_n : dmP.fieldTyR vD vR 0 0 [] = TyM.nat := rfl
theorem fieldTy_x0 : dmP.fieldTyR vD vR 0 1 [.el0 Nat 0] = dmP.tyR fin1D (fin1Rec (.el Nat 0)) := rfl

theorem onlyOne_mem : onlyOne ∈ₛ[dmP.read] dmP.tyR fin1D (fin1Rec (.el Nat 1)) := by
  refine (DataModel.mem_tyR dmP fin1D _ rfl _).2 ?_
  refine mem_intro fin1D _ ⟨0, by decide⟩ _ ?_
  exact ⟨_, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩

theorem leaf_n : OField dmP progDecls vD vR 0 0 [] (.el0 Nat 0) :=
  .leaf (fun _ _ _ _ h => by cases h) ⟨[], .nil, by rw [fieldTy_n]; exact ⟨0, rfl⟩⟩

/-- **`BelowAt`'s value is an open member** (whole, open, below no whole member). -/
theorem omem_belowAt : OMem dmP progDecls (.dat "V" vR 0 [.el0 Nat 0, onlyOne]) (dmP.tyR vD vR) := by
  refine OMem.dat (d := vD) find_V (by decide) (by decide) rfl ?_
  intro i f hf
  match i, hf with
  | 0, hf => simp only [List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf; exact leaf_n
  | 1, hf =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf
    exact .tree find_Fin1 (.mem onlyOne_mem)
  | _ + 2, hf => simp at hf

/-- **`BelowMovedAt`'s value (its field moved out) is an open member.** -/
theorem omem_belowMovedAt : OMem dmP progDecls (.dat "V" vR 0 [.el0 Nat 0, .moved]) (dmP.tyR vD vR) := by
  refine OMem.dat (d := vD) find_V (by decide) (by decide) rfl ?_
  intro i f hf
  match i, hf with
  | 0, hf => simp only [List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf; exact leaf_n
  | 1, hf =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf
    exact .moved
  | _ + 2, hf => simp at hf


theorem not_mem_fin1_leaf : ¬ (Sem.el0 Unit () ∈ₛ[dmP.read] dmP.tyR fin1D (fin1Rec (.el Nat 0))) := by
  intro h
  have hm := (DataModel.mem_tyR dmP fin1D _ rfl _).1 h
  obtain ⟨_, _, he, _⟩ := (mem_iff S fin1D _ _).1 hm
  cases he

theorem leaf_x0_false {e e' : List Sem} {f : Sem} (hf : f = .el0 Unit ())
    (he : e = [.el0 Nat 0]) (hl : MovedOfList progDecls e e') (hm : f ∈ₛ[dmP.read] dmP.fieldTyR vD vR 0 1 e') :
    False := by
  subst hf he
  cases hl with
  | cons h0 hnil =>
    cases hnil
    rw [movedOf_el0_inv h0 _ _ rfl, fieldTy_x0] at hm
    exact not_mem_fin1_leaf hm

/-- **The junk value `OpenIn` admits is no open member**: a leaf in `x` must be a member of
`Fin1(0)`'s code, which has only trees (and is empty). -/
theorem not_omem_junk : ¬ OMem dmP progDecls (.dat "V" vR 0 [.el0 Nat 0, .el0 Unit ()]) (dmP.tyR vD vR) := by
  have key : ∀ s T, OMem dmP progDecls s T → s = .dat "V" vR 0 [.el0 Nat 0, .el0 Unit ()] →
      T = dmP.tyR vD vR → False := by
    intro s T h hs hT
    cases h with
    | moved => cases hs
    | mem hm =>
      subst hs hT
      exact v_index_zero_empty _ ((DataModel.mem_tyR dmP vD vR rfl _).1 hm)
    | @dat d r c fs hfind _ _ _ hfs =>
      simp only [Sem.dat.injEq] at hs
      obtain ⟨hn, rfl, rfl, rfl⟩ := hs
      have hd : d = vD := by
        rw [hn] at hfind
        have : progDecls.find? (·.name == "V") = some vD := rfl
        rw [this] at hfind
        exact (Option.some.inj hfind).symm
      subst hd
      have h1 := hfs 1 (.el0 Unit ()) rfl
      have key2 : ∀ d r c i e f, OField dmP progDecls d r c i e f → d = vD → r = vR → c = 0 → i = 1 →
          e = [.el0 Nat 0] → f = .el0 Unit () → False := by
        intro d r c i e f hof hd hr hc hi he hf
        cases hof with
        | moved => cases hf
        | tree _ _ => cases hf
        | leaf _ hex =>
          subst hd hr hc hi
          obtain ⟨e', hl, hm⟩ := hex
          exact leaf_x0_false hf he hl hm
      exact key2 _ _ _ _ _ _ h1 rfl rfl rfl rfl rfl rfl
  exact fun h => key _ _ h rfl rfl

end OMemCases

end Ochr.Meaning.Dep

