import Ochr.Meaning.DataModel.Exists.Knot.CongrN
import Ochr.Meaning.DataModel.Exists.Knot.Checks

/-!
# D118's check gives the name tests (exists13)

`Knot.Term.nok N t` (every name `t` mentions passes `N`'s tests, the congruence `runT_congrN` needs) from
what the checker's `undeclaredCheck` established of `t` (D118: `Term.undeclared okC okT t = none`, every
constant `okC` and every inductive type or constructor's type `okT`), for a term holding no embedded value
(resolution builds none). The two tests differ in three places, each handled here:
* an embedded value: `undeclared` does not look inside one, `nok` does; resolved terms hold none;
* a match's type: `undeclared` tests it, `nok` does not;
* a constructor's type: `undeclared` tests it with `okT`, which for a declaration's field types also admits
  the declaration itself (`self`), while `Assembly.fieldNames` admits only earlier declarations' constructors.
  The premise `nok (ctorsOnly R) t` says every constructor's type passes `R`; for field types it holds with
  `R := (· != n)` by `firstOrderTerm` (`foB_ctorFree`: a field type names no constructor of the type being
  declared, the checker's K4).
-/

namespace Ochr.Meaning.DataModel.Exists.Names

open Ochr Ochr.Meaning Ochr.Meaning.DataModel.Exists.Knot

/-- The name test that asks only of constructors' types. -/
def ctorsOnly (R : String → Bool) : NameOk := ⟨fun _ => true, R, fun _ => true⟩

theorem up_none {p : Term} {r : Option UndeclaredName} (h : UndeclaredName.up p r = none) : r = none := by
  unfold UndeclaredName.up at h; cases r <;> simp_all

theorem orElse_none {a b : Option UndeclaredName} (h : (a.orElse fun _ => b) = none) : a = none ∧ b = none := by
  cases a <;> simp_all [Option.orElse]

set_option linter.unusedSectionVars false

section
variable (okC okT : String → Bool) (N : NameOk) (R : String → Bool)
  (hC : ∀ m, okC m = true → N.gl m = true) (hT : ∀ m, okT m = true → N.ty m = true)
  (hR : ∀ m, okT m = true → R m = true → N.rc m = true)
include hC hT hR

mutual
theorem nok_of_undeclared : ∀ t : Term, t.undeclared okC okT = none → t.anyAtom (fun _ => true) = false →
    Term.nok (ctorsOnly R) t = true → Term.nok N t = true
  | t, hu, hv, hr => by
    cases t with
    | const m =>
      unfold Term.undeclared at hu; split at hu
      · rename_i h; simp only [Term.nok]; exact hC m h
      · cases hu
    | tind m as =>
      unfold Term.undeclared at hu; split at hu
      · rename_i h
        simp only [Term.nok, Term.anyAtom, Bool.and_eq_true] at hv hr ⊢
        exact ⟨hT m h, nok_of_undeclaredList as (up_none hu) hv hr.2⟩
      · cases hu
    | ctor ty c h ps as =>
      unfold Term.undeclared at hu; split at hu
      · rename_i hty
        obtain ⟨h1, h2⟩ := orElse_none (up_none hu)
        simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
        exact ⟨⟨hR ty hty hr.1.1, nok_of_undeclaredList ps h1 hv.1 hr.1.2⟩, nok_of_undeclaredList as h2 hv.2 hr.2⟩
      · cases hu
    | matchInd p ty arms =>
      unfold Term.undeclared at hu; split at hu
      · simp only [Term.nok, Term.anyAtom] at hv hr ⊢
        exact nok_of_undeclaredArms arms (up_none hu) hv hr
      · cases hu
    | val v => rw [Term.anyAtom] at hv; unfold Value.anyAtom at hv; simp at hv
    | assign p u =>
      unfold Term.undeclared at hu
      simp only [Term.nok, Term.anyAtom] at hv hr ⊢
      exact nok_of_undeclared u (up_none hu) hv hr
    | succ u =>
      unfold Term.undeclared at hu
      simp only [Term.nok, Term.anyAtom] at hv hr ⊢
      exact nok_of_undeclared u (up_none hu) hv hr
    | ref u =>
      unfold Term.undeclared at hu
      simp only [Term.nok, Term.anyAtom] at hv hr ⊢
      exact nok_of_undeclared u (up_none hu) hv hr
    | letIn h u w =>
      unfold Term.undeclared at hu
      obtain ⟨h1, h2⟩ := orElse_none (up_none hu)
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨nok_of_undeclared u h1 hv.1 hr.1, nok_of_undeclared w h2 hv.2 hr.2⟩
    | seq u w =>
      unfold Term.undeclared at hu
      obtain ⟨h1, h2⟩ := orElse_none (up_none hu)
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨nok_of_undeclared u h1 hv.1 hr.1, nok_of_undeclared w h2 hv.2 hr.2⟩
    | cong u w =>
      unfold Term.undeclared at hu
      obtain ⟨h1, h2⟩ := orElse_none (up_none hu)
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨nok_of_undeclared u h1 hv.1 hr.1, nok_of_undeclared w h2 hv.2 hr.2⟩
    | ascribe u w =>
      unfold Term.undeclared at hu
      obtain ⟨h1, h2⟩ := orElse_none (up_none hu)
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨nok_of_undeclared u h1 hv.1 hr.1, nok_of_undeclared w h2 hv.2 hr.2⟩
    | matchNat p u w =>
      unfold Term.undeclared at hu
      obtain ⟨h1, h2⟩ := orElse_none (up_none hu)
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨nok_of_undeclared u h1 hv.1 hr.1, nok_of_undeclared w h2 hv.2 hr.2⟩
    | pi hs ds c =>
      unfold Term.undeclared at hu
      obtain ⟨h1, h2⟩ := orElse_none (up_none hu)
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨nok_of_undeclaredList ds h1 hv.1 hr.1, nok_of_undeclared c h2 hv.2 hr.2⟩
    | «fix» f hs ds c dec b =>
      unfold Term.undeclared at hu
      obtain ⟨h12, h3⟩ := orElse_none (up_none hu)
      obtain ⟨h1, h2⟩ := orElse_none h12
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨⟨nok_of_undeclaredList ds h1 hv.1.1 hr.1.1, nok_of_undeclared c h2 hv.1.2 hr.1.2⟩,
        nok_of_undeclared b h3 hv.2 hr.2⟩
    | call f as hd =>
      unfold Term.undeclared at hu
      obtain ⟨h1, h2⟩ := orElse_none (up_none hu)
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨nok_of_undeclared f h1 hv.1 hr.1, nok_of_undeclaredList as h2 hv.2 hr.2⟩
    | eq a b c =>
      unfold Term.undeclared at hu
      obtain ⟨h12, h3⟩ := orElse_none (up_none hu)
      obtain ⟨h1, h2⟩ := orElse_none h12
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨⟨nok_of_undeclared a h1 hv.1.1 hr.1.1, nok_of_undeclared b h2 hv.1.2 hr.1.2⟩,
        nok_of_undeclared c h3 hv.2 hr.2⟩
    | id a b c =>
      unfold Term.undeclared at hu
      obtain ⟨h12, h3⟩ := orElse_none (up_none hu)
      obtain ⟨h1, h2⟩ := orElse_none h12
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
      exact ⟨⟨nok_of_undeclared a h1 hv.1.1 hr.1.1, nok_of_undeclared b h2 hv.1.2 hr.1.2⟩,
        nok_of_undeclared c h3 hv.2 hr.2⟩
    | prim nm as =>
      unfold Term.undeclared at hu
      simp only [Term.nok, Term.anyAtom] at hv hr ⊢
      exact nok_of_undeclaredList as (up_none hu) hv hr
    | place p => simp [Term.nok]
    | borrow p => simp [Term.nok]
    | sort l => simp [Term.nok]
    | nat => simp [Term.nok]
    | zero => simp [Term.nok]
    | unit => simp [Term.nok]
    | tt => simp [Term.nok]

theorem nok_of_undeclaredList : ∀ ts : List Term, Term.undeclaredList okC okT ts = none →
    Term.anyAtomList (fun _ => true) ts = false → Term.nokList (ctorsOnly R) ts = true → Term.nokList N ts = true
  | [], _, _, _ => by simp [Term.nokList]
  | t :: ts, hu, hv, hr => by
    unfold Term.undeclaredList at hu
    obtain ⟨h1, h2⟩ := orElse_none hu
    simp only [Term.nokList, Term.anyAtomList, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
    exact ⟨nok_of_undeclared t h1 hv.1 hr.1, nok_of_undeclaredList ts h2 hv.2 hr.2⟩

theorem nok_of_undeclaredArms : ∀ ts : List (Hint × Term), Term.undeclaredArms okC okT ts = none →
    Term.anyAtomArms (fun _ => true) ts = false → Term.nokArms (ctorsOnly R) ts = true → Term.nokArms N ts = true
  | [], _, _, _ => by simp [Term.nokArms]
  | (h, t) :: ts, hu, hv, hr => by
    unfold Term.undeclaredArms at hu
    obtain ⟨h1, h2⟩ := orElse_none hu
    simp only [Term.nokArms, Term.anyAtomArms, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hr ⊢
    exact ⟨nok_of_undeclared t h1 hv.1 hr.1, nok_of_undeclaredArms ts h2 hv.2 hr.2⟩
end

end

/-! ## The premise on constructors: anything (`R := true`), or no constructor of the declared type -/

theorem val_false {v : Value} (hv : Term.anyAtom (fun _ => true) (.val v) = false) : False := by
  rw [Term.anyAtom] at hv; unfold Value.anyAtom at hv; simp at hv

mutual
/-- With no restriction on constructors, a term with no embedded value passes. -/
theorem nok_ctorsOnly_true : ∀ t : Term, t.anyAtom (fun _ => true) = false → Term.nok (ctorsOnly fun _ => true) t = true
  | t, hv => by
    cases t with
    | val v => exact (val_false hv).elim
    | tind m as =>
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true] at hv ⊢
      exact ⟨rfl, nok_ctorsOnly_trueList as hv⟩
    | ctor ty c h ps as =>
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
      exact ⟨⟨rfl, nok_ctorsOnly_trueList ps hv.1⟩, nok_ctorsOnly_trueList as hv.2⟩
    | matchInd p ty arms =>
      simp only [Term.nok, Term.anyAtom] at hv ⊢
      exact nok_ctorsOnly_trueArms arms hv
    | assign p u | succ u | ref u =>
      simp only [Term.nok, Term.anyAtom] at hv ⊢
      exact nok_ctorsOnly_true u hv
    | letIn _ u w | seq u w | cong u w | ascribe u w | matchNat _ u w =>
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
      exact ⟨nok_ctorsOnly_true u hv.1, nok_ctorsOnly_true w hv.2⟩
    | pi hs ds c =>
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
      exact ⟨nok_ctorsOnly_trueList ds hv.1, nok_ctorsOnly_true c hv.2⟩
    | «fix» f hs ds c dec b =>
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
      exact ⟨⟨nok_ctorsOnly_trueList ds hv.1.1, nok_ctorsOnly_true c hv.1.2⟩, nok_ctorsOnly_true b hv.2⟩
    | call f as hd =>
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
      exact ⟨nok_ctorsOnly_true f hv.1, nok_ctorsOnly_trueList as hv.2⟩
    | eq a b c | id a b c =>
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
      exact ⟨⟨nok_ctorsOnly_true a hv.1.1, nok_ctorsOnly_true b hv.1.2⟩, nok_ctorsOnly_true c hv.2⟩
    | prim nm as =>
      simp only [Term.nok, Term.anyAtom] at hv ⊢
      exact nok_ctorsOnly_trueList as hv
    | const m => rfl
    | place p | borrow p | sort l | nat | zero | unit | tt => simp [Term.nok]

theorem nok_ctorsOnly_trueList : ∀ ts : List Term, Term.anyAtomList (fun _ => true) ts = false →
    Term.nokList (ctorsOnly fun _ => true) ts = true
  | [], _ => by simp [Term.nokList]
  | t :: ts, hv => by
    simp only [Term.nokList, Term.anyAtomList, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
    exact ⟨nok_ctorsOnly_true t hv.1, nok_ctorsOnly_trueList ts hv.2⟩

theorem nok_ctorsOnly_trueArms : ∀ ts : List (Hint × Term), Term.anyAtomArms (fun _ => true) ts = false →
    Term.nokArms (ctorsOnly fun _ => true) ts = true
  | [], _ => by simp [Term.nokArms]
  | (h, t) :: ts, hv => by
    simp only [Term.nokArms, Term.anyAtomArms, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
    exact ⟨nok_ctorsOnly_true t hv.1, nok_ctorsOnly_trueArms ts hv.2⟩
end

mutual
/-- A term that does not mention `n` names no constructor of `n`. -/
theorem nok_ctorFree_of_mentions (n : String) : ∀ t : Term, t.mentionsType n = false → t.anyAtom (fun _ => true) = false →
    Term.nok (ctorsOnly (· != n)) t = true
  | t, hm, hv => by
    cases t with
    | val v => exact (val_false hv).elim
    | tind m as =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
      exact ⟨rfl, nok_ctorFree_of_mentionsList n as hm.2 hv⟩
    | ctor ty c h ps as =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
      refine ⟨⟨?_, nok_ctorFree_of_mentionsList n ps hm.1.2 hv.1⟩, nok_ctorFree_of_mentionsList n as hm.2 hv.2⟩
      show (ty != n) = true
      simpa using hm.1.1
    | matchInd p ty arms =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType, Bool.or_eq_false_iff] at hv hm ⊢
      exact nok_ctorFree_of_mentionsArms n arms hm.2 hv
    | assign p u | succ u | ref u =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType] at hv hm ⊢
      exact nok_ctorFree_of_mentions n u hm hv
    | letIn _ u w | seq u w | cong u w | ascribe u w | matchNat _ u w =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
      exact ⟨nok_ctorFree_of_mentions n u hm.1 hv.1, nok_ctorFree_of_mentions n w hm.2 hv.2⟩
    | pi hs ds c =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
      exact ⟨nok_ctorFree_of_mentionsList n ds hm.1 hv.1, nok_ctorFree_of_mentions n c hm.2 hv.2⟩
    | «fix» f hs ds c dec b =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
      exact ⟨⟨nok_ctorFree_of_mentionsList n ds hm.1.1 hv.1.1, nok_ctorFree_of_mentions n c hm.1.2 hv.1.2⟩,
        nok_ctorFree_of_mentions n b hm.2 hv.2⟩
    | call f as hd =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
      exact ⟨nok_ctorFree_of_mentions n f hm.1 hv.1, nok_ctorFree_of_mentionsList n as hm.2 hv.2⟩
    | eq a b c | id a b c =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
      exact ⟨⟨nok_ctorFree_of_mentions n a hm.1.1 hv.1.1, nok_ctorFree_of_mentions n b hm.1.2 hv.1.2⟩,
        nok_ctorFree_of_mentions n c hm.2 hv.2⟩
    | prim nm as =>
      simp only [Term.nok, Term.anyAtom, Term.mentionsType] at hv hm ⊢
      exact nok_ctorFree_of_mentionsList n as hm hv
    | const m => rfl
    | place p | borrow p | sort l | nat | zero | unit | tt => simp [Term.nok]

theorem nok_ctorFree_of_mentionsList (n : String) : ∀ ts : List Term, Term.mentionsTypeList n ts = false →
    Term.anyAtomList (fun _ => true) ts = false → Term.nokList (ctorsOnly (· != n)) ts = true
  | [], _, _ => by simp [Term.nokList]
  | t :: ts, hm, hv => by
    simp only [Term.nokList, Term.anyAtomList, Term.mentionsTypeList, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
    exact ⟨nok_ctorFree_of_mentions n t hm.1 hv.1, nok_ctorFree_of_mentionsList n ts hm.2 hv.2⟩

theorem nok_ctorFree_of_mentionsArms (n : String) : ∀ ts : List (Hint × Term), Term.mentionsTypeArms n ts = false →
    Term.anyAtomArms (fun _ => true) ts = false → Term.nokArms (ctorsOnly (· != n)) ts = true
  | [], _, _ => by simp [Term.nokArms]
  | (h, t) :: ts, hm, hv => by
    simp only [Term.nokArms, Term.anyAtomArms, Term.mentionsTypeArms, Bool.and_eq_true, Bool.or_eq_false_iff] at hv hm ⊢
    exact ⟨nok_ctorFree_of_mentions n t hm.1 hv.1, nok_ctorFree_of_mentionsArms n ts hm.2 hv.2⟩
end

mutual
/-- **A field type passing `firstOrderTerm` names no constructor of the type being declared** (K4: no
constructor at the top, a type argument first-order again, a value argument, a call's arguments and an
equation's parts not mentioning `n`). -/
theorem foB_ctorFree (Γd : List IndDecl) (nest : NestTable) (n : String) (np : Nat) :
    ∀ t : Term, foB Γd nest n np t = true → t.anyAtom (fun _ => true) = false → Term.nok (ctorsOnly (· != n)) t = true
  | t, hf, hv => by
    cases t with
    | tind m as =>
      simp only [foB] at hf
      split at hf
      · rename_i dm _
        simp only [Term.nok, Term.anyAtom, Bool.and_eq_true] at hv ⊢
        exact ⟨rfl, foArgsB_ctorFree Γd nest n np m dm 0 as hf hv⟩
      · cases hf
    | call f as hd =>
      cases f with
      | const g =>
        simp only [foB, Bool.not_eq_true'] at hf
        simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
        exact ⟨rfl, nok_ctorFree_of_mentionsList n as hf hv.2⟩
      | _ => simp [foB] at hf
    | eq A a b =>
      simp only [foB, Bool.and_eq_true, Bool.not_eq_true'] at hf
      simp only [Term.nok, Term.anyAtom, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
      exact ⟨⟨nok_ctorFree_of_mentions n A hf.1.1 hv.1.1, nok_ctorFree_of_mentions n a hf.1.2 hv.1.2⟩,
        nok_ctorFree_of_mentions n b hf.2 hv.2⟩
    | nat | unit => simp [Term.nok]
    | place p => simp [Term.nok]
    | _ => simp [foB] at hf

theorem foArgsB_ctorFree (Γd : List IndDecl) (nest : NestTable) (n : String) (np : Nat) (m : String) (dm : IndDecl) :
    ∀ (i : Nat) (as : List Term), foArgsB Γd nest n np m dm i as = true → Term.anyAtomList (fun _ => true) as = false →
      Term.nokList (ctorsOnly (· != n)) as = true
  | _, [], _, _ => by simp [Term.nokList]
  | i, a :: as, hf, hv => by
    simp only [foArgsB, Bool.and_eq_true] at hf
    simp only [Term.nokList, Term.anyAtomList, Bool.and_eq_true, Bool.or_eq_false_iff] at hv ⊢
    refine ⟨?_, foArgsB_ctorFree Γd nest n np m dm (i + 1) as hf.2 hv.2⟩
    have h1 := hf.1
    split at h1
    · simp only [Bool.and_eq_true] at h1
      exact foB_ctorFree Γd nest n np a h1.1 hv.1
    · simp only [Bool.not_eq_true'] at h1
      exact nok_ctorFree_of_mentions n a h1 hv.1
end

end Ochr.Meaning.DataModel.Exists.Names
