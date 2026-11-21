import Ochr.Meaning.Strict.Comb

/-!
# The fundamental lemma: the clauses that make a type, a number, or a proof of `True`

Universes: `sort l : sort (sortSucc l)` is a member where the bounded model has the universe (`l ≤ 1`)
and a type value at `err` above. A Π-type and a declaration's type are members of the universe the run
gives them (`l ≤ 2`, resp. a declaration not at `Type₁`), or type values at `err`.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {R : DataRead}

theorem ty_univ1_mem {A : Type} (c : Code0 A) (hc : c.level = some 1) : Sem.ty (.t0 A c) ∈ₛ[R] TyM.univ 1 :=
  ⟨⟨A, c, hc⟩, rfl⟩

theorem ty_univ0_mem (P : Prop) : Sem.ty (TyM.prop P) ∈ₛ[R] TyM.univ 0 := ⟨ULift.up P, rfl⟩

theorem ty_univ2_mem {A : Type 1} (c : Code1 A) (hc : c.level = some 2) : Sem.ty (.t1 A c) ∈ₛ[R] TyM.univ 2 :=
  ⟨⟨A, c, hc⟩, rfl⟩

theorem goodRes_ty_err (X : TyM) : GoodRes R (.ty X, .plain TyM.err) := .inr (.inr ⟨rfl, .inl ⟨X, rfl⟩⟩)

/-- `sort l : sort (sortSucc l)`. -/
theorem goodRes_sort (l : Nat) : GoodRes R (.ty (TyM.univ l), .plain (TyM.univ (sortSucc l))) := by
  match l with
  | 0 => exact .inl (ty_univ2_mem Code1.univ0 rfl)
  | 1 => exact .inl (ty_univ2_mem Code1.univ1 rfl)
  | 2 => exact goodRes_ty_err _
  | n + 3 =>
    show GoodRes R (.ty TyM.err, .plain (TyM.univ (sortSucc (n + 3))))
    have : TyM.univ (sortSucc (n + 3)) = TyM.err := by simp [sortSucc, TyM.univ]
    rw [this]; exact goodRes_ty_err _

/-- A Π-type at its declared sort. -/
theorem goodRes_pi (l : Nat) (ds : List PiDom) (out : PiCod) :
    GoodRes R (.ty (piTyAt R l ds out), .plain (TyM.univ l)) := by
  match l with
  | 0 => exact .inl (ty_univ0_mem _)
  | 1 => exact .inl (ty_univ1_mem _ rfl)
  | 2 => exact .inl (ty_univ2_mem _ rfl)
  | 3 => exact goodRes_ty_err _
  | n + 4 => exact goodRes_ty_err _

/-- A declaration's type at its sort (not `Type₁`). -/
theorem goodRes_tyR (dm : DataModel) (d : IndDecl) (r : Rec) (hs : d.sort ≠ 2) :
    GoodRes dm.read (.ty (dm.tyR d r), .plain (TyM.univ d.sort)) := by
  unfold DataModel.tyR
  by_cases h0 : d.sort = 0
  · simp only [h0, beq_self_eq_true, if_true]; exact .inl (ty_univ0_mem _)
  · have hb : (d.sort == 0) = false := by simpa using h0
    simp only [hb, Bool.false_eq_true, if_false]
    by_cases h1 : d.sort = 1
    · rw [h1]; exact .inl (ty_univ1_mem _ rfl)
    · obtain ⟨n, hn⟩ : ∃ n, d.sort = n + 3 := ⟨d.sort - 3, by omega⟩
      rw [hn]; exact goodRes_ty_err _

end

section
variable {dm : DataModel} {Γ : List IndDecl} {φ : Future}

/-- A pure clause: its result, the state unchanged. -/
theorem fund_pure {r : Res} (hr : GoodRes dm.read r) (hl : r.2.label = none) :
    FundAt dm Γ φ (pure r) := by
  intro s s' r' hs h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
  exact ⟨hr, (fun l h' => by rw [hl] at h'; cases h'), (fun l h' => by rw [hl] at h'; cases h'), hs⟩

/-- A clause on a copy: its result, the state unchanged, the result's label dropped by the clause. -/
theorem fund_onCopy {x : SM Res} (hx : ∀ s s' r, x s = some (r, s') → GoodRes dm.read r ∧ r.2.label = none) :
    FundAt dm Γ φ (SM.onCopy x) := by
  intro s s' r hs h
  obtain ⟨s₁, h1⟩ := SM.onCopy_result h
  have e : s' = s := SM.onCopy_state h
  obtain ⟨hr, hl⟩ := hx s s₁ r h1
  exact ⟨hr, (fun l h' => by rw [hl] at h'; cases h'), (fun l h' => by rw [hl] at h'; cases h'), e ▸ hs⟩

end

end Ochr.Meaning.Strict
