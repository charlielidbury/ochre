import Ochr.Meaning.Strict.Good

/-!
# A call's result is a member (from `ApplyMem.app_mem'`)

A call that succeeds unpacked its callee (so the callee is not `⊥` and not a constructor tree) and
walked its type's telescope to a codomain (`applyTelL_cod`). A good callee that is neither is a
member of its function type (`mem_of_pmem_el`), and then `app_mem'` / `app_mem_ref` (proved in
`ApplyMem.lean`) say the result is a member of the type the call gives it.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

universe u

section
variable (L : Lvl.{u})

/-- An application that succeeds walked the telescope to a codomain. -/
theorem applyTelL_cod : ∀ {Fin C : Type u} (t : Tel L.Code Fin C) (rf : Fin → List Sem) (F : C) (args : List Sem)
    (out : AppResultL L), applyTelL L t rf F args = some out → ∃ b B, telCodL L t args = some (b, B)
  | _, _, .dat _ _ c, _, _, [], _, _ => ⟨false, L.toTy c, rfl⟩
  | _, _, .ref _ _ c, _, _, [], _, _ => ⟨true, L.toTy c, rfl⟩
  | _, _, .param _ _ _ c _ k, rf, f, a :: as, out, h => by
    unfold applyTelL at h
    unfold telCodL
    cases hd : L.dec c a with
    | none => rw [hd] at h; cases h
    | some x =>
      rw [hd] at h
      exact applyTelL_cod (k x) _ (f x) as out h
  | _, _, .dat .., _, _, _ :: _, _, h => by simp [applyTelL] at h
  | _, _, .ref .., _, _, _ :: _, _, h => by simp [applyTelL] at h
  | _, _, .param .., _, _, [], _, h => by simp [applyTelL] at h

/-- A call at level `L` that succeeds unpacked its callee and reached a codomain. -/
theorem callOfL_some {C : Type u} {t : Tel L.Code PUnit C} {fv : Sem} {args : List Res} {s s' : SState} {r : Res}
    (h : callOfL L t fv args s = some (r, s')) :
    (∃ F, L.unpack C fv = some F) ∧ ∃ b B, telCodL L t (args.map (·.1)) = some (b, B) := by
  unfold callOfL at h
  simp only at h
  cases ha : applyFnL L t fv (args.map (·.1)) with
  | none => rw [ha] at h; cases h
  | some out =>
    unfold applyFnL at ha
    cases hu : L.unpack C fv with
    | none => rw [hu] at ha; cases ha
    | some F =>
      rw [hu, Option.bind_some] at ha
      exact ⟨⟨F, rfl⟩, applyTelL_cod L t _ F _ out ha⟩

end

/-- A partly moved member that is neither `⊥` nor a constructor tree is a member. -/
theorem mem_of_pmem_el {R : DataRead} {Γ : List IndDecl} {v : Sem} {T : TyM} (hm : v ≠ .moved)
    (hd : ∀ n r c fs, v ≠ .dat n r c fs) (h : DataModel.pmem R Γ v T) : v ∈ₛ[R] T := by
  rcases h with h | ⟨t, _, hmo, ht | ho⟩
  · exact absurd h hm
  · cases hmo with
    | moved => exact absurd rfl hm
    | refl => exact ht
    | dat => exact absurd rfl (hd _ _ _ _)
    | succ => exact absurd rfl (hd _ _ _ _)
  · cases hmo with
    | moved => exact absurd rfl hm
    | refl =>
      exfalso
      unfold DataModel.OpenIn at ho
      split at ho
      · exact hd _ _ _ _ rfl
      · exact ho
    | dat => exact absurd rfl (hd _ _ _ _)
    | succ => exact absurd rfl (hd _ _ _ _)

theorem el0_of_as {A : Type} {v : Sem} {a : A} (h : Sem.as A v = some a) : v ≠ .moved ∧ ∀ n r c fs, v ≠ .dat n r c fs := by
  cases v <;> simp_all [Sem.as]

theorem el1_of_as {A : Type 1} {v : Sem} {a : A} (h : Sem.as1 A v = some a) : v ≠ .moved ∧ ∀ n r c fs, v ≠ .dat n r c fs := by
  cases v <;> simp_all [Sem.as1]

theorem el2_of_as {A : Type 2} {v : Sem} {a : A} (h : Sem.as2 A v = some a) : v ≠ .moved ∧ ∀ n r c fs, v ≠ .dat n r c fs := by
  cases v <;> simp_all [Sem.as2]

/-- **A call's result is a member of the type the call gives it**: a good callee that the call
unpacks is a member of its function type, and application lands in the codomain (`app_mem'`, at a
returned borrow `app_mem_ref`). -/
theorem callOf_res_mem {R : DataRead} {fv : Res} {args : List Res} {s s' : SState} {r : Res}
    (hf : GoodRes R fv) (h : callOf R fv args s = some (r, s')) : r.1 ∈ₛ[R] r.2.m := by
  rcases fv with ⟨fv, ⟨T, lab⟩⟩
  -- the callee: a member of its type
  have key : ∀ (hel : fv ≠ .moved ∧ ∀ n r c fs, fv ≠ .dat n r c fs) (hT : T ≠ TyM.err), fv ∈ₛ[R] T := by
    intro hel hT
    rcases hf with hf | hf | hf
    · exact hf
    · exact absurd hf hel.1
    · exact absurd hf.1 hT
  -- at a codomain reached: the result, by `app_mem'` or `app_mem_ref`
  have fin : fv ∈ₛ[R] T → (∃ b B, T.codAt? R (args.map (·.1)) = some (b, B)) → r.1 ∈ₛ[R] r.2.m := by
    rintro hmem ⟨b, B, hcod⟩
    cases b with
    | false =>
      obtain ⟨r', s'', h', hr', hT'⟩ := app_mem' R (fv, ⟨T, lab⟩) args s B hmem hcod
      rw [h'] at h; cases h; rw [hT']; exact hr'
    | true =>
      obtain ⟨r', s'', h', hr', hT'⟩ := app_mem_ref R (fv, ⟨T, lab⟩) args s B hmem hcod
      rw [h'] at h; cases h; rw [hT']; exact hr'
  unfold callOf at h
  cases T with
  | t0 A c =>
    cases c with
    | pi C t =>
      dsimp only at h
      obtain ⟨⟨F, hu⟩, hc⟩ := callOfL_some (lvl0 R) h
      exact fin (key (el0_of_as hu) (fun h => by injection h with h1 h2; subst h1; cases h2)) hc
    | _ => simp at h
  | t1 A c =>
    cases c with
    | pi C t =>
      dsimp only at h
      obtain ⟨⟨F, hu⟩, hc⟩ := callOfL_some (lvl1 R) h
      exact fin (key (el1_of_as hu) (by simp [TyM.err])) hc
    | _ => simp at h
  | t2 A c =>
    cases c with
    | pi C t =>
      dsimp only at h
      obtain ⟨⟨F, hu⟩, hc⟩ := callOfL_some (lvl2 R) h
      exact fin (key (el2_of_as hu) (by simp [TyM.err])) hc
    | _ => simp at h

/-- The repaired call returns what `callOf` returns (only the lenders' reading at an undecodable final
content differs). -/
theorem callOfLS_res.{v} (L : Lvl.{v}) {C : Type v} {t : Tel L.Code PUnit C} {fv : Sem} {args : List Res} {s s' : SState}
    {r : Res} (h : callOfL L t fv args s = some (r, s')) : ∃ s'', callOfL L t fv args s = some (r, s'') := by
  unfold callOfL at h
  unfold callOfL
  simp only at h ⊢
  cases ha : applyFnL L t fv (args.map (·.1)) with
  | none => rw [ha] at h; cases h
  | some out =>
    rw [ha] at h
    cases out with
    | data r0 T fins =>
      simp only [Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj h
      exact ⟨_, rfl⟩
    | ref U c fwd back =>
      simp only [Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj h
      exact ⟨_, rfl⟩

theorem callOfS_res {R : DataRead} {fv : Res} {args : List Res} {s s' : SState} {r : Res}
    (h : callOf R fv args s = some (r, s')) : ∃ s'', callOf R fv args s = some (r, s'') := by
  rcases fv with ⟨fv, ⟨T, lab⟩⟩
  unfold callOf at h
  unfold callOf
  cases T with
  | t0 A c => cases c with
    | pi C t => exact callOfLS_res _ h
    | _ => cases h
  | t1 A c => cases c with
    | pi C t => exact callOfLS_res _ h
    | _ => cases h
  | t2 A c => cases c with
    | pi C t => exact callOfLS_res _ h
    | _ => cases h

end Ochr.Meaning.Strict
