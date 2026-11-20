import Ochr.Meaning.Places

/-!
# Where the reference's drop can write (the slice)

`dropAt` does nothing exactly where its write cannot be made (`Sem.updAt` fails): the path passes by
a field step through a part with no fields. Facts about `Sem.updAt` for that test: it does not read
its type; through a moved part it fails at the first step that is not a `*`; and along a path the
read reaches it fails as the rest fails from what the read reaches.
-/

namespace Ochr.Meaning.Steps.Slice

open Ochr Ochr.Meaning

section
variable (dm : DataModel) (Γ : List IndDecl)

/-- `Sem.updAt` does not read its type. -/
theorem updAt_T (f : Sem → Sem) : ∀ (p : List Step) (T T' : TyS) (v : Sem),
    Sem.updAt dm Γ T f p v = Sem.updAt dm Γ T' f p v
  | [], T, T', v => by rw [Sem.updAt.eq_def, Sem.updAt.eq_def]
  | x :: p, T, T', v => by
    rw [Sem.updAt.eq_def, Sem.updAt.eq_def]
    cases x with
    | deref => exact updAt_T f p T T' v
    | proj i => simp only [updAt_T f p T T']
    | field g => simp only [updAt_T f p T T']

theorem asNat_moved : Sem.moved.asNat = none := rfl
theorem asNat_proof : Sem.proof.asNat = none := rfl

/-- **Through a moved part the write fails at the first step that is not a `*`.** -/
theorem updAt_moved_none (f : Sem → Sem) : ∀ (r : List Step) (T : TyS), (∃ x ∈ r, x ≠ .deref) →
    Sem.updAt dm Γ T f r .moved = none
  | [], _, ⟨x, hx, _⟩ => absurd hx List.not_mem_nil
  | .deref :: r, T, ⟨x, hx, hne⟩ => by
    rw [Sem.updAt.eq_def]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact absurd rfl hne
    exact updAt_moved_none f r T ⟨x, hx, hne⟩
  | .proj i :: r, T, _ => by
    rw [Sem.updAt.eq_def]; simp only [asNat_moved]
  | .field g :: r, T, _ => by
    rw [Sem.updAt.eq_def]

/-- **Along a path the read reaches, the write fails as it fails from what the read reaches.** -/
theorem updAt_append_none (f : Sem → Sem) : ∀ (p : List Step) (T : TyS) (V w : Sem) (T₁ : TyS) (r : List Step),
    Sem.follow dm Γ T V p = some (w, T₁) → Sem.updAt dm Γ T₁ f r w = none →
    Sem.updAt dm Γ T f (p ++ r) V = none
  | [], T, V, w, T₁, r, h, hr => by
    simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hr
  | x :: p, T, V, w, T₁, r, h, hr => by
    simp only [Sem.follow] at h
    obtain ⟨⟨V', T'⟩, hstep, hrest⟩ := Option.bind_eq_some_iff.mp h
    have ih := updAt_append_none f p T' V' w T₁ r hrest hr
    rw [List.cons_append, Sem.updAt.eq_def]
    cases x with
    | deref =>
      simp only [Sem.step, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ih
    | proj i =>
      rw [updAt_T dm Γ f (p ++ r) T' T] at ih
      cases i with
      | zero =>
        simp only [Sem.step] at hstep
        cases hV : V.asNat with
        | some n =>
          rw [hV] at hstep
          cases n with
          | zero => cases hstep
          | succ n =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            simp only [hV]
            rw [updAt_T dm Γ f (p ++ r) T (.plain TyM.nat)] at ih
            simp [ih]
        | none =>
          rw [hV] at hstep
          simp only [hV]
          rcases V with a | a | a | a | _ | _ | ⟨n, rr, c, fs⟩ | _
          all_goals first
            | (simp [Sem.stepField] at hstep; done)
            | rfl
            | skip
          by_cases hn : n = "Nat" ∧ c = 1 ∧ fs.length = 1
          · obtain ⟨rfl, rfl, hl⟩ := hn
            match fs, hl with
            | [w'], _ =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              rw [updAt_T dm Γ f (p ++ r) T (.plain TyM.nat)] at ih
              simp [ih]
          · simp only at hstep
            split at hstep
            · rename_i heq; simp only [Sem.dat.injEq] at heq
              obtain ⟨rfl, -, rfl, rfl⟩ := heq; exact absurd ⟨rfl, rfl, rfl⟩ hn
            · simp only [Sem.stepField] at hstep
              split at hstep
              · rename_i hc0; subst hc0
                obtain ⟨f0, hf0, he⟩ := Option.map_eq_some_iff.mp hstep
                simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he
                split
                · rename_i heq; simp only [Sem.dat.injEq] at heq; omega
                · rename_i heq; simp only [Sem.dat.injEq] at heq
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
                  rw [hf0]; simp [ih]
                · rfl
              · cases hstep
      | succ i =>
        rcases V with a | a | a | a | _ | _ | ⟨n, rr, c, fs⟩ | _
        all_goals simp only [Sem.step, Sem.stepField] at hstep
        all_goals first
          | (cases hstep; done)
          | (simp [asNat_proof]; done)
          | skip
        split at hstep
        · rename_i hc0; subst hc0
          obtain ⟨f0, hf0, he⟩ := Option.map_eq_some_iff.mp hstep
          simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he
          simp [hf0, ih]
        · cases hstep
    | field g =>
      rw [updAt_T dm Γ f (p ++ r) T' T] at ih
      rcases V with a | a | a | a | _ | _ | ⟨n, rr, c, fs⟩ | _
      all_goals simp only [Sem.step, Sem.stepField] at hstep
      all_goals first
        | (cases hstep; done)
        | (simp [asNat_proof]; done)
        | skip
      -- a named field step reads a constructor value of `g`'s declaration only
      split at hstep
      · split at hstep
        · rename_i _ hc0; subst hc0
          obtain ⟨f0, hf0, he⟩ := Option.map_eq_some_iff.mp hstep
          simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he
          have hasN : (Sem.dat n rr g.ctor fs).asNat = none := rfl
          simp only [hasN]
          split
          · rfl
          · rename_i heq; simp only [Sem.dat.injEq] at heq
            obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
            simp [hf0, ih]
          · rfl
        · cases hstep
      · cases hstep

end

end Ochr.Meaning.Steps.Slice
