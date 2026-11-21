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

/-- A typed field step reads a proof's `⋆` or a constructor value's field (route (c): the read is
typed by the type it starts at; only its value is used here). -/
theorem stepField_inv {T U : TyS} {c i : Nat} {s x : Sem} (h : Sem.stepField dm Γ T c i s = some (x, U)) :
    (s = .proof ∧ x = .proof) ∨ ∃ n r fs, s = .dat n r c fs ∧ fs[i]? = some x := by
  unfold Sem.stepField at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact .inl ⟨rfl, h.1.symm⟩
  · rename_i n r c' fs
    split at h
    · split at h
      · rename_i hc
        split at h
        · rename_i f hf
          obtain ⟨U', -, he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, -⟩ := he
          exact .inr ⟨n, r, fs, by rw [hc.2], hf⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- The write at a field of a constructor value, through the field (not a `Nat`-named `1`-tree's
predecessor): the field's write, rebuilt. -/
theorem updAt_dat_field (f : Sem → Sem) (T : TyS) (st : Step) (rest : List Step) (n : String) (r : Rec)
    (c i : Nat) (fs : List Sem) (fi : Sem) (hst : st = .proj i ∨ ∃ g, st = .field g ∧ g.idx = i)
    (hnat : ¬ (n = "Nat" ∧ c = 1 ∧ ∃ w, fs = [w])) (hf : fs[i]? = some fi) (hn : Sem.updAt dm Γ T f rest fi = none) :
    Sem.updAt dm Γ T f (st :: rest) (.dat n r c fs) = none := by
  rw [Sem.updAt.eq_def]
  have hasN : (Sem.dat n r c fs).asNat = none := rfl
  rcases hst with rfl | ⟨g, rfl, rfl⟩
  · simp only [hasN]
    split
    · rename_i heq; simp only [Sem.dat.injEq] at heq
      obtain ⟨rfl, -, rfl, rfl⟩ := heq; exact absurd ⟨rfl, rfl, _, rfl⟩ hnat
    · rename_i heq; simp only [Sem.dat.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      simp [hf, hn]
    · rfl
  · simp only [hasN]
    split
    · rename_i heq; simp only [Sem.dat.injEq] at heq
      obtain ⟨rfl, -, rfl, rfl⟩ := heq; exact absurd ⟨rfl, rfl, _, rfl⟩ hnat
    · rename_i heq; simp only [Sem.dat.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      simp [hf, hn]
    · rfl

/-- A field step of a `Nat`-named `1`-tree by name: the write fails. -/
theorem updAt_natTree_field (f : Sem → Sem) (T : TyS) (g : FieldRef) (rest : List Step) (r : Rec) (w : Sem) :
    Sem.updAt dm Γ T f (.field g :: rest) (.dat "Nat" r 1 [w]) = none := by
  rw [Sem.updAt.eq_def]; rfl

/-- **One step**: where the read steps, the write fails as it fails from what the read reaches. -/
theorem updAt_step_none (f : Sem → Sem) {T T' : TyS} {st : Step} {V V' : Sem}
    (hstep : Sem.step dm Γ T st V = some (V', T')) (rest : List Step)
    (hn : Sem.updAt dm Γ T' f rest V' = none) : Sem.updAt dm Γ T f (st :: rest) V = none := by
  have hT : ∀ T'', Sem.updAt dm Γ T'' f rest V' = none := fun T'' => by rw [updAt_T dm Γ f rest T'' T']; exact hn
  -- a field step read by `stepField`
  have hfield : ∀ (c i : Nat), (st = .proj i ∨ ∃ g, st = .field g ∧ g.idx = i ∧ g.ctor = c) →
      (∀ r w, st = .proj 0 → V ≠ .dat "Nat" r 1 [w]) →
      Sem.stepField dm Γ T c i V = some (V', T') → Sem.updAt dm Γ T f (st :: rest) V = none := by
    intro c i hst hnn hs
    rcases stepField_inv dm Γ hs with ⟨rfl, rfl⟩ | ⟨n, r, fs, rfl, hf0⟩
    · rw [Sem.updAt.eq_def]
      rcases hst with rfl | ⟨g, rfl, -⟩
      · simp only [show Sem.proof.asNat = none from rfl]
      · rfl
    · by_cases hnat : n = "Nat" ∧ c = 1 ∧ ∃ w, fs = [w]
      · obtain ⟨rfl, rfl, w, rfl⟩ := hnat
        rcases hst with rfl | ⟨g, rfl, -, -⟩
        · cases i with
          | zero => exact absurd rfl (hnn r w rfl)
          | succ i =>
            rw [Sem.updAt.eq_def]
            simp only [show (Sem.dat "Nat" r 1 [w]).asNat = none from rfl]
        · exact updAt_natTree_field dm Γ f T g rest r w
      · rcases hst with rfl | ⟨g, rfl, hgi, -⟩
        · exact updAt_dat_field dm Γ f T _ rest n r c i fs V' (.inl rfl) hnat hf0 (hT T)
        · exact updAt_dat_field dm Γ f T _ rest n r c i fs V' (.inr ⟨g, rfl, hgi⟩) hnat hf0 (hT T)
  cases st with
  | deref =>
    simp only [Sem.step, Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    rw [Sem.updAt.eq_def]; exact hn
  | proj i =>
    cases i with
    | zero =>
      simp only [Sem.step] at hstep
      cases hV : V.asNat with
      | some k =>
        rw [hV] at hstep
        cases k with
        | zero => cases hstep
        | succ k =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          rw [Sem.updAt.eq_def]; simp only [hV]; simp [hT (.plain TyM.nat)]
      | none =>
        rw [hV] at hstep
        simp only at hstep
        split at hstep
        · simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          rw [Sem.updAt.eq_def]
          simp [hV, hT (.plain TyM.nat)]
        · rename_i hne
          exact hfield 0 0 (.inl rfl) (fun r w _ e => hne r w (by
            rcases stepField_inv dm Γ hstep with ⟨rfl, -⟩ | ⟨n, r', fs, rfl, -⟩
            · cases e
            · simp only [Sem.dat.injEq] at e; omega) e) hstep
    | succ i => exact hfield 0 (i + 1) (.inl rfl) (fun _ _ h => by cases h) hstep
  | field g =>
    simp only [Sem.step] at hstep
    split at hstep
    · split at hstep
      · exact hfield g.ctor g.idx (.inr ⟨g, rfl, rfl, rfl⟩) (fun _ _ h => by cases h) hstep
      · cases hstep
    · exact hfield g.ctor g.idx (.inr ⟨g, rfl, rfl, rfl⟩) (fun _ _ h => by cases h) hstep

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
    rw [List.cons_append]
    exact updAt_step_none dm Γ f hstep (p ++ r) (updAt_append_none f p T' V' w T₁ r hrest hr)

end

end Ochr.Meaning.Steps.Slice
