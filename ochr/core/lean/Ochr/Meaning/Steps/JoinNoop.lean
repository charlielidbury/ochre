import Ochr.Meaning.Steps.DropOneAsm

/-!
# The drop where `movedPlace` re-rooted to a prefix holding `⊥` or `⋆` (docs/31 D56)

The checker's drop does nothing there. The reference's drop of the place itself reads through
that prefix: a `⋆` part reads `⋆` along any path, and the drop does nothing; a moved part reads
`moved` along `*` steps only, and the drop then writes `moved` over the moved part, which changes
nothing the relation reads; through anything else it reads nothing, and the drop does nothing. In
every case nothing is lent over, at or under the prefix, so neither the lent prefix's access nor
the place's own access ends anything. The helpers are here; `joinDropOne_noop` is assembled in
`MovedPlace.lean`, beside `joinDropOne_alp`.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

/-- A prefix of a place at the join's grain is at the grain. -/
theorem grain_prefix {D : Decisions} {Γ : List IndDecl} {sc : List DeclInfo} {q q' : Place}
    (h : GrainOk D Γ sc q) (h1 : q'.steps.1 = q.steps.1) (h2 : q'.steps.2 <+: q.steps.2) :
    GrainOk D Γ sc q' := by
  intro p x rest hp he
  obtain ⟨t, ht⟩ := h2
  exact h p x (rest ++ t) (hp.trans h1) (by rw [← ht, he]; simp)

/-- An access of a longer path reaches only what an access of its prefix reaches (both read sites
by key, and two prefixes of one key are comparable). -/
theorem dataHit_of_prefix {a b ψ : List Step} (hab : a <+: b) (h : dataHit b ψ = true) : dataHit a ψ = true := by
  have hk : pathKey a <+: pathKey b := hab.filterMap _
  simp only [dataHit, Bool.or_eq_true, List.isPrefixOf_iff_prefix] at h ⊢
  rcases h with h | h
  · exact List.prefix_or_prefix_of_prefix h hk
  · exact .inr (hk.trans h)

/-- The reference reaches no label at `pos` with `hit` where the checker has no live site there
that `hit` accepts (the relation makes the sites the checker's). -/
theorem unreached_of_clear (K : RunCtx) (ρ : Assignment) (φ : Future) {st : MState} {s : SState}
    {π : Nat → Nat} (hs : Rel K ρ φ π st s) (pos : Pos) (hit : List Step → Bool)
    (hclr : ∀ l, liveLoan st.env l = true → ∀ x ∈ Env.sitesOf st.env l, x.pos = pos → hit x.path = false) :
    ∀ y, s.Live y → s.reached pos hit y = false := by
  intro y hy
  obtain ⟨l, hl, rfl⟩ := rel_live_ref K ρ φ st s π hs hy
  unfold SState.reached
  rw [List.any_eq_false]
  intro x hx hpx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpx
  rw [hclr l hl x ((hs.sites l hl x).mp hx) hpx.1] at hpx
  exact Bool.false_ne_true hpx.2

/-- No strict prefix of the path is lent where nothing is lent comparable with a prefix of it. -/
theorem lentPrefix_none_of_unreached {s : SState} {pos : Pos} {p steps : List Step} (hp : p <+: steps)
    (h : ∀ y, s.Live y → s.reached pos (dataHit p) y = false) : lentPrefix s pos steps = none := by
  unfold lentPrefix
  apply List.find?_eq_none.mpr
  intro ψ hψ hany
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
  obtain ⟨y, hy, hr⟩ := List.any_eq_true.mp hany
  have h0 := h y hy
  rw [← Bool.not_eq_true] at h0
  apply h0
  unfold SState.reached at hr ⊢
  obtain ⟨x, hx, hxr⟩ := List.any_eq_true.mp hr
  refine List.any_eq_true.mpr ⟨x, hx, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxr ⊢
  refine ⟨hxr.1, dataHit_of_prefix hp ?_⟩
  simp only [dataHit, Bool.or_eq_true, List.isPrefixOf_iff_prefix]
  left
  rw [hxr.2]
  exact (List.take_prefix j steps).filterMap _

/-- `⋆` reads `⋆` along any path. -/
theorem sem_follow_proof (dm : DataModel) (Γ : List IndDecl) :
    ∀ (rest : List Step) (T : TyS), ∃ T', Sem.follow dm Γ T .proof rest = some (.proof, T')
  | [], T => ⟨T, rfl⟩
  | x :: rest, T => by
    obtain ⟨T₁, h1⟩ := sem_step_proof dm Γ T x
    obtain ⟨T', h2⟩ := sem_follow_proof dm Γ rest T₁
    exact ⟨T', by simp [Sem.follow, h1, h2]⟩

/-- `moved` reads `moved` along `*` steps, and nothing along any other step. -/
theorem sem_follow_moved (dm : DataModel) (Γ : List IndDecl) :
    ∀ (rest : List Step) (T : TyS), Sem.follow dm Γ T .moved rest = none ∨
      ((∀ x ∈ rest, x = .deref) ∧ ∃ T', Sem.follow dm Γ T .moved rest = some (.moved, T'))
  | [], T => .inr ⟨by simp, T, rfl⟩
  | .deref :: rest, T => by
    rcases sem_follow_moved dm Γ rest T with h | ⟨hd, T', h⟩
    · exact .inl (by simpa [Sem.follow, Sem.step] using h)
    · exact .inr ⟨by simpa using hd, T', by simpa [Sem.follow, Sem.step] using h⟩
  | .proj i :: rest, T => by
    left
    have : Sem.asNat .moved = none := by
      cases h : Sem.asNat .moved with
      | none => rfl
      | some n => exact absurd (Sem.asNat_some h) (by simp)
    rcases i with _ | i <;> simp [Sem.follow, Sem.step, Sem.stepField, this]
  | .field g :: rest, T => .inl (by simp [Sem.follow, Sem.step, Sem.stepField])

/-- Updating along a path and then `*`s is updating along the path (`*` is the identity). -/
theorem sem_updAt_append_derefs (dm : DataModel) (Γ : List IndDecl) (f : Sem → Sem) (ds : List Step)
    (hd : ∀ x ∈ ds, x = .deref) : ∀ (p : List Step) (T : TyS) (v : Sem),
    Sem.updAt dm Γ T f (p ++ ds) v = Sem.updAt dm Γ T f p v
  | [], T, v => by rw [List.nil_append, Sem.updAt_derefs dm Γ T f ds v hd]; rw [Sem.updAt.eq_def]
  | x :: p, T, v => by
    have ih := sem_updAt_append_derefs dm Γ f ds hd p
    rw [List.cons_append]
    conv => lhs; rw [Sem.updAt.eq_def]
    conv => rhs; rw [Sem.updAt.eq_def]
    cases x <;> simp only [ih]

/-- A field step of `⋆` is `⋆`. -/
theorem follow_proof_fields : ∀ (fs : List Step), (∀ x ∈ fs, x ≠ .deref) → Value.proof.follow fs = some .proof
  | [], _ => rfl
  | .deref :: _, h => absurd rfl (h _ List.mem_cons_self)
  | .proj _ :: fs, h => by
    simp only [Value.follow, stepV, Option.bind_some]
    exact follow_proof_fields fs fun x hx => h x (List.mem_cons_of_mem _ hx)
  | .field _ :: fs, h => by
    simp only [Value.follow, stepV, Option.bind_some]
    exact follow_proof_fields fs fun x hx => h x (List.mem_cons_of_mem _ hx)

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The join derefs no proof**: a place at the join's grain goes through `*` only at a place
declared a borrow (`StepOk .deref`), and a place at the grain holding `⋆` is declared a copy
((C⋆)), which no borrow is (`declCopy`). PROVED. (The grain asked nothing of a `*` step from main's
D94 until the slice, 2026-11-20, and the leaf was then false, `Regress/GrainDerefProof.lean`: an arm
the run does not take is never checked, so `*h` of a proof `h` reached the join. Restated with the
checker's D101: `jdGrain` rejects a `*` through a place not declared a borrow.) -/
theorem grain_deref_not_proof (st : MState) (s : SState) (π : Nat → Nat) (q p : Place)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (hp1 : p.steps.1 = q.steps.1) (hp2 : p.steps.2 ++ [.deref] <+: q.steps.2)
    (hp : ckContent st.env p = some .proof) : False := by
  obtain ⟨rest, hrest⟩ := hp2
  -- the `*` after `p` is through a place declared a borrow (the grain)
  obtain ⟨d, hd⟩ : ∃ d, K.D.placeDecl (scopeOf s) p = .ref d :=
    hgrain p .deref rest hp1 (by rw [← hrest]; simp)
  -- `p` is at the grain and holds `⋆`, so it is declared a copy ((C⋆))
  have hgp : GrainOk K.D K.Γ (scopeOf s) p := grain_prefix hgrain hp1 ⟨[.deref] ++ rest, by rw [← hrest]; simp⟩
  have hc := hctx.shapes.proofCopy p (by rw [← rel_scopeOf K ρ φ hs]; exact hgp) hp
  rw [← rel_scopeOf K ρ φ hs, hd] at hc
  -- no borrow type is a copy type (`declCopy`)
  have hnc : K.D.copy (.ref d) = false :=
    hctx.dec.copy 1 (.ref d) false 0 st ⟨#[], _, _, rfl⟩
  rw [hnc] at hc
  cases hc

/-- **No place the join drops is at or below a `⋆`**: through field steps it holds `⋆` too, and is
a copy ((C⋆)), which the join does not drop; through a `*`, the join derefs no proof
(`grain_deref_not_proof`). PROVED from `grain_deref_not_proof`. (Below a variable only until the
slice, 2026-11-20; at a variable too since (C⋆) covers variables.) -/
theorem not_below_proof (st : MState) (s : SState) (π : Nat → Nat) (q q' : Place)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (h1 : q'.steps.1 = q.steps.1) (h2 : q'.steps.2 <+: q.steps.2)
    (hq' : ckContent st.env q' = some .proof) : False := by
  obtain ⟨rest, hrest⟩ := h2
  obtain ⟨pos, hck, hf⟩ := Option.bind_eq_some_iff.mp hq'
  have key : ∀ (rs fs : List Step), q.steps.2 = q'.steps.2 ++ fs ++ rs → (∀ x ∈ fs, x ≠ .deref) → False := by
    intro rs
    induction rs with
    | nil =>
      intro fs he hfs
      have hc : ckContent st.env q = some .proof := by
        unfold ckContent
        rw [← h1, hck, Option.bind_some, he, List.append_nil, follow_append, hf, Option.bind_some]
        exact follow_proof_fields fs hfs
      have h := hctx.shapes.proofCopy q (by rw [← rel_scopeOf K ρ φ hs]; exact hgrain) hc
      rw [← rel_scopeOf K ρ φ hs, hcopy] at h
      cases h
    | cons x rs ih =>
      intro fs he hfs
      cases x with
      | deref =>
        refine grain_deref_not_proof K ρ φ st s π q (Ochr.jdExtend q' fs) hg hctx hs hgrain hcopy
          (by rw [jdExtend_steps]; exact h1) (by rw [jdExtend_steps, he]; simp) ?_
        unfold ckContent
        rw [jdExtend_steps]
        simp only
        rw [hck, Option.bind_some, follow_append, hf, Option.bind_some]
        exact follow_proof_fields fs hfs
      | proj i =>
        exact ih (fs ++ [.proj i]) (by rw [he]; simp) (by
          intro y hy; rcases List.mem_append.mp hy with hy | hy
          · exact hfs y hy
          · simp at hy; rw [hy]; exact fun h => nomatch h)
      | field g =>
        exact ih (fs ++ [.field g]) (by rw [he]; simp) (by
          intro y hy; rcases List.mem_append.mp hy with hy | hy
          · exact hfs y hy
          · simp at hy; rw [hy]; exact fun h => nomatch h)
  exact key rest [] (by rw [← hrest]; simp) (by simp)

end

end Ochr.Meaning.Steps
