import Pss.Mpss.Substitution
import Pss.Mpss.Weakening
import Pss.Mpss.AvoidsPro

/-! # `Pss.Mpss.Renaming` — fresh-variable renaming for MPSS reductions

When two cofinite-quantified body premises need to be combined (as in the
`fun_ × fun_` and `fOp × fOp` cases of Lemma 2 / the diamond property),
the result is naturally proved at one specific fresh `y`. We then need to
**rename** that body-level derivation to an arbitrary other fresh `z` so
the conclusion can be packaged back into a cofinite premise.

This module provides:

* `MEqRed.rename_sub` — rename `y → z` in
  `MEqRed (⟨y, t, .sub⟩::Γ) s (body^[y]) (body'^[y])`
  to obtain the same statement at `z`.
* `MEqRed.rename_equ` — same shape but for an `.equ` head binding.
* `MSubRed.rename_sub` / `MSubRed.rename_equ` — analogues for `MSubRed`.

## Strategy

Each renaming theorem is proved by direct induction on the derivation,
mirroring the structure of `Lemma_31_ReductionUnderSubst_Eq` /
`Lemma_32_ReductionUnderSubst_Eq_OfEqu` from `Pss.Mpss.Substitution`,
specialized to the case where the substituted term is `(.fvar z)` for
a fresh `z`.

For the `.sub`-head version we leverage Lemma 31 directly (after a
weakening step that brings `z` into scope, so `SubstOk` is satisfied).
For the `.equ`-head version we use Lemma 32's restricted form
(`s = v`) on a special instance (`y → y` for the kind change), but the
real renaming uses a custom proof inlined here.
-/

namespace Pss

/-! ## §1. Substitution-fresh helpers -/

/-- `Stack.subst` is the identity on a stack whose terms don't mention `x`. -/
theorem Stack.subst_fresh {x : String} {u : Term} {s : Stack}
    (h : ∀ α ∈ s, x ∉ Term.fv α) :
    Stack.subst x u s = s := by
  induction s with
  | nil => rfl
  | cons α tail ih =>
    have hα : x ∉ Term.fv α := h α (List.mem_cons_self α tail)
    have htail : ∀ β ∈ tail, x ∉ Term.fv β := fun β hβ =>
      h β (List.mem_cons_of_mem α hβ)
    rw [Stack.subst_cons, Term.subst_fresh hα, ih htail]

/-- `Ctx.subst` is the identity on a context whose entries don't mention `x`
in their bound terms. -/
theorem Ctx.subst_fresh {x : String} {u : Term} {Γ : Ctx}
    (h : ∀ e ∈ Γ, x ∉ Term.fv e.bound) :
    Ctx.subst x u Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons e rest ih =>
    have he : x ∉ Term.fv e.bound := h e (List.mem_cons_self e rest)
    have hrest : ∀ f ∈ rest, x ∉ Term.fv f.bound := fun f hf =>
      h f (List.mem_cons_of_mem e hf)
    rw [Ctx.subst_cons, Term.subst_fresh he, ih hrest]

/-- Helper: `fv u ⊆ Γ.dom` and `x ∉ Γ.dom` imply `x ∉ fv u`. -/
private lemma fv_notin_of_dom_notin {Γ : Ctx} {u : Term} {x : String}
    (hfv : Term.fv u ⊆ Γ.dom) (hx : x ∉ Γ.dom) : x ∉ Term.fv u :=
  fun h => hx (hfv h)

/-- Renaming via subst-then-open: when `y ∉ fv e`, opening with `z` is
the same as opening with `y` then substituting `y → z`. The mirror of
`Term.subst_intro`. -/
theorem Term.subst_open_fresh {y z : String} {e : Term}
    (hy : y ∉ Term.fv e) :
    Term.subst y (.fvar z) (e^[y]) = e^[z] :=
  (Term.subst_intro (x := y) (u := .fvar z) (e := e) hy
    (Term.LC.fvar z)).symm

/-! ## §2. Renaming for MEqRed under a `.sub` head binding

We invoke Lemma 31 with the substituted term `(.fvar z)`. To satisfy
`SubstOk`'s `fv (.fvar z) ⊆ Γ.dom` constraint we first weaken (Lemma 22)
to insert `⟨z, t, .sub⟩` into the tail, then apply Lemma 31. The
substituted output context drops the `y`-head (since Lemma 31 with
`Γ₂ = []` yields the tail directly).
-/

/-- **Renaming for `MEqRed` under a `.sub`-head binding.** Given a
derivation at a fresh `y`, produce one at any other fresh `z`. -/
noncomputable def MEqRed.rename_sub
    {Γ : Ctx} {s : Stack} {body body' t : Term} {y z : String}
    (hpvΓ : Prevalid Γ)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ.dom)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hfv_body : Term.fv body ⊆ Γ.dom) (hfv_body' : Term.fv body' ⊆ Γ.dom)
    (hy_notin_stack : ∀ α ∈ s, y ∉ Term.fv α)
    (h : MEqRed (⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MEqRed (⟨z, t, .sub⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  by_cases hyz : y = z
  · subst hyz; exact h
  -- Step 1: Build prevalidity for the weakened context ⟨y⟩::⟨z⟩::Γ.
  have hpvz : Prevalid (⟨z, t, .sub⟩ :: Γ) :=
    Prevalid.sub hpvΓ hz_notin_Γ hfvt hLCt
  have hyzdom : y ∉ Ctx.dom (⟨z, t, .sub⟩ :: Γ) := by
    rw [Ctx.dom_cons]
    intro hmem
    rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
    · exact hyz hyz'
    · exact hy_notin_Γ hyΓ
  have hfvt_z : Term.fv t ⊆ Ctx.dom (⟨z, t, .sub⟩ :: Γ) := by
    intro w hw
    rw [Ctx.dom_cons]
    exact Finset.mem_insert_of_mem (hfvt hw)
  have hpv_yz : Prevalid (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ) :=
    Prevalid.sub hpvz hyzdom hfvt_z hLCt
  -- Step 2: fv bound on body^[y].
  have hfv_open_y : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, t, .sub⟩ :: Γ) := by
    intro w hw
    have hsub := Term.fv_open_subset 0 (.fvar y) body
    rw [Ctx.dom_cons]
    rcases Finset.mem_union.mp (hsub hw) with hwBody | hwY
    · exact Finset.mem_insert_of_mem (hfv_body hwBody)
    · have hwy : w = y := by simpa [Term.fv] using hwY
      subst hwy
      exact Finset.mem_insert_self _ _
  -- Step 3: Apply Lemma 22. Insert [⟨z, t, .sub⟩] between [⟨y, t, .sub⟩] and Γ.
  have hpv_pre : Prevalid (([⟨y, t, .sub⟩] : Ctx) ++ Γ) := by
    show Prevalid (⟨y, t, .sub⟩ :: Γ)
    exact Prevalid.sub hpvΓ hy_notin_Γ hfvt hLCt
  have hpv_post : Prevalid (([⟨y, t, .sub⟩] : Ctx) ++ [⟨z, t, .sub⟩] ++ Γ) := by
    show Prevalid (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ)
    exact hpv_yz
  have h_weakened : MEqRed (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ)
      s (body^[y]) (body'^[y]) := by
    have hh : MEqRed (([⟨y, t, .sub⟩] : Ctx) ++ Γ) s (body^[y]) (body'^[y]) := by
      show MEqRed (⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y]); exact h
    have hfvU : Term.fv (body^[y]) ⊆ Ctx.dom (([⟨y, t, .sub⟩] : Ctx) ++ Γ) := by
      show Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, t, .sub⟩ :: Γ); exact hfv_open_y
    have hres :=
      Lemma_22_WeakeningMEqRed (Γ₁ := [⟨y, t, .sub⟩]) (Δ := [⟨z, t, .sub⟩]) (Γ₂ := Γ)
        hpv_pre hfvU hpv_post hh
    -- hres : MEqRed ([⟨y,...⟩] ++ [⟨z,...⟩] ++ Γ) ...; rewrite to cons form.
    have heq : (([⟨y, t, .sub⟩] : Ctx) ++ [⟨z, t, .sub⟩] ++ Γ) =
        (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ) := by simp
    exact heq ▸ hres
  -- Step 4: Apply Lemma 31. Γ₂ = [], Γ₁ = ⟨z, t, .sub⟩ :: Γ, x = y, s_sub = .fvar z.
  have hsub_ok : SubstOk (⟨z, t, .sub⟩ :: Γ) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  have h_weakened' :
      MEqRed (([] : Ctx) ++ ⟨y, t, .sub⟩ :: (⟨z, t, .sub⟩ :: Γ))
        s (body^[y]) (body'^[y]) := by
    show MEqRed (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y])
    exact h_weakened
  have h_subst :=
    Lemma_31_ReductionUnderSubst_Eq (Γ₂ := []) h_weakened' hsub_ok
  -- h_subst : MEqRed (Ctx.subst y (.fvar z) [] ++ ⟨z, t, .sub⟩ :: Γ)
  --                  (Stack.subst y (.fvar z) s)
  --                  (Term.subst y (.fvar z) (body^[y]))
  --                  (Term.subst y (.fvar z) (body'^[y]))
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, t, .sub⟩ :: Γ) =
        ⟨z, t, .sub⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-! ## §3. Renaming for MEqRed under an `.equ` head binding

For an `.equ`-head context `⟨y, α, .equ⟩ :: Γ`, Lemma 32 (restricted to
`s = v`) doesn't directly apply to renaming (we'd need `.fvar z = α`,
which is generally false).

We use a different tactic: we first apply Lemma 32 with a TRIVIAL
self-substitution `subst y (.fvar y)` to enable the IH machinery, then
notice that this is the identity. That alone doesn't help. The clean
fix is to inline the proof.

Below we provide a from-scratch renaming proof for `.equ` head, by
direct induction on the derivation (mirroring Lemma 32's structure).
The crucial `Me-Pro y_inner = y` arm uses uniqueness of the head
binding to rewrite the target, then applies `Me-Pro` for `z` against
the renamed head binding.
-/

/-- Specialized renaming substitution lemma for an `.equ` head binding.
Substitutes `(.fvar z)` for `y` in a derivation whose head-`.equ`
binding is `⟨y, α, .equ⟩`, where `y ∉ fv α` (always true by
prevalidity of the input context).

The proof is a direct induction on the derivation, mirroring
`Lemma_32_ReductionUnderSubst_Eq_OfEqu`. The renaming provides exactly
the structural simplification needed to dispatch the `Me-Pro y_inner = y`
arm uniformly: the looked-up `α` (= the head binding) is unaffected by
substitution, and the renamed lookup target `.fvar z` is found in the
new head `⟨z, α, .equ⟩`. -/
private noncomputable def MEqRed.subst_yz_equ_head
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) st u u') :
    MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  -- The substituted term s = .fvar z, the bound α at head is independent of y.
  -- We pose Lemma 32 with v := α, s := .fvar z, but Lemma 32 requires s = v.
  -- So we need to handle this via direct induction. Inline the proof.
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyiy : yi = y
    · -- yi = y. The .equ head for y has bound α — uniqueness gives β = α.
      have heq_y : (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁).equBinds y β :=
        hyiy ▸ heq
      have hβα : β = α := equBinds_at_equ_head_unique hpvL heq_y
      -- We rewrite β to α in ihβ rather than substituting (which would erase α).
      have ihβ_app := ihβ (Γ₂ := Γ₂) rfl
      rw [hβα] at ihβ_app
      have hα_subst : Term.subst y (.fvar z) α = α := Term.subst_fresh hy_notin_α
      rw [hα_subst] at ihβ_app
      -- We need equBinds for z in the renamed context.
      have hz_eqbinds :
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds z α := by
        -- z ∉ Γ₂.dom (and so z ∉ (Ctx.subst y (.fvar z) Γ₂).dom = Γ₂.dom).
        -- Then lookup misses in Γ₂ and finds z at the head of the tail.
        have hpvL_norm : Prevalid (Γ₂ ++ (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁)) :=
          hpvL
        have hpv_inner : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
          Prevalid.outer hpvL_norm
        -- z fresh w.r.t. ⟨y,α,.equ⟩ :: ... — actually z ∈ ⟨z,α,.equ⟩ :: Γ₁'s dom (it's the head).
        -- But is z ∈ Γ₂.dom? We need Γ₂.dom ∩ {z} = ∅. By prevalidity, all entries in Γ₂ have
        -- names ∉ subsequent context dom, so e.name ≠ z for all e in Γ₂.
        have hz_notin_Γ₂ : z ∉ Γ₂.dom := by
          intro hzΓ₂
          have hpv_inner' : Prevalid (⟨z, α, .equ⟩ :: Γ₁) :=
            Prevalid.outer (Γ₂ := [⟨y, α, .equ⟩]) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁) (by
              show Prevalid ([⟨y, α, .equ⟩] ++ ⟨z, α, .equ⟩ :: Γ₁); exact hpv_inner)
          -- z is the head's name; from Prevalid we get z ∉ Γ₁.dom but not Γ₂.dom directly.
          -- Need: from Prevalid (Γ₂ ++ ⟨y,α,.equ⟩ :: ⟨z,α,.equ⟩ :: Γ₁), prove z ∉ Γ₂.dom.
          -- This follows from the NoDup property: NoDup of names in the full list.
          -- Use Ctx.notin_delta_of_in_tail (from Weakening): z ∈ tail.dom → z ∉ Δ.dom.
          -- Treat Γ₂ as Δ, ⟨y,α,.equ⟩ :: ⟨z,α,.equ⟩ :: Γ₁ as the inner Γ₂.
          have hz_in_tail : z ∈ Ctx.dom (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
            rw [Ctx.dom_cons, Ctx.dom_cons]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          exact (Ctx.notin_delta_of_in_tail hpvL hz_in_tail) hzΓ₂
        -- Now, lookupEqu in Γ₂ for z is none (z ∉ dom).
        -- Then lookupEqu in ⟨z,α,.equ⟩ :: Γ₁ for z is some α.
        -- Use a helper: Ctx.lookupEqu_append_right.
        have hlk_tail : Ctx.lookupEqu (⟨z, α, .equ⟩ :: Γ₁) z = some α := by
          simp [Ctx.lookupEqu, Ctx.lookupEqu_cons]
        have hz_notin_subst_Γ₂ : z ∉ (Ctx.subst y (.fvar z) Γ₂).dom := by
          rw [Ctx.dom_subst]; exact hz_notin_Γ₂
        show Ctx.lookupEqu (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) z = some α
        exact Ctx.lookupEqu_append_right (Ctx.subst y (.fvar z) Γ₂) _ z α
          hz_notin_subst_Γ₂ hlk_tail
      have hfvar_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hfvar_eq]
      exact MEqRed.pro hpv' hz_eqbinds ihβ_app
    · -- yi ≠ y: standard case. Look up yi's .equ binding in renamed context.
      rw [Term.subst_fvar_ne hyiy]
      have heq' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds yi
          (Term.subst y (.fvar z) β) := by
        -- equBinds_split_equ: handles ⟨y, v, .equ⟩-head case via Lemma 32 lemma.
        -- Our context is Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁; substitute y → fvar z.
        -- equBinds_split_equ handles substituting at an .equ head, where the head is
        -- ⟨y, α, .equ⟩, the tail is ⟨z, α, .equ⟩ :: Γ₁.
        exact equBinds_split_equ (s := .fvar z) hyiy hpvL heq
      exact MEqRed.pro hpv' heq' (ihβ (Γ₂ := Γ₂) rfl)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody hv ihbody ihv =>
    subst hΓ
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open : Term.subst y (.fvar z) (Term.opening v0' bd') =
        Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      simp [Term.opening, Term.subst_open hLCfz]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app (.abs tBound bd) v0))
      (Term.subst y (.fvar z) (Term.opening v0' bd'))
    rw [hsubst_open]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (.app (.abs (Term.subst y (.fvar z) tBound) (Term.subst y (.fvar z) bd))
            (Term.subst y (.fvar z) v0))
      (Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd'))
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ ?_
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := Γ₂) rfl
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      exact ih_body
    · have ihv' := ihv (Γ₂ := Γ₂) rfl
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    exact MEqRed.top (Lemma_28_SubstPreservesPrevalid hpv hok)
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) rfl
    have ihv' := ihv (Γ₂ := Γ₂) rfl
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyiy : yi = y
    · -- subst y (.fvar z) (.fvar yi) = .fvar z when yi = y.
      have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hsubst_eq]
      have hLCz : Term.LC (.fvar z) := Term.LC.fvar z
      have hfvz : Term.fv (.fvar z) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
        intro w hw
        have hwz : w = z := by simpa [Term.fv] using hw
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      exact MEqRed.refl hpv' hLCz hfvz
    · rw [Term.subst_fvar_ne hyiy]
      exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y}) ?_ ?_
    · have iht' := iht (Γ₂ := Γ₂) rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂) (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
          hfv hwfv
        rw [Ctx.dom_append] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst]
        rcases Finset.mem_union.mp hwΓ with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · simp [Ctx.dom_cons] at htail
          rcases htail with hwy | hwz | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · subst hwz
            apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]
          · apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]; exact Or.inr hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst]
        apply Finset.mem_union.mpr; right
        simp [Ctx.dom_cons]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app .top u_)) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y}) ?_ ?_
    · have iht' := iht (Γ₂ := Γ₂) rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂) (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-- **Renaming for `MEqRed` under an `.equ`-head binding.** Given a
derivation at a fresh `y`, produce one at any other fresh `z`. -/
noncomputable def MEqRed.rename_equ
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hpvΓ : Prevalid Γ)
    (hLCα : Term.LC α) (hfvα : Term.fv α ⊆ Γ.dom)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hfv_body : Term.fv body ⊆ Γ.dom) (hfv_body' : Term.fv body' ⊆ Γ.dom)
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MEqRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  by_cases hyz : y = z
  · subst hyz; exact h
  -- Build prevalidity for ⟨y,α,.equ⟩ :: ⟨z,α,.equ⟩ :: Γ.
  have hy_notin_α : y ∉ Term.fv α := fv_notin_of_dom_notin hfvα hy_notin_Γ
  have hpvz : Prevalid (⟨z, α, .equ⟩ :: Γ) :=
    Prevalid.equ hpvΓ hz_notin_Γ hfvα hLCα
  have hyzdom : y ∉ Ctx.dom (⟨z, α, .equ⟩ :: Γ) := by
    rw [Ctx.dom_cons]
    intro hmem
    rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
    · exact hyz hyz'
    · exact hy_notin_Γ hyΓ
  have hfvα_z : Term.fv α ⊆ Ctx.dom (⟨z, α, .equ⟩ :: Γ) := by
    intro w hw
    rw [Ctx.dom_cons]
    exact Finset.mem_insert_of_mem (hfvα hw)
  have hpv_yz : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) :=
    Prevalid.equ hpvz hyzdom hfvα_z hLCα
  -- Build fv bound on body^[y].
  have hfv_open_y : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
    intro w hw
    have hsub := Term.fv_open_subset 0 (.fvar y) body
    rw [Ctx.dom_cons]
    rcases Finset.mem_union.mp (hsub hw) with hwBody | hwY
    · exact Finset.mem_insert_of_mem (hfv_body hwBody)
    · have hwy : w = y := by simpa [Term.fv] using hwY
      subst hwy
      exact Finset.mem_insert_self _ _
  -- Apply Lemma 22.
  have hpv_pre : Prevalid (([⟨y, α, .equ⟩] : Ctx) ++ Γ) := by
    show Prevalid (⟨y, α, .equ⟩ :: Γ)
    exact Prevalid.equ hpvΓ hy_notin_Γ hfvα hLCα
  have hpv_post : Prevalid (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ) := by
    show Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ)
    exact hpv_yz
  have h_weakened : MEqRed (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ)
      s (body^[y]) (body'^[y]) := by
    have hh : MEqRed (([⟨y, α, .equ⟩] : Ctx) ++ Γ) s (body^[y]) (body'^[y]) := by
      show MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]); exact h
    have hfvU : Term.fv (body^[y]) ⊆ Ctx.dom (([⟨y, α, .equ⟩] : Ctx) ++ Γ) := by
      show Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ); exact hfv_open_y
    have hres :=
      Lemma_22_WeakeningMEqRed (Γ₁ := [⟨y, α, .equ⟩]) (Δ := [⟨z, α, .equ⟩]) (Γ₂ := Γ)
        hpv_pre hfvU hpv_post hh
    have heq : (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ) =
        (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) := by simp
    exact heq ▸ hres
  -- Apply our specialized renaming substitution.
  have h_norm : MEqRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ)
      s (body^[y]) (body'^[y]) := by
    show MEqRed (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])
    exact h_weakened
  have h_subst :=
    MEqRed.subst_yz_equ_head (Γ₂ := []) hyz hy_notin_α h_norm
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, α, .equ⟩ :: Γ) =
        ⟨z, α, .equ⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-! ## §4. Renaming for MSubRed

Same pattern as MEqRed but invokes Lemma 30 / Lemma 21 internally. The
escape-hatch `Lemma_30_msPro_x_axiom` only fires for the `Ms-Pro y = x`
arm; under our renaming use case (`x = .fvar z`, `t = subBinds`), this
becomes `MSubRed _ _ (.fvar z) (subst y (.fvar z) t)` which still uses
the axiom — but the axiom's preconditions are met.
-/

/-- **Renaming for `MSubRed` under a `.sub`-head binding.** Analogous to
`MEqRed.rename_sub`, via Lemma 30 and Lemma 21. -/
noncomputable def MSubRed.rename_sub
    {Γ : Ctx} {s : Stack} {body body' t : Term} {y z : String}
    (hpvΓ : Prevalid Γ)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ.dom)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hfv_body : Term.fv body ⊆ Γ.dom) (hfv_body' : Term.fv body' ⊆ Γ.dom)
    (hy_notin_stack : ∀ α ∈ s, y ∉ Term.fv α)
    (h : MSubRed (⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MSubRed (⟨z, t, .sub⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  by_cases hyz : y = z
  · subst hyz; exact h
  have hpvz : Prevalid (⟨z, t, .sub⟩ :: Γ) :=
    Prevalid.sub hpvΓ hz_notin_Γ hfvt hLCt
  have hyzdom : y ∉ Ctx.dom (⟨z, t, .sub⟩ :: Γ) := by
    rw [Ctx.dom_cons]
    intro hmem
    rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
    · exact hyz hyz'
    · exact hy_notin_Γ hyΓ
  have hfvt_z : Term.fv t ⊆ Ctx.dom (⟨z, t, .sub⟩ :: Γ) := by
    intro w hw
    rw [Ctx.dom_cons]
    exact Finset.mem_insert_of_mem (hfvt hw)
  have hpv_yz : Prevalid (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ) :=
    Prevalid.sub hpvz hyzdom hfvt_z hLCt
  have hfv_open_y : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, t, .sub⟩ :: Γ) := by
    intro w hw
    have hsub := Term.fv_open_subset 0 (.fvar y) body
    rw [Ctx.dom_cons]
    rcases Finset.mem_union.mp (hsub hw) with hwBody | hwY
    · exact Finset.mem_insert_of_mem (hfv_body hwBody)
    · have hwy : w = y := by simpa [Term.fv] using hwY
      subst hwy; exact Finset.mem_insert_self _ _
  have hpv_pre : Prevalid (([⟨y, t, .sub⟩] : Ctx) ++ Γ) := by
    show Prevalid (⟨y, t, .sub⟩ :: Γ)
    exact Prevalid.sub hpvΓ hy_notin_Γ hfvt hLCt
  have hpv_post : Prevalid (([⟨y, t, .sub⟩] : Ctx) ++ [⟨z, t, .sub⟩] ++ Γ) := by
    show Prevalid (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ); exact hpv_yz
  have h_weakened : MSubRed (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ)
      s (body^[y]) (body'^[y]) := by
    have hh : MSubRed (([⟨y, t, .sub⟩] : Ctx) ++ Γ) s (body^[y]) (body'^[y]) := by
      show MSubRed (⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y]); exact h
    have hfvU : Term.fv (body^[y]) ⊆ Ctx.dom (([⟨y, t, .sub⟩] : Ctx) ++ Γ) := by
      show Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, t, .sub⟩ :: Γ); exact hfv_open_y
    have hres :=
      Lemma_21_WeakeningMSubRed (Γ₁ := [⟨y, t, .sub⟩]) (Δ := [⟨z, t, .sub⟩]) (Γ₂ := Γ)
        hpv_pre hfvU hpv_post hh
    have heq : (([⟨y, t, .sub⟩] : Ctx) ++ [⟨z, t, .sub⟩] ++ Γ) =
        (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ) := by simp
    exact heq ▸ hres
  have hsub_ok : SubstOk (⟨z, t, .sub⟩ :: Γ) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  have h_weakened' :
      MSubRed (([] : Ctx) ++ ⟨y, t, .sub⟩ :: (⟨z, t, .sub⟩ :: Γ))
        s (body^[y]) (body'^[y]) := by
    show MSubRed (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y])
    exact h_weakened
  have h_subst :=
    Lemma_30_ReductionUnderSubst_Sub (Γ₂ := []) h_weakened' hsub_ok
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, t, .sub⟩ :: Γ) =
        ⟨z, t, .sub⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-! ## §5. Renaming for MSubRed under an `.equ` head binding

Build via the `Ms-Equ` arm: an `MSubRed` derivation that's not merely
`Ms-Equ` of an `MEqRed` requires special handling. We mirror the
structure of `MEqRed.subst_yz_equ_head` for `MSubRed`'s constructors.
-/

/-- Specialized renaming substitution lemma for `MSubRed` under an
`.equ` head binding. Mirrors `MEqRed.subst_yz_equ_head`. -/
private noncomputable def MSubRed.subst_yz_equ_head
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MSubRed (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) st u u') :
    MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi t' hpv hsb =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyiy : yi = y
    · -- yi = y. Only y-entry is .equ, not .sub: contradiction.
      subst hyiy
      exact (subBinds_at_equ_head_impossible hpvL hsb).elim
    · rw [Term.subst_fvar_ne hyiy]
      have hsb' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).subBinds yi
          (Term.subst y (.fvar z) t') :=
        subBinds_split_equ (s := .fvar z) hyiy hpvL hsb
      exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
          hfv hwfv
        rw [Ctx.dom_append] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst]
        rcases Finset.mem_union.mp hwΓ with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · simp [Ctx.dom_cons] at htail
          rcases htail with hwy | hwz | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · subst hwz
            apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]
          · apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]; exact Or.inr hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst]
        apply Finset.mem_union.mpr; right
        simp [Ctx.dom_cons]
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) u_) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MSubRed.top hpv' hLCu' hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have heq' :=
      MEqRed.subst_yz_equ_head (Γ₂ := Γ₂) hyz hy_notin_α heq
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) rfl
    have hLCv' : Term.LC (Term.subst y (.fvar z) v_) :=
      Term.subst_lc (Term.LC.fvar z) hLCv
    have hfvv' :
        Term.fv (Term.subst y (.fvar z) v_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) v_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
          hfvv hwfv
        rw [Ctx.dom_append] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst]
        rcases Finset.mem_union.mp hwΓ with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · simp [Ctx.dom_cons] at htail
          rcases htail with hwy | hwz | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · subst hwz
            apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]
          · apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]; exact Or.inr hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst]
        apply Finset.mem_union.mpr; right
        simp [Ctx.dom_cons]
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app u_ v_)) (Term.subst y (.fvar z) (.app u_' v_))
    simp [Term.subst]
    refine MSubRed.app ?_ hLCv' hfvv'
    simpa using ihu'
  | @fun_ Γ tt bd bd' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
    intro yfresh hyfresh
    simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
    have hyfL : yfresh ∉ L := hyfresh.1
    have hyfy : yfresh ≠ y := hyfresh.2
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂) (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' tt αi bd bd' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
    intro yfresh hyfresh
    simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
    have hyfL : yfresh ∉ L := hyfresh.1
    have hyfy : yfresh ≠ y := hyfresh.2
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂) (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body

/-- **Renaming for `MSubRed` under an `.equ`-head binding.** -/
noncomputable def MSubRed.rename_equ
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hpvΓ : Prevalid Γ)
    (hLCα : Term.LC α) (hfvα : Term.fv α ⊆ Γ.dom)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hfv_body : Term.fv body ⊆ Γ.dom) (hfv_body' : Term.fv body' ⊆ Γ.dom)
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MSubRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  by_cases hyz : y = z
  · subst hyz; exact h
  have hy_notin_α : y ∉ Term.fv α := fv_notin_of_dom_notin hfvα hy_notin_Γ
  have hpvz : Prevalid (⟨z, α, .equ⟩ :: Γ) :=
    Prevalid.equ hpvΓ hz_notin_Γ hfvα hLCα
  have hyzdom : y ∉ Ctx.dom (⟨z, α, .equ⟩ :: Γ) := by
    rw [Ctx.dom_cons]
    intro hmem
    rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
    · exact hyz hyz'
    · exact hy_notin_Γ hyΓ
  have hfvα_z : Term.fv α ⊆ Ctx.dom (⟨z, α, .equ⟩ :: Γ) := by
    intro w hw
    rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem (hfvα hw)
  have hpv_yz : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) :=
    Prevalid.equ hpvz hyzdom hfvα_z hLCα
  have hfv_open_y : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
    intro w hw
    have hsub := Term.fv_open_subset 0 (.fvar y) body
    rw [Ctx.dom_cons]
    rcases Finset.mem_union.mp (hsub hw) with hwBody | hwY
    · exact Finset.mem_insert_of_mem (hfv_body hwBody)
    · have hwy : w = y := by simpa [Term.fv] using hwY
      subst hwy; exact Finset.mem_insert_self _ _
  have hpv_pre : Prevalid (([⟨y, α, .equ⟩] : Ctx) ++ Γ) := by
    show Prevalid (⟨y, α, .equ⟩ :: Γ)
    exact Prevalid.equ hpvΓ hy_notin_Γ hfvα hLCα
  have hpv_post : Prevalid (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ) := by
    show Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ); exact hpv_yz
  have h_weakened : MSubRed (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ)
      s (body^[y]) (body'^[y]) := by
    have hh : MSubRed (([⟨y, α, .equ⟩] : Ctx) ++ Γ) s (body^[y]) (body'^[y]) := by
      show MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]); exact h
    have hfvU : Term.fv (body^[y]) ⊆ Ctx.dom (([⟨y, α, .equ⟩] : Ctx) ++ Γ) := by
      show Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ); exact hfv_open_y
    exact Lemma_21_WeakeningMSubRed hpv_pre hfvU hpv_post hh
  have h_norm : MSubRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ)
      s (body^[y]) (body'^[y]) := by
    have heq : (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ) =
        (([] : Ctx) ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) := by simp
    exact heq ▸ h_weakened
  have h_subst :=
    MSubRed.subst_yz_equ_head (Γ₂ := []) hyz hy_notin_α h_norm
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, α, .equ⟩ :: Γ) =
        ⟨z, α, .equ⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

end Pss
