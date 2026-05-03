import Pss.Reduction.Operational
import Pss.Mpss.Reductions
import Pss.Mpss.Substitution

set_option linter.unusedVariables false

/-! # `Pss.Mpss.OperationalSem` — Proposition 17 (operational ↣ MPSS equiv-red)

Pasquale & García-Pérez 2024 (CSL 2026), Proposition 17 (p. 33):

> Let `u` and `v` be terms. If `u ↦ v` then `Γ; s ⊢ u ⟶^≡ v` for all
> extended context `Γ; s`.

The paper's proof:
> By induction on the derivation tree of `u ↦ v`. The base case is when
> the last rule used is `Os-Bet`, and the result holds by rule `Me-Bet`
> and reflexivity of `⟶^≡` (Proposition 18). The induction cases is
> when the last rule used is `Os-Con`, and the result holds by induction
> and rules `Me-Fun`, `Me-FOp` and `Me-App`.

## Mechanization

Three of the five `Step` constructors (`appL`, `appR`, `absBound`,
`absBody`) reduce directly to the corresponding congruence rules of
`MEqRed`. The β case (`Step.beta`) is more subtle in our
locally-nameless encoding: `MEqRed.bet`'s body sub-derivation requires
`MEqRed Γ s (body^[y]) (body^[y])` for fresh `y`, which would need
`fv (body^[y]) ⊆ Γ.dom` — but `body^[y]` may free-mention `y ∉ Γ.dom`.

`MEqRed.refl` (proven in `Pss/Mpss/Substitution.lean`) handles binders
by extending the context with the freshly chosen name. But Me-Bet's body
sub-derivation is at the SAME context `Γ; s`, not the extended one. The
paper's proof glosses over this — it implicitly treats the bound name
as a meta-variable rather than a free variable in the context. Our
locally-nameless encoding makes the obstruction explicit.

The fix would be a custom β-helper that constructs `MEqRed Γ s e e` from
`LC e` by walking the structure and using `MEqRed.var` (which has no
fv-scope requirement) at fvars. The recursive `.app` case would still
need `PrevalidExt Γ (b :: s)`, requiring `fv b ⊆ Γ.dom`. So this is a
real obstacle for terms with stray fvars.

## Status

The four congruence cases (`appL`, `appR`, `absBound`, `absBody`) are
PROVED directly. The β case (`Step.beta`) is AXIOMATIZED as
`Proposition_17_beta_axiom` — see comment in §1 below.

Combined statement `Proposition_17_FromOperationalToEqRed` is then
PROVED conditional on `Proposition_17_beta_axiom`. -/

namespace Pss

/-! ## §1. The β-case axiom

The `Step.beta` case requires showing `MEqRed Γ s ((λ ≤ bound. body) arg)
(Term.opening arg body)` from the operational β-step. The natural
construction via `MEqRed.bet` requires a body sub-derivation in `Γ; s`
(NOT extended), which fails the fv-scope requirement of `MEqRed.refl`
when the freshly opened body mentions a name outside `Γ.dom`.

**Path-1 (custom β-helper) blocker analysis (2026-05-03 attempted):**
The naive recipe — "walk `LC body^[y]` and use `MEqRed.var` at fvars (no
fv-scope check)" — does NOT close. The wall is `MEqRed.app`'s
constructor signature:

```
| app : MEqRed Γ (v :: s) u u' → MEqRed Γ [] v v' →
        MEqRed Γ s (.app u v) (.app u' v')
```

To CONSTRUCT the first sub-derivation `MEqRed Γ (v :: s) u u'` we
recurse into `u`; every leaf (e.g. `MEqRed.var hpv`) requires
`PrevalidExt Γ (v :: s)`, which requires `fv v ⊆ Γ.dom`. When `body`
contains `.app a b` with `b` syntactically containing `.bvar 0`,
`b^[y]` free-mentions `y ∉ Γ.dom` and the PrevalidExt fails. Concrete
counterexample: `body = .app (.bvar 0) (.bvar 0)` ⇒ `body^[y] =
.app (.fvar y) (.fvar y)`; PrevalidExt Γ (.fvar y :: s) needs
`{y} ⊆ Γ.dom`, FALSE for fresh y.

**Path-1 + strip blocker analysis.** Building at the EXTENDED context
`⟨y, .top, .sub⟩ :: Γ` (where y has scope) succeeds, but the strip
`MEqRed (⟨y, .top, .sub⟩ :: Γ) s u u' → MEqRed Γ s u u'` fails on the
`MEqRed.app` arm: the recursion needs `y ∉ fv v` for the operand to
re-establish PrevalidExt at unextended Γ, but in the just-built
derivation `v` may free-mention y (precisely the case that motivated
the extended-ctx construction). Strip and construct hit the same
`.app`-operand wall.

**Path-2 (alpha-equivariance) is forbidden.** Per the discharge-campaign
constraints, alpha-equivariance is the cluster-wide blocker for the
β-residuals and is not available here.

**Path-3 (refine `MEqRed.bet`'s body premise) is forbidden.** Per
`MEQRED-BET-AUDIT.md`, the unextended-Γ body premise is paper-faithful
and required for Lemma 1's commutativity proof. Modifying it would
break headline Lemma 1.

**Path-4 (Type-LC + alpha-aware MEqRed) is multi-day cross-codebase
refactor.** Redesigning `MEqRed.bet` / `.fun_` / `.fOp` to take a
Type-valued cofinite quantifier whose sample point is invariant under
the rename functors. See `AXIOMS.md` axiom #5 for the full plan.

The axiom remains. -/

/-- **Escape-hatch axiom** for the β-case of Proposition 17.

For any prevalid extended context `Γ; s` and any LC well-scoped β-redex
`(λ ≤ bound. body) arg`, the operational β-step embeds into MPSS
equivalence reduction.

**Why an axiom (precise blocker):** `MEqRed.bet`'s body sub-derivation
is at `Γ; s` (NOT extended) — see `MEQRED-BET-AUDIT.md` for confirmation
that this is paper-faithful and must NOT be modified. The natural
construction needs `MEqRed Γ s (body^[x]) (body^[x])` for fresh `x`,
which would require `fv (body^[x]) ⊆ Γ.dom` for `MEqRed.refl` — but
`body^[x]` may free-mention `x ∉ Γ.dom`.

The 2026-05-03 path-1 attempt confirmed the LN obstruction propagates
through `MEqRed.app`'s implicit PrevalidExt-on-stack requirement. The
discharge requires alpha-equivariance OR the Type-LC + alpha-aware
MEqRed redesign (Path 4). See `AXIOMS.md` axiom #5 for full analysis. -/
axiom Proposition_17_beta_axiom
    {Γ : Ctx} {s : Stack} {bound body arg : Term}
    (hpv : PrevalidExt Γ s)
    (hAbs : Term.LC (.abs bound body))
    (hArg : Term.LC arg)
    (hfv : Term.fv (.app (.abs bound body) arg) ⊆ Γ.dom) :
    MEqRed Γ s (.app (.abs bound body) arg) (Term.opening arg body)

/-! ## §2. Auxiliary -/

/-- Free-variable scoping for `Term.opening`. -/
private theorem _fv_opening_subset (u e : Term) :
    Term.fv (Term.opening u e) ⊆ Term.fv e ∪ Term.fv u :=
  fun _ hx => Term.fv_open_subset 0 u e hx

/-! ## §3. Proposition 17 -/

/-- **Proposition 17 (Pasquale & García-Pérez 2024 §3, From operational
to equivalence reduction).**

The operational small-step `t ↦ t'` (Hutchins-style β + congruence)
embeds into MPSS equivalence reduction `Γ; s ⊢ t ⟶^≡ t'` at every
prevalid extended context that scopes `t`.

Side conditions: prevalidity of `Γ; s`, local closure of `t`, and
free-variable scoping `fv t ⊆ Γ.dom`.

PROVED conditional on `Proposition_17_beta_axiom` (the β-case escape
hatch, see §1). The four congruence cases (`appL`, `appR`, `absBound`,
`absBody`) are proved directly via the corresponding `MEqRed`
congruence constructors. -/
theorem Proposition_17_FromOperationalToEqRed
    {Γ : Ctx} {s : Stack} {t t' : Term}
    (hpv : PrevalidExt Γ s)
    (hLC : Term.LC t)
    (hfv : Term.fv t ⊆ Γ.dom)
    (hstep : Step t t') :
    Nonempty (MEqRed Γ s t t') := by
  induction hstep generalizing Γ s with
  | @beta bound body arg hAbs hArg =>
    exact ⟨Proposition_17_beta_axiom hpv hAbs hArg hfv⟩
  | @appL t t' u hstep huLC ih =>
    have hLCt : Term.LC t := by cases hLC with | app h _ => exact h
    have hfv_t : Term.fv t ⊆ Γ.dom := by
      intro y hy; apply hfv; simp [Term.fv]; exact Or.inl hy
    have hfv_u : Term.fv u ⊆ Γ.dom := by
      intro y hy; apply hfv; simp [Term.fv]; exact Or.inr hy
    have hpv' : PrevalidExt Γ (u :: s) := PrevalidExt.cons hpv huLC hfv_u
    have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    obtain ⟨ihResult⟩ := ih hpv' hLCt hfv_t
    obtain ⟨huRefl⟩ : MEqRedJ Γ [] u u := MEqRed.refl_J hpvNil huLC hfv_u
    exact ⟨MEqRed.app ihResult huRefl⟩
  | @appR t u u' htLC hstep ih =>
    have hLCu : Term.LC u := by cases hLC with | app _ h => exact h
    have hfv_t : Term.fv t ⊆ Γ.dom := by
      intro y hy; apply hfv; simp [Term.fv]; exact Or.inl hy
    have hfv_u : Term.fv u ⊆ Γ.dom := by
      intro y hy; apply hfv; simp [Term.fv]; exact Or.inr hy
    have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    obtain ⟨ihResult⟩ := ih hpvNil hLCu hfv_u
    have hpv' : PrevalidExt Γ (u :: s) := PrevalidExt.cons hpv hLCu hfv_u
    obtain ⟨htRefl⟩ : MEqRedJ Γ (u :: s) t t := MEqRed.refl_J hpv' htLC hfv_t
    exact ⟨MEqRed.app htRefl ihResult⟩
  | @absBound bound bound' body L hstep hbodyLC ih =>
    have hLCbound : Term.LC bound := Step.lc_left hstep
    have hfvBound : Term.fv bound ⊆ Γ.dom := by
      intro y hy; apply hfv; simp [Term.fv]; exact Or.inl hy
    have hfvBody : Term.fv body ⊆ Γ.dom := by
      intro y hy; apply hfv; simp [Term.fv]; exact Or.inr hy
    have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    obtain ⟨ihBound⟩ := ih hpvNil hLCbound hfvBound
    cases s with
    | nil =>
      classical
      have hbody_each : ∀ y, y ∉ (L ∪ Γ.dom ∪ Term.fv body) →
          Nonempty (MEqRed (⟨y, bound, .sub⟩ :: Γ) [] (body^[y]) (body^[y])) := by
        intro y hy
        have hyL : y ∉ L := fun h => hy (by
          apply Finset.mem_union.mpr; left
          apply Finset.mem_union.mpr; left; exact h)
        have hyΓ : y ∉ Γ.dom := fun h => hy (by
          apply Finset.mem_union.mpr; left
          apply Finset.mem_union.mpr; right; exact h)
        have hpvy : Prevalid (⟨y, bound, .sub⟩ :: Γ) :=
          Prevalid.sub (extractPrevalid hpv) hyΓ hfvBound hLCbound
        have hpvyExt : PrevalidExt (⟨y, bound, .sub⟩ :: Γ) [] :=
          PrevalidExt.nil hpvy
        have hLCbodyOpen : Term.LC (Term.opening (.fvar y) body) := hbodyLC y hyL
        have hfvBodyOpen : Term.fv (Term.opening (.fvar y) body) ⊆
            Ctx.dom (⟨y, bound, .sub⟩ :: Γ) := by
          intro z hz
          have h := _fv_opening_subset (.fvar y) body hz
          rcases Finset.mem_union.mp h with h | h
          · have : z ∈ Γ.dom := hfvBody h
            simp [Ctx.dom_cons]; exact Or.inr this
          · have : z = y := by simpa [Term.fv] using h
            subst this; simp [Ctx.dom_cons]
        exact MEqRed.refl_J hpvyExt hLCbodyOpen hfvBodyOpen
      exact ⟨MEqRed.fun_ (L ∪ Γ.dom ∪ Term.fv body) ihBound
        (fun y hy => (hbody_each y hy).some) trivial⟩
    | cons α tail =>
      cases hpv with
      | cons hpvR hLCα hfvα =>
        classical
        have hbody_each : ∀ y, y ∉ (L ∪ Γ.dom ∪ Term.fv body) →
            Nonempty (MEqRed (⟨y, α, .equ⟩ :: Γ) tail (body^[y]) (body^[y])) := by
          intro y hy
          have hyL : y ∉ L := fun h => hy (by
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; left; exact h)
          have hyΓ : y ∉ Γ.dom := fun h => hy (by
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; right; exact h)
          have hpvy : Prevalid (⟨y, α, .equ⟩ :: Γ) :=
            Prevalid.equ (extractPrevalid hpvR) hyΓ hfvα hLCα
          have hpvyExt : PrevalidExt (⟨y, α, .equ⟩ :: Γ) tail := by
            induction hpvR with
            | nil _ => exact PrevalidExt.nil hpvy
            | @cons s_ β hpvE hLCβ hfvβ ihTail =>
              refine PrevalidExt.cons ihTail hLCβ ?_
              intro z hz
              have : z ∈ Γ.dom := hfvβ hz
              simp [Ctx.dom_cons]; exact Or.inr this
          have hLCbodyOpen : Term.LC (Term.opening (.fvar y) body) := hbodyLC y hyL
          have hfvBodyOpen : Term.fv (Term.opening (.fvar y) body) ⊆
              Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
            intro z hz
            have h := _fv_opening_subset (.fvar y) body hz
            rcases Finset.mem_union.mp h with h | h
            · have : z ∈ Γ.dom := hfvBody h
              simp [Ctx.dom_cons]; exact Or.inr this
            · have : z = y := by simpa [Term.fv] using h
              subst this; simp [Ctx.dom_cons]
          exact MEqRed.refl_J hpvyExt hLCbodyOpen hfvBodyOpen
        exact ⟨MEqRed.fOp (L ∪ Γ.dom ∪ Term.fv body) ihBound
          (fun y hy => (hbody_each y hy).some) trivial⟩
  | @absBody bound body body' L hLCbound hbody ih =>
    have hfvBound : Term.fv bound ⊆ Γ.dom := by
      intro y hy; apply hfv; simp [Term.fv]; exact Or.inl hy
    have hfvBody : Term.fv body ⊆ Γ.dom := by
      intro y hy; apply hfv; simp [Term.fv]; exact Or.inr hy
    have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    obtain ⟨hboundRefl⟩ : MEqRedJ Γ [] bound bound :=
      MEqRed.refl_J hpvNil hLCbound hfvBound
    cases s with
    | nil =>
      classical
      have hbody_each : ∀ y, y ∉ (L ∪ Γ.dom ∪ Term.fv body ∪ Term.fv body') →
          Nonempty (MEqRed (⟨y, bound, .sub⟩ :: Γ) [] (body^[y]) (body'^[y])) := by
        intro y hy
        have hyL : y ∉ L := fun h => hy (by
          apply Finset.mem_union.mpr; left
          apply Finset.mem_union.mpr; left
          apply Finset.mem_union.mpr; left; exact h)
        have hyΓ : y ∉ Γ.dom := fun h => hy (by
          apply Finset.mem_union.mpr; left
          apply Finset.mem_union.mpr; left
          apply Finset.mem_union.mpr; right; exact h)
        have hpvy : Prevalid (⟨y, bound, .sub⟩ :: Γ) :=
          Prevalid.sub (extractPrevalid hpv) hyΓ hfvBound hLCbound
        have hpvyExt : PrevalidExt (⟨y, bound, .sub⟩ :: Γ) [] :=
          PrevalidExt.nil hpvy
        have hLCopen : Term.LC (Term.opening (.fvar y) body) := by
          cases hLC with
          | abs L₀ _ hb =>
            classical
            let z : String :=
              Classical.choose (Term.exists_fresh (L₀ ∪ Term.fv body ∪ {y}))
            have hz : z ∉ L₀ ∪ Term.fv body ∪ {y} :=
              Classical.choose_spec (Term.exists_fresh (L₀ ∪ Term.fv body ∪ {y}))
            have hzL₀ : z ∉ L₀ := fun h => hz (by
              apply Finset.mem_union.mpr; left
              apply Finset.mem_union.mpr; left; exact h)
            have hzFvBody : z ∉ Term.fv body := fun h => hz (by
              apply Finset.mem_union.mpr; left
              apply Finset.mem_union.mpr; right; exact h)
            have hLCz : Term.LC (Term.opening (.fvar z) body) := hb z hzL₀
            rw [Term.subst_intro hzFvBody (Term.LC.fvar y)]
            exact Term.subst_lc (Term.LC.fvar y) hLCz
        have hfvBodyOpen : Term.fv (Term.opening (.fvar y) body) ⊆
            Ctx.dom (⟨y, bound, .sub⟩ :: Γ) := by
          intro z hz
          have h := _fv_opening_subset (.fvar y) body hz
          rcases Finset.mem_union.mp h with h | h
          · have : z ∈ Γ.dom := hfvBody h
            simp [Ctx.dom_cons]; exact Or.inr this
          · have : z = y := by simpa [Term.fv] using h
            subst this; simp [Ctx.dom_cons]
        exact ih y hyL hpvyExt hLCopen hfvBodyOpen
      exact ⟨MEqRed.fun_ (L ∪ Γ.dom ∪ Term.fv body ∪ Term.fv body') hboundRefl
        (fun y hy => (hbody_each y hy).some) trivial⟩
    | cons α tail =>
      cases hpv with
      | cons hpvR hLCα hfvα =>
        classical
        have hbody_each : ∀ y, y ∉ (L ∪ Γ.dom ∪ Term.fv body ∪ Term.fv body') →
            Nonempty (MEqRed (⟨y, α, .equ⟩ :: Γ) tail (body^[y]) (body'^[y])) := by
          intro y hy
          have hyL : y ∉ L := fun h => hy (by
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; left; exact h)
          have hyΓ : y ∉ Γ.dom := fun h => hy (by
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; right; exact h)
          have hpvy : Prevalid (⟨y, α, .equ⟩ :: Γ) :=
            Prevalid.equ (extractPrevalid hpvR) hyΓ hfvα hLCα
          have hpvyExt : PrevalidExt (⟨y, α, .equ⟩ :: Γ) tail := by
            induction hpvR with
            | nil _ => exact PrevalidExt.nil hpvy
            | @cons s_ β hpvE hLCβ hfvβ ihTail =>
              refine PrevalidExt.cons ihTail hLCβ ?_
              intro z hz
              have : z ∈ Γ.dom := hfvβ hz
              simp [Ctx.dom_cons]; exact Or.inr this
          have hLCopen : Term.LC (Term.opening (.fvar y) body) := by
            cases hLC with
            | abs L₀ _ hb =>
              classical
              let z : String :=
                Classical.choose (Term.exists_fresh (L₀ ∪ Term.fv body ∪ {y}))
              have hz : z ∉ L₀ ∪ Term.fv body ∪ {y} :=
                Classical.choose_spec (Term.exists_fresh (L₀ ∪ Term.fv body ∪ {y}))
              have hzL₀ : z ∉ L₀ := fun h => hz (by
                apply Finset.mem_union.mpr; left
                apply Finset.mem_union.mpr; left; exact h)
              have hzFvBody : z ∉ Term.fv body := fun h => hz (by
                apply Finset.mem_union.mpr; left
                apply Finset.mem_union.mpr; right; exact h)
              have hLCz : Term.LC (Term.opening (.fvar z) body) := hb z hzL₀
              rw [Term.subst_intro hzFvBody (Term.LC.fvar y)]
              exact Term.subst_lc (Term.LC.fvar y) hLCz
          have hfvBodyOpen : Term.fv (Term.opening (.fvar y) body) ⊆
              Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
            intro z hz
            have h := _fv_opening_subset (.fvar y) body hz
            rcases Finset.mem_union.mp h with h | h
            · have : z ∈ Γ.dom := hfvBody h
              simp [Ctx.dom_cons]; exact Or.inr this
            · have : z = y := by simpa [Term.fv] using h
              subst this; simp [Ctx.dom_cons]
          exact ih y hyL hpvyExt hLCopen hfvBodyOpen
        exact ⟨MEqRed.fOp (L ∪ Γ.dom ∪ Term.fv body ∪ Term.fv body') hboundRefl
          (fun y hy => (hbody_each y hy).some) trivial⟩

end Pss
