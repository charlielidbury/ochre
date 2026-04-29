import Pss.Mpss.Substitution
import Pss.Mpss.Weakening
import Pss.Mpss.AvoidsPro
import Pss.Mpss.Renaming
import Pss.Mpss.Narrowing

/-! # `Pss.Mpss.Diamond` — Diamond property and reflexivity for `⟶^≡`

Pasquale & García-Pérez 2024 (CSL 2026), §3 (and appendix proofs).

This module mechanizes:

* **Proposition 18 (Reflexivity).** Every locally-closed, in-scope term
  reduces to itself in one step under both `⟶^≡` and `⟶^≤`.
* **Lemma 2 (Diamond).** `⟶^≡` has the diamond property.

## History note: the dropped "no Me-Pro on `x`" side condition

The paper's Lemma 2 has a "moreover" clause that propagates a "no
`Me-Pro` on `x`" side condition through the closing derivations. In an
earlier revision we tried to mechanize this clause as a `Prop`-valued
inductive predicate `MEqRedAvoidsPro x : MEqRed Γ s u v → Prop`.

That predicate was **unsound**: because `MEqRed` is in `Prop`, two
derivations of the same proposition are definitionally equal under
proof irrelevance regardless of constructor shape. So a `pro`-shaped
avoidance witness could be fabricated by the `var` constructor without
ever supplying the inner avoidance witness. See
`Pss/Mpss/AvoidsPro.lean`'s module docstring for the full analysis.

We dropped the side-condition clause from this revision because:
1. The predicate as formulated is unsound.
2. No downstream consumer in this codebase actually uses the side
   condition. `Lemma_1_StrongCommutativity` is itself axiomatized
   without one, and the only Lemma 2 callers (`_sameCtx`, `_bare`)
   discard it.
3. The paper's own use of the "moreover" clause is internal to its
   Lemma 1 proof (Me-Bet/Ms-App case, p.22). When a future agent
   discharges Lemma 1 here, the natural fix is a Bool-valued
   structurally-recursive function on the derivation tree (which sees
   the constructor shape, not just the proposition), NOT a re-introduction
   of an indexed Prop predicate.

The headline theorem `Lemma_2_DiamondMEqRed` accordingly states only
the diamond property: existence of a common reduct. The "moreover"
clause is documented in the comment on the theorem but is not part of
the conclusion.

## Status

* `Proposition_18_ReflexivityMEqRed`  — **PROVED**.
* `Proposition_18_ReflexivityMSubRed` — **PROVED** (via `Ms-Equ`).
* `Proposition_18_Reflexivity`       — **PROVED** (combined statement).
* `Lemma_2_DiamondMEqRed` — **THEOREM**, modulo a handful of narrow
  per-case private inline axioms (see the case grid below) and the
  context-evolution lift `Lemma_2_DiamondMEqRed_ctx_axiom`.

## Case grid for `Lemma_2_DiamondMEqRed_core` (single-context form)

| t₀ shape    | (h₁ rule × h₂ rule)        | Status  | Notes                       |
|-------------|----------------------------|---------|-----------------------------|
| `.bvar k`   | (any × any)                | V       | impossible — no MEqRed constructor produces `.bvar` |
| `.top`      | (Top × Top)                | P       | `t₃ := .top`, both `.top`    |
| `.fvar x`   | (Var × Var)                | P       | `t₃ := .fvar x`, both `.var` |
|             | (Var × Pro)                | P       | `t₃ := α'`; refl + reuse Pro |
|             | (Pro × Var)                | P       | symmetric                    |
|             | (Pro × Pro)                | T       | `Lemma_2_inline_pro_pro` (IH-aware theorem) |
| `.abs t b`  | (Fun × Fun) at empty stack | T       | `Lemma_2_inline_fun_fun` — discharged via `MEqRed.rename_sub` + `Lemma_25_NarrowingMEqRed` |
|             | (FOp × FOp) at α::s stack  | T       | `Lemma_2_inline_fOp_fOp` — discharged via local `MEqRed.rename_equ_no_fv` (Renaming's wrapper requires fv body precondition) |
| `.app u v`  | (TAp × TAp/App)            | T       | `Lemma_2_inline_tAp` (theorem) |
|             | (App × TAp)                | T       | discharged inside `Lemma_2_inline_app` |
|             | (App × App)                | T       | discharged via `_ctx_axiom` |
|             | (App × Bet)                | A       | `Lemma_2_inline_app_bet_residual_axiom` |
|             | (Bet × *)                  | A       | `Lemma_2_inline_bet_residual_axiom` |

Legend: P = proved inline (in `_core`); T = real `theorem`; A = inline
private axiom that consumes the outer-induction IH; V = vacuous.

The newly-dispatched App × App arm uses
`Lemma_2_DiamondMEqRed_ctx_axiom` to lift the operator's joining
derivation across the single-step Ct-Stk evolution `Γ; v::s ↣ Γ; v'::s`
(and analogously to `v₂::s`). This trades one residual for re-use of
an existing one — net axiom count is unchanged but the residual surface
has shrunk from {App × App, App × Bet, Bet × *} to {App × Bet, Bet × *}.

The newly-introduced `avoidsPro` Bool-valued recursion in
`Pss/Mpss/AvoidsPro.lean` (post-`16eed34`) provides the foundation
for the term-size-bounded discharge of the App × Bet, Bet × * arms,
but that discharge requires changing `_core`'s induction scheme to
term-size induction with `avoidsPro` as the bounding measure — a
non-trivial refactor scheduled separately.
-/

namespace Pss

/-! ## §1. Auxiliary scope-preservation helpers (in `Pss.Mpss.AvoidsPro`)

The scope-preservation lemmas (`fv_subset_open_fvar`, `MEqRed_fv_subset`,
`MEqRed_fv_preserve`) live in `Pss.Mpss.AvoidsPro`. The previous
`MEqRedAvoidsPro` predicate has been dropped (see the module docstring
for the full analysis). -/

/-! ## §2. Proposition 18 — Reflexivity of `⟶^≡` and `⟶^≤` -/

/-- **Proposition 18 (Reflexivity, equivalence half).** For any prevalid
extended context `Γ; s` and any locally-closed in-scope term `u`,
`Γ; s ⊢ u ⟶^≡ u`.

This is a direct re-export of `MEqRed.refl` from `Pss.Mpss.Substitution`,
exposed at this module under the paper's name.

Returns the bare Type-valued derivation; converted from `theorem` to
`noncomputable def` because `MEqRed` is `Type`-valued and the underlying
`MEqRed.refl` uses `Classical.choice`. -/
noncomputable def Proposition_18_ReflexivityMEqRed
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRed Γ s u u :=
  MEqRed.refl hpv hLC hfv

/-- **Proposition 18 (Reflexivity, subtyping half).** Same statement, for
`⟶^≤`. Follows by `Ms-Equ` from the equivalence half. -/
noncomputable def Proposition_18_ReflexivityMSubRed
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MSubRed Γ s u u :=
  MSubRed.equ hpv (Proposition_18_ReflexivityMEqRed hpv hLC hfv)

/-- **Proposition 18 (Reflexivity, combined).** Both halves. -/
noncomputable def Proposition_18_Reflexivity
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRed Γ s u u × MSubRed Γ s u u :=
  ⟨Proposition_18_ReflexivityMEqRed hpv hLC hfv,
   Proposition_18_ReflexivityMSubRed hpv hLC hfv⟩

/-! ## §3. Lemma 2 — Diamond property of `⟶^≡`

The paper's statement (verbatim, modulo notation):

  Let `Γ₀; s₀` be an extended context. Let `t₀, t₁, t₂` be terms.
  If `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₁` and `Γ₀; s₀ ⊢ t₀ ⟶^≡ t₂`, then for any
  extended contexts `Γ₁; s₁` and `Γ₂; s₂` such that `Γ₀; s₀ ↣ Γ₁; s₁`
  and `Γ₀; s₀ ↣ Γ₂; s₂`, there exists a term `t₃` such that
  `Γ₁; s₁ ⊢ t₁ ⟶^≡ t₃` and `Γ₂; s₂ ⊢ t₂ ⟶^≡ t₃`.

  [The paper additionally has a "Moreover" clause threading a
  `no-promotion-of-x` side condition through the closing derivations.
  See the module docstring above for why we dropped that clause.] -/

/-! ### §3.0 Context-evolution lifting (axiomatised)

The context evolution `↣*` is handled by a separate axiom that lifts a
same-context joining derivation across two `↣*` evolutions. We also
invoke it locally inside the App × App arm of `Lemma_2_inline_app` to
shift across a single Ct-Stk step `Γ; v::s ↣ Γ; v'::s` (in which case
the source context-stack pair is the SAME, but the target stack-head
swaps from `v` to `v'`/`v₂`). -/

/-- Lift a same-context joining derivation across two `↣*` evolutions. -/
private axiom Lemma_2_DiamondMEqRed_ctx_axiom
    {Γ₀ : Ctx} {s₀ : Stack} {t₁ t₂ : Term}
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂))
    {t₃ : Term} (h₁'₀ : MEqRed Γ₀ s₀ t₁ t₃) (h₂'₀ : MEqRed Γ₀ s₀ t₂ t₃) :
    Σ' (t₃' : Term), MEqRed Γ₁ s₁ t₁ t₃' × MEqRed Γ₂ s₂ t₂ t₃'

/-! ### §3.1 Inline residual fallbacks (IH-aware)

The hard cells of the diamond grid require recursive applications of
the diamond property on syntactic sub-derivations. We capture each
remaining case as an **inline `private axiom` whose signature receives
the IH(s) of the outer induction as parameters**. This makes the
residual obligation explicit and small: every axiom takes the structural
IH it needs, so discharging it does not require recursive descent
inside the axiom's own statement. -/

/-- Inline residual (DISCHARGED): both derivations are `Me-Pro` on the
same free variable `y`, looking up the same `equBinds y α`. The IH
closes the inner sub-derivations of `α ⟶ α₁` vs `α ⟶ α₂` directly:
applying `ihα₁` to `hα₂` produces the common reduct `t₃` such that
`α₁ ⟶ t₃` and `α₂ ⟶ t₃`, which is exactly the conclusion. -/
private noncomputable def Lemma_2_inline_pro_pro
    {Γ : Ctx} {s : Stack} {y : String} {α α₁ α₂ : Term}
    (_hpv₁ _hpv₂ : PrevalidExt Γ s) (_heq : Γ.equBinds y α)
    (_hα₁ : MEqRed Γ s α α₁) (hα₂ : MEqRed Γ s α α₂)
    (ihα₁ : ∀ {t₂' : Term}, MEqRed Γ s α t₂' →
      Σ' (t₃ : Term), MEqRed Γ s α₁ t₃ × MEqRed Γ s t₂' t₃) :
    Σ' (t₃ : Term), MEqRed Γ s α₁ t₃ × MEqRed Γ s α₂ t₃ :=
  ihα₁ hα₂

/-! #### Status of the App × Bet, Bet × {App, Bet} arms

After the App × App discharge (via `_ctx_axiom`-mediated stack-shift)
and the Fun × Fun / FOp × FOp discharges below (post this commit),
the remaining axiomatised arms are:

* App × Bet (`Lemma_2_inline_app_bet_residual_axiom`)
* Bet × {App, Bet} (`Lemma_2_inline_bet_residual_axiom`)

The β-step arms (App × Bet, Bet × {App, Bet}) all share the same
fundamental obstruction: the β-reduction `(.abs t body) v ⟶ body[v/x]`
can grow the term, so structural induction on the derivation tree does
not terminate for the closing argument. The paper threads a "moreover"
side condition (no `Me-Pro` step on the bound name) to bound the
opening, allowing term-size induction.

`avoidsPro` (in `Pss/Mpss/AvoidsPro.lean`, post-`16eed34`) provides
the Bool-valued mechanisation of that side condition, but consuming it
requires changing `_core`'s induction scheme from
`induction h₁ generalizing t₂` to a lex measure on `(Term.size t₀,
avoidsPro-count of h₁)`. That refactor is non-trivial enough to be
scheduled separately.

The Fun × Fun and FOp × FOp arms have been discharged using the
`MEqRed.rename_sub` and `MEqRed.rename_equ_no_fv` (local) renaming
helpers. The local `_no_fv` variant is needed for FOp × FOp because
the Renaming module's `MEqRed.rename_equ` requires `fv body ⊆ Γ.dom`
(via Lemma 22 weakening), which is not guaranteed for the source body
of an `MEqRed.fOp` constructor. -/

/-- App × Bet residual: the operator is an `.abs t' body'` and the RHS
β-reduces. Discharge needs term-size induction on the body bounded by
the avoidance count — see comment above.

Now that `MEqRed` is `Type`-valued, `avoidsPro` is definable (see
`Pss/Mpss/AvoidsPro.lean`), but the term-size induction itself still
needs to be set up at the `_core` level (induction scheme change). For
the moment we keep the App × Bet arm as a private axiom whose
signature receives the necessary IHs. The operator's source type
`(.abs t' body')` is forced by the source-shape match in the caller. -/
private axiom Lemma_2_inline_app_bet_residual_axiom
    {Γ : Ctx} {s : Stack} {u' v v' : Term} {t' body' body'' : Term}
    {L₂ : Finset String} {v₂' : Term}
    (hu : MEqRed Γ (v :: s) (.abs t' body') u') (hv : MEqRed Γ [] v v')
    (hLCt₂ : Term.LC t')
    (hbody₂ : ∀ y, y ∉ L₂ → MEqRed Γ s (body'^[y]) (body''^[y]))
    (hv₂ : MEqRed Γ [] v v₂')
    (ihu : ∀ {t₂' : Term}, MEqRed Γ (v :: s) (.abs t' body') t₂' →
      Σ' (t₃ : Term), MEqRed Γ (v :: s) u' t₃ × MEqRed Γ (v :: s) t₂' t₃)
    (ihv : ∀ {t₂' : Term}, MEqRed Γ [] v t₂' →
      Σ' (t₃ : Term), MEqRed Γ [] v' t₃ × MEqRed Γ [] t₂' t₃) :
    Σ' (t₃ : Term),
      MEqRed Γ s (.app u' v') t₃ × MEqRed Γ s (Term.opening v₂' body'') t₃

/-- Inline residual (DISCHARGED, except App × Bet): `Me-App` on the LHS,
any rule on the RHS.

* App × TAp: vacuous-source dispatch (operator forced to `.top`).
* App × App: discharged via `Lemma_2_DiamondMEqRed_ctx_axiom`.
  The IHs close `(u', u₂)` at stack `(v::s)` and `(v', v₂)` at stack
  `[]`; we then use the context-evolution axiom `Γ; v::s ↣ Γ; v'::s`
  (Ct-Stk on `v ⟶ v'`) and `Γ; v::s ↣ Γ; v₂::s` to lift the operator
  closure across the stack evolution. The lifted derivations rebuild
  `MEqRed.app` at stack `s`.
* App × Bet: still axiomatised (`Lemma_2_inline_app_bet_residual_axiom`).
-/
private noncomputable def Lemma_2_inline_app
    {Γ : Ctx} {s : Stack} {u u' v v' : Term} {t₂ : Term}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v')
    (h₂ : MEqRed Γ s (.app u v) t₂)
    (ihu : ∀ {t₂' : Term}, MEqRed Γ (v :: s) u t₂' →
      Σ' (t₃ : Term), MEqRed Γ (v :: s) u' t₃ × MEqRed Γ (v :: s) t₂' t₃)
    (ihv : ∀ {t₂' : Term}, MEqRed Γ [] v t₂' →
      Σ' (t₃ : Term), MEqRed Γ [] v' t₃ × MEqRed Γ [] t₂' t₃) :
    Σ' (t₃ : Term), MEqRed Γ s (.app u' v') t₃ × MEqRed Γ s t₂ t₃ := by
  cases h₂ with
  | @tAp _ _ _ hpv hLCv hfvv =>
    -- App × TAp: t₀ = .app .top v. Cases on `hu : MEqRed Γ (v::s) .top u'`:
    -- only `.top` produces `.top` as source on this fvar-free shape, so
    -- `u' = .top` and the joined reduct is `.top` itself.
    cases hu with
    | top hpvU =>
      -- Pop v-head from hpvU : PrevalidExt Γ (v::s).
      have hpvS : PrevalidExt Γ s := by
        cases hpvU with
        | cons hpv' _ _ => exact hpv'
      have hLCv' : Term.LC v' := MEqRed.lc_right hv
      have hfvv' : Term.fv v' ⊆ Γ.dom := MEqRed_fv_preserve hv hfvv
      exact ⟨.top, MEqRed.tAp hpvS hLCv' hfvv', MEqRed.top hpvS⟩
  | @app _ _ _ u₂ _ v₂ hu₂ hv₂ =>
    -- App × App via _ctx_axiom: close (u', u₂) at (v::s) and (v', v₂) at [],
    -- then lift the operator closure across Γ; v::s ↣ Γ; v'::s and
    -- Γ; v::s ↣ Γ; v₂::s (single Ct-Stk steps on v ⟶ v' / v ⟶ v₂).
    obtain ⟨w, hu'_w, hu₂_w⟩ := ihu hu₂
    obtain ⟨v₃, hv'_v₃, hv₂_v₃⟩ := ihv hv₂
    have hCt₁ : ExtCtxRedStar (Γ, v :: s) (Γ, v' :: s) :=
      ExtCtxRed.to_star (.stk .refl hv)
    have hCt₂ : ExtCtxRedStar (Γ, v :: s) (Γ, v₂ :: s) :=
      ExtCtxRed.to_star (.stk .refl hv₂)
    obtain ⟨w', hu'_w', hu₂_w'⟩ :=
      Lemma_2_DiamondMEqRed_ctx_axiom hCt₁ hCt₂ hu'_w hu₂_w
    exact ⟨.app w' v₃, MEqRed.app hu'_w' hv'_v₃, MEqRed.app hu₂_w' hv₂_v₃⟩
  | @bet _ _ t' _ _ _ body' L₂ hLCt₂ hbody₂ hv₂ =>
    -- App × Bet: still axiomatised. The source-shape match equates u with
    -- the .abs t' body' shape; the axiom takes the operator-MEqRed at that
    -- forced shape directly.
    exact Lemma_2_inline_app_bet_residual_axiom hu hv hLCt₂ hbody₂ hv₂ ihu ihv

/-- Bet × non-TAp residual: covers Bet × App and Bet × Bet.
Same closure obstruction as App × non-TAp. -/
private axiom Lemma_2_inline_bet_residual_axiom
    {Γ : Ctx} {s : Stack} {t v v' body body' : Term} {L : Finset String}
    {t₂ : Term}
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hv : MEqRed Γ [] v v')
    (h₂ : MEqRed Γ s (.app (.abs t body) v) t₂)
    (ihbody : ∀ y (_hy : y ∉ L) {t₂' : Term}, MEqRed Γ s (body^[y]) t₂' →
      Σ' (t₃ : Term), MEqRed Γ s (body'^[y]) t₃ × MEqRed Γ s t₂' t₃)
    (ihv : ∀ {t₂' : Term}, MEqRed Γ [] v t₂' →
      Σ' (t₃ : Term), MEqRed Γ [] v' t₃ × MEqRed Γ [] t₂' t₃) :
    Σ' (t₃ : Term), MEqRed Γ s (Term.opening v' body') t₃ × MEqRed Γ s t₂ t₃

/-- Inline residual (vacuous-Bet × TAp + delegate Bet × {App, Bet}):
the Bet × TAp arm cannot occur (sources `.app (.abs t body) v` and
`.app .top u` differ in their `.app`-head), so case-analysis on `h₂`
exposes only the dispatched arms. -/
private noncomputable def Lemma_2_inline_bet
    {Γ : Ctx} {s : Stack} {t v v' body body' : Term} {L : Finset String}
    {t₂ : Term}
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hv : MEqRed Γ [] v v')
    (h₂ : MEqRed Γ s (.app (.abs t body) v) t₂)
    (ihbody : ∀ y (_hy : y ∉ L) {t₂' : Term}, MEqRed Γ s (body^[y]) t₂' →
      Σ' (t₃ : Term), MEqRed Γ s (body'^[y]) t₃ × MEqRed Γ s t₂' t₃)
    (ihv : ∀ {t₂' : Term}, MEqRed Γ [] v t₂' →
      Σ' (t₃ : Term), MEqRed Γ [] v' t₃ × MEqRed Γ [] t₂' t₃) :
    Σ' (t₃ : Term), MEqRed Γ s (Term.opening v' body') t₃ × MEqRed Γ s t₂ t₃ :=
  Lemma_2_inline_bet_residual_axiom hLCt hbody hv h₂ ihbody ihv

/-- Inline residual (DISCHARGED): `Me-TAp` on the LHS, anything (TAp/App
on `.app .top u` shape) on the RHS. The `bet` constructor is vacuous
because `Top` is not an `.abs`. -/
private noncomputable def Lemma_2_inline_tAp
    {Γ : Ctx} {s : Stack} {u : Term} {t₂ : Term}
    (hpv : PrevalidExt Γ s) (_hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom)
    (h₂ : MEqRed Γ s (.app .top u) t₂) :
    Σ' (t₃ : Term), MEqRed Γ s .top t₃ × MEqRed Γ s t₂ t₃ := by
  cases h₂ with
  | @app _ _ _ uDst _ vDst hu hv =>
    have hLCvDst : Term.LC vDst := MEqRed.lc_right hv
    have hfvvDst : Term.fv vDst ⊆ Γ.dom := MEqRed_fv_preserve hv hfvu
    cases hu with
    | top hpvU =>
      refine ⟨.top, MEqRed.top hpv, ?_⟩
      exact MEqRed.tAp hpv hLCvDst hfvvDst
  | tAp hpv₂ hLCu' hfvu' =>
    exact ⟨.top, MEqRed.top hpv, MEqRed.top hpv⟩

/-! #### Helpers for the cofinite body discharges -/

/-- Closing a term over `x` removes `x` from its free-variable set. -/
private theorem Term.fv_close_notMem (x : String) :
    ∀ (k : Nat) (e : Term), x ∉ Term.fv (Term.close_ k x e) := by
  intro k e
  induction e generalizing k with
  | bvar i => simp [Term.close_, Term.fv]
  | fvar y =>
    by_cases h : y = x
    · simp [Term.close_, h, Term.fv]
    · simp [Term.close_, h, Term.fv]; exact Ne.symm h
  | top => simp [Term.close_, Term.fv]
  | abs t b iht ihb =>
    simp [Term.close_, Term.fv, Finset.mem_union]
    exact ⟨iht k, ihb (k+1)⟩
  | app t u iht ihu =>
    simp [Term.close_, Term.fv, Finset.mem_union]
    exact ⟨iht k, ihu k⟩

/-- Local re-proof of the `Prevalid` extractor for `MEqRed`. -/
private theorem _extractPrevalidOfMEqRed_loc {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x α α' hpv _ _ _ => exact extractPrevalid hpv
  | @bet Γ s t v v' body body' L _ _ _ _ ihv => exact ihv
  | @top Γ s hpv => exact extractPrevalid hpv
  | @app Γ s u u' v v' _ _ _ ihv => exact ihv
  | @var Γ s x hpv => exact extractPrevalid hpv
  | @fun_ Γ t t' body body' L _ _ iht _ => exact iht
  | @tAp Γ s u hpv _ _ => exact extractPrevalid hpv
  | @fOp Γ s t t' α body body' L _ _ iht _ => exact iht

/-- Inline residual (DISCHARGED): both derivations are `Me-Fun`. Cofinite
body-IH at a fresh name, plus annotation-IH.

Strategy:
1. Pick a fresh `y` against `L₁ ∪ L₂ ∪ Γ.dom ∪ fv body₁ ∪ fv body₂`.
2. Apply `iht ht₂` to get joining annotation `t₃ann`.
3. Apply `ihbody y _ (hbody₂ y _)` to get a joining body `b` at `y`.
4. Define `body₃ := Term.close_ 0 y b`. Then `body₃^[y] = b` (by
   `open_close` since `b` is LC).
5. For arbitrary fresh `z`, use `MEqRed.rename_sub` to lift the body
   derivations from `y` to `z`, then `Lemma_25_NarrowingMEqRed` to swap
   the head annotation `t → t₁'` (resp. `t → t₂'`). -/
private noncomputable def Lemma_2_inline_fun_fun
    {Γ : Ctx} {t t₁' body body₁ body₂ : Term} {L₁ L₂ : Finset String}
    {t₂' : Term}
    (ht₁ : MEqRed Γ [] t t₁') (ht₂ : MEqRed Γ [] t t₂')
    (hbody₁ : ∀ y, y ∉ L₁ →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₁^[y]))
    (hbody₂ : ∀ y, y ∉ L₂ →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₂^[y]))
    (iht : ∀ {t₂'' : Term}, MEqRed Γ [] t t₂'' →
      Σ' (t₃ : Term), MEqRed Γ [] t₁' t₃ × MEqRed Γ [] t₂'' t₃)
    (ihbody : ∀ y (_hy : y ∉ L₁) {body₂' : Term},
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) body₂' →
      Σ' (t₃ : Term),
        MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body₁^[y]) t₃ ×
        MEqRed (⟨y, t, .sub⟩ :: Γ) [] body₂' t₃) :
    Σ' (t₃ : Term),
      MEqRed Γ [] (.abs t₁' body₁) t₃ × MEqRed Γ [] (.abs t₂' body₂) t₃ := by
  classical
  obtain ⟨t₃ann, ht₁'_t₃ann, ht₂'_t₃ann⟩ := iht ht₂
  -- Helper to introduce union-membership avoidance: w ∈ A ∪ B → w ∈ A ∨ w ∈ B.
  let Lall : Finset String :=
    L₁ ∪ L₂ ∪ Γ.dom ∪ Term.fv body ∪ Term.fv body₁ ∪ Term.fv body₂
  let y : String := Classical.choose (Term.exists_fresh Lall)
  have hyfresh : y ∉ Lall := Classical.choose_spec (Term.exists_fresh Lall)
  have hy_notin_L₁ : y ∉ L₁ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl h)
  have hy_notin_L₂ : y ∉ L₂ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_Γ : y ∉ Γ.dom := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_body₁ : y ∉ Term.fv body₁ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_body₂ : y ∉ Term.fv body₂ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inr h)
  have hb₁_y : MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₁^[y]) :=
    hbody₁ y hy_notin_L₁
  have hb₂_y : MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₂^[y]) :=
    hbody₂ y hy_notin_L₂
  obtain ⟨b, hb₁_to_b, hb₂_to_b⟩ := ihbody y hy_notin_L₁ hb₂_y
  let body₃ := Term.close_ 0 y b
  have hLCb : Term.LC b := MEqRed.lc_right hb₁_to_b
  have hb_eq : body₃^[y] = b := by
    show Term.open_ 0 (.fvar y) (Term.close_ 0 y b) = b
    exact Term.open_close hLCb 0 y
  have hy_notin_body₃ : y ∉ Term.fv body₃ :=
    Term.fv_close_notMem y 0 b
  have hpv_y : Prevalid (⟨y, t, .sub⟩ :: Γ) :=
    _extractPrevalidOfMEqRed_loc hb₁_y
  have hpvΓ : Prevalid Γ := hpv_y.tail
  have hLCt : Term.LC t := by
    cases hpv_y with
    | sub _ _ _ hLCt => exact hLCt
  have hfvt : Term.fv t ⊆ Γ.dom := by
    cases hpv_y with
    | sub _ _ hfvt _ => exact hfvt
  have hLCt₁' : Term.LC t₁' := MEqRed.lc_right ht₁
  have hLCt₂' : Term.LC t₂' := MEqRed.lc_right ht₂
  have hfvt₁' : Term.fv t₁' ⊆ Γ.dom := MEqRed_fv_preserve ht₁ hfvt
  have hfvt₂' : Term.fv t₂' ⊆ Γ.dom := MEqRed_fv_preserve ht₂ hfvt
  refine ⟨.abs t₃ann body₃, ?_, ?_⟩
  · refine MEqRed.fun_ (Γ.dom ∪ Term.fv body₁ ∪ Term.fv body₃ ∪ {y})
      ht₁'_t₃ann ?_
    intro z hzfresh
    have hz_notin_Γ : z ∉ Γ.dom := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl h)
    have hz_notin_body₁ : z ∉ Term.fv body₁ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inr h)
    have hz_notin_body₃ : z ∉ Term.fv body₃ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
    have h_at_y : MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body₁^[y]) (body₃^[y]) := by
      rw [hb_eq]; exact hb₁_to_b
    have h_at_z : MEqRed (⟨z, t, .sub⟩ :: Γ) [] (body₁^[z]) (body₃^[z]) :=
      MEqRed.rename_sub hpvΓ hLCt hfvt hy_notin_Γ hz_notin_Γ
        hy_notin_body₁ hy_notin_body₃ (by intro α hα; cases hα) h_at_y
    -- Narrow head annotation t → t₁' (Lemma 25 via Γ₂ := []).
    exact Lemma_25_NarrowingMEqRed (Γ₂ := []) (Γ₁ := Γ) (x := z)
      (t := t₁') (t' := t) h_at_z hLCt₁' hfvt₁'
  · refine MEqRed.fun_ (Γ.dom ∪ Term.fv body₂ ∪ Term.fv body₃ ∪ {y})
      ht₂'_t₃ann ?_
    intro z hzfresh
    have hz_notin_Γ : z ∉ Γ.dom := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl h)
    have hz_notin_body₂ : z ∉ Term.fv body₂ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inr h)
    have hz_notin_body₃ : z ∉ Term.fv body₃ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
    have h_at_y : MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body₂^[y]) (body₃^[y]) := by
      rw [hb_eq]; exact hb₂_to_b
    have h_at_z : MEqRed (⟨z, t, .sub⟩ :: Γ) [] (body₂^[z]) (body₃^[z]) :=
      MEqRed.rename_sub hpvΓ hLCt hfvt hy_notin_Γ hz_notin_Γ
        hy_notin_body₂ hy_notin_body₃ (by intro α hα; cases hα) h_at_y
    exact Lemma_25_NarrowingMEqRed (Γ₂ := []) (Γ₁ := Γ) (x := z)
      (t := t₂') (t' := t) h_at_z hLCt₂' hfvt₂'

/-! #### `lookupEqu` lift through a fresh middle insertion -/

/-- A successful `lookupEqu` for `x` implies `x ∈ Γ.dom`. -/
private lemma Ctx.lookupEqu_some_mem_dom_loc {Γ : Ctx} {x : String} {α : Term}
    (h : Γ.lookupEqu x = some α) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.lookupEqu] at h
  | cons e rest ih =>
    rw [Ctx.lookupEqu_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

/-- Lift `Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁)` to
`Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁)` by inserting a fresh
`⟨z, α, .equ⟩` entry between the head and the tail. -/
private theorem Prevalid.insert_fresh_equ_mid
    {Γ₁ Γ₂ : Ctx} {y z : String} {α : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁)) :
    Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
  classical
  have hpv_inner : Prevalid (⟨y, α, .equ⟩ :: Γ₁) := Prevalid.outer hpv
  cases hpv_inner with
  | equ hpvΓ₁ hy_notin_Γ₁ hfvα hLCα =>
    have hpv_z : Prevalid (⟨z, α, .equ⟩ :: Γ₁) :=
      Prevalid.equ hpvΓ₁ hz_notin_Γ₁ hfvα hLCα
    have hyz_zα : y ∉ Ctx.dom (⟨z, α, .equ⟩ :: Γ₁) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
      · exact hyz hyz'
      · exact hy_notin_Γ₁ hyΓ
    have hfvα_z : Term.fv α ⊆ Ctx.dom (⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw; rw [Ctx.dom_cons]
      exact Finset.mem_insert_of_mem (hfvα hw)
    have hpv_yz : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
      Prevalid.equ hpv_z hyz_zα hfvα_z hLCα
    induction Γ₂ with
    | nil => simpa using hpv_yz
    | cons e rest ih =>
      have hpv'' : Prevalid (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) := by
        simpa using hpv
      have hpv_rest : Prevalid (rest ++ ⟨y, α, .equ⟩ :: Γ₁) := hpv''.tail
      have hz_notin_rest : z ∉ Ctx.dom rest := by
        intro hmem; apply hz_notin_Γ₂
        rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem hmem
      have ih' := ih hz_notin_rest hpv_rest
      have he_notin : e.name ∉ Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: Γ₁) := by
        cases hpv'' with
        | sub _ hen _ _ => exact hen
        | equ _ hen _ _ => exact hen
      have he_notin' : e.name ∉
          Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
        intro hmem
        rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons] at hmem
        rw [Ctx.dom_append, Ctx.dom_cons] at he_notin
        rcases Finset.mem_union.mp hmem with hr | htail
        · apply he_notin; exact Finset.mem_union.mpr (Or.inl hr)
        · rcases Finset.mem_insert.mp htail with hey | hrest_x
          · apply he_notin
            exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
          · rcases Finset.mem_insert.mp hrest_x with hez | hΓ
            · apply hz_notin_Γ₂
              rw [show z = e.name from hez.symm]
              exact Finset.mem_insert_self _ _
            · apply he_notin
              exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))
      cases hpv'' with
      | @sub _ name u' _ _ hfve hlce =>
        have hfve' : Term.fv u' ⊆
            Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
          intro w hw
          have hw' := hfve hw
          rw [Ctx.dom_append, Ctx.dom_cons] at hw'
          rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
          rcases Finset.mem_union.mp hw' with hr | htail
          · exact Finset.mem_union.mpr (Or.inl hr)
          · rcases Finset.mem_insert.mp htail with hey | hΓ
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
        exact Prevalid.sub ih' he_notin' hfve' hlce
      | @equ _ name αe _ _ hfve hlce =>
        have hfve' : Term.fv αe ⊆
            Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
          intro w hw
          have hw' := hfve hw
          rw [Ctx.dom_append, Ctx.dom_cons] at hw'
          rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
          rcases Finset.mem_union.mp hw' with hr | htail
          · exact Finset.mem_union.mpr (Or.inl hr)
          · rcases Finset.mem_insert.mp htail with hey | hΓ
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
        exact Prevalid.equ ih' he_notin' hfve' hlce

/-- `PrevalidExt` analog of `Prevalid.insert_fresh_equ_mid`. -/
private theorem PrevalidExt.insert_fresh_equ_mid
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st) :
    PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) st := by
  induction st with
  | nil =>
    cases hpv with
    | nil hpvL =>
      exact PrevalidExt.nil
        (Prevalid.insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpvL)
  | cons αs srest ihst =>
    cases hpv with
    | cons hpvr hLCαs hfvαs =>
      have ihst' := ihst hpvr
      have hfvαs' : Term.fv αs ⊆
          Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
        intro w hw
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfvαs hw
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inl hwy)))
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inr hwΓ₁)))))
      exact PrevalidExt.cons ihst' hLCαs hfvαs'

/-- Inserting a `⟨z, α, .equ⟩` entry between `Γ₂` and `Γ₁` preserves
`lookupEqu yi` when `yi ≠ z`. Proved by structural induction on `Γ₂`. -/
private theorem Ctx.lookupEqu_lift_middle
    {Γ₁ Γ₂ : Ctx} {yi z : String} {α β' : Term}
    (hyiz : yi ≠ z)
    (h : (Γ₂ ++ Γ₁).lookupEqu yi = some β') :
    (Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).lookupEqu yi = some β' := by
  induction Γ₂ with
  | nil =>
    simpa [Ctx.lookupEqu_cons, Ne.symm hyiz] using h
  | cons e rest ih =>
    rw [List.cons_append, Ctx.lookupEqu_cons] at h ⊢
    by_cases hex : e.name = yi
    · simp [hex] at h ⊢
      cases hkind : e.kind with
      | sub => simp [hkind] at h
      | equ => simp [hkind] at h ⊢; exact h
    · simp [hex] at h ⊢
      exact ih h

/-! #### Local renaming helper for `.equ`-head binding without `fv body` precondition

`MEqRed.rename_equ` in `Pss.Mpss.Renaming` requires `fv body ⊆ Γ.dom`
because it goes through Lemma 22 (weakening) to lift the derivation
into a doubled context `⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ` before
applying the `subst_yz_equ_head` primitive.

In `Lemma_2_inline_fOp_fOp` below, the body `body` of the source
abstraction need not satisfy `fv body ⊆ Γ.dom` — the `MEqRed.fOp`
constructor doesn't enforce it. We therefore re-prove the renaming
inline here, by direct induction on the derivation, mirroring
`subst_yz_equ_head` from `Pss.Mpss.Renaming`. The proof structure is
identical except it operates on the non-doubled context
`Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁` and produces a derivation in the renamed
context `Γ₂.subst y (.fvar z) ++ ⟨z, α, .equ⟩ :: Γ₁` directly. -/

/-- Renaming `MEqRed` under an `.equ`-head binding, working directly on the
non-doubled context (no `fv body ⊆ Γ.dom` precondition required).
Mirrors the structure of `subst_yz_equ_head` from `Pss.Mpss.Renaming`. -/
private noncomputable def MEqRed.rename_equ_loc
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u') :
    MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  -- Helper to build the renamed prevalidity at any prefix Γ₂'.
  -- We re-derive z-freshness for sub-prefixes during induction.
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv_doubled :=
      PrevalidExt.insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    by_cases hyiy : yi = y
    · have heq_y : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds y β := hyiy ▸ heq
      have hβα : β = α := equBinds_at_equ_head_unique hpvL heq_y
      have ihβ_app := ihβ (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      rw [hβα] at ihβ_app
      have hα_subst : Term.subst y (.fvar z) α = α := Term.subst_fresh hy_notin_α
      rw [hα_subst] at ihβ_app
      have hz_eqbinds :
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds z α := by
        have hz_notin_subst_Γ₂ : z ∉ (Ctx.subst y (.fvar z) Γ₂).dom := by
          rw [Ctx.dom_subst]; exact hz_notin_Γ₂
        have hlk_tail : Ctx.lookupEqu (⟨z, α, .equ⟩ :: Γ₁) z = some α := by
          simp [Ctx.lookupEqu, Ctx.lookupEqu_cons]
        show Ctx.lookupEqu (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) z = some α
        exact Ctx.lookupEqu_append_right (Ctx.subst y (.fvar z) Γ₂) _ z α
          hz_notin_subst_Γ₂ hlk_tail
      have hfvar_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hfvar_eq]
      -- ihβ_app already constructed via the by_cases above; we need to thread hz_notin_Γ₂.
      -- Re-apply with the correct argument:
      exact MEqRed.pro hpv' hz_eqbinds ihβ_app
    · rw [Term.subst_fvar_ne hyiy]
      -- Build heq' by composing equBinds_split_equ (gives lookup in
      -- Ctx.subst y (.fvar z) Γ₂ ++ Γ₁) with Ctx.lookupEqu_lift_middle
      -- (lifts past the freshly-inserted ⟨z, α, .equ⟩ head).
      have heq_un : (Ctx.subst y (.fvar z) Γ₂ ++ Γ₁).equBinds yi
          (Term.subst y (.fvar z) β) :=
        equBinds_split_equ (s := .fvar z) hyiy hpvL heq
      -- yi ≠ z because yi ∈ original.dom and z ∉ original.dom.
      have hyi_in_orig : yi ∈ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom :=
        Ctx.lookupEqu_some_mem_dom_loc heq
      have hz_notin_orig : z ∉ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_union.mp hmem with hΓ₂' | htail
        · exact hz_notin_Γ₂ hΓ₂'
        · rcases Finset.mem_insert.mp htail with hzy | hzΓ₁
          · exact hyz hzy.symm
          · exact hz_notin_Γ₁ hzΓ₁
      have hyiz : yi ≠ z := by
        intro hh; subst hh; exact hz_notin_orig hyi_in_orig
      have heq' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds yi
          (Term.subst y (.fvar z) β) :=
        Ctx.lookupEqu_lift_middle hyiz heq_un
      exact MEqRed.pro hpv' heq' (ihβ (Γ₂ := Γ₂) hz_notin_Γ₂ rfl)
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
      have ih_body := ihbody yfresh hyfL (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      exact ih_body
    · have ihv' := ihv (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    have hpv_doubled :=
      PrevalidExt.insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
    have ihv' := ihv (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    have hpv_doubled :=
      PrevalidExt.insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    by_cases hyiy : yi = y
    · have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
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
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_
    · have iht' := iht (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ₂
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂)
        hz_notin_Γ₂' (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv_doubled :=
      PrevalidExt.insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · apply Finset.mem_union.mpr
            right; exact Finset.mem_insert_of_mem hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        apply Finset.mem_union.mpr
        right; exact Finset.mem_insert_self _ _
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
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_
    · have iht' := iht (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ₂
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂)
        hz_notin_Γ₂' (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-- Wrapper: rename the head `.equ`-binding's name `y → z` for an `MEqRed`
in `⟨y, α, .equ⟩ :: Γ`. Uses `MEqRed.rename_equ_loc` with `Γ₂ := []`. -/
private noncomputable def MEqRed.rename_equ_no_fv
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hyz : y ≠ z)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MEqRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  have hz_notin_empty : z ∉ Ctx.dom ([] : Ctx) := by simp [Ctx.dom]
  have h_in : MEqRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: Γ) s
      (body^[y]) (body'^[y]) := by simpa using h
  have h_subst :=
    MEqRed.rename_equ_loc (Γ₂ := []) (Γ₁ := Γ) hyz hz_notin_Γ hz_notin_empty
      hy_notin_α h_in
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

/-- Inline residual (DISCHARGED): both derivations are `Me-FOp`. Cofinite
body-IH at a fresh name with `.equ` binding, plus annotation-IH.

Same structure as `Lemma_2_inline_fun_fun`, but the body context uses
`⟨y, α, .equ⟩` (where `α` comes from the stack head and is unchanged).
The annotation `t` reduces to `t₁'`/`t₂'` but the body context binding
is `α`, not `t`, so no narrowing of the head annotation is needed.

Uses `MEqRed.rename_equ_no_fv` (the local fv-precondition-free renaming
helper above) instead of `MEqRed.rename_equ` from `Pss.Mpss.Renaming`,
because the source `body` of an `MEqRed.fOp` constructor isn't required
to satisfy `fv body ⊆ Γ.dom`. -/
private noncomputable def Lemma_2_inline_fOp_fOp
    {Γ : Ctx} {s : Stack} {α t t₁' body body₁ body₂ : Term}
    {L₁ L₂ : Finset String} {t₂' : Term}
    (ht₁ : MEqRed Γ [] t t₁') (ht₂ : MEqRed Γ [] t t₂')
    (hbody₁ : ∀ y, y ∉ L₁ →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₁^[y]))
    (hbody₂ : ∀ y, y ∉ L₂ →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₂^[y]))
    (iht : ∀ {t₂'' : Term}, MEqRed Γ [] t t₂'' →
      Σ' (t₃ : Term), MEqRed Γ [] t₁' t₃ × MEqRed Γ [] t₂'' t₃)
    (ihbody : ∀ y (_hy : y ∉ L₁) {body₂' : Term},
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) body₂' →
      Σ' (t₃ : Term),
        MEqRed (⟨y, α, .equ⟩ :: Γ) s (body₁^[y]) t₃ ×
        MEqRed (⟨y, α, .equ⟩ :: Γ) s body₂' t₃) :
    Σ' (t₃ : Term),
      MEqRed Γ (α :: s) (.abs t₁' body₁) t₃ ×
      MEqRed Γ (α :: s) (.abs t₂' body₂) t₃ := by
  classical
  obtain ⟨t₃ann, ht₁'_t₃ann, ht₂'_t₃ann⟩ := iht ht₂
  -- Build a stack-fv union to make freshness w.r.t. stack contents possible.
  let stkFv : Finset String := s.foldr (fun α acc => Term.fv α ∪ acc) ∅
  let Lall : Finset String :=
    L₁ ∪ L₂ ∪ Γ.dom ∪ Term.fv α ∪ Term.fv body₁ ∪ Term.fv body₂ ∪ stkFv
  let y : String := Classical.choose (Term.exists_fresh Lall)
  have hyfresh : y ∉ Lall := Classical.choose_spec (Term.exists_fresh Lall)
  -- Decompose Lall.
  have hy_notin_L₁ : y ∉ L₁ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl h)
  have hy_notin_L₂ : y ∉ L₂ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_Γ : y ∉ Γ.dom := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_α : y ∉ Term.fv α := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_body₁ : y ∉ Term.fv body₁ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_body₂ : y ∉ Term.fv body₂ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_stkFv : y ∉ stkFv := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inr h)
  -- Helper: membership in stack implies fv ⊆ stkFv.
  have hfv_in_stkFv : ∀ {ss : Stack} (β : Term), β ∈ ss → Term.fv β ⊆
      ss.foldr (fun α acc => Term.fv α ∪ acc) ∅ := by
    intro ss β hβ w hw
    induction ss with
    | nil => exact (List.not_mem_nil _ hβ).elim
    | cons γ rest ih =>
      simp only [List.foldr_cons, Finset.mem_union]
      cases hβ with
      | head => exact Or.inl hw
      | tail _ hβ' => exact Or.inr (ih hβ')
  have hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β := by
    intro β hβ hyβ
    exact hy_notin_stkFv (hfv_in_stkFv β hβ hyβ)
  have hb₁_y : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₁^[y]) :=
    hbody₁ y hy_notin_L₁
  have hb₂_y : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₂^[y]) :=
    hbody₂ y hy_notin_L₂
  obtain ⟨b, hb₁_to_b, hb₂_to_b⟩ := ihbody y hy_notin_L₁ hb₂_y
  let body₃ := Term.close_ 0 y b
  have hLCb : Term.LC b := MEqRed.lc_right hb₁_to_b
  have hb_eq : body₃^[y] = b := by
    show Term.open_ 0 (.fvar y) (Term.close_ 0 y b) = b
    exact Term.open_close hLCb 0 y
  have hy_notin_body₃ : y ∉ Term.fv body₃ :=
    Term.fv_close_notMem y 0 b
  refine ⟨.abs t₃ann body₃, ?_, ?_⟩
  · refine MEqRed.fOp (Γ.dom ∪ Term.fv body₁ ∪ Term.fv body₃ ∪ Term.fv α ∪ {y})
      ht₁'_t₃ann ?_
    intro z hzfresh
    have hz_notin_Γ : z ∉ Γ.dom := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl h)
    have hz_notin_body₁ : z ∉ Term.fv body₁ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
    have hz_notin_body₃ : z ∉ Term.fv body₃ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inr h)
    have hyz : y ≠ z := by
      intro hyz; apply hzfresh
      apply Finset.mem_union.mpr; right
      simp [Finset.mem_singleton]; exact hyz.symm
    have h_at_y : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body₁^[y]) (body₃^[y]) := by
      rw [hb_eq]; exact hb₁_to_b
    exact MEqRed.rename_equ_no_fv hyz hy_notin_Γ hz_notin_Γ hy_notin_α
      hy_notin_body₁ hy_notin_body₃ hy_notin_stack h_at_y
  · refine MEqRed.fOp (Γ.dom ∪ Term.fv body₂ ∪ Term.fv body₃ ∪ Term.fv α ∪ {y})
      ht₂'_t₃ann ?_
    intro z hzfresh
    have hz_notin_Γ : z ∉ Γ.dom := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl h)
    have hz_notin_body₂ : z ∉ Term.fv body₂ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
    have hz_notin_body₃ : z ∉ Term.fv body₃ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inr h)
    have hyz : y ≠ z := by
      intro hyz; apply hzfresh
      apply Finset.mem_union.mpr; right
      simp [Finset.mem_singleton]; exact hyz.symm
    have h_at_y : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body₂^[y]) (body₃^[y]) := by
      rw [hb_eq]; exact hb₂_to_b
    exact MEqRed.rename_equ_no_fv hyz hy_notin_Γ hz_notin_Γ hy_notin_α
      hy_notin_body₂ hy_notin_body₃ hy_notin_stack h_at_y

/-! ### §3.2 Same-context core lemma -/

/-- **Same-context Lemma 2 (core).** Diamond property of `MEqRed` at a
single extended context. Proved by induction on `h₁`, with the `t₂`
index generalized so each constructor case has access to the structural
IH of its own sub-derivations against an arbitrary `t₂`.

Returns a `Σ'` (Type-valued sigma) since `MEqRed` is `Type`-valued and
`∃` requires a `Prop`-valued body. -/
noncomputable def Lemma_2_DiamondMEqRed_core
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRed Γ s t₀ t₂) :
    Σ' (t₃ : Term), MEqRed Γ s t₁ t₃ × MEqRed Γ s t₂ t₃ := by
  induction h₁ generalizing t₂ with
  | @pro Γ s yvr aLkup α' hpv₁ heq₁ hα₁ ihα₁ =>
    cases h₂ with
    | @pro _ _ _ aLkupB _ hpv₂ heq₂ hα₂ =>
      have hα_eq : aLkup = aLkupB := by
        have h1 : Ctx.lookupEqu Γ yvr = some aLkup := heq₁
        have h2 : Ctx.lookupEqu Γ yvr = some aLkupB := heq₂
        rw [h1] at h2
        exact Option.some.inj h2
      subst hα_eq
      exact Lemma_2_inline_pro_pro hpv₁ hpv₂ heq₁ hα₁ hα₂ ihα₁
    | var hpv₂ =>
      have hLCα' : Term.LC α' := MEqRed.lc_right hα₁
      have hfvaLkup : Term.fv aLkup ⊆ Ctx.dom Γ :=
        Prevalid.fv_lookupEqu (extractPrevalid hpv₁) heq₁
      have hfvα' : Term.fv α' ⊆ Ctx.dom Γ :=
        MEqRed_fv_preserve hα₁ hfvaLkup
      exact ⟨α', MEqRed.refl hpv₁ hLCα' hfvα', MEqRed.pro hpv₂ heq₁ hα₁⟩
  | @bet Γ s tBound vSrc vDst body bodyDst L hLCt hbody hv ihbody ihv =>
    exact Lemma_2_inline_bet hLCt hbody hv h₂ ihbody ihv
  | top hpv₁ =>
    cases h₂ with
    | top hpv₂ =>
      exact ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂⟩
  | @app Γ s u u' v v' hu hv ihu ihv =>
    exact Lemma_2_inline_app hu hv h₂ ihu ihv
  | @var Γ s yvr hpv₁ =>
    cases h₂ with
    | @pro _ _ _ aLkup _ hpv₂ heq₂ hα₂ =>
      have hLCt₂ : Term.LC t₂ := MEqRed.lc_right hα₂
      have hfvaLkup : Term.fv aLkup ⊆ Ctx.dom Γ :=
        Prevalid.fv_lookupEqu (extractPrevalid hpv₂) heq₂
      have hfvt₂ : Term.fv t₂ ⊆ Ctx.dom Γ :=
        MEqRed_fv_preserve hα₂ hfvaLkup
      exact ⟨t₂, MEqRed.pro hpv₁ heq₂ hα₂, MEqRed.refl hpv₂ hLCt₂ hfvt₂⟩
    | var hpv₂ =>
      exact ⟨.fvar yvr, MEqRed.var hpv₁, MEqRed.var hpv₂⟩
  | @fun_ Γ tBound tBoundDst body body₁ L₁ ht₁ hbody₁ iht ihbody =>
    cases h₂ with
    | @fun_ _ _ tBoundDst₂ _ body₂ L₂ ht₂ hbody₂ =>
      exact Lemma_2_inline_fun_fun ht₁ ht₂ hbody₁ hbody₂ iht ihbody
  | tAp hpv₁ hLCu hfvu =>
    exact Lemma_2_inline_tAp hpv₁ hLCu hfvu h₂
  | @fOp Γ s tBound tBoundDst αHd body body₁ L₁ ht₁ hbody₁ iht ihbody =>
    cases h₂ with
    | @fOp _ _ _ tBoundDst₂ _ _ body₂ L₂ ht₂ hbody₂ =>
      exact Lemma_2_inline_fOp_fOp ht₁ ht₂ hbody₁ hbody₂ iht ihbody

/-! ### §3.3 Context-evolution lifting

(The lift axiom is hoisted to §3.0 above so it can be invoked inside
the App × App arm of `Lemma_2_inline_app`.) -/

/-- **Lemma 2** (Pasquale & García-Pérez 2024 §3, Diamond property of
`⟶^≡`).

Status: **DEF** (modulo per-case private inline axioms in §3.1 and the
context-evolution lift in §3.3). Returns `Σ'` since `MEqRed` is now
`Type`-valued. -/
noncomputable def Lemma_2_DiamondMEqRed
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁)
    (h₂ : MEqRed Γ₀ s₀ t₀ t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂)) :
    Σ' (t₃ : Term), MEqRed Γ₁ s₁ t₁ t₃ × MEqRed Γ₂ s₂ t₂ t₃ := by
  obtain ⟨t₃, h₁'₀, h₂'₀⟩ := Lemma_2_DiamondMEqRed_core h₁ h₂
  exact Lemma_2_DiamondMEqRed_ctx_axiom hCt₁ hCt₂ h₁'₀ h₂'₀

/-! ## §4. Convenience: the bare-existence corollary

This is now identical to `Lemma_2_DiamondMEqRed` itself (since the
side-condition clause has been dropped); kept as a name-compatible
alias for downstream consumers. -/

/-- Bare-existence corollary of `Lemma_2_DiamondMEqRed`. -/
noncomputable def Lemma_2_DiamondMEqRed_bare
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁)
    (h₂ : MEqRed Γ₀ s₀ t₀ t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂)) :
    Σ' t₃, MEqRed Γ₁ s₁ t₁ t₃ × MEqRed Γ₂ s₂ t₂ t₃ :=
  Lemma_2_DiamondMEqRed h₁ h₂ hCt₁ hCt₂

/-! ## §5. Same-context corollary

The most common application of Lemma 2 takes `Γ₁; s₁ = Γ₂; s₂ = Γ₀; s₀`
(reflexive `↣*`), which is the actual diamond property in the standard
sense. -/

/-- The diamond property of `MEqRed` at a single extended context. -/
noncomputable def Lemma_2_DiamondMEqRed_sameCtx
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRed Γ s t₀ t₂) :
    Σ' t₃, MEqRed Γ s t₁ t₃ × MEqRed Γ s t₂ t₃ :=
  Lemma_2_DiamondMEqRed_bare h₁ h₂
    (Relation.ReflTransGen.refl) (Relation.ReflTransGen.refl)

end Pss
