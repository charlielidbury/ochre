import Pss.Mpss.Substitution
import Pss.Mpss.Weakening
import Pss.Mpss.AvoidsPro

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
| `.abs t b`  | (Fun × Fun) at empty stack | A       | `Lemma_2_inline_fun_fun` (IH-aware) |
|             | (FOp × FOp) at α::s stack  | A       | `Lemma_2_inline_fOp_fOp` (IH-aware) |
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

After the App × App discharge (via `_ctx_axiom`-mediated stack-shift),
the remaining axiomatised arms are:

* App × Bet (`Lemma_2_inline_app_bet_residual_axiom`)
* Bet × {App, Bet} (`Lemma_2_inline_bet_residual_axiom`)
* Fun × Fun (`Lemma_2_inline_fun_fun`)
* FOp × FOp (`Lemma_2_inline_fOp_fOp`)

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

The Fun × Fun and FOp × FOp arms are body-recursive under cofinite
quantification on a fresh name; their discharge needs renaming
infrastructure. -/

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

/-- Inline residual: both derivations are `Me-Fun`. Cofinite body-IH at
a fresh name, plus annotation-IH. -/
private axiom Lemma_2_inline_fun_fun
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
      MEqRed Γ [] (.abs t₁' body₁) t₃ × MEqRed Γ [] (.abs t₂' body₂) t₃

/-- Inline residual: both derivations are `Me-FOp`. Cofinite body-IH at
a fresh name with `.equ` binding, plus annotation-IH. -/
private axiom Lemma_2_inline_fOp_fOp
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
      MEqRed Γ (α :: s) (.abs t₂' body₂) t₃

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
