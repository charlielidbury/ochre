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

## Discharge attempt (this session, 2026-04-29) — moreover-clause threading blocker

Threading the paper's "moreover" clause (avoidance of Me-Pro on `x`
through both closing derivations) is necessary to discharge the
β-step residuals using term-size induction. The plan was to give
`_core` the signature

```
Σ' (t₃ : Term) (h₁' : MEqRed Γ s t₁ t₃) (h₂' : MEqRed Γ s t₂ t₃),
  ∀ x : String,
    (avoidsPro h₁ x = true → avoidsPro h₂' x = true) ∧
    (avoidsPro h₂ x = true → avoidsPro h₁' x = true)
```

Per-constructor `avoidsPro_*` simp lemmas were added to
`Pss.Mpss.AvoidsPro` (see `avoidsPro_pro`/`_bet`/`_top`/`_app`/`_var`/
`_fun_`/`_tAp`/`_fOp`) precisely to support this threading. They unfold
`avoidsPro` constructor-by-constructor without manual recursor unfolds.

**The blocker:** `_core`'s `var × pro` arm closes the diagram with
`MEqRed.refl hpv hLCα' hfvα' : MEqRed Γ s α' α'` on the right edge,
where `α'` is the destination of the `pro`'s inner reduction. To prove
the moreover clause we need `avoidsPro (MEqRed.refl hpv hLCα' hfvα') x =
true` for all `x`, but `MEqRed.refl` is built via `Classical.choice` on
top of `MEqRed.refl_J : MEqRedJ Γ s α' α'` (a `Nonempty`-wrapped
derivation). The `.some` extraction is opaque: we cannot observe which
constructor tree `Classical.choice` returned, hence `avoidsPro` of a
`refl`-built derivation is not provably `true` in Lean.

The same blocker hits any cell where the closing edge is a refl
(symmetric `pro × var`, the `MEqRed.tAp` discharger, etc.).

**Three resolution paths, none ready in this session:**

1. **Type-valued `Term.LC`.** Lifts `LC` from `Prop` to `Type`, making
   `MEqRed.refl_J` itself Type-valued and therefore observably built
   from `MEqRed` constructors (no `Classical.choice`). Then `avoidsPro`
   can be computed structurally on the refl-derivation. This is a
   massive cross-codebase refactor — `Term.LC` appears in dozens of
   theorem statements and proofs across `Pss/Syntax`, `Pss/Mpss`, etc.

2. **Source-driven refl construction.** Replace `MEqRed.refl hpv hLC hfv`
   with a construction that takes a witness `MEqRed Γ s α α'` and
   returns BOTH the refl and a proof of `avoidsPro = true` at once,
   via Type-induction on the source derivation. Doable but ~200 lines
   of mirror-recursion that mostly duplicates `MEqRed.refl_J`'s tree.

3. **`avoidsPro_refl` as a single new axiom.** One-line axiom
   `avoidsPro (MEqRed.refl _ _ _) x = true`, morally true (refl uses
   only top/var/app/fun_/fOp constructors, all of which trivially avoid
   Pro). Violates this session's "no new axioms" constraint, but would
   unblock the entire threading in ~30 lines of additional code on top
   of the simp lemmas already committed.

**What WAS shipped this session:** Per-constructor `avoidsPro_*` simp
lemmas in `Pss/Mpss/AvoidsPro.lean` (commit `3d08efd`). These are the
foundation for any of the three paths above; they let downstream proofs
unfold `avoidsPro` on a constructor-shaped derivation by `simp` alone.
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

/-- Lift a same-context joining derivation across two `↣*` evolutions.

**Why an axiom (precise blocker):** identical to `Lemma_1_ctx_axiom`'s
blocker (see `Pss/Mpss/Commutation.lean`). The Ct-Stk and Ct-Ann
inductive arms re-cast the inner `MEqRed` derivations across an
`MEqRed`-step on the popped stack head / annotation, requiring
`.equ`-narrowing of `MEqRed` along an `MEqRed`-step on the bound term
— itself confluence-shaped (recursive). Both consumers of this axiom
(`Lemma_2_DiamondMEqRed` and the App × App arm of `Lemma_2_inline_app`)
pass refl-or-near-refl chains.

**Discharge plan:** see `AXIOMS.md` axiom #8
(`Lemma_2_DiamondMEqRed_ctx_axiom`).

**Phase 5e blocker (2026-05-03):** Phase 5d's `stack_head_replace_univ_exists`
takes a `CofinAvoidsProSelfUniv` premise on the input derivation. Phase 5e
attempted to use this helper to discharge `_inline_app`'s App×App internal
use of `_ctx_axiom`. The architectural gap that blocks the discharge:

1. **`_inline_app`'s App×App arm needs `CofinAvoidsProSelfUniv hu'_w` and
   `CofinAvoidsProSelfUniv hu₂_w`** to invoke `stack_head_replace_univ_exists`.
   These IH outputs come from `ihu hu₂`. Preserving CAPSU through the IH
   requires `_core`'s motive enrichment with output-CAPSU guarantees.

2. **`_core`'s motive enrichment requires INPUT CAPSU on `h₁` and `h₂`**.
   Specifically, the Pro × Var case OUTPUTS `MEqRed.pro hpv₂ heq₁ hα₁` whose
   `CAPSU` (by `CofinAvoidsProSelfUniv_pro` simp) reduces to `CAPSU hα₁` —
   where `hα₁` is the input's inner derivation (sub-derivation of `h₁`).
   So output CAPSU requires input CAPSU on h₁.

3. **CAPSU is NOT universally provable on arbitrary `MEqRed Γ s u v`**. The
   `fOp` arm of `CAPSU` requires `AvoidsProUniv (hbody y_i _) y_i` for every
   cofinite witness — but in the body's context `⟨y_i, α, .equ⟩ :: Γ`, a
   `Me-Pro y_i` step is a LEGAL constructor (looks up `equBinds y_i α`).
   Arbitrary derivations may include such steps, so `AvoidsProUniv` fails
   in general. There is no "CAPSU normalize" recipe.

4. **The public `Lemma_2_DiamondMEqRed_sameCtx` callers cannot supply input
   CAPSU**. Callers in `Pss/Mpss/Commutation.lean` (`Lemma_1_StrongCommutativity_sameCtx`
   line 546) and `Pss/Mpss/TransitivityElim.lean` (line 122) pass arbitrary
   `MEqRed` derivations from outer case-splits / `Classical.choice` extractions.
   Adding `CAPSU` premises to `_sameCtx` would propagate up to
   `Lemma_1_StrongCommutativity`, `Theorem_3_TransitivityIsAdmissible`, etc.
   — changing public APIs to take side conditions the paper does not include
   and that downstream callers cannot supply.

**Verdict**: Phase 5e as designed (use Phase 5d infrastructure to discharge
`_ctx_axiom` from headline closures via input-CAPSU premises) is BLOCKED
by the same fundamental mismatch identified in the Phase 4b second-pass
analysis. The `AvoidsProUniv` / `CofinAvoidsProSelfUniv` rename-stable
predicates are TRUE rename-stable infrastructure but they cannot be
populated at the public Lemma 2 entry point without altering its API.

**Alternative paths forward** (none ready, listed for future sessions):
* **Restructure `_inline_app`'s App×App** to NOT use `_ctx_axiom` —
  e.g., reduce `v ⟶ v'` first and shift IH stacks, requires deeper
  refactor of `_core`'s induction scheme.
* **Direct `_ctx_axiom` discharge via `.equ`-narrowing chain** —
  the original confluence-shaped recursive narrowing. ~300-500 lines.
  Independent of the Phase 5d infrastructure.
* **Type-LC + alpha-aware MEqRed constructors** — make body sample
  invariant under rename so CAPSU is definitionally preserved across
  cofinite-set widening. Cross-codebase refactor on the scale of Type-LC.
* **Side-condition-strengthened public Lemma 2** — accept that
  Lemma 2 / Theorem 3 / Lemma 1 take CAPSU side conditions. Paper-
  faithfulness suffers; downstream callers (e.g. `TransitivityElim`)
  also need to supply CAPSU on `Classical.choice`-extracted
  derivations, which is itself unprovable.

**Phase 5f: Option (a) "App×App restructure" viability analysis (2026-05-03,
post-Phase-5e).** A subsequent attempt examined whether the App×App arm of
`_inline_app` could be rewritten to AVOID stack-head replacement entirely —
sidestepping `_ctx_axiom` without enriching `_core`'s motive with CAPSU.
Four sub-variants were explored; ALL are blocked by the same structural
constraint:

* **(a1) "Diamond at u doesn't care about stack mismatches".** The output
  goal is `Σ' t₃, MEqRed Γ s (.app u' v') t₃ × MEqRed Γ s (.app u₂ v₂) t₃`.
  The only `MEqRed` constructors that produce a target of shape
  `MEqRed Γ s (.app _ _) t₃` with arbitrary operator are `.app` (forces
  `t₃ = .app w v_w`, requires sub-derivation at stack `(v_first :: s)` for
  the operator) and `.bet` (forces `u' = .abs t' body'`, not generally
  true here). `.tAp` requires `u' = .top`. So any closing derivation MUST
  use `.app` constructor with operator at stack `(v' :: s)` and `(v₂ :: s)`
  respectively. The IHs `ihu` give the operator at stack `(v :: s)` only.
  `MEqRed` is a parallel-reduction relation, not transitively closed, so
  composing derivations to bridge stack heads is not available. Blocked.

* **(a2) "Reduce v's first, then close operator".** `_core` is structural-
  recursive on `h₁`, so `ihu` and `ihv` are FIXED at the stacks determined
  by `h₁`'s `.app` constructor signature (`hu : MEqRed Γ (v :: s) u u'`,
  `hv : MEqRed Γ [] v v'`). Any new operator derivation at a different
  stack `(v_w :: s)` must be CONSTRUCTED — there's no IH that gives one
  for free. Constructing `MEqRed Γ (v_w :: s) u u_w` from existing
  `MEqRed Γ (v :: s) u u'` is precisely `stack_head_replace`, which is
  exactly the helper Phase 5e tried to discharge and which requires the
  CAPSU side condition. Blocked.

* **(a3) "Output cofin* guarantee in `_core`'s motive (no input CAPSU)".**
  The Pro × Var case of `_core` outputs `MEqRed.pro hpv₂ heq₁ hα₁`. By
  the `cofinAvoidsProSelf_pro` simp lemma, output CAPSU reduces to CAPSU
  on `hα₁` — a sub-derivation of the INPUT `h₁`. So a "produces CAPSU as
  output" motive still bottoms out at input CAPSU on `h₁/h₂`. Even
  proving CAPSU by structural induction on `_core`'s OUTPUT derivation
  fails because the output's leaves are input sub-derivations whose CAPSU
  is not definable without input CAPSU. Blocked.

* **(a4) "Ship analysis, propose option (b)".** Selected. The analysis
  above shows that any closing of App×App at stack `s` from operator
  IHs at stack `(v :: s)` MUST use stack-head replacement somewhere,
  and stack-head replacement requires side conditions that cannot be
  populated at the public entry. Option (a) is fundamentally blocked.

**The structural reason in one paragraph.** `MEqRed.app`'s constructor
signature is `MEqRed Γ (v :: s) u u' → MEqRed Γ [] v v' → MEqRed Γ s
(.app u v) (.app u' v')`. The operator's stack-head `v` is *the same
term* as the operand's source `v`. When two parallel reductions step
the operand to `v'` and `v₂` (different reducts), the joining target
must satisfy BOTH operator chains' stack-head invariants — but the IH
only gives the operator at stack `(v :: s)`. There's no way around
this without either (i) a stack-head-replacement lemma (which requires
side conditions on input derivations the public API cannot supply), or
(ii) restricting the diamond to inputs that carry CAPSU evidence
(altering the public API in a paper-unfaithful way).

**Recommended next direction: option (b) "inline WSubM-transitivity".**
The current call chain `Theorem_3 → MSub.trans_step → commute_subStar_eqStar
→ Lemma_1_StrongCommutativity_sameCtx` (uses `Lemma_1_ctx_axiom`) and
`→ Lemma_2_DiamondMEqRed_sameCtx` (uses `Lemma_2_DiamondMEqRed_ctx_axiom`)
is the entire surface area for these axioms. A direct discharge of WSubM
transitivity (the headline of `TransitivityElim`) WITHOUT routing through
`Lemma_1`/`Lemma_2` would eliminate the dependency. The paper's
transitivity-elimination proof is the diamond + commutativity construction;
inlining it requires either a different transitivity proof technique
(e.g., logical relations) or accepting that transitivity is paper-faithfully
proven via diamond. Option (b) is therefore "proof-theoretic" rather than
"proof-engineering" — out of scope for a single discharge campaign session.
The honest path is the cross-codebase Type-LC + alpha-aware MEqRed refactor
(third bullet above), which preserves the paper's proof structure but
makes the rename-stable infrastructure (Phase 5a–5d) work end-to-end. -/
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
`(.abs t' body')` is forced by the source-shape match in the caller.

**Discharge plan:** see `AXIOMS.md` axiom #9
(`Lemma_2_inline_app_bet_residual_axiom`). The blocker shared with
axiom #10 / `Lemma_1_inline_app_bet_residual` is that
`avoidsPro (MEqRed.refl _) x = true` is not structurally provable
because `MEqRed.refl` extracts via `Classical.choice` from a
`Nonempty`. Three resolution paths in `PLAN.md`'s discharge campaign:
Type-LC refactor (Option B), source-driven refl construction, or
consume the standalone `avoidsPro_refl` axiom. -/
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
  | @bet _ _ t' _ _ _ body' L₂ hLCt₂ hbody₂ _hUni₂ hv₂ =>
    -- App × Bet: still axiomatised. The source-shape match equates u with
    -- the .abs t' body' shape; the axiom takes the operator-MEqRed at that
    -- forced shape directly.
    exact Lemma_2_inline_app_bet_residual_axiom hu hv hLCt₂ hbody₂ hv₂ ihu ihv

/-- Bet × non-TAp residual: covers Bet × App and Bet × Bet.
Same closure obstruction as App × non-TAp.

**Discharge plan:** see `AXIOMS.md` axiom #10
(`Lemma_2_inline_bet_residual_axiom`). Same blocker as #9. -/
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
private noncomputable def _extractPrevalidOfMEqRed_loc {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x α α' hpv _ _ _ => exact extractPrevalid hpv
  | @bet Γ s t v v' body body' L _ _ _ _ _ ihv => exact ihv
  | @top Γ s hpv => exact extractPrevalid hpv
  | @app Γ s u u' v v' _ _ _ ihv => exact ihv
  | @var Γ s x hpv => exact extractPrevalid hpv
  | @fun_ Γ t t' body body' L _ _ _ iht _ => exact iht
  | @tAp Γ s u hpv _ _ => exact extractPrevalid hpv
  | @fOp Γ s t t' α body body' L _ _ _ iht _ => exact iht

/-! #### Bool-and helper lemmas (used to thread the moreover clause) -/

private theorem _bool_and_mp1 {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true _ _).mp h).1
private theorem _bool_and_mp2 {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true _ _).mp h).2
private theorem _bool_and_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true :=
  (Bool.and_eq_true _ _).mpr ⟨ha, hb⟩

/-! ### §3.1.5 Avoidance preservation: partial implementation

For 6 of the 8 `MEqRed` constructors (`top`, `var`, `tAp`, `pro`, `app`,
`bet`), `Lemma_25_NarrowingMEqRed`'s tactic-mode `induction` definition
reduces by definitional `rfl` once `subst hΓ` consumes the indexed-Γ
equality. The `fun_` and `fOp` cases are blocked by a `simpa using
ih_body` inside `Lemma_25_NarrowingMEqRed`'s body lambda, which inserts
a transport that breaks pure definitional reduction.

Per-constructor avoidance equation (definitional, only for the 6
working constructors). Used by `avoidsPro_NarrowingMEqRed_aux` below
for the simple cases. -/

private theorem _Lemma_25_NarrowingMEqRed_pro_eq
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack}
    {y : String} {α α' : Term}
    (hpv : PrevalidExt (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) s)
    (heq : (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁).equBinds y α)
    (hα : MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) s α α')
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed (MEqRed.pro hpv heq hα) hLCt hfvt) w =
      (decide (y ≠ w) && avoidsPro (Lemma_25_NarrowingMEqRed hα hLCt hfvt) w) :=
  rfl

private theorem _Lemma_25_NarrowingMEqRed_top_eq
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack}
    (hpv : PrevalidExt (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) s)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed (MEqRed.top hpv) hLCt hfvt) w = true :=
  rfl

private theorem _Lemma_25_NarrowingMEqRed_var_eq
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack} {y : String}
    (hpv : PrevalidExt (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) s)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed (@MEqRed.var _ _ y hpv) hLCt hfvt) w =
      true :=
  rfl

private theorem _Lemma_25_NarrowingMEqRed_tAp_eq
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack} {u : Term}
    (hpv : PrevalidExt (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁).dom)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed (MEqRed.tAp hpv hLCu hfvu) hLCt hfvt) w =
      true :=
  rfl

private theorem _Lemma_25_NarrowingMEqRed_app_eq
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack}
    {u u' v v' : Term}
    (hu : MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) (v :: s) u u')
    (hv : MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) [] v v')
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed (MEqRed.app hu hv) hLCt hfvt) w =
      (avoidsPro (Lemma_25_NarrowingMEqRed hu hLCt hfvt) w &&
       avoidsPro (Lemma_25_NarrowingMEqRed hv hLCt hfvt) w) :=
  rfl

private theorem _Lemma_25_NarrowingMEqRed_bet_eq
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack}
    {tBound v0 v0' body body' : Term} (L : Finset String)
    (hLCtB : Term.LC tBound)
    (hbody : ∀ y, y ∉ L →
      MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) [] v0 v0')
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed (MEqRed.bet L hLCtB hbody hUni hv) hLCt hfvt) w =
      (avoidsPro (Lemma_25_NarrowingMEqRed
        (hbody (pickFresh L) (pickFresh_notMem L)) hLCt hfvt) w &&
       avoidsPro (Lemma_25_NarrowingMEqRed hv hLCt hfvt) w) :=
  rfl

private theorem _Lemma_25_NarrowingMEqRed_fun_eq
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term}
    {tBound tBound' body body' : Term} (L : Finset String)
    (ht : MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) [] tBound tBound')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, tBound, .sub⟩ :: (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁)) []
        (body^[y]) (body'^[y]))
    (hUni : True)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed (MEqRed.fun_ L ht hbody hUni) hLCt hfvt) w =
      (avoidsPro (Lemma_25_NarrowingMEqRed ht hLCt hfvt) w &&
       avoidsPro (Lemma_25_NarrowingMEqRed
         (Γ₂ := ⟨pickFresh L, tBound, .sub⟩ :: Γ₂)
         (hbody (pickFresh L) (pickFresh_notMem L)) hLCt hfvt) w) :=
  rfl

private theorem _Lemma_25_NarrowingMEqRed_fOp_eq
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack}
    {tBound tBound' α body body' : Term} (L : Finset String)
    (ht : MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) [] tBound tBound')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁)) s
        (body^[y]) (body'^[y]))
    (hUni : True)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed (MEqRed.fOp L ht hbody hUni) hLCt hfvt) w =
      (avoidsPro (Lemma_25_NarrowingMEqRed ht hLCt hfvt) w &&
       avoidsPro (Lemma_25_NarrowingMEqRed
         (Γ₂ := ⟨pickFresh L, α, .equ⟩ :: Γ₂)
         (hbody (pickFresh L) (pickFresh_notMem L)) hLCt hfvt) w) :=
  rfl

/-- `Lemma_25_NarrowingMEqRed` preserves `avoidsPro` for any variable `w`.

Proved by structural induction on the source `h`, with the indexed Γ
generalized via `Γ₂` quantification. Each constructor case uses the
per-constructor `_Lemma_25_NarrowingMEqRed_*_eq` lemma above (all
`rfl`-provable thanks to `Lemma_25_NarrowingMEqRed`'s tactic-mode
`induction` definition reducing definitionally on each constructor
shape) plus the IH on sub-derivations. -/
private theorem avoidsPro_NarrowingMEqRed_aux
    {Γ₁ : Ctx} {x : String} {t t' : Term}
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String)
    {Γold : Ctx} {st : Stack} {u v : Term} (h : MEqRed Γold st u v) :
    ∀ (Γ₂ : Ctx) (hΓ : Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁ = Γold),
      avoidsPro (Lemma_25_NarrowingMEqRed (hΓ ▸ h) hLCt hfvt) w =
        avoidsPro h w := by
  induction h with
  | @top Γ s hpv =>
    intro Γ₂ hΓ; subst hΓ
    rw [_Lemma_25_NarrowingMEqRed_top_eq, avoidsPro_top]
  | @var Γ s y hpv =>
    intro Γ₂ hΓ; subst hΓ
    rw [_Lemma_25_NarrowingMEqRed_var_eq, avoidsPro_var]
  | @tAp Γ s u_ hpv hLCu hfvu =>
    intro Γ₂ hΓ; subst hΓ
    rw [_Lemma_25_NarrowingMEqRed_tAp_eq, avoidsPro_tAp]
  | @pro Γ s y α α' hpv heq hα ihα =>
    intro Γ₂ hΓ; subst hΓ
    rw [_Lemma_25_NarrowingMEqRed_pro_eq, avoidsPro_pro, ihα Γ₂ rfl]
  | @app Γ s u₀ u₀' v₀ v₀' hu hv ihu ihv =>
    intro Γ₂ hΓ; subst hΓ
    rw [_Lemma_25_NarrowingMEqRed_app_eq, avoidsPro_app,
        ihu Γ₂ rfl, ihv Γ₂ rfl]
  | @bet Γ s tB v₀ v' body body' L hLCtB hbody _hUni hv ihbody ihv =>
    intro Γ₂ hΓ; subst hΓ
    rw [_Lemma_25_NarrowingMEqRed_bet_eq, avoidsPro_bet,
        ihbody (pickFresh L) (pickFresh_notMem L) Γ₂ rfl,
        ihv Γ₂ rfl]
  | @fun_ Γ tB tB' body body' L ht hbody _hUni iht ihbody =>
    intro Γ₂ hΓ; subst hΓ
    rw [_Lemma_25_NarrowingMEqRed_fun_eq, avoidsPro_fun_,
        iht Γ₂ rfl,
        ihbody (pickFresh L) (pickFresh_notMem L)
          (⟨pickFresh L, tB, .sub⟩ :: Γ₂) (by simp)]
  | @fOp Γ s tB tB' α body body' L ht hbody _hUni iht ihbody =>
    intro Γ₂ hΓ; subst hΓ
    rw [_Lemma_25_NarrowingMEqRed_fOp_eq, avoidsPro_fOp,
        iht Γ₂ rfl,
        ihbody (pickFresh L) (pickFresh_notMem L)
          (⟨pickFresh L, α, .equ⟩ :: Γ₂) (by simp)]

/-- `Lemma_25_NarrowingMEqRed` preserves `avoidsPro` for any `w`. -/
private theorem avoidsPro_NarrowingMEqRed
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' u v : Term} {st : Stack}
    (h : MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) st u v)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ₁.dom) (w : String) :
    avoidsPro (Lemma_25_NarrowingMEqRed h hLCt hfvt) w = avoidsPro h w :=
  avoidsPro_NarrowingMEqRed_aux hLCt hfvt w h Γ₂ rfl

/-! #### Avoidance preservation for `MEqRed.rename_sub` and
`MEqRed.rename_equ_no_fv`

Strategy: the wrappers `MEqRed.rename_sub` (in `Pss.Mpss.Renaming`) and
`MEqRed.rename_equ_no_fv` (locally below) take their underlying
substitution result and `rw` it through several index equalities. The
resulting `cast`s preserve `avoidsPro` (since `avoidsPro` reads the
constructor tree, which `cast` does not touch).

Below we prove:
1. A generic `avoidsPro_cast` lemma (cast invariance).
2. Avoidance preservation for the local `MEqRed.rename_equ_loc`
   (the underlying primitive of `MEqRed.rename_equ_no_fv`).
3. Avoidance preservation for `MEqRed.rename_equ_no_fv` (via 1+2).
4. For `MEqRed.rename_sub`, since its primitive
   `MEqRed.subst_yz_sub_head` is `private` to Renaming.lean, we
   re-derive a parallel local primitive `_subst_yz_sub_head_local`
   along with its avoidance preservation, then prove
   `MEqRed.rename_sub`'s avoidance preservation by parallel
   construction (taking advantage of `MEqRed.rename_sub`'s structure
   being `by_cases hyz; subst+exact h | rewrite-cast-of-subst`). -/

/-- Cast invariance of `avoidsPro` — when the indices match, casting
is trivial. Uses heterogeneous equality decomposition. -/
private theorem avoidsPro_cast {Γ Γ' : Ctx} {s s' : Stack}
    {u u' v v' : Term}
    (hΓ : Γ = Γ') (hs : s = s') (hu : u = u') (hv : v = v')
    (h : MEqRed Γ s u v) (w : String) :
    avoidsPro (hΓ ▸ hs ▸ hu ▸ hv ▸ h) w = avoidsPro h w := by
  subst hΓ hs hu hv; rfl

/-- Single-index transport invariance: `avoidsPro (eq ▸ h)` for an
equation `v = v'` between source/destination indices.

Special case: `hu_eq ▸ h` where `hu_eq : u = u'`, lifts `h : MEqRed Γ s u v`
to `MEqRed Γ s u' v`. -/
private theorem avoidsPro_subst_eq_dest
    {Γ : Ctx} {s : Stack} {u v v' : Term}
    (heq : v = v') (h : MEqRed Γ s u v) (w : String) :
    avoidsPro (heq ▸ h) w = avoidsPro h w := by
  subst heq; rfl

private theorem avoidsPro_subst_eq_src
    {Γ : Ctx} {s : Stack} {u u' v : Term}
    (heq : u = u') (h : MEqRed Γ s u v) (w : String) :
    avoidsPro (heq ▸ h) w = avoidsPro h w := by
  subst heq; rfl

private theorem avoidsPro_subst_eq_ctx
    {Γ Γ' : Ctx} {s : Stack} {u v : Term}
    (heq : Γ = Γ') (h : MEqRed Γ s u v) (w : String) :
    avoidsPro (heq ▸ h) w = avoidsPro h w := by
  subst heq; rfl

private theorem avoidsPro_subst_eq_stack
    {Γ : Ctx} {s s' : Stack} {u v : Term}
    (heq : s = s') (h : MEqRed Γ s u v) (w : String) :
    avoidsPro (heq ▸ h) w = avoidsPro h w := by
  subst heq; rfl

/-- Cast invariance for the `MEqRed.refl`-shaped transport: both source
and destination indices are the same term, transported simultaneously. -/
private theorem avoidsPro_subst_eq_both
    {Γ : Ctx} {s : Stack} {u u' : Term}
    (heq : u = u') (h : MEqRed Γ s u u) (w : String) :
    avoidsPro (heq ▸ h : MEqRed Γ s u' u') w = avoidsPro h w := by
  subst heq; rfl


/-! #### Local re-derivation of `subst_yz_sub_head` and `rename_sub`

The originals (`MEqRed.subst_yz_sub_head` and the wrappers around it
inside `MEqRed.rename_sub`) live in `Pss.Mpss.Renaming` and are
`private`, so we cannot reference them from this file. We re-derive
them here as `_subst_yz_sub_head_local` and `_rename_sub_local`,
mirroring the original code, then prove avoidance preservation by
parallel structural induction. The constructions produce IDENTICAL
results to the originals (by mutual definitional equivalence), so
substituting `_rename_sub_local` for `MEqRed.rename_sub` at use sites
inside `Lemma_2_inline_fun_fun` is sound. -/

/-- Local re-derivation: `Prevalid` of the renamed context. Mirrors
`Pss.Mpss.Renaming.prevalid_rename_sub_head`. -/
private noncomputable def _prevalid_rename_sub_head_local
    {Γ₂ Γ₁ : Ctx} {y z : String} {t : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : Prevalid (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁)) :
    Prevalid (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
  classical
  have hpv_inner : Prevalid (⟨y, t, .sub⟩ :: Γ₁) := Prevalid.outer hpv
  cases hpv_inner with
  | sub hpvΓ₁ hy_notin_Γ₁ hfvt hLCt =>
    have hpv_zsub : Prevalid (⟨z, t, .sub⟩ :: Γ₁) :=
      Prevalid.sub hpvΓ₁ hz_notin_Γ₁ hfvt hLCt
    have hyz_zsub : y ∉ Ctx.dom (⟨z, t, .sub⟩ :: Γ₁) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
      · exact hyz hyz'
      · exact hy_notin_Γ₁ hyΓ
    have hfvt_z : Term.fv t ⊆ Ctx.dom (⟨z, t, .sub⟩ :: Γ₁) := by
      intro w hw
      rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem (hfvt hw)
    have hpv_y_z : Prevalid (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) :=
      Prevalid.sub hpv_zsub hyz_zsub hfvt_z hLCt
    have hpv_doubled :
        Prevalid (Γ₂ ++ ⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) := by
      induction Γ₂ with
      | nil => simpa using hpv_y_z
      | cons e rest ih =>
        have hpv' : Prevalid (e :: (rest ++ ⟨y, t, .sub⟩ :: Γ₁)) := by simpa using hpv
        have hpv_rest : Prevalid (rest ++ ⟨y, t, .sub⟩ :: Γ₁) := hpv'.tail
        have hz_notin_rest : z ∉ Ctx.dom rest := by
          intro hmem
          apply hz_notin_Γ₂
          rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem hmem
        have ih' := ih hz_notin_rest hpv_rest
        have he_notin : e.name ∉ Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: Γ₁) := by
          cases hpv' with
          | sub _ hen _ _ => exact hen
          | equ _ hen _ _ => exact hen
        have he_notin' : e.name ∉ Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) := by
          intro hmem
          rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons] at hmem
          rw [Ctx.dom_append, Ctx.dom_cons] at he_notin
          rcases Finset.mem_union.mp hmem with hr | htail
          · apply he_notin; exact Finset.mem_union.mpr (Or.inl hr)
          · rcases Finset.mem_insert.mp htail with hey | hrest
            · apply he_notin
              exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
            · rcases Finset.mem_insert.mp hrest with hez | hΓ
              · apply hz_notin_Γ₂
                rw [show z = e.name from hez.symm]
                exact Finset.mem_insert_self _ _
              · apply he_notin
                exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))
        cases hpv' with
        | @sub _ name u' _ _ hfve hlce =>
          have hfve' : Term.fv u' ⊆
              Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) := by
            intro w hw
            have hw' := hfve hw
            rw [Ctx.dom_append, Ctx.dom_cons] at hw'
            rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
            rcases Finset.mem_union.mp hw' with hr | htail
            · exact Finset.mem_union.mpr (Or.inl hr)
            · rcases Finset.mem_insert.mp htail with hey | hΓ
              · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
              · exact Finset.mem_union.mpr
                  (Or.inr (Finset.mem_insert.mpr
                    (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
          have res := Prevalid.sub ih' he_notin' hfve' hlce
          simpa using res
        | @equ _ name α _ _ hfve hlce =>
          have hfve' : Term.fv α ⊆
              Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) := by
            intro w hw
            have hw' := hfve hw
            rw [Ctx.dom_append, Ctx.dom_cons] at hw'
            rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
            rcases Finset.mem_union.mp hw' with hr | htail
            · exact Finset.mem_union.mpr (Or.inl hr)
            · rcases Finset.mem_insert.mp htail with hey | hΓ
              · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
              · exact Finset.mem_union.mpr
                  (Or.inr (Finset.mem_insert.mpr
                    (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
          have res := Prevalid.equ ih' he_notin' hfve' hlce
          simpa using res
    have hok : SubstOk (⟨z, t, .sub⟩ :: Γ₁) (.fvar z) := by
      refine ⟨Term.LC.fvar z, ?_⟩
      intro w hw
      have hwz : w = z := by simpa [Term.fv] using hw
      subst hwz
      rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
    exact Lemma_28a_SubstPreservesPrevalid_kind hpv_doubled hok

/-- Local re-derivation: `PrevalidExt` of the renamed context with stack
also renamed. Mirrors `Pss.Mpss.Renaming.prevalidExt_rename_sub_head`. -/
private noncomputable def _prevalidExt_rename_sub_head_local
    {Γ₂ Γ₁ : Ctx} {st : Stack} {y z : String} {t : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) st) :
    PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st) := by
  classical
  have hpv_base := extractPrevalid hpv
  have hpv_renamed := _prevalid_rename_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv_base
  have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
  induction st with
  | nil =>
    cases hpv with
    | nil _ => exact PrevalidExt.nil hpv_renamed
  | cons α st' ih =>
    match hpv with
    | PrevalidExt.cons hpvr hLCα hfvα =>
      have ih' := ih hpvr
      have hLCα' : Term.LC (Term.subst y (.fvar z) α) := Term.subst_lc hLCfz hLCα
      have hfvα' : Term.fv (Term.subst y (.fvar z) α) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
        intro w hw
        have hsub := Term.fv_subst_subset y (.fvar z) α hw
        rcases Finset.mem_union.mp hsub with hsd | hsd
        · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
          have hw_in : w ∈ Ctx.dom (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := hfvα hwfv
          rw [Ctx.dom_append, Ctx.dom_cons] at hw_in
          show w ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
          rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
          rcases Finset.mem_union.mp hw_in with hΓ₂ | htail
          · exact Finset.mem_union.mpr (Or.inl hΓ₂)
          · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
            · exact absurd hwy (fun hh => hwne (by simp [hh]))
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert_of_mem hwΓ₁))
        · have hwz : w = z := by simpa [Term.fv] using hsd
          rw [hwz]
          show z ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
          rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
          exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_insert_self _ _))
      exact PrevalidExt.cons ih' hLCα' hfvα'

/-- Local re-derivation: `MEqRed.subst_yz_sub_head`. Mirrors the
private function in `Pss.Mpss.Renaming`. -/
private noncomputable def _subst_yz_sub_head_local
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {t u u' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (h : MEqRed (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) st u u') :
    MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  generalize hΓ : (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) = Γ at h
  revert hz_notin_Γ₂
  induction h generalizing Γ₂ with
  | @pro Γ st' yi α α' hpv heq hα ihα =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpvL : Prevalid (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      _prevalidExt_rename_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hyiy : yi ≠ y := equBinds_ne_x_at_sub_head hpvL heq
    have heq_lifted : (Ctx.subst y (.fvar z) Γ₂ ++ Γ₁).equBinds yi
        (Term.subst y (.fvar z) α) :=
      equBinds_split (s := .fvar z) hyiy hpvL heq
    have hpv_big : Prevalid (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) :=
      _prevalid_rename_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂ hpvL
    have hpv_big_assoc :
        Prevalid (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) := by
      have heq : (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) =
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by simp
      exact heq ▸ hpv_big
    have heq' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁).equBinds yi
        (Term.subst y (.fvar z) α) := by
      have := Ctx.equBinds_insert_middle
        (Γ₁ := Ctx.subst y (.fvar z) Γ₂) (Δ := [⟨z, t, .sub⟩]) (Γ₂ := Γ₁)
        hpv_big_assoc heq_lifted
      have heq_simp : (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) =
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by simp
      exact heq_simp ▸ this
    -- Use ▸ at outermost instead of `rw [Term.subst_fvar_ne hyiy]` in goal.
    have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar yi :=
      Term.subst_fvar_ne hyiy _
    exact hsubst_eq.symm ▸ MEqRed.pro hpv' heq' (ihα (Γ₂ := Γ₂) rfl hz_notin_Γ₂)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    intro hz_notin_Γ₂
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open : Term.subst y (.fvar z) (Term.opening v0' bd') =
        Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      simp [Term.opening, Term.subst_open hLCfz]
    -- Goal type initially: MEqRed _ _ X (subst y z (opening v0' bd')).
    -- Construct the .bet term at its natural type and transport once.
    -- The transport `hsubst_open.symm ▸` lives at OUTERMOST position so
    -- avoidsPro_subst_eq_dest can peel it.
    refine hsubst_open.symm ▸ ?_
    -- Goal now: MEqRed _ _ X (opening (subst y z v0') (subst y z bd'))
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ trivial ?_
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := Γ₂) rfl hz_notin_Γ₂
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      exact ih_body
    · have ihv' := ihv (Γ₂ := Γ₂) rfl hz_notin_Γ₂
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    intro hz_notin_Γ₂
    exact MEqRed.top
      (_prevalidExt_rename_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv)
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    intro hz_notin_Γ₂
    have ihu' := ihu (Γ₂ := Γ₂) rfl hz_notin_Γ₂
    have ihv' := ihv (Γ₂ := Γ₂) rfl hz_notin_Γ₂
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      _prevalidExt_rename_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    by_cases hyiy : yi = y
    · -- yi = y: result is refl. Use ▸ at outermost.
      have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      have hLCz : Term.LC (.fvar z) := Term.LC.fvar z
      have hfvz : Term.fv (.fvar z) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
        intro w hw
        have hwz : w = z := by simpa [Term.fv] using hw
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      exact hsubst_eq.symm ▸ MEqRed.refl hpv' hLCz hfvz
    · -- yi ≠ y: result is var. Use ▸ at outermost.
      have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar yi :=
        Term.subst_fvar_ne hyiy _
      exact hsubst_eq.symm ▸ (@MEqRed.var _ _ yi hpv')
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_ trivial
    · have iht' := iht (Γ₂ := Γ₂) rfl hz_notin_Γ₂
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1.1
      have hyfy : yfresh ≠ y := hyfresh.1.2
      have hyfz : yfresh ≠ z := hyfresh.2
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ
      have ih_body :=
        ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂) (by simp) hz_notin_Γ₂'
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      _prevalidExt_rename_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hw_in : w ∈ Ctx.dom (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := hfv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hw_in
        show w ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hw_in with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert_of_mem hwΓ₁))
      · have hwz : w = z := by simpa [Term.fv] using hsd
        rw [hwz]
        show z ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_insert_self _ _))
    -- The goal `MEqRed _ _ (Term.subst y z (.app .top u_)) (Term.subst y z .top)`
    -- reduces definitionally to `MEqRed _ _ (.app .top (Term.subst y z u_)) .top`
    -- (via Term.subst's pattern matching). Provide MEqRed.tAp directly.
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    -- The goal `MEqRed _ (Stack.subst y z (αi :: st')) ...` reduces
    -- definitionally to `MEqRed _ (Term.subst y z αi :: Stack.subst y z st') ...`
    -- via List.map_cons. So we don't need rw [Stack.subst_cons].
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_ trivial
    · have iht' := iht (Γ₂ := Γ₂) rfl hz_notin_Γ₂
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1.1
      have hyfy : yfresh ≠ y := hyfresh.1.2
      have hyfz : yfresh ≠ z := hyfresh.2
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ
      have ih_body :=
        ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂) (by simp) hz_notin_Γ₂'
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-! #### Avoidance preservation for `_subst_yz_sub_head_local`

Per-constructor `rfl`-equations: most cases reduce by `rfl` (top, app,
tAp). The `pro`, `var`, and recursive cases (bet, fun_, fOp) have
internal `rw`-induced transports inside `_subst_yz_sub_head_local` that
break direct `rfl`. To prove preservation, we'd need to navigate these
manually for each case (~100 lines of manipulation per arm).

Status: top, app, tAp `_eq` lemmas confirmed `rfl`-provable below.
The remaining cases (pro, var, bet, fun_, fOp) require explicit
transport navigation; deferred to a follow-up commit. -/

private theorem _subst_yz_sub_head_local_top_eq
    {Γ₁ Γ₂ : Ctx} {y z : String} {t : Term} {st : Stack}
    (hyz : y ≠ z) (hz_notin_Γ₁ : z ∉ Γ₁.dom) (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) st) (w : String) :
    avoidsPro (_subst_yz_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂
      (MEqRed.top hpv)) w = true := rfl

private theorem _subst_yz_sub_head_local_app_eq
    {Γ₁ Γ₂ : Ctx} {y z : String} {t : Term} {st : Stack}
    {u u' v v' : Term}
    (hyz : y ≠ z) (hz_notin_Γ₁ : z ∉ Γ₁.dom) (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hu : MEqRed (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) (v :: st) u u')
    (hv : MEqRed (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) [] v v') (w : String) :
    avoidsPro (_subst_yz_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂
      (MEqRed.app hu hv)) w =
    (avoidsPro (_subst_yz_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂ hu) w &&
     avoidsPro (_subst_yz_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂ hv) w) :=
  rfl

private theorem _subst_yz_sub_head_local_tAp_eq
    {Γ₁ Γ₂ : Ctx} {y z : String} {t : Term} {st : Stack}
    {u : Term}
    (hyz : y ≠ z) (hz_notin_Γ₁ : z ∉ Γ₁.dom) (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) st)
    (hLCu : Term.LC u)
    (hfvu : Term.fv u ⊆ (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁).dom) (w : String) :
    avoidsPro (_subst_yz_sub_head_local hyz hz_notin_Γ₁ hz_notin_Γ₂
      (MEqRed.tAp hpv hLCu hfvu)) w = true := rfl

/-! ### Avoidance preservation: status

The combined-function approach (`_subst_yz_sub_head_with_av` returning
`Σ' h' (preservation)`) works for the simple cases (top, app, tAp, var,
pro) but bottoms out at the COFINITE BODY cases (bet, fun_, fOp).

The blocker: `avoidsPro_bet` (and `_fun_`, `_fOp`) evaluate the body at
`pickFresh L`. The renamed bet uses `MEqRed.bet (L ∪ {y}) ...`, so its
`avoidsPro` evaluates at `pickFresh (L ∪ {y}) ≠ pickFresh L`. To compare
the two `avoidsPro` values, we need an **alpha-equivariance** lemma for
`avoidsPro`: `avoidsPro (hbody y₁ _) w = avoidsPro (hbody y₂ _) w` for
any two fresh y₁, y₂ valid for `hbody`.

This is a real deeper theorem requiring its own structural proof. It
holds because under a `.sub` head binding (the case we're in here),
`Me-Pro yi` always has `yi ≠ y` (equBinds_ne_x_at_sub_head), so the
fresh y' choice doesn't affect any `Me-Pro yi = w` check for any
user-chosen w.

Future-work: prove `avoidsPro_alpha_equivariance` for cofinite-body
constructors under `.sub`-head context, then complete the bet/fun_/fOp
cases of `_subst_yz_sub_head_with_av`. -/













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
      ht₁'_t₃ann ?_ trivial
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
      ht₂'_t₃ann ?_ trivial
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
private noncomputable def Prevalid.insert_fresh_equ_mid
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
private noncomputable def PrevalidExt.insert_fresh_equ_mid
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
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
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
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ trivial ?_
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
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_ trivial
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
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_ trivial
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

/-! ### §3.7 Avoidance preservation for `MEqRed.rename_equ_loc` and
`MEqRed.rename_equ_no_fv`

Same approach as for `Lemma_25_NarrowingMEqRed`: per-constructor `_eq`
lemmas (rfl-provable at simple cases; var case handles the
`yi=y → refl` branch via `avoidsPro_refl`) plus a structural-induction
aux theorem.

The `var (yi = y)` case is the constructor-introducing arm — the
result is `MEqRed.refl` rather than `MEqRed.var`, but both have
`avoidsPro = true` (the latter via the `avoidsPro_refl` axiom). -/

private theorem _MEqRed_rename_equ_loc_top_eq
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st) (w : String) :
    avoidsPro (MEqRed.rename_equ_loc hyz hz_notin_Γ₁ hz_notin_Γ₂ hy_notin_α
      (MEqRed.top hpv)) w = true := rfl

private theorem _MEqRed_rename_equ_loc_tAp_eq
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α : Term} {u : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st)
    (hLCu : Term.LC u)
    (hfvu : Term.fv u ⊆ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom) (w : String) :
    avoidsPro (MEqRed.rename_equ_loc hyz hz_notin_Γ₁ hz_notin_Γ₂ hy_notin_α
      (MEqRed.tAp hpv hLCu hfvu)) w = true := rfl

private theorem _MEqRed_rename_equ_loc_app_eq
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α : Term}
    {u u' v v' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (hu : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (v :: st) u u')
    (hv : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) [] v v') (w : String) :
    avoidsPro (MEqRed.rename_equ_loc hyz hz_notin_Γ₁ hz_notin_Γ₂ hy_notin_α
      (MEqRed.app hu hv)) w =
    (avoidsPro (MEqRed.rename_equ_loc hyz hz_notin_Γ₁ hz_notin_Γ₂ hy_notin_α hu) w &&
     avoidsPro (MEqRed.rename_equ_loc hyz hz_notin_Γ₁ hz_notin_Γ₂ hy_notin_α hv) w) :=
  rfl

-- The bet case rewrites a TYPE via Term.subst_open, which inserts a
-- transport. So rfl won't work. We document this rather than fight it
-- — the strategy is to prove `avoidsPro_rename_equ_loc` via the cast
-- invariance lemma in cases where rfl-eqs aren't immediate.

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
      ht₁'_t₃ann ?_ trivial
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
      ht₂'_t₃ann ?_ trivial
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
  | @bet Γ s tBound vSrc vDst body bodyDst L hLCt hbody _hUni hv ihbody ihv =>
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
  | @fun_ Γ tBound tBoundDst body body₁ L₁ ht₁ hbody₁ _hUni iht ihbody =>
    cases h₂ with
    | @fun_ _ _ tBoundDst₂ _ body₂ L₂ ht₂ hbody₂ _hUni₂ =>
      exact Lemma_2_inline_fun_fun ht₁ ht₂ hbody₁ hbody₂ iht ihbody
  | tAp hpv₁ hLCu hfvu =>
    exact Lemma_2_inline_tAp hpv₁ hLCu hfvu h₂
  | @fOp Γ s tBound tBoundDst αHd body body₁ L₁ ht₁ hbody₁ _hUni iht ihbody =>
    cases h₂ with
    | @fOp _ _ _ tBoundDst₂ _ _ body₂ L₂ ht₂ hbody₂ _hUni₂ =>
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

/-- The diamond property of `MEqRed` at a single extended context.

Routed directly through `_core` (skipping the `_ctx_axiom` for the
trivial refl/refl context evolution case), so this does NOT depend on
`Lemma_2_DiamondMEqRed_ctx_axiom` *directly* — though it still depends
on it transitively via `_core → _inline_app`'s App×App arm. -/
noncomputable def Lemma_2_DiamondMEqRed_sameCtx
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRed Γ s t₀ t₂) :
    Σ' t₃, MEqRed Γ s t₁ t₃ × MEqRed Γ s t₂ t₃ :=
  Lemma_2_DiamondMEqRed_core h₁ h₂

end Pss
