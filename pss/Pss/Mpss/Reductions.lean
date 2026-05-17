import Pss.Context.Prevalid
import Mathlib.Logic.Relation

/-! # `Pss.Mpss.Reductions` — MPSS equivalence and subtyping reductions

Pasquale & García-Pérez 2024 (CSL 2026), Figure 2.

Two stack-aware reductions on extended contexts `Γ; s ⊢ u ⟶^◁ v`
(◁ ∈ {≡, ≤}). The paper presents the two relations together; `Ms-Equ`
links them by embedding an equivalence step into the subtyping reduction.

Implementation note: the dependency is one-directional — `MSubRed` mentions
`MEqRed` (in `Ms-Equ`) but `MEqRed` does NOT reference `MSubRed`. We
exploit this asymmetry and define `MEqRed` first as a plain inductive,
then `MSubRed` as a plain inductive that *uses* `MEqRed`. This avoids the
multi-motive eliminator that a Lean 4 `mutual` block would generate, and
lets us use the `induction` tactic on either relation directly.

* `MEqRed Γ s u v`  — equivalence reduction `Γ; s ⊢ u ⟶^≡ v`. 8 rules:
  Me-Pro, Me-Bet, Me-Top, Me-App, Me-Var, Me-Fun, Me-TAp, Me-FOp.
* `MSubRed Γ s u v` — subtype reduction    `Γ; s ⊢ u ⟶^≤ v`. 6 rules:
  Ms-Pro, Ms-Top, Ms-Equ, Ms-App, Ms-Fun, Ms-FOp.

## Locally-nameless idiom

Paper rules use named binders, e.g. `λx ≤ t.u`. We encode in locally-nameless
style: `λx ≤ t.u` becomes `Term.abs t body`, with `body` indexed by `bvar 0`.
A premise of the form "u reduces under the binder named x" is encoded with
**cofinite quantification**: `(L : Finset String) (∀ x ∉ L, ... body^[x] ...)`.

The paper's β-substitution `u'[x\v']` becomes `Term.opening v' body'` once
the named `x` is eliminated.

The paper's premises `Γ; s prevalid` become explicit `PrevalidExt Γ s` premises
on leaf rules. Premises about free variables / local closure of subterms not
governed by an inductive premise are carried as `Term.LC ·` side conditions,
matching the convention used by `Step` in `Pss.Reduction.Operational`.
-/

namespace Pss

/-- MPSS equivalence reduction `Γ; s ⊢ u ⟶^≡ v`. Pasquale & García-Pérez
2024 Figure 2 (top half).

Note: although the paper presents `MEqRed` and `MSubRed` together, only
`MSubRed` actually depends on `MEqRed` (via `Ms-Equ`); `MEqRed` does not
reference `MSubRed`. We exploit this and define `MEqRed` as a plain
inductive, which gives us a single-motive eliminator for `induction`. -/
inductive MEqRed : Ctx → Stack → Term → Term → Type where
  /-- **Me-Pro**: variable promotion under an `≡`-binding. If `x ≡ α ∈ Γ`
  and `α` reduces to `α'`, then `x` reduces to `α'`. -/
  | pro {Γ : Ctx} {s : Stack} {x : String} {α α' : Term} :
      PrevalidExt Γ s →
      Γ.equBinds x α →
      MEqRed Γ s α α' →
      MEqRed Γ s (.fvar x) α'

  /-- **Me-Bet**: β-step on an applied abstraction. The body reduces under
  the bound name, the operand reduces under the empty stack, and the result
  substitutes the reduced operand into the reduced body.

  Paper:  `Γ; s ⊢ u ⟶^≡ u',  Γ; nil ⊢ v ⟶^≡ v'`
          ────────────────────────────────────────
          `Γ; s ⊢ (λx ≤ t.u) v ⟶^≡ u'[x\v']`

  Cofinite encoding: pick fresh `x ∉ L`, reduce `body^[x] ⟶^≡ body'^[x]`
  under `Γ; s` (the bound name `x` does NOT enter the context here — it just
  names the open hole), then result is `opening v' body'`. -/
  | bet {Γ : Ctx} {s : Stack} {t v v' body body' : Term} (L : Finset String) :
      Term.LC t →
      (∀ x, x ∉ L → MEqRed Γ s (body^[x]) (body'^[x])) →
      MEqRed Γ [] v v' →
      MEqRed Γ s (.app (.abs t body) v) (Term.opening v' body')

  /-- **Me-Top**: `Top` reduces to itself (reflexively). -/
  | top {Γ : Ctx} {s : Stack} :
      PrevalidExt Γ s →
      MEqRed Γ s .top .top

  /-- **Me-App**: congruence on application. Pushing the operand onto the
  stack lets the operator be reduced in a stack-aware fashion.

  Paper:  `Γ; v::s ⊢ u ⟶^≡ u',  Γ; nil ⊢ v ⟶^≡ v'`
          ────────────────────────────────────────────
          `Γ; s ⊢ u v ⟶^≡ u' v'` -/
  | app {Γ : Ctx} {s : Stack} {u u' v v' : Term} :
      MEqRed Γ (v :: s) u u' →
      MEqRed Γ [] v v' →
      MEqRed Γ s (.app u v) (.app u' v')

  /-- **Me-Var**: a free variable reduces to itself (reflexively). -/
  | var {Γ : Ctx} {s : Stack} {x : String} :
      PrevalidExt Γ s →
      MEqRed Γ s (.fvar x) (.fvar x)

  /-- **Me-Fun**: descend under an *unapplied* abstraction (empty stack).
  The bound annotation reduces, and the body reduces under the context
  extended with the new `≤`-binding.

  Paper:  `Γ; nil ⊢ t ⟶^≡ t',  Γ, x ≤ t; nil ⊢ u ⟶^≡ u'`
          ───────────────────────────────────────────────
          `Γ; nil ⊢ λx ≤ t.u ⟶^≡ λx ≤ t'.u'`

  Cofinite encoding on the body name `x`. -/
  | fun_ {Γ : Ctx} {t t' body body' : Term} (L : Finset String) :
      MEqRed Γ [] t t' →
      (∀ x, x ∉ L →
        MEqRed (⟨x, t, .sub⟩ :: Γ) [] (body^[x]) (body'^[x])) →
      MEqRed Γ [] (.abs t body) (.abs t' body')

  /-- **Me-TAp**: `Top` applied to anything reduces to `Top`. (A "technical
  device" of Hutchins, kept in MPSS to make the relation reflexive on
  `Top u` shapes that arise during reduction.) -/
  | tAp {Γ : Ctx} {s : Stack} {u : Term} :
      PrevalidExt Γ s →
      Term.LC u →
      Term.fv u ⊆ Γ.dom →
      MEqRed Γ s (.app .top u) .top

  /-- **Me-FOp**: descend under an *applied* abstraction by popping the
  stack. The popped operand `α` becomes an `≡`-binding for the body name.

  Paper:  `Γ; nil ⊢ t ⟶^≡ t',  Γ, x ≡ α; s ⊢ u ⟶^≡ u'`
          ──────────────────────────────────────────────
          `Γ; α::s ⊢ λx ≤ t.u ⟶^≡ λx ≤ t'.u'`

  Cofinite on the body name `x`. The bound annotation reduces; the body
  reduces under `Γ, x ≡ α; s`. -/
  | fOp {Γ : Ctx} {s : Stack} {t t' α body body' : Term} (L : Finset String) :
      MEqRed Γ [] t t' →
      (∀ x, x ∉ L →
        MEqRed (⟨x, α, .equ⟩ :: Γ) s (body^[x]) (body'^[x])) →
      MEqRed Γ (α :: s) (.abs t body) (.abs t' body')

/-- MPSS subtype reduction `Γ; s ⊢ u ⟶^≤ v`. Pasquale & García-Pérez 2024
Figure 2 (bottom half). The only mutual link with `MEqRed` is via the
`Ms-Equ` constructor, so we define `MSubRed` as a plain inductive that
**references** `MEqRed`. -/
inductive MSubRed : Ctx → Stack → Term → Term → Type where
  /-- **Ms-Pro**: variable promotion under a `≤`-binding. -/
  | pro {Γ : Ctx} {s : Stack} {x : String} {t : Term} :
      PrevalidExt Γ s →
      Γ.subBinds x t →
      MSubRed Γ s (.fvar x) t

  /-- **Ms-Top**: anything (LC, in-scope) is below `Top`. -/
  | top {Γ : Ctx} {s : Stack} {u : Term} :
      PrevalidExt Γ s →
      Term.LC u →
      Term.fv u ⊆ Γ.dom →
      MSubRed Γ s u .top

  /-- **Ms-Equ**: an equivalence step counts as a subtyping step.

  Paper:  `Γ; s prevalid,  Γ; s ⊢ u ⟶^≡ v`
          ──────────────────────────────────
          `Γ; s ⊢ u ⟶^≤ v` -/
  | equ {Γ : Ctx} {s : Stack} {u v : Term} :
      PrevalidExt Γ s →
      MEqRed Γ s u v →
      MSubRed Γ s u v

  /-- **Ms-App**: congruence on application — push the operand onto the
  stack and reduce the operator. NOTE: the operand is **not** reduced
  (cf. Me-App which reduces both via equivalence). The paper writes:

  Paper:  `Γ; v::s ⊢ u ⟶^≤ u'`
          ────────────────────────
          `Γ; s ⊢ u v ⟶^≤ u' v` -/
  | app {Γ : Ctx} {s : Stack} {u u' v : Term} :
      MSubRed Γ (v :: s) u u' →
      Term.LC v →
      Term.fv v ⊆ Γ.dom →
      MSubRed Γ s (.app u v) (.app u' v)

  /-- **Ms-Fun**: descend under an *unapplied* abstraction. The bound
  annotation is **invariant** (the paper does not change type annotations
  in subtyping; see §2 discussion).

  Paper:  `Γ, x ≤ t; nil ⊢ u ⟶^≤ u'`
          ──────────────────────────────────
          `Γ; nil ⊢ λx ≤ t.u ⟶^≤ λx ≤ t.u'` -/
  | fun_ {Γ : Ctx} {t body body' : Term} (L : Finset String) :
      Term.LC t →
      (∀ x, x ∉ L →
        MSubRed (⟨x, t, .sub⟩ :: Γ) [] (body^[x]) (body'^[x])) →
      MSubRed Γ [] (.abs t body) (.abs t body')

  /-- **Ms-FOp**: descend under an *applied* abstraction by popping the
  stack. The popped operand `α` becomes an `≡`-binding for the body name.
  Annotation invariant.

  Paper:  `Γ, x ≡ α; s ⊢ u ⟶^≤ u'`
          ──────────────────────────────────
          `Γ; α::s ⊢ λx ≤ t.u ⟶^≤ λx ≤ t.u'` -/
  | fOp {Γ : Ctx} {s : Stack} {t α body body' : Term} (L : Finset String) :
      Term.LC t →
      (∀ x, x ∉ L →
        MSubRed (⟨x, α, .equ⟩ :: Γ) s (body^[x]) (body'^[x])) →
      MSubRed Γ (α :: s) (.abs t body) (.abs t body')

/-- Prop-wrapped MPSS equivalence reduction. Used by callers that only
need provability (not derivation-tree shape) — notably the reflexive
transitive closure built via Mathlib's `Relation.ReflTransGen`, which is
restricted to `Prop`-valued relations. -/
def MEqRedJ (Γ : Ctx) (s : Stack) (u v : Term) : Prop :=
  Nonempty (MEqRed Γ s u v)

/-- Prop-wrapped MPSS subtype reduction. See `MEqRedJ`. -/
def MSubRedJ (Γ : Ctx) (s : Stack) (u v : Term) : Prop :=
  Nonempty (MSubRed Γ s u v)

/-- Many-step equivalence reduction (reflexive-transitive closure of the
Prop-wrapped single-step relation). -/
abbrev MEqRedStar (Γ : Ctx) (s : Stack) : Term → Term → Prop :=
  Relation.ReflTransGen (MEqRedJ Γ s)

/-- Many-step subtype reduction. -/
abbrev MSubRedStar (Γ : Ctx) (s : Stack) : Term → Term → Prop :=
  Relation.ReflTransGen (MSubRedJ Γ s)

/-! ## Local-closure preservation

Every term occurring in a derivation is locally closed. We prove this in a
single mutual induction over both relations. -/

/-- Helper: every `PrevalidExt Γ s` carries a `Prevalid Γ` underneath.

`noncomputable def` (since `PrevalidExt : Type` post-Type-LC refactor; the
recursion uses `PrevalidExt.rec` which the code generator does not synth). -/
noncomputable def extractPrevalid {Γ : Ctx} {s : Stack} (h : PrevalidExt Γ s) :
    Prevalid Γ := by
  induction h with
  | nil hΓ => exact hΓ
  | cons _ _ _ ih => exact ih

/-- Combined LC-preservation for the mutual reduction relations. We can't
use the `induction` tactic on a mutual inductive (multiple motives), so we
fall back to manual `rec` application via the `motive_*` formulation: prove
`(LC u × LC v)` for both relations simultaneously by mutual recursion.

`Type`-valued (`PProd`) and `noncomputable def` (since `Term.LC : Type`). -/
private noncomputable def MEqRed.lc_pair {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : PProd (Term.LC u) (Term.LC v)
  := by
  induction h with
  | @pro Γ s x α α' hpv heq hα ihα =>
      exact ⟨Term.LC.fvar _, ihα.2⟩
  | @bet Γ s t v v' body body' L hLCt hbody hv ihbody ihv =>
      refine ⟨Term.LC.app (Term.LC.abs L hLCt ?_) ihv.1, ?_⟩
      · intro x hx; exact (ihbody x hx).1
      -- RHS: opening v' body'. Use subst_intro + subst_lc.
      classical
      have hv'LC : Term.LC v' := ihv.2
      let x : String := Classical.choose (Term.exists_fresh (L ∪ Term.fv body'))
      have hx : x ∉ L ∪ Term.fv body' :=
        Classical.choose_spec (Term.exists_fresh (L ∪ Term.fv body'))
      have hxL : x ∉ L := fun h' => hx (Finset.mem_union.mpr (Or.inl h'))
      have hxFv : x ∉ Term.fv body' :=
        fun h' => hx (Finset.mem_union.mpr (Or.inr h'))
      have hopen : Term.LC (body'^[x]) := (ihbody x hxL).2
      rw [Term.subst_intro hxFv hv'LC]
      exact Term.subst_lc hv'LC hopen
  | top _ => exact ⟨Term.LC.top, Term.LC.top⟩
  | @app Γ s u u' v v' hu hv ihu ihv =>
      exact ⟨Term.LC.app ihu.1 ihv.1, Term.LC.app ihu.2 ihv.2⟩
  | var _ => exact ⟨Term.LC.fvar _, Term.LC.fvar _⟩
  | @fun_ Γ t t' body body' L ht hbody iht ihbody =>
      refine ⟨Term.LC.abs L iht.1 ?_, Term.LC.abs L iht.2 ?_⟩
      · intro x hx; exact (ihbody x hx).1
      · intro x hx; exact (ihbody x hx).2
  | tAp _ hLCu _ => exact ⟨Term.LC.app Term.LC.top hLCu, Term.LC.top⟩
  | @fOp Γ s t t' α body body' L ht hbody iht ihbody =>
      refine ⟨Term.LC.abs L iht.1 ?_, Term.LC.abs L iht.2 ?_⟩
      · intro x hx; exact (ihbody x hx).1
      · intro x hx; exact (ihbody x hx).2

/-- LHS of any equivalence step is locally closed. -/
noncomputable def MEqRed.lc_left {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Term.LC u := (MEqRed.lc_pair h).1

/-- RHS of any equivalence step is locally closed. -/
noncomputable def MEqRed.lc_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Term.LC v := (MEqRed.lc_pair h).2

/-- Combined LC-preservation for `MSubRed`. Uses `MEqRed.lc_pair` for the
`Ms-Equ` arm — the only place where the two relations interact.

`Type`-valued (`PProd`) and `noncomputable def`. -/
private noncomputable def MSubRed.lc_pair {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : PProd (Term.LC u) (Term.LC v)
  := by
  induction h with
  | @pro Γ s x t hpv hb =>
      exact ⟨Term.LC.fvar _,
             Prevalid.lc_lookupSub (extractPrevalid hpv) hb⟩
  | top _ hLCu _ => exact ⟨hLCu, Term.LC.top⟩
  | @equ Γ s u v hpv heq =>
      exact ⟨MEqRed.lc_left heq, MEqRed.lc_right heq⟩
  | @app Γ s u u' v hu hLCv hfv ihu =>
      exact ⟨Term.LC.app ihu.1 hLCv, Term.LC.app ihu.2 hLCv⟩
  | @fun_ Γ t body body' L hLCt hbody ihbody =>
      refine ⟨Term.LC.abs L hLCt ?_, Term.LC.abs L hLCt ?_⟩
      · intro x hx; exact (ihbody x hx).1
      · intro x hx; exact (ihbody x hx).2
  | @fOp Γ s t α body body' L hLCt hbody ihbody =>
      refine ⟨Term.LC.abs L hLCt ?_, Term.LC.abs L hLCt ?_⟩
      · intro x hx; exact (ihbody x hx).1
      · intro x hx; exact (ihbody x hx).2

/-- LHS of any subtyping step is locally closed. -/
noncomputable def MSubRed.lc_left {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Term.LC u := (MSubRed.lc_pair h).1

/-- RHS of any subtyping step is locally closed. -/
noncomputable def MSubRed.lc_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Term.LC v := (MSubRed.lc_pair h).2

end Pss
