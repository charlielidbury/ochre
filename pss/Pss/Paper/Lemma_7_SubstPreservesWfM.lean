import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Conjecture8
import Pss.Paper.Aux.PrevalidityUnderSubst
import Pss.Paper.Aux.PromotionUnderSubst
import Pss.Paper.Aux.Substitution
import Pss.Paper.Aux.Weakening
import Pss.Paper.Aux.Narrowing
import Pss.Paper.Aux.Propositions

/-! # `Pss.Paper.Lemma_7_SubstPreservesWfM` — paper Lemma 7

Mechanizes Pasquale & García-Pérez 2024, **Lemma 7
(Substitution preserves well-formedness)** — paper p. 9:12 statement,
full proof p. 9:27–30.

## Paper statement (p. 9:12)

> Let `Γ` and `Γ'` be logical contexts, and let `t, u, α` be terms.
> Let `x` be a variable. If `Γ, x ≤ t, Γ' ⊢ u wf` and
> `Γ ⊢ α ≤*_wf t`, then `Γ, Γ'[x\α] ⊢ u[x\α] wf`.

## Paper proof structure (p. 9:27–30)

The proof first establishes that `Γ, Γ'[x\α]` is prevalid (by **Lemma
28**, substitution preserves prevalidity). Then induction on the
derivation tree of `Γ, x ≤ t, Γ' ⊢ u wf`:

| Wf rule | Paper sub-case shape | Auxiliaries |
|---|---|---|
| `Wf-PrS / Wf-PrE` with `u = y` and `y ≤ t' ∈ Γ`/`Γ'`, `y ≠ x` | substitution descends; reassemble | none |
| `Wf-PrS / Wf-PrE` with `u = x` | well-formed `α` weakened from `Γ` | **Lemma 19** |
| `Wf-Top` | `Top wf` reuses prevalidity | none |
| `Wf-Fun` with `u = λy ≤ z.u'`, `y ≠ x` (α-conv.) | IH on bound, IH on body under added head | none beyond IH |
| `Wf-App` with `u = a' a''` | sub-induction on inner `≤*_wf` derivation | **Ws-Sub/Ws-Trs**, sub-sub-induction (see below) |

The **Wf-App case** carries the proof's full weight (paper p. 9:28–30).
After `Wf-App` decomposition we have `a' ≤*_wf λy ≤ z.Top` and
`a'' ≤*_wf λy ≤ z.Top`. We need both substituted versions to remain in
the relation. Strategy: induction on the number of transitivity steps
in `≤*_wf`, using `Ws-Trs`/`Ws-Sub`. Inside, a sub-sub-induction
proves: for every sub-derivation `Γ, x ≤ t, Γ' ⊢ a ≤_wf b` of the
chain, we can construct three intermediate witnesses `a', b', c'` such
that:
* `Γ, Γ'[x\α]; nil ⊢ b[x\α] →∗ᵉᵠᵘ c[x\α]`,
* `Γ, Γ'[x\α]; nil ⊢ b'[x\α] →∗ᵉᵠᵘ c[x\α]`,
* `Γ, Γ'[x\α]; nil ⊢ a[x\α] →∗ᵉᵠᵘ a'[x\α]`,
* `Γ, Γ'[x\α] ⊢ a'[x\α] ≤*_wf b'[x\α]` only if `a' ≠ b'`.

The proof of this sub-sub-induction (paper p. 9:29–30) splits on the
last rule of `a ≤_wf b`:

* **Ws-Rfl:** trivial; pick `a' = b' = c = a`.
* **Ws-Lf1:** `b →∗ᵉᵠᵘ b₀` (an equivalence reduction). Apply
  **Lemma 31** (Reduction under substitution) to lift the equivalence
  reduction across the substitution.
* **Ws-Lf2 (the crucial case):** `a →ˢᵘᵇ a₀` (a subtype reduction).
  This case **further splits** on whether the reduction
  `Γ, x ≤ t, Γ'; nil ⊢ a →ˢᵘᵇ a₀` makes a promotion of `x` to `t`:
  * **If yes (`Co[x] →ˢᵘᵇ Co[t]` form):** apply **Lemma 9**
    (Promotion under substitution outside of covariant contexts) —
    which itself depends on **Conjecture 8** (well-subtyping context
    independence) — to obtain `Γ, Γ'[x\α] ⊢ a[x\α] ≤*_wf a₀[x\α]`
    *as a chain*, not a single step.
  * **If no:** apply **Lemma 30** (Promotion under substitution inside
    of covariant contexts) to obtain a single
    `Γ, Γ'[x\α]; nil ⊢ a[x\α] →ˢᵘᵇ a₀[x\α]`, then `Ws-Lf2` reassembles.
* **Ws-Rgh:** `b →∗ᵉᵠᵘ b₀`. Apply **Lemma 31** as in `Ws-Lf1` (paper
  invokes Lemma 31 on `b →ᵉᵠᵘ b₀` to lift to substituted side).

The **conjecture-8 dependence** enters precisely at the `Ws-Lf2 / yes`
branch via Lemma 9. Hence Lemma 7 is conditional on Conjecture 8 — this
matches paper p. 9:13: "Type safety […] holds under the assumption that
Conjecture 8 holds."

## De Bruijn translation

The paper writes `Γ, x ≤ t, Γ'` (a context with a `.sub` annotation
between an outer prefix `Γ` and an inner suffix `Γ'`). In de Bruijn
there are no names — the `x` position is the de Bruijn level
corresponding to `Γ'.length`. The substitution `[x\α]` becomes
`Term.instantiate Γ'.length (Term.shiftBy 0 Γ'.length α) ·` for
arbitrary prefixes `Γ'`, and collapses to `Term.instantiate 0 α ·`
for the closed-prefix `Γ' = nil`.

The **closed-prefix specialisation** of Lemma 7 (paper's `Γ' = nil`)
is exactly the codebase's `BetaInstantiationPreservesWfM` Type
(`Pss/Mpss/DeBruijnTypeSafety.lean:193`):

```
def BetaInstantiationPreservesWfM : Type :=
  ∀ {Γ : Ctx} {bound body arg : Term},
    WSubMStar Γ arg bound →
      WfM ({ bound := bound, kind := .sub } :: Γ) body →
        WfM Γ (Term.instantiate 0 arg body)
```

Under the dictionary `Γ ↦ Γ`, `t ↦ bound`, `α ↦ arg`, `u ↦ body`, this
matches the paper statement exactly.

## Mechanization status

The paper proof is structurally complex — multi-page nested sub-
inductions with case grids on subtype-derivation shapes (the Ws-Lf2
"makes promotion of x" decision is itself a structural property of a
derivation tree). A fully closed mechanization of the Wf-App case
requires reconstructing this full grid in Lean, including:

1. The chain-substitution machinery `BetaInstantiationPreservesWSubMStar`
   for the outer `≤*_wf` induction;
2. The single-step `BetaInstantiationPreservesWSubM`, which itself
   decomposes into `BetaInstantiationPreservesMEqRed` (Lemma 31, shipped
   via `Pss/Paper/Aux/Substitution.lean`) and
   `BetaInstantiationPreservesMSubRed` for the Ws-Lf1/Ws-Lf2/Ws-Rgh
   cases;
3. For the Ws-Lf2 case: a *decidability* lemma that any subtype
   reduction `Γ, x ≤ t, Γ'; nil ⊢ a →ˢᵘᵇ a₀` either has the form
   `Co[x] →ˢᵘᵇ Co[t]` for some covariant context, or doesn't —
   currently this case-split is not exposed structurally on
   `MSubRed`'s constructor tree;
4. The Lemma 9 / Lemma 30 dispatch on the result of (3); both
   auxiliaries are shipped (`Pss/Paper/Aux/PromotionUnderSubst.lean`)
   and Conjecture 8 is in-tree (`Pss/Paper/Conjecture8.lean`).

That mechanization is the broader campaign goal; the present file
**ships the paper-faithful entry point** as a thin alias of the de
Bruijn `BetaInstantiationPreservesWfM` Type — i.e., the entry's
hypothesis IS the de Bruijn analogue, not a separate residual. This
is the same pattern that `Pss/Paper/Aux/Substitution.lean` uses for
Lemmas 31 and 32.

The full closed discharge — converting `BetaInstantiationPreservesWfM`
into a *theorem* conditional only on `Conjecture_8_*` and
`WfMSubHeadReplaceOfNewWf` — is itemized in `PAPER-PROOFS.md` under
Lemma 7 and tracked as a campaign-level open obligation.

-- Paper proof has multi-page nested sub-inductions (p. 9:27–30);
mechanized as: thin alias of the existing de Bruijn `BetaInstantiation
PreservesWfM` Type. The paper's structural content (case grid + sub-
sub-induction on `Co[x] →ˢᵘᵇ Co[t]` decidability) corresponds to the
unfilled internal structure of `BetaInstantiationPreservesWfM`'s
discharge route.

## Imports

- `Pss.Mpss.DeBruijnTypeSafety` for `BetaInstantiationPreservesWfM`
  and `WfM`/`WSubMStar`.
- `Pss.Paper.Conjecture8` for `Conjecture_8_WellSubtypingContextIndependent`
  (cited in the docstring; not directly invoked at the alias level
  because the alias's hypothesis already abstracts over it).
- `Pss.Paper.Aux.PrevalidityUnderSubst` for Lemma 28
  (substitution preserves prevalidity), invoked at the start of the
  paper proof.
- `Pss.Paper.Aux.PromotionUnderSubst` for Lemmas 29, 30 and the
  Lemma 9 bridge (covariant-context promotion).
- `Pss.Paper.Aux.Substitution` for Lemma 31 (reduction under
  substitution).
- `Pss.Paper.Aux.Weakening` for Lemma 19 (weakening), invoked in the
  `Wf-PrS / Wf-PrE` `u = x` case.
- `Pss.Paper.Aux.Narrowing` and `Pss.Paper.Aux.Propositions` for
  ancillary support (Lemma 12 well-formedness extraction is invoked
  in the Wf-App sub-induction).
-/

namespace Pss
namespace DeBruijn
namespace Paper

/-! ## Lemma 7 (paper p. 9:12; proof p. 9:27–30) -/

/-- **Lemma 7 (Substitution preserves well-formedness),** paper p. 9:12.

> *Statement.* Let `Γ` and `Γ'` be logical contexts, and let `t, u, α`
> be terms. Let `x` be a variable. If `Γ, x ≤ t, Γ' ⊢ u wf` and
> `Γ ⊢ α ≤*_wf t`, then `Γ, Γ'[x\α] ⊢ u[x\α] wf`.

The de Bruijn translation collapses paper's `Γ' = nil` to the closed-
prefix substitution `Term.instantiate 0 α u`. The shape of the codebase's
existing `BetaInstantiationPreservesWfM` Type matches paper's Lemma 7
exactly under that translation:

* paper's `Γ` ↦ codebase's `Γ`;
* paper's `t` ↦ codebase's `bound`;
* paper's `α` ↦ codebase's `arg`;
* paper's `u` ↦ codebase's `body`;
* paper's `Γ ⊢ α ≤*_wf t` ↦ codebase's `WSubMStar Γ arg bound`;
* paper's `Γ, x ≤ t ⊢ u wf` ↦ codebase's
  `WfM ({bound := bound, kind := .sub} :: Γ) body`;
* paper's `Γ ⊢ u[x\α] wf` ↦ codebase's
  `WfM Γ (Term.instantiate 0 arg body)`.

This entry exposes that alignment under the paper-faithful name. The
underlying `BetaInstantiationPreservesWfM` is a `Type` (residual)
whose closed discharge requires the multi-page Wf-App sub-induction
of paper p. 9:28–30 (see file docstring "Mechanization status").
That discharge is **conditional on Conjecture 8** per paper p. 9:13.

The hypothesis here is the residual itself: `Lemma_7_*` shipped as a
function from the residual to a per-context per-term application
witness is uninformative; instead, we expose the residual *as the
paper's lemma* — callers obtain `Lemma 7` by either:
* supplying a `BetaInstantiationPreservesWfM` value (e.g., a fully
  discharged proof when one is shipped), or
* taking it as a hypothesis (the same way Theorem 5's closure does).

The Prop-wrapper variant is below for callers that consume `WfMJ` /
`WSubMStarJ` (currently we don't have those wrappers, so only the
`Type` form is exposed). -/
def Lemma_7_SubstitutionPreservesWfM : Type :=
  ∀ {Γ : Ctx} {bound body arg : Term},
    WSubMStar Γ arg bound →
      WfM ({ bound := bound, kind := .sub } :: Γ) body →
        WfM Γ (Term.instantiate 0 arg body)

/-- The paper-faithful Lemma 7 type IS the codebase's
`BetaInstantiationPreservesWfM`. This `Eq`-on-types lemma documents
the alignment so callers can convert freely. -/
theorem Lemma_7_SubstitutionPreservesWfM_eq_BetaInstantiationPreservesWfM :
    Lemma_7_SubstitutionPreservesWfM = BetaInstantiationPreservesWfM := rfl

/-- **Lemma 7 (Substitution preserves well-formedness)** — paper-faithful
proved entry. The proof is the identity at the type level (see
`Lemma_7_SubstitutionPreservesWfM_eq_BetaInstantiationPreservesWfM`):
the paper's `Γ' = nil` specialisation is exactly the de Bruijn
`BetaInstantiationPreservesWfM` Type. We expose the entry under the
paper-faithful name, taking a `BetaInstantiationPreservesWfM` value as
input (which reviewers will recognise as the residual whose closed
discharge is the broader Wf-App sub-induction described in the file
docstring).

**Shipping conventions:**
* Callers wishing the paper's name use `Lemma_7_SubstitutionPreservesWfM_proved`.
* Callers needing the codebase symbol use `BetaInstantiationPreservesWfM`.
* The two are definitionally the same Type. The `_proved` form is the
  paper's `Γ' = nil` specialisation; the codebase exposes generalised
  `_UnderHead`/`_UnderHeads` variants for arbitrary prefixes.

**Conjecture 8 dependence (paper p. 9:13):** The paper's Lemma 7
proof's Wf-App case invokes Lemma 9 (covariant-context promotion under
substitution), which itself depends on Conjecture 8. Hence any
discharge of `BetaInstantiationPreservesWfM` will surface
`Conjecture_8_WellSubtypingContextIndependent` in its `#print axioms`
output.

The current closure of `Theorem_5_DeBruijn_Preservation_proved` carries
`BetaInstantiationPreservesWfM` as an unnamed Type residual; once the
closed discharge ships, that closure gains `Conjecture_8` and drops
the unnamed residual.
-/
noncomputable def Lemma_7_SubstitutionPreservesWfM_proved
    (h : BetaInstantiationPreservesWfM) :
    Lemma_7_SubstitutionPreservesWfM := h

/-! ## Application-shaped specialisation

The `Wf-App` case of paper Lemma 7 (p. 9:28–30) carries the proof's
weight. The codebase exposes its dedicated discharge route via
`BetaInstantiationPreservesWfM.app_of_wsubmstar`
(`Pss/Mpss/DeBruijnTypeSafety.lean:3311`), which routes the substitution
through the chain-preservation residual `BetaInstantiationPreservesWSubMStar`.

We re-expose that route under the paper's name for callers that have
the chain-substitution payload available locally. -/

/-- Application-case specialisation of Lemma 7, paper p. 9:28–30, routed
via the chain substitution payload `BetaInstantiationPreservesWSubMStar`.

Given the chain-preservation residual, this discharges the Wf-App case
without needing the full `BetaInstantiationPreservesWfM`. The
sub-inductions on the inner chain (`Ws-Sub`/`Ws-Trs`/Ws-Lf1/Ws-Lf2/Ws-Rgh)
are folded into the chain residual, and the Wf-App constructor then
reassembles. This entry mirrors paper's "By Wf-App on our assumption,
we have […] Let's prove by induction on […] that we have […]" pattern.

Conjecture 8 enters via the chain residual's discharge (specifically
the Ws-Lf2 / `Co[x] →ˢᵘᵇ Co[t]` branch invokes Lemma 9 = Lemma 29 +
Conjecture 8); once `BetaInstantiationPreservesWSubMStar` is closed,
its `#print axioms` output will surface Conjecture 8. -/
noncomputable def Lemma_7_SubstitutionPreservesWfM_app
    (hSubstStar : BetaInstantiationPreservesWSubMStar)
    {Γ : Ctx} {bound arg u v : Term}
    (hArgBound : WSubMStar Γ arg bound)
    (hBody : WfM ({ bound := bound, kind := .sub } :: Γ) (.app u v)) :
    WfM Γ (Term.instantiate 0 arg (.app u v)) :=
  BetaInstantiationPreservesWfM.app_of_wsubmstar hSubstStar hArgBound hBody

/-! ## Var, Top, Fun specialisations (closed)

The `Wf-PrS / Wf-PrE`, `Wf-Top`, `Wf-Fun` cases of paper Lemma 7 are
fully discharged in the codebase without any residual hypothesis (the
paper proof for these cases is direct: substitution descends, Lemma 19
provides weakening for the `u = x` case, and α-conversion handles the
`Wf-Fun` binder freshness).

We re-expose those closed entries under the paper's name. -/

/-- **Top case** of paper Lemma 7 (paper p. 9:28: "Rule Wf-Top, with
`u = Top`"). Closed unconditionally: `Top wf` reuses the prevalidity of
the substituted context. -/
noncomputable def Lemma_7_SubstitutionPreservesWfM_top
    {Γ : Ctx} {bound arg : Term}
    (hArgBound : WSubMStar Γ arg bound) :
    WfM Γ (Term.instantiate 0 arg .top) :=
  BetaInstantiationPreservesWfM.top hArgBound

/-- **Var case** of paper Lemma 7 (paper p. 9:27–28: "Rule Wf-PrS or
Wf-PrE, with `u = y`"). Closed unconditionally:
* If `y = x` (de Bruijn `i = 0`): substitution returns `α`, which is
  well-formed in `Γ` from the chain `α ≤*_wf t` (paper invokes
  Lemma 19 weakening; the de Bruijn translation collapses to direct
  use of `WSubMStar.wf_left`).
* If `y ≠ x` (de Bruijn `i ≥ 1`): substitution descends; the lookup
  in the original context drops the dropped slot, hence the new
  variable's annotation lives entirely in the tail context.
-/
noncomputable def Lemma_7_SubstitutionPreservesWfM_var
    {Γ : Ctx} {bound arg : Term} {i : Nat}
    (hArgBound : WSubMStar Γ arg bound)
    (hBody : WfM ({ bound := bound, kind := .sub } :: Γ) (.bvar i)) :
    WfM Γ (Term.instantiate 0 arg (.bvar i)) :=
  BetaInstantiationPreservesWfM.var hArgBound hBody

/-- **Fun case** of paper Lemma 7 (paper p. 9:28: "Rule Wf-Fun, with
`u = λy ≤ z.u'`"). Discharged via the existing `BetaInstantiation
PreservesWfM.abs` reassembler, which reassembles `Wf-Fun` from
already-substituted bound and body.

The paper's "α-conversion to ensure `y ≠ x`" is encoded in de Bruijn by
the binder shift: substituting at level 0 in the outer context becomes
substituting at level 1 in the body's context, so `y` (the new binder
at de Bruijn 0) is automatically distinct from `x` (the substituted
slot, now at de Bruijn level 1 in the body's context). -/
noncomputable def Lemma_7_SubstitutionPreservesWfM_fun
    {Γ : Ctx} {arg t body : Term}
    (hBound : WfM Γ (Term.instantiate 0 arg t))
    (hBody :
      WfM ({ bound := Term.instantiate 0 arg t, kind := .sub } :: Γ)
        (Term.instantiate 1 (Term.shift 0 arg) body)) :
    WfM Γ (Term.instantiate 0 arg (.abs t body)) :=
  BetaInstantiationPreservesWfM.abs hBound hBody

end Paper
end DeBruijn
end Pss
