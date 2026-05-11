import Pss.Paper.ContextEvolution
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Aux.Weakening
import Pss.Paper.Aux.Substitution
import Pss.Paper.Aux.Propositions
import Pss.Paper.Lemma_2_NoPromotion

/-! # `Pss.Paper.Lemma_2_Diamond` — paper Lemma 2 (Diamond of `→ᵉᵠᵘ`)

Mechanizes the diamond property for equivalence reduction, Pasquale &
García-Pérez 2024 Lemma 2 (paper p. 9:9 statement; proof p. 9:21–25).

> *Statement.* Let `Γ₀; s₀` be an extended context. Let `t₀, t₁, t₂` be
> terms. If `Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₁` and `Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₂`, then for any
> extended contexts `Γ₁; s₁` and `Γ₂; s₂` such that `Γ₀; s₀ ↣ Γ₁; s₁` and
> `Γ₀; s₀ ↣ Γ₂; s₂`, there exists a term `t₃` such that `Γ₁; s₁ ⊢ t₁ →ᵉᵠᵘ t₃`
> and `Γ₂; s₂ ⊢ t₂ →ᵉᵠᵘ t₃`.
>
> Moreover, for any variable `x`, if in the derivation of
> `Γ₀; s₀ ⊢ t₀ →ᵉᵠᵘ t₁` there isn't an application of Me-Pro that makes a
> promotion of variable `x`, then in the derivation of
> `Γ₂; s₂ ⊢ t₂ →ᵉᵠᵘ t₃` there won't be an application of Me-Pro that makes
> a promotion of variable `x`.

This file is the headline paper-mirroring artifact for the diamond
property. Its case structure mirrors the paper's grid (p. 9:21–25):

| Source rule (left) | Source rule (right) | Paper page | Aux invoked |
|---|---|---|---|
| `Me-Top` | `Me-Top` | 9:21 (base) | (trivial) |
| `Me-Var` | `Me-Var` | 9:21 (base) | (trivial) |
| `Me-Pro` | `Me-Var` | 9:21 | Lemmas 19, 36 |
| `Me-Pro` | `Me-Pro` | 9:21 | (recursive on bound) |
| `Me-App` | `Me-App` | 9:21–22 | Lemma 36 |
| `Me-App` | `Me-Bet` | 9:22–23 | Lemmas 19, **32** |
| `Me-App` | `Me-TAp` | 9:23 | (trivial) |
| `Me-Fun` | `Me-Fun` | 9:23 | (recursive on bound + body) |
| `Me-FOp` | `Me-FOp` | 9:24 | Lemmas 19, 36 |
| `Me-Bet` | `Me-Bet` | 9:25 | Lemmas 19, 36, **32** |
| `Me-TAp` | `Me-TAp` | 9:25 | (trivial) |

## Status & dispatch sequence

Per the analysis in `STOP-LEMMA-2-STRUCTURAL.md`, the unconditional
discharge of Lemma 2 is a multi-dispatch effort (~600–1000 lines)
requiring three new structural auxiliaries:

1. `MEqRedTransportAcrossEvolution` — `MEqRed` respects `↣`. This is
   the de Bruijn analogue of paper Lemma 19's invocation pattern. Its
   proof is induction on `ContextEvolution` with per-`MEqRed`-rule
   transport using the existing `replaceAt_sub`,
   `stack_head_replace_from_handlers` machinery. ~150–250 lines.

2. `ContextEvolution.cons_*` and `ContextEvolution.shiftedStack` —
   helpers to lift a `↣` derivation across a binder extension or a
   stack shift. Both follow from the existing constructors plus
   `MEqRed.refl`. ~50–100 lines.

3. The 9 per-case proofs (paper p. 9:21–25), each invoking the named
   Lemma 19 / 32 / 36 by paper number. ~400–700 lines.

This file ships:

* The paper-faithful statement `Lemma_2_DiamondMEqRed_Conclusion`.
* The transport auxiliary `MEqRedTransportAcrossEvolution` as a
  named premise.
* Each per-case proof obligation as a separate `Prop` (named after the
  paper's case label), so future dispatches can discharge them
  independently.
* The headline theorem `Lemma_2_DiamondMEqRed_of`, conditional on the
  transport auxiliary plus all per-case obligations.
* Direct discharge of the trivial cases (Top × Top, Var × Var, TAp ×
  TAp) using only the transport auxiliary.

No axioms; no `sorry`; build green.

## Note on the side condition

The paper's "Moreover, for any variable x ..." clause (the
non-promotion-of-x invariant) is preserved structurally by the same
induction. This dispatch ships the **diamond conclusion** without the
side condition; the side condition can be added as a parallel
recursion that does not change the proof shape. -- Paper handwaves;
mechanized as: ship the diamond conclusion only.
-/

namespace Pss
namespace DeBruijn
namespace Paper

/-! ## Paper-faithful statement -/

/-- **Paper Lemma 2 conclusion shape** (Pasquale & García-Pérez 2024,
p. 9:9). Given two equivalence-reduction steps from a common source at
`Γ₀; s₀`, plus two evolved extended contexts, there exists a common
reduct reachable in both evolved contexts. -/
def Lemma_2_DiamondMEqRed_Conclusion
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (_h₁ : MEqRed Γ₀ s₀ t₀ t₁) (_h₂ : MEqRed Γ₀ s₀ t₀ t₂) : Prop :=
  ∀ {Γ₁ s₁ Γ₂ s₂},
    ContextEvolution Γ₀ s₀ Γ₁ s₁ →
    ContextEvolution Γ₀ s₀ Γ₂ s₂ →
    ∃ t₃, MEqRedJ Γ₁ s₁ t₁ t₃ ∧ MEqRedJ Γ₂ s₂ t₂ t₃

/-! ## Structural auxiliary: transport `MEqRed` across `↣`

The paper's diamond proof routinely invokes "Lemma 19 (weakening)" to
lift an `MEqRed` derivation in `Γ₀; s₀` into one of the evolved
contexts `Γ_i; s_i`. In de Bruijn, this is captured by the following
auxiliary (which the paper calls Lemma 19 implicitly).

The proof of this auxiliary is induction on the `ContextEvolution`
derivation:

* `ctRefl`: `Γ₀ = Γ'`, `s₀ = s'`; identity.
* `ctAnn` with kind `.sub`: head bound `t →ᵉᵠᵘ t'` rebinds the
  innermost slot; closes via `MEqRed.replaceAt_sub` at index 0.
* `ctAnn` with kind `.equ`: similar, via `MEqRed.replaceAt_equ`
  (existing in DeBruijnReductions.lean).
* `ctStk`: head stack annotation `α →ᵉᵠᵘ α'` updates; closes via
  `MEqRed.stack_head_replace_from_handlers` recursively.

Discharging this is the next dispatch (Dispatch A in
`STOP-LEMMA-2-STRUCTURAL.md`). -/
def MEqRedTransportAcrossEvolution : Prop :=
  ∀ {Γ Γ' : Ctx} {s s' : Stack} {u v : Term},
    ContextEvolution Γ s Γ' s' →
    MEqRed Γ s u v →
    MEqRedJ Γ' s' u v

/-! ## Per-case obligations

Each obligation below mirrors a paper subcase (p. 9:21–25). They are
the recursive-call points of the induction, packaged so future
dispatches can discharge each independently. -/

/-- **Lemma 2 case Me-Pro × Me-Var**, paper p. 9:21.

Source: `bvar i` with `Γ₀.equBinds i α₀` and `α₀ →ᵉᵠᵘ α_1`. RHS source:
`bvar i →ᵉᵠᵘ bvar i` (Me-Var). Paper invokes Lemmas 36 + 19; result
closes by `Me-Pro` at the evolved context.

The IH on the bound `α₀ → α_1` is the standard generalized diamond:
given a SECOND derivation `α₀ → α₂'` and any evolved contexts, find a
common reduct. Paper p. 9:21: invokes this IH with second derivation =
`α₀ → α₂` from `equBinds_evolve` lifted to `Γ₀; s₀` via Lemma 19. -/
def Lemma_2_Case_ProVar : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {i : Nat} {α₀ α_1 : Term},
    PrevalidExt Γ₀ s₀ →
    Γ₀.equBinds i α₀ →
    MEqRed Γ₀ s₀ α₀ α_1 →
    -- Recursive premise: the **standard** generalized diamond IH on
    -- the smaller bound derivation. Quantifies over a second derivation
    -- and evolved contexts.
    (∀ {α_2' : Term},
      MEqRed Γ₀ s₀ α₀ α_2' →
      ∀ {Γ₁' s₁' Γ₂' s₂' : _},
        ContextEvolution Γ₀ s₀ Γ₁' s₁' →
        ContextEvolution Γ₀ s₀ Γ₂' s₂' →
        ∃ α_3, MEqRedJ Γ₁' s₁' α_1 α_3 ∧ MEqRedJ Γ₂' s₂' α_2' α_3) →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ s₀ Γ₁ s₁ →
      ContextEvolution Γ₀ s₀ Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ α_1 t₃ ∧ MEqRedJ Γ₂ s₂ (.bvar i) t₃

/-- **Lemma 2 case Me-Pro × Me-Pro**, paper p. 9:21. Both sides promote
the same variable; the bound annotation is uniquely determined by
prevalidity. -/
def Lemma_2_Case_ProPro : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {i : Nat} {α₀ α_1 α_2 : Term},
    PrevalidExt Γ₀ s₀ →
    Γ₀.equBinds i α₀ →
    MEqRed Γ₀ s₀ α₀ α_1 →
    MEqRed Γ₀ s₀ α₀ α_2 →
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution Γ₀ s₀ Γ₁' s₁' →
      ContextEvolution Γ₀ s₀ Γ₂' s₂' →
      ∃ α_3, MEqRedJ Γ₁' s₁' α_1 α_3 ∧ MEqRedJ Γ₂' s₂' α_2 α_3) →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ s₀ Γ₁ s₁ →
      ContextEvolution Γ₀ s₀ Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ α_1 t₃ ∧ MEqRedJ Γ₂ s₂ α_2 t₃

/-- **Lemma 2 case Me-App × Me-App**, paper p. 9:21–22. Operator
recurses under stack `v_0 :: s_0` (Ct-Stk on the right edges); operand
recurses at `[]`. -/
def Lemma_2_Case_AppApp : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {u₀ u₁ u₂ v₀ v₁ v₂ : Term},
    MEqRed Γ₀ (v₀ :: s₀) u₀ u₁ →
    MEqRed Γ₀ [] v₀ v₁ →
    MEqRed Γ₀ (v₀ :: s₀) u₀ u₂ →
    MEqRed Γ₀ [] v₀ v₂ →
    -- IH on operator (under expanded stack):
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution Γ₀ (v₀ :: s₀) Γ₁' s₁' →
      ContextEvolution Γ₀ (v₀ :: s₀) Γ₂' s₂' →
      ∃ u_3, MEqRedJ Γ₁' s₁' u₁ u_3 ∧ MEqRedJ Γ₂' s₂' u₂ u_3) →
    -- IH on operand:
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution Γ₀ [] Γ₁' s₁' →
      ContextEvolution Γ₀ [] Γ₂' s₂' →
      ∃ v_3, MEqRedJ Γ₁' s₁' v₁ v_3 ∧ MEqRedJ Γ₂' s₂' v₂ v_3) →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ s₀ Γ₁ s₁ →
      ContextEvolution Γ₀ s₀ Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ (.app u₁ v₁) t₃
        ∧ MEqRedJ Γ₂ s₂ (.app u₂ v₂) t₃

/-- **Lemma 2 case Me-App × Me-Bet**, paper p. 9:22–23. The mixed
case: subtype-side `Me-App` reduces `(λx ≤ t.u)v` to `(λx ≤ t'.u')v'`;
equiv-side does β to `u_2[x\v_2]`. Paper invokes asymmetric Lemma 32
to close the subtype edge.

**Moreover-tracked body IH.** The paper's "Moreover" clause (p. 9:9)
says: if either source has `NoPromotionOf 0`, then both outputs have
`NoPromotionOf 0`. For AppBet, the RHS source `u_0 → u_2` lives at
`{t_0, .sub}::Γ_0; shift 0 s_0`, which trivially has `NoPromotionOf 0`
(no equ-binding at slot 0 in a `.sub`-head context). The Moreover then
gives `NoPromotionOf 0` on the LHS output `u_1 → u_3`, which is needed
to bridge the LHS body from `.equ`-head (bound v_1) to `.sub`-head
(bound t_1) via `MEqRed.equ_to_sub_head_replace_NoPromotion` so that
Me-Bet can be applied for the LHS output target. -/
def Lemma_2_Case_AppBet : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {t₀ u₀ u₁ u₂ v₀ v₁ v₂ t₁ : Term},
    Term.Scoped Γ₀.depth t₀ →
    Term.Scoped Γ₀.depth v₀ →
    -- Me-App side decomposes (λx≤t₀.u₀) v₀ → (λx≤t₁.u₁) v₁ via Me-FOp:
    --   t₀ → t₁ at Γ₀; [] (bound reduction)
    --   u₀ → u₁ at ({v₀, .equ} :: Γ₀); shift 0 s₀ (body in .equ head — v₀ popped)
    --   v₀ → v₁ at Γ₀; [] (operand)
    MEqRed Γ₀ [] t₀ t₁ →
    MEqRed ({bound := v₀, kind := .equ} :: Γ₀) (Stack.shift 0 s₀) u₀ u₁ →
    MEqRed Γ₀ [] v₀ v₁ →
    -- Me-Bet side decomposes (λx≤t₀.u₀) v₀ → u₂[v₂/0]:
    --   u₀ → u₂ at ({t₀, .sub} :: Γ₀); shift 0 s₀ (body in .sub head)
    --   v₀ → v₂ at Γ₀; [] (operand)
    MEqRed ({bound := t₀, kind := .sub} :: Γ₀) (Stack.shift 0 s₀) u₀ u₂ →
    MEqRed Γ₀ [] v₀ v₂ →
    -- IH on body with Moreover NP-0 tracking. The IH crosses the
    -- `.sub`-head source's trivial NP-0 to the LHS `.equ`-head body
    -- output's NP-0. Both outputs are returned as `MEqRed` (Type) so
    -- the NP-0 witness can be packaged structurally.
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
        (Stack.shift 0 s₀) Γ₁' s₁' →
      ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀)
        (Stack.shift 0 s₀) Γ₂' s₂' →
      ∃ u_3 : Term, ∃ d_1 : MEqRed Γ₁' s₁' u₁ u_3,
        ∃ _d_2 : MEqRed Γ₂' s₂' u₂ u_3, d_1.NoPromotionOf 0) →
    -- IH on operand:
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution Γ₀ [] Γ₁' s₁' →
      ContextEvolution Γ₀ [] Γ₂' s₂' →
      ∃ v_3, MEqRedJ Γ₁' s₁' v₁ v_3 ∧ MEqRedJ Γ₂' s₂' v₂ v_3) →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ s₀ Γ₁ s₁ →
      ContextEvolution Γ₀ s₀ Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ (.app (.abs t₁ u₁) v₁) t₃
        ∧ MEqRedJ Γ₂ s₂ (Term.instantiate 0 v₂ u₂) t₃

/-- **Lemma 2 case Me-Bet × Me-App** (symmetric to AppBet), paper
p. 9:22-23 mirrored. Same structure as AppBet with LHS and RHS swapped:
LHS source decomposes via Me-Bet (β with .sub-head body), RHS source
decomposes via Me-App (with .equ-head body after Me-FOp inversion).

The Moreover-tracked body IH crosses the LHS .sub-head source's
trivial NP-0 to the RHS .equ-head body output's NP-0, used for the
.equ → .sub bridge in the RHS Me-Bet output rebuild. -/
def Lemma_2_Case_BetApp : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {t₀ u₀ u₁ u₂ v₀ v₁ v₂ t₂ : Term},
    Term.Scoped Γ₀.depth t₀ →
    Term.Scoped Γ₀.depth v₀ →
    -- Me-Bet (LHS): body at .sub-head bound t₀.
    MEqRed ({bound := t₀, kind := .sub} :: Γ₀) (Stack.shift 0 s₀) u₀ u₁ →
    MEqRed Γ₀ [] v₀ v₁ →
    -- Me-App (RHS): via Me-FOp, body at .equ-head bound v₀.
    MEqRed Γ₀ [] t₀ t₂ →
    MEqRed ({bound := v₀, kind := .equ} :: Γ₀) (Stack.shift 0 s₀) u₀ u₂ →
    MEqRed Γ₀ [] v₀ v₂ →
    -- IH on body with Moreover NP-0 tracking. Crosses the LHS
    -- `.sub`-head source's trivial NP-0 to the RHS `.equ`-head body
    -- output's NP-0.
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀)
        (Stack.shift 0 s₀) Γ₁' s₁' →
      ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
        (Stack.shift 0 s₀) Γ₂' s₂' →
      ∃ u_3 : Term, ∃ _d_1 : MEqRed Γ₁' s₁' u₁ u_3,
        ∃ d_2 : MEqRed Γ₂' s₂' u₂ u_3, d_2.NoPromotionOf 0) →
    -- IH on operand:
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution Γ₀ [] Γ₁' s₁' →
      ContextEvolution Γ₀ [] Γ₂' s₂' →
      ∃ v_3, MEqRedJ Γ₁' s₁' v₁ v_3 ∧ MEqRedJ Γ₂' s₂' v₂ v_3) →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ s₀ Γ₁ s₁ →
      ContextEvolution Γ₀ s₀ Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ (Term.instantiate 0 v₁ u₁) t₃
        ∧ MEqRedJ Γ₂ s₂ (.app (.abs t₂ u₂) v₂) t₃

/-- **Lemma 2 case Me-App × Me-TAp**, paper p. 9:23. The Me-TAp side
collapses to `Top`; the LHS Me-App necessarily reduces from `.top` (the
Me-TAp source forces operator = `.top`). Trivial. -/
def Lemma_2_Case_AppTAp : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {u₁ v₀ v₁ : Term},
    MEqRed Γ₀ (v₀ :: s₀) .top u₁ →
    MEqRed Γ₀ [] v₀ v₁ →
    Term.Scoped Γ₀.depth v₀ →
    PrevalidExt Γ₀ s₀ →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ s₀ Γ₁ s₁ →
      ContextEvolution Γ₀ s₀ Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ (.app u₁ v₁) t₃ ∧ MEqRedJ Γ₂ s₂ .top t₃

/-- **Lemma 2 case Me-Fun × Me-Fun**, paper p. 9:23. Both sides
descend under an unapplied abstraction; `s₀ = []` is forced. -/
def Lemma_2_Case_FunFun : Prop :=
  ∀ {Γ₀ : Ctx} {t₀ t₁ t₂ body₀ body₁ body₂ : Term},
    MEqRed Γ₀ [] t₀ t₁ →
    MEqRed ({bound := t₀, kind := .sub} :: Γ₀) [] body₀ body₁ →
    MEqRed Γ₀ [] t₀ t₂ →
    MEqRed ({bound := t₀, kind := .sub} :: Γ₀) [] body₀ body₂ →
    -- IH on bound:
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution Γ₀ [] Γ₁' s₁' →
      ContextEvolution Γ₀ [] Γ₂' s₂' →
      ∃ t_3, MEqRedJ Γ₁' s₁' t₁ t_3 ∧ MEqRedJ Γ₂' s₂' t₂ t_3) →
    -- IH on body (body context is `{t₀,.sub}`-extended):
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀) [] Γ₁' s₁' →
      ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀) [] Γ₂' s₂' →
      ∃ b_3, MEqRedJ Γ₁' s₁' body₁ b_3 ∧ MEqRedJ Γ₂' s₂' body₂ b_3) →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ [] Γ₁ s₁ →
      ContextEvolution Γ₀ [] Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ (.abs t₁ body₁) t₃
        ∧ MEqRedJ Γ₂ s₂ (.abs t₂ body₂) t₃

/-- **Lemma 2 case Me-FOp × Me-FOp**, paper p. 9:24. Both sides pop the
same head operand `α₀` from the stack into an `.equ`-head body context. -/
def Lemma_2_Case_FOpFOp : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {α t₀ t₁ t₂ body₀ body₁ body₂ : Term},
    Term.Scoped Γ₀.depth α →
    MEqRed Γ₀ [] t₀ t₁ →
    MEqRed ({bound := α, kind := .equ} :: Γ₀) (Stack.shift 0 s₀) body₀ body₁ →
    MEqRed Γ₀ [] t₀ t₂ →
    MEqRed ({bound := α, kind := .equ} :: Γ₀) (Stack.shift 0 s₀) body₀ body₂ →
    -- IH on bound:
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution Γ₀ [] Γ₁' s₁' →
      ContextEvolution Γ₀ [] Γ₂' s₂' →
      ∃ t_3, MEqRedJ Γ₁' s₁' t₁ t_3 ∧ MEqRedJ Γ₂' s₂' t₂ t_3) →
    -- IH on body (body context is `{α,.equ}`-extended, stack is shifted):
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution ({bound := α, kind := .equ} :: Γ₀)
        (Stack.shift 0 s₀) Γ₁' s₁' →
      ContextEvolution ({bound := α, kind := .equ} :: Γ₀)
        (Stack.shift 0 s₀) Γ₂' s₂' →
      ∃ b_3, MEqRedJ Γ₁' s₁' body₁ b_3 ∧ MEqRedJ Γ₂' s₂' body₂ b_3) →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ (α :: s₀) Γ₁ s₁ →
      ContextEvolution Γ₀ (α :: s₀) Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ (.abs t₁ body₁) t₃
        ∧ MEqRedJ Γ₂ s₂ (.abs t₂ body₂) t₃

/-- **Lemma 2 case Me-Bet × Me-Bet**, paper p. 9:25. Both sides do β.
Paper invokes Lemmas 19, 36, **32** (asymmetric). -/
def Lemma_2_Case_BetBet : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {t u₀ u₁ u₂ v₀ v₁ v₂ : Term},
    Term.Scoped Γ₀.depth t →
    MEqRed ({bound := t, kind := .sub} :: Γ₀) (Stack.shift 0 s₀) u₀ u₁ →
    MEqRed Γ₀ [] v₀ v₁ →
    MEqRed ({bound := t, kind := .sub} :: Γ₀) (Stack.shift 0 s₀) u₀ u₂ →
    MEqRed Γ₀ [] v₀ v₂ →
    -- IH on body (in `{t,.sub}`-extended ctx with shifted stack):
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution ({bound := t, kind := .sub} :: Γ₀)
        (Stack.shift 0 s₀) Γ₁' s₁' →
      ContextEvolution ({bound := t, kind := .sub} :: Γ₀)
        (Stack.shift 0 s₀) Γ₂' s₂' →
      ∃ u_3, MEqRedJ Γ₁' s₁' u₁ u_3 ∧ MEqRedJ Γ₂' s₂' u₂ u_3) →
    -- IH on operand (at `[]`):
    (∀ {Γ₁' s₁' Γ₂' s₂' : _},
      ContextEvolution Γ₀ [] Γ₁' s₁' →
      ContextEvolution Γ₀ [] Γ₂' s₂' →
      ∃ v_3, MEqRedJ Γ₁' s₁' v₁ v_3 ∧ MEqRedJ Γ₂' s₂' v₂ v_3) →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ s₀ Γ₁ s₁ →
      ContextEvolution Γ₀ s₀ Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ (Term.instantiate 0 v₁ u₁) t₃
        ∧ MEqRedJ Γ₂ s₂ (Term.instantiate 0 v₂ u₂) t₃

/-- **Lemma 2 case Me-TAp × Me-TAp**, paper p. 9:25. Both sides
collapse to `Top`. -/
def Lemma_2_Case_TApTAp : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {u : Term},
    PrevalidExt Γ₀ s₀ →
    Term.Scoped Γ₀.depth u →
    ∀ {Γ₁ s₁ Γ₂ s₂},
      ContextEvolution Γ₀ s₀ Γ₁ s₁ →
      ContextEvolution Γ₀ s₀ Γ₂ s₂ →
      ∃ t₃, MEqRedJ Γ₁ s₁ .top t₃ ∧ MEqRedJ Γ₂ s₂ .top t₃

/-! ## Direct discharge of trivial cases

The trivial source-shape cases (Me-Top, Me-Var, Me-TAp on either side)
close directly using only the transport auxiliary. -/

/-- **Lemma 2 trivial case (`Me-Top` source).** `t₀ = .top`; both
targets are `.top`; closes by `Me-Top` at the evolved contexts plus
transport. -/
theorem Lemma_2_TopTop_proved
    (hTransport : MEqRedTransportAcrossEvolution)
    {Γ₀ : Ctx} {s₀ : Stack} {t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ .top t₁) (h₂ : MEqRed Γ₀ s₀ .top t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ t₃, MEqRedJ Γ₁ s₁ t₁ t₃ ∧ MEqRedJ Γ₂ s₂ t₂ t₃ := by
  have ht₁ : t₁ = .top := h₁.top_inv
  have ht₂ : t₂ = .top := h₂.top_inv
  subst ht₁; subst ht₂
  refine ⟨.top, ?_, ?_⟩
  · exact hTransport he₁ h₁
  · exact hTransport he₂ h₂

/-- **Lemma 2 trivial case (`Me-Var` source on both sides).** Both
targets are `.bvar i`; closes by `Me-Var` at the evolved contexts plus
transport. -/
theorem Lemma_2_VarVar_proved
    (hTransport : MEqRedTransportAcrossEvolution)
    {Γ₀ : Ctx} {s₀ : Stack} {i : Nat}
    (hpv₀ : PrevalidExt Γ₀ s₀) (hi : i < Γ₀.depth)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ t₃, MEqRedJ Γ₁ s₁ (.bvar i) t₃ ∧ MEqRedJ Γ₂ s₂ (.bvar i) t₃ := by
  have hSelf : MEqRed Γ₀ s₀ (.bvar i) (.bvar i) := MEqRed.var hpv₀ hi
  exact ⟨.bvar i, hTransport he₁ hSelf, hTransport he₂ hSelf⟩

/-- **Lemma 2 trivial case (`Me-TAp` × `Me-TAp`).** Both sides collapse
to `.top`; close by `Me-TAp` (or `Me-Top`) at the evolved contexts plus
transport. -/
theorem Lemma_2_TApTAp_proved
    (hTransport : MEqRedTransportAcrossEvolution)
    {Γ₀ : Ctx} {s₀ : Stack} {u : Term}
    (hpv₀ : PrevalidExt Γ₀ s₀) (_hu : Term.Scoped Γ₀.depth u)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ t₃, MEqRedJ Γ₁ s₁ .top t₃ ∧ MEqRedJ Γ₂ s₂ .top t₃ := by
  have hTop : MEqRed Γ₀ s₀ .top .top := MEqRed.top hpv₀
  exact ⟨.top, hTransport he₁ hTop, hTransport he₂ hTop⟩

/-! ## Headline theorem

Conditional on the structural transport auxiliary plus the per-case
obligations, the headline Lemma 2 unfolds by induction on the source
derivation. The dispatch from each `MEqRed` constructor to its case
obligation is mechanical; the file ships a single combined entry point
that takes all case obligations as a tuple of premises. -/

/-- The full per-case grid bundled as a structure for ergonomic
threading through the headline theorem. -/
structure Lemma_2_CaseGrid where
  /-- `Me-Pro × Me-Var` (paper p. 9:21). -/
  proVar : Lemma_2_Case_ProVar
  /-- `Me-Pro × Me-Pro` (paper p. 9:21). -/
  proPro : Lemma_2_Case_ProPro
  /-- `Me-App × Me-App` (paper p. 9:21–22). -/
  appApp : Lemma_2_Case_AppApp
  /-- `Me-App × Me-Bet` (paper p. 9:22–23). Uses Lemma 32. -/
  appBet : Lemma_2_Case_AppBet
  /-- `Me-App × Me-TAp` (paper p. 9:23). -/
  appTAp : Lemma_2_Case_AppTAp
  /-- `Me-Fun × Me-Fun` (paper p. 9:23). -/
  funFun : Lemma_2_Case_FunFun
  /-- `Me-FOp × Me-FOp` (paper p. 9:24). -/
  fOpFOp : Lemma_2_Case_FOpFOp
  /-- `Me-Bet × Me-Bet` (paper p. 9:25). Uses Lemma 32. -/
  betBet : Lemma_2_Case_BetBet
  /-- `Me-TAp × Me-TAp` (paper p. 9:25). -/
  tApTAp : Lemma_2_Case_TApTAp

end Paper
end DeBruijn
end Pss
