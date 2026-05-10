import Pss.Paper.ContextEvolution

/-! # `Pss.Paper.Aux.EvolutionTransport` — `ContextEvolution` preservation

This file ships the **paper-faithful preservation lemmas** for
`ContextEvolution` (Pasquale & García-Pérez 2024 `Γ; s ↣ Γ'; s'`,
p. 9:7) and uses them to discharge the **trivial cells of Lemma 2**
unconditionally:

* `Lemma_2_TopTop_proved_unconditional`
* `Lemma_2_VarVar_proved_unconditional`
* `Lemma_2_TApTAp_proved_unconditional`

The unconditional cells supersede the wrapper-style cells in
`Pss.Paper.Lemma_2_Diamond` (which were conditional on a structural
auxiliary `MEqRedTransportAcrossEvolution`).

## Why the original `MEqRedTransportAcrossEvolution` is structurally
circular — the dispatch's load-bearing finding

The auxiliary's claim was:

> `ContextEvolution Γ s Γ' s' → MEqRed Γ s u v → MEqRedJ Γ' s' u v`

(same `u`, same `v`, only the context evolves). This auxiliary is
**circular**: its `Me-Pro` case requires Lemma 2 itself, the very
diamond we are trying to prove. To see this, take a `Me-Pro` source
derivation `MEqRed (.equ α₀ :: tailΓ) s (.bvar 0) v` whose body
sub-derivation is `MEqRed (.equ α₀ :: tailΓ) s (Term.shift 0 α₀) v`.
The whole context evolves via `Ct-Ann`: `(.equ α₀ :: tailΓ); s ↣
(.equ α₁ :: tailΓ'); s'` with `α₀ →ᵉᵠᵘ α₁`.

To rebuild a `Me-Pro` at the evolved context yielding the SAME `v`,
we need a body derivation `MEqRed (.equ α₁ :: tailΓ') s' (Term.shift 0
α₁) v`. By the inductive hypothesis on the body we obtain
`MEqRedJ (.equ α₁ :: tailΓ') s' (Term.shift 0 α₀) v`, and from
`Ct-Ann` plus weakening (Lemma 19) we obtain `MEqRed (.equ α₁ ::
tailΓ') s' (Term.shift 0 α₀) (Term.shift 0 α₁)`. Closing this fork —
two reducts of `Term.shift 0 α₀` rejoining at `v` — is precisely the
diamond claim. The auxiliary cannot be discharged without a prior
diamond; it cannot be a *standalone* premise of Lemma 2.

The paper does NOT use such a transport. Reading p. 9:21 carefully:
the paper's `Me-Pro × Me-Var` case uses **Lemma 36** to reduce the
non-empty stack `↣` to its empty-stack `nil` projection, then
**Lemma 19 (weakening)** to lift the bound's reduction across the
new heads of the evolved context, and finally invokes the **inductive
hypothesis on the bound's reduction** (a strictly smaller `MEqRed`
derivation) to obtain a common reduct. Nowhere does the paper need a
transport that preserves both endpoints across an evolution.

## What the trivial cells actually need

The paper-faithful tools needed at the trivial cells are far weaker:

1. **`Nonempty PrevalidExt` is preserved across `↣`.** Each `Ct-Ann`
   / `Ct-Stk` step exhibits, via the `MEqRed Γ [] _ _` hypothesis on
   the new bound, a scopedness witness for the new entry; combined
   with the head-replacement helpers in `Pss.Context.DeBruijn` this
   suffices to rebuild the new prevalidity.
2. **Context depth is preserved across `↣`** (already shipped in
   `Pss.Paper.ContextEvolution.preserves_ctx_depth`).

Note that since `ContextEvolution` is `Prop`-valued and `PrevalidExt`
is `Type`-valued, the preservation must produce
`Nonempty (PrevalidExt Γ' s')` and the trivial cells extract via
`Classical.choice` (already in the codebase's axiom basis).

With these two, the trivial cells re-derive `Me-Top` / `Me-Var` /
`Me-TAp` directly at the evolved `Γ'; s'` — no transport needed.

## Paper handwave note

> -- Paper handwaves: the paper text describes Lemma 2's trivial
>    bottom-left subcases simply as "the lemma holds by using the rule
>    Me-Top (respectively Me-Var) for the missing edges" (p. 9:21,
>    base case paragraph). The de Bruijn mechanization here uses
>    `ContextEvolution.preservesNonemptyPrevalidExt` to obtain the
>    scoping premise needed to instantiate the rebuild.

-/

namespace Pss
namespace DeBruijn
namespace Paper

namespace ContextEvolution

/-! ## Auxiliary: `Stack.Scoped` is preserved across `↣` at any depth
≥ `Γ.depth`

The induction on `ContextEvolution` keeps `s'` scoped at the same
depth as `s` because each `ctStk` step replaces a stack head α by α'
with `α' →ᵉᵠᵘ` evidence (Type-erased to scopedness via
`MEqRed.scoped_right`), and the contexts have equal depth (preserved). -/
private theorem stack_scoped_preserved_at
    {Γ Γ' : Ctx} {s s' : Stack}
    (h : ContextEvolution Γ s Γ' s')
    {n : Nat} (hn : Γ.depth ≤ n) :
    Nonempty (Stack.Scoped n s) → Nonempty (Stack.Scoped n s') := by
  intro hs
  induction h with
  | @ctRefl Γp sp => exact hs
  | @ctAnn Γp Γp' sp sp' t t' kind h_evol _ ih =>
      -- ctAnn doesn't touch the stack; the underlying evolution Γp;sp ↣
      -- Γp';sp' transports sp into sp' and we recurse with the same `n`.
      -- The cons-context's depth is `Γp.depth + 1`, but the stack is
      -- still scoped at the wider `n`; we pass the WEAKER bound via
      -- `Nat.le_of_succ_le` after `Ctx.depth_cons` simplification.
      have hnTail : Γp.depth ≤ n := Nat.le_of_succ_le (by
        simpa [Ctx.depth_cons] using hn)
      exact ih hnTail hs
  | @ctStk Γp Γp' sp sp' α α' h_evol hα_red ih =>
      let hs₀ : Stack.Scoped n (α :: sp) := Classical.choice hs
      cases hs₀ with
      | cons hαScoped hRestScoped =>
          have hRestScoped' : Nonempty (Stack.Scoped n sp') :=
            ih hn ⟨hRestScoped⟩
          let hRestScoped'₀ : Stack.Scoped n sp' :=
            Classical.choice hRestScoped'
          have hα'_at_Γp : Term.Scoped Γp.depth α' := hα_red.scoped_right
          have hα'_at_n : Term.Scoped n α' :=
            Term.scoped_mono hn hα'_at_Γp
          exact ⟨Stack.Scoped.cons hα'_at_n hRestScoped'₀⟩

/-! ## `Prevalid` and `PrevalidExt` preservation across `↣`

Both `Prevalid` and `PrevalidExt` are `Type`-valued in this codebase,
while `ContextEvolution` is `Prop`-valued. The preservations therefore
target `Nonempty` wrappers; downstream callers can extract via
`Classical.choice` (already in this codebase's axiom basis). -/

/-- `ContextEvolution` preserves logical-context prevalidity (existence
form). Proof is induction on the evolution. -/
theorem preservesNonemptyPrevalid {Γ Γ' : Ctx} {s s' : Stack}
    (h : ContextEvolution Γ s Γ' s') (hpv : Nonempty (Prevalid Γ)) :
    Nonempty (Prevalid Γ') := by
  induction h with
  | @ctRefl Γp sp => exact hpv
  | @ctAnn Γp Γp' sp sp' t t' kind h_evol hbound ih =>
      let hpv₀ : Prevalid Γp := Prevalid.tail (Classical.choice hpv)
      have hpvTail' : Nonempty (Prevalid Γp') := ih ⟨hpv₀⟩
      have hpv₀' : Prevalid Γp' := Classical.choice hpvTail'
      have ht'_at_Γp : Term.Scoped Γp.depth t' := hbound.scoped_right
      have hdepth : Γp.depth = Γp'.depth :=
        preserves_ctx_depth h_evol
      have ht'_at_Γp' : Term.Scoped Γp'.depth t' := by
        rw [← hdepth]; exact ht'_at_Γp
      cases kind with
      | sub => exact ⟨Prevalid.sub hpv₀' ht'_at_Γp'⟩
      | equ => exact ⟨Prevalid.equ hpv₀' ht'_at_Γp'⟩
  | @ctStk Γp Γp' sp sp' α α' _ _ ih =>
      exact ih hpv

/-- `ContextEvolution` preserves extended-context prevalidity (existence
form). Decomposes `PrevalidExt` into `Prevalid Γ` plus
`Stack.Scoped Γ.depth s`, transports each piece via
`preservesNonemptyPrevalid` and `stack_scoped_preserved_at`, then
recombines via `PrevalidExt.of_stack_scoped`. -/
theorem preservesNonemptyPrevalidExt {Γ Γ' : Ctx} {s s' : Stack}
    (h : ContextEvolution Γ s Γ' s')
    (hpvE : Nonempty (PrevalidExt Γ s)) :
    Nonempty (PrevalidExt Γ' s') := by
  let hpvE₀ : PrevalidExt Γ s := Classical.choice hpvE
  -- Logical-context piece:
  have hpvCtx' : Nonempty (Prevalid Γ') :=
    preservesNonemptyPrevalid h ⟨PrevalidExt.ctx hpvE₀⟩
  let hpvCtx'₀ : Prevalid Γ' := Classical.choice hpvCtx'
  -- Stack scopedness piece (at Γ.depth, lifted to Γ'.depth = Γ.depth):
  have hsScoped : Stack.Scoped Γ.depth s :=
    PrevalidExt.stack_scoped hpvE₀
  have hsScoped'_ne : Nonempty (Stack.Scoped Γ.depth s') :=
    stack_scoped_preserved_at h (Nat.le_refl _) ⟨hsScoped⟩
  let hsScoped'₀ : Stack.Scoped Γ.depth s' := Classical.choice hsScoped'_ne
  have hdepth : Γ.depth = Γ'.depth := preserves_ctx_depth h
  have hsScoped'' : Stack.Scoped Γ'.depth s' := by
    rw [← hdepth]; exact hsScoped'₀
  exact ⟨PrevalidExt.of_stack_scoped hpvCtx'₀ hsScoped''⟩

end ContextEvolution

/-! ## Unconditional discharge of Lemma 2's trivial cells

These three theorems supersede the conditional `_proved` versions in
`Pss.Paper.Lemma_2_Diamond` (which depended on
`MEqRedTransportAcrossEvolution`). They use only
`ContextEvolution.preservesNonemptyPrevalidExt` and
`preserves_ctx_depth`.
-/

/-- **Lemma 2 trivial case (`Me-Top` source), unconditional.**

Paper p. 9:21 base case: when the source LHS is `.top`, both reducts
must be `.top` (by `MEqRed.top_inv`), and the diagonal closes by
`Me-Top` rebuilt at the evolved contexts. -/
theorem Lemma_2_TopTop_proved_unconditional
    {Γ₀ : Ctx} {s₀ : Stack} {t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ .top t₁) (h₂ : MEqRed Γ₀ s₀ .top t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ t₃, MEqRedJ Γ₁ s₁ t₁ t₃ ∧ MEqRedJ Γ₂ s₂ t₂ t₃ := by
  have ht₁ : t₁ = .top := h₁.top_inv
  have ht₂ : t₂ = .top := h₂.top_inv
  subst ht₁; subst ht₂
  have hpvE₀ : PrevalidExt Γ₀ s₀ := h₁.prevalidExt
  have hpvE₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpvE₀⟩)
  have hpvE₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpvE₀⟩)
  exact ⟨.top, ⟨MEqRed.top hpvE₁⟩, ⟨MEqRed.top hpvE₂⟩⟩

/-- **Lemma 2 trivial case (`Me-Var` source on both sides), unconditional.**

Paper p. 9:21 base case: when both sides are `Me-Var`, both reducts
are `.bvar i`, and the diagonal closes by `Me-Var` rebuilt at the
evolved contexts. -/
theorem Lemma_2_VarVar_proved_unconditional
    {Γ₀ : Ctx} {s₀ : Stack} {i : Nat}
    (hpv₀ : PrevalidExt Γ₀ s₀) (hi : i < Γ₀.depth)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ t₃, MEqRedJ Γ₁ s₁ (.bvar i) t₃ ∧ MEqRedJ Γ₂ s₂ (.bvar i) t₃ := by
  have hpvE₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  have hpvE₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  have hi₁ : i < Γ₁.depth := by
    rw [← ContextEvolution.preserves_ctx_depth he₁]; exact hi
  have hi₂ : i < Γ₂.depth := by
    rw [← ContextEvolution.preserves_ctx_depth he₂]; exact hi
  exact ⟨.bvar i,
    ⟨MEqRed.var hpvE₁ hi₁⟩,
    ⟨MEqRed.var hpvE₂ hi₂⟩⟩

/-- **Lemma 2 trivial case (`Me-TAp` × `Me-TAp`), unconditional.**

Paper p. 9:25 trivial case: both sides collapse to `.top`, the diagonal
closes by `Me-Top` rebuilt at the evolved contexts. -/
theorem Lemma_2_TApTAp_proved_unconditional
    {Γ₀ : Ctx} {s₀ : Stack} {u : Term}
    (hpv₀ : PrevalidExt Γ₀ s₀) (_hu : Term.Scoped Γ₀.depth u)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ t₃, MEqRedJ Γ₁ s₁ .top t₃ ∧ MEqRedJ Γ₂ s₂ .top t₃ := by
  have hpvE₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  have hpvE₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  exact ⟨.top, ⟨MEqRed.top hpvE₁⟩, ⟨MEqRed.top hpvE₂⟩⟩

end Paper
end DeBruijn
end Pss
