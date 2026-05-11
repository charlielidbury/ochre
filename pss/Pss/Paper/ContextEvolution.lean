import Pss.Mpss.DeBruijnReductions

/-! # `Pss.Paper.ContextEvolution` — paper-faithful extended-context reduction

Mechanizes the paper's relation `Γ; s ↣ Γ'; s'` (Pasquale & García-Pérez 2024,
p. 9:7), the *reduction of an extended context*. The paper presents two rules,
`Ct-Ann` and `Ct-Stk`, whose textual forms are:

```
   Γ; s ↣ Γ'; s'   Γ; nil ⊢ t →ᵉᵠᵘ t'                Γ; s ↣ Γ'; s'   Γ; nil ⊢ α →ᵉᵠᵘ α'
   ─────────────────────────────────── Ct-Ann        ───────────────────────────────────── Ct-Stk
   Γ, x ⊲ t; s ↣ Γ', x ⊲ t'; s'                      Γ; α :: s ↣ Γ'; α' :: s'
```

This file is the first paper-mirroring artifact in the codebase
reorganization. It lives beside (not on top of) the de Bruijn working
relation `Pss.DeBruijn.ExtCtxRed` in `Pss.Mpss.DeBruijnContextRed`; both
are kept until the paper-mirroring layer is fully populated. The proofs
of paper lemmas (Lemma 36, ...) are mechanized against THIS relation, so
they textually mirror the paper.

## De Bruijn translation

The paper writes context entries as `x ⊲ t` (an `x ≤ t` *subtype* binding
or `x ≡ t` *equivalence* binding). In de Bruijn there are no names; the
entry's position in the list IS the variable index. We therefore replace
the paper's `Γ, x ⊲ t` with prepending a `CtxEntry { bound := t, kind }`
to `Γ`, where `kind` is `.sub` or `.equ`. The paper's CT-ANN is split
into a single rule that quantifies over the `kind` — both binder forms
follow the same evolution shape.

The paper's `→ᵉᵠᵘ` (empty-stack equivalence reduction) is mechanized as
`MEqRed Γ [] _ _` per `Pss/Mpss/DeBruijnReductions.lean`.

## Implicit base case

The paper text on p. 9:7 gives only Ct-Ann and Ct-Stk. Both rules have
the relation in their premise, so without a base case the relation is
empty. The paper's proofs (e.g. Lemma 36, Lemma 1) routinely use the
relation at `Γ; s ↣ Γ; s` (no change), making clear that the paper
silently assumes a reflexivity case. We mechanize that case explicitly
as `ctRefl`. -- Paper handwaves; mechanized as: explicit `ctRefl` base.
-/

namespace Pss
namespace DeBruijn
namespace Paper

/-- The paper's `Γ; s ↣ Γ'; s'` (reduction of extended context) in de Bruijn
form. Constructors are named after the paper's rules. -/
inductive ContextEvolution : Ctx → Stack → Ctx → Stack → Prop where
  /-- Reflexivity. The paper does not give this rule a name but its proofs
  rely on it; see the file docstring's "Implicit base case" note. -/
  | ctRefl {Γ : Ctx} {s : Stack} :
      ContextEvolution Γ s Γ s

  /-- **Ct-Ann** (paper p. 9:7). Reduce the bound of the innermost binding,
  preserving the binder kind. The paper writes `Γ, x ⊲ t` for either a
  subtype or equivalence binding; in de Bruijn both shapes prepend a
  `CtxEntry`, so we quantify over `kind`.

  **De Bruijn shift on the stack** — the inner stack `s` lives at
  `Γ.depth`; when we add a new innermost entry, every existing index
  in the stack shifts up by one to refer to the same binder. The paper
  formulation hides this because named binders are stable under
  context extension; the de Bruijn formulation has to make the shift
  explicit. -- Paper handwaves; mechanized as: shifted stack on both
  sides of the Ct-Ann conclusion. -/
  | ctAnn {Γ Γ' : Ctx} {s s' : Stack} {t t' : Term}
      {kind : CtxEntryKind} :
      ContextEvolution Γ s Γ' s' →
      MEqRed Γ [] t t' →
      ContextEvolution
        ({ bound := t,  kind } :: Γ) (Stack.shift 0 s)
        ({ bound := t', kind } :: Γ') (Stack.shift 0 s')

  /-- **Ct-Stk** (paper p. 9:7). Reduce the head stack annotation. -/
  | ctStk {Γ Γ' : Ctx} {s s' : Stack} {α α' : Term} :
      ContextEvolution Γ s Γ' s' →
      MEqRed Γ [] α α' →
      ContextEvolution Γ (α :: s) Γ' (α' :: s')

  /-- **Body-context lift** (paper-implicit). The body cases of paper
  Lemma 2 (`Me-Fun`, `Me-FOp`, `Me-Bet`, `Me-App × Me-Bet`, etc.) need to
  lift an outer evolution `Γ; s ↣ Γ'; s'` to the body context's
  evolution `(entry :: Γ); shift 0 s ↣ (entry :: Γ'); shift 0 s'`. The
  paper uses this implicitly when invoking weakening (Lemma 19) under a
  binder; the de Bruijn mechanization makes it an explicit constructor
  so that inductions and discharges of the body cases close without
  needing a separate `cons_lift` walk over the underlying derivation.
  The same `entry` is added to BOTH sides, preserving all evolution
  invariants. The scoping witness for the bound at `Γ.depth` (= `Γ'.depth`
  by `preserves_ctx_depth`) ensures we can rebuild prevalidity of the
  new heads on both sides. -- Paper handwaves; mechanized as: explicit
  `cons_lift` constructor.
  -/
  | cons_lift {Γ Γ' : Ctx} {s s' : Stack} {entry : CtxEntry} :
      ContextEvolution Γ s Γ' s' →
      Term.Scoped Γ.depth entry.bound →
      ContextEvolution
        (entry :: Γ) (Stack.shift 0 s)
        (entry :: Γ') (Stack.shift 0 s')

namespace ContextEvolution

/-- Alias for `ContextEvolution.ctAnn` — the old `cons_evolve` constructor
was identical to `ctAnn` after the de Bruijn-faithful stack-shift fix.
Provided for backward compatibility with downstream callers. -/
@[reducible] def cons_evolve {Γ Γ' : Ctx} {s s' : Stack} {t t' : Term}
    {kind : CtxEntryKind}
    (h : ContextEvolution Γ s Γ' s') (hbound : MEqRed Γ [] t t') :
    ContextEvolution ({ bound := t, kind } :: Γ) (Stack.shift 0 s)
      ({ bound := t', kind } :: Γ') (Stack.shift 0 s') :=
  ContextEvolution.ctAnn h hbound

/-! ## Basic structural invariants -/

/-- Stack length is preserved by `ContextEvolution`. -/
theorem preserves_stack_length {Γ Γ' : Ctx} {s s' : Stack}
    (h : ContextEvolution Γ s Γ' s') : s.length = s'.length := by
  induction h with
  | ctRefl => rfl
  | ctAnn _ _ ih =>
      simp [Stack.shift, Stack.shiftBy, List.length_map, ih]
  | ctStk _ _ ih => simp [ih]
  | cons_lift _ _ ih =>
      simp [Stack.shift, Stack.shiftBy, List.length_map, ih]

/-- Context depth is preserved by `ContextEvolution`. -/
theorem preserves_ctx_depth {Γ Γ' : Ctx} {s s' : Stack}
    (h : ContextEvolution Γ s Γ' s') : Γ.depth = Γ'.depth := by
  induction h with
  | ctRefl => rfl
  | ctAnn _ _ ih =>
      simp [Ctx.depth_cons, ih]
  | ctStk _ _ ih => exact ih
  | cons_lift _ _ ih =>
      simp [Ctx.depth_cons, ih]

end ContextEvolution

end Paper
end DeBruijn
end Pss
