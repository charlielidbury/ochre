import Pss.Mpss.Reductions
import Mathlib.Logic.Relation

/-! # `Pss.Mpss.ContextRed` — extended-context reduction `Γ; s ↣ Γ'; s'`

Pasquale & García-Pérez 2024 (CSL 2026), §3, Figure 3 (the figure that
introduces the relation just before Lemma 1).

This relation captures "how the ambient extended context `Γ; s` evolves
during a single MPSS reduction step on the term being reduced". Two
structural rules:

* **Ct-Ann**: an annotation in `Γ` (the bound `t` of an `x ◁ t` entry,
  for `◁ ∈ {≤, ≡}`) reduces by an equivalence step on the empty stack;
  the rest of the context-and-stack reduces in lockstep.

  Paper:  `Γ; s ↣ Γ'; s'      Γ; nil ⊢ t ⟶^≡ t'`
          ─────────────────────────────────────  Ct-Ann
          `Γ, x ◁ t; s ↣ Γ', x ◁ t'; s'`

* **Ct-Stk**: the topmost element of the stack reduces by an equivalence
  step on the empty stack; the underlying `Γ; s` reduces in lockstep.

  Paper:  `Γ; s ↣ Γ'; s'      Γ; nil ⊢ α ⟶^≡ α'`
          ─────────────────────────────────────  Ct-Stk
          `Γ; α :: s ↣ Γ'; α' :: s'`

The paper's Figure 3 only shows these two rules, but the recursive
premise `Γ; s ↣ Γ'; s'` in both rules requires a **base case**. We
add an explicit reflexive base `refl : Γ; s ↣ Γ; s`. This matches the
paper's usage in proofs (e.g. line 1577 of the appendix: "By rule Ct-Ann,
we have `Γ, x ≤ t0; nil ↣ Γ', x ≤ t1; nil` from `Γ; nil ⊢ t0 ⟶^≡ t1`"
— here the inner `Γ; nil ↣ Γ'; nil` is taken as already established
elsewhere, and the smallest derivation from no input is precisely
reflexivity).

## Notational note

The paper writes `Γ, x ◁ t` for "extend with new innermost binding";
under our list-head-is-innermost convention this becomes
`⟨x, t, k⟩ :: Γ` for `k ∈ {.sub, .equ}`. Hence `Ct-Ann` operates on the
**head** of the context (innermost binding). The paper's "multiple use of
Ct-Ann" idiom — used to reduce annotations at arbitrary positions in
`Γ` — is then expressed by iterating over the spine (one `annSub` /
`annEqu` per layer of the context, on top of a chain of `refl` and the
two rules).

## Lemma 36

The headline lemma proved here (paper, appendix p.~31):

> If `Γ; s ↣ Γ'; s'` then `Γ; nil ↣ Γ'; nil`.

Used ~10× in the appendix to "strip" stack steps off a context-reduction
witness so the underlying logical-context reduction can be exploited.
The paper's proof is by induction on `s`. Mechanized below.
-/

namespace Pss

/-- Extended-context reduction `Γ; s ↣ Γ'; s'`.
Pasquale & García-Pérez 2024 §3, Figure 3.

The annotation/stack-element steps in Ct-Ann/Ct-Stk are MPSS equivalence
reductions on the empty stack (`MEqRed Γ [] _ _`). The paper writes
`Γ; nil ⊢ _ ⟶^≡ _` for these.

The recursive premise `Γ; s ↣ Γ'; s'` of Ct-Ann/Ct-Stk requires a base
case; we use reflexivity (`refl`).
-/
inductive ExtCtxRed : Ctx → Stack → Ctx → Stack → Prop where
  /-- Reflexive base case (implicit in the paper's figure but used by
  every proof that combines Ct-Ann/Ct-Stk with a starting state). -/
  | refl {Γ : Ctx} {s : Stack} :
      ExtCtxRed Γ s Γ s

  /-- **Ct-Ann**: an annotation in the innermost (head) entry of `Γ`
  reduces by `⟶^≡` on the empty stack, while the underlying `Γ; s` also
  reduces by `↣`. The kind `◁` (sub or equ) is preserved.

  Paper rule (with `◁ ∈ {≤, ≡}`):
      `Γ; s ↣ Γ'; s'      Γ; nil ⊢ t ⟶^≡ t'`
      ─────────────────────────────────────
      `Γ, x ◁ t; s ↣ Γ', x ◁ t'; s'`
  -/
  | ann {Γ Γ' : Ctx} {s s' : Stack} {x : String} {t t' : Term}
        {k : CtxEntryKind} :
      ExtCtxRed Γ s Γ' s' →
      MEqRed Γ [] t t' →
      ExtCtxRed (⟨x, t, k⟩ :: Γ) s (⟨x, t', k⟩ :: Γ') s'

  /-- **Ct-Stk**: the topmost element of the stack reduces by `⟶^≡` on
  the empty stack, while the underlying `Γ; s` also reduces by `↣`.

  Paper rule:
      `Γ; s ↣ Γ'; s'      Γ; nil ⊢ α ⟶^≡ α'`
      ─────────────────────────────────────
      `Γ; α :: s ↣ Γ'; α' :: s'`
  -/
  | stk {Γ Γ' : Ctx} {s s' : Stack} {α α' : Term} :
      ExtCtxRed Γ s Γ' s' →
      MEqRed Γ [] α α' →
      ExtCtxRed Γ (α :: s) Γ' (α' :: s')

@[inherit_doc] notation:50 Γ " ;ₘ " s " ↣ " Γ' " ;ₘ " s' =>
  ExtCtxRed Γ s Γ' s'

/-- The four-place `ExtCtxRed` repackaged as a binary relation on `ExtCtx`,
so we can apply Mathlib's `Relation.ReflTransGen` directly. -/
abbrev ExtCtxRed' (E E' : ExtCtx) : Prop :=
  ExtCtxRed E.1 E.2 E'.1 E'.2

/-- Many-step extended-context reduction `Γ; s ↣* Γ'; s'`, defined as the
reflexive-transitive closure of the four-place `ExtCtxRed`, packaged as a
binary relation on `ExtCtx = Ctx × Stack`. -/
abbrev ExtCtxRedStar : ExtCtx → ExtCtx → Prop :=
  Relation.ReflTransGen ExtCtxRed'

@[inherit_doc] notation:50 Γ " ;ₘ " s " ↣* " Γ' " ;ₘ " s' =>
  ExtCtxRedStar (Γ, s) (Γ', s')

namespace ExtCtxRed

/-! ## Basic structural lemmas

These don't appear named in the paper but are mechanical sanity checks
that downstream agents can rely on. -/

/-- The lengths of the two contexts agree. (`refl` is length-preserving;
`ann` adds one binding to each side; `stk` doesn't touch the contexts.) -/
theorem preserves_ctx_length {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : Γ.length = Γ'.length := by
  induction h with
  | refl => rfl
  | ann _ _ ih => simp [ih]
  | stk _ _ ih => exact ih

/-- The lengths of the two stacks agree. -/
theorem preserves_stack_length {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : s.length = s'.length := by
  induction h with
  | refl => rfl
  | ann _ _ ih => exact ih
  | stk _ _ ih => simp [ih]

/-- The names in the two contexts agree pointwise. (`refl` and `stk` are
trivial; `ann` preserves the head name.) -/
theorem preserves_dom {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : Γ.dom = Γ'.dom := by
  induction h with
  | refl => rfl
  | ann _ _ ih => simp [Ctx.dom_cons, ih]
  | stk _ _ ih => exact ih

/-- The kinds at corresponding positions agree. (`refl` is trivial;
`ann` preserves the kind on the new head; `stk` doesn't touch the
contexts.) -/
theorem preserves_kinds {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') :
    (Γ.map (·.kind)) = (Γ'.map (·.kind)) := by
  induction h with
  | refl => rfl
  | ann _ _ ih => simp [ih]
  | stk _ _ ih => exact ih

/-! ## Lemma 36 (Commutativity — context weakening)

> Pasquale & García-Pérez 2024 Lemma 36 (appendix). Let `Γ; s` and `Γ'; s'`
> be extended contexts such that `Γ; s ↣ Γ'; s'`. Then `Γ; nil ↣ Γ'; nil`.

The paper's proof is by induction on `s`. We follow it almost verbatim,
strengthening the statement to `∃ s', s' agrees with s in length` so the
inductive structure on `s` works cleanly. The cleanest mechanization,
however, is by induction on the derivation of `↣` itself: each Ct-Stk
step strips one element from BOTH stacks; Ct-Ann preserves the stack;
`refl` is trivial. We collapse the proof in the latter style.
-/

/-- **Lemma 36** (Pasquale & García-Pérez 2024). If `Γ; s ↣ Γ'; s'`,
then the underlying `Γ; nil ↣ Γ'; nil` also holds.

Used pervasively in the appendix proofs (Lemma 1, Theorem 3) to "strip"
the stack from a context-reduction witness so the underlying logical
context reduction can be exploited.
-/
theorem lemma_36 {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : ExtCtxRed Γ [] Γ' [] := by
  induction h with
  | refl => exact .refl
  | @ann Γ Γ' s s' x t t' k hΓ ht ih =>
      -- ih : Γ; nil ↣ Γ'; nil. Re-apply Ct-Ann with the same annotation
      -- step on the empty stack; the result is Γ, x ◁ t; nil ↣ Γ', x ◁ t'; nil.
      exact .ann ih ht
  | stk _ _ ih =>
      -- The Ct-Stk step adds one operand to each stack; the underlying
      -- Γ; s ↣ Γ'; s' was already nil-ified by the IH.
      exact ih

/-! ## A few derived helpers

Light-weight constructors / inversion principles to make Wave 5/6 proofs
more pleasant. -/

/-- A single Ct-Stk step lifts to many-step reduction. -/
theorem stk_star {Γ Γ' : Ctx} {s s' : Stack} {α α' : Term}
    (h : ExtCtxRed Γ s Γ' s') (hα : MEqRed Γ [] α α') :
    ExtCtxRed Γ (α :: s) Γ' (α' :: s') :=
  .stk h hα

/-- A single Ct-Ann step lifts to many-step reduction. -/
theorem ann_star {Γ Γ' : Ctx} {s s' : Stack} {x : String} {t t' : Term}
    {k : CtxEntryKind}
    (h : ExtCtxRed Γ s Γ' s') (ht : MEqRed Γ [] t t') :
    ExtCtxRed (⟨x, t, k⟩ :: Γ) s (⟨x, t', k⟩ :: Γ') s' :=
  .ann h ht

/-- ExtCtxRed' on `(Γ, s) → (Γ', s')` matches the four-place relation. -/
@[simp] theorem extCtxRed'_iff {Γ Γ' : Ctx} {s s' : Stack} :
    ExtCtxRed' (Γ, s) (Γ', s') ↔ ExtCtxRed Γ s Γ' s' := Iff.rfl

/-- Lift a single step to its reflexive-transitive closure. -/
theorem to_star {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : ExtCtxRedStar (Γ, s) (Γ', s') :=
  Relation.ReflTransGen.single h

end ExtCtxRed

end Pss
