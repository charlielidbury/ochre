import Pss.Mpss.DeBruijnReductions
import Mathlib.Logic.Relation

/-! # `Pss.Mpss.DeBruijnContextRed` — de Bruijn extended-context reduction

This module ports the MPSS extended-context reduction relation `Γ; s ↣ Γ'; s'`
to the de Bruijn refactor. It mirrors `Pss.Mpss.ContextRed`, but context
annotations are nameless `CtxEntry` bounds and binder positions are represented
by list indices rather than variable names.
-/

namespace Pss
namespace DeBruijn

/-- De Bruijn extended-context reduction.

`ann` reduces the bound of the innermost context entry, preserving its binding
kind. `stk` reduces the head stack operand. Both annotation and stack steps use
empty-stack equivalence reduction, as in the paper's `Ct-Ann` / `Ct-Stk`
rules. The explicit `refl` base matches the locally-nameless formalization and
the paper's recursive use of the relation.
-/
inductive ExtCtxRed : Ctx → Stack → Ctx → Stack → Prop where
  /-- Reflexive base case. -/
  | refl {Γ : Ctx} {s : Stack} :
      ExtCtxRed Γ s Γ s

  /-- **Ct-Ann** for the nameless innermost context entry. -/
  | ann {Γ Γ' : Ctx} {s s' : Stack} {t t' : Term}
      {kind : CtxEntryKind} :
      ExtCtxRed Γ s Γ' s' →
      MEqRed Γ [] t t' →
      ExtCtxRed ({ bound := t, kind } :: Γ) s
        ({ bound := t', kind } :: Γ') s'

  /-- **Ct-Stk** for the stack head. -/
  | stk {Γ Γ' : Ctx} {s s' : Stack} {α α' : Term} :
      ExtCtxRed Γ s Γ' s' →
      MEqRed Γ [] α α' →
      ExtCtxRed Γ (α :: s) Γ' (α' :: s')

/-- The four-place de Bruijn context reduction as a binary relation on
extended contexts. -/
abbrev ExtCtxRedRel (E E' : ExtCtx) : Prop :=
  ExtCtxRed E.1 E.2 E'.1 E'.2

/-- Reflexive-transitive closure of de Bruijn extended-context reduction. -/
abbrev ExtCtxRedStar : ExtCtx → ExtCtx → Prop :=
  Relation.ReflTransGen ExtCtxRedRel

namespace ExtCtxRed

/-! ## Structural invariants -/

/-- De Bruijn extended-context reduction preserves context depth. -/
theorem preserves_ctx_depth {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : Γ.depth = Γ'.depth := by
  induction h with
  | refl => rfl
  | ann _ _ ih =>
      simpa [Ctx.depth] using congrArg Nat.succ (by
        simpa [Ctx.depth] using ih)
  | stk _ _ ih => exact ih

/-- De Bruijn extended-context reduction preserves stack length. -/
theorem preserves_stack_length {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : s.length = s'.length := by
  induction h with
  | refl => rfl
  | ann _ _ ih => exact ih
  | stk _ _ ih => simp [ih]

/-- De Bruijn extended-context reduction preserves context-entry kinds. -/
theorem preserves_kinds {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') :
    Γ.map (·.kind) = Γ'.map (·.kind) := by
  induction h with
  | refl => rfl
  | ann _ _ ih => simp [ih]
  | stk _ _ ih => exact ih

/-! ## Lemma 36 -/

/-- De Bruijn form of MPSS Lemma 36: stack changes can be stripped from a
single extended-context reduction, leaving the underlying empty-stack context
reduction. -/
theorem lemma_36 {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : ExtCtxRed Γ [] Γ' [] := by
  induction h with
  | refl => exact .refl
  | ann _ hred ih => exact .ann ih hred
  | stk _ _ ih => exact ih

/-! ## Derived helpers -/

/-- A single de Bruijn extended-context reduction embeds into its
reflexive-transitive closure. -/
theorem to_star {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') :
    ExtCtxRedStar (Γ, s) (Γ', s') :=
  Relation.ReflTransGen.single h

/-- Constructor alias for one de Bruijn `Ct-Ann` step. -/
theorem ann_step {Γ Γ' : Ctx} {s s' : Stack} {t t' : Term}
    {kind : CtxEntryKind}
    (h : ExtCtxRed Γ s Γ' s') (hred : MEqRed Γ [] t t') :
    ExtCtxRed ({ bound := t, kind } :: Γ) s
      ({ bound := t', kind } :: Γ') s' :=
  .ann h hred

/-- Constructor alias for one de Bruijn `Ct-Stk` step. -/
theorem stk_step {Γ Γ' : Ctx} {s s' : Stack} {α α' : Term}
    (h : ExtCtxRed Γ s Γ' s') (hred : MEqRed Γ [] α α') :
    ExtCtxRed Γ (α :: s) Γ' (α' :: s') :=
  .stk h hred

end ExtCtxRed

end DeBruijn
end Pss
