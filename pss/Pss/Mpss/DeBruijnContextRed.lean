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

/-! ## Prevalidity invariants -/

/-- De Bruijn extended-context reduction preserves logical-context
prevalidity from left to right. This intentionally tracks only the logical
context: under `Ct-Ann`, the recursive stack belongs to the annotation tail,
while the conclusion lives under the re-added head. -/
theorem prevalid_ctx_right_nonempty {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : Nonempty (Prevalid Γ → Prevalid Γ') := by
  induction h with
  | refl =>
      exact ⟨fun hpv => hpv⟩
  | @ann Γ Γ' s s' t t' kind hInner hred ih =>
      exact ⟨fun hpv =>
        have hTail : Prevalid Γ := Prevalid.tail hpv
        have hTargetCtx : Prevalid Γ' := ih.some hTail
        have hScopedTarget : Term.Scoped Γ'.depth t' := by
          simpa [← hInner.preserves_ctx_depth] using hred.scoped_right
        match kind with
        | .sub => Prevalid.sub hTargetCtx hScopedTarget
        | .equ => Prevalid.equ hTargetCtx hScopedTarget⟩
  | stk _ _ ih =>
      exact ih

/-- De Bruijn extended-context reduction preserves logical-context
prevalidity from left to right. -/
noncomputable def prevalid_ctx_right {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') : Prevalid Γ → Prevalid Γ' :=
  h.prevalid_ctx_right_nonempty.some

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

namespace ExtCtxRedStar

/-! ## Star helpers -/

/-- Reflexivity of de Bruijn extended-context reduction stars. -/
theorem refl {Γ : Ctx} {s : Stack} : ExtCtxRedStar (Γ, s) (Γ, s) :=
  Relation.ReflTransGen.refl

/-- A single de Bruijn extended-context reduction as a star. -/
theorem single {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRed Γ s Γ' s') :
    ExtCtxRedStar (Γ, s) (Γ', s') :=
  ExtCtxRed.to_star h

/-- Transitivity of de Bruijn extended-context reduction stars. -/
theorem trans {Γ₁ Γ₂ Γ₃ : Ctx} {s₁ s₂ s₃ : Stack}
    (h₁ : ExtCtxRedStar (Γ₁, s₁) (Γ₂, s₂))
    (h₂ : ExtCtxRedStar (Γ₂, s₂) (Γ₃, s₃)) :
    ExtCtxRedStar (Γ₁, s₁) (Γ₃, s₃) :=
  Relation.ReflTransGen.trans h₁ h₂

/-! ## Star structural invariants -/

/-- De Bruijn extended-context reduction stars preserve context depth. -/
theorem preserves_ctx_depth {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRedStar (Γ, s) (Γ', s')) : Γ.depth = Γ'.depth := by
  refine Relation.ReflTransGen.head_induction_on
    (P := fun E (_ : ExtCtxRedStar E (Γ', s')) => E.1.depth = Γ'.depth)
    h ?_ ?_
  · rfl
  · intro E F hHead _ ih
    exact Eq.trans hHead.preserves_ctx_depth ih

/-- De Bruijn extended-context reduction stars preserve stack length. -/
theorem preserves_stack_length {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRedStar (Γ, s) (Γ', s')) : s.length = s'.length := by
  refine Relation.ReflTransGen.head_induction_on
    (P := fun E (_ : ExtCtxRedStar E (Γ', s')) => E.2.length = s'.length)
    h ?_ ?_
  · rfl
  · intro E F hHead _ ih
    exact Eq.trans hHead.preserves_stack_length ih

/-- De Bruijn extended-context reduction stars preserve context-entry kinds. -/
theorem preserves_kinds {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRedStar (Γ, s) (Γ', s')) :
    Γ.map (·.kind) = Γ'.map (·.kind) := by
  refine Relation.ReflTransGen.head_induction_on
    (P := fun E (_ : ExtCtxRedStar E (Γ', s')) => E.1.map (·.kind) = Γ'.map (·.kind))
    h ?_ ?_
  · rfl
  · intro E F hHead _ ih
    exact Eq.trans hHead.preserves_kinds ih

/-! ## Star prevalidity invariants -/

/-- De Bruijn extended-context reduction stars preserve logical-context
prevalidity from left to right. -/
theorem prevalid_ctx_right_nonempty {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRedStar (Γ, s) (Γ', s')) :
    Nonempty (Prevalid Γ → Prevalid Γ') := by
  refine Relation.ReflTransGen.head_induction_on
    (P := fun E (_ : ExtCtxRedStar E (Γ', s')) =>
      Nonempty (Prevalid E.1 → Prevalid Γ'))
    h ?_ ?_
  · exact ⟨fun hpv => hpv⟩
  · intro E F hHead _ ih
    exact ⟨fun hpv => ih.some (hHead.prevalid_ctx_right hpv)⟩

/-- De Bruijn extended-context reduction stars preserve logical-context
prevalidity from left to right. -/
noncomputable def prevalid_ctx_right {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRedStar (Γ, s) (Γ', s')) :
    Prevalid Γ → Prevalid Γ' :=
  h.prevalid_ctx_right_nonempty.some

/-- Star-level de Bruijn Lemma 36: stack changes can be stripped from an
extended-context reduction star. -/
theorem lemma_36 {Γ Γ' : Ctx} {s s' : Stack}
    (h : ExtCtxRedStar (Γ, s) (Γ', s')) :
    ExtCtxRedStar (Γ, []) (Γ', []) := by
  refine Relation.ReflTransGen.head_induction_on
    (P := fun E (_ : ExtCtxRedStar E (Γ', s')) =>
      ExtCtxRedStar (E.1, []) (Γ', []))
    h ?_ ?_
  · exact refl
  · intro E F hHead _ ih
    exact trans (single hHead.lemma_36) ih

end ExtCtxRedStar

end DeBruijn
end Pss
