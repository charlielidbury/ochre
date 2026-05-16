import Och.Subtyping
import Och.EvalSubst
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll

/-!
# Neutral-arm helpers for SubCheckSubstSoundness

Provides auxiliary lemmas (`subCheckSpine_sound_bvar_bvar`,
`app_cong_from_spine_ih`, `liftSeenList`) used by the main
`SubCheckSubstSoundness` dispatch. The old "level-var wall"
documented here was eliminated by the de Bruijn refactor.
-/

namespace Och.Soundness

open SubstEval

/-! ## Bridge primitives

`liftSeenList` translates the engine's seen-list into the declarative
`Seen` type. The `tyCtxToCtx` translation lives in `CloseAll.lean`. -/

/-- Lift the engine's seen-list (no depth tag) to a declarative
seen-set, tagging each entry with the *current* depth `tyCtx.size`
**and** applying `closeAll depth` to the entries' terms.

The `closeAll` translation is the **Design A** convention from
`docs/ideas/tyCtxPush-bridge-wall.md`: the canonical declarative form
is "closeAll'd everywhere", so seen-list entries are pre-translated.
This makes the engine's `seen.any (a == av && b == bv)` short-circuit
match a `Subtype'.hyp` lookup directly under translation. -/
def liftSeenList (depth : Nat) (seen : List (Expr × Expr)) : Seen :=
  seen.map (fun (a, b) => (depth, closeAll depth a, closeAll depth b))

theorem liftSeenList_nil (depth : Nat) :
    liftSeenList depth [] = [] := rfl

theorem liftSeenList_cons (depth : Nat) (a b : Expr)
    (seen : List (Expr × Expr)) :
    liftSeenList depth ((a, b) :: seen)
    = (depth, closeAll depth a, closeAll depth b)
        :: liftSeenList depth seen := rfl

/-! ## Spine helpers -/

def subCheckSpine_sound_bvar_bvar
    {S : Seen} {Γ : Ctx} {k1 k2 : Nat}
    (h : k1 == k2) :
    Subtype' S Γ (.bvar k1) (.bvar k2) := by
  have heq' : k1 = k2 := by simpa using h
  subst heq'
  exact .refl _

/-! ### app-app spine inductive step -/

def app_cong_from_spine_ih
    {S : Seen} {Γ : Ctx} {f1 f2 v1 v2 : Expr}
    (ih_head : Subtype' S Γ f1 f2)
    (ih_v12 : Subtype' S Γ v1 v2)
    (ih_v21 : Subtype' S Γ v2 v1) :
    Subtype' S Γ (.app f1 v1) (.app f2 v2) := by
  -- `app_cong : Subtype' S Γ f₂ f₁ → Subtype' S Γ a₂ a₁ →
  --             Subtype' S Γ a₁ a₂ → Subtype' S Γ (.app f₂ a₂) (.app f₁ a₁)`
  -- Match: f₂ := f1, f₁ := f2, a₂ := v1, a₁ := v2.
  -- Premises: f1 ⊑ f2, v1 ⊑ v2, v2 ⊑ v1.
  exact .app_cong ih_head ih_v12 ih_v21

/-! ### neutralAscent soundness

Composed in `SubCheckSubstSoundness.lean`; see `neutralAscent_sound`
and `neutralAscent_bvar_sound` there. -/

end Och.Soundness
