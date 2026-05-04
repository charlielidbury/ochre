import Pss.Reduction.DeBruijnOperational
import Pss.Mpss.DeBruijnReductions

/-! # `Pss.Mpss.DeBruijnOperationalSem` — operational steps embed in MPSS

This module ports Proposition 17 to the de Bruijn refactor. The locally
nameless version needs an axiom for the β case; here the body premise of
`MEqRed.bet` is a single derivation under an indexed binder context, so the
β case is built by reflexivity under that context.
-/

namespace Pss
namespace DeBruijn

namespace MEqRed

/-- Prop-friendly core of de Bruijn Proposition 17. A `Nonempty` wrapper is
needed because `StepAt` is `Prop`-valued while `MEqRed` is `Type`-valued. -/
theorem of_StepAt_nonempty {depth : Nat} {t t' : Term}
    (hstep : StepAt depth t t') :
    Nonempty (∀ {Γ : Ctx}, Γ.depth = depth →
      ∀ {s : Stack}, PrevalidExt Γ s → MEqRed Γ s t t') := by
  induction hstep with
  | @beta depth bound body arg hAbs hArg =>
      exact ⟨fun {Γ} hdepth {s} hpv =>
        have hAbsΓ : Term.Scoped Γ.depth (.abs bound body) := by
          simpa [hdepth] using hAbs
        have hArgΓ : Term.Scoped Γ.depth arg := by
          simpa [hdepth] using hArg
        have hBoundΓ : Term.Scoped Γ.depth bound := hAbsΓ.abs_inv.1
        have hBodyΓ : Term.Scoped (Γ.depth + 1) body := hAbsΓ.abs_inv.2
        have hpvBodyCtx : Prevalid ({ bound := bound, kind := .sub } :: Γ) :=
          Prevalid.sub (PrevalidExt.ctx hpv) hBoundΓ
        have hpvBody : PrevalidExt ({ bound := bound, kind := .sub } :: Γ)
            (Stack.shift 0 s) :=
          PrevalidExt.weaken_head hpv hpvBodyCtx
        have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
        MEqRed.bet hBoundΓ
          (MEqRed.refl hpvBody hBodyΓ)
          (MEqRed.refl hpvNil hArgΓ)⟩
  | @appL depth t t' u hstep hScopedU ih =>
      exact ⟨fun {Γ} hdepth {s} hpv =>
        have hUΓ : Term.Scoped Γ.depth u := by
          simpa [hdepth] using hScopedU
        have hpvOp : PrevalidExt Γ (u :: s) := PrevalidExt.cons hpv hUΓ
        have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
        MEqRed.app (ih.some hdepth hpvOp) (MEqRed.refl hpvNil hUΓ)⟩
  | @appR depth t u u' hScopedT hstep ih =>
      exact ⟨fun {Γ} hdepth {s} hpv =>
        have hTΓ : Term.Scoped Γ.depth t := by
          simpa [hdepth] using hScopedT
        have hUΓ : Term.Scoped Γ.depth u := by
          simpa [hdepth] using (StepAt.scoped_left hstep)
        have hpvOp : PrevalidExt Γ (u :: s) := PrevalidExt.cons hpv hUΓ
        have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
        MEqRed.app (MEqRed.refl hpvOp hTΓ) (ih.some hdepth hpvNil)⟩
  | @absBound depth bound bound' body hstep hBody ih =>
      exact ⟨fun {Γ} hdepth {s} hpv => by
        have hBodyΓ : Term.Scoped (Γ.depth + 1) body := by
          simpa [hdepth] using hBody
        have hBoundΓ : Term.Scoped Γ.depth bound := by
          simpa [hdepth] using StepAt.scoped_left hstep
        have hBoundStep : MEqRed Γ [] bound bound' :=
          ih.some hdepth (PrevalidExt.nil (PrevalidExt.ctx hpv))
        cases s with
        | nil =>
            have hBound'Γ : Term.Scoped Γ.depth bound' := hBoundStep.scoped_right
            have hpvBodyCtx : Prevalid ({ bound := bound, kind := .sub } :: Γ) :=
              Prevalid.sub (PrevalidExt.ctx hpv) hBoundΓ
            have hpvBody : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) [] :=
              PrevalidExt.nil hpvBodyCtx
            exact MEqRed.fun_ hBoundStep (MEqRed.refl hpvBody hBodyΓ)
        | cons α s' =>
            have hα : Term.Scoped Γ.depth α := PrevalidExt.head_scoped hpv
            have hpvTail : PrevalidExt Γ s' := PrevalidExt.tail hpv
            have hpvBodyCtx : Prevalid ({ bound := α, kind := .equ } :: Γ) :=
              Prevalid.equ (PrevalidExt.ctx hpv) hα
            have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ)
                (Stack.shift 0 s') :=
              PrevalidExt.weaken_head hpvTail hpvBodyCtx
            exact MEqRed.fOp hBoundStep hα (MEqRed.refl hpvBody hBodyΓ)⟩
  | @absBody depth bound body body' hBound hstep ih =>
      exact ⟨fun {Γ} hdepth {s} hpv => by
        have hBoundΓ : Term.Scoped Γ.depth bound := by
          simpa [hdepth] using hBound
        have hBoundRefl : MEqRed Γ [] bound bound :=
          MEqRed.refl (PrevalidExt.nil (PrevalidExt.ctx hpv)) hBoundΓ
        cases s with
        | nil =>
            have hpvBodyCtx : Prevalid ({ bound := bound, kind := .sub } :: Γ) :=
              Prevalid.sub (PrevalidExt.ctx hpv) hBoundΓ
            have hpvBody : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) [] :=
              PrevalidExt.nil hpvBodyCtx
            have hdepthBody : Ctx.depth ({ bound := bound, kind := .sub } :: Γ) = depth + 1 := by
              have hlen : List.length Γ = depth := by
                simpa [Ctx.depth] using hdepth
              simp [Ctx.depth, hlen, Nat.add_comm]
            exact MEqRed.fun_ hBoundRefl (ih.some hdepthBody hpvBody)
        | cons α s' =>
            have hα : Term.Scoped Γ.depth α := PrevalidExt.head_scoped hpv
            have hpvTail : PrevalidExt Γ s' := PrevalidExt.tail hpv
            have hpvBodyCtx : Prevalid ({ bound := α, kind := .equ } :: Γ) :=
              Prevalid.equ (PrevalidExt.ctx hpv) hα
            have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ)
                (Stack.shift 0 s') :=
              PrevalidExt.weaken_head hpvTail hpvBodyCtx
            have hdepthBody : Ctx.depth ({ bound := α, kind := .equ } :: Γ) = depth + 1 := by
              have hlen : List.length Γ = depth := by
                simpa [Ctx.depth] using hdepth
              simp [Ctx.depth, hlen, Nat.add_comm]
            exact MEqRed.fOp hBoundRefl hα (ih.some hdepthBody hpvBody)⟩

/-- De Bruijn Proposition 17: operational small-step reduction embeds into
MPSS equivalence reduction at any prevalid extended context with matching
ambient depth. -/
noncomputable def of_StepAt {depth : Nat} {Γ : Ctx} {s : Stack}
    {t t' : Term}
    (hstep : StepAt depth t t') (hdepth : Γ.depth = depth)
    (hpv : PrevalidExt Γ s) :
    MEqRed Γ s t t' :=
  (of_StepAt_nonempty hstep).some hdepth hpv

/-- Closed de Bruijn operational steps embed into empty-stack MPSS
equivalence reduction at the empty context. -/
noncomputable def of_Step {t t' : Term}
    (hstep : Step t t') :
    MEqRed [] [] t t' :=
  of_StepAt hstep rfl (PrevalidExt.nil Prevalid.empty)

end MEqRed

end DeBruijn
end Pss
