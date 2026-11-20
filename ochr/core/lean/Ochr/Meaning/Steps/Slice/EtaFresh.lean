import Ochr.Meaning.Steps.Slice.Recorded

/-!
# A fresh η refinement, recorded (the slice, `etaFresh_sim`)

`Machine.etaInPlace`'s fresh branch runs `ctorRefinement` (the one constructor of the unknown's type,
its fields fresh unknowns) and records `σ := r` in `etaRefs`. What the run of `ctorRefinement`
gives is [Split]'s coverage at the one constructor: an extension of the assignment at the fresh
fields under which the refinement means `ρ σ`. `CovConcl` is that conclusion in the simulation form
the steps use (the form proposed to main for `split_coverage_stmt`, which as stated gives SOME run of
`ctorRefinement` at its own budget, not the checker's run). Recording the refinement then keeps the
extended context, the relation and `Good` (`etaRecord_ext`), with the block's captures at the new
state asked separately (the clause the lead is moving out of `CtxOk`).
-/

namespace Ochr.Meaning.Steps

open Ochr

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **[Split]'s coverage at the checker's run of `ctorRefinement`, in the simulation form**
(PROPOSED for `split_coverage_stmt`'s conclusion, the slice, 2026-11-20): an extension at the fresh
fields under which the state after is good, meets the context and is related to the same reference
state; the refinement is one `refine_step` accepts (`RefineOk`), top-hint-free (it records its
parameters); and every unknown the state names once `σ := r` is recorded is typed (the fields are
named by nothing before the record or the substitution, so `Good` at the state after does not type
them: without this clause neither use can conclude `Good` once they are named). -/
structure CovConcl (π : Nat → Nat) (st st' : MState) (s : SState) (σ : Nat) (r : Value)
    (ρ' : Assignment) (Δ' : Nat → TyS) : Prop where
  ext : ExtOk K ρ st st' ρ' Δ'
  rel : Rel { K with Δ := Δ' } ρ' φ π st' s
  size : st.absTy.size ≤ st'.absTy.size
  ok : RefineOk { K with Δ := Δ' } ρ' st' σ r
  hint : r.topHintFree K.Γ = true
  typed : ∀ τ, ({ st' with etaRefs := (σ, r) :: st'.etaRefs } : MState).Refd τ → τ < st'.absTy.size →
    ρ' τ ∈ₛ[K.dm.read] MState.absTyM K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' τ ∧
    (MState.absTyM K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' τ).level.isSome ∧
    Δ' τ = deltaOf { K with Δ := Δ' } ρ' st' τ


/-- **Recording the refinement keeps the extended context** (`etaInPlace`'s fresh branch after
`ctorRefinement`): from the coverage's conclusion, the state with `σ := r` added to `etaRefs` is
good (the record is the path condition the refinement meets, `RefineOk`'s first part at the constant
future; the unknowns it names are typed, `typed`; it holds no loan and names typed unknowns), meets
the context (`Δ` at the newly named unknowns, `typed`; (Hη) and (Hη≠) for the new record) and is
related to the same reference state (the relation reads no record). The decisions, block captures
included, are asked at the new state (`hdec`). -/
theorem etaRecord_ext (π : Nat → Nat) (st st' : MState) (s : SState) (σ : Nat) (r : Value)
    (ρ' : Assignment) (Δ' : Nat → TyS) (hc : CovConcl K ρ φ π st st' s σ r ρ' Δ')
    (hdec : DecAligned K.D { st' with etaRefs := (σ, r) :: st'.etaRefs }) :
    Ext K ρ φ π st { st' with etaRefs := (σ, r) :: st'.etaRefs } s ρ' Δ' := by
  obtain ⟨⟨agree, ctx, good⟩, rel, size, ok, hint, typed⟩ := hc
  obtain ⟨ta, mem, w1, w2, w3, w4, w6, w7, w8, w9, w10, w11, w12, w14, w15, w16⟩ := good
  have hrefd : ∀ τ, ({ st' with etaRefs := (σ, r) :: st'.etaRefs } : MState).Refd τ → τ < st'.absTy.size := by
    intro τ h
    induction h with
    | val v hv h => exact w6.1 _ (.val v hv h)
    | ty f i b T hb hT h => exact w6.1 _ (.ty f i b T hb hT h)
    | lazyTy f i b P ws j hb hT h => exact w6.1 _ (.lazyTy f i b P ws j hb hT h)
    | goal G hG h => exact w6.1 _ (.goal G hG h)
    | neutral n σ' hn h => exact w6.1 _ (.neutral n σ' hn h)
    | eta σ' v he h =>
      rcases List.mem_cons.mp he with e | e
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rcases h with rfl | h
        · exact ok.2.1
        · exact ok.2.2.1 _ h
      · exact w6.1 _ (.eta σ' v e h)
    | dep σ' T _ hT h _ => exact w6.2.1 T (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hT)) _ h
  refine ⟨size, agree, ⟨ctx.inds, ctx.covers, ctx.faithful, fun τ h hlt => (typed τ h hlt).2.2, ctx.noLabel,
    ctx.globals.of_globals rfl, hdec, ⟨ctx.shapes.fits, ctx.shapes.loans, ctx.shapes.ctors, ctx.shapes.proofCopy,
      fun σ' v hv => ?_, fun σ' v hv => ?_, ctx.shapes.readingsSorted⟩⟩,
    ⟨rel.1, rel.2, rel.3, rel.4, rel.5, rel.6, rel.7⟩,
    ⟨⟨fun τ h hlt => (typed τ h hlt).1, ta.neutral, fun σ' v hv => ?_, ta.refs⟩,
      ⟨mem.pos, fun τ h hlt => (typed τ h hlt).2.1, mem.goal⟩,
      ⟨w1, w2, w3, w4, ⟨hrefd, w6.2⟩, w7, w8, w9, w10,
        ⟨w11.1, w11.2.1, w11.2.2.1, w11.2.2.2.1, fun σ' v hv => ?_⟩, w12, w14, w15, w16⟩⟩⟩
  · rcases List.mem_cons.mp hv with e | e
    · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact hint
    · exact ctx.shapes.etaHint σ' v e
  · rcases List.mem_cons.mp hv with e | e
    · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact ok.2.2.2.1
    · exact ctx.shapes.etaNoSelf σ' v e
  · rcases List.mem_cons.mp hv with e | e
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [ok.1 (fun _ => .err) (.plain (MState.absTyM K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' σ'))]
      exact (meanV_eq_mean_aux { K with Δ := Δ' } ρ' (fun _ => .err) _ v).symm
    · exact ta.eta σ' v e
  · rcases List.mem_cons.mp hv with e | e
    · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact ok.2.2.2.2
    · exact w11.2.2.2.2 σ' v e

end

end Ochr.Meaning.Steps
