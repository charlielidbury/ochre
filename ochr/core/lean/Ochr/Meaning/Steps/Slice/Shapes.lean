import Ochr.Meaning.Steps.DropOne

/-!
# The checker's typing of places across the move log (the slice)

After the checker's access the drop reads only the typing of places (`ShapeFacts`), which the
induction hypothesis's [Access] now concludes; the log of moves it writes next changes nothing
the relation, `Good` or that typing reads.
-/

namespace Ochr.Meaning.Steps.Slice

open Ochr Ochr.Meaning Ochr.Meaning.Steps

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **`logEffect` changes nothing the relation, `Good` or the typing of places reads** (it writes
`placeLog` only, `runs_logEffect_inv`): `logEffect_rel` with the typing of places in place of the
whole run context. -/
theorem logEffect_rel_shapes (st st₁ : MState) (s : SState) (π : Nat → Nat) (q : Place) (k : String) (b : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hsh : ShapeFacts K.D K.Γ st) (hs : Rel K ρ φ π st s)
    (h : Runs (Ochr.logEffect q k) st b () st₁) :
    Rel K ρ φ π st₁ s ∧ Good K.dm K.M K.Γ ρ st₁ ∧ ShapeFacts K.D K.Γ st₁ ∧ st₁.env = st.env := by
  obtain ⟨X, rfl⟩ := runs_logEffect_inv h
  obtain ⟨ta, mem, wf⟩ := hg
  have hrefd : ∀ τ, ({ st with placeLog := X } : MState).Refd τ → st.Refd τ :=
    fun τ h => refd_of_same (st := st) (st' := { st with placeLog := X }) rfl rfl rfl rfl rfl h
  exact ⟨⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7⟩,
    ⟨⟨fun τ hr hlt => ta.mem τ (hrefd τ hr) hlt, ta.neutral, ta.eta, ta.refs⟩,
     ⟨mem.pos, fun τ hr hlt => mem.absTy τ (hrefd τ hr) hlt, mem.goal⟩,
     ⟨wf.1, wf.2.1, wf.2.2.1, wf.2.2.2.1, ⟨fun τ hr => wf.2.2.2.2.1.1 τ (hrefd τ hr), wf.2.2.2.2.1.2⟩,
      wf.2.2.2.2.2⟩⟩,
    hsh.of_sameDec rfl rfl rfl rfl, rfl⟩

end

end Ochr.Meaning.Steps.Slice
