import Ochr.Meaning.Rules.Sound
import Ochr.Meaning.Rules.RefineEq

/-!
# The rules trial, part C: A and B composed into the area's statements

The first design's compositions are superseded by `ComposeT.lean` (proved, under the typing
predicate). What remains here: the side condition of the first form (`SideOk`, now `SoundEq.SideMem`)
and the split of `ExtOk`.

- `ExtOk` is not produced by A or B. On this route it splits as a machine-side fact, that the run
  leaves no new reference (`Quiet`), and a model-side lemma independent of conversion
  (`extOk_of_quiet`: a state that differs from a good one only in tables grown at unreferenced
  unknowns is good under the same assignment). With the amended checker change (a comparison keeps
  the names it used and drops the records it made), `Quiet` is the target form of a comparison. The machine-side fact is false for conversions whose
  private copy refines a generic argument in place (`Rules/EmptyDomain.lean`), and then `ExtOk` can
  be false outright.
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-! The first design's compositions (`conv_C`, `conv_C_same`, `mkEqM_C`, `mkEqM_C'`), which called the
removed `sorry`'d statements of `Sound.lean`, are superseded by `ComposeT.lean` (proved). -/

/-- A side of an `Eq`: `⊥` (D84: moved on every path), or a whole member of the type. -/
def SideOk (A a : Value) : Prop :=
  a = .bot ∨ ((meanV K ρ φ (.plain (tyOf K ρ φ A)) a).whole ∧
    meanV K ρ φ (.plain (tyOf K ρ φ A)) a ∈ₛ[K.dm.read] tyOf K ρ φ A)

theorem SideOk.pmem {A a : Value} (h : SideOk K ρ φ A a) :
    DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain (tyOf K ρ φ A)) a) (tyOf K ρ φ A) := by
  rcases h with rfl | ⟨hw, hm⟩
  · exact .inl rfl
  · exact DataModel.pmem_of_mem K.dm.read K.Γ hw hm

theorem SideOk.not_moved {A a : Value} (h : SideOk K ρ φ A a) (hb : a ≠ .bot) :
    meanV K ρ φ (.plain (tyOf K ρ φ A)) a ≠ .moved := by
  rcases h with rfl | ⟨hw, -⟩
  · exact absurd rfl hb
  · intro e; rw [e] at hw; simp [Sem.whole] at hw

end

/-- A run that leaves no new reference: the state after is the state before with its tables grown
(`KeptAfter`), the same records, Σ and frozen readings of the old unknowns, and the counter of
unknowns still the table's size. Machine-side. -/
def Quiet (st st' : MState) : Prop :=
  KeptAfter st st' ∧ st'.neutrals = st.neutrals ∧ st'.etaRefs = st.etaRefs ∧ st'.globals = st.globals ∧
    st'.absTy.size = st'.nextAbs ∧ (∀ i, i < st.absDecl.size → st'.absDecl[i]? = st.absDecl[i]?) ∧
    st'.liveScope = st.liveScope

/-- (C, model side, a guess) A state that differs from a good one only by tables grown at
unreferenced unknowns is good, under the same assignment and `Δ`, with the checker's decisions at
the state after (which agree with the old ones on old inputs). Not about conversion. -/
theorem extOk_of_quiet (K : RunCtx) (ρ : Assignment) (st st' : MState) (hg : Good K.dm K.M K.Γ ρ st)
    (hctx : CtxOk K ρ st) (hq : Quiet st st') : ∃ D', ExtOk K ρ st st' ρ K.Δ D' := by
  sorry

end Ochr.Meaning.Rules
