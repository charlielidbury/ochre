import Ochr.Meaning.Rules.Sound
import Ochr.Meaning.Rules.Refine

/-!
# The rules trial, part C: A and B composed into the area's statements

What the composition reaches, beside each existing statement, and what it needs beyond the
existing statement's hypotheses:

- `conv_C` (beside `conv_sound_stmt`, which is false, `Rules/Counter.lean`): the meaning part and
  `KeptAfter`, PROVED from A and B. Beyond the existing hypotheses it needs (i) the bridge from the
  machine's untyped parts to sound ones at the values compared (`hbridge`: a typing fact about the
  values inside `v` and `w`; it is what the existing statement was missing), (ii) the premises'
  soundness at the machine's instance (`hprem`: the generic call of each function pair and the
  generic arguments of each Π-pair the comparison made stand for every instance; a statement about
  machine runs from the states the comparison reached), and (iii) `CounterMono` for `KeptAfter`.
  `Good` and `CtxOk` are not used by the composition: they are what (ii) needs.
- `mkEqM_C` (beside `mkEqM_step_stmt`, false): likewise, with part A's hypotheses on the sides.
- `ExtOk` is not produced by A or B. On this route it splits as a machine-side fact, that the run
  leaves no new reference (`Quiet`), and a model-side lemma independent of conversion
  (`extOk_of_quiet`: a state that differs from a good one only in tables grown at unreferenced
  unknowns is good under the same assignment). The machine-side fact is false for conversions whose
  private copy refines a generic argument in place (`Rules/EmptyDomain.lean`), and then `ExtOk` can
  be false outright.
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **(C) `conv`**, from A and B. -/
theorem conv_C (hmono : CounterMono) (E : Syn) (hs : SynSound K ρ φ E) (fuel : Nat) (st st' : MState)
    (v w : Value) (bh : Nat)
    (hbridge : ConvV Syn.machine (machPremises st) st.globals v w → ConvV E (machPremises st) st.globals v w)
    (hprem : PremSound K ρ φ (machPremises st))
    (h : Runs (Ochr.conv fuel v w) st bh true st') (T : TyM) :
    meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w ∧ KeptAfter st st' := by
  obtain ⟨hd, hk⟩ := conv_refine hmono fuel st st' v w bh h
  exact ⟨conv_sound_at K ρ φ hs hprem (hbridge hd) T, hk⟩

/-- **(C) `mkEqM`**, from A and B, with part A's hypotheses on the sides. -/
theorem mkEqM_C (hmono : CounterMono) (E : Syn) (hs : SynSound K ρ φ E) (hl : LibOk K ρ φ)
    (fuel : Nat) (st st' : MState) (A a b P : Value) (bh : Nat) (hΓ : K.Γ = st.inds)
    (hbridge : EqTo Syn.machine (machPremises st) st.globals st.inds A a b P →
      EqTo E (machPremises st) st.globals st.inds A a b P)
    (hprem : PremSound K ρ φ (machPremises st))
    (ha : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain (tyOf K ρ φ A)) a) (tyOf K ρ φ A))
    (hb : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain (tyOf K ρ φ A)) b) (tyOf K ρ φ A))
    (hma : a ≠ .bot → meanV K ρ φ (.plain (tyOf K ρ φ A)) a ≠ .moved)
    (hmb : b ≠ .bot → meanV K ρ φ (.plain (tyOf K ρ φ A)) b ≠ .moved)
    (hda : a.anyAtom (dataCtorBad K.Γ) = false) (hdb : b.anyAtom (dataCtorBad K.Γ) = false)
    (h : Runs (Ochr.mkEqM fuel A a b) st bh P st') :
    KeptAfter st st' ∧ ∀ hint, meanV K ρ φ hint P =
      .ty (TyM.prop (meanV K ρ φ (.plain (tyOf K ρ φ A)) a = meanV K ρ φ (.plain (tyOf K ρ φ A)) b)) := by
  obtain ⟨hd, hk⟩ := mkEqM_refine hmono fuel st st' A a b P bh h
  have hd' := hbridge hd
  rw [← hΓ] at hd'
  exact ⟨hk, eqTo_sound K ρ φ hs hprem hl hd' ha hb hma hmb hda hdb⟩

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
