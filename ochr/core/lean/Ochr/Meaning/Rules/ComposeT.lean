import Ochr.Meaning.Rules.SoundT
import Ochr.Meaning.Rules.RefineEq

/-!
# The rules trial, part C under the typing predicate: the true restatements, composed

Each statement here is B (proved, model-free: `RefineConv`, `RefineEq`) followed by A (proved
under the typing predicate: `SoundT`), with nothing between them but the instantiation of the
abstract premises with the machine's runs. What each rests on is a hypothesis, named:

- `GenericKept` / `EqKept` (B's one assumption: the generic sub-computations keep the state as a
  private computation does; true by construction under full restore);
- `PremSoundT` at the machine's premises (the function rules' semantic content: a successful
  generic call, or comparison of generic arguments' types, makes the two values alike);
- `UnitOk` (the library's unit laws keep a well-typed value's meaning);
- `CodeOk` on a closed class `Q` (the code cases; outright for the first-order class `FO`);
- for the values: `HWT` at the type (the typing gap: nothing in the proof supplies it today).
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **Conversion is sound** (the true restatement of `conv_sound_stmt`): a successful comparison of
two values of a closed class, both hereditarily well typed at `T`, means they mean the same at
`T`, and the state after is reached from the one before. -/
theorem conv_sound_T (hk : GenericKept StateRel.reach) {Q : Value → Prop} (hQ : Closed Q)
    {fuel : Nat} {st st' : MState} {v w : Value} {bh : Nat}
    (hp : PremSoundT K ρ φ (machPremises st)) (hu : UnitOk K ρ φ Q)
    (hc : CodeOk K ρ φ Q (machPremises st) st.globals)
    (h : Runs (Ochr.conv fuel v w) st bh true st') (hqv : Q v) (hqw : Q w)
    {T : TyM} (hv : HWT K ρ φ T v) (hw : HWT K ρ φ T w) :
    meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w ∧ KeptAfter st st' := by
  obtain ⟨d, hkept⟩ := conv_refine' hk fuel st st' v w bh h
  exact ⟨(convV_alike hQ hp hu hc d hqv hqw).1 T hv hw, hkept⟩

/-- The same in the target form (comparisons restore their start state): the state unchanged. -/
theorem conv_sound_T_same (hk : GenericKept StateRel.same) {Q : Value → Prop} (hQ : Closed Q)
    {fuel : Nat} {st st' : MState} {v w : Value} {bh : Nat}
    (hp : PremSoundT K ρ φ (machPremisesR (fun a b => b = a) st)) (hu : UnitOk K ρ φ Q)
    (hc : CodeOk K ρ φ Q (machPremisesR (fun a b => b = a) st) st.globals)
    (h : Runs (Ochr.conv fuel v w) st bh true st') (hqv : Q v) (hqw : Q w)
    {T : TyM} (hv : HWT K ρ φ T v) (hw : HWT K ρ φ T w) :
    meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w ∧ st' = st := by
  obtain ⟨d, he⟩ := conv_refine_same hk fuel st st' v w bh h
  exact ⟨(convV_alike hQ hp hu hc d hqv hqw).1 T hv hw, he⟩

/-- **Conversion is sound, first-order fragment**: for values with no code, resting only on the
function rules' premises (here only [Conv-fun] at two globals can fire) and the unit laws. -/
theorem conv_sound_T_fo (hk : GenericKept StateRel.reach)
    {fuel : Nat} {st st' : MState} {v w : Value} {bh : Nat}
    (hp : PremSoundT K ρ φ (machPremises st)) (hu : UnitOk K ρ φ FO)
    (h : Runs (Ochr.conv fuel v w) st bh true st') (hqv : FO v) (hqw : FO w)
    {T : TyM} (hv : HWT K ρ φ T v) (hw : HWT K ρ φ T w) :
    meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w ∧ KeptAfter st st' :=
  conv_sound_T hk FO.closed hp hu (FO.codeOk K ρ φ _ _) h hqv hqw hv hw

end

end Ochr.Meaning.Rules

#print axioms Ochr.Meaning.Rules.conv_sound_T
#print axioms Ochr.Meaning.Rules.conv_sound_T_same
#print axioms Ochr.Meaning.Rules.conv_sound_T_fo
