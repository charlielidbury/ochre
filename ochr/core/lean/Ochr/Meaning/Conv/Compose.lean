import Ochr.Meaning.Conv.Sound
import Ochr.Meaning.Conv.Refine

/-!
# N3 for plain values, composed (conv1, 2026-11-28)

The machine half (`Refine.conv_refine`, nothing assumed) followed by the model half
(`Sound.convV_alike_plain`, from [Conv-fun]'s premise and the unit laws).
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Steps

/-- **Conversion is sound on plain values** (no code, no constructor value): a successful
comparison answering `true` changes only names, and the two values are alike: read at any one hint,
holding no `Prop` constructor value and both fitting any one type there, they mean the same, under
every assignment and future at which the two named facts hold.
Assumes 2 facts: [Conv-fun]'s premise sound at the machine's runs from this state (`PremFn`; mixed;
(II) at the generic call, C1, the observation's completeness; only between two globals here) and the
unit laws (`UnitOk`; model; read true for plain values given `LibOk`). -/
theorem conv_sound_plain {K : RunCtx} {ρ : Assignment} {φ : Future} {fuel : Nat} {st st' : MState}
    {v w : Value} {bh : Nat} (hp : PremFn K ρ φ (machPremises st)) (hu : UnitOk K ρ φ Plain)
    (h : Runs (Ochr.conv fuel v w) st bh true st') (pv : Plain v) (pw : Plain w) :
    NamesKept st st' ∧ Alike K ρ φ v w := by
  obtain ⟨d, hk⟩ := conv_refine fuel st st' v w bh h
  exact ⟨hk, convV_alike_plain hp hu d pv pw⟩

end Ochr.Meaning.Conv
