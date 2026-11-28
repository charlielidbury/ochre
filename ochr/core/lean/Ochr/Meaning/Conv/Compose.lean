import Ochr.Meaning.Conv.Sound
import Ochr.Meaning.Conv.Refine
import Ochr.Meaning.Conv.SoundEq

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

/-- **`Eq` computes soundly on plain sides** (`mkEqM`): the state after is reached from the state before
(Ω, the goal, the refinements and the declarations kept, the tables grown), and the proposition
`mkEqM` returns means `⟦a⟧ = ⟦b⟧` at `⟦A⟧`, at every hint, under every assignment and future at which
the named facts hold, when the sides are plain, hold no `Prop` constructor value, are each `⊥` or a
member of `⟦A⟧`, and `⟦A⟧` has a level.
Assumes 4 facts: `FieldTysKept` (checker; `fieldTypesOf` keeps the reached-state relation; read
true), `PremFn` (mixed; as for `conv`), `UnitOk` (model; read true given `LibOk`), `LibOk` (model;
the `Prelude`'s `True`, `False`, `And`; read true under a faithful data model). -/
theorem mkEqM_sound_plain {K : RunCtx} {ρ : Assignment} {φ : Future} {fuel : Nat} {st st' : MState}
    {A a b P : Value} {bh : Nat} (hf : FieldTysKept) (hp : PremFn K ρ φ (machPremisesR Reach st))
    (hu : UnitOk K ρ φ Plain) (hl : LibOk K ρ φ)
    (h : Runs (Ochr.mkEqM fuel A a b) st bh P st') (pa : Plain a) (pb : Plain b)
    (na : NoProp K a) (nb : NoProp K b)
    (sa : SideOkV K ρ φ (capTy K ρ φ A) a) (sb : SideOkV K ρ φ (capTy K ρ φ A) b)
    (hA : (capTy K ρ φ A).level.isSome = true) :
    Reach st st' ∧
      PropU K ρ φ P (meanV K ρ φ (.plain (capTy K ρ φ A)) a = meanV K ρ φ (.plain (capTy K ρ φ A)) b) := by
  obtain ⟨d, hk⟩ := mkEqM_refine hf fuel st st' A a b P bh h
  exact ⟨hk, eqTo_plain hp hu hl d pa pb na nb sa sb hA⟩

end Ochr.Meaning.Conv
