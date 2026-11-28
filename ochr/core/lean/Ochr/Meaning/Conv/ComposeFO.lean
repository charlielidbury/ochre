import Ochr.Meaning.Conv.Compose
import Ochr.Meaning.Conv.CtorEq
import Ochr.Meaning.Conv.FieldLen
import Ochr.Meaning.DataModel.Exists.Defs

/-!
# N3 for values that hold no code, composed (conv2, 2026-11-28)

The machine halves (`Refine.conv_refine`, nothing assumed; `RefineEq.mkEqM_refine`, from
`FieldTysKept`) followed by the model halves at constructor values (`Ctor.convV_alike_fo`,
`CtorEq.eqTo_fo`), with what the step's `Pre` already carries discharged: the checker's
declarations are a prefix of the context's (`CtxS.inds`), and records at typed parameters have no
junk leaf (`CtxS.faithful`, `RecordsFaithfulAt.leafOk`).
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- The checker's declarations are found as the context finds them. -/
theorem find_ctx {K : RunCtx} {st : MState} (hc : CtxS K st.norm) :
    ∀ t d, st.inds.find? (·.name == t) = some d → K.Γ.find? (·.name == t) = some d :=
  fun _ _ hd => DataModel.Exists.find_of_prefix hc.inds hd

/-- Records at typed parameters of the checker's declarations have no junk leaf. -/
theorem leafsOk_ctx {K : RunCtx} {st : MState} (hc : CtxS K st.norm) : LeafsOk K st.inds := by
  intro t d hd ps hl hp
  have hm : d ∈ st.norm.inds := List.mem_of_find?_eq_some hd
  exact ((hc.faithful d hm) K.Δ (fun _ => .err)).2.2.leafOk ps hl hp

/-- **Conversion is sound on values that hold no code** (constructor values included): a successful
comparison answering `true` changes only names, and the two values are alike. Assumes 2 facts:
`PremFn` (mixed; (II) at the generic call, C1; only between two globals here) and `UnitOk` at `FO`
(model; PROVED from `LibOk` and `AndParams` by `unitOk_fo`). -/
theorem conv_sound_fo {K : RunCtx} {ρ : Assignment} {φ : Future} {fuel : Nat} {st st' : MState}
    {v w : Value} {bh : Nat} (hp : PremFn K ρ φ (machPremises st)) (hu : UnitOk K ρ φ FO)
    (h : Runs (Ochr.conv fuel v w) st bh true st') (pv : FO v) (pw : FO w) :
    NamesKept st st' ∧ Alike K ρ φ v w := by
  obtain ⟨d, hk⟩ := conv_refine fuel st st' v w bh h
  exact ⟨hk, convV_alike_fo hp hu d pv pw⟩

/-- The same, the unit laws discharged. Assumes 3 facts: `PremFn` (mixed), `LibDecls` (checker: the
`Prelude`'s shapes; model: `And`'s parameters are propositions), `LibAnd` (model; read true under
faithfulness). -/
theorem conv_sound_fo' {K : RunCtx} {ρ : Assignment} {φ : Future} {fuel : Nat} {st st' : MState}
    {v w : Value} {bh : Nat} (hp : PremFn K ρ φ (machPremises st)) (hd : LibDecls K) (ha : LibAnd K ρ φ)
    (h : Runs (Ochr.conv fuel v w) st bh true st') (pv : FO v) (pw : FO w) :
    NamesKept st st' ∧ Alike K ρ φ v w :=
  conv_sound_fo hp (unitOk_fo (libOk_of hd ha) hd.andP) h pv pw

/-- **`Eq` computes soundly on sides that hold no code** (`mkEqM`; constructor values included: the
refutation [Eq-disj], injectivity [Eq-inj], [Eq-refl], [Eq-stuck]): the state after is reached from
the state before, and the proposition `mkEqM` returns means `⟦a⟧ = ⟦b⟧` at `⟦A⟧`, at every hint, when
the sides hold no code and no `Prop` constructor value, are each `⊥` or a member of `⟦A⟧`, `⟦A⟧` has a
level.
Assumes 6 facts: `FieldTysKept` (C; read true, pinned), `PremFn` (X), `LibDecls` (C+M), `LibAnd` (M),
`FieldTysSoundT` (X; conv1's `FieldTysSound` restated at typed parameters and fields, with a level; its
length half is PROVED for the machine, `FieldLen.machPremises_len`),
and `CtxS` at the start (part of every step's `Pre`). (Branch `conv2-eqargs`: `mkEqM` takes [Eq-inj]'s
parameters from the equation's type only, so no class condition on the sides; 6 facts.) -/
theorem mkEqM_sound_fo {K : RunCtx} {ρ : Assignment} {φ : Future} {fuel : Nat} {st st' : MState}
    {A a b P : Value} {bh : Nat} (hfk : FieldTysKept) (hp : PremFn K ρ φ (machPremisesR Reach st))
    (hd : LibDecls K) (ha : LibAnd K ρ φ) (hf : FieldTysSoundT K ρ φ (machPremisesR Reach st))
    (hc : CtxS K st.norm)
    (h : Runs (Ochr.mkEqM fuel A a b) st bh P st') (pa : FO a) (pb : FO b)
    (na : NoProp K a) (nb : NoProp K b)
    (sa : SideOkV K ρ φ (capTy K ρ φ A) a) (sb : SideOkV K ρ φ (capTy K ρ φ A) b)
    (hA : (capTy K ρ φ A).level.isSome = true) :
    Reach st st' ∧
      PropU K ρ φ P (meanV K ρ φ (.plain (capTy K ρ φ A)) a = meanV K ρ φ (.plain (capTy K ρ φ A)) b) := by
  obtain ⟨d, hk⟩ := mkEqM_refine hfk fuel st st' A a b P bh h
  have hl := libOk_of hd ha
  exact ⟨hk, eqTo_fo hp (unitOk_fo hl hd.andP) hl ⟨machPremises_len Reach st, hf⟩ (leafsOk_ctx hc) (find_ctx hc) d pa pb na nb
    sa sb hA⟩

end Ochr.Meaning.Conv
