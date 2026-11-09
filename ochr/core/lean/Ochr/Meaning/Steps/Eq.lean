import Ochr.Meaning.Steps.Borrow

/-!
# Step lemmas, `Eq` and conversion: `mkEqM`, `conv`, `convPi`, `convFn`, `rewriteGoal`
(milestone 3; docs/18 Lemma "conversion respects meaning", (V1)–(V9))

`Eq` computes (`mkEqM`) to `True`, `False`, a conjunction of field equations, or stays stuck:
every outcome means the proposition `⟦a⟧ = ⟦b⟧` (docs/24 C10, `Eq` reads no type; distinct
tags are distinct meanings; whole constructor values are equal iff their fields are, by
`DataModel.pack_fields`; under D84 a moved field is a definite value, so a partly moved value is
equal only to one with the same moved fields, `Sem.ctor`). Conversion is a *check*: only its
accepting direction carries an obligation, that convertible values have equal meanings, for
two values that are members of one type (their recorded parameters then mean the same). The
statements are monotone-free: under D84 nothing is identified that may stand for different
values ([Conv-bot] is retired), so no clause about `⊥` is needed beyond definiteness.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The truth of a type value read as a proposition. -/
noncomputable def propOf (P : Value) : Prop := ((meanV K ρ φ (.plain .err) P).asTy).true

/-- `Eq` computes soundly: whatever `mkEqM` returns means `⟦a⟧ = ⟦b⟧` at `A`, and the state's
core is unchanged. -/
theorem mkEqM_step (st st' : MState) (fuel : Nat) (A a b P : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hA : ∀ φ, (meanV K ρ φ (.plain .err) A).asTy = (meanV K ρ noFuture (.plain .err) A).asTy)
    (h : Runs (Ochr.mkEqM fuel A a b) st fuel P st') :
    (∀ φ, propOf K ρ φ P ↔
      meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) a = meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) b) ∧
    st'.core = st.core := by
  sorry

/-- Conversion is sound: two values convertible at a state, both (partly moved) members of one
type, have equal meanings under every future. The accepting direction only; `convStack` only
makes `conv` answer `false` more often, so no hypothesis on it. -/
theorem conv_sound (st st' : MState) (fuel : Nat) (v w : Value) (T : TyM)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hv : (meanV K ρ φ (.plain T) v).pmem T) (hw : (meanV K ρ φ (.plain T) w).pmem T)
    (h : Runs (Ochr.conv fuel v w) st fuel true st') :
    meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w := by
  sorry

/-- [Conv-pi]: convertible Π-type values have equal type meanings (equal Lean carriers), by
`funext` over the generic arguments, which range over the whole domain (docs/18 (V4)). -/
theorem convPi_sound (st st' : MState) (fuel : Nat) (P Q : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (h : Runs (Ochr.convPi fuel P Q) st fuel true st') :
    ∀ φ, (meanV K ρ φ (.plain .err) P).asTy = (meanV K ρ φ (.plain .err) Q).asTy := by
  sorry

/-- [Conv-fun]: two function values with convertible observations of their generic calls mean
the same function (extensionality on good carriers, docs/18 (V5), `Slice.pi_ext`). -/
theorem convFn_sound (st st' : MState) (fuel : Nat) (f g : Value) (T : TyM)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hf : meanV K ρ φ (.plain T) f ∈ₛ T) (hgm : meanV K ρ φ (.plain T) g ∈ₛ T)
    (h : Runs (Ochr.convFn fuel f g) st fuel true st') :
    meanV K ρ φ (.plain T) f = meanV K ρ φ (.plain T) g := by
  sorry

/-- [Rewrite]: when the equation `h : Eq(A, a, b)` is true, the rewritten goal is true iff the
goal is (the occurrences replaced mean the same). -/
theorem rewriteGoal_step (st st' : MState) (fuel : Nat) (rev : Bool) (hT : Term) (A a b G G' : Value)
    (hg : Good K.dm K.C K.Γ ρ st)
    (hh : Runs (Ochr.eval fuel true hT) st fuel (.proof, some (.tEq A a b)) st)
    (h : Runs (Ochr.rewriteGoal fuel rev hT G) st fuel G' st') :
    ∀ φ, propOf K ρ φ (.tEq A a b) → (propOf K ρ φ G' ↔ propOf K ρ φ G) := by
  sorry

/-- The meaning of a type value does not depend on the future (docs/27 Lemma 5: no stored type
holds a live loan), at every state the checker reaches. Used to read types under `noFuture`. -/
theorem type_futureFree (st : MState) (T : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hT : ∃ p, MState.posTyM K.dm K.C K.Γ ρ st p = some (meanV K ρ noFuture (.plain .err) T).asTy) :
    ∀ φ', (meanV K ρ φ (.plain .err) T).asTy = (meanV K ρ φ' (.plain .err) T).asTy := by
  sorry

end

end Ochr.Meaning.Steps
