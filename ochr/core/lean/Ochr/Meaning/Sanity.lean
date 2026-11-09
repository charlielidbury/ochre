import Ochr.Meaning.WF
import Ochr.Machine

/-!
# Sanity theorems on concrete states

The toy results of `Ochr/Model/State.lean` and `State2.lean` restated on real `MState`s: a
borrow is exact, an end is `semEnd` (and the checker's `endBorrow` produces that state), `⊥` is
a definite value (D84), and `Pick`'s early end is an end and nothing else. The code-dependent
meanings (`CodeMeaning`) and the data model are arbitrary here: nothing below involves a
closure, a sealed program's run or a user inductive, except the `Pick` shape, which only reads
the sealed programs' meanings as given.
-/

namespace Ochr.Meaning.Sanity

variable (dm : DataModel) (C : CodeMeaning) (ρ : Assignment)

/-- A binding of `Nat` holding `v`. -/
def natBind (x : String) (v : Value) : Binding := { hint := ⟨x⟩, ty := some .tNat, val := v }
/-- A binding of `&Nat` holding `v`. -/
def refBind (x : String) (v : Value) : Binding := { hint := ⟨x⟩, ty := some (.tRef .tNat), val := v }

/-- `a : Nat ↦ σ₀`. -/
def Ω₀ : MState := { env := #[{ binds := #[natBind "a" (.abs 0)] }], absTy := #[.tNat], nextAbs := 1 }
/-- After `let t = &a` (label 0): `a ↦ loan_0`, `t : &Nat ↦ borrow_0 σ₀`. -/
def Ω₁ : MState :=
  { env := #[{ binds := #[natBind "a" (.loan 0), refBind "t" (.borrow 0 (.abs 0))] }],
    absTy := #[.tNat], nextAbs := 1, nextLoan := 1 }
/-- After [End 0]: `a ↦ σ₀`, `t ↦ ⊥`. -/
def Ω₂ : MState :=
  { env := #[{ binds := #[natBind "a" (.abs 0), refBind "t" .bot] }],
    absTy := #[.tNat], nextAbs := 1, nextLoan := 1 }

def a : Pos := .bind 0 0
def t : Pos := .bind 0 1

/-- [Borrow] on meanings (docs/27 §6, `step_borrow`): `a` now means the borrow's final content,
and `t` means what `a` meant; exact, under every future. -/
theorem borrow_exact (φ : Future) :
    (MState.mean dm C [] ρ Ω₀).val φ a = ρ 0 ∧
    (MState.mean dm C [] ρ Ω₁).val φ a = φ 0 ∧
    (MState.mean dm C [] ρ Ω₁).val φ t = ρ 0 ∧
    (MState.mean dm C [] ρ Ω₁).shape t = some 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- [End 0] is `semEnd` at the positions of the state: `a` reads the content `t` held, under
every future (the future is fixed at label 0 to it), and `t` is forgotten. -/
theorem end_is_semEnd (φ : Future) :
    (MState.mean dm C [] ρ Ω₂).val φ a = ((MState.mean dm C [] ρ Ω₁).semEnd t 0).val φ a ∧
    (MState.mean dm C [] ρ Ω₂).val φ t = ((MState.mean dm C [] ρ Ω₁).semEnd t 0).val φ t := by
  constructor
  · have h : (a = t) = False := eq_false (by decide)
    simp only [Mean.semEnd, h, if_false]
    show ρ 0 = (φ.upd 0 (ρ 0)) 0
    simp [Future.upd]
  · have h : (t = t) = True := eq_true rfl
    simp only [Mean.semEnd, if_true]; rfl

/-- Ending loses only information (`Mean.semEnd_below`): the ended state is below the state
before it, at its positions. -/
theorem end_below (φ' : Future) : ∃ φ,
    (MState.mean dm C [] ρ Ω₂).val φ' a ⊑ (MState.mean dm C [] ρ Ω₁).val φ a ∧
    (MState.mean dm C [] ρ Ω₂).val φ' t ⊑ (MState.mean dm C [] ρ Ω₁).val φ t := by
  obtain ⟨φ, h, _⟩ := Mean.semEnd_below (MState.mean dm C [] ρ Ω₁) t 0 φ'
  obtain ⟨ha, ht⟩ := end_is_semEnd dm C ρ φ'
  exact ⟨φ, ha ▸ h a, ht ▸ h t⟩

/-- The checker's [End] (`Machine.endBorrow`) on `Ω₁` produces `Ω₂`'s environment: the theorem
above is about the state the checker reaches. Evaluated, not proved: the step lemma for
`endBorrow` is milestone 3's. -/
def envValues (st : MState) : List Value := (allPos st.env).map (valAt st.env)
#guard match runMachine (endBorrow 100 0) Ω₁ 1000 with
  | (.ok () st', _, _) => envValues st' == envValues Ω₂
  | _ => false

/-- `⊥` is a definite value (D84): two moved places are equal, and a moved place differs from
every value, so `eq(⊥, ⊥)` means `True` and `eq(⊥, v)` means `False` in the model. -/
theorem moved_definite (n : Nat) : (Sem.moved = Sem.moved) ∧ (Sem.moved ≠ Sem.el0 Nat n) :=
  ⟨rfl, Sem.noConfusion⟩

/-! ## `Pick`'s shape (docs/27 §3.2, §7)

`let r = σ_p(&a, &b)` at an unknown `σ_p : Π(x y : &Nat). &Nat` closes off: `a` and `b` hold
fills sharing the hole `loan_2`, and `r` holds `borrow_2` of the result program. Reading `b` ends
`r` early (its hole is in `b`'s fill). The sealed programs' meanings are whatever `C` says. -/

/-- A state of `Pick`'s shape, with the two fills and the result program given as terms. -/
def Ωpick (fA fB fR : Term) : MState :=
  { env := #[{ binds := #[natBind "a" (.sealed fA), natBind "b" (.sealed fB),
      refBind "r" (.borrow 2 (.sealed fR))] }],
    absTy := #[.tNat, .tNat, .tPi [] (.pi [⟨"x"⟩, ⟨"y"⟩] [.ref .nat, .ref .nat] (.ref .nat)) []],
    nextAbs := 3, nextLoan := 3 }

def b : Pos := .bind 0 1
def r : Pos := .bind 0 2

/-- Reading `b` ends `r`: on meanings, `a` and `b` mean their fills with the hole fixed to the
content `r` holds now, under every future, and `r` is forgotten. The early end is an [End] and
nothing else; under an assignment where `σ_p` returned `a`'s borrow, `b`'s fill does not depend
on the hole, so the reference run would not have ended `r` (docs/27: `pk2_b_at_rhoX`), and the
checker's state is below it by `Mean.semEnd_below`. -/
theorem pick_early_end (fA fB fR : Term) (φ : Future) :
    let m := MState.mean dm C [] ρ (Ωpick fA fB fR)
    (m.semEnd r 2).val φ a = C.sealed ρ (φ.upd 2 (C.sealed ρ φ fR)) fA ∧
    (m.semEnd r 2).val φ b = C.sealed ρ (φ.upd 2 (C.sealed ρ φ fR)) fB ∧
    (m.semEnd r 2).val φ r = .moved := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (a = r) = False := eq_false (by decide)
    simp only [Mean.semEnd, h, if_false]; rfl
  · have h : (b = r) = False := eq_false (by decide)
    simp only [Mean.semEnd, h, if_false]; rfl
  · simp [Mean.semEnd]

end Ochr.Meaning.Sanity
