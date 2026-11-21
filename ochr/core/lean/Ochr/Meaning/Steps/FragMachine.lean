import Ochr.Meaning.Steps.FragEnd

/-!
# Facts about the checker alone that the fragment's steps use (lead10; for the machine lane)

Each is a `Prop` about the checker's runs or states with no model in it, taken as a hypothesis by the
fragment's steps (`Steps/Frag*.lean`) and to be reviewed against `Machine.lean` and proved by the
machine lane; none is proved here. Stated at exactly the entry conditions the fragment's steps
have; each is read against the checklist of `OPEN.md` (the term in tail position or not, a handed
down reading, a lazily typed binding, the place lent, an untyped run, the stored type of the place
read, the old content, an undecided reading, when a decision is read, a sub-run's type an `Option`,
`ModeEq` across a stretch, a free decision table), and sanity-run at those conditions in
`Steps/FragGuards.lean`.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **`evalCore` of a read of a number variable that is LENT** (`.place (.var i)`, the generalisation of
`VarEndInv` to any fragment environment): `x` at `.bind f j`, stored at `Nat`, holds `loan_l`; its
borrow `borrow_l c` (`c` a number) is held at the BINDING `ph` (a temporary holding it is a value in
flight, and the access ends no borrow a value in flight holds, D106: the run fails); every position
holds a fragment value, `loan_l`/`borrow_l` lie only there (`FEnd`). The read's [Repack] of the place
at its type is quiet (`st₁`: with a loan inside, D73 may make unknowns); the access ends `l`
(`endBorrow`: `ph ↦ ⊥`, `x ↦ c`; its [Repack] of `c` at `Nat` passes; D98's test passes, `c` being
whole), which is `endE`; then the read copies (the kernel kept) or moves (`x ↦ ⊥`) as the aligned
copy decision, read at the entry's readings, says. The value is `c`, at the stored type `Nat` in a
typed run. -/
def VarLentInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (i : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (f j : Nat) (b : Binding) (f' j' l : Nat) (c : Value) (D : Decisions),
    Mode st → ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
    b.ty = some .tNat → FEnd st.env (.bind f j) (.bind f' j') l c → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) typed (.place (.var i)) hint) st bh (v, T?) st' →
    v = c ∧ (∀ T, T? = some T → T = .tNat) ∧ (typed = true → T?.isSome) ∧ Mode st' ∧
    ∃ st₁, Quiet st st₁ ∧ KeepsInv st st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var i)) = true →
        Kern { st₁ with env := endE st₁.env (.bind f j) (.bind f' j') c } st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var i)) = false →
        Kern { st₁ with env := Env.setAtE (endE st₁.env (.bind f j) (.bind f' j') c) (.bind f j) .bot } st')

/-- **The invariant across the end of one borrow in a fragment environment** (state-level; the
generalisation of `InvEndRead`): the holder set to `⊥`, the lender, a number binding read `.other`,
given its content back. -/
def InvEnd : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (px ph : Pos) (l : Nat) (c : Value),
    PlaceLocal D → FEnd st.env px ph l c →
    (∀ f j, px = .bind f j → ∀ b, st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = .other) →
    Inv D Γ st.norm → Inv D Γ { st with env := endE st.env px ph c }.norm

end Ochr.Meaning.Steps.Form
