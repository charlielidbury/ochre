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

/-- **`evalCore` of a read of a MOVED number variable fails** (`readPlace`: "[Read] reading ⊥"; the
typed run's [Repack] first, then the read). -/
def VarBotInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (i : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (f j : Nat) (b : Binding),
    ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
    b.val = .bot → b.ty = some .tNat →
    ¬ Runs (Ochr.evalCore (n + 1) typed (.place (.var i)) hint) st bh (v, T?) st'

/-- **`eval` below fuel `3` fails** for a term that is not an embedded value (`eval` and `evalAt` each
take one unit, `evalCore 0` is out of fuel at once). -/
def EvalLow : Prop :=
  ∀ (m : Nat) (typed : Bool) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (r : Value × Option Value),
    m < 3 → (∀ w, t ≠ .val w) → ¬ Runs (Ochr.eval m typed t hint) st bh r st'

/-! ## For the open cases (`let` and `;` ending a borrow; lead10, stated for the machine lane's review) -/

/-- **[Drop] of a `let`'s binding holding a borrow** (`dropTopBind`, the top binding `y ↦ borrow_l c`,
`c` a number, lent by the number binding `px`; a fragment environment, `FEnd`): after a quiet
stretch (the end's [Repack] of `c` at `Nat`), `endBorrow l` (`y ↦ ⊥`, `px ↦ c`), then the binding is
popped. The tail's value is parked as a temporary meanwhile (a number, `()` or another label's
borrow: `FEnd` asks only that no temporary hold a loan). -/
def DropBorrowInv : Prop :=
  ∀ (n : Nat) (st st' : MState) (bh : Nat) (fr : Frame) (b : Binding) (px : Pos) (l : Nat) (c : Value),
    st.env[st.env.size - 1]? = some fr → fr.binds.back? = some b → b.val = .borrow l c →
    FEnd st.env px (.bind (st.env.size - 1) (fr.binds.size - 1)) l c →
    Runs (Ochr.dropTopBind n) st bh () st' →
    ∃ st₁, Quiet st st₁ ∧ KeepsInv st st₁ ∧
      Kern { st₁ with env := Env.popBindE (endE st₁.env px (.bind (st.env.size - 1) (fr.binds.size - 1)) c) } st'

/-- **`evalCore` of a typed `u; w` whose first part is a borrow** (`.seq`; `SeqInv` for the value
`borrow_l c`, `c` a number, lent by the number binding `px`): `dropValue` parks it, ends `l` (`px ↦ c`,
the parked holder `⊥`) and pops it, after a quiet stretch (the end's [Repack]); then `w` as in
`SeqInv`. The mode is kept only under the antecedent (lead11, as `SeqInv`: unconditional it would ask
the ending machinery of any value to keep the mode, a whole-machine fact). -/
def SeqBorInv : Prop :=
  ∀ (n : Nat) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.seq u w) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ stW : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ bh₂ : Nat),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧
      (stW.tailDecl = none ∨ stW.tailDecl = st.curDecl) ∧ Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      DecTab D st₁ ∧
      (∀ l c px, v₀ = .borrow l c → c.Num → (∀ q ∈ allPos st₁.env, FVal (valAt st₁.env q)) →
        valAt st₁.env px = .loan l → px ∈ allPos st₁.env →
        (∀ q ∈ allPos st₁.env, ∀ w', valAt st₁.env q ≠ .borrow l w') →
        ∃ st₂, Quiet st₁ st₂ ∧ KeepsInv st₁ st₂ ∧ Kern { st₂ with env := Env.setAtE st₂.env px c } stW ∧
          ModeEq st₁ stW) ∧
      stW.tailNext = st.curTail ∧
      Runs (Ochr.eval n true w none) stW bh₂ (v, T?) st'

/-! ## For the `let` of the fragment (lead11) -/

/-- **[Drop] of a `let`'s binding LENT to the value in flight fails** (`dropTopBind`: ending the
binding's loans would end a borrow a value in flight holds, D106). In the fragment a binding lends
only to younger bindings or to the value in flight (`FSt.order`), so this is the only way the
binding a `let` drops can be lent (`let x = Z; &x` is rejected). -/
def DropLentFail : Prop :=
  ∀ (n : Nat) (st st' : MState) (bh : Nat) (fr : Frame) (b : Binding) (m f i : Nat) (w : Value),
    st.env[st.env.size - 1]? = some fr → fr.binds.back? = some b → b.val = .loan m →
    Pos.temp f i ∈ allPos st.env → valAt st.env (.temp f i) = .borrow m w →
    ¬ Runs (Ochr.dropTopBind n) st bh () st'

/-- `InvBindNum` for `()` (state-level): the value in flight, `()`, moved into a binding pushed at
`Unit` read `.unit`. -/
def InvBindUnit : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (h : Hint) (T? : Option Value) (p : Bool),
    PlaceLocal D → 0 < st.env.size → Inv D Γ (st.withTempT .unit T?).norm →
    Inv D Γ { st with env := Env.pushBindE st.env h (some .tUnit) .unit p .unit }.norm

/-- `InvPopBind` for a binding holding `()` (state-level). -/
def InvPopUnit : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (fr : Frame) (b : Binding),
    PlaceLocal D → st.env[st.env.size - 1]? = some fr → fr.binds.back? = some b → b.val = .unit →
    Inv D Γ st.norm → Inv D Γ { st with env := Env.popBindE st.env }.norm


/-! ## For the open cases `&x`, `x := u`, `*y := u` (lead11, stated for the machine lane's review) -/

/-- **`evalCore` of `&x` for `x` LENT** (`.borrow (.var i)`; the generalisation of `BorrowNumInv`): `x`
at `.bind f j`, stored at `Nat`, holds `loan_m` whose borrow `borrow_m c` is held at the binding
`.bind f' j'` (`FEnd`; a temporary holder is a value in flight, whose end the access rejects, D106).
After a quiet stretch (the end's [Repack]) the access ends `m` (`endE`), then `x` is lent at the
counter: the value is `borrow_{st₁.nextLoan} c` at `&Nat`. `#eval`ed in `FragGuards`. -/
def BorrowLentInv : Prop :=
  ∀ (n i : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value) (f j : Nat)
    (b : Binding) (f' j' m : Nat) (c : Value) (D : Decisions),
    Mode st → ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
    b.ty = some .tNat → FEnd st.env (.bind f j) (.bind f' j') m c → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.borrow (.var i)) hint) st bh (v, T?) st' →
    Mode st' ∧ ∃ st₁, Quiet st st₁ ∧ KeepsInv st st₁ ∧ v = .borrow st₁.nextLoan c ∧ T? = some (.tRef .tNat) ∧
      Kern { st₁ with env := Env.setAtE (endE st₁.env (.bind f j) (.bind f' j') c) (.bind f j) (.loan st₁.nextLoan),
        nextLoan := st₁.nextLoan + 1 } st'

/-- **`&x` of a MOVED number variable fails** (typed). -/
def BorrowBotInv : Prop :=
  ∀ (n i : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value) (f j : Nat)
    (b : Binding),
    ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
    b.val = .bot → b.ty = some .tNat →
    ¬ Runs (Ochr.evalCore (n + 1) true (.borrow (.var i)) hint) st bh (v, T?) st'

/-- **`evalCore` of a typed write at a ROOT number variable** (`x := u`; `AssignNumInv` is the field
write `x.0 := u`): `u` run from the entry's kernel, in mode, the one-shot flag clear, at the hint the
checker hands (left free); then, where `u`'s value is a number, after a quiet stretch (the place's
type, the comparison of `u`'s type with it, the end's [Repack]), the write: `x`'s old content a number
or `⊥` is overwritten; `x` LENT (`FEnd` at `u`'s end, holder a binding) has its borrow ended first
(`endE`), then is overwritten. The invariant across the quiet stretch where `u`'s type is `Nat` (as
`AssignDerefInv`). `#eval`ed in `FragGuards` (number, lent with another borrow live, moved). -/
def AssignVarInv : Prop :=
  ∀ (n i : Nat) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none →
    (∀ f j b, ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
      b.ty = some .tNat) → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.assign (.var i) u) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (hu : Option Value) (v₀ : Value) (T₀ : Option Value) (bh₁ : Nat),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧ Runs (Ochr.eval n true u hu) st₀ bh₁ (v₀, T₀) st₁ ∧
      DecTab D st₁ ∧ v = .unit ∧ T? = some .tUnit ∧
      ∀ f j b, ckVarPos st₁.env i = some (.bind f j) → st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
        v₀.Num →
        ∃ st₂, Quiet st₁ st₂ ∧ ((∀ T, T₀ = some T → (T == .tNat) = true) → KeepsInv st₁ st₂) ∧ ModeEq st₁ st' ∧
          ((b.val.Num ∨ b.val = .bot) → Kern { st₂ with env := Env.setAtE st₂.env (.bind f j) v₀ } st') ∧
          (∀ f' j' m c, FEnd st₁.env (.bind f j) (.bind f' j') m c →
            Kern { st₂ with env := Env.setAtE (endE st₂.env (.bind f j) (.bind f' j') c) (.bind f j) v₀ } st')

/-- **`AssignDerefInv` with the case it leaves out**: where `y` holds `⊥` at `u`'s end (its borrow
ended by `u`, e.g. `*y := x` with `y = &x`) the write fails. Stated as `AssignDerefInv`'s
decomposition with one more conjunct (the machine lane's proof of `AssignDerefInv` plus that case). -/
def AssignDerefInvF : Prop :=
  ∀ (n i : Nat) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none →
    (∀ f j b, ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
      b.ty = some (.tRef .tNat)) → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.assign (.deref (.var i)) u) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (hu : Option Value) (v₀ : Value) (T₀ : Option Value) (bh₁ : Nat),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧ Runs (Ochr.eval n true u hu) st₀ bh₁ (v₀, T₀) st₁ ∧
      DecTab D st₁ ∧ v = .unit ∧ T? = some .tUnit ∧
      (∀ f j b, ckVarPos st₁.env i = some (.bind f j) → st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
        b.val ≠ .bot) ∧
      ∀ f j b l w, ckVarPos st₁.env i = some (.bind f j) → st₁.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
        b.val = .borrow l w → w.Num →
        ∃ st₂, Quiet st₁ st₂ ∧ ((∀ T, T₀ = some T → (T == .tNat) = true) → KeepsInv st₁ st₂) ∧ ModeEq st₁ st' ∧
          ckVarPos st₂.env i = some (.bind f j) ∧ st₂.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧
          Kern { st₂ with env := Env.setAtE st₂.env (.bind f j) (.borrow l v₀) } st'

end Ochr.Meaning.Steps.Form
