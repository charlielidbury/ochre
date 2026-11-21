import Ochr.Meaning.Steps.FormKern
import Ochr.Meaning.Steps.ColumnPlumb

/-!
# Facts about the checker alone that the column of `Steps/Form.lean` uses (lead7; for the machine lane)

Each is a statement about the checker's runs with no model in it (`Kern`, `Mode`, `Inv` and `DecTab`
are the checker's), stated here as a `Prop` and taken as a hypothesis by the column's lemmas; none is
proved here. They are of three kinds:

* **inversions**: a successful run of a checker function is made of the sub-runs its code makes, at
  states whose kernel (`Kern`) is given (the bookkeeping fields between them are not);
* **preservation**: the checker's syntactic invariant (`Inv`) holds after a run that started from it;
* **alignment**: where the checker reads a decision (the erasure pre-pass, a binding's reading, the
  copy decision), the answer is the aligned table's (`DecTab`).

Every one is read off `Machine.lean` at `spine` 3347196b; the docstring of each says which code.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **The mode of an evaluation's entry**: not a call's head (`headEval`: the pre-pass classifies the
term), not inside `clone`/`peek` (`copying`) or in place (`inPlace`), not inside an erased term
(`erasedDepth`): where the checker's read moves exactly when the strict run's does. A step statement
without it is false: inside `clone(x)` the checker's read of `x` copies where the strict run's
`.place` clause moves. -/
structure Mode (st : MState) : Prop where
  headEval : st.headEval = false
  copying : st.copying = false
  inPlace : st.inPlace = false
  erased : st.erasedDepth = 0

/-- **`eval` around `evalCore`** (`Machine.eval`, `evalAt`), for a term the pre-pass does not erase:
`eval (n + 2)` runs `evalCore n` from a state with the same kernel, the one-shot tail flag moved to
`curTail` and cleared, in the same mode, and ends with the kernel `evalCore` left (the after-the-fact
classification agrees with the pre-pass and restores nothing). "Does not erase" is read from the
aligned table: where it classifies the term as neither a statement nor a proof at the top frame's
readings, so does the checker's pre-pass, at the term's own reading or at the one its context hands
it (`tailDecl`). The table is the one aligned at the end of the run (`DecTab.back` carries it to
the start). The pre-pass is pinned by the term's READING, handed down or computed (machine2's
correction, 2026-11-21): where the reading is handed down (`tailDecl`) `evalAt` runs no `declOf` on
the term, so the table's `flags` and `declOf` are tied by no run and `D.flags … = (false, false)`
pins nothing. So: the reading is decided (not `.any`: else the after-the-fact classification decides,
and an erasure restores Ω), it is not a proof, and the term is not a call (for a call `preFlags`
also erases at a sort reading). Every column term reads `.other` or `.unit`. This is the machine
lane's `Machine.EvalInvR`, PROVED (`Machine.evalInvR`). -/
def EvalInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    Mode st → DecTab D st' → (∀ w, t ≠ .val w) → (∀ f as h, t ≠ .call f as h) →
    D.declOf (DecideScope.topReadings st) t ≠ .any → (D.declOf (DecideScope.topReadings st) t).isProof = false →
    (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) t)) →
    Runs (Ochr.eval (n + 2) typed t hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (bh' : Nat), Kern st st₀ ∧ Mode st₀ ∧ st₀.curTail = st.tailNext ∧ st₀.tailNext = false ∧
      st₀.tailDecl = none ∧ st₀.curDecl = some (D.declOf (DecideScope.topReadings st₀) t) ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' (v, T?) st₁ ∧ Kern st₁ st' ∧ (Mode st₁ → Mode st')

/-- **`evalCore` of `Z`**: the value `Z` at `Nat`, the kernel and the mode as they were. -/
def ZeroInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
    Runs (Ochr.evalCore (n + 1) typed .zero hint) st bh (v, T?) st' →
    v = .zero ∧ T? = some .tNat ∧ Kern st st' ∧ (Mode st → Mode st')

/-- **The columns' terms**: `Z`, `S(u)`, a variable, `let`, a write at the field `0` of a variable
(the first column); a borrow of a variable, a write through a variable, a sequence (the borrow
column, lead8); closed under their sub-terms. A fact stated over this class, never over every term
(the machine lane: `InvCore` over EVERY term is the whole checker's well-formedness preservation,
with a clause suspected false, `borrow_wf`; "a typed `eval` returns a type" is an induction on this
class, over every term one over the whole machine). -/
inductive ColTerm : Term → Prop
  | zero : ColTerm .zero
  | succ {u : Term} : ColTerm u → ColTerm (.succ u)
  | var (i : Nat) : ColTerm (.place (.var i))
  | letIn (x : Hint) {u w : Term} : ColTerm u → ColTerm w → ColTerm (.letIn x u w)
  | assign (i : Nat) {u : Term} : ColTerm u → ColTerm (.assign (.proj 0 (.var i)) u)
  | borrow (i : Nat) : ColTerm (.borrow (.var i))
  | assignDeref (i : Nat) {u : Term} : ColTerm u → ColTerm (.assign (.deref (.var i)) u)
  | seq {u w : Term} : ColTerm u → ColTerm w → ColTerm (.seq u w)

/-- **The invariant is kept by `evalCore` at the column's terms, its result counted** (part (c), for the forms of the column):
from a state meeting `Inv` at decisions aligned with the checker at the end, a successful run of
`evalCore` ends at one meeting `Inv` with its value in flight at its stored type. -/
def InvCore : Prop :=
  ∀ (n : Nat) (typed : Bool) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions) (Γ : List IndDecl),
    ColTerm t → Inv D Γ st.norm → DecTab D st' → Runs (Ochr.evalCore n typed t hint) st bh (v, T?) st' →
    Inv D Γ (st'.withTempT v T?).norm

/-- **A quiet step**: what a private computation leaves (a comparison, main's D103: it keeps nothing
but the counters of fresh names and the types of the unknowns it made, which nothing names): the
kernel but the counters and the new tail of Δ. -/
structure Quiet (st st' : MState) : Prop where
  env : st.env.erase = st'.env.erase
  globals : st.globals = st'.globals
  inds : st.inds = st'.inds
  refs : st.refs = st'.refs
  etaRefs : st.etaRefs = st'.etaRefs
  goal : st.goal = st'.goal
  neutrals : st.neutrals = st'.neutrals
  liveScope : st.liveScope = st'.liveScope
  nextLoan : st.nextLoan ≤ st'.nextLoan
  absSize : st.absTy.size ≤ st'.absTy.size
  absTy : ∀ σ, σ < st.absTy.size → st'.absTy[σ]? = st.absTy[σ]?

/-- **`evalCore` of `S(u)`**: `u` evaluated with no hint from a state with the kernel and mode it was
entered with and the one-shot flag clear; the value `S v₀` at `Nat`; in a typed run, `u`'s type
checked against `Nat` (`expectTy`), which is quiet; in an untyped one, nothing after. For `u` of
the column's terms (`ColTerm`): "a typed `eval` returns a type" is proved by induction on that class,
and for every term it would be an induction over the whole machine (the machine lane's review). -/
def SuccInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value),
    ColTerm u → Mode st → st.tailNext = false → st.tailDecl = none →
    Runs (Ochr.evalCore (n + 1) typed (.succ u) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ : Nat), Kern st st₀ ∧ Mode st₀ ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ Runs (Ochr.eval n typed u none) st₀ bh₁ (v₀, T₀) st₁ ∧ v = .succ v₀ ∧
      T? = some .tNat ∧ Quiet st₁ st' ∧ (∀ D, DecTab D st' → DecTab D st₁) ∧
      (typed = true → ∃ (T : Value) (st₂ : MState) (bh₂ : Nat), T₀ = some T ∧
        Runs (Ochr.expectTy n "the argument of S" (some T) .tNat) st₁ bh₂ () st₂ ∧ Kern st₂ st')

/-- **`evalCore` of a variable holding a number** (`.place (.var i)`; the column's read): the value is
the binding's, its type the binding's stored type (a typed run has one); the run's [Repack] and the
access are quiet (a number holds no dependent constructor, no loan); then the read copies or moves as
the aligned copy decision says: a copy leaves the kernel, a move writes `⊥` at the binding. -/
def VarNumInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (i : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (f j : Nat) (b : Binding) (D : Decisions),
    Mode st → ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
    b.val.Num → b.ty.isSome → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) typed (.place (.var i)) hint) st bh (v, T?) st' →
    v = b.val ∧ (∀ T, T? = some T → b.ty = some T) ∧ (typed = true → T?.isSome) ∧ Mode st' ∧
    ∃ st₁, Quiet st st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var i)) = true → Kern st₁ st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var i)) = false →
        Kern { st₁ with env := Env.setAtE st₁.env (.bind f j) .bot } st')

/-- **`evalCore` of a typed `let h = u; w`**: `u` evaluated with no hint from the entry's kernel, in
mode, the one-shot flag clear, to a value at a type; the binding's reading the aligned table's at
the state after `u`; the binding pushed; `w` evaluated (no hint: a typed run's tail has none) from
there, in mode, in the `let`'s tail position; its result pushed as a temporary at its type; the
binding dropped (`dropTopBind`); the temporary popped, which is the `let`'s value. The table aligned
at the end is aligned at the states between, and the invariant holds where `w` starts. The binding's
reading is taken at the ENTRY state (`Machine.lean`'s `.letIn` reads `du` before it evaluates `u`;
the machine lane's review), and `u`'s run leaves the top frame's readings as they were (where the
reference reads its binding's reading, after `u`; lead8). For `u` of the column's terms (`ColTerm`),
as `SuccInv`. -/
def LetInv : Prop :=
  ∀ (n : Nat) (h : Hint) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions) (Γ : List IndDecl),
    ColTerm u → Mode st → st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.letIn h u w) hint) st bh (v, T?) st' →
    ∃ (du : DeclInfo) (st₀ st₁ stB st₂ st₃ : MState) (v₀ r T₀ : Value) (p : Bool) (bh₁ bh₂ bh₃ : Nat),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧
      (stB.tailDecl = none ∨ stB.tailDecl = st.curDecl) ∧
      Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, some T₀) st₁ ∧ 0 < st₁.env.size ∧
      D.declOf (DecideScope.topReadings st) u = du ∧ DecideScope.topReadings st₁ = DecideScope.topReadings st ∧
      Kern { st₁ with env := Env.pushBindE st₁.env h (some T₀) v₀ p du } stB ∧ Mode stB ∧
      stB.tailNext = st.curTail ∧
      Runs (Ochr.eval n true w none) stB bh₂ (r, T?) st₂ ∧
      Runs (Ochr.dropTopBind n) (st₂.withTempT r T?) bh₃ () st₃ ∧
      Kern st₃ (st'.withTempT v T?) ∧
      DecTab D st₁ ∧ DecTab D st₂ ∧ (ColTerm u → Inv D Γ st.norm → Inv D Γ stB.norm)

/-- **[Drop] of a binding that holds no borrow and has no site** (`dropTopBind`): it ends nothing and
pops the binding. -/
def DropNoopInv : Prop :=
  ∀ (n : Nat) (st st' : MState) (bh : Nat) (fr : Frame) (b : Binding),
    st.env[st.env.size - 1]? = some fr → fr.binds.back? = some b → b.val.loans = [] →
    (∀ l w, b.val ≠ .borrow l w) → (∀ l, b.val.holdsBorrow l = false) →
    Runs (Ochr.dropTopBind n) st bh () st' → Kern { st with env := Env.popBindE st.env } st'

/-- **`evalCore` of a typed write at the field `0` of a variable** (`x.0 := u`; the column's write):
`u` evaluated from the entry's kernel, in mode, the one-shot flag clear (with whatever hint the
checker hands it: the place's type for a constructor or an embedded value, none otherwise); then
quiet steps (the place's type, read privately; `u`'s type checked against the field's; the
accesses, which end nothing where nothing is lent; the temporary `assignPlace` parks `u`'s value in
and takes back); the variable then holds `S(w)` (the path exists) and the write leaves it holding
`S(v₀)` (`setPlace`); D112's invalidation writes nothing at a field of `Nat` (`openWrite`: `Nat` is no
declaration); the value `()` at `Unit`. The table aligned at the end is aligned after `u`. The
variable is stored at `Nat`: a field step under a parent that is not a number runs as a match
(`placeOperand?`, `projIn`, `projMatch`), and with `Box := box(Nat)`, `x ↦ box(Z) : Box` the write
`x.0 := S(Z)` leaves `box(S(Z))` (the machine lane's review: false with `b.ty.isSome`). -/
def AssignNumInv : Prop :=
  ∀ (n i : Nat) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none →
    (∀ f j b, ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
      b.ty = some .tNat) → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.assign (.proj 0 (.var i)) u) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ st₂ : MState) (hu : Option Value) (v₀ : Value) (T₀ : Option Value) (bh₁ f j : Nat) (b : Binding)
      (w : Value),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧
      Runs (Ochr.eval n true u hu) st₀ bh₁ (v₀, T₀) st₁ ∧
      DecTab D st₁ ∧ Quiet st₁ st₂ ∧ ckVarPos st₂.env i = some (.bind f j) ∧
      st₂.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧ b.val = .succ w ∧
      ((∀ l, (valAt st₂.env (.bind f j)).sitesOf l (.bind f j) [] = []) →
        Kern { st₂ with env := Env.setAtE st₂.env (.bind f j) (.succ v₀) } st') ∧ v = .unit ∧ T? = some .tUnit

/-! ## The borrow column (`def B : Nat := let x = S(Z); let y = &x; *y := Z; x`) -/

/-- **`evalCore` of a typed borrow of a variable holding a number stored at `Nat`** (`&x`;
`Machine.evalCore`'s `.borrow`, `borrowPlace`): the place's type read and [Repack]ed privately
(quiet), the access ends nothing (nothing is lent at a number), a fresh label `l` (the counter), `x`
holds `loan_l`, the value `borrow_l v` at `&Nat`; D112's invalidation writes nothing at a root. As
first stated (lead7) the binding's stored type was free and the conclusion `T? = b.ty.map .tRef`: at a
binding typed lazily (`ty := none`, a deferred codomain in `lazyTy`) the checker's typed run returns
`&Nat` where it said `none` (`ColumnB`'s sanity runs, `stLazy`; lead8). -/
def BorrowNumInv : Prop :=
  ∀ (n i : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value) (f j : Nat)
    (b : Binding) (D : Decisions),
    Mode st → ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
    b.val.Num → b.ty = some .tNat → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.borrow (.var i)) hint) st bh (v, T?) st' →
    Mode st' ∧ ∃ st₁, Quiet st st₁ ∧ v = .borrow st₁.nextLoan b.val ∧ T? = some (.tRef .tNat) ∧
      Kern { st₁ with env := Env.setAtE st₁.env (.bind f j) (.loan st₁.nextLoan), nextLoan := st₁.nextLoan + 1 } st'

/-- **`evalCore` of a typed write through a borrow variable** (`*y := u`, `y` holding `borrow_l w`):
as `AssignNumInv`, the path `[*]`: after the write `y` holds `borrow_l v₀`, where nothing is lent
inside `y`'s content. As first stated (lead7) that condition was missing, and where `y`'s content is
reborrowed (`y ↦ borrow_0 loan_1`, `r ↦ borrow_1 S(Z)`) the write's access ends `r` (`r ↦ ⊥`), which
the conclusion excluded (`ColumnB`'s sanity runs, `stReb`; lead8). `y` is stored at `&Nat` (the
step's entry condition: a whole write through `*`, no strong update, no lent proof). -/
def AssignDerefInv : Prop :=
  ∀ (n i : Nat) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none →
    (∀ f j b, ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
      b.ty = some (.tRef .tNat)) → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.assign (.deref (.var i)) u) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ st₂ : MState) (hu : Option Value) (v₀ : Value) (T₀ : Option Value) (bh₁ f j : Nat) (b : Binding)
      (l : Nat) (w : Value),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧ Runs (Ochr.eval n true u hu) st₀ bh₁ (v₀, T₀) st₁ ∧
      DecTab D st₁ ∧ Quiet st₁ st₂ ∧ ckVarPos st₂.env i = some (.bind f j) ∧
      st₂.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧ b.val = .borrow l w ∧
      ((∀ l', (valAt st₂.env (.bind f j)).sitesOf l' (.bind f j) [] = []) →
        Kern { st₂ with env := Env.setAtE st₂.env (.bind f j) (.borrow l v₀) } st') ∧ v = .unit ∧ T? = some .tUnit

/-- **`evalCore` of a typed `u; w`** (`Machine.evalCore`'s `.seq`), for a first part whose value
holds no borrow and no loan: `u` evaluated with no hint from the entry's kernel, in mode, the
one-shot flag clear; its value dropped (`dropValue`: nothing ends; a value holding a loan has its
borrowers ended, `endLoansOfTopTemp`, so the loans' condition is needed; lead8); `w` evaluated with
no hint (a typed run's tail), in mode, in the sequence's tail position. -/
def SeqInv : Prop :=
  ∀ (n : Nat) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.seq u w) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ stW : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ bh₂ : Nat),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧
      (stW.tailDecl = none ∨ stW.tailDecl = st.curDecl) ∧ Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      DecTab D st₁ ∧ ((∀ l, v₀.holdsBorrow l = false) → v₀.loans = [] → Kern st₁ stW) ∧ Mode stW ∧
      stW.tailNext = st.curTail ∧
      Runs (Ochr.eval n true w none) stW bh₂ (v, T?) st'

/-- **`evalCore` of a read of `x` lent to `y`'s borrow** (`.place (.var 1)` at the state of `B`'s
read: one frame, `x ↦ loan_l : Nat`, `y ↦ borrow_l w : &Nat`, `w` a number): the access ends `l`
(`endBorrow`: `y`'s content `w` goes back to `x`, `y` holds `⊥`; [Repack] of a number passes, D98's
test passes: the content is whole: (M-c)); then the read copies or moves as the aligned decision
says. Quiet besides. `x` is stored at `Nat`: as first stated (lead7) nothing said so, and with `x`
stored at `Unit` the typed read returns `0` at `Unit` where the conclusion said `Nat` (`ColumnB`'s
sanity runs, `stUnitX`; lead8). -/
def VarEndInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (l : Nat) (w : Value) (D : Decisions),
    Mode st → allPos st.env = [.bind 0 0, .bind 0 1] → valAt st.env (.bind 0 0) = .loan l →
    valAt st.env (.bind 0 1) = .borrow l w → w.Num →
    (∀ bx, st.env[0]?.bind (fun fr : Frame => fr.binds[0]?) = some bx → bx.ty = some .tNat) → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) typed (.place (.var 1)) hint) st bh (v, T?) st' →
    v = w ∧ (typed = true → T? = some .tNat) ∧ Mode st' ∧ ∃ st₁, Quiet st st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var 1)) = true →
        Kern { st₁ with env := Env.setAtE (Env.setAtE st₁.env (.bind 0 1) .bot) (.bind 0 0) w } st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var 1)) = false →
        Kern { st₁ with env := Env.setAtE (Env.setAtE st₁.env (.bind 0 1) .bot) (.bind 0 0) .bot } st')

end Ochr.Meaning.Steps.Form
