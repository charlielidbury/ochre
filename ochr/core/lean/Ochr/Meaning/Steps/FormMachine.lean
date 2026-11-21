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

/-- **The mode's fields equal** (the machine lane's `Machine.ModeEq`, restated here because the
machine lane's files import the column's: `Steps/ColumnCFF` converts). A step concludes `ModeEq`
across a stretch with no sub-run, never `Mode` at a later state: a sub-run's end mode is the
sub-run's own fact (lead, 2026-11-21). -/
structure ModeEq (a b : MState) : Prop where
  headEval : a.headEval = b.headEval
  copying : a.copying = b.copying
  inPlace : a.inPlace = b.inPlace
  erased : a.erasedDepth = b.erasedDepth

theorem Mode.of_modeEq {a b : MState} (hm : Mode a) (h : ModeEq a b) : Mode b :=
  ⟨h.headEval ▸ hm.headEval, h.copying ▸ hm.copying, h.inPlace ▸ hm.inPlace, h.erased ▸ hm.erased⟩

/-- **A private computation keeps the invariant** (lead9; `InvCore` is dropped, docs/31 D116): the
conjunct an inversion fact attaches to its `Quiet` stretch. Not a state-level fact: `Quiet` leaves
`nextAbs` and the types of the unknowns the computation made free, and `Inv` reads them ((WF6)'s
`absTy.size = nextAbs` and its bound on the unknowns of `absTy`, (WF8), (WF11)), so "`Inv` survives
`Quiet`" is false of states; it is a fact about the computation (a comparison or a [Repack] makes
only unknowns whose types are clean). -/
def KeepsInv (a b : MState) : Prop := ∀ (D : Decisions) (Γ : List IndDecl), Inv D Γ a.norm → Inv D Γ b.norm

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
entered with and the one-shot flag clear; the value `S v₀` at `Nat`; in a typed run, `u`'s type as
its run returned it (`T₀`, an `Option`) checked against `Nat` (`expectTy`), which is quiet; the mode
after `u` kept. This is the machine lane's `Machine.SuccInvR` word for word (`ModeEq` restated),
PROVED (`Machine.succInvR`; `Steps/ColumnCFF.succInv`). -/
def SuccInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value),
    Mode st → st.tailNext = false → st.tailDecl = none →
    Runs (Ochr.evalCore (n + 1) typed (.succ u) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ : Nat), Kern st st₀ ∧ Mode st₀ ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ Runs (Ochr.eval n typed u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      v = .succ v₀ ∧ T? = some .tNat ∧ Quiet st₁ st' ∧ ModeEq st₁ st' ∧ (∀ D, DecTab D st' → DecTab D st₁) ∧
      (typed = true → ∃ (st₂ : MState) (bh₂ : Nat),
        Runs (Ochr.expectTy n "the argument of S" T₀ .tNat) st₁ bh₂ () st₂ ∧ Kern st₂ st')

/-- **A type check keeps the invariant** (`expectTy`, a comparison, D103: quiet; lead9): what `S(u)`
needs after `u`'s type is checked. A fact about the comparison's run, not about states (`KeepsInv`). -/
def InvExpectTy : Prop :=
  ∀ (n : Nat) (w : String) (T : Option Value) (A : Value) (st st' : MState) (bh : Nat),
    Runs (Ochr.expectTy n w T A) st bh () st' → KeepsInv st st'

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
    ∃ st₁, Quiet st st₁ ∧ KeepsInv st st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var i)) = true → Kern st₁ st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var i)) = false →
        Kern { st₁ with env := Env.setAtE st₁.env (.bind f j) .bot } st')

/-- **`evalCore` of a typed `let h = u; w`**: `u` evaluated with no hint from the entry's kernel, in
mode, the one-shot flag clear, to a value at the type its run returned (`T₀`, an `Option`); the
binding's reading `du` read at the ENTRY (`Machine.lean`'s `.letIn` reads it before evaluating `u`);
the binding pushed at `T₀`; the mode after `u` carried to `w`'s entry; `w` evaluated (no hint: a
typed run's tail has none) in the `let`'s tail position, its reading handed down; its result pushed
as a temporary at its type; the binding dropped (`dropTopBind`); the temporary popped, which is the
`let`'s value; the mode from the drop to the end kept. The table aligned at the end is aligned at
the states between. This is the machine lane's `Machine.LetInvR` word for word, PROVED
(`Machine.letInvR`; `Steps/ColumnCFF.letInv`). What lead8's form also had is the caller's: that `u`'s
run leaves the top frame's readings and a frame (the column's run facts give both), and the invariant
where `w` starts (the state-level lemmas below). -/
def LetInv : Prop :=
  ∀ (n : Nat) (h : Hint) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.letIn h u w) hint) st bh (v, T?) st' →
    ∃ (du : DeclInfo) (st₀ st₁ stB st₂ st₃ : MState) (v₀ r : Value) (T₀ : Option Value) (p : Bool)
      (bh₁ bh₂ bh₃ : Nat),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧ stB.tailDecl = st.curDecl ∧
      Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      D.declOf (DecideScope.topReadings st) u = du ∧
      Kern { st₁ with env := Env.pushBindE st₁.env h T₀ v₀ p du } stB ∧ ModeEq st₁ stB ∧
      stB.tailNext = st.curTail ∧
      Runs (Ochr.eval n true w none) stB bh₂ (r, T?) st₂ ∧
      Runs (Ochr.dropTopBind n) (st₂.withTempT r T?) bh₃ () st₃ ∧
      Kern st₃ (st'.withTempT v T?) ∧ ModeEq st₃ st' ∧
      DecTab D st₁ ∧ DecTab D st₂

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
      DecTab D st₁ ∧ Quiet st₁ st₂ ∧ KeepsInv st₁ st₂ ∧ ModeEq st₁ st' ∧ ckVarPos st₂.env i = some (.bind f j) ∧
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
    Mode st' ∧ ∃ st₁, Quiet st st₁ ∧ KeepsInv st st₁ ∧ v = .borrow st₁.nextLoan b.val ∧ T? = some (.tRef .tNat) ∧
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
      DecTab D st₁ ∧ Quiet st₁ st₂ ∧ KeepsInv st₁ st₂ ∧ ModeEq st₁ st' ∧ ckVarPos st₂.env i = some (.bind f j) ∧
      st₂.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧ b.val = .borrow l w ∧
      ((∀ l', (valAt st₂.env (.bind f j)).sitesOf l' (.bind f j) [] = []) →
        Kern { st₂ with env := Env.setAtE st₂.env (.bind f j) (.borrow l v₀) } st') ∧ v = .unit ∧ T? = some .tUnit

/-- **`evalCore` of a typed `u; w`** (`Machine.evalCore`'s `.seq`), for a first part whose value
holds no borrow and no loan: `u` evaluated with no hint from the entry's kernel, in mode, the
one-shot flag clear; its value dropped (`dropValue`: nothing ends; a value holding a loan has its
borrowers ended, `endLoansOfTopTemp`, so the loans' condition is needed; lead8); `w` evaluated with
no hint (a typed run's tail) in the sequence's tail position, the mode after `u` carried to `w`'s
entry (`ModeEq`, as `LetInv`; lead9: first stated as `Mode stW`, which no inversion of `.seq` alone
gives, `u`'s end mode being `u`'s run's fact). The invariant where `w` starts is the caller's
(`InvPopInert`, lead9; first stated here as a conjunct, dropped with `InvCore`). -/
def SeqInv : Prop :=
  ∀ (n : Nat) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.seq u w) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ stW : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ bh₂ : Nat),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧
      (stW.tailDecl = none ∨ stW.tailDecl = st.curDecl) ∧ Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      DecTab D st₁ ∧ ((∀ l, v₀.holdsBorrow l = false) → v₀.loans = [] → Kern st₁ stW) ∧ ModeEq st₁ stW ∧
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
    v = w ∧ (typed = true → T? = some .tNat) ∧ Mode st' ∧ ∃ st₁, Quiet st st₁ ∧ KeepsInv st st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var 1)) = true →
        Kern { st₁ with env := Env.setAtE (Env.setAtE st₁.env (.bind 0 1) .bot) (.bind 0 0) w } st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var 1)) = false →
        Kern { st₁ with env := Env.setAtE (Env.setAtE st₁.env (.bind 0 1) .bot) (.bind 0 0) .bot } st')

/-! ## The invariant across the state changes the columns' steps make (lead9; for the machine lane)

`InvCore` is dropped (docs/31 D116): stated over every state and run of the columns' terms, it was
the whole checker's well-formedness preservation. Instead each step carries `Inv` from where it has
it (its entry, or a sub-step's conclusion) through the EXACT state change its inversion fact
concludes, by one of the lemmas below, each "`Inv` before, the change, `Inv` after", reading no run.
`Inv` under `Kern` is free (`Kern a b` gives `a.norm = b.norm`); a private computation's stretch
(`Quiet`) is its inversion fact's (`KeepsInv`, `InvExpectTy`). `Inv` erases temporaries' stored
types, so a temporary's `T?` is free. A pushed binding's reading is `.other` (for a borrow, `.ref
.other`): every reading the columns bind; a reading `.ind n _` would ask the value fit `n` ((V)). -/

/-- A number or `()` pushed as a temporary (`Z`, `S`, a read's value, a write's `()`). -/
def InvPushInert : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (v : Value) (T? : Option Value),
    (v.Num ∨ v = .unit) → Inv D Γ st.norm → Inv D Γ (st.withTempT v T?).norm

/-- The top temporary, a number or `()`, popped (`S` takes its argument's value; `;` drops `()`). -/
def InvPopInert : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (v : Value) (T? : Option Value),
    (v.Num ∨ v = .unit) → Inv D Γ (st.withTempT v T?).norm → Inv D Γ st.norm

/-- A binding holding a number set to `⊥` (a move out of a variable). -/
def InvSetBot : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (f j : Nat),
    (valAt st.env (.bind f j)).Num → Inv D Γ st.norm →
    Inv D Γ { st with env := Env.setAtE st.env (.bind f j) .bot }.norm

/-- A binding holding a number overwritten by a number (`x.0 := u` at `Nat`: `S(w)` to `S(v₀)`). -/
def InvSetNum : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (f j : Nat) (v₀ : Value),
    (valAt st.env (.bind f j)).Num → v₀.Num → Inv D Γ st.norm →
    Inv D Γ { st with env := Env.setAtE st.env (.bind f j) v₀ }.norm

/-- The value in flight, a number, moved into a binding pushed at `Nat` read `.other` (`let`'s push:
the temporary that parked it is gone, the binding holds it). -/
def InvBindNum : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (h : Hint) (v : Value) (T? : Option Value) (p : Bool),
    v.Num → 0 < st.env.size → Inv D Γ (st.withTempT v T?).norm →
    Inv D Γ { st with env := Env.pushBindE st.env h (some .tNat) v p .other }.norm

/-- The value in flight, a borrow of a number, moved into a binding pushed at `&Nat` read `.ref .other`
(`let y = &x`'s push). -/
def InvBindBorrow : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (h : Hint) (l : Nat) (w : Value) (T? : Option Value)
    (p : Bool),
    w.Num → 0 < st.env.size → Inv D Γ (st.withTempT (.borrow l w) T?).norm →
    Inv D Γ { st with env := Env.pushBindE st.env h (some (.tRef .tNat)) (.borrow l w) p (.ref .other) }.norm

/-- The top binding, `⊥` or a number, popped (`let`'s drop; the tail's value parked above it). -/
def InvPopBind : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (fr : Frame) (b : Binding),
    st.env[st.env.size - 1]? = some fr → fr.binds.back? = some b → (b.val = .bot ∨ b.val.Num) →
    Inv D Γ st.norm → Inv D Γ { st with env := Env.popBindE st.env }.norm

/-- A binding holding a number at `Nat` lent at the counter, the borrow in flight (`&x`), where no
loan is live. -/
def InvLend : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (f j : Nat) (b : Binding) (T? : Option Value),
    st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.val.Num → b.ty = some .tNat →
    (∀ l, liveLoan st.env l = false) → Inv D Γ st.norm →
    Inv D Γ (({ st with env := Env.setAtE st.env (.bind f j) (.loan st.nextLoan), nextLoan := st.nextLoan + 1 } :
      MState).withTempT (.borrow st.nextLoan b.val) T?).norm

/-- A write through a borrow binding holding a number: the borrow now holds the written number
(`*y := u`). -/
def InvWriteDeref : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (f j l : Nat) (w v₀ : Value),
    valAt st.env (.bind f j) = .borrow l w → w.Num → v₀.Num → Inv D Γ st.norm →
    Inv D Γ { st with env := Env.setAtE st.env (.bind f j) (.borrow l v₀) }.norm

/-- The end of a borrow by an access to its lender (`B`'s read of `x`): one frame, `x ↦ loan_l`, `y ↦
borrow_l w`; `y` set to `⊥`, `x` to `w` (then read by a copy) or `⊥` (a move). -/
def InvEndRead : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (l : Nat) (w xv : Value),
    allPos st.env = [.bind 0 0, .bind 0 1] → valAt st.env (.bind 0 0) = .loan l →
    valAt st.env (.bind 0 1) = .borrow l w → w.Num → (xv = w ∨ xv = .bot) → Inv D Γ st.norm →
    Inv D Γ { st with env := Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv }.norm

/-- The state-level lemmas together (the columns' steps take the bundle). -/
structure InvSteps : Prop where
  pushInert : InvPushInert
  popInert : InvPopInert
  setBot : InvSetBot
  setNum : InvSetNum
  bindNum : InvBindNum
  bindBorrow : InvBindBorrow
  popBind : InvPopBind
  lend : InvLend
  writeDeref : InvWriteDeref
  endRead : InvEndRead
  expectTy : InvExpectTy

end Ochr.Meaning.Steps.Form
