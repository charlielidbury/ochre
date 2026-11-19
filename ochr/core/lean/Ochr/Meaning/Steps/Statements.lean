import Ochr.Meaning.Lemmas
import Ochr.Meaning.HintIndep
import Ochr.Meaning.DecisionsInst
import Ochr.Meaning.Program
import Ochr.Meaning.WF
import Ochr.Machine
import Ochr.Check

/-!
# The step statements (milestone 3), centralised

Re-normalisation (`nfSealed`, inside `substV`, `substEnv`, `endBorrow`, `refine`, `renormAll`)
may run a known callee's body, whose checker run is only *below* the callee's meaning (an early
end inside it), so those steps are stated `⊑`/`Below`, not exact; the leaf's wholeness turns
`⊑` into equality where the main theorem needs it.

Every step lemma of the skeleton as a `Prop` indexed by the fuel of the checker call it speaks
about: `X_stmt K ρ φ fuel`. `Steps/IH.lean` bundles them into `StepsIH fuel`, each area file
(`Steps/Borrow.lean`, …) proves `StepsIH fuel → X_stmt (fuel + 1)`, and `Steps/Knot.lean` ties
the knot by induction on fuel: the checker's functions are mutually recursive on fuel
(`endBorrow → substEnv → substV → nfSealed → eval`), so no step lemma is provable alone (the
pilot prover's finding), while this shape keeps the files independently provable and the import
order irrelevant. The spine owns every definition and statement here; provers own only the area
files' proofs and their private auxiliaries.

Statement fixes from the pilot (`spine-prover-borrow`, Scratch.lean): a value a step returns is
in flight and counts as a temporary of the state (`MState.withTemp`) for `Good` and `Below`
(readPlace, borrowPlace); an assigned value is itself part of a `Good` state (assignPlace); a
dropped or popped position means `err` on both sides (`Env.mean` is bounds-checked); [Access] is
stated as the checker's composite `accessPath; accessInside` against `SState.access`.

**THE `Below` FORM IS FALSE; migration in progress (docs/31 D20 item 1; second lead,
2026-11-13).** A statement that runs the reference from `SM' K ρ st` and concludes
`Below (MState.mean … st') s'.toMean` is false once a borrow has been held: `Below` compares
temporaries by position, the reference keeps the temporary a borrow was parked in and the checker
has none (`Regress/StaleTemp.lean`, on `let r = &y; ()`). Nor do two such statements compose. The
form to state a step in is the simulation form: from ANY reference state `s` with
`Rel K ρ φ π st s`, concluding `Rel` after (`Steps/Sim.lean`: `Rel.start`, `sim_seq`).
`Rel` compares a binding's Π-shape and asks a renaming only of the labels that occur (docs/31 D22,
D23: both were first left out, and both omissions made the migrated statements false).
`Rel` compares meanings by EQUALITY (D24: `⊑` admitted states from which a match's join and `Id`
differ). Since D29 (main's D90: when a borrow ends is a decision every run shares) the reference
ends borrows statically, as the checker does, and `Rel` carries no list of borrows the checker
ended early and no loan witness (D27's `Wit`, deleted): it compares holders both ways and where
each live borrow is lent.
MIGRATED: `evalCore_step_stmt`, `eval_step_stmt`, `letIn_step_stmt` (the three refuted); the match
area (`evalMatch`, `evalMatchInd`, `evalMatchByType`, `closeBlock`, and the join's `joinEntry_stmt`,
`joinDrop_step_stmt`); the observation area (`observe`, `footprint_coverage`, `idType`) and `eq`
(D26). NOT YET:
every other statement here with a `Below (MState.mean … st') s'.toMean` conjunct against a run
from `SM'` (the leaves: read, borrow, assign, access, drop, pop; matches, calls, `J`, [Close], the
tail forms). Do not start a step proof against a `Below` conjunct.

**No knot hypothesis (docs/31 D18).** A state is read through `K.M = codeMeaning K`, which reads
each sealed program, closure and Π-closure by the run at the assignment and future asked; `K.C`
supplies the globals only. The induction hypothesis an area file gets is at every assignment and
future (`∀ ρ φ, StepsIH K ρ φ fuel`): a step's statement reads its state at other futures
(`Below`, `Mean.semEnd`, `Membership`) and hands on an extended assignment.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-! ### The run context is the checker state's (docs/31 D20, item 6)

Every statement quantifies over a run context `K`, and used to tie only `K.Δ` to the state. The
rest was free: `K.Γ` (a constructor of a declared type has no meaning at `K.Γ = []`), the data
model's coverage of it, and `K.C.global` (`.const n` means `K.C.global n`, so
`evalCore_step_stmt` was false at a `K.C.global` that is not Σ's: `Regress/ConstFree_70247f07.lean`,
kernel-checked). `CtxOk K ρ st` is the one hypothesis that ties them. -/

/-- `K.C.global` is Σ: each global of the state has its stored type, a constant means its stored
value read at that type (`⋆` at a proposition, as `evalCore`'s `.const` reads it), a function means
the closure of its `fix` term formed in the empty frame, with its Π-shape, and each is a member of
its type. The last is the outer induction of docs/18's theorem: while a definition is checked,
every global is an earlier, accepted one. A global is closed, so these hold at every assignment
and future. -/
structure GlobalsOk (K : RunCtx) (st : MState) : Prop where
  ty : ∀ n g, st.globals.find? (·.name == n) = some g → ∀ ρ,
    (K.C.global n).2.m = (meanV K ρ noFuture (.plain .err) g.ty).asTy
  const : ∀ n g, st.globals.find? (·.name == n) = some g → g.fn? = none → ∀ ρ φ,
    (K.C.global n).1 = constMean (K.C.global n).2.m (meanV K ρ φ (K.C.global n).2 g.val)
  fn : ∀ n g t, st.globals.find? (·.name == n) = some g → g.fn? = some t → ∀ ρ φ,
    (K.C.global n).1 = meanV K ρ φ (.plain .err) (.clo [] t []) ∧
    (K.C.global n).2.shape = (piShapeOf K ρ φ (stateOf 0 []) t).map fun sh => (sh.ps, sh.out)
  mem : ∀ n g, st.globals.find? (·.name == n) = some g → (K.C.global n).1 ∈ₛ (K.C.global n).2.m

/-- The run context is the checker state's: its declarations, a data model that speaks for each,
Δ at the state's unknowns (`DeltaOk`), globals with no label (`run_congr`'s `hK`), and Σ
(`GlobalsOk`). A hypothesis of every statement. -/
structure CtxOk (K : RunCtx) (ρ : Assignment) (st : MState) : Prop where
  inds : K.Γ = st.inds
  covers : ∀ d ∈ K.Γ, K.dm.covers d
  delta : DeltaOk K ρ st
  noLabel : ∀ n, (K.C.global n).2.label = none
  globals : GlobalsOk K st

/-! ### Helpers from `Steps/Borrow.lean` -/

/-- `runMachine` from a given log. -/
def runMachineL {α : Type} (x : M α) (st : MState) (fuel : Nat) (L : Array LogEntry) :
    Outcome α × Nat × Array LogEntry :=
  let ((r, fl), log) := (((((x.run st).run).run).run ⟨fuel⟩).run L)
  let o := match r with
    | .error e => Outcome.exhausted e.msg
    | .ok (.error f) => .fail f
    | .ok (.ok (a, st')) => .ok a st'
  (o, fl.left, log)

theorem runMachine_eq_L {α : Type} (x : M α) (st : MState) (fuel : Nat) :
    runMachine x st fuel = runMachineL x st fuel #[] := rfl

/-- `f` run from `st`, with the budget `fuel`, succeeds with `a` and `st'`, from SOME starting log.
The log is a trace the checker only appends to; a run nested in a `do` block starts from the log
the steps before it left, and a statement about it must apply there (the drop at the join's loop,
docs/31 D29, task C). As first written (from the empty log only) a statement about a step could
not be used at its nested occurrences. The top-level run (`runMachine`, the empty log) is a case. -/
def Runs {α : Type} (f : M α) (st : MState) (fuel : Nat) (a : α) (st' : MState) : Prop :=
  ∃ L left log, runMachineL f st fuel L = (.ok a st', left, log)

theorem Runs.of_runMachine {α : Type} {f : M α} {st : MState} {fuel : Nat} {a : α} {st' : MState} {left : Nat}
    {log : Array LogEntry} (h : runMachine f st fuel = (.ok a st', left, log)) : Runs f st fuel a st' :=
  ⟨#[], left, log, h⟩

/-- The meaning of a checker state as the run sees it (read through `K.M`; `CtxOk K ρ st` is a
hypothesis of every statement). -/
noncomputable def SM' (st : MState) : SState := MState.sstate K.dm K.M K.Γ ρ st

/-- A step is exact: the meanings agree at every position and so do the shapes. -/
def Exact (m m' : Mean) : Prop := (∀ φ p, m.val φ p = m'.val φ p) ∧ ∀ p, m.shape p = m'.shape p

/-! ### The simulation relation (docs/31 D20 item 1, D29; `Steps/Sim.lean` has the account) -/

/-- The checker's state `m'` and the reference state `s` at the SAME future, up to the renaming
`π` of the checker's labels to the reference's, over the futures `F` (docs/31 D29, point 4):
- bindings mean the same, position by position (the two push and drop bindings in step);
- a binding holds the borrow `l` in the checker exactly when it holds `π l` in the reference;
- a borrow a temporary of the checker holds (a value in flight) is held under `π l` by some
  temporary of the same frame of the reference, with the same content, and every borrow a
  temporary of the reference holds is one the checker's temporaries hold (renamed).
Temporaries are otherwise not compared: the reference parks a borrow in a temporary until it is
bound and leaves the temporary behind, the checker carries a value in flight in its monad
(`Regress/StaleTemp.lean`). With the holders compared both ways, the live labels correspond one
to one (with `Rel.inj`).

The meanings compared are EQUAL, not `⊑` (docs/31 D24: with `⊑` the relation admitted a reference
state holding a value where the checker's holds `⊥` inside a partly moved tuple, from which a
match's join and `Id` differ). Since D29 there are no borrows the checker ended early: the two
end the same borrows at the same steps, so the comparison needs no list of early ends. -/
def SimEq (π : Nat → Nat) (F : Future → Prop) (m' : Mean) (s : SState) : Prop :=
  (∀ ψ, F ψ → ∀ p, ¬ IsTemp p → m'.val (fun l => ψ (π l)) p = s.valAt p ψ) ∧
  (∀ p l, ¬ IsTemp p → m'.shape p = some l → s.shape p = some (π l)) ∧
  (∀ p l', ¬ IsTemp p → s.shape p = some l' → ∃ l, m'.shape p = some l ∧ π l = l') ∧
  (∀ f i l, m'.shape (.temp f i) = some l →
    ∃ j, s.shape (.temp f j) = some (π l) ∧
      ∀ ψ, F ψ → m'.val (fun l => ψ (π l)) (.temp f i) = s.valAt (.temp f j) ψ) ∧
  (∀ f j l', s.shape (.temp f j) = some l' → ∃ i l, m'.shape (.temp f i) = some l ∧ π l = l')

/-- The old order without its positional reading of temporaries: for every future of the lower
state, a future of the upper at which bindings are below position by position and a borrow in
flight is held, by label, with a content above. Implied by `Below` (`Sim.of_below`); true where
`Below` is false (`Regress/StaleTemp.lean`). -/
def Sim (m' : Mean) (s : SState) : Prop :=
  ∀ φ', ∃ φ,
    (∀ p, ¬ IsTemp p → m'.val φ' p ⊑ s.valAt p φ) ∧
    (∀ p l, ¬ IsTemp p → m'.shape p = some l → s.shape p = some l) ∧
    (∀ f i l, m'.shape (.temp f i) = some l →
      ∃ j, s.shape (.temp f j) = some l ∧ m'.val φ' (.temp f i) ⊑ s.valAt (.temp f j) φ)

theorem Sim.of_below {m' : Mean} {s : SState} (h : Below m' s.toMean) : Sim m' s := fun φ' => by
  obtain ⟨φ, hv, hs⟩ := h φ'
  exact ⟨φ, fun p _ => hv p, fun p l _ hl => hs p l hl, fun f i l hl => ⟨i, hs _ l hl, hv _⟩⟩

/-- What `run` reads of a binding besides its meaning: its type's meaning, Π-shape and data, and
its declared reading. (The label a type recorded when it was bound is read by no clause.)

The Π-shape was left out when `Rel` was first stated, as an open lemma. Without it the relation
admits a reference state whose bindings have lost their shapes, from which every call through a
variable fails, so the statements in the simulation form were false of any accepted call through
a variable (docs/31 D22; third lead). With it, a step that binds must show the shapes agree: the
type conjunct of `evalCore_step_stmt` (`StrAgree`), which rests on `piShape_step_stmt` at a
Π-term and is FALSE today where the run drops structure (a call's result, a field read:
`Regress/ShapeAgree.lean`, the audit's A11, A12, A18). -/
def bindSkel (b : SBinding) : TyM × Option (List PiParam × PiOut) × Option (String × List Sem) × DeclInfo :=
  (b.ty.m, b.ty.shape, b.ty.data, b.decl)

/-- The futures a relation compares at: those that agree with the run's `φ` off the reference's
live labels (a binding holding an inert loan means the constant `φ ℓ` in the reference and `ψ ℓ`
in the checker's state, D20 item 2). Every read the reference run makes of its state is at such a
future (docs/31 D29, point 3), so this is what pins the run. -/
def RelF (φ : Future) (s : SState) (ψ : Future) : Prop := ∀ l, ¬ s.Live l → ψ l = φ l

/-- **The reference state `s` simulates the checker's state `st`** (docs/31 D29, point 4), for a
reference run at the future `φ`, with the checker's labels renamed by `π`. -/
structure Rel (π : Nat → Nat) (st : MState) (s : SState) : Prop where
  /-- the same frames, each with the same bindings at the same types and readings -/
  skel : (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel)
  /-- every label that occurs in the checker's state is renamed to one the reference has issued,
  so the next labels the two issue are new on both sides. Only a label that OCCURS: the checker
  issues labels inside private copies and keeps its counter (D37), the reference restores its
  own, and as first stated (every label below the checker's counter) the clause had no renaming
  once the checker had issued more labels than the reference, in particular after any proof or
  type that borrows from a state whose counter is `0` (`Regress/CopyLabels.lean`). A label issued
  inside a copy occurs nowhere after it (docs/31 D23, (WF11)). -/
  fresh : ∀ l, l < st.nextLoan → st.Occurs l → π l < s.nextLoan
  /-- the same meanings, holders and borrows in flight, at every future that leaves the live
  labels free -/
  sim : SimEq π (RelF φ s) (MState.mean K.dm K.M K.Γ ρ st) s
  /-- the renaming is one to one on the checker's live labels -/
  inj : ∀ l l', liveLoan st.env l = true → liveLoan st.env l' = true → π l = π l' → l = l'
  /-- each live borrow is lent at the same places, in the same way (fill or loan), on both sides:
  the reference's [Access] reads these, the checker's reads its values (`Env.sitesOf`) -/
  sites : ∀ l, liveLoan st.env l = true → ∀ x, x ∈ s.lent (π l) ↔ x ∈ Env.sitesOf st.env l

/-! ### Helpers from `Steps/Eq.lean` -/

/-- The truth of a type value read as a proposition. -/
noncomputable def propOf (P : Value) : Prop := ((meanV K ρ φ (.plain .err) P).asTy).true

/-! ### Helpers from `Steps/Borrow.lean` -/

/-- The content of a borrow in a (WF10) state is hint-free when it holds no sealed program: what
[End]'s substitution needs (`substV_loan_step_stmt`'s `hf`), discharged from the clause. -/
theorem hintFree_of_wf10 (st : MState) (hwf : WF10 K.Γ st) (v : Value)
    (hv : v ∈ Env.values st.env) (l : Nat) (w : Value) (hvw : v = .borrow l w)
    (hs : w.anyAtom Value.isSealed = false) : HintFree K ρ φ w := by
  have hb := hwf v hv
  subst hvw
  simp only [Value.anyAtom, Value.bareCtor, Bool.false_or] at hb
  exact hintFree_of_recorded K ρ φ w hb hs

/-- A top-hint-free value (its parameters recorded, its sealed programs with hint-free tails:
[Close]'s results and fills) is `HintFree`: the substitution lemmas' hypothesis at [End] on a
borrow of a closed-off call's result, `HintIndep.lean`. -/
theorem hintFree_of_topHintFree (w : Value) (hw : Value.topHintFree K.Γ w = true) : HintFree K ρ φ w :=
  fun h h' => meanV_hintIndep K ρ φ w hw h h'

/-! ### Helpers from `Steps/Call.lean` -/

/-- The callee as the run sees it: its meaning and its type value's shape. The shape is read
through the run of the type value (the `.pi` clause of `run`); a callee whose type is not a
Π-type has none. -/
noncomputable def calleeRes (fv : Value) (fT : Value) : Res :=
  (meanV K ρ φ (.plain .err) fv,
    match fT with
    | .tPi caps t rd =>
      match piShapeOf K ρ φ (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) t with
      | some sh => ⟨(meanV K ρ φ (.plain .err) fT).asTy, some (sh.ps, sh.out), none, none⟩
      | none => .plain .err
    | _ => .plain .err)

/-- The arguments as the run sees them, with each borrow argument's label. -/
noncomputable def argsRes (ws : Array Value) : List Res :=
  ws.toList.map fun w => (meanV K ρ φ (.plain .err) w,
    ⟨.err, none, (match w with | .borrow l _ => some l | _ => none), none⟩)

/-! ### Helpers from `Steps/Match.lean` -/

/-- `ρ'` extends `ρ` on the unknowns of `st`. -/
def Extends (st : MState) (ρ ρ' : Assignment) : Prop := ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ

/-! ### Helpers from `Steps/Obs.lean` -/

/-- The reference observation of a side, if its run succeeds: the result and the positions the side
started with (the audit's A5), as `run`'s `.id` clause reads it. -/
noncomputable def refObs (reps : List Place) (ws : List Sem) (hint : TyS) (t : Term) (s : SState) : Option (List Sem) :=
  (run K ρ φ hint t s).map fun (r, s') => observation φ reps ws s.positions r s'

/-! ### Helpers from `Steps/Eval.lean` -/

/-- The type the context gives, as a `TyM` (`err` when none). -/
noncomputable def hintM (hint : Option Value) : TyS :=
  (hint.map (Value.tyS K.dm K.M K.Γ ρ)).getD (.plain .err)

/-- [End ℓ] (`Machine.endBorrow`) in the simulation form (docs/31 D29): from any related reference
state, the checker's end of a live borrow `ℓ` is the reference's `endLabel (π ℓ)`: the meanings
are `semEnd`'s (the substitution is fixing the future, `meanV_substLoan`; re-normalisation keeps
a meaning; a mark has none), the holder is forgotten on both sides, and the places `ℓ` was lent
pass to the borrows of its content alike (main's `lendEnv (.ended ℓ …)` against `SState.relend`).
`Good` is kept. The content is whole, which the checker checks outside an observation (D53 (h),
D68). (As first stated, in the order form against `Mean.semEnd` from the checker's own state.) -/
def endBorrow_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s) (hl : liveLoan st.env l = true)
    (bh : Nat) (h : Runs (Ochr.endBorrow fuel l) st bh () st'),
    Rel K ρ φ π st' (s.endLabel (π l)) ∧ Good K.dm K.M K.Γ ρ st'

/-- [Access] as the checker performs it before a read (`accessPath` then `accessInside`), in the
simulation form (docs/31 D29): it ends the borrows lent on the path, at the place or inside its
content, iterated, which is the reference's static access of the place (`dataHit`), whose sites
the relation makes the checker's. (`accessPath` alone ends only the path: the pilot prover's
finding, so it is not stated on its own.)

With `owned` (before an assignment, D67) the checker ends only the loans inside the part the
place owns: none at a borrow variable written whole, where the reference's assignment does no
access either (`assignAt`; the audit's A2). -/
def access_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (p : Place) (pos : Pos) (owned : Bool) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s p = some (pos, (p.steps).2))
    (bh : Nat) (h : Runs (do Ochr.accessPath fuel p; Ochr.accessInside fuel p owned) st bh () st'),
    Rel K ρ φ π st'
      (if owned && (p.steps).2.isEmpty && (s.shape pos).isSome then s else s.access pos (dataHit (p.steps).2)) ∧
    Good K.dm K.M K.Γ ρ st'

/-- The flight of a result: its label, typed at its content type (the reference's result type
carries both). The in-flight value is typed by this where `MState.withTemp` holds it untyped
(`GoodF`, the pilot's refutations in `BorrowCE.lean`). -/
def flightOf (T : TyS) : Flight := match T.label with | some l => [(l, T.m)] | none => []

/-- The flight of a value about to be written at a place of content type `T`: a borrow's label,
typed at `T`. -/
def flightOfWrite (v : Value) (T : TyM) : Flight := match v with | .borrow l _ => [(l, T)] | _ => []

/-- [Read] (`readPlace`): after its access, the result is the place's meaning (future-free), and
the place is unchanged (a copy, by the declared reading, D80) or `moved` (a move); exact against
the run's `readPlace` with the same copy decision (`Decisions.copy`, aligned). -/
def readPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value) (copy : Bool)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf (SM' K ρ st)) p) = copy)
    (bh : Nat) (h : Runs (Ochr.readPlace fuel p) st bh v st'),
    ∃ r s', Ochr.Meaning.readPlace K φ p copy (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Below (MState.mean K.dm K.M K.Γ ρ (st'.withTemp v)) s'.toMean ∧
      GoodF K.dm K.M K.Γ ρ (st'.withTemp v) (flightOf r.2)

/-- [Borrow] (`borrowPlace`): exact against the run's `borrowPlace` with the same fresh label
(`nextLoan`): the place means the label's final content and the borrow the old content. -/
def borrowPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.borrowPlace fuel p) st bh v st'),
    ∃ r s', Ochr.Meaning.borrowPlace K φ p (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Below (MState.mean K.dm K.M K.Γ ρ (st'.withTemp v)) s'.toMean ∧
      GoodF K.dm K.M K.Γ ρ (st'.withTemp v) (flightOf r.2)

/-- [Assign] (`assignPlace`): the owned access (D67, ends), the old content's borrows end
([Drop], ends), then the place means the new value and, at a root, holds the borrow written:
below the run's `assignAt` (the `.assign` clause's tail, `Run.lean`). The written value's meaning
is given, and its label is the borrow's. (As first stated, against `setContent` after a full
`access`, it missed the old borrow's end and the new one's hold, and was false at a borrow
variable written whole: the audit's A2.) -/
def assignPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hpos : resolve (SM' K ρ st) p = some (pos, (p.steps).2))
    (hgv : GoodF K.dm K.M K.Γ ρ (st.withTemp v) (flightOfWrite v (Env.hintAt K.dm K.M K.Γ ρ st.env pos).m))
    (bh : Nat) (h : Runs (Ochr.assignPlace fuel p v) st bh () st'),
    ∃ r s', assignAt K φ p (meanV K ρ φ (.plain .err) v) (match v with | .borrow l _ => some l | _ => none)
        (SM' K ρ st) = some (r, s') ∧
      Below (MState.mean K.dm K.M K.Γ ρ st') s'.toMean ∧ Good K.dm K.M K.Γ ρ st'

/-- [Drop] of the top binding (`dropTopBind`): its borrows end, each live loan in it ends its
borrower when held in a binding (D65), then the binding is gone: ends followed by `forget`,
below. -/
def dropTopBind_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.dropTopBind fuel) st bh () st'),
    Below (MState.mean K.dm K.M K.Γ ρ st') ((SM' K ρ st).dropLast).toMean ∧
    Good K.dm K.M K.Γ ρ st'

/-- Popping a frame (`popFrame`): each binding dropped in turn; below. -/
def popFrame_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    -- the popped frame's temporaries hold no borrow (the pilot's refutation: a pop discards
    -- temporaries without ending them; both call sites move the result below first)
    (htemps : ∀ fr, st.env[st.env.size - 1]? = some fr → ∀ v ∈ fr.temps, v.hasBorrow = false)
    (bh : Nat) (h : Runs (Ochr.popFrame fuel) st bh () st'),
    Below (MState.mean K.dm K.M K.Γ ρ st') (MState.mean K.dm K.M K.Γ ρ st) ∧
    Good K.dm K.M K.Γ ρ st'

/-- `substV` of a loan: the result means the value read under the future fixed at `ℓ` to the
filling value's meaning (the pure lemma plus re-normalisation). -/
def substV_loan_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (w v v' : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hw : ¬ w.hasLoanM l) (hf : HintFree K ρ φ w)
    (bh : Nat) (h : Runs (Ochr.substV fuel (.loan l) w v) st bh v' st'),
    meanV K ρ φ hint v' ⊑ meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v ∧ st'.core = st.core

/-- `substV` of an abstract value by a refinement `r` it means: exact. -/
def substV_abs_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r v v' : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hσ : ρ σ = meanV K ρ φ (.plain (MState.absTyM K.dm K.M K.Γ ρ st σ)) r)
    (bh : Nat) (h : Runs (Ochr.substV fuel (.abs σ) r v) st bh v' st'),
    (∀ φ, meanV K ρ φ hint v' ⊑ meanV K ρ φ hint v) ∧ st'.core = st.core

/-- `substEnv` of a loan (the state-wide half of [End] and of [Close]'s fills): every position
reads the fixed future; stored types are untouched (`types = false`: no type holds a loan). -/
def substEnv_loan_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (w : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hw : ¬ w.hasLoanM l) (hf : HintFree K ρ φ w)
    (bh : Nat) (h : Runs (Ochr.substEnv fuel (.loan l) w false) st bh () st'),
    (∀ p, (MState.mean K.dm K.M K.Γ ρ st').val φ p ⊑
        (MState.mean K.dm K.M K.Γ ρ st).val (φ.upd l (meanV K ρ φ (.plain .err) w)) p) ∧
    (∀ p, Env.shape st'.env p = Env.shape st.env p)

/-- `substEnv` of an abstract value by a refinement it means (`types = true`: stored types, Δ
and the goal are refined too): exact, and `Good` is kept. -/
def substEnv_abs_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hσ : ρ σ = meanV K ρ φ (.plain (MState.absTyM K.dm K.M K.Γ ρ st σ)) r)
    (bh : Nat) (h : Runs (Ochr.substEnv fuel (.abs σ) r true) st bh () st'),
    Below (MState.mean K.dm K.M K.Γ ρ st') (MState.mean K.dm K.M K.Γ ρ st) ∧
    Good K.dm K.M K.Γ ρ st'

/-- [Seal]: a re-run of a sealed program means the sealed program (its run), and changes nothing
of the state's core (it runs on a private copy). -/
def nfSealed_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (v : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.nfSealed fuel t) st bh v st'),
    (∀ φ, meanV K ρ φ hint v ⊑ meanV K ρ φ hint (.sealed t)) ∧ st'.core = st.core

/-- `canonNeutral`: a sealed program already generalised in this world is its `σ`, which the
path condition makes mean the same. -/
def canonNeutral_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (v v' : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.canonNeutral v) st bh v' st'),
    (∀ φ, meanV K ρ φ hint v' = meanV K ρ φ hint v) ∧ st'.core = st.core

/-- `renormAll`: re-running every sealed program of the state keeps every meaning. -/
def renormAll_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.renormAll fuel) st bh () st'),
    Below (MState.mean K.dm K.M K.Γ ρ st') (MState.mean K.dm K.M K.Γ ρ st) ∧
    Good K.dm K.M K.Γ ρ st'

/-- [Split]'s refinement `σ := r` (`refine`): under an assignment that gives `σ` the meaning of
`r` (the arm the assignment selects, with its fields assigned), the substitution is exact and
`Good` is kept; the record in `refs` states no fact. -/
def refine_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hσ : ρ σ = meanV K ρ φ (.plain (MState.absTyM K.dm K.M K.Γ ρ st σ)) r)
    (bh : Nat) (h : Runs (Ochr.refine fuel σ r) st bh () st'),
    Below (MState.mean K.dm K.M K.Γ ρ st') (MState.mean K.dm K.M K.Γ ρ st) ∧
    Good K.dm K.M K.Γ ρ st'

/-- `Eq` computes soundly: whatever `mkEqM` returns means `⟦a⟧ = ⟦b⟧` at `A`, and the state's
core is unchanged. -/
def mkEqM_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (A a b P : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hA : ∀ φ, (meanV K ρ φ (.plain .err) A).asTy = (meanV K ρ noFuture (.plain .err) A).asTy)
    (bh : Nat) (h : Runs (Ochr.mkEqM fuel A a b) st bh P st'),
    (∀ φ, propOf K ρ φ P ↔
      meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) a = meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) b) ∧
    st'.core = st.core

/-- Conversion is sound: two values convertible at a state, both (partly moved) members of one
type, have equal meanings under every future. The accepting direction only; `convStack` only
makes `conv` answer `false` more often, so no hypothesis on it. -/
def conv_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (v w : Value) (T : TyM)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hv : DataModel.pmem K.Γ (meanV K ρ φ (.plain T) v) T) (hw : DataModel.pmem K.Γ (meanV K ρ φ (.plain T) w) T)
    (bh : Nat) (h : Runs (Ochr.conv fuel v w) st bh true st'),
    meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w

/-- [Conv-pi]: convertible Π-type values have equal type meanings (equal Lean carriers), by
`funext` over the generic arguments, which range over the whole domain (docs/18 (V4)). -/
def convPi_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (P Q : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.convPi fuel P Q) st bh true st'),
    ∀ φ, (meanV K ρ φ (.plain .err) P).asTy = (meanV K ρ φ (.plain .err) Q).asTy

/-- [Conv-fun]: two function values with convertible observations of their generic calls mean
the same function (extensionality on good carriers, docs/18 (V5), `Slice.pi_ext`). -/
def convFn_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (f g : Value) (T : TyM)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hf : meanV K ρ φ (.plain T) f ∈ₛ T) (hgm : meanV K ρ φ (.plain T) g ∈ₛ T)
    (bh : Nat) (h : Runs (Ochr.convFn fuel f g) st bh true st'),
    meanV K ρ φ (.plain T) f = meanV K ρ φ (.plain T) g

/-- [Rewrite]: when the equation `h : Eq(A, a, b)` is true, the rewritten goal is true iff the
goal is (the occurrences replaced mean the same). -/
def rewriteGoal_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (rev : Bool) (hT : Term) (A a b G G' : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bhh : Nat) (hh : Runs (Ochr.eval fuel true hT) st bhh (.proof, some (.tEq A a b)) st)
    (bh : Nat) (h : Runs (Ochr.rewriteGoal fuel rev hT G) st bh G' st'),
    ∀ φ, propOf K ρ φ (.tEq A a b) → (propOf K ρ φ G' ↔ propOf K ρ φ G)

/-- The meaning of a type value does not depend on the future (docs/27 Lemma 5: no stored type
holds a live loan), at every state the checker reaches. Used to read types under `noFuture`. -/
def type_futureFree_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hT : ∃ p, MState.posTyM K.dm K.M K.Γ ρ st p = some (meanV K ρ noFuture (.plain .err) T).asTy),
    ∀ φ', (meanV K ρ φ (.plain .err) T).asTy = (meanV K ρ φ' (.plain .err) T).asTy

/-- A direct call (`callFn`, untyped or typed): below the reference's `callOf` on the callee's
meaning, and `Good` kept. The arguments are loan-free (WF5, `ArgsLoanFree`). -/
def callFn_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (fv : Value) (fT : Value)
    (ws : Array Value) (tys : Array (Option Value)) (hd : Bool) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hargs : ArgsLoanFree st.env ws)
    -- the callee as the run reads it (`closeCall_step_stmt`); `fT` is the checker's input only
    (fres : Res) (hf : run K ρ φ (.plain .err) (.val fv) (SM' K ρ st) = some (fres, SM' K ρ st))
    (bh : Nat) (h : Runs (Ochr.callFn fuel typed fv (some fT) ws tys hd) st bh (v, T?) st'),
    ∃ r s', callOf fres (argsRes K ρ φ ws) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.M K.Γ ρ st') s'.toMean ∧ Good K.dm K.M K.Γ ρ st'

/-- Running a body (`runBody`): the frame pushed with the captures and parameters, the body run,
the frame popped: below the function's meaning applied (the induction hypothesis on the body). -/
def runBody_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (cs : List Value) (t : Term)
    (rd : List (DeclInfo × Value)) (ws : Array Value) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hargs : ArgsLoanFree st.env ws)
    (hfv : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n)
    -- the callee as the run reads it (the pilot form took `fT` free: `Regress/CloseCallStmt.lean`)
    (fres : Res) (hf : run K ρ φ (.plain .err) (.val fv) (SM' K ρ st) = some (fres, SM' K ρ st))
    (bh : Nat) (h : Runs (Ochr.runBody fuel fv cs t rd ws) st bh v st'),
    ∃ r s', callOf fres (argsRes K ρ φ ws) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.M K.Γ ρ st') s'.toMean ∧ Good K.dm K.M K.Γ ρ st'

/-- [Close] (`closeCall`), every row: exact against `callOf`. The result is a sealed program (or
`()` at a declared `Unit`, or a borrow of one), and each lent place a fill: both mean what the
reference's call gives them, since a sealed program means its run.

The callee's meaning and shape are the run's reading of the value (`run (.val fv)`: a closure's
or Π-closure's shape from its term, a global's from `K.C`, an abstract value's from `Δ`; a sealed
callee has no shape yet, docs/31 item 3), not a separately quantified type (the pilot form took
`fT` free, so `fT := .zero` refuted it at once: `Regress/CloseCallStmt.lean`). The row and the
declared-`Unit` readings `kind`, `res`, `fills` and the cells' types `tys` are read off the call
as written (`evalCall`) and trusted; typing makes them agree with the callee's shape, which the
hypotheses `hkind`, `hres`, `hfills`, `htys` state (without them a `res := .unit` at a `Nat`
codomain, or a `fills` entry at a `Nat` cell, made the checker return `()` where the reference
returns the value: the same file). -/
def closeCall_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (fv : Value) (ws : Array Value)
    (kind : Kind) (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hargs : ArgsLoanFree st.env ws)
    (fres : Res) (hf : run K ρ φ (.plain .err) (.val fv) (SM' K ρ st) = some (fres, SM' K ρ st))
    (ps : List PiParam) (out : PiOut) (hsh : fres.2.shape = some (ps, out))
    (hkind : kind = .ref ↔ ∃ U, out = .ref U)
    (hres : res = .unit → ∀ B, out = .data B → B ((argsRes K ρ φ ws).map (·.1)) = .ty0 Unit)
    (hfills : ∀ i : Nat, fills.getD i false = true → ∀ p : PiParam, ps[i]? = some p →
      p.dom (((argsRes K ρ φ ws).map (·.1)).take i) = .ty0 Unit)
    (htys : ∀ (i l : Nat) (w : Value), ws[i]? = some (Value.borrow l w) → ∀ p : PiParam, ps[i]? = some p →
      ∃ T : Value, tys[i]? = some (some (Value.tRef T)) ∧
        (Value.tyS K.dm K.M K.Γ ρ T).m = p.dom (((argsRes K ρ φ ws).map (·.1)).take i))
    (bh : Nat) (h : Runs (Ochr.closeCall fuel fv ws kind res fills tys) st bh v st'),
    ∃ r s', callOf fres (argsRes K ρ φ ws) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Exact (MState.mean K.dm K.M K.Γ ρ st') s'.toMean ∧ Good K.dm K.M K.Γ ρ st'

/-- [Call-type] (`callType`, `declCallType`): the codomain at the arguments is the reference's
result type. -/
def callType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (piTy : Value) (ws : Array Value)
    (tys : Array (Option Value)) (B : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.callType fuel piTy ws tys) st bh B st'),
    ∀ ps out, (calleeRes K ρ φ .proof piTy).2.shape = some (ps, out) →
      (meanV K ρ noFuture (.plain .err) B).asTy =
        (match out with
          | .data B' => B' ((argsRes K ρ φ ws).map (·.1))
          | .ref U => U ((argsRes K ρ φ ws).map (·.1)))

/-- [Rec]'s accepting direction (`recCheck`), semantically: for a recursive function whose every
recursive call passes a strict subterm of the entry value, the stages of the `fix` clause
stabilise, so the closure's meaning is not `err` and the guard never fires (docs/24 §4, the
semantic form of [Rec]; `Slice.stage_stable` generalised). Stated on the closure value: its
meaning is a member of its Π-type. -/
def recCheck_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (fv : Value) (fT : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    -- `fT` is the value's own declared Π-type, as the checker reads it (the pilot form took it
    -- free: `fT := .zero` refuted it, the defect class of `Regress/CloseCallStmt.lean`)
    (hfT : ∃ bfT st', Runs (Ochr.funType? fuel fv none) st bfT (some fT) st')
    (hacc : ∃ fuel st', Runs (Ochr.checkFix fuel fv [] (match fv with | .clo _ t _ => t | _ => .tt)) st fuel () st'),
    meanV K ρ φ (.plain .err) fv ∈ₛ (meanV K ρ φ (.plain .err) fT).asTy

/-! ### The match area, in the simulation form (docs/31 D24; third lead)

The conclusion every statement of this area shares: the reference's run of the match from the
related state does not fail, the checker's value IS its result, and the two states after are
related, for an assignment extending `ρ` to the unknowns created and a renaming extending `π`. -/

/-- The conclusion of a step in the simulation form, for the reference computation `x` run from
`s`: `x` does not fail, the checker's value `v` (read at the run's future pulled back along the
renaming) is its result, and the states after are related, under an assignment that extends `ρ`
on the unknowns of `st` and a renaming that agrees with `π` on the labels `st` had issued. -/
def SimConcl (π : Nat → Nat) (st st' : MState) (s : SState) (x : Assignment → SM Res) (v : Value) : Prop :=
  ∃ ρ' π' r s', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
    x ρ' s = some (r, s') ∧
    meanV K ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    Rel K ρ' φ π' st' s' ∧ Good K.dm K.M K.Γ ρ' st'

/-- The checker's entry set of a match (`Machine.staticJoin`): every place under a variable of the
top frame whose content is `⊥`, at the grain of the value (`botPlaces`). -/
def entryOf (st : MState) : List Place :=
  match st.env.back? with
  | some fr => (List.range fr.binds.size).flatMap fun o =>
      botPlaces (fr.binds[fr.binds.size - 1 - o]!).val (.var o)
  | none => []

/-- **[Join], the entry set** (docs/31 D20 item 1 (e), D24, D29): from related states the
reference's entry set (`movedPlaces`) is the checker's (`entryOf`, `Machine.staticJoin`'s
`botPlaces`), in order. As first written the reference's set held whole variables only, and the
statement was false at any partly moved binding (`Regress/JoinProbes.lean`); then it carried the
borrow variables the checker had ended early, which no longer exist (D29). -/
def joinEntry_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s),
    movedPlaces φ s = entryOf st

/-- `q` takes a field step through `p` (the same root, `p`'s path, then a field step). -/
def FieldParent (p q : Place) : Prop :=
  p.steps.1 = q.steps.1 ∧ ∃ st rest, ((∃ i, st = Step.proj i) ∨ (∃ g, st = Step.field g)) ∧
    q.steps.2 = p.steps.2 ++ st :: rest

/-- **The join's grain** (main's D84, `Decide.jdGrain`): every field step of a dropped place is
through a place whose declared reading is an inductive of `Γ` with exactly one constructor. Through
anything else (several constructors, a type computed by a match, a type parameter, a number's
predecessor) the join moves the value whole, so no dropped place steps into it. A finding of the
drop's proof (docs/31 D29, task C): `Machine.movedPlace` re-roots a place that does not exist to
its longest existing prefix, η-refining or generalising that prefix only when its type has one
constructor; the reference never re-roots. Without the grain the two drop different places (the
checker the prefix whole, the reference the field), so the drop's statement needs it of its list,
which `Decisions.joinMoves`, aligned with `Decide.jdMoves`, provides. -/
def GrainOk (D : Decisions) (Γ : List IndDecl) (sc : List DeclInfo) (q : Place) : Prop :=
  ∀ p, FieldParent p q → ∃ n args d, D.placeDecl sc p = .ind n args ∧ Γ.find? (·.name == n) = some d ∧
    d.ctors.length = 1

/-- The reference's drop of one place (`joinDrop`'s fold body). -/
noncomputable def joinDropOne (K : RunCtx) (φ : Future) (s : SState) (q : Place) : SState :=
  match resolve s q with
  | some (pos, steps) => dropAt K φ q pos steps (accessLentPrefix pos steps s)
  | none => s

/-- **[Join], the drop of one place** (`Machine.joinDrop`'s loop body: `movedPlace`, then
`dropAtJoin`), in the simulation form: from related states, the checker's re-rooting and drop of a
place of the join's list is the reference's drop of it (`joinDropOne`: the lent prefix accessed
whole, then `dropAt`). The place is at the join's grain (`GrainOk`) and is not of a copy type (the
join moves only what is not a copy: D84, `jdMoves`). `movedPlace` may η-refine an unknown or
generalise a sealed program, creating unknowns, so the assignment AND the run context's `Δ` are
extended (docs/31 D20 item 7: a step that creates unknowns hands on an extended context; the
reference's drop reads no `Δ`, so `joinDropOne` is the same under either). -/
def dropOne_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (q : Place) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hgrain : GrainOk K.D K.Γ (scopeOf s) q) (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (bh : Nat) (h : Runs (do Ochr.dropAtJoin fuel (← Ochr.movedPlace fuel q)) st bh () st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), st.absTy.size ≤ st'.absTy.size ∧
      (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧
      Rel { K with Δ := Δ' } ρ' φ π st' (joinDropOne K φ s q) ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st'

/-- **[Join], the drop** (`Machine.joinDrop`'s loop after the arm: `dropAtJoin` of each place the
join says is moved, re-rooted by `movedPlace`), in the simulation form: from related states, with
the join's drop list (`Decisions.joinMoves`, the same on both sides, at the join's grain and moving
no copy), the states after the checker's drops and after the reference's `joinDrop` are related,
under an assignment and a `Δ` extended at the unknowns `movedPlace` creates (D20 item 7). The arm's
result is in flight: the checker's state is given with it pushed as a temporary, as `joinDrop`
holds it. (D28's alignment of two drop lists that differed by early-ended borrow variables is gone
with them, D29; the grain and copy hypotheses and the extended context are D29's task C findings.) -/
def joinDrop_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (mt : Term) (entry : List Place)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hgrain : ∀ q ∈ K.D.joinMoves (scopeOf s) entry mt, GrainOk K.D K.Γ (scopeOf s) q)
    (hcopy : ∀ q ∈ K.D.joinMoves (scopeOf s) entry mt, K.D.copy (K.D.placeDecl (scopeOf s) q) = false)
    (bh : Nat) (h : Runs (do for q in K.D.joinMoves (scopeOf s) entry mt do
      Ochr.dropAtJoin fuel (← Ochr.movedPlace fuel q)) st bh () st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧
      Rel { K with Δ := Δ' } ρ' φ π st' (joinDrop K φ entry mt s) ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st'

/-- [Match] on `Nat` (`evalMatch`): the run's `.matchNat` clause, in the simulation form. With a
known constructor the arm runs and the join drops (`joinEntry_stmt`, `joinDrop_step_stmt`); on an
unknown the checker splits or closes off, and the run takes the arm the assignment selects.
`hns`: the run's clause is under `SM.erasedIf`, which `evalMatch` is not. -/
def evalMatch_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (p : Place) (z u : Term)
    (expected : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) (.matchNat p z u) = (false, false))
    (bh : Nat) (h : Runs (Ochr.evalMatch fuel typed p z u expected) st bh (v, T?) st'),
    -- the run's hint is the checker's expected type (a free hint against `expected` was refutable
    -- on a hint-dependent arm value)
    SimConcl K ρ φ π st st' s (fun ρ' => run K ρ' φ (hintM K ρ expected) (.matchNat p z u)) v

/-- [Match] on a declared inductive (`evalMatchInd`): the run's `.matchInd` clause, in the
simulation form. -/
def evalMatchInd_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (p : Place) (ty : String)
    (arms : List (Hint × Term)) (expected : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) (.matchInd p ty arms) = (false, false))
    (bh : Nat) (h : Runs (Ochr.evalMatchInd fuel typed p ty arms expected) st bh (v, T?) st'),
    -- the hint is the checker's expected type, as for `evalMatch` (it was free here)
    SimConcl K ρ φ π st st' s (fun ρ' => run K ρ' φ (hintM K ρ expected) (.matchInd p ty arms)) v

/-- A match on a proof, by its type (`evalMatchByType`, D45): the one arm of a one-constructor
proposition, its proof fields `⋆` and its data fields fresh unknowns; the run's clause for a proof
scrutinee under an assignment extended at those unknowns by the fields of the proof's witness (the
proposition is inhabited, since the scrutinee is a member of it). In the simulation form. -/
def evalMatchByType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (p : Place) (ty : String)
    (arms : List (Hint × Term)) (expected : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) (.matchInd p ty arms) = (false, false))
    (bh : Nat) (h : Runs (Ochr.evalMatchByType fuel typed p ty arms expected) st bh (v, T?) st'),
    SimConcl K ρ φ π st st' s (fun ρ' => run K ρ' φ (hintM K ρ expected) (.matchInd p ty arms)) v

/-- [Split] coverage: at a place whose content is the unknown `σ` of a data type, every typed
assignment selects a constructor `c` (exactly one: distinct constructors mean distinct tags), and extends to the arm's fresh field unknowns
(`ctorRefinement`) so that `σ`'s refinement is satisfied. -/
def split_coverage_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (σ : Nat) (d : IndDecl) (ps : List Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hσ : st.absTy[σ]? = some (.tInd d.name ps)),
    ∃ c ρ' r st', Extends st ρ ρ' ∧
      Runs (Ochr.ctorRefinement fuel d (ps) c) st fuel r st' ∧
      TypedAssignment K.dm K.M K.Γ ρ' st' ∧
      ρ' σ = meanV K ρ' φ (.plain (MState.absTyM K.dm K.M K.Γ ρ' st' σ)) r

/-- [Split-gen] (`generalizeNeutral`): the sealed program `n` at place `p` becomes a fresh `σ`
with the record `n := σ`; under `ρ` extended at `σ` by `⟦n⟧`, the state means the same and the
assignment is typed (the path condition). -/
def generalizeNeutral_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (n : Value) (σ : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.generalizeNeutral fuel p n) st bh σ st'),
    -- `n` is read at the type the checker gives `σ` (as `refine_step_stmt`'s `hσ`; a free hint
    -- was refutable: the place read `n` at its own hint, `σ` at the free one)
    let ρ' := ρ.ext σ (meanV K ρ φ (.plain (MState.absTyM K.dm K.M K.Γ ρ st' σ)) n)
    Exact (MState.mean K.dm K.M K.Γ ρ' st') (MState.mean K.dm K.M K.Γ ρ st) ∧
    Good K.dm K.M K.Γ ρ' st'

/-- A stuck block closed off (`closeBlock`): the block is a call of an anonymous function of its
captures, so its sealed result and fills mean what running the match means: the run's match
clause, in the simulation form (the capture by move of a place the selected arm keeps is D84's
join, which the run performs too). The arms are given as the match term `mt`; `B?` is the match's
annotated type. -/
def closeBlock_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (mt : Term) (arms : List BlockArm)
    (B? : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hmt : mt matches .matchNat .. | .matchInd .. | .prim "J" _)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) mt = (false, false))
    (bh : Nat) (h : Runs (Ochr.closeBlock fuel mt arms B?) st bh (v, T?) st'),
    SimConcl K ρ φ π st st' s (fun ρ' => run K ρ' φ (hintM K ρ B?) mt) v

/-- Worlds (X1)–(X4), `exitWorld`: the restored state means the snapshot (every component but
the name counters and the types of unknowns created inside the arm is the snapshot's), and is
`Good` for any assignment the snapshot was. -/
def exitWorld_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (w : World)
    (hg : Good K.dm K.M K.Γ ρ w.saved)
    (bh : Nat) (h : Runs (Ochr.exitWorld w) st bh () st'),
    Exact (MState.mean K.dm K.M K.Γ ρ st') (MState.mean K.dm K.M K.Γ ρ w.saved) ∧
    (∀ σ, σ < w.saved.absTy.size → st'.absTy[σ]? = w.saved.absTy[σ]?) ∧
    st'.neutrals = w.saved.neutrals ∧ st'.etaRefs = w.saved.etaRefs ∧ st'.goal = w.saved.goal ∧
    Good K.dm K.M K.Γ ρ st'

/-! ### The observation area, in the simulation form (docs/31 D26; third lead)

`observe` and `idType` run their sides on private copies, so the checker's Ω is unchanged
(`st'.env = st.env`; the counters, the records and the types of the unknowns created inside
survive, D23, so the core is not) and the reference state is untouched. The values the checker
returns are read under an assignment extended at the unknowns created inside, among them the
fresh values [Obs-ref] writes through the re-pointed bindings. -/

/-- `observe` (a side on a private copy, the fresh values `refs` written through the re-pointed
bindings ([Obs-ref]), every borrow ended, the result and the owners read), from a related state:
the reference's side run does not fail, and the checker's result and each observed owner mean
their components of the reference observation, for the written values the fresh unknowns mean.
The side is run at the hint `A`, as the checker runs it. -/
def observe_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (A : Value) (W : List Pos)
    (refs : List (Place × Value)) (r : Value) (ws : List Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (bh : Nat) (h : Runs (Ochr.observe fuel typed t A W refs) st bh (r, ws) st'),
    st'.env = st.env ∧
    ∀ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) → TypedAssignment K.dm K.M K.Γ ρ' st' →
      ∃ o, refObs K ρ' φ (refs.map (·.1)) (refs.map fun x => meanV K ρ' noFuture (.plain .err) x.2)
          (Value.tyS K.dm K.M K.Γ ρ A) t s = some o ∧
        o[0]? = some (meanV K ρ' (fun l => φ (π l)) (Value.tyS K.dm K.M K.Γ ρ A) r) ∧
        ∀ (i j : Nat) (p : Pos), W[i]? = some p → s.positions[j]? = some p →
          ws[i]?.map (meanV K ρ' (fun l => φ (π l)) (Env.hintAt K.dm K.M K.Γ ρ st.env p)) = o.tail[j]?

/-- Footprint coverage (docs/18 "Footprint coverage", the third of the five lemmas), from a
related state: a position that was there when the sides started and is outside the footprint of
the two means the same after either side, GIVEN that the two leave the same type-state
([Id-typestate]: the same places moved, the same borrow bindings consumed, re-pointed and left
open). Without that hypothesis it was false: the footprint lists what the sides write or borrow,
not what they move, and a place one side moves and the other does not is outside it. -/
def footprint_coverage_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st₁ st₂ : MState) (A t u : Term) (p : Pos) (o₁ o₂ : List Sem) (j : Nat) (reps : List Place) (ws : List Sem)
    (hint : TyS) (tsT tsU : TypeState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (bhtT : Nat) (htT : Runs (withLive true (Ochr.typeState fuel t)) st bhtT tsT st₁)
    (bhtU : Nat) (htU : Runs (withLive true (Ochr.typeState fuel u)) st bhtU tsU st₂)
    (hmv : jdMissing tsT.moved tsU.moved = none ∧ jdMissing tsU.moved tsT.moved = none)
    (hcs : jdMissing tsT.consumed tsU.consumed = none ∧ jdMissing tsU.consumed tsT.consumed = none)
    (hrp : jdMissing tsT.repointed tsU.repointed = none ∧ jdMissing tsU.repointed tsT.repointed = none)
    (hlo : jdMissing tsT.leftOpen tsU.leftOpen = none ∧ jdMissing tsU.leftOpen tsT.leftOpen = none)
    (hp : p ∉ footprint st.env [t, u]) (hj : s.positions[j]? = some p)
    (h₁ : refObs K ρ φ reps ws hint t s = some o₁)
    (h₂ : refObs K ρ φ reps ws hint u s = some o₂),
    o₁.tail[j]? = o₂.tail[j]?

/-- `Id` computes (`idType`), from a related state: the checker's Ω is unchanged, the reference's
run of `Id` does not fail and leaves its state, and under SOME assignment of the unknowns created
(the fresh values [Obs-ref] wrote: a member of the borrowed type at which the two sides differ,
where there is one) the checker's conjunction over the result and the footprint's owners is true
exactly when the reference's `Id` is, and it is true under EVERY such assignment when the
reference's is.

As first stated the last conjunct read `(run … = some (r, s') ∧ ⟦P⟧ true) ↔ ⟦r⟧ true` under
`∃ r s'` (`∧` binds tighter than `↔`), which any `r` that is not the run's result satisfies: it
said nothing (`Regress/IdUnitWrite.old_stmt_vacuous`). -/
def idType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A t u : Term) (P : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (bh : Nat) (h : Runs (Ochr.idType fuel typed A t u) st bh P st'),
    st'.env = st.env ∧
    ∃ r, run K ρ φ (.plain .err) (.id A t u) s = some (r, s) ∧
      (∃ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ Good K.dm K.M K.Γ ρ' st' ∧
        (((meanV K ρ' (fun l => φ (π l)) (.plain .err) P).asTy).true ↔ (r.1.asTy).true)) ∧
      ((r.1.asTy).true → ∀ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) → TypedAssignment K.dm K.M K.Γ ρ' st' →
        ((meanV K ρ' (fun l => φ (π l)) (.plain .err) P).asTy).true)

/-- Owners (RULES §4): every position `owners env l` lists holds, directly or through the content
of a borrow it holds, a loan of `l`; and conversely every position whose meaning depends on `l`
is among them (`Mean.dependsOn`). -/
def owners_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (l : Nat) (p : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hl : liveLoan st.env l = true),
    (MState.mean K.dm K.M K.Γ ρ st).dependsOn p l → p ∈ owners st.env l

/-- `evalType` (a type term, on a private copy): the result means the run's result, and the
state's core is unchanged. -/
def evalType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.evalType fuel t) st bh T st'),
    st'.core = st.core ∧
    ∃ r s', run K ρ φ (.plain .err) t (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) T = r.1

/-- `piSort` agrees with the aligned decision (D55: a type's declared sort is its computed sort). -/
def piSort_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (caps : List Value) (hs : List Hint)
    (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) (l : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.piSort fuel (.tPi caps (.pi hs ds c) rd)) st bh l st'),
    K.D.piSort (scopeOf (SM' K ρ st)) (.pi hs ds c) = l

/-- `capture`: the closure value the checker forms (captures by value, the term rewritten to read
them as slots) means what the run's `.fix` clause gives the original term in the forming state. -/
def capture_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (cs : List Value) (t' : Term)
    (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hfix : t matches .fix ..)
    (bh : Nat) (h : Runs (Ochr.capture fuel t) st bh (cs, t', rd) st'),
    ∃ r s', run K ρ φ (.plain .err) t (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) (.clo cs t' rd) = r.1 ∧
      Below (MState.mean K.dm K.M K.Γ ρ st') s'.toMean ∧ Good K.dm K.M K.Γ ρ st'

/-- `evalCtor` (a constructor value, its parameters written or inferred): the run's `.ctor`
clause at the hint the context gives. -/
def evalCtor_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (ty : String) (c : Nat) (h0 : Hint)
    (pts as : List Term) (hint : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.evalCtor fuel typed ty c h0 pts as hint) st bh (v, T?) st'),
    let hm : TyS := (hint.map (Value.tyS K.dm K.M K.Γ ρ)).getD (.plain .err)
    ∃ r s', run K ρ φ hm (.ctor ty c h0 pts as) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ hm v = r.1 ∧
      Below (MState.mean K.dm K.M K.Γ ρ st') s'.toMean ∧ Good K.dm K.M K.Γ ρ st'

/-- `evalTInd`: `D(ā)` means the run's `.tind` clause. -/
def evalTInd_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (n : String) (as : List Term)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.evalTInd fuel typed n as) st bh (v, T?) st'),
    ∃ r s', run K ρ φ (.plain .err) (.tind n as) (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ (.plain .err) v = r.1 ∧ st'.core = st.core

/-- `fieldTypesOf`: the checker's field types at parameters and fields mean `DataModel.fieldTy`
at their meanings (the telescope, D64). -/
def fieldTypesOf_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (d : IndDecl) (ps : List Value) (c : Nat)
    (fs : List Value) (tys : List (String × Value))
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.fieldTypesOf fuel d ps c fs) st bh tys st'),
    ∀ i T, tys[i]?.map (·.2) = some T →
      (meanV K ρ noFuture (.plain .err) T).asTy =
        K.dm.fieldTy d (Value.meanParams K.dm K.M K.Γ ρ noFuture d 0 [] ps) c i
          (Value.meanFields K.dm K.M K.Γ ρ noFuture d (Value.meanParams K.dm K.M K.Γ ρ noFuture d 0 [] ps) c 0 [] (fs.take i))

/-- [Repack]'s accepting direction (`repackCheck`): a value checked whole against `T`, with each
part still lent read as an unknown of its type (D73), is a member of `T` under every typed
future. -/
def repackCheck_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (what : String) (v T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.repackCheck fuel what v T) st bh () st'),
    TypedFuture K.dm K.M K.Γ ρ st φ →
      meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ T) v ∈ₛ (meanV K ρ noFuture (.plain .err) T).asTy

/-- [Return]'s accepting direction (`bodyReturns`): the returned value is a member of its type
and every place held by borrow is whole, under every typed future. -/
def bodyReturns_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (what : String) (v T : Value)
    (lent : List Place) (lw : String)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.bodyReturns fuel what v T lent lw) st bh () st'),
    TypedFuture K.dm K.M K.Γ ρ st φ →
      meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ T) v ∈ₛ (meanV K ρ noFuture (.plain .err) T).asTy ∧
      (meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ T) v).whole

/-- `valType?` is sound (the second of the five lemmas): the meaning of a value lies in the
meaning of the type the checker reads off it. -/
def valType_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (v T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hv : ∃ p, valAt st.env p = v)
    (bh : Nat) (h : Runs (Ochr.valType? fuel v) st bh (some T) st'),
    TypedFuture K.dm K.M K.Γ ρ st φ →
      DataModel.pmem K.Γ (meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ T) v) (meanV K ρ noFuture (.plain .err) T).asTy

/-- [Borrow] keeps (WF1)–(WF3): the fresh label is held once, at the destination; the lent
place's content holds no live loan (after [Access]), so the borrow relation stays acyclic. -/
def borrow_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.borrowPlace fuel p) st bh v st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env

/-- [End] keeps (WF1)–(WF3): the ended label leaves Ω; a reborrow's loan in its content moves
to the lender, above it in the borrow relation. (WF2) needs (WF3) here (docs/18 §"Well-formedness"). -/
def end_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.endBorrow fuel l) st bh () st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env

/-- [Assign] keeps (WF1)–(WF3): D67 ends the loans in the overwritten owned part, and the old
content's borrows end ([Drop]). -/
def assign_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.assignPlace fuel p v) st bh () st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env

/-- [Close] keeps (WF1)–(WF4): the fills are closed sealed programs (C1), the arguments were
loan-free (C8), and a returned borrow's fresh label is held once. -/
def close_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (ws : Array Value) (kind : Kind)
    (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hargs : ArgsLoanFree st.env ws)
    (bh : Nat) (h : Runs (Ochr.closeCall fuel fv ws kind res fills tys) st bh v st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env ∧ WF4 st'.env

/-- Closure formation keeps (WF4): the captures are read after [Access] (loan-free) and may not
hold `⊥` (the capture check), and a Π-closure captures no borrow (D48). -/
def capture_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (cs : List Value) (t' : Term)
    (rd : List (DeclInfo × Value))
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.capture fuel t) st bh (cs, t', rd) st'),
    ¬ (Value.clo cs t' rd).anyAtom Value.badCapture ∧ WF4 st'.env

/-- Every step of `evalCore` keeps (WF6): names are allocated at and below the counters, which
only grow. -/
def eval_wf6_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.evalCore fuel typed t hint) st bh (v, T?) st'),
    WF6 st' ∧ st.nextAbs ≤ st'.nextAbs ∧ st.nextLoan ≤ st'.nextLoan

/-- Every step of `evalCore` keeps (WF7) and (WF8): the only places a borrow type is formed
check D66 and D48, and no step puts `&` below the top of a type. -/
def eval_wf78_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hprog : t.refsOk = true)
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed t hint) st bh (v, T?) st'),
    WF7 K.dm K.M K.Γ ρ st' ∧ WF8 st'

/-- Types and records hold no loan at every `Good` state: the clause (WF11) (docs/27 Lemma 5,
docs/31 D23). It is what lets a type and a record be read at the constant future, and what makes
a label issued inside a private copy occur nowhere after it. PROVED (`Steps/WF.lean`), now that it
is a clause of `Good`; as first stated (no LIVE loan in a stored type, as a consequence of `Good`)
it did not follow from `Good`, which said nothing of a type's loans. -/
def types_holeFree_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st), WF11 st

/-- The run's result type `R` is the checker's type `T` of the value `v`, with its structure
(docs/31 D22): the same meaning, Π-shape and data, where the checker's side is its stored type
read as a reference binding reads it (`Value.tyS`, with the structure of `v` itself when `v` is a
type: `Value.strS`). This is what a `let` needs to keep `Rel.skel`. As first stated the conjunct
compared the meanings only. -/
def StrAgree (v T : Value) (R : TyS) : Prop :=
  (Value.strS K.dm K.M K.Γ ρ v (Value.tyS K.dm K.M K.Γ ρ T)).m = R.m ∧
  (Value.strS K.dm K.M K.Γ ρ v (Value.tyS K.dm K.M K.Γ ρ T)).shape = R.shape ∧
  (Value.strS K.dm K.M K.Γ ρ v (Value.tyS K.dm K.M K.Γ ρ T)).data = R.data

/-- **[T-Pi]: a Π-type's shape does not depend on where it is read** (docs/31 D22; prerequisite
(a) of the migration). The checker closes a Π-term or a `fix` over the values of its free
variables (`capture`) and stores the Π-type as that closed value, whose shape a later reading takes
off its term in the frame of its captures, at the constant future (`tyShape`, through
`Value.tyS`). The reference run reads the shape off the ORIGINAL term in the forming state, at the
run's future (`piShapeOf`, the `.pi` and `.fix` clauses). The two are the same shape, from any
reference state that simulates the checker's.

Three things carry it, none proved: the captured term in the captures' frame runs as the original
in the forming state (the capture lemma: a term's run reads the state only at its free variables,
each after [Access], which the checker's capture also performs); a type holds no live loan, so the
future does not matter (`tyShape_congrE`, proved, gives this once the captures are loan-free);
and the decisions read the same readings through the renaming (`rd` records each capture's).
Where it is KNOWN false: a captured PROOF variable is inlined as `(⋆ : T)`, which the run types
`T` where a read of the variable is typed `err` (`SM.erasedIf`), and a constructor's parameter
solved by such a field's type differs (the audit's A17, `Regress/ShapeProbes.lean`). -/
def piShape_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (t : Term) (cs : List Value) (t' : Term) (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (ht : t matches .pi .. | .fix ..)
    (bh : Nat) (h : Runs (Ochr.capture fuel t) st bh (cs, t', rd) st'),
    (piShapeOf K ρ φ s t).map (fun sh => (sh.ps, sh.out)) = tyShape K ρ noFuture (.tPi cs t' rd)

/-- **The induction step, in the simulation form** (docs/31 D20 item 1). For every `Good`
assignment `ρ` and every reference state `s` that simulates the checker's state under a renaming
`π` of its labels (`Rel`), following at each split the arm `ρ` selects: the reference run of `t`
from `s` does not fail; the checker's value, read at the run's future pulled back along the
renaming, IS its result (equal, not below: a value that is bound must satisfy `Rel`'s equality at
its binding; docs/31 D24); the state the run reaches simulates the checker's, for an
assignment `ρ'` extending `ρ` to the unknowns created and a renaming `π'` that agrees with `π` on
the labels the checker had issued; and `Good` is kept.

(As first stated, the reference ran from `SM' K ρ st` and the conclusion was
`Below (MState.mean … st') s'.toMean`: false after any borrow was held, `Regress/StaleTemp.lean`,
and two such statements did not compose.)

`hns`: `evalCore` does not erase (`evalAt` does), and the run of a statement is on a copy and of
an erased term is `•` unrun (`SM.erasedIf`), so the two agree where the term is neither. (It
asked only for "not a statement" before the audit's A3 made the run skip an erased term.) -/
def evalCore_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) t = (false, false))
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed t hint) st bh (v, T?) st'),
    ∃ ρ' π', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
      ∃ r s', run K ρ' φ (hintM K ρ hint) t s = some (r, s') ∧
        meanV K ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
        (∀ T, T? = some T → StrAgree K ρ' v T r.2) ∧
        Rel K ρ' φ π' st' s' ∧ Good K.dm K.M K.Γ ρ' st'

/-- **The induction step as the checker recurses** (docs/31 D20, item 5): every recursive
position of the checker calls `Machine.eval`, which is `evalAt`: it classifies the term
(`preFlags`), runs an erased one on a private copy and restores the environment. The run does
the same at `Decisions.flags` (`SM.erasedIf`, D19), so this statement has no side condition,
where `evalCore_step_stmt` has `hns`. Same conclusion, in the simulation form. -/
def eval_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (bh : Nat) (h : Runs (Ochr.eval fuel typed t hint) st bh (v, T?) st'),
    ∃ ρ' π', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
      ∃ r s', run K ρ' φ (hintM K ρ hint) t s = some (r, s') ∧
        meanV K ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
        -- not of a proof: the run does not run one and gives it no type (`SM.erasedIf`), where
        -- the checker returns its proposition (the audit's row 26, and A17). As first stated the
        -- conjunct had no such condition and was false of every proof term
        (∀ T, T? = some T → (K.D.flags (scopeOf s) t).2 = false → StrAgree K ρ' v T r.2) ∧
        Rel K ρ' φ π' st' s' ∧ Good K.dm K.M K.Γ ρ' st'

/-- [Let]: the binding is pushed at the right-hand side's type and dropped after the tail
(`dropTopBind`); the run's `.letIn` clause. In the simulation form, as `evalCore_step_stmt`. -/
def letIn_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (h0 : Hint) (u w : Term)
    (hint : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) (.letIn h0 u w) = (false, false))
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed (.letIn h0 u w) hint) st bh (v, T?) st'),
    ∃ ρ' π' r s', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
      run K ρ' φ (hintM K ρ hint) (.letIn h0 u w) s = some (r, s') ∧
      meanV K ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
      Rel K ρ' φ π' st' s' ∧ Good K.dm K.M K.Γ ρ' st'

/-- `Eq` (the `.eq` form): both sides on private copies, the type a statement; the result means
`⟦a⟧ = ⟦b⟧` (`Steps/Eq.mkEqM_step`), the checker's Ω is unchanged and the reference state is
untouched. From a related state. (As first stated the last conjunct was
`(run … = some (r, s') ∧ ⟦v⟧ true) ↔ ⟦r⟧ true` under `∃ r s'`, which said nothing:
`Regress/IdUnitWrite.old_stmt_vacuous`.) -/
def eq_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A a b : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed (.eq A a b) hint) st bh (v, T?) st'),
    st'.env = st.env ∧
    ∃ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ Good K.dm K.M K.Γ ρ' st' ∧
      ∃ r, run K ρ' φ (.plain .err) (.eq A a b) s = some (r, s) ∧
        (((meanV K ρ' (fun l => φ (π l)) (.plain .err) v).asTy).true ↔ (r.1.asTy).true)

/-- `J`, both outcomes: computed at convertible endpoints (the transported term runs in place)
or closed off as a stuck block whose one arm is the transported term ([T-J-stuck]); each means
the transported term (docs/24 C9). -/
def J_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A a b P hh u : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    -- neither a statement nor erased (since the audit's A3 the run skips an erased term, which
    -- `evalCore` runs)
    (hns : K.D.flags (scopeOf (SM' K ρ st)) (.prim "J" [A, a, b, P, hh, u]) = (false, false))
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed (.prim "J" [A, a, b, P, hh, u]) hint) st bh (v, T?) st'),
    ∃ ρ' r s', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧
      run K ρ' φ (hintM K ρ hint) (.prim "J" [A, a, b, P, hh, u]) (SM' K ρ' st) = some (r, s') ∧
      meanV K ρ' φ r.2 v ⊑ r.1 ∧
      Below (MState.mean K.dm K.M K.Γ ρ' st') s'.toMean ∧ Good K.dm K.M K.Γ ρ' st'

/-- A proof position (a proof-returning call, a proof primitive, a proof `let`): its value is
`⋆`, which is a member of its proposition exactly when the proposition is true; the state is
unchanged (a statement runs on a copy). Membership here is where "a proof's value is `⋆`"
(docs/26 row 1, *same* given membership) is discharged. -/
def proof_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hp : (K.D.flags (scopeOf (SM' K ρ st)) t).2 = true)
    -- `eval`, not `evalCore`: it is `evalAt` that runs a proof on a copy (as stated for `evalCore`
    -- a proof-valued `let` whose right-hand side moves a place refuted "the state is unchanged")
    (bh : Nat) (h : Runs (Ochr.eval fuel typed t hint) st bh (.proof, some T) st'),
    st'.core = st.core ∧ Sem.proof ∈ₛ (meanV K ρ φ (.plain .err) T).asTy

/-- η at `Unit` (D80): where a position's declared reading is `Unit`, the value is `()`, and
`()` is the one element of `⟦Unit⟧`, so the normalisation keeps meaning given membership. -/
def etaUnit_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (d : DeclInfo) (v : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hd : d = .unit)
    (hv : meanV K ρ φ hint v ∈ₛ .ty0 Unit),
    meanV K ρ φ hint (Ochr.etaUnit d v) = meanV K ρ φ hint v

/-- The generic state of a `fix` is `Good` for every assignment that gives each parameter's
unknown an element of its type (and the goal is a type). -/
def generic_good_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (cs : List Value) (t : Term)
    (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.checkFix fuel fv cs t capRec rd) st bh () st'),
    ∀ ρ', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) →
      TypedAssignment K.dm K.M K.Γ ρ' st' → Good K.dm K.M K.Γ ρ' st'

/-- `checkTail` with a leaf continuation: every typed assignment of the start state reaches a
leaf (coverage along splits), where the continuation's hypotheses hold for the leaf's value and
type, and the leaf's value means the reference run's result at the start. -/
def checkTail_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (k : Value → Value → M Unit)
    (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.checkTail fuel t k) st bh () st'),
    ∃ ρ' v T stl stl', (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) ∧ Good K.dm K.M K.Γ ρ' stl ∧
      Runs (k v T) stl fuel () stl' ∧
      ∃ r s', run K ρ' φ hint t (SM' K ρ' st) = some (r, s') ∧
        meanV K ρ' φ r.2 v ⊑ r.1 ∧ (meanV K ρ' noFuture (.plain .err) T).asTy = r.2.m

/-- [Def]/[Fix] (`checkFix`): an accepted `fix` means an element of its Π-type (docs/18
Corollary 15): under every assignment of its parameters, the body's reference run gives a
member of the goal, so `mkTele` succeeds and the closure's meaning is in the carrier. -/
def checkFix_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (cs : List Value) (t : Term)
    (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value)) (fT : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    -- `fT` is the fix's own Π-type (the pilot form's `∨` left `fT` free on one side; the defect
    -- class of `Regress/CloseCallStmt.lean`)
    (hT : ∃ self hs ds c r body, t = .fix self hs ds c r body ∧ fT = .tPi cs (.pi hs ds c) rd)
    (bh : Nat) (h : Runs (Ochr.checkFix fuel fv cs t capRec rd) st bh () st'),
    meanV K ρ φ (.plain .err) (.clo cs t rd) ∈ₛ (meanV K ρ φ (.plain .err) fT).asTy

/-- [Const]: an accepted constant's value is a member of its goal, under the empty assignment. -/
def checkConst_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (d : Ochr.Def) (goal v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hd : d.doms = [])
    (h : Runs (Ochr.checkDef d) st 2000000 () st')
    (hgl : ∃ g ∈ st'.globals, g.name = d.name ∧ g.ty = goal ∧ g.val = v),
    meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ goal) v ∈ₛ (meanV K ρ noFuture (.plain .err) goal).asTy

/-- [Ind-decl] (`checkInd`): an accepted declaration satisfies (I1)–(I9), so the data model covers
it (the least fixed point exists in the sort's universe; docs/18 Lemma 2). -/
def checkInd_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (d : IndDecl)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (h : Runs (Ochr.checkInd d) st 2000000 () st'),
    K.dm.covers d

/-- The scope of readings the checker uses at `st`'s top frame is `scopeOf` of its semantic
state (each binding's `decl`, innermost first). -/
def scopeOf_sstate_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState),
    scopeOf (SM' K ρ st) = ((st.env.back?.map (·.binds.toList.map (·.decl))).getD []).reverse

/-- `Decisions.flags` is `Decide.preFlags` where the latter answers. -/
def flags_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (t : Term) (fl : Bool × Bool)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    -- the decisions are the checker's own at `st` (`DecisionsInst.checkerDecisions`); the call
    -- is the live form `Machine.evalAt` makes (decide-scope's `checkerDecisions_flags`)
    (hD : K.D = checkerDecisions st fuel)
    (bh : Nat) (h : Runs (do
      let d ← withLive true (Ochr.declOf fuel false [] [] t)
      pure ((← Ochr.preFlags t d).getD (false, false))) st bh fl st'),
    K.D.flags (scopeOf (SM' K ρ st)) t = fl

/-- `Decisions.placeDecl` is `Decide.placeDecl`. -/
def placeDecl_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (d : DeclInfo)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : K.D = checkerDecisions st fuel)
    (bh : Nat) (h : Runs (withLive true (Ochr.placeDecl fuel [] p)) st bh d st'),
    K.D.placeDecl (scopeOf (SM' K ρ st)) p = d

/-- `Decisions.declOf` is `Decide.declOf` (unchecked mode). -/
def declOf_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (d : DeclInfo)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : K.D = checkerDecisions st fuel)
    (bh : Nat) (h : Runs (withLive true (Ochr.declOf fuel false [] [] t)) st bh d st'),
    K.D.declOf (scopeOf (SM' K ρ st)) t = d

/-- `Decisions.copy` is `Decide.declCopy`. -/
def copy_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (d : DeclInfo) (b : Bool)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.declCopy fuel d) st bh b st'),
    K.D.copy d = b

/-- `Decisions.piSort` is `Decide.sortOf` of the Π-type value (D55: declared sort = computed). -/
def piSort_aligned'_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (hs : List Hint) (ds : List Term) (c : Term) (l : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : K.D = checkerDecisions st fuel)
    (bh : Nat) (h : Runs (withLive true (Ochr.sortOf fuel (.tPi [] (.pi hs ds c) []))) st bh l st'),
    K.D.piSort (scopeOf (SM' K ρ st)) (.pi hs ds c) = l

/-- D84 [Join]: `Decisions.joinMoves` is `Decide.jdMoves` as `Machine.staticJoin` calls it (the
places already `⊥` at the match as its `entry`). -/
def joinMoves_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (entry ms : List Place) (t : Term)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.jdMoves fuel [] [] t entry) st bh ms st'),
    K.D.joinMoves (scopeOf (SM' K ρ st)) entry t = ms

/-- D84 [Id-typestate]/[Obs-ref]: `Decisions.rePointed` is the `repointed` component of
`Decide.typeState`, as `Machine.idType` reads it. -/
def rePointed_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (ts : TypeState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.typeState fuel t) st bh ts st'),
    K.D.rePointed (scopeOf (SM' K ρ st)) t = ts.repointed

/-- `Decisions.typeDecl` is `Decide.typeDecl`, the reading of a type term (D19, R3: a closure's
frame binds its parameters at their domain terms' readings, `Decide.paramDecls`). -/
def typeDecl_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (T : Term) (d : DeclInfo)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : K.D = checkerDecisions st fuel)
    (bh : Nat) (h : Runs (withLive true (Ochr.typeDecl fuel false [] [] T)) st bh d st'),
    K.D.typeDecl (scopeOf (SM' K ρ st)) T = d

end

end Ochr.Meaning.Steps
