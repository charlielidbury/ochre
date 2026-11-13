import Ochr.Meaning.Run
import Ochr.Check

/-!
# The meaning of a program (docs/18 Def. "meaning of a program", docs/31 milestone 2)

A program is a list of items (`Check.Item`: definitions and inductive declarations), checked in
order, each from a fresh state that keeps only Σ, the globals and inductive types accepted so
far (`Check.checkDefs`, `Check.globalsAfterFrom`). Its meaning follows the same recursion: the
globals in program order, each accepted definition meaning what the reference run (`run`) of
its body gives against the meanings of the earlier globals. That reaches later code through
`CodeMeaning.global` and, for a state's values, through `codeMeaning`, which ties the knot.

## The tie to `Check.lean`

`ProgState` carries two things side by side: Σ exactly as the checker has it (`globals`,
`inds`: the `GDef`s and `IndDecl`s of the accepted items), and the model's meaning of each
accepted definition (`means`). One item is one iteration of `globalsAfterFrom`'s loop (`step`):
it runs `checkItem` from `{ globals, inds, cfg }`, which is the state `checkDefs` builds for an
item when no editor locations are asked for, as `Consistency.Accepted` never asks. So the Σ half
of `progMeaning` *is* `globalsAfterFrom` (`progMeaning_sig`, proved) and, on a program whose
every item is accepted (the hypothesis of `consistencyBounded`), also `checkDefs`' Σ. `checkDefs`
additionally marks as undecided an item that mentions an undecided one, and neither checks nor
adds it. An `Accepted` program has no undecided item, so this recursion leaves that rule out.

## What "accepted" contributes

The checker's verdict boundary is the only place where acceptance is read (`runMachine`'s
`Outcome.ok`). A rejected or exhausted item contributes nothing, to Σ or to the meaning.
* An accepted **inductive declaration** contributes its `IndDecl` to Σ (`inds`). Its meaning
  is the data model's (`DataModel`, a parameter here; the generic model is data-generic's
  `DataGeneric.lean`). The run reads it through `RunCtx.Γ`. The model must speak for it
  (`DataModel.covers`; `ProgState.Covered` is that hypothesis for every declaration of Σ).
* An accepted **definition** contributes its `GDef` to Σ and its meaning and type to `means`
  (`defMeaning`). Its type is read off the type the checker stores, `GDef.ty` (`globalTyS`):
  `Value.tyS` of it (its meaning, and for `D(ā)` its parameters, D8), and, for a Π-type, its
  shape from its Π-term (`piShapeOf`, as `run`'s `.val` clause gives a Π-type value's). For a
  function, `GDef.ty` is `tPi [] (pi x̄ Ā B) []`, so this is the shape of the `fix` term's binders
  and codomain.
  * A function `def f (x̄ : Ā) : B := b` means the run, from the empty state, of the closed term
    `fix f (x̄:Ā):B := b` that [Def] checks (`checkFix`): its closure, the guarded fixpoint by
    stages when it has `by xⱼ` (`run`'s `.fix` clause), recursing through its `self` binder as the
    surface resolves it. Its value in the checker is `gfn f` whatever its type, so its meaning is
    the closure's, never `•`.
  * A constant `def c : B := b` means the run of `b`, from the empty state, at its goal's type
    (the checker's `eval true d.body goal`; the goal is `GDef.ty`, and it is the structured hint of
    D8). It means `•` when the goal means a proposition (`constMean`), as the checker stores `⋆`
    for a constant whose goal `isPropV`.
  A definition is closed and holds no live loan ([Return], D76), so it is run at the constant
  future `noFuture`. An accepted definition whose run is undefined is recorded as `err`, so that
  every name of Σ has a meaning in the same position. milestone 4's corollary (an accepted
  definition means an element of its type) says this never happens.

## Decisions

The run of item `i` makes the aligned decisions (`Decisions`) as the checker makes them while
checking item `i`. They read Σ (declared types, type functions' bodies, inductive
declarations) and Δ, and never read a run. The program meaning therefore takes them as a function
of a checker state, `D : MState → Decisions` (`DecisionsInst.lean`'s `checkerDecisions` is the
instance), and reads them at the state the accepted item's check ended in. For a function, that
state's Σ is the one its body was checked under: `checkDef` adds the function's `GDef` before
[Def]. For a constant it has one more global, the constant itself, which its own body cannot
name: `resolveDecl` resolves a constant's body in the empty context, so its own name there is
`.const c`, which `lookupGlobal` cannot find while `c` is checked.

The assignment `ρ` is a parameter. A program's terms mention no abstract value (a hole is
`.prim "hole" []`, where `run` is undefined), so the run of a definition's body does not read it.
A stored type does when it holds a hole's abstract value (`GDef.absTys`), and so do a state's
values, through `ProgState.codeMeaning`.

## Sanity (`ProgSanity`, without `sorry`)

`def one : Nat := S(Z)` means `1` (`defMeaning_one`). The checker accepts it from empty Σ and
stores it at type `Nat`: the kernel runs `checkItem`, in about a second (`one_accepted`). So the
program `[one]` gives the global `one` the meaning `1` (`progMeaning_one`), and a later
`.const "one"` reads that (`run_const_one`). A version after the library prelude is out of reach:
the kernel runs out of memory on the prelude's inductive declarations (`checkInd`).

## Gaps (reported to the spine)

Since D12 (4ea4b9e0) the `.fix` clause reads `Decisions.piSort`. A proof-valued function means
`•` and a `Type₀` one an element of `piCar0`, each in its type's meaning. A function in `Type₁` or
`Type₂`, such as `id (A : Type) (x : A) : A`, means `err` until the level-1/2 construction
(`Apply1.lean`'s `closureAt`/`piTyAt`) is wired into the `.fix`, `.pi` and call clauses. Until
then, milestone 4's corollary fails for polymorphic definitions.
-/

namespace Ochr.Meaning

/-- What the program meaning carries from one item to the next: Σ as the checker has it after
the items accepted so far, and the meaning of each accepted definition. -/
structure ProgState : Type 3 where
  /-- The checker's globals after the accepted items (`checkDefs`' and `globalsAfterFrom`'s
  `globals`), as `GDef`s: the decisions read them. -/
  globals : List GDef := []
  /-- The checker's inductive declarations after the accepted items (their `inds`): the run's
  `Γ`, interpreted by the data model. -/
  inds : List IndDecl := []
  /-- Each accepted definition, in program order: its name, its meaning, and its type as the
  run knows it (with its Π-shape, docs/31 D9). -/
  means : List (String × Sem × TyS) := []

namespace ProgState

/-- The meaning of the global `n`: the first accepted definition named `n`, as the checker's
`lookupGlobal` finds the first `GDef` named `n` (an accepted program has distinct names,
`Check.declared`); `err` for a name that is not a global. -/
def globalMean (P : ProgState) (n : String) : Sem :=
  match P.means.find? (·.1 == n) with
  | some (_, s, _) => s
  | none => .err

/-- The type of the global `n` as the run knows it, with its Π-shape (`run`'s `.const` reads it,
through `CodeMeaning.global`). -/
def globalTy (P : ProgState) (n : String) : TyS :=
  match P.means.find? (·.1 == n) with
  | some (_, _, T) => T
  | none => .plain .err

/-- The code meaning a later item's run reads: each global's meaning and type. `run` reads only
`CodeMeaning.global` of its context (`.const`, and `meanV`'s and `.val`'s `.gfn`): it gives the
other forms, sealed programs, closures, Π-closures and deferred types, by running their code
itself (the knot, `Run.lean`), so the other fields here are never read and are `err`.
`codeMeaning` builds the full one from this. -/
def baseC (P : ProgState) : CodeMeaning where
  global n := (P.globalMean n, P.globalTy n)
  sealed _ _ _ _ := .err
  clo _ _ _ _ _ := .err
  pi _ _ _ _ _ := .err
  paramTy _ _ _ _ := .plain .err

/-- The run context of code checked from the checker state `st` after the items of `P`: the data
model, `st`'s inductive declarations, the meanings of `P`'s globals, and the decisions at `st`. -/
def ctx (dm : DataModel) (D : MState → Decisions) (P : ProgState) (st : MState) : RunCtx :=
  { dm, Γ := st.inds, C := P.baseC, D := D st }

/-- The data model speaks for every inductive declaration of Σ (`DataModel.covers`): the
hypothesis under which its laws hold for the program. -/
def Covered (dm : DataModel) (P : ProgState) : Prop := ∀ d ∈ P.inds, dm.covers d

end ProgState

section
variable (dm : DataModel) (D : MState → Decisions) (ρ : Assignment)

/-- The meaning of an accepted constant at its type: `•` at a proposition, as the checker
stores `⋆` for a constant whose goal is a proposition (`checkDef`: `isPropV goal`); otherwise
the body's meaning. -/
def constMean (T : TyM) (v : Sem) : Sem :=
  match T with
  | .prop _ => .proof
  | _ => v

/-- The type of a global as the run knows it, from the type value the checker stores
(`GDef.ty`): `Value.tyS` (its meaning at the constant future, and for `D(ā)` the parameters'
meanings, D8), and for a Π-type its shape read off its Π-term in the frame of its captures
(`piShapeOf`), as `run`'s `.val` clause gives a Π-type value's. A function's stored type is
`tPi [] (pi x̄ Ā B) []`, whose shape is that of its `fix` term (same binders and codomain). -/
noncomputable def globalTyS (K : RunCtx) (T : Value) : TyS :=
  { Value.tyS K.dm (codeMeaning K) K.Γ ρ T with
    shape := match T with
      | .tPi caps t rd =>
        (piShapeOf K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))) t).map
          fun sh => (sh.ps, sh.out)
      | _ => none }

/-- The meaning of a definition whose stored type is `T` (`GDef.ty`), with its type
(`globalTyS`), under the run context `K` (`ProgState.ctx`); `none` where the reference run is
undefined. Both forms run from the empty state at the constant future (a definition is closed and
returns no live loan, [Return] D76).
* A function `def f (x̄ : Ā) : B := b` ([Def], `checkFix (.gfn f) [] fixT`): the run of the
  closed term `fix f (x̄:Ā):B := b`, which `checkDef` builds and checks. The `.fix` clause makes
  it a closure on its annotated domain, with `self` bound to the function itself (by stages when
  it recurses, `by xⱼ`).
* A constant `def c : B := b` ([Const]): the run of `b` at its goal's type, the goal being the
  stored type (the checker's `eval true d.body goal`, the goal as hint, D8); `•` at a proposition
  (`constMean`). -/
noncomputable def defMeaning (K : RunCtx) (d : Def) (T : Value) : Option (Sem × TyS) :=
  let A := globalTyS ρ K T
  if d.doms.isEmpty then
    match run K ρ noFuture A d.body (emptyState 0) with
    | some ((v, _), _) => some (constMean A.m v, A)
    | none => none
  else
    match run K ρ noFuture (.plain .err) (.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) (emptyState 0) with
    | some ((v, _), _) => some (v, A)
    | none => none

/-- One item, as one iteration of `globalsAfterFrom`'s loop: `checkItem` from the state that
keeps only Σ; if it is accepted (`Outcome.ok`), Σ becomes the final state's (the checker's
globals and inductive types after the item) and an accepted definition's meaning is appended
(`err` where the run is undefined), read under the decisions at that final state and at the
definition's stored type there (`GDef.ty`, the first global of its name, as `lookupGlobal`
finds it). An item not
accepted changes nothing (the verdict boundary). -/
noncomputable def ProgState.step (cfg : Config) (fuel : Nat) (P : ProgState) (it : Item) : ProgState :=
  let st : MState := { globals := P.globals, inds := P.inds, cfg := cfg }
  match (runMachine (checkItem it) st fuel).1 with
  | .ok () st' =>
    let means := match it with
      | .defn d =>
        let T := ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot
        P.means ++ [(d.name, (defMeaning ρ (P.ctx dm D st') d T).getD (.err, .plain .err))]
      | .ind _ => P.means
    { globals := st'.globals, inds := st'.inds, means }
  | _ => P

/-- The meaning of a list of items from a start: the items in program order (`ProgState.step`). -/
noncomputable def progMeaningFrom (cfg : Config) (fuel : Nat) (start : ProgState) (items : List Item) :
    ProgState :=
  items.foldl (ProgState.step dm D ρ cfg fuel) start

/-- The meaning of a program: its items from empty Σ, the library's among them, first, as in
`checkDefs` and `globalsAfter`. -/
noncomputable def progMeaning (cfg : Config) (fuel : Nat) (items : List Item) : ProgState :=
  progMeaningFrom dm D ρ cfg fuel {} items

/-- The code meaning of the program's globals for a state the checker reaches at `st` after the
items of `P` (`Run.lean`'s `codeMeaning`, read at the assignment and future it is asked at): what
`Value.mean` reads for globals, sealed programs, closures, Π-closures and deferred types. -/
noncomputable def ProgState.codeMeaning (P : ProgState) (st : MState) : CodeMeaning :=
  Ochr.Meaning.codeMeaning (P.ctx dm D st)

/-- The Σ the program meaning carries is the checker's: from any start, it is
`globalsAfterFrom` at the same items (at the fuel `globalsAfterFrom` fixes). -/
theorem progMeaningFrom_sig (cfg : Config) (P : ProgState) (items : List Item) :
    let P' := progMeaningFrom dm D ρ cfg 2000000 P items
    (P'.globals, P'.inds) = globalsAfterFrom cfg (P.globals, P.inds) items := by
  induction items generalizing P with
  | nil => simp [progMeaningFrom, globalsAfterFrom]
  | cons it rest ih =>
    simp only [progMeaningFrom, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [globalsAfterFrom, ProgState.step]
    generalize (runMachine (checkItem it) _ 2000000).fst = o
    cases o <;> rfl

/-- The Σ of a program's meaning is `globalsAfter`'s. -/
theorem progMeaning_sig (cfg : Config) (items : List Item) :
    let P := progMeaning dm D ρ cfg 2000000 items
    (P.globals, P.inds) = globalsAfter cfg items :=
  progMeaningFrom_sig dm D ρ cfg {} items

end

/-! ## Sanity: a constant's meaning, through the checker's verdict, to later code -/

namespace ProgSanity

/-- `def one : Nat := S(Z)`, as `resolveDecl` makes it. -/
def oneDef : Def := { name := "one", hs := [], doms := [], cod := .nat, body := .succ .zero }

theorem run_const (K : RunCtx) (ρ : Assignment) (φ : Future) (h : TyS) (n : String) (s : SState) :
    run K ρ φ h (.const n) s = some (K.C.global n, s) := rfl

theorem run_succ_zero (K : RunCtx) (ρ : Assignment) (φ : Future) (h : TyS) (s : SState) :
    run K ρ φ h (.succ .zero) s = some (((Sem.el0 Nat 0).succ, .plain (.ty0 Nat)), s) := rfl

/-- `Nat`'s stored type value means the carrier `Nat`, with no shape. -/
theorem globalTyS_nat (K : RunCtx) (ρ : Assignment) : globalTyS ρ K .tNat = .plain (.ty0 Nat) := rfl

/-- `one` means the number `1` at type `Nat`, under every run context. -/
theorem defMeaning_one (K : RunCtx) (ρ : Assignment) :
    defMeaning ρ K oneDef .tNat = some (.el0 Nat 1, .plain (.ty0 Nat)) := by
  simp only [defMeaning, globalTyS_nat, oneDef, List.isEmpty_nil, if_true, run_succ_zero]
  simp [TyS.plain, constMean, Sem.succ, Sem.asNat, Sem.as]

/-- A stored type that is `Nat`. -/
def isNatTy : Option Value → Bool
  | some .tNat => true
  | _ => false

theorem isNatTy_eq {x : Option Value} (h : isNatTy x = true) : x = some .tNat := by
  rcases x with _ | v
  · simp [isNatTy] at h
  · cases v <;> simp_all [isNatTy]

set_option maxRecDepth 100000 in
/-- The checker accepts `one` from empty Σ and stores it at type `Nat` (the kernel runs
`checkItem`). -/
theorem one_accepted :
    ∃ st', (runMachine (checkItem (.defn oneDef)) { globals := [], inds := [], cfg := {} } 2000000).1 = .ok () st' ∧
      (st'.globals.find? (·.name == "one")).map (·.ty) = some .tNat := by
  have h : (match (runMachine (checkItem (.defn oneDef)) { globals := [], inds := [], cfg := {} } 2000000).1 with
      | .ok () st' => isNatTy ((st'.globals.find? (·.name == "one")).map (·.ty))
      | _ => false) = true := by decide
  revert h
  generalize (runMachine (checkItem (.defn oneDef)) _ 2000000).1 = o
  cases o with
  | ok a st' => intro h; exact ⟨st', rfl, isNatTy_eq h⟩
  | fail => intro h; cases h
  | exhausted => intro h; cases h

/-- The program `def one : Nat := S(Z)` records `one` with the meaning `1` at type `Nat`, whatever
the data model, decisions and assignment: the checker accepts it, so its meaning is recorded. -/
theorem progMeaning_one (dm : DataModel) (D : MState → Decisions) (ρ : Assignment) :
    (progMeaning dm D ρ {} 2000000 [.defn oneDef]).means = [("one", .el0 Nat 1, .plain (.ty0 Nat))] := by
  obtain ⟨st', h, hT⟩ := one_accepted
  simp only [progMeaning, progMeaningFrom, List.foldl_cons, List.foldl_nil, ProgState.step]
  rw [show ({ globals := ({} : ProgState).globals, inds := ({} : ProgState).inds, cfg := {} } : MState)
      = { globals := [], inds := [], cfg := {} } from rfl, h]
  dsimp only
  rw [show oneDef.name = "one" from rfl, hT]
  simp only [Option.getD_some]
  rw [defMeaning_one]
  rfl

/-- ... and a later term reads it: the run of `one` in any state of the program's context. -/
theorem run_const_one (dm : DataModel) (D : MState → Decisions) (ρ : Assignment) (st : MState)
    (φ : Future) (h : TyS) (s : SState) :
    run ((progMeaning dm D ρ {} 2000000 [.defn oneDef]).ctx dm D st) ρ φ h (.const "one") s =
      some ((.el0 Nat 1, .plain (.ty0 Nat)), s) := by
  rw [run_const]
  simp only [ProgState.ctx, ProgState.baseC, ProgState.globalMean, ProgState.globalTy, progMeaning_one]
  rfl

end ProgSanity

end Ochr.Meaning
