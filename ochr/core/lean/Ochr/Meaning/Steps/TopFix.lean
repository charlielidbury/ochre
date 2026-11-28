import Ochr.Meaning.Steps.TopConst

/-!
# The top, a function: from `TailAt` at its body to its closure being a member of its type (THE KNOT; lead43, docs/31 D254)

A definition with parameters is checked by `checkDef`'s function branch: its entry appended to Σ, then `checkFix`, which
builds the generic state (a cell per borrow parameter in frame 0; the captures, the definition's own binding, the
parameters in frame 1; the goal) and runs `checkTail` on the body with the continuation `fixCont` (copied from
`checkFix`: [Return], the frame's pop, the conversion of the leaf's type to the goal as refined on the path).

**The knot** (`knot_step`, assembled here): the guarded fixpoint's stage `b + 1` at member arguments `a` of rank below
`b + 1` is the body run in the closure's frame with its own binding the stage-`b` closure at the weakened type
(`FixEqDesc.stG_succ`, by definition). It is good because the checker's check of the body is simulated there: `TailAt`
(from `master`) at the context `K_b` of the check with the definition under check at bound `b` meaning that very
stage closure (`ctxAt … (some (f, b, stageClo …))`), from the generic state related to the closure's frame at `a`
(`FixStartAt`, which consumes the induction hypothesis: stage `b` good below `b` is `GlobalsOk.memBelow` at `K_b`); the
fundamental lemma at the reference's run; the leaf (`FixLeafAt`). `Steps.knot_member` (PROVED) then makes the closure a
member of its true type.

**Two contexts, one run.** The knot's stages are runs at the stage's context `P.ctx` (where the program meaning forms
the closure, `defMeaning`); the simulation runs at `K_b`, which differs only in naming the definition under check
(`K.cur`) and giving its name the stage closure. A body that reads its own name only through its own binding runs alike
under both (`BodyCongrAt`); that is false until decision (b)'s model clause for a body forming a closure or a block that
names the definition by its global (main's D139).
-/

namespace Ochr.Meaning.Steps.Form.Top

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Meaning.Assembly

/-- **`checkFix`'s continuation**, copied from `Machine.checkFix` (the function `name`, at fuel `fuel'`): [Return] of the
leaf's value, the value held as a temporary of the cells' frame while the body's frame pops, then the conversion of the
leaf's type to the goal as the path refined it. -/
def fixCont (fuel' : Nat) (name : String) : Value → Value → M Unit := fun v T => do
  wholeReturned v
  bodyReturns fuel' s!"{name} returns it" v T [] ""
  pushTempAt ((← topIdx) - 1) v (some T) "checkFix"
  popFrame fuel'
  discard popTemp
  let g := (← get).goal.getD .bot
  trace fun _ => s!"[Def] {name}: path ends with type {T} against goal {g}"
  unless ← conv fuel' T g do
    err s!"the body of {name} has type {T}, but the goal is {g}"

section
variable (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (fuel : Nat)

/-- The stage-`b` closure of the code `(hs, ds, c, dec, body)` at the context `K`, at the weakened type, with that type:
the definition's own binding in stage `b + 1`'s run (`stG_succ`), and the meaning of its name in `K_b`. -/
noncomputable def stageClo (K : RunCtx) (ρ : Assignment) (φ : Future) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (b : Nat) : Sem × TyS :=
  (closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) (weakCod (lG K hs ds c) (fixRank dec) b (outG K ρ φ ds c))
      (stageFn (lG K hs ds c) (psG K ρ φ ds) (fixRank dec) b (stG K ρ φ hs ds c dec body b)),
    .plain (piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) (weakCod (lG K hs ds c) (fixRank dec) b (outG K ρ φ ds c))))

/-- The closure's frame at the arguments `a`, at stage `b + 1` (the start state `fixBodyAt` runs the body from). -/
noncomputable def startAt (K : RunCtx) (ρ : Assignment) (φ : Future) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (b : Nat) (a : List Sem) : SState :=
  let G := stageClo K ρ φ hs ds c dec body b
  let sb : SBinding := ⟨.plain G.2.m, fun _ => G.1, .pi (fbG K ρ φ ds c).2.2, none⟩
  ((a.zip (psG K ρ φ ds)).foldl (fixStep (fbG K ρ φ ds c)) (formG.under.pushBind sb, [], [])).1

/-- The entry `checkDef` appends to Σ for a function (`model` as the checker decides it). -/
def fnEntry (d : Def) (model : Bool) : GDef :=
  { name := d.name, ty := .tPi [] (.pi d.hs d.doms d.cod) [], fn? := some (.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body),
    val := .gfn d.name, model }

/-- What the checker's inversion of an accepted function produces: the fuel of its body's tail check, the generic
state `st₀` it starts from, the state after it, and the entry's `model` flag. Every other link of a function is a
predicate on THIS witness (docs/31 D254: as first stated, about every state and definition, they were false at junk
arguments). -/
structure FixWit where
  n : Nat
  st₀ : MState
  st₁ : MState
  bh : Nat
  model : Bool

/-- **The function branch of `checkDef`, inverted to the body's tail check** (CHECKER; read true against `checkDef`,
`checkFix`; the machine lane's to prove). The generic state the body is checked from (the plain mode, no reading handed
down, Σ the stage's and the function's entry), the run of `checkTail` with `fixCont`, what `TailAt` asks of the
continuation (it only extends the tables, `GrowsM`, and keeps their invariant, `KeepsTab`: owed since D250, machine code
throughout), and the entry stored. -/
def FixCheckAt (P : ProgState) (d : Def) (st' : MState) (w : FixWit) : Prop :=
  ModeR w.st₀ ∧ w.st₀.tailNext = false ∧ 0 < w.st₀.env.size ∧ w.st₀.tailDecl = none ∧
  w.st₀.globals = P.globals ++ [fnEntry d w.model] ∧
  Runs (Ochr.checkTail w.n d.body (fixCont w.n d.name)) w.st₀ w.bh () w.st₁ ∧
  (∀ v T, GrowsM (fixCont w.n d.name v T)) ∧ (∀ v T, KeepsTab (fixCont w.n d.name v T)) ∧
  st'.globals = P.globals ++ [fnEntry d w.model] ∧
  ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot = .tPi [] (.pi d.hs d.doms d.cod) []

/-- **The context of the check at bound `b`**: the item's context with the definition under check at `b`, meaning its
stage-`b` closure (formed at the stage's context, at the knot's assignment and future). -/
noncomputable def ctxB (P : ProgState) (d : Def) (st' : MState) (ρ : Assignment) (φ : Future) (b : Nat) : RunCtx :=
  ctxAt dm Γ P (D st') (some (d.name, b, stageClo (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b))

/-- The knot's induction hypothesis at `b`: stage `b` is good at member arguments of rank below `b`. -/
def GoodBelowB (K : RunCtx) (ρ : Assignment) (φ : Future) (d : Def) (b : Nat) : Prop :=
  ∀ a, DomMembers K.dm.read (psG K ρ φ d.doms) a → fixRank d.dec a < b →
    ∃ o, stG K ρ φ d.hs d.doms d.cod d.dec d.body b a = some o ∧
      OutGood' K.dm.read (psG K ρ φ d.doms) (outG K ρ φ d.doms d.cod) a o

/-- **The function type fits its sort** (MIXED; the old chain's `fix_sortRule` and `fix_canon`, UNCERTAIN: the sort rule
for the parts of a function type as the run reads them, and canonical codes). -/
def FixFitsAt (P : ProgState) (d : Def) (st' : MState) : Prop :=
  ∀ (ρ : Assignment) (φ : Future),
    PiFits dm.read (lG (P.ctx dm D Γ st') d.hs d.doms d.cod) (psG (P.ctx dm D Γ st') ρ φ d.doms)
      (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod) (fun _ => True)

/-- **The start of the check at bound `b`** (MIXED; read true by parts, unproved). At member arguments `a` of rank below
`b + 1`, given the induction hypothesis, there is an assignment of the generic state's unknowns (each parameter's its
argument) under which: `Pre` at the generic state in `K_b` (its `GlobalsOk`: the stage's globals from the invariant,
the definition's own `memBelow` at `b` from the induction hypothesis, its `codeValFree` from resolution; `RecCurG` both
ways once `EvalAt` carries it, false until main's D147); the generic state related to the closure's frame at `a`
(`startAt`: cells, its own binding, the parameters; docs/31 D126) and that frame good; the body holding no embedded value,
unknown or hole; the table aligned at the run's end; and the checker's goal read under the assignment as the closure's
body hint at `a` (the codomain at `a`, (M1)). -/
def FixStartAt (P : ProgState) (d : Def) (st' : MState) (w : FixWit) : Prop :=
  ∀ (ρ : Assignment) (φ : Future) (b : Nat) (a : List Sem),
    GoodBelowB (P.ctx dm D Γ st') ρ φ d b →
    DomMembers dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) a → fixRank d.dec a < b + 1 →
    ∃ (ρa : Assignment) (π : Nat → Nat),
      Pre (ctxB dm D Γ P d st' ρ φ b) ρa w.st₀ ∧
      Rel (ctxB dm D Γ P d st' ρ φ b) ρa φ π w.st₀
        (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) ∧
      Strict.SGood dm Γ φ (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) ∧
      d.body.valsOk (Strict.ValsP (ctxB dm D Γ P d st' ρ φ b) ρa φ) ∧ d.body.absBelow w.st₀.absTy.size ∧
      d.body.hasHolePrim = false ∧ DecTab (D st') w.st₁ ∧
      hintM (ctxB dm D Γ P d st' ρ φ b) ρa w.st₀.goal = (fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod).2.1 a

/-- **The body runs alike in the check's context and the stage's** (MODEL; read true for a body that reads its own name
only through its own binding: the run reads neither `K.cur` nor, then, the global under check's meaning, and a closed
body no assignment; FALSE until decision (b)'s model clause for a body forming a closure or a block that names the
definition by its global, main's D139, which the stage's context reads as `ProgState.dfltGlobal`). -/
def BodyCongrAt (P : ProgState) (d : Def) (st' : MState) : Prop :=
  ∀ (ρ ρa : Assignment) (φ : Future) (b : Nat) (h : TyS) (s : SState),
    runT (ctxB dm D Γ P d st' ρ φ b) ρa φ true h d.body s = runT (P.ctx dm D Γ st') ρ φ true h d.body s

/-- **The leaf of the check at bound `b`** (MIXED; unread as one fact). Its parts: the leaf's type converts to the goal
as the path refined it, which the extended assignment meets, so the reference's result type is the codomain at `a`
(conversion's soundness at a type, N3); [Return] makes the result whole, not `⊥`; the reference's frame pop (`fixBodyAt`'s
ends) passes and leaves members in the cells (the checker's pop, through the relation at the leaf, for a body not read
as a proof; for a proof, whose leaf gives no relation, the reference restores the start's state, so the finals are the
arguments); a returned borrow's backward function is injective (N5's (X5)). From `TailAt`'s conclusion, the fundamental
lemma at the reference's run, and the run being the stage's: stage `b + 1`'s output at `a` is good.

Since docs/31 D256 it also takes what the knot has at that point and lead43's form left out: `a`'s rank below `b + 1` (above
it the stage-`b` self returns its weakened output, and nothing else in the hypotheses excludes that) and the start's `Pre`
and relation at the assignment `ρa` (which ties `ρa`'s parameters to `a`, so that the goal under `ρa` is the codomain at
`a`). Both only weaken the link. -/
def FixLeafAt (P : ProgState) (d : Def) (st' : MState) (w : FixWit) : Prop :=
  ∀ (ρ ρa : Assignment) (φ : Future) (π : Nat → Nat) (b : Nat) (a : List Sem),
    DomMembers dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) a → fixRank d.dec a < b + 1 →
    Pre (ctxB dm D Γ P d st' ρ φ b) ρa w.st₀ →
    Rel (ctxB dm D Γ P d st' ρ φ b) ρa φ π w.st₀ (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) →
    TailConcl (ctxB dm D Γ P d st' ρ φ b) ρa φ π w.st₀ (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a)
      d.body (runT (ctxB dm D Γ P d st' ρ φ b) ρa φ true (hintM (ctxB dm D Γ P d st' ρ φ b) ρa w.st₀.goal) d.body)
      (fixCont w.n d.name) →
    runT (ctxB dm D Γ P d st' ρ φ b) ρa φ true (hintM (ctxB dm D Γ P d st' ρ φ b) ρa w.st₀.goal) d.body
        (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) =
      runT (P.ctx dm D Γ st') ρ φ true ((fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod).2.1 a) d.body
        (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) →
    (∀ r s', runT (P.ctx dm D Γ st') ρ φ true ((fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod).2.1 a) d.body
        (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) = some (r, s') →
      Strict.GoodRes dm.read r ∧ Strict.SGood dm Γ φ s') →
    ∃ o, stG (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body (b + 1) a = some o ∧
      OutGood' dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod) a o

/-! ## The knot's step, composed -/

/-- **`FundCtx` at a check's context** (PROVED): the stage's members, the definition under check's meaning a good result
with no label, and no data declaration at `Type₁`. -/
theorem fundCtx_ctxAt (dm : DataModel) (Γ : List IndDecl) (P : ProgState) (Dd : Decisions) (f : String) (b : Nat)
    (G : Sem × TyS) (hmem : MeansMember dm P) (hlab : ∀ e ∈ P.means, e.2.2.label = none)
    (hG : Strict.GoodRes dm.read G) (hGl : G.2.label = none) (hsorts : ∀ d ∈ Γ, d.sort ≠ 2) :
    Strict.FundCtx (ctxAt dm Γ P Dd (some (f, b, G))) := by
  refine ⟨fun n => ?_, hsorts⟩
  show Strict.GoodRes dm.read (if n = f then G else P.baseC.global n) ∧ (if n = f then G else P.baseC.global n).2.label = none
  by_cases hn : n = f
  · simp only [hn, if_true]; exact ⟨hG, hGl⟩
  · simp only [hn, if_false]
    exact (fundCtx_progCtx dm (fun _ => Dd) Γ P ({} : MState) hmem hlab hsorts).globals n

/-- **The stage closure at the weakened type is a member** (PROVED): from the type fitting its sort and the stage good
below its bound (`stageFn_good'`, `closure_mem_of_total`). -/
theorem stageClo_mem (K : RunCtx) (ρ : Assignment) (φ : Future) (d : Def) (b : Nat)
    (hfit : PiFits K.dm.read (lG K d.hs d.doms d.cod) (psG K ρ φ d.doms) (outG K ρ φ d.doms d.cod) (fun _ => True))
    (hIH : GoodBelowB K ρ φ d b) :
    (stageClo K ρ φ d.hs d.doms d.cod d.dec d.body b).1 ∈ₛ[K.dm.read] (stageClo K ρ φ d.hs d.doms d.cod d.dec d.body b).2.m :=
  closure_mem_of_total K.dm.read _ φ _ _ _ (piFits_weakCod hfit _ _) (stageFn_good' hfit hIH)

end

section
variable (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (fuel : Nat)

/-- **The function's meaning is its guarded fixpoint's closure, at its stored type** (MODEL; read true: `run_fix_def`,
the `.fix` clause at the empty state, where a global captures nothing; its strict test is the closure's membership, the
premise; at sort `0` (a lemma) the clause is erased to `•`, which is the closure at sort `0`; the stored type
`Π(x̄ : Ā). B`'s meaning is the code the `.fix` term's domains and codomain run to, `piTyAt (lG) (psG) (outG)` at the
forming state `formG = emptyState 0`). -/
def FixMeanAt (P : ProgState) (d : Def) (st' : MState) : Prop :=
    closureAt dm.read (lG (P.ctx dm D Γ st') d.hs d.doms d.cod) noFuture
        (psG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.doms) (outG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.doms d.cod)
        (GG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.hs d.doms d.cod d.dec d.body) ∈ₛ[dm.read]
      piTyAt dm.read (lG (P.ctx dm D Γ st') d.hs d.doms d.cod) (psG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.doms)
        (outG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.doms d.cod) →
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d (.tPi [] (.pi d.hs d.doms d.cod) []) = some m ∧
      m.1 ∈ₛ[dm.read] m.2.m


/-- **The function type's parts run at every member tuple** (`PartsRun`; MIXED, read true: (II) at `checkFix`'s own
evaluations of the parameter types and the codomain at the generic arguments, then (I); docs/31 D257). Its failure
makes the stored type mean `err`, which has no member. FixFitsAt's sort-0 clause is an instance. -/
def FixPartsAt (P : ProgState) (d : Def) (st' : MState) : Prop :=
  PiOk dm.read (psG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.doms) [] (outG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.doms d.cod)

/-- **A global's code is closed** (RESOLUTION, read true: a top-level definition's resolved `fix` term has no free
variable). -/
def FixClosedAt (d : Def) : Prop := (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body).freeVars = []

/-- **The table reads the `fix` term as a proof only at sort `0`** (DECISIONS, read true: the proof flag and `piSort`
both read the codomain's declared sort). -/
def FixFlagAt (P : ProgState) (d : Def) (st' : MState) : Prop :=
  ((P.ctx dm D Γ st').D.flags (scopeOf (emptyState 0)) (.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body)).2 = true →
    lG (P.ctx dm D Γ st') d.hs d.doms d.cod = 0

/-- **A function's links, about its own check**: an accepted function at a stage meeting the invariant has a witness
meeting all eight (`FixMeanAt` is derived from the last three, `fixMeanAt_of`, docs/31 D257). -/
def FixG (items : List Item) : Prop :=
  ∀ (P : ProgState) (d : Def) (st' : MState), AtStage dm D Γ fuel items P (.defn d) → d.doms ≠ [] →
    (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st' →
    StageOk dm D Γ P → DataFaithful dm D Γ P → (∀ d' ∈ Γ, dm.covers d') → P.inds <+: Γ →
    ∃ w : FixWit, FixCheckAt P d st' w ∧ FixFitsAt dm D Γ P d st' ∧ FixStartAt dm D Γ P d st' w ∧
      BodyCongrAt dm D Γ P d st' ∧ FixLeafAt dm D Γ P d st' w ∧ FixPartsAt dm D Γ P d st' ∧ FixClosedAt d ∧
      FixFlagAt dm D Γ P d st'

end

/-! ## `FixMeanAt` derived (docs/31 D257): the round trip of codes is definitional -/

/-- **The stored Π-type's meaning is the `.pi` term's run at the forming state**: `piTyAt` at the parts when they run
(`PiOk`). -/
theorem globalTyS_tPi (K : RunCtx) (hs : List Hint) (ds : List Term) (c : Term)
    (hok : PiOk K.dm.read (psG K (fun _ => .err) noFuture ds) [] (outG K (fun _ => .err) noFuture ds c)) :
    globalTyS (fun _ => .err) K (.tPi [] (.pi hs ds c) []) =
      .plain (piTyAt K.dm.read (lG K hs ds c) (psG K (fun _ => .err) noFuture ds) (outG K (fun _ => .err) noFuture ds c)) := by
  unfold globalTyS Value.tyS
  rw [meanV_eq_mean]
  have h1 : meanV K (fun _ => .err) (fun _ => .err) (.plain .err) (.tPi [] (.pi hs ds c) []) =
      (match run K (fun _ => .err) (fun _ => .err) (.plain .err) (.pi hs ds c) (stateOf 0 []) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err) := by
    classical
    show (if CapsOk K.dm.read (capsVals K (fun _ => .err) (fun _ => .err) []) (capsTys K (fun _ => .err) (fun _ => .err) []) then
        match run K (fun _ => .err) (fun _ => .err) (.plain .err) (.pi hs ds c)
          (stateOf 0 (capsState (capsVals K (fun _ => .err) (fun _ => .err) []) (capsTys K (fun _ => .err) (fun _ => .err) []))) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err
      else .ty TyM.err) = _
    rw [capsVals, capsTys, if_pos (show CapsOk K.dm.read [] [] from trivial)]
    rfl
  have hok' : PiOk K.dm.read (runDoms K (fun _ => .err) (fun _ => .err) (stateOf 0 []) ds) []
      (codOf K (fun _ => .err) (fun _ => .err) (stateOf 0 []) (bindsOf K (fun _ => .err) (fun _ => .err) (stateOf 0 []) ds)
        (ds.map Term.isRefTy) c) := hok
  rw [h1, run, run_pi_def, if_pos hok']
  rfl

/-- A strict test that passes. -/
theorem strictS_some (R : DataRead) (x : Sem × TyS) (s : SState) (h : x.1 ∈ₛ[R] x.2.m) :
    SM.strictS R (fun s' => some (x, s')) s = some (x, s) := by
  simp only [SM.strictS, if_pos h]

/-- **`FixMeanAt` from `PartsRun`** (kernel-checked; standard axioms): a function's recorded meaning is a member of its
stored type, given the parts of that type running at every member tuple (`PartsRun`, `PiOk`: (II) at `checkFix`'s
evaluations of the parameter types and the codomain, then (I)), the code closed (a resolution fact), and the table's proof
flag on the fix term only at sort `0` (both decisions read the codomain's declared sort). -/
theorem fixMeanAt_of (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (P : ProgState) (d : Def) (st' : MState)
    (hd : d.doms ≠ []) (hclosed : FixClosedAt d) (hparts : FixPartsAt dm D Γ P d st') (hflag : FixFlagAt dm D Γ P d st') :
    FixMeanAt dm D Γ P d st' := by
  intro hmem
  unfold FixFlagAt at hflag
  have hA := globalTyS_tPi (P.ctx dm D Γ st') d.hs d.doms d.cod hparts
  have hcap : capOrder (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) = [] := by
    have hc : (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body).freeVars = [] := hclosed
    unfold capOrder; rw [hc]; rfl
  have hne : d.doms.isEmpty = false := by
    cases h : d.doms with
    | nil => exact absurd h hd
    | cons _ _ => rfl
  unfold defMeaning
  have hfm : fixMoves (P.ctx dm D Γ st') (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) (emptyState 0) = emptyState 0 := by
    unfold fixMoves; rw [hcap]; rfl
  have he0 : (emptyState 0 : SState) = stateOf 0 [] := rfl
  rw [hne, if_neg Bool.false_ne_true, run, run_fix_def, hcap, hfm, hA]
  simp only [FoldOk, if_true, he0]
  simp only [psG, outG, lG, GG, formG, fbG] at hmem hflag
  rw [he0] at hflag
  generalize hfl : (P.ctx dm D Γ st').D.flags (scopeOf (stateOf 0 [])) (Term.fix ⟨d.name⟩ d.hs d.doms d.cod d.dec d.body) = fl at hflag ⊢
  obtain ⟨b1, b2⟩ := fl
  rw [strictS_some]
  · cases b2 with
    | false =>
      cases b1
      · exact ⟨_, rfl, hmem⟩
      · exact ⟨_, rfl, hmem⟩
    | true =>
      have hl : lG (P.ctx dm D Γ st') d.hs d.doms d.cod = 0 := hflag rfl
      have hl' : (P.ctx dm D Γ st').D.piSort (scopeOf (stateOf 0 [])) (Term.pi d.hs d.doms d.cod) = 0 := hl
      simp only [SM.erasedIf, if_true, hl', closureAt]
      refine ⟨_, rfl, ?_⟩
      have h0 := hmem
      simp only [hl', closureAt] at h0
      show Sem.proof ∈ₛ[dm.read] piTyAt dm.read (lG (P.ctx dm D Γ st') d.hs d.doms d.cod) _ _
      rw [hl]
      exact h0
  · exact hmem

section
variable {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {fuel : Nat}

/-- **THE KNOT'S STEP, composed** (assembled in Lean): stage `b + 1` good below `b + 1` from stage `b` good below `b`, by
`TailAt` at the body in the check's context at bound `b` (`master`), started by `FixStartAt`, the fundamental lemma at
the reference's run (`FundCtx` at that context PROVED from the invariant and the stage closure's membership), the run
being the stage's (`BodyCongrAt` with the start's hint), and the leaf (`FixLeafAt`). -/
theorem knot_step
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (P : ProgState) (d : Def) (st' : MState) (hP : StageOk dm D Γ P) (w : FixWit)
    (hck : FixCheckAt P d st' w) (hfits : FixFitsAt dm D Γ P d st') (hstart : FixStartAt dm D Γ P d st' w)
    (hcongr : BodyCongrAt dm D Γ P d st') (hleaf : FixLeafAt dm D Γ P d st' w)
    (ρ : Assignment) (φ : Future) (b : Nat) (hIH : GoodBelowB (P.ctx dm D Γ st') ρ φ d b) :
    ∀ a, DomMembers dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) a → fixRank d.dec a < b + 1 →
      ∃ o, stG (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body (b + 1) a = some o ∧
        OutGood' dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod) a o := by
  intro a ha hlt
  obtain ⟨hm, htn, hsz, htd, -, hrt, hgr, hkt, -, -⟩ := hck
  obtain ⟨ρa, π, hpre, hrel, hsg, hvals, hab, hhole, hdt, hhint⟩ := hstart ρ φ b a hIH ha hlt
  have hGmem := stageClo_mem (P.ctx dm D Γ st') ρ φ d b (hfits ρ φ) hIH
  have hfc : Strict.FundCtx (ctxB dm D Γ P d st' ρ φ b) :=
    fundCtx_ctxAt dm Γ P (D st') d.name b _ hP.mem hP.lab (.inl hGmem) rfl hsorts
  have hall := hsteps (ctxB dm D Γ P d st' ρ φ b) φ (fun _ => ⟨hfc.globals, hfc.sorts⟩)
  have hT := tail_all hall ρa w.n d.body w.st₀ (fixCont w.n d.name) _ π w.bh w.st₁ hm htn hsz htd hgr hkt hpre hrel hsg
    hvals hab hhole hdt hrt
  have heq := (congrArg (fun h => runT (ctxB dm D Γ P d st' ρ φ b) ρa φ true h d.body
      (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a)) hhint).trans
    (hcongr ρ ρa φ b _ _)
  refine hleaf ρ ρa φ π b a ha hlt hpre hrel hT heq (fun r s' hx => ?_)
  rw [← heq] at hx
  have hF := Strict.fund_all hfc d.body hvals true _ _ s' r hsg hx
  exact ⟨hF.1, hF.2.2.2⟩

end

section
variable {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {fuel : Nat}

/-- **The knot's output** (assembled): the guarded fixpoint is good at every member argument, at every assignment and
future, and the function type fits its sort (`stages_below` over `knot_step`). -/
theorem fnGoodAt_of_knot
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (P : ProgState) (d : Def) (st' : MState) (hP : StageOk dm D Γ P) (w : FixWit)
    (hck : FixCheckAt P d st' w) (hfits : FixFitsAt dm D Γ P d st') (hstart : FixStartAt dm D Γ P d st' w)
    (hcongr : BodyCongrAt dm D Γ P d st') (hleaf : FixLeafAt dm D Γ P d st' w) (ρ : Assignment) (φ : Future) :
    FnGoodAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body :=
  ⟨hfits ρ φ, fun a ha => Steps.stages_below (stG (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body)
    (fixRank d.dec) _ _ (fun b hb => knot_step hsteps hsorts P d st' hP w hck hfits hstart hcongr hleaf ρ φ b hb) a ha⟩

/-- **An accepted function means a member of its type** (assembled in Lean; THE KNOT): the witness of its check
(`FixG`), the knot's step at every bound, the induction on the bound and the closure's membership
(`Steps.knot_member`, PROVED), the meaning (`FixMeanAt`). At the program's assignment and the constant future, where the
program meaning forms a global's closure (`defMeaning`). -/
theorem fix_member
    (hsteps : ∀ (K : RunCtx) (φ : Future), (∀ Δ, Strict.FundCtx { K with Δ := Δ }) → AllSteps K φ)
    (hsorts : SortsG Γ) (P : ProgState) (d : Def) (st' : MState) (hP : StageOk dm D Γ P) (w : FixWit)
    (hck : FixCheckAt P d st' w) (hfits : FixFitsAt dm D Γ P d st') (hstart : FixStartAt dm D Γ P d st' w)
    (hcongr : BodyCongrAt dm D Γ P d st') (hleaf : FixLeafAt dm D Γ P d st' w) (hmean : FixMeanAt dm D Γ P d st') :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D Γ st') d
        (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  have hk := knot_member dm.read _ noFuture _ _
    (stG (P.ctx dm D Γ st') (fun _ => .err) noFuture d.hs d.doms d.cod d.dec d.body) (fixRank d.dec) (hfits _ _)
    (fun b hb => knot_step hsteps hsorts P d st' hP w hck hfits hstart hcongr hleaf _ _ b hb)
  rw [hck.2.2.2.2.2.2.2.2.2]
  exact hmean hk

end

end Ochr.Meaning.Steps.Form.Top
