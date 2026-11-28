import Ochr.Meaning.Lemmas
import Ochr.Meaning.HintIndep
import Ochr.Meaning.DecisionsInst
import Ochr.Meaning.DecideScope
import Ochr.Meaning.Program
import Ochr.Meaning.WF
import Ochr.Meaning.CallRef
import Ochr.Machine
import Ochr.Check
import Ochr.Meaning.DataModel.Faithful

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

/-- Arguments are members along a function type's code: each at the domain the code reaches at the
earlier ones. -/
def ArgsMember (R : DataRead) (T : TyM) (args : List Res) : Prop :=
  ∀ (i : Nat) (a : Res), args[i]? = some a → a.1 ∈ₛ[R] T.domAfter R ((args.take i).map (·.1))

/-- Arguments of a closure's code: one per domain, each a member of its domain at the earlier ones. -/
def DomMembers (R : DataRead) (ds : List PiDom) (args : List Sem) : Prop :=
  args.length = ds.length ∧
    ∀ (i : Nat) (a : Sem) (d : PiDom), args[i]? = some a → ds[i]? = some d → a ∈ₛ[R] d.dom (args.take i)

/-- **The labels a body's result holds past the body**, each with the type it is held at (docs/31 D141): the returned
borrow's label at the codomain's content type. They are the labels the frame pop keeps live (`Run.lean`'s `.fix`,
`keep`: at a data codomain a labelled result is ill-typed and its label is ended with the rest), so a data codomain's
result holds none. The model's result holds at most one label (`TyS.label`, `BodyOut.retLabel`), as the checker's does:
no borrow sits inside data (core D8, D48), and a borrow of a borrow is rejected (`Steps/BorrowParGuards.lean`). -/
def _root_.Ochr.Meaning.BodyOut.held (out : PiCod) (args : List Sem) (o : BodyOut) : List (Nat × TyM) :=
  if out.isRef then (o.retLabel.map fun k => (k, out.cod args)).toList else []

/-- A body's output is good at arguments: its result is a member of the codomain there, and each
borrow parameter's final content (`BodyOut.finals`, one per borrow parameter, in order) is a member
of that parameter's content type at every future TYPED FOR THE RESULT (docs/31 D141, the orchestrator's ruling): one
that gives each label the result holds a member of the type it is held at (`HeldTyped` at `BodyOut.held`, the
restriction of `TypedFut` to the result's labels). The body's own borrows have ended; a returned borrow's has not, and
the final of a borrow parameter it reborrows or returns is what the caller leaves in it (`K (r : &Nat) : &Nat := r`:
the final is the future at the returned label). At a data codomain the result holds no label and the clause is at
every future, as before D141; as first stated it was at every future for every codomain, false for every function
returning a borrow parameter (`ColumnW.not_outGood_K`). -/
def OutGood (R : DataRead) (ds : List PiDom) (out : PiCod) (args : List Sem) (o : BodyOut) : Prop :=
  o.result ∈ₛ[R] out.cod args ∧
    ∀ (i : Nat) (d : PiDom), ds[i]? = some d → d.isRef = true →
      ∃ f, o.finals[((ds.take i).filter (·.isRef)).length]? = some f ∧
        ∀ ψ, HeldTyped R (o.held out args) ψ → f ψ ∈ₛ[R] d.dom (args.take i)

/-- A data codomain's result holds no label. -/
theorem _root_.Ochr.Meaning.BodyOut.held_data {out : PiCod} (args : List Sem) (o : BodyOut) (h : out.isRef = false) :
    o.held out args = [] := by
  simp [BodyOut.held, h]

/-- Every future is typed at no label. -/
theorem heldTyped_nil (R : DataRead) (ψ : Future) : HeldTyped R [] ψ := fun _ _ h => by cases h

/-- At a data codomain every future is typed for the result. -/
theorem heldTyped_data {R : DataRead} {out : PiCod} (args : List Sem) (o : BodyOut) (h : out.isRef = false)
    (ψ : Future) : HeldTyped R (o.held out args) ψ := by
  rw [BodyOut.held_data args o h]; exact heldTyped_nil R ψ

/-- The future that leaves a member `v` of the codomain in the returned borrow is typed for the result: what the
closure's construction reads the finals at (`ClosureRef.refLeafFrom_start`). -/
theorem heldTyped_upd {R : DataRead} {out : PiCod} {args : List Sem} {o : BodyOut} {k : Nat} (φ : Future) {v : Sem}
    (href : out.isRef = true) (hk : o.retLabel = some k) (hv : v ∈ₛ[R] out.cod args) :
    HeldTyped R (o.held out args) (φ.upd k v) := by
  intro l T hm
  simp only [BodyOut.held, href, if_true, hk, Option.map_some, Option.toList_some, List.mem_singleton,
    Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  rw [Future.upd_same]; exact hv

/-- A producer that shows the finals good at every future shows `OutGood`. -/
theorem OutGood.of_every {R : DataRead} {ds : List PiDom} {out : PiCod} {args : List Sem} {o : BodyOut}
    (hres : o.result ∈ₛ[R] out.cod args)
    (hfin : ∀ (i : Nat) (d : PiDom), ds[i]? = some d → d.isRef = true →
      ∃ f, o.finals[((ds.take i).filter (·.isRef)).length]? = some f ∧ ∀ ψ, f ψ ∈ₛ[R] d.dom (args.take i)) :
    OutGood R ds out args o :=
  ⟨hres, fun i d hi hd => (hfin i d hi hd).imp fun _ h => ⟨h.1, fun ψ _ => h.2 ψ⟩⟩

/-- The rank of a call's decreasing argument (the global's `fix` names it; `0` for a function that
does not recurse): `semRank`, the height of the meaning after the data-layer port (D73's R1–R3). -/
noncomputable def decRank (K : RunCtx) (g : GDef) (args : List Sem) : Nat :=
  match g.fn? with
  | some (.fix _ _ _ _ (some j) _) => ((args[j]?).map fun a => semRank a).getD 0
  | _ => 0

/-- **A body's output is good** at arguments (docs/34, the weakened stage closure): `OutGood`, a
returned borrow's label and injective backward function (`RetGood`: what an element of the carrier
of a borrow-returning function type holds, `mkLeafRefL`), and one final content per borrow
parameter (what the strict construction decodes; the run's frame pop gives one per borrow cell). -/
def OutGood' (R : DataRead) (ds : List PiDom) (out : PiCod) (args : List Sem) (o : BodyOut) : Prop :=
  OutGood R ds out args o ∧ (out.isRef = true → RetGood R out args o) ∧
    o.finals.length = (ds.filter (·.isRef)).length

/-- **What membership consumes of a function type**, at the argument tuples `P` admits: at sort `0`
a borrow-free codomain that is a proposition; at a data sort `1 ≤ l ≤ 3`, a codomain that fits the
level (`LevelFit`). -/
def PiFits (R : DataRead) : Nat → List PiDom → PiCod → (List Sem → Prop) → Prop
  | 0, ds, out, P => out.isRef = false ∧ ∀ args, DomMembers R ds args → P args → ∃ Q, out.cod args = TyM.prop Q
  | n + 1, ds, out, P => n + 1 ≤ 3 ∧ ∀ args, DomMembers R ds args → P args → LevelFit (n + 1) (out.cod args)

/-- **What a call consumes of a function type** beyond membership, at the argument tuples `P`
admits: a canonical codomain, and domains that fit the level. -/
def PiCallable (R : DataRead) (l : Nat) (ds : List PiDom) (out : PiCod) (P : List Sem → Prop) : Prop :=
  ∀ args, DomMembers R ds args → P args →
    (out.cod args).Canon ∧ ∀ (i : Nat) (d : PiDom), ds[i]? = some d → LevelFit l (d.dom (args.take i))

/-- **Membership below a bound** (docs/31 D73, D80; docs/34, the weakened stage closure): the
global is the stage closure (`closureAt` of `stageFn`) of a function good (`OutGood'`) at member
arguments whose decreasing component has rank below `b`, typed at the WEAKENED function type
(`weakCod`: the true codomain below `b`, `Unit`/`True` above), an honest element
(`FixKnot.memBelow_mem`); below the bound, the function type meets what membership and (at a data
sort) a call consume. What `CtxOk` asks of the definition being checked (`RunCtx.cur`): in the
induction's step the global is the run's own `self` at stage `b + 1` (`RunCongr.fixStage`, with
`fn` the stage `b`). A call reads it through `FixKnot.memBelow_apply`. -/
def MemBelow (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) : Prop :=
  ∃ (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod) (fn : List Sem → Option BodyOut),
    PiFits K.dm.read l ds out (decRank K g · < b) ∧
    (1 ≤ l → PiCallable K.dm.read l ds out (decRank K g · < b)) ∧
    G.1 = closureAt K.dm.read l φ ds (weakCod l (decRank K g) b out) (stageFn l ds (decRank K g) b fn) ∧
    G.2.m = piTyAt K.dm.read l ds (weakCod l (decRank K g) b out) ∧
    ∀ args, DomMembers K.dm.read ds args → decRank K g args < b →
      ∃ o, fn args = some o ∧ OutGood' K.dm.read ds out args o

/-! ## The globals' own clauses, which `GlobalsOk` carries (moved here by lead43, docs/31 D253)

The step for a call of a global consumed three clauses about the callee, the fixpoint equation (`FixEqG`), its meaning
being its own closure (`AcceptedMeanG`) and the label kind of its result (`RetKindG`), and they were asked at EVERY
checker state (`∀ st, FixEqG K st`, `∀ st, AcceptedGlobalG K st`), which is false at every context: a state may hold
any code under a global's name (`Regress/EveryStateCE.lean`'s two counterexamples, one line each in D253). Ruled
(2026-11-28): they are clauses of `GlobalsOk`, asked of the state's own globals but the one under check (`K.cur`),
and read only `st.globals` and `K`, so every run keeps them as it keeps the rest (`GlobalsOk.of_globals`). They were
defined in `FrameRec`, `MasterCall`, `CallStep`, downstream of `GlobalsOk`; the definitions are moved here unchanged. -/

mutual
/-- **The term holds no embedded value** (no `.val` node; a resolved program's code is such: the resolver builds none).
Mirrors `Term.valsOk`, so a value-free term meets `valsOk` at every predicate (`CallStep.valsOk_of_valFree`). -/
def _root_.Ochr.Term.valFree : Term → Bool
  | .val _ => false
  | .assign _ t | .succ t | .ref t => t.valFree
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.valFree && u.valFree
  | .matchNat _ z s => z.valFree && s.valFree
  | .pi _ ds c => Term.valFreeList ds && c.valFree
  | .fix _ _ ds c _ b => Term.valFreeList ds && c.valFree && b.valFree
  | .call f as _ => f.valFree && Term.valFreeList as
  | .eq a b c | .id a b c => a.valFree && b.valFree && c.valFree
  | .prim _ as | .tind _ as => Term.valFreeList as
  | .ctor _ _ _ ps as => Term.valFreeList ps && Term.valFreeList as
  | .matchInd _ _ arms => Term.valFreeArms arms
  | _ => true
termination_by structural t => t

def _root_.Ochr.Term.valFreeList : List Term → Bool
  | [] => true
  | t :: ts => t.valFree && Term.valFreeList ts
termination_by structural ts => ts

def _root_.Ochr.Term.valFreeArms : List (Hint × Term) → Bool
  | [] => true
  | (_, t) :: ts => t.valFree && Term.valFreeArms ts
termination_by structural ts => ts
end

namespace Form

section GlobalFix

/-- A global's forming state: `meanV` reads `.clo [] t []` by the `.fix` clause from it (`GlobalsOk.fn`). -/
def formG : SState := stateOf 0 []

/-- The closure's binders, body hint and codomain reading at a global's code (`run_fix_def`'s `fb`, at `formG`). -/
noncomputable def fbG (ds : List Term) (c : Term) : List PBind × (List Sem → TyS) × DeclInfo :=
  (bindsOf K ρ φ formG ds, fixCod K ρ φ formG (bindsOf K ρ φ formG ds) (ds.map Term.isRefTy) c,
    K.D.typeDecl (K.D.teleDecls (scopeOf formG) ds) c)

/-- Its domains and codomain. -/
noncomputable def psG (ds : List Term) : List PiDom := runDoms K ρ φ formG ds
noncomputable def outG (ds : List Term) (c : Term) : PiCod :=
  codOf K ρ φ formG (bindsOf K ρ φ formG ds) (ds.map Term.isRefTy) c

/-- The declared sort, the function type, the closure's function (`fixG`, from the counter `0`) and the global's meaning
(its closure), all at `formG`. -/
noncomputable def lG (hs : List Hint) (ds : List Term) (c : Term) : Nat := K.D.piSort (scopeOf formG) (.pi hs ds c)
noncomputable def piTG (hs : List Hint) (ds : List Term) (c : Term) : TyM :=
  piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) (outG K ρ φ ds c)
noncomputable def GG (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : List Sem → Option BodyOut :=
  fixG K ρ φ (fbG K ρ φ ds c) (lG K hs ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) (piTG K ρ φ hs ds c) 0 dec body
noncomputable def selfG (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : Sem :=
  closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) (outG K ρ φ ds c) (GG K ρ φ hs ds c dec body)

end GlobalFix

/-- **The fixpoint equation of an accepted global** (MODEL; docs/31 D202, restated by D232). For every global `n` of the
checker's state other than the one being checked, with a `fix` code, at every assignment and future, at member arguments:
the global's function (`GG`, the `.fix` clause's `fixG` at the global's forming state `formG`: stage `rank + 1`) equals one
run of the body with `self` the global's own closure at its true function type. Stated at `formG` only (D232: a global is
formed there and nowhere else; at another state the body's variables are not its own, and the right side's closure is `err`
wherever the function is not good everywhere). Since D232 a THEOREM, not an assumed clause: `FixEqDesc.fixEqG_of`, from
the descent clause `RecDescG` and the knot's goodness `FnGoodG`. -/
def FixEqG (K : RunCtx) (st : MState) : Prop :=
  ∀ (n : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    st.globals.find? (·.name == n) = some gd → K.cur.map (·.1) ≠ some n →
    gd.fn? = some (.fix self hs ds c dec body) →
    ∀ (ρ : Assignment) (φ : Future) (args : List Sem), DomMembers K.dm.read (psG K ρ φ ds) args →
      GG K ρ φ hs ds c dec body args =
        fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) (piTG K ρ φ hs ds c) 0 body
          (selfG K ρ φ hs ds c dec body) args

namespace Master

/-- **(R3) A callee's result is labelled exactly where its codomain is written `&`** (MODEL; a clause of the context,
to be established when each definition is accepted, through the relation, from its typed check at unknown parameters:
the checker's leaf value is a borrow exactly when the reference's result is labelled (`Out`'s label clause, both
directions), a borrow only at a type `&A` (`OutL`'s kind clause, R3), the leaf type converts to the goal, and the goal
is `&` exactly when the codomain is written `&` (`refTopOk`)). For every earlier global with a `fix`, at every
assignment, future and forming state, the closure's function (`fixG`, what `run_fix_def` forms and `GlobalsOk.fn`
names) at member arguments returns a body output whose result label is present exactly when the codomain is a borrow
type (`codOf`'s `isRef`: the codomain term is `&U`). Both directions are consumed: at a data codomain `callOf`'s result
carries no label, so the checker's in-place value must not be a borrow (machine12's `gb (r : &Nat) : Nat := r`, which the
checker never accepted and the context admitted); at a borrow codomain `callOf`'s result always carries a fresh label,
and `callFn` relabels the body's value into it only if it is a borrow. -/
def RetKindG (K : RunCtx) (st : MState) : Prop :=
  ∀ (n : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    st.globals.find? (·.name == n) = some gd → K.cur.map (·.1) ≠ some n →
    gd.fn? = some (.fix self hs ds c dec body) →
    ∀ (ρ : Assignment) (φ : Future) (s : SState) (piT : TyM) (args : List Sem) (o : BodyOut),
      DomMembers K.dm.read (runDoms K ρ φ s ds) args →
      fixG K ρ φ (bindsOf K ρ φ s ds, fixCod K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c, K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c)
        (K.D.piSort (scopeOf s) (.pi hs ds c)) s (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c) piT
        s.nextLoan dec body args = some o →
      o.retLabel.isSome = (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c).isRef

/-- **An accepted global means its own closure at its forming state** (MODEL; a clause of `GlobalsOk`, docs/31 D253):
`CallStep.AcceptedGlobalG` but its last conjunct (the body's embedded values good), which follows from the code holding
none (`GlobalsOk.codeValFree`, `CallStep.acceptedGlobalG_of`). Asked of every global with a `fix` code but the one under
check. -/
def AcceptedMeanG (K : RunCtx) (st : MState) : Prop :=
  ∀ (g : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    st.globals.find? (·.name == g) = some gd → K.cur.map (·.1) ≠ some g → gd.fn? = some (.fix self hs ds c dec body) →
    ∀ (Δ : Nat → TyS) (ρ : Assignment) (φ : Future),
      (K.C.global g).1 = selfG { K with Δ := Δ } ρ φ hs ds c dec body ∧
      (K.C.global g).2.m = piTG { K with Δ := Δ } ρ φ hs ds c ∧
      (K.C.global g).1 ∈ₛ[K.dm.read] (K.C.global g).2.m

end Master

end Form

/-- `K.C.global` is Σ: each global of the state has its stored type, a constant means its stored
value read at that type (`⋆` at a proposition, as `evalCore`'s `.const` reads it), a function means
the closure of its `fix` term formed in the empty frame, whose run gives the stored type's code,
and each is a member of its type. The last is the outer induction of docs/18's theorem: while a definition is checked,
every global is an earlier, accepted one. A global is closed, so these hold at every assignment
and future. The definition being checked (`K.cur`, pushed by `checkDef` before its body is checked
so that recursive calls find it) is asked only membership below the bound (`memBelow`), at the
weakened function type and as the stage closure, so neither its stored type (`ty`) nor its closure
(`fn`) is asked of it: as first stated every global was asked membership, which for that one is
`checkFix_sound`'s conclusion, so the statement was vacuous at a definition (the knot, docs/31 D72,
D73, `Regress/DefKnot`); and a function good only below the bound is an element of the weakened
type, not of its stored one (docs/34). -/
structure GlobalsOk (K : RunCtx) (st : MState) : Prop where
  ty : ∀ n g, st.globals.find? (·.name == n) = some g → (K.cur.map (·.1)) ≠ some n → ∀ ρ,
    (K.C.global n).2.m = (meanV K ρ noFuture (.plain .err) g.ty).asTy
  const : ∀ n g, st.globals.find? (·.name == n) = some g → g.fn? = none → ∀ ρ φ,
    (K.C.global n).1 = constMean (K.C.global n).2.m (meanV K ρ φ (K.C.global n).2 g.val)
  fn : ∀ n g t, st.globals.find? (·.name == n) = some g → g.fn? = some t → (K.cur.map (·.1)) ≠ some n → ∀ ρ φ,
    (K.C.global n).1 = meanV K ρ φ (.plain .err) (.clo [] t []) ∧
    ∀ r s', run K ρ φ (.plain .err) t (stateOf 0 []) = some (r, s') → r.2.m = (K.C.global n).2.m
  /-- every global but the definition being checked is a member of its type -/
  mem : ∀ n g, st.globals.find? (·.name == n) = some g → (K.cur.map (·.1)) ≠ some n →
    (K.C.global n).1 ∈ₛ[K.dm.read] (K.C.global n).2.m
  /-- the definition being checked (docs/31 D73): only membership below the bound -/
  memBelow : ∀ n g b, st.globals.find? (·.name == n) = some g → K.cur = some (n, b) → MemBelow K (K.C.global n) g b
  /-- every global with a `fix` code but the one under check satisfies its fixpoint equation (docs/31 D253) -/
  fixEq : Form.FixEqG K st
  /-- every global with a `fix` code but the one under check means its own closure, a member (docs/31 D253) -/
  accepted : Form.Master.AcceptedMeanG K st
  /-- every global with a `fix` code but the one under check returns a labelled result exactly at a borrow codomain
  (R3; docs/31 D253) -/
  retKind : Form.Master.RetKindG K st
  /-- every global's code holds no embedded value (docs/31 D253; the resolver builds none) -/
  codeValFree : ∀ n g t, st.globals.find? (·.name == n) = some g → g.fn? = some t → t.valFree = true

/-- `GlobalsOk` reads the globals only. -/
theorem GlobalsOk.of_globals {K : RunCtx} {st st' : MState} (h : GlobalsOk K st) (hg : st'.globals = st.globals) :
    GlobalsOk K st' :=
  ⟨fun n g hf => h.ty n g (hg ▸ hf), fun n g hf => h.const n g (hg ▸ hf), fun n g t hf => h.fn n g t (hg ▸ hf),
    fun n g hf => h.mem n g (hg ▸ hf), fun n g b hf => h.memBelow n g b (hg ▸ hf),
    fun n gd self hs ds c dec body hf => h.fixEq n gd self hs ds c dec body (hg ▸ hf),
    fun g gd self hs ds c dec body hf => h.accepted g gd self hs ds c dec body (hg ▸ hf),
    fun n gd self hs ds c dec body hf => h.retKind n gd self hs ds c dec body (hg ▸ hf),
    fun n g t hf => h.codeValFree n g t (hg ▸ hf)⟩

/-- The run context knows the types of the unknowns the state names: `K.Δ` is `deltaOf` at every
referenced unknown (`MState.Refd`). Elsewhere `K.Δ` is free, so a step that names new unknowns
extends it (as it extends the assignment) and leaves what the earlier ones read unchanged.

Until 2026-11-21 it was asked at every typed unknown (`σ < absTy.size`). But the checker keeps
unknowns nothing names: an end of a borrow of a dependent type checks its content against the type
again (`endBorrow`'s `repackCheck`, D64), which opens an unknown for a lent part and keeps its type
(394 of the ends the end probe ran from the suite's recorded states, in 21 declarations; none
named after the end, none adding a record: docs/31 D35). At a fixed context `K`, `K.Δ` at that
unknown is whatever it was, so after any access that ends such a borrow the old clause asked `K`
for what it cannot know, and `access_ctx` (the context is kept by an access) was false. The
reference reads `Δ` only at the unknowns of the terms and values it runs, which are referenced,
so the clause asks what the run reads, as `TypedAssignment.mem` and `Membership.absTy` do. -/
def DeltaOk (K : RunCtx) (ρ : Assignment) (st : MState) : Prop :=
  ∀ σ, st.Refd σ → σ < st.absTy.size → K.Δ σ = deltaOf K ρ st σ

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

/-- The checker's position of de Bruijn variable `i` (`Machine.varPos`, as a function). -/
def ckVarPos (env : Env) (i : Nat) : Option Pos :=
  if i < env[env.size - 1]!.binds.size then some (.bind (env.size - 1) (env[env.size - 1]!.binds.size - 1 - i))
  else none

/-- The checker's content of a place, as a function (`Machine.content`: the variable's position,
then the path). -/
def ckContent (env : Env) (p : Place) : Option Value :=
  (ckVarPos env p.steps.1).bind fun pos => (valAt env pos).follow p.steps.2

/-- The checker's entry set of a match (`Machine.staticJoin`): every place under a variable of the
top frame whose content is `⊥`, at the grain of the value (`botPlaces`). -/
def entryOf (st : MState) : List Place :=
  match st.env.back? with
  | some fr => (List.range fr.binds.size).flatMap fun o =>
      botPlaces (fr.binds[fr.binds.size - 1 - o]!).val (.var o)
  | none => []

/-- `Machine.blockEntry`'s captures before their accesses, what `Decisions.blockCaps` reads: the
places `blockCaptures`' K1(a) asks `movedPlace` of (before re-rooting, in order: a copy of its
first lines) and its captures in `blockEntry`'s order. -/
def ckBlockCaps (fuel : Nat) (mt : Term) : M (List Place × List (Place × Nat)) := do
  let (_, net) ← Ochr.staticJoin fuel mt
  let mut mv := net
  for (o, p) in mt.fnOccs 0 do
    let q := p.mapRoot fun _ => .var o
    unless ← Ochr.copyRead fuel q do
      unless mv.any (placeEq · q) do mv := mv ++ [q]
  let (caps, _, _) ← Ochr.blockCaptures fuel mt net
  let capsS := blockCapOrder caps
  pure (mv, capsS.toList)

/-- Two checker states the same up to what no decision reads (the move log and the [Split]
refinements: `DecideScope.EnvRel` ignores both, and its simulation of every decision is proved). -/
def SameDec (st st' : MState) : Prop :=
  { st with placeLog := #[], refs := [] } = { st' with placeLog := #[], refs := [] }

/-- **The context's decisions are the checker's at this state** (team lead's decision,
2026-11-21: assumed and concluded by every step, never a separate hypothesis). Wherever the
checker's own decision procedure, called as the machine calls it, answers at the state's tables in
a scope of readings `sc` (`scopeState st sc`; at the top frame's readings this is the call at `st`
itself, `DecideScope.envRel_scopeState`), the decision `D` in that scope gives the same answer.
Copy-ness reads no frame. D90's [Entry] captures (`blockCaps`) are read from values by the
checker (`Machine.blockCaptures`): they are asked at the top frame only, at the places then moved
(`entryOf`), and of every state the same up to what no decision reads (`SameDec`); that the static
instance gives them is D90's obligation 1 (`BlockCaps.lean`'s docstring lists the value reads). -/
structure DecTab (D : Decisions) (st : MState) : Prop where
  flags : ∀ fuel sc t fl b st', Runs (do
      let d ← withLive true (Ochr.declOf fuel false [] [] t)
      pure ((← Ochr.preFlags t d).getD (false, false))) (scopeState st sc) b fl st' → D.flags sc t = fl
  placeDecl : ∀ fuel sc p d b st', Runs (withLive true (Ochr.placeDecl fuel [] p)) (scopeState st sc) b d st' →
    D.placeDecl sc p = d
  declOf : ∀ fuel sc t d b st', Runs (withLive true (Ochr.declOf fuel false [] [] t)) (scopeState st sc) b d st' →
    D.declOf sc t = d
  copy : ∀ fuel r c b st', Runs (Ochr.declCopy fuel r) st b c st' → D.copy r = c
  piSort : ∀ fuel sc t l b st', Runs (withLive true (Ochr.sortOf fuel (.tPi [] t []))) (scopeState st sc) b l st' →
    D.piSort sc t = l
  joinMoves : ∀ fuel sc entry t ms b st', Runs (withLive true (Ochr.jdMoves fuel [] [] t entry)) (scopeState st sc) b ms st' →
    D.joinMoves sc entry t = ms
  rePointed : ∀ fuel sc t ts b st', Runs (withLive true (Ochr.typeState fuel t)) (scopeState st sc) b ts st' →
    D.rePointed sc t = ts.repointed
  typeDecl : ∀ fuel sc T d b st', Runs (withLive true (Ochr.typeDecl fuel false [] [] T)) (scopeState st sc) b d st' →
    D.typeDecl sc T = d

/-- `DecTab` and the block's captures, which read values: the decisions are the checker's at `st`.
Split (the slice, 2026-11-20, main's fixed decision table): `DecTab` reads only the tables, so it
transfers from a later state of a run to an earlier one (`MachineMono.DecTab.back`); the block's
captures are the checker's at each state (D90's obligation 1 there). -/
structure DecAligned (D : Decisions) (st : MState) extends DecTab D st : Prop where
  blockCaps : ∀ st₀, SameDec st₀ st → ∀ fuel mt bc b st', Runs (ckBlockCaps fuel mt) st₀ b bc st' →
    D.blockCaps (DecideScope.topReadings st) (entryOf st) mt = bc

/-- What may sit at a place declared an inductive `n`: `⊥`, `⋆`, an unknown, a sealed program, a
loan, a constructor value of `n`, or a mark over any of these (the mark sits over the place's own
content, docs/31 D44; first stated over anything). -/
def _root_.Ochr.Value.fitsInd (n : String) : Value → Bool
  | .bot | .proof | .abs _ | .sealed _ | .loan _ => true
  | .gloan _ w => w.fitsInd n
  | .ind ty _ _ _ _ => ty == n
  | _ => false

/-- A constructor value of a `Prop`-sorted declaration, of none, or of one named `Nat` (an atom
test, docs/31 D47). -/
def dataCtorBad (Γ : List IndDecl) : Value → Bool
  | .ind n _ _ _ _ => match Γ.find? (·.name == n) with
    | some d => d.sort == 0 || d.name == "Nat"
    | none => true
  | _ => false

/-- What the step `x` from a place of declared reading `r` needs of it, at the join's grain: a field
step (`.proj i`, `.field g`) is through an inductive of `Γ` with exactly one constructor; a `*` step
is through a place declared a borrow (`Decide.jdGrain`). (Restated at main's D94: the index a field
step names and the borrow type a `*` step goes through were asked too, for `movedPlace`'s exits,
which D94 replaced by a rejection, docs/31 D51. The borrow type is asked again since the slice,
2026-11-20, with the checker's D101 (`jdGrain` rejects a move through `*` of a place not declared a
borrow): an arm the run does not take is never checked, so `*h` of a proof `h` reached the join, where the checker re-roots to the
`⋆` and does nothing; the reference wrote `moved` through the `*` (`Regress/GrainDerefProof.lean`),
or, under a mark of a live returned borrow above the `⋆`, its lent-prefix access ended a borrow the
checker kept. With the `*` step's borrow type at the grain no non-copy place of the join is at or
below a `⋆` (`JoinNoop.not_below_proof`), which is what the reference's drop assumes.) -/
def StepOk (Γ : List IndDecl) (r : DeclInfo) : Step → Prop
  | .proj _ | .field _ => ∃ n args d, r = .ind n args ∧ Γ.find? (·.name == n) = some d ∧ d.ctors.length = 1
  | .deref => ∃ d, r = .ref d

/-- **The join's grain** (main's D84, `Decide.jdGrain`): every field step of a dropped place, from its
prefix, is through a place whose declared reading is an inductive of `Γ` with exactly one
constructor, and every `*` step through a place declared a borrow (`StepOk`). Through anything else (several constructors, a type computed by a match, a
type parameter, a number's predecessor) the join moves the value whole. It is what the drop's
reading of the place needs (`PlaceTyping.followMean`, `natAlong_grain`: no number's predecessor on
the path, and the constructor value there is of the declared type), which `Decisions.joinMoves`,
aligned with `Decide.jdMoves`, provides. -/
def GrainOk (D : Decisions) (Γ : List IndDecl) (sc : List DeclInfo) (q : Place) : Prop :=
  ∀ (p : Place) (x : Step) (rest : List Step), p.steps.1 = q.steps.1 → q.steps.2 = p.steps.2 ++ x :: rest →
    StepOk Γ (D.placeDecl sc p) x

/-- (Rd), a clause of `ShapeFacts` (the lead's decision, docs/31 D78): an unknown whose frozen reading is `Sort l` (D96) has the type `Sort l`.
`freshAbsR` freezes `valTypeDecl` of the type it pushes, which is `.sort l` exactly at `Sort l`;
nothing else writes a reading, and a type `Sort l` holds no unknown, so no substitution changes it.
Swept on the suite's recorded states (docs/31 D77): 40,214 unknowns read as a sort over 76,568
states, every one of type `Sort l`. -/
def ReadingsSorted (st : MState) : Prop :=
  ∀ (σ l : Nat), st.absDecl[σ]? = some (DeclInfo.sort l) → st.absTy[σ]? = some (Value.sort l)

/-- **The checker's typing of places** (docs/31 D34, D40, D47, D49, D51): at every place in scope
that exists, by its declared reading (`Decisions.placeDecl` at the top frame's readings), a place
declared an inductive of the declarations holds a constructor value of it or a stand-in (V); every
loan and mark anywhere in Ω is of a live borrow (L); every constructor value is of a data
declaration, not named `Nat` (N); a place below a variable holding `⋆` is declared a copy type
(C⋆); every η record is top-hint-free (Hη). What the drop's reading of a place and its write
need. Syntactic typing, which `Good`'s membership does not give. Read off the checker and swept;
NOT proved preserved: every step's `CtxOk` conclusion owes it. (U), (R), (P), (A) and (M), which
`movedPlace`'s exits needed, went with main's D94, which made those exits a rejection. (Ty), a
variable holding a type value is declared a sort, went with D59: the write of `⊥` over a type
value needed it only because the binding's structure was read off the value it held
(`Value.strS`); a type value now carries its own code. -/
structure ShapeFacts (D : Decisions) (Γ : List IndDecl) (st : MState) : Prop where
  /-- (V) a place declared an inductive of `Γ` holds a constructor value of it or a stand-in -/
  fits : ∀ p v n args, ckContent st.env p = some v → D.placeDecl (DecideScope.topReadings st) p = .ind n args →
    (Γ.find? (·.name == n)).isSome → v.fitsInd n = true
  /-- (L) every loan and mark in Ω is of a live borrow -/
  loans : ∀ v ∈ Env.values st.env, ∀ l ∈ v.loans, liveLoan st.env l = true
  /-- (N) every constructor value is of a data declaration of `Γ` (a `Prop`-sorted one's values are
  `⋆`, `Machine.evalCtor`, D42), not named `Nat` (numbers are `zero`/`succ`) -/
  ctors : ∀ v ∈ Env.values st.env, v.anyAtom (dataCtorBad Γ) = false
  /-- (C⋆) a place at the join's grain holding `⋆` is declared a copy type, at a variable as below
  one: the join, which moves no copy, never drops a `⋆`, so the reference's drop needs no test of
  the meaning at the place (the slice, 2026-11-20). True since main's D100 (every proposition, a Π
  into proofs included, is a copy); before it a variable declared a Π into proofs held `⋆` and was no
  copy (6,447 suite states, docs/31 D49 for the earlier borrow of a proposition). First stated for
  EVERY place below a variable, which is false: a data field of a proof, `p.w` for `p : ExW(n)`
  (`Wit(w : Word, …) : Prop`), exists in the checker (a step from `⋆` reaches `⋆`) and is read
  `other` (a field of a place read `prop`), no copy; it is off the grain (a field step needs a place
  read as a one-constructor inductive) and the sweep, which walks no place under a `⋆`, never saw
  it. -/
  proofCopy : ∀ p, GrainOk D Γ (DecideScope.topReadings st) p → ckContent st.env p = some .proof →
    D.copy (D.placeDecl (DecideScope.topReadings st) p) = true
  /-- (Hη) every η record is top-hint-free (a constructor value of fresh unknowns recording its
  parameters, `ctorRefinement`), so it means its unknown at every hint (docs/31 D55) -/
  etaHint : ∀ σ r, (σ, r) ∈ st.etaRefs → r.topHintFree Γ = true
  /-- (Hη≠) no η record names its own unknown (`ctorRefinement` makes the fields fresh, after the
  unknown; the parameters it records are the unknown's type's): what `refine_step`'s `RefineOk` asks
  of a recorded refinement (the slice, main's decision 2026-11-20). Swept: no violation in 11,805
  suite states and 167 probe states holding an η record. The stronger "names only unknowns made
  after its unknown" is false: the recorded parameters name the type's older unknowns (9,636 suite
  states, the smallest `HashMapResize.NOf`, `σ1 := HM[σ0](σ2, σ3, σ4)` for `m : HashMap(V)`, `V ↦ σ0`);
  the fields are always newer. -/
  etaNoSelf : ∀ σ r, (σ, r) ∈ st.etaRefs → r.hasAbs σ = false
  /-- (Rd) an unknown read as `Sort l` has the type `Sort l` (docs/31 D77, D78): with `Good` and
  `CtxOk`, what makes the checker's `sortOf` sound (`sortOf_sound_stmt`) -/
  readingsSorted : ReadingsSorted st

/-- A term's unknowns are below `n`. -/
def _root_.Ochr.Term.absBelow (n : Nat) (t : Term) : Prop := ∀ σ, t.anyAtom (· == .abs σ) = true → σ < n

theorem _root_.Ochr.Term.absBelow_mono {n m : Nat} {t : Term} (h : t.absBelow n) (hnm : n ≤ m) : t.absBelow m :=
  fun σ hσ => Nat.lt_of_lt_of_le (h σ hσ) hnm

/-- The run context is the checker state's: its declarations, a data model that speaks for each
and reads their declared types as the run does (`CtxFaithful`, docs/34 §9), Δ at the state's
unknowns (`DeltaOk`), globals with no label (`run_congr`'s `hK`), Σ (`GlobalsOk`), its decisions
the checker's (`DecAligned`), and the checker's typing of places (`ShapeFacts`). A hypothesis of
every statement. -/
structure CtxOk (K : RunCtx) (ρ : Assignment) (st : MState) : Prop where
  /-- the checker's declarations are a prefix of the context's one list (docs/31 D174) -/
  inds : st.inds <+: K.Γ
  covers : ∀ d ∈ K.Γ, K.dm.covers d
  /-- faithfulness at the checker's declarations only (docs/31 D174) -/
  faithful : DeclsFaithful K st.inds
  delta : DeltaOk K ρ st
  noLabel : ∀ n, (K.C.global n).2.label = none
  globals : GlobalsOk K st
  dec : DecAligned K.D st
  shapes : ShapeFacts K.D K.Γ st

/-- A run of a decision transfers between states that agree on what decisions read. -/
theorem runs_envRel {α : Type} {x : M α} (hx : DecideScope.Sim DecideScope.EnvRel x) {s₁ s₂ : MState}
    (h : DecideScope.EnvRel s₁ s₂) {b : Nat} {a : α} {s₁' : MState} (hr : Runs x s₁ b a s₁') :
    ∃ s₂', Runs x s₂ b a s₂' := by
  obtain ⟨L, left, log, hr⟩ := hr
  have hs := hx s₁ s₂ ⟨b⟩ L h
  unfold DecideScope.runAll at hs
  have key : ∀ s, runMachineL x s b L = (match x s ⟨b⟩ L with
      | ((r, fl), log) => ((match r with
        | .error e => Outcome.exhausted e.msg
        | .ok (.error f) => .fail f
        | .ok (.ok (a, st')) => .ok a st'), fl.left, log)) := fun s => rfl
  rw [key] at hr
  have hgoal : ∀ s₂', (∃ left log, runMachineL x s₂ b L = (.ok a s₂', left, log)) → Runs x s₂ b a s₂' :=
    fun s₂' ⟨left, log, e⟩ => ⟨L, left, log, e⟩
  simp only [key] at hgoal
  revert hr hs hgoal
  generalize x s₁ ⟨b⟩ L = o₁
  generalize x s₂ ⟨b⟩ L = o₂
  intro hr hs hgoal
  rcases o₁ with ⟨⟨e₁ | e₁ | ⟨a₁, t₁⟩, f₁⟩, l₁⟩
  · simp at hr
  · simp at hr
  rcases o₂ with ⟨⟨e₂ | e₂ | ⟨a₂, t₂⟩, f₂⟩, l₂⟩
  · exact hs.elim
  · exact hs.elim
  obtain ⟨rfl, -, rfl, rfl⟩ := hs
  simp only [Prod.mk.injEq, Outcome.ok.injEq] at hr
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hr
  exact ⟨t₂, hgoal t₂ ⟨_, _, rfl⟩⟩

/-- **Two states with the same decision core** (`DecideScope.EnvRel` but for the frames: Σ, the
unknowns' frozen readings (main's D96: no decision reads their types), the reading mode; docs/31
D53, D65): what the decisions read besides the top frame's readings. -/
structure DecCore (st st' : MState) : Prop where
  globals : st.globals = st'.globals
  inds : st.inds = st'.inds
  absDecl : st.absDecl = st'.absDecl
  liveScope : st.liveScope = st'.liveScope

theorem DecCore.of_sameDec {st st' : MState} (h : SameDec st st') : DecCore st st' := by
  have e := congrArg (fun s : MState => (s.globals, s.inds, s.absDecl, s.liveScope)) h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1, e.2.1, e.2.2.1, e.2.2.2⟩

theorem envRel_scope_of_core {st st' : MState} (h : DecCore st st') (sc : List DeclInfo) :
    DecideScope.EnvRel (scopeState st sc) (scopeState st' sc) :=
  ⟨h.globals, h.inds, h.absDecl, h.liveScope, fun i => by
    rw [DecideScope.liveVal_scopeState, DecideScope.liveVal_scopeState]⟩

theorem envRel_of_core {st st' : MState} (h : DecCore st st') (hl : ∀ i, DecideScope.liveVal st i = DecideScope.liveVal st' i) :
    DecideScope.EnvRel st st' :=
  ⟨h.globals, h.inds, h.absDecl, h.liveScope, hl⟩

theorem sameDec_envRel_scope {st st' : MState} (h : SameDec st st') (sc : List DeclInfo) :
    DecideScope.EnvRel (scopeState st sc) (scopeState st' sc) :=
  envRel_scope_of_core (DecCore.of_sameDec h) sc

theorem sameDec_envRel {st st' : MState} (h : SameDec st st') (he : st.env = st'.env) :
    DecideScope.EnvRel st st' :=
  envRel_of_core (DecCore.of_sameDec h) fun i => by simp [DecideScope.liveVal, he]

/-- D84's join set reads only what the other decisions read (PROVED, docs/31 D53:
`DecideScope.jdSim`, the same induction as `decideSim`, over `jdMoves`' mutual block). -/
theorem jdMoves_sim (fuel : Nat) (t : Term) (entry : List Place) :
    DecideScope.Sim DecideScope.EnvRel (withLive true (Ochr.jdMoves fuel [] [] t entry)) :=
  DecideScope.sim_withLive _ ((DecideScope.jdSim fuel).1 _ _ _ _)

/-- [Id-typestate]'s re-pointed set likewise (PROVED, `DecideScope.sim_typeState`). -/
theorem typeState_sim (fuel : Nat) (t : Term) :
    DecideScope.Sim DecideScope.EnvRel (withLive true (Ochr.typeState fuel t)) :=
  DecideScope.sim_withLive _ (DecideScope.sim_typeState fuel t)

theorem SameDec.symm {st st' : MState} (h : SameDec st st') : SameDec st' st := Eq.symm h
theorem SameDec.trans {a b c : MState} (h₁ : SameDec a b) (h₂ : SameDec b c) : SameDec a c := Eq.trans h₁ h₂

/-- **The typing of places stays across a change of what no decision reads**, the environment and
the unknowns' types kept. -/
theorem ShapeFacts.of_sameDec {D : Decisions} {Γ : List IndDecl} {st st' : MState} (hf : ShapeFacts D Γ st)
    (h : SameDec st' st) (he : st'.env = st.env) (ha : st'.absTy = st.absTy) (hη : st'.etaRefs = st.etaRefs) :
    ShapeFacts D Γ st' := by
  have e1 : DecideScope.topReadings st' = DecideScope.topReadings st := by
    unfold DecideScope.topReadings; rw [he]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p v n args hp hd hn; rw [he] at hp; rw [e1] at hd; exact hf.fits p v n args hp hd hn
  · rw [he]; exact hf.loans
  · rw [he]; exact hf.ctors
  · intro p hgr hp; rw [he] at hp; rw [e1] at hgr ⊢; exact hf.proofCopy p hgr hp
  · rw [hη]; exact hf.etaHint
  · rw [hη]; exact hf.etaNoSelf
  · have hd : st'.absDecl = st.absDecl := by
      have := congrArg MState.absDecl h
      simpa using this
    intro σ l h1
    rw [hd] at h1; rw [ha]
    exact hf.readingsSorted σ l h1

/-- **The decisions stay the checker's across what no decision reads** (docs/31 D53): from a state
with the same decision core (Σ, Δ and the reading mode, `DecCore`) and the same top frame's readings, every scope decision transfers by the simulation of
`Decide.lean` (`DecideScope.decideSim`); the env's values, the move log, the counters and the
records may differ. The block's captures (`blockCaps`) read values (D90's first obligation) and are
asked of the new state separately. -/
theorem DecAligned.of_core {D : Decisions} {st st' : MState} (hd : DecAligned D st) (h : DecCore st' st)
    (hl : ∀ i, DecideScope.liveVal st' i = DecideScope.liveVal st i)
    (hbc : ∀ st₀, SameDec st₀ st' → ∀ fuel mt bc b st₁, Runs (ckBlockCaps fuel mt) st₀ b bc st₁ →
      D.blockCaps (DecideScope.topReadings st') (entryOf st') mt = bc) : DecAligned D st' where
  flags fuel sc t fl b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_bind (DecideScope.sim_withLive _
      ((DecideScope.decideSim fuel).2.2.2.2.2.2.2.2.1 _ _ _ _)) fun d =>
        DecideScope.sim_bind (DecideScope.sim_preFlags t d) fun _ => DecideScope.sim_pure _)
      (envRel_scope_of_core h sc) hr
    exact hd.flags fuel sc t fl b _ hr'
  placeDecl fuel sc p d b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_withLive _ ((DecideScope.decideSim fuel).1 _ _))
      (envRel_scope_of_core h sc) hr
    exact hd.placeDecl fuel sc p d b _ hr'
  declOf fuel sc t d b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_withLive _ ((DecideScope.decideSim fuel).2.2.2.2.2.2.2.2.1 _ _ _ _))
      (envRel_scope_of_core h sc) hr
    exact hd.declOf fuel sc t d b _ hr'
  copy fuel r c b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel ((DecideScope.decideSim fuel).2.2.2.1 _) (envRel_of_core h hl) hr
    exact hd.copy fuel r c b _ hr'
  piSort fuel sc t l b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_withLive _ ((DecideScope.decideSim fuel).2.2.2.2.2.2.1 _))
      (envRel_scope_of_core h sc) hr
    exact hd.piSort fuel sc t l b _ hr'
  joinMoves fuel sc entry t ms b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (jdMoves_sim fuel t entry) (envRel_scope_of_core h sc) hr
    exact hd.joinMoves fuel sc entry t ms b _ hr'
  rePointed fuel sc t ts b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (typeState_sim fuel t) (envRel_scope_of_core h sc) hr
    exact hd.rePointed fuel sc t ts b _ hr'
  typeDecl fuel sc T d b st₁ hr := by
    obtain ⟨_, hr'⟩ := runs_envRel (DecideScope.sim_withLive _ ((DecideScope.decideSim fuel).2.2.2.2.2.2.2.2.2.1 _ _ _ _ _ _))
      (envRel_scope_of_core h sc) hr
    exact hd.typeDecl fuel sc T d b _ hr'
  blockCaps := hbc

/-- The decisions stay across what only the move log and the refinements change (`DecAligned.of_core`
with the block's captures read from the same environment). -/
theorem DecAligned.of_sameDec {D : Decisions} {st st' : MState} (hd : DecAligned D st) (h : SameDec st' st)
    (he : st'.env = st.env) : DecAligned D st' :=
  hd.of_core (DecCore.of_sameDec h) (fun i => by simp [DecideScope.liveVal, he]) fun st₀ h₀ => by
    have e1 : DecideScope.topReadings st' = DecideScope.topReadings st := by
      unfold DecideScope.topReadings; rw [he]
    have e2 : entryOf st' = entryOf st := by unfold entryOf; rw [he]
    rw [e1, e2]
    exact hd.blockCaps st₀ (h₀.trans h)

/-! ### Helpers from `Steps/Borrow.lean` -/

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

/-- What `run` reads of a binding besides its meaning: its type's code, and its declared reading.
(The label a type recorded when it was bound is read by no clause.)

The type's structure was left out when `Rel` was first stated, as an open lemma. Without it the
relation admits a reference state whose bindings have lost their Π-shapes, from which every call
through a variable fails, so the statements in the simulation form were false of any accepted
call through a variable (docs/31 D22; third lead). Since D59 a type is its code, which carries
its whole structure (a function type's telescope, a data type's declaration and parameters), so
the skeleton compares codes, and a step that binds must show the codes agree: the type conjunct
of `evalCore_step_stmt` (`StrAgree`). -/
def bindSkel (b : SBinding) : TyM × DeclInfo :=
  (b.ty.m, b.decl)

/-- The futures a relation compares at: those that agree with the run's `φ` off the reference's
live labels (a binding holding an inert loan means the constant `φ ℓ` in the reference and `ψ ℓ`
in the checker's state, D20 item 2). Every read the reference run makes of its state is at such a
future (docs/31 D29, point 3), so this is what pins the run. -/
def RelF (φ : Future) (s : SState) (ψ : Future) : Prop := ∀ l, ¬ s.Live l → ψ l = φ l

/-- The content type of the borrow `l`, read at its HOLDER (docs/31 D66): a binding's stored type,
a parked temporary's recorded one (`SState.heldTy`). -/
noncomputable def holderTy (s : SState) (l : Nat) : TyM :=
  match s.holderOf l with
  | some (.bind f i) => (s.tyAt (.bind f i)).m
  | some (.temp _ _) => s.heldTy l
  | none => TyM.err

/-- The holder's content type depends only on the positions, the holders, the stored types and the
recorded ones. -/
theorem holderTy_congr {s t : SState} (hpos : t.positions = s.positions) (hsh : t.shape = s.shape)
    (hty : ∀ p, t.tyAt p = s.tyAt p) (hht : t.heldTy = s.heldTy) (l : Nat) : holderTy t l = holderTy s l := by
  have hh : t.holderOf l = s.holderOf l := by unfold SState.holderOf; rw [hpos, hsh]
  unfold holderTy
  rw [hh]
  split
  · rw [hty]
  · rw [hht]
  · rfl

theorem tyAt_setAt (s : SState) (p : Pos) (g : SVal) (q : Pos) : (s.setAt p g).tyAt q = s.tyAt q := by
  cases q with
  | temp => rfl
  | bind f' i' =>
    cases p with
    | bind f i =>
      simp only [SState.setAt, SState.tyAt, List.getElem?_modify]
      cases hfr : s.env[f']? with
      | none => rfl
      | some fr =>
        by_cases hf : f = f'
        · simp only [Option.map_eq_map, Option.map_some, hf, if_true, Option.bind_some, List.getElem?_modify]
          cases fr.binds[i']? with
          | none => rfl
          | some b => simp only [Option.map_eq_map, Option.map_some]; split <;> rfl
        · simp only [Option.map_eq_map, Option.map_some, hf, if_false, Option.bind_some]
    | temp f i =>
      simp only [SState.setAt, SState.tyAt, List.getElem?_modify]
      cases hfr : s.env[f']? with
      | none => rfl
      | some fr =>
        by_cases hf : f = f' <;> simp only [Option.map_eq_map, Option.map_some, hf, if_true, if_false, Option.bind_some]

theorem holderTy_setAt (s : SState) (p : Pos) (g : SVal) (l : Nat) : holderTy (s.setAt p g) l = holderTy s l :=
  holderTy_congr (SState.positions_setAt s p g) (SState.shape_setAt s p g) (tyAt_setAt s p g) (by cases p <;> rfl) l

/-- **A typed future** for the reference state `s` (docs/31 D66): it gives each live label a whole
member of its holder's content type. A future gives each borrow its FINAL content, which is a whole
member of its type (the checker rejects an end over a moved or partly moved content, D53), so these
are the futures that can occur; at the others the two runs may read a returned borrow differently
(the checker raw, `callOf` decoded through the backward function, `Regress/ReturnedRead.lean`). -/
def TypedLive (s : SState) (ψ : Future) : Prop :=
  ∀ l, s.Live l → (ψ l).whole ∧ ψ l ∈ₛ[K.dm.read] holderTy s l

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
  sim : SimEq π (fun ψ => RelF φ s ψ ∧ TypedLive K s ψ) (MState.mean K.dm K.M K.Γ ρ st) s
  /-- the renaming is one to one on the checker's live labels -/
  inj : ∀ l l', liveLoan st.env l = true → liveLoan st.env l' = true → π l = π l' → l = l'
  /-- each live borrow is lent at the same places, in the same way (fill or loan), on both sides:
  the reference's [Access] reads these, the checker's reads its values (`Env.sitesOf`) -/
  sites : ∀ l, liveLoan st.env l = true → ∀ x, x ∈ s.lent (π l) ↔ x ∈ Env.sitesOf st.env l
  /-- the reference holds borrows at its own positions only (a reference-state fact every reference
  step keeps: a holder is pushed with its position, `dropLast` and [End] clear theirs). Added for
  the lent prefix (`MovedPlace.lentPrefix_some_of_fill`): without it a live borrow of the checker
  held in a temporary need not be live in the reference, whose `SimEq` gives its holder a
  temporary index but not that the index exists. -/
  holders : ∀ p l, s.shape p = some l → p ∈ s.positions
  /-- every live label's RECORD is a whole member of its holder's content type (docs/31 D68): made
  where a label is made (`borrowPlace` records the content it borrowed, a member by the checker's
  [Borrow], whose [Repack] rejects lending an open value whole; `callOf`'s `.ref` row records the
  forward value, a member by construction), and kept, since records and held types are written
  once per label and a binding holder's stored type is the held type. So the future a place is read
  at (`SState.typedFuture`) is typed. (It replaces D66's inhabitation clause, which asked only that
  some member exist.) -/
  records : ∀ l, s.Live l → (s.heldMem l).whole ∧ s.heldMem l ∈ₛ[K.dm.read] holderTy s l

/-- The future a place is read at agrees with the run's off the live labels. -/
theorem relF_typedFuture (φ : Future) (s : SState) : RelF φ s (s.typedFuture φ) := fun l hl => by
  have : l ∉ s.liveLabels := hl
  simp [SState.typedFuture, this]

/-- **The future a place is read at is typed** at a related state (docs/31 D68). -/
theorem Rel.typedFuture_typed {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState}
    {s : SState} (hs : Rel K ρ φ π st s) (ψ : Future) : TypedLive K s (s.typedFuture ψ) := fun l hl => by
  have : l ∈ s.liveLabels := hl
  simp only [SState.typedFuture, this, if_true]
  exact hs.records l hl

/-- **A typed future exists** that agrees with any given one off the live labels: the records. -/
theorem Rel.typed_exists {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hs : Rel K ρ φ π st s) (ψ : Future) :
    ∃ ψ' : Future, (∀ l, ¬ s.Live l → ψ' l = ψ l) ∧ TypedLive K s ψ' :=
  ⟨s.typedFuture ψ, relF_typedFuture ψ s, hs.typedFuture_typed ψ⟩

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

/-- The callee as the run sees it: its meaning, and its type value's meaning (a code, which holds
the telescope a call walks). -/
noncomputable def calleeRes (fv : Value) (fT : Value) : Res :=
  (meanV K ρ φ (.plain .err) fv, .plain (meanV K ρ φ (.plain .err) fT).asTy)

/-- The arguments as the run sees them, with each borrow argument's label. -/
noncomputable def argsRes (ws : Array Value) : List Res :=
  ws.toList.map fun w => (meanV K ρ φ (.plain .err) w,
    ⟨TyM.err, (match w with | .borrow l _ => some l | _ => none)⟩)

/-! ### Helpers from `Steps/Match.lean` -/

/-- `ρ'` extends `ρ` on the unknowns of `st`. -/
def Extends (st : MState) (ρ ρ' : Assignment) : Prop := ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ

/-! ### Helpers from `Steps/Obs.lean` -/

/-- The reference observation of a side, if its run succeeds: the result and the positions the side
started with (the audit's A5), as `run`'s `.id` clause reads it. -/
noncomputable def refObs (reps : List Place) (ws : List Sem) (hint : TyS) (t : Term) (s : SState) : Option (List Sem) :=
  (run K ρ φ hint t s).map fun (r, s') => observation φ reps ws s.positions r s'

/-- **What each re-pointed binding points to, on the reference** (main's D113, [Obs-ref]): after the
side's run, each re-pointed binding's content (what it points to as the side left it) is moved out
and held as a temporary, and the written value put in its place; then every live borrow ends (so a
reborrow of part of a moved-out content fills it), and each held content is read. The checker's
`observe` returns these as its third component and `idType` compares them (`Eq(T, c, c')`).
Defined here for the restated `observe_step_stmt`; the model's own observation (`Run.observation`,
which `run`'s `.id` clause compares) does not yet read them: see `idType_step_stmt`. -/
noncomputable def refTargetsOf (reps : List Place) (ws : List Sem) (s : SState) : List Sem :=
  let (s, cs) := (reps.zipIdx).foldl (fun (sc : SState × List Pos) (q, i) =>
    match resolve sc.1 q, ws[i]? with
    | some (pos, []), some w =>
      let s₁ := (sc.1.setAt pos fun _ => w).pushTemp (sc.1.valAt pos)
      (s₁, sc.2 ++ [Pos.temp s₁.topIdx (((s₁.env.getLast?).map (·.temps.length)).getD 1 - 1)])
    | _, _ => sc) (s, [])
  let s := s.liveLabels.foldl SState.endLabel s
  cs.map fun p => s.valAt p φ

/-- `refTargetsOf` after the side's run, if it succeeds. -/
noncomputable def refTargets (reps : List Place) (ws : List Sem) (hint : TyS) (t : Term) (s : SState) : Option (List Sem) :=
  (run K ρ φ hint t s).map fun (_, s') => refTargetsOf φ reps ws s'

/-- A term's embedded value, if it is one (`Machine.forceHint`'s reading of the deferred hint's arguments). -/
def _root_.Ochr.Term.val? : Term → Option Value
  | .val v => some v
  | _ => none

/-- **D124's deferred hint taken apart** (`Machine.hintLater P ws = ⌈⋄hint(P, ws)⌉`, the sealed program that only
`forceHint` reads): the function type and the arguments, as `forceHint` reads them. -/
def deferredHint? : Value → Option (Value × List Value)
  | .sealed (.prim "⋄hint" (.val P :: as)) => some (P, as.filterMap Term.val?)
  | _ => none

theorem anyAtomList_filterMap_val {Q : Value → Bool} : ∀ (as : List Term),
    Value.anyAtomList Q (as.filterMap Term.val?) = true → Term.anyAtomList Q as = true
  | [], h => by simp [Value.anyAtomList] at h
  | a :: as, h => by
    cases a with
    | val v =>
      simp only [List.filterMap_cons, Term.val?, Value.anyAtomList, Bool.or_eq_true] at h
      rcases h with h | h
      · simp [Term.anyAtomList, Term.anyAtom, h]
      · simp [Term.anyAtomList, anyAtomList_filterMap_val as h]
    | _ =>
      simp only [List.filterMap_cons, Term.val?] at h
      simp [Term.anyAtomList, anyAtomList_filterMap_val as h]

/-- The deferred hint's function type and arguments are atoms of the hint. -/
theorem deferredHint?_atoms {T P : Value} {ws : List Value} (h : deferredHint? T = some (P, ws)) (Q : Value → Bool) :
    (P.anyAtom Q = true → T.anyAtom Q = true) ∧ (Value.anyAtomList Q ws = true → T.anyAtom Q = true) := by
  unfold deferredHint? at h
  split at h
  · rename_i P' as
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun hp => ?_, fun hw => ?_⟩
    · simp [Value.anyAtom, Term.anyAtom, Term.anyAtomList, hp]
    · simp [Value.anyAtom, Term.anyAtom, Term.anyAtomList, anyAtomList_filterMap_val as hw]
  · cases h

/-- The number of domains of a function type value (`paramTy` at this index reads the codomain). -/
def piArity : Value → Nat
  | .tPi _ (.pi _ ds _) _ => ds.length
  | .tPi _ (.fix _ _ ds _ _ _) _ => ds.length
  | _ => 0

/-! ### Helpers from `Steps/Eval.lean` -/

/-- The type the context gives, as a `TyM` (`err` when none). D124's deferred hint `⌈⋄hint(P, ws)⌉`
(`Machine.hintLater`: a called body's declared codomain at its arguments, evaluated where it is read,
`forceHint`) is read as what it defers, the codomain of `P` at `ws` (`CodeMeaning.paramTy` past the last
domain), exactly as the statement reads a deferred call type (`LaterOk`) and a binding's deferred type
(`Env.hintAt`): the hint is a type the checker computes later, not a value of the model (the orchestrator's
ruling on docs/31 D243; read as a value it means `err`, `CallRanAttack.tyS_hintLater`, and the induction
hypothesis could not reach a called body that reads its hint, `BareNone`). Every other hint as before. -/
noncomputable def hintM (hint : Option Value) : TyS :=
  match hint with
  | none => .plain .err
  | some T => match deferredHint? T with
    | some (P, ws) => K.M.paramTy ρ P ws (piArity P)
    | none => Value.tyS K.dm K.M K.Γ ρ T

/-- **What a private computation leaves** (`inStatement`, `privately`: `restoreKeep`, D37): Ω, the
goal, the path condition and the declarations are the snapshot's; the tables of unknowns and labels
only grow, the old unknowns keeping their types. With `ExtOk`, an extension under which the state
after meets `CtxOk` and is good, it is the conclusion of every private computation; the relation to
the reference state, which a private computation does not touch, follows (`Rel.kept`).
As first stated `mkEqM` and `evalType` kept the state's core unchanged and the conversions said
nothing of the state after: false, and incomplete. A conversion of two functions or Π-types runs
their generic calls on a private copy, whose new unknowns' types `restoreKeep` keeps, so the table
grows (`Regress/EqJ`: `conv`, `mkEqM` and `evalType` at `F` and `G`); and `J` runs its transported
term from the state its conversion leaves (docs/31 D75). -/
def KeptAfter (st st' : MState) : Prop :=
  st'.env = st.env ∧ st'.goal = st.goal ∧ st'.refs = st.refs ∧ st'.inds = st.inds ∧
    st.absTy.size ≤ st'.absTy.size ∧ (∀ σ, σ < st.absTy.size → st'.absTy[σ]? = st.absTy[σ]?) ∧
    st.nextLoan ≤ st'.nextLoan

/-- An extension of the assignment and `Δ` at the unknowns created between `st` and `st'` (D71's
rule) under which `st'` meets `CtxOk` and is good. The decisions are the context's, fixed for the
run (the slice, main's decision 2026-11-20: as the lead first had it, they were extended with `Δ`,
`D'` agreeing on old inputs, which needed the run's congruence in the decisions; a step now assumes
them aligned at the state after it, `DecTab K.D st'`, `Steps/MachineMono.lean`). -/
def ExtOk (st st' : MState) (ρ' : Assignment) (Δ' : Nat → TyS) : Prop :=
  (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
    CtxOk { K with Δ := Δ' } ρ' st' ∧ Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st'

/-- [End ℓ] (`Machine.endBorrow`) in the simulation form (docs/31 D29): from any related reference
state, the checker's end of a live borrow `ℓ` is the reference's `endLabel (π ℓ)`: the meanings
are `semEnd`'s (the substitution is fixing the future, `meanV_substLoan`; re-normalisation keeps
a meaning; a mark has none), the holder is forgotten on both sides, and the places `ℓ` was lent
pass to the borrows of its content alike (main's `lendEnv (.ended ℓ …)` against `SState.relend`).
The content is whole, which the checker checks outside an observation (D53 (h), D68). In the
extended form (docs/31 D71's rule; the slice, main's item 3, 2026-11-20): an end substitutes its
content for the loan (`substEnv_loan_step`), whose re-runs of sealed programs keep unknowns and
records (D37), and its [Repack] check may make an unknown nothing names, so the assignment and `Δ`
are extended, the decisions aligned after it (`hD`), and the context and `Good` hold after it.
(As first stated, in the order form against `Mean.semEnd` from the checker's own state; then
`Rel` and `Good` at the same context, which a re-run's kept unknowns falsify.) -/
def endBorrow_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s) (hl : liveLoan st.env l = true)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.endBorrow fuel l) st bh () st'),
    st.absTy.size ≤ st'.absTy.size ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS),
      ExtOk K ρ st st' ρ' Δ' ∧ Rel { K with Δ := Δ' } ρ' φ π st' (s.endLabel (π l))

/-- [Access] as the checker performs it before a read (`accessPath` then `accessInside`), in the
simulation form (docs/31 D29): it ends the borrows lent on the path, at the place or inside its
content, iterated, which is the reference's static access of the place (`dataHit`), whose sites
the relation makes the checker's. (`accessPath` alone ends only the path: the pilot prover's
finding, so it is not stated on its own.)

With `owned` (before an assignment, D67) the checker ends only the loans inside the part the
place owns: none at a borrow variable written whole, where the reference's assignment does no
access either (`assignAt`; the audit's A2).

In the extended form (docs/31 D71's rule; the slice, main's item 3, 2026-11-20): the ends it runs
extend the assignment and `Δ` (`endBorrow_step_stmt`), the decisions aligned after it (`hD`), and
the context holds after it, the checker's typing of places (`ShapeFacts`) included. (As first
stated, `Rel` and `Good` at the same context; the slice added `ShapeFacts`; the whole `CtxOk` at
the same context, the old `access_ctx`, is false where the access grows the table of unknowns,
docs/31 D57 (1).) -/
def access_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (p : Place) (pos : Pos) (owned : Bool) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s p = some (pos, (p.steps).2))
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (do Ochr.accessPath fuel p; Ochr.accessInside fuel p owned) st bh () st'),
    st.absTy.size ≤ st'.absTy.size ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ' ∧
      Rel { K with Δ := Δ' } ρ' φ π st'
        (if owned && (p.steps).2.isEmpty && (s.shape pos).isSome then s else s.access pos (dataHit (p.steps).2))

/-- The flight of a result: its label, typed at its content type (the reference's result type
carries both). The in-flight value is typed by this where `MState.withTemp` holds it untyped
(`GoodF`, the pilot's refutations in `BorrowCE.lean`). -/
def flightOf (T : TyS) : Flight := match T.label with | some l => [(l, T.m)] | none => []

/-- The flight of a value about to be written at a place of content type `T`: a borrow's label,
typed at `T`. -/
def flightOfWrite (v : Value) (T : TyM) : Flight := match v with | .borrow l _ => [(l, T)] | _ => []

/-- The conclusion of a step in the simulation form, for the reference computation `x` run from
`s`: `x` does not fail, the checker's value `v` (read at the run's future pulled back along the
renaming) is its result, and the states after are related, under an assignment that extends `ρ`
on the unknowns of `st`, a run context whose `Δ` is extended there too, and a renaming that agrees
with `π` on the labels `st` had issued; the state after meets the context's conditions again
(`CtxOk`), and its tables of unknowns and labels only grew. As first stated it kept the context and
concluded no `CtxOk`, so no step could follow it: the assembly of a body's run (the frame pushed,
the body, the frame popped) had nothing to apply the pop's step to (docs/31 D71; the join's
statements already had this form, docs/31 D29 task C). The value returned is in flight: it is
counted as a temporary of the checker's state (`MState.withTemp`, as the borrow statements read a
result), since the reference parks a returned borrow in a temporary (D14) and the relation matches
temporaries by the borrows they hold; as first stated the state after was compared without it, and
after `&x` the reference's parked borrow matched nothing (docs/31 D71). -/
def SimConcl (π : Nat → Nat) (st st' : MState) (s : SState) (x : Assignment → SM Res) (v : Value) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState), st.absTy.size ≤ st'.absTy.size ∧
    st.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
    x ρ' s = some (r, s') ∧
    meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π' (st'.withTemp v) s' ∧
    GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp v) (flightOf r.2)

/-- The reference's end of a `let` (`run`'s `.letIn` clause after its tail): the borrow the top
binding holds ended, or else the borrows lent at it (`letLenders`), then the binding dropped. -/
noncomputable def letEnd (s : SState) : SState :=
  let held : Option Nat := match s.env.getLast? with
    | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
    | none => none
  (match held with | some l => s.endLabel l | none => letLenders s).dropLast

/-- [Read] (`readPlace`), in the simulation form (docs/31 D80): from a related state, the
reference's `readPlace` at the same copy decision (`Decisions.copy`, aligned) gives the result the
checker's value means, the states after related with the value in flight, under an extension at the
unknowns an end's [Repack] makes (named by nothing), the decisions aligned after it. As first
stated: `Below`, from the checker state's image. -/
def readPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value) (copy : Bool)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf s) p) = copy)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.readPlace fuel p) st bh v st'),
    SimConcl K ρ φ π st st' s (fun _ => Ochr.Meaning.readPlace K φ p copy) v

/-- [Borrow] (`borrowPlace`), in the simulation form (docs/31 D80): from a related state, the
reference's `borrowPlace` gives the borrow the checker's value means, parked in flight on both sides
(D14), the states after related under an extension (the access may repack). As first stated:
`Below`, from the checker state's image. -/
def borrowPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.borrowPlace fuel p) st bh v st'),
    SimConcl K ρ φ π st st' s (fun _ => Ochr.Meaning.borrowPlace K φ p) v

/-- [Assign] (`assignPlace`), in the simulation form (docs/31 D80): the value written is in flight
before the step (counted in the checker's state, `withTemp`, and typed at the place, `flightOfWrite`);
from a state so related, the reference's `assignAt` at its meaning and label gives a state related to
the checker's after, under an extension (the access ends borrows, which may repack). As first
stated: `Below`, from the checker state's image. -/
def assignPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value) (T : Option Value) (pos : Pos)
    (hgv : GoodF K.dm K.M K.Γ ρ (st.withTemp v) (flightOfWrite v (Env.hintAt K.dm K.M K.Γ ρ st.env pos).m))
    (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemp v) s) (hpos : resolve s p = some (pos, (p.steps).2))
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.assignPlace fuel p) (st.withTempT v T) bh () st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
      (∀ l, l < st.nextLoan → π' l = π l) ∧ ExtOk K ρ st st' ρ' Δ' ∧ st.absTy.size ≤ st'.absTy.size ∧
      assignAt K φ p (meanV K ρ φ (.plain .err) v) (match v with | .borrow l _ => some l | _ => none) s = some (r, s') ∧
      Rel { K with Δ := Δ' } ρ' φ π' st' s'

/-- The end of a `let` (`dropTopBind`: the top binding dropped, the borrow it holds ended, or the
borrows lent at it ended, D65), in the simulation form (docs/31 D80): against the reference's end of
a `let` (`letEnd`, `run`'s `.letIn` clause after its tail). As first stated: `Below`, from the
checker state's image. -/
def dropTopBind_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.dropTopBind fuel) st bh () st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat),
      (∀ l, l < st.nextLoan → π' l = π l) ∧ ExtOk K ρ st st' ρ' Δ' ∧ st.absTy.size ≤ st'.absTy.size ∧
      Rel { K with Δ := Δ' } ρ' φ π' st' (letEnd s)

/-- The pop of a frame (`popFrame`: its borrows ended, its positions dropped), in the simulation
form (docs/31 D80): against the reference's pop of a call frame (`popCallFrame start none`), where
every live label at or above `start` is held in the top frame (the frame's own, issued since it was
pushed), so both end exactly the frame's borrows. As first stated: `Below`. -/
def popFrame_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    -- the popped frame's temporaries hold no borrow (the pilot's refutation: a pop discards
    -- temporaries without ending them; both call sites move the result below first)
    (htemps : ∀ fr, st.env[st.env.size - 1]? = some fr → ∀ v ∈ fr.temps, v.hasBorrow = false)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) (start : Nat)
    (hstart : ∀ l, start ≤ l → s.Live l → ∃ f i, (s.holderOf l = some (.bind f i) ∨ s.holderOf l = some (.temp f i)) ∧ f = s.topIdx)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.popFrame fuel) st bh () st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat),
      (∀ l, l < st.nextLoan → π' l = π l) ∧ ExtOk K ρ st st' ρ' Δ' ∧ st.absTy.size ≤ st'.absTy.size ∧
      Rel { K with Δ := Δ' } ρ' φ π' st' (popCallFrame start none s)

/-- `substV` of a loan (a fill at [End], [Close]): the value means the value read under the future
fixed at `ℓ` to the filler's meaning, exactly (D29), under an extension at the unknowns its re-runs
keep (a changed sealed program re-runs; D75, D76). As first stated: `⊑` and the core unchanged. -/
def substV_loan_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (w v v' : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hw : ¬ w.hasLoanM l) (hf : HintFree K ρ φ w)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.substV fuel (.loan l) w v) st bh v' st'),
    KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ' ∧
      meanV { K with Δ := Δ' } ρ' φ hint v' = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v

/-- What a refinement `σ := r` must be for its substitution to keep every meaning (docs/31 D76): it
means what the assignment gives `σ`, at every future and every hint (it holds no loan and records
its parameters), it names typed unknowns other than `σ`, and `σ` is typed. -/
def RefineOk (st : MState) (σ : Nat) (r : Value) : Prop :=
  (∀ ψ H, ρ σ = meanV K ρ ψ H r) ∧ σ < st.absTy.size ∧ (∀ τ, r.hasAbs τ = true → τ < st.absTy.size) ∧
    r.hasAbs σ = false ∧ ∀ l, r.hasLoan l = false

/-- `substV` of an abstract value by a refinement it means: the value means the same, at every
future and hint, under an extension at the unknowns its re-runs keep (a changed sealed program
re-runs, `nfSealed`, and an `Eq` is rebuilt, `mkEqM`: both private computations, D75). As first
stated, `⊑` and the core unchanged: the second false, since a re-run keeps its unknowns' types. -/
def substV_abs_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r v v' : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hr : RefineOk K ρ st σ r)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.substV fuel (.abs σ) r v) st bh v' st'),
    KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ' ∧
      ∀ ψ, meanV { K with Δ := Δ' } ρ' ψ hint v' = meanV K ρ ψ hint v

/-- `substEnv` of a loan (the state-wide half of [End] and of [Close]'s fills): every position
means what it meant at the future fixed at `ℓ`, exactly, under an extension at the unknowns the
re-runs keep; stored types are untouched (`types = false`: no type holds a loan) and so is Ω's
shape. As first stated: `⊑`, the context fixed. -/
def substEnv_loan_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (l : Nat) (w : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hw : ¬ w.hasLoanM l) (hf : HintFree K ρ φ w)
    (bh : Nat) (h : Runs (Ochr.substEnv fuel (.loan l) w false) st bh () st'),
    (∀ p, Env.shape st'.env p = Env.shape st.env p) ∧ st.absTy.size ≤ st'.absTy.size ∧
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧
      ∀ p, (MState.mean K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st').val φ p =
        (MState.mean K.dm K.M K.Γ ρ st).val (φ.upd l (meanV K ρ φ (.plain .err) w)) p

/-- What a substitution over the whole state leaves: which positions exist and which hold borrows
(Ω's shape) are the snapshot's, so are the goal's presence and the declarations; the tables only
grow. (The values, stored types, goal and table entries are rewritten; what they MEAN is kept, which
the relation and `ExtOk` say.) -/
def SubstShape (st st' : MState) : Prop :=
  (∀ p, Env.shape st'.env p = Env.shape st.env p) ∧ allPos st'.env = allPos st.env ∧ st'.inds = st.inds ∧
    st.absTy.size ≤ st'.absTy.size ∧ st.nextLoan ≤ st'.nextLoan

/-- **Replacing an unknown by what a refinement says it is keeps every meaning** (`substEnv` of
`.abs σ` by `r`, `types = true`: Ω, the stored types, the table and the goal; docs/31 D76): the
counterpart for unknowns of the substitution lemma for borrows. From a related state, under an
assignment at which the refinement holds (`RefineOk`), the state after is related to the SAME
reference state with the same renaming (the reference does not split: every position means what
it meant), and is good and meets `CtxOk` under an extension at the unknowns the re-runs keep. A
changed sealed program re-runs (`nfSealed`): a loan-free one may compute (`Regress/SplitSubst`,
`Pred2(σ)` at `σ := S(σ₁)` is `σ₁`), one holding a hole stays sealed with its text substituted
(D97); a type is rebuilt (`Eq(…, G, Choose(σ))` at `σ := S(σ₃)` converts `G` and `F`, which keeps an
unknown); a generalisation record whose program names `σ` is left as it is, and still holds. As
first stated: `Below` from the checker state's image, the context fixed. -/
def substEnv_abs_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) (hr : RefineOk K ρ st σ r)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.substEnv fuel (.abs σ) r true) st bh () st'),
    SubstShape st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS),
      ExtOk K ρ st st' ρ' Δ' ∧ Rel { K with Δ := Δ' } ρ' φ π st' s

/-- What a value `r` must be to replace a sealed program `n` everywhere (`substEnv n r`): it means
what `n` means, at every future and hint, names typed unknowns only, and holds no loan. -/
def NeutralOk (st : MState) (n r : Value) : Prop :=
  (∀ ψ H, meanV K ρ ψ H r = meanV K ρ ψ H n) ∧ (∀ τ, r.hasAbs τ = true → τ < st.absTy.size) ∧
    ∀ l, r.hasLoan l = false

/-- **Replacing a sealed program by a value that means it keeps every meaning** (`substEnv` of a
sealed program `n` by `r`, `types = true`: a generalisation's record read back, `recordedNeutral`,
or a program replaced by its unknown), in the form of `substEnv_abs_step_stmt`: the state after is
related to the SAME reference state, good and meeting `CtxOk` under an extension at the unknowns the
re-runs keep, the decisions aligned after it. Added for the slice (main's item 3, 2026-11-20; the
drop's `recorded_sim`). -/
def substEnv_neutral_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (n r : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) (hr : NeutralOk K ρ st n r)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.substEnv fuel n r true) st bh () st'),
    SubstShape st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS),
      ExtOk K ρ st st' ρ' Δ' ∧ Rel { K with Δ := Δ' } ρ' φ π st' s

/-- **[Seal]: a re-run of a sealed program means the sealed program** (`nfSealed`: its run from
the empty state, kept where it is stuck), EXACTLY (since D29 no borrow ends early in a run, so the
old `⊑` is equality), under an assignment extending `ρ` at the unknowns the nested run created
(`restoreKeep` keeps their types and the generalisation and η records, docs/31 D20 item 9); the
environment, goal and records in force are the state's, the table of unknowns only grows, and
`Good` holds of the state after.

`t` is the text of a sealed program the state holds, or one a substitution made of it: its loans
are live borrows of the state (its holes, `hholes`), its tail reads no hint (`htf`, (WF16)), and its
reference run succeeds (`hok`, the restriction of untyped runs to checked code, docs/31 D20 item 4).
Since main's D97 a text that holds a loan is not run: `nfSealed` returns `⌈t⌉` as it is, which
means itself (`ρ' = ρ`); a text that holds none is run, and that is `nestedRun_sim` (`Steps/Call.lean`)
for a hole-free program under plain `Good` (docs/31 D63). The nested state no longer holds loans
whose borrows are outside it, which no relative form of `Good` is needed for. -/
def nfSealed_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (t : Term) (v : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hholes : ∀ l ∈ t.loans, liveLoan st.env l = true) (htf : Term.tailHintFree K.Γ t = true)
    (hok : ∀ ψ, (runT K ρ ψ false hint t (emptyState 0)).isSome)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.nfSealed fuel t) st bh v st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ ψ, meanV { K with Δ := Δ' } ρ' ψ hint v = meanV K ρ ψ hint (.sealed t)) ∧
      st'.env = st.env ∧ st'.goal = st.goal ∧ st'.refs = st.refs ∧
      st.absTy.size ≤ st'.absTy.size ∧ (∀ σ, σ < st.absTy.size → st'.absTy[σ]? = st.absTy[σ]?) ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧ Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st'

/-- `canonNeutral`: a sealed program already generalised in this world is its `σ`, which the
path condition makes mean the same. -/
def canonNeutral_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (v v' : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.canonNeutral v) st bh v' st'),
    (∀ φ, meanV K ρ φ hint v' = meanV K ρ φ hint v) ∧ st'.core = st.core

/-- `renormAll` (after a generalised unknown is refined): re-running every sealed program of the
state keeps every meaning, in the simulation form of `substEnv_abs_step_stmt` (the reference does
nothing). As first stated: `Below` from the checker state's image, the context fixed. -/
def renormAll_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.renormAll fuel) st bh () st'),
    SubstShape st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS),
      ExtOk K ρ st st' ρ' Δ' ∧ Rel { K with Δ := Δ' } ρ' φ π st' s

/-- [Split]'s refinement `σ := r` (`refine`: the substitution, the path condition recorded, the
re-normalisation when `σ` is a generalisation's), in the simulation form of `substEnv_abs_step_stmt`:
under an assignment that gives `σ` the meaning of `r` (the arm the assignment selects, with its
fields assigned) every meaning is kept, and the record is the path condition the assignment meets.
Assembled in `Steps/SplitAsm.lean`. As first stated: `Below` from the checker state's image. -/
def refine_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (σ : Nat) (r : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) (hr : RefineOk K ρ st σ r)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.refine fuel σ r) st bh () st'),
    SubstShape st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS),
      ExtOk K ρ st st' ρ' Δ' ∧ Rel { K with Δ := Δ' } ρ' φ π st' s

/-- `Eq` computes soundly: whatever `mkEqM` returns means the proposition `⟦a⟧ = ⟦b⟧` at `A`
(every outcome, `True`, `False`, a conjunction of field equations, the stuck `Eq`, is a proposition,
`Data.tyM` at a declaration of sort `0`, so its meaning is that proposition, not only as true), and
it is a private computation (`KeptAfter`: its conversions run on copies). -/
def mkEqM_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (A a b P : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hA : ∀ φ, (meanV K ρ φ (.plain .err) A).asTy = (meanV K ρ noFuture (.plain .err) A).asTy)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.mkEqM fuel A a b) st bh P st'),
    KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ' ∧
      ∀ φ (hint : TyS), meanV { K with Δ := Δ' } ρ' φ hint P = .ty (TyM.prop
        (meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) a = meanV K ρ φ (.plain (meanV K ρ noFuture (.plain .err) A).asTy) b))

/-- Conversion is sound: two values convertible at a state, both (partly moved) members of one
type, have equal meanings under every future. The accepting direction only; `convStack` only
makes `conv` answer `false` more often, so no hypothesis on it. -/
def conv_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (v w : Value) (T : TyM)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hv : DataModel.pmem K.dm K.Γ (meanV K ρ φ (.plain T) v) T) (hw : DataModel.pmem K.dm K.Γ (meanV K ρ φ (.plain T) w) T)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.conv fuel v w) st bh true st'),
    meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w ∧ KeptAfter st st' ∧
      ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ'

/-- [Conv-pi]: convertible Π-type values have equal type meanings (equal Lean carriers), by
`funext` over the generic arguments, which range over the whole domain (docs/18 (V4)). -/
def convPi_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (P Q : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.convPi fuel P Q) st bh true st'),
    (∀ φ, (meanV K ρ φ (.plain .err) P).asTy = (meanV K ρ φ (.plain .err) Q).asTy) ∧ KeptAfter st st' ∧
      ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ'

/-- [Conv-fun]: two function values with convertible observations of their generic calls mean
the same function (extensionality on good carriers, docs/18 (V5), `Slice.pi_ext`). -/
def convFn_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (f g : Value) (T : TyM)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hf : meanV K ρ φ (.plain T) f ∈ₛ[K.dm.read] T) (hgm : meanV K ρ φ (.plain T) g ∈ₛ[K.dm.read] T)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.convFn fuel f g) st bh true st'),
    meanV K ρ φ (.plain T) f = meanV K ρ φ (.plain T) g ∧ KeptAfter st st' ∧
      ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ'

/-- [Rewrite]: when the equation `h : Eq(A, a, b)` is true, the rewritten goal is true iff the
goal is (the occurrences replaced mean the same). -/
def rewriteGoal_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (rev : Bool) (hT : Term) (A a b G G' : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bhh : Nat) (hh : Runs (Ochr.eval fuel true hT) st bhh (.proof, some (.tEq A a b)) st)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.rewriteGoal fuel rev hT G) st bh G' st'),
    (KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ') ∧
    (∀ φ, propOf K ρ φ (.tEq A a b) → (propOf K ρ φ G' ↔ propOf K ρ φ G))

/-- The meaning of a type value does not depend on the future (docs/27 Lemma 5: no stored type
holds a live loan), at every state the checker reaches. Used to read types under `noFuture`. -/
def type_futureFree_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hT : ∃ p, MState.posTyM K.dm K.M K.Γ ρ st p = some (meanV K ρ noFuture (.plain .err) T).asTy),
    ∀ φ', (meanV K ρ φ (.plain .err) T).asTy = (meanV K ρ φ' (.plain .err) T).asTy

/-- [Call-type] (`callType`, `declCallType`): the codomain the callee's telescope code reaches at
the arguments (for a returned borrow, its content) is the reference's result type. -/
def callType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (piTy : Value) (ws : Array Value)
    (tys : Array (Option Value)) (B : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.callType fuel piTy ws tys) st bh B st'),
    (KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ') ∧
    (∀ b U, (calleeRes K ρ φ .proof piTy).2.m.codAt? K.dm.read ((argsRes K ρ φ ws).map (·.1)) = some (b, U) →
      (meanV K ρ noFuture (.plain .err) B).asTy = U)

/-! ### The match area, in the simulation form (docs/31 D24; third lead)

The conclusion every statement of this area shares: the reference's run of the match from the
related state does not fail, the checker's value IS its result, and the two states after are
related, for an assignment extending `ρ` to the unknowns created and a renaming extending `π`. -/


/-- **[Join], the entry set** (docs/31 D20 item 1 (e), D24, D29): from related states the
reference's entry set (`movedPlaces`) is the checker's (`entryOf`, `Machine.staticJoin`'s
`botPlaces`), in order. As first written the reference's set held whole variables only, and the
statement was false at any partly moved binding (`Regress/JoinProbes.lean`); then it carried the
borrow variables the checker had ended early, which no longer exist (D29). -/
def joinEntry_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s),
    movedPlaces φ s = entryOf st

/-- The reference's drop of one place (`joinDrop`'s fold body). -/
noncomputable def joinDropOne (K : RunCtx) (φ : Future) (s : SState) (q : Place) : SState :=
  match resolve s q with
  | some (pos, steps) => dropAt K φ q pos steps (accessLentPrefix pos steps s)
  | none => s

/-- What `movedPlace` leaves of a place `q` it was asked for (`q'`): `q` itself, which now exists;
or a prefix of it (the same root, a prefix of the path) holding `⊥` or `⋆`, whose drop does
nothing. -/
def MPOut (st : MState) (q q' : Place) : Prop :=
  (q' = q ∧ ∃ w, ckContent st.env q = some w) ∨
  (q'.steps.1 = q.steps.1 ∧ q'.steps.2 <+: q.steps.2 ∧
    (ckContent st.env q' = some .bot ∨ ckContent st.env q' = some .proof))

/-- **`movedPlace`** (D84, the join's re-rooting of a place to drop), in the simulation form: from
related states, with the place at the join's grain, the checker η-refines the unknowns and
generalises the sealed programs of one-constructor types on its path and accesses a filled parent
whole; the reference does nothing or accesses the shortest lent prefix whole (`accessLentPrefix`,
which the drop does first in any case). Afterwards the place exists, or the checker re-rooted to a
prefix holding `⊥` or `⋆` (`MPOut`). The context is extended at the unknowns created. Recursive,
like the checker's function: the recursion is the field at the fuel below. -/
def movedPlace_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (q q' : Place) (pos : Pos) (s : SState) (π : Nat → Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hpos : resolve s q = some (pos, q.steps.2)) (hgrain : GrainOk K.D K.Γ (scopeOf s) q)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.movedPlace fuel q) st bh q' st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (s' : SState), st.absTy.size ≤ st'.absTy.size ∧
      (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (s' = s ∨ s' = accessLentPrefix pos q.steps.2 s) ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π st' s' ∧
      Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' ∧ MPOut st' q q'

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
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (do Ochr.dropAtJoin fuel (← Ochr.movedPlace fuel q)) st bh () st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS), st.absTy.size ≤ st'.absTy.size ∧
      (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ CtxOk { K with Δ := Δ' } ρ' st' ∧
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
    (hD : DecTab K.D st')
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
    (hD : DecTab K.D st')
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
    (hD : DecTab K.D st')
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
    (hD : DecTab K.D st')
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

/-- [Split-gen] (`generalizeNeutral`), in the simulation form (docs/31 D76): the sealed program `n`
at place `p` becomes a fresh `σ` with the record `n := σ`; under an extension giving `σ` the meaning
of `n` (read at the type the checker gives `σ`) and the unknowns `placeType`'s private copies keep
their values, the state is related to the same reference state (the substitution of a program by an
unknown that means it), good, and meets `CtxOk`. `n` is `p`'s content, a sealed program holding no
loan, as at both callers (`evalMatch`'s scrutinee, `movedPlace`'s prefix); without the first the
statement was false (`Regress/GenNeutralContent.lean`: generalising `⋆` at `a : Nat` records a
proof as a number), and the record needs the others (a partly moved value is no member of its
type; (WF11) forbids a record holding a loan). The decisions are aligned after it (`hD`: the fresh
unknown's frozen reading, D96). As first stated: `Exact` from the checker state's image, `Good` only. -/
def generalizeNeutral_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (n : Value) (σ : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hn : ckContent st.env p = some n) (hsealed : ∃ t, n = .sealed t) (hfree : ∀ l, n.hasLoan l = false)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.generalizeNeutral fuel p n) st bh σ st'),
    SubstShape st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS),
      ExtOk K ρ st st' ρ' Δ' ∧ Rel { K with Δ := Δ' } ρ' φ π st' s ∧
      ρ' σ = meanV K ρ (fun _ => .err) (.plain (MState.absTyM K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' σ)) n

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
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.closeBlock fuel mt arms B?) st bh (v, T?) st'),
    SimConcl K ρ φ π st st' s (fun ρ' => run K ρ' φ (hintM K ρ B?) mt) v

/-- Worlds (X1)–(X4), `exitWorld`, in the simulation form (docs/31 D76): leaving an arm's world
restores the snapshot (Ω, the stored types, the goal, the path condition and the records), keeping
the counters and the types of the unknowns the arm created, which nothing restored names. From the
snapshot's goodness and relation, the restored state is related to the snapshot's reference state
and good under the same assignment and `Δ`, the decisions aligned after it (the arm's unknowns keep
their frozen readings, `absDecl`, D96). The refinement the arm made is gone: the sibling world does
not see it. As first stated: no `CtxOk` after (the next step had none to start from), and before
that false outright (`Regress/ExitWorld_f32a7048.lean`). -/
def exitWorld_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (w : World)
    (hg : Good K.dm K.M K.Γ ρ w.saved) (hctx : CtxOk K ρ w.saved)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π w.saved s)
    -- the arm's run only issued labels (its counter is the snapshot's or above)
    (hgrow : w.saved.nextLoan ≤ st.nextLoan)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.exitWorld w) st bh () st'),
    st'.env = w.saved.env ∧ st'.goal = w.saved.goal ∧ st'.refs = w.saved.refs ∧
      st'.neutrals = w.saved.neutrals ∧ st'.etaRefs = w.saved.etaRefs ∧
      w.saved.absTy.size ≤ st'.absTy.size ∧ (∀ σ, σ < w.saved.absTy.size → st'.absTy[σ]? = w.saved.absTy[σ]?) ∧
      ExtOk K ρ w.saved st' ρ K.Δ ∧ Rel K ρ φ π st' s

/-! ### The level the checker reads of a stored type (area (g), docs/31 D77; candidates)

The slice's drop needs that a stored type's code has the level the checker's `sortOf` computes
(`Good` says only that a level exists, `Membership.absTy`, `Membership.goal`). As a clause of every
state it would be read off the state at each step; it is rather a consequence of `Good`, `CtxOk` and
one small clause on frozen readings (`ReadingsSorted`), plus facts of the model (the levels of the
codes of `Nat`, `Unit`, `Sort l`, a proposition, a data type and a Π-type, and that a member of
`Sort l` is a code of level `l`). `sortOf_sound_stmt` states it so. -/

/-- A type the state stores: a binding's type, a referenced unknown's type, or the goal. -/
def StoredTy (st : MState) (T : Value) : Prop :=
  (∃ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b ∧ b.ty = some T) ∨
    (∃ σ, st.Refd σ ∧ st.absTy[σ]? = some T) ∨ st.goal = some T

/-- (Sort), candidate: a stored type's code has the level the checker reads of it (`sortOf`, at the
state). Swept: `sortOf?` reads a sort of every one of the 392,852 stored binding types of the suite's
recorded states (the premise always arises); the levels need meanings, so are not swept. -/
def SortSound (K : RunCtx) (ρ : Assignment) (st : MState) : Prop :=
  ∀ T, StoredTy st T → ∀ (fuel b l : Nat) (st' : MState), Runs (Ochr.sortOf fuel T) st b l st' →
    (Value.tyM K.dm K.M K.Γ ρ (fun _ => .err) T).level = some l

/-- **The checker's `sortOf` is sound for the model at every good state** (the slice's second fact;
`slice1` owns it). By cases on the type value's head, as `sortOf` reads it: `Nat`, `Unit` and a
borrow type (level 1: the model, and (WF7) for `&A`), `D(ā)` (the declaration's sort: the data
model's `tyM`), `Eq` (a proposition: level 0), `Sort l` (its successor), an unknown (its frozen
reading `Sort l` is its type, (Rd); it is a member of `Sort l` by `TypedAssignment`; a member of
`Sort l` is a code of level `l`), a sealed program (its head call's declared codomain, a sort read by
the aligned `declOf`; the call's result is a member of it), a Π-type (the aligned `piSort`,
`piSort_aligned_stmt`, against the model's level of a telescope). -/
def sortOf_sound_stmt (K : RunCtx) (ρ : Assignment) : Prop :=
  ∀ (st : MState), Good K.dm K.M K.Γ ρ st → CtxOk K ρ st → ReadingsSorted st → SortSound K ρ st

/-! ### The observation area, in the simulation form (docs/31 D26; third lead)

`observe` and `idType` run their sides on private copies, so the checker's Ω is unchanged
(`st'.env = st.env`; the counters, the records and the types of the unknowns created inside
survive, D23, so the core is not) and the reference state is untouched. The values the checker
returns are read under an assignment extended at the unknowns created inside, among them the
fresh values [Obs-ref] writes through the re-pointed bindings. -/

/-- `observe` (a side on a private copy; each re-pointed binding's content moved out as one more
component and the fresh value of `refs` put in its place ([Obs-ref], main's D113); every borrow
ended; the result, the owners and the components read), from a related state: the reference's side
run does not fail, and the checker's result, each observed owner and each component mean their
counterparts of the reference observation (`refObs`, `refTargets`), for the written values the fresh
unknowns mean. The side is run at the hint `A`, as the checker runs it.

RESTATED BY D113 (2026-11-21, the merge of main into the proof line). Before main's D113 [Obs-ref]
wrote the fresh value THROUGH each re-pointed binding (`*y := σ_y`, an [Access] and a drop of what
the side left in the target, unobserved) and `observe` returned the result and the owners. Since
D113 the binding's content `c` (what it points to as the side left it) is taken out of the borrow
without an access and held as a temporary, `σ_y` is put in its place (`borrow_k σ_y`), the ends fill
`c`'s holes, and `observe` returns a third component, the `c`s; `idType` compares them. The
conclusion gains the components (`cs`, against `refTargets`, each at its binding's content type
`Tσ`, `refs`' third entry). NOT PROVED (like the statement before it). -/
def observe_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (A : Value) (W : List Pos)
    (refs : List (Place × Value × Value)) (r : Value) (ws cs : List Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.observe fuel typed t A W refs) st bh (r, ws, cs) st'),
    st'.env = st.env ∧ st.absTy.size ≤ st'.absTy.size ∧ st.nextLoan ≤ st'.nextLoan ∧
    ∀ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) →
      TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' →
      -- the state after (the side ran on a copy) is good again, for the next observation of the
      -- same `Id`, which starts from it (docs/31 D74: as first stated nothing was said of it)
      (Good K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' ∧ CtxOk { K with Δ := Δ' } ρ' st' ∧
        Rel { K with Δ := Δ' } ρ' φ π st' s) ∧
      (∃ o, refObs K ρ' φ (refs.map (·.1)) (refs.map fun x => meanV { K with Δ := Δ' } ρ' noFuture (.plain .err) x.2.1)
          (Value.tyS K.dm K.M K.Γ ρ A) t s = some o ∧
        o[0]? = some (meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (Value.tyS K.dm K.M K.Γ ρ A) r) ∧
        ∀ (i j : Nat) (p : Pos), W[i]? = some p → s.positions[j]? = some p →
          ws[i]?.map (meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (Env.hintAt K.dm K.M K.Γ ρ st.env p)) = o.tail[j]?) ∧
      -- D113: what each re-pointed binding points to, at its content type
      ∃ c, refTargets K ρ' φ (refs.map (·.1)) (refs.map fun x => meanV { K with Δ := Δ' } ρ' noFuture (.plain .err) x.2.1)
          (Value.tyS K.dm K.M K.Γ ρ A) t s = some c ∧ cs.length = refs.length ∧
        ∀ (i : Nat) (q : Place) (σ Tσ x : Value), refs[i]? = some (q, σ, Tσ) → cs[i]? = some x →
          c[i]? = some (meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (Value.tyS K.dm K.M K.Γ ρ Tσ) x)

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
said nothing (`Regress/IdUnitWrite.old_stmt_vacuous`).

FALSE SINCE MAIN'S D113 (found at the merge of main into the proof line, 2026-11-21; kept as it
was, as a finding). D113 makes the checker's conjunction also compare what each re-pointed binding
points to (`Eq(T, c, c')`, `observe`'s third component, `refTargets` on the reference). The model's
`Id` (`run`'s `.id` clause, `Run.observation`) still compares only the result and the positions,
and loses what a side left in a re-pointed binding's target exactly as the checker did before D113
(`observation` puts the written value in the binding's place, so the content is never read). At
`Hide`'s sides (`y := &x` against `y := &x; *y := 5`, main's `Equality.ObsRef`) the reference's `Id`
is true and the checker's conjunction contains `Eq(Nat, 0, 5)`, so the last conjunct (`r` true →
`P` true) is false, and with it the statement. Since a hypothesis of such an `Id` type is used
through the conjunction, the model must follow: `Run.observation` reads the moved-out contents
(as `refTargetsOf` does) and the `.id` clause compares them. That is a change to the model's
definition of `Id`, for the model lane. -/
def idType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A t u : Term) (P : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.idType fuel typed A t u) st bh P st'),
    st'.env = st.env ∧ st.absTy.size ≤ st'.absTy.size ∧ st.nextLoan ≤ st'.nextLoan ∧
    ∃ r, run K ρ φ (.plain .err) (.id A t u) s = some (r, s) ∧
      (∃ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π (st'.withTemp P) s ∧
        GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp P) [] ∧
        (((meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (.plain .err) P).asTy).true ↔ (r.1.asTy).true)) ∧
      ((r.1.asTy).true → ∀ (ρ' : Assignment) (Δ' : Nat → TyS), (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) →
        TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' st' →
        ((meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (.plain .err) P).asTy).true)

/-- Owners (RULES §4): every position `owners env l` lists holds, directly or through the content
of a borrow it holds, a loan of `l`; and conversely every position whose meaning depends on `l`
is among them (`Mean.dependsOn`). -/
def owners_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (l : Nat) (p : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hl : liveLoan st.env l = true),
    (MState.mean K.dm K.M K.Γ ρ st).dependsOn p l → p ∈ owners st.env l

/-- `evalType` (a type term, on a private copy), from a related state: the result means the run's
result under an extension at the unknowns it made, the reference state untouched (a type is a
statement, which the run runs on a copy at the aligned flags), and it is a private computation
(`KeptAfter`).
As first stated the state's core was unchanged, false: a type that compares two functions keeps
the types of the unknowns its conversion made (`Regress/EqJ`); and the run was from the checker
state's image rather than a related reference state (docs/31 D75). -/
def evalType_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.evalType fuel t) st bh T st'),
    KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ' ∧
      ∃ (r : Res), run K ρ' φ (.plain .err) t s = some (r, s) ∧
        meanV { K with Δ := Δ' } ρ' (fun l => φ (π l)) (.plain .err) T = r.1

/-- `placeType?` (a place's type, its field and parameter types evaluated on private copies) is a
private computation (`KeptAfter`), in the form of `evalType_step_stmt`: the state after is good and
meets `CtxOk` under an extension at the unknowns the copies keep, the decisions aligned after it.
Its value is not stated: `movedPlace` reads it only to test for one constructor. Added for the
slice (main's item 3, 2026-11-20; the drop's `placeTypeQ_sim`). Swept first for the other lane's
fault (a private copy leaving a record that names an unknown of an empty type, so that no typed
assignment exists): see `Sweep.recordNamesEmpty`. -/
def placeTypeQ_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (p : Place) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.placeType? fuel p) st bh T? st'),
    KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ'

/-- `piSort` agrees with the aligned decision (D55: a type's declared sort is its computed sort). -/
def piSort_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (caps : List Value) (hs : List Hint)
    (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)) (l : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.piSort fuel (.tPi caps (.pi hs ds c) rd)) st bh l st'),
    K.D.piSort (scopeOf (SM' K ρ st)) (.pi hs ds c) = l

/-- The run's result type `R` is the checker's type `T`, with its structure (docs/31 D22): the
same code, where the checker's side is its stored type read as a reference binding reads it
(`Value.tyS`). This is what a `let` needs to keep `Rel.skel`. As first stated the conjunct compared
the meanings only; then the meaning, Π-shape and data, with a type-valued value's own structure
carried in its type (`Value.strS`). Since D59 the code carries the structure and a type value
carries its own code, so one equation of codes says it all. -/
def StrAgree (T : Value) (R : TyS) : Prop :=
  (Value.tyS K.dm K.M K.Γ ρ T).m = R.m

/-- `SimConcl`, and the type the checker returns agrees with the reference's (`StrAgree`). -/
def SimConclT (π : Nat → Nat) (st st' : MState) (s : SState) (x : Assignment → SM Res) (v : Value)
    (T? : Option Value) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState), st.absTy.size ≤ st'.absTy.size ∧
    st.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
    x ρ' s = some (r, s') ∧
    meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
    CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π' (st'.withTemp v) s' ∧
    GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp v) (flightOf r.2)

/-- `capture`: the closure value the checker forms (captures by value, the term rewritten to read
them as slots), in the simulation form (docs/31 D80): the run's `.fix` clause from the related state
(its captures accessed and the non-copy ones moved, `fixMoves`) gives the meaning of `.clo cs t' rd`,
the states after related with the closure in flight. As first stated: `Below`, from the checker
state's image. -/
def capture_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (cs : List Value) (t' : Term)
    (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hfix : t matches .fix ..)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) t = (false, false))
    (hD : DecTab K.D st')
    (bh : Nat) (kept : List Nat) (h : Runs (Ochr.capture fuel t) st bh (cs, t', rd, kept) st'),
    SimConcl K ρ φ π st st' s (fun ρ' => runT K ρ' φ false (.plain .err) t) (.clo cs t' rd)

/-- A constructor (`evalCtor`, [Ctor]), in the simulation form with the type (docs/31 D80): the
run's `.ctor` clause from the related state at the hint the checker was given. As first stated:
`Below`, from the checker state's image. -/
def evalCtor_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (ty : String) (c : Nat) (h0 : Hint)
    (pts as : List Term) (hint : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) (.ctor ty c h0 pts as) = (false, false))
    (hok : typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) (.ctor ty c h0 pts as) s).isSome)
    (htn : st.tailNext = false)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.evalCtor fuel typed ty c h0 pts as hint) st bh (v, T?) st'),
    SimConclT K ρ φ π st st' s (fun ρ' => runT K ρ' φ st.curTail (hintM K ρ hint) (.ctor ty c h0 pts as)) v T?

/-- An inductive type applied to its parameters (`evalTInd`), in the simulation form with the type
(docs/31 D80): its parameters run as statements, on copies, so Ω is unchanged; the type value means
the run's. As first stated: from the checker state's image, the core unchanged (false: the
parameters' private runs keep their unknowns' types, D75). -/
def evalTInd_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (n : String) (as : List Term)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hok : typed = false → (runT K ρ φ st.curTail (.plain .err) (.tind n as) s).isSome)
    (htn : st.tailNext = false)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.evalTInd fuel typed n as) st bh (v, T?) st'),
    KeptAfter st st' ∧ SimConclT K ρ φ π st st' s (fun ρ' => runT K ρ' φ st.curTail (.plain .err) (.tind n as)) v T?

/-- `fieldTypesOf`: the checker's field types at parameters and fields mean `DataModel.fieldTy`
at their meanings (the telescope, D64). -/
def fieldTypesOf_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (d : IndDecl) (ps : List Value) (c : Nat)
    (fs : List Value) (tys : List (String × Value))
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.fieldTypesOf fuel d ps c fs) st bh tys st'),
    (KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ') ∧
    (∀ i T, tys[i]?.map (·.2) = some T →
      (meanV K ρ noFuture (.plain .err) T).asTy =
        K.dm.fieldTy d (Value.meanParams K.dm K.M K.Γ ρ noFuture d 0 [] ps) c i
          (Value.meanFields K.dm K.M K.Γ ρ noFuture d (K.dm.recOf d (Value.meanParams K.dm K.M K.Γ ρ noFuture d 0 [] ps)) c 0 [] (fs.take i)))

/-- [Repack]'s accepting direction (`repackCheck`): a value checked whole against `T`, with each
part still lent read as an unknown of its type (D73), is a member of `T` under every typed
future. -/
def repackCheck_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (what : String) (v T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.repackCheck fuel what v T) st bh () st'),
    (KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ') ∧
    (TypedFuture K.dm K.M K.Γ ρ st φ →
      meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ T) v ∈ₛ[K.dm.read] (meanV K ρ noFuture (.plain .err) T).asTy)

/-- [Return]'s accepting direction (`bodyReturns`): the returned value is a member of its type
and every place held by borrow is whole, under every typed future. The value is in flight: the state
it is good in counts it (`MState.withTemp`, its label typed by the step that made it, `fl`), as the
step that returned it concludes (docs/31 D71); as first stated it asked `Good` of the state without
it, false when it is a borrow (its loan then has no borrow in the state, (WF2); docs/31 D72). -/
def bodyReturns_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (what : String) (v T : Value)
    (lent : List Place) (lw : String) (fl : Flight)
    (hg : GoodF K.dm K.M K.Γ ρ (st.withTemp v) fl) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (Ochr.bodyReturns fuel what v T lent lw) st bh () st'),
    TypedFutureF K.dm K.M K.Γ ρ (st.withTemp v) fl φ →
      meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ T) v ∈ₛ[K.dm.read] (meanV K ρ noFuture (.plain .err) T).asTy ∧
      (meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ T) v).whole

/-- `valType?` is sound (the second of the five lemmas): the meaning of a value lies in the
meaning of the type the checker reads off it. -/
def valType_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (v T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hv : ∃ p, valAt st.env p = v)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.valType? fuel v) st bh (some T) st'),
    (KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ') ∧
    (TypedFuture K.dm K.M K.Γ ρ st φ →
      DataModel.pmem K.dm K.Γ (meanV K ρ φ (Value.tyS K.dm K.M K.Γ ρ T) v) (meanV K ρ noFuture (.plain .err) T).asTy)

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
  ∀ (st st' : MState)  (p : Place) (v : Value) (T : Option Value)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (h : Runs (Ochr.assignPlace fuel p) (st.withTempT v T) bh () st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env

/-- [Close] keeps (WF1)–(WF4): the fills are closed sealed programs (C1), the arguments were
loan-free (C8), and a returned borrow's fresh label is held once. -/
def close_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (ws : Array Value) (kind : Kind)
    (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hargs : ArgsLoanFree st.env ws)
    (bh : Nat) (h : Runs (Ochr.closeCall fuel ws.size kind res fills tys) ((fv :: ws.toList).foldl MState.withTemp st) bh v st'),
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env ∧ WF4 st'.env

/-- Closure formation keeps (WF4): the captures are read after [Access] (loan-free) and may not
hold `⊥` (the capture check), and a Π-closure captures no borrow (D48). -/
def capture_wf_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (cs : List Value) (t' : Term)
    (rd : List (DeclInfo × Value))
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (bh : Nat) (kept : List Nat) (h : Runs (Ochr.capture fuel t) st bh (cs, t', rd, kept) st'),
    ¬ (Value.clo cs t' rd).anyAtom Value.badCapture ∧ WF4 st'.env

/-- Every step of `evalCore` keeps (WF6): names are allocated at and below the counters, which
only grow. -/
def eval_wf6_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hwf : WF K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (htn : st.tailNext = false)
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed t hint) st bh (v, T?) st'),
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

/-- **[T-Pi]: a Π-type's code does not depend on where it is read** (docs/31 D22; prerequisite
(a) of the migration). The checker closes a Π-term or a `fix` over the values of its free
variables (`capture`) and stores the closed value, which a later reading runs in the frame of its
captures, at the constant future (`Value.tyS`, `run`'s `.val` clause). The reference run reads the
ORIGINAL term in the forming state, at the run's future (the `.pi` and `.fix` clauses). The two
give the same code (the type a Π-term denotes, the type a closure has), from any reference state
that simulates the checker's.

Three things carry it, none proved: the captured term in the captures' frame runs as the original
in the forming state (the capture lemma: a term's run reads the state only at its free variables,
each after [Access], which the checker's capture also performs); a type holds no live loan, so the
future does not matter (`run_congrE`, proved, gives this once the captures are loan-free); and the
decisions read the same readings through the renaming (`rd` records each capture's).
Where it is KNOWN false: a captured PROOF variable is inlined as `(⋆ : T)`, which the run types
`T` where a read of the variable is typed `err` (`SM.erasedIf`), and a constructor's parameter
solved by such a field's type differs (the audit's A17, `Regress/ShapeProbes.lean`). -/
def piShape_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (t : Term) (cs : List Value) (t' : Term) (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (ht : t matches .pi .. | .fix ..)
    (bh : Nat) (kept : List Nat) (h : Runs (Ochr.capture fuel t) st bh (cs, t', rd, kept) st'),
    (run K ρ φ (.plain .err) t s).map (fun r => (r.1.1.asTy, r.1.2.m)) =
      (run K ρ noFuture (.plain .err) t'
        (stateOf 0 (capsState (capsVals K ρ noFuture cs) (capsTys K ρ noFuture rd)))).map
        (fun r => (r.1.1.asTy, r.1.2.m))

/-! ### The call area, in the simulation form (fifth lead; docs/31 D62)

The checker's call (`Machine.callFn`) is reached from `evalCall` once the head and the arguments
are evaluated and popped from the temporaries; the reference's (`run`'s `.call` clause) applies the
callee's meaning to the head's and the arguments' results (`callOf`). The statements below start
from the checker's state with the head and the arguments still counted as temporaries
(`MState.withTemps`), where the relation holds as it held before the pops; the reference's
arguments are the checker's read through the renaming (`ArgsAgree`). (As first stated, in the order
form against `callOf` from `SM' K ρ st`, which is false once a borrow was held, docs/31 D20.) -/

/-- The state with values in flight counted as temporaries of the top frame, in order. -/
def _root_.Ochr.MState.withTemps (st : MState) (ws : List Value) : MState := ws.foldl MState.withTemp st

/-- The reference's arguments are the checker's: each argument's meaning at the run's future pulled
back along the renaming, and a borrow argument's label renamed (`callOf` reads nothing else). -/
def ArgsAgree (π : Nat → Nat) (ws : Array Value) (as : List Res) : Prop :=
  as.length = ws.size ∧ ∀ (i : Nat) (w : Value) (a : Res), ws[i]? = some w → as[i]? = some a →
    a.1 = meanV K ρ (fun l => φ (π l)) (.plain .err) w ∧
    a.2.label = (match w with | .borrow l _ => some (π l) | _ => none)

/-- **A call** (`callFn`) of a callee that is neither a statement nor a proof (`hns`: the run's
`SM.erasedIf` is not taken; such calls are `eval`'s, on a copy), in the simulation form: the
reference applies the callee's meaning (`callOf`), and the checker's result, read through the
renaming, is its result, of the same type. Its assembly (`Steps/Call.lean`, docs/31 D62): the
call's type and decisions, the result's lending (static ends, rule 1), then a neutral callee closed
off (`closeCall_step_stmt`) or a known one's body run (`runBody_step_stmt`, then
`callOf_inPlace`), or, where the body is stuck, the call closed off from the state before it. -/
def callFn_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (typed : Bool) (f : Term) (args : List Term) (hd : Bool) (fv : Value)
    (fT : Option Value) (ws : Array Value) (tys : Array (Option Value)) (recUid? : Option Nat)
    (res : DeclInfo) (fills : Array Bool) (want defer : Bool) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s)
    (hns : K.D.flags (scopeOf s) (.call f args hd) = (false, false))
    (fres : Res) (hf : run K ρ (fun l => φ (π l)) (.plain .err) (.val fv) s = some (fres, s))
    (as : List Res) (has : ArgsAgree K ρ φ π ws as)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.callFn fuel typed fT ws.size tys hd none recUid? res fills want defer) (st.withTemps (fv :: ws.toList)) bh
      (v, T?) st'),
    SimConclT K ρ φ π (st.withTemps (fv :: ws.toList)) st' s (fun ρ' => callOf K.dm.read fres as) v T?

/-- **A known callee's body, run in place** (`runBody`), in the simulation form: against the
reference's run in place (`CallRef.runBodyRef`: the frame pushed, the body run, the frame popped),
which the induction hypothesis reaches from a related state. That the run in place is the
application of the callee's meaning is the reference's own lemma (`callOf_inPlace`).

`hok`: the body runs untyped (`eval fuel' false body`), and an untyped run of arbitrary text can
succeed in the checker where the reference has no meaning (an unannotated `Nil`; docs/31 D20 item 4),
so the statement is for code whose reference run succeeds; for a body, the callee's meaning being a
member of its type gives it. -/
def runBody_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value))
    (ws : Array Value) (B : Option Value) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s)
    (hfix : fv = .clo cs t rd ∨ ∃ n, fv = .gfn n ∧ Runs (Ochr.fixOf fv) st 0 (cs, t, rd) st)
    (fres : Res) (hf : run K ρ (fun l => φ (π l)) (.plain .err) (.val fv) s = some (fres, s))
    (as : List Res) (has : ArgsAgree K ρ φ π ws as)
    (hok : (runBodyRef K ρ φ fres cs t rd as s).isSome)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.runBody fuel fv cs t rd ws B) st bh v st'),
    SimConcl K ρ φ π (st.withTemps (fv :: ws.toList)) st' s (fun ρ' => runBodyRef K ρ' φ fres cs t rd as) v

/-- **[Close]** (`closeCall`), every row, in the simulation form: EXACT against `callOf`. The
result is a sealed program (or `()` at a declared `Unit`, or a borrow of one), and each lent place
a fill; both mean what the reference's call gives them (the result, the finals; for a returned
borrow, the forward value and the backward function at its final content), since a sealed program
means its run from the empty state, whose call is the same `callOf`. The lending marks `callFn`
made before (`lent_g`) are no site of a live borrow, so they are not compared. The row and the
declared-`Unit` readings (`kind`, `res`, `fills`) and the cells' types (`tys`) are read off the call
as written and trusted; `hkind`, `hres`, `hfills`, `htys` tie them to the callee's telescope code at
the arguments, as before (`Regress/CloseCallStmt.lean` refuted the statement without them). -/
def closeCall_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (fv : Value) (ws : Array Value)
    (kind : Kind) (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hg : Good K.dm K.M K.Γ ρ (st.withTemps (fv :: ws.toList))) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π (st.withTemps (fv :: ws.toList)) s)
    (fres : Res) (hf : run K ρ (fun l => φ (π l)) (.plain .err) (.val fv) s = some (fres, s))
    (hpi : fres.2.m.isPi = true)
    (as : List Res) (has : ArgsAgree K ρ φ π ws as)
    (hkind : kind = .ref ↔ ∃ U, fres.2.m.codAt? K.dm.read (as.map (·.1)) = some (true, U))
    (hres : res = .unit → ∀ B, fres.2.m.codAt? K.dm.read (as.map (·.1)) = some (false, B) → B = TyM.unit)
    (hfills : ∀ i : Nat, fills.getD i false = true → ∀ p,
      fres.2.m.paramAt? K.dm.read ((as.map (·.1)).take i) = some p → p.2 = TyM.unit)
    (htys : ∀ (i l : Nat) (w : Value), ws[i]? = some (Value.borrow l w) → ∀ p,
      fres.2.m.paramAt? K.dm.read ((as.map (·.1)).take i) = some p →
      ∃ T : Value, tys[i]? = some (some (Value.tRef T)) ∧ (Value.tyS K.dm K.M K.Γ ρ T).m = p.2)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.closeCall fuel ws.size kind res fills tys) (st.withTemps (fv :: ws.toList)) bh v st'),
    SimConcl K ρ φ π (st.withTemps (fv :: ws.toList)) st' s (fun ρ' => callOf K.dm.read fres as) v

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
asked only for "not a statement" before the audit's A3 made the run skip an erased term.)

The tail flag is `st.curTail`: `eval` reads the one-shot `tailNext`, clears it, and hands it to
`evalCore` in `curTail`, which the forms read (a `let`'s or sequence's tail, an arm). As first
migrated (docs/31 D71) this statement and the `evalCore` forms' (`letIn`, `eq`, `J`) read
`st.tailNext`, which is `false` at every `evalCore` entry, so a body's `let` was compared with the
reference out of tail position and `eval_step` could not be assembled from it (docs/31 D75, found by
the `Eq` assembly). `htn` records that clearing: a form's subterms are run through `eval`, which
reads `tailNext`, so a set flag would make the first of them a tail.

`hok`: an untyped run (a body's, a sealed program's re-run) is claimed only of code whose reference
run succeeds. Without it the statement is false: the checker's untyped run of an unannotated `Nil`
with no hint returns a bare constructor value, and the reference cannot solve its parameter
(`Regress/UntypedNil.lean`, `evalCore_untyped_false`, `eval_untyped_false`; docs/31 D20 item 4,
D64). Accepted code meets it: the reference run of a callee's body succeeds where its meaning is a
member of its type. -/
def evalCore_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) t = (false, false))
    (hok : typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) t s).isSome)
    (htn : st.tailNext = false)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed t hint) st bh (v, T?) st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat), st.absTy.size ≤ st'.absTy.size ∧
      st.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
      ∃ r s', runT K ρ' φ st.curTail (hintM K ρ hint) t s = some (r, s') ∧
        meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
        (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
        CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π' (st'.withTemp v) s' ∧
        GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp v) (flightOf r.2)

/-- **The induction step as the checker recurses** (docs/31 D20, item 5; the tail flag, D71): every recursive
position of the checker calls `Machine.eval`, which is `evalAt`: it classifies the term
(`preFlags`), runs an erased one on a private copy and restores the environment. The run does
the same at `Decisions.flags` (`SM.erasedIf`, D19), so this statement has no side condition on
the term's class, where `evalCore_step_stmt` has `hns`. The reference runs in tail position exactly
when the checker's state says the term is (`st.tailNext`, D90's one-shot flag, which `runBody` sets
before a body and a tail `let`, sequence or arm hands on): as first stated the reference ran every
term out of tail position (`run`), and the step for a body, run in tail position on both sides
(`runBody`, `CallRef.runBodyRef`), had no hypothesis to use (docs/31 D71, found by the assembly). Same conclusion, in the simulation form,
and the same restriction of untyped runs (`hok`; `Regress/UntypedNil.eval_untyped_false`). -/
def eval_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hok : typed = false → (runT K ρ φ st.tailNext (hintM K ρ hint) t s).isSome)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.eval fuel typed t hint) st bh (v, T?) st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat), st.absTy.size ≤ st'.absTy.size ∧
      st.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
      ∃ r s', runT K ρ' φ st.tailNext (hintM K ρ hint) t s = some (r, s') ∧
        meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
        -- not of a proof: the run does not run one and gives it no type (`SM.erasedIf`), where
        -- the checker returns its proposition (the audit's row 26, and A17). As first stated the
        -- conjunct had no such condition and was false of every proof term
        (∀ T, T? = some T → (K.D.flags (scopeOf s) t).2 = false → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
        CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π' (st'.withTemp v) s' ∧
        GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp v) (flightOf r.2)

/-- [Let]: the binding is pushed at the right-hand side's type and dropped after the tail
(`dropTopBind`); the run's `.letIn` clause. In the simulation form, as `evalCore_step_stmt`, with its
`hok` (missing until docs/31 D75: an untyped run's right-hand side and tail need it). -/
def letIn_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (h0 : Hint) (u w : Term)
    (hint : Option Value) (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) (.letIn h0 u w) = (false, false))
    (hok : typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) (.letIn h0 u w) s).isSome)
    (htn : st.tailNext = false)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed (.letIn h0 u w) hint) st bh (v, T?) st'),
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState), st.absTy.size ≤ st'.absTy.size ∧
      st.nextLoan ≤ st'.nextLoan ∧ (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) ∧ (∀ l, l < st.nextLoan → π' l = π l) ∧
      runT K ρ' φ st.curTail (hintM K ρ hint) (.letIn h0 u w) s = some (r, s') ∧
      meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
      CtxOk { K with Δ := Δ' } ρ' st' ∧ Rel { K with Δ := Δ' } ρ' φ π' (st'.withTemp v) s' ∧
      GoodF K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' (st'.withTemp v) (flightOf r.2)

/-- `Eq` (the `.eq` form), in the simulation form (D71's rule; docs/31 D75): the type and both
sides on private copies, the result `mkEqM`'s. The reference runs the same on copies and returns the
proposition `⟦a⟧ = ⟦b⟧`, which the checker's value means (not only as true: every outcome of
`mkEqM` is a proposition); its state is untouched, the checker's Ω is unchanged and its tables
grow. (As first stated the last conjunct was `(run … = some (r, s') ∧ ⟦v⟧ true) ↔ ⟦r⟧ true` under
`∃ r s'`, which said nothing: `Regress/IdUnitWrite.old_stmt_vacuous`; then it kept the context and
said nothing of `CtxOk` or the relation after.) `hok`, the restriction of untyped runs, as
`evalCore_step_stmt` (missing until the assembly: an untyped side's run needs it). -/
def eq_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A a b : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hok : typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) (.eq A a b) s).isSome)
    (htn : st.tailNext = false)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed (.eq A a b) hint) st bh (v, T?) st'),
    SimConclT K ρ φ π st st' s (fun ρ' => runT K ρ' φ st.curTail (hintM K ρ hint) (.eq A a b)) v T?

/-- `J`, in the simulation form (D71's rule; docs/31 D75), both outcomes: computed at convertible
endpoints, where the transported term runs in place at the join's grain (static ends, rule 2: its
entry first, `blockEntry`), or closed off as a stuck block whose one arm is the transported term
([T-J-stuck], `closeBlock`). The reference's `J` means its transported term whatever the endpoints
([J-run]: `Regress/EqJ.ref_J_runs_t`). `hns`: the run's clause is under `SM.erasedIf`, which
`evalCore` is not; `hok`, the restriction of untyped runs, as `evalCore_step_stmt` (missing until the
assembly: an untyped run's transported term needs it). (As first stated: the old `⊑`/`Below` form,
from the checker state's image.) -/
def J_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (A a b P hh u : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hns : K.D.flags (scopeOf s) (.prim "J" [A, a, b, P, hh, u]) = (false, false))
    (hok : typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) (.prim "J" [A, a, b, P, hh, u]) s).isSome)
    (htn : st.tailNext = false)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.evalCore fuel typed (.prim "J" [A, a, b, P, hh, u]) hint) st bh (v, T?) st'),
    SimConclT K ρ φ π st st' s (fun ρ' => runT K ρ' φ st.curTail (hintM K ρ hint) (.prim "J" [A, a, b, P, hh, u])) v T?

/-- A proof position (a proof-returning call, a proof primitive, a proof `let`), run on a private
copy (`evalAt`): its value is `⋆`, a member of its proposition exactly when the proposition is true;
the reference does not run it (`SM.erasedIf`). In the simulation form (docs/31 D80): a private
computation (`KeptAfter`), the state after related to the same reference state, and `⋆` a member
under the extension. As first stated: the core unchanged (false: the copy keeps its unknowns'
types, D75), from the checker state's image. -/
def proof_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (typed : Bool) (t : Term) (hint : Option Value)
    (T : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s)
    (hp : (K.D.flags (scopeOf s) t).2 = true)
    -- `eval`, not `evalCore`: it is `evalAt` that runs a proof on a copy (as stated for `evalCore`
    -- a proof-valued `let` whose right-hand side moves a place refuted "the state is unchanged")
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.eval fuel typed t hint) st bh (.proof, some T) st'),
    KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ' ∧
      Rel { K with Δ := Δ' } ρ' φ π st' s ∧
      Sem.proof ∈ₛ[K.dm.read] (meanV { K with Δ := Δ' } ρ' φ (.plain .err) T).asTy

/-- η at `Unit` (D80): where a position's declared reading is `Unit`, the value is `()`, and
`()` is the one element of `⟦Unit⟧`, so the normalisation keeps meaning given membership. -/
def etaUnit_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st : MState) (d : DeclInfo) (v : Value) (hint : TyS)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hd : d = .unit)
    (hv : meanV K ρ φ hint v ∈ₛ[K.dm.read] TyM.unit),
    meanV K ρ φ hint (Ochr.etaUnit d v) = meanV K ρ φ hint v

/-- The callee's (or a closure's) frame and codomain as the run in place computes them
(`runBodyRef`'s `let`s; `bodyAt`'s at a global, whose captures are none). -/
noncomputable def bodyFrame (fres : Res) (cs : List Value) (rd : List (DeclInfo × Value)) (ds : List Term) (c : Term)
    (args : List Res) (s : SState) : SState × PiCod :=
  -- docs/31 D230: the closure value's forming state (`runBodyRef`)
  let s₀ := stateOf 0 (capsState (capsVals K ρ φ cs) (capsTys K ρ φ rd))
  let bs := bindsOf K ρ φ s₀ ds
  (callFrame K ρ φ cs rd fres (K.D.typeDecl (K.D.teleDecls (scopeOf s₀) ds) c) bs args s, codOf K ρ φ s₀ bs (ds.map Term.isRefTy) c)

/-- The end of `checkFix` at each leaf of the body (`Machine.checkFix`'s continuation): the value
returned whole, [Return] (`bodyReturns`), the frame popped with the value parked below, the value's
type converted to the goal. -/
def fixReturn (fuel : Nat) (self : Hint) (v T : Value) : M Unit := do
  Ochr.wholeReturned v
  Ochr.bodyReturns fuel s!"{self.name} returns it" v T [] ""
  Ochr.pushTempAt ((← Ochr.topIdx) - 1) v (some T) "checkFix"
  Ochr.popFrame fuel
  discard Ochr.popTemp
  let g := (← get).goal.getD .bot
  Ochr.trace fun _ => s!"[Def] {self.name}: path ends with type {T} against goal {g}"
  unless ← Ochr.conv fuel T g do
    Ochr.err s!"the body of {self.name} has type {T}, but the goal is {g}"

/-- **The generic state of a `fix`** (`checkFix`, docs/31 D73, D80), in the simulation form. `checkFix`
pushes a frame of cells for the borrow parameters (frame 0: `x° ↦ loan_l`) and one binding the
captures, `self` (the closure value `fv` at its Π-type) and each parameter (a fresh unknown at its
type, a borrow `borrow_l σ` of a fresh unknown for a borrow parameter, `⋆` for a proof), sets the goal
(the codomain at the parameters), and checks the body in tail position (`checkTail`, with the return
check `fixReturn` at each leaf; as an erased term where the function's calls are erased), then
restores the snapshot (`restoreKeep`). Checked on a recorded state (`F (x : &Nat) (n : Nat) : Nat`:
frame 0 `x° ↦ loan_0`, frame 1 `F`, `x ↦ borrow_0 σ0`, `n ↦ σ1`, the goal `Nat`). For every list of
arguments that are members along the closure's Π-type, the generic state is good and meets `CtxOk`
under an extension giving each parameter's unknown its argument, and is related to the reference's
frame for the body at those arguments (`bodyFrame`, from the empty state, `self` the closure's
meaning). As first stated: `Good` of `checkFix`'s END state for any typed assignment, which said
nothing of the body's run. -/
def generic_good_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (fv : Value) (cs : List Value) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value))
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.checkFix fuel fv cs (.fix self hs ds c dec body) capRec rd) st bh () st'),
    ∃ (stgen stend : MState) (erased : Bool) (bt : Nat),
      Runs (Ochr.withErasedIf erased (Ochr.checkTail (fuel - 1) body (fixReturn (fuel - 1) self))) stgen bt () stend ∧
      stgen.tailNext = false ∧
      ∀ (args : List Res), ArgsMember K.dm.read (meanV K ρ φ (.plain .err) (.tPi cs (.pi hs ds c) rd)).asTy args →
        ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π : Nat → Nat), ExtOk K ρ st stgen ρ' Δ' ∧
          Rel { K with Δ := Δ' } ρ' φ π stgen
            (bodyFrame K ρ' φ (meanV K ρ φ (.plain .err) fv, .plain (meanV K ρ φ (.plain .err) (.tPi cs (.pi hs ds c) rd)).asTy)
              cs rd ds c args (emptyState 0)).1 ∧
          stgen.goal.map (fun G => (meanV { K with Δ := Δ' } ρ' noFuture (.plain .err) G).asTy) =
            some ((bodyFrame K ρ' φ (meanV K ρ φ (.plain .err) fv, .plain (meanV K ρ φ (.plain .err) (.tPi cs (.pi hs ds c) rd)).asTy)
              cs rd ds c args (emptyState 0)).2.cod (args.map (·.1)))

/-- **`checkTail`** (a body checked in tail position, splitting at its matches, `fixReturn` or the
caller's continuation at each leaf), in the simulation form (docs/31 D80): from a related state, for
the given assignment, the world it selects reaches a leaf where the continuation ran; the leaf's
value and type are the reference's run of the whole body in tail position (`runT … true`, as
`bodyAt` and `runBodyRef` run it) at the goal's hint, with the value in flight, under an extension (the
splits' fields, the generalisations; the decisions aligned after it). As first stated: `⊑`, from the checker
state's image, the context fixed. -/
def checkTail_step_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (k : Value → Value → M Unit)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (s : SState) (π : Nat → Nat) (hs : Rel K ρ φ π st s) (htn : st.tailNext = false)
    (hD : DecTab K.D st')
    (bh : Nat) (h : Runs (Ochr.checkTail fuel t k) st bh () st'),
    ∃ (stl stl' : MState) (v T : Value) (bk : Nat), Runs (k v T) stl bk () stl' ∧
      SimConclT K ρ φ π st stl s (fun ρ' => runT K ρ' φ true (hintM K ρ st.goal) t) v (some T)

/-- [Fix] (`checkFix`) for a closure formed in a body (a local `fix`): an accepted `fix` means an
element of its Π-type (docs/18 Corollary 15). NOT for a definition: there the knot is cut by
`RunCtx.cur` (`Assembly.step_member_fix`, docs/31 D79). For a local closure the same circularity
stands through `Membership` of its `self` binding (docs/31 D73 item 5): not yet restated, not ready
for a prover. ([Rec]'s accepting direction, `recCheck_sound_stmt`, and [Const]'s, `checkConst_sound_stmt`,
were deleted: superseded by `recDecreases` with the knot's induction and by `step_member_const`.) -/
def checkFix_sound_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (fv : Value) (cs : List Value) (t : Term)
    (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value)) (fT : Value)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    -- `fT` is the fix's own Π-type (the pilot form's `∨` left `fT` free on one side; the defect
    -- class of `Regress/CloseCallStmt.lean`)
    (hT : ∃ self hs ds c r body, t = .fix self hs ds c r body ∧ fT = .tPi cs (.pi hs ds c) rd)
    (bh : Nat) (h : Runs (Ochr.checkFix fuel fv cs t capRec rd) st bh () st'),
    meanV K ρ φ (.plain .err) (.clo cs t rd) ∈ₛ[K.dm.read] (meanV K ρ φ (.plain .err) fT).asTy

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
    -- the call is the live form `Machine.evalAt` makes; that the decisions are the checker's is
    -- `CtxOk.dec` (no separate hypothesis: team lead's decision, 2026-11-21)
    (bh : Nat) (h : Runs (do
      let d ← withLive true (Ochr.declOf fuel false [] [] t)
      pure ((← Ochr.preFlags t d).getD (false, false))) st bh fl st'),
    K.D.flags (scopeOf (SM' K ρ st)) t = fl

/-- `Decisions.placeDecl` is `Decide.placeDecl`. -/
def placeDecl_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (d : DeclInfo)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (withLive true (Ochr.placeDecl fuel [] p)) st bh d st'),
    K.D.placeDecl (scopeOf (SM' K ρ st)) p = d

/-- `Decisions.declOf` is `Decide.declOf` (unchecked mode). -/
def declOf_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (d : DeclInfo)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
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
    (bh : Nat) (h : Runs (withLive true (Ochr.sortOf fuel (.tPi [] (.pi hs ds c) []))) st bh l st'),
    K.D.piSort (scopeOf (SM' K ρ st)) (.pi hs ds c) = l

/-- D84 [Join]: `Decisions.joinMoves` is `Decide.jdMoves` as `Machine.staticJoin` calls it (the
places already `⊥` at the match as its `entry`). -/
def joinMoves_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (entry ms : List Place) (t : Term)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (withLive true (Ochr.jdMoves fuel [] [] t entry)) st bh ms st'),
    K.D.joinMoves (scopeOf (SM' K ρ st)) entry t = ms

/-- D84 [Id-typestate]/[Obs-ref]: `Decisions.rePointed` is the `repointed` component of
`Decide.typeState`, as `Machine.idType` reads it. -/
def rePointed_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (t : Term) (ts : TypeState)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (withLive true (Ochr.typeState fuel t)) st bh ts st'),
    K.D.rePointed (scopeOf (SM' K ρ st)) t = ts.repointed

/-- `Decisions.typeDecl` is `Decide.typeDecl`, the reading of a type term (D19, R3: a closure's
frame binds its parameters at their domain terms' readings, `Decide.paramDecls`). -/
def typeDecl_aligned_stmt (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState) (T : Term) (d : DeclInfo)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (bh : Nat) (h : Runs (withLive true (Ochr.typeDecl fuel false [] [] T)) st bh d st'),
    K.D.typeDecl (scopeOf (SM' K ρ st)) T = d

end

end Ochr.Meaning.Steps
