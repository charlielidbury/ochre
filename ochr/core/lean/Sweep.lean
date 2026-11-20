import Ochr.Examples.Registry
import SweepProbes

/-!
# `lake exe sweep`: `Good`'s read-off clauses on the checker's own states (DEV TOOLING)

Not part of the checker, of its consistency statement or of the artefact: a development probe,
as `Tests.lean` is. It checks every example and case study the build asserts
(`Registry.programs ++ Registry.caseStudies`, 2,094 verdicts) in `located` mode with
`Config.recordStates` on, so that the log holds the whole machine state at each located term of
each declaration's own code (call depth 0), on entry to its evaluation and on a successful exit
(`LogEntry.state`), and it evaluates Bool mirrors of the purely syntactic clauses of the meaning
spine's `Good` on every recorded state.

Which states. On entry, the state as recorded. On an evaluated term's exit, the state with the
term's value counted as a temporary of the top frame, the spine's `MState.withTemp` (a step's
result is read through it, `Good (st.withTemp v)`); a violation that only that value makes is
labelled so. A tail term's exit (`checkTail`) comes after its continuation consumed the result,
which is then in flight with no record of it: those states are counted, not checked. States at a
call depth above 0 (a callee's body, a sealed program's re-run) are not located, so not recorded:
a callee's generic call is swept in its own declaration, its instance runs are not.

The clauses are those of branch `spine` at a3e22c78, with (WF8), (WF12) and (iii) restated after
this sweep's first run (spine, 2026-11-21: see each mirror) (`Ochr/Meaning/WF.lean`; the helpers in
`SState.lean`, `State.lean`, `Value.lean`, `Run.lean`; clause (iii) from `Steps/DropOne.lean`,
`lentPrefix_none_of_noop`), read there and copied here, since `spine` is not on `main`. Each mirror
quotes the statement it mirrors and says where it is weaker or stronger. No step lemma of the spine
has its `Good` conclusion proved (`Steps/WF.lean` is `sorry`'d), so every syntactic clause is one
that no step has proved preserved.

Not mirrored, because they need meanings: (WF7) (the level of a borrow type's content's meaning),
`TypedAssignment` and `Membership`. (WF5) `ArgsLoanFree` is a property of a run at a call point, not
of a state. (WF13) was deleted from `Good` (spine ffc4458e, docs/31 D32: a data value describes
itself).

Two deliberately false clauses (`planted…`) guard against a vacuous sweep: the run fails unless
both are reported.

Usage: `lake exe sweep [Block …]` (all blocks if none named), `lake exe sweep --probes` (the
adversarial programs of `SweepProbes.lean`, written to make clauses' premises arise), `lake exe sweep --ends`
(`--ends --probes`: from each recorded state, end each live borrow and report new unknowns and records, docs/31 D35), or `Sweep.sweep [("B", B)]` from a
file that imports this module and declares the `ochr` block `B` (a minimal program). Exit 0 iff
every real clause holds on every state, both planted clauses are violated, and every verdict is as
expected.
-/

namespace Sweep
open Ochr Ochr.Test Ochr.Surface Ochr.Registry

/-! ## The spine's helpers, copied -/

/-- `Ochr.Meaning.Site` (SState.lean): a place a borrow is lent at. -/
structure Site where
  pos : Pos
  path : List Step
  fill : Bool

/-- `Step.key` (SState.lean). -/
def stepKey : Step → Option (Nat × Nat)
  | .deref => none
  | .proj i => some (0, i)
  | .field g => some (g.ctor, g.idx)

/-- `pathKey` (SState.lean). -/
def pathKey (ψ : List Step) : List (Option (Nat × Nat)) := ψ.map stepKey

mutual
/-- `Value.sitesOf` (SState.lean), verbatim. -/
def sitesOf (l : Nat) (pos : Pos) (path : List Step) : Value → List Site
  | .loan m => if m = l then [⟨pos, path, false⟩] else []
  | .gloan m w => if m = l then [⟨pos, path, true⟩] else sitesOf l pos path w
  | .sealed t => if (Value.sealed t).hasLoan l then [⟨pos, path, true⟩] else []
  | .borrow _ w => sitesOf l pos (path ++ [.deref]) w
  | .succ w => sitesOf l pos (path ++ [.proj 0]) w
  | .ind ty c _ _ fs => sitesOfFields l pos path ty c 0 fs
  | _ => []

/-- `Value.sitesOfFields` (SState.lean), verbatim. -/
def sitesOfFields (l : Nat) (pos : Pos) (path : List Step) (ty : String) (c : Nat) :
    Nat → List Value → List Site
  | _, [] => []
  | i, w :: ws => sitesOf l pos (path ++ [.field ⟨ty, c, i, ""⟩]) w ++ sitesOfFields l pos path ty c (i + 1) ws
end

/-- `Env.sitesOf` (SState.lean): the sites of the borrow `l` in Ω. -/
def envSitesOf (env : Env) (l : Nat) : List Site :=
  (allPos env).flatMap fun p => sitesOf l p [] (valAt env p)

mutual
/-- `Value.outerLoans` (WF.lean), verbatim. -/
def outerLoans : Value → List Nat
  | .loan l => [l]
  | .succ w | .tRef w | .borrow _ w | .gloan _ w => outerLoans w
  | .tEq A a b => outerLoans A ++ outerLoans a ++ outerLoans b
  | .clo cs _ _ | .tPi cs _ _ => outerLoansList cs
  | .ind _ _ _ ps fs => outerLoansList ps ++ outerLoansList fs
  | .tInd _ fs => outerLoansList fs
  | _ => []

/-- `Value.outerLoansList` (WF.lean), verbatim. -/
def outerLoansList : List Value → List Nat
  | [] => []
  | v :: vs => outerLoans v ++ outerLoansList vs
end

/-- `Value.badCapture` (WF.lean), verbatim. -/
def badCapture : Value → Bool
  | .clo cs _ _ | .tPi cs _ _ => cs.any fun c => c.hasBorrow || c.hasHole
  | .sealed t => !t.freeVars.isEmpty
  | _ => false

/-- `Value.bareCtor` (Value.lean), verbatim. -/
def bareCtor (Γ : List IndDecl) : Value → Bool
  | .ind ty _ _ [] _ => match Γ.find? (·.name == ty) with | some d => !d.params.isEmpty | none => false
  | _ => false

/-- `Env.shape` (State.lean). -/
def shape (env : Env) (p : Pos) : Option Nat :=
  match valAt env p with
  | .borrow l _ => some l
  | _ => none

/-! ## Reading a state -/

/-- The labels `Value.holdsBorrow` can find in a value (through borrows and `S`): every `l` with
`v.holdsBorrow l = true` is among them. -/
def borrowLabels : Value → List Nat
  | .borrow m w => m :: borrowLabels w
  | .succ w => borrowLabels w
  | _ => []

/-- Exactly the `l` with `liveLoan env l = true` (main's `liveLoan`, `Obs.lean`), without repeats.
The spine's `SState.liveLabels` are the labels of the shape (a borrow at the top of a position);
under (WF1) the two agree. -/
def liveLabels (env : Env) : List Nat :=
  ((allPos env).flatMap fun p => borrowLabels (valAt env p)).eraseDups.filter (liveLoan env)

/-- Every site of every live borrow, with its label. -/
def liveSites (env : Env) : List (Nat × Site) :=
  (liveLabels env).flatMap fun l => (envSitesOf env l).map (l, ·)

/-- `Env.values` (WF.lean), with each value's position. -/
def posVals (env : Env) : List (Pos × Value) := (allPos env).map fun p => (p, valAt env p)

/-- Every binding of every frame, `(f, i, b)`: what `st.env[f]?.bind (·.binds[i]?) = some b` ranges over. -/
def bindings (env : Env) : List (Nat × Nat × Binding) :=
  (List.range env.size).flatMap fun f =>
    let bs := env[f]!.binds
    (List.range bs.size).map fun i => (f, i, bs[i]!)

def posName (env : Env) : Pos → String
  | .bind f i => s!"{env[f]!.binds[i]!.hint.name} (binding {f}.{i})"
  | .temp f i => s!"temporary {f}.{i}"

def posKind : Pos → String
  | .bind .. => "a binding"
  | .temp .. => "a temporary"

def clip (s : String) (n : Nat := 240) : String :=
  if s.length ≤ n then s else (s.take n).toString ++ "…"

/-- What a site is: the value `follow` finds at its path (a mark, a sealed program, a loan). -/
def siteForm (env : Env) (x : Site) : String :=
  match (valAt env x.pos).follow x.path with
  | some (.gloan ..) => "a mark"
  | some (.sealed _) => "a sealed fill"
  | some (.loan _) => "a loan"
  | some v => s!"`{clip v.pp 40}`"
  | none => "(no value at its path)"

def ppPath (ψ : List Step) : String :=
  if ψ.isEmpty then "the whole position" else
  "".intercalate (ψ.map fun | .deref => "*" | .proj i => s!".{i}" | .field g => s!".{g.ctor}:{g.idx}")

/-- The state, printed: every frame's bindings (name, stored or deferred type, value) and
temporaries, the unknowns' types, the goal, the records, the live borrows. -/
def ppState (st : MState) : String := Id.run do
  let mut out : Array String := #[]
  for h : f in [0:st.env.size] do
    let fr := st.env[f]
    out := out.push s!"  frame {f}:"
    for h : i in [0:fr.binds.size] do
      let b := fr.binds[i]
      let ty := match b.ty, b.lazyTy with
        | some T, _ => clip T.pp 120
        | none, some (P, ws, j) => s!"(deferred: param {j} of {clip P.pp 80} at {clip (", ".intercalate (ws.map Value.pp)) 80})"
        | none, none => "(no type)"
      out := out.push s!"    {i} {b.hint.name} : {ty} = {clip b.val.pp}"
    for h : i in [0:fr.temps.size] do
      out := out.push s!"    t{i} = {clip fr.temps[i].pp}"
  let tys := (List.range st.absTy.size).map fun σ => s!"σ{σ} : {clip st.absTy[σ]!.pp 80}"
  out := out.push s!"  unknowns: {clip (", ".intercalate tys) 1200}"
  out := out.push s!"  goal: {match st.goal with | some G => clip G.pp | none => "none"}"
  out := out.push s!"  generalisation records: {clip (", ".intercalate (st.neutrals.map fun (n, σ) => s!"{n.pp} := σ{σ}")) 600}"
  out := out.push s!"  η records: {clip (", ".intercalate (st.etaRefs.map fun (σ, v) => s!"σ{σ} := {v.pp}")) 600}"
  out := out.push s!"  live borrows: {liveLabels st.env}; nextLoan {st.nextLoan}, nextAbs {st.nextAbs}; privateDepth {st.privateDepth}, typing {st.typing}"
  pure ("\n".intercalate out.toList)

/-! ## Clauses -/

/-- A violation in one state: its kind (what the report groups by) and where in the state. -/
structure Viol where
  kind : String
  detail : String

/-- A clause: its name, whether it is planted (deliberately false), the premises counted (states
where the clause has something to say), and its check, which lists the violations in a state. -/
structure Clause where
  name : String
  planted : Bool := false
  /-- A report (the slice): its cases are listed with their smallest programs, and it never fails
  the sweep (neither when it has cases nor when it has none). -/
  report : Bool := false
  premises : List (String × (MState → Bool)) := []
  check : MState → List Viol

/-! ### (i) (WF11): types and records hold no loan -/

/-- A loan or a lent mark: `(∃ l, v.hasLoan l = true) ↔ v.anyAtom isLoanAtom = true`, since main's
`Value.hasLoan l v` is `v.anyAtom fun | .loan m | .gloan m _ => m == l | _ => false` (Basic.lean). -/
def isLoanAtom : Value → Bool
  | .loan _ | .gloan _ _ => true
  | _ => false

def loanForm (v : Value) : String :=
  if v.anyAtom (fun | .loan _ => true | _ => false) then "a loan" else "a lent mark"

/-- The types and records (WF11) ranges over, each with what it is and where: every binding's
stored type, its deferred type's Π-type and arguments, every unknown's type, the goal, every
generalisation record's program and every η record's value. -/
def typesAndRecords (st : MState) : List (String × String × Value) :=
  ((bindings st.env).flatMap fun (f, i, b) =>
    (match b.ty with | some T => [("a stored type", s!"{b.hint.name} (binding {f}.{i})", T)] | none => []) ++
    (match b.lazyTy with
      | some (P, ws, _) => ("a deferred type", s!"{b.hint.name} (binding {f}.{i})", P) ::
          ws.map fun w => ("a deferred type's argument", s!"{b.hint.name} (binding {f}.{i})", w)
      | none => [])) ++
  ((List.range st.absTy.size).map fun σ => ("the type of an unknown", s!"σ{σ}", st.absTy[σ]!)) ++
  (match st.goal with | some G => [("the goal", "", G)] | none => []) ++
  (st.neutrals.map fun (n, σ) => ("a generalisation record", s!":= σ{σ}", n)) ++
  (st.etaRefs.map fun (σ, v) => ("an η record", s!"σ{σ} :=", v))

/-- A type that mentions a run-time value: an unknown, data, a sealed program, a function (not
only type formers). -/
def isValueAtom : Value → Bool
  | .tNat | .tUnit | .tEq .. | .tRef _ | .tPi .. | .sort _ | .tInd .. => false
  | _ => true

/-- (WF11), mirrored EXACTLY (the same five conjuncts over the same ranges; `∀ l, T.hasLoan l = false`
is `!T.anyAtom isLoanAtom`):
```
def WF11 (st : MState) : Prop :=
  (∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
    (∀ T, b.ty = some T → ∀ l, T.hasLoan l = false) ∧
    (∀ P ws j, b.lazyTy = some (P, ws, j) → ∀ l, P.hasLoan l = false ∧ ∀ w ∈ ws, w.hasLoan l = false)) ∧
  (∀ T ∈ st.absTy.toList, ∀ l, T.hasLoan l = false) ∧
  (∀ G, st.goal = some G → ∀ l, G.hasLoan l = false) ∧
  (∀ n σ, (n, σ) ∈ st.neutrals → ∀ l, n.hasLoan l = false) ∧
  (∀ σ v, (σ, v) ∈ st.etaRefs → ∀ l, v.hasLoan l = false)
``` -/
def wf11 : Clause where
  name := "(i) (WF11) no stored type, type of an unknown, goal or record holds a loan or a lent mark"
  premises := [
    ("a type (stored, deferred, an unknown's, the goal) mentions a run-time value", fun st =>
      (typesAndRecords st).any fun (c, _, v) => !c.endsWith "record" && v.anyAtom isValueAtom),
    ("... and a borrow is live", fun st =>
      !(liveLabels st.env).isEmpty &&
      (typesAndRecords st).any fun (c, _, v) => !c.endsWith "record" && v.anyAtom isValueAtom),
    ("a generalisation or η record is in force", fun st => !st.neutrals.isEmpty || !st.etaRefs.isEmpty)]
  check st := (typesAndRecords st).filterMap fun (c, w, v) =>
    if v.anyAtom isLoanAtom then some ⟨s!"{c} holds {loanForm v}", s!"{c} {w}: {clip v.pp}"⟩ else none

/-! ### (ii) (WF12): at a live fill, nothing else is lent -/

/-- (WF12), mirrored (restated a second time, docs/31 D39, after main's D93 made
`LentUnder.TwoParts` accepted: two live borrows filled at one place):
```
def WF12 (env : Env) : Prop :=
  ∀ k l, liveLoan env k = true → liveLoan env l = true →
    ∀ x ∈ Env.sitesOf env k, x.fill = true → ∀ y ∈ Env.sitesOf env l, y.pos = x.pos →
      (pathKey x.path).isPrefixOf (pathKey y.path) = true →
      ∃ z ∈ Env.sitesOf env l, z.pos = x.pos ∧ pathKey z.path = pathKey x.path ∧ z.fill = true
```
Under a live fill only borrows filled there. The labels range over `liveLabels env`. The D33 form
("no other live borrow is lent at the fill's path or below") is kept as a premise, counted. -/
def wf12Viols (env : Env) : List Viol := Id.run do
  let live := (liveLabels env).map fun l => (l, envSitesOf env l)
  let mut out : Array Viol := #[]
  for (k, xs) in live do
    for x in xs do
      if x.fill then
        for (l, ys) in live do
          for y in ys do
            if y.pos == x.pos && (pathKey x.path).isPrefixOf (pathKey y.path) then
              unless ys.any (fun z => z.pos == x.pos && pathKey z.path == pathKey x.path && z.fill) do
                out := out.push ⟨s!"{siteForm env y} of a live borrow at or under {siteForm env x} of another, not filled there, at {posKind x.pos}",
                  s!"{posName env x.pos}: borrow {k}'s fill at {ppPath x.path}, borrow {l}'s site at {ppPath y.path}"⟩
  pure out.toList

/-- The D33 form's violations (another live borrow with any site at or under a live fill). -/
def wf12D33 (env : Env) : Bool :=
  let ss := liveSites env
  ss.any fun (k, x) => x.fill && ss.any fun (l, y) => l != k && y.pos == x.pos && (pathKey x.path).isPrefixOf (pathKey y.path)

def wf12 : Clause where
  name := "(ii) (WF12) under a live fill, only borrows filled at its path"
  premises := [
    ("a live fill exists", fun st => (liveSites st.env).any (·.2.fill)),
    ("(the D33 form's violation) another live borrow has a site at or under a live fill", fun st => wf12D33 st.env),
    ("another live borrow has a site at the same position as a live fill", fun st =>
      let ss := liveSites st.env
      ss.any fun (k, x) => x.fill && ss.any fun (l, y) => l != k && y.pos == x.pos)]
  check st := wf12Viols st.env

/-! ### (WF14), formerly (iii): no live fill above a moved part (`lentPrefix_none_of_noop`) -/

mutual
/-- The paths `ψ` of a value at which `Value.follow` gives `⊥` (`false`) or `⋆` (`true`), at their
canonical steps (`*` into a borrow, `.0` into `S`, `.field ⟨ty, c, i, ""⟩` into a constructor value,
as `sitesOf` writes them): every path `follow` sends to `⊥` or `⋆` has the `pathKey` of one of
these, or extends a `⋆` one inside the `⋆` (whose further prefixes hold no site). `direct` says no
mark was passed at this very path: `follow ψ` returns the mark there, not its content, so
`lent_k ⊥` is not a `⊥` part; but `follow` steps through a mark into `⋆` (`stepV`), so `lent_k ⋆`
at `ψ` gives the `⋆` part `ψ ++ [.0]`, whose strict prefix `ψ` carries the mark. -/
def noopParts : Value → List Step → Bool → List (List Step × Bool)
  | .bot, ψ, d => if d then [(ψ, false)] else []
  | .proof, ψ, d => if d then [(ψ, true)] else [(ψ ++ [.proj 0], true)]
  | .gloan _ w, ψ, _ => noopParts w ψ false
  | .borrow _ w, ψ, _ => noopParts w (ψ ++ [.deref]) true
  | .succ w, ψ, _ => noopParts w (ψ ++ [.proj 0]) true
  | .ind ty c _ _ fs, ψ, _ => noopPartsFields ty c ψ 0 fs
  | _, _, _ => []

def noopPartsFields (ty : String) (c : Nat) (ψ : List Step) : Nat → List Value → List (List Step × Bool)
  | _, [] => []
  | i, w :: ws => noopParts w (ψ ++ [.field ⟨ty, c, i, ""⟩]) true ++ noopPartsFields ty c ψ (i + 1) ws
end

/-- `lentPrefix` (Run.lean) on the state the relation makes of `env` (its sites `Env.sitesOf`, its
live labels the live borrows): the shortest strict prefix of `steps` at which a live label has a
site at `pos`, with that label and site.
```
def lentPrefix (s : SState) (pos : Pos) (steps : List Step) : Option (List Step) :=
  ((List.range steps.length).map steps.take).find? fun ψ =>
    s.liveLabels.any (s.reached pos fun ψ' => pathKey ψ' == pathKey ψ)
``` -/
def lentPrefix (ss : List (Nat × Site)) (pos : Pos) (steps : List Step) : Option (List Step × Nat × Site) :=
  ((List.range steps.length).map steps.take).findSome? fun ψ =>
    (ss.find? fun (_, x) => x.pos == pos && pathKey x.path == pathKey ψ).map fun (l, x) => (ψ, l, x)

/-- (WF14) (`WF.lean`, docs/31 D43), first swept as clause (iii), the conclusion of
`lentPrefix_none_of_noop` (Steps/DropOne.lean) made a state clause; the Lean clause is this mirror's
form exactly (strict prefixes by `pathKey`, at every path `follow` sends to `⊥`): at every `⊥` part of every position, no live borrow has a site at a strict prefix.
```
theorem lentPrefix_none_of_noop (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hnoop : (valAt st.env pos).follow q.steps.2 = some .bot) :
    lentPrefix s pos q.steps.2 = none
```
Restated from the first run's form, which also asked it at `⋆` parts and was refuted there (a place
lent whole keeps its proof field under the mark); the `⋆` parts under a live borrow's site are now
counted as a premise. STRONGER than the theorem: asked at every `⊥` part of every position (bindings and
temporaries), where the theorem asks it only at the places the join drops (`resolve s q`, a place
some arm moves). The relation's `sites` and holders clauses identify `s.lent` with `Env.sitesOf`
and `s.liveLabels` with the live borrows, which is what this reads. A loan or a sealed fill can
only be a site at a strict prefix of an existing path if `follow` went through it, which it never
does, so every violation is at a mark (`lent_k`). -/
def noopViols (env : Env) : List Viol := Id.run do
  let ss := liveSites env
  let mut out : Array Viol := #[]
  for (p, v) in posVals env do
    for (ψ, prf) in noopParts v [] true do
      if prf then continue
      if let some (pre, l, x) := lentPrefix ss p ψ then
        out := out.push ⟨s!"a {if prf then "⋆" else "⊥"} part strictly under {siteForm env x} of a live borrow, at {posKind p}",
          s!"{posName env p}: the part at {ppPath ψ}, borrow {l}'s site at {ppPath pre}"⟩
  pure out.toList

def noopClause : Clause where
  name := "(WF14) no live fill sits above a moved part"
  premises := [
    ("(not a violation since the restatement) a ⋆ part lies strictly under a live borrow's site", fun st =>
      let ss := liveSites st.env
      (posVals st.env).any fun (p, v) =>
        (noopParts v [] true).any fun (ψ, prf) => prf && (lentPrefix ss p ψ).isSome),
    ("a ⊥ part lies at a position holding a live fill (moved under or beside one)", fun st =>
      let ss := liveSites st.env
      (posVals st.env).any fun (p, v) =>
        ss.any (fun (_, x) => x.fill && x.pos == p) && (noopParts v [] true).any (!·.2)),
    ("a ⋆ part lies at a position holding a live fill", fun st =>
      let ss := liveSites st.env
      (posVals st.env).any fun (p, v) =>
        ss.any (fun (_, x) => x.fill && x.pos == p) && (noopParts v [] true).any (·.2)),
    ("a ⊥ or ⋆ part lies strictly under a mark of any label, live or not", fun st =>
      (posVals st.env).any fun (_, v) =>
        v.anyAtom fun | .gloan _ w => !(noopParts w [] false).isEmpty | _ => false),
    ("(not covered by the clause) a live borrow's mark directly over ⊥", fun st =>
      let live := liveLabels st.env
      (posVals st.env).any fun (_, v) => v.anyAtom fun | .gloan k .bot => live.contains k | _ => false)]
  check st := noopViols st.env

/-! ### The other syntactic clauses of `Good` -/

/-- (WF1), mirrored EXACTLY:
```
def WF1 (env : Env) : Prop :=
  (∀ p ∈ allPos env, match valAt env p with
    | .borrow _ w => ¬ w.hasBorrow
    | v => ¬ v.hasBorrow) ∧
  ∀ p ∈ allPos env, ∀ q ∈ allPos env, ∀ l, Env.shape env p = some l → Env.shape env q = some l → p = q
``` -/
def wf1 : Clause where
  name := "(WF1) a borrow is a whole position's value, and each label has at most one"
  check st :=
    let env := st.env
    let ps := allPos env
    (ps.filterMap fun p => match valAt env p with
      | .borrow _ w => if w.hasBorrow then some ⟨s!"a borrow inside a borrow's content, at {posKind p}", posName env p⟩ else none
      | v => if v.hasBorrow then some ⟨s!"a borrow inside a value, at {posKind p}", posName env p⟩ else none) ++
    (ps.flatMap fun p => ps.filterMap fun q =>
      match shape env p, shape env q with
      | some l, some l' => if l == l' && !(p == q) then some ⟨"two borrows of one label", s!"borrow {l} at {posName env p} and {posName env q}"⟩ else none
      | _, _ => none)

/-- (WF2), mirrored EXACTLY (`count l ≤ 1` checked for every label that occurs):
```
def WF2 (env : Env) : Prop :=
  (∀ v ∈ Env.values env, ∀ l ∈ v.outerLoans, liveLoan env l = true) ∧
  ∀ l, ((Env.values env).flatMap Value.outerLoans).count l ≤ 1
``` -/
def wf2 : Clause where
  name := "(WF2) every loan outside a sealed program is live and occurs once"
  check st :=
    let env := st.env
    let all := (posVals env).flatMap fun (_, v) => outerLoans v
    ((posVals env).flatMap fun (p, v) => (outerLoans v).filterMap fun l =>
      if liveLoan env l then none else some ⟨s!"a loan of an ended borrow, at {posKind p}", s!"loan {l} in {posName env p}"⟩) ++
    (all.eraseDups.filterMap fun l =>
      if all.count l ≤ 1 then none else some ⟨"a loan occurring twice", s!"loan {l}, {all.count l} times"⟩)

/-- (WF3), mirrored EXACTLY: the relation has finitely many pairs, so it is well-founded iff it has
no cycle, which the fixpoint below decides (a label is accessible once every label under it is).
```
def loanUnder (env : Env) (l m : Nat) : Prop :=
  ∃ p ∈ allPos env, ∃ w, valAt env p = .borrow m w ∧ l ∈ w.loans
def WF3 (env : Env) : Prop := WellFounded (loanUnder env)
``` -/
def wf3 : Clause where
  name := "(WF3) \"a loan of l lies in borrow m's content\" is acyclic"
  check st := Id.run do
    let edges := (posVals st.env).flatMap fun (_, v) => match v with
      | .borrow m w => w.loans.eraseDups.map fun l => (l, m)
      | _ => []
    let nodes := (edges.flatMap fun (l, m) => [l, m]).eraseDups
    let mut acc : List Nat := []
    for _ in [0:nodes.length + 1] do
      acc := nodes.filter fun x => edges.all fun (y, x') => x' != x || acc.contains y
    let bad := nodes.filter (!acc.contains ·)
    if bad.isEmpty then return [] else return [⟨"a cycle of loans under borrows", s!"labels {bad}"⟩]

/-- (WF4), mirrored EXACTLY:
```
def WF4 (env : Env) : Prop := ∀ v ∈ Env.values env, ¬ v.anyAtom Value.badCapture
``` -/
def wf4 : Clause where
  name := "(WF4) closures capture no borrow and no ⊥; sealed programs are closed"
  check st := (posVals st.env).filterMap fun (p, v) =>
    if v.anyAtom badCapture then some ⟨s!"a bad capture or an open sealed program, at {posKind p}", posName st.env p⟩ else none

def absAbove (n : Nat) (v : Value) : Bool := v.anyAtom fun | .abs σ => σ ≥ n | _ => false

/-- (WF6), mirrored (`∀ σ, v.hasAbs σ → σ < n` is `!absAbove n v`):
```
def WF6 (st : MState) : Prop :=
  (∀ σ, st.Refd σ → σ < st.absTy.size) ∧
  (∀ T ∈ st.absTy.toList, ∀ σ, T.hasAbs σ → σ < st.absTy.size) ∧
  (∀ σ r, (σ, r) ∈ st.refs → σ < st.absTy.size ∧ ∀ τ, r.hasAbs τ → τ < st.absTy.size) ∧
  st.absTy.size = st.nextAbs ∧
  ∀ v ∈ Env.values st.env, ∀ l ∈ v.loans, l < st.nextLoan
```
`MState.Refd` is mirrored by the places it reads (values of Ω, stored and deferred types, the goal,
the generalisation and η records, each with its own unknown), its last case (the types of
referenced unknowns) by the second part, which asks it of every unknown's type: so the mirror is
exact. The counter conjunct was `≤` at a3e22c78; the spine made it `=` (a fresh unknown is named
by the counter and typed at index `absTy.size`, `Regress/GenNeutralContent.lean`). The first part
was "every unknown in a value of Ω" and the third "in the goal" until the spine's FreshBound
(2026-11-21: a record naming the counter, `Regress/FreshBound.lean`). -/
def wf6 : Clause where
  name := "(WF6) names: every unknown has a type, every name is below its counter"
  check st :=
    let n := st.absTy.size
    let a := absAbove n
    ((posVals st.env).filterMap fun (p, v) => if a v then some ⟨"an unknown without a type, in Ω", posName st.env p⟩ else none) ++
    ((bindings st.env).filterMap fun (_, _, b) =>
      if (b.ty.map a).getD false then some ⟨"an unknown without a type, in a stored type", b.hint.name⟩ else none) ++
    ((bindings st.env).filterMap fun (_, _, b) =>
      if (match b.lazyTy with | some (P, ws, _) => a P || ws.any a | none => false) then
        some ⟨"an unknown without a type, in a deferred type", b.hint.name⟩ else none) ++
    (st.absTy.toList.filterMap fun T => if a T then some ⟨"an unknown without a type, in an unknown's type", clip T.pp⟩ else none) ++
    (match st.goal with | some G => if a G then [⟨"an unknown without a type, in the goal", clip G.pp⟩] else [] | none => []) ++
    (st.neutrals.filterMap fun (v, σ) => if a v || σ ≥ n then some ⟨"an unknown without a type, in a generalisation record", s!"{clip v.pp} := σ{σ}"⟩ else none) ++
    (st.etaRefs.filterMap fun (σ, v) => if a v || σ ≥ n then some ⟨"an unknown without a type, in an η record", s!"σ{σ} := {clip v.pp}"⟩ else none) ++
    (st.refs.filterMap fun (σ, v) => if a v || σ ≥ n then some ⟨"an unknown without a type, in a refinement", s!"σ{σ} := {clip v.pp}"⟩ else none) ++
    (if n = st.nextAbs then [] else [⟨"the counter of unknowns is not the number typed", s!"{n} typed, counter {st.nextAbs}"⟩]) ++
    ((posVals st.env).flatMap fun (p, v) => v.loans.filterMap fun l =>
      if l < st.nextLoan then none else some ⟨"a label at or above the counter", s!"{l} in {posName st.env p}"⟩)

/-- `Value.isRefV` (WF.lean), verbatim. -/
def isRefV : Value → Bool
  | .tRef _ => true
  | _ => false

/-- `Value.refMisplaced` (WF.lean), verbatim. -/
def refMisplaced (v : Value) : Bool := v.anyAtom fun
  | .tRef A => isRefV A
  | .tInd _ ps => ps.any isRefV
  | .ind _ _ _ ps _ => ps.any isRefV
  | .tEq A a b => isRefV A || isRefV a || isRefV b
  | _ => false

/-- (WF8), mirrored EXACTLY:
```
def WF8 (st : MState) : Prop :=
  (∀ v ∈ Env.values st.env, v.refMisplaced = false) ∧
  (∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
    ∀ T : Value, b.ty = some T → T.refMisplaced = false) ∧
  (∀ T ∈ st.absTy.toList, T.refMisplaced = false) ∧
  (∀ G, st.goal = some G → G.refMisplaced = false)
```
Restated from the first run's form ("& only at the top of a declared type", false at a borrow type
in flight and at a stuck block's function, both with `&` at the top of a type); the old form's
violations are counted as a premise. -/
def refTopOk (T : Value) : Bool := match T with | .tRef A => !A.typeHasRef | T => !T.typeHasRef

def wf8 : Clause where
  name := "(WF8) & applied to no borrow type, and never inside a data type or an equation"
  premises := [
    ("(not a violation since the restatement) a borrow type inside a value, or not at the top of a stored type, an unknown's type or the goal", fun st =>
      (posVals st.env).any (fun (_, v) => v.typeHasRef) ||
      (bindings st.env).any (fun (_, _, b) => match b.ty with | some T => !refTopOk T | none => false) ||
      st.absTy.toList.any (!refTopOk ·) ||
      (match st.goal with | some G => !refTopOk G | none => false))]
  check st :=
    ((posVals st.env).filterMap fun (p, v) => if refMisplaced v then some ⟨s!"a borrow type out of place inside a value, at {posKind p}", s!"{posName st.env p}: {clip v.pp}"⟩ else none) ++
    ((bindings st.env).filterMap fun (f, i, b) => match b.ty with
      | some T => if refMisplaced T then some ⟨"a borrow type out of place in a stored type", s!"{b.hint.name} (binding {f}.{i}): {clip T.pp}"⟩ else none
      | none => none) ++
    (st.absTy.toList.filterMap fun T => if refMisplaced T then some ⟨"a borrow type out of place in an unknown's type", clip T.pp⟩ else none) ++
    (match st.goal with | some G => if refMisplaced G then [⟨"a borrow type out of place in the goal", clip G.pp⟩] else [] | none => [])

/-- (WF9), mirrored EXACTLY: `MState.posTyM … st p` is `some` exactly at a binding with a stored
type or a deferred one (State.lean: `some T, _ => some …`, `none, some (P, ws, j) => some …`,
`none, none => none`, a temporary `none`), whatever the meanings.
```
def WF9 (ρ : Assignment) (st : MState) : Prop :=
  ∀ p ∈ allPos st.env, (valAt st.env p).outerLoans ≠ [] → ∃ T, MState.posTyM dm C Γ ρ st p = some T
``` -/
def wf9 : Clause where
  name := "(WF9) a loan outside a sealed program sits at a typed position"
  check st := (posVals st.env).filterMap fun (p, v) =>
    if (outerLoans v).isEmpty then none else
    let typed := match p with
      | .bind f i => match st.env[f]?.bind (·.binds[i]?) with
        | some b => b.ty.isSome || b.lazyTy.isSome
        | none => false
      | .temp .. => false
    if typed then none else some ⟨s!"a loan at an untyped {match p with | .bind .. => "binding" | .temp .. => "temporary"}",
      s!"{posName st.env p} = {clip v.pp}"⟩

/-- (WF10), mirrored EXACTLY, reading the model's declarations `Γ` as the state's `inds`:
```
def WF10 (st : MState) : Prop := ∀ v ∈ Env.values st.env, v.anyAtom (Value.bareCtor Γ) = false
``` -/
def wf10 : Clause where
  name := "(WF10) every constructor value records its parameters"
  check st := (posVals st.env).filterMap fun (p, v) =>
    if v.anyAtom (bareCtor st.inds) then some ⟨s!"a constructor value without its parameters, at {posKind p}", posName st.env p⟩ else none

/-! ### (WF16), first (H): sealed programs read no hint at their tails (`mean_updAt_botS`, docs/31 D45, D47) -/

mutual
/-- `Term.tailHintFree` (`HintIndep.lean`), mirrored EXACTLY. -/
def tailHintFree (Γ : List IndDecl) : Term → Bool
  | .letIn _ _ w => tailHintFree Γ w
  | .seq _ w => tailHintFree Γ w
  | .matchNat _ z u => tailHintFree Γ z && tailHintFree Γ u
  | .matchInd _ _ arms => armsHintFree Γ arms
  | .ctor ty _ _ ps _ =>
    !ps.isEmpty || (match Γ.find? (·.name == ty) with | some d => d.params.isEmpty | none => true)
  | .val v => topHintFree Γ v
  | .prim n [.place _] => n == "peek" || n == "clone"
  | .prim _ _ => false
  | _ => true

def armsHintFree (Γ : List IndDecl) : List (Hint × Term) → Bool
  | [] => true
  | (_, t) :: rest => tailHintFree Γ t && armsHintFree Γ rest

/-- `Value.topHintFree`, mirrored EXACTLY. -/
def topHintFree (Γ : List IndDecl) : Value → Bool
  | .borrow _ w => topHintFree Γ w
  | .gloan _ w => topHintFree Γ w
  | .sealed t => tailHintFree Γ t
  | .ind ty _ _ [] _ => (match Γ.find? (·.name == ty) with | some d => d.params.isEmpty | none => true)
  | _ => true
end

/-- (H): no sealed program anywhere in Ω (inside sealed programs and code included) reads the hint
at a tail: `∀ v ∈ Env.values st.env, v.anyAtom (fun a => a.isSealed && !a.topHintFree Γ) = false`,
what the write of `⊥` with sealed siblings needs (`botWrite_hyps`). (WF16) in `WF.lean`, exactly. -/
def hintFreeSealed : Clause where
  name := "(WF16) every sealed program in Ω reads no hint at its tails"
  premises := [
    ("a sealed program in Ω", fun st => (posVals st.env).any fun (_, v) =>
      v.anyAtom fun | .sealed _ => true | _ => false),
    ("a sealed program in a constructor value's field", fun st => (posVals st.env).any fun (_, v) =>
      v.anyAtom fun | .ind _ _ _ _ fs => fs.any (fun | .sealed _ => true | _ => false) | _ => false)]
  check st := (posVals st.env).filterMap fun (p, v) =>
    if v.anyAtom (fun a => match a with | .sealed _ => !topHintFree st.inds a | _ => false) then
      some ⟨s!"a sealed program whose tail reads the hint, at {posKind p}", s!"{posName st.env p} = {clip v.pp}"⟩
    else none

/-! ### (WF15), first (RD): no loan or mark in a recorded reading (`sealed_loanFree`; docs/31 D46) -/

/-- (WF15) (`WF.lean`, as `∀ v ∈ values, ∀ l, v.anyAtom (Value.rdLoan l) = false`, which is this
for every label at once): no closure or Π-type anywhere in Ω (inside sealed programs and code included) records a
declared type (`rd`, D82) holding a loan or a mark. `Value.loans` (the checker's) does not collect
them and `Value.hasLoan` (an `anyAtom`) does, so without it a sealed program can have a site
(`sitesOf`, by `hasLoan`) that no live-loan scan (`liveLoansIn`, by `loans`) sees. -/
def readingsLoanFree : Clause where
  name := "(WF15) no recorded reading holds a loan or a mark"
  premises := [
    ("a closure or Π-type with a recorded reading", fun st => (posVals st.env).any fun (_, v) =>
      v.anyAtom fun | .clo _ _ rd | .tPi _ _ rd => !rd.isEmpty | _ => false)]
  check st := (posVals st.env).filterMap fun (p, v) =>
    let bad : Value → Bool := fun
      | .clo _ _ rd | .tPi _ _ rd => rd.any fun (_, T) => T.anyAtom fun | .loan _ | .gloan _ _ => true | _ => false
      | _ => false
    if v.anyAtom bad then some ⟨s!"a recorded reading holding a loan or mark, at {posKind p}", s!"{posName st.env p} = {clip v.pp}"⟩
    else none

/-! ### Planted: deliberately false, to show the sweep is not vacuous -/

/-! ### Candidates for `movedPlace`'s exits (not yet clauses of `Good`; spine, 2026-11-21)

`movedPlace` re-roots a place the join drops to its parent when the parent holds nothing it can
refine (`MovedPlace.exit_abs`, `exit_sealed`, `exit_other`). The proof needs the parent to hold
`⊥`, `⋆`, or an unknown of the parent's declared inductive type. These clauses test the facts that
would give it, on the states recorded. -/

/-- The labels of marks outside sealed programs and code (as `outerLoans` walks). -/
def outerMarks : Value → List Nat
  | .gloan l w => l :: outerMarks w
  | .succ w | .tRef w | .borrow _ w => outerMarks w
  | .ind _ _ _ ps fs => (ps.attach.flatMap fun ⟨v, _⟩ => outerMarks v) ++ (fs.attach.flatMap fun ⟨v, _⟩ => outerMarks v)
  | _ => []

/-- (M) Every mark outside a sealed program is of a live borrow ([End] removes its marks). -/
def marksLive : Clause where
  name := "(M, candidate) every mark outside a sealed program is of a live borrow"
  premises := [("a mark exists", fun st => (posVals st.env).any fun (_, v) => !(outerMarks v).isEmpty)]
  check st := (posVals st.env).flatMap fun (p, v) => (outerMarks v).filterMap fun l =>
    if liveLoan st.env l then none else some ⟨"a mark of an ended borrow", s!"{posName st.env p}: lent_{l}"⟩

/-- The head of an inductive type value. -/
def indHead? : Value → Option String
  | .tInd n _ => some n
  | _ => none

/-- (U) An unknown has its holder's declared inductive type: at a binding whose stored type is an
inductive `D(…)` and whose value is an unknown `σ`, `σ`'s type is `D(…)`; and an unknown that is a
field of a constructor value whose declared field type is written `E(…)` has a type `E(…)`. -/
def unknownTyped : Clause where
  name := "(U, candidate) an unknown has its holder's declared inductive type"
  premises := [
    ("a binding of an inductive type holds an unknown", fun st => (bindings st.env).any fun (_, _, b) =>
      (match b.ty with | some (.tInd _ _) => true | _ => false) && (match b.val with | .abs _ => true | _ => false)),
    ("a constructor field declared `E(…)` holds an unknown", fun st => (posVals st.env).any fun (_, v) =>
      v.anyAtom fun
        | .ind ty c _ _ fs => match st.inds.find? (·.name == ty) with
          | some d => match d.ctors[c]? with
            | some (_, flds) => (fs.zip flds).any fun (w, (_, FT)) =>
                (match FT with | .tind _ _ => true | _ => false) && (match w with | .abs _ => true | _ => false)
            | none => false
          | none => false
        | _ => false)]
  check st :=
    ((bindings st.env).filterMap fun (f, i, b) => match b.ty, b.val with
      | some (.tInd n _), .abs σ =>
        if indHead? (st.absTy.getD σ .bot) == some n then none
        else some ⟨"an unknown at a binding of an inductive type, with another type",
          s!"{b.hint.name} (binding {f}.{i}) : {n}(…) holds σ{σ} : {clip (st.absTy.getD σ .bot).pp}"⟩
      | _, _ => none) ++
    ((posVals st.env).flatMap fun (p, v) =>
      let bad := fun (w : Value) => match w with
        | .ind ty c _ _ fs => match st.inds.find? (·.name == ty) with
          | some d => match d.ctors[c]? with
            | some (_, flds) => (fs.zip flds).any fun (w, (_, FT)) => match FT, w with
              | .tind m _, .abs σ => indHead? (st.absTy.getD σ .bot) != some m
              | _, _ => false
            | none => false
          | none => false
        | _ => false
      if v.anyAtom bad then [⟨"an unknown field declared `E(…)`, with another type", s!"{posName st.env p}: {clip v.pp}"⟩] else [])

/-- What may sit at a place declared an inductive `n` of the declarations: `⊥`, `⋆`, an unknown, a
sealed program, a loan, a constructor value of `n`, or a mark over any of these (`Value.fitsInd`,
`Steps/Statements.lean`, mirrored EXACTLY; docs/31 D44: first a mark over anything). -/
def fitsInd (n : String) : Value → Bool
  | .bot | .proof | .abs _ | .sealed _ | .loan _ => true
  | .gloan _ w => fitsInd n w
  | .ind ty _ _ _ _ => ty == n
  | _ => false

/-- (V) A place declared an inductive holds a value of that inductive or a stand-in for one: at a
binding whose declared reading is `.ind n _` with `n` declared, and at a constructor field whose
declared type is written `E(…)` with `E` declared. -/
def valueFits : Clause where
  name := "(V, candidate) a place declared an inductive holds one of its values or a stand-in"
  premises := [
    ("a binding is declared an inductive of the declarations", fun st => (bindings st.env).any fun (_, _, b) =>
      match b.decl with | .ind n _ => (st.inds.find? (·.name == n)).isSome | _ => false)]
  check st :=
    ((bindings st.env).filterMap fun (f, i, b) => match b.decl with
      | .ind n _ =>
        if (st.inds.find? (·.name == n)).isSome && !fitsInd n b.val then
          some ⟨s!"a binding declared an inductive holds something else", s!"{b.hint.name} (binding {f}.{i}) : {n}(…) holds {clip b.val.pp}"⟩
        else none
      | _ => none) ++
    ((posVals st.env).flatMap fun (p, v) =>
      let bad := fun (w : Value) => match w with
        | .ind ty c _ _ fs => match st.inds.find? (·.name == ty) with
          | some d => match d.ctors[c]? with
            | some (_, flds) => (fs.zip flds).any fun (w, (_, FT)) => match FT with
              | .tind m _ => (st.inds.find? (·.name == m)).isSome && !fitsInd m w
              | _ => false
            | none => false
          | none => false
        | _ => false
      if v.anyAtom bad then [⟨"a field declared `E(…)` holds something else", s!"{posName st.env p}: {clip v.pp}"⟩] else [])

/-- (R) A binding declared a borrow type holds a borrow, `⊥`, a loan or a mark over one (so `*p` exists
where `p` holds anything else than `⊥`). -/
def refFits : Value → Bool
  | .borrow _ _ | .bot | .loan _ => true
  | .gloan _ w => refFits w
  | _ => false

def refHolds : Clause where
  name := "(R, candidate) a binding declared a borrow type holds a borrow, ⊥ or a loan"
  premises := [("a binding is declared a borrow type", fun st => (bindings st.env).any fun (_, _, b) =>
    match b.decl with | .ref _ => true | _ => false)]
  check st := (bindings st.env).filterMap fun (f, i, b) => match b.decl with
    | .ref _ => if refFits b.val then none
      else some ⟨"a binding declared a borrow type holds something else", s!"{b.hint.name} (binding {f}.{i}) holds {clip b.val.pp}"⟩
    | _ => none

/-- (A) A constructor value of a declared inductive has its constructor's number of fields. -/
def arity : Clause where
  name := "(A, candidate) a constructor value has its constructor's fields"
  check st := (posVals st.env).flatMap fun (p, v) =>
    let bad := fun (w : Value) => match w with
      | .ind ty c _ _ fs => match st.inds.find? (·.name == ty) with
        | some d => match d.ctors[c]? with
          | some (_, flds) => fs.length != flds.length
          | none => true
        | none => false
      | _ => false
    if v.anyAtom bad then [⟨"a constructor value with the wrong fields", s!"{posName st.env p}: {clip v.pp}"⟩] else []

/-- The labels of every loan and mark anywhere in a value, sealed programs and code included
(`Value.loans`). -/
def allLoans (v : Value) : List Nat := v.loans

/-- (L) Every loan and mark anywhere in Ω, inside sealed programs and code included, is of a live
borrow ([End] substitutes a loan everywhere its borrow ends, and removes its marks). With it, a
sealed program with no live hole holds no loan (`MovedPlace.sealed_loanFree`). -/
def loansLive : Clause where
  name := "(L, candidate) every loan and mark anywhere in Ω is of a live borrow"
  premises := [("a loan or mark inside a sealed program or code", fun st => (posVals st.env).any fun (_, v) =>
    v.anyAtom fun | .sealed t => !t.loans.isEmpty | .clo cs t _ => !t.loans.isEmpty || !(Value.loansList cs).isEmpty | _ => false)]
  check st := (posVals st.env).flatMap fun (p, v) => (allLoans v).eraseDups.filterMap fun l =>
    if liveLoan st.env l then none else some ⟨"a loan or mark of an ended borrow", s!"{posName st.env p}: label {l} in {clip v.pp}"⟩

/-- Planted, FALSE: "no live borrow has a fill". It reads the same sites and live labels as (ii) and
(iii), so its violations must be exactly the states (ii)'s first premise counts. -/
def plantedFill : Clause where
  name := "(planted) no live borrow has a fill"
  planted := true
  check st := (liveSites st.env).filterMap fun (l, x) =>
    if x.fill then some ⟨s!"a live fill ({siteForm st.env x}) at {posKind x.pos}", s!"borrow {l} at {posName st.env x.pos}, {ppPath x.path}"⟩ else none

/-- Planted, FALSE: "no type or record holds an unknown". It walks the same types and records as
(i), with the atom test changed. -/
def plantedAbs : Clause where
  name := "(planted) no type or record holds an unknown"
  planted := true
  check st := (typesAndRecords st).filterMap fun (c, w, v) =>
    if v.anyAtom (fun | .abs _ => true | _ => false) then some ⟨s!"{c} holds an unknown", s!"{c} {w}: {clip v.pp}"⟩ else none

/-! ### The shape facts at every place in scope (docs/31 D34, D40)

The candidates (U), (V), (R) above read only bindings' declared readings and constructor fields
whose declared type is written `E(…)`. The Lean form quantifies over every place in scope and its
declared reading as the decisions give it (`Decisions.placeDecl` at the top frame's readings). This
clause closes the gap: it walks every place of the top frame that exists (a binding, the fields of
a constructor value, the content of a borrow, through marks), asks the checker's own `placeDecl`
(live, at the state) for its reading, and checks (U), (V) and (R) there; at a place holding a sealed
program whose reading is an inductive, it also asks the checker's `placeType?` (P: `exit_sealed`'s
alignment of the computed type with the declared reading). -/

/-- The places of the top frame under `q` holding `v`, with their values, to a depth. -/
def placesIn (q : Place) : Value → Nat → List (Place × Value)
  | v, 0 => [(q, v)]
  | v, n + 1 => (q, v) :: match v with
    | .gloan _ w => (placesIn q w n).drop 1
    | .borrow _ w => placesIn (.deref q) w n
    | .ind t c _ _ fs => (fs.zipIdx).flatMap fun (w, i) => placesIn (.field ⟨t, c, i, ""⟩ q) w n
    | _ => []

def topPlaces (st : MState) : List (Place × Value) :=
  match st.env.back? with
  | some fr => (List.range fr.binds.size).flatMap fun o => placesIn (.var o) (fr.binds[fr.binds.size - 1 - o]!).val 8
  | none => []

/-- The checker's declared reading of a place, live at the state. -/
def declAt (st : MState) (q : Place) : Option DeclInfo :=
  match (runMachine (withLive true (Ochr.placeDecl 1000 [] q)) st 100000).1 with
  | .ok d _ => some d
  | _ => none

def shapeViols (st : MState) : List Viol :=
  (topPlaces st).flatMap fun (q, v) =>
    let pq := (posName st.env (match st.env.back? with | some fr => .bind (st.env.size - 1) (fr.binds.size - 1 - q.root) | none => .bind 0 0))
    match declAt st q with
    | some (.ind n _) =>
      if (st.inds.find? (·.name == n)).isNone then [] else
      (if fitsInd n v then [] else [⟨"(V) a place declared an inductive holds something else", s!"{pq}…: {n}(…) holds {clip v.pp}"⟩]) ++
      (match v with
        | .abs σ => if indHead? (st.absTy.getD σ .bot) == some n then []
          else [⟨"(U) an unknown at a place declared an inductive has another type", s!"{pq}…: {n}(…) holds σ{σ} : {clip (st.absTy.getD σ .bot).pp}"⟩]
        | .sealed _ => match (runMachine (Ochr.placeType? 1000 q) st 1000000).1 with
          | .ok (some T) _ => if indHead? T == some n then []
            else [⟨"(P) a sealed program's computed type is not its declared inductive", s!"{pq}…: {n}(…), placeType? gives {clip T.pp}"⟩]
          | _ => [⟨"(P) a sealed program's computed type is missing", s!"{pq}…: {n}(…)"⟩]
        | _ => [])
    | some (.ref _) =>
      if refFits v then [] else [⟨"(R) a place declared a borrow type holds something else", s!"{pq}…: holds {clip v.pp}"⟩]
    | _ => []

def shapeFacts : Clause where
  name := "(U, V, R, P) at every place in scope, by the checker's declared reading"
  premises := [
    ("a place in scope is declared an inductive", fun st => (topPlaces st).any fun (q, _) =>
      match declAt st q with | some (.ind n _) => (st.inds.find? (·.name == n)).isSome | _ => false),
    ("... and holds an unknown", fun st => (topPlaces st).any fun (q, v) =>
      (match v with | .abs _ => true | _ => false) && (match declAt st q with | some (.ind _ _) => true | _ => false)),
    ("... and holds a sealed program", fun st => (topPlaces st).any fun (q, v) =>
      (match v with | .sealed _ => true | _ => false) && (match declAt st q with | some (.ind _ _) => true | _ => false)),
    ("a place in scope below a binding is declared an inductive", fun st => (topPlaces st).any fun (q, _) =>
      !(q matches .var _) && (match declAt st q with | some (.ind _ _) => true | _ => false)),
    ("a place in scope is declared a borrow type", fun st => (topPlaces st).any fun (q, _) =>
      match declAt st q with | some (.ref _) => true | _ => false)]
  check st := shapeViols st

/-! ### (N): constructor values of data declarations (docs/31 D47) -/

/-- `Steps.dataCtorBad`, mirrored EXACTLY. -/
def dataCtorBad (Γ : List IndDecl) : Value → Bool
  | .ind n _ _ _ _ => match Γ.find? (·.name == n) with
    | some d => d.sort == 0 || d.name == "Nat"
    | none => true
  | _ => false

/-- (N) (`ShapeFacts.ctors`): every constructor value anywhere in Ω is of a data declaration of the
state's declarations, not named `Nat`. -/
def ctorsData : Clause where
  name := "(N) every constructor value is of a data declaration, not named Nat"
  premises := [("a constructor value in Ω", fun st => (posVals st.env).any fun (_, v) =>
    v.anyAtom fun | .ind .. => true | _ => false)]
  check st := (posVals st.env).filterMap fun (p, v) =>
    if v.anyAtom (dataCtorBad st.inds) then
      some ⟨s!"a constructor value of a Prop or undeclared or Nat declaration, at {posKind p}", s!"{posName st.env p} = {clip v.pp}"⟩
    else none


/-- (C⋆) (`ShapeFacts.proofCopy`, docs/31 D49): a place in scope BELOW A VARIABLE holding `⋆` is
declared a copy type (a field of a proof), by the checker's own `placeDecl` and `declCopy`; so the
join, which moves no copy, never drops a `⋆` below a variable (`lentPrefix_none_of_proof`'s
premise; at a variable there is no strict prefix to be lent). First asked at every place: false at
a variable declared a borrow of a proposition, which holds `⋆` (`PiSorts.BorrowQ`, 6,447 states). -/
def proofCopy : Clause where
  name := "(C⋆) a place below a variable holding ⋆ is declared a copy type"
  premises := [
    ("a place in scope holds ⋆", fun st => (topPlaces st).any fun (_, v) => v matches .proof),
    ("... below a binding", fun st => (topPlaces st).any fun (q, v) => (v matches .proof) && !(q matches .var _))]
  check st := (topPlaces st).filterMap fun (q, v) =>
    if !(v matches .proof) || (q matches .var _) then none else
    match declAt st q with
    | some d => match (runMachine (Ochr.declCopy 1000 d) st 100000).1 with
      | .ok true _ => none
      | _ => some ⟨"a place holding ⋆ is declared a type that is not a copy", s!"{q.root}…: {d.beq .prop}"⟩
    | none => some ⟨"a place holding ⋆ has no declared reading", s!"{q.root}"⟩

/-- The content of the borrow `l`, where some position holds it. -/
def holderContent (st : MState) (l : Nat) : Option Value :=
  (posVals st.env).findSome? fun (_, v) => match v with
    | .borrow m w => if m == l then some w else none
    | _ => none

def sortIsProp (st : MState) (T : Value) : Bool :=
  match (runMachine (Ochr.sortOf 1000 T) st 100000).1 with
  | .ok 0 _ => true
  | _ => false

/-- Why a value at the place `q` could mean `⋆` (the atoms whose meaning is not their own: an
unknown of a proposition, a sealed program of one, a loan whose borrow holds `⋆` or such an
unknown, through a mark), or `none`. -/
def meansProof (st : MState) (q : Place) : Value → Option String
  | .gloan _ w => meansProof st q w
  | .abs σ => if sortIsProp st (st.absTy.getD σ .bot) then some s!"σ{σ} of a proposition" else none
  | .sealed _ => match (runMachine (Ochr.placeType? 1000 q) st 1000000).1 with
    | .ok (some T) _ => if sortIsProp st T then some "a sealed program of a proposition" else none
    | _ => none
  | .loan l => match holderContent st l with
    | some .proof => some s!"a loan ℓ{l} whose borrow holds ⋆"
    | some (.abs σ) => if sortIsProp st (st.absTy.getD σ .bot) then some s!"a loan ℓ{l} whose borrow holds σ{σ} of a proposition" else none
    | _ => none
  | _ => none

/-- (D⋆) (`dataMean_ne_proof`, `access_root_not_proof`, docs/31 D54): a place in scope of a
non-copy reading that holds data (not `⋆`, `⊥` or a borrow) holds nothing the reference reads as
`⋆`, and nothing the checker's access turns into `⋆` (a loan whose borrow holds `⋆`). The atoms
checked are those whose meaning is not fixed by their form. A clause since the slice:
`ShapeFacts.dataNotProof` (`Steps/Statements.lean`), with `MeansProof` mirroring `meansProof`; the
Lean form asks it at every place in scope (this walk stops at depth 8 and steps into fields by
constructor field), and runs `sortOf`/`placeType?` at any fuel from any state the same up to the move
log and the refinements (`SameDec`), where this runs them at the state itself with fixed fuel. -/
def dataNotProof : Clause where
  name := "(D⋆) a place of a non-copy reading holding data holds nothing meaning ⋆"
  premises := [
    ("a place in scope holds an unknown", fun st => (topPlaces st).any fun (_, v) => v matches .abs _),
    ("a place in scope holds a sealed program", fun st => (topPlaces st).any fun (_, v) => v matches .sealed _),
    ("a place in scope holds a loan", fun st => (topPlaces st).any fun (_, v) => v matches .loan _),
    ("a place in scope holds a loan whose borrow holds ⋆", fun st => (topPlaces st).any fun (_, v) =>
      match v with | .loan l => holderContent st l == some .proof | _ => false)]
  check st := (topPlaces st).filterMap fun (q, v) =>
    if v matches .proof || v matches .bot || v matches .borrow .. then none else
    match meansProof st q v with
    | none => none
    | some m => match declAt st q with
      | some d => match (runMachine (Ochr.declCopy 1000 d) st 100000).1 with
        | .ok true _ => none
        | _ => some ⟨"a place of a non-copy reading holds data meaning ⋆", s!"{q.root}…: {m}"⟩
      | none => some ⟨"a place holding data meaning ⋆ has no declared reading", s!"{q.root}…: {m}"⟩

def isCtorV : Value → Bool
  | .ind .. => true
  | _ => false

/-- A value under its marks. -/
def underMarks : Value → Value
  | .gloan _ w => underMarks w
  | v => v

/-- (Vℓ, CANDIDATE, the slice): a loan at a place declared an inductive `n` of the declarations
(under marks) is of a borrow whose content fits `n` (`fitsInd`). What (V) needs to survive the
borrow's [End], which puts that content at the place; not a clause (its preservation belongs to
the access step). A loan whose borrow is not in Ω (inert) is not checked. -/
def loanContentFits : Clause where
  name := "(Vℓ, candidate) a loan at a place declared an inductive is of a borrow whose content fits it"
  premises := [
    ("a place declared an inductive holds a loan", fun st => (topPlaces st).any fun (q, v) =>
      (underMarks v matches .loan _) &&
        (match declAt st q with | some (.ind n _) => (st.inds.find? (·.name == n)).isSome | _ => false)),
    ("... whose borrow holds a constructor value", fun st => (topPlaces st).any fun (q, v) =>
      (match underMarks v with
        | .loan l => (match holderContent st l with | some c => isCtorV (underMarks c) | none => false)
        | _ => false) &&
        (match declAt st q with | some (.ind n _) => (st.inds.find? (·.name == n)).isSome | _ => false))]
  check st := (topPlaces st).filterMap fun (q, v) =>
    match underMarks v, declAt st q with
    | .loan l, some (.ind n _) =>
      if (st.inds.find? (·.name == n)).isNone then none else
      match holderContent st l with
      | some c => if fitsInd n c then none
        else some ⟨"a loan at a place declared an inductive is of a borrow whose content does not fit it",
          s!"{q.root}…: {n}(…) holds loan {l}, whose borrow holds {clip c.pp}"⟩
      | none => none
    | _, _ => none

/-- A declared reading, briefly. -/
partial def declStr : DeclInfo → String
  | .sort l => s!"sort {l}"
  | .prop => "prop"
  | .pi c => s!"pi({declStr c})"
  | .ref a => s!"ref({declStr a})"
  | .unit => "unit"
  | .ind n _ => s!"ind {n}"
  | .alt ds => s!"alt[{", ".intercalate (ds.map declStr)}]"
  | .other => "other"
  | .any => "any"
  | .conflict => "conflict"

/-- The places in scope whose declared reading is not a copy (`declCopy` does not run to `true`),
with their values and readings. -/
def nonCopyPlaces (st : MState) : List (Place × Value × DeclInfo) :=
  (topPlaces st).filterMap fun (q, v) => match declAt st q with
    | some d => match (runMachine (Ochr.declCopy 1000 d) st 100000).1 with
      | .ok true _ => none
      | _ => some (q, v, d)
    | none => none

/-- The checker's computed type of a place (`Machine.placeType?`), at the state. -/
def placeTypeOf (st : MState) (q : Place) : Option Value :=
  match (runMachine (Ochr.placeType? 1000 q) st 1000000).1 with
  | .ok (some T) _ => some T
  | _ => none

/-- The head of a value, briefly. -/
def valHead : Value → String
  | .gfn _ => "a global function name" | .clo .. => "a closure" | .abs _ => "an unknown"
  | .sealed _ => "a sealed program" | .loan _ => "a loan" | .gloan _ _ => "a mark"
  | .borrow _ _ => "a borrow" | .ind .. => "a constructor value" | _ => "other"

/-- The place is the top frame's first binding (a function's own binding, `self`). -/
def isSelf (st : MState) (q : Place) : Bool :=
  match q, st.env.back? with
  | .var o, some fr => o + 1 == fr.binds.size
  | _, _ => false

/-- (D⋆T, REFUTED CANDIDATE, the slice; kept as a report): a place in scope whose declared reading
is not a copy and which holds neither `⋆` nor `⊥` has a computed type (`placeType?`) that the
checker's sort test (`sortOf … = 0`) does not call a proposition. Proposed to replace the per-value
(D⋆). False on the suite: a place declared a Π into proofs (`pi(prop)`, `pi(pi(prop))`) is no
copy, and a function's or closure's own binding of a proof-valued type holds the function's name
or the closure, not `⋆` (19,132 states, every one such a binding or a capture of one). -/
def typeNotProp : Clause where
  name := "(D⋆T, REFUTED candidate, kept as a report) a non-copy place holding neither ⋆ nor ⊥ has a computed type that is no proposition"
  report := true
  premises := [
    ("a non-copy place in scope holds neither ⋆ nor ⊥", fun st => (nonCopyPlaces st).any fun (_, v, _) =>
      !(v matches .proof) && !(v matches .bot)),
    ("... and has a computed type", fun st => (nonCopyPlaces st).any fun (q, v, _) =>
      !(v matches .proof) && !(v matches .bot) && (placeTypeOf st q).isSome),
    ("... and has none (placeType? fails or gives none)", fun st => (nonCopyPlaces st).any fun (q, v, _) =>
      !(v matches .proof) && !(v matches .bot) && (placeTypeOf st q).isNone)]
  check st := (nonCopyPlaces st).filterMap fun (q, v, d) =>
    if v matches .proof || v matches .bot then none else
    match placeTypeOf st q with
    | some T => if sortIsProp st T then
        some ⟨s!"a non-copy place ({declStr d}) holding {if q matches .var _ then "at a variable" else "below a variable"} data of a proposition: {valHead v}{if isSelf st q then ", the function's own binding" else ""}",
          s!"{q.root}…: holds {clip v.pp} : {clip T.pp}"⟩ else none
    | none => none

/-- REPORT (not a clause): the non-copy places in scope that hold `⋆`, by where and by declared
reading. -/
def nonCopyProof : Clause where
  name := "(report) a non-copy place holding ⋆"
  report := true
  premises := [("a non-copy place holds ⋆", fun st => (nonCopyPlaces st).any fun (_, v, _) => v matches .proof)]
  check st := (nonCopyPlaces st).filterMap fun (q, v, d) =>
    if v matches .proof then
      some ⟨s!"⋆ {if q matches .var _ then "at a variable" else "below a variable"} declared {declStr d}",
        s!"{q.root}…: {declStr d}"⟩
    else none

/-- REPORT (not a clause): the top frame's bindings with no stored type (`ty` and `lazyTy` both
`none`), where `Good`'s membership says nothing of the binding. -/
def untypedBindings : Clause where
  name := "(report) a binding of the top frame with no stored type"
  report := true
  premises := [
    ("a binding of the top frame has no stored type", fun st => match st.env.back? with
      | some fr => fr.binds.any fun b => b.ty.isNone && b.lazyTy.isNone
      | none => false),
    ("... outside a private copy", fun st => st.privateDepth == 0 && match st.env.back? with
      | some fr => fr.binds.any fun b => b.ty.isNone && b.lazyTy.isNone
      | none => false),
    ("... at a non-copy place holding neither ⋆ nor ⊥", fun st => (nonCopyPlaces st).any fun (q, v, _) =>
      (q matches .var _) && !(v matches .proof) && !(v matches .bot) &&
      (match st.env.back? with
        | some fr => match fr.binds[fr.binds.size - 1 - q.root]? with
          | some b => b.ty.isNone && b.lazyTy.isNone
          | none => false
        | none => false))]
  check st := match st.env.back? with
    | some fr => (List.range fr.binds.size).filterMap fun o =>
      let b := fr.binds[fr.binds.size - 1 - o]!
      if b.ty.isNone && b.lazyTy.isNone then
        some ⟨s!"an untyped binding {if st.privateDepth > 0 then "inside a private copy" else "outside private copies"}, declared {declStr b.decl}{if b.val matches .proof then ", holding ⋆" else if b.val matches .bot then ", holding ⊥" else ""}",
          s!"{b.hint.name}: {clip b.val.pp}"⟩
      else none
    | none => []

/-- (Hη) (`ShapeFacts.etaHint`, docs/31 D55): every η record is top-hint-free (a constructor value
of fresh unknowns that records its parameters, `ctorRefinement`), so it means its unknown at every
hint (`etaRecorded_sim`). -/
def etaHintFree : Clause where
  name := "(Hη) every η record is top-hint-free"
  premises := [("an η record", fun st => !st.etaRefs.isEmpty),
    ("an η record of a declaration with parameters", fun st => st.etaRefs.any fun (_, r) => match r with
      | .ind n _ _ _ _ => match st.inds.find? (·.name == n) with | some d => !d.params.isEmpty | none => false
      | _ => false)]
  check st := st.etaRefs.filterMap fun (σ, r) =>
    if topHintFree st.inds r then none else some ⟨"an η record reads the hint", s!"σ{σ} := {clip r.pp}"⟩

/-- (Rd) (`ShapeFacts.readingsSorted`, docs/31 D77, D78): an unknown whose frozen reading is
`Sort l` (D96) has the type `Sort l`; with `Good` and `CtxOk` it makes the checker's `sortOf` sound
for the model (`sortOf_sound_stmt`). -/
def readingsSorted : Clause where
  name := "(Rd) an unknown read as Sort l has the type Sort l"
  premises := [("an unknown read as a sort", fun st => st.absDecl.any fun | DeclInfo.sort _ => true | _ => false)]
  check st := (List.range st.absTy.size).filterMap fun (σ : Nat) =>
    match (st.absDecl[σ]? : Option DeclInfo) with
    | some (DeclInfo.sort l) => match (st.absTy[σ]? : Option Value) with
      | some (Value.sort l') => if l' == l then none else
          some ⟨"an unknown read as a sort has another sort", s!"σ{σ} : Sort {l'}, read Sort {l}"⟩
      | some T => some ⟨"an unknown read as a sort has another type", s!"σ{σ} : {clip T.pp}, read Sort {l}"⟩
      | none => some ⟨"an unknown read as a sort has no type", s!"σ{σ}"⟩
    | _ => none

def clauses : List Clause :=
  [wf11, wf12, noopClause, wf1, wf2, wf3, wf4, wf6, wf8, wf9, wf10, marksLive, unknownTyped, valueFits, refHolds, arity, loansLive, shapeFacts, hintFreeSealed, readingsLoanFree, ctorsData, proofCopy, dataNotProof, loanContentFits, typeNotProp, etaHintFree, readingsSorted, plantedFill, plantedAbs, nonCopyProof, untypedBindings]

/-! ## The sweep -/

/-- A violation's example: the declaration (its source span, to pick the smallest), the located
term, and the state. -/
structure Example where
  block : String
  decl : String
  size : Nat
  span : Loc
  loc : Loc
  exit : Bool
  detail : String
  state : String
deriving Inhabited

structure KindStat where
  states : Nat := 0
  exits : Nat := 0
  decls : Array String := #[]
  best : Option Example := none
deriving Inhabited

structure Stat where
  states : Nat := 0
  violating : Nat := 0
  premises : Array Nat
  kinds : Array (String × KindStat) := #[]
deriving Inhabited

/-- The source file of an `ochr` block (`Ochr/Prelude.lean` or under `Ochr/Examples/`), and its text. -/
def blockSource (block : String) : IO (Option String) := do
  let files ← (System.FilePath.mk "Ochr/Examples").walkDir
  for f in #[System.FilePath.mk "Ochr/Prelude.lean"] ++ files do
    if f.extension == some "lean" then
      let s ← IO.FS.readFile f
      if (s.splitOn s!"\nochr {block} ").length > 1 || (s.splitOn s!"\nochr {block}\n").length > 1 then return some s
  return none

/-- The text of the byte range `l` of `s`. -/
def slice (s : String) (l : Loc) : String :=
  String.fromUTF8! (s.toUTF8.extract l.start l.stop)

/-- Sweep the blocks; print the report; 0 iff every real clause holds on every state checked,
both planted clauses are reported, and every verdict is as expected. -/
def sweep (blocks : List (String × Block)) : IO UInt32 := do
  let cfg : Config := { recordStates := true }
  let mut stats : Array Stat := (clauses.map fun c => ({ premises := c.premises.toArray.map fun _ => 0 } : Stat)).toArray
  let mut total := 0
  let mut entries := 0
  let mut decls := 0
  let mut rowsAll := 0
  let mut asExpected := 0
  let mut privateStates := 0
  let mut tailExits := 0
  -- (Δ↑) along each run, the table of unknowns never shrinks (docs/31 D58, `access_absTy`)
  let mut pairs := 0
  let mut shrank := 0
  let mut shrinkEx : Array String := #[]
  for (bn, b) in blocks do
    let r := runWith (some Prelude) bn b cfg 2000000 (located := true)
    for row in r.rows do
      rowsAll := rowsAll + 1
      if row.asExpected then asExpected := asExpected + 1
      -- on exit, an evaluated term's value is in flight: the state its rules see has it as a
      -- temporary of the top frame (the spine's `MState.withTemp`, State.lean). A tail term's
      -- exit is after its continuation (`checkTail`'s `k`), which consumed the result (returned
      -- it, checked it against the goal, dropped the frame): the result is in flight there with
      -- no record of it, so those states are counted and not checked.
      tailExits := tailExits + (row.trace.filter fun | .state _ true none _ => true | _ => false).size
      let sts := row.trace.filterMap fun
        | .state l e v st => if e && v.isNone then none else some (l, e, st, v)
        | _ => none
      if sts.isEmpty then continue
      for h : k in [1:sts.size] do
        let (_, _, p, _) := sts[k - 1]!
        let (lq, eq, q, _) := sts[k]!
        pairs := pairs + 1
        if q.absTy.size < p.absTy.size || q.nextAbs < p.nextAbs then
          shrank := shrank + 1
          if shrinkEx.size < 3 then
            shrinkEx := shrinkEx.push s!"{bn}.{row.name} at {repr lq} on {if eq then "exit" else "entry"}: absTy {p.absTy.size}→{q.absTy.size}, nextAbs {p.nextAbs}→{q.nextAbs}"
      decls := decls + 1
      let lo := sts.foldl (fun a (l, _, _, _) => min a l.start) sts[0]!.1.start
      let hi := sts.foldl (fun a (l, _, _, _) => max a l.stop) 0
      let key := s!"{bn}.{row.name}"
      for (l, e, st0, flight) in sts do
        let st := match flight with
          | some v => { st0 with env := st0.env.modify (st0.env.size - 1) fun fr => { fr with temps := fr.temps.push v } }
          | none => st0
        total := total + 1
        if !e then entries := entries + 1
        if st.privateDepth > 0 then privateStates := privateStates + 1
        for h : ci in [0:clauses.length] do
          let c := clauses[ci]
          let mut s := stats[ci]!
          s := { s with states := s.states + 1 }
          for h : pi in [0:c.premises.length] do
            if c.premises[pi].2 st then s := { s with premises := s.premises.modify pi (· + 1) }
          -- a violation that only the value in flight makes is labelled so
          -- (the state the rules see is `st`, with it; `st0` is without it)
          let vs := c.check st
          let vs := if flight.isNone then vs else
            let vs0 := c.check st0
            vs.map fun x => if vs0.any (fun y => y.kind == x.kind && y.detail == x.detail) then x else
              { x with kind := x.kind ++ " [only with the exit's value in flight]" }
          if !vs.isEmpty then s := { s with violating := s.violating + 1 }
          for k in (vs.map (·.kind)).eraseDups do
            let idx := s.kinds.findIdx? (·.1 == k)
            let ks : KindStat := match idx with | some j => s.kinds[j]!.2 | none => {}
            let better : Bool := match ks.best with | some ex => decide (hi - lo < ex.size) | none => true
            let best : Option Example :=
              if better then
                some { block := bn, decl := row.name, size := hi - lo, span := Loc.mk lo hi, loc := l, exit := e
                       detail := "\n      ".intercalate ((vs.filter (·.kind == k)).map (·.detail))
                       state := ppState st }
              else ks.best
            let decls' := if ks.decls.contains key then ks.decls else ks.decls.push key
            let ks : KindStat := { states := ks.states + 1, exits := ks.exits + (if e then 1 else 0), decls := decls', best := best }
            s := { s with kinds := match idx with | some j => s.kinds.set! j (k, ks) | none => s.kinds.push (k, ks) }
          stats := stats.set! ci s
  IO.println s!"lake exe sweep (dev tooling): {blocks.length} blocks, {rowsAll} verdicts, {asExpected} as expected with the flag on"
  IO.println s!"states checked: {total} ({entries} on entry, {total - entries} on exit; {privateStates} inside a private copy) in {decls} declarations; not checked: {tailExits} tail terms' exits"
  IO.println s!"(Δ↑) consecutive recorded states of one run: {pairs}; where the table of unknowns shrank: {shrank}"
  for x in shrinkEx do IO.println s!"   {x}"
  let mut ok := asExpected == rowsAll
  for h : ci in [0:clauses.length] do
    let c := clauses[ci]
    let s := stats[ci]!
    IO.println ""
    IO.println s!"== {c.name}"
    IO.println s!"   states checked: {s.states}; states with a violation: {s.violating}"
    for h : pi in [0:c.premises.length] do
      IO.println s!"   premise \"{c.premises[pi].1}\": {s.premises[pi]!} states"
    if s.kinds.isEmpty then
      IO.println s!"   violations: none"
      if c.planted then
        IO.println "   PLANTED CLAUSE NOT REPORTED: the sweep is vacuous"
        ok := false
    else
      if c.planted then IO.println "   (planted: violations expected)"
      else if c.report then IO.println "   (a report: its cases are listed, not violations)"
      else ok := false
      for (k, ks) in s.kinds do
        IO.println s!"   VIOLATED: {k}: {ks.states} states ({ks.states - ks.exits} on entry, {ks.exits} on exit), in {ks.decls.size} declarations: {", ".intercalate (ks.decls.toList.take 8)}{if ks.decls.size > 8 then ", …" else ""}"
        if let some ex := ks.best then
          IO.println s!"     smallest: {ex.block}.{ex.decl} ({ex.size} bytes), at the term {repr ex.loc} on {if ex.exit then "exit" else "entry"}"
          IO.println s!"      {ex.detail}"
          if !c.planted && !c.report then
            match ← blockSource ex.block with
            | some src =>
              IO.println s!"     source of the term:\n{slice src ex.loc}"
              IO.println s!"     source of the declaration's body:\n{slice src ex.span}"
            | none => IO.println "     (source file not found)"
            IO.println s!"     state:\n{ex.state}"
  IO.println ""
  IO.println (if ok then "sweep: every real clause holds on every state; both planted clauses reported" else "sweep: FAILED (see above)")
  return if ok then 0 else 1

/-! ## Do ends create unknowns or records? (docs/31 D35)

From every recorded state, end each live borrow (`Machine.endBorrow`, as the checker would there)
and compare the state's unknowns and records before and after: `nextAbs`, `absTy`, `neutrals`,
`etaRefs`, `refs`. An end substitutes the borrow's content into every sealed program holding its
loan, and a changed sealed program re-runs (`nfSealed`, whose `restoreKeep` keeps the unknowns'
types and the generalisation and η records of the run, D37); with `typing` on it also checks the
content against a dependent borrow type (`repackCheck`). Counted: the ends run, those that touched
a sealed program holding the loan (the premise: a re-run), those that failed or ran out of fuel,
and those after which the state has more unknowns or records. -/

/-- Some sealed program inside `v` holds a loan of `l`. -/
def sealedHolds (l : Nat) (v : Value) : Bool :=
  v.anyAtom fun | .sealed t => t.anyAtom (· == .loan l) | _ => false

structure EndStat where
  states : Nat := 0
  ends : Nat := 0
  reruns : Nat := 0
  failed : Nat := 0
  grew : Nat := 0
  grewRecords : Nat := 0
  grewReferenced : Nat := 0
  grewRerun : Nat := 0
  grewTyping : Nat := 0
  grewDecls : Array String := #[]
  examples : Array String := #[]
  shrank : Nat := 0
  accesses : Nat := 0
  accFailed : Nat := 0
  accGrew : Nat := 0
  accShrank : Nat := 0
  shrinkEx : Array String := #[]

/-- Some unknown at or above `n` occurs in a value of Ω, a stored or deferred type, the goal, or a
record: the syntactic `MState.Refd` of a new unknown (its types' dependencies aside). -/
def refdAbove (st : MState) (n : Nat) : Bool :=
  let a := absAbove n
  (posVals st.env).any (fun (_, v) => a v) ||
  (bindings st.env).any (fun (_, _, b) => (b.ty.map a).getD false ||
    (match b.lazyTy with | some (P, ws, _) => a P || ws.any a | none => false)) ||
  (st.goal.map a).getD false ||
  st.neutrals.any (fun (v, σ) => a v || σ ≥ n) || st.etaRefs.any (fun (σ, v) => a v || σ ≥ n) ||
  st.refs.any (fun (σ, v) => a v || σ ≥ n)

def endProbe (blocks : List (String × Block)) : IO UInt32 := do
  let cfg : Config := { recordStates := true }
  let mut S : EndStat := {}
  for (bn, b) in blocks do
    let r := runWith (some Prelude) bn b cfg 2000000 (located := true)
    for row in r.rows do
      for e in row.trace do
        let .state _ _ _ st := e | continue
        S := { S with states := S.states + 1 }
        -- (Δ↑) an access of each variable of the top frame: the table of unknowns never shrinks
        let nv := match st.env.back? with | some fr => fr.binds.size | none => 0
        for i in List.range nv do
          S := { S with accesses := S.accesses + 1 }
          match (runMachine (do Ochr.accessPath 100000 (.var i); Ochr.accessInside 100000 (.var i)) st 100000).1 with
          | .ok () st' =>
            if st'.absTy.size < st.absTy.size || st'.nextAbs < st.nextAbs ||
                st'.neutrals.length < st.neutrals.length || st'.etaRefs.length < st.etaRefs.length ||
                st'.refs.length < st.refs.length then
              S := { S with accShrank := S.accShrank + 1 }
              if S.shrinkEx.size < 3 then
                S := { S with shrinkEx := S.shrinkEx.push s!"{bn}.{row.name}: access of variable {i}: absTy {st.absTy.size}→{st'.absTy.size}" }
            if st'.absTy.size != st.absTy.size then S := { S with accGrew := S.accGrew + 1 }
          | _ => S := { S with accFailed := S.accFailed + 1 }
        for l in liveLabels st.env do
          let rerun := (posVals st.env).any fun (_, v) => sealedHolds l v
          S := { S with ends := S.ends + 1, reruns := S.reruns + (if rerun then 1 else 0) }
          match (runMachine (Ochr.endBorrow 100000 l) st 100000).1 with
          | .ok () st' =>
            if st'.absTy.size < st.absTy.size || st'.nextAbs < st.nextAbs ||
                st'.neutrals.length < st.neutrals.length || st'.etaRefs.length < st.etaRefs.length ||
                st'.refs.length < st.refs.length then
              S := { S with shrank := S.shrank + 1 }
              if S.shrinkEx.size < 3 then
                S := { S with shrinkEx := S.shrinkEx.push s!"{bn}.{row.name}: ending {l}: absTy {st.absTy.size}→{st'.absTy.size}" }
            let grew := st'.nextAbs != st.nextAbs || st'.absTy.size != st.absTy.size ||
              st'.neutrals.length != st.neutrals.length || st'.etaRefs.length != st.etaRefs.length ||
              st'.refs.length != st.refs.length
            if grew then
              let recs := st'.neutrals.length != st.neutrals.length || st'.etaRefs.length != st.etaRefs.length ||
                st'.refs.length != st.refs.length
              let key := s!"{bn}.{row.name}"
              S := { S with grew := S.grew + 1, grewRecords := S.grewRecords + (if recs then 1 else 0)
                            grewReferenced := S.grewReferenced + (if refdAbove st' st.nextAbs then 1 else 0)
                            grewRerun := S.grewRerun + (if rerun then 1 else 0)
                            grewTyping := S.grewTyping + (if st.typing then 1 else 0)
                            grewDecls := if S.grewDecls.contains key then S.grewDecls else S.grewDecls.push key }
              if S.examples.size < 5 then
                let msg := s!"{bn}.{row.name}: ending {l}: nextAbs {st.nextAbs}→{st'.nextAbs}, absTy {st.absTy.size}→{st'.absTy.size}, neutrals {st.neutrals.length}→{st'.neutrals.length}, etaRefs {st.etaRefs.length}→{st'.etaRefs.length}, refs {st.refs.length}→{st'.refs.length} (re-run: {rerun})\n{ppState st}"
                S := { S with examples := S.examples.push msg }
          | _ => S := { S with failed := S.failed + 1 }
  IO.println s!"end probe (dev tooling): {blocks.length} blocks, {S.states} states, {S.ends} ends run, {S.reruns} touching a sealed program that holds the loan, {S.failed} failed or out of fuel"
  IO.println s!"ends after which the state has more unknowns or records: {S.grew} (with more records: {S.grewRecords}; a new unknown referenced after: {S.grewReferenced}; touching a re-run: {S.grewRerun}; with typing on: {S.grewTyping}), in {S.grewDecls.size} declarations: {", ".intercalate S.grewDecls.toList}"
  IO.println s!"(Δ↑) ends after which the table of unknowns or a record list shrank: {S.shrank}"
  IO.println s!"(Δ↑) accesses of a top-frame variable run: {S.accesses} ({S.accFailed} failed or out of fuel); after which the table grew: {S.accGrew}; shrank, or a record list did: {S.accShrank}"
  for x in S.shrinkEx do IO.println s!"   {x}"
  for x in S.examples do IO.println x
  return 0

end Sweep

def main (args : List String) : IO UInt32 :=
  if args == ["--probes"] then Sweep.sweep Sweep.probes else
  if args == ["--ends"] then Sweep.endProbe (Ochr.Registry.programs ++ Ochr.Registry.caseStudies) else
  if args == ["--ends", "--probes"] then Sweep.endProbe Sweep.probes else
  Sweep.sweep ((Ochr.Registry.programs ++ Ochr.Registry.caseStudies).filter fun (n, _) => args.isEmpty || args.contains n)
