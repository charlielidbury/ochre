import Ochr.Examples.Registry

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

The clauses are those of branch `spine` at a3e22c78 (`Ochr/Meaning/WF.lean`; the helpers in
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

Usage: `lake exe sweep [Block …]` (all blocks if none named), or `Sweep.sweep [("B", B)]` from a
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

/-! ### (ii) (WF12): under a live fill, only what ending that fill reaches -/

/-- (WF12), mirrored EXACTLY, with `liveLoan` (main's, as the Prop) and `Env.sitesOf` (copied):
```
def WF12 (env : Env) : Prop :=
  ∀ k l, liveLoan env k = true → liveLoan env l = true →
    ∀ x ∈ Env.sitesOf env k, x.fill = true → ∀ y ∈ Env.sitesOf env l, y.pos = x.pos →
      (pathKey x.path).isPrefixOf (pathKey y.path) = true → pathKey y.path ≠ pathKey x.path →
      ∃ z ∈ Env.sitesOf env l, z.pos = x.pos ∧ (pathKey z.path).isPrefixOf (pathKey x.path) = true
```
The labels range over `liveLabels env`, which is exactly the set of `k` with `liveLoan env k`. -/
def wf12Viols (env : Env) : List Viol := Id.run do
  let live := (liveLabels env).map fun l => (l, envSitesOf env l)
  let mut out : Array Viol := #[]
  for (k, xs) in live do
    for x in xs do
      if x.fill then
        for (l, ys) in live do
          for y in ys do
            if y.pos == x.pos && (pathKey x.path).isPrefixOf (pathKey y.path) && pathKey y.path != pathKey x.path then
              unless ys.any fun z => z.pos == x.pos && (pathKey z.path).isPrefixOf (pathKey x.path) do
                out := out.push ⟨s!"{siteForm env y} of a live borrow strictly under {siteForm env x} of another, at {posKind x.pos}",
                  s!"{posName env x.pos}: borrow {k}'s fill at {ppPath x.path}, borrow {l}'s site at {ppPath y.path}, {l} not lent at or above {ppPath x.path}"⟩
  pure out.toList

/-- The antecedent of (WF12) holds somewhere: a live site strictly under another live borrow's fill. -/
def wf12Premise (env : Env) : Bool :=
  let ss := liveSites env
  ss.any fun (k, x) => x.fill && ss.any fun (l, y) =>
    l != k && y.pos == x.pos && (pathKey x.path).isPrefixOf (pathKey y.path) && pathKey y.path != pathKey x.path

def wf12 : Clause where
  name := "(ii) (WF12) under a live fill, only what ending that fill reaches"
  premises := [
    ("a live fill exists", fun st => (liveSites st.env).any (·.2.fill)),
    ("a live site lies strictly under another live borrow's fill", fun st => wf12Premise st.env)]
  check st := wf12Viols st.env

/-! ### (iii) No live fill above a moved or proof part (`lentPrefix_none_of_noop`) -/

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

/-- Clause (iii), the conclusion of `lentPrefix_none_of_noop` (Steps/DropOne.lean) made a state
clause: at every `⊥` or `⋆` part of every position, no live borrow has a site at a strict prefix.
```
theorem lentPrefix_none_of_noop (st : MState) (s : SState) (π : Nat → Nat) (q : Place) (pos : Pos)
    (hg : Good K.dm K.M K.Γ ρ st) (hs : Rel K ρ φ π st s) (hpos : resolve s q = some (pos, q.steps.2))
    (hnoop : (valAt st.env pos).follow q.steps.2 = some .bot ∨ (valAt st.env pos).follow q.steps.2 = some .proof) :
    lentPrefix s pos q.steps.2 = none
```
STRONGER than the theorem: asked at every `⊥`/`⋆` part of every position (bindings and
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
      if let some (pre, l, x) := lentPrefix ss p ψ then
        out := out.push ⟨s!"a {if prf then "⋆" else "⊥"} part strictly under {siteForm env x} of a live borrow, at {posKind p}",
          s!"{posName env p}: the part at {ppPath ψ}, borrow {l}'s site at {ppPath pre}"⟩
  pure out.toList

def noopClause : Clause where
  name := "(iii) no live fill sits above a moved or proof part"
  premises := [
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

/-- (WF6), mirrored EXACTLY (`∀ σ, v.hasAbs σ → σ < n` is `!absAbove n v`):
```
def WF6 (st : MState) : Prop :=
  (∀ v ∈ Env.values st.env, ∀ σ, v.hasAbs σ → σ < st.absTy.size) ∧
  (∀ T ∈ st.absTy.toList, ∀ σ, T.hasAbs σ → σ < st.absTy.size) ∧
  (∀ G, st.goal = some G → ∀ σ, G.hasAbs σ → σ < st.absTy.size) ∧
  st.absTy.size ≤ st.nextAbs ∧
  ∀ v ∈ Env.values st.env, ∀ l ∈ v.loans, l < st.nextLoan
``` -/
def wf6 : Clause where
  name := "(WF6) names: every unknown has a type, every name is below its counter"
  check st :=
    let n := st.absTy.size
    ((posVals st.env).filterMap fun (p, v) => if absAbove n v then some ⟨"an unknown without a type, in Ω", posName st.env p⟩ else none) ++
    (st.absTy.toList.filterMap fun T => if absAbove n T then some ⟨"an unknown without a type, in an unknown's type", clip T.pp⟩ else none) ++
    (match st.goal with | some G => if absAbove n G then [⟨"an unknown without a type, in the goal", clip G.pp⟩] else [] | none => []) ++
    (if n ≤ st.nextAbs then [] else [⟨"more unknowns' types than the counter", s!"{n} > {st.nextAbs}"⟩]) ++
    ((posVals st.env).flatMap fun (p, v) => v.loans.filterMap fun l =>
      if l < st.nextLoan then none else some ⟨"a label at or above the counter", s!"{l} in {posName st.env p}"⟩)

def refTopOk (T : Value) : Bool := match T with | .tRef A => !A.typeHasRef | T => !T.typeHasRef

/-- (WF8), mirrored EXACTLY:
```
def WF8 (st : MState) : Prop :=
  (∀ v ∈ Env.values st.env, ¬ v.typeHasRef) ∧
  (∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr => fr.binds[i]?) = some b →
    ∀ T : Value, b.ty = some T →
    match T with | .tRef A => ¬ A.typeHasRef | T => ¬ T.typeHasRef) ∧
  (∀ T ∈ st.absTy.toList, match T with | .tRef A => ¬ A.typeHasRef | T => ¬ T.typeHasRef) ∧
  (∀ G, st.goal = some G → match G with | .tRef A => ¬ A.typeHasRef | G => ¬ G.typeHasRef)
``` -/
def wf8 : Clause where
  name := "(WF8) & only at the top of a declared type"
  check st :=
    ((posVals st.env).filterMap fun (p, v) => if v.typeHasRef then some ⟨s!"a borrow type inside a value, at {posKind p}", posName st.env p⟩ else none) ++
    ((bindings st.env).filterMap fun (f, i, b) => match b.ty with
      | some T => if refTopOk T then none else some ⟨"a borrow type inside a stored type", s!"{b.hint.name} (binding {f}.{i}): {clip T.pp}"⟩
      | none => none) ++
    (st.absTy.toList.filterMap fun T => if refTopOk T then none else some ⟨"a borrow type inside an unknown's type", clip T.pp⟩) ++
    (match st.goal with | some G => if refTopOk G then [] else [⟨"a borrow type inside the goal", clip G.pp⟩] | none => [])

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

/-! ### Planted: deliberately false, to show the sweep is not vacuous -/

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

def clauses : List Clause :=
  [wf11, wf12, noopClause, wf1, wf2, wf3, wf4, wf6, wf8, wf9, wf10, plantedFill, plantedAbs]

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
      if c.planted then IO.println "   (planted: violations expected)" else ok := false
      for (k, ks) in s.kinds do
        IO.println s!"   VIOLATED: {k}: {ks.states} states ({ks.states - ks.exits} on entry, {ks.exits} on exit), in {ks.decls.size} declarations: {", ".intercalate (ks.decls.toList.take 8)}{if ks.decls.size > 8 then ", …" else ""}"
        if let some ex := ks.best then
          IO.println s!"     smallest: {ex.block}.{ex.decl} ({ex.size} bytes), at the term {repr ex.loc} on {if ex.exit then "exit" else "entry"}"
          IO.println s!"      {ex.detail}"
          if !c.planted then
            match ← blockSource ex.block with
            | some src =>
              IO.println s!"     source of the term:\n{slice src ex.loc}"
              IO.println s!"     source of the declaration's body:\n{slice src ex.span}"
            | none => IO.println "     (source file not found)"
            IO.println s!"     state:\n{ex.state}"
  IO.println ""
  IO.println (if ok then "sweep: every real clause holds on every state; both planted clauses reported" else "sweep: FAILED (see above)")
  return if ok then 0 else 1

end Sweep

def main (args : List String) : IO UInt32 :=
  Sweep.sweep ((Ochr.Registry.programs ++ Ochr.Registry.caseStudies).filter fun (n, _) => args.isEmpty || args.contains n)
