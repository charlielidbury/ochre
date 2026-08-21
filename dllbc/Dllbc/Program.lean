import Dllbc.Boundary
import Dllbc.FnMacro

/-!
# Programs are terms (`docs/combining-fns.md` §8)

> "There is no declaration former and no module story, because there is nothing
> left for one to do: **a program is an arbitrary term, and running it is
> ⇒-evaluating it.**"

A module is a let-chain: transparent `let`s, sealed `let`s, and a tail
expression. Every piece of structure a declaration form ever carried already
lives on the binding — mode by case (§6), opacity by `.seal` on the right-hand
side (§5), recursion inside the term as a recursor (§7) — so this file adds no
kernel rule at all. It is two entry points and their test helpers.

**Checking a program is the symbolic ⇒-walk of it.** `explore` already is that
walk: each `let` binds, each sealed `let` fires its audit once at its own `.seal`
node (in program order, since ⇒ evaluates a let-chain in order), a symbolic match
forks paths, and the tail is checked in the accumulated Ω. What `checkFn` adds on
top of the walk — seeding a telescope, pinning a dependent return type, exit
snapshots — a program has no need of: it takes no arguments. So `checkProgram` is
`explore` plus the audit of each path's result, and nothing else.

**Scope is the call table.** A callee is a binding lexically above the call
(an app spine on a slot, resolved by the surface from scope alone), so there is no
table at all — not an empty one. The `table` parameter these entry points carried
was J1's bridge for half-migrated programs, whose un-migrated callees were still
`FnDef`s; the corpus has none, and the bridge retired with `FnDef`'s departure
from the kernel (M28 D9).

**No forward references, by construction.** A let-chain cannot reference
downward: a name used before its binding is not in scope, so it does not resolve
to a later definition — it fails to resolve at all. Nothing rejects a forward
reference, because none can be written (`S26Prog` pins it).
-/

namespace Dllbc

/-- **The end of a program is a demand on everything it still holds.** A program
    that lends a local to a call and never looks at it again leaves the loan
    parked: the checking machine releases a group when something demands it (§5.2,
    "every demand collapses first"), and nothing ever does. The executing machine
    is not lazy in the same way — a frame's loans are released on the way out of
    it — so without this the two machines would end in visibly different Ωs on an
    ordinary program, and the differential would report a counterexample that is
    only a difference in *when*.

    Ending the scope is what a `FnDef`'s audit does for its arguments
    (`collapseResidue`) and what `popScope` does for a frame or a match arm; at the
    top level there is no caller to hand anything back to, so every parked loan is
    simply demanded. It can legitimately FAIL — a group whose release is not
    justified is rejected here rather than passed over — which is why it belongs
    to checking and not to the harness.

    **This is the drop half of a pop WITHOUT the pop** (M31 Stage 0), and that is
    deliberate: the program's scope has no enclosing scope to return control to,
    so there is no moment at which its bindings stop being reachable, and its Ω is
    the observable the whole test suite reads. A scope pops when control leaves it
    INTO an enclosing scope; the outermost one never does. -/
partial def endScope (fuel : Nat) : M Unit := do
  match (← getEnv).findSome? (fun kv => firstLoanMarker kv.2) with
  | some ℓ => do endLoan fuel ℓ; endScope fuel
  | none => pure ()

/-- The symbolic ⇒-walk's paths, each with its scope ended. Split out of
    `checkProgramDiag` so that the hover variant below is the SAME walk rather
    than a second one written to agree with it: the two differ in the seed state
    and in what they do with the paths afterwards, and in nothing else. -/
def programPaths (st0 : St) (t : Term) : List (Except Diag (Val × St)) :=
  (exploreD defaultFuel (atBoundary t) st0).map
    (fun r => r.bind (fun p =>
      match (endScope defaultFuel).run p.2 with
      | .ok _ st => .ok (p.1, st)
      | .error e s => .error (Diag.of e s)))

/-- The verdict on a walk's paths. THE accept/reject decision, in one place. -/
def programVerdict (retType? : Option Term)
    (paths : List (Except Diag (Val × St))) : Except Diag Unit :=
  match retType? with
  | some retType => auditPathsD retType paths
  -- WALK ONLY. The surface uses this when the program does not say what it
  -- returns: every rejection the ⇒-walk itself raises is still caught and still
  -- localized, and only the audit — the one check that needs a return type — is
  -- left to whoever states one.
  | none => paths.foldl (fun acc r => acc.bind (fun _ => r.map (fun _ => ()))) (.ok ())

/-- **Check a program** (§8): one symbolic ⇒-walk, auditing each path's result at
    `retType`. No table: scope is the call table (§8). -/
def checkProgramDiag (t : Term) (retType? : Option Term := some ty{ Unit }) :
    Except Diag Unit :=
  programVerdict retType? (programPaths initSt t)

/-! ## Replaying the deltas — what was true at a point (docs/17)

    The recording side keeps changes, not snapshots, because a `refineSym` sweeps
    all of Ω and storing a fact per binder per point would be quadratic (§2). The
    reading side pays for that here: a binder's fact at a point is recovered by
    applying the deltas that precede it.

    **This is the deferred half of the cost**, and it is paid per HOVER rather
    than per check — a hover asks about one point, so the replay stops there. -/

/-- What a replay has reconstructed at some point: the live bindings, and the
    σ-context as it stood there. -/
structure PointState where
  env : List (Var × Val) := []
  sctx : List (Nat × Term) := []
deriving Inhabited

/-- Apply one delta. `refine` is the expensive one and the reason `substSym`
    exists: learning σ rewrites every binding that mentions it, which is exactly
    what the checker itself did at that moment. -/
def PointState.step (s : PointState) (d : PointDelta) : PointState :=
  match d.change with
  | .bound x v => { s with env := s.env.filter (fun kv => kv.1 != x) ++ [(x, v)], sctx := d.sctx }
  | .set x v => { s with env := s.env.map (fun kv => if kv.1 == x then (x, v) else kv), sctx := d.sctx }
  | .refine σ repl =>
    { env := s.env.map (fun kv => (kv.1, substSym σ repl kv.2)), sctx := d.sctx }

/-- The state as it stood ENTERING the statement keyed `key` on the first path
    that reaches it — i.e. with every delta filed under an earlier statement
    applied, and none of this statement's own.

    **"Entering" is the right instant and not an off-by-one.** An occurrence in
    `let d = *b` is read while the checker is inside that statement but before
    the statement's own binding lands, so the state it sees is the state on
    entry. Answering with the state after would show a reader the result of the
    line they are looking at.

    `none` when no delta is filed under the key at all — the honest answer, and
    the one that keeps decline-don't-guess: an unrecognised point declines rather
    than falling back to some nearby state. -/
def replayTo (deltas : List PointDelta) (key : Term) : Option PointState :=
  let key := stmtKeyOf key
  if !(deltas.any fun d => match d.stmtKey with | some k => stmtKeyOf k == key | none => false)
  then none
  else
    some <| Id.run do
      let mut st : PointState := {}
      for d in deltas do
        match d.stmtKey with
        | some k => if stmtKeyOf k == key then return st else st := st.step d
        | none => st := st.step d
      return st

/-- What a binder held at a point, with the σ-context to render it against, and
    the ARM TRAIL of the path this answer is from.

    One entry per path that reaches the point. A statement inside a match is
    walked once per branch and legitimately holds different things each time
    (§4), so the surface is handed all of them and decides what to show —
    rather than being handed the first and left to imply it is the only one. -/
def factsAt (paths : List (List PointDelta)) (key : Term) (x : Var) :
    List (List (String × String) × Val × List (Nat × Term)) :=
  paths.filterMap fun deltas =>
    match replayTo deltas key with
    | none => none
    | some st => (st.env.find? (fun kv => kv.1 == x)).map fun kv =>
        -- The trail of the delta filed AT this statement on this path: where the
        -- reader's cursor is, in branch terms.
        let trail := (deltas.find? (fun d =>
          match d.stmtKey with | some k => stmtKeyOf k == stmtKeyOf key | none => false)).map
            (·.trail) |>.getD []
        (trail, kv.2, st.sctx)

/-- The state at the END of the seeding run filed under `key`, provided `x`
    itself was BOUND during that run — the ENTRY point of a `fn` body.

    A telescope occurrence sits inside what the seeds build, so its answer is
    the seeds' result: "entering the body" rather than "entering a statement".
    The seeds file under the `fn`'s own `let`-statement key (the cursor does not
    move between `letStep` and `seedTelescopeV`), so the key is one the surface
    can construct — but the same key also names the `fn` statement in the
    ENCLOSING path, where the run binds the function name rather than the
    parameters. The x-was-bound-in-this-run guard is what tells the two apart:
    a run that did not seed `x` is skipped, and a path with no run that did
    declines. This also keeps a colliding enclosing ⟨id, name⟩ from answering
    for a parameter.

    Known limit, stated rather than hidden: a fn NESTED inside a same-named fn
    shares its ancestor's key, and its ancestor's seeds are in its paths'
    history, so a same-named-and-same-positioned parameter answers from the
    ancestor's run. -/
def replayEntry (deltas : List PointDelta) (key : Term) (x : Var) :
    Option (List (String × String) × PointState) := Id.run do
  let key := stmtKeyOf key
  let mut st : PointState := {}
  let mut inRun := false
  let mut seeded := false
  let mut outer := false
  let mut trail : List (String × String) := []
  for d in deltas do
    let isKey := match d.stmtKey with
      | some k => stmtKeyOf k == key
      | none => false
    if isKey then
      if !inRun then
        inRun := true; seeded := false; outer := false
      if let .bound y _ := d.change then
        -- A run that binds the fn's own `declSlot`-tagged Var is the ENCLOSING
        -- instance of the key — the ledger crosses the seal as a unit, so the
        -- outer stream carries the seeds too, but with the post-restore σ
        -- context and an env the outer scope never had. Skip it; the body
        -- path's own run is the honest one.
        if y.id == declSlot then outer := true
        else if y == x then seeded := true; trail := d.trail
      st := st.step d
    else
      if inRun && seeded && !outer then return some (trail, st)
      inRun := false
      st := st.step d
  if inRun && seeded && !outer then return some (trail, st)
  return none

/-- `factsAt` for ENTRY-tagged occurrences (telescope positions): one entry per
    path whose keyed run seeded the binder. Ancestor prefixes make a body's seed
    run appear in every descendant path too; identical runs render identically
    and collapse in `renderPaths`' distinctness fold. -/
def factsAtEntry (paths : List (List PointDelta)) (key : Term) (x : Var) :
    List (List (String × String) × Val × List (Nat × Term)) :=
  paths.filterMap fun deltas =>
    (replayEntry deltas key x).bind fun (trail, st) =>
      (st.env.find? (fun kv => kv.1 == x)).map fun kv => (trail, kv.2, st.sctx)

/-- **The same walk, with the `let` type table carried out of it** (docs/16).

    Same seed but for `hover`, same paths, same verdict — so a program accepted
    here is accepted by `checkProgramDiag` and rejected here is rejected there,
    by construction rather than by a test. What it adds is the binding-time types
    the surface turns into `x : τ` tooltips.

    Paths are concatenated in walk order and each path's own entries are put back
    into program order, so a key's FIRST entry is the first path's — which is the
    v1 rule, and the reason the surface can say "(differs per path)" without
    merging anything. -/
def checkProgramHover (t : Term) (retType? : Option Term := none)
    (pointHover : Bool := false) :
    Except Diag (List LetNote × List (List PointDelta)) :=
  let paths := programPaths { initSt with hover := true, pointHover } t
  (programVerdict retType? paths).map fun _ =>
    (paths.foldr (fun r acc =>
      match r with
      | .ok (_, st) => st.ledgers.letTypes.reverse ++ acc
      | .error _ => acc) [],
     -- The change history, oldest first WITHIN each path and grouped BY path
     -- (docs/17 §2). Grouped rather than concatenated because a point is a
     -- position ON A PATH (§4): the same statement is walked once per path with
     -- a different state each time, and flattening them would silently answer
     -- with whichever path happened to come first. Empty unless `pointHover`,
     -- which is what makes the option observable.
     paths.flatMap (fun r =>
      match r with
      -- This top-level path's own stream, plus every sealed body path that
      -- finished inside it — each kept separate (docs/17 §4).
      | .ok (_, st) => st.ledgers.points.reverse :: st.ledgers.paths
      | .error _ => []))

/-- **Check a program** (§8): one symbolic ⇒-walk, auditing each path's result at
    `retType`. No table: scope is the call table (§8). -/
def checkProgram (t : Term) (retType : Term := ty{ Unit }) : Except String Unit :=
  Except.mapError Diag.msg (checkProgramDiag t (some retType))

/-- **Run a program** (§8): ⇒-evaluate it, concretely (executing mode — a call
    runs the callee's actual body), and return the final canonicalized Ω.

    **The `id < 10000` frame filter is gone** (M31 Stage 0). It was here — and in
    `programEnvs`, `tailEnvs` and `Programs.rawEnvs` — because a frame's slots
    stayed in Ω forever once the frame had returned, so every harness that read Ω
    had to say "except the frames" to describe what a program leaves. Frames now
    pop, and the whole corpus staying green without the filter is that claim's
    standing assertion: if a frame slot ever survived its frame, it would appear
    here under the callee's own binder name. -/
def runProgram (t : Term) : Except String Env :=
  match (do let _ ← readR defaultFuel (atBoundary t); endScope defaultFuel).run
      { initSt with executing := true } with
  | .ok _ st => .ok (canonicalize st.env)
  | .error e _ => .error e

/-- The symbolic paths' final environments — for inspecting *what* a program
    leaves in Ω, and for the differential's checking side. -/
def programEnvs (t : Term) : List (Except String Env) :=
  (explore defaultFuel (atBoundary t) initSt).map
    (fun r => r.bind (fun p =>
      match (endScope defaultFuel).run p.2 with
      | .ok _ st => .ok (canonicalize st.env)
      | .error e _ => .error e))

/-! ## Test helpers -/

/-- The program checks. -/
def progOk (t : Term) (retType : Term := ty{ Unit }) : Bool :=
  match checkProgram t retType with | .ok _ => true | .error _ => false

/-- The program is rejected, with `needle` in the message.

    Asserted on the message rather than on a Bool for the reason phase A gave:
    `hasType` returns `false` for "does not have this type" and the audit turns
    that into an error, so a helper that collapsed error and false would let a
    *stuckness* pass for a *typing* rejection. -/
def progRejects (t : Term) (needle : String) (retType : Term := ty{ Unit }) : Bool :=
  match checkProgram t retType with
  | .ok _ => false
  | .error e => strContains e needle

/-- **The program RUNS**: ⇒-evaluating it concretely completes, without getting
    stuck. The weaker half of `progRunsTo`, for the case where the final Ω is not
    predictable — a generated body's, say — and the claim is exactly "this is not
    stuck". -/
def progRuns (t : Term) : Bool :=
  match runProgram t with | .ok _ => true | .error _ => false

/-- The program runs to the given final Ω. -/
def progRunsTo (t : Term) (expected : Env) : Bool :=
  match runProgram t with | .ok env => env == expected | .error _ => false

-- (`progRunErr` — the execution counterpart of `progRejects` — retired in M28 ο
-- with zero users. Nothing in the corpus asserts that a program's RUN gets stuck:
-- a rejection is a checking claim, and the differential is what compares the two
-- machines. It is two lines to restore from history if a run-stuckness test is
-- ever wanted.)

/-! ## Inspecting what a program's TAIL leaves (M28 θ)

    A program declares its functions and then runs something, so its Ω carries one
    entry per declaration on top of what the running part left. These are
    `programEnvs` with those entries dropped, which is what makes "what this code
    leaves in Ω" mean the same thing whether the callees are declared beside it or
    somewhere else.

    **They must be dropped BEFORE canonicalization, and that is not a detail.** A
    sealed function IS a σ, so a declaration participates in `canonicalize`'s
    first-appearance σ ordering and shifts the index of every σ after it — filter
    afterwards and an unchanged tail's `y ↦ σ0` reads `σ2`, which would look like a
    rewrite having changed what the code leaves. So the walk is done here and the
    filter asks the VAR whether it is a declaration's.

    **The key is `Var.declSlot`, a tag** (M32 R4). It was `id < FnMacro.progBase`
    — declarations lived above a base, so "not a declaration" was "below 900".
    R4 deleted the arithmetic (name-keyed Ω never read those ids), and this
    projection is the reason the tag exists at all rather than the ids simply
    going: dropping the filter would put every `fn` in the corpus's expected
    environments, and keying it on the VALUE instead would drop `let F = (λ… :
    Π…)`, which is a σ a program deliberately leaves. So the question "is this
    entry a declaration?" is answered by the binder that made it.
    (`Migrate.progEnvsOfT` said the same thing about the same hazard for the
    `FnDef` path; it retired with its users in M28 ο, so this is now the only
    statement of it.) -/
def tailEnvs (t : Term) : List (Except String Env) :=
  (explore defaultFuel (atBoundary t) initSt).map
    (fun r => r.bind (fun p =>
      match (endScope defaultFuel).run p.2 with
      | .ok _ st => .ok (canonicalize (st.env.filter (fun kv =>
          kv.1.id != declSlot)))
      | .error e _ => .error e))

/-- One path, and the tail leaves exactly this Ω. -/
def tailEnv (t : Term) (expected : Env) : Bool :=
  match tailEnvs t with
  | [.ok env] => env == expected
  | _ => false

/-- The symbolic walk forks into exactly these paths, in branch-declaration order,
    each leaving exactly this Ω. The COUNT is half the assertion: a symbolic match
    SPLITS the run, and a check of the environments alone would still pass if the
    forking stopped. -/
def tailPaths (t : Term) (expected : List Env) : Bool :=
  let rs := tailEnvs t
  rs.length == expected.length &&
    (rs.zip expected).all (fun pr => match pr.1 with | .ok env => env == pr.2 | .error _ => false)

/-! ## Module states (docs/20): a block's ending state, persisted

    A module is a `prog` block interpreted once, at its own elaboration; its
    ending `St` is kept and a later block seeds from it. Seeding means literally
    "begin the walk with this state" — the same code path as mid-program state,
    which stage 0 pinned by construction: every runner already threads the
    initial `St` as an explicit parameter, so these functions substitute one. -/

/-- A checked block: the term and the state its walk ends in. `env` is a CACHE
    of the value the prefix-splice semantics assigns ("this program checks
    exactly as if the seed's chain were textually prefixed to it") — `St` is
    strict first-order data in a pure language, so the cache is definitionally
    that value however it is reached. -/
structure Checked where
  term : Term
  env : St

/-- **The seeded program boundary**: `atBoundary` with the seal-site numbering
    threaded. A seeded block's seals number from where the seed's numbering
    stopped (`St.nextSite`) — numbered from 0 they would collide with the keys
    the seed's `sealSites` table already owns, and the collision is silent: the
    consumer's first seal at the same captured inputs REUSES the seed's σ
    (stage-0 finding). Returns the next free site alongside the prepared term so
    the final state can record where THIS block stopped. -/
def moduleBoundary (seed : St) (t : Term) : Nat × Term :=
  let (n', t') := Term.numberSealsGo seed.nextSite t
  (n', pushContinuations t')

/-- The seeded walk's paths, Diag-level, WITHOUT the closing `endScope`: a
    module's bindings must persist into the next block, and `endScope` is the
    demand that would consume them (the probe's `finalSt`). Mode is PINNED to
    checking — a module is interpreted as knowledge, and a chain must be
    mode-consistent (stage-0 finding: a checking-mode seed with `executing`
    flipped on silently takes the checking path anyway, so the pin makes the
    decision explicit rather than emergent). Hover flags ride the seed
    untouched, so the elaborator can run this same walk collecting ledgers. -/
def modulePathsD (seed : St) (t : Term) : Nat × List (Except Diag (Val × St)) :=
  let (n', prepared) := moduleBoundary seed t
  (n', exploreD defaultFuel prepared { seed with executing := false })

/-- **A module's final state**: the single-path walk from `seed`, bindings kept.
    Multi-path is refused — a block that forks has no one ending state to
    persist. Hover collection is pinned OFF here, so a persisted state carries
    empty ledgers regardless of what the seed carried: the judgment-relevant
    projection is the whole value, and state equality on it means what it says
    (docs/20's ledger-equivalence caveat, answered by construction until stage 3
    deliberately puts spans in). -/
def moduleFinalSt (seed : St) (t : Term) : Except String St :=
  let (n', paths) := modulePathsD { seed with hover := false, pointHover := false } t
  match paths with
  | [.ok p] => .ok { p.2 with nextSite := n' }
  | [.error d] => .error d.msg
  | ps => .error s!"module: the walk forked into {ps.length} paths; a module must be single-path"

/-- **Stage 2's resolution table**: the seed's declarations, name → the very
    `Var` the seed's Ω entry holds, newest binding first (Ω resolves
    newest-wins, `findSlot?`). The `[k]` scrutinee hint does NOT travel in `St`
    (stage-0 finding: it is macro-layer state), so every hint is `none` — an
    imported `[k]`-hoisted fn whose scrutinee is not already parameter 0 is not
    yet callable, because its call would be built unpermuted against the hoisted
    telescope. Undetectable from here: the seed holds only the sealed σ and its
    Π, and a hoisted signature is indistinguishable from one declared in that
    order. The hint table joins the ledgers at stage 3. -/
def moduleBinds (seed : St) : List (String × Var × Option Nat) :=
  ((seed.env.filter (fun kv => kv.1.id == declSlot)).map
    (fun kv => (kv.1.name, kv.1, (none : Option Nat)))).reverse

/-- Retarget a consumer block's unresolved `.call`s at the seed's declarations —
    the same app-spine build `FnMacro.retarget` does for local `fn`s, from the
    same function, so an imported call and a local call are one shape. -/
def moduleRetarget (seed : St) (t : Term) : Term :=
  FnMacro.retarget (moduleBinds seed) t

/-- The value a `prog () { … }` / `prog (e) { … }` block elaborates to. The
    state is RE-DERIVED by the walk rather than quoted — `St` needs no `ToExpr`
    — and by purity it is the value the elaboration-time check computed: that
    check ran the same walk from the same seed, differing only in the hover
    ledgers, which `moduleFinalSt` pins empty. The error branch is a documented
    panic, not a rejection channel: elaboration already REJECTED any block whose
    walk fails, so this branch is reachable only by calling it directly on a
    term the surface never accepted. -/
def Checked.seeded (seed : St) (t : Term) : Checked :=
  let t := moduleRetarget seed t
  { term := t
    env := match moduleFinalSt seed t with
      | .ok st => st
      | .error e => panic! s!"Checked.seeded: the module walk failed after elaboration accepted it — {e}" }

end Dllbc
