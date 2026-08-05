import Dllbc.Machine

/-!
# Boundaries: telescopes, `checkFn`, and the audit at return (§5)

The milestone the calculus has been aiming at. A function is checked once
against its signature: seed the telescope (each argument a fresh symbolic
value or an argument borrow), explore the body (one path per symbolic branch),
and — the ONLY check in the whole borrow story (§5.4) — audit each path at
return: every argument borrow must hold a value of its owed type, and the
result must have the return type.

The call rule (§5.3) is deliberately NOT here — calls are a later milestone.
This module makes the machine a *type checker* for closed function bodies:
`push` for lists and the Σ-paired `VecF` push check end-to-end.
-/

namespace Dllbc

-- `Obligation` now lives in `Machine.lean` (so it can be an `St` field that a
-- §10 Refl refinement reaches — see its docstring there).

-- `seedTelescope`, `collapseArg`, `reachesLoan`, `auditObligation`,
-- `resolveTree`, `collectResultBorrows` and `auditAction` moved to
-- `Machine.lean` (M26-C): the seal rule runs the audit AT THE NODE, from
-- inside `readR`, so the audit has to precede it. Same names, same
-- namespace, unchanged — every use site here and in the corpus is as it was.


/-- Audit every explored path; the whole function checks iff all do. Each path
    carries its own (refinement-updated) obligations in `St`. -/
def auditPaths (retType : Term) :
    List (Except String (Val × St)) → Except String Unit
  | [] => .ok ()
  | .error e :: _ => .error e
  | .ok (v, st) :: rest =>
    match (auditAction defaultFuel retType v).run st with
    | .error e _ => .error e
    | .ok _ _ => auditPaths retType rest

-- `hasBorrowT` moved to `Syntax.lean` (M26-A): the seal rule lives in `Machine`,
-- which cannot import `Boundary`. Same name, same namespace — every use site is
-- unchanged.

/-- Check a function declaration end-to-end: seed the telescope, explore the
    body (one path per symbolic branch), audit each path at return. `table` is
    the function context calls resolve against (signature-only, §5.3) — it
    includes `decl` itself for recursion. -/
def checkFn (table : List Decl) (decl : Decl) : Except String Unit :=
  -- M27 SOUNDNESS CONTAINMENT, before anything else runs: refuse a return type
  -- that mixes borrow and non-borrow components. See `retMixesBorrow` for why the
  -- mixture is unsound rather than merely unchecked.
  if retMixesBorrow decl.retType then
    .error s!"return type: '{decl.name}' a borrow-carrying return type may not also carry VALUE components. A borrow-returning function is audited structurally — each issued borrow against its owed type — and the value check is skipped for the whole type, so a non-borrow component here would be judged by nothing and the caller would still receive it as a proof. A cursor's sayable contract is its issued borrows' owed types; state value claims on a value-returning function, where they are checked."
  else
  -- Seed the telescope, then pin the (value) return type while the params are
  -- still live (§5.3): a dependent return type may mention a param the body
  -- consumes, so it must be evaluated at entry, not re-read at return. A
  -- borrow-carrying return is not pinned (it is audited structurally instead).
  let seed : M (List Obligation) := do
    let obs ← seedTelescope defaultFuel 0 decl.telescope
    -- §5.4 exit-snapshot: mint one σ_exit per borrow param and record it (ONLY in
    -- exitSyms — never sctx/obligations — until the audit defines it). The return
    -- type is `markExit`-transformed so a bare `*v` pins to σ_exit and `old *v` to
    -- the entry σ, before the entry pin.
    let borrowIds := borrowParamIds decl.telescope
    let exits ← borrowIds.mapM (fun i => do pure (i, ← freshSym))
    modify (fun s => { s with exitSyms := exits })
    if hasBorrowT decl.retType then pure ()
    else do
      let rv ← readC defaultFuel (markExit borrowIds decl.retType)
      modify (fun s => { s with retTyVal := some rv })
    -- §8's snapshot-subterm guard: record who is being checked, and — if `[k]` is
    -- declared — the decreasing parameter's snapshot AS SEEDED. From here it rides
    -- `refineSym` with the rest of the σ-bearing state, so at a self-call it reads
    -- whatever the enclosing matches have refined it to.
    let dk ← match decl.dec with
      | none => pure none
      | some k =>
        match decl.telescope.get? k with
        | none => throwErr s!"recursion: '{decl.name}' declares decreasing argument [{k}], which is out of range for its {decl.telescope.length}-parameter telescope"
        | some (nm, _) => do
          -- A borrow parameter decreases through its PAYLOAD snapshot — which is
          -- §8's guard in its most literal form, and the only thing that shrinks in
          -- a list cursor (`zero_all(tl)` passes no counter at all). Snapshots are
          -- entry-knowledge and are never rewritten by mutation (§3.2), so the
          -- payload's structural decomposition is a fixed, well-founded order.
          match ← lookupSlot ⟨k, nm⟩ with
          | .borrowM _ payload => pure (some (k, payload))
          | v => pure (some (k, v))
    modify (fun s => { s with selfRec := some (decl.name, dk) })
    pure obs
  match seed.run { initSt with decls := table } with
  | .error e _ => .error e
  | .ok obs st => auditPaths decl.retType (explore defaultFuel (pushContinuations decl.body) { st with obligations := obs })

/-- Run a declaration's body (no audit), returning one canonicalized final Ω
    per path — for inspecting *what* a body leaves in Ω (e.g. §5.3's fresh
    existential y). -/
def runFn (table : List Decl) (decl : Decl) : List (Except String Env) :=
  match (seedTelescope defaultFuel 0 decl.telescope).run { initSt with decls := table } with
  | .error e _ => [.error e]
  | .ok _ st => (explore defaultFuel (pushContinuations decl.body) st).map
      (fun r => r.map (fun p => canonicalize p.2.env))

/-! ## Test helpers -/

/-- The declaration checks. `table` defaults to `[decl]` (self-recursion). -/
def checkFnOk (decl : Decl) (table : List Decl := [decl]) : Bool :=
  match checkFn table decl with | .ok _ => true | .error _ => false

/-- The declaration is rejected with an error containing `needle`. -/
def checkFnErr (decl : Decl) (needle : String) (table : List Decl := [decl]) : Bool :=
  match checkFn table decl with | .ok _ => false | .error e => strContains e needle

/-- A single-path body leaves exactly the given final Ω (for inspecting §5.3's
    fresh existential). -/
def expectFnEnv (table : List Decl) (decl : Decl) (expected : Env) : Bool :=
  match runFn table decl with
  | [.ok env] => env == expected
  | _ => false

end Dllbc
