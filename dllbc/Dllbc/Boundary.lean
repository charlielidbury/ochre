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

/-- Seed the telescope into Ω and `sctx`, returning the borrow obligations.
    Argument `i` gets runtime var id `i`. A pure (unrestricted) type τ →
    `x ↦ sym σ`, `sctx[σ : τ]`. A borrow type `&mut (s : τ ↝ S)` → fresh ℓ and
    σ, `x ↦ borrowM ℓ (sym σ)`, `sctx[σ : τ]`, and an obligation carrying `S`
    instantiated at `s := σ`. Crucially there is NO owner entry for an argument
    borrow's loan — the caller holds it; nothing in the body can collapse the
    borrow by owner-demand, only the audit can. -/
def seedTelescope (fuel : Nat) : Nat → List (String × Term) → M (List Obligation)
  | _, [] => pure []
  | i, (name, tyTerm) :: rest => do
    let x : Var := ⟨i, name⟩
    match tyTerm with
    | .borrowT τ S => do
      let τVal ← readC fuel τ
      let σ ← freshSym
      let ℓ ← freshLoan
      bindSlot x (.borrowM ℓ (.sym σ))
      -- record σ as this borrow's entry snapshot (§5.4 `old *v`).
      modify (fun s => { s with sctx := (σ, τVal) :: s.sctx, entrySyms := (x.id, σ) :: s.entrySyms })
      let SVal ← readC fuel S
      let owed := Val.nfV fuel (Val.substPure 0 (Val.sym σ) SVal)   -- S[s := σ]
      pure (⟨x, ℓ, owed⟩ :: (← seedTelescope fuel (i + 1) rest))
    -- ¶4's RUNTIME-LENGTH SLICE, `Σ (c : Nat). &mut (Array c T)`, as a parameter.
    -- §5's second opacity ("borrows stored under a type constructor") reaching a
    -- telescope entry for the first time. The slot holds a genuine pair — a length
    -- and a borrow — so the length is a σ the body can name, and the borrow carries
    -- an ordinary obligation. PROBE (M24 STEP 1): see `docs/DELTAS.md` G2 for why
    -- this is not enough on its own.
    | .sigmaT aTy (.borrowT τ S) => do
      let aVal ← readC fuel aTy
      let σc ← freshSym
      modify (fun s => { s with sctx := (σc, aVal) :: s.sctx })
      let τVal := Val.substPure 0 (.sym σc) (← readC fuel τ)
      let σ ← freshSym
      let ℓ ← freshLoan
      bindSlot x (.ctor "Pair" [.sym σc, .borrowM ℓ (.sym σ)])
      modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
      -- `S` binds the payload snapshot at pvar 0; the Σ's own binder sits at pvar 1
      -- and drops to 0 once the payload is substituted.
      let SVal ← readC fuel S
      let owed := Val.nfV fuel (Val.substPure 0 (.sym σc) (Val.substPure 0 (.sym σ) SVal))
      pure (⟨x, ℓ, owed⟩ :: (← seedTelescope fuel (i + 1) rest))
    | tyTerm => do
      let τVal ← readC fuel tyTerm
      let σ ← freshSym
      bindSlot x (.sym σ)
      modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
      seedTelescope fuel (i + 1) rest

/-- Collapse an argument borrow's payload at the boundary: End-Mut every loan
    marker in the payload whose borrow is an Ω entry (this is how §3.3's field
    loans collapse at a real boundary — there being no owner to demand it).
    Errors distinctively if a marker's borrow is missing (via `endMut`). -/
def collapseArg : Nat → Var → M Unit
  | 0, _ => throwErr "audit: out of fuel (collapse)"
  | fuel + 1, arg => do
    match ← lookupSlot arg with
    | .borrowM _ payload =>
      match firstLoanMarker payload with
      | some ℓ => do endLoan fuel ℓ; collapseArg fuel arg   -- normal or group (§6.1) loan
      | none => pure ()
    | _ => pure ()

/-- Does borrow `ℓ` transitively reborrow into `target`? An `advance`-style body
    returns a reborrow of a FIELD of an argument borrow (`&mut *hd` after
    matching `v`); that argument is then the CAPTURED OWNER of the issued result
    and must be exempt from the callee-side obligation audit, exactly as a
    directly-returned borrow is (§6.1) — its field loan is legitimately in
    flight. We follow the loan markers parked in each borrow's payload down to
    the result loan. -/
partial def reachesLoan (ℓ target : Nat) : M Bool := do
  if ℓ == target then pure true
  else
    -- (a) reborrow chain: loan markers parked in ℓ's payload.
    let viaBorrow ← match (← getEnv).findSome? (fun kv => findBorrowPayload ℓ kv.2) with
      | some payload => (Val.loanIds payload).anyM (fun ℓc => reachesLoan ℓc target)
      | none => pure false
    if viaBorrow then pure true
    else
      -- (b) group link: if ℓ was captured by a call, that call's issued borrows
      -- are reachable through it — this is how a returned reborrow that came out
      -- of a recursive call connects back to the argument that fed the call.
      let grps := (← get).groups
      (grps.filter (fun g => g.captured.any (·.1 == ℓ))).anyM (fun g =>
        g.issued.anyM (fun iss => reachesLoan iss.1 target))

/-- Audit one argument-borrow obligation (§6.1's narrowed rule). `resultLoan`
    is the returned borrow's loan (for a borrow-returning body). Exempt iff the
    borrow was consumed into the result (directly, or as the captured owner of a
    field reborrow that became the result) OR into another call (its loan is
    captured by some group). Otherwise it must be **locatable** — as a live
    `borrowM ℓ` anywhere in Ω's values, not just at its own slot (it may have
    been moved into a local value) — and its (collapsed) payload is typed
    against the owed type. Neither locatable nor continued rejects distinctively. -/
def auditObligation (fuel : Nat) (resultLoans : List Nat) (ob : Obligation) : M Unit := do
  if resultLoans.contains ob.loan then pure ()                            -- consumed into a result borrow
  else if (← resultLoans.anyM (fun rl => reachesLoan ob.loan rl)) then pure ()  -- captured owner of a field reborrow
  else if (← get).groups.any (fun g => g.captured.any (·.1 == ob.loan)) then pure ()  -- into another call
  else
    -- Still at its own slot? collapse its field loans first, in place.
    match ← lookupSlot ob.arg with
    | .borrowM _ _ => collapseArg fuel ob.arg
    | _ => pure ()
    -- Locate the borrow anywhere in Ω and audit its payload.
    match (← getEnv).findSome? (fun kv => findBorrowPayload ob.loan kv.2) with
    | none =>
      throwErr s!"audit: argument borrow {ob.arg.name} (ℓ{ob.loan}) is neither locatable in Ω nor continued into a call — it was lost"
    | some .bot =>
      throwErr s!"audit: argument borrow {ob.arg.name} (ℓ{ob.loan}) holds a hole (⊥) at return — take without refill"
    | some payload =>
      if ← hasType fuel payload ob.owed then pure ()
      else throwErr s!"audit: {ob.arg.name}'s payload ({payload.pretty}) does not have its owed type ({ob.owed.pretty})"

/-- Reconstruct a captured borrow's payload as the §6.2 suspension tree with
    holes: follow each loan marker — an ISSUED loan (reached directly or down its
    reborrow chain) becomes the fresh de Bruijn hole `pvar i`; a non-issued field
    loan collapses to its current payload (the field the body left in place). The
    result is the backward function the body implements, to convert against the
    declared spec. -/
partial def resolveTree (issued : List Nat) : Val → M Val
  | .loanM ℓ => do
    match issued.findIdx? (· == ℓ) with
    | some i => pure (.pvar i)
    | none =>
      -- captured by a sub-call's group? its release is the sub-spec applied to
      -- (the resolved) issued borrows — LLBC's backward function composing.
      match (← get).groups.find? (fun g => g.captured.any (·.1 == ℓ)) with
      | some g =>
        match g.backSpec with
        | some f => do
          let ievs ← g.issued.mapM (fun p => resolveTree issued (.loanM p.1))
          pure (Val.nfV 1000 (Val.rebuildSpine f ievs))
        | none => pure (.loanM ℓ)                        -- opaque sub-group — unresolvable
      | none => match (← getEnv).findSome? (fun kv => findBorrowPayload ℓ kv.2) with
        | some p => resolveTree issued p                 -- follow the reborrow chain / collapse
        | none => pure (.loanM ℓ)
  | .borrowM ℓ p =>
    match issued.findIdx? (· == ℓ) with
    | some i => pure (.pvar i)
    | none => do pure (.borrowM ℓ (← resolveTree issued p))
  | .ctor n args => do pure (.ctor n (← args.mapM (resolveTree issued)))
  | v => pure v

/-- Walk a return type against the result value, collecting each borrow position
    as `(issued loan, payload, owed type)`. `none` = value-returning (no borrow);
    a `Σ`/`Pair` of borrows gives the multi-issued list (`nth2`, §6.1). -/
def collectResultBorrows (fuel : Nat) : Term → Val → M (Option (List (Nat × Val × Val)))
  | .borrowT _ S, .borrowM ℓ payload => do
    let owed := Val.nfV fuel (Val.substPure 0 payload (← readC fuel S))
    pure (some [(ℓ, payload, owed)])
  | .borrowT _ _, other =>
    throwErr s!"audit: borrow-returning body did not return a borrow (got {other.pretty})"
  | .sigmaT a b, .ctor "Pair" [va, vb] => do
    let ra ← collectResultBorrows fuel a va
    let rb ← collectResultBorrows fuel b vb
    match ra, rb with
    | none, none => pure none                        -- a genuine value pair, not borrows
    | _, _ => pure (some (ra.getD [] ++ rb.getD []))
  | _, _ => pure none                                -- value-returning
  termination_by t _ => sizeOf t

/-- The audit for one path. A **value-returning** body (§5.4): every argument
    borrow meets its obligation and the result has the (entry-pinned) return
    type. A **borrow-returning** body (§6.1 callee side): the result carries one
    or more issued borrows (a single `&mut`, or a `Pair` of them — the
    multi-issued group); each argument borrow that was consumed into a result
    borrow (directly or as its captured owner) is exempt, the rest meet their
    obligations, and every issued borrow's payload has its owed type. -/
def auditAction (fuel : Nat) (retType : Term) (resultVal : Val) : M Unit := do
  let obs := (← get).obligations                    -- this path's (refined) obligations
  -- Ex falso: a branch whose result is `botElim _ x` with `x : ⊥` is
  -- unreachable (a bounds-proof `nth`'s `Nil` branch, where `p : Le (S i) 0 = ⊥`).
  -- It is vacuously well-formed at ANY return type — no borrow/obligation audit,
  -- and the `botElim` motive need not be the (unreflectable) borrow return type.
  match Val.collectSpine resultVal with
  | (.const "botElim", [_, x]) =>
    if ← hasType fuel x (.const "Bot") then pure ()
    else throwErr s!"audit: botElim result on a non-⊥ argument ({x.pretty})"
  | _ =>
  match ← collectResultBorrows fuel retType resultVal with
  | some checks => do
    let issuedLoans := checks.map (·.1)
    obs.forM (auditObligation fuel issuedLoans)
    checks.forM (fun c =>
      let (_, payload, owed) := c
      do if ← hasType fuel payload owed then pure ()
         else throwErr s!"audit: returned borrow's payload ({payload.pretty}) does not have its owed type ({owed.pretty})")
    -- §6.2 callee check: if a backward spec is declared, the captured borrow's
    -- payload-with-issued-holes must convert with the spec applied to fresh hole
    -- variables. The suspension tree IS the backward function; we check the
    -- DECLARED one against it (sound where M8's inferred wire was not).
    match (← get).selfBack with
    | none => pure ()
    | some backV => do
      -- the captured borrow: the (single) obligation consumed into a result,
      -- directly (`through` — its loan IS a result loan) or as a field reborrow's
      -- owner (`advance`/`nth2` — it reaches a result loan).
      let caps ← obs.filterMapM (fun ob => do
        let direct := issuedLoans.contains ob.loan
        let viaField ← issuedLoans.anyM (fun rl => reachesLoan ob.loan rl)
        pure (if direct || viaField then some ob else none))
      match caps.head? with
      | none => pure ()                                  -- no captured borrow to check
      | some ob =>
        -- the tree with holes: the captured borrow's payload (or, if it WAS the
        -- returned borrow, the hole itself), resolved down the reborrow chains.
        let raw : Val ← match (← getEnv).findSome? (fun kv => findBorrowPayload ob.loan kv.2) with
          | some payload => pure payload
          | none => pure (.loanM ob.loan)                  -- returned directly
        let tree ← resolveTree issuedLoans raw
        let holes := (List.range issuedLoans.length).map Val.pvar
        let spec := Val.nfV fuel (Val.rebuildSpine backV holes)
        if Val.convert fuel tree spec then pure ()
        else throwErr s!"audit: declared backward spec ({spec.pretty}) does not match the body's suspension tree ({tree.pretty})"
  | none => do
    obs.forM (auditObligation fuel [])
    -- §6.2 for a value/Unit-returning body that mutates an argument borrow IN
    -- PLACE (swapS, partScan): the back spec describes what the argument borrow's
    -- payload becomes, and there are no issued result borrows — so the spec is
    -- applied to NO holes and checked against the borrow's suspension tree
    -- directly. (Without this, an in-place fn's back was unchecked at the callee
    -- and only validated by the differential — the M20 finding.)
    match (← get).selfBack with
    | none => pure ()
    | some backV => do
      let spec := Val.nfV fuel (Val.rebuildSpine backV [])
      -- Check the back against the argument borrow's suspension tree WHERE it is
      -- directly locatable (untouched, or composed from Unit-returning sub-groups
      -- whose declared backs the spec is authored from — partScan). NOT resolved
      -- through a sub-call that ISSUES borrows with a REFORMULATED back (swapS's
      -- `swapL` vs nth2's set-based tree): those backs are higher-level than the
      -- raw tree, so they never convert and stay differential-validated (M17).
      match obs.head? with
      | none => pure ()
      | some ob =>
        match (← getEnv).findSome? (fun kv => findBorrowPayload ob.loan kv.2) with
        | some payload => do
          let tree ← resolveTree [] payload
          if Val.convert fuel tree spec then pure ()
          else throwErr s!"audit: declared backward spec ({spec.pretty}) does not match the body's suspension tree ({tree.pretty})"
        | none => pure ()
    -- The return type was pinned at entry (§5.3 dependent types over consumed
    -- params); fall back to reading it here only if it was never pinned.
    let retTy0 ← match (← get).retTyVal with
      | some v => pure v
      | none => readC fuel retType
    -- §5.4 exit-snapshot: DEFINE each borrow's σ_exit as its collapsed final
    -- payload — a bare `*v` in the return type thus reads the EXIT value. This is a
    -- dedicated audit-local substitution (plain substSym over retTy), NOT refineSym:
    -- σ_exit is a fresh name being defined here, so no mutation result ever flows
    -- through ⇜'s knowledge channel and the §3.2 assertion is unconcerned.
    --
    -- The payload goes through ¶1.3's ⇝ FOLD first, exactly as `readC` does for
    -- every other comptime reading. Without it the exit snapshot of a carved array
    -- is the STATE form — a `§segs` node — on which no predicate computes, so any
    -- postcondition naming `*v` is stuck. It never showed before because merge
    -- concatenates adjacent RUNS, so a concrete-extent carve rejoins to a plain run
    -- and needs no fold; a SYMBOLIC segment cannot merge (only runs do), and that is
    -- the case every in-place array program is made of.
    let exits := (← get).exitSyms
    let retTy ← obs.foldlM (fun acc ob =>
      match exits.lookup ob.arg.id with
      | none => pure acc
      | some σ => do
        match (← getEnv).findSome? (fun kv => findBorrowPayload ob.loan kv.2) with
        | some payload => pure (Val.nfV fuel (substSym σ (Val.arrFoldDeep payload) acc))
        | none => pure acc) retTy0
    if ← hasType fuel resultVal retTy then pure ()
    else throwErr s!"audit: result ({resultVal.pretty}) does not have return type ({retTy.pretty})"

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
    -- §6.2: reflect this fn's own declared backward spec over the seeded
    -- telescope snapshots, so the callee audit can check the body against it.
    match decl.back with
    | some b => do
      let bv ← readC defaultFuel b
      modify (fun s => { s with selfBack := some bv })
    | none => pure ()
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
