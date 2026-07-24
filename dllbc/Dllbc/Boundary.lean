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

/-- What an argument borrow owes at the boundary: its slot variable, its loan
    id, and the owed type (§5.1's `S`, instantiated at the entry snapshot).
    (`Decl` itself now lives in `Machine.lean` so the call rule can see it.) -/
structure Obligation where
  arg : Var
  loan : Nat
  owed : Val

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
      modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
      let SVal ← readC fuel S
      let owed := Val.nfV fuel (Val.substPure 0 (Val.sym σ) SVal)   -- S[s := σ]
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
      | some ℓ => do endLoan ℓ; collapseArg fuel arg     -- normal or owed (§5.3) loan
      | none => pure ()
    | _ => pure ()

/-- Audit one obligation: collapse the borrow, reject a hole (⊥ — the
    take-without-refill of §2.4/§4.1), else type the payload against its owed
    type. -/
def auditOne (fuel : Nat) (ob : Obligation) : M Unit := do
  collapseArg fuel ob.arg
  match ← lookupSlot ob.arg with
  | .borrowM _ payload =>
    match payload with
    | .bot => throwErr s!"audit: argument {ob.arg.name} holds a hole (⊥) at return — take without refill"
    | _ =>
      if ← hasType fuel payload ob.owed then pure ()
      else throwErr s!"audit: {ob.arg.name}'s payload ({payload.pretty}) does not have its owed type ({ob.owed.pretty})"
  | _ => throwErr s!"audit: argument {ob.arg.name} is not a borrow at return"

/-- The §5.4 audit for one path: every argument borrow meets its obligation,
    and the result has the return type. -/
def auditAction (fuel : Nat) (retType : Term) (obs : List Obligation) (resultVal : Val) : M Unit := do
  obs.forM (auditOne fuel)
  let retTy ← readC fuel retType
  if ← hasType fuel resultVal retTy then pure ()
  else throwErr s!"audit: result ({resultVal.pretty}) does not have return type ({retTy.pretty})"

/-- Audit every explored path; the whole function checks iff all do. -/
def auditPaths (retType : Term) (obs : List Obligation) :
    List (Except String (Val × St)) → Except String Unit
  | [] => .ok ()
  | .error e :: _ => .error e
  | .ok (v, st) :: rest =>
    match (auditAction defaultFuel retType obs v).run st with
    | .error e _ => .error e
    | .ok _ _ => auditPaths retType obs rest

/-- Check a function declaration end-to-end: seed the telescope, explore the
    body (one path per symbolic branch), audit each path at return. `table` is
    the function context calls resolve against (signature-only, §5.3) — it
    includes `decl` itself for recursion. -/
def checkFn (table : List Decl) (decl : Decl) : Except String Unit :=
  match (seedTelescope defaultFuel 0 decl.telescope).run { initSt with decls := table } with
  | .error e _ => .error e
  | .ok obs st => auditPaths decl.retType obs (explore defaultFuel (pushContinuations decl.body) st)

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
