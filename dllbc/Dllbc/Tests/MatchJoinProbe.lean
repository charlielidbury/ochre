import Dllbc.Boundary

/-! # Stage 0 viability probe for docs/19 (match environment unification)

    NOT in the build. A standalone join driver assembled from the machine's own
    public pieces — no library edits — probing the §3.4 composition risk:
    continuation-from-St₀ with re-minted payloads, under the fn-level audit.

    The driver here is deliberately NAIVE: no slot-diff (arms are assumed to
    touch only the scrutinee and their own scope), owned/borrow sym dispatch
    only. Its job is to answer "does the join state compose with exploreD and
    auditPaths", not to be the Stage 2 driver. -/

namespace Dllbc.Tests.MatchJoinProbe
open Dllbc

abbrev PathsD := List (Except Diag (Val × St))

def natT  : Term := .const "Nat"
def boolT : Term := .const "Bool"
def unitT : Term := .const "Unit"
def listNatT : Term := .app (.const "List") natT

/-- First arm error wins, else all (value, exit-state) pairs. -/
def collectOks (ps : PathsD) : Except Diag (List (Val × St)) :=
  ps.foldr (fun p acc => do pure ((← p) :: (← acc))) (pure [])

/-- Advance the mint counters past every arm exit, so post-join mints cannot
    collide with arm-minted ids (the `auditAllPathsD` move). -/
def bumpCounters (base : St) (exits : List St) : St :=
  exits.foldl (fun a s =>
    { a with nextLoan := max a.nextLoan s.nextLoan,
             nextVar := max a.nextVar s.nextVar,
             nextSym := max a.nextSym s.nextSym,
             nextGroup := max a.nextGroup s.nextGroup }) base

/-- The seam check on one arm result: the typing half of `auditAction` — the
    botElim ex-falso escape, then `hasType` against the arm's own `retTyVal`,
    which holds the MOTIVE as this arm's refinement rewrote it. -/
def armSeamCheck (fuel : Nat) (v : Val) : M Unit := do
  match (← get).retTyVal with
  | none => throwErr "join probe: arm state lost its motive"
  | some motiveArm =>
    match (match v with | .know t => Pure.collectSpineT t | _ => (.unit, [])) with
    | (.const "botElim", [_, x]) =>
      if ← hasTypeT fuel x (.const "Bot") then pure ()
      else throwErr s!"join: botElim arm result on a non-⊥ argument ({x.pretty})"
    | _ =>
      if ← hasType fuel v motiveArm then pure ()
      else throwErr s!"join: arm result ({v.pretty}) does not have the motive ({motiveArm.pretty})"

/-- The probe join driver, continuation-style so joins sequence.
    `x` is bound to a fresh σ : motive; the continuation `k` runs ONCE. -/
def joinMatchK (fuel : Nat) (x scrut : Var) (motive : Term)
    (branches : List Branch) (k : St → PathsD) (st : St) : PathsD :=
  match (do noteStmt (.matchE scrut none none branches)
            fenceComptime scrut "cannot be the scrutinee of a runtime match"
            let mv ← readC fuel motive
            let d ← reorgScrut fuel scrut
            pure (mv, d)).run st with
  | .error e s => [.error (Diag.of e s)]
  | .ok (mv, disp) stR =>
    let picked : Option (Nat × (Branch → M Term) × M Unit) := match disp with
      | .ownedSym σ stuck =>
        some (σ, symOwnedSetup fuel scrut σ stuck none, setSlot scrut .bot)
      | .borrowSym ℓ σ =>
        -- Arms may have written through the borrow: re-mint the payload as a
        -- fresh σ' at the scrutinee σ's own type (probe stand-in for the owed
        -- type off the loan's debt — same term for a plain `&mut τ` parameter).
        some (σ, symBorrowSetup fuel scrut ℓ σ none, do
          match (← get).sctx.lookup σ with
          | none => throwErr "join probe: borrow scrutinee σ untyped"
          | some τs => do
            let σ' ← freshSym
            modify fun s => { s with sctx := (σ', τs) :: s.sctx }
            setSlot scrut (.borrowM ℓ (.know (.sym σ'))))
      | _ => none
    match picked with
    | none => [.error { msg := "join probe: unsupported dispatch (concrete scrutinee)" }]
    | some (σ, setup, scrutJoin) =>
      match (checkExhaustive fuel σ branches).run stR with
      | .error e s => [.error (Diag.of e s)]
      | .ok _ st0 =>
        let armPaths : PathsD := (branches.map (fun br =>
          match (setup br).run st0 with
          | .error e s => [Except.error (Diag.of e s)]
          | .ok body st' =>
            -- The arm carries the MOTIVE in retTyVal, so refineSym instantiates
            -- it per-arm for free (the refinement sweeps retTyVal).
            (exploreD fuel body { st' with retTyVal := some mv }).map (fun p =>
              match p with
              | .error d => .error d
              | .ok (v, stA) =>
                match (armSeamCheck fuel v).run stA with
                | .error e s => .error (Diag.of e s)
                | .ok _ stA' => .ok (v, stA')))).flatten
        match collectOks armPaths with
        | .error d => [.error d]
        | .ok exits =>
          let stM := bumpCounters st0 (exits.map (·.2))
          let joinAct : M Unit := do
            scrutJoin
            let σb ← freshSym
            modify fun s => { s with sctx := (σb, motive) :: s.sctx }
            bindSlot x (.know (.sym σb))
          match joinAct.run stM with
          | .error e s => [.error (Diag.of e s)]
          | .ok _ stJ => k stJ

/-- Seed a telescope and drive, then audit — `checkRFnBody`'s skeleton with the
    driver spliced where `exploreD (pushContinuations body)` sits. -/
def checkBodyWith (tel : List (Var × Term)) (ret : Term) (drive : St → PathsD) : String :=
  let m : M PathsD := do
    let obs ← seedTelescopeV defaultFuel tel
    let borrowIds := borrowVarIds tel
    let exits ← borrowIds.mapM (fun i => do pure (i, ← freshSym))
    modify fun s => { s with exitSyms := exits, debts := obs }
    let rv ← readC defaultFuel ret
    modify fun s => { s with retTyVal := some rv }
    let st0 ← get
    pure (drive st0)
  match m.run initSt with
  | .error e _ => s!"seed error: {e}"
  | .ok paths _ =>
    match auditPaths ret (paths.map (Except.mapError Diag.msg)) with
    | .ok _ => s!"OK ({paths.length} path(s))"
    | .error e => s!"REJECTED ({paths.length} path(s)): {e}"

end Dllbc.Tests.MatchJoinProbe

namespace Dllbc.Tests.MatchJoinProbe
open Dllbc

def fuel : Nat := defaultFuel
def vN : Var := ⟨0, "n"⟩
def vM : Var := ⟨1, "m"⟩
def vV : Var := ⟨0, "v"⟩
def vB : Var := ⟨100, "b"⟩
def vC : Var := ⟨101, "c"⟩
def vD : Var := ⟨102, "d"⟩
def vK : Var := ⟨103, "k"⟩
def vK2 : Var := ⟨104, "k2"⟩
def vHd : Var := ⟨105, "hd"⟩
def vTl : Var := ⟨106, "tl"⟩
def vW : Var := ⟨107, "w"⟩

def armsBoolN : List Branch :=
  [ .mk "Z" [] (.ctorApp "True" []), .mk "S" [vK] (.ctorApp "False" []) ]
def armsBoolM : List Branch :=
  [ .mk "Z" [] (.ctorApp "True" []), .mk "S" [vK2] (.ctorApp "False" []) ]

-- (A) `let b : Bool = match n { Z => True, S(k) => False }; let c = b; ()`
#eval IO.println ("A one join, continuation once:  " ++
  checkBodyWith [(vN, natT)] unitT
    (joinMatchK fuel vB vN boolT armsBoolN
      (fun st => exploreD fuel (.letIn vC (.var vB) .unit) st)))

-- (B) two SEQUENTIAL joined matches — the 2^N shape, expect ONE path out.
#eval IO.println ("B two sequential joins:         " ++
  checkBodyWith [(vN, natT), (vM, natT)] unitT
    (joinMatchK fuel vB vN boolT armsBoolN
      (joinMatchK fuel vC vM boolT armsBoolM
        (fun st => exploreD fuel (.letIn vD (.var vB) .unit) st))))

-- (C) THE §3.4 RISK: borrow-mode scrutinee, an arm WRITES through a field
-- borrow, the join re-mints the payload, the continuation reads and writes
-- back through the parent borrow, and the fn-level audit must still pass.
def armsListWrite : List Branch :=
  [ .mk "Nil" [] .unit,
    .mk "Cons" [vHd, vTl] (.assign (.deref (.var vHd)) Term.zero .unit) ]
#eval IO.println ("C borrow arms write, audit:     " ++
  checkBodyWith [(vV, .borrowT "s" listNatT listNatT)] unitT
    (joinMatchK fuel vB vV unitT armsListWrite
      (fun st => exploreD fuel
        (.letIn vW (.deref (.var vV))
          (.assign (.deref (.var vV)) (.var vW) .unit)) st)))

-- (D) the weakening pin: post-join σb is OPAQUE Bool — a continuation match
-- with only a True branch must be rejected NON-EXHAUSTIVE (under the fork, b
-- is concrete per path and the True path would sail through selection).
#eval IO.println ("D join is a weakening:          " ++
  checkBodyWith [(vN, natT)] unitT
    (joinMatchK fuel vB vN boolT armsBoolN
      (fun st => exploreD fuel
        (pushContinuations (.seq (.matchE vB none none [.mk "True" [] .unit]) .unit)) st)))

end Dllbc.Tests.MatchJoinProbe
