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

/-! ## `checkFn` is gone (M27-δ)

    The declaration path — `checkFn`, `runFn`, `checkFnOk`, `checkFnErr`,
    `expectFnEnv` — is deleted, and with it the `[k]` guard it fed (`St.selfRec`
    was set here and nowhere else, so the guard was dead the moment this went).
    The two had to leave in ONE commit: removing the guard alone would have left
    this function admitting `fn recBad () -> Id Nat Z (S Z) { recBad() }`, since
    signature-only checking admits a self-call at the function's own declared
    return type and the decrease was that rule's side condition.

    What replaced it is not another check. §8 makes a program a term and scope the
    let-chain, so `checkProgram` — one symbolic ⇒-walk plus the audit of each
    path's result — is the whole of it, and a self-call resolves to nothing
    because a let-chain cannot reference downward. `auditPaths` above is the only
    thing this file still contributes, and it is shared with that walk. -/

end Dllbc
