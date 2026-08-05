import Dllbc.Machine

/-!
# `fn` is a macro (M26-D)

`combining-fns.md` §7 promotes "guarded `fn`-recursion is sugar for recursors"
from soundness argument to semantics: **`fn f (…) -> R { body }` is a binding of
`.seal ⟨recursor term⟩ ⟨the Π⟩`**, and `Decl` is not a primitive. This module is
that elaboration.

## Not in the TCB (constraint 7)

Nothing in `Machine`/`Boundary` imports this file, and that is the point rather
than an accident: **macro output is always kernel-checked**. The `[k]` guard used
to police that a self-call's argument decreases; what replaces it is that the
elaborated recursor is re-checked at its seal, where `ih` is a binder and the
arms are checked at their own constructors. So a bug in this file is an
inconvenience — a program that fails to check, or checks as a different function
— and never an unsoundness. Every claim it makes is re-derived downstream.

## The elaboration, and the one thing that is not obvious

`[k]` is demoted to a **scrutinee-selection hint**: it names which parameter the
recursion is on, the macro hoists it to the front, and the motive is the sealed Π
with that binder peeled off (§7: "the macro needs no inference").

What is not obvious is how the body becomes two arms. It is *not* "split the body
at its `match k`" — `quicksort`'s `match fuel` is nested inside `match l`'s `Cons`
branch, after a `let`, and its `Nil` branch never mentions fuel at all. Instead
**the whole body becomes both arms**, with every `match k` RESOLVED to the
corresponding branch: the base arm is the body with `match k` replaced by its `Z`
branch, the step arm is the body with `match k` replaced by its `S` branch and the
branch's binder renamed to the arm's predecessor. That is exactly what ι does
operationally — `natRec P z s (S m)` selects `s`, and inside, `match fuel` would
have selected the `S` branch — so the elaboration is the ι rule read backwards,
which is why it is uniform over where the match sits.

Self-calls then become `ih` applications with the scrutinee argument dropped, and
`ih` is the sealed self-view at the predecessor.

## What it refuses, and why each refusal is honest

  * **`[k]` on a borrow** (`partition [v]`) — true payload decrease, which §9's
    borrow-mode eliminator would serve and which is FILED, not built. §12 decision
    8 blesses fuel-threading as the interim, and fuel is something the programmer
    threads, not something a macro invents: the signature changes, and so does
    every caller. Refused, pointing at the decision.
  * **A declared `back`** — §6.2's backward specs are a `Decl` mechanism with no
    seal counterpart. M23's corpus has none.
  * **A residual reference to the scrutinee** after the arms are resolved, and a
    self-call left in the base arm — both mean the body was not of the shape the
    elaboration assumes, and both are better said than silently mis-elaborated.
-/

namespace Dllbc.FnMacro

/-! ## Abstraction: a runtime parameter into a pure binder

    Building the sealed Π means turning a telescope — whose types reference their
    parameters as `.var ⟨i, name⟩`, the §5.2 convention — into nested Πs, whose
    binders are de Bruijn. That is abstraction of a VARIABLE, which is a different
    and simpler operation than §18's `abstractOccurrences` (an arbitrary subterm),
    and it has to descend the forms a TYPE is made of: `*v` and `&mut (s : τ ↝ S)`
    and the array steps, none of which `absOcc` looks inside because a §18 motive
    never contains them. -/

/-- Replace `.var x` by the de Bruijn `pvar depth`, descending binders. Free pure
    variables of the term (index ≥ depth) shift up by one to make room for the
    binder being introduced; bound ones (< depth) stay. -/
partial def absVar (x : Var) (depth : Nat) : Term → Term
  | .var y => if y == x then .pvar depth else .var y
  | .pvar k => if k < depth then .pvar k else .pvar (k + 1)
  -- Binders: the codomain/body/snapshot sits one level deeper.
  | .pi d c => .pi (absVar x depth d) (absVar x (depth + 1) c)
  | .sigmaT d c => .sigmaT (absVar x depth d) (absVar x (depth + 1) c)
  | .lam d b => .lam (absVar x depth d) (absVar x (depth + 1) b)
  | .borrowT τ S => .borrowT (absVar x depth τ) (absVar x (depth + 1) S)
  | .app f a => .app (absVar x depth f) (absVar x depth a)
  | .idT a b c => .idT (absVar x depth a) (absVar x depth b) (absVar x depth c)
  | .ctorApp n args => .ctorApp n (args.map (absVar x depth))
  | .cmpT τ => .cmpT (absVar x depth τ)
  | .deref t => .deref (absVar x depth t)
  | .index t i ev => .index (absVar x depth t) (absVar x depth i) (ev.map (absVar x depth))
  | .range t lo cnt rest ev eq =>
    .range (absVar x depth t) (absVar x depth lo) (cnt.map (absVar x depth))
      (rest.map (absVar x depth)) (ev.map (absVar x depth)) (eq.map (absVar x depth))
  | t => t

/-- A λ/Π domain carrying its binder's mode (§6): `⇝τ` for a capitalized binder.
    `piPeel` checks the two against each other, so getting this wrong is caught. -/
def markDom (x : Var) (τ : Term) : Term :=
  if x.isComptime then .cmpT τ else τ

/-- A telescope and a return type as nested Πs — the inverse of the kernel's
    `piPeel`, and the reason the round trip is exact: each binder is abstracted
    over everything to its right, which is precisely what peeling substitutes
    back. -/
def telePi : List (Var × Term) → Term → Term
  | [], ret => ret
  | (x, τ) :: rest, ret => .pi (markDom x τ) (absVar x 0 (telePi rest ret))

/-! ## Resolving the scrutinee's match, and rewriting self-calls -/

/-- The largest runtime var id anywhere in a term — for minting `ih` above every
    id the body already uses. -/
partial def maxVarId : Term → Nat
  | .var x => x.id
  | .letIn x rhs rest => max x.id (max (maxVarId rhs) (maxVarId rest))
  | .assign p e rest => max (maxVarId p) (max (maxVarId e) (maxVarId rest))
  | .ctorApp _ args | .call _ args => args.foldl (fun a t => max a (maxVarId t)) 0
  | .callV x args => args.foldl (fun a t => max a (maxVarId t)) x.id
  | .borrow t | .deref t | .cmpT t => maxVarId t
  | .index t i ev =>
    max (maxVarId t) (max (maxVarId i) ((ev.map maxVarId).getD 0))
  | .range t lo cnt rest ev eq =>
    [maxVarId t, maxVarId lo, (cnt.map maxVarId).getD 0, (rest.map maxVarId).getD 0,
     (ev.map maxVarId).getD 0, (eq.map maxVarId).getD 0].foldl max 0
  | .matchE s eqn brs =>
    brs.foldl (fun a b => max a (max (b.binders.foldl (fun c v => max c v.id) 0) (maxVarId b.body)))
      (max s.id ((eqn.map (·.id)).getD 0))
  | .seq a b | .app a b | .pi a b | .lam a b | .sigmaT a b | .borrowT a b =>
    max (maxVarId a) (maxVarId b)
  | .seal a b => max (maxVarId a) (maxVarId b)
  | .idT a b c => max (maxVarId a) (max (maxVarId b) (maxVarId c))
  | .lamR xs body => xs.foldl (fun a v => max a v.id) (maxVarId body)
  | _ => 0

/-- Rename one runtime variable throughout (binding occurrences included). -/
partial def renameVar (from_ to : Var) : Term → Term
  | .var x => if x.id == from_.id then .var to else .var x
  | .letIn x rhs rest =>
    .letIn (if x.id == from_.id then to else x) (renameVar from_ to rhs) (renameVar from_ to rest)
  | .assign p e rest =>
    .assign (renameVar from_ to p) (renameVar from_ to e) (renameVar from_ to rest)
  | .seq a b => .seq (renameVar from_ to a) (renameVar from_ to b)
  | .ctorApp n args => .ctorApp n (args.map (renameVar from_ to))
  | .call n args => .call n (args.map (renameVar from_ to))
  | .callV x args =>
    .callV (if x.id == from_.id then to else x) (args.map (renameVar from_ to))
  | .borrow t => .borrow (renameVar from_ to t)
  | .deref t => .deref (renameVar from_ to t)
  | .matchE s eqn brs =>
    .matchE (if s.id == from_.id then to else s) eqn (brs.map (fun b =>
      Branch.mk b.ctor (b.binders.map (fun v => if v.id == from_.id then to else v))
        (renameVar from_ to b.body)))
  | .app a b => .app (renameVar from_ to a) (renameVar from_ to b)
  | .idT a b c => .idT (renameVar from_ to a) (renameVar from_ to b) (renameVar from_ to c)
  | .pi a b => .pi (renameVar from_ to a) (renameVar from_ to b)
  | .lam a b => .lam (renameVar from_ to a) (renameVar from_ to b)
  | .sigmaT a b => .sigmaT (renameVar from_ to a) (renameVar from_ to b)
  | .cmpT t => .cmpT (renameVar from_ to t)
  | t => t

/-- Resolve every `match k { … }` on the scrutinee parameter to one branch.

    `ctor` names the branch to keep; `rebind` maps that branch's field binders to
    the arm's own binders (the predecessor), which is how `S(f2)`'s `f2` becomes
    the recursor arm's `f2`. Matches on anything else are traversed, not touched —
    which is what makes this work when the scrutinee's match is nested inside
    another one, as `quicksort`'s is. -/
partial def resolveScrut (k : Var) (ctor : String) (rebind : List Var) : Term → Term
  | .matchE s eqn brs =>
    if s.id == k.id then
      match brs.find? (fun b => b.ctor == ctor) with
      | some b =>
        -- The kept branch, with its field binders renamed to the arm's. The
        -- equation binder (M23's `match h : x`) has no arm counterpart, so a
        -- branch that uses one is rejected upstream rather than silently dropped.
        let body := (b.binders.zip rebind).foldl
          (fun t p => renameVar p.1 p.2 t) (resolveScrut k ctor rebind b.body)
        body
      | none => .matchE s eqn (brs.map (fun b =>
          Branch.mk b.ctor b.binders (resolveScrut k ctor rebind b.body)))
    else
      .matchE s eqn (brs.map (fun b =>
        Branch.mk b.ctor b.binders (resolveScrut k ctor rebind b.body)))
  | .letIn x rhs rest => .letIn x (resolveScrut k ctor rebind rhs) (resolveScrut k ctor rebind rest)
  | .assign p e rest =>
    .assign (resolveScrut k ctor rebind p) (resolveScrut k ctor rebind e) (resolveScrut k ctor rebind rest)
  | .seq a b => .seq (resolveScrut k ctor rebind a) (resolveScrut k ctor rebind b)
  | .ctorApp n args => .ctorApp n (args.map (resolveScrut k ctor rebind))
  | .call n args => .call n (args.map (resolveScrut k ctor rebind))
  | .callV x args => .callV x (args.map (resolveScrut k ctor rebind))
  | .borrow t => .borrow (resolveScrut k ctor rebind t)
  | .deref t => .deref (resolveScrut k ctor rebind t)
  | t => t
/-- The binder the body's own `match k { … S(k2) => … }` gives the predecessor.

    Used as the recursor arm's predecessor binder, rather than a minted name, for
    two reasons that are the same reason: the programmer chose `i2`/`f2` and every
    rejection inside the arm should say so, and reusing the binder makes the arm's
    rebinding the identity — the body is not rewritten at all in the common case
    of a single `match` on the scrutinee. -/
partial def succBinder (k : Var) : Term → Option Var
  | .matchE s _ brs =>
    if s.id == k.id then
      match brs.find? (fun b => b.ctor == "S") with
      | some b => b.binders.head?
      | none => none
    else brs.findSome? (fun b => succBinder k b.body)
  | .letIn _ rhs rest => (succBinder k rhs).orElse (fun _ => succBinder k rest)
  | .assign _ e rest => (succBinder k e).orElse (fun _ => succBinder k rest)
  | .seq a b => (succBinder k a).orElse (fun _ => succBinder k b)
  | _ => none

/-- The scrutinee argument of every self-call, in order. `ih` is the sealed view
    **at the predecessor**, so translating a self-call into one is honest only when
    that argument IS the predecessor; `fnElab` checks these before rewriting.

    Without the check the macro silently repairs a non-terminating program: the
    corpus's `recGrow` — `fn recGrow [n] (n) { match n { Z => Refl, S(m2) =>
    recGrow(S(m2)) } }` — recurses on ITSELF, is rejected by the declaration
    path's snapshot-subterm guard, and elaborates to a recursor that recurses on
    `m2` and checks. §7 says the guard evaporates because `ih` is a binder and a
    binder cannot be a self-call; that is true of the ELABORATED term, and this is
    what makes it true of the source it came from. Constraint 7 held either way —
    the kernel accepted a well-founded program — but "checks as a different
    function" is precisely the macro bug that constraint is willing to tolerate
    and a reader is not. -/
partial def selfScrutArgs (name : String) (k : Nat) : Term → List Term
  | .call f args =>
    (if f == name then (args.get? k).toList else []) ++ args.flatMap (selfScrutArgs name k)
  | .letIn _ rhs rest => selfScrutArgs name k rhs ++ selfScrutArgs name k rest
  | .assign p e rest =>
    selfScrutArgs name k p ++ selfScrutArgs name k e ++ selfScrutArgs name k rest
  | .seq a b => selfScrutArgs name k a ++ selfScrutArgs name k b
  | .ctorApp _ args | .callV _ args => args.flatMap (selfScrutArgs name k)
  | .borrow t | .deref t => selfScrutArgs name k t
  | .matchE _ _ brs => brs.flatMap (fun b => selfScrutArgs name k b.body)
  | _ => []

/-- A self-call becomes an `ih` application with the scrutinee argument dropped:
    `f(a₀ … a_k … aₙ)` ↦ `ih(a₀ … â_k … aₙ)`. The remaining arguments keep their
    order, which is the order the motive binds them in — hoisting `k` to the front
    removes it from the middle and changes nothing else. -/
partial def selfToIh (name : String) (k : Nat) (ih : Var) : Term → Term
  | .call f args =>
    let args' := args.map (selfToIh name k ih)
    if f == name then .callV ih (args'.eraseIdx k) else .call f args'
  | .letIn x rhs rest => .letIn x (selfToIh name k ih rhs) (selfToIh name k ih rest)
  | .assign p e rest =>
    .assign (selfToIh name k ih p) (selfToIh name k ih e) (selfToIh name k ih rest)
  | .seq a b => .seq (selfToIh name k ih a) (selfToIh name k ih b)
  | .ctorApp n args => .ctorApp n (args.map (selfToIh name k ih))
  | .callV x args => .callV x (args.map (selfToIh name k ih))
  | .borrow t => .borrow (selfToIh name k ih t)
  | .deref t => .deref (selfToIh name k ih t)
  | .matchE s eqn brs =>
    .matchE s eqn (brs.map (fun b => Branch.mk b.ctor b.binders (selfToIh name k ih b.body)))
  | t => t

/-! ## The elaboration -/

/-- The telescope as `Var`s, at the §5.2 positional convention its own types are
    written against. -/
def teleVars (tel : List (String × Term)) : List (Var × Term) :=
  tel.enum.map (fun p => (Var.mk p.1 p.2.1, p.2.2))

/-- Move the `[k]`-th entry to the front.

    Legal exactly when the scrutinee's type mentions no earlier parameter — it has
    to be statable before them if it is to bind before them. For every recursion
    this phase serves that type is `Nat`, which is closed, so the condition is
    free; it is checked rather than assumed because a future `[k]` on a dependent
    parameter would otherwise be silently reordered into nonsense. -/
def hoist (k : Nat) (tel : List (Var × Term)) : Except String (List (Var × Term)) :=
  match tel.get? k with
  | none => .error s!"fn: [{k}] is out of range for a {tel.length}-parameter telescope"
  | some (kv, kτ) =>
    let earlier := (tel.take k).map (·.1)
    match (Term.freeRVars [] kτ).find? (fun y => earlier.any (fun e => e.id == y.id)) with
    | some y =>
      .error s!"fn: the decreasing parameter '{kv.name}' cannot be hoisted to the front of the telescope — its type mentions '{y.name}', which is declared before it. §7 makes [k] a scrutinee-selection hint and the motive is the sealed Π with that binder peeled off the FRONT, so the scrutinee's own type must be statable first."
    | none => .ok ((kv, kτ) :: (tel.take k ++ tel.drop (k + 1)))

/-- `fn` as a macro: a `Decl` becomes the term §7 says it is — `.seal ⟨recursor⟩
    ⟨Π⟩` when it recurses, `.seal ⟨runtime λ⟩ ⟨Π⟩` when it does not.

    Returns the sealed TERM. Binding it is the caller's business, which is §8's
    direction: a declaration is a `let`, and this is its right-hand side. -/
def fnElab (d : Decl) : Except String Term := do
  if d.back.isSome then
    .error s!"fn: '{d.name}' declares a backward spec, and §6.2's `back` is a `Decl` mechanism with no seal counterpart — the ensures IS the contract now (§5 point 4). M23's corpus declares none."
  let tel := teleVars d.telescope
  match d.dec with
  -- NON-RECURSIVE: the whole function is one runtime λ, sealed at its signature.
  | none => .ok (.seal (.lamR (tel.map (·.1)) d.body) (telePi tel d.retType))
  | some k => do
    let (kv, kτ) ← match tel.get? k with
      | some e => pure e
      | none => .error s!"fn: [{k}] is out of range for a {tel.length}-parameter telescope"
    -- §12 decision 8: TRUE payload decrease has no recursor form, and fuel is
    -- something a programmer threads (it changes the signature, and every
    -- caller), never something a macro invents.
    match kτ with
    | .borrowT _ _ =>
      .error s!"fn: '{d.name}' decreases through the PAYLOAD of the borrow '{kv.name}' ([{k}]), which has no recursor form — §9's borrow-mode eliminator is filed, not built. §12 decision 8 blesses fuel-threading as the interim: add a `fuel : Nat` parameter and a `Le (len *{kv.name}) fuel` bound, recurse on the fuel, and every caller supplies one. That is a source change, not an elaboration."
    | _ => pure ()
    if !(Term.beq kτ (.const "Nat")) then
      .error s!"fn: '{d.name}' recurses on '{kv.name}', whose type is not `Nat`. This phase elaborates `natRec` recursions only; a structural recursion over `List` is the same shape with `listRec` and is not yet wired."
    let hoisted ← hoist k tel
    let rest := hoisted.drop 1
    -- THE MOTIVE, derived from the signature: the sealed Π with the scrutinee
    -- peeled off (§7 — "so the macro needs no inference").
    let piT := telePi hoisted d.retType
    let motive : Term := .lam (markDom kv kτ) (absVar kv 0 (telePi rest d.retType))
    -- Fresh binders for the step arm, above every id the body already uses.
    let base := max (maxVarId d.body) (tel.foldl (fun a p => max a p.1.id) 0) + 1
    -- The predecessor keeps the name AND the id the body's own `match k` gave it,
    -- so the rebinding below is the identity whenever there is one such match.
    let pred : Var := (succBinder kv d.body).getD ⟨base, kv.name ++ "'"⟩
    let ih : Var := ⟨base + 1, "ih"⟩
    -- THE ARMS: the WHOLE body twice, with `match k` resolved to one branch each.
    let zBody := resolveScrut kv "Z" [] d.body
    let sResolved := resolveScrut kv "S" [pred] d.body
    -- `ih` is the sealed view AT THE PREDECESSOR, so a self-call may only be
    -- rewritten into one when that is what it recurses on. Checked here rather
    -- than left to the kernel, which would accept the (well-founded) elaboration
    -- of a source that is not.
    match (selfScrutArgs d.name k sResolved).find? (fun a =>
        match a with | .var y => y.id != pred.id | _ => true) with
    | some a =>
      .error s!"fn: '{d.name}' calls itself with a non-predecessor as its decreasing argument [{k}], which is not the predecessor '{pred.name}'. §7 makes a recursive occurrence `ih` — the sealed self-view AT THE PREDECESSOR — so there is nothing for a self-call at any other argument to become. (This is the check that keeps the macro from silently turning a non-terminating source into a terminating recursor: the elaborated term would be well-founded and would check, but it would be a different function.)"
    | none => pure ()
    match (selfScrutArgs d.name k zBody).head? with
    | some _ =>
      .error s!"fn: '{d.name}' calls itself in the branch its `match {kv.name}` selects at `Z`. The base arm has no `ih` — that is what a base case IS — so a self-call there has nothing to become."
    | none => pure ()
    let sBody := selfToIh d.name k ih sResolved
    -- The scrutinee is gone from both arms; a residual reference to it means the
    -- body used `k` as a value somewhere no `match` resolved, and the arm would be
    -- non-closed. Said here rather than left to the kernel's closedness rejection,
    -- which would name the variable without naming the cause.
    let restIds := rest.map (·.1)
    let stray := (Term.freeRVars ((restIds.map (·.id))) zBody).find? (fun y => y.id == kv.id)
    match stray with
    | some _ =>
      .error s!"fn: the base arm still mentions '{kv.name}' after `match {kv.name}` was resolved to its `Z` branch. The scrutinee does not exist inside an arm — it is the recursor's argument — so a body may only reach it through a match on it."
    | none => pure ()
    -- `natRec P z s`, UNAPPLIED: the scrutinee is the sealed Π's own first binder,
    -- so the recursor is exactly a function of it (§7's derived motive read the
    -- other way round).
    .ok (.seal
      (.app (.app (.app (.const "natRec") motive)
        (.lamR restIds zBody))
        (.lamR (pred :: ih :: restIds) sBody))
      piT)

/-! ## §8: assembling a program from declarations

    A `Decl` becomes a `let` (§8: "every piece of structure a declaration form
    ever carried already lives on the binding"), and the only thing that changes
    inside the bodies is how a callee is named: `f(…)` was a TABLE lookup and is
    now a variable — the same rewrite the surface has done since M26-A, applied to
    terms that were elaborated before their callees had ids.

    Like `fnElab`, this is not in the TCB: the kernel re-derives everything at the
    seal, and a bug here yields a program that fails to check or checks as a
    different program. That is what licenses the migration tests to be
    COMPARISONS — does the assembled program accept what the declared cohort
    accepted, and refuse what it refused — rather than proofs. -/

/-- Retarget table calls to the bindings that now hold those functions. A name
    with no binding is left as a `.call`, so a half-migrated program still
    reaches the J1 table for whatever has not moved yet.

    **And the arguments are permuted to match the callee's hoist.** `[k]` is a
    scrutinee-selection hint, and `fnElab` hoists that parameter to the FRONT
    because the motive is the sealed Π with the scrutinee peeled off the front —
    so a sealed callee's telescope is not its declaration's telescope, and a call
    written against the declaration has to be reordered the same way. Omitting
    this is invisible whenever `[k]` is already parameter 0 (which every flagship
    in this corpus happens to satisfy) and silently passes a borrow where a `Nat`
    is expected otherwise. It was found by the migration report's disagreement
    list, on `swap_at` and `pick` — two callers of `[i]`/`[k]` functions whose
    decreasing parameter is not first. -/
partial def retarget (binds : List (String × Var × Option Nat)) : Term → Term
  | .call f args =>
    let args' := args.map (retarget binds)
    match binds.lookup f with
    | some (v, some k) =>
      match args'.get? k with
      | some a => .callV v (a :: args'.eraseIdx k)
      | none => .callV v args'                  -- arity mismatch: the kernel reports it
    | some (v, none) => .callV v args'
    | none => .call f args'
  | .callV x args => .callV x (args.map (retarget binds))
  | .ctorApp n args => .ctorApp n (args.map (retarget binds))
  | .letIn x rhs rest => .letIn x (retarget binds rhs) (retarget binds rest)
  | .assign p e rest => .assign (retarget binds p) (retarget binds e) (retarget binds rest)
  | .seq a b => .seq (retarget binds a) (retarget binds b)
  | .borrow t => .borrow (retarget binds t)
  | .deref t => .deref (retarget binds t)
  | .matchE s eqn brs =>
    .matchE s eqn (brs.map (fun b => Branch.mk b.ctor b.binders (retarget binds b.body)))
  | .lamR xs body => .lamR xs (retarget binds body)
  | .seal t u => .seal (retarget binds t) (retarget binds u)
  | .app a b => .app (retarget binds a) (retarget binds b)
  | .idT a b c => .idT (retarget binds a) (retarget binds b) (retarget binds c)
  | .pi a b => .pi (retarget binds a) (retarget binds b)
  | .lam a b => .lam (retarget binds a) (retarget binds b)
  | .sigmaT a b => .sigmaT (retarget binds a) (retarget binds b)
  | .index t i ev => .index (retarget binds t) (retarget binds i) (ev.map (retarget binds))
  | .range t lo cnt rest ev eq =>
    .range (retarget binds t) (retarget binds lo) (cnt.map (retarget binds))
      (rest.map (retarget binds)) (ev.map (retarget binds)) (eq.map (retarget binds))
  | t => t

/-- The program-level binding ids. Chosen above every id a body mints (the
    elaborated terms are checked against this below) and below the executing
    machine's frame base, so a global is neither shadowed by a local nor mistaken
    for a frame slot. `progWith [..] { … }` binds the same ids, which is how a
    hand-written tail agrees with an assembled prefix. -/
def progBase : Nat := 900

/-- **A program from a cohort of declarations** (§8), in dependency order: each
    becomes a sealed `let`, each body's calls are retargeted to the bindings above
    it, and `tail` runs in the accumulated scope. No table, no forward reference —
    a callee not yet bound stays a `.call` and is reported by the kernel as the
    unknown function it is. -/
def progOf (ds : List Decl) (tail : Term) : Except String Term := do
  let binds : List (String × Var × Option Nat) :=
    ds.enum.map (fun p => (p.2.name, ⟨progBase + p.1, p.2.name⟩, p.2.dec))
  let rec go (i : Nat) : List Decl → Except String Term
    -- The tail is in the accumulated scope, so its calls are retargeted too — which
    -- is what lets an existing `Decl`-era caller term be handed over unchanged and
    -- become the program's `main`.
    | [] => .ok (retarget binds tail)
    | d :: rest => do
      let t ← fnElab d
      if maxVarId t ≥ progBase then
        .error s!"prog: '{d.name}' elaborates to a term using variable id {maxVarId t}, at or above the program-binding base {progBase} — a global would collide with one of its own locals."
      -- Only the bindings STRICTLY ABOVE this one are in scope for it — a binding
      -- is not in scope in its own right-hand side — which is what makes both a
      -- forward reference and a residual self-call show up as the unknown
      -- function they are, rather than as a dangling variable.
      let above := binds.take i
      pure (.letIn ⟨progBase + i, d.name⟩ (retarget above t) (← go (i + 1) rest))
  go 0 ds

end Dllbc.FnMacro
