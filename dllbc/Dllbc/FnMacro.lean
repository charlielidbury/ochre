import Dllbc.Value

/-!
# `fn` is a macro (M26-D)

`combining-fns.md` §7 promotes "guarded `fn`-recursion is sugar for recursors"
from soundness argument to semantics: **`fn f (…) -> R { body }` is a binding of
`.seal ⟨recursor term⟩ ⟨the Π⟩`**, and `FnDef` is not a primitive. This module is
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
  * **A declared `back`** — §6.2's backward specs are a `FnDef` mechanism with no
    seal counterpart. M23's corpus has none.
  * **A residual reference to the scrutinee** after the arms are resolved, and a
    self-call left in the base arm — both mean the body was not of the shape the
    elaboration assumes, and both are better said than silently mis-elaborated.
-/

namespace Dllbc

/-- **The declaration record** — what a `fn` statement builds and `fnElab`
    consumes. It carries the four things a `let` of a seal needs: a name to bind, a
    telescope and a return type to make the Π, and a body.

    It lives HERE, above the macro and below nothing (M28 D9). §8 made a
    declaration a `let` of a sealed λ, so there is no declaration form in the
    calculus and nothing in `Machine`/`Boundary` has a use for this type: `St.fsig`
    holds the ascribed Π itself and `callDeclC` takes a telescope and a return
    type. It was declared in `Machine.lean` for four milestones after that stopped
    being true, which is the ordinary way a claim in a docstring outlives the code
    that made it so. -/
structure FnDef where
  name : String
  telescope : List (String × Term)
  retType : Term
  body : Term
  /-- §1.2's `[k]` — purely the **scrutinee-selection hint**: which parameter the
      elaboration recurses on, hoisted to the front so the motive is the sealed Π
      with that binder peeled off (§7).

      The guard it once named is gone (M27-δ), and §7's word for what happened is
      the right one: it EVAPORATED rather than being deleted. A recursive
      occurrence is the `ih` binder and a binder cannot be a self-call, so there is
      no rule left for a side condition to attach to. `none` now means only "does
      not recurse", with no rejection riding on it. -/
  dec : Option Nat := none

namespace FnMacro

/-! ## Abstraction: a runtime parameter into a pure binder

    Building the sealed Π means turning a telescope — whose types reference their
    parameters as `.var ⟨i, name⟩`, the §5.2 convention — into nested Πs, whose
    binders are pure. That is abstraction of a VARIABLE, which is a different and
    simpler operation than §18's `abstractOccurrences` (an arbitrary subterm), and
    it has to descend the forms a TYPE is made of: `*v` and `&mut (s : τ ↝ τ')` and
    the array steps, none of which `absOcc` looks inside because a §18 motive never
    contains them.

    **It is now a leaf rewrite** (M30 step 2): no depth, and nothing happens at a
    binder except recursion. The de Bruijn version had to lift the term's own free
    indices past the binder it was introducing, at every binder crossed, and that
    lifting is the identity under names. -/

/-- The pure binder a telescope parameter is abstracted to. RESERVED, keyed on the
    parameter's globally-unique runtime id: a source binder cannot write one, and
    two parameters cannot collide even if a program names them both `x`, so the
    abstraction needs no freshness check and no not-under-a-shadowing-binder guard.
    (The parameter's own name would read better in a printed Π and would be wrong
    for exactly those two reasons.) -/
def paramName (x : Var) : String := "§p" ++ toString x.id

/-- Replace `.var x` by the pure variable `paramName x`, descending everything a
    type is made of. -/
partial def absVar (x : Var) : Term → Term
  | .var y => if y == x then .pvar (paramName x) else .var y
  | .pi n d c => .pi n (absVar x d) (absVar x c)
  | .sigmaT n d c => .sigmaT n (absVar x d) (absVar x c)
  | .lam n d b => .lam n (absVar x d) (absVar x b)
  | .borrowT n τ S => .borrowT n (absVar x τ) (absVar x S)
  | .app f a => .app (absVar x f) (absVar x a)
  | .idT a b c => .idT (absVar x a) (absVar x b) (absVar x c)
  | .ctorApp n args => .ctorApp n (args.map (absVar x))
  | .cmpT τ => .cmpT (absVar x τ)
  | .deref t => .deref (absVar x t)
  | .index t i ev => .index (absVar x t) (absVar x i) (ev.map (absVar x))
  | .range t lo cnt rest ev eq =>
    .range (absVar x t) (absVar x lo) (cnt.map (absVar x))
      (rest.map (absVar x)) (ev.map (absVar x)) (eq.map (absVar x))
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
  | (x, τ) :: rest, ret => .pi (paramName x) (markDom x τ) (absVar x (telePi rest ret))

/-! ## Resolving the scrutinee's match, and rewriting self-calls -/

/-- A `Var`'s id if it is one, and `0` if it is a sentinel — `noSlot` (a comptime
    binder) or `declSlot` (a program declaration). Neither is an id in the
    program's space and either would swamp a maximum. -/
def realId (x : Var) : Nat := if x.id == noSlot || x.id == declSlot then 0 else x.id

/-- The largest runtime var id anywhere in a term — for minting `ih` above every
    id the body already uses. -/
partial def maxVarId : Term → Nat
  | .var x => x.id
  -- Both SENTINELS are excluded (M32 R4 adds `declSlot` beside `noSlot`): they
  -- are tags, not ids in the program's space, and either would swamp the max.
  | .letIn x rhs => max (realId x) (maxVarId rhs)
  | .assign p e => max (maxVarId p) (maxVarId e)
  | .ctorApp _ args | .call _ args => args.foldl (fun a t => max a (maxVarId t)) 0
  | .borrow t | .deref t | .cmpT t => maxVarId t
  | .index t i ev =>
    max (maxVarId t) (max (maxVarId i) ((ev.map maxVarId).getD 0))
  | .range t lo cnt rest ev eq =>
    [maxVarId t, maxVarId lo, (cnt.map maxVarId).getD 0, (rest.map maxVarId).getD 0,
     (ev.map maxVarId).getD 0, (eq.map maxVarId).getD 0].foldl max 0
  | .matchE s eqn brs =>
    brs.foldl (fun a b => max a (max (b.binders.foldl (fun c v => max c v.id) 0) (maxVarId b.body)))
      (max s.id ((eqn.map (·.id)).getD 0))
  | .seq a b | .app a b | .seal _ a b => max (maxVarId a) (maxVarId b)
  -- The one λ (M32 R2): the BINDER's id counts too, which is what the `lamR`
  -- fold over its telescope was for. A comptime binder's `noSlot` would swamp
  -- the maximum, so it is excluded — it is not an id in the program's space.
  | .lam x a b => max (realId x) (max (maxVarId a) (maxVarId b))
  | .pi _ a b | .sigmaT _ a b | .borrowT _ a b =>
    max (maxVarId a) (maxVarId b)
  | .idT a b c => max (maxVarId a) (max (maxVarId b) (maxVarId c))
  | _ => 0

/-- Rename one runtime variable throughout (binding occurrences included). -/
partial def renameVar (from_ to : Var) : Term → Term
  | .var x => if x.id == from_.id then .var to else .var x
  | .letIn x rhs =>
    .letIn (if x.id == from_.id then to else x) (renameVar from_ to rhs)
  | .assign p e =>
    .assign (renameVar from_ to p) (renameVar from_ to e)
  | .seq a b => .seq (renameVar from_ to a) (renameVar from_ to b)
  | .ctorApp n args => .ctorApp n (args.map (renameVar from_ to))
  | .call n args => .call n (args.map (renameVar from_ to))
  | .borrow t => .borrow (renameVar from_ to t)
  | .deref t => .deref (renameVar from_ to t)
  | .matchE s eqn brs =>
    .matchE (if s.id == from_.id then to else s) eqn (brs.map (fun b =>
      Branch.mk b.ctor (b.binders.map (fun v => if v.id == from_.id then to else v))
        (renameVar from_ to b.body)))
  | .app a b => .app (renameVar from_ to a) (renameVar from_ to b)
  | .idT a b c => .idT (renameVar from_ to a) (renameVar from_ to b) (renameVar from_ to c)
  | .pi n a b => .pi n (renameVar from_ to a) (renameVar from_ to b)
  | .lam n a b => .lam n (renameVar from_ to a) (renameVar from_ to b)
  | .sigmaT n a b => .sigmaT n (renameVar from_ to a) (renameVar from_ to b)
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
  | .letIn x rhs => .letIn x (resolveScrut k ctor rebind rhs)
  | .assign p e =>
    .assign (resolveScrut k ctor rebind p) (resolveScrut k ctor rebind e)
  | .seq a b => .seq (resolveScrut k ctor rebind a) (resolveScrut k ctor rebind b)
  | .ctorApp n args => .ctorApp n (args.map (resolveScrut k ctor rebind))
  | .call n args => .call n (args.map (resolveScrut k ctor rebind))
  | .app f a => .app (resolveScrut k ctor rebind f) (resolveScrut k ctor rebind a)
  | .borrow t => .borrow (resolveScrut k ctor rebind t)
  | .deref t => .deref (resolveScrut k ctor rebind t)
  | t => t
/-- The binder the body's own `match k { … S(k2) => … }` gives the predecessor.

    Used as the recursor arm's predecessor binder, rather than a minted name, for
    two reasons that are the same reason: the programmer chose `i2`/`f2` and every
    rejection inside the arm should say so, and reusing the binder makes the arm's
    rebinding the identity — the body is not rewritten at all in the common case
    of a single `match` on the scrutinee. -/
partial def branchBinders (k : Var) (ctor : String) : Term → Option (List Var)
  | .matchE s _ brs =>
    if s.id == k.id then
      match brs.find? (fun b => b.ctor == ctor) with
      | some b => some b.binders
      | none => none
    else brs.findSome? (fun b => branchBinders k ctor b.body)
  | .letIn _ rhs => branchBinders k ctor rhs
  | .assign _ e => branchBinders k ctor e
  | .seq a b => (branchBinders k ctor a).orElse (fun _ => branchBinders k ctor b)
  | _ => none

/-- The `S` branch's binder, which is the `Nat` case of `branchBinders`. -/
def succBinder (k : Var) (t : Term) : Option Var := (branchBinders k "S" t).bind (·.head?)

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
    (if f == name then (args[k]?).toList else []) ++ args.flatMap (selfScrutArgs name k)
  | .letIn _ rhs => selfScrutArgs name k rhs
  | .assign p e => selfScrutArgs name k p ++ selfScrutArgs name k e
  | .seq a b => selfScrutArgs name k a ++ selfScrutArgs name k b
  | .ctorApp _ args => args.flatMap (selfScrutArgs name k)
  | .app f a => selfScrutArgs name k f ++ selfScrutArgs name k a
  | .borrow t | .deref t => selfScrutArgs name k t
  | .matchE _ _ brs => brs.flatMap (fun b => selfScrutArgs name k b.body)
  | _ => []

/-- Rename every call of `from_` to `to`. For comparing two declarations that are
    the same function under two names — which is what a hint-only migration
    produces, since a declaration's self-call names it. -/
partial def renameSelf (from_ to : String) : Term → Term
  | .call f args =>
    .call (if f == from_ then to else f) (args.map (renameSelf from_ to))
  | .app f a => .app (renameSelf from_ to f) (renameSelf from_ to a)
  | .ctorApp n args => .ctorApp n (args.map (renameSelf from_ to))
  | .letIn x rhs => .letIn x (renameSelf from_ to rhs)
  | .assign p e =>
    .assign (renameSelf from_ to p) (renameSelf from_ to e)
  | .seq a b => .seq (renameSelf from_ to a) (renameSelf from_ to b)
  | .borrow t => .borrow (renameSelf from_ to t)
  | .deref t => .deref (renameSelf from_ to t)
  | .matchE s eqn brs =>
    .matchE s eqn (brs.map (fun b => Branch.mk b.ctor b.binders (renameSelf from_ to b.body)))
  | .lam x d body => .lam x d (renameSelf from_ to body)
  | t => t

/-- A self-call becomes an `ih` application with the scrutinee argument dropped:
    `f(a₀ … a_k … aₙ)` ↦ `ih(a₀ … â_k … aₙ)`. The remaining arguments keep their
    order, which is the order the motive binds them in — hoisting `k` to the front
    removes it from the middle and changes nothing else. -/
partial def selfToIh (name : String) (k : Nat) (ih : Var) : Term → Term
  | .call f args =>
    let args' := args.map (selfToIh name k ih)
    if f == name then Term.appSpine (.var ih) (args'.eraseIdx k) else .call f args'
  | .letIn x rhs => .letIn x (selfToIh name k ih rhs)
  | .assign p e =>
    .assign (selfToIh name k ih p) (selfToIh name k ih e)
  | .seq a b => .seq (selfToIh name k ih a) (selfToIh name k ih b)
  | .ctorApp n args => .ctorApp n (args.map (selfToIh name k ih))
  | .app f a => .app (selfToIh name k ih f) (selfToIh name k ih a)
  | .borrow t => .borrow (selfToIh name k ih t)
  | .deref t => .deref (selfToIh name k ih t)
  | .matchE s eqn brs =>
    .matchE s eqn (brs.map (fun b => Branch.mk b.ctor b.binders (selfToIh name k ih b.body)))
  | t => t

/-! ## The elaboration -/

/-- The telescope as `Var`s, at the §5.2 positional convention its own types are
    written against. -/
def teleVars (tel : List (String × Term)) : List (Var × Term) :=
  tel.zipIdx.map (fun p => (Var.mk p.2 p.1.1, p.1.2))

/-- Move the `[k]`-th entry to the front.

    Legal exactly when the scrutinee's type mentions no earlier parameter — it has
    to be statable before them if it is to bind before them. For every recursion
    this phase serves that type is `Nat`, which is closed, so the condition is
    free; it is checked rather than assumed because a future `[k]` on a dependent
    parameter would otherwise be silently reordered into nonsense. -/
def hoist (k : Nat) (tel : List (Var × Term)) : Except String (List (Var × Term)) :=
  match tel[k]? with
  | none => .error s!"fn: [{k}] is out of range for a {tel.length}-parameter telescope"
  | some (kv, kτ) =>
    let earlier := (tel.take k).map (·.1)
    match (Term.freeRVars [] kτ).find? (fun y => earlier.any (fun e => e.id == y.id)) with
    | some y =>
      .error s!"fn: the decreasing parameter '{kv.name}' cannot be hoisted to the front of the telescope — its type mentions '{y.name}', which is declared before it. §7 makes [k] a scrutinee-selection hint and the motive is the sealed Π with that binder peeled off the FRONT, so the scrutinee's own type must be statable first."
    | none => .ok ((kv, kτ) :: (tel.take k ++ tel.drop (k + 1)))

/-- **The nullary `fn`'s Unit parameter** (M32 R2, suspensions.md §1).

    One λ former means a λ has a binder, so `Term.lamTel [] body` is the body
    itself and `fn F () -> T { … }` would elaborate to `.seal ⟨body⟩ T` — which is
    exactly what the surface ascription `(e : T)` elaborates to. The two were
    different terms while `lamR []` existed and are the same term after the fold,
    so the seal could no longer tell a nullary FUNCTION from an ascribed
    expression. §1 already prescribes the resolution — "nullary `fn` desugars to
    `λ (U : Unit)`" — and this is it, arriving here rather than at R4 because the
    fold is what forces it.

    **The binder itself moved to `Syntax.lean` at M33b** (`unitBinder`), because a
    recursor arm with an empty residual telescope needs the same one and the
    kernel has to recognize it: ι asks whether an arm owes a `()`, and both
    contract derivations ask whether its Π gains a `Unit`. `retarget` supplies the
    `()` at every no-argument call site, so the desugar stays invisible to the
    surface in both directions. -/
abbrev nullaryVar : Var := unitBinder

/-- **An arm's telescope, with the unit binder supplied when it would be empty**
    (M33b, suspensions.md §5's ruling).

    A base arm whose motive is DATA and whose residual telescope is empty binds
    nothing, and `Term.lamTel [] body` is `body` — so without this the arm is a
    bare term, `readRecArgs` ⇒-reads it when the SPINE is formed rather than when
    ι selects it, and its value is computed once and shared by every application.
    Every other arm is a λ; this is what makes that "every" true. -/
def armTelOrUnit (tel : List (Var × Term)) : List (Var × Term) :=
  if tel.isEmpty then [(unitBinder, markDom unitBinder (.const "Unit"))] else tel

/-- `fn` as a macro: a `FnDef` becomes the term §7 says it is — `.seal ⟨recursor⟩
    ⟨Π⟩` when it recurses, `.seal ⟨runtime λ⟩ ⟨Π⟩` when it does not.

    Returns the sealed TERM. Binding it is the caller's business, which is §8's
    direction: a declaration is a `let`, and this is its right-hand side. -/
def fnElab (d : FnDef) : Except String Term := do
  let tel := if d.telescope.isEmpty then [(nullaryVar, Term.const "Unit")]
             else teleVars d.telescope
  match d.dec with
  -- NON-RECURSIVE: the whole function is one runtime λ, sealed at its signature.
  -- A self-call here is deliberately NOT refused, and that is §8's own mechanism
  -- rather than an omission: the elaborated `let` is not in scope in its own
  -- right-hand side, so the self-call resolves to nothing and the program is
  -- rejected as the forward reference it is. M26-C pinned exactly that as the
  -- reason `bad()` is unwritable — "not by a recursion rule; the binding is not in
  -- scope in its own right-hand side" — and a macro refusal here would paper over
  -- the demonstration.
  -- The telescope IS the annotated binder list (M27) — `markDom` puts each
  -- binder's mode on its domain, which is what `telePi` does to build the Π the
  -- seal converts against, so the λ and its ascription are built from one source.
  | none =>
    .ok (.seal 0 (Term.lamTel (tel.map (fun p => (p.1, markDom p.1 p.2))) d.body)
               (telePi tel d.retType))
  | some k => do
    let (kv, kτ) ← match tel[k]? with
      | some e => pure e
      | none => .error s!"fn: [{k}] is out of range for a {tel.length}-parameter telescope"
    -- §12 decision 8: TRUE payload decrease has no recursor form, and fuel is
    -- something a programmer threads (it changes the signature, and every
    -- caller), never something a macro invents.
    match kτ with
    | .borrowT _ _ _ =>
      .error s!"fn: '{d.name}' decreases through the PAYLOAD of the borrow '{kv.name}' ([{k}]), which has no recursor form — §9's borrow-mode eliminator is filed, not built. §12 decision 8 blesses fuel-threading as the interim: add a `fuel : Nat` parameter and a `Le (len *{kv.name}) fuel` bound, recurse on the fuel, and every caller supplies one. That is a source change, not an elaboration."
    | _ => pure ()
    -- WHICH RECURSOR, decided by the scrutinee's type and nothing else. The two
    -- differ only in what the step arm binds and what the constructors are called;
    -- everything below — the motive, the arms-are-the-whole-body-twice
    -- elaboration, the self-call rewrite, the stray check — is shared, which is
    -- what says `listRec` is the same elaboration and not a second one.
    let elemTy? : Option Term := match kτ with
      | .app (.const "List") a => some a
      | _ => none
    if !(Term.beq kτ (.const "Nat")) && elemTy?.isNone then
      .error s!"fn: '{d.name}' recurses on '{kv.name}', whose type is neither `Nat` nor `List A`. Those are the two eliminators this macro emits; the kernel's `sealRec` also checks `boolRec`, which no recursion decreases on."
    let hoisted ← hoist k tel
    let rest := hoisted.drop 1
    -- THE MOTIVE, derived from the signature: the sealed Π with the scrutinee
    -- peeled off (§7 — "so the macro needs no inference").
    let piT := telePi hoisted d.retType
    let scrutDom := markDom kv kτ
    -- The motive's BODY: the residual telescope-and-return with the scrutinee
    -- abstracted. Named because every arm annotation below is an instance of it,
    -- and because the kernel calls the same thing `R` (`sealRec` peels it off the
    -- ascription instead of building it, and the two agree by `telePi`/`piPeel`
    -- being inverse).
    let R : Term := absVar kv (telePi rest d.retType)
    let motive : Term := .lam (paramName kv) scrutDom R
    -- Fresh binders for the step arm, above every id the body already uses.
    let base := max (maxVarId d.body) (tel.foldl (fun a p => max a p.1.id) 0) + 1
    -- The step arm's binders keep the names AND the ids the body's own `match k`
    -- gave them, so the rebinding below is the identity whenever there is one such
    -- match. For a list that is the head and the tail; for a `Nat`, the
    -- predecessor. `dec` is the one a self-call must recurse on.
    let (baseCtor, stepCtor) := if elemTy?.isSome then ("Nil", "Cons") else ("Z", "S")
    let stepBs : List Var := match branchBinders kv stepCtor d.body with
      | some bs =>
        if elemTy?.isSome then
          match bs with
          | [h, t] => [h, t]
          | _ => [⟨base, "hd"⟩, ⟨base + 2, kv.name ++ "'"⟩]
        else match bs with
          | [p] => [p]
          | _ => [⟨base, kv.name ++ "'"⟩]
      | none =>
        if elemTy?.isSome then [⟨base, "hd"⟩, ⟨base + 2, kv.name ++ "'"⟩]
        else [⟨base, kv.name ++ "'"⟩]
    let dec : Var := stepBs.getLast!
    -- `ih`'s domain is the motive at the PREDECESSOR — a term nothing in the
    -- source wrote. Computed here rather than below because its SHAPE decides the
    -- binder's own spelling.
    let ihTy : Term := Term.substP (paramName kv) (.var dec) R
    -- **`Ih` IS CAPITAL WHEN IT HOLDS A FUNCTION, and lowercase when it holds
    -- data** (M33b, suspensions.md §2.1/§2.5). §2.1's rule reaches every binder
    -- and this one was out of its migration's reach — the corpus's `ih`s were
    -- renamed by a sweep over what programs WRITE, and this one is minted. But
    -- the rule is "capital binds comptime knowledge", not "capital is spelled on
    -- recursor arms", so it has to be asked of what the binder actually holds.
    --
    -- The answer is the arm's own type, and it splits exactly where eagerness
    -- does. A Π motive — the residual telescope is non-empty, `SetAt`'s `v`, `i`,
    -- `x`, quicksort's borrows — gives `Ih` a FUNCTION, which §2.5 makes law:
    -- no runtime binding may hold one. A data motive with an empty residual
    -- telescope gives `ih` the recursive RESULT, which under commit 3 is a
    -- finished value of the return type (`RecGood`'s `Id Nat Z Z`, `Build`'s
    -- `List Nat`) — ordinary runtime data, moved and returned like any.
    --
    -- MEASURED, not chosen: renaming unconditionally reds exactly the three
    -- programs whose residual telescope is empty (`recGood`, `recList`,
    -- `recCaller`), each at `fence: 'Ih' … cannot be ⇒-moved`, because their
    -- self-call `RecGood(m)` drops its only argument and IS the bare `.var ih`
    -- that the arm returns. Making that return legal would need the recursor's
    -- signature to carry modes, which is filed as its own milestone.
    let ih : Var :=
      ⟨base + 1, match ihTy with | .pi _ _ _ => "Ih" | _ => "ih"⟩
    -- THE ARMS: the WHOLE body twice, with `match k` resolved to one branch each.
    let zBody := resolveScrut kv baseCtor [] d.body
    let sResolved := resolveScrut kv stepCtor stepBs d.body
    -- `ih` is the sealed view AT THE PREDECESSOR, so a self-call may only be
    -- rewritten into one when that is what it recurses on. Checked here rather
    -- than left to the kernel, which would accept the (well-founded) elaboration
    -- of a source that is not.
    match (selfScrutArgs d.name k sResolved).find? (fun a =>
        match a with | .var y => y.id != dec.id | _ => true) with
    | some _ =>
      .error s!"fn: '{d.name}' calls itself with a decreasing argument [{k}] that is not the predecessor '{dec.name}' its `{stepCtor}` branch binds. §7 makes a recursive occurrence `ih` — the sealed self-view AT THE PREDECESSOR — so there is nothing for a self-call at any other argument to become. (This is the check that keeps the macro from silently turning a non-terminating source into a terminating recursor: the elaborated term would be well-founded and would check, but it would be a different function.)"
    | none => pure ()
    match (selfScrutArgs d.name k zBody).head? with
    | some _ =>
      .error s!"fn: '{d.name}' calls itself in the branch its `match {kv.name}` selects at `{baseCtor}`. The base arm has no `ih` — that is what a base case IS — so a self-call there has nothing to become."
    | none => pure ()
    let sBody := selfToIh d.name k ih sResolved
    -- The scrutinee is gone from both arms; a residual reference to it means the
    -- body used `k` as a value somewhere no `match` resolved, and the arm would be
    -- non-closed. Said here rather than left to the kernel's closedness rejection,
    -- which would name the variable without naming the cause.
    let restIds := rest.map (·.1)
    let stray := (Term.freeRVars (restIds.map (·.name)) zBody).find? (fun y => y.name == kv.name)
    match stray with
    | some _ =>
      .error s!"fn: the base arm still mentions '{kv.name}' after `match {kv.name}` was resolved to its `{baseCtor}` branch. The scrutinee does not exist inside an arm — it is the recursor's argument — so a body may only reach it through a match on it."
    | none => pure ()
    -- **THE ARM ANNOTATIONS** (M27), and the one place in this elaboration that is
    -- design judgement rather than transcription.
    --
    -- An arm is checked at the MOTIVE INSTANTIATED AT ITS CONSTRUCTOR, so its
    -- trailing binders' domains are `rest`'s with the scrutinee substituted — not
    -- `rest`'s. `absVar kv 0` abstracted the scrutinee over the whole nested Π,
    -- domains included, so a later parameter whose type mentions it moves with it:
    -- `quicksort [fuel] (fuel, v, hfuel : Le (len *v) fuel)` wants
    -- `Le (len *v) Z` in the base arm and `Le (len *v) (S fuel')` in the step. And
    -- `ih`'s domain is the motive at the PREDECESSOR, which is a term nothing in
    -- the source wrote.
    --
    -- All three are recovered by peeling with the kernel's own `piPeel`, rather
    -- than transcribed — the same argument §7 makes for deriving the motive: two
    -- derivations by one function cannot disagree. `piPeel` strips the mode
    -- marker it just checked, and `markDom` puts back exactly what it took, so an
    -- annotation is the domain as a source λ would have written it.
    let armTel (names : List Var) (ty : Term) : Except String (List (Var × Term)) := do
      let (tel, _) ← piPeel names ty
      .ok (tel.map (fun p => (p.1, markDom p.1 p.2)))
    -- (`ihTy` is derived above `ih`, since its shape is what decides that
    -- binder's case.)
    -- The recursor, UNAPPLIED: the scrutinee is the sealed Π's own first binder,
    -- so the recursor is exactly a function of it (§7's derived motive read the
    -- other way round). `listRec` takes its element type first, which is the only
    -- difference in the spine.
    match elemTy? with
    | none =>
      let zTel := armTelOrUnit (← armTel restIds (Term.substP (paramName kv) (.ctorApp "Z" []) R))
      let sTel ← armTel restIds (Term.substP (paramName kv) (.ctorApp "S" [.var dec]) R)
      .ok (.seal 0
        (.app (.app (.app (.const "natRec") motive)
          (Term.lamTel zTel zBody))
          (Term.lamTel ((dec, scrutDom) :: (ih, ihTy) :: sTel) sBody))
        piT)
    | some a =>
      let hd : Var := stepBs.head!
      let zTel := armTelOrUnit (← armTel restIds (Term.substP (paramName kv) (.ctorApp "Nil" []) R))
      let sTel ← armTel restIds
        (Term.substP (paramName kv) (.ctorApp "Cons" [.var hd, .var dec]) R)
      .ok (.seal 0
        (.app (.app (.app (.app (.const "listRec") a) motive)
          (Term.lamTel zTel zBody))
          (Term.lamTel ((hd, a) :: (dec, scrutDom) :: (ih, ihTy) :: sTel) sBody))
        piT)

/-! ## §8: assembling a program from declarations

    A `FnDef` becomes a `let` (§8: "every piece of structure a declaration form
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

    **The target is an app SPINE** (M32 R4). `.callV v args` retired, so `f(a, b)`
    lands as `.app (.app (.var v) a) b` — surface sugar for the one application
    form. This function is where the surface's n-ary shape becomes the grammar's
    binary one, and it is the only place in the pipeline that ever built a call.

    **And the arguments are permuted to match the callee's hoist.** `[k]` is a
    scrutinee-selection hint, and `fnElab` hoists that parameter to the FRONT
    because the motive is the sealed Π with the scrutinee peeled off the front —
    so a sealed callee's telescope is not its declaration's telescope, and a call
    written against the declaration has to be reordered the same way. Omitting
    this is invisible whenever `[k]` is already parameter 0 (which every flagship
    in this corpus happens to satisfy) and silently passes a borrow where a `Nat`
    is expected otherwise. It was found on callers of `[i]`/`[k]` functions whose
    decreasing parameter is not first. -/
partial def retarget (binds : List (String × Var × Option Nat)) : Term → Term
  | .call f args =>
    let args' := args.map (retarget binds)
    match binds.lookup f with
    | some (v, some k) =>
      match args'[k]? with
      | some a => Term.appSpine (.var v) (a :: args'.eraseIdx k)
      | none => Term.appSpine (.var v) args'    -- arity mismatch: the kernel reports it
    -- **A no-argument call supplies the nullary desugar's `()`** (M32 R2). A
    -- declared callee with an empty argument list is a nullary `fn`, and
    -- `fnElab` gave it the comptime `U§ : ⇝Unit` binder that §1 prescribes; the
    -- unit is put here rather than written, so the desugar is invisible at the
    -- surface from both ends. (A no-argument call of a callee that is NOT nullary
    -- is an arity error either way, and the kernel still reports it.)
    | some (v, none) => Term.appSpine (.var v) (if args'.isEmpty then [.unit] else args')
    | none => .call f args'
  | .ctorApp n args => .ctorApp n (args.map (retarget binds))
  | .letIn x rhs => .letIn x (retarget binds rhs)
  | .assign p e => .assign (retarget binds p) (retarget binds e)
  | .seq a b => .seq (retarget binds a) (retarget binds b)
  | .borrow t => .borrow (retarget binds t)
  | .deref t => .deref (retarget binds t)
  | .matchE s eqn brs =>
    .matchE s eqn (brs.map (fun b => Branch.mk b.ctor b.binders (retarget binds b.body)))
  | .seal s t u => .seal s (retarget binds t) (retarget binds u)
  | .app a b => .app (retarget binds a) (retarget binds b)
  | .idT a b c => .idT (retarget binds a) (retarget binds b) (retarget binds c)
  | .pi n a b => .pi n (retarget binds a) (retarget binds b)
  | .lam n a b => .lam n (retarget binds a) (retarget binds b)
  | .sigmaT n a b => .sigmaT n (retarget binds a) (retarget binds b)
  | .index t i ev => .index (retarget binds t) (retarget binds i) (ev.map (retarget binds))
  | .range t lo cnt rest ev eq =>
    .range (retarget binds t) (retarget binds lo) (cnt.map (retarget binds))
      (rest.map (retarget binds)) (ev.map (retarget binds)) (eq.map (retarget binds))
  | t => t

/-! ## The statement form's lowering (M28 θ)

    `fn` is a STATEMENT of the one grammar (Uni.lean), and a statement elaborates
    to a `Term`. There is no `Except` for the macro to pattern-match on, because
    the macro runs on SYNTAX while `fnElab` runs on the elaborated `Term`s — so
    the two refusal timings are genuinely different and the difference has to be
    handled rather than wished away.

    Cheap syntactic refusals stay at Lean elaboration, where `decl{ }` already put
    them: `[k]` naming a non-parameter is a name-to-index resolution the macro
    performs anyway, so it throws there. Everything `fnElab` refuses is SEMANTIC —
    it needs the elaborated telescope type to see that `[v]` decreases through a
    borrow's payload, or that a scrutinee is neither `Nat` nor `List A` — and those
    are deliberately NOT duplicated as syntactic checks. Two implementations of one
    rule is one implementation too many, and the copy would be the one that drifts.

    So a refusal becomes a term the checker refuses DISTINCTIVELY: an unknown
    function whose NAME carries `fnElab`'s own message. Three things make that the
    right sentinel rather than a hack — it can never check (an unbound `.call` is
    unconditionally rejected, and this one's name is unwritable), it is reached
    unconditionally (the `let`'s right-hand side is evaluated at the binding, so it
    does not wait for a call site), and the diagnosis survives to the message,
    prefixed by a needle no other error can produce. -/

/-- The needle a refused `fn` statement is recognised by. -/
def fnRefusedNeedle : String := "§fn-lowering-refused"

/-- `fnElab`, made total for the statement form: a refusal becomes a term whose
    rejection carries the refusal. -/
def fnElabOrFail (d : FnDef) : Term :=
  match fnElab d with
  | .ok t => t
  | .error e => .call s!"{fnRefusedNeedle}: {e}" []

/-- **Bind a `fn` statement's slot over the rest of the block.** `retarget`, and
    since M32 R4 nothing else.

    It used to carry an id-collision check in front of `retarget`: each `fn`
    chain numbered its slots from `progBase`, so two chains composed through a
    `%` splice — `withA (withB (ty{ … }))`, the obvious way to share a prefix —
    both started at `900`, and the inner chain's FIRST declaration landed on the
    outer chain's first. `bindFn` refused that.

    **R4 retires it, because the hazard was the arithmetic's and R1 removed the
    arithmetic's teeth.** The collision was on the ID and never on the NAME —
    `withA (withB …)` collided `A` with `B` — and Ω resolves by name, so the two
    entries were never confusable in the first place. Composing chains is now
    ordinary let-chain composition, which is what `%` splicing always looked
    like. What genuinely shadows is a chain redeclaring an outer chain's NAME,
    and that is lexical shadowing doing its job. -/
def bindFn (v : Var) (dec : Option Nat) (rest : Term) : Term :=
  retarget [(v.name, v, dec)] rest


/-- **A program from a cohort of declarations** (§8), in dependency order: each
    becomes a sealed `let`, each body's calls are retargeted to the bindings above
    it, and `tail` runs in the accumulated scope. No table, no forward reference —
    a callee not yet bound stays a `.call` and is reported by the kernel as the
    unknown function it is. -/
def progOf (ds : List FnDef) (tail : Term) : Except String Term := do
  let binds : List (String × Var × Option Nat) :=
    ds.map (fun d => (d.name, ⟨declSlot, d.name⟩, d.dec))
  let rec go (i : Nat) : List FnDef → Except String Term
    -- The tail is in the accumulated scope, so its calls are retargeted too — which
    -- is what lets an existing `FnDef`-era caller term be handed over unchanged and
    -- become the program's `main`.
    | [] => .ok (retarget binds tail)
    | d :: rest => do
      let t ← fnElab d
      -- Only the bindings STRICTLY ABOVE this one are in scope for it — a binding
      -- is not in scope in its own right-hand side — which is what makes both a
      -- forward reference and a residual self-call show up as the unknown
      -- function they are, rather than as a dangling variable.
      let above := binds.take i
      pure (.seq (.letIn ⟨declSlot, d.name⟩ (retarget above t)) (← go (i + 1) rest))
  go 0 ds

end FnMacro

end Dllbc
