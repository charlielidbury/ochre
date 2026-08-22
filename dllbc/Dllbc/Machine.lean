import Dllbc.Syntax
import Dllbc.Value
import Dllbc.Pure

/-!
# DLLBC Concrete Machine (§2)

The runtime interpreter for the doc's §2: the two runtime arrows

  * `readR : Term → M Val`   — the doc's ⇒ (consume-read / move), and
  * `writeR : Term → Val → M Unit` — the doc's ⇐ (destructive fill),

plus the two **reorganizations** the arrows fire *lazily* (doc §2's standing
convention — the environment is only rewritten when a rule's premise demands
it):

  * `endMut ℓ`  — End-Mut: plug a borrow's current payload back where its loan
    marker sits, and kill the borrow to ⊥.
  * `drop v`    — §2.3's total procedure: end the displaced value's ownership
    nodes innermost-first, then discard the remainder.

Both reorganizations reduce to two Ω-primitives — `killBorrowInΩ` and
`sendPayloadToLoan` — which is why "the borrow machinery has no rules of its
own beyond bookkeeping" (§2.5).

Totality: no `partial`. Value-tree traversals are structural (mutual with a
list helper). The reorganize-then-retry loops (`readR` on a loan chain,
`drop` ending several nodes) take an explicit fuel `Nat`, so the whole machine
is kernel-transparent for the later proof phase. Later milestones add
`readC`/`writeC` (⇝/⇜) with parallel signatures.
-/

namespace Dllbc

/-! **`FnDef` has left this file** (M28 D9). It was the declaration record — a
    name, a telescope, a return type, a body and `[k]` — and §8 made a declaration
    a `let` of a sealed λ, so there is no declaration FORM in the calculus and no
    table in `St` for one to live in.

    Its docstring has said "it is deliberately NOT in the kernel's vocabulary any
    more" since M27-δ, and that was true of the RULES and false of the file: `St`
    still carried a `decls` table, `.call` still looked a name up in it, and the
    type was still declared here. All three are gone. `FnDef` is `FnMacro`'s own
    record now — what a `fn` statement builds and `fnElab` consumes — and nothing
    below the macro layer knows the type exists. -/


/-- Where a debt was registered — for error messages and the audit's routing
    (12-design §2.1). `.param` is a signature telescope's mint (`seedTelescopeV`);
    `.call`/`.issue` are a call's captured/issued loans (`callDeclC`), keyed by
    the group's ρ so a group's end can find (and drop) exactly its own debts. -/
inductive DebtSite where
  | param (arg : Var)
  | call (ρ : Nat)
  | issue (ρ : Nat)
deriving BEq, Inhabited

/-- A **debt**: a claim registered on a loan at its mint, asserted at its end
    (12-design §2.1). One table, keyed by loan, replacing three: what an argument
    borrow owes at the boundary was `Obligation ⟨arg, loan, owed, trivialOwed⟩`
    (site `.param`); a call's captured/issued owed types rode on `Group`
    (`.call`/`.issue`); and §5.4's caller-side exit-snapshot pinning was
    `Group.exitRelease` (now `pin = some (sym σ′)`). A group is an ORDERING, a
    debt is a CONTRACT — separating them is what lets a debt exist outside a
    call (§2.6) and survive relocation (§6: a `Debt` is keyed by ℓ, not by slot).

    `owed` is the type the loan's payload must have at its end, OPENED at the
    entry snapshot at registration. There is no separate `entry` field: D15's
    content — the debt's own binder `s` IS the entry snapshot — is realized by
    that opening having already happened, and `St.entrySyms` still names the σ
    for `old *v`.

    `pin` is the VALUE the release is; `none` = opaque, which is today's rule
    byte for byte. Until stage 5 the only pins are §5.4's `some (sym σ′)`.

    Lives in `St` (not just returned by `seedTelescope`) so that a §10 Refl
    refinement — which substitutes a σ everywhere — reaches the owed types and
    pins too: a through-borrow `p : &mut (Id A a b)` matched against `Refl`
    refines the σ that its *own* owed type mentions, and the audit must see the
    refined type, not the frozen entry snapshot. -/
structure Debt where
  loan : Nat
  owed : Term
  pin : Option Term := none
  /-- Was this owed type TRIVIAL (`&mut τ`, owing back the type it was lent) as
      written? Recorded at registration, where the `Term` is still in hand, and
      read by the M27 containment in `auditObligation`: §6.1 exempts a borrow
      consumed into the result from the payload audit, so a NON-trivial owed type
      there is a claim neither end checks. Only consulted at `.param` sites. -/
  trivial : Bool := true
  site : DebtSite

/-- A **loan group** (§6.1): the node a call mints, tying the loans it
    **captured** (the argument borrows' loans, with their owed types) to the
    borrows it **issued** (loans of any borrows in the result, owed-typed from
    the return type). The ending discipline is the group's whole content —
    every issued borrow ends first, then the group ends atomically, releasing
    each captured loan. A §5.3 wire is the degenerate `issued = []` group.

    There was a `constrained` field here — an identity wire releasing its captured
    loan with the issued borrow's surrendered payload. Inferring it is UNSOUND
    (`through` and `advance` share a signature and differ in exactly what it would
    claim), so it was dead in real checking and survived only because a test flipped
    it on to prove the differential could catch the bug. That validation moved to
    the comparator (S9Diff, M28 σ) and the field went with it: the kernel does not
    carry a case for a rule it does not have. -/
structure Group where
  id : Nat                      -- the group node's ρ, its identity in the table
  captured : List Nat           -- the argument borrows' loans, in telescope order
  issued : List Nat             -- the result borrows' loans, in return-type order
  -- The owed types that rode here, and §5.4's `exitRelease` (ℓ, σ′) pinning, are
  -- `St.debts` entries now (site `.call`/`.issue` at this group's ρ; the σ′ is a
  -- `pin` of `some (sym σ′)`). A group is an ORDERING — what must end before
  -- what — and nothing else (12-design §2.1).

/-- One change to the checker's state, tagged with where it happened (docs/17).

    The three constructors are the three kinds of change a tooltip can be asked
    about: a binder appearing, a binder's value being replaced, and a σ being
    learned. Everything else that mutates Ω is one of these at a different call
    site.

    **No rendering and no traversal** — every field is a value already in hand at
    the primitive, so a delta costs one allocation. -/
inductive PointChange where
  /-- `bindSlot`: a binder enters Ω. -/
  | bound  (x : Var) (v : Val)
  /-- `setSlot`: a binder's value is replaced in place. -/
  | set    (x : Var) (v : Val)
  /-- `refineSym`: σ is learned to be `repl`, everywhere at once. -/
  | refine (sym : Nat) (repl : Term)
deriving Inhabited

/-- A change, plus the breadcrumb identifying WHERE it happened — which is what
    makes it a point-fact rather than just a change. -/
structure PointDelta where
  stmtKey : Option Term
  trail : List (String × String)
  change : PointChange
  /-- The σ-context as it stood at this change.

      **A pointer copy, and it is here for RENDERING rather than for soundness.**
      docs/17 §3 argues that the 26 monotone `sctx` conses cannot falsify an
      earlier fact, which is why they need no instrumentation — true, and about
      soundness. But a σ's TYPE is what the `x : τ` form prints, so the replay
      still has to know the σ-context AT the point, and using the final one would
      print a type refined after the point the reader asked about. Carrying it per
      delta is O(1) (the list is immutable), and it keeps immutability honest at
      the rendering end as well as the soundness end. -/
  sctx : List (Nat × Term)
deriving Inhabited

/-- What the checker knew about one `let` binder at its binding (docs/16 S2).

    **Everything here is a value the machine already held**, which is what keeps
    the hover table off the cost ledger: no rendering, no traversal, and `sctx` is
    an immutable list so carrying it is a pointer copy rather than a copy.

    `ty?` is the σ's type when the bound value IS a σ. It is `none` for a value
    that is not one — including a CONSTRUCTOR TREE OVER σs, `Cons σ0 σ1`, which
    has no single σ to look up and no type recorded anywhere. `sctx` is what lets
    the surface say something useful about that case anyway: the σs are in the
    rendered value, and their types are in here. -/
structure LetNote where
  binder : Var
  ty? : Option Term
  val : Val
  /-- The σ-context AS IT STOOD at this binding — so a σ inside `val` can be
      given its type without the surface having to guess or re-derive one. -/
  sctx : List (Nat × Term)
deriving Inhabited

/-! ## The diagnostic LEDGERS — one record, so a new channel crosses for free

    **Why this is a record and not three fields on `St`.** Three diagnostic
    channels have now been added to this machine — the breadcrumb (docs/05), the
    hover type table (docs/16) and the point deltas (docs/17) — and **all three
    had to be taught, separately and after the fact, to cross `checkRFnBody`'s
    seal**, because a sealed body's state is discarded and each channel was a
    field threaded by hand. The third was written by the author of the second's
    documentation, which is the evidence that finished the argument:

    > A signpost its own author misses is not working as a signpost.

    The fix is not a fourth warning. It is to make the carry a UNIT: the ledgers
    are one field, `auditAllPathsD` carries one thing, and a fourth channel joins
    by construction rather than by remembering.

    **The breadcrumb is deliberately NOT in here, and the distinction is real.**
    It is a CURSOR — overwritten as the walk moves, copied out only on the failing
    path so a rejection reports where it happened. These are LEDGERS —
    append-only, accumulated across every path, carried out on success. Same door,
    opposite direction, different rule; grouping them would make one line shorter
    and the semantics wrong. -/
structure Ledgers where
  /-- Binder ↦ what the checker knew at its binding (docs/16 S2). Newest first. -/
  letTypes : List LetNote := []
  /-- THIS path's change history as DELTAS, newest first (docs/17 §2).

      **Deltas, not per-binder snapshots**, and the difference is asymptotic. A
      `refineSym` sweeps every entry of Ω, so recording "the fact for each binder
      at this point" would be O(|Ω|) per refinement and quadratic over a walk.
      The refinement's own content is one pair — σ and its replacement — so the
      delta is O(1) and a binder's fact at a point is recovered by replaying.
      Written down here because the naive reading of "record a fact at every
      primitive" is the quadratic one. -/
  points : List PointDelta := []
  /-- COMPLETED sub-paths, each oldest-first — a sealed body's branches, kept
      APART rather than concatenated (docs/17 §4).

      **This is the third lesson from the same door, and the first that changed
      the shape rather than joining it.** Appending body paths into one stream
      was the settled carry, and it is wrong at this granularity: a point is a
      position ON A PATH, so a statement walked once per branch has one answer
      per branch. Flattened, the replay stops at whichever branch came first and
      the rest are unreachable — first-path-unlabelled, in `fn` bodies, which is
      where every multi-path answer that matters lives. -/
  paths : List (List PointDelta) := []
deriving Inhabited

/-- How much this ledger grew past `base` — the entries a sealed body added on
    its own, with the enclosing ones left behind so they are not copied per path. -/
def Ledgers.own (path base : Ledgers) : Ledgers :=
  { letTypes := path.letTypes.take (path.letTypes.length - base.letTypes.length)
    points   := path.points.take   (path.points.length   - base.points.length)
    paths    := path.paths.take    (path.paths.length    - base.paths.length) }

/-- Prepend one ledger to another. Prepending keeps the earliest path's entries
    last in a newest-first list, which is what makes the surface's first-path rule
    come out right after its reverse. -/
def Ledgers.append (a b : Ledgers) : Ledgers :=
  { letTypes := a.letTypes ++ b.letTypes, points := a.points ++ b.points
    paths := a.paths ++ b.paths }

/-- Retire one finished sub-path. Its deltas become a path of their own and the
    enclosing stream does NOT absorb them — that is the whole point (docs/17 §4).

    **`full`, not `own`, and this is not an optimisation detail.** A path is its
    WHOLE history, so the entry it is closed with must include everything before
    the fork — the telescope seed above all, since `seedTelescopeV` runs before
    the body's state is captured and therefore lands in the base. Closing with
    `own` alone produces branches that begin after their own parameters were
    bound, and a replay over one of those finds no binding for any parameter at
    all. (It did that for exactly one build; the symptom was every parameter
    losing its point answer while `let`-bound locals kept theirs.)

    `own` is still right for `letTypes`, which is keyed by binder and would
    otherwise gain a duplicate per branch. -/
def Ledgers.closePath (full own acc : Ledgers) : Ledgers :=
  { letTypes := own.letTypes ++ acc.letTypes
    points := acc.points
    paths := full.points.reverse :: (own.paths ++ acc.paths) }


/-- Machine state: the environment Ω plus fresh-supply counters. `nextVar` is
    unused by §2 (all runtime var ids are minted by the macro) but is here for
    the runtime-binder minting later milestones (match) will need. -/
structure St where
  env : Omega
  nextLoan : Nat
  nextVar : Nat
  nextSym : Nat
  /-- The σ-context (§3.2's seam, §4): each symbolic id's type. Types are
      KNOWLEDGE, so since M32 R1 they are canonical `Term`s. -/
  sctx : List (Nat × Term) := []
  /-- **The moded-Π context** (M26-C): for a σ minted by sealing a function, the
      signature it was sealed at — **the Π itself**, peeled on demand at the call
      (M27-δ). It used to be an `FnDef`, "a telescope and a return type with no
      body", which is what a Π already is; a record beside it was a second
      representation of one thing, kept in step by hand. There is no type called
      `FnDef` in the kernel at all since M28 D9.

      Why this is not `sctx`. A borrow-moded Π has **no `Val`** — `readC` refuses
      `borrowT`, and rightly, since a borrow type is a telescope-position marker
      and not a type anything inhabits. So the sealed view of a function that
      takes a `&mut` cannot be recorded where `sctx` records types, and the
      honest place is one that keeps it as a `Term` telescope: exactly the shape
      the call rule already reads. That is what makes a CALL on such a σ the
      SAME rule as `.call` on a table entry (`callDeclC`) rather than a second
      one — §3's "abstract application at a moded Π", with nothing new under it.

      `sctx` still holds the borrow-free case (phase A's `σ : Π`), so the two
      contexts partition abstract callees by whether their type has a value. -/
  fsig : List (Nat × Term) := []
  /-- **What σ a seal SITE has at given inputs** (M32 R3, suspensions.md §2.4) —
      the table that makes the seal ⇝-evaluable.

      ⇝ is a judgment with no events, and the old rule refused the seal for
      exactly that reason: minting a fresh σ needs one, so a seal reduced twice
      under ⇝ would disagree with itself. What the refusal actually needed was
      not an event but a FUNCTION — a rule that gives the same answer both times
      — and this is that function, tabulated. The key is the seal's site
      (`Term.seal`'s first field, assigned at the program boundary) paired with
      its CAPTURED INPUTS: the values its admitted citations resolve to at the
      moment it is read. The value is the σ that pair names.

      **§2.4's "the seal site applied to its captured inputs", with the
      application interned rather than written out.** The doc's structured
      neutral `§σs i₁ … iₙ` and this table agree on everything a judgment can
      ask — the same site at the same inputs is one value (here, literally one
      σ), different inputs are different values — and they differ in what the
      value IS: a spine there, an atom here. Interning is what lets `fsig`,
      `sctx`, `callDeclC` and every golden go on speaking about a
      bare σ, and it is what makes a sealed function's type a plain entry rather
      than one that has to be instantiated at the spine's arguments before it
      can be read. Recorded as a deviation, with the reasoning, in the R3
      addendum.

      `nextSym` is what fills it, first-come, so a program whose seals are read
      in program order numbers them exactly as the ⇒-seal did. -/
  sealSites : List ((Nat × List Val) × Nat) := []
  /-- Loan groups (§6.1). A call mints one; ending a captured loan ends the
      whole group. Replaces M6's flat owed map — a wire is the degenerate
      `issued = []` group. -/
  groups : List Group := []
  /-- Fresh-supply for group ρ ids. -/
  nextGroup : Nat := 0
  -- (`decls`, the function table the `.call` rule looked names up in, retired in
  -- M28 D9 with `FnDef`. Scope is the call table: a callee is a binding lexically
  -- above the call, resolved by the surface into a spine on that slot.)
  /-- The loan-attached debts (12-design §2.1): the argument-borrow obligations
      (§5.1, site `.param`), seeded from the telescope and audited at return,
      plus each call's captured/issued contracts (sites `.call`/`.issue`).
      Held in state (not just returned by `seedTelescope`) so a §10 Refl
      refinement propagates into the owed types and pins — see `Debt`. Each
      explored path carries (and refines) its own copy. -/
  debts : List Debt := []
  /-- The return type, evaluated ONCE at function entry (where the telescope
      params are live) and pinned. A dependent return type (§5.3) may mention a
      param the body then consumes — re-reading it at return would find a ⊥ — so
      it is fixed at entry and refined per-path with the σ's (like obligations).
      `none` for a borrow-returning body, whose owed type is read at return
      against the surrendered payload. -/
  retTyVal : Option Term := none
  /-- D9 (M35): a BORROW-CARRYING return type, pinned at entry like `retTyVal`
      but RAW (readC refuses `borrowT`), with `old *v` resolved to the entry σ
      at seed — so the per-path refinement sweep reaches a mixed return's VALUE
      components exactly as it reaches the value-return path's pinned type. A
      type rebuilt at audit time would hold a STALE entry σ: refinement is a
      destructive rewrite of occurrences, and a freshly minted `sym σ` after
      the sweep names what the σ was, not what the branch learned. Consumed
      only by the audit's `collectResultBorrows` walk. -/
  retTyBorrow : Option Term := none
  /-- §5.4 exit-snapshot: per borrow parameter `v` (by var id), a fresh σ that
      the transformed return type pins a bare `*v` to. It lives ONLY here and in
      the pinned `retTyVal` — never in `sctx`/`obligations` — until the audit
      DEFINES it by substituting the borrow's collapsed final payload (a dedicated
      audit-local pass, not `refineSym`, so ⇜ stays knowledge-only). `old *v` pins
      to the entry σ instead and is untouched by that substitution. -/
  exitSyms : List (Nat × Nat) := []
  /-- §5.4 `old *v`: per borrow param (by var id), the ENTRY-payload σ minted at
      seed. `reflectC` resolves `old *v` to it in BOTH the return type and the body
      — a non-consuming snapshot reference to the entry value, which after the body
      mutates `v` is no longer `*v`'s live payload. Never substituted by the audit. -/
  entrySyms : List (Nat × Nat) := []
  /-- Execution mode (§8/§9 differential). `false` = CHECKING (the call rule
      uses the §5.3/§6.1 signature rule — groups, existentials); `true` =
      EXECUTING (a call runs the callee's actual body concretely). checkFn is
      always checking; the differential's concrete side is executing. -/
  executing : Bool := false
  /-- **Scope watermarks** (M31 Stage 0, pop-with-drop): for each still-open
      lexical scope, innermost first, the Ω *length* recorded when it was entered
      and whether it is a **match arm** (as opposed to a call frame).

      The arm flag exists because the two are unwound by different events. A
      frame unwinds to a depth it recorded itself. An arm unwinds at the `@popArm`
      seam the lazy builders (`pushJoinArms`) left in its body — and the seam has to take any
      scopes still open *inside* the arm with it, since a match in TAIL position
      within that arm has no seam of its own and its binders die with the arm that
      contains them. "Pop until an arm has been popped" is that rule, and the flag
      is what makes it askable.

      No new bookkeeping structure was needed for this and that is the point:
      `bindSlot` APPENDS and `setSlot` rewrites in place, so a scope's own
      entries are exactly the suffix of Ω past the length it recorded — the
      watermark is a `Nat` per open scope and nothing else. Every Ω-writing
      primitive preserves the invariant (`bindSlot` appends; `setSlot`,
      `writeC`, `refineSym`, `killBorrowInΩ`, `sendPayloadToLoan`, `endIssued`,
      `mergeRoot` all `map` over Ω and so are length- and order-preserving), so
      an index taken before a drop sweep is still valid after it.

      **The one site that is neither** is `readCWith`, which APPENDS a callee's
      actuals (it PREPENDED until M32 R1 re-keyed resolution by name) and restores
      Ω exactly before returning — so the violation cannot be observed: it opens no
      scope, closes none, and nothing inside a ⇝ reflection takes a watermark.
      Enumerated here rather than trusted, because a second Ω-splicing site would
      break the mechanism silently. -/
  scopeMarks : List (Nat × Bool) := []
  -- THE DIAGNOSTIC BREADCRUMB. Three fields that no rule reads. They exist so a
  -- rejection can be reported at the *source* the offending statement was written
  -- at: the surface holds a table from these keys to spans, and maps whatever the
  -- error was raised under. They are NOT σ-bearing state — no value is observed
  -- across a refinement through them — so `refineSym`/`generalizeStuck` leave them
  -- alone and §3.2's swept-state principle does not apply.
  --
  -- The key is the statement's own TERM rather than a path index because a
  -- statement can still be walked more than once — arms of a terminal match are
  -- one path each, and single-path walks rebuild the seam shape lazily
  -- (`pushJoinArms`) — so its position in the walked term is not its position
  -- in the source, while its term is the same term in every copy.
  /-- The statement currently being executed, in `stmtKeyOf` normal form. -/
  stmtKey : Option Term := none
  /-- The call argument currently being checked (`processArgs`), if any. Restored
      to the enclosing call's argument when an inner argument list completes. -/
  argKey : Option Term := none
  /-- The arms entered on this path, INNERMOST first: `(scrutinee, constructor)`.
      One statement is checked once per path, so which path failed is half the
      diagnosis. -/
  trail : List (String × String) := []
  -- THE HOVER TYPE TABLE (docs/16). Same class of thing as the breadcrumb above,
  -- and it sits here for the same reason: no rule reads it, no accept/reject
  -- depends on it, and it is not σ-bearing, so the sweeps leave it alone.
  --
  -- It differs from the breadcrumb in ONE way, and the difference is why it needs
  -- a flag of its own: a breadcrumb is read only when a check FAILS, and this is
  -- read only when one SUCCEEDS. A rejected program pays for its spans once; an
  -- accepted one would pay for its types on every path of every check in the
  -- corpus — including the differential's executing runs, which want none of it.
  /-- Collect `letTypes`? Off for every existing caller (`initSt`), on only for the
      elaborator's hover pass. A `let` costs one boolean test when it is off. -/
  hover : Bool := false
  /-- Collect `ledgers.points`? Off for every existing caller. -/
  pointHover : Bool := false
  /-- **THE DIAGNOSTIC LEDGERS, as one field.** See `Ledgers`: a new channel is a
      field there and crosses the seal for free, because the carry is this one
      name and not a list of them. -/
  ledgers : Ledgers := {}
deriving Inhabited

/-- The machine monad: errors are `String`s, state is `St`. -/
abbrev M := EStateM String St

/-- Raise a machine error. Errors are rich and stably-shaped (operation +
    variable/loan + reason); tests assert on distinctive substrings. -/
def throwErr {α : Type} (msg : String) : M α := fun s => EStateM.Result.error msg s

/-! ## The diagnostic breadcrumb

    Everything here is written and read for diagnostics only. Removing all of it
    would not change a single accept/reject. -/

/-- A rejection together with the breadcrumb it was raised under. `checkProgram`
    still returns a bare `String`; this is what the surface asks for when it needs
    to know *where* to put the squiggle. -/
structure Diag where
  msg : String
  stmtKey : Option Term := none
  argKey : Option Term := none
  trail : List (String × String) := []
  /-- Raised by the audit at return, so it is about the program's RESULT, whatever
      statement happened to run last. -/
  atReturn : Bool := false

/-- Pair a machine error with the state it was raised in. -/
def Diag.of (msg : String) (s : St) : Diag :=
  { msg := msg, stmtKey := s.stmtKey, argKey := s.argKey, trail := s.trail }

/-- The key a statement is filed under: the statement stripped of its
    continuation, since the walkers rebuild continuations (the lazy seam shape)
    but never the statement itself. A `let` reduces to its binder — runtime ids are globally
    unique, so that alone identifies the statement and costs nothing to carry. -/
def stmtKeyOf : Term → Term
  | .letIn x _ _ => .letIn x .unit .unit
  | .assign p rhs _ => .assign p rhs .unit
  | .seq e _ => e
  | .matchE s eqn _ => .matchE s eqn []
  | t => t

/-- Enter a statement. Clears the argument key: a failure after a call returned
    belongs to the statement, not to that call's last argument. -/
def noteStmt (t : Term) : M Unit :=
  modify fun s => { s with stmtKey := some (stmtKeyOf t), argKey := none }

/-- Enter a call argument (`processArgs`). -/
def noteArg (t : Term) : M Unit := modify fun s => { s with argKey := some t }

/-- Enter a match arm. Prepends — an executing-mode run enters an arm per
    recursive step, and appending would make the cost of a diagnostic nobody is
    reading quadratic in the length of the run. -/
def noteArm (scrut : Var) (ctor : String) : M Unit :=
  modify fun s => { s with trail := (scrut.name, ctor) :: s.trail }

/-- Record a state change against the breadcrumb it happened under (docs/17 §2).

    Called from the mutation primitives themselves, which is what makes
    carry-forward the definition of "the state here" rather than an interpolation
    (§3). One boolean test when the flag is off. -/
def notePoint (c : PointChange) : M Unit :=
  modify fun s =>
    if !s.pointHover then s else
      { s with ledgers.points :=
          { stmtKey := s.stmtKey, trail := s.trail, change := c, sctx := s.sctx }
            :: s.ledgers.points }

/-- Record what a `let` bound, for `x : τ` tooltips (docs/16). Called from
    `letStep` — the one shared binding site — so all three drivers file, and a
    fourth would inherit it exactly as it inherits the breadcrumb.

    **A σ is where a TYPE lives.** A symbolic value is a reserved pure name whose
    type `sctx` holds, so that lookup is the whole of the type case. A concrete
    value has no type recorded anywhere and none is invented: the value is stored
    and the surface says what it is, which is the honest answer rather than a
    synthesized one this bidirectional checker has no function to produce. -/
def noteLetType (x : Var) (v : Val) : M Unit :=
  modify fun s =>
    if !s.hover then s else
      let τ? : Option Term :=
        match v with
        | .know (.pvar p) => match symOfName? p with
          | some σ => s.sctx.lookup σ
          | none => none
        | _ => none
      { s with ledgers.letTypes :=
          { binder := x, ty? := τ?, val := v, sctx := s.sctx } :: s.ledgers.letTypes }

/-! ## State helpers -/

/-- Mint a fresh loan id. -/
def freshLoan : M Nat := do
  let s ← get
  set { s with nextLoan := s.nextLoan + 1 }
  pure s.nextLoan

/-- Mint a fresh symbolic id. -/
def freshSym : M Nat := do
  let s ← get
  set { s with nextSym := s.nextSym + 1 }
  pure s.nextSym

/-- Mint a fresh group ρ id. -/
def freshGroup : M Nat := do
  let s ← get
  set { s with nextGroup := s.nextGroup + 1 }
  pure s.nextGroup

/-- Read Ω. -/
def getEnv : M Omega := do pure (← get).env

/-- Replace Ω. -/
def setEnv (ω : Omega) : M Unit := modify (fun s => { s with env := ω })

/-! ### Resolution is by NAME, newest entry wins (M32 R1, E2 option (i))

    Ω is still an insertion-ordered `List (Var × Val)` and every `Var` still
    carries its id; what changed is that RESOLUTION ignores the id. `bindSlot`
    appends, so the newest binding of a name is the RIGHTMOST entry and "newest
    wins" is "take the last match" — which is why every reader below is a
    `getLast?` over a filter rather than a `find?`.

    What makes it sound is M31 Stage 0's pop-with-drop: an ended scope leaves no
    entry behind to shadow a later lookup, and a body may name only its own
    binders and the capital bindings above it (functions-are-comptime §2.4), so a
    live duplicate name is always a genuine shadowing and newest-wins is what it
    means. Everything that crosses frames — loans, borrows, obligations, the
    audit — is ℓ-keyed and shadow-immune by construction.

    **The frame shift is GONE** (M32 R4). `freshFrame`/`shiftVarsK` renumbered a
    body's ids on entry so a frame could not collide with its caller's; under
    name-keyed Ω `findSlot?` never reads an id, so the renumbering was inert and
    R4 deleted it with its differential. What separates two live frames is the
    scope watermark, which is what actually pops them.

    **The soundness condition this creates** is the L-suffix convention (M31
    Stage C's addendum item 2), which stops being style the moment a name is what
    resolves: a library lemma sharing a spelling with a `fn` is genuinely shadowed
    by it. `Dllbc.Std.lemmaFnCollisions` is that check. -/

/-- The newest binding of `x`'s NAME in `ω`, if any. -/
def findSlot? (ω : Omega) (x : Var) : Option (Var × Val) :=
  (ω.filter (fun kv => kv.1.name == x.name)).getLast?

/-- **Must a call of this callee be ENTERED?** — i.e. is applying it an EVENT?
    (M32 R4.)

    True for a sealed function (its σ has a moded signature in `fsig`) and for an
    imperative closure. Both are entered: a fresh frame, a fresh existential, an
    audit — things that happen once, at a point in time.

    This is what `reflectC` needs, and it is the same fact `.callV`'s retired
    refusal was keyed on, moved from the NODE to the VALUE. ⇝ has no events, so
    it has no reading of an application of one of these; what it does have a
    reading of is application of an ABSTRACT function — a `σ : Π` with no
    signature, a pure λ, a constant — which is the structured neutral `f a`, and
    which reflects structurally. The old refusal's advice ("written as an
    application") is now vacuous, because `f(a)` IS the application. -/
def calleeMustEnter (st : St) (v : Val) : Bool :=
  match v with
  | .closure _ node _ => Term.lamImperative node
  | v =>
    match v.symOf? with
    | some σ => (st.fsig.lookup σ).isSome
    | none => false

/-- Its position, for the in-place update `setSlot` must make. -/
def slotIdx? (ω : Omega) (x : Var) : Option Nat :=
  (ω.zipIdx.filter (fun p => p.1.1.name == x.name)).getLast?.map (·.2)

/-- Look up a slot by name, newest wins. Errors if the name is not an entry. -/
def lookupSlot (x : Var) : M Val := do
  match findSlot? (← getEnv) x with
  | some kv => pure kv.2
  | none => throwErr s!"lookupSlot: {x.name}#{x.id} is not an entry of Ω (unbound at runtime)"

/-- Append a fresh binding to Ω (insertion-ordered). -/
def bindSlot (x : Var) (v : Val) : M Unit := do
  notePoint (.bound x v)
  modify (fun s => { s with env := s.env ++ [(x, v)] })

/-! ### Scope watermarks (M31 Stage 0)

    A lexical scope is opened by recording Ω's length and closed by dropping the
    suffix past it. `openScope`/`takeScopeMark` are the bookkeeping half; the
    *drop* half (ending the loans inside the popped values) needs `endLoan` and
    therefore lives below `hasType`, as `popScope`. -/

/-- Open a lexical scope: record Ω's current length as the watermark. `arm` says
    whether this is a match arm (unwound by its seam) or a call frame (unwound to
    a depth the frame recorded). -/
def openScope (arm : Bool) : M Unit :=
  modify (fun s => { s with scopeMarks := (s.env.length, arm) :: s.scopeMarks })

/-- The number of scopes currently open — the handle a frame keeps so it can
    unwind back to it, however many scopes its body left open inside. -/
def scopeDepth : M Nat := do pure (← get).scopeMarks.length

/-- Take the innermost watermark off the stack, or `none` if no scope is open. -/
def takeScopeMark : M (Option (Nat × Bool)) := do
  match (← get).scopeMarks with
  | [] => pure none
  | m :: rest => do
    modify (fun s => { s with scopeMarks := rest })
    pure (some m)

/-- Overwrite an existing slot in place, preserving order. Errors if absent. -/
def setSlot (x : Var) (v : Val) : M Unit := do
  notePoint (.set x v)
  let ω ← getEnv
  match slotIdx? ω x with
  | some j => setEnv (ω.zipIdx.map (fun p => if p.2 == j then (p.1.1, v) else p.1))
  | none => throwErr s!"setSlot: {x.name}#{x.id} is not an entry of Ω"

/-! ## Value-tree search and rewrite

    All structural on `Val`, mutual with a `List Val` helper to cross the
    constructor-argument nesting. A loan id is unique across Ω, so each search
    finds at most one occurrence. -/

/-- Which kind of ownership node was found (drop needs to know which end of
    the loan lives inside the value being dropped). -/
inductive OwnKind where
  | loanMarker    -- a `loanM ℓ` sits in the value; its *borrow* is elsewhere
  | borrowNode    -- a `borrowM ℓ _` sits in the value; its *loan* is elsewhere
deriving Repr, DecidableEq

/-! The innermost (deepest, leftmost) ownership node of `v`, with its kind.
    "Innermost first" is load-bearing for the §2.5 self-reborrow rejection:
    a `borrowM ℓ (loanM ℓ′)` must surface ℓ′ before ℓ. -/
mutual
  def firstOwnNode : Val → Option (Nat × OwnKind)
    | .bot => none
    | .loanM ℓ => some (ℓ, .loanMarker)
    | .borrowM ℓ p =>
      match firstOwnNode p with
      | some r => some r            -- payload (deeper) first
      | none => some (ℓ, .borrowNode)
    | .node _ args => firstOwnNodeList args
    | _ => none                    -- a knowledge leaf holds no ownership node, by type
  termination_by v => sizeOf v
  def firstOwnNodeList : List Val → Option (Nat × OwnKind)
    | [] => none
    | v :: vs =>
      match firstOwnNode v with
      | some r => some r
      | none => firstOwnNodeList vs
  termination_by vs => sizeOf vs
end

/-! A borrow this value **holds** — the outermost `borrowM ℓ _` node whose loan
    is not in `keep` — if any. The complement of `firstOwnNode` for the drop
    sweep's purposes: dropping a scope must end the borrows its entries hold
    (sending each payload home), and must NOT reach for the loan markers they
    carry, whose borrows live elsewhere and end on their own owner's drop.

    Outermost-first, unlike `firstOwnNode`: a `borrowM ℓ (borrowM ℓ' _)` is
    surrendered from the outside in, because ending ℓ sends the inner borrow home
    as ℓ's payload and there is then nothing left here to end. -/
mutual
  def firstHeldBorrow (keep : List Nat) : Val → Option Nat
    | .borrowM ℓ p => if keep.contains ℓ then firstHeldBorrow keep p else some ℓ
    | .node _ args => firstHeldBorrowList keep args
    | _ => none
  termination_by v => sizeOf v
  def firstHeldBorrowList (keep : List Nat) : List Val → Option Nat
    | [] => none
    | v :: vs =>
      match firstHeldBorrow keep v with
      | some ℓ => some ℓ
      | none => firstHeldBorrowList keep vs
  termination_by vs => sizeOf vs
end

/-! The payload of the `borrowM ℓ _` node in `v`, if present. -/
mutual
  def findBorrowPayload (ℓ : Nat) : Val → Option Val
    | .borrowM ℓ' p => if ℓ' == ℓ then some p else findBorrowPayload ℓ p
    | .node _ args => findBorrowPayloadList ℓ args
    | _ => none
  termination_by v => sizeOf v
  def findBorrowPayloadList (ℓ : Nat) : List Val → Option Val
    | [] => none
    | v :: vs =>
      match findBorrowPayload ℓ v with
      | some p => some p
      | none => findBorrowPayloadList ℓ vs
  termination_by vs => sizeOf vs
end

/-! Substitute `newV` for the (unique) `loanM ℓ` marker in `v`. -/
mutual
  def replaceLoanMarker (ℓ : Nat) (newV : Val) : Val → Val
    | .loanM ℓ' => if ℓ' == ℓ then newV else .loanM ℓ'
    | .borrowM ℓ' p => .borrowM ℓ' (replaceLoanMarker ℓ newV p)
    | .node n args => .ctor n (replaceLoanMarkerList ℓ newV args)
    | v => v                       -- ⊥, knowledge: no loan markers
  termination_by v => sizeOf v
  def replaceLoanMarkerList (ℓ : Nat) (newV : Val) : List Val → List Val
    | [] => []
    | v :: vs => replaceLoanMarker ℓ newV v :: replaceLoanMarkerList ℓ newV vs
  termination_by vs => sizeOf vs
end

/-! Replace the (unique) `borrowM ℓ _` node in `v` with ⊥ (kill the borrow). -/
mutual
  def replaceBorrowWithBot (ℓ : Nat) : Val → Val
    | .borrowM ℓ' p => if ℓ' == ℓ then .bot else .borrowM ℓ' (replaceBorrowWithBot ℓ p)
    | .loanM ℓ' => .loanM ℓ'
    | .node n args => .ctor n (replaceBorrowWithBotList ℓ args)
    | v => v                       -- ⊥, knowledge: no borrow to kill
  termination_by v => sizeOf v
  def replaceBorrowWithBotList (ℓ : Nat) : List Val → List Val
    | [] => []
    | v :: vs => replaceBorrowWithBot ℓ v :: replaceBorrowWithBotList ℓ vs
  termination_by vs => sizeOf vs
end

/-! Whether a `loanM ℓ` marker occurs anywhere in `v`. -/
mutual
  def containsLoan (ℓ : Nat) : Val → Bool
    | .loanM ℓ' => ℓ' == ℓ
    | .borrowM _ p => containsLoan ℓ p
    | .node _ args => containsLoanList ℓ args
    | _ => false                   -- ⊥, knowledge: no loan markers
  termination_by v => sizeOf v
  def containsLoanList (ℓ : Nat) : List Val → Bool
    | [] => false
    | v :: vs => containsLoan ℓ v || containsLoanList ℓ vs
  termination_by vs => sizeOf vs
end

/-! A loan marker in *owned position* of `v` — the constructor spine — if any,
    leftmost-innermost first. Crucially this does NOT descend into `borrowM`
    payloads: a borrow the value *carries* is relocated as-is on a move, its
    internal reborrow suspension travelling with it; only markers in owned
    position must be ended (End-Mut) before the value can be moved or matched.
    This is what makes a match's field-loan chain collapse lazily when the
    owner is finally read back (§3.3). -/
mutual
  def firstLoanMarker : Val → Option Nat
    | .loanM ℓ => some ℓ
    | .borrowM _ _ => none
    | .node _ args => firstLoanMarkerList args
    | _ => none                    -- ⊥, knowledge: no owned loan marker
  termination_by v => sizeOf v
  def firstLoanMarkerList : List Val → Option Nat
    | [] => none
    | v :: vs =>
      match firstLoanMarker v with
      | some ℓ => some ℓ
      | none => firstLoanMarkerList vs
  termination_by vs => sizeOf vs
end

/-! Is a **type** index-kind (§2.1) — `Nat`/`Bool`/`Unit`, a pure-former type
    (an `Id` proof type, a `Type`, a function type), or a **Σ pack all of whose
    components are themselves copyable-or-erased**? A σ of such a type reads by
    copy. `List`/`Array`/user types are data.

    **THE Σ CASE IS NEW (M34 sigma-copy)** and it is the one place this file's
    doctrine moved. What it says: `Σ (x : A). B` copies iff each of its two
    positions copies, where an ERASED position — comptime-marked and erasure-bound,
    `erasureBound` below — is exempt, because a position that costs nothing at
    runtime duplicates nothing when the pack is copied. `Σ0 (n : Nat). Le n MAX` —
    a machine integer written as a refinement pack — is therefore Copy: the value
    half is a `Nat` and the proof half is erased. `Σ (c : Nat). &mut (Array c T)`
    is NOT: a borrow is neither copyable nor erased, and duplicating exclusive
    access is unsound.

    The dependent tail is decided with the binder **opaque**: `cod` still mentions
    `x`, nothing is substituted for it, and a tail whose kind cannot be settled
    without knowing the binder's value falls through to `false`. That is the same
    conservative default a σ with no `sctx` entry gets, and it is why
    `Σ (n : Nat). VecF Nat n` moves.

    Fuel is what makes this terminate and what bounds the `whnf` at each
    component; a Σ nested deeper than the fuel answers MOVE, conservatively. -/
mutual
  def indexKindTy : Nat → Term → Bool
    | _, .const "Nat" => true
    | _, .const "Bool" => true
    | _, .const "Unit" => true
    | _, .idT _ _ _ => true
    -- The `.type`/`.pi` arms are REACHABLE, but no longer from a ⇒-read of a
    -- written or computed type (types-no-exec removed that reading outright).
    -- What still arrives here typed `Type` or `Π` is a σ — a generic `fn`'s
    -- comptime type parameter in `sctx`, which `indexKindV` classifies by its
    -- recorded TYPE — and a Σ component position via `indexKindComp` below.
    -- Copy-on-read is a KEEP: these say a type-classified σ copies rather than
    -- moves, which the differential needs (modes cannot replace index-kind
    -- copying).
    | _, .type => true
    | _, .pi _ _ _ => true
    | fuel + 1, .sigmaT _ dom cod => indexKindComp fuel dom && indexKindComp fuel cod
    | _, _ => false
  termination_by fuel _ => (fuel, 0)
  /-- One component POSITION of a Σ: erased (`erasureBound` below) or index-kind
      in its own right. `whnf` first, for the same reason the σ case below does
      it: a redex-headed component type that reduces to `Nat` should copy. -/
  def indexKindComp : Nat → Term → Bool
    | fuel, τ => erasureBound fuel τ || indexKindTy fuel (Pure.whnf fuel τ)
  termination_by fuel _ => (fuel, 2)
  /-- **Is this Σ position ERASED — marked comptime AND erasure-bound?** The
      marker is what a capital Σ binder puts on the domain and `Σ0` puts on the
      tail, and it is most of the answer: a comptime position costs nothing at
      runtime, so duplicating it duplicates nothing.

      **The second conjunct is a DIFFERENTIAL requirement, not a semantic one**,
      and it exists because the marker alone is not a fact both machines can read.
      The checking machine holds a pack as a σ and asks this question of its TYPE;
      the executing machine holds `Pair(3, Cons(1, Nil))` and asks `indexKindT`'s
      Pair rule of the VALUE, where a concrete component carries no mode anywhere.
      Marker-alone therefore ACCEPTS a program the run gets stuck on — measured,
      not feared: `Σ0 (n : Nat). List Nat` passed to a callee that uses it twice
      checked and then died at `readR: p#0 holds ⊥`.

      So a marked position is exempt only when it is erasure-bound in the sense
      §2.1 already uses: index-kind, or a type whose constructor set the machine
      does not know — a stuck proposition spine like `Le n MAX`, whose concrete
      inhabitants are `unit`/`Refl` and therefore index-kind on the value side
      too. `List Nat` has a known constructor set and is not index-kind, so a
      marked `List` component is NOT exempt and the pack moves in both machines.

      RESIDUAL, stated because it is narrow rather than absent: a marked component
      whose type is STUCK but computes to an aggregate at concrete indices
      (`VecF (List Nat) n`) is exempt here and data at the value side. That is the
      same discrimination `Direct.lean`'s pain diary already ruled undecidable
      without making `Le` a primitive former — "a σ typed by a stuck `VecF Nat n`
      is exactly stuck-recursor-to-`Type` yet copying it copies DATA" — so it is a
      known gap of a known shape, filed with that arc, not a new class. -/
  def erasureBound : Nat → Term → Bool
    | fuel, τ =>
      Term.domComptime τ &&
        (let τ' := Pure.whnf fuel τ.stripCmp
         indexKindTy fuel τ' || (Pure.typeCtors τ').isNone)
  termination_by fuel _ => (fuel, 1)
end

/-- Is this `Pair` component ERASED — a σ whose `sctx` entry is marked and
    erasure-bound? This is `componentMode`'s question (§2.1, M33a) asked from the
    copy side, and asked the same way: a component σ's `sctx` entry is `⇝τ`
    exactly when the producing Σ marked that position comptime (`buildResult` on
    the concrete path, `reattachSigmaMode` on the symbolic one). `erasureBound` is
    then the same second conjunct the type side applies, so the two levels answer
    one question rather than two that happen to agree.

    `false` for a component that is not a σ is the honest answer rather than a
    rounded-up one — a concrete constructor tree has no mode recorded anywhere —
    and it is safe HERE in a way it would not be at `componentMode`, because the
    caller falls through to classifying the component by shape, and `erasureBound`
    has already restricted the type side to positions whose concrete inhabitants
    that shape test accepts. -/
def packCompErased (fuel : Nat) (sctx : List (Nat × Term)) : Term → Bool
  | .pvar x =>
    match symOfName? x with
    | some σ => match sctx.lookup σ with
      | some τ => erasureBound fuel τ
      | none => false
    | none => false
  | _ => false

/-! Is a piece of KNOWLEDGE index-kind, so §2.1's copy-on-read applies? A concrete
    `Nat`/`Bool`/`Unit` tree, a pure-former value (a proof — `Refl` or a neutral
    proof spine — a type, a λ), or a σ whose `sctx` type is index-kind. Data
    proper (`Cons`-trees, pairs, user constructors) MOVES even when marker-free:
    silent aggregate duplication is the cost-opacity Rust's move discipline
    prevents, so the calculus keeps Rust's line (§2.1). Copy-or-move is decided by
    value shape — the σ-context's type for symbolic values — not a declared trait.
    A σ with NO sctx entry moves (the conservative default).

    **THE DEFERRAL IS PARTLY OVER** (M34 sigma-copy). What stood here said:
    "DEFERRED (until measured pain, per team-lead): tuple-of-copyables (a `Pair
    Nat Nat` as Copy, Rust-style) — a data ctor all of whose fields are
    index-kind stays a MOVE for now." The pain was measured — a machine integer
    written as a refinement pack (`Σ0 (n : Nat). Le n MAX`) is morally a scalar
    and cost a capture-before-consume staging at every reuse — so the amended
    doctrine is:

      **DATA PROPER STILL MOVES; a Σ PACK copies iff every component is
      copyable-or-erased.**

    Rust's line is unchanged where Rust draws it: a `Cons`-tree moves, a user
    constructor moves, and a pack with a `List` in it moves, because silent
    aggregate duplication is the cost-opacity the move discipline prevents. What
    moved is the one shape where Rust ALSO copies and DLLBC did not — `#[derive
    (Copy)]` on a struct of scalars — with erased positions counted as free
    because they are erased. `Pair` is the only constructor this reaches, since
    `Pair` is the only one a Σ builds; every other ctor is data by name. -/
def indexKindT (fuel : Nat) (sctx : List (Nat × Term)) : Term → Bool
  | .ctorApp "Z" [] => true
  | .ctorApp "S" [n] => indexKindT fuel sctx n
  | .ctorApp "True" [] => true
  | .ctorApp "False" [] => true
  | .ctorApp "unit" [] => true
  | .ctorApp "Refl" _ => true                               -- a proof
  -- A Σ pack, at the value level. Each component is exempt if the producing Σ
  -- marked it comptime (`packCompErased`, which reads the same `sctx` entry
  -- `componentMode` reads), and otherwise must be index-kind itself. Nesting is
  -- free: the recursive call handles `Pair(n, Pair(h, unit))` without a case.
  -- A pack that HOLDS STATE never arrives here — `Val.ctor` only collapses a
  -- node to a knowledge leaf when every child is knowledge, so the slice pack
  -- `Σ (c : Nat). &mut (Array c T)` is a `node` and takes `indexKindV`'s
  -- data answer below.
  | .ctorApp "Pair" [a, b] =>
    (packCompErased fuel sctx a || indexKindT fuel sctx a)
      && (packCompErased fuel sctx b || indexKindT fuel sctx b)
  | .ctorApp _ _ => false                                   -- data → move
  -- A σ, which is a reserved pure NAME since M32 R1. Whnf its type before
  -- classifying: a redex-headed type that reduces to Nat should copy, not be
  -- mistaken for data. Misclassification is otherwise only ever toward MOVE
  -- (conservative), but the whnf hardens the σ side. An ordinary pure name is a
  -- proof/type variable and copies, which is what `.pvar => true` used to say
  -- when σ's were a former of their own.
  | .pvar x =>
    match symOfName? x with
    | some σ => match sctx.lookup σ with
      | some τ => indexKindTy fuel (Pure.whnf fuel τ).stripCmp
      | none => false
    | none => true
  | .type => true
  | .const _ => true
  | .pi _ _ _ => true
  | .lam _ _ _ => true
  | .sigmaT _ _ _ => true                                   -- a type
  | .idT _ _ _ => true
  | .app _ _ => true                                        -- a pure-former spine
  -- A binder-mode marker is not a value and never stands in a slot (§6); it
  -- reaches here only through a malformed term, and the conservative answer is
  -- the one every unclassifiable shape gets.
  | _ => false

/-- The same question of a STORE value. Two lines of it are new information and
    the rest is dispatch: a node holds state, so it is data and it moves; a
    marker is not a value at all. -/
def indexKindV (fuel : Nat) (sctx : List (Nat × Term)) : Val → Bool
  | .know t => indexKindT fuel sctx t
  -- A recursor spine over runtime arms is a FUNCTION VALUE, so it copies for the
  -- same reason a λ does — and it must, because that spine is what `ih` holds in
  -- executing mode and a body may name `ih` twice. Before R1 it was a `.app`
  -- spine and took the pure-former answer; the skeleton is where it lives now,
  -- and the answer travels with it rather than with the former it used to be.
  | .node "§rec" _ => true
  -- **AND THIS IS THE Σ-COPY NEGATIVE CONTROL** (M34 sigma-copy). A `node` is
  -- what a constructor tree becomes when something inside it holds STATE — a
  -- borrow, a loan marker, a hole — because `Val.ctor` collapses to a `know`
  -- leaf only when every child is knowledge. So the M24 slice pack
  -- `Σ (c : Nat). &mut (Array c T)` reaches HERE and not the `Pair` rule above:
  -- its borrow component is neither copyable nor erased, and duplicating
  -- exclusive access would hand out two owners of the same payload. The rule
  -- costs nothing to state because the representation already states it.
  | .node _ _ => false                                      -- data/state → move
  -- A runtime function value is closed and marker-free, so the ownership
  -- machinery is doubly vacuous on it exactly as it is on a λ; §7 cost 2's "never
  -- partially applied, closed" is what earns this. A CONSERVATIVE DEFAULT, and
  -- corrected at M27-P3: `ih` is CALLED, and a call LOCATES its callee rather
  -- than moving it, so a recursive call never reaches here at all.
  | .closure _ _ _ => true
  | .borrowM _ _ => false
  | .loanM _ => false
  | .bot => false

/-! ## The two store-wide sweeps, two-layered (M32 R1)

    Both used to be `Val`-tree traversals over a domain that was sometimes
    semantics and sometimes syntax. With knowledge at rest being a canonical
    `Term`, each is a walk down the STATE SKELETON that switches to `Term`-level
    machinery the moment it reaches a leaf — and at the leaf, refinement is not a
    traversal at all but `substP` at the σ's reserved name.

    A knowledge leaf is where every σ lives, so the skeleton walk exists only to
    find the leaves: markers hold no σ's, and a node's job here is to be descended
    through. -/

/-! Substitute the knowledge `repl` for every occurrence of σ in a store value —
    the store half of ⇜ (§3.2 refinement substitutes σ *everywhere*). -/
mutual
  def substSym (σ : Nat) (repl : Term) : Val → Val
    | .know t => .know (Term.substSym σ repl t)
    | .node n args => .ctor n (substSymList σ repl args)
    | .borrowM ℓ p => .borrowM ℓ (substSym σ repl p)
    -- **Refinement reaches a captured environment** (M32 R2, suspensions.md §3):
    -- σ := v is atom-keyed and COMMUTES with evaluation, so rewriting ρ and
    -- evaluating the body later agrees with cooking first. No cooking here, and
    -- that is the criterion's answer rather than an optimisation. The body is
    -- rewritten too: raw it holds no σ (a program cannot write one), cooked it
    -- holds exactly the ones a later comparison would see.
    | .closure ρ b u => .closure (substSymRho σ repl ρ) (Term.substSym σ repl b)
                                 (u.map (Term.substSym σ repl))
    | .loanM ℓ => .loanM ℓ
    | .bot => .bot
  termination_by v => sizeOf v
  def substSymList (σ : Nat) (repl : Term) : List Val → List Val
    | [] => []
    | v :: vs => substSym σ repl v :: substSymList σ repl vs
  termination_by vs => sizeOf vs
  def substSymRho (σ : Nat) (repl : Term) : List (Var × Val) → List (Var × Val)
    | [] => []
    | (x, v) :: ps => (x, substSym σ repl v) :: substSymRho σ repl ps
  termination_by ps => sizeOf ps
end

/-! Abstract a whole sub-TERM `target` into the σ `σb` everywhere — the inverse of
    `substSym`, keyed on structural identity of the whole subterm rather than a σ
    id. It is the store half of the §19 stuck-spine split: a Bool scrutinee that
    reduced to a stuck spine (`leb σ σp`, not a bare σ) is generalized to a fresh
    σb, so the ordinary True/False refinement can fire.

    Only the leaves are rewritten, and that is exact rather than approximate: the
    target is a spine over σ's, which is knowledge, and knowledge cannot be a
    marker or a node — so an occurrence of it inside a store value is inside a
    knowledge leaf, always. NF the target before abstracting so the match is up to
    conversion-stable syntactic identity. -/
mutual
  def abstractInto (target : Term) (σb : Nat) : Val → Val
    | .know t => .know (Term.abstractInto target σb t)
    | .node n args => .ctor n (abstractIntoList target σb args)
    | .borrowM ℓ p => .borrowM ℓ (abstractInto target σb p)
    -- The generalization sweep reaches ρ and the body alike. What it does NOT do
    -- is cook — `cookForGen` below has already run on the values this sweep is
    -- about, because cooking is an evaluation and this is a rewrite (§3).
    | .closure ρ b u => .closure (abstractIntoRho target σb ρ) (Term.abstractInto target σb b)
                                 (u.map (Term.abstractInto target σb))
    | .loanM ℓ => .loanM ℓ
    | .bot => .bot
  termination_by v => sizeOf v
  def abstractIntoList (target : Term) (σb : Nat) : List Val → List Val
    | [] => []
    | v :: vs => abstractInto target σb v :: abstractIntoList target σb vs
  termination_by vs => sizeOf vs
  def abstractIntoRho (target : Term) (σb : Nat) : List (Var × Val) → List (Var × Val)
    | [] => []
    | (x, v) :: ps => (x, abstractInto target σb v) :: abstractIntoRho target σb ps
  termination_by ps => sizeOf ps
end

/-- **COOK a closure** (M32 R2, suspensions.md §2.3/§3): evaluate the raw body
    under its captured ρ, canonically.

    `Term.underRho` is the whole of it plus `Pure.nf`, and cooking is therefore
    NOT a new judgment — it is the pure fragment reading the suspension, using the
    `let` rule it already had. It deliberately does not go through `readC`: a
    comptime λ's free names are all in ρ (`admitGlobals` is what guarantees that
    at formation), so there is no live place left to resolve, and keeping cooking
    out of `reflectC` keeps ⇝ a structural recursion instead of a fuelled one.

    Used three ways, differing only in what is done with the answer: TRANSIENTLY
    for a conversion or a typing (§2.3 — Stage V measured the raw pair a wash,
    since `convert` normalizes both sides either way), PERSISTENTLY at a
    generalization sweep (§3, `cookForGen`), and as the formation CHECK (§2.2). -/
def cookClosure (fuel : Nat) (ρ : List (Var × Val)) (node : Term) : Term :=
  Pure.nf fuel (Term.underRho (Val.rhoTerms ρ) node)

/-- **COOK-AT-GENERALIZATION** (M32 R2, suspensions.md §3) — the one place cooking
    is PERSISTENT, and the rule is derived rather than chosen.

    The criterion: a store-wide sweep is safe iff it commutes with evaluation.
    Refinement (σ := v) is atom-keyed and commutes, so raw closures are fully
    correct under it and `substSym` above just rewrites ρ. Generalization is
    keyed on a COMPOUND — a whole spine — and does not: a raw body plus its ρ
    holds the spine's INGREDIENTS and can re-mint it after the sweep has passed,
    speaking pre-generalization vocabulary while the branch speaks σb.

    Stage V sharpened it to MATERIALIZED-vs-LATENT: `abstractInto` already
    descends captured environments, so a spine materialized in ρ survives the
    sweep and raw agrees with cooked. Only a spine the body RE-MINTS from ρ's
    ingredients diverges. Hence **the rule is support-scoped**: cook exactly the
    closures whose ρ mentions a σ in the abstracted spine's support, and leave
    every other closure raw. Not an optimization — a closure with no σ of the
    support in its ρ cannot re-mint the spine, so cooking it would be work with
    no question attached.

    **Imperative bodies are never cooked, ever** (§3): they never participate in
    conversion — audited once at formation, then only entered — and cooking one
    is not merely pointless, it is undefined (`readC` has no rule for a body).
    Their ρ's are still descended, because a comptime closure can sit inside one.

    Cannot cascade: cooking normalizes, and normalization cannot trigger a split
    (a split is a ⇒ event, and this is ⇝). Composes with the sweep's traversal
    order because it is a separate pass over the same targets, run first — the
    cooked form is what `abstractInto` then rewrites. -/
partial def cookForGen (fuel : Nat) (support : List Nat) : Val → Val
  | .closure ρ node u =>
    let ρ' := ρ.map (fun p => (p.1, cookForGen fuel support p.2))
    if Term.lamImperative node then .closure ρ' node u
    else if (Val.symIdsRho ρ).any (fun σ => support.contains σ) then
      -- Cooked, and WRITTEN BACK: the cooked body is closed, so its ρ is empty
      -- and the raw syntax is gone. §6's sharp edge answered — nothing downstream
      -- shows source syntax for a λ (the renderer prints binders and elides), so
      -- no message depended on it. The ascription rides through untouched: it is
      -- the contract, not the code, and cooking is about the body.
      .closure [] (cookClosure fuel ρ node) u
    else .closure ρ' node u
  | .node n args => .ctor n (args.map (cookForGen fuel support))
  | .borrowM ℓ p => .borrowM ℓ (cookForGen fuel support p)
  | v => v

/-! ## The two Ω-primitives

    Everything the borrow machinery does is one of these two, aimed at Ω's
    own bookkeeping (§2.5: "no rules of its own beyond bookkeeping"). Each
    errors distinctively when its target end is not an entry of Ω — the
    stuckness that rejects the self-reborrow (§2.5). -/

/-- Find the `borrowM ℓ p` node in Ω, set it to ⊥, and return its payload `p`.
    Errors if no such borrow is an entry (its other end may be in flight). -/
def killBorrowInΩ (ℓ : Nat) : M Val := do
  let ω ← getEnv
  match ω.findSome? (fun kv => findBorrowPayload ℓ kv.2) with
  | none =>
    throwErr s!"end: borrow of ℓ{subNat ℓ} is not an entry of Ω (its other end is in flight — cannot end)"
  | some p => do
    setEnv (ω.map (fun kv => (kv.1, replaceBorrowWithBot ℓ kv.2)))
    pure p

/-- Find the `loanM ℓ` marker in Ω and replace it with payload `p` (send the
    borrowed value home). Errors if no such loan marker is an entry. -/
def sendPayloadToLoan (ℓ : Nat) (p : Val) : M Unit := do
  let ω ← getEnv
  if ω.any (fun kv => containsLoan ℓ kv.2) then
    -- **Rejoin is merge** (¶3.3), and this is where it belongs: the moment a payload
    -- plugs back into its marker is the moment the last marker under an array node
    -- can be gone. Every End-Mut path — owner demand, the §5.4 audit collapse, a §6.1
    -- group release — funnels through here, so a rejoined array is a run again
    -- wherever it lives, with no rule having to remember to say so.
    setEnv (ω.map (fun kv => (kv.1, Val.mergeArrays (replaceLoanMarker ℓ p kv.2))))
  else
    throwErr s!"end: loan ℓ{subNat ℓ} is not an entry of Ω (cannot plug payload back)"

-- `endLoan` (group-aware, §6.1) is defined after `hasType`, which it needs to
-- audit issued-borrow payloads at group end.

/-- **Drop** (§2.3): the total procedure that vacates a displaced value. End
    its ownership nodes innermost-first — a `loanM ℓ` in the value kills its
    borrow in Ω and the payload returns into the value (re-scanned); a
    `borrowM ℓ p` in the value sends `p` home to its loan in Ω and the node
    becomes ⊥ — then discard the (now ownership-free) remainder.

    Each end requires the complementary end to be an entry of Ω, else the
    program is rejected (§2.5). Fuel bounds the reorganize-then-retry loop
    (the number of ownership nodes is finite). -/
def drop : Nat → Val → M Unit
  | 0, _ => throwErr "drop: out of fuel"
  | fuel + 1, v =>
    match firstOwnNode v with
    | none => pure ()                                   -- ownership-free: discard
    | some (ℓ, .loanMarker) => do
      let p ← killBorrowInΩ ℓ                           -- kill borrow, payload returns
      drop fuel (replaceLoanMarker ℓ p v)
    | some (ℓ, .borrowNode) =>
      match findBorrowPayload ℓ v with
      | none => throwErr "drop: internal invariant — borrow node vanished mid-scan"
      | some p => do
        sendPayloadToLoan ℓ p                           -- send payload home
        drop fuel (replaceBorrowWithBot ℓ v)

/-! ## Places and their positions

    §1.1's positional restriction generalizes (¶2.1). A place is a variable under a
    **path**, and a path is a sequence of steps:

        step ::=  *              peel a borrow            (§2)
               |  [t]            index step, t : Nat      (new)
               |  [t ; t′]       range step               (new)

    The old `derefs : Nat` was exactly this path restricted to `peel`. ⇐, `&mut` and
    the ⇒-take are all defined only on places, and all share this resolution.

    Navigation below is purely STRUCTURAL: it assumes the tree is already segmented
    at each index/range boundary. `carveAt` (further down — premise (2) is a
    `hasType` call, so the carve cannot be defined until `hasType` is) is what
    arranges that. Keeping the two apart is what lets the borrow machinery's own
    reads stay free of the carve's premises, which is ¶8.1's claim that nothing in
    the borrow machinery changed. -/

/-- One step of a place path. -/
inductive Step where
  /-- `*` — peel a borrow (§2.2). -/
  | peel : Step
  /-- `[i | ev]` — the index step. `ev` is the cited containment evidence, `none`
      when the bound computes: ¶3.2's supply route 1, "every literal-indexed array
      access is free". -/
  | idx : Term → Option Term → Step
  /-- `[lo ; cnt | ev]` — the range step, in OFFSET-AND-COUNT (¶2.1), so that
      `a[lo ; cnt] : Array cnt T` is read straight off the syntax with no arithmetic
      and no rule below ever produces a `sub`. -/
  | rng : Term → Term → Option Term → Step

/-- A resolved place: a root variable and the path from it. -/
structure Pos where
  root : Var
  path : List Step

/-- The all-peels path of length `n` — what a `Pos` used to be, verbatim. -/
def peels : Nat → List Step
  | 0 => []
  | n + 1 => .peel :: peels n

/-- The extent of an array-shaped value. Read off the value itself wherever that is
    possible (`arrExtentPure?`: a run knows its length, a segment list sums, an
    `arrCat` spine carries both halves); a bare σ's extent lives in its `sctx` type,
    which is the one case only the machine can serve. That partiality is what lets
    ¶1.1's abbreviation stand — an uncarved array needs no wrapper stamping it with
    its length. -/
def arrExtent (fuel : Nat) (v : Val) : M Term := do
  match Val.arrExtentPure? v with
  | some c => pure (Pure.nf fuel c)
  | none =>
    match v.symOf? with
    | some σ =>
      match (← get).sctx.lookup σ with
      | some τ =>
        match Pure.asArrayTy? (Pure.whnf fuel τ).stripCmp with
        | some (n, _) => pure (Pure.nf fuel n)
        | none => throwErr s!"array: σ{subNat σ} is not of array type (its sctx type is {τ.pretty})"
      | none => throwErr s!"array: σ{subNat σ} has no type in sctx — cannot read its extent"
    | none => throwErr s!"array: {v.pretty} is not an array value (no extent to read)"

/-- One entry of ¶3.1's **extent map**: an offset, a count, and the body sitting
    there. `Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ⟩` induces `[(0,1,owned), (1,2,loaned ℓ)]`.

    The map IS the aliasing invariant, and it is maintained by construction rather
    than checked: segments partition the array, so **no two loans of one array can
    overlap, ever, because two segments cannot overlap**. There is no disjointness
    *test* anywhere below — only the question of whether a requested range can be
    MADE into a segment, which is what the carve answers. -/
structure Leaf where
  base : Term
  count : Term
  body : Val

/-- The range's exclusive end, `lo + cnt`, spelled the way a program can write it.

    `add` recurses on its FIRST argument, so `add lo cnt` is stuck whenever `lo` is
    symbolic — including at every `a[i]`, where `cnt` is literally 1 and the obligation
    would read `Le (add i (S Z)) n`. No program writes that. `S i` denotes the same
    number and is what M13/M14's cursor bound already is (`p : Le (S i) (len *v)`) —
    which is ¶3.5's own observation that range places "take the same terms" the swap
    sites have been threading since M13. So a CONCRETE count is unrolled into
    successors and a symbolic one keeps `add`, where it computes. -/
def rangeEnd (fuel : Nat) (lo cnt : Term) : Term :=
  match Term.natOf? (Pure.nf fuel cnt) with
  | some k => (List.range k).foldl (fun acc _ => Term.succ acc) lo
  | none => ty{ %(Pure.kAddFn) %lo %cnt }

def extentMapGo (fuel : Nat) (b : Term) : List Val → M (List Leaf)
  | [] => pure []
  | s :: rest =>
    match Val.asSeg? s with
    | none => throwErr "array: malformed segment node (expected §seg [c, body])"
    | some (c, body) => do
      let tl ← extentMapGo fuel (Pure.nf fuel (rangeEnd fuel b c)) rest
      pure (⟨b, c, body⟩ :: tl)

/-- The sum of a leaf list's extents, RIGHT-NESTED and with no trailing `Z`.

    The shape matters and is not cosmetic. `add` recurses on its first argument, so a
    trailing `add c Z` is STUCK the moment `c` is symbolic — and then the audit's
    `Array (add k (add rest Z))` never converts with the owed `Array (add k rest)`,
    which is the one conversion premise (3)'s residue transition exists to make
    definitional. Right-nesting also matches the `arrCat` spine the ⇝ fold builds and
    the `m ≡ add lo' (add cnt rest)` the transition solves, so all three agree. -/
def sumExtents : List Leaf → Term
  | [] => Term.zero
  | [l] => l.count
  | l :: rest => ty{ %(Pure.kAddFn) %(l.count) %(sumExtents rest) }

/-- The extent map of an array node. An UNCARVED array is a single leaf spanning it. -/
def extentMap (fuel : Nat) (v : Val) : M (List Leaf) :=
  match v with
  | .node "§segs" segs => extentMapGo fuel Term.zero segs
  | _ => do pure [⟨Term.zero, ← arrExtent fuel v, v⟩]

/-- Locate the segment a step designates, by its (base, count) rather than by its
    position in the list — so navigation survives a sibling's body changing under it
    (a drop that ends a loan elsewhere in the same node, a merge that ran in between).
    Returns the segment's index and its leaf. -/
def findSeg (fuel : Nat) (lo cnt : Term) (v : Val) : M (Nat × Leaf) := do
  let leaves ← extentMap fuel v
  match leaves.findIdx? (fun l => Pure.convert fuel l.base lo && Pure.convert fuel l.count cnt) with
  | some i =>
    match leaves[i]? with
    | some l => pure (i, l)
    | none => throwErr "array: internal — segment index out of range"
  | none =>
    throwErr s!"array: no segment at [{lo.pretty} ; {cnt.pretty}] in {v.pretty} (the place was never carved there)"

/-- The distinctive rejection for peeling a non-borrow, stated once because two
    rules need it and each used to spell all five cases out. A knowledge leaf
    answers for the three shapes it can be (a σ, a constructor tree, anything
    else pure), which is the two-layer principle at its smallest. -/
def notABorrow (v : Val) : String :=
  match v with
  | .bot => "*: cannot peel a vacant slot (⊥)"
  | .loanM ℓ => s!"*: cannot peel loanₘ ℓ{subNat ℓ} (suspended borrow)"
  | v =>
    match v.symOf? with
    | some σ => s!"*: cannot peel symbolic value σ{subNat σ} (not a borrow)"
    | none =>
      match Val.asCtor? v with
      | some (n, _) => s!"*: cannot peel constructor '{n}' (not a borrow)"
      | none => "*: cannot peel a pure value (not a borrow)"

/-- Read through one step. -/
def navStep (fuel : Nat) : Step → Val → M Val
  | .peel, v =>
    match v with
    | .borrowM _ p => pure p
    | v => throwErr (notABorrow v)
  | .rng lo cnt _, v => do pure (← findSeg fuel lo cnt v).2.body
  | .idx i _, v => do
    -- ¶2.1: `a[i]` is NOT `a[i ; 1]`. They carve identically, but the range place's
    -- payload is an `Array 1 T` while the index place's is the ELEMENT itself, of
    -- type `T` — which is what spares every element access a coercion.
    let (_, l) ← findSeg fuel i (Term.nat 1) v
    match Val.asCtor? l.body with
    | some ("Arr", [e]) => pure e
    | _ => throwErr s!"a[i]: the one-slot segment at {i.pretty} holds {l.body.pretty}, not a single-element run"

/-- Write `inner` back through one step, rebuilding the node around it. -/
def setStep (fuel : Nat) : Step → Val → Val → M Val
  | .peel, v, inner =>
    match v with
    | .borrowM ℓ _ => pure (.borrowM ℓ inner)
    | v => throwErr (notABorrow v)
  | .rng lo cnt _, v, inner => do
    let (i, _) ← findSeg fuel lo cnt v
    match v with
    | .node "§segs" segs =>
      pure (Val.segsNode (segs.zipIdx.map (fun (s, j) =>
        if j == i then (match Val.asSeg? s with
                        | some (c, _) => Val.segNode c inner
                        | none => s)
        else s)))
    | _ => pure inner                              -- degenerate: the node IS the request
  | .idx i _, v, inner => do
    let (j, _) ← findSeg fuel i (Term.nat 1) v
    match v with
    | .node "§segs" segs =>
      pure (Val.segsNode (segs.zipIdx.map (fun (s, k) =>
        if k == j then (match Val.asSeg? s with
                        | some (c, _) => Val.segNode c (.ctor "Arr" [inner])
                        | none => s)
        else s)))
    | _ => pure (.ctor "Arr" [inner])

/-- Read the value at a resolved position (peeks; no side effect). -/
def navRead (fuel : Nat) : List Step → Val → M Val
  | [], v => pure v
  | s :: rest, v => do navRead fuel rest (← navStep fuel s v)

/-- Functionally set the value at a path inside `v` to `newLeaf`. -/
def navWrite (fuel : Nat) : List Step → Val → Val → M Val
  | [], _, newLeaf => pure newLeaf
  | s :: rest, v, newLeaf => do
    let inner ← navStep fuel s v
    setStep fuel s v (← navWrite fuel rest inner newLeaf)

/-- Read the value at a resolved position (peeks; no side effect). -/
def getAtPos (fuel : Nat) (pos : Pos) : M Val := do
  navRead fuel pos.path (← lookupSlot pos.root)

/-- Overwrite the value at a resolved position, threading the update back
    through the borrow payloads and segment bodies to the root slot. -/
def setAtPos (fuel : Nat) (pos : Pos) (newLeaf : Val) : M Unit := do
  let v ← lookupSlot pos.root
  setSlot pos.root (← navWrite fuel pos.path v newLeaf)

/-- Resolve a PEEL-ONLY place (`x`, `*x`, `**x`, …). This is ⇜'s place shape: a
    refinement is a substitution and only a variable has a substitutable identity
    (§3.2), so the array steps are rejected here rather than silently carving inside
    a comptime write. The full resolver, which evaluates index terms and carves, is
    `placeToPos` — it cannot be defined until `hasType` is. -/
def placeToPosRaw : Term → M Pos
  | .var x => pure ⟨x, []⟩
  | .deref t => do let p ← placeToPosRaw t; pure ⟨p.root, p.path ++ [.peel]⟩
  | .index _ _ _ =>
    throwErr "place (⇜): an array index place is not a refinement target (§3.2)"
  | .range _ _ _ _ _ _ =>
    throwErr "place (⇜): an array range place is not a refinement target (§3.2)"
  | _ => throwErr "place: target is not a place (must be a variable under * peels)"

/-- Refine `σ := v` **everywhere** — in every Ω slot AND every `sctx` type
    (§3.2's "everywhere", now including the type layer: a snapshot type that
    mentions the refined σ, e.g. `Id Nat σ 2`, is substituted like anything
    else — the seam §10 exercises). The replacement `v` must be marker-free
    (§3.2 knowledge/state): substituting a hole/loan/borrow for a σ would smuggle
    state into entry-knowledge — the etiology of a class of bug where a spec is instantiated at `⊥`. -/
def refineSym (σ : Nat) (v : Val) : M Unit := do
  -- The knowledge/state premise, which is now the SHAPE of the argument rather
  -- than a scan of it: a store value is knowledge exactly when it is a `know`
  -- leaf, so the guard that used to walk the tree for a marker is the match
  -- below, and the rejection it produces is the same sentence.
  let repl ← match v with
    | .know t => pure t
    | _ => throwErr s!"refineSym: σ{subNat σ} := {v.pretty} carries a state marker (⊥/loan/borrow) — knowledge/state violation (§3.2)"
  -- THE HOT ONE (docs/17 §9): this fires during array place evaluation
  -- (`carveAt`/`carveBody`/`elementize`), not only at arm entries, so its
  -- frequency in the flagship is the lane's go/no-go. The delta is the σ and its
  -- replacement — O(1) — never the swept Ω, which would be quadratic.
  notePoint (.refine σ repl)
  modify (fun s => { s with
    env := s.env.map (fun kv => (kv.1, substSym σ repl kv.2)),
    sctx := s.sctx.map (fun p => (p.1, Term.substSym σ repl p.2)),
    -- A dependent call's captured/issued owed types may mention a caller σ (via
    -- an instantiated actual, §5.3); they live in the debt table beside the
    -- parameter obligations, so ONE map reaches all of them — the "refinement
    -- reaches all σ-bearing state" invariant (§3.2). The pin joins the owed
    -- type: both are claims opened at snapshots a refinement may name.
    debts := s.debts.map (fun d => { d with
      owed := Term.substSym σ repl d.owed,
      pin := d.pin.map (Term.substSym σ repl) }),
    retTyVal := s.retTyVal.map (Term.substSym σ repl),
    retTyBorrow := s.retTyBorrow.map (Term.substSym σ repl),
    -- The decreasing parameter's snapshot refines with everything else — this is
    -- how `match fuel { S(f2) => … }` makes the guard's comparison possible.
    })

/-- **Generalize a stuck Bool spine** (§19) — the inverse of `refineSym`, and the
    two-layer principle at the machine level. When a match/`if` scrutinee reduces
    to a stuck spine `leb σ σp` (a neutral, not a bare σ), the ⇜ split cannot fire
    (it needs a substitutable σ). So NF the spine, mint a fresh `σb : Bool`, and
    `abstractInto` it across ALL σ-bearing state — the SAME targets `refineSym`
    reaches (Ω, sctx, debts, retTyVal: the M10 invariant).
    Every occurrence of the spine in values AND types now reads `σb`, so the
    ordinary owned-sym split (`symOwnedSetup`'s `writeC`/`refineSym`) refines the
    spine to `True`/`False` per branch — including inside a declared spec's
    instantiation, which is exactly what the per-path back-spec conversion needs.

    Returns the fresh σb **together with the normalized pre-abstraction spine**.
    Abstraction is precisely what makes the spine unnameable afterwards — nothing
    in the state mentions `leb σ σp` any more, and a body that recomputes it gets
    a term the refinement never touched — so the value returned here is the only
    thing a branch EQUATION can be built from (M23). The caller threads it to the
    branch setup. -/
def generalizeStuck (fuel : Nat) (spine : Term) : M (Nat × Term) := do
  let sp := Pure.nf fuel spine
  let σb ← freshSym
  -- **COOK FIRST, THEN SWEEP** (M32 R2, suspensions.md §3). This is the one
  -- non-commuting sweep in the system and therefore the one event at which
  -- cooking is persistent. `cookForGen` is support-scoped — only closures whose
  -- ρ mentions a σ of `sp` can re-mint `sp` after the sweep has passed — and it
  -- writes the cooked form back, so what `abstractInto` rewrites below is the
  -- cooked body and the raw syntax is gone. Ω only: sctx, debts and retTyVal
  -- hold `Term`s, and a `Term` is not a suspension.
  let support := sp.symIds
  modify (fun s => { s with env := s.env.map (fun kv => (kv.1, cookForGen fuel support kv.2)) })
  modify (fun s => { s with
    env := s.env.map (fun kv => (kv.1, abstractInto sp σb kv.2)),
    sctx := (σb, .const "Bool") :: s.sctx.map (fun p => (p.1, Term.abstractInto sp σb p.2)),
    debts := s.debts.map (fun d => { d with
      owed := Term.abstractInto sp σb d.owed,
      pin := d.pin.map (Term.abstractInto sp σb) }),
    retTyVal := s.retTyVal.map (Term.abstractInto sp σb),
    retTyBorrow := s.retTyBorrow.map (Term.abstractInto sp σb),
    })
  pure (σb, sp)

/-- **Refl-match — the solution transition** (§10). Matching against `Refl` at
    scrutinee type `Id A a b` unifies the endpoints: whnf both; if one is a
    substitutable σ not occurring on the other side, ⇜-refine it to the other,
    everywhere; if already equal, nothing; if BOTH are rigid, the match is
    STUCK — no unification beyond solution (no injectivity/conflict/cycle in the
    kernel; those are the fording library's job via j/k). -/
def reflUnify (fuel : Nat) (a b : Term) : M Unit := do
  let a' := Pure.whnf fuel a
  let b' := Pure.whnf fuel b
  if Pure.convert fuel a' b' then pure ()                         -- endpoints already equal
  else match a'.symOf?, b'.symOf? with
    | some σa, _ =>
      if b'.symIds.contains σa then
        throwErr s!"Refl: occurs check — endpoint σ{subNat σa} occurs in the other endpoint ({b'.pretty})"
      else refineSym σa (.know b')
    | _, some σb =>
      if a'.symIds.contains σb then
        throwErr s!"Refl: occurs check — endpoint σ{subNat σb} occurs in the other endpoint ({a'.pretty})"
      else refineSym σb (.know a')
    | _, _ =>
      throwErr s!"Refl: both endpoints are rigid ({a'.pretty} vs {b'.pretty}) — no solution by refinement; use j/k to eliminate the identity"

/-- **⇜ (comptime write / refinement)** — the doc's ⇜, signature parallel to
    `writeR`. Defined on the same place shapes (a variable under peels). The
    place must currently hold a symbolic value `sym σ`; the effect is global
    refinement `σ := refined` (Ω and sctx). Errors distinctively otherwise. -/
def writeC (place : Term) (refined : Val) : M Unit := do
  let pos ← placeToPosRaw place
  let v ← getAtPos 1000 pos
  match v.symOf? with
  | some σ => refineSym σ refined
  | none => throwErr s!"writeC (⇜): place holds {v.pretty}, expected a symbolic value (sym σ)"

/-! ## ⇝ (comptime read) and value typing (§4)

    `readC` is the ⇝ column: it evaluates a term in the borrow-free fragment.
    Discipline (to be a lemma later): it NEVER writes a slot. Reflection reads
    Ω only for snapshots — a variable reads its slot non-destructively, `*x`
    projects a borrow's payload — and `&mut`, assignment, and consumption
    through a loan are all outside the fragment (errors). Reflected pure terms
    are then normalized by `nfV`. -/

/-! Reflect a comptime term, resolving Ω snapshot reads.

    **It produces a store value, not knowledge, and that is the domain split
    showing where it belongs** (M32 R1). A reflection resolves places — `x`, `*x`,
    `a[i]` — and a place is exactly the thing that may hold state, so a
    half-resolved term is a skeleton with knowledge leaves. `readC` is where the
    demand for knowledge is made, once, after the ⇝ bridge has had its chance to
    fold a carve back into an `arrCat` spine.

    Everything above the places is knowledge by construction, which is what
    `needKnow` asks at each pure former: `Cons(3, *b)` where `*b` is a borrowed
    field reflects to a NODE and is refused at `readC`, exactly where a value
    carrying a marker used to be refused by whatever tried to type it.

    **`let` is read by β, and `eval` performs it** (M32 R1). M29 α carried a
    substitution and M30 step 2 built a redex here; both existed because the
    let-bound VALUE must not be carried under a binder, which is the one move a
    named representation cannot make safely. An environment extension cannot make
    it either — the argument is a value before the inner binder is entered — and
    `eval` has an environment, so the `letIn` rides through as itself and the
    evaluator binds `Pure.letName x.id`. The redex construction is gone. -/

/-- A ⇝ position demands knowledge; a store value that is not a leaf is state. -/
def needKnow (what : String) (v : Val) : M Term :=
  match v with
  | .know t => pure t
  -- **A comptime λ COOKS on demand** (M32 R2, §2.3). A closure is not knowledge —
  -- it is a suspension — but a comptime one has a knowledge reading, and the
  -- demand for it is exactly here. `underRho` hands back the body under its
  -- capture and `readC`'s own `Pure.nf` is what canonicalizes it, so a snapshot
  -- read of a slot holding a λ is the λ's normal form, which is what it was
  -- before R2 made the value raw. An IMPERATIVE closure keeps the rejection
  -- below, and keeps it for the same reason `.rfn` had it: its body is a body.
  | .closure ρ node _ =>
    if Term.lamImperative node then
      throwErr s!"readC (⇝{what}): {v.pretty} is state, not knowledge — a comptime read reaches a hole, a loan marker or a borrow through the place grammar only (§3.2)"
    else pure (Term.underRho (Val.rhoTerms ρ) node)
  | v => throwErr s!"readC (⇝{what}): {v.pretty} is state, not knowledge — a comptime read reaches a hole, a loan marker or a borrow through the place grammar only (§3.2)"

mutual
  def reflectC (lets : List Nat) : Term → M Val
    | .var x => do
      -- A ⇝ `let` binding first: it is the innermost scope there is, and it is
      -- the one Ω knows nothing about. Its occurrences ride through to `eval`,
      -- which resolves them against the environment the `letIn` case extends.
      if lets.contains x.id then pure (.know (.var x)) else
        -- snapshot read (non-destructive) — but §2.1: every read-shaped rule
        -- excludes ⊥. A comptime read of a moved/uninitialized slot is a
        -- use-after-move; rejecting it here stops a silent ⊥ from riding into a
        -- pure value and surfacing layers later as an opaque untypeable ⊥ (the
        -- spec-at-`⊥` etiology: reading the owned-consumed scrutinee).
        match ← lookupSlot x with
        | .bot => throwErr s!"readC (⇝): {x.name}#{x.id} holds ⊥ (use-after-move or uninitialized in a comptime read)"
        | v => pure v
    | .deref t => do
      match ← reflectC lets t with
      | .borrowM _ p => pure p                       -- *(borrowₘ ℓ v) ⇝ v
      | _ => throwErr "readC (⇝ *): dereferenced value is not a borrow"
    | .ctorApp n args => do pure (.ctor n (← reflectCList lets args))
    | .type => pure (.know .type)
    | .const c => pure (.know (.const c))
    | .pvar x => pure (.know (.pvar x))
    -- The mode marker reflects structurally. ⇝ carries it without ever reading
    -- it: conversion is mode-blind, so no comptime judgment can branch on a mode
    -- (§6, "case is inert under ⇝"). It is here so that ⇒ can read it off a
    -- value callee's Π — the one arrow that is entitled to ask.
    | .cmpT τ => do pure (.know (.cmpT (← needKnow " ⇝τ" (← reflectC lets τ))))
    -- The three pure BINDERS, carrying their names across unchanged.
    | .pi x d c => do
      pure (.know (.pi x (← needKnow " Π" (← reflectC lets d)) (← needKnow " Π" (← reflectC lets c))))
    | .sigmaT x d c => do
      pure (.know (.sigmaT x (← needKnow " Σ" (← reflectC lets d)) (← needKnow " Σ" (← reflectC lets c))))
    -- **The λ, both fragments, told apart by its BODY** (M32 R2). ⇝ reflects a
    -- comptime λ structurally, as it always did. An IMPERATIVE λ keeps the exact
    -- refusal `.lamR` had, and the sentence is unchanged because the reason is:
    -- its body is a body, and ⇝ has no rule for a write, a call or a borrow.
    -- (A λ reached HERE is one inside a TYPE — a motive, a spec, an ascription —
    -- which §2.4 says is consumed at its own event, so its citations are inlined.
    -- A λ formed as a VALUE reaches `readR`'s λ arm and becomes a closure, which
    -- is where the raw body and its ρ come from.)
    | .lam x d b => do
      if Term.lamImperative (.lam x d b) then
        throwErr "readC (⇝): a runtime λ (`λ(x : τ, …){ … }`) is not in the comptime fragment — its body is a body (writes, calls, borrows) and its binders are Ω slots. The comptime λ is `λ (x : τ). e` (§1.3)"
      pure (.know (.lam x (← needKnow " λ" (← reflectC lets d)) (← needKnow " λ" (← reflectC lets b))))
    -- §5.4 exit-snapshot marker: `markExit` stamps a bare borrow-param `*v` in a
    -- return type as `@exit(*v)`; here it pins to that borrow's fresh σ_exit (the
    -- audit later defines it as the collapsed final payload). Unmarked bare `*v`
    -- and `old *v` both fall to the plain `.deref` read (the entry snapshot).
    | .app (.const "@exit") (.deref (.var v)) => do
      match (← get).exitSyms.lookup v.id with
      | some σ => pure (.know (Term.sym σ))
      | none => reflectC lets (.deref (.var v))
    -- §5.4 `old *v`: the ENTRY snapshot σ (recorded at seed) — a non-consuming read
    -- of the entry value, in the return type OR the body (where `*v`'s live payload
    -- has since been mutated). Falls back to the live deref outside a borrow-param.
    | .app (.const "old") (.deref (.var v)) => do
      match (← get).entrySyms.lookup v.id with
      | some σ => pure (.know (Term.sym σ))
      | none => reflectC lets (.deref (.var v))
    -- **A CALL HAS NO ⇝ READING, and R4 moved that fact from the node to the
    -- value.** `reflectC` used to refuse `.callV` by name; with one application
    -- node the refusal has to ask what the head HOLDS. A sealed function or an
    -- imperative closure is ENTERED, and entering is an event — its result is a
    -- fresh existential minted once, so a ⇝ reading of the same term would have
    -- to invent one, and two reads would disagree. An ABSTRACT function is
    -- different and still reflects below: `σ a` is the structured neutral, which
    -- is §12 decision 5's ⇝ half and exactly what the old message told the
    -- programmer to write instead.
    | .app f a => do
      let entered ← match Term.appSpineVar? (.app f a) with
        | some (x, _) =>
          if lets.contains x.id then pure false
          else do
            let st ← get
            pure (match findSlot? st.env x with
              | some kv => calleeMustEnter st kv.2
              | none => false)
        | none => pure false
      if entered then
        throwErr "readC (⇝): a call is not in the comptime fragment — its result is a fresh existential, minted at an EVENT, and ⇝ has none. (Comptime application of an ABSTRACT function is the structured neutral `f a` and does reflect; a sealed or imperative callee must be entered, which is ⇒'s.)"
      pure (.know (.app (← needKnow "" (← reflectC lets f)) (← needKnow "" (← reflectC lets a))))
    | .idT a b c => do
      pure (.know (.idT (← needKnow " Id" (← reflectC lets a)) (← needKnow " Id" (← reflectC lets b))
        (← needKnow " Id" (← reflectC lets c))))
    | .unit => pure (.ctor "unit" [])
    | .letIn x rhs rest => do
      -- Nothing is written to Ω, so a comptime read has no footprint and two
      -- reads cannot disagree.
      let v ← needKnow " let" (← reflectC lets rhs)
      pure (.know (.letIn x v (← needKnow " let" (← reflectC (x.id :: lets) rest))))
    -- ¶2.2's ⇝ column at the two new steps. The snapshot of an array place is the
    -- snapshot of the SEGMENT sitting there — exact, and needing no new constant.
    -- Read-only, as ⇝ must be: it merges a local copy to find the segment but never
    -- carves, so a place the program has not carved is honestly stuck here rather
    -- than silently reorganized inside a type.
    | .index t i _ => do
      let a := Val.mergeArrays (← reflectC lets t)
      navStep 1000 (.idx (Pure.nf 1000 (← needKnow " a[i]" (← reflectC lets i))) none) a
    | .range t lo (some cnt) _ _ _ => do
      let a := Val.mergeArrays (← reflectC lets t)
      navStep 1000 (.rng (Pure.nf 1000 (← needKnow " a[lo ; cnt]" (← reflectC lets lo)))
        (Pure.nf 1000 (← needKnow " a[lo ; cnt]" (← reflectC lets cnt))) none) a
    | .range _ _ none _ _ _ =>
      -- `a[lo ; ..]` reads its count off the extent map, which is STATE; ⇝ is the
      -- read-only projection and may not consult it. Write the count in a type.
      throwErr "readC (⇝): `a[lo ; ..]` has no comptime reading — its count is read off the extent map, which is state (§3.2)"
    | .assign _ _ _ => throwErr "readC (⇝): `:=` is excluded from the comptime fragment"
    | .borrow _ => throwErr "readC (⇝): `&mut` is not in the comptime fragment"
    | .seq _ _ => throwErr "readC (⇝): statement sequencing is not a comptime read"
    | .matchE _ _ _ => throwErr "readC (⇝): match not implemented in the comptime fragment this milestone"
    | .borrowT _ _ _ => throwErr "readC (⇝): borrow type `&mut (τ ↝ τ')` is only valid at a telescope position"
    -- **The callee is NAMED** (M31 Stage A), and it is load-bearing rather than
    -- cosmetic: `fn`'s statement lowering turns a refusal into an unbound `.call`
    -- whose NAME carries the diagnosis, and this arm is what reports it.
    | .call f _ => throwErr s!"readC (⇝): a call is not in the comptime fragment (its result is a fresh existential) — '{f}'"
    -- The seal is a ⇒-form and only a ⇒-form (combining-fns §5). Minting needs an
    -- EVENT; ⇝ is a pure judgment with none, so a seal reduced twice under ⇝ would
    -- disagree with itself.
    -- **Still refused HERE, and R3 did not weaken it** (M32 R3). What became
    -- ⇝-evaluable is the seal at a BINDING (`readComptimeVal`), where the σ its
    -- site names is a value a slot can hold. `reflectC` is the read-only
    -- projection INTO A TYPE, and a type is consumed at its own event (§2.4) —
    -- there is no binding for a seal inside one to be the seal of, and a σ
    -- appearing in a type by being written there is generalization in a position
    -- that cannot mean it. The sentence is unchanged for the case it still
    -- covers.
    | .seal _ _ _ => throwErr "readC (⇝): `seal` is not in the comptime fragment — a seal inside a TYPE has no reading, because a type is consumed at its own event and there is no binding for the sealed σ to land in. A seal is read at a `let` (§2.4)"
  def reflectCList (lets : List Nat) : List Term → M (List Val)
    | [] => pure []
    | t :: ts => do pure ((← reflectC lets t) :: (← reflectCList lets ts))
end

/-- ⇝: reflect, FOLD, demand knowledge, then normalize. Ω is read-only throughout.

    The fold is ¶1.3's bridge, and putting it here rather than at the audit is the
    doc's own preference ("the latter is cleaner, since merge is then part of what
    *the snapshot of an array* means rather than a step the audit remembers to
    take"). A collapsed segment list becomes its `arrCat` spine — knowledge, never
    mentioning a marker — and `arrCat`'s ι then computes it back to a run when the
    bodies are runs, so a carved-and-rejoined array has the SAME snapshot as one
    that was never carved. A still-suspended one is state, and is refused here. -/
def readC (fuel : Nat) (t : Term) : M Term := do
  pure (Pure.nf fuel (← needKnow "" (Val.arrFoldDeep (← reflectC [] t))))

/-- ⇝ against extra bindings prepended to Ω — how a dependent call instantiates a
    callee telescope type (§5.3): the decl's parameter vars are bound to the
    caller's actuals in `extra`, so a `.var`-reference to an earlier parameter
    (the §5.2 convention) reflects to the value passed for it.

    **The instantiation is APPENDED, and this is the one site where re-keying is
    not a local rewrite** (M32 R1). Under id keying `extra` had to go in FRONT,
    because `find?` takes the first match and the decl's parameter ids (`0 … k`)
    collide with the caller's own locals — prepending was how the actuals won.
    Under rightmost-wins name keying, front is the OLDEST position, so prepending
    would make the CALLER's binding of a parameter's name win: the parameter type
    would be read at the caller's value instead of the actual. Appending restores
    the intended shadowing, and the id collision that forced the original order is
    void.

    Env is restored afterward (the reflection's let-footprint is discarded). -/
def readCWith (fuel : Nat) (extra : Omega) (t : Term) : M Term := do
  let saved := (← get).env
  modify (fun s => { s with env := s.env ++ extra })
  let v ← readC fuel t
  modify (fun s => { s with env := saved })
  pure v

-- §5.4 exit-snapshot transform on a RETURN TYPE (moved here from Boundary so the
-- call rule can reach it too). A bare borrow-parameter `*v` (`v.id ∈ borrowIds`) is
-- stamped `@exit(*v)` — it pins to that borrow's σ_exit; `old *v` is left intact
-- (reflectC resolves it to the entry σ). Non-borrow derefs untouched. Types only.
mutual
  def markExit (borrowIds : List Nat) : Term → Term
    | .deref (.var v) =>
      if borrowIds.contains v.id then .app (.const "@exit") (.deref (.var v)) else .deref (.var v)
    | .deref t => .deref (markExit borrowIds t)
    | .app (.const "old") (.deref (.var v)) => .app (.const "old") (.deref (.var v))
    | .app f a => .app (markExit borrowIds f) (markExit borrowIds a)
    | .ctorApp n args => .ctorApp n (markExitList borrowIds args)
    | .pi x d c => .pi x (markExit borrowIds d) (markExit borrowIds c)
    | .sigmaT x d c => .sigmaT x (markExit borrowIds d) (markExit borrowIds c)
    | .lam x d b => .lam x (markExit borrowIds d) (markExit borrowIds b)
    | .idT a b c => .idT (markExit borrowIds a) (markExit borrowIds b) (markExit borrowIds c)
    -- **The mode marker is TRANSPARENT to this walk** (M33a), and its absence was
    -- a silent skip rather than a refusal. Since R3b a Σ/Π/λ domain may be `⇝τ`,
    -- and the fallthrough below treats an unrecognised former as a leaf — so a
    -- comptime Σ component's type kept its `*v` UNMARKED and read the ENTRY
    -- payload where every other component read the exit. Measured on `splitOff`:
    -- capitalising one Σ binder made the audit demand `Id σ0 Nil` of a branch
    -- that returns `Refl` at `Id Nil Nil`.
    | .cmpT τ => .cmpT (markExit borrowIds τ)
    | t => t
  termination_by t => sizeOf t
  def markExitList (borrowIds : List Nat) : List Term → List Term
    | [] => []
    | t :: ts => markExit borrowIds t :: markExitList borrowIds ts
  termination_by ts => sizeOf ts
end

-- **`@res k` — a pin's name for the k-th issued borrow's exit payload**
-- (12-design §2.5/D3(a)). The surface's `*res` lowers to `@res 0`; the marker is
-- a neutral const spine, so it rides through nf/convert/readC untouched and is
-- substituted only here, by the two discharge sites:
-- the audit opens a pin at FRESH exit σ's, the group end at the ACTUAL
-- surrendered payloads. Same substitution, two instantiations — §2.3's "one
-- rule" requirement, made literal.
partial def substResIdx (exits : List Term) : Term → Term
  | .app (.const "@res") idx =>
    match Term.natOf? idx with
    | some k => (exits[k]?).getD (.app (.const "@res") idx)
    | none => .app (.const "@res") idx
  | .deref t => .deref (substResIdx exits t)
  | .app f a => .app (substResIdx exits f) (substResIdx exits a)
  | .ctorApp n args => .ctorApp n (args.map (substResIdx exits))
  | .pi x d c => .pi x (substResIdx exits d) (substResIdx exits c)
  | .sigmaT x d c => .sigmaT x (substResIdx exits d) (substResIdx exits c)
  | .lam x d b => .lam x (substResIdx exits d) (substResIdx exits b)
  | .idT a b c => .idT (substResIdx exits a) (substResIdx exits b) (substResIdx exits c)
  | .borrowT n τ S => .borrowT n (substResIdx exits τ) (substResIdx exits S)
  | .cmpT τ => .cmpT (substResIdx exits τ)
  | .index t i ev => .index (substResIdx exits t) (substResIdx exits i) (ev.map (substResIdx exits))
  | .range t lo cnt rest ev eq =>
    .range (substResIdx exits t) (substResIdx exits lo) (cnt.map (substResIdx exits))
      (rest.map (substResIdx exits)) (ev.map (substResIdx exits)) (eq.map (substResIdx exits))
  | t => t

/-- `old *v ↦ sym σ_entry` (D9, M35): resolve the entry-snapshot form at SEED
    time, where the entry σ is what `old` means and the refinement sweep is
    still ahead of it. Used to pin a borrow-carrying return type raw
    (`St.retTyBorrow`) — the reflectC route the value-return path takes cannot
    run on a `borrowT`-carrying term. -/
partial def resolveOldEntry (entries : List (Nat × Nat)) : Term → Term
  | .app (.const "old") (.deref (.var v)) =>
    (match entries.lookup v.id with
     | some σ => Term.sym σ
     | none => .app (.const "old") (.deref (.var v)))
  | .deref t => .deref (resolveOldEntry entries t)
  | .app f a => .app (resolveOldEntry entries f) (resolveOldEntry entries a)
  | .ctorApp n args => .ctorApp n (args.map (resolveOldEntry entries))
  | .pi x d c => .pi x (resolveOldEntry entries d) (resolveOldEntry entries c)
  | .sigmaT x d c => .sigmaT x (resolveOldEntry entries d) (resolveOldEntry entries c)
  | .lam x d b => .lam x (resolveOldEntry entries d) (resolveOldEntry entries b)
  | .idT a b c => .idT (resolveOldEntry entries a) (resolveOldEntry entries b) (resolveOldEntry entries c)
  | .borrowT n τ S => .borrowT n (resolveOldEntry entries τ) (resolveOldEntry entries S)
  | .cmpT τ => .cmpT (resolveOldEntry entries τ)
  | .index t i ev => .index (resolveOldEntry entries t) (resolveOldEntry entries i) (ev.map (resolveOldEntry entries))
  | .range t lo cnt rest ev eq =>
    .range (resolveOldEntry entries t) (resolveOldEntry entries lo) (cnt.map (resolveOldEntry entries))
      (rest.map (resolveOldEntry entries)) (ev.map (resolveOldEntry entries)) (eq.map (resolveOldEntry entries))
  | t => t

/-- `*x ↦ x`, for a named Σ binder `x` standing for a BORROW component (D9,
    M35). What a later component sees of an earlier one is its KNOWLEDGE, and
    the knowledge of a borrow is its payload — so by the time the tail is
    opened, the deref is already taken, and leaving it would wrap the payload
    term in a `.deref` nothing reads. Only the exact `.deref (.pvar x)` shape
    collapses; a shadowing binder of the same name stops the walk. -/
partial def collapseDerefOf (x : String) : Term → Term
  | .deref (.pvar y) => if y == x then .pvar y else .deref (.pvar y)
  | .deref t => .deref (collapseDerefOf x t)
  | .app f a => .app (collapseDerefOf x f) (collapseDerefOf x a)
  | .ctorApp n args => .ctorApp n (args.map (collapseDerefOf x))
  | .pi y d c => .pi y (collapseDerefOf x d) (if y == x then c else collapseDerefOf x c)
  | .sigmaT y d c => .sigmaT y (collapseDerefOf x d) (if y == x then c else collapseDerefOf x c)
  | .lam y d b => .lam y (collapseDerefOf x d) (if y.name == x then b else collapseDerefOf x b)
  | .idT a b c => .idT (collapseDerefOf x a) (collapseDerefOf x b) (collapseDerefOf x c)
  | .borrowT n τ S => .borrowT n (collapseDerefOf x τ) (if n == x then S else collapseDerefOf x S)
  | .cmpT τ => .cmpT (collapseDerefOf x τ)
  | .index t i ev => .index (collapseDerefOf x t) (collapseDerefOf x i) (ev.map (collapseDerefOf x))
  | .range t lo cnt rest ev eq =>
    .range (collapseDerefOf x t) (collapseDerefOf x lo) (cnt.map (collapseDerefOf x))
      (rest.map (collapseDerefOf x)) (ev.map (collapseDerefOf x)) (eq.map (collapseDerefOf x))
  | t => t

-- (`isOwedTypeT` — D1's one-slot kind classification — lives BELOW the value-
-- typing mutual now: since the universe rule it IS the semantic judgment
-- `hasTypeT · Type`, sandboxed, and `buildResult` moved with it as its one
-- pre-mutual caller.)

/-- The telescope's borrow-parameter var ids (param `i` gets var id `i`). -/
def borrowParamIds (telescope : List (String × Term)) : List Nat :=
  telescope.zipIdx.filterMap (fun (p, i) => match p.2 with | .borrowT _ _ _ => some i | _ => none)

/-- What a value contributes to a dependent tail's context: its knowledge. A
    borrow node surrenders its payload; anything else is already a leaf.

    Stated on the FOLDED value (`subsKnowledge` below) — see there. -/
def subsKnowledgeRaw : Val → Term
  | .know t => t
  | .borrowM _ p => subsKnowledgeRaw p
  -- **A closure COOKS here** (M32 R2), and this is the seam R1 named and
  -- predicted the third case of: a closure `(ρ, body)` is a value and not a
  -- `Term`, so the only way to hand one to a type — a dependent field, a Π
  -- codomain being instantiated, a Σ tail — is to evaluate it. That is a
  -- TRANSIENT cook (§2.3): the closure at rest is untouched, and what the type
  -- receives is the body under its capture, which the `Pure.nf` every one of
  -- these call sites already applies then normalizes.
  | .closure ρ node _ => Term.underRho (Val.rhoTerms ρ) node
  -- A component that is neither: a node holding state — a hole, a live loan, or a
  -- carve the fold could not close. It contributes a name that converts with
  -- nothing, so a type that reached for it is rejected rather than silently typed
  -- against a marker.
  | _ => .const "@stateComponent"
  termination_by v => sizeOf v

/-- What a value contributes to a dependent tail's context: its knowledge. A
    borrow node surrenders its payload, a closure cooks, anything else is already
    a leaf.

    **A REJOINED CARVE contributes its `arrCat` spine**, and that is the whole of
    `docs/14-packed-borrows.md`'s Gap A. A `§segs` node is STATE and stays state in
    the store — `Val.ctor` refuses to collapse one (M32 R1) so that the borrow
    machinery can see a carve — but a type asking what a component IS is asking a
    knowledge question, and ¶1.3's ⇝ bridge is the one route from a carve to
    knowledge. So the fold happens HERE, on the way into a type, and nothing is
    written back: the carve in Ω is untouched and the live borrows stay live.

    Without it, a `&mut (Σ0 (a : Array n T). P a)` whose array was carved three
    ways and every borrow returned could not be re-typed at its exit audit — the
    dependent tail was demanded at `P @stateComponent` while the entry clause
    inhabited `P σ_entry`, even though the two arrays are definitionally equal (the
    carve's own `refineSym` made them so). `Tests.AuditFold` is that program.

    `arrFoldDeep` is TOTAL and folds only what it can: a segment list with a hole,
    a live loan or an unfoldable body stays the state form it is and still lands on
    `@stateComponent`. So this widens what can be typed by exactly the rejoined
    case and leaves the suspended one refused, which is the scope the doc's Gap A
    draws. `readC` already folds at its own comptime reading, so the two sites
    agree rather than this being a new licence.

    The `.know` arm is a FAST PATH, and it is equal by construction rather than by
    argument: `arrFoldDeep` bottoms out at `| v => v` on a knowledge leaf, so
    folding one is the identity. It earns its line because `checkFields` calls this
    once per dependent field and almost every field is a leaf. Measured, `Measure.lean`
    §4 at x50 — main 166 ms / 385 ms, fold without this arm 171 ms / 398 ms (+3%),
    fold with it 166 ms / 385 ms. The traversal is free where there is nothing to
    traverse, and this is what makes it so. -/
def subsKnowledge : Val → Term
  | .know t => t
  | v => subsKnowledgeRaw (Val.arrFoldDeep v)

/-! ## §8's snapshot-subterm guard — what makes a self-call admissible

    A call is checked against a signature alone (§5.3), so a self-call is admitted
    at the function's own declared return type. With declared backs removed that
    return type IS the postcondition, and admitting it unconditionally is the Hoare
    rule for recursion without its side condition — every false statement proves
    itself (`fn bad () -> Id Nat Z (S Z) { bad() }`). The side condition is
    structural decrease, and the checker being a symbolic interpreter makes it
    cheap to state: compare the actual against the parameter's *current snapshot*,
    which the enclosing matches have already refined. -/

/-- The function names a body calls directly. -/
partial def calleeNames : Term → List String
  | .call f args => f :: (args.flatMap calleeNames)
  -- A seal's body is ordinary runtime code and may call; a value-callee call
  -- names no DECLARATION (that is the point of it), but its arguments may.
  | .seal _ t u => calleeNames t ++ calleeNames u
  | .letIn _ a b => calleeNames a ++ calleeNames b
  | .assign a b c => calleeNames a ++ calleeNames b ++ calleeNames c
  | .seq a b => calleeNames a ++ calleeNames b
  | .ctorApp _ args => args.flatMap calleeNames
  | .borrow t | .deref t => calleeNames t
  | .matchE _ _ bs => bs.flatMap (fun b => calleeNames b.body)
  | .app f a => calleeNames f ++ calleeNames a
  -- The one λ covers what `.lamR` used to need its own line for: an imperative
  -- body is ordinary runtime code and may call declared functions, so the
  -- reachability check must see through it or a recursion routed through an arm
  -- would be invisible to it.
  | .lam _ d b | .pi _ d b | .sigmaT _ d b => calleeNames d ++ calleeNames b
  | .idT a b c => calleeNames a ++ calleeNames b ++ calleeNames c
  | .cmpT τ => calleeNames τ                             -- M33a: ⇝ is transparent here
  | _ => []

/-- **The premise every formation arm of `hasTypeT` shares** (M35, the universe
    rule): the expected type IS the universe, and the candidate carries no
    borrow.

    Stated once, used at each arm, for two reasons that pull the same way.

    The FIRST is the ordering it forces: the expected type is settled before any
    parameter is visited, so `List Nat : Nat` is a clean `false` and never a
    recursion into an argument nobody asked about.

    The SECOND is `docs/12-design-borrow-refounding.md` §4.2's proof-fragment
    exclusion — "a `borrowT` may not occur inside an `Id`, inside a `Σ` a proof
    inhabits, or anywhere `Pure.nf` output is consumed as a proof term" — written
    for the first time as a rule of the universe rather than as a gate at a call
    site. The doc assigns `hasBorrowT` exactly this job; this is the assignment.

    Why the exclusion cannot be left to the recursion: `hasTypeT` REFUSES a bare
    `⇝τ` or `&mut (s : τ ↝ τ′)` with an error, because asking whether a binder
    mode is a type is a category error and deserves a sentence. But a former
    that merely CONTAINS one — `Π (v : &mut τ) → …`, `Π (x : Nat) → &mut Nat`,
    `List (&mut T)` — is a well-formed thing (a function signature; a runtime-only
    list) that simply does not inhabit `Type`. It owes a verdict, not an error.
    Without this premise the recursion would walk into the marker arm and throw
    one. -/
def atUniverse (fuel : Nat) (ty v : Term) : Bool :=
  Pure.convert fuel ty .type && !hasBorrowT v

/-! Value typing (§4), the future audit's engine. `sym σ` is typed by `sctx`
    and conversion; a constructor value by the signature table, checking each
    field against its (dependently instantiated) type; a type former inhabits
    the universe. Cases no test forces error distinctively (M5 grows them). -/
mutual
  /-- **Value typing of a STORE value** (§4) — the skeleton half. Two lines of it
      decide anything; the rest routes. A knowledge leaf is judged by `hasTypeT`
      below; a node is either the array layer's carved form or a constructor whose
      fields are store values; a marker is not a value of any type and says so. -/
  def hasType : Nat → Val → Term → M Bool
    | 0, _, _ => throwErr "hasType: out of fuel"
    | fuel + 1, v, ty => do
      -- `⇝τ` is a binder MODE, not a type (§6): a value inhabits it exactly when
      -- it inhabits `τ`. Stripped once here rather than at each of the rules that
      -- consult a binder's domain, so no path can accidentally ask `Z : ⇝Nat` and
      -- get `false` for the wrong reason.
      let ty := Term.stripCmp ty
      match v with
      | .know t => hasTypeT fuel t ty
      -- ¶1.1's carved array node, and ruling 2's **extent-consistency invariant**,
      -- machine-asserted here: the segments' extents must sum to the array's own
      -- length index, and each body must hold its own extent's worth. This is the
      -- guard on the representation's one redundancy (extents are carried in the
      -- tree AND implied by the type), and it is exactly the conversion that
      -- premise (3)'s residue transition arranges to be definitional.
      | .node "§segs" segs =>
        match Pure.asArrayTy? (Pure.whnf fuel ty) with
        | none => pure false
        | some (n, t) => do
          let leaves ← extentMap fuel (.node "§segs" segs)
          if !(Pure.convert fuel (sumExtents leaves) n) then pure false
          else leaves.allM (fun l => do
            if !Val.segOwned l.body then
              throwErr s!"hasType: array segment at [{l.base.pretty} ; {l.count.pretty}) holds {l.body.pretty} — a suspended array has no value of its type (§5.2)"
            else hasType fuel l.body ty{ Array %(l.count) %t })
      -- A recursor spine over RUNTIME arms is a neutral the checker cannot type:
      -- its arms are BODIES, so there is nothing to synthesize from. Same
      -- rejection the `.app` case gives a neutral it does not recognise, and
      -- deliberately so — before R1 this value WAS an `.app` spine and took that
      -- path, and the skeleton is a representation change, not a rule change.
      | .node "§rec" _ => throwErr s!"hasType: cannot type neutral {v.pretty}"
      | .node name args =>
        match Pure.ctorSig name with
        | none => throwErr s!"hasType: unknown constructor '{name}'"
        | some sig =>
          match sig.fieldTypes (Pure.whnf fuel ty) with
          | none => pure false                       -- constructor does not inhabit this type
          | some ftys => checkFields fuel args ftys
      -- **A closure is typed by COOKING it, transiently** (M32 R2, §2.3) — and
      -- only when there is a judgment to reach. The two exclusions are the two
      -- halves of R1's §rec checklist arriving at the λ:
      --
      --   * an IMPERATIVE closure has no value the pure fragment could type (its
      --     body is a body), so it is a neutral here and says so in the sentence
      --     the `.app` case gives one. What checks such a λ is §5.4's audit,
      --     reached through the seal, and never this;
      --   * a BORROW-MODED Π is not a type a value inhabits — it is a function
      --     SIGNATURE, and `fsig` is where one lives (`callDeclC` reads it). It
      --     cannot be `readC`'d at all (`borrowT` is telescope-position), so the
      --     question is unaskable rather than merely unanswered.
      --
      -- What is left is a comptime λ against a borrow-free Π, which is exactly
      -- the judgment `hasTypeT`'s own λ case makes.
      | .closure ρ node _ =>
        if Term.lamImperative node || hasBorrowT ty then
          throwErr s!"hasType: cannot type neutral {v.pretty}"
        else hasTypeT fuel (cookClosure fuel ρ node) ty
      | _ => throwErr s!"hasType: cannot type value {v.pretty} (λ/neutral typing deferred to M5)"
  termination_by fuel _ _ => (fuel, 0, 0)
  /-- **Value typing of KNOWLEDGE** — the judgment §4 was always about, now stated
      on the one representation knowledge has. `sym σ` is typed by `sctx` and
      conversion; a constructor value by the signature table, checking each field
      against its (dependently instantiated) type; a type former inhabits the
      universe. Cases no test forces error distinctively (M5 grows them). -/
  def hasTypeT : Nat → Term → Term → M Bool
    | 0, _, _ => throwErr "hasType: out of fuel"
    | fuel + 1, v, ty => do
      let ty := Term.stripCmp ty
      -- Whnf the value first: a β-redex or stuck recursor (e.g. `eqb m a`,
      -- a λ-headed spine) must reduce to its weak head before we can type it.
      let v := Pure.whnf fuel v
      match v.symOf? with
      | some σ =>
        match (← get).sctx.lookup σ with
        | some vty => pure (Pure.convert fuel vty ty)
        | none => throwErr s!"hasType: σ{subNat σ} has no type in sctx"
      | none =>
      match v with
      -- A carved array node that collapsed into knowledge cannot occur — the
      -- skeleton's smart constructor refuses to collapse a `§segs` — so this
      -- judgment never meets one, and the state form above is the only reading.
      | .ctorApp name args =>
        match Pure.ctorSig name with
        | none => throwErr s!"hasType: unknown constructor '{name}'"
        | some sig =>
          match sig.fieldTypes (Pure.whnf fuel ty) with
          | none => pure false                       -- constructor does not inhabit this type
          | some ftys => checkFields fuel (args.map Val.know) ftys
      -- **`Type : Type`, a DELIBERATE inconsistency** (M35, the universe rule).
      -- In a full theory this is Girard's paradox and the logic is unsound as a
      -- logic. It is accepted here because the repo's standing policy is
      -- consistency-DEFERRED-for-soundness (`docs/what-is-ochre.md`; the Ochre
      -- logic goal): the property under construction is that a checked program
      -- does what its types say at RUN time, and a universe hierarchy buys
      -- nothing for that while costing every type former a level argument. The
      -- arm predates M35 — what M35 adds is that the formation rules below now
      -- DEPEND on it (`Σ (T : Type). T` is a type only if `Type` is one), so
      -- what used to be a harmless leaf is now load-bearing and is flagged
      -- accordingly rather than left to be discovered.
      | .type => pure (atUniverse fuel ty v)           -- Type : Type (type-in-type)
      -- **The base type constants** (M35). `Nat`, `Bool`, `Unit`, `Bot` are the
      -- ground types of the fixed basis, and the predicate is DERIVED from
      -- `Pure.typeCtors` rather than written as a second list: a constant is a
      -- ground type exactly when the exhaustiveness table knows its constructor
      -- set (`Bot`'s is empty, which is why `.isSome` and not `≠ []`).
      --
      -- Every other `.const` — the eliminators (`natRec`, `j`, …), `@exit`,
      -- `old` — is not a type and falls to the deferral below, unapplied.
      | .const c =>
        if (Pure.typeCtors (.const c)).isSome then pure (atUniverse fuel ty v)
        else throwErr s!"hasType: cannot type value {v.pretty} (λ/neutral typing deferred to M5)"
      -- **The two binder-mode markers are REFUSED at `Type`, by an arm and not by
      -- a fall-through** (M35). `⇝τ` and `&mut (s : τ ↝ τ′)` are written in type
      -- position but are not types — they say how a BINDER takes its argument
      -- (comptime snapshot; runtime borrow), which is the house doctrine stated
      -- at both of their definitions in `Syntax.lean`. Two things depend on the
      -- refusal being explicit: a `Π` whose domain is `&mut …` is a function
      -- SIGNATURE, which `hasType` already refuses to admit a value at, and
      -- `docs/12-design-borrow-refounding.md`'s proof-fragment exclusion is
      -- exactly "no `borrowT` inhabits the universe". A fall-through would give
      -- the same verdict today and lose the reason tomorrow.
      --
      -- These two arms answer the DIRECT question — "is this marker a type?" —
      -- which is a category error and gets a sentence. A former that merely
      -- CONTAINS a marker is a different question and gets a verdict; that is
      -- `atUniverse`'s second conjunct, above the mutual block.
      | .cmpT _ =>
        throwErr s!"hasType: {v.pretty} is a binder MODE, not a type — ⇝ marks a comptime binder (§6) and does not inhabit Type"
      | .borrowT _ _ _ =>
        throwErr s!"hasType: {v.pretty} is a binder MODE, not a type — &mut marks a runtime borrow binder (§5.1) and does not inhabit Type"
      -- **The binder formers, checked RECURSIVELY** (M35). These three arms
      -- existed before — as three unconditional `pure (convert ty .type)`, i.e.
      -- "any `Π` whatsoever is a type" — and that was sound only because nothing
      -- could reach them: with no rule for `Nat : Type` there was no `Type`-typed
      -- position for a former to sit in. The arms above create those positions,
      -- so the formers now have to earn the universe rather than assert it.
      --
      -- The binder is opened at a FRESH σ carrying the domain, exactly as the λ
      -- arm below opens a body — a checking-time hypothesis, which is what lets
      -- `Π (T : Type) → Π (X : T) → A` type its own second domain (`T` is a σ
      -- whose sctx type is `Type`) and `Π (n : Nat) → Array n (List Nat)` type
      -- its codomain's length index.
      --
      -- The domain STRIPS its mode marker before it is typed: `⇝τ` is a legal
      -- binder mode, so a Π carrying one is an ordinary type, and it is the
      -- underlying `τ` that has to be one.
      | .pi x d c =>
        if !(atUniverse fuel ty v) then pure false
        else do
          let dom := d.stripCmp
          if !(← hasTypeT fuel dom .type) then pure false
          else do
            let σ ← freshSym
            modify (fun st => { st with sctx := (σ, dom) :: st.sctx })
            hasTypeT fuel (Pure.openBinder fuel x c (Term.sym σ)) .type
      -- Σ's TAIL carries a mode marker of its own — `Σ0 (x : A). P` is the
      -- comptime-second-component spelling (M33, suspensions.md §2.7) — so the
      -- codomain strips too, where a Π's never does.
      | .sigmaT x d c =>
        if !(atUniverse fuel ty v) then pure false
        else do
          let dom := d.stripCmp
          if !(← hasTypeT fuel dom .type) then pure false
          else do
            let σ ← freshSym
            modify (fun st => { st with sctx := (σ, dom) :: st.sctx })
            hasTypeT fuel (Pure.openBinder fuel x c.stripCmp (Term.sym σ)) .type
      -- `Id A a b : Type` iff `A : Type` and both endpoints inhabit `A`. The
      -- endpoint premises are what make the identity type's own formation say
      -- what `Refl`'s `ctorSig` entry already assumes when it converts them.
      | .idT a l r =>
        if !(atUniverse fuel ty v) then pure false
        else if !(← hasTypeT fuel a .type) then pure false
        else do
          let lOk ← hasTypeT fuel l a
          let rOk ← hasTypeT fuel r a
          pure (lOk && rOk)
      | .app _ _ =>
        -- A neutral spine. We synthesize a type only for the eliminator
        -- constants (§10 elaboration of `match` to eliminators): their result
        -- type is the motive applied to the target(s), and their premises are
        -- checked recursively. This is what lets the *library* fording terms
        -- (`natNoConf` via `j`, `botElim` on a derived ⊥) type-check as ordinary
        -- terms — no new machine rule, just the eliminators' typing.
        let (head, args) := Pure.collectSpineT v
        -- An eliminator may be OVER-applied (its result is a function further
        -- applied — `natRec … n` returning `P n = A → B`, then given the `A`):
        -- type the fixed part to its base result, then `synthSpine` the extras.
        let finish (baseTy : Term) (rest : List Term) (premises : Bool) : M Bool := do
          match ← synthSpine fuel baseTy rest with
          | some resTy => pure (Pure.convert fuel ty resTy && premises)
          | none => pure false
        match head, args with
        -- **The two parameterised type formers** (M35), read before the
        -- eliminators because a spine headed by `List`/`Array` is a TYPE and not
        -- an elimination. Both are checked, not synthesized, against the shared
        -- `atUniverse` premise — which is what settles `List Nat : Nat` as a
        -- `false` before any parameter is visited, and what keeps
        -- `List (&mut T)` (a runtime-only value, 12- §4.2) out of the universe.
        --
        -- Arity is exact. `List` alone is `Type → Type` and `Array n` is
        -- `Type → Type`; neither inhabits `Type`, and a partially applied one
        -- therefore falls past these arms to the neutral reading below, which
        -- says so.
        | .const "List", [a] =>
          if !(atUniverse fuel ty v) then pure false
          else hasTypeT fuel a .type
        | .const "Array", [n, t] =>
          if !(atUniverse fuel ty v) then pure false
          else do
            let nOk ← hasTypeT fuel n (.const "Nat")
            let tOk ← hasTypeT fuel t .type
            pure (nOk && tOk)
        | .const "botElim", t :: x :: rest =>            -- botElim T x : T   (x : ⊥)
          let xOk ← hasTypeT fuel x (.const "Bot")
          finish t rest xOk
        | .const "j", a :: aa :: p :: d :: b :: pf :: rest =>   -- j A a P d b p : P b p
          let dOk ← hasTypeT fuel d (Pure.nf fuel (.app (.app p aa) (.ctorApp "Refl" [])))
          let pOk ← hasTypeT fuel pf (.idT a aa b)
          finish (Pure.nf fuel (.app (.app p b) pf)) rest (dOk && pOk)
        | .const "k", a :: aa :: p :: d :: pf :: rest =>        -- k A a P d p : P p
          let dOk ← hasTypeT fuel d (Pure.nf fuel (.app p (.ctorApp "Refl" [])))
          let pOk ← hasTypeT fuel pf (.idT a aa aa)
          finish (Pure.nf fuel (.app p pf)) rest (dOk && pOk)
        | .const "natRec", p :: z :: s :: n :: rest =>   -- natRec P z s n : P n
          let zOk ← hasTypeT fuel z (Pure.nf fuel (.app p (.ctorApp "Z" [])))
          let sTy : Term :=
            .pi "§k" (.const "Nat")
              (.pi "§ih" (.app p (.pvar "§k")) (.app p (.ctorApp "S" [.pvar "§k"])))
          let sOk ← hasTypeT fuel s sTy
          let nOk ← hasTypeT fuel n (.const "Nat")
          finish (Pure.nf fuel (.app p n)) rest (zOk && sOk && nOk)
        | .const "boolRec", p :: t :: f :: b :: rest =>  -- boolRec P t f b : P b
          let tOk ← hasTypeT fuel t (Pure.nf fuel (.app p (.ctorApp "True" [])))
          let fOk ← hasTypeT fuel f (Pure.nf fuel (.app p (.ctorApp "False" [])))
          let bOk ← hasTypeT fuel b (.const "Bool")
          finish (Pure.nf fuel (.app p b)) rest (tOk && fOk && bOk)
        | .const "listRec", a :: p :: pn :: pc :: l :: rest =>  -- listRec A P pn pc l : P l
          let listA : Term := ty{ List %a }
          let pnOk ← hasTypeT fuel pn (Pure.nf fuel (.app p (.ctorApp "Nil" [])))
          let pcTy : Term :=
            .pi "§h" a
              (.pi "§t" listA
                (.pi "§ih" (.app p (.pvar "§t"))
                  (.app p (.ctorApp "Cons" [.pvar "§h", .pvar "§t"]))))
          let pcOk ← hasTypeT fuel pc pcTy
          let lOk ← hasTypeT fuel l listA
          finish (Pure.nf fuel (.app p l)) rest (pnOk && pcOk && lOk)
        | .const "sigmaRec", a :: b :: p :: f :: s :: rest =>  -- sigmaRec A B P f s : P s
          -- Σ's parameters are a type `A` and a FAMILY `B : A → Type`, so unlike
          -- List's uniform parameter both premises cross binders and `B`/`P` are
          -- read under them. The binders are RESERVED names, and that is what
          -- makes splicing `b` and `p` under them safe: a source program cannot
          -- write `§x`, so nothing embedded here has a free occurrence to capture.
          let sigTy : Term := .sigmaT "§x" a (.app b (.pvar "§x"))
          let fTy : Term :=
            .pi "§x" a (.pi "§y" (.app b (.pvar "§x"))
              (.app p (.ctorApp "Pair" [.pvar "§x", .pvar "§y"])))
          let fOk ← hasTypeT fuel f fTy
          let sOk ← hasTypeT fuel s sigTy
          finish (Pure.nf fuel (.app p s)) rest (fOk && sOk)
        -- ¶1.3's array basis. `arrCat`/`acons` are CHECKED rather than synthesized —
        -- their element type is recovered from the expected type, which is why
        -- neither carries a `T` argument. `aget` and `arrRec` synthesize, so they
        -- keep theirs.
        | .const "arrCat", [m, k, a, b] =>
          match Pure.asArrayTy? (Pure.whnf fuel ty) with
          | none => pure false
          | some (n, t) =>
            if !(Pure.convert fuel n ty{ %(Pure.kAddFn) %m %k }) then pure false
            else do
              let aOk ← hasTypeT fuel a ty{ Array %m %t }
              let bOk ← hasTypeT fuel b ty{ Array %k %t }
              pure (aOk && bOk)
        | .const "acons", [n, x, xs] =>
          match Pure.asArrayTy? (Pure.whnf fuel ty) with
          | none => pure false
          | some (n', t) =>
            if !(Pure.convert fuel n' (.ctorApp "S" [n])) then pure false
            else do
              let xOk ← hasTypeT fuel x t
              let xsOk ← hasTypeT fuel xs ty{ Array %n %t }
              pure (xOk && xsOk)
        -- `atake i k a : Array i T` and `adrop i k a : Array k T`, for
        -- `a : Array (add i k) T`. CHECKED like their `arrCat`, and for the same
        -- reason — the element type comes from the expected type, so neither
        -- carries a `T`. The extent the caller wants is the one the projection
        -- names, so it is read off `ty` and the argument's type is BUILT from
        -- both extents rather than decomposed out of it.
        | .const "atake", [i, k, a] =>
          match Pure.asArrayTy? (Pure.whnf fuel ty) with
          | none => pure false
          | some (n, t) =>
            if !(Pure.convert fuel n i) then pure false
            else do
              let kOk ← hasTypeT fuel k (.const "Nat")
              let aOk ← hasTypeT fuel a ty{ Array %(ty{ %(Pure.kAddFn) %i %k }) %t }
              pure (kOk && aOk)
        | .const "adrop", [i, k, a] =>
          match Pure.asArrayTy? (Pure.whnf fuel ty) with
          | none => pure false
          | some (n, t) =>
            if !(Pure.convert fuel n k) then pure false
            else do
              let iOk ← hasTypeT fuel i (.const "Nat")
              let aOk ← hasTypeT fuel a ty{ Array %(ty{ %(Pure.kAddFn) %i %k }) %t }
              pure (iOk && aOk)
        | .const "aget", tt :: n :: i :: a :: rest =>       -- aget T n i a : T
          let iOk ← hasTypeT fuel i (.const "Nat")
          let aOk ← hasTypeT fuel a ty{ Array %n %tt }
          finish tt rest (iOk && aOk)
        | .const "arrRec", tt :: p :: pn :: pc :: n :: a :: rest =>   -- arrRec T P pn pc n a : P n a
          -- The cons view's recursor, so the pure library over arrays is written
          -- exactly like the one over lists (¶1.3).
          let pnOk ← hasTypeT fuel pn
            (Pure.nf fuel (.app (.app p Term.zero) (.ctorApp "Arr" [])))
          let pcTy : Term :=
            .pi "§n" (.const "Nat")
              (.pi "§x" tt
                (.pi "§xs" ty{ Array %(Term.pvar "§n") %tt }
                  (.pi "§ih" (.app (.app p (.pvar "§n")) (.pvar "§xs"))
                    (.app (.app p (.ctorApp "S" [.pvar "§n"]))
                      (.app (.app (.app (.const "acons") (.pvar "§n")) (.pvar "§x"))
                        (.pvar "§xs"))))))
          let pcOk ← hasTypeT fuel pc pcTy
          let nOk ← hasTypeT fuel n (.const "Nat")
          let aOk ← hasTypeT fuel a ty{ Array %n %tt }
          finish (Pure.nf fuel (.app (.app p n) a)) rest (pnOk && pcOk && nOk && aOk)
        | hd, args =>
          -- A bound function variable applied (`ih b c hab hbc`): synthesize by
          -- iterating Π-instantiation from its `sctx` type, checking each argument
          -- against the domain. This is ordinary application typing — what a
          -- surface lemma application (§15) or a proof reused under a binder needs.
          match hd.symOf? with
          | some σ =>
            match (← get).sctx.lookup σ with
            | none => throwErr s!"hasType: σ{subNat σ} (applied) has no type in sctx"
            | some hty =>
              match ← synthSpine fuel hty.stripCmp args with
              | some resTy => pure (Pure.convert fuel ty resTy)
              | none => pure false
          | none => throwErr s!"hasType: cannot type neutral {v.pretty}"
      | .lam x d b =>
        -- λ against Π: check the domains convert, then the body under a fresh σ
        -- witness for the binder (a checking-time hypothesis added to `sctx`).
        -- This is what lets a Π-typed lemma (`LeRefl : Π n. Le n n`) and the
        -- recursors' step arguments — both λs — type-check.
        --
        -- The λ's binder and the Π's need not agree in NAME, and the two openings
        -- below use each side's own — which is what makes checking `λ (a : τ). …`
        -- against `Π (b : τ) → …` work, i.e. what makes the rule α-insensitive
        -- where `beq` is not.
        match Pure.whnf fuel ty with
        | .pi y d' c =>
          if Pure.convert fuel d d' then do
            let σ ← freshSym
            modify (fun st => { st with sctx := (σ, d') :: st.sctx })
            hasTypeT fuel (Pure.openBinder fuel x.name b (Term.sym σ))
              (Pure.openBinder fuel y c (Term.sym σ))
          else pure false
        | _ => pure false
      | _ => throwErr s!"hasType: cannot type value {v.pretty} (λ/neutral typing deferred to M5)"
  termination_by fuel _ _ => (fuel, 0, 0)
  /-- Synthesize the result type of applying a value of type `hty` to `args`:
      each argument's domain (a Π) is checked, and the codomain is instantiated at
      the argument. `none` if an argument mistypes or a non-Π is applied. -/
  def synthSpine : Nat → Term → List Term → M (Option Term)
    | _, hty, [] => pure (some hty)
    | fuel, hty, a :: rest => do
      match Pure.whnf fuel hty with
      | .pi x dom cod =>
        if ← hasTypeT fuel a dom then synthSpine fuel (Pure.openBinder fuel x cod a) rest
        else pure none
      | _ => pure none                                 -- applied a non-function
  termination_by fuel _ args => (fuel, 2, args.length)
  /-- Check a constructor's fields against its field-type telescope, threading
      each checked field value into the remaining (dependent) field types.

      The fields are STORE values — a constructor node's children may be state —
      while the telescope is knowledge, which is the asymmetry §2.3 calls correct.
      A dependent later entry is opened at the field's knowledge, which is what a
      type can mean by an earlier field. -/
  def checkFields : Nat → List Val → List (String × Term) → M Bool
    | _, [], [] => pure true
    | fuel, v :: vs, (x, ty) :: tys => do
      if ← hasType fuel v ty then
        checkFields fuel vs (tys.map (fun e => (e.1, Pure.openBinder fuel x e.2 (subsKnowledge v))))
      else pure false
    | _, _, _ => pure false                          -- arity mismatch
  termination_by fuel _ tys => (fuel, 1, tys.length)
end

/-- **D1's one-slot kind classification**: is this `~>` RHS (already opened at
    its entry snapshot) a TYPE — today's owed-type claim — or a value, i.e. a
    PIN? Since the universe rule this IS the semantic judgment, sandboxed:
    `hasTypeT rhs Type` with the state discarded (the judgment mints hypothesis
    σs, and a classification is a query) and a REFUSAL read as "not a type" —
    a pin's shapes (a ctor value, a `Set`-spine citing `@res`, a payload σ) are
    falsified or refused by the same arms that admit every owed type, so the
    two verdicts partition the slot.

    History: before the universe rule this was a hand-rolled head-recognizer,
    because `hasTypeT · Type` threw on `Nat`/`List Nat` (the stage-0 probe's
    finding). The swap's ledger is the suite replaying green — the recognizer's
    corpus-inventory argument, now checked by the judgment instead of asserted
    by a head list. One deliberate reading change: a `borrowT`/`⇝`-headed RHS
    (a binder MODE in the slot; nothing writes one) classified as a type under
    the recognizer and classifies as a PIN here, failing loudly downstream —
    which is the more honest verdict for a slot that means neither. -/
def isOwedTypeT (fuel : Nat) (t : Term) : M Bool := do
  let st ← get
  match (hasTypeT fuel t .type).run st with
  | .ok b _ => pure b
  | .error _ _ => pure false

/-- Build a call's fresh result value from the (instantiated) return type, and
    collect the loans it ISSUES (§6.1). Each `&mut (τ ↝ τ')` position mints a
    fresh issued reborrow `borrowₘ ℓ σ` with `σ : τ` in `sctx` and owed type
    `τ'[s := σ]`; a `Pair`/`Σ` of results issues one loan PER borrow component
    (the multi-issued group — `nth2`); a non-borrow leaf is a plain fresh
    existential `σ` with no issued loan (the §5.3 wire).

    **Σ is DEPENDENT here** (M23): the tail's type may mention the components
    already built — that is the whole point of a pinned result (`Σ (r : List Nat).
    Id (List Nat) r (drop i (old *v))`, split_off's ensures), and with declared
    backs removed it is a caller's only route to knowing anything about a returned
    value. `subs` carries the built components for the enclosing Σ binders as
    `(binder name, value)`, innermost first; a leaf opens each of them in its type
    before minting the σ. Order stopped mattering at M30 step 2 — under de Bruijn
    the fold had to run from the head because `substPure 0` shifted the outer
    binders down as it went, and under names each entry is found by its own name.
    (Before M23 the tail was built independently, leaving a dangling `pvar` in the
    σ's sctx type, so the pin was unusable at the call site — `useIt(a, h)` failed
    with `argument (σ1) does not have its parameter type (Id σ0 (S Z))`.) -/
partial def buildResult (fuel : Nat) (inst : Omega) (subs : List (String × Term)) :
    Term → M (Val × List (Nat × Term × Option Term))
  | .borrowT s τ S => do
    let τVal := (subs.foldl (fun t p => Pure.openBinder fuel p.1 t p.2) (← readCWith fuel inst τ))
    let σ ← freshSym
    let ℓr ← freshLoan
    -- `S` binds the snapshot at `s`; the enclosing Σ binders are named too, so
    -- opening one no longer disturbs the others.
    let sVal ← readCWith fuel inst S
    let sVal := Pure.openBinder fuel s sVal (Term.sym σ)
    let opened := Pure.nf fuel (subs.foldl (fun t p => Pure.openBinder fuel p.1 t p.2) sVal)
    modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
    -- D1 on an ISSUED borrow: a pin here is the RESULT's own contract — the
    -- identity pin is the read-only law (§5), asserted by `endIssued` when the
    -- caller's group ends. Opened at the issued payload's σ, which is this
    -- borrow's entry snapshot from the caller's side.
    if ← isOwedTypeT fuel opened then
      pure (.borrowM ℓr (.know (Term.sym σ)), [(ℓr, opened, none)])
    else
      pure (.borrowM ℓr (.know (Term.sym σ)), [(ℓr, τVal, some opened)])
  | .sigmaT x a b => do
    let (vA, issA) ← buildResult fuel inst subs a
    -- **What a later component SEES of an earlier one is its knowledge** (M32
    -- R1), which for a borrow component is the payload σ rather than the
    -- `borrowₘ ℓ σ` node the caller receives. The old code pushed the node, i.e.
    -- put a loan marker in a type; under the split it cannot, and the payload is
    -- the only reading of "what this component is" a type could have meant.
    -- Reachable since M35 (D9): `retMixesBorrow` is lifted, so a dependent tail
    -- over a borrow component is writable — `Σ (r : &mut Nat). Id Nat (*r) …`.
    -- The deref of the binder collapses first: the knowledge of a borrow IS its
    -- payload, so `*r` opens to the payload σ, which is what the caller's
    -- minted evidence should be ABOUT.
    let (vB, issB) ← buildResult fuel inst ((x, subsKnowledge vA) :: subs) (collapseDerefOf x b)
    pure (.ctor "Pair" [vA, vB], issA ++ issB)
  | rt => do
    let retTy := (subs.foldl (fun t p => Pure.openBinder fuel p.1 t p.2) (← readCWith fuel inst rt))
    let σ ← freshSym
    modify (fun s => { s with sctx := (σ, retTy) :: s.sctx })
    pure (.know (Term.sym σ), [])
  -- (partial since M35: the Σ arm recurses on the deref-collapsed tail, which
  -- is not a structural subterm once a dependent tail over a borrow is legal.)


/-! ## Loan groups (§6.1): the ending cascade

    A call mints a `Group`. Ending a captured loan does not end it alone — it
    triggers the whole group's end: **every issued borrow ends first** (locate
    it, audit its payload against its owed type, surrender it), **then the
    group ends atomically**, releasing each captured loan — each getting a fresh,
    unconstrained existential at its owed type. The ordering *is* the soundness argument
    (§6.1): a captured owner cannot recover while an issued borrow lives. -/

/-- End one issued borrow: locate it in Ω, audit its (collapsed) payload against
    its owed type — and against its PIN if it carries one (§5: the read-only
    law's enforcement site; an identity-pinned result whose caller wrote through
    it fails here) — kill it, and return the surrendered payload. -/
def endIssued (fuel : Nat) (ℓ : Nat) (owed : Term) (pin : Option Term := none) : M Val := do
  match (← getEnv).findSome? (fun kv => findBorrowPayload ℓ kv.2) with
  | none => throwErr s!"group end: issued borrow ℓ{subNat ℓ} is not locatable in Ω (cannot end the group)"
  | some payload => do
    match payload with
    | .bot => throwErr s!"group end: issued borrow ℓ{subNat ℓ} holds a hole (⊥) — nothing surrendered"
    | _ =>
      if ← hasType fuel payload owed then do
        match pin with
        | some p =>
          if Pure.convert fuel (subsKnowledge payload) p then pure ()
          else throwErr s!"group end: issued borrow ℓ{subNat ℓ}'s surrendered payload ({payload.pretty}) violates the borrow's pin ({p.pretty}) — its contract says what comes back through it is {p.pretty}, and writing anything else through a pinned borrow is refused here"
        | none => pure ()
        setEnv ((← getEnv).map (fun kv => (kv.1, replaceBorrowWithBot ℓ kv.2)))   -- kill
        pure payload
      else
        throwErr s!"group end: issued borrow ℓ{subNat ℓ}'s payload ({payload.pretty}) does not have its owed type ({owed.pretty})"

/-- Release one captured loan: plug `v` where its marker sits. -/
def releaseCaptured (ℓ : Nat) (v : Val) : M Unit := sendPayloadToLoan ℓ v

/-- The debt a group registered on loan `ℓ` at `site` (a `.call`/`.issue` of its
    own ρ). Total for any group `callDeclC` minted — a missing entry is a
    registration bug, and failing loudly is what finds it. -/
def groupDebt (ℓ : Nat) (site : DebtSite) : M Debt := do
  match (← get).debts.find? (fun d => d.loan == ℓ && d.site == site) with
  | some d => pure d
  | none => throwErr s!"group end: loan ℓ{subNat ℓ} has no registered debt at its group site"

/-- End a whole loan group (§6.1): issued borrows first, then captured atomically. -/
def endGroup (fuel : Nat) (grp : Group) : M Unit := do
  -- 1. end every issued borrow, collecting surrendered payloads (in order) —
  -- asserting each one's own pin (§5, the read-only law) as it ends.
  let surrendered ← grp.issued.mapM (fun ℓ => do
    let d ← groupDebt ℓ (.issue grp.id)
    endIssued fuel ℓ d.owed d.pin)
  -- 2. remove the group from the table (by its ρ id)
  modify (fun s => { s with groups := s.groups.filter (fun g => g.id != grp.id) })
  -- 3. release captured loans atomically
  -- §6.2's SPEC end used to sit first here, and M28 σ's identity wire after it.
  -- Both are gone — the backward-spec mechanism with M27, the identity wire with
  -- its test. What decides a release now is the captured loan's debt: a PIN is
  -- the release, with `@res k` substituted by the k-th issued borrow's ACTUAL
  -- surrendered payload — the same substitution the audit ran at fresh exit σ's,
  -- instantiated at the values the caller really wrote (§2.3's one rule, second
  -- instantiation; D2(a)'s one-slot simplification: the release is `.know (nf e)`
  -- directly, no σ′ intermediary). §5.4's exit-snapshot pin `sym σ′` is the
  -- degenerate res-free case and releases byte-identically to the old rule.
  let exitsIdx := surrendered.map subsKnowledge
  grp.captured.forM (fun ℓc => do
    let d ← groupDebt ℓc (.call grp.id)
    match d.pin with
    | some p => releaseCaptured ℓc (.know (Pure.nf fuel (substResIdx exitsIdx p)))
    | none => do                                        -- opaque: fresh existential each
      let σ ← freshSym
      modify (fun s => { s with sctx := (σ, d.owed) :: s.sctx })
      releaseCaptured ℓc (.know (Term.sym σ)))
  -- 4. the group's debts leave with it (its loans' stories are over; a param
  -- debt on the same loan — site `.param` — survives for the exit audit).
  modify (fun s => { s with debts := s.debts.filter (fun d => match d.site with
    | .call ρ | .issue ρ => ρ != grp.id
    | .param _ => true) })

/-- **End loan** ℓ (§6.1-aware). If ℓ is a group's captured loan, ending it
    ends the whole group (issued first, then captured). Otherwise it is an
    ordinary loan: kill its borrow and plug the payload home (§2.2 End-Mut). -/
def endLoan (fuel : Nat) (ℓ : Nat) : M Unit := do
  match (← get).groups.find? (fun g => g.captured.contains ℓ) with
  | some grp => endGroup fuel grp
  | none => sendPayloadToLoan ℓ (← killBorrowInΩ ℓ)

/-! ## Pop-with-drop (M31 Stage 0): a scope's entries leave with it

    `openScope` recorded Ω's length; closing the scope drops the suffix past it.
    Two halves, in this order:

      1. **The drop sweep**, in REVERSE binding order (Rust's order: the
         last-bound local is dropped first). Each popped entry surrenders the
         borrows it *holds* — `endLoan` sends each payload home to its marker,
         wherever that lives. Loan MARKERS in a popped entry are not touched:
         their borrows are held elsewhere and end on their own owner's drop, and
         reaching for them here would kill a borrow that is still live.
      2. **The truncation.** What is left of the scope's entries is discarded —
         except entries that still carry an ownership node, which are RETAINED.

    Retention is the answer to the one semantic edge, and it is the answer frame
    exit already gives today: `releaseFrameLoans` skips the loans the result
    carries out (`keep`), and the frame slot holding the matching `loanM` marker
    then survives because the arena never popped. Under pop-with-drop that
    survival has to be *stated* rather than inherited, and the statement is
    exactly this: **a scope-local whose borrow escaped the scope keeps its
    storage, because that storage is where the escaping borrow's payload returns
    to.** Popping it would leave the marker unfindable and the next `endLoan` on
    that loan stuck ("cannot plug payload back"), turning a program that runs
    into one that does not. The checker rejects an escaping borrow of a local at
    the audit's boundary check, so this retention is only ever reached by the
    executing machine on a program the checker never saw.

    Ending a loan early is sound: the demand machinery already ends loans lazily
    (§5.2, "every demand collapses first"), so eager ending at scope exit moves
    the same events earlier and adds none.

    `endLoan` and everything it calls REWRITE Ω rather than resize it, so `mark`
    and the retained-tail length stay valid across the sweep. -/

/-- The drop sweep for the entries of `Ω[mark … len - retain)`: end every borrow
    they hold whose loan is not in `keep`, last-bound first. `retain` shields the
    trailing entries that belong to the ENCLOSING scope — the `let x = match …`
    seam binds `x` after the arm's own entries, and `x` outlives the arm. -/
partial def dropScopeEntries (fuel : Nat) (mark retain : Nat) (keep : List Nat) : M Unit := do
  match fuel with
  | 0 => throwErr "pop: out of fuel (scope drop sweep)"
  | f + 1 => do
    let env ← getEnv
    let inner := (env.drop mark).take (env.length - mark - retain)
    match (inner.filterMap (fun kv => firstHeldBorrow keep kv.2)).getLast? with
    | none => pure ()
    | some ℓ => do endLoan fuel ℓ; dropScopeEntries f mark retain keep

/-- **Close the innermost open scope**: drop its entries (above), then truncate
    Ω past its watermark, retaining any entry that still carries an ownership
    node. Returns whether the scope closed was a match arm; `true` when there was
    nothing open, so the unwinding loops terminate. -/
def popScope (fuel : Nat) (retain : Nat) (keep : List Nat) : M Bool := do
  match ← takeScopeMark with
  | none => pure true
  | some (mark, arm) => do
    dropScopeEntries fuel mark retain keep
    let env ← getEnv
    let inner := (env.drop mark).take (env.length - mark - retain)
    setEnv (env.take mark
              ++ inner.filter (fun kv => (firstOwnNode kv.2).isSome)
              ++ env.drop (env.length - retain))
    pure arm

/-- Close scopes until only `depth` remain open, innermost first — a frame's
    unwind. The loop, rather than one pop, because a body may leave inner scopes
    open behind it: a match arm in TAIL position has no seam (there is no
    continuation for the fusion to splice), so its scope closes with the
    enclosing body's. Inner scopes drop before the frame containing them, which
    is Rust's order. -/
partial def popScopesTo (fuel : Nat) (depth : Nat) (retain : Nat) (keep : List Nat) : M Unit := do
  if (← scopeDepth) > depth then do
    let _ ← popScope fuel retain keep
    popScopesTo fuel depth retain keep
  else pure ()

/-- Close scopes up to and including the innermost **match arm** — the `@popArm`
    seam's unwind. Everything still open inside the arm is a tail-position match
    within it, and dies with it. -/
partial def popArmScope (fuel : Nat) (retain : Nat) (keep : List Nat) : M Unit := do
  if ← popScope fuel retain keep then pure () else popArmScope fuel retain keep

-- (`releaseFrameLoans` — "scope-aware release at call return", the drop half of
-- frame exit keyed on the frame's ID WINDOW rather than on a watermark — retired
-- in M31 Stage 0. `popScope` is the same sweep generalized twice: it finds a
-- borrow anywhere in a popped value rather than only at its top, and it takes the
-- slots with it instead of leaving a frame's environment in Ω forever. The id
-- window was doing the watermark's job with arithmetic; `bindSlot` appends, so
-- the length was always the honest key.)

/-! ## CARVE (¶3) — the proof-licensed reorganization

    The design's one new rule, and the only one of ¶8.1's five additions with
    semantic content. It sits alongside `drop` and `endLoan` as a **third
    reorganization**: lazy like both, fired when a rule's premise demands it, and
    aimed at the environment's own bookkeeping.

                    Ω(p) = an array node of type Array n T
                    the extent map has an OWNED leaf L at (b, m)                   (1)
                    e ⊢ Le b lo  ×  Le (add lo cnt) (add b m)                      (2)
                    the decomposition transitions on lo and on m succeed           (3)
    ───────────────────────────────────────────────────────────────────────────  CARVE
       L : Array m T  ↦  ⟨ lo′ ▷ L₁ , cnt ▷ L₂ , rest ▷ L₃ ⟩

    Premise (3) is the aggressive part (¶9a) and the part that pays: the extents are
    equations the transition SOLVES, never differences it computes, so no `sub` is
    produced here or anywhere downstream of here, and the audit's rejoin conversion
    is definitional rather than lemma-mediated. -/

/-- Premise (2)'s obligation type for a candidate leaf at `(b, m)`. When the leaf
    starts at the node's base — "the overwhelmingly common case" — it is the single
    `Le (add lo cnt) n` that ¶3.2 says is "character for character, the bound the M22
    quicksort already threads through every call as `hbnd`". -/
def carveObligation (fuel : Nat) (b m lo cnt : Term) : Term :=
  -- LEAF-RELATIVE wherever the leaf-relative offset is already known, which is both
  -- cases the design's programs actually produce. `Le` computes by double `natRec`,
  -- so `Le (add b cnt) (add b m)` is STUCK on a symbolic `b` and never converts with
  -- the `Le cnt m` a program can supply — stating the obligation absolutely would
  -- demand evidence about the leaf's absolute end that nothing can produce. Premise
  -- (3)'s own logic says the offsets are leaf-relative; premise (2) should be too.
  if Pure.convert fuel lo b then ty{ %(Pure.kLeFn) %cnt %m }                       -- base-aligned: lo' = Z
  else if Pure.convert fuel b Term.zero then ty{ %(Pure.kLeFn) %(rangeEnd fuel lo cnt) %m }  -- leaf at the node base
  else
    let low := ty{ %(Pure.kLeFn) %b %lo }
    let high := ty{ %(Pure.kLeFn) %(rangeEnd fuel lo cnt) (%(Pure.kAddFn) %b %m) }
    .sigmaT "§lo" low high

/-- Is the cited evidence good for this leaf? With no evidence cited we try the
    canonical inhabitant of ⊤ — ¶3.2's supply route 1, "conversion alone", which is
    what makes every literal-indexed access free. Route 3 is that there is no route
    3: no inference, no decision procedure, no `omega`. -/
def carveEvidenceOk (fuel : Nat) (ev : Option Term) (oblig : Term) : M Bool := do
  match ev with
  | some e => hasTypeT fuel e oblig
  | none =>
    let star : Term := .ctorApp "unit" []
    if ← hasTypeT fuel star oblig then pure true
    else hasTypeT fuel (.ctorApp "Pair" [star, star]) oblig

/-- Split an owned body into the three pieces the carve's extents name. Only the two
    forms ¶3.2 defines the split on: a literal run (split positionally, which needs
    concrete extents — one cannot cut a run at an offset one does not know) and a σ
    (refined to the `arrCat` spine, which is ordinary ⇜, marker-free, and true of the
    value timelessly). Returns the three bodies. -/
def carveBody (fuel : Nat) (body : Val) (loN cntN restN : Nat) (lo' cnt rest : Term)
    : M (Val × Val × Val) := do
  match Val.asCtor? body, body.symOf? with
  | some ("Arr", vs), _ =>
    pure (.ctor "Arr" (vs.take loN),
          .ctor "Arr" ((vs.drop loN).take cntN),
          .ctor "Arr" (vs.drop (loN + cntN)))
  | _, some σ =>
    match (← get).sctx.lookup σ with
    | none => throwErr s!"carve: σ{subNat σ} has no type in sctx"
    | some τ =>
      match Pure.asArrayTy? (Pure.whnf fuel τ).stripCmp with
      | none => throwErr s!"carve: σ{subNat σ} is not of array type ({τ.pretty})"
      | some (_, t) => do
        let mk : Term → M Term := fun c => do
          let s ← freshSym
          modify (fun st => { st with sctx := (s, ty{ Array %c %t }) :: st.sctx })
          pure (Term.sym s)
        let b₁ ← mk lo'; let b₂ ← mk cnt; let b₃ ← mk rest
        -- The spine is built over the NONEMPTY pieces only. A zero-extent σ would be
        -- a name for the empty array that nothing can ever compute away (`arrCat`'s
        -- ι absorbs an empty RUN, not an empty σ), and it would leave every rejoin
        -- conversion needing a lemma. `restN`/`loN` are meaningful only in the
        -- concrete case; the symbolic test is `convert c Z`, below.
        let isZ : Term → Bool := fun c => Pure.convert fuel c Term.zero
        let spine :=
          if isZ lo' then (if isZ rest then b₂ else ty{ arrCat %cnt %rest %b₂ %b₃ })
          else if isZ rest then ty{ arrCat %lo' %cnt %b₁ %b₂ }
          else ty{ arrCat %lo' (%(Pure.kAddFn) %cnt %rest) %b₁ (arrCat %cnt %rest %b₂ %b₃) }
        refineSym σ (.know spine)
        pure (.know b₁, .know b₂, .know b₃)
  | _, _ =>
    throwErr s!"carve: leaf body {body.pretty} cannot be split (¶3.2 defines the split on an owned run or a σ; a compound neutral is stuck)"

/-- Make a one-slot segment's body an explicit single-element run, so that an INDEX
    place reaches the element as a subterm. When the body is a σ this fires a
    refinement `σ := [σₑ]` — knowledge, and marker-free: a length-1 array IS the
    singleton of its element, timelessly.

    This is ¶9's fourth, smaller uncertainty measured: "whether element access `a[i]`
    should be a one-slot carve, as designed, or a cheaper dedicated rule … every
    element read then fires a refinement, and in a loop-free recursive cursor that is
    a lot of σ churn for what compiles to one load." It costs exactly one σ per
    symbolic element access, and none at all on a run. -/
def elementize (fuel : Nat) (body : Val) : M Val := do
  match Val.asCtor? body, body.symOf? with
  | some ("Arr", [_]), _ => pure body
  | _, some σ =>
    match (← get).sctx.lookup σ with
    | none => throwErr s!"a[i]: σ{subNat σ} has no type in sctx"
    | some τ =>
      match Pure.asArrayTy? (Pure.whnf fuel τ).stripCmp with
      | none => throwErr s!"a[i]: σ{subNat σ} is not of array type ({τ.pretty})"
      | some (_, t) => do
        let e ← freshSym
        modify (fun st => { st with sctx := (e, t) :: st.sctx })
        refineSym σ (.know (.ctorApp "Arr" [Term.sym e]))
        pure (.ctor "Arr" [.know (Term.sym e)])
  | _, _ => throwErr s!"a[i]: the one-slot segment holds {body.pretty}, which is not a single-element run"

/-- §5.2's demand-end, at the NODE rather than at a leaf.

    "Any rule that READS a place ends the suspensions parked there before it looks",
    and a carve reads the place — it consults the extent map. `carveAt` already
    demand-ends a loaned LEAF (a segment out on loan) and a marker buried inside a
    one-slot run; what it lacked is the case where the WHOLE payload is suspended,
    which has exactly one producer: a reborrow into a call. `f(&mut *v)` parks a marker
    at `*v`, and the group's release plugs the payload back only when something demands
    it — so `*v` is `loanₘ ℓ` until then, and `arrExtent` has no array value to read.

    `readR` performs the same collapse at its own reborrow and match sites; this is that
    rule reaching the carve, and it is why a recursive array program can carve the
    argument it just handed to its recursive call. -/
partial def demandNode (fuel : Nat) (pos : Pos) : M Unit := do
  match ← getAtPos fuel pos with
  | .loanM ℓ => do endLoan fuel ℓ; demandNode fuel pos
  | _ => pure ()

/-! **The carve**, at the array node sitting at `pos`. `isIdx` selects the one-slot
    variant (`a[i]` is a one-slot carve — ruling 4's uniformity, no dedicated rule).

    Everything is re-read from Ω rather than threaded, because premises (2) and (3)
    both REFINE: the residue transition rewrites a length index everywhere and the
    body split rewrites the leaf's σ everywhere, so a detached copy of the node goes
    stale the moment either fires. -/
partial def carveAt (fuel : Nat) (pos : Pos) (lo cnt : Term) (given : Option Term)
    (ev : Option Term) (eqc : Option Term) (isIdx : Bool) : M Unit := do
  demandNode fuel pos
  -- G5, THIRD SITE (EXECUTING only). A ZERO-WIDTH request is the empty slice at `lo`:
  -- it must borrow nothing and disturb nothing. In particular it must not select the
  -- leaf it ABUTS — `Le (add lo Z) (add b m)` holds at a leaf's far end, so the ordinary
  -- selection picks the neighbour and demand-ends the live borrow pinned to it, which is
  -- how `partitionA`'s pivot cell died at `k3 = 0, r2 = 0`. A DEGENERATE carve leaves no
  -- trailing piece behind either, so there is nothing at that base to find.
  --
  -- Unreachable symbolically — a residue σ is never known to be zero — and routine
  -- concretely, since an empty right half is what a runtime split produces constantly.
  -- So: give the empty slice its own zero-extent segment, inserted at `lo` without
  -- touching any existing leaf, and let the ordinary degenerate path borrow it.
  if (← get).executing && !isIdx && Pure.convert fuel cnt Term.zero then do
    setAtPos fuel pos (Val.mergeArrays (← getAtPos fuel pos))
    let leaves ← extentMap fuel (← getAtPos fuel pos)
    if (leaves.any (fun l => Pure.convert fuel l.base lo && Pure.convert fuel l.count Term.zero))
    then pure ()
    else do
      let segs := leaves.map (fun l => Val.segNode l.count l.body)
      let rec place (acc : List Val) (bse : Term) : List Val → List Val
        | [] => acc ++ [Val.segNode Term.zero (.ctor "Arr" [])]
        | sg :: rest =>
          if Pure.convert fuel bse lo then acc ++ [Val.segNode Term.zero (.ctor "Arr" [])] ++ (sg :: rest)
          else match Val.asSeg? sg with
            | some (c, _) => place (acc ++ [sg]) ty{ %(Pure.kAddFn) %bse %c } rest
            | none => acc ++ (sg :: rest)
      setAtPos fuel pos (.node "§segs" (place [] Term.zero segs))
  else pure ()
  -- ROUTE (a), step one: the program SUPPLIED the residue's extent, so solve premise
  -- (3)'s equation against it HERE, before premise (2) is even formed. That ordering is
  -- the whole trick — with the leaf's extent refined to `add cnt rest`, the obligation
  -- is stated over a DECOMPOSED extent and often computes away entirely: at the pivot
  -- carve `Le 1 rest` becomes `Le 1 (S j)` ⇝ `Le Z j` ⇝ ⊤, needing no evidence at all.
  -- ¶3.2 says `Le a b` "is precisely the assertion that `b` decomposes as `a` plus
  -- something", so supplying the decomposition supplies most of the proof.
  --
  -- The leaf is selected by BASE ALIGNMENT here rather than by the evidence's type:
  -- `a[lo ; cnt ; rest]` says where it starts. Base alignment alone does NOT determine
  -- the leaf, though, and an earlier draft of this comment claimed it did: a ZERO-EXTENT
  -- segment shares its base with the segment after it, so a node holding one has two
  -- leaves at that base. Zero-extent segments are unreachable symbolically — a residue
  -- σ is never known to be zero — and routine concretely, since every runtime-computed
  -- split has an empty side eventually. So the supplied DECOMPOSITION disambiguates:
  -- prefer the leaf whose extent already IS `add cnt rest`, then any leaf that is not
  -- empty (an empty leaf cannot contain a request of positive width), then give up.
  match given with
  | none => pure ()
  | some rest => do
    setAtPos fuel pos (Val.mergeArrays (← getAtPos fuel pos))
    let leaves ← extentMap fuel (← getAtPos fuel pos)
    let aligned := leaves.filter (fun l => Pure.convert fuel l.base lo)
    let pick :=
      (aligned.find? (fun l => Pure.convert fuel l.count ty{ %(Pure.kAddFn) %cnt %rest }))
        <|> (aligned.find? (fun l => !(Pure.convert fuel l.count Term.zero)))
        <|> aligned.head?
    match pick with
    | none =>
      throwErr s!"carve: no segment starts at {lo.pretty}, so the supplied residue has no leaf to decompose (¶3.2 premise 1)"
    | some l =>
      -- THE DECOMPOSITION IS DECLARED, NOT INFERRED. When it already holds by
      -- conversion there is nothing to record and nothing to check — that is the case
      -- of a leaf whose extent is a constructor tree (`S m` against `add 1 m`), and it
      -- stays free. Otherwise the supplied residue ASSERTS a decomposition of the
      -- leaf's extent, and refining a telescope parameter's σ to match would impose an
      -- unrecorded constraint on this function's CALLERS — M7/M8's signature-inferred
      -- constrained wire, whose lesson (M17) is that cross-boundary constraints must be
      -- DECLARED and checked. §3.2's own line is that refinement carries equation
      -- SOLUTIONS; a cited, checked `Id` is legitimate ⇜ knowledge with recorded
      -- provenance, an unrecorded unification against a universal is not. So the
      -- program cites the equation and premise (3) solves ALONG it — the same refl-match
      -- solution transition, now licensed.
      if Pure.convert fuel l.count ty{ %(Pure.kAddFn) %cnt %rest } then pure ()
      else
        let owed := Term.idT (.const "Nat") l.count ty{ %(Pure.kAddFn) %cnt %rest }
        match eqc with
        | some q =>
          if ← hasTypeT fuel q owed then reflUnify fuel l.count ty{ %(Pure.kAddFn) %cnt %rest }
          else throwErr s!"carve: the cited decomposition does not have type {owed.pretty} (¶3.2 premise 3: the citation is the license, and its TYPE is what licenses)"
        | none =>
          throwErr s!"carve: the supplied residue asserts {owed.pretty}, which does not hold by conversion, and premise (3) may not impose it by refining a telescope parameter's σ — that would constrain this function's callers without recording it in its signature (M17). Cite the equation as a[lo ; cnt ; rest | h | heq]"
  -- Merge first: premise (1) wants MAXIMAL owned leaves, so a range spanning two
  -- adjacent owned segments must see them as one. This is also where merge fires
  -- after a mid-body demand-end — the read is the trigger, so nothing else has to be.
  setAtPos fuel pos (Val.mergeArrays (← getAtPos fuel pos))
  let node ← getAtPos fuel pos
  let leaves ← extentMap fuel node
  -- Degenerate carve (¶3.2): "when the request coincides with the leaf, no split and
  -- no refinement happen at all". No obligation either — `Le b b` and `Le x x` are
  -- `LeRefl`, so demanding evidence would be friction with no content. This is the
  -- asymmetry ¶3.4 says IS the design: an exhaustive split costs ONE proof, not two.
  let degenerate := leaves.find? (fun l => Pure.convert fuel l.base lo && Pure.convert fuel l.count cnt)
  -- Premise (2): form each candidate leaf's obligation and check the evidence against
  -- it; the first that types SELECTS the leaf — "the evidence's type is the selector".
  -- Deterministic without a tie-break, because leaves are disjoint. A degenerate
  -- request needs no evidence at all: its two `Le`s are `LeRefl`, so demanding a term
  -- would be friction with no content. That asymmetry is ¶3.4's, and it is why an
  -- exhaustive split costs ONE proof rather than two.
  let sel ← match degenerate with
    | some l => pure (some l)
    | none => do
      let cands ← leaves.filterMapM (fun l => do
        if ← carveEvidenceOk fuel ev (carveObligation fuel l.base l.count lo cnt)
        then pure (some l) else pure none)
      pure cands.head?
  match sel with
  | none =>
    -- ¶3.5's OVERLAP, and the shape it actually takes: after `&mut a[0 ; 3]` the map
    -- is `[(0,3,loaned ℓ₁), (3,rest,owned)]` and the request [2,5) is contained in
    -- NEITHER leaf — it straddles the boundary. So the rejection needs no
    -- owned-versus-loaned test: two segments cannot overlap, so a range that crosses
    -- a segment boundary has no leaf at all. No arithmetic was performed and no proof
    -- could have helped.
    throwErr s!"carve: no leaf of {node.pretty} contains [{lo.pretty} ; {cnt.pretty}] with the evidence given — either the range meets a loan boundary (¶3.5 overlap: the ownership is elsewhere) or the containment obligation `Le (add lo cnt) n` is neither computable nor cited (¶3.2: there is no inference, no decision procedure; cite it as a[lo ; cnt | h])"
  | some l =>
    -- A DEGENERATE range request needs nothing at all: no split, no obligation, no
    -- ownership test. That last is not laxity — it is what makes ¶2.2's take-and-refill
    -- work at a range place, since between the take and the refill the segment holds a
    -- hole and the ⇐-fill is its one legal successor. An INDEX request still has to
    -- reach an element, so it falls through.
    if degenerate.isSome && !isIdx then pure ()
    else match l.body with
    | .loanM ℓ => do
      -- §5.2's demand-end rule, arriving at an array node as its sixth site: "any rule
      -- that READS a place ends the suspensions parked there before it looks". ¶3.6's
      -- trace is exactly this (`let z = a[0]` ends the group, releasing both captured
      -- loans), and so is ¶3.3's. It is also what the whole-place rules already do —
      -- `&mut x` and a move of `x` both End-Mut a marker sitting at `x`. The overlap
      -- rejection is NOT this case: it is the no-leaf-contains-it case above.
      endLoan fuel ℓ; carveAt fuel pos lo cnt given ev eqc isIdx
    | .bot =>
      throwErr s!"carve: range [{lo.pretty} ; {cnt.pretty}) meets a hole (⊥) at [{l.base.pretty} ; {l.count.pretty}) — the run was moved out and not refilled, and a hole is not owned"
    | body =>
      if !Val.segOwned body then do
        -- A run with a marker buried in it (an element cursor's `Arr [loanₘ ℓ]`) is
        -- not owned either. Same demand-end, found by the same traversal §2.2 already
        -- uses for a marker in owned position.
        match firstLoanMarker body with
        | some ℓ => do endLoan fuel ℓ; carveAt fuel pos lo cnt given ev eqc isIdx
        | none =>
          throwErr s!"carve: leaf body {body.pretty} at [{l.base.pretty} ; {l.count.pretty}) is not owned (it carries a hole)"
      else if degenerate.isSome then do
        -- ¶3.2: "Degenerate carves are no-ops: when the request coincides with the
        -- leaf, no split and no refinement happen at all." An index place still needs
        -- its one slot made an explicit element.
        if isIdx then do
          let b' ← elementize fuel body
          setAtPos fuel ⟨pos.root, pos.path ++ [.rng lo cnt none]⟩ b'
        else pure ()
      else do
        -- Premise (3), the decomposition transitions. The leaf-relative offset first.
        -- Two shapes cover every carve the design's programs perform, and each avoids
        -- minting anything: a leaf at the node's base (`lo' = lo`) and a request at
        -- the leaf's base (`lo' = Z`). The general case mints a witness and solves
        -- `lo ≡ add b lo'` by the §10 solution transition — M10's machinery, unchanged.
        let lo' ←
          if Pure.convert fuel lo l.base then pure Term.zero
          else if Pure.convert fuel l.base Term.zero then pure lo
          else do
            let d ← freshSym
            modify (fun st => { st with sctx := (d, .const "Nat") :: st.sctx })
            reflUnify fuel lo ty{ %(Pure.kAddFn) %(l.base) %(Term.sym d) }
            pure (Term.sym d)
        -- Then the residue. Concrete extents COMPUTE (¶3.3's trace: "n = 3 concrete,
        -- both sides compute — nothing refined"), and the arithmetic is meta-level on
        -- numerals, never a `sub` in the object language. Symbolic extents mint `rest`
        -- and solve `m ≡ add lo' (add cnt rest)` — the equation ¶3.2 reaches with
        -- `le_split` twice plus an add-cancellation lemma, asserted here in its cancelled form
        -- because the checker unpacks the witnesses itself and no program term ever
        -- projects them.
        let lo'N := Term.natOf? (Pure.nf fuel lo')
        let cntN := Term.natOf? (Pure.nf fuel cnt)
        let mN := Term.natOf? (Pure.nf fuel l.count)
        let rest ←
          match given, lo'N, cntN, mN with
          -- ROUTE (a), step two: premise (3)'s residue is the term the program wrote.
          -- Its equation was already solved above, so nothing is minted and nothing is
          -- left nameless.
          | some r, _, _, _ => pure r
          | none, some a, some c, some m =>
            if a + c ≤ m then pure (Term.nat (m - a - c))
            else throwErr s!"carve: [{lo.pretty} ; {cnt.pretty}) runs past the leaf at [{l.base.pretty} ; {l.count.pretty})"
          | none, _, _, _ => do
            let r ← freshSym
            modify (fun st => { st with sctx := (r, .const "Nat") :: st.sctx })
            -- ¶3.2's two outcomes, and they are M10's two. FLEX — the leaf's extent is
            -- a bare σ, which is the case whenever the length came from a telescope
            -- parameter, i.e. always in the programs this is for: the solution
            -- transition refines it and the decomposition holds DEFINITIONALLY from
            -- here on. RIGID — a compound neutral like `add p q` — is stuck, and the
            -- remedy is the one the north star already uses: take the length as a
            -- parameter. A real restriction on which signatures are carvable (¶8.4).
            (do reflUnify fuel l.count ty{ %(Pure.kAddFn) %lo' (%(Pure.kAddFn) %cnt %(Term.sym r)) }) <|>
              throwErr s!"carve: premise (3) is stuck — the leaf's extent ({l.count.pretty}) is a compound neutral, not a flexible σ, so `m ≡ add lo' (add cnt rest)` has no solution by refinement. Take the length as a telescope PARAMETER rather than an expression (¶3.2, ¶8.4's rigid-length restriction)"
            pure (Term.sym r)
        -- The bodies. Positional on a run (which needs concrete extents — one cannot
        -- cut a literal at an offset one does not know), ⇜ on a σ.
        let restN := Term.natOf? (Pure.nf fuel rest)
        let (b₁, b₂, b₃) ←
          match Val.asCtor? body, lo'N, cntN, restN with
          | some ("Arr", _), none, _, _ =>
            throwErr s!"carve: cannot split the literal run {body.pretty} at a symbolic offset"
          | some ("Arr", _), _, none, _ =>
            throwErr s!"carve: cannot split the literal run {body.pretty} at a symbolic count"
          | _, a, c, r =>
            carveBody fuel body (a.getD 0) (c.getD 0) (r.getD 0) lo' cnt rest
        let b₂ ← if isIdx then elementize fuel b₂ else pure b₂
        -- Assemble: the leaf's segment becomes up to three, zero-extent ones dropped
        -- (¶1.1's drop-empty), and `segsNode` unwraps a lone survivor. So a carve
        -- whose residue is empty leaves no wrapper behind at all.
        -- G5 probe: a zero-extent piece is KEPT when the node is or becomes suspended.
        -- Dropping it (¶1.1's drop-empty) leaves no segment at that base, so a
        -- later zero-width request there — `a[S k ; 0]`, which is what an empty right
        -- half is — selects the NEIGHBOURING segment instead and demand-ends the live
        -- borrow pinned to it. Kept unconditionally here; the extent map sums the same
        -- (`add Z k ⇝ k`) and the ⇝ fold absorbs an empty run definitionally.
        let isZ : Term → Bool := fun c => Pure.convert fuel c Term.zero
        let ex := (← get).executing
        let pieces := (if isZ lo' && !ex then [] else [Val.segNode lo' b₁])
                   ++ [Val.segNode cnt b₂]
                   ++ (if isZ rest && !ex then [] else [Val.segNode rest b₃])
        let node' ← getAtPos fuel pos                    -- re-read: (3) may have refined
        match node' with
        | .node "§segs" segs => do
          let (i, _) ← findSeg fuel l.base l.count node'
          setAtPos fuel pos (Val.segsNode ((segs.take i) ++ pieces ++ (segs.drop (i + 1))))
        | _ => setAtPos fuel pos (Val.segsNode pieces)

/-- Resolve `a[lo ; ..]`'s count: the extent of the segment starting at `lo`.

    This NAMES the residue rather than computing it. Premise (3) already minted
    `rest` and parked it in the extent map as a *given*, so reading it back costs
    nothing and produces no `sub` — which is the whole point of ¶2.1's ban on
    lower-and-upper. Without it a program cannot write ¶3.4's second borrow at all:
    both ¶3.4 and ¶5 spell it `&mut (*a)[k ; rest]`, and `rest` is a machine-internal
    σ with no surface name. (A `lo` that does not START a segment is resolvable only
    when everything is concrete, where the arithmetic is meta-level on numerals; the
    symbolic case is rejected rather than papered over with a subtraction.) -/
def restOfLeaf (fuel : Nat) (pos : Pos) (lo : Term) : M Term := do
  let node := Val.mergeArrays (← getAtPos fuel pos)
  let leaves ← extentMap fuel node
  match leaves.find? (fun l => Pure.convert fuel l.base lo) with
  | some l => pure l.count
  | none =>
    let loN := Term.natOf? (Pure.nf fuel lo)
    let hit := leaves.findSome? (fun l =>
      match loN, Term.natOf? (Pure.nf fuel l.base), Term.natOf? (Pure.nf fuel l.count) with
      | some i, some b, some m => if b ≤ i && i < b + m then some (Term.nat (b + m - i)) else none
      | _, _, _ => none)
    match hit with
    | some c => pure c
    | none =>
      throwErr s!"a[{lo.pretty} ; ..]: no segment of {node.pretty} starts at {lo.pretty}, and the offsets are not concrete enough to read the remainder off the extent map — carve the prefix first"

/-- Resolve a place term to a `Pos`, CARVING as it descends so that each array step's
    request is a segment of its own by the time the next step looks. Resolution and
    carving are one pass rather than two, because `a[lo ; ..]` must read its count off
    the extent map of the *already-carved* prefix.

    Every place-consuming rule goes through this one door, so no rule can forget to
    carve. A path with no array step never reaches a carve at all, which is why §2's
    traces are unaffected. Errors on any non-place shape, which is exactly how ⇐ and
    `&mut` reject writes and borrows of arbitrary expressions. -/
def placeToPos (fuel : Nat) : Term → M Pos
  | .var x => pure ⟨x, []⟩
  | .deref t => do let p ← placeToPos fuel t; pure ⟨p.root, p.path ++ [.peel]⟩
  | .index t i ev => do
    let p ← placeToPos fuel t
    let iv ← readC fuel i
    let evv ← ev.mapM (fun e => readC fuel e)
    carveAt fuel p iv (Term.nat 1) none evv none true
    pure ⟨p.root, p.path ++ [.idx iv evv]⟩
  | .range t lo cnt rest ev eqc => do
    let p ← placeToPos fuel t
    let lov ← readC fuel lo
    let cntv ← match cnt with
      | some c => readC fuel c
      | none => restOfLeaf fuel p lov
    let restv ← rest.mapM (fun r => readC fuel r)
    let evv ← ev.mapM (fun e => readC fuel e)
    let eqv ← eqc.mapM (fun e => readC fuel e)
    carveAt fuel p lov cntv restv evv eqv false
    pure ⟨p.root, p.path ++ [.rng lov cntv evv]⟩
  | _ => throwErr "place: target is not a place (must be a variable under * peels and array steps)"

/-- **Rejoin is merge** (¶3.3): restore canonical form once a place operation has
    finished with a slot. There is no rejoin rule to invoke — when the last marker
    under an array node is gone the segments simply collapse, and the array is a run
    again, indistinguishable from one that was never carved.

    Placing it at the END of every place-consuming rule is what makes ¶3.3's
    mechanization caveat moot rather than handled: merge "must be robust to being
    triggered mid-body by a comptime read, not only by owner demand or the boundary",
    and the way to be robust to a trigger list is to not have one. A carve merges
    before it scans and every operation merges after it finishes, so no site can be
    forgotten. Cheap and total on non-array values. -/
def mergeRoot (root : Var) : M Unit := do
  match findSlot? (← getEnv) root with
  | some kv => setSlot root (Val.mergeArrays kv.2)
  | none => pure ()

/-- The syntactic root of a place, without navigating (or carving) it. The fence
    must fire *before* a place expression reorganizes anything, so it cannot go
    through `placeToPos`. -/
def placeRoot? : Term → Option Var
  | .var x => some x
  | .deref t => placeRoot? t
  | .borrow t => placeRoot? t
  | .index t _ _ => placeRoot? t
  | .range t _ _ _ _ _ => placeRoot? t
  | _ => none

/-- **The fence.** Reject a ⇒-use of a comptime binder, naming the use. -/
def fenceComptime (x : Var) (what : String) : M Unit :=
  if x.isComptime then
    throwErr s!"fence: '{x.name}' is a COMPTIME binder (capitalized — §6) and {what}. A comptime binder is erased: it is never moved, never scrutinized, never borrowed or written through, and exists only in ⇝-positions (types, proofs, and the capital argument positions of other calls). If it must exist at runtime, lower-case it — unless it holds a FUNCTION, which cannot be lower-cased (§2.1: functions are comptime), in which case the binder to capitalise is the destination's."
  else pure ()

/-- **The fence at a Σ chain's TAIL** (M33's Σ0, suspensions.md §2.7), and it
    exists because of a UX finding rather than a soundness one.

    M33a's migration report: today's tail is INVISIBLY special. A six-component
    chain reads uniformly for five components — each says its mode with its
    binder's case — and then silently reverts to ⇒ at the sixth, because the tail
    has no binder to say anything with. What the programmer then sees is
    `fenceComptime`'s sentence, which names the CONSEQUENCE ("'Cnt' … cannot be
    ⇒-moved", advice: "lower-case it") and not the POSITION, and whose advice is
    wrong here: lower-casing `Cnt` would be lower-casing a proof to satisfy a
    marker that should have been on the type.

    So the tail says it itself. Reached only from `readResult`'s Σ rule, at the
    second component of the INNERMOST Σ — a codomain that is another Σ is not a
    tail, and a codomain that is `⇝` is a Σ0 and needs no sentence. -/
def tailFence (fuel : Nat) (cod : Term) (b : Term) : M Unit := do
  match Pure.whnf fuel cod with
  | .cmpT _ => pure ()                      -- Σ0: the tail is comptime, nothing to say
  | .sigmaT _ _ _ => pure ()                -- not the tail: another component follows
  | _ =>
    match b with
    | .var x =>
      if x.isComptime then
        throwErr s!"the TAIL of a Σ chain is runtime-moded, and '{x.name}' is a COMPTIME binder (capitalized — §6), so returning it here would ⇒-move erased knowledge. This is the one position in a Σ with no binder: every component before it spells its mode with its binder's case, and the tail can only spell it on the TYPE. Write the innermost former as `Σ0 (x : A). P` instead of `Σ (x : A). P` — the `0` marks the SECOND projection comptime (DLLBC's subset type, Lean's Subtype), after which the tail is ⇝-read, erased, and never moved."
    | _ => pure ()

-- **`isFnValue` IS DELETED TOO** (M33b), with its one caller. Its docstring
-- carried R3's seven-binding measurement and the blocker it recorded — "what has
-- to move first is a Σ component's binder mode … after which a returned proof can
-- be capital and this exclusion can go". That moved at R3b, the exclusion went at
-- M33 Σ0's terminal attempt, and the rule the predicate served goes here. The
-- measurement itself survives where it belongs, in suspensions.md §2.5 and the
-- R3/R3b addenda.


-- **`refuseFnBinding` IS DELETED** (M33b), and with it the last of Stage A's
-- three backstops. §2.5 promised it would become derivable once ⇒ could not
-- construct a function; M33 Σ0 made that law and MEASURED that it did not —
-- neutralising the rule red exactly one assertion, `Functions.m1`'s `let g = ih`,
-- where a function is not constructed but COPIED out of one runtime slot into
-- another. Σ0 named the deeper repair in the same breath: "`ih` is a binder
-- holding a function and should be `Ih`".
--
-- That is done. `fnElab` mints `Ih` wherever the self-view holds a function, the
-- corpus's hand-written arms follow, and `let g = Ih` is now a ⇒-MOVE of a
-- capital binding — which `fenceComptime` refuses one layer earlier, in a message
-- that ends with this very fix. Re-measured with the rename in place: the whole
-- corpus is green with the rule neutralised, so the site is empty and the rule
-- goes.
--
-- What survives is the pair of refusals that IS the law: `readR`'s λ arm (a
-- function WRITTEN) and the pure lift's λ case (a function COMPUTED), plus
-- `fenceComptime` for a function COPIED. Three ways to arrive, three refusals,
-- none of them a backstop.

/-! ## The mode backstop's SCATTER is gone (M32 R3, suspensions.md §2.5)

    Stage A enforced "a function may not land in a runtime binding" at THREE
    sites — `backstopFnRhs` (before a `let`'s right-hand side was evaluated),
    `backstopFnBinding` (after), and `bindFields` (a constructor field). §2.5
    predicted all three would go, because with λ formation ⇝-only "⇒ can no
    longer construct a function value". What landed is ONE site, and the two
    that went, went for different reasons:

      * **`backstopFnRhs` is deleted.** It existed only to improve a message:
        `let g = F` is a ⇒-read of a capital binder, `fenceComptime` gets there
        first, and its advice ("lower-case it") is wrong when the value is a
        function. R3 takes the trade — the rule the program breaks IS erasure,
        so `fenceComptime` should be the one to say so — and widens that
        message instead, so the advice survives where the check does not.
        (`S31A.f1read`/`f2read` assert the new sentence.)
      * **`bindFields`' site is deleted** because it is unreachable, not because
        it is redundant. Putting a function in a constructor field requires
        ⇒-reading one, and the only bindings that hold one are capital, which
        `fenceComptime` refuses. Asserted rather than argued (`S32Backstop`).
      * **`backstopFnBinding` — renamed `refuseFnBinding` — SURVIVED R3 and R4
        and M33 Σ0, and is DELETED at M33b.** It outlived §2.5's prediction by
        two milestones, and each time for a reason worth having: R3 because ⇒
        still constructed function values (a proof of a ∀-statement is a λ); Σ0
        because law about CONSTRUCTING one says nothing about COPYING one, which
        is what `let g = ih` does. M33b removes the site rather than the rule:
        the arm binder that held a function is `Ih` now, so the copy is a ⇒-move
        of a capital binding and `fenceComptime` refuses it a layer earlier.
        Measured, with the rename in place: the corpus is green with the rule
        neutralised.

    **So the scatter is not reduced but GONE**, and what enforces §2.1 is three
    refusals that each name a way a function can arrive — WRITTEN (`readR`'s λ
    arm), COMPUTED (the pure lift's λ case), COPIED (`fenceComptime`). None of
    them is a backstop; each is the rule at the event it is about. -/

/-- Weak-head a store value: knowledge reduces, state is already a head. -/
def whnfV (fuel : Nat) (v : Val) : Val :=
  match v with
  | .know t => .know (Pure.whnf fuel t)
  | v => v

/-- …and the same at a place expression, keyed on the place's root. -/
def fencePlace (t : Term) (what : String) : M Unit :=
  match placeRoot? t with
  | some x => fenceComptime x what
  | none => pure ()

/-- **⇐ (write)** — the fill-only write arrow, defined only on places. Its
    premise is a vacant (⊥) target; when the target is live a **drop** is
    forced first (§2.3), vacating it, then the value drops in. We vacate the
    slot *before* dropping so drop's Ω-scans never see a stale copy of the
    displaced value.

    **A parked loan is demanded first, and ⇐ says so itself** (M29 δ, paper
    finding 15). §5.2's standing rule is that every demand collapses first, and
    overwriting a place is a demand on it exactly as reading one is — but the two
    arrows used to disagree about that. `readR`'s `.var` case ends a parked loan
    through `endLoan`, which is GROUP-AWARE: if ℓ is a call's captured loan, the
    whole §6.1 cascade runs (issued borrows audited and ended, then the captured
    released). ⇐ had no such step, so the marker reached `drop`, whose
    `.loanMarker` case ends it with `killBorrowInΩ` directly — no group check —
    and a captured loan's borrow is by definition NOT an Ω entry, since the callee
    holds it. The result was a read/write asymmetry on a group-captured owner:
    `let y = a` after `keep(&m a)` was ACCEPTED, `a := 5` was rejected with "its
    other end is in flight — cannot end". Measured both ways before the fix.

    **The demand belongs here and not in `drop`, for two independent reasons.**
    `drop` is defined above `hasType`, and `endLoan` must live below it (a group
    end audits each issued borrow's payload against its owed type) — so `drop`
    cannot reach `endLoan` where it sits. And even if it could, it is called on a
    value this function has ALREADY vacated from Ω, while `endLoan` plugs the
    payload back into the marker's Ω entry: it would fail at
    `sendPayloadToLoan` with "loan is not an entry of Ω" instead. Ending BEFORE
    the vacate is what makes the marker's slot still be there to plug into.

    **End, then retry** — the same shape `readR`'s `.var`, `.deref`, `.borrow` and
    match-scrutinee cases all use, and the reason this is an extension rather than
    a change: for an ORDINARY (non-group) loan the two routes reach the same Ω.
    Ending sends the payload home to this very place and the retry then drops an
    ownership-free value, where before the vacate-then-drop put the payload into
    the displaced value and discarded it. Same final Ω, verified — no golden trace
    moves. What is new is only that a GROUP-captured marker now takes the cascade
    it always took under ⇒. A completeness fix: it admits programs, and refuses
    none that were admitted. -/
def writeR : Nat → Term → Val → M Unit
  | 0, _, _ => throwErr "writeR: out of fuel"
  | fuel + 1, place, newval => do
    -- §6's fence, before the place is navigated: a write through a comptime binder
    -- would make an erased thing observable, and `placeToPos` may carve.
    fencePlace place "cannot be written through (⇐)"
    let pos ← placeToPos (fuel + 1) place
    -- `displaced` rather than `old`: `old` is a SURFACE keyword (`old *v`, §5.4's
    -- entry snapshot), and since M33 macro-top the surface sits below the kernel,
    -- so its tokens are reserved here too.
    let displaced ← getAtPos (fuel + 1) pos
    match displaced with
    | .bot => do setAtPos (fuel + 1) pos newval; mergeRoot pos.root    -- fill
    | _ =>
      -- §5.2: every demand collapses first. A `borrowM` in the displaced value is
      -- NOT one of these — `firstLoanMarker` is `none` on it — so the
      -- send-the-payload-home half of `drop` is reached exactly as before.
      match firstLoanMarker displaced with
      | some ℓ => do endLoan fuel ℓ; writeR fuel place newval
      | none => do
        setAtPos (fuel + 1) pos .bot                 -- vacate first (no stale copy in Ω scans)
        drop (fuel + 1) displaced                    -- drop the displaced value
        setAtPos (fuel + 1) pos newval               -- fill
        mergeRoot pos.root                           -- rejoin is merge (¶3.3)

/-! ## Match branch selection (§3)

    These set up Ω for a branch and return the body term to evaluate; they do
    not call `readR`, so they stay outside the read recursion. `readR`'s match
    case reorganizes the scrutinee, then calls one of these, then reads the
    returned body. -/

/-! ## The ⇝-side demand-end (M23)

    §5.2 makes `*b` under ⇝ a **projection**, defined only on a proper payload: "a
    *suspended* borrow, its payload holding loan markers mid-§3.3, has no meaningful
    snapshot, and comptime deref is stuck on it until the reborrows end." §2's
    standing convention says who is supposed to arrange that — reorganization is
    lazy and fires "when some rule's premise demands it" — and "the payload is
    proper" is exactly such a premise. Nothing was firing it, so the projection
    silently returned the `loanₘ` itself.

    That matters the moment a body proves something about a call it just made. M23's
    `append_back` hands `&mut *tl` to its recursive call and must then NAME the
    released value to apply a congruence — `*tl` is the only way to name it — and a
    `loanₘ` rode into the proof term, surfacing layers later as an untypeable audit
    failure. It is the same silent-marker class as the `⊥`-into-a-pure-value bug
    §3.2 records, and the fix is the ⇝ counterpart of the `&mut`-on-a-parked-loan
    demand-end M22-a already added for the reborrow path. -/

/-- Resolve a PEEL-ONLY place term without throwing (`placeToPosRaw`'s total
    sibling). An array place is `none`: this pre-pass exists to demand-end what a
    comptime read is about to project through, and a range place's own collapse is
    the carve's business, not this walk's. -/
def placeOf? : Term → Option (Var × Nat)
  | .var x => some (x, 0)
  | .deref t => (placeOf? t).map (fun p => (p.1, p.2 + 1))
  | _ => none

/-- Peel `n` borrow layers, or `none` if the value is not a borrow that deep. -/
def peek? : Nat → Val → Option Val
  | 0, v => some v
  | n + 1, .borrowM _ p => peek? n p
  | _, _ => none

/-- Demand-end the loans parked at the places a comptime read is about to project
    through, innermost place first. Outside a place shape this is a plain structural
    walk; a place whose slot is unbound or not a borrow that deep is left alone (the
    read itself will produce the honest error).

    A bare `.var` counts as a place (M23). `let hs = quicksort(f, &mut hi, …)` parks
    `loanₘ ℓ` in `hi`'s own slot, and a body that then names `hi` in a proof — `count
    n hi`, the only way to say what the callee left there — must collapse it first,
    for exactly the reason the deref case must. The `⇒` side has always done this
    (`readR`'s `.var` move ends a marker before moving); without it here the two
    arrows disagree about the same slot and the pure read silently yields the marker. -/
partial def collapseCDerefs (fuel : Nat) : Term → M Unit
  | .var x => do
    match findSlot? (← getEnv) x with
    | some ⟨_, .loanM ℓ⟩ => do endLoan fuel ℓ; collapseCDerefs fuel (.var x)
    | _ => pure ()
  | .deref inner => do
    collapseCDerefs fuel inner
    match placeOf? (.deref inner) with
    | none => pure ()
    | some (root, d) =>
      match findSlot? (← getEnv) root with
      | none => pure ()
      | some kv =>
        match peek? d kv.2 with
        | some (.loanM ℓ) => do endLoan fuel ℓ; collapseCDerefs fuel (.deref inner)
        | _ => pure ()
  | .app f a => do collapseCDerefs fuel f; collapseCDerefs fuel a
  | .ctorApp _ args => args.forM (collapseCDerefs fuel)
  | .idT a b c => do collapseCDerefs fuel a; collapseCDerefs fuel b; collapseCDerefs fuel c
  | .lam _ d b => do collapseCDerefs fuel d; collapseCDerefs fuel b
  | .pi _ d b => do collapseCDerefs fuel d; collapseCDerefs fuel b
  | .sigmaT _ d b => do collapseCDerefs fuel d; collapseCDerefs fuel b
  | .cmpT τ => collapseCDerefs fuel τ                    -- M33a: ⇝ is transparent here
  | .letIn _ rhs rest => do collapseCDerefs fuel rhs; collapseCDerefs fuel rest
  | _ => pure ()

/-- Find the branch whose constructor name matches `name`. -/
def findBranch (branches : List Branch) (name : String) : Option Branch :=
  branches.find? (fun b => b.ctor == name)

/-- **Does this arm body carry a seam?** (M31 Stage 0.) The lazy seam builders
    (`pushJoinArms`/`pushJoinArmsSeq`) mark every arm they fuse with a
    continuation by wrapping its body in `@armScope`, and the mark is what the
    arm's scope is TAGGED with when it opens. A joining match's arms carry no
    mark — they are checked terminally and their states end at the seam.

    The tag is load-bearing rather than decorative, and the case that forces it is
    an arm whose body ends in a TAIL-position match: at the seam, the open scopes
    are that inner arm's and this one's, and the seam must take both — the inner
    arm has no continuation of its own to close it. So "unwind to the innermost
    arm" is the wrong rule and "unwind to the innermost arm THAT OWNS A SEAM" is
    the right one; nothing in the mark stack could distinguish the two, because
    which arm a seam belongs to is a fact about the TERM. Hence the announcement,
    written at the one place that knows. -/
def armSeamed? : Term → Bool
  | .seq (.const "@armScope") _ => true
  | _ => false

/-! ## §2.1's convention reaches the MATCH ARM (M33a)

    Every binder spells its mode. A match arm's binders are binders, and until
    here they were the last position where the spelling was unread: a `Pair`
    destructure could bind a comptime component — an erased proof — at a
    lowercase name, which is the runtime-binding-holds-knowledge state the `let`
    refuses (`fenceComptime`; `refuseFnBinding` beside it until M33b deleted it),
    reached by a rule that was not looking.

    The check is BOTH directions, because they are two different mistakes:

      * a CAPITAL arm binder over a runtime data component claims erasure of
        something that moves — the component is `⇒`-read into the binder, and a
        capital binding is one the fence then refuses to move again;
      * a LOWERCASE arm binder over a comptime component is the mis-moded state
        above.

    **Where the mode comes from, and why this is not a second type derivation.**
    `Pure.ctorSig` is the fixed constructor basis, and it splits: `Pair` is the
    only constructor whose field modes are not a fact about the constructor
    itself. `Cons`' head and tail, `S`'s predecessor, `Arr`'s elements are DATA
    at every type there is, so a capital binder over one is refusable with no
    type in hand at all. `Pair`'s first field is a Σ's component and takes that
    Σ binder's mode — which the match already holds, on the field: a component
    σ's `sctx` entry is `⇝τ` exactly when the component is comptime
    (`buildResult` on the concrete path, `reattachSigmaMode` on the symbolic
    one). One lookup in a context the match consults anyway.

    `.unknown` is the honest third answer rather than a rounded-up one: a `Pair`
    field that is not a σ — a component built and destructured inside one body,
    a concrete constructor tree — has no mode recorded anywhere, and refusing on
    a guess would be a false rejection. Nothing is checked there, and the
    close-out says so. -/
inductive CompMode where
  | data
  | comptime
  | unknown
  deriving BEq

/-- The mode of the component a match is about to bind. See the note above. -/
def componentMode (ctor : String) (field : Val) : M CompMode := do
  if ctor != "Pair" then
    pure (if (Pure.ctorSig ctor).isSome then .data else .unknown)
  else
    match field.symOf? with
    | none => pure .unknown
    | some σ =>
      match (← get).sctx.lookup σ with
      | none => pure .unknown
      | some τ => pure (if Term.domComptime τ then .comptime else .data)

/-- **The arm-binder mode check** (M33a, suspensions.md §2.1). Runs at every
    match that binds arm binders to components, in both modes, on both the
    concrete and the symbolic path. -/
def checkArmModes (ctor : String) : List Var → List Val → M Unit
  | [], _ => pure ()
  | _, [] => pure ()
  | x :: xs, v :: vs => do
    match ← componentMode ctor v with
    | .data =>
      if x.isComptime then
        throwErr s!"match: arm binder '{x.name}' is capitalized (comptime, §6) but the component of '{ctor}' it binds is runtime DATA. A comptime binder is erased and never moved, and this one receives a value that the match moves into it — lower-case the arm binder."
    | .comptime =>
      if !x.isComptime then
        throwErr s!"match: arm binder '{x.name}' is lowercase (runtime, §6) but the component of '{ctor}' it binds is COMPTIME — the producing Σ binds it capital, so the value is erased knowledge and there is nothing for a runtime binding to hold. Capitalise the arm binder."
    | .unknown => pure ()
    checkArmModes ctor xs vs

/-- Bind constructor fields to fresh binder entries (owned mode: the fields
    move in as owned values). Errors on arity mismatch. -/
def bindFields : List Var → List Val → M Unit
  | [], [] => pure ()
  -- (The backstop's third acquisition site was here — M31 Stage A, E1 — and went
  -- with the rest of it at M32 R3: a constructor field cannot hold a function,
  -- because nothing could have put one there.)
  | x :: xs, v :: vs => do bindSlot x v; bindFields xs vs
  | _, _ => throwErr "match: constructor arity mismatch (binders vs fields)"

/-- Bind each field binder to a whole-value reborrow `borrowM ℓᵢ fieldᵢ`
    (borrow mode, §3.3). Errors on arity mismatch. -/
def bindBorrowFields : List Var → List Nat → List Val → M Unit
  | [], [], [] => pure ()
  | x :: xs, ℓ :: ℓs, v :: vs => do bindSlot x (.borrowM ℓ v); bindBorrowFields xs ℓs vs
  | _, _, _ => throwErr "match: constructor arity mismatch (borrow mode)"

/-- Bind a **branch equation** whose two endpoints are already identical, i.e.
    `Refl` inhabits it (M23). That is the case for every split except the stuck
    one: on a concrete scrutinee the branch IS the value's constructor, and on a
    plain symbolic σ the ⇜ refinement has just rewritten the pre-split value to
    this very constructor tree. The equation only carries new information where
    the pre-split value was ABSTRACTED away rather than refined — the stuck
    spine, handled in `symOwnedSetup`. -/
def bindEqnRefl (eqn : Option Var) : M Unit :=
  match eqn with
  | none => pure ()
  | some h => bindSlot h (.ctor "Refl" [])

/-- **Owned mode** (§3.1): ⇒-consume the scrutinee (slot → ⊥), select the
    branch by head constructor, move the fields into fresh binders, and return
    the branch body. -/
def ownedSelect (scrut : Var) (eqn : Option Var) (branches : List Branch) (name : String)
    (fields : List Val) : M Term := do
  match findBranch branches name with
  | none => throwErr s!"match: no branch for constructor '{name}' (scrutinee {scrut.name}#{scrut.id})"
  | some br => do
    noteArm scrut br.ctor
    checkArmModes name br.binders fields       -- M33a: §2.1 reaches the arm
    openScope (armSeamed? br.body)             -- M31 Stage 0: the arm is a scope
    setSlot scrut .bot                         -- ⇒-consume
    bindFields br.binders fields
    bindEqnRefl eqn
    pure br.body

/-- **Borrow mode** (§3.3): the binders become reborrows of the fields. Mint a
    fresh loan ℓᵢ per field, park a `loanM ℓᵢ` in the parent's payload (which
    suspends the parent — no rule reads through a loan), bind each binder to
    `borrowM ℓᵢ fieldᵢ`, and return the branch body. -/
def borrowSelect (scrut : Var) (eqn : Option Var) (branches : List Branch) (ℓ : Nat) (name : String)
    (fields : List Val) : M Term := do
  match findBranch branches name with
  | none => throwErr s!"match: no branch for constructor '{name}' (scrutinee {scrut.name}#{scrut.id})"
  | some br => do
    noteArm scrut br.ctor
    if br.binders.length != fields.length then
      throwErr "match: constructor arity mismatch (borrow mode)"
    checkArmModes name br.binders fields       -- M33a: §2.1 reaches the arm
    openScope (armSeamed? br.body)             -- M31 Stage 0: the arm is a scope
    let ℓs ← fields.mapM (fun _ => freshLoan)
    setSlot scrut (.borrowM ℓ (.ctor name (ℓs.map Val.loanM)))   -- suspend the parent
    bindBorrowFields br.binders ℓs fields
    bindEqnRefl eqn
    pure br.body

/-! ## Peeling a borrow-moded Π into a telescope (M26-C)

    **`piPeel` moved DOWN to `Syntax.lean` at M33 macro-top**, where its
    docstring now lives. It is a function of `Term` and nothing else, and it was
    the single real edge from the macro layer up into the kernel: `fnElab` peels
    the sealed Π with it, so `FnMacro` had to import `Machine` in order to reach
    one address. With it below, the surface sits under the kernel and the
    dependency runs the way the layering says it should. Nothing about the rule
    changed — the mode agreement check is still the one place §6 could be stated
    twice and disagree, and it is still stated once. -/

/-- **The seal's one conversion** (M27 α.1b): an annotated runtime λ's binders
    against the ascribed Π.

    This is what `piPeel` becomes once the λ carries its own domains. `piPeel`
    SUPPLIED each binder a type — a bidirectional descent, the ascription pushing
    inward — and this AGREES with the type the λ already states. The λ synthesizes
    its telescope; the ascription supplies the one thing a body cannot synthesize,
    its return type; and what happens at each binder is a comparison.

    **Syntactic, on the same reasoning `sealRec` gives for the motive**: "the
    motive contains borrow types, which have no `Val` and therefore no conversion
    to be compared up to". A binder domain is where the borrow types actually LIVE
    (`&mut (s : τ ↝ τ')` is a telescope-position form and nothing else), so a
    conversion up to computation is not merely unimplemented here — for the
    domains that matter it is unaskable. One rule, applied everywhere, rather than
    conversion where a `Val` happens to exist and syntax where it does not.

    The mode is compared before the domain because its diagnosis is different in
    kind: a mode disagreement is a claim about what callers were promised, not a
    mistyped binder, and it earns its own sentence.

    Returns the telescope with the mode marker stripped — the shape
    `seedTelescopeV` seeds and `auditAction` audits, and the same shape `piPeel`
    returned, so what changed at the call sites is the CHECK and not the data. -/
def piAgree : List (Var × Term) → Term → Except String (List (Var × Term) × Term)
  | [], u => .ok ([], u)
  | (x, τ) :: xs, u =>
    match u with
    | .pi y dom cod =>
      if Term.domComptime dom != x.isComptime then
        .error s!"seal: binder '{x.name}' is {if x.isComptime then "capitalized (comptime, §6)" else "lowercase (runtime, §6)"} but the ascribed type binds it as {if Term.domComptime dom then "comptime (⇝τ)" else "runtime"}. A binder's mode is a claim about whether the body may observe its argument at runtime, and the ascription is what callers are promised — the two cannot differ."
      else if !(Term.alphaEq dom.stripCmp τ.stripCmp) then
        .error s!"seal: binder '{x.name}' is annotated with a domain the ascription does not bind it at. A λ states its own binder types and the seal converts that Π against what was written (§5 point 4: the ascription is the contract), so the two cannot differ — either the annotation is wrong or the ascription is."
      else
        match piAgree xs (Term.substP y (.var x) cod) with
        | .ok (rest, ret) => .ok ((x, τ.stripCmp) :: rest, ret)
        | .error e => .error e
    | _ =>
      .error s!"seal: the runtime λ binds '{x.name}' but the ascribed type has no Π binder left for it. Runtime application is saturated (§12 decision 4), so a λ and its ascription must have the same arity — either the λ binds too much or the ascription promises too little."

/-- Synthesized binder names for a Π that has none — the `ih` case (§7 cost 1),
    where the sealed self-view at the predecessor arrives as a TYPE and a
    telescope has to be derived from it.

    The case matters and is not cosmetic: §6 makes capitalisation the binder-mode
    marker, and `piPeel` checks that a name's case agrees with its domain's, so a
    comptime domain must be given a capitalized name or the derived telescope
    would contradict the type it was derived from. -/
def piBinderNames (t : Term) : List Var :=
  let rec go : Nat → Nat → Term → List Var
    | 0, _, _ => []
    | fuel + 1, i, .pi _ dom cod =>
      Var.mk i (if Term.domComptime dom then s!"A{i}" else s!"a{i}") :: go fuel (i + 1) cod
    | _, _, _ => []
  go 64 0 t

/-- A Var-keyed telescope's borrow parameters, by var id (`borrowParamIds`'
    counterpart for a telescope that brought its own names). -/
def borrowVarIds (tel : List (Var × Term)) : List Nat :=
  tel.filterMap (fun p => match p.2 with | .borrowT _ _ _ => some p.1.id | _ => none)

/-- **The return type an ENTERED callee's tail is read against** (M33 Σ0's
    prerequisite, suspensions.md §2.7) — the executing machine's counterpart of
    the `retTyVal` that `checkRFnBody` pins.

    The closure carries the ascribed Π; peeling one binder per parameter leaves
    the return type, which is what `readResult` consults for a returned `Pair`'s
    component MODES. Two deliberate differences from the checking side, each
    because this is EXECUTION and execution does not verify:

      * a `piPeel` failure is `none`, not a rejection. `piPeel` re-checks the
        binder/domain mode agreement, and that check belongs to the seal; a
        program that got here was already accepted, and re-refusing it at every
        call would be the checker's rule enforced twice, in the one place M33a
        recorded that doing so "breaks running programs to protect a checker".
      * the type is left RAW — not `readC`'d, not `markExit`'d. What is wanted
        from it is the Σ binders' modes, and those survive evaluation of a term
        with free runtime `.var`s untouched (`Pure.eval` leaves an unbound `.var`
        stuck and `.cmpT`/`.sigmaT` structural). `markExit` is §5.4's exit-snapshot
        transform, which is about a symbolic audit and means nothing here.

    A borrow-carrying return type gets `none`: `retMixesBorrow` already forbids
    mixing borrow and value components, so such a type has no comptime component
    to find, and `hasBorrowT` is the same guard `checkRFnBody` puts in front of
    its own pin. -/
def calleeRetTy (names : List Var) : Option Term → Option Term
  | none => none
  | some u =>
    match piPeel names u with
    | .error _ => none
    | .ok (_, ret) => if hasBorrowT ret then none else some ret

/-- **Selecting a match's branch, as ONE rule with two drivers** (M33 Σ0's
    prerequisite). This is `readR`'s `.matchE` case with the continuation lifted
    out: it fences, reorganizes a suspended scrutinee (End-Mut, then retry), picks
    the branch, binds its fields, and returns the BODY to go on with — leaving
    "and then read that body" to the caller, which is the only thing `readR` and
    the tail-typed `readRTail` disagree about.

    Extracted rather than duplicated because the alternative was a third copy of a
    30-line rule; the two retries stay recursion here, on the same decreasing
    fuel they had when they were `readR fuel (.matchE …)`. -/
def matchStep : Nat → Var → Option Var → List Branch → M Term
  | 0, _, _, _ => throwErr "match: out of fuel"
  | fuel + 1, scrut, eqn, branches => do
    -- §6's fence. A runtime match on a comptime binder is the erasure
    -- violation the fence exists for: it is the rule that would make an
    -- erased value's CONSTRUCTOR observable to ⇒ (and, in borrow mode, would
    -- reborrow its fields). Scrutinize it in a type or a proof instead.
    fenceComptime scrut "cannot be the scrutinee of a runtime match"
    -- Mode is chosen by what the scrutinee's slot holds, after the usual
    -- lazy reorganization. Both retries decrease fuel.
    match ← lookupSlot scrut with
    | .bot => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} holds ⊥ (use-after-move)"
    | .borrowM ℓ payload =>
      match Val.asCtor? payload with
      | some (name, fields) => borrowSelect scrut eqn branches ℓ name fields
      | none =>
        match payload with
        | .loanM ℓ' => do endLoan fuel ℓ'; matchStep fuel scrut eqn branches  -- reborrowed payload: end, retry
        | .bot => throwErr s!"match: matching through a hole (⊥) at {scrut.name}#{scrut.id}"
        | .borrowM _ _ => throwErr s!"match: scrutinee payload is a nested borrow (unsupported in §3)"
        | p =>
          if p.symOf?.isSome then
            throwErr s!"match: symbolic scrutinee {scrut.name}#{scrut.id} in expression position — only a statement-position match may split (use the explore driver)"
          else throwErr s!"match: scrutinee {scrut.name}#{scrut.id} payload is not a constructor"
    | v =>
      match firstLoanMarker v with
      | some ℓ => do endLoan fuel ℓ; matchStep fuel scrut eqn branches  -- suspended owner: end, retry
      | none =>
        match Val.asCtor? v with
        | some (name, fields) => ownedSelect scrut eqn branches name fields
        | none =>
          if v.symOf?.isSome then
            throwErr s!"match: symbolic scrutinee {scrut.name}#{scrut.id} in expression position — only a statement-position match may split (use the explore driver)"
          else throwErr s!"match: scrutinee {scrut.name}#{scrut.id} is not a constructor value"

/-! ## The symbolic driver and the boundary audit (relocated here, M26-C)

    These lived below `readR` (the driver) and in `Boundary.lean` (the audit)
    while nothing above them needed them. M26-C's seal rule does: checking
    `.seal t u` at a borrow-moded Π **is** §5.4's audit — seed a telescope,
    explore the body (one path per symbolic branch), audit each path at return —
    and that check happens AT THE NODE (§5), which is inside `readR`. So `readR`
    and `explore` are genuinely mutual now, and everything the audit needs has to
    precede them.

    This is the shape §8 is heading for anyway: once a program is a term,
    checking one is the symbolic ⇒-walk of it, and the walk and the reader are
    one thing. Nothing below is changed from where it was — the relocation is
    mechanical, and its commit carries no behaviour change so that a regression
    stays bisectable. `auditPaths` and `checkFn` stay in `Boundary`: they sit
    above the mutual block rather than inside it. -/

/-! ## The symbolic driver (§3.2): matching a symbolic scrutinee splits the run

    The four arrows stay single-path in `M`; a driver on top owns the split.
    A statement-spine pre-pass makes every match terminal, then `explore`
    walks the spine — non-match steps delegate to the `M` machinery, and a
    terminal match on a symbolic scrutinee forks one path per branch. -/

/-- What a match scrutinee resolves to after lazy reorganization. -/
inductive Dispatch where
  | ownedCtor  : String → List Val → Dispatch        -- owned concrete constructor
  | borrowCtor : Nat → String → List Val → Dispatch  -- borrow mode, loan ℓ + payload ctor
  /-- Owned symbolic value `sym σ`. The `Option Val` is the **pre-abstraction
      spine** when σ was minted by `generalizeStuck` from a stuck scrutinee —
      the one split where the branch equation says something the refinement
      does not (M23); `none` for an ordinary σ, whose equation is `Refl`. -/
  | ownedSym   : Nat → Option Term → Dispatch
  | borrowSym  : Nat → Nat → Dispatch                -- borrow mode, loan ℓ + payload sym σ

/-- Reorganize a match scrutinee (exactly as `readR`'s match would — End-Mut a
    suspended owner or a reborrowed payload, innermost first) and classify what
    it holds. Fuel bounds the reorganize-retry loop. -/
def reorgScrut : Nat → Var → M Dispatch
  | 0, _ => throwErr "match: out of fuel (scrutinee reorganization)"
  | fuel + 1, scrut => do
    match ← lookupSlot scrut with
    | .bot => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} holds ⊥ (use-after-move)"
    | .borrowM ℓ payload =>
      match payload.symOf?, Val.asCtor? payload with
      | _, some (name, fields) => pure (.borrowCtor ℓ name fields)
      | some σ, _ => pure (.borrowSym ℓ σ)
      | _, _ =>
        match payload with
        | .loanM ℓ' => do endLoan fuel ℓ'; reorgScrut fuel scrut
        | .bot => throwErr s!"match: matching through a hole (⊥) at {scrut.name}#{scrut.id}"
        | .borrowM _ _ => throwErr s!"match: scrutinee payload is a nested borrow (unsupported in §3)"
        | _ => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} payload is not a constructor"
    | v =>
      match firstLoanMarker v with
      | some ℓ => do endLoan fuel ℓ; reorgScrut fuel scrut
      | none =>
        match v.symOf?, Val.asCtor? v with
        | _, some (name, fields) => pure (.ownedCtor name fields)
        | some σ, _ => pure (.ownedSym σ none)
        -- §19: a stuck spine (`leb σ σp`, a neutral application). Generalize it to
        -- a fresh σb : Bool across all σ-bearing state, then split on σb as an
        -- ordinary owned sym — the True/False refinement rewrites the spine per path.
        -- The spine itself rides along so the branch can bind an equation about it.
        | _, _ =>
          match v with
          | .know (.app f a) => do
            let (σb, sp) ← generalizeStuck fuel (.app f a); pure (.ownedSym σb (some sp))
          | _ => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} is not a constructor or symbolic value"

/-- Mint fresh σ's for the given field types, typing each in `sctx`
    (dependent positions instantiated at earlier fresh σ's — a real telescope).
    Returns the fresh σ ids. -/
def typeFieldSyms (fuel : Nat) : List Var → List (String × Term) → M (List Nat)
  | [], [] => pure []
  | _ :: bs, (x, ty) :: tys => do
    let σ ← freshSym
    modify (fun s => { s with sctx := (σ, ty) :: s.sctx })
    let rest ← typeFieldSyms fuel bs (tys.map (fun e => (e.1, Pure.openBinder fuel x e.2 (Term.sym σ))))
    pure (σ :: rest)
  | _, _ => throwErr "match: constructor arity mismatch (σ-typing)"

/-- **Re-attach the Σ component mode that `ctorSig` deliberately strips** (M33a).

    `Pure.ctorSig "Pair"` hands back `(x, a.stripCmp)` because its callers TYPE
    the field, and `⇝τ` is not a type. `typeFieldSyms` is the caller that does
    something else with it as well: it writes the field's type into `sctx`, and
    that entry is where a match reads the component's MODE from (`componentMode`
    below). The concrete path gets this for free — `buildResult` mints its
    components straight off the return type, so a comptime one's `⇝` rides into
    `sctx` through `readCWith` — and this is the symbolic path paying the same
    fact, so that ONE rule reads both.

    **BOTH ends since M33's Σ0.** What stood here said "only the first component
    takes a mode; a Σ chain's TAIL has no binder to carry one (suspensions.md
    §2.5's surviving spelling), so it is left alone and reads as runtime, which is
    what ⇒ does with it today". That was the residual, stated at the line that
    implemented it. `Σ0 (x : A). P` gives the tail a marker on the CODOMAIN, and
    this is where a destructuring match reads it: `componentMode` needs no case of
    its own, because it already asks `sctx` per field and the tail's entry is now
    written the same way the first component's is. The M33a hook note predicted
    the change would be in `componentMode`; it is one step upstream, at the two
    places that WRITE the mode (here, and `buildResult`, which gets the codomain's
    `⇝` for free by reading the return type through `readCWith`). -/
def reattachSigmaMode : Term → List (String × Term) → List (String × Term)
  | .sigmaT _ dom cod, (x, τ) :: rest =>
    let fst := if Term.domComptime dom then (x, Term.cmpT τ) else (x, τ)
    let rest' := match cod, rest with
      | .cmpT _, (y, σ) :: r => (y, Term.cmpT σ) :: r
      | _, r => r
    fst :: rest'
  | _, ftys => ftys

/-- Mint the field σ's for a symbolic branch. `Refl` is special (§10): it has
    no fields, and it unifies the `Id` endpoints (`reflUnify`) rather than
    consulting the signature table's field types. When the scrutinee's σ has a
    type in `sctx` (§3.2's seam, closed in §5): require the branch constructor
    to be a constructor of that type and type each field σ by the instantiated
    field types. When untyped (pre-telescope), fall back to fresh untyped σ's. -/
def mintFieldSyms (fuel : Nat) (scrutσ : Nat) (br : Branch) : M (List Nat) := do
  match (← get).sctx.lookup scrutσ with
  | none => br.binders.mapM (fun _ => freshSym)     -- untyped scrutinee (M3)
  | some τ =>
    let τw := (Pure.whnf fuel τ).stripCmp
    if br.ctor == "Refl" then
      match τw with
      | .idT _ a b => do reflUnify fuel a b; pure []            -- unify endpoints, no fields
      | _ => throwErr "match: Refl branch on a non-Id scrutinee"
    else match Pure.ctorSig br.ctor with
    | none => throwErr s!"match: unknown constructor '{br.ctor}'"
    | some sig =>
      match sig.fieldTypes τw with
      | none => throwErr s!"match: constructor '{br.ctor}' does not belong to the scrutinee's type"
      | some ftys => typeFieldSyms fuel br.binders (reattachSigmaMode τw ftys)

/-- **The branch equation for a stuck split** (M23) — M18's second layer, on the
    imperative side. At an ordinary split, ⇜ rewrites every OCCURRENCE of the
    scrutinee's value to this branch's constructor, and that is all a body can
    ever need. At a STUCK split it is not: `generalizeStuck` abstracted the spine
    before refining, so a body that recomputes `leb a b` after the split writes a
    term the refinement never saw, and learns nothing (the M23-iv wall). This
    mints the missing hypothesis — a fresh σ typed `Id τ ⟨spine⟩ ⟨C σ₁ … σₙ⟩`,
    the branch's own match-shape knowledge reified as a citable term rather than
    applied only as substitution. Sound for the same reason the substitution is:
    the branch is entered exactly when the scrutinee evaluates to `C`.
    Registered in `sctx` BEFORE the ⇜ fires, so `refineSym` sweeps its type with
    the rest of the σ-bearing state (the M10 invariant). -/
def mintStuckEqn (scrutσ : Nat) (spine : Term) (ctor : String) (σs : List Nat) : M Nat := do
  let σe ← freshSym
  match (← get).sctx.lookup scrutσ with
  | none => pure σe                                      -- untyped scrutinee: untyped equation
  | some τ =>
    modify (fun s => { s with
      sctx := (σe, .idT τ.stripCmp spine (.ctorApp ctor (σs.map Term.sym))) :: s.sctx })
    pure σe

/-- Symbolic **owned** branch entry (§3.2): mint (σ-typed) fresh σ's for the
    pattern fields, ⇜-refine the scrutinee to `C (sym σ₁) … (sym σₙ)`
    *everywhere*, then destructure as owned match (scrutinee → ⊥, binders ↦
    `sym σᵢ`). Returns the branch body. `stuck` carries the pre-abstraction spine
    when there was one; the declared equation binder (M23) is bound to its
    hypothesis, or to `Refl` when refinement has already equated the endpoints. -/
def symOwnedSetup (fuel : Nat) (scrut : Var) (scrutσ : Nat) (stuck : Option Term)
    (eqn : Option Var) (br : Branch) : M Term := do
  noteArm scrut br.ctor
  let σs ← mintFieldSyms fuel scrutσ br
  let eqv : Option Val ← match eqn, stuck with
    | none, _ => pure none
    | some _, none => pure (some (.ctor "Refl" []))
    | some _, some spine => do
      pure (some (.know (Term.sym (← mintStuckEqn scrutσ spine br.ctor σs))))
  let fvs := σs.map (fun σ => Val.know (Term.sym σ))
  checkArmModes br.ctor br.binders fvs                   -- M33a: §2.1 reaches the arm
  openScope (armSeamed? br.body)                         -- M31 Stage 0: the arm is a scope
  writeC (.var scrut) (.know (.ctorApp br.ctor (σs.map Term.sym)))   -- ⇜ everywhere
  setSlot scrut .bot                                     -- owned consume
  bindFields br.binders fvs
  match eqn, eqv with | some h, some v => bindSlot h v | _, _ => pure ()
  pure br.body

/-- Symbolic **borrow** branch entry (§3.3): mint fresh σ's, ⇜-refine the
    payload to `C (sym σ₁) … (sym σₙ)` *everywhere* (refinement first), THEN
    reborrow the fields — the scrutinee payload becomes `C (loanM ℓ₁) …`
    (suspended parent), each binder ↦ `borrowM ℓᵢ (sym σᵢ)`. Order matters:
    ⇜ hits every occurrence of σ across Ω; only the scrutinee payload is then
    rewritten to markers (§3.2 "everywhere"; M5 depends on this). -/
def symBorrowSetup (fuel : Nat) (scrut : Var) (ℓ : Nat) (scrutσ : Nat)
    (eqn : Option Var) (br : Branch) : M Term := do
  noteArm scrut br.ctor
  let σs ← mintFieldSyms fuel scrutσ br
  checkArmModes br.ctor br.binders (σs.map (fun σ => Val.know (Term.sym σ)))  -- M33a
  openScope (armSeamed? br.body)                                 -- M31 Stage 0: the arm is a scope
  writeC (.deref (.var scrut)) (.know (.ctorApp br.ctor (σs.map Term.sym)))  -- ⇜ at payload
  let ℓs ← br.binders.mapM (fun _ => freshLoan)
  setSlot scrut (.borrowM ℓ (.ctor br.ctor (ℓs.map Val.loanM)))   -- suspend the parent
  bindBorrowFields br.binders ℓs (σs.map (fun σ => Val.know (Term.sym σ)))
  -- A borrow payload is a bare σ (a stuck spine has no `&mut`), so the refinement
  -- has already equated the equation's endpoints.
  bindEqnRefl eqn
  pure br.body

/-- **Exhaustiveness** (§9): a match on a *symbolic* scrutinee must cover the
    full constructor set of the scrutinee's type (read from the signature
    table). This is what makes "accepted ⟹ concrete-safe" unconditional — a
    concrete run cannot hit a constructor no branch handles. Skipped when the
    scrutinee σ is untyped (a pre-telescope testing artifact) or its type has
    no known constructor set. A ⊥-typed scrutinee has the empty set, so an
    empty match on it is vacuously exhaustive. Concrete-scrutinee matches are
    NOT checked here — dynamic selection is stuck-prone only on a genuinely
    missing branch, which stays the runtime error it is. -/
def checkExhaustive (fuel : Nat) (scrutσ : Nat) (branches : List Branch) : M Unit := do
  match (← get).sctx.lookup scrutσ with
  | none => pure ()                                   -- untyped scrutinee: skip
  | some τ =>
    match Pure.typeCtors (Pure.whnf fuel τ).stripCmp with
    | none => pure ()                                 -- unknown type: nothing to check against
    | some ctors =>
      let covered := branches.map (·.ctor)
      match ctors.find? (fun c => !covered.contains c) with
      | some missing =>
        throwErr s!"match: non-exhaustive — no branch for constructor '{missing}' of the scrutinee's type"
      | none => pure ()


/-- Seed the telescope into Ω and `sctx`, returning the borrow obligations.
    Argument `i` gets runtime var id `i`. A pure (unrestricted) type τ →
    `x ↦ sym σ`, `sctx[σ : τ]`. A borrow type `&mut (s : τ ↝ τ')` → fresh ℓ and
    σ, `x ↦ borrowM ℓ (sym σ)`, `sctx[σ : τ]`, and an obligation carrying `τ'`
    instantiated at `s := σ`. Crucially there is NO owner entry for an argument
    borrow's loan — the caller holds it; nothing in the body can collapse the
    borrow by owner-demand, only the audit can.

    **Var-keyed** since M26-C, because the seal seeds one too: a `FnDef` names its
    parameters positionally (argument `i` ↦ var id `i`, which is what the corpus's
    types reference), while a runtime λ brings its own binder `Var`s and its body
    reaches them by those ids. Same seeding either way; only who supplies the
    names differs. -/
def seedTelescopeV (fuel : Nat) : List (Var × Term) → M (List Debt)
  | [] => pure []
  | (x, tyTerm) :: rest => do
    let name := x.name
    -- §6, "checked, not assumed": a borrow-typed binder MUST be lowercase. A
    -- comptime binder is ⇝-read at the call and erased in the body, and neither
    -- is meaningful of a `&mut` — there is no ⇝ reading of a borrow, and a loan
    -- that no ⇒-rule may touch can be neither written through nor audited. The
    -- declaration is where this is caught (the call site checks it again, for a
    -- table entry that was never checked).
    if x.isComptime then
      match tyTerm with
      | .borrowT _ _ _ | .sigmaT _ _ (.borrowT _ _ _) =>
        throwErr s!"telescope: parameter '{name}' is capitalized (comptime, §6) but its type is a borrow — a ⇝-read of `&mut` is meaningless, so borrow-typed binders must be lowercase"
      | _ => pure ()
    match tyTerm with
    | .borrowT sn τ S => do
      let τVal ← readC fuel τ
      let σ ← freshSym
      let ℓ ← freshLoan
      -- The type is registered BEFORE the binding files, so the binding's point
      -- delta carries its own σ's type (docs/17): registration and binding are
      -- one seeding instant, so this is ordering within a point, not a fact from
      -- the future. Also records σ as this borrow's entry snapshot (§5.4 `old *v`).
      modify (fun s => { s with sctx := (σ, τVal) :: s.sctx, entrySyms := (x.id, σ) :: s.entrySyms })
      bindSlot x (.borrowM ℓ (.know (Term.sym σ)))
      let SVal ← readC fuel S
      let opened := Pure.nf fuel (Pure.openBinder fuel sn SVal (Term.sym σ))   -- RHS[s := σ]
      -- D1's one-slot classification: a TYPE is the owed-type claim (today's
      -- meaning, unchanged); anything else is a PIN, opened at the entry σ
      -- exactly as an owed type is (D15: the binder IS the entry snapshot,
      -- pinned at mint), whose owed type is the payload type it releases at.
      if ← isOwedTypeT fuel opened then
        pure ({ loan := ℓ, owed := opened, trivial := trivialOwedT tyTerm, site := .param x }
                :: (← seedTelescopeV fuel rest))
      else
        pure ({ loan := ℓ, owed := τVal, pin := some opened, trivial := false, site := .param x }
                :: (← seedTelescopeV fuel rest))
    -- ¶4's RUNTIME-LENGTH SLICE, `Σ (c : Nat). &mut (Array c T)`, as a parameter.
    -- §5's second opacity ("borrows stored under a type constructor") reaching a
    -- telescope entry for the first time. The slot holds a genuine pair — a length
    -- and a borrow — so the length is a σ the body can name, and the borrow carries
    -- an ordinary obligation. PROBE (M24 STEP 1): see `docs/DELTAS.md` G2 for why
    -- this is not enough on its own.
    | .sigmaT cn aTy (.borrowT sn τ S) => do
      let aVal ← readC fuel aTy
      let σc ← freshSym
      modify (fun s => { s with sctx := (σc, aVal) :: s.sctx })
      let τVal := Pure.openBinder fuel cn (← readC fuel τ) (Term.sym σc)
      let σ ← freshSym
      let ℓ ← freshLoan
      -- Type before binding, as in the borrow branch above: the seed delta
      -- carries its own σ's type.
      modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
      bindSlot x (.ctor "Pair" [.know (Term.sym σc), .borrowM ℓ (.know (Term.sym σ))])
      -- `S` binds the payload snapshot at `sn`, the Σ's own binder is `cn`, and
      -- the two are opened by name — where under de Bruijn the second opening had
      -- to know that the first had dropped it from index 1 to index 0.
      let SVal ← readC fuel S
      let opened := Pure.nf fuel (Pure.openBinder fuel cn (Pure.openBinder fuel sn SVal (Term.sym σ)) (Term.sym σc))
      if ← isOwedTypeT fuel opened then
        pure ({ loan := ℓ, owed := opened, trivial := trivialOwedT tyTerm, site := .param x }
                :: (← seedTelescopeV fuel rest))
      else
        pure ({ loan := ℓ, owed := τVal, pin := some opened, trivial := false, site := .param x }
                :: (← seedTelescopeV fuel rest))
    -- **`ih` — a parameter whose type is a borrow-moded Π** (M26-C, §7 cost 1).
    -- It has no `Val` (`readC` refuses `borrowT`), so it cannot be a σ in `sctx`;
    -- it is a σ whose signature lives in `fsig`, which is what makes calling it
    -- the ordinary call rule. §7's convergence argument arrives here as one
    -- branch: "the only available view of the function is the σ-side, so the
    -- recursive call is abstract application at `u` — self-ensures FORCED rather
    -- than stipulated". Nothing about this branch knows it is for a recursor.
    | .pi _ _ _ => do
      if hasBorrowT tyTerm then do
        let σ ← freshSym
        bindSlot x (.know (Term.sym σ))
        -- **`fsig` stores the Π ITSELF** (M27-δ), peeled on demand at the call.
        -- A signature IS a Π and the AST already has one; a record beside it was
        -- a second representation of the same thing, kept in step by hand.
        modify (fun s => { s with fsig := (σ, tyTerm) :: s.fsig })
        seedTelescopeV fuel rest
      else do
        let τVal ← readC fuel tyTerm
        let σ ← freshSym
        modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
        bindSlot x (.know (Term.sym σ))
        seedTelescopeV fuel rest
    | tyTerm => do
      let τVal ← readC fuel tyTerm
      let σ ← freshSym
      modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
      bindSlot x (.know (Term.sym σ))
      seedTelescopeV fuel rest

/-- The `FnDef` view: parameter `i` gets runtime var id `i` — the §5.2 convention a
    declaration's own types are written against. -/
def seedTelescope (fuel : Nat) (i : Nat) (tel : List (String × Term)) : M (List Debt) :=
  seedTelescopeV fuel ((tel.zipIdx.map (fun p => (Var.mk (p.2 + i) p.1.1, p.1.2))))

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
      (grps.filter (fun g => g.captured.contains ℓ)).anyM (fun g =>
        g.issued.anyM (fun iss => reachesLoan iss target))

/-! ## The residue of an exempted parameter (M34)

    An argument borrow consumed into the result is exempt from the payload audit,
    and correctly so ABOUT THE SUB-PLACE THE RESULT POINTS AT: that place is under
    a live borrow, so there is no payload here to judge, and what the caller will
    recover is not what sits there now. The exemption was granted to the WHOLE
    parameter, which is more than the argument buys — every OTHER leaf of the
    parameter is a place the callee is done with and the caller will recover
    verbatim, so it is auditable and must be audited.

    Two questions, and the residue must answer both: is anything MISSING from a
    leaf the callee is finished with (`residueHoles`), and is what is there still
    the TYPE it was lent (`spliceInFlight` + `hasType`). The second is not implied
    by the first — a wrong-typed write leaves no hole — and the ordinary audit asks
    it of every non-exempt parameter, so the exempt one is not entitled to less. -/

mutual
  /-- Loan markers PARKED in a value — the places this value has lent out. A
      `borrowM` is not descended into: a borrow sitting here is somebody else's
      holding, and its payload is audited when that borrow ends. -/
  def parkedLoanMarkers : Val → List Nat
    | .loanM ℓ => [ℓ]
    | .borrowM _ _ => []
    | .node _ args => parkedLoanMarkersList args
    | _ => []
  termination_by v => sizeOf v
  def parkedLoanMarkersList : List Val → List Nat
    | [] => []
    | v :: vs => parkedLoanMarkers v ++ parkedLoanMarkersList vs
  termination_by vs => sizeOf vs
end

/-- Is loan `ℓ` in flight toward the result — i.e. does it reach one of the
    result's issued loans? Those are the places the audit must leave alone. -/
def inFlight (resultLoans : List Nat) (ℓ : Nat) : M Bool :=
  resultLoans.anyM (fun rl => reachesLoan ℓ rl)

/-- The first parked loan that is NOT in flight — the next piece of residue to
    pull home. -/
def firstNotInFlight (resultLoans : List Nat) : List Nat → M (Option Nat)
  | [] => pure none
  | ℓ :: rest => do
    if ← inFlight resultLoans ℓ then firstNotInFlight resultLoans rest else pure (some ℓ)

/-- **Collapse an argument borrow's payload at the boundary**: End-Mut every parked
    loan whose borrow is NOT in flight toward the result, pulling those sub-payloads
    home. This is how §3.3's field loans collapse at a real boundary, there being no
    owner to demand them; `endLoan` errors distinctively if a marker's borrow is
    missing.

    With NO result loans this ends every parked loan, which is what the audit always
    did, under two names this replaces. Locating by LOAN rather than by slot is
    what the second of them existed for: a Σ-packaged
    borrow (`Σ (n : Nat). &mut …`, §5's second opacity) sits inside a `Pair` in its
    slot, so a slot-shaped match falls through and the suspended field loans ride
    into `hasType`, which has no rule for a `loanₘ`. An exempted parameter's slot
    may equally have been moved from. One lookup covers both.

    Ending a loan early is sound (§ pop-with-drop: "the demand machinery already
    ends loans lazily, so eager ending moves the same events earlier and adds
    none"). -/
def collapseResidue : Nat → List Nat → Nat → M Unit
  | 0, _, _ => throwErr "audit: out of fuel (residue collapse)"
  | fuel + 1, resultLoans, ℓarg => do
    match (← getEnv).findSome? (fun kv => findBorrowPayload ℓarg kv.2) with
    | none => pure ()
    | some payload => do
      match ← firstNotInFlight resultLoans (parkedLoanMarkers payload) with
      | some ℓ => do endLoan fuel ℓ; collapseResidue fuel resultLoans ℓarg
      | none => pure ()

mutual
  /-- Hunt a collapsed residue for holes. `⊥` anywhere the callee still owns is a
      take-without-refill the caller will inherit; a parked marker survives only if
      its borrow is in flight (`collapseResidue` ended the rest).

      It stops AT an in-flight marker rather than descending through it: what is
      inside the returned place is not this audit's business, and `retHole`'s ⊥ in
      the returned cell belongs to the issued-borrow check, which has already run.
      The type question about the residue is asked separately, below. -/
  partial def residueHoles (resultLoans : List Nat) : Val → M (Option String)
    | .bot => pure (some "a hole (⊥)")
    | .loanM ℓ => do
      if ← inFlight resultLoans ℓ then pure none
      else pure (some s!"an uncollapsed loan (ℓ{subNat ℓ})")
    | .node _ args => residueHolesList resultLoans args
    | _ => pure none
  partial def residueHolesList (resultLoans : List Nat) : List Val → M (Option String)
    | [] => pure none
    | v :: vs => do
      match ← residueHoles resultLoans v with
      | some m => pure (some m)
      | none => residueHolesList resultLoans vs
end

mutual
  /-- **The residue as a whole value** — a READ-ONLY view, for the type half.

      The ⊥ hunt above answers "is anything missing"; it does not answer "is what
      is there still the type it was lent", and a wrong-typed write into a sibling
      leaf slipped through step 1 (probe `E7`). `hasType` is what answers that, and
      it has no rule for a `loanₘ` — so this splices each in-flight marker back to
      the payload its borrow currently holds, WITHOUT ending anything. Nothing is
      written to Ω; the live borrows stay live.

      **An ESCAPING place is filled OPAQUELY, an in-flight one with its payload.**
      That is the one distinction here, and it is where the honesty comes from. A
      place under a borrow the callee KEEPS holds a value nobody else can reach, so
      its current contents are the exit state and typing them is a claim about the
      exit state. A place under a borrow the callee ISSUED into the result is the
      opposite: the caller writes there next, and its current contents are the one
      thing the audit may not rely on. Filling it with a fresh σ at the borrow's
      own owed type asks the only question that survives the caller — does the
      parameter have its owed type for EVERY value that could land in the lent
      cell — and a fresh σ is the checker's native universal quantifier.

      Without it the two fills were the same fill, and the exit audit could not
      tell a `&mut` handed out onto a hashmap's VALUE cell from one handed out onto
      its KEY. Four programs measure that: a borrow escaping onto a cell a packed
      invariant hashes (`escKey`), onto an array's EXTENT (`escExtent`), onto a
      cell a Σ0 tail pins (`escPinned`), and onto a cell a later runtime binder's
      TYPE needs (`escRuntimeDep`). All four checked GREEN before this, and
      `escKeyExploit` is the end of that road — the checker accepted it, the
      machine ran it to a pack whose `Refl` proves `Id Nat 99 7`, and `chkL` of
      that value against its own declared type is `false`. `Tests.OpaqueFill` is
      the suite.

      **Mint at the ISSUED BORROW's owed type, never at the component's.** The
      granularity is the whole rule. An escaping `&mut Nat` owes back `Nat`, so the
      σ lands on the LEAF and the structure around it stays concrete — which is
      what lets a packed invariant still compute over the rest. A σ at the
      component's type is a different and much worse thing: the fold has nothing to
      step on and the packed proof is orphaned. That is not a hypothetical. The
      kernel already does it twice, at the two places where nothing better is
      available — the captured-by-an-open-group arm below, and `endGroup`'s opaque
      release — and `layer1`/`layer1Val` are the two programs that go red because
      of it, with the array component printing as a bare fresh σ. Reading
      `issued`'s owed type rather than `ob.owed` is what keeps this arm on the
      right side of that line.

      What the splice is honest about: at a TRIVIAL owed type the in-flight fill is
      a property of the exit state alone — "still an `Array 3 Nat`" — and
      `ob.trivialOwed` is guaranteed here by M27's containment, which throws before
      this point for anything richer. It would NOT be fine for a relational claim,
      which is exactly why the containment stays.

      Every marker has an answer, and there is no silent skip: the issued list, Ω,
      and the group table between them cover the corpus (instrumented as a hard
      error and replayed over the whole suite and the `hm-probe-getmut` corpus —
      neither arm fires). A marker with no answer REJECTS, distinctively: the audit
      cannot see that place, so it cannot certify it, and failing closed is what
      says so. -/
  partial def spliceInFlight (issued : List (Nat × Val × Term × Option Term)) : Val → M Val
    | .loanM ℓ => do
      -- ISSUED into the result: OPAQUE FILL. A fresh σ at the type this borrow
      -- owes back — the LEAF's type, not the parameter's — so the check that
      -- follows reads "for every value the caller could write here". Minting is
      -- safe from here because the whole fill runs sandboxed (see the call site):
      -- a query has no business moving the σ supply the rest of the check is named
      -- against, and stage 5's finding (2) is why that sandbox exists.
      match issued.lookup ℓ with
      | some (_, owed, _) => do
        let σ ← freshSym
        modify (fun st => { st with sctx := (σ, owed) :: st.sctx })
        pure (.know (Term.sym σ))
      | none => do
        -- No in-flight test here, deliberately. `residueHoles` has already
        -- rejected any marker in the residue PROPER that is not in flight; the
        -- markers this arm sees are the ones found by descending INTO an in-flight
        -- place, where a live sibling borrow is ordinary (`orInsertA` peels its
        -- bucket in borrow mode and returns `&m *hd` while `tl`'s field loan sits
        -- beside it, unreturned and perfectly legitimate).
        match (← getEnv).findSome? (fun kv => findBorrowPayload ℓ kv.2) with
          | some p => spliceInFlight issued p
          | none =>
            -- Not in Ω: the borrow was CAPTURED by a call whose group is still
            -- open (`GetMutOr` lending its bucket borrow to `Walk` and returning
            -- what `Walk` issued). The group table knows what it was lent at, and
            -- a fresh σ at that owed type is precisely what `endGroup`'s opaque
            -- release will put here — so the stand-in is the rule's own answer,
            -- not an assumption.
            --
            -- This is the COMPONENT-level mint the docstring warns about, and it
            -- is here because nothing better exists: the payload went into the
            -- group and the group is the only record of it. The cost is real and
            -- pinned — `layer1` in `Tests.OpaqueFill` is a carve moved behind a
            -- callee boundary, and its pack cannot be re-typed because this σ
            -- carries no relation to what the packed proof names. Do not read this
            -- arm as licence to mint at a component's type where a leaf's type is
            -- available; the arm above is where that distinction is made.
            match ((← get).groups.findSome? (fun g =>
                if g.captured.contains ℓ then some g.id else none)) with
            | none =>
              throwErr s!"audit: the residue of a returned-borrow parameter holds a loan (ℓ{subNat ℓ}) whose borrow is in neither Ω nor an open group, so the leaves the callee does not return cannot be typed. §6.1 exempts the returned sub-place, not the parameter — a place the audit cannot see is a place it cannot certify."
            | some ρ => do
              let owed := (← groupDebt ℓ (.call ρ)).owed
              let σ ← freshSym
              modify (fun st => { st with sctx := (σ, owed) :: st.sctx })
              pure (.know (Term.sym σ))
    | .node n args => do
      pure (Val.ctor n (← spliceInFlightList issued args))
    | v => pure v
  partial def spliceInFlightList (issued : List (Nat × Val × Term × Option Term)) : List Val → M (List Val)
    | [] => pure []
    | v :: vs => do pure ((← spliceInFlight issued v) :: (← spliceInFlightList issued vs))
end

/-! ## The pin discharge (12-design §2.3/§3.3, stage 5)

    A pin is checked SYMBOLICALLY at the callee's audit: the returned borrow has
    not been written through yet — the caller will do that — so the claim has to
    hold for every value that could come back. One exit term per issued loan,
    minted ONCE and shared between the fill and the pin's `@res` substitution:
    that sharing is the borrow-identity discipline the published systems all
    need (rust-verifiers doc, design input 1) — the same σ names "what lands in
    the lent cell" on both sides of the conversion, and two independent mints
    would make every pin unprovable.

    At a real caller's group end the SAME substitution runs with the exits
    instantiated to the actually-surrendered payloads (`endGroup`). One rule,
    two instantiations — the uniformity test §2.3 sets. -/

mutual
  /-- The exit term of loan `ℓ` under the given exit assignment: the issued
      exits themselves; a loan still held in Ω contributes its hole-filled
      payload; a loan captured by an open inner group contributes that group's
      own pinned release PROJECTED (§2.3's recursive case — its `@res` names
      the INNER call's issued exits, resolved through the same assignment), or
      a fresh σ at its owed type when the inner call is unpinned — the opaque
      sub-group as an unresolvable hole, §2.2's composition-climbs refusal
      arriving as a failed conversion rather than a special case. -/
  partial def exitOfLoan (fuel : Nat) (exits : List (Nat × Term)) (ℓ : Nat) : M Term := do
    match exits.lookup ℓ with
    | some e => pure e
    | none =>
      match (← getEnv).findSome? (fun kv => findBorrowPayload ℓ kv.2) with
      | some p => pinFill fuel exits p
      | none =>
        match (← get).groups.find? (fun g => g.captured.contains ℓ) with
        | some g => do
          let d ← groupDebt ℓ (.call g.id)
          match d.pin with
          | some p => do
            let innerExits ← g.issued.mapM (exitOfLoan fuel exits)
            pure (Pure.nf fuel (substResIdx innerExits p))
          | none => do
            let σ ← freshSym
            modify (fun st => { st with sctx := (σ, d.owed) :: st.sctx })
            pure (Term.sym σ)
        | none =>
          throwErr s!"audit: pin discharge — loan ℓ{subNat ℓ} is in neither the result, Ω, nor an open group, so its exit cannot be named"

  /-- The pin fill: the parameter's payload as a TERM, with every lent place
      standing at its exit. The `Term`-producing twin of `spliceInFlight`, and
      it must be one — the pin check is a CONVERSION, not a typing. -/
  partial def pinFill (fuel : Nat) (exits : List (Nat × Term)) : Val → M Term
    | .loanM ℓ => exitOfLoan fuel exits ℓ
    | .node "§segs" segs => pinFillSegs fuel exits segs
    | v@(.node n args) => do
      -- A remaining skeleton node (`§rec`, a stray `§seg`) is not a constructor
      -- a Term can spell; `subsKnowledge` folds what folds and marks the rest
      -- `@stateComponent`, which converts with nothing — a loud failure, not a
      -- fabricated term.
      if n.startsWith "§" then pure (subsKnowledge v)
      else pure (Term.ctorApp n (← pinFillList fuel exits args))
    | .bot => throwErr "audit: pin discharge reached a hole (⊥) the hole hunt should have refused"
    | v => pure (subsKnowledge v)

  /-- **A CARVE, filled** — `arrFoldSegs?`'s spine, with each segment body run
      through the fill instead of being required to be knowledge already. This is
      what lets a pin be discharged over a carved array: the lent cell inside the
      carve stands at its exit (the shared `@res` σ, or an issued pin's value)
      and every other segment at its actual payload, and the resulting `arrCat`
      spine normalizes exactly as the entry σ's own carve-refinement did — so
      when the body's flow has exposed the prefix (a run-headed left), `arrCat`'s
      ι fires on both sides of the conversion and an index-first update computes
      past it, precisely as the list discharge computes past a `Cons`. -/
  partial def pinFillSegs (fuel : Nat) (exits : List (Nat × Term)) : List Val → M Term
    | [] => pure (.ctorApp "Arr" [])
    | [s] =>
      (match Val.asSeg? s with
       | some (_, b) => pinFill fuel exits b
       | none => throwErr "audit: pin discharge — a segment list holds a non-segment")
    | s :: rest => do
      match Val.asSeg? s with
      | some (c, b) => do
        let bt ← pinFill fuel exits b
        let btl ← pinFillSegs fuel exits rest
        match Val.segsExtent? rest with
        | some ct => pure ty{ arrCat %c %ct %bt %btl }
        | none => throwErr "audit: pin discharge — a carve's tail extent does not sum"
      | none => throwErr "audit: pin discharge — a segment list holds a non-segment"

  partial def pinFillList (fuel : Nat) (exits : List (Nat × Term)) : List Val → M (List Term)
    | [] => pure []
    | v :: vs => do pure ((← pinFill fuel exits v) :: (← pinFillList fuel exits vs))
end

/-- **Discharge a PINNED parameter obligation** (12-design §2.3/§3.3 step 2's
    second branch — the repeal of the M27 containment, for pins). The exit
    assignment is built once — an issued borrow's exit is a FRESH σ at its owed
    type, unless the issued borrow carries its own pin, which CONSTRAINS the
    exit to it (how §5's read-only container law computes) — then the
    parameter's payload is filled at that assignment and CONVERTED against the
    pin opened at the same assignment. Conversion, not typing: the pin is a
    value claim, and its owed type rides inside it (D1's one-slot rule).

    The residue collapse stays OUTSIDE the sandbox (a real event, as on the
    unpinned path); the hole hunt runs first with the same rejection; the fill
    and its mints are sandboxed (stage-5 finding (2)). -/
def auditPinnedObligation (fuel : Nat) (issued : List (Nat × Val × Term × Option Term))
    (ob : Debt) (argName : String) (pin : Term) : M Unit := do
  let resultLoans := issued.map (·.1)
  collapseResidue fuel resultLoans ob.loan
  let payload? := (← getEnv).findSome? (fun kv => findBorrowPayload ob.loan kv.2)
  match payload? with
  | some payload =>
    (match ← residueHoles resultLoans payload with
     | some what =>
       throwErr s!"audit: argument borrow {argName} (ℓ{subNat ob.loan}) holds {what} at return, in a leaf it still owns — take without refill. (payload: {payload.pretty})"
     | none => pure ())
  | none =>
    -- Fine iff the borrow itself left in the result (its exit IS the filled
    -- payload below) or continued into an open group (the projection reaches
    -- it); anything else is the ordinary "lost" rejection.
    if (← inFlight resultLoans ob.loan)
       || (← get).groups.any (fun g => g.captured.contains ob.loan) then pure ()
    else throwErr s!"audit: argument borrow {argName} (ℓ{subNat ob.loan}) is neither locatable in Ω nor continued into a call — it was lost"
  let saved ← get
  let verdict ← (do
    -- One exit per issued loan, minted ONCE — shared by the fill and the pin's
    -- `@res` substitution (the borrow-identity discipline).
    let exits ← issued.mapM (fun (ℓk, _, owedk, ipin) => do
      match ipin with
      | some p => pure (ℓk, p)
      | none => do
        let σ ← freshSym
        modify (fun st => { st with sctx := (σ, owedk) :: st.sctx })
        pure (ℓk, Term.sym σ))
    let filled ← match payload? with
      | some payload => pinFill fuel exits payload
      | none => exitOfLoan fuel exits ob.loan
    let opened := Pure.nf fuel (substResIdx (exits.map (·.2)) pin)
    let filledN := Pure.nf fuel filled
    if Term.convEq filledN opened then pure none
    else pure (some (filledN, opened)))
  set saved
  match verdict with
  | none => pure ()
  | some (f, o) =>
    throwErr s!"audit: {argName}'s pin is not met — the exit payload, hole-filled at the issued borrows' exits ({f.pretty}), does not convert with the declared pin ({o.pretty}). A pin is proved by the body's own flow: an opaque sub-call holding the loan, or a write the pin does not describe, is why this fails."

/-- **Audit one argument-borrow obligation** — §6.1's rule, at the granularity of
    the PLACE (M34). `issued` is the result's borrows with their payloads AND
    their owed types; empty for a value-returning body.

    The owed types are carried because the fill needs them: an escaping place is
    filled with a fresh σ at the borrow's own owed type, and `ob.owed` — the
    PARAMETER's — is the wrong type to mint at (`spliceInFlight`). They cost
    nothing to carry: `collectResultBorrows` already collects the triple for the
    issued-borrow check, and this used to project it back down on the way in.

    There used to be two rules here, and the second was a `pure ()`. §6.1 exempts
    an argument borrow whose derived borrow was consumed into the result, and the
    argument for that is sound but LOCAL: it is about the sub-place the result
    points at, which is under a live borrow, so there is no payload to judge and
    what the caller eventually recovers is not what sits there now. It says
    nothing about the parameter's other leaves — those are places the callee is
    finished with and the caller recovers verbatim. `hm-probe-getmut`'s second
    finding is what the whole-parameter reading cost: a three-way carve returns
    the middle cell, leaves a ⊥ in the left one, and is ACCEPTED, while §6.2's
    opacity re-mints the owner at the declared type downstream — so the checker
    repaired the hole and the machine handed back an array with a ⊥ in a leaf.

    So there is one rule, and the exemption is not a branch of it but a fact about
    which loans it can reach: **collapse what the callee is finished with, reject a
    hole in what it still owns, then type the whole thing with the in-flight places
    filled in.** A value-returning body has nothing in flight, so the collapse is
    total, the hole hunt sees everything, and the fill is the identity — which is
    exactly the old value-returning rule, recovered as the degenerate case rather
    than written out again. -/
def auditObligation (fuel : Nat) (issued : List (Nat × Val × Term × Option Term)) (ob : Debt) : M Unit := do
  let resultLoans := issued.map (·.1)
  -- The parameter this debt was seeded on (`site = .param`); the audit walks
  -- only those, so the fallback is unreachable and honest about being so.
  let argName := match ob.site with | .param x => x.name | _ => "?"
  -- A PINNED parameter takes the discharge (§2.3) — the containment below is
  -- repealed for exactly this case, because there is now something to check:
  -- the claim is proved symbolically, not exempted.
  --
  -- M27 SOUNDNESS CONTAINMENT (b1's second closed `Bot`). §6.1's exemption is
  -- correct about the PAYLOAD of a consumed borrow, but it used to skip the OWED
  -- TYPE with it, and the caller's group end then MINTS the release at that type —
  -- so a non-trivial owed type on a consumed parameter was a claim the callee was
  -- exempted from and the caller received as fact. Neither end checked it.
  --
  -- Refused rather than repaired, for the same reason as the mixed-return
  -- containment: checking a freshly minted σ against the type it was minted at
  -- proves nothing, so the honest move is to make the unjudged position
  -- unwritable. A cursor that hands its borrow onward owes back what it was lent.
  --
  -- It is also what makes the fill below honest: `ob.owed` past this point is
  -- always the type the parameter was LENT, so typing the filled payload against
  -- it is a claim about the exit state alone, never a relation.
  if let some pin := ob.pin then
    auditPinnedObligation fuel issued ob argName pin
  else if !ob.trivial && (← inFlight resultLoans ob.loan) then
    throwErr s!"boundary: '{argName}' is consumed into the result, and §6.1 exempts such a borrow from the payload audit — so its non-trivial owed type ({ob.owed.pretty}) would be checked by nobody, while the caller's group end mints the release AT it. A parameter passed onward into the result owes back the type it was lent; state a richer claim on a parameter the body keeps, where the audit runs."
  -- Continued into ANOTHER CALL whose group is still open, and not toward the
  -- result: a genuinely different exemption from the one above, and the only one
  -- left. The payload is not recoverable here at all — the group holds it — so
  -- there is nothing to collapse, hunt or fill.
  else if !(← inFlight resultLoans ob.loan)
          && (← get).groups.any (fun g => g.captured.contains ob.loan) then pure ()
  else do
    -- (1) COLLAPSE the residue: End-Mut every parked loan whose borrow is not in
    -- flight toward the result, pulling those sub-payloads home. With no result
    -- loans this ends every parked loan, which is the value-returning case.
    collapseResidue fuel resultLoans ob.loan
    match (← getEnv).findSome? (fun kv => findBorrowPayload ob.loan kv.2) with
    | none =>
      -- Not in Ω. Fine iff the borrow itself left in the result (there is then no
      -- residue at all, and the issued-borrow check types what it points at);
      -- otherwise it is the old "lost" rejection.
      if ← inFlight resultLoans ob.loan then pure ()
      else throwErr s!"audit: argument borrow {argName} (ℓ{subNat ob.loan}) is neither locatable in Ω nor continued into a call — it was lost"
    | some payload => do
      -- (2) HUNT what the callee still owns for holes. Stops AT an in-flight
      -- marker: inside the returned place is the issued-borrow check's business.
      match ← residueHoles resultLoans payload with
      | some what =>
        let exempt := if resultLoans.isEmpty then "" else
          " §6.1 exempts the sub-place a returned borrow points at, not the whole parameter: every other leaf is a place the caller recovers verbatim, and this one has no value in it."
        throwErr s!"audit: argument borrow {argName} (ℓ{subNat ob.loan}) holds {what} at return, in a leaf it still owns — take without refill.{exempt} (payload: {payload.pretty})"
      | none => do
        -- (3) TYPE it, with the in-flight places filled in — the ESCAPING ones
        -- opaquely, the rest with their payloads. A QUERY, so it runs SANDBOXED:
        -- the fill mints a σ for every escaping place and wherever the group table
        -- is its only source, and a query has no business moving the σ supply that
        -- the rest of the check is named against. Restoring the state on the way
        -- out is the difference between this landing silently and it renumbering
        -- the corpus — and with opaque fill the sandbox stopped being a nicety,
        -- since every borrow-returning body now mints here. The collapse above
        -- stays outside it — ending those loans is a real event, and it is one the
        -- old rule performed too.
        let saved ← get
        let verdict ← (do
          let filled ← spliceInFlight issued payload
          if ← hasType fuel filled ob.owed then pure none else pure (some filled.pretty))
        set saved
        match verdict with
        | none => pure ()
        | some filled =>
          let exempt := if resultLoans.isEmpty then "" else
            " §6.1 exempts the sub-place a returned borrow points at, not the whole parameter — the leaves the callee is finished with are recovered verbatim and must still be what they were lent."
          throwErr s!"audit: {argName}'s payload ({filled}) does not have its owed type ({ob.owed.pretty}).{exempt}"

/-- Walk a return type against the result value, collecting each borrow position
    as `(issued loan, payload, owed type, pin?)`. `none` = value-returning (no
    borrow); a `Σ`/`Pair` of borrows gives the multi-issued list (`nth2`, §6.1).
    A pin RHS (D1) is opened at the payload's own knowledge — the callee side of
    §5's read-only law, where the identity pin is met by construction — and the
    owed type is then the payload type as written. -/
partial def collectResultBorrows (fuel : Nat) : Term → Val → M (Option (List (Nat × Val × Term × Option Term)))
  | .borrowT sn τ S, .borrowM ℓ payload => do
    let opened := Pure.nf fuel (Pure.openBinder fuel sn (← readC fuel S) (subsKnowledge payload))
    if ← isOwedTypeT fuel opened then
      pure (some [(ℓ, payload, opened, none)])
    else
      pure (some [(ℓ, payload, ← readC fuel τ, some opened)])
  | .borrowT _ _ _, other =>
    throwErr s!"audit: borrow-returning body did not return a borrow (got {other.pretty})"
  | .sigmaT x a b, pr => do
    match Val.asCtor? pr with
    | some ("Pair", [va, vb]) => do
      let ra ← collectResultBorrows fuel a va
      -- The tail is DEPENDENT (D9, M35): it may cite the first component — for
      -- a borrow component, `*r` collapses to the binder and opens at the
      -- PAYLOAD, which is the component's knowledge.
      let b' := Pure.openBinder fuel x (collapseDerefOf x b) (subsKnowledge va)
      let rb ← collectResultBorrows fuel b' vb
      match ra, rb with
      | none, none => pure none                      -- a genuine value pair, not borrows
      | _, _ => do
        -- A MIXED return type — borrow and value components — is audited per
        -- component (D9's repeal of `retMixesBorrow`): the borrows join the
        -- issued checks, and a VALUE component is judged here, at its opened
        -- type, against the actual component. No ∀ and no exit σ: the callee
        -- KNOWS its own first component, and the fact stated is about the
        -- payload as issued — which is exactly what lets a cursor say WHERE it
        -- points (`Id Nat (*r) (NthL i (old *v))`).
        (match ra with
         | none => do
           let aTy ← readC fuel a
           if ← hasType fuel va aTy then pure ()
           else throwErr s!"audit: mixed return type — value component ({va.pretty}) does not have its declared type ({aTy.pretty})"
         | some _ => pure ())
        (match rb with
         | none => do
           let bTy ← readC fuel b'
           if ← hasType fuel vb bTy then pure ()
           else throwErr s!"audit: mixed return type — value component ({vb.pretty}) does not have its declared type ({bTy.pretty})"
         | some _ => pure ())
        pure (some (ra.getD [] ++ rb.getD []))
    | _ => pure none
  | _, _ => pure none                                -- value-returning
  -- (partial since M35: the Σ arm recurses on the OPENED tail, which is not a
  -- structural subterm once a dependent tail is legal.)

/-- The audit for one path. A **value-returning** body (§5.4): every argument
    borrow meets its obligation and the result has the (entry-pinned) return
    type. A **borrow-returning** body (§6.1 callee side): the result carries one
    or more issued borrows (a single `&mut`, or a `Pair` of them — the
    multi-issued group); each argument borrow that was consumed into a result
    borrow (directly or as its captured owner) is exempt, the rest meet their
    obligations, and every issued borrow's payload has its owed type. -/
def auditAction (fuel : Nat) (retType : Term) (resultVal : Val) : M Unit := do
  -- This path's (refined) parameter obligations: the debts seeded on the
  -- telescope (`site = .param`), in seeding order. Call-site debts (`.call`/
  -- `.issue`) belong to their groups' ends, not to this walk.
  let obs := (← get).debts.filter (fun d => match d.site with
    | .param _ => true | _ => false)
  -- Ex falso: a branch whose result is `botElim _ x` with `x : ⊥` is
  -- unreachable (a bounds-proof `nth`'s `Nil` branch, where `p : Le (S i) 0 = ⊥`).
  -- It is vacuously well-formed at ANY return type — no borrow/obligation audit,
  -- and the `botElim` motive need not be the (unreflectable) borrow return type.
  match (match resultVal with | .know t => Pure.collectSpineT t | _ => (.unit, [])) with
  | (.const "botElim", [_, x]) =>
    if ← hasTypeT fuel x (.const "Bot") then pure ()
    else throwErr s!"audit: botElim result on a non-⊥ argument ({x.pretty})"
  | _ =>
  -- D9 (M35): the walk runs on the PINNED borrow-return type when one exists —
  -- entry-resolved and branch-swept — so a mixed return's value components are
  -- judged at what the branch learned, not at a stale entry σ. Value-returning
  -- bodies have no `retTyBorrow` and walk the AST as before (both are
  -- borrow-free, so the walk's answer is `none` either way).
  match ← collectResultBorrows fuel ((← get).retTyBorrow.getD retType) resultVal with
  | some checks => do
    -- The ISSUED borrows first, then the obligations — M34's order, and the
    -- reason is a diagnosis one. `auditObligation` fills each escaping place in a
    -- parameter's payload at the ISSUED BORROW'S OWN OWED TYPE, so a defect in
    -- what the result points at would otherwise surface as a complaint about the
    -- parameter. `retHole` is the control: a body that empties the cell it returns
    -- should be told its RESULT holds ⊥, not that its argument does; `badTyElem`
    -- and `badWidth` are the two that keep their own sentences because of it.
    -- Running the issued checks first means the obligations are only ever asked
    -- once the result side is known good, and that ordering is what made opaque
    -- fill affordable — stage 5's finding (1) recorded these diagnoses being
    -- STOLEN by an owed-type fill, and it was measuring one written before M34 put
    -- this order in place.
    --
    -- Nothing depended on the old order: the residue collapse ends only loans that
    -- do NOT reach a result loan, so it cannot disturb an issued borrow's payload.
    checks.forM (fun c =>
      let (_, payload, owed, ipin) := c
      do if ← hasType fuel payload owed then
           -- The issued borrow's own PIN (§5): opened at the payload's
           -- knowledge, so the identity pin is met by construction here — the
           -- callee side of the read-only law; the caller's endIssued is where
           -- a violating write is caught.
           match ipin with
           | some p =>
             if Pure.convert fuel (subsKnowledge payload) p then pure ()
             else throwErr s!"audit: returned borrow's payload ({payload.pretty}) does not meet the result's own pin ({p.pretty})"
           | none => pure ()
         else throwErr s!"audit: returned borrow's payload ({payload.pretty}) does not have its owed type ({owed.pretty})")
    -- The triple goes through WHOLE. It used to be projected down to (loan,
    -- payload) here, and the owed type it dropped is the one the fill mints at.
    obs.forM (auditObligation fuel checks)
  | none => do
    obs.forM (auditObligation fuel [])
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
    --
    -- The fold used to be spelled out at this one site. It is `subsKnowledge`'s own
    -- now (Gap A), which is where it always belonged: this site had already found
    -- that a type reaching for a carved array wants its `arrCat` spine, and the exit
    -- audit's OTHER re-typing — the dependent tail in `checkFields` — wanted the
    -- same thing and had no way to say so.
    --
    -- That the two ARE one rule is measured rather than asserted: take the fold back
    -- out of `subsKnowledge` while this line no longer spells it out, and
    -- `ArraySort`'s 519, 885 and 888 go red — `quicksortA`'s exit snapshot is a
    -- `§segs` again and its `SortedA`/`CountA` postconditions get stuck on it.
    -- Either site alone covers those three; neither alone covers the packed tail.
    let exits := (← get).exitSyms
    let retTy ← obs.foldlM (fun acc ob =>
      match (match ob.site with
             | .param x => exits.lookup x.id
             | _ => none) with
      | none => pure acc
      | some σ => do
        match (← getEnv).findSome? (fun kv => findBorrowPayload ob.loan kv.2) with
        | some payload => pure (Pure.nf fuel (Term.substSym σ (subsKnowledge payload) acc))
        | none => pure acc) retTy0
    if ← hasType fuel resultVal retTy then pure ()
    else throwErr s!"audit: result ({resultVal.pretty}) does not have return type ({retTy.pretty})"

/-! ## Binder modes: the fence, and the comptime-argument read (combining-fns §6, M26-B)

    A capitalized binder is **comptime**: erased, never moved, never observable
    by ⇒, and usable only in ⇝-positions — types, proofs, and the capital
    argument positions of other calls. Two mechanisms carry that, and they are
    the two halves of the same sentence:

      * `readComptimeArg` — the ⇝ side. At a ⇒-call, an argument standing in a
        capital-bindered position is evaluated by ⇝: a pure, NON-CONSUMING read.
        This is what retires R16's proof-consumption staging — a proof passed to
        a call is still there afterwards, because passing it never moved it.
      * `fenceComptime` — the ⇒ side. Every rule that would make a comptime
        binder observable at runtime rejects instead.

    **A negative control per DEMAND SITE, not per rule branch** (phase A's
    finding, now doctrine): `readC` computes without checking, so the fence is
    only exercised where a rule actually demands the thing. The sites are
    enumerated below and each has its own test. -/

/-- The ⇝ read at a ⇒-position: what a capital binder's argument gets, and what
    a `let X = e` evaluates its right-hand side with.

    It is `readC` preceded by the demand-collapse §5.2 states as one rule
    ("every demand collapses first") — a comptime argument mentioning `*v` while
    `v`'s payload holds a parked loan must end it before the projection, exactly
    as the pure lift's own `.app`/`.lam` cases do. Non-consuming is the whole
    point, so nothing else here writes a slot. -/
def readComptimeArg (fuel : Nat) (t : Term) : M Term := do
  collapseCDerefs fuel t
  readC fuel t

/-- The binder modes of a callee, one per argument the spine supplies (§6).

    Peels λ- or Π-binders left to right, reading `domComptime` off each domain.
    A callee with fewer binders than arguments pads with runtime and lets the
    existing over-application rejection fire — this function decides *which
    arrow reads an argument*, never whether the arity is right.

    **It OPENS each binder rather than descending into its body** (M30). Under
    substitution the two were the same move — a body was a subterm and its binders
    were visible from outside — and this function walked straight in. Under NbE a
    body is a closure, and walking in finds no `Π` at all: the fallback fires and
    reports every remaining binder as RUNTIME. That is the worst shape a bug can
    have here, because it is silent and it is not a rejection — a comptime
    parameter read by ⇒ is a proof CONSUMED instead of snapshotted, and the failure
    surfaces at the audit of a function whose telescope was fine.

    The probe argument is a rigid constant, deliberately: modes live on the
    domains as written, so nothing should reduce on the way, and a neutral keeps
    every dependent domain honestly stuck instead of computing at a made-up
    value. -/
def modeProbe : Term := .const "@modeProbe"

def binderModes : Nat → Term → Nat → List Bool
  | _, _, 0 => []
  | 0, _, n => List.replicate n false
  | fuel + 1, v, n + 1 =>
    match Pure.whnf fuel v with
    | .lam x dom body =>
      Term.domComptime dom :: binderModes fuel (Pure.openBinder fuel x.name body modeProbe) n
    | .pi x dom cod => Term.domComptime dom :: binderModes fuel (Pure.openBinder fuel x cod modeProbe) n
    | _ => List.replicate (n + 1) false

/-! ## Value-callee application (combining-fns §7 cost 2, M26-A)

    `x a₁ … aₙ` applies whatever slot `x` holds. The two rules are §2's
    two rows for "what does applying a function yield", and the slot's contents —
    not a flag, not a table — pick the row:

      * **body known** ⟹ unfold. A literal λ is bound-and-run: β, with each
        argument checked against its binder's domain. Both machines take this
        rule, which is what makes a *transparent* definition mean the same thing
        in both (`applyLam`).
      * **body withheld** ⟹ the type's promise and nothing more. A `σ : Π` is an
        abstract function — a seal's mint, or a Π-typed binder — and applying it
        yields a fresh σ at the instantiated codomain (`instantiatePi` computes
        the codomain; the call rule mints). Checking mode only: no concrete run
        ever has a σ in a slot.

    **Both are saturated** (§12 decision 4). Under-application is rejected rather
    than curried, because a partial application at runtime is precisely a closure
    holding its arguments — including, in general, borrows — while it waits, and
    that is the thing §7 defers. The cost is stated honestly in the rejection: a
    function that legitimately RETURNS a function is syntactically identical to an
    under-applied one, and phase A has no mode information to tell them apart, so
    both are refused here. -/

/-! ## Effectful recursors: the spine layouts, and where the arms sit (M26-C)

    §7 promotes "recursion is eliminators" from soundness argument to semantics,
    and cost 5 says the executing machine takes the change first: **ι-reduction
    of a recursor whose arms are BODIES**. The layouts below are the only
    kernel knowledge that rule needs — everything else is the arms' own. -/

/-- For a recursor constant: how many arguments precede the scrutinee, the index
    of the **motive**, and the index of the **base arm**.

    The base arm is where a spine's binder MODES are read from — its binders are
    exactly the trailing, motive-supplied ones (`z : P Z` and `s : Π k → P k →
    P (S k)` end in the same telescope), and the arms are the only place a
    runtime recursor has names at all.

    The motive index is here because of the rule below it: **⇒ does not evaluate
    the motive.** -/
def recLayout : String → Option (Nat × Nat × Nat)
  | "natRec"  => some (3, 0, 1)   -- P z s ⟨n⟩          ; motive `P`, base arm `z`
  | "listRec" => some (4, 1, 2)   -- A P pn pc ⟨l⟩      ; motive `P`, base arm `pn`
  | "boolRec" => some (3, 0, 1)   -- P t f ⟨b⟩          ; motive `P`, base arm `t`
  | _ => none

/-- What ⇒ puts in a runtime recursor spine's **motive** slot.

    A runtime recursor's motive is `λ f. Π (v : &mut List Nat) → …` — a
    borrow-moded Π, and `readC` refuses `borrowT` outright ("only valid at a
    telescope position"), so the motive has **no ⇝ reading and therefore no
    value**. That is not an obstacle to work around; it is the fragment line
    doing its job, and the right response is that ⇒ has no use for the motive
    either: ι never inspects it (only the scrutinee's constructor selects an
    arm), and §7 settles where the checking side gets it — "the motive is derived
    from the signature", i.e. from the seal's ascription, which the checker holds
    as a TERM.

    So the slot is kept — one grammar, one arity, `recLayout` unchanged between
    fragments — and filled with this marker, which no rule reads. The motive a
    program writes is checked where it can be: at the seal, against the one
    derived from the ascribed Π. -/
def erasedMotive : Term := .const "@motive"

/-- Collect a `Term` application spine into head and arguments (the mirror of
    `Pure.collectSpineT`, needed because ⇒ meets recursors as terms first). -/
def collectAppT : Term → Term × List Term
  | .app f a => let (h, as) := collectAppT f; (h, as ++ [a])
  | t => (t, [])

/-- Is this term a recursor spine with at least one **runtime** arm — i.e. one ⇒
    must evaluate rather than hand to `readC`? Keyed syntactically on a literal
    `.lamR` in an argument position, which is exactly what the `fn` elaboration
    produces and what `readC` would refuse. A recursor over pure arms is
    untouched and still goes through the pure lift. -/
def runtimeRecSpine? (t : Term) : Option (String × List Term) :=
  match collectAppT t with
  | (.const c, args) =>
    if (recLayout c).isSome && args.any (fun a => match a with
        | .lam _ _ _ => Term.lamImperative a | _ => false)
    then some (c, args) else none
  | _ => none

/-! ## A sealed RECURSOR's arms carry their ascriptions too (M33 Σ0's prerequisite)

    A recursive `fn` does not seal a λ. `fn [k] Partition …` elaborates to
    `natRec P z s` and the seal ascribes the whole spine, so `sealExec`'s λ case
    never fires and the arms — which ARE the bodies — would enter with no return
    type in hand. That is the same asymmetry M33a measured, arriving by a second
    road, and it is the road quicksort's tail actually takes: `cnt` is returned
    from `Partition`, and `Partition` is `fn [k]`.

    **The derivation is `sealRec`'s, not a new one.** §7 derives the motive from
    the signature — peel the scrutinee off the ascribed Π and the codomain `R` IS
    the motive's body — so an arm's contract is `R` at that arm's constructor,
    under the leading binders the recursor's premise gives it (the predecessor,
    and `ih` at the predecessor). `checkArm` states exactly this on the checking
    side; these two functions state it on the executing side, and the only thing
    they do differently is not check it. -/

/-- A leading binder's domain, wearing the mode its binder's case declares — so
    that `piPeel` (which compares the two) agrees by construction. The checking
    side has already verified the real agreement at the seal; re-deriving it here
    would be the checker's rule enforced twice, in execution. -/
def preDom (x : Var) (dom : Term) : Term := if x.isComptime then .cmpT dom else dom

/-- **Does ι owe this arm a `()`?** (M33b.) An arm the motive owes nothing binds
    the unwritable `U§ : ⇝Unit` (`Syntax.unitBinder`) so that it is a suspension
    rather than a bare term, and ι is what forces it. Reading the answer off the
    arm's own leading binder is what resolves `S26Rec` §A4's ambiguity — "the arm
    applied to no arguments" and "the arm with nothing owed" are now different
    terms, and only the elaboration can write the first. -/
def Val.armTakesUnit : Val → Bool
  -- (`nd` rather than `node`, which is a `Val` constructor and would be read as
  -- one inside this namespace.)
  | .closure _ nd _ => Term.telTakesUnit (Term.peelLams nd).1
  | _ => false

/-- The Π each argument of a sealed recursor spine is checked against, aligned
    with the spine's arguments (`none` at the motive and the type parameter, which
    are not arms). `u` is the ascription; `arms` are the argument VALUES, consulted
    only for the arms' own binder names and cases. -/
def recArmPis (c : String) (u : Term) (arms : List Val) : List (Option Term) :=
  match u with
  | .pi sn scrutDom R =>
    let leading : Val → List (Var × Term) := fun v =>
      match v with | .closure _ node _ => (Term.peelLams node).1 | _ => []
    let atCtor : Term → Term := fun ct => Term.substP sn ct R
    -- The arm's leading binders, wrapped back into Πs. Names are unwritable and
    -- unused: `piPeel` substitutes each for the λ's own binder, and `R` already
    -- speaks of the λ's binders (`sealRec` substituted them in).
    let wrap : List (Var × Term) → Term → Term := fun pre ret =>
      pre.foldr (fun p acc => .pi "§pre" (preDom p.1 p.2) acc) ret
    -- **A base arm's contract grows the unit binder when the arm took one**
    -- (M33b) — `checkArm`'s rule, on the executing side, read off the same place:
    -- the arm's own leading binder. Without it `applyClosure`'s `calleeRetTy`
    -- peels the ascription at a name the Π does not have.
    let baseTy : Nat → Term → Option Term := fun i ty =>
      some (if Term.telTakesUnit ((arms[i]?).map leading |>.getD []) then Term.unitPi ty else ty)
    match c with
    | "natRec" =>
      -- args: P z s
      let step : Option Term :=
        match (arms[2]?).map leading with
        | some (k :: ih :: _) =>
          some (wrap [(k.1, scrutDom), (ih.1, atCtor (.var k.1))]
                 (atCtor (.ctorApp "S" [.var k.1])))
        | _ => none
      [none, baseTy 1 (atCtor (.ctorApp "Z" [])), step]
    | "listRec" =>
      -- args: A P pn pc
      let elemTy : Term := match scrutDom with
        | .app (.const "List") a => a
        | _ => .const "Nat"
      let cons : Option Term :=
        match (arms[3]?).map leading with
        | some (h :: tl :: ih :: _) =>
          some (wrap [(h.1, elemTy), (tl.1, scrutDom), (ih.1, atCtor (.var tl.1))]
                 (atCtor (.ctorApp "Cons" [.var h.1, .var tl.1])))
        | _ => none
      [none, none, baseTy 2 (atCtor (.ctorApp "Nil" [])), cons]
    | "boolRec" =>
      [none, baseTy 1 (atCtor (.ctorApp "True" [])), baseTy 2 (atCtor (.ctorApp "False" []))]
    | _ => []
  | _ => []

/-- Give a sealed recursor spine's arm closures the contracts `recArmPis` derives.
    Anything that is not an un-ascribed closure is left exactly as it was — a
    knowledge arm has no closure to carry one, and an arm that somehow arrived
    with an ascription keeps its own. -/
def ascribeRecArms (u : Term) (v : Val) : Val :=
  match Val.asRecSpine? v with
  | some (c, args) =>
    let pis := recArmPis c u args
    Val.recSpine c ((args.zipWith (fun a p =>
      match a, p with
      | .closure ρ node none, some π => .closure ρ node (some π)
      | a, _ => a) (pis ++ List.replicate args.length none)))
  | none => v

/-- A juxtaposition spine `x a b …` whose head is a runtime variable (M27 β).

    `Nil` when the head is anything else — a constant, a pure former, a peel — in
    which case the spine is an ordinary term and ⇒'s pure lift reads it.

    (`Term.appSpineVar?` since R4, because `Term.imperative` consults it too; the
    name is kept here for the machine's call sites.) -/
abbrev appSpineVar? : Term → Option (Var × List Term) := Term.appSpineVar?


/-- The head constant of a `Term` application spine, if it has one. -/
partial def termSpineHead : Term → Option String
  | .const c => some c
  | .app f _ => termSpineHead f
  | _ => none

/-- The head constant of a knowledge application spine, if it has one. -/
partial def valSpineHead : Val → Option String
  | v => (Val.asRecSpine? v).map (·.1)

/-- **Does ⇒ own the application of this callee value?** (M32 R4.)

    With `callV` retired there is one application node, so this is the whole of
    what used to be carried by the choice between two of them — and it is a
    question about the VALUE the head slot holds, asked after the ⇝ fetch.

    `true` means the ⇒ call rule runs (entry, ι, β-with-saturation, the mint, or
    an honest rejection); `false` means the pure lift, where ⇝ remembers the
    structured neutral. The `true` cases, and why each is not the lift's:

      * a **closure**, either fragment. An imperative one is ⇒-ENTRY; a comptime
        one is β, but β that CHECKS — arity and each argument against its
        binder's domain, which the normalizer does not do (c6, c7).
      * **a value holding a loan marker** — §5.2's "every demand collapses
        first" at the callee slot. The lift would read the marker as knowledge
        instead of ending the loan and retrying (c11).
      * **⊥** — a call on a moved slot is a use-after-move, and ⇒ is where it is
        named. The lift would report it as a comptime read of ⊥, which is a
        true sentence about the wrong event.
      * a **recursor spine** over runtime arms — ι is ⇒'s (§7 cost 5).
      * a **σ**, and this is the case that carries §12 decision 5. With an
        `fsig` it is a sealed function and `callDeclC` enters it. With only an
        `sctx` type it is ABSTRACT, and the call MINTS a fresh existential at
        the instantiated codomain rather than remembering `σ a` — deliberately
        not the structured neutral, which is ⇝'s reading of the same term.
      * a **constructor value** — data at the head of a call. Not a function,
        and ⇒ says so rather than handing `3 2` to the normalizer to remember as
        a neutral nobody can ever use.

    Everything else is knowledge with a comptime reading and no ⇒ entry — a
    stuck spine, a constant, a pure variable that is not a σ — and the lift is
    exactly right for it. That is where the corpus's staged proof-builders live
    (`let Cnt = MkL lo hi hcnt` applied later), and it is why this is a value
    test and not "a `.var` head means a call". -/
def calleeIsRuntime (st : St) (v : Val) : Bool :=
  match v with
  | .closure _ _ _ => true
  | .bot => true
  | v => if (firstLoanMarker v).isSome then true else
  match v with
  | v =>
    match valSpineHead v with
    | some c => (recLayout c).isSome
    | none =>
      match v.symOf? with
      | some σ => (st.fsig.lookup σ).isSome || (st.sctx.lookup σ).isSome
      | none => (Val.asCtor? v).isSome

/-- The binder modes of a callee **value**, generalizing `binderModes` past the
    types it can read them off (§6, M26-C).

    A `Π`/`λ` carries its modes on its domains, which is what `binderModes`
    reads. A runtime function carries them where §6 puts them for every other
    runtime binder — **the binder's own name** — so no type is consulted at all,
    and none could be: a borrow-moded Π has no `Val` form. A recursor spine
    borrows its trailing modes from its BASE arm, whose binders are exactly the
    ones the motive supplies (`z : P Z` and `s : Π k → P k → P (S k)` end in the
    same telescope); its own scrutinee is runtime, being the thing ι splits on. -/
def valBinderModes : Nat → Val → Nat → M (List Bool)
  | _, _, 0 => pure []
  | 0, _, n => pure (List.replicate n false)
  | fuel + 1, v, n + 1 => do
    match v with
    -- **A closure's binder modes are its own binders'** (M32 R2). `rfn` read them
    -- off the binder NAMES because its value had dropped the domains; the closure
    -- keeps the λ as written, so both sources are present and they agree by
    -- construction (`markDom` puts a capital binder's mode on its domain). The
    -- name is what is read, unchanged, because that is §6's rule for every other
    -- runtime binder and the corpus's hand-written `.lam "T" .type` λs are
    -- capital-by-spelling without ever having been comptime.
    | .closure _ node _ =>
      let names := (Term.peelLams node).1
      if Term.lamImperative node then
        pure ((names.map (fun q => q.1.isComptime) ++ List.replicate (n + 1) false).take (n + 1))
      else pure ((names.map (fun q => Term.domComptime q.2)
                    ++ List.replicate (n + 1) false).take (n + 1))
    | v =>
      match Val.asRecSpine? v with
      | some (c, args) =>
        match recLayout c with
        | none =>
          match v with
          | .know t => pure (binderModes fuel t (n + 1))
          | _ => pure (List.replicate (n + 1) false)
        | some (k, _, b) =>
          if args.length == k then
            pure (false :: (← valBinderModes fuel (args.getD b .bot) n))
          else if args.length == k + 1 then
            valBinderModes fuel (args.getD b .bot) (n + 1)
          else pure (List.replicate (n + 1) false)
      | none =>
        match v with
        | .know t =>
          let (head, _) := Pure.collectSpineT t
          match head.symOf? with
          | some σ =>
            match (← get).sctx.lookup σ with
            | some σty => pure (binderModes fuel σty.stripCmp (n + 1))
            | none => pure (List.replicate (n + 1) false)
          | none => pure (binderModes fuel t (n + 1))
        | _ => pure (List.replicate (n + 1) false)

/-- Instantiate an abstract callee's Π-type at the arguments, returning the result
    type. This is `synthSpine` with the errors kept apart: a mistyped argument and
    an over-applied callee are different rejections, and `synthSpine`'s `none`
    collapses them. -/
def instantiatePi : Nat → Term → List Val → M Term
  | 0, _, _ => throwErr "call: out of fuel (Π instantiation)"
  | _, ty, [] => pure ty
  | fuel + 1, ty, a :: rest =>
    match Pure.whnf fuel ty with
    | .pi x dom cod => do
      if ← hasType fuel a dom then
        instantiatePi fuel (Pure.openBinder fuel x cod (subsKnowledge a)) rest
      else throwErr s!"call: argument ({a.pretty}) does not have its parameter type ({dom.pretty})"
    | other => throwErr s!"call: too many arguments — the callee's type is {other.pretty}, not a function type"

/-- Audit every explored path of a sealed body, and return the fresh supplies
    advanced past everything those paths minted.

    The advance is the whole of what survives frame isolation: a sealed body's Ω,
    obligations and groups are ITS OWN and are discarded, but its σ, loan, group
    and frame ids must never be handed out again, or a later mint would collide
    with one that is still referenced by a type the check produced. -/
def auditAllPaths : Nat → Term → List (Except String (Val × St)) → St → M St
  | _, _, [], acc => pure acc
  | _, _, .error e :: _, _ => throwErr e
  | fuel, ret, .ok (v, st) :: rest, acc =>
    match (auditAction fuel ret v).run st with
    | .error e _ => throwErr e
    | .ok _ st' =>
      auditAllPaths fuel ret rest
        { acc with nextLoan := max acc.nextLoan st'.nextLoan
                   nextSym := max acc.nextSym st'.nextSym
                   nextGroup := max acc.nextGroup st'.nextGroup }

/-- **`auditAllPaths` that carries the breadcrumb OUT of the sealed body.**

    A function body is checked inside a seal, on its own `St`, and the audit
    throws a plain `String` into the ENCLOSING state — whose breadcrumb points at
    the `fn` statement, not at the statement inside the body that failed. So every
    rejection from inside any `fn` used to report at the declaration at best, which
    is where most real code lives and therefore where the localization is worth
    the most.

    This writes the failing path's breadcrumb into the enclosing state on the way
    out, at both throw sites: the ⇒-walk's own rejection (which arrives as a
    `Diag`) and the audit's (which has the path's `St` in hand and so knows the
    same thing). Nothing else changes — the message and the accept/reject are the
    same, and a body that checks pays nothing.

    The breadcrumb crossing a seal boundary is sound precisely because it is NOT
    σ-bearing: it is a key into a source table, no value is observed through it,
    and the frame isolation this function exists to enforce is about Ω,
    obligations and groups, none of which it touches. -/
def auditAllPathsD : Nat → Term → List (Except Diag (Val × St)) → Ledgers → St → M St
  | _, _, [], _, acc => pure acc
  | _, _, .error d :: _, _, _ => do
    modify fun s => { s with stmtKey := d.stmtKey, argKey := d.argKey, trail := d.trail }
    throwErr d.msg
  | fuel, ret, .ok (v, st) :: rest, base, acc =>
    match (auditAction fuel ret v).run st with
    | .error e sErr => do
      modify fun s =>
        { s with stmtKey := sErr.stmtKey, argKey := sErr.argKey, trail := sErr.trail }
      throwErr e
    | .ok _ st' =>
      auditAllPathsD fuel ret rest base
        { acc with nextLoan := max acc.nextLoan st'.nextLoan
                   nextSym := max acc.nextSym st'.nextSym
                   nextGroup := max acc.nextGroup st'.nextGroup
                   -- THE HOVER TABLE CROSSES THE SEAL, for the same reason and by
                   -- the same argument as the breadcrumb above (docs/16, docs/05
                   -- pillar B): a `fn` body is where the corpus lives, so a table
                   -- that stopped at the seal would give `x : τ` tooltips to toy
                   -- programs and nothing else. It is a binder ↦ description map,
                   -- not σ-bearing state; the frame isolation this function
                   -- enforces is about Ω, obligations and groups, and it touches
                   -- none of them.
                   --
                   -- `base` is the entry length, so each path contributes only its
                   -- OWN entries and the enclosing ones are not copied per path.
                   -- Prepending keeps the earliest path's entries last in the
                   -- newest-first list, which is what makes the surface's
                   -- first-path rule come out right after its reverse.
                   -- ONE CARRY FOR EVERY LEDGER (docs/17). This line used to be
                   -- one per channel, added after the fact each time a channel
                   -- was found to be dying at the seal — three for three. It is
                   -- now a unit, so a fourth channel is a field on `Ledgers` and
                   -- crosses without touching this function.
                   --
                   -- `closePath`, not `append`: each body path's deltas stay a
                   -- path of their own instead of being concatenated into one
                   -- stream. Appending was the settled shape and was wrong —
                   -- see `Ledgers.paths`.
                   ledgers := Ledgers.closePath st'.ledgers
                                (Ledgers.own st'.ledgers base) acc.ledgers }

/-! ## §8's globals: what a function body may name besides its own binders

    §7 cost 2 admits "closed" function values — "arms reference only their own
    binders **and globals**" — and until M26-E there were no globals, because the
    callees lived in the declaration table and were reached by name. §8 deletes
    the table and puts them in scope instead ("a caller sees exactly the bindings
    lexically above it"), so the phrase acquires a referent: a body's free
    variables are its **callees**, resolved against the enclosing Ω.

    That line USED to be drawn at what the body can do with the binding: a
    function is called (a place read — the call rule locates its callee, never moves
    it), while data is moved, borrowed or written, so a `globalKind` predicate
    admitted exactly the function VALUES and everything else kept M26-C's
    rejection. **M31 Stage A (§2.4) replaced that with the binder's MODE**, and
    the predicate is gone with it (M31 Stage C): a λ body may name its own binders
    and the capital bindings in scope, which subsumes the function case — a
    function is a comptime binding — and additionally admits proofs and snapshots,
    which is what makes §2.4's migration writable. `admitGlobals` below is the
    whole rule now; the value-directed test it superseded is recorded there in the
    one place a reader looking at the rule will meet it. -/

/-- Resolve a function body's free variables against the enclosing scope, and
    return the bindings — the globals it is entitled to name. Rejects a free
    variable that names nothing, and one that names a binding which is not a
    function (that is capture, and it stays deferred).

    Returned as an `Omega` because both callers need the bindings themselves and
    not merely permission: the checking side seeds them into the sealed body's
    own fresh Ω (frame isolation keeps the locals out and lets the globals
    through), and the executing side leaves them where they are — its `keep` set
    is these same ids. -/
def admitGlobals (what : String) (nbinders : Nat) (free : List Var) : M Omega := do
  let st ← get
  free.foldlM (fun acc x => do
    if acc.any (fun kv => kv.1.name == x.name) then pure acc
    else
      -- **THE CITATION RULE** (M31 Stage A, §2.4). The test is the binder's MODE,
      -- and it is asked before the lookup because it is a fact about the name
      -- rather than about what the name happens to hold.
      --
      -- This dissolves the old check rather than relocating it. `admitGlobals`
      -- used to admit exactly the FUNCTION values (`globalKind`) and refuse
      -- everything else as the deferred environment capture — "may name a
      -- function to call it, captures nothing". Under M31 the exemption IS the
      -- rule: functions are comptime, so naming one is comptime capture, and what
      -- is left to say is simply that a λ body may reference its own binders and
      -- the capital bindings in scope, nothing more and nothing less.
      --
      -- What that buys, beyond one rule where there were two: a λ may now close
      -- over a PROOF or a snapshot (`let H0 = *hd`), which is what makes §2.4's
      -- migration writable at all. Nothing is lost by it — comptime bindings are
      -- immutable, so capture and eager inlining are indistinguishable, and the
      -- freeze merely becomes visible as a binding.
      -- The LOOKUP comes first, and the order is load-bearing: a name that is
      -- bound nowhere is a forward reference, and saying "it is lowercase" of one
      -- would diagnose the wrong thing about a program whose real problem is that
      -- the name does not exist.
      match findSlot? st.env x with
      | none =>
        throwErr s!"{what}: the body mentions {x.name}#{x.id}, which is none of its {nbinders} binder(s) and is not bound anywhere above it. §8 makes SCOPE the call table — a body may call the functions bound lexically above it, and a let-chain cannot reference downward, so a forward reference is unwritable rather than merely rejected."
      | some kv =>
        if !x.isComptime then
          throwErr s!"{what}: the body cites '{x.name}', a runtime (lowercase) binding, and a λ body may reference only its own binders and the capital bindings in scope (§2.4). A λ is formed now and used later, and a runtime citation would be an implicit snapshot taken in that gap. Make it a parameter, or name the snapshot first: `let {x.name.capitalize} = …;` above the λ, and cite `{x.name.capitalize}`."
        else pure (acc ++ [kv])) []

/-- **λ formation** (M32 R2/R3, suspensions.md §2.2), and since R3 the ONE
    place a function value comes into being.

    CAPTURE IS A FILTER, not a guard. `admitGlobals` is §8's globals rule and
    §2.4's citation rule — a body may name its own binders and the capital
    bindings in scope — and its RESULT is ρ. Nothing extra had to be written
    to decide what a λ may capture, because that question was already
    answered here; what R2 added is that the answer is kept.

    CLOSEDNESS is therefore not a separate check any more. §7's "arms
    reference only their own binders and globals" used to be a real premise
    because a body was entered under a fresh id window with nothing carried:
    a free variable would be silently rebound to whatever the shift landed
    on. A closure carries its bindings, so the rule survives as the FILTER
    (which bindings are admissible) rather than as a refusal to have any. -/
def mkClosure (fuel : Nat) (node : Term) (ascr : Option Term := none) : M Val := do
    let (tel, _) := Term.peelLams node
    let imper := Term.lamImperative node
    let what := if imper then "λr" else "λ"
    let ρω ← admitGlobals what tel.length (Term.freeRVars [] node)
    -- **The knowledge-only invariant, as a rejection with a place to stand.**
    -- R1 made it a fact about `Sem`; here it is a fact about ρ's type, and the
    -- one way to violate it is to cite a capital binding that holds state — a
    -- capital slot holding a borrow. §2.2: captured ρ supplies knowledge only,
    -- and state arrives through arguments.
    let ρ ← ρω.mapM (fun kv => do
      if Val.hasStateMarker kv.2 then
        throwErr s!"{what}: the body captures '{kv.1.name}', which holds {kv.2.pretty} — a λ captures KNOWLEDGE only (§2.2), and that value carries a hole, a loan marker or a borrow. State reaches a body through its arguments, so make it a parameter."
      else pure kv)
    -- **FORMATION EVALUATES THE BODY AS A CHECK** (§2.2), and stores the
    -- syntax. For the comptime fragment that check is the ⇝ reading this arm
    -- used to store; the result is discarded, which is the whole difference
    -- between R2 and cook-at-formation (user-rejected, §3).
    if !imper then do
      collapseCDerefs fuel node
      let _ ← readC fuel node
      pure ()
    pure (.closure ρ node ascr)

/-- **The pure lift** (§1.3): on the borrow-free fragment ⇒ coincides with ⇝ up
    to variable consumption, so a comptime-only former — a proof term, an
    eliminator application, `Id A a b`, a type — is read by ⇝ and handed back as
    an ordinary runtime datum. It can be stored in a constructor field, passed to
    a call, or returned. (Snapshot reads are non-destructive; that is the "up to
    consumption" — these values are copyable/erasable, so nothing is moved out.)

    **suspensions.md §2.5 wanted the function invariant enforced HERE — "the pure
    lift's result must be data, not a function" — and the corpus refuted it.**
    Recorded at the site rather than in a log, because the next reader will have
    the same idea. The refusal was written, and quicksort's count equation went
    red: what the lift returns at `Direct.lean:1592` is

        λ(§0 : Nat). boolRec … (j Nat … Refl …) …

    — the PROOF of `Π (n : Nat) → Id Nat (Count n …) (Count n …)`, computed by
    lifting a lemma spine. A proof of a ∀-statement is a λ, this calculus returns
    them in Σ tails, and the pure lift is how they are read. There is no
    reformulation that separates them from `Add 1` here, because there is nothing
    to separate: both are functions, and only one of them is being BOUND at a
    runtime binder. So the rule lives where the binder is (`readR`'s `.letIn`),
    and it is still ONE point.

    **M33, THE TERMINAL ATTEMPT: the lift's result must be DATA.** `readR`'s λ arm
    refuses a λ that is WRITTEN (M33's destination rule); this refuses one that is
    COMPUTED, and the two together are §2.5's rule with nothing outside them. The
    shape is `Add 1` — a spine, not a λ, until it is evaluated, at which point it
    is `λ (B : Nat). natRec …`. R3 measured this refusal twice and R3b once, and
    each time the corpus said no: "what it returns is the PROOF of `Π (n : Nat) →
    Id Nat …`, and there is no reformulation that separates them from `Add 1`
    here". That reading was right and is what §2.7 answers — not by separating
    proofs from computations, which this calculus cannot do, but by giving every
    position that legitimately holds a function a way to SAY SO. A function
    arriving here is a function arriving at the move arrow. -/
def pureLift (fuel : Nat) (t : Term) : M Val := do
  let v ← readC fuel t
  match Pure.whnf fuel v with
  | .lam _ _ _ =>
    throwErr s!"⇒ produced a function value ({v.pretty}) — a λ is knowledge and needs a comptime destination: a capital `let`, a ⇝ parameter, a Σ0 component or tail, or an ascription. A PARTIAL APPLICATION is a function too (`Add 1` awaits its second argument), which is why this fires on a spine that was not written as a λ. Bind it to a capital name first, pass it at a capital parameter, put it under a `Σ0` tail, or ascribe it."
  -- **…and the lift's result must not be a TYPE either** (types-no-exec,
  -- 2026-08-20): the λ arm's sentence, completed. `readR`'s arm removal
  -- refuses a type former WRITTEN at ⇒; this refuses one COMPUTED — a
  -- projection or eliminator spine that whnf's to `Nat`, or an APPLIED former
  -- like `List Nat`, which is an `.app` spine and so can only be caught here,
  -- by its head. Everything else the `.app` arm sends over still lifts: a
  -- stuck `natRec P z s σ` is a runtime list value in checking mode, an
  -- `arrCat xs ys` is a runtime array value, and neither has a type-former
  -- head (`Pure.typeFormerHead`).
  | w =>
    if Pure.typeFormerHead w then
      throwErr s!"⇒ produced a type ({v.pretty}) — a ⇝ form with no ⇒ reading (a type has no runtime representation, so it cannot be moved into a runtime slot). Give it a comptime destination: a capital `let`, a ⇝ parameter, a capital Σ component, or an ascription."
    else pure (.know v)

/-! ## Seal sites, and the σ a site has (M32 R3, suspensions.md §2.4)

    §2.4 makes the seal ⇝-evaluable, and the whole of what that needed is a
    forgetting half that is a FUNCTION of the node rather than of the moment.
    The node's half of the argument is `Term.seal`'s site, assigned once at the
    program boundary. This is the other half: what the site is applied to.

    **The inputs are the values the seal READS.** A seal's own free runtime
    variables are exactly the slots its check consults — `readC u` and `readC t`
    resolve `.var` through Ω, and `checkRFnBody` seeds its fresh Ω from
    `admitGlobals` over the same set — so two readings of one site that agree on
    them agree on everything the check can see, and therefore on its outcome.
    That is the argument that licenses the table to be a memo rather than a
    cache with a soundness hole: a hit skips a check whose answer is already
    determined, not one that might have changed.

    **What a hit buys, beyond ⇝-legality**: the audit of a `fn` runs once per
    (site, inputs) rather than once per reading, which is what makes a sealed
    function inside a body entered twice cost what it costs inside a body
    entered once. -/

/-- The identity of one sealed value: its site, and what that site was read at. -/
abbrev SealKey := Nat × List Val

/-- The captured inputs of a seal node: what each of its free runtime variables
    holds, in the order the term mentions them. A citation Ω cannot resolve
    contributes nothing — the check that follows is what reports it, and with
    the message that names the citation rather than the table. -/
def sealInputs (t : Term) : M (List Val) := do
  let ω ← getEnv
  pure ((Term.freeRVars [] t).filterMap (fun x => (findSlot? ω x).map (·.2)))

/-- The σ this site has at these inputs: the one already recorded, or a fresh
    one recorded now.

    Minting on a MISS, from `nextSym`, is what keeps the numbering the ⇒-seal
    produced: a program whose seals are read in program order — a let-chain of
    declarations, which is every program — allocates them in exactly the order
    and at exactly the moment `sealMint`'s `freshSym` did. -/
def sealSym (key : SealKey) : M Nat := do
  let st ← get
  match st.sealSites.find? (fun e => e.1.1 == key.1 && e.1.2 == key.2) with
  | some e => pure e.2
  | none => do
    let σ ← freshSym
    modify (fun s => { s with sealSites := (key, σ) :: s.sealSites })
    pure σ

/-! ## The join seam's helpers (docs/19 v2)

    Plain defs — the drivers live in the mutual below, these do not recurse
    into it. -/

/-- Rebuild the FORK shape for a statement match that will be walked
    SINGLE-PATH — a concrete scrutinee (⇒, or checking selection) and the
    one-branch match (where fork ≡ join exactly): the arm body, the binder, and
    the continuation behind the `@armScope`/`@popArmL` seam the pre-pass used
    to build. `let` form. -/
def pushJoinArms (x : Var) (rest : Term) (bs : List Branch) : List Branch :=
  bs.map (fun br => Branch.mk br.ctor br.binders
    (.seq (.const "@armScope") (.letIn x br.body (.seq (.const "@popArmL") rest))))

/-- As `pushJoinArms`, `seq` form (`@popArm`, no binder survives the arm). -/
def pushJoinArmsSeq (rest : Term) (bs : List Branch) : List Branch :=
  bs.map (fun br => Branch.mk br.ctor br.binders
    (.seq (.const "@armScope") (.seq br.body (.seq (.const "@popArm") rest))))

mutual
  /-- Marker-free: knowledge and constructor nodes only — no holes, loans,
      borrows, closures. What the join's value rules may pass or type. -/
  def pureValP : Val → Bool
    | .know _ => true
    | .node _ args => pureValListP args
    | _ => false
  termination_by v => sizeOf v
  def pureValListP : List Val → Bool
    | [] => true
    | v :: vs => pureValP v && pureValListP vs
  termination_by vs => sizeOf vs
end

/-- Does `t` avoid every σ in `[lo, hi)`? An arm-minted σ may not cross the
    seam: two arms mint from the SAME counter, so the same id can mean two
    different things (both arms of an `if` mint their equation at one id), and
    a value or type citing one would smuggle arm-local meaning into the joined
    state. Probed by substitution rather than a dedicated collector. -/
def symFreeIn (lo hi : Nat) (t : Term) : Bool :=
  (List.range (hi - lo)).all (fun i =>
    Term.beq (Term.substSym (lo + i) (.const "@joinProbe") t) t)

/-- The closed constructor basis's head types — rule (b)'s synthesis for
    constructor-headed values. Parametrized heads (`Cons`…) are NOT here: their
    parameter is not synthesizable from a value, so they fall through to the
    pack rule or the rejection. -/
def ctorHeadTy? : String → Option Term
  | "True" | "False" => some (.const "Bool")
  | "Z" | "S" => some (.const "Nat")
  | "unit" => some (.const "Unit")
  | _ => none

/-- A candidate type for one arm's value: a bare σ reads its type from that
    ARM's exit `sctx`; a constructor-headed value from the closed basis. -/
def joinHeadTy? (v : Val) (sctxA : List (Nat × Term)) : Option Term :=
  match v.symOf? with
  | some σ => sctxA.lookup σ
  | none =>
    match subsKnowledge v with
    | .ctorApp c _ => ctorHeadTy? c
    | t =>
      match Pure.collectSpineT t with
      | (.const c, _) => ctorHeadTy? c
      | _ => none

/-- Merge the arms' minted state into the join base: counters past every arm's
    (the `auditAllPathsD` move), seal-site keys unioned (a σ a nested seal was
    handed inside an arm stays spoken for), and each arm's diagnostic ledger
    closed as its own sub-path (the seal carry's rule — paths stay separate). -/
def mergeArmMints (base : St) (exits : List St) : St :=
  exits.foldl (fun a s =>
    { a with nextLoan := max a.nextLoan s.nextLoan,
             nextVar := max a.nextVar s.nextVar,
             nextSym := max a.nextSym s.nextSym,
             nextGroup := max a.nextGroup s.nextGroup,
             sealSites := s.sealSites.foldl (fun acc e =>
               if acc.any (fun e2 => e2.1.1 == e.1.1 && e2.1.2 == e.1.2) then acc
               else e :: acc) a.sealSites,
             ledgers := Ledgers.closePath s.ledgers
                          (Ledgers.own s.ledgers base.ledgers) a.ledgers }) base

/-- End every loan an ARM minted (id ≥ `lo`), innermost (latest) first — the
    loan-ending half of the seam pop, run on the arm's exit state so a borrow
    scrutinee's payload collapses back to a VALUE the ladder can read. Loans
    the arm inherited (id < `lo`) are the continuation's business, not the
    arm's, and are left alone. -/
def collapseArmLoansFrom (fuel : Nat) (lo : Nat) : M Unit := do
  let hi := (← get).nextLoan
  for i in List.range (hi - lo) do
    let ℓ := hi - 1 - i
    if (← getEnv).any (fun kv => (findBorrowPayload ℓ kv.2).isSome) then
      endLoan fuel ℓ

/-- **Anti-unification for the pack heuristic** (docs/19 v2 rule (c)). Join the
    arms' candidate TYPES: a position where every arm agrees stays; a position
    where each arm's subterm is that arm's OWN first-component value (or an
    already-minted σf hole from an earlier fold step) becomes `σf`; same-shaped
    nodes recurse; anything else fails the heuristic — whole-term abstraction is
    NOT enough, because a value like `True` also occurs INSIDE an unfolded
    `Leb` spine and blanket replacement mangles each arm differently (found by
    the flagship `Pair(True, e)` case itself). Pure-fragment node coverage;
    an exotic head fails closed. -/
partial def antiUnify (σf : Nat) : List (Term × Term) → Option Term
  | [] => none
  | ts@((t0, _) :: rest) =>
    if ts.all (fun (t, r) => Term.alphaEq t r || Term.beq t (.sym σf)) then some (.sym σf)
    else if rest.all (fun (t, _) => Term.alphaEq t t0) then some t0
    else
      let zip1 := fun (f : Term → Term) (get : Term → Option Term) => do
        let sub ← antiUnify σf (← ts.mapM (fun (t, r) => (get t).map ((·, r))))
        pure (f sub)
      let zip2 := fun (f : Term → Term → Term)
                      (g1 : Term → Option Term) (g2 : Term → Option Term) => do
        let s1 ← antiUnify σf (← ts.mapM (fun (t, r) => (g1 t).map ((·, r))))
        let s2 ← antiUnify σf (← ts.mapM (fun (t, r) => (g2 t).map ((·, r))))
        pure (f s1 s2)
      match t0 with
      | .app _ _ => zip2 .app
          (fun t => match t with | .app f _ => some f | _ => none)
          (fun t => match t with | .app _ a => some a | _ => none)
      | .idT _ _ _ => do
        let ga := fun (t : Term) => match t with | .idT a _ _ => some a | _ => none
        let gb := fun (t : Term) => match t with | .idT _ b _ => some b | _ => none
        let gc := fun (t : Term) => match t with | .idT _ _ c => some c | _ => none
        let sa ← antiUnify σf (← ts.mapM (fun (t, r) => (ga t).map ((·, r))))
        let sb ← antiUnify σf (← ts.mapM (fun (t, r) => (gb t).map ((·, r))))
        let sc ← antiUnify σf (← ts.mapM (fun (t, r) => (gc t).map ((·, r))))
        pure (.idT sa sb sc)
      | .ctorApp c args0 => do
        let argss ← ts.mapM (fun (t, r) => match t with
          | .ctorApp c2 args => if c2 == c && args.length == args0.length
                                then some (args, r) else none
          | _ => none)
        let joined ← (List.range args0.length).mapM (fun i =>
          antiUnify σf (argss.map (fun (args, r) => (args[i]!, r))))
        pure (.ctorApp c joined)
      | .cmpT _ => zip1 .cmpT (fun t => match t with | .cmpT u => some u | _ => none)
      | .pi n _ _ => zip2 (.pi n)
          (fun t => match t with | .pi n2 d _ => if n2 == n then some d else none | _ => none)
          (fun t => match t with | .pi n2 _ b => if n2 == n then some b else none | _ => none)
      | .sigmaT n _ _ => zip2 (.sigmaT n)
          (fun t => match t with | .sigmaT n2 d _ => if n2 == n then some d else none | _ => none)
          (fun t => match t with | .sigmaT n2 _ b => if n2 == n then some b else none | _ => none)
      | .lam x _ _ => zip2 (.lam x)
          (fun t => match t with | .lam x2 d _ => if x2 == x then some d else none | _ => none)
          (fun t => match t with | .lam x2 _ b => if x2 == x then some b else none | _ => none)
      | _ => none

/-- **THE LADDER** (docs/19 v2 §2): join one slot's (or the result's) values
    across the arms, conservatively.

      1. a base value every arm left `Val.beq`-identical → the base (lossless);
      2. `⊥` anywhere on top → `⊥` (conditional move = moved after);
      3. borrows: same loan in every arm → recurse on the payloads (owed type
         as the synthesis source); anything else structural → reject;
      4. marker-free values that CONVERT across arms, citing no arm-minted σ →
         pass the agreed value through (lossless — this is what keeps agreeing
         arms free);
      5. a synthesizable common type (arm `sctx` for σs, the closed basis for
         constructor heads) → fresh σ at it;
      6. `Pair` values → the dependent-pack heuristic: join components left to
         right; when a component joins at a fresh σ, LATER components' candidate
         types first abstract that component's per-arm VALUE into the σ
         (`Term.abstractInto`) — `Pair(True, e)`/`Pair(False, e)` joins at
         `Σ (b : Bool). Id … b` with no annotation;
      7. otherwise reject, naming the slot, the arms, and the remedy.

    `arms` pairs each arm's value with (its exit `sctx`, its σ-mint range).
    `where` is the slot's name for the error; `ctors` label the arms. -/
def joinVal (slotName : String) (ctors : List String) (st0sctx : List (Nat × Term))
    (lo : Nat) :
    Nat → Option Val → List (Val × List (Nat × Term) × Nat) → Option Term → M Val
  | 0, _, _, _ => throwErr "join: out of fuel (value ladder)"
  | _, _, [], _ => throwErr s!"join: no arms at {slotName} (unreachable)"
  | fuel + 1, base?, arms@((v0, sctx0, hi0) :: restArms), tySrc => do
    let vs := arms.map (·.1)
    let disagreeMsg := s!"join: the arms disagree at {slotName} ({String.intercalate ", " (ctors.zip vs |>.map (fun (c, v) => s!"{c} ⇒ {v.pretty}"))}) and no common type is synthesizable — make the match return the disagreement as data (with its evidence, e.g. a Pair carrying a branch equation), or restructure into one match"
    -- (1) untouched slot
    if let some b := base? then
      if vs.all (fun v => Val.beq v b) then return b
    -- (2) conditional move
    if vs.any (fun v => match v with | .bot => true | _ => false) then return .bot
    -- (3) borrow structure
    match base? with
    | some (.borrowM ℓ pb) =>
      let pays ← arms.mapM (fun (v, sctxA, hiA) => do
        match v with
        | .borrowM ℓ2 p =>
          if ℓ2 == ℓ then pure (p, sctxA, hiA)
          else throwErr s!"join: the arms disagree at {slotName} — the slot holds DIFFERENT loans per arm (ℓ{ℓ} vs ℓ{ℓ2}); a borrow chosen per-branch needs loan-set borrows, which are out of scope — restructure so both branches leave the same borrow"
        | _ => throwErr s!"join: the arms disagree at {slotName} — a borrow in one arm is {v.pretty} in another; restructure so the branches leave the same shape")
      -- the owed type: the loan's debt if the caller recorded one, else the
      -- payload σ's own type in the pre-split sctx
      let tySrc2 := tySrc.orElse (fun _ => pb.symOf?.bind (st0sctx.lookup ·))
      let p ← joinVal slotName ctors st0sctx lo fuel (some pb) pays tySrc2
      return .borrowM ℓ p
    | _ =>
    if !(vs.all pureValP) then throwErr disagreeMsg
    -- (4) agreeing pure values, arm-σ-free
    let armFree := arms.all (fun (v, _, hiA) => symFreeIn lo hiA (subsKnowledge v))
    if armFree && vs.all (fun v => Pure.convert fuel (subsKnowledge v) (subsKnowledge v0)) then
      return v0
    -- (6, tried before 5 for Pairs) the dependent-pack heuristic
    match vs.mapM Val.asCtor? with
    | some cs =>
      if cs.all (fun c => c.1 == "Pair" && c.2.length == 2) then do
        let fsts := (arms.zip cs).map (fun ((_, sctxA, hiA), c) => (c.2[0]!, sctxA, hiA))
        let snds := (arms.zip cs).map (fun ((_, sctxA, hiA), c) => (c.2[1]!, sctxA, hiA))
        let fst ← joinVal (slotName ++ ".1") ctors st0sctx lo fuel none fsts none
        match fst.symOf? with
        | none => do
          let snd ← joinVal (slotName ++ ".2") ctors st0sctx lo fuel none snds none
          return .ctor "Pair" [fst, snd]
        | some σf => do
          -- σf is fresh: ANTI-UNIFY the later components' types across the
          -- arms — agreement stays, each arm's own first-component value (at a
          -- position where the arms disagree) becomes σf, mismatched shapes
          -- fail the heuristic
          let cands ← snds.foldlM (fun acc (v, sctxA, hiA) => do
            match joinHeadTy? v sctxA with
            | none => throwErr disagreeMsg
            | some τ => pure (acc ++ [(τ, subsKnowledge (fsts[acc.length]!).1, hiA)])) []
          match antiUnify σf (cands.map (fun (τ, r, _) => (τ, r))) with
          | none => throwErr disagreeMsg
          | some τj => do
            if !(cands.all (fun (_, _, hiA) => symFreeIn lo hiA τj)) then throwErr disagreeMsg
            let σs ← freshSym
            modify fun st => { st with sctx := (σs, τj) :: st.sctx }
            return .ctor "Pair" [fst, .know (.sym σs)]
      else joinFreshTyped fuel arms tySrc disagreeMsg
    | none => joinFreshTyped fuel arms tySrc disagreeMsg
  termination_by fuel _ _ _ => fuel
where
  /-- (5) a fresh σ at a synthesized common type: the owed/declared source when
      one exists, else the first arm's head synthesis — then every arm's value
      must actually HAVE the candidate type (`hasType`, the checker's own
      judgment — not per-arm re-synthesis, which would refuse `Nil` at
      `List Nat` for wanting a parameter it cannot invent). -/
  joinFreshTyped (fuel : Nat)
      (arms : List (Val × List (Nat × Term) × Nat)) (tySrc : Option Term)
      (disagreeMsg : String) : M Val := do
    let cand? := tySrc.orElse (fun _ =>
      match arms with
      | (v0, sctx0, _) :: _ => joinHeadTy? v0 sctx0
      | [] => none)
    match cand? with
    | none => throwErr disagreeMsg
    | some τ => do
      if !(symFreeIn lo ((arms.map (·.2.2)).foldl max lo) τ) then throwErr disagreeMsg
      -- an arm's value is typed in the ARM's context — its σs live in the
      -- arm's exit sctx, not the join's
      let oks ← arms.mapM (fun (v, sctxA, _) => do
        let saved := (← get).sctx
        modify fun st => { st with sctx := sctxA }
        let ok ← hasType fuel v τ
        modify fun st => { st with sctx := saved }
        pure ok)
      if !(oks.all id) then throwErr disagreeMsg
      let σ ← freshSym
      modify fun st => { st with sctx := (σ, τ) :: st.sctx }
      pure (.know (.sym σ))

/-! ## ⇒ (read): the move arrow

    `readR` evaluates a term to a value with move semantics. Fuel decreases on
    every recursive call (including the End-Mut retry and the constructor-args
    loop), so the machine is total; the list helper `readArgs` keeps the
    constructor case structural.

    **Heartbeats.** M26-C grew this block from five functions to twelve — the
    explore driver joined it (readR and explore are mutual now, §8's direction),
    and the seal's audit brought `sealFn`/`checkRFnBody`/`callDeclC` with it — and
    the default budget is not enough for the well-founded-recursion proof over
    twelve measures. This is elaboration cost, not checker cost: no program pays
    it. -/
set_option maxHeartbeats 1000000 in
mutual
  def readR : Nat → Term → M Val
    | 0, _ => throwErr "readR: out of fuel"
    | fuel + 1, t =>
      match t with
      | .var x => do
        -- §6's fence, first: a ⇒-read of a variable is a MOVE, and a comptime
        -- binder is erased — there is nothing at runtime to move. This is the
        -- rejection R16's staging pains were the absence of: with it, the only
        -- way a capital binder reaches a call is the capital argument position,
        -- which reads it by ⇝ and leaves it where it was.
        --
        -- **BOTH MACHINES AGAIN** (M33 Σ0's prerequisite), and the gate that was
        -- here is worth recording because its removal is the prerequisite's whole
        -- point rather than a tidy-up.
        --
        -- M33a made this line checking-side-only. A body's tail is read against
        -- its return type — `readResult`, where a capital Σ binder makes its
        -- component ⇝-read — and `retTyVal` was `checkRFnBody`'s alone, so the
        -- EXECUTING machine entered a callee through `applyClosure` with no
        -- return type in hand and ⇒-read the same tail. With the flagship's proof
        -- components capital, `Pair(hi, Pair(Hub2, …))` was then a ⇒-move of a
        -- capital binding, and nine executing differentials died on a discipline
        -- the checker had already enforced on that very program. The gate was the
        -- honest response to an ASYMMETRY, not to a disagreement about the rule.
        --
        -- The asymmetry is gone: an executing closure carries its ascription
        -- (`Val.closure`'s third field, `sealExec`), `applyClosure` peels the
        -- return type off it (`calleeRetTy`) and reads the tail with
        -- `readRTail`, so a comptime component is ⇝-read on both sides and never
        -- reaches this line. Measured: with the gate removed the corpus is green,
        -- those nine differentials included. Erasure is one rule for two machines
        -- again — which is what the Σ0 tail needs, since a rule stated on a
        -- tail's MODE has to be a rule both machines can read.
        fenceComptime x "cannot be ⇒-moved"
        match ← lookupSlot x with
        -- The M26-B pointer, in the one message that R16's pain surfaces at: a
        -- proof consumed by a call is reported here, one line later, and the fix
        -- is at the CALLEE's declaration rather than anywhere near the report.
        | .bot => throwErr s!"readR: {x.name}#{x.id} holds ⊥ (use-after-move or uninitialized). If a CALL moved it and that callee only needs it in types or proofs, capitalizing the callee's parameter makes the argument a ⇝-read, which consumes nothing (§6)."
        | v =>
          -- A value with a loan marker in owned position cannot be moved: end
          -- it first (End-Mut), then retry. This is the lazy chain-collapse —
          -- a top-level loanM (§2.2/§2.5) and a Cons of field-loans left by a
          -- borrow-mode match (§3.3) are the same case.
          match firstLoanMarker v with
          | some ℓ => do endLoan fuel ℓ; readR fuel (.var x)
          | none => do
            -- **THE FUNCTION-READ REFUSAL IS GONE** (M31 Stage A), and what stood
            -- here is worth recording because the deletion is a change of model
            -- rather than a relaxation.
            --
            -- It said: functions are reached by NAME (M27 α.2), so the one move
            -- forbidden is reading a function out of its slot into a second
            -- binding — `let g = ih`. That rule existed because a function had no
            -- mode: it lived in a runtime slot, so a second runtime binding of it
            -- was a second OWNER, and M27's third containment (c1's curry probe)
            -- had measured the resulting simulation break on an accepted program
            -- (`f = ⊥` checking, the λ-spine executing).
            --
            -- M31 gives functions a mode, and that dissolves the premise rather
            -- than the symptom. A function binding is comptime: ⇝-read, erased,
            -- never ⇒-consumed. So reading one is not a move at all — `let F =
            -- Main` copies knowledge and leaves the original exactly where it was
            -- — and there is no second owner for the two machines to disagree
            -- about. What IS still wrong is binding a function to a runtime slot,
            -- which is a claim about the BINDER — and since M32 R3 nothing says
            -- it, because nothing has to: ⇒ cannot construct a function and
            -- cannot read one out of a capital binding, so no function ever
            -- reaches a runtime slot to be refused there.
            --
            -- §2.1 copy-on-read: an INDEX-KIND value (a Nat/Bool/Unit tree, a
            -- proof, a type, a λ, or a σ typed as one of these) is read by COPY,
            -- leaving the owner intact — the ownership machinery is doubly vacuous
            -- on it (marker-free AND erasure-bound), and it is what lets a comptime
            -- index be used more than once. Data proper moves even when
            -- marker-free (Rust's line — §2.1).
            if indexKindV fuel (← get).sctx v then pure v
            -- §19: moving a borrow whose PAYLOAD is a suspended reborrow (a `&mut
            -- *v` handed to a call that has since returned) must first end that
            -- reborrow, so its mutations flow back into the payload before the
            -- move. Mirrors the match-scrutinee "reborrowed payload: end, retry".
            else match v with
            | .borrowM _ payload =>
              match firstLoanMarker payload with
              | some ℓ' => do endLoan fuel ℓ'; readR fuel (.var x)
              | none => do setSlot x .bot; pure v
            | _ => do setSlot x .bot; pure v            -- move out, leave ⊥
      | .deref t' => do
        -- take: read the payload through the borrow, leaving a hole (⊥) in it.
        --
        -- §5.2's "proper payload" premise, on the ⇒ side (M23). A payload holding a
        -- parked loan is a SUSPENSION, not a value — a `&mut *v` handed to a call
        -- that has since returned, or a field reborrow from a borrow-mode match. The
        -- take is a demand like any other, so it collapses first: End the reborrow
        -- (innermost-first, as the `.var` move's payload loop and the match
        -- scrutinee's reorganization already do), then retry. Without this the
        -- MARKER itself is taken and rides on as if it were a value — the same
        -- silent-marker class as the ⇝-side gap M23-ii closed and §3.2's
        -- `⊥`-into-a-pure-value bug, and the one that made `let lo = *v` after a
        -- recursive call put `loanₘ ℓ` where the partition's count proof expected
        -- the callee's released list.
        let pos ← placeToPos fuel (.deref t')
        match ← getAtPos fuel pos with
        | .bot => throwErr "readR(*): borrow payload is already a hole (⊥) — nothing to take"
        | p =>
          match firstLoanMarker p with
          | some ℓ => do endLoan fuel ℓ; readR fuel (.deref t')
          | none => do setAtPos fuel pos .bot; pure p
      | .ctorApp name args => do
        pure (.ctor name (← readArgs fuel args))
      | .borrow t' => do
        -- §6's fence. `&mut X` is a runtime capability over an erased binder;
        -- and symmetrically, a borrow-TYPED binder must be lowercase, which
        -- `seedTelescope`/`processArgs` check at the declaration and the call.
        fencePlace t' "cannot be borrowed (`&mut`)"
        let pos ← placeToPos fuel t'
        match ← getAtPos fuel pos with
        | .bot => throwErr "&mut: target place holds ⊥ (nothing to borrow)"
        | .loanM ℓ => do endLoan fuel ℓ; readR fuel (.borrow t')   -- suspended: demand-end the group, then reborrow
        | v =>
          -- §9 executing-mode reborrow fidelity. A value peeled from a
          -- demand-ended suspension can still carry owned FIELD-loan markers
          -- whose borrows hold freshly-mutated payloads: a callee that swapped
          -- through `*v` (nth2 → element reborrows) leaves the swapped elements
          -- in the callee's element-borrows, and demand-ending the single top
          -- loan (the `.loanM ℓ` case above) recovers a `Cons(loanₘ ℓ₂, loanₘ ℓ₃)`
          -- whose element loans are still suspended. Reborrowing that as-is hands
          -- out a value a later comptime `*v` reads stale (`nth Z (*v) = loanₘ ℓ₂`,
          -- so its `leb` scrutinee is stuck). Checking mode collapses these
          -- atomically at group-end; executing mode must End-Mut them here —
          -- innermost-first, exactly as the `.var` move's payload loop does — so
          -- the reborrowed value is fully re-collapsed before the next read sees
          -- it (the M22 mode-equivalence obligation: checking and executing reach
          -- the same state by different routes). Gated on `executing`: a
          -- checking-mode group release is a fresh existential σ or a marker-free
          -- spec value (refineSym enforces marker-freedom), so `firstLoanMarker`
          -- there is always `none` — behaviourally identity for checking mode.
          match (← get).executing, firstLoanMarker v with
          | true, some ℓ' => do endLoan fuel ℓ'; readR fuel (.borrow t')
          | _, _ => do
            let ℓ ← freshLoan
            setAtPos fuel pos (.loanM ℓ)                   -- park the loan marker
            mergeRoot pos.root                             -- the residues re-merge around it
            pure (.borrowM ℓ v)                            -- ownership of v moves into the borrow
      -- A STATEMENT-SHAPE match evaluated by ⇒ (docs/19 v2): the spine keeps
      -- its continuations now, so the seam shape the pre-pass used to build is
      -- built HERE, lazily — one arm is selected (⇒ is concrete), the marker
      -- walk pops the arm scope, and executing behaviour is the old normal
      -- form's by construction.
      | .letIn x (.matchE s eqn bs) rest =>
        readR fuel (.matchE s eqn (pushJoinArms x rest bs))
      | .seq (.matchE s eqn bs) rest =>
        readR fuel (.matchE s eqn (pushJoinArmsSeq rest bs))
      | .letIn x rhs rest => do
        -- **`let X = e` is a comptime binding** (§6): `e` is evaluated under ⇝,
        -- `X` is erased and non-consuming, and the fence confines it to
        -- ⇝-positions. Local spec abbreviations and locally-derived certificates
        -- without a new form — and without the capture-before-call staging that
        -- a runtime `let` of a proof forces. `let x = e` is unchanged.
        --
        -- **The arrow is the BINDER'S CASE, and nothing else** (M32 R3). It used
        -- to be `Var.comptimeRhs`, a predicate on the right-hand side as well,
        -- because two right-hand sides were ⇒-formation events ⇝ had no rule for.
        -- ⇝ has the rules now (`readComptimeVal`), so the predicate is gone and
        -- this line is the invariant.
        letStep fuel x rhs
        readR fuel rest
      | .assign place rhs rest => do
        assignStep fuel place rhs
        readR fuel rest
      -- **One match rule, two drivers** (M33 Σ0's prerequisite): `matchStep` is
      -- what used to be spelled out here, and `readRTail` reaches the same rule
      -- rather than a copy of it.
      | .matchE scrut eqn branches => do readR fuel (← matchStep fuel scrut eqn branches)
      | .seq e rest => do
        seqStep fuel e
        readR fuel rest
      -- **A `.call` never resolves** (M28 D9). §8's scope IS the call table: the
      -- surface turns `f(…)` into a SPINE on the binding lexically above it, so
      -- a `.call` that survives to here names nothing — a forward reference, a
      -- typo, or a function that was never declared. It used to consult `St.decls`,
      -- the J1 bridge for half-migrated programs, and the corpus has no half-
      -- migrated programs left.
      | .call f _ => throwErr s!"call: unknown function '{f}'"
      -- **The seal** (combining-fns §5): opacity as one node. The two readings
      -- are the two machines'. Since M32 R3 there is ONE seal rule and both
      -- arrows call it (`sealNode`); this arm is the executing machine's
      -- transparency plus that call.
      | .seal site t u => do
        if (← get).executing then
          -- Concrete evaluation is always transparent: the body exists and runs.
          -- No check here — execution does not verify, it computes (and the
          -- checker has already accepted the node, or this program was never
          -- admitted). This is why a sealed value costs nothing at runtime, and
          -- why R3's site table is not consulted here: the executing machine
          -- never asks which σ a seal has, because it never has one.
          --
          -- **Transparent is not the same as FORGETFUL** (M33 Σ0's prerequisite,
          -- suspensions.md §2.7): `sealExec`.
          sealExec fuel t u
        else sealNode fuel site t u
      -- **THE DESTINATION RULE** (M33, suspensions.md §2.7): a λ is knowledge and
      -- needs a comptime destination. Reaching HERE is the definition of not
      -- having one — every comptime destination there is routes a λ somewhere
      -- else before ⇒ ever sees it:
      --
      --   * a capital `let` → `readComptimeVal`'s own λ case;
      --   * a ⇝ parameter → `readComptimeArg` (`processArgs`, `readArgsModed`);
      --   * a Σ0 component or tail → `readResult`'s `⇝` arm;
      --   * an ascription → `sealValue`, where a λ is FORMED, not ⇒-read.
      --
      -- What is left is a λ written in a position with nothing to say it is
      -- knowledge — R3's `Pair(SplitANil …, λ (q : Nat). Refl)`, a constructor
      -- ARGUMENT read by `readArgs`, which had no type in hand and so no way to
      -- decide. That is §2.5's FIRST surviving spelling, and Σ0 is what makes
      -- refusing it a rule with a fix rather than a rule with a wall: the fix is
      -- always to give the λ a destination, and the message lists them.
      --
      -- (What stood here was R2's LIFT, with R3's correction recorded on it: "a
      -- proof of a ∀-statement IS a λ, and this calculus returns them in Σ tails
      -- — refusing here rejects the flagship's count equation and `sort2`,
      -- measured". That measurement was correct and is what §2.7 exists to
      -- answer: a Σ tail is now a destination, so the λ never arrives.)
      | .lam _ _ _ => throwErr s!"a λ is knowledge and needs a comptime destination — a capital `let`, a ⇝ parameter, a Σ0 component or tail, or an ascription. This one ({t.pretty}) is in none of them: it is being ⇒-read, which is the arrow that MOVES runtime data, and a function value is not runtime data. Bind it to a capital name first (`let F = λ …`), pass it at a capital parameter, put it under a `Σ0` tail, or ascribe it (`(λ … : Π …)`)."

      | .unit => pure (.ctor "unit" [])
      -- **The match-arm seam** (M31 Stage 0). A single-path walk fuses a
      -- statement-position match with the continuation that followed it
      -- (`pushJoinArms`, built where the match is walked), which
      -- puts the continuation lexically INSIDE each arm and so silently extends
      -- the arm binders' scope over it. These two markers are the seam the fusion
      -- would otherwise erase: they name the point where the arm's own body
      -- ended, and closing the scope there restores the source's lexical reading
      -- (`match x { Cons(h,t) => … }; k` — `h` and `t` are not in scope in `k`).
      --
      -- Two of them because the two splices differ by one binding. The `seq`
      -- splice discards the arm's value, so nothing outlives the arm. The
      -- `letIn` splice binds it — `let y = match x { … }; k` — and `y` is the
      -- ENCLOSING scope's, bound (by `bindSlot`, which appends) as the last entry
      -- at the moment the seam is reached: hence `retain = 1`, and the loans that
      -- value carries out are the `keep` set the drop sweep must not touch.
      -- The arm-scope announcement itself is inert at runtime: it was read off
      -- the arm body by `armSeamed?` when the scope opened.
      | .const "@armScope" => pure (.ctor "unit" [])
      | .const "@popArm" => do popArmScope fuel 0 []; pure (.ctor "unit" [])
      | .const "@popArmL" => do
        let ω ← getEnv
        popArmScope fuel 1 ((ω.drop (ω.length - 1)).flatMap (fun kv => kv.2.loanIds))
        pure (.ctor "unit" [])
      -- **TYPES HAVE NO ⇒ READING** (types-no-exec, 2026-08-20) — and this is
      -- a REVERSAL of the documented §1.3 stance, not a hole closed. The
      -- comment that stood here argued: "on the borrow-free fragment ⇒
      -- coincides with ⇝ up to variable consumption. A comptime-only former (a
      -- proof term — an eliminator application, a Π-typed λ, `Id A a b`, a
      -- type) is an unrestricted value, so ⇒ delegates to ⇝ (`readC`) and
      -- hands back the result as an ordinary runtime datum" — and these five
      -- arms were that delegation's front door, so `let t = Σ (l : Nat). Nat;`
      -- checked and RAN with a type sitting in a runtime slot. The coincidence
      -- argument is true and does not license that: it says the VALUE the two
      -- arrows compute agrees, not that a runtime destination for it exists. A
      -- type has no meaningful runtime representation, so ⇒ has nothing to
      -- move — the ruling removes the reading rather than fencing it, and what
      -- stands here is the same refusal-by-name `.borrowT` and `.cmpT` always
      -- had (Lean match exhaustiveness is why a removed case is spelled as a
      -- named throwErr arm).
      --
      -- **The boundary the lift keeps**: PROOFS and computed DATA still lift;
      -- types and functions do not, each with its own refusal site. A proof
      -- term is admitted exactly as §1.3 said — `Refl` is an ordinary
      -- `ctorApp` (handled above), a stuck eliminator application or a `len`/
      -- `add`/`j` spine reaches `pureLift` through the `.app` arm and lifts as
      -- `.know` — because a proof VALUE is erasable data, not a type. A
      -- Π-typed λ is refused by the destination rule (`readR`'s λ arm WRITTEN,
      -- `pureLift`'s λ case COMPUTED); a type is refused HERE when written and
      -- by `pureLift`'s head test when computed or applied
      -- (`Pure.typeFormerHead` — `List Nat` is an `.app` spine, so arm
      -- removal alone cannot reach it).
      | .type => throwErr "readR (⇒): `Type` is a type — a ⇝ form with no ⇒ reading (a type has no runtime representation, so it cannot be moved into a runtime slot). Give it a comptime destination: a capital `let`, a ⇝ parameter, a capital Σ component, or an ascription."
      | .const c => throwErr s!"readR (⇒): the constant `{c}` is comptime knowledge (a type or a pure former) — a ⇝ form with no ⇒ reading. Give it a comptime destination: a capital `let`, a ⇝ parameter, a capital Σ component, or an ascription."
      | .pvar n => throwErr s!"readR (⇒): pure variable `{n}` is comptime knowledge — a ⇝ form with no ⇒ reading. Give it a comptime destination: a capital `let`, a ⇝ parameter, a capital Σ component, or an ascription."
      | .pi _ _ _ => throwErr s!"readR (⇒): `Π` ({t.pretty}) is a type — a ⇝ form with no ⇒ reading (a type has no runtime representation, so it cannot be moved into a runtime slot). Give it a comptime destination: a capital `let`, a ⇝ parameter, a capital Σ component, or an ascription."
      | .sigmaT _ _ _ => throwErr s!"readR (⇒): `Σ` ({t.pretty}) is a type — a ⇝ form with no ⇒ reading (a type has no runtime representation, so it cannot be moved into a runtime slot). Give it a comptime destination: a capital `let`, a ⇝ parameter, a capital Σ component, or an ascription."
      -- **A recursor over runtime arms is ⇒'s, not ⇝'s** (§7 cost 5). The pure
      -- lift below sends every other application spine to `readC`; one whose arms
      -- are BODIES has no comptime reading at all (`readC` refuses `.lamR`), so ⇒
      -- evaluates the spine itself — arms to runtime function values, the rest by
      -- the ordinary rules — and hands it to `applyR`. Unsaturated (the sealed
      -- `natRec P z s`, three arguments and no scrutinee) that is a value; at a
      -- concrete scrutinee it ι-reduces on the spot.
      | .app _ _ => do
        match runtimeRecSpine? t with
        | some (c, args) => do
          let vs ← readRecArgs fuel (match recLayout c with | some (_, m, _) => m | none => 0) 0 args
          applyR fuel (Val.recSpine c vs) []
        | none => do
          -- **JUXTAPOSITION APPLICATION** (M27 β). The document's grammar has one
          -- application form, `t t′`; the n-ary `f(a, …)` is the declaration era's
          -- telescope leaking into the term language, and it dies at δ. So `f a b`
          -- has to mean a call when `f` names a runtime function — and WHICH ARROW
          -- applies a spine is decided here rather than at the surface, because the
          -- surface cannot know: `let finish = (λ (e : List Nat). …)` and
          -- `let f = (… : …)` are both lowercase slots holding functions.
          --
          -- **The router is §7 cost 5's own distinction, not a new test.** The two
          -- λs are "the same former in the document, two representations in the
          -- machine, because one substitutes and the other binds". A pure `.lam`
          -- substitutes — that is ⇝'s rule, and the staged proof-builders across
          -- the corpus are exactly this, applied to snapshots and proofs that a ⇒
          -- read would MOVE. A `Val.rfn`, a σ with a signature, or a recursor spine
          -- binds Ω slots — that is ⇒'s. Same room, two doors (§2.3).
          --
          -- **THE MODE PRE-FILTER IS GONE** (M31 Stage A, §2.2). This used to
          -- exclude a capital head *before anything was looked up*, on the ground
          -- that §6.3 made such a binder a SPEC parameter which routing here could
          -- only ever get `fenceComptime`'s rejection for. With the fence deleted
          -- that ground is gone, and the exclusion would now be the one thing
          -- preventing the model's own sentence — every function binding is
          -- capital, so a mode filter on heads filters out all of them.
          --
          -- What survives is NOT arrow-inspection by mode but §2.2's own step 3:
          -- the head is fetched (a non-destructive slot read, the ⇝ fetch), and
          -- the value decides which rule applies (`calleeIsRuntime`). The
          -- mint-vs-remember split it keys is arrow-keyed rather than node-keyed
          -- (§12 decision 5: write an application in a type and ⇝ remembers the
          -- spine, write it as a statement and ⇒ mints) — which is exactly why
          -- retiring `callV` could take the node away without taking the split.
          --
          -- **THE CALL RULE LIVES HERE NOW** (M32 R4). Everything below the
          -- router was `readR`'s `.callV` arm; `f(a, b)` is the same term as
          -- `f a b`, so there is one arm and it is this one.
          --
          -- **The callee is LOCATED, not consumed** (§7 cost 2): calling a
          -- function is a place read, like a match scrutinee's, so a slot can be
          -- called twice — which `ih` needs, since `quicksort` recurses twice
          -- from one arm. What licenses that is M27's model — **functions are
          -- reached by NAME** (§8: a declaration is a `let`, and the binding IS
          -- the name), so calling where bound is a name-use rather than a read.
          -- `readR`'s `.var` case refuses reading a function into a second
          -- binding for the same reason; the two rules are one sentence seen
          -- from both ends. (The old note here argued location was the
          -- CONSERVATIVE statement, which c1 caught as exactly inverted: for a
          -- non-copyable closure it is the permissive one, and it was safe only
          -- because phase A's values are all index-kind.)
          --
          -- **THE FENCE IS GONE** (M31 Stage A, §2.2): a capital binder is what
          -- every function binding now looks like, so refusing to call one would
          -- refuse every call there is. The head is FETCHED BY ⇝ — the
          -- non-destructive slot read below — so nothing about erasure is
          -- weakened by letting an erased binder be the callee: `G a` in a spec
          -- and `G(a)` in a body reach the same value by the same read, and
          -- since R4 they are also the same term.
          match appSpineVar? t with
          | some (x, args) =>
            match findSlot? (← get).env x with
            | some kv => do
              if calleeIsRuntime (← get) kv.2 then
                match kv.2 with
                | .bot => throwErr s!"call: callee {x.name}#{x.id} holds ⊥ (use-after-move or uninitialized)"
                | callee =>
                  -- §5.2's "every demand collapses first": a call is a demand on
                  -- its callee slot, so a parked loan there ends before we look
                  -- at what the slot holds. Listed rather than omitted — every
                  -- UNLISTED demand site in this calculus has so far turned out
                  -- to be a bug waiting for its first program.
                  match firstLoanMarker callee with
                  | some ℓ => do endLoan fuel ℓ; readR fuel t
                  -- **A SEALED FUNCTION is called by the table's own rule**
                  -- (M26-C). Its σ carries a moded signature rather than a `Val`
                  -- type (`St.fsig`), and `callDeclC` is what reads one.
                  -- Dispatched HERE, before the arguments are read, because
                  -- `processArgs` does its own §6 mode routing off the telescope
                  -- — pre-reading them would consume a comptime argument the
                  -- callee promised never to touch.
                  | none =>
                    match callee.symOf? with
                    | some σ =>
                      match (← get).fsig.lookup σ with
                      | some piT =>
                        -- Peel the stored Π at POSITIONAL binders, which is the
                        -- convention `processArgs`/`buildResult` read a telescope
                        -- by, and which `piBinderNames` reproduces mode and all.
                        match piPeel (piBinderNames piT) piT with
                        | .error e => throwErr e
                        | .ok (tel, ret) => callDeclC fuel (tel.map (fun p => (p.1.name, p.2))) ret args
                      | none => applyCallee fuel x callee args
                    | none => applyCallee fuel x callee args
              else do collapseCDerefs fuel t; pureLift fuel t
            | none => do collapseCDerefs fuel t; pureLift fuel t
          | none => do collapseCDerefs fuel t; pureLift fuel t
      | .idT _ _ _ => throwErr s!"readR (⇒): `Id` ({t.pretty}) is a type — a ⇝ form with no ⇒ reading (a type has no runtime representation, so it cannot be moved into a runtime slot; its PROOF `Refl` is an ordinary constructor and moves as data). Give the type a comptime destination: a capital `let`, a ⇝ parameter, a capital Σ component, or an ascription."
      -- ¶2.2's ⇒ column at the two new steps, and the regularity §1.3 asks the
      -- reader to notice: each behaves the way the corresponding column behaves at
      -- `*`. `t[i]` moves the element out (a hole in the slot) or copies it under
      -- §2.1's index-kind refinement; `t[lo ; cnt]` moves the whole run out, leaving
      -- a hole of known extent whose one legal successor is the ⇐-refill — §2.4's
      -- take-and-refill generalized from "the payload of a borrow" to "a run of an
      -- array", which is how a rotation or a memmove is written without a copy.
      | .index _ _ _ | .range _ _ _ _ _ _ => do
        fencePlace t "cannot be indexed or sliced at runtime"
        let pos ← placeToPos fuel t
        match ← getAtPos fuel pos with
        | .bot => throwErr "readR: array place holds a hole (⊥) — take without refill"
        | p =>
          match firstLoanMarker p with
          | some ℓ => do endLoan fuel ℓ; readR fuel t     -- §5.2: every demand collapses first
          | none =>
            if indexKindV fuel (← get).sctx p then do mergeRoot pos.root; pure p  -- §2.1 copy-on-read
            else do setAtPos fuel pos .bot; mergeRoot pos.root; pure p
      | .borrowT _ _ _ => throwErr "readR (⇒): borrow type `&mut (τ ↝ τ')` is a telescope-position form, not a movable value"
      -- `⇝τ` outside a λ/Π domain is a mode marker that escaped its binder. Same
      -- standing as `borrowT` on the line above, and the same rejection.
      | .cmpT _ => throwErr "readR (⇒): `⇝τ` is a binder-mode marker (§6), legal only as a λ/Π domain — not a term and not a movable value"
  termination_by fuel _ => (fuel, 0, 0)
  /-- **One rule per statement former, three drivers** (M33 Σ0's prerequisite).

      A body's statement spine is walked by `readR` (⇒, single path), by `explore`
      (the checking driver, one path per symbolic branch) and now by `readRTail`
      (⇒ again, with the tail's type in hand). They differ ONLY in how they
      continue; the step each takes is the same step, and `letStep`/`assignStep`/
      `seqStep` are those steps.

      `explore` used to spell its own `let` step out, with a comment explaining
      that "the duplication is two lines" and that a rule living only in `readR`
      would be dead for every real body. That reasoning was right and the
      duplication was the wrong answer to it: a third driver would have made it
      three copies of the mode backstop that used to sit here.

      This one: **⇝ for a capital binder, ⇒ for a lowercase one, and nothing
      else** (M33b). The backstop between them — "a runtime-moded binding may not
      receive a function" — is gone, because the three ways a function can arrive
      each have their own refusal now and none of them is here. R3's invariant is
      the whole rule with no rider: *a capital `let` ⇝-reads its right-hand side;
      a lowercase `let` ⇒-reads it.* -/
  def letStep : Nat → Var → Term → M Unit
    | fuel, x, rhs => do
      -- The breadcrumb is filed HERE rather than in each driver, for the reason
      -- the rule itself is: three drivers take this same step. A `let` files
      -- under its binder alone — runtime ids are globally unique, so that
      -- identifies the statement outright and carries none of the RHS's bulk.
      noteStmt (.letIn x .unit .unit)
      let v ← if x.isComptime then readComptimeVal fuel rhs else readR fuel rhs
      -- The hover type table, filed at the same one site and for the same reason
      -- (docs/16). AFTER the read, because the read is what produces the value the
      -- binder's type is read off, and BEFORE `bindSlot`, which is arbitrary —
      -- neither observes the other.
      noteLetType x v
      bindSlot x v
  termination_by fuel _ _ => (fuel, 16, 0)
  /-- The `assign` step: RHS by ⇒ first (§2.5 ordering), target by ⇐. -/
  def assignStep : Nat → Term → Term → M Unit
    | fuel, place, rhs => do
      noteStmt (.assign place rhs .unit)
      let v ← readR fuel rhs
      writeR fuel place v
  termination_by fuel _ _ => (fuel, 16, 0)
  /-- The `seq` step: evaluate for effect, discard. -/
  def seqStep : Nat → Term → M Unit
    | fuel, e => do noteStmt (.seq e .unit); let _ ← readR fuel e; pure ()
  termination_by fuel _ => (fuel, 16, 0)
  /-- **⇒ with the tail's type in hand** (M33 Σ0's prerequisite, suspensions.md
      §2.7) — `readR` for every step of a body's statement spine, and `readResult`
      at the end of it.

      This is the executing machine's half of the rule `readResult` states: a
      `Pair` returned at a `Σ` is read component by component, each by ITS binder's
      mode. The checker has read tails that way since R3b (`explore`, against
      `St.retTyVal`); execution could not, because a closure had dropped its
      ascription at the seal and `applyClosure` had no return type to read. M33a
      measured what that costs — nine executing differentials — and gated the
      ⇒-move fence checking-side rather than let the machines disagree. With the
      closure carrying its contract, the two read a tail by the same rule.

      `none` is the ordinary case and means `readR`: a λ with no ascription
      promises nothing about its result, and there is no mode to consult. -/
  def readRTail : Nat → Option Term → Term → M Val
    | 0, _, _ => throwErr "readRTail: out of fuel"
    | fuel + 1, ty, t =>
      match t with
      | .letIn x (.matchE s eqn bs) rest =>
        readRTail fuel ty (.matchE s eqn (pushJoinArms x rest bs))
      | .seq (.matchE s eqn bs) rest =>
        readRTail fuel ty (.matchE s eqn (pushJoinArmsSeq rest bs))
      | .letIn x rhs rest => do letStep fuel x rhs; readRTail fuel ty rest
      | .assign place rhs rest => do assignStep fuel place rhs; readRTail fuel ty rest
      | .seq e rest => do seqStep fuel e; readRTail fuel ty rest
      | .matchE scrut eqn branches => do
        -- A match in TAIL position: every arm's body ends where this one does,
        -- so the type goes into the arm. (A STATEMENT-position match never gets
        -- here raw — the rows above rebuild the seam shape first — so this is
        -- the genuine tail case, plus the rebuilt shapes those rows produce.)
        readRTail fuel ty (← matchStep fuel scrut eqn branches)
      | other => readResult fuel ty other
  termination_by fuel _ _ => (fuel, 0, 0)
  def readArgs : Nat → List Term → M (List Val)
    | _, [] => pure []
    | fuel, a :: as => do
      let v ← readR fuel a
      pure (v :: (← readArgs fuel as))
  termination_by fuel as => (fuel, 1, as.length)
  /-- `readArgs` with a per-position mode (combining-fns §6): a `true` position is
      a capital binder's, and its argument is read by ⇝ — pure and NON-CONSUMING,
      so the caller still holds whatever it passed. A short mode list defaults to
      runtime, which is what the arity rejections downstream expect to see. -/
  def readArgsModed : Nat → List Bool → List Term → M (List Val)
    | _, _, [] => pure []
    | fuel, ms, a :: as => do
      let v ← match ms.head? with
        | some true => do pure (Val.know (← readComptimeArg fuel a))
        | _ => readR fuel a
      pure (v :: (← readArgsModed fuel (ms.drop 1) as))
  termination_by fuel _ as => (fuel, 1, as.length)
  /-- A runtime recursor spine's arguments: everything ⇒-read, except the motive,
      which is not read at all (`erasedMotive` — a borrow-moded Π has no ⇝
      reading, and ι has no use for one). -/
  def readRecArgs : Nat → Nat → Nat → List Term → M (List Val)
    | _, _, _, [] => pure []
    | fuel, mi, i, a :: as => do
      -- **A RECURSOR ARM IS A DESTINATION** (M33's destination rule), and it is
      -- the fifth one — the list in `readR`'s λ arm names the four a programmer
      -- writes, and this is the one the `fn [k]` elaboration writes for them. An
      -- arm is a BODY, the seal ascribes the whole spine, and `sealRec`/`checkArm`
      -- check each arm against the Π §7 derives for it (which `ascribeRecArms`
      -- also hands the executing machine, since M33's prerequisite). So the arm
      -- is formed here rather than ⇒-read: it has a contract, and having one is
      -- exactly what the destination rule asks for.
      -- **A pre-motive slot is a TYPE PARAMETER, and it is ⇝'s** (types-no-exec,
      -- 2026-08-20). A recursor's telescope is [type params…, motive, arms…] —
      -- `listRec A P pn pc` has exactly one, the element type `A` — and this
      -- used to `readR` it, which worked only because `readR` gave a written
      -- `.const` a ⇒ reading via the pure lift. Stage 0's flip ledger caught it
      -- (b3/d1: `listRec Nat …` red on the removed arm): the slot is a type
      -- position, comptime knowledge exactly as the motive beside it, so it is
      -- read by the same channel a ⇝ call argument is, not patched back into ⇒.
      let v ← if i < mi then pure (Val.know (← readComptimeArg fuel a))
              else if i == mi then pure (Val.know erasedMotive)
              else match a with
                   | .lam _ _ _ => mkClosure fuel a
                   | _ => readR fuel a
      pure (v :: (← readRecArgs fuel mi (i + 1) as))
  termination_by fuel _ _ as => (fuel, 1, as.length)
  /-- β for a literal λ callee: check each argument against its binder's domain,
      substitute, repeat. Domain-checking is CHECKING-mode only — executing mode
      runs already-accepted programs and `bindActuals` sets that precedent — so
      the two machines perform the same reduction and differ only in what they
      verify. (In the mutual block since M26-C: a residual that is not a `.lam`
      may be a runtime function, and application composes through `applyR`.) -/
  def applyLam : Nat → Val → List Val → M Val
    | 0, _, _ => throwErr "call: out of fuel (λ application)"
    -- **A residual λ is a VALUE here, and R4 is where that was measured**
    -- (M32 R4). This case used to refuse it as §12 decision 4's unsaturated
    -- application. That decision is about ⇒-ENTRY — "a partial application at
    -- runtime is a closure holding its arguments, including in general borrows,
    -- while it waits" — and it is enforced where entry happens: `applyR`'s
    -- closure case for an imperative λ, and `applyCallee`'s residual-Π case for
    -- a sealed σ. Neither is this rule. What reaches HERE is β of a COMPTIME λ,
    -- whose capture is knowledge-only, which holds no borrow, and which the
    -- flagship applies partially — its staged proof-builders are exactly that.
    --
    -- The refusal survived this long because `callV` and juxtaposition were two
    -- nodes: `f(2)` came here and was refused, `f 2` went to the pure lift and
    -- β'd. Retiring the node made them one term and forced the question, and
    -- the corpus answered it — the flagship goes red the other way.
    | fuel + 1, .know ft, [] => pure (.know (Pure.whnf fuel ft))
    | _ + 1, f, [] => pure f
    -- **A comptime closure is β'd by COOKING it** (M32 R2, §2.2/§2.3). The
    -- suspension has a knowledge reading and application is where the demand for
    -- it is made; what the rest of this function then sees is the `.know` λ it
    -- always saw. An imperative closure is not this rule's — it is ⇒-entry, and
    -- `applyR` owns it.
    | fuel + 1, .closure ρ node u, a :: rest =>
      if Term.lamImperative node then applyR fuel (.closure ρ node u) (a :: rest)
      else applyLam fuel (.know (cookClosure fuel ρ node)) (a :: rest)
    | fuel + 1, .know ft, a :: rest =>
      match Pure.whnf fuel ft with
      | .lam x dom body => do
        let ak := subsKnowledge a
        if (← get).executing then applyLam fuel (.know (Pure.openBinder fuel x.name body ak)) rest
        -- `hasType` strips the mode marker: which arrow READ the argument was
        -- settled before this call (`valBinderModes`), and what remains is the
        -- ordinary domain check.
        else if ← hasType fuel a dom then
          applyLam fuel (.know (Pure.openBinder fuel x.name body ak)) rest
        else throwErr s!"call: argument ({a.pretty}) does not have its parameter type ({dom.pretty})"
      -- A pure λ whose body turns out to be a runtime function (or a recursor):
      -- hand the remaining spine to the ⇒-application rule rather than calling it
      -- an arity error. One application story, two reduction rules.
      | other => applyR fuel (.know other) (a :: rest)
    | fuel + 1, f, a :: rest => applyR fuel f (a :: rest)
  termination_by fuel _ args => (fuel, 1, args.length)
  /-- **⇒-application of a function VALUE to a saturated spine** (§7 costs 2/3/5).

      Three reduction rules, chosen by the head — and the point of collecting the
      spine first is that they COMPOSE: ι hands its arm the scrutinee's
      predecessor, the recursor at that predecessor, and everything the caller
      still owed, all in one saturated application, so no intermediate partial
      application ever exists to hold a borrow (§12 decision 4's whole reason).

        * a **runtime function** (`rfn`) — bind its names in a fresh frame and
          ⇒-evaluate its body (`applyRFn`). This is the rule phase A could not
          write: a body is not a `Val`, so β cannot substitute it.
        * a **recursor at a constructor scrutinee** — ι, with the arm applied as
          a body. `natRec P z s (S m) v … ↦ s m ⟨natRec P z s m⟩ v …`, and the
          middle argument is `ih`: literally the recursor at the predecessor,
          closed, a value, never partially applied (§7 cost 2's "boring kind").
        * a **pure λ** — β, delegated to `applyLam` unchanged.

      A recursor **stuck on a symbolic scrutinee is a value**, not an error: that
      is exactly what an unapplied `ih` is in checking mode. Applying one is
      arms-as-bodies checking, and is rejected here until that rule lands. -/
  def applyR : Nat → Val → List Val → M Val
    | 0, _, _ => throwErr "applyR: out of fuel"
    -- **A closure over an imperative body: ⇒-ENTRY** (M32 R2, §2.2). A comptime
    -- closure falls through to the β rule below, which is the fragments' one
    -- difference and the only place it is consulted.
    | fuel + 1, .closure ρ node ascr, args =>
      if Term.lamImperative node then
        let (tel, body) := Term.peelLams node
        let names := tel.map (·.1)
        if args.length == names.length then applyClosure fuel ρ names body ascr args
        else if args.length < names.length then
          throwErr s!"call: partial application — the runtime λ {(Val.closure ρ node ascr).pretty} binds {names.length} argument(s) and was given {args.length}. Runtime application is saturated (§12 decision 4): a partial application at runtime is a closure holding its arguments — including, in general, borrows — while it waits."
        else
          throwErr s!"call: too many arguments — the runtime λ {(Val.closure ρ node ascr).pretty} binds {names.length} argument(s) and was given {args.length}"
      else applyLam (fuel + 1) (.closure ρ node ascr) args
    | fuel + 1, f, args => do
      let (headName, sargs) := (Val.asRecSpine? f).getD ("", [])
      let all := sargs ++ args
      match (Term.const headName : Term), all with
      -- **`ih` IS EAGER AT A DATA MOTIVE** (M33b; user ruling, suspensions.md §5).
      -- *"Passing a Nat to natRec causes the Nat to get recursed over all the way
      -- to the end … I don't see why we would want anything unevaluated leaving
      -- the natRec; this is not a lazy language."* A recursor spine at a CONCRETE
      -- scrutinee is a redex, never a value, and the one place a
      -- concrete-scrutinee spine used to survive as one is here: the `ih` handed
      -- to a step arm. Running it BEFORE entering the arm is call-by-value, and it
      -- is what stops `Cons(0, ih)` from putting a `§rec` — a state form with no
      -- `Term` — inside a constructor the program declared `List Nat`.
      --
      -- **The discriminator is the base arm's unit binder**, which is the right
      -- question asked in the shortest way: an arm binds `U§` iff the motive owes
      -- it nothing, i.e. iff the recursion at the predecessor runs to a FINISHED
      -- value with nothing left to apply. When it does not — a Π motive, whose
      -- arms take the residual telescope (`SetAt`'s `v`, `i`, `x`) — the recursion
      -- cannot run without arguments nobody has yet, and the spine at the
      -- predecessor stays what §7's convergence argument says a recursive
      -- occurrence is: the applicable self-view. That is not laziness surviving in
      -- a corner. **A function value IS finished**, which is the same sentence the
      -- ruling makes about data.
      --
      -- Eagerness costs fuel proportional to the recursion's DEPTH where the lazy
      -- form deferred it, and costs it even when the arm never cites `ih`. That is
      -- what eager means; it is not a defect to optimize away here.
      | .const "natRec", motive :: z :: s :: n :: rest => do
        match Val.asCtor? (whnfV fuel n) with
        | some ("Z", []) => applyRest fuel z rest
        | some ("S", [m]) => do
          let sp := Val.recSpine "natRec" [motive, z, s, m]
          let ihv ← if z.armTakesUnit then applyR fuel sp [] else pure sp
          applyRest fuel s (m :: ihv :: rest)
        | _ => stuckRec fuel "natRec" [motive, z, s, whnfV fuel n] rest
      | .const "boolRec", motive :: t :: e :: b :: rest =>
        match Val.asCtor? (whnfV fuel b) with
        | some ("True", []) => applyRest fuel t rest
        | some ("False", []) => applyRest fuel e rest
        | _ => stuckRec fuel "boolRec" [motive, t, e, whnfV fuel b] rest
      -- The same eager `ih`, at the same discriminator (the `Nil` arm's unit
      -- binder) — see the `natRec` case above for why.
      | .const "listRec", a :: motive :: pn :: pc :: l :: rest => do
        match Val.asCtor? (whnfV fuel l) with
        | some ("Nil", []) => applyRest fuel pn rest
        | some ("Cons", [h, tl]) => do
          let sp := Val.recSpine "listRec" [a, motive, pn, pc, tl]
          let ihv ← if pn.armTakesUnit then applyR fuel sp [] else pure sp
          applyRest fuel pc (h :: tl :: ihv :: rest)
        | _ => stuckRec fuel "listRec" [a, motive, pn, pc, whnfV fuel l] rest
      -- Not a recursor redex. A pure λ (or a λ-headed spine) is β; applied to
      -- nothing — the under-applied `natRec P z s` a seal ascribes, or a recursor
      -- stuck on a σ — it is a VALUE; applied to something it cannot consume, it
      -- is over-application.
      | _, _ =>
        match f with
        | .know ft =>
          match Pure.whnf fuel ft with
          | .lam x d b => applyLam fuel (.know (.lam x d b)) args
          | w =>
            if args.isEmpty then pure (.know w)
            else throwErr s!"call: too many arguments — {w.pretty} is not a function (expected a λ, a runtime λ, or a recursor spine)"
        | v =>
          if args.isEmpty then pure v
          else throwErr s!"call: too many arguments — {v.pretty} is not a function (expected a λ, a runtime λ, or a recursor spine)"
  termination_by fuel _ _ => (fuel, 2, 0)
  /-- ι's continuation: the selected arm, applied to the `()` it owes and to
      whatever the caller still owed.

      **The `()` is the M33b half.** An arm the motive owes nothing binds the
      unwritable `U§ : ⇝Unit` so that it is a suspension at all, and this is where
      it is forced: ι selects the arm and hands it its unit, the body runs, and
      what leaves the recursor is a value rather than a λ that has not been
      entered. One site rather than five, because a STEP arm never binds it (it
      leads with the predecessor and `ih`), so asking every arm costs nothing and
      spares the two recursors' five ι rules a conditional each.

      **With nothing owed the arm IS the value** — `natRec P z s Z` at a motive
      that computes a function TYPE is that function, not a call of it — and
      keeping that distinct from `applyR arm []` is what lets a zero-argument
      value-callee call (`f()`) still be the partial application it is.

      Since M33b that case no longer covers a NO-BINDER arm: such an arm is owed
      its unit, so `rest` is never empty for one. What is left of it is the
      Π-motive shape above, and the corpus does not reach that either — measured
      by making this line throw, which leaves the whole corpus green. It is kept
      rather than deleted because it is the value side of the same coin the eager
      rule turns over: a function value IS finished, so an arm that is one leaves
      the recursor as it stands. Deleting it would make that shape a partial
      application error instead, which is a different claim about a live
      semantics and not a tidy-up. -/
  def applyRest : Nat → Val → List Val → M Val
    | fuel, arm, rest =>
      match (if arm.armTakesUnit then Val.ctor "unit" [] :: rest else rest) with
      | [] => pure (whnfV fuel arm)
      | rest' => applyR fuel arm rest'
  termination_by fuel _ _ => (fuel, 3, 0)
  /-- A recursor that did not ι. With nothing owed it is a VALUE — the abstract
      self-view `ih` at a symbolic predecessor, which is precisely what §7's
      convergence argument says a recursive occurrence must be. With arguments
      owed it is arms-as-bodies checking at a symbolic scrutinee.

      **A SYMBOLIC scrutinee is why this survives M33b's eager rule.** ι cannot
      fire without a constructor, so there is nothing to run to the end; this is
      checking's `ih`, and it is correct. -/
  def stuckRec : Nat → String → List Val → List Val → M Val
    | _, head, spine, [] => pure (Val.recSpine head spine)
    | _, head, spine, _ =>
      throwErr s!"applyR: {head} is stuck on a symbolic scrutinee ({(spine.getD (spine.length - 1) .bot).pretty}) and cannot ι. Applying a recursor at a symbolic scrutinee is arms-as-bodies CHECKING (§7 cost 1) — reachable through a seal, not through a call."
  /-- Apply a runtime function: bind its named binders in a fresh SCOPE and
      ⇒-evaluate its body.

      **There is no id window any more** (M32 R4). The frame used to renumber the
      body's ids by a fresh offset (`freshFrame`/`shiftVarsK`) so that two live
      frames of the same recursive body could not collide. Under name-keyed Ω
      (M32 R1) `findSlot?` never reads an id — newest binding of the NAME wins —
      so the renumbering decided nothing, and shadowing is what separates the
      frames. Measured, not argued: the whole corpus is green without it, and
      `keep` went first on its own (see below).

      **`keep` was §8's globals, and it was INERT.** It held the ids a body has
      free — its callees, bound at program level — carried through the shift
      unchanged so that a body calling `quicksort#901` would still find `#901`.
      R4 asserted it empty-by-construction as the plan predicted and the corpus
      REFUTED that: `swap`'s body yields `keep = [901]`. What is true instead is
      that it never mattered, because the lookup that would have been broken by
      shifting resolves by name; emptying it alone is green, which is the
      differential that licensed deleting the shift entirely.

      The scope survives all of this and does the real work (M31 Stage 0): its
      borrows are surrendered and its slots taken on the way out, so neither a
      frame's loans nor its environment can outlive it. -/
  def applyClosure : Nat → Omega → List Var → Term → Option Term → List Val → M Val
    | fuel, ρ, names, body, ascr, args => do
      -- **No pre-normalization since docs/19 v2**: the spine keeps its
      -- continuations, and the seam shape is built lazily at the point of use —
      -- `readRTail`'s own statement-match rows (⇒, concrete selection) and
      -- `exploreD`'s join rows (checking) construct the SAME `pushJoinArms`
      -- shape, so the M31 checker/executor arm-scope agreement holds at the
      -- builder rather than at a pre-pass.
      -- **The frame is a scope** (M31 Stage 0): its watermark is taken before the
      -- parameters land, and `popScopesTo` below both ends the borrows it still
      -- holds and takes its slots with it. Loans the result carries out are
      -- retained, which is what `releaseFrameLoans` achieved by never popping.
      openScope false
      let depth ← scopeDepth
      -- **ρ ENTERS THE FRAME FIRST** (M32 R2, §2.2): the captured knowledge, then
      -- the arguments, so a parameter shadows a capture of the same name and the
      -- body reads what the λ SAW rather than what the caller's Ω holds now. This
      -- is the escape-safety §2.6 is about, and it is one `bindSlot` loop: under
      -- name-keyed newest-wins Ω "shadow the ambient binding" is just binding
      -- later — which is now also the whole of what a frame is.
      ρ.forM (fun kv => bindSlot kv.1 kv.2)
      (names.zip args).forM (fun p => bindSlot p.1 p.2)
      let res ← readRTail fuel (calleeRetTy names ascr) body
      popScopesTo fuel (depth - 1) 0 res.loanIds
      pure res
  termination_by fuel _ _ _ _ _ => (fuel, 4, 0)
  /-- Consume a call's arguments left-to-right, checking each against its
      telescope entry, and RETURN the captured loans (§6.1): each argument
      borrow's loan ℓ with its owed type `τ'[s := v]`. A pure argument must
      `hasType` its parameter type; a borrow argument must be a `borrowM ℓ v`
      whose payload `v` has the parameter type τ, and is consumed. -/
  def processArgs : Nat → Nat → Omega → List (String × Term) → List Term →
      M (List (Nat × Term × Option Term) × Omega)
    | _, _, inst, [], [] => pure ([], inst)
    | fuel, i, inst, (name, tyTerm) :: tRest, arg :: aRest => do
      -- File the diagnostic under THIS argument. Every rejection below already
      -- names the *instantiated* parameter type — the checker reads it at the
      -- actuals already consumed — so the squiggle lands on the offending
      -- argument and the message states what was expected there.
      noteArg arg
      -- Parameter `i`'s runtime var (the §5.2 convention: a later type mentions
      -- it as `.var ⟨i, name⟩`). `inst` binds parameters `0 … i-1` to the
      -- actuals already checked, so this type is read at those actuals.
      let declVar : Var := ⟨i, name⟩
      -- **The comptime-argument rule** (§6). A capital parameter is comptime: the
      -- argument expression is evaluated under ⇝ — pure, non-consuming — so the
      -- caller keeps it and may cite it after the call. This is R16's proof
      -- consumption resolved at its source: the pain was never "proofs are
      -- linear", it was that ⇒ was the only arrow a call site had.
      --
      -- Two consequences worth stating. A capital parameter may not be
      -- borrow-typed (rejected here and at `seedTelescope`) — a ⇝-read of `&mut`
      -- is meaningless, §6's "checked, not assumed". And the argument must be a
      -- COMPTIME term: a call's result is a fresh existential and has no ⇝
      -- reading, so `f(g())` at a capital position is refused by `readC` and must
      -- be `let`-bound first. Both are honest rejections rather than silent
      -- fallbacks to ⇒.
      if declVar.isComptime then
        match tyTerm with
        | .borrowT _ _ _ | .sigmaT _ _ (.borrowT _ _ _) =>
          throwErr s!"call: parameter '{name}' is capitalized (comptime, §6) but its type is a borrow — a ⇝-read of `&mut` is meaningless, so borrow-typed binders must be lowercase"
        | _ => do
          let argVal ← readComptimeArg fuel arg
          let τVal ← readCWith fuel inst tyTerm.stripCmp
          if ← hasTypeT fuel argVal τVal then
            processArgs fuel (i + 1) ((declVar, .know argVal) :: inst) tRest aRest
          else throwErr s!"call: comptime argument ({argVal.pretty}) does not have its parameter type ({τVal.pretty})"
      else
      match tyTerm with
      | .borrowT sn τ S => do
        match ← readR fuel arg with
        | .borrowM ℓ payload => do
          let τVal ← readCWith fuel inst τ
          if ← hasType fuel payload τVal then do
            let SVal ← readCWith fuel inst S
            let opened := Pure.nf fuel (Pure.openBinder fuel sn SVal (subsKnowledge payload))
            -- D1's one-slot classification at the CALL: the RHS instantiated at
            -- the actual payload — a TYPE is the owed type; anything else is
            -- the callee's PIN, which the group end will release (with the
            -- issued exits substituted) instead of a fresh existential.
            let (owed, upin) ← do
              if ← isOwedTypeT fuel opened then pure (opened, none)
              else pure (τVal, some opened)
            -- A borrow parameter is bound to the actual borrow itself, so a later
            -- type mentioning `*b` (§5.2's comptime-deref at the call site)
            -- reflects the peel to the payload snapshot just passed.
            let (rest, inst') ← processArgs fuel (i + 1) ((declVar, .borrowM ℓ payload) :: inst) tRest aRest
            pure ((ℓ, owed, upin) :: rest, inst')
          else
            throwErr s!"call: borrow argument's payload ({payload.pretty}) does not have its parameter type ({τVal.pretty})"
        | v => throwErr s!"call: expected a borrow argument (&mut …), got {v.pretty}"
      -- ¶4's runtime-length slice at a CALL SITE (M24 STEP 1's probe). The actual is a
      -- genuine pair — a length and a borrow — so the capture is the borrow's loan and
      -- the length is checked like any other argument. See `docs/DELTAS.md` G2.
      | .sigmaT cn aTy (.borrowT sn τ S) => do
        let pr ← readR fuel arg
        match Val.asCtor? pr with
          | some ("Pair", [cv, .borrowM ℓ payload]) => do
            let aVal ← readCWith fuel inst aTy
            if !(← hasType fuel cv aVal) then
              throwErr s!"call: slice length ({cv.pretty}) does not have its parameter type ({aVal.pretty})"
            else
            let τVal := Pure.openBinder fuel cn (← readCWith fuel inst τ) (subsKnowledge cv)
            if ← hasType fuel payload τVal then do
              let SVal ← readCWith fuel inst S
              let opened := Pure.nf fuel (Pure.openBinder fuel cn
                (Pure.openBinder fuel sn SVal (subsKnowledge payload)) (subsKnowledge cv))
              let (owed, upin) ← do
                if ← isOwedTypeT fuel opened then pure (opened, none)
                else pure (τVal, some opened)
              let pairV : Val := .ctor "Pair" [cv, .borrowM ℓ payload]
              let (rest, inst') ← processArgs fuel (i + 1) ((declVar, pairV) :: inst) tRest aRest
              pure ((ℓ, owed, upin) :: rest, inst')
            else
              throwErr s!"call: slice payload ({payload.pretty}) does not have its parameter type ({τVal.pretty})"
          | _ => throwErr s!"call: expected a Σ-typed slice (a Pair of a length and a borrow), got {pr.pretty}"
      | tyTerm => do
        let argVal ← readR fuel arg
        let τVal ← readCWith fuel inst tyTerm
        if ← hasType fuel argVal τVal then
          processArgs fuel (i + 1) ((declVar, argVal) :: inst) tRest aRest
        else throwErr s!"call: argument ({argVal.pretty}) does not have its parameter type ({τVal.pretty})"
    | _, _, _, _, _ => throwErr "call: arity mismatch (arguments vs telescope)"
  termination_by fuel _ _ _ args => (fuel, 1, args.length)
  -- (`bindActuals` — executing mode's telescope binder for a TABLE callee —
  -- retired in M28 D9 with the table. Its rule survives where it is still needed:
  -- `applyR`'s runtime-λ application takes §6's comptime-argument rule in lockstep
  -- for the same reason, so the two machines still agree on what a caller holds
  -- after a capital argument.)
  /-- Application of a value callee that is NOT a sealed function: the phase-A
      rules (β for a λ, abstract application at a `Val` Π) plus M26-C's
      ⇒-application (`applyR`) for a runtime λ or a recursor spine. Split out
      of the call rule only so the sealed case can be dispatched before the
      arguments are read; the rules themselves are unchanged. -/
  def applyCallee : Nat → Var → Val → List Term → M Val
    | fuel, x, callee, args => do
      -- **The callee is inspected BEFORE any argument is read** (M26-B).
          -- Which arrow evaluates an argument is a property of the *binder it
          -- lands on*, so the modes have to be in hand first; phase A could
          -- read the whole spine up front only because there was one arrow.
          -- A λ callee carries its modes on its own domains; a σ : Π carries
          -- them on the Π it was sealed at — which is the version that matters,
          -- since the seal's ascription is the whole of what a caller sees.
          -- M26-C generalizes the mode read past the types it could be read
          -- from: a runtime function carries its modes on its binder NAMES
          -- (§6's rule for every other runtime binder), and a recursor spine
          -- borrows its from its base arm. A borrow-moded Π has no `Val` form,
          -- so there was never a type here to read them off.
          let modes ← valBinderModes fuel callee args.length
          let argVals ← readArgsModed fuel modes args  -- ⇒ or ⇝ per binder, left to right
          match callee with
          -- A COMPTIME closure: body known ⟹ β (`applyLam` cooks it).
          | .closure _ node _ =>
            if Term.lamImperative node then applyR fuel callee argVals
            else applyLam fuel callee argVals
          -- A runtime function, or a recursor over runtime arms: ⇒-application
          -- (bind-and-run, and ι with the arm as a body). `ih` arrives here.
          -- A recursor spine over RUNTIME arms (§7 cost 5). It is a function
          -- value with non-knowledge children, so the skeleton is where it lives
          -- (`Val.recSpine`) and `applyR` is what ι's it.
          | .node "§rec" _ => applyR fuel callee argVals
          | .know (.app _ _) => applyR fuel callee argVals
          | .know (.const _) => applyR fuel callee argVals
          | .know (.pvar cx) =>
            match symOfName? cx with
            | none => applyR fuel callee argVals
            | some σ =>
            match (← get).sctx.lookup σ with
            | none => throwErr s!"call: callee {x.name} is σ{subNat σ}, which has no type in sctx"
            | some σty => do
              let resTy ← instantiatePi fuel σty.stripCmp argVals
              match Pure.whnf fuel resTy with
              | .pi _ d _ => throwErr s!"call: partial application — σ{subNat σ} still expects an argument of type {d.pretty}, and runtime application is saturated (§12 decision 4)"
              | resTy => do
                -- The runtime column of §2.3: the call FORGETS the application
                -- and keeps only what the type promised. Deliberately NOT the
                -- structured neutral `σ a` — that is ⇝'s rule, and §12 decision
                -- 5 keeps the door to remembered-spine runtime calls closed. The
                -- two rules coexist unconfused because they are keyed by ARROW:
                -- write the application in a type or proof and ⇝ remembers it;
                -- write it as a statement and ⇒ mints.
                let σ' ← freshSym
                modify (fun s => { s with sctx := (σ', resTy) :: s.sctx })
                pure (.know (Term.sym σ'))
          | v => throwErr s!"call: {x.name}#{x.id} holds {v.pretty}, which is not a function value (expected a λ or a σ : Π)"
  termination_by fuel _ _ _ => (fuel, 8, 0)
  /-- **§5.4's audit, relocated to the seal** (M26-C, phase A's deferral).

      Checking a runtime λ against a borrow-moded Π *is* `checkFn`'s content, and
      this is that content reached from the node instead of from a declaration:
      seed the telescope, pin the return type at entry (§5.3 — a dependent return
      type may mention a parameter the body consumes), explore the body one path
      per symbolic branch, and audit each path at return with exit snapshots and
      obligations. When this was written `checkFn` still checked every `FnDef` in
      the corpus and nothing had been deleted; M27-δ deleted it, and this is now
      the ONLY audit site there is.

      **FRAME ISOLATION.** The sealed body gets a fresh Ω, fresh obligations and
      fresh groups — because it is a function being defined, not code running in
      the caller's world. Phase A evaluated a seal's
      body IN PLACE ("correct for phase A, and a sealed FUNCTION body will want
      frame isolation") and this is that debt paid. What crosses the boundary in
      each direction is exactly one thing: the ascribed type comes IN (already
      peeled, so it was read while the enclosing slots were live), and the fresh
      supplies go OUT advanced, so no later mint can collide with a σ the check
      put into a type. -/
  def checkRFnBody : Nat → List (Var × Term) → Term → Term → M Unit
    | fuel, tel, ret, body => do
      let saved ← get
      -- §8's globals cross frame isolation, and nothing else does. The seal's free
      -- variables are its citations — bindings lexically above it — and the fresh Ω
      -- is seeded with exactly those, resolved (and admitted) against the
      -- enclosing scope BEFORE the wipe. This is also where a sealed function's
      -- capture check happens at all: a sealed λ goes straight to `sealFn`
      -- without ever forming the closure, so `readR`'s own capture filter never
      -- runs on it.
      --
      -- The scan covers the TYPES as well as the body: the telescope domains and
      -- the return type are read inside the fresh frame too (`seedTelescopeV`,
      -- the `readC ret` below), so a comptime alias cited there — `let NatPair =
      -- Σ …; fn Fst(p : NatPair) …` — crosses the wipe by the same rule as one
      -- cited in the body. This is also what `Term.freeRVars` says of the seal
      -- node itself (its `.seal`/`.lam` rows scan the ascription and the
      -- domains), so the memo key and this admission agree on the citation set.
      -- Telescope names are bound throughout: a param cited by a later param's
      -- type or by the return type resolves against the frame's own seeds, not
      -- the enclosing scope.
      let telNames := tel.map (·.1.name)
      let gl ← admitGlobals "seal" tel.length
        (Term.freeRVars telNames body
          ++ (tel.map (fun p => Term.freeRVars telNames p.2)).flatten
          ++ Term.freeRVars telNames ret)
      -- `scopeMarks` joins the wipe for the same reason as Ω: a watermark is an
      -- index INTO Ω, so an enclosing scope's mark means nothing against the
      -- fresh one, and the sealed body's own scopes are its own (M31 Stage 0).
      modify (fun s => { s with env := gl, debts := [], groups := [],
                                exitSyms := [], entrySyms := [], retTyVal := none,
                                retTyBorrow := none, scopeMarks := [] })
      let obs ← seedTelescopeV fuel tel
      -- §5.4 exit snapshots: one σ per borrow parameter, recorded ONLY here until
      -- the audit defines it as that borrow's collapsed final payload.
      let borrowIds := borrowVarIds tel
      let exits ← borrowIds.mapM (fun i => do pure (i, ← freshSym))
      modify (fun s => { s with exitSyms := exits, debts := obs })
      -- The M27 `retMixesBorrow` containment stood HERE until M35 (D9). Its
      -- reason — "a non-borrow component of a borrow-carrying return type is
      -- judged by nothing" — is answered now: `collectResultBorrows` opens a
      -- mixed Σ's tail at the earlier components' knowledge and judges each
      -- VALUE component against its opened type, at the ACTUAL first component
      -- (no ∀ — the callee knows this one). So a cursor can say WHERE it
      -- points: `Σ (r : &mut Nat). Id Nat (*r) (NthL i (old *v))`.
      if !hasBorrowT ret then do
        let rv ← readC fuel (markExit borrowIds ret)
        modify (fun s => { s with retTyVal := some rv })
      else do
        -- D9's carrier: the mixed/borrow return type, pinned raw with `old *v`
        -- resolved at entry so the branch sweeps reach its value components.
        let entries := (← get).entrySyms
        modify (fun s => { s with retTyBorrow := some (resolveOldEntry entries ret) })
      let st0 ← get
      -- `auditAllPathsD`, not `auditAllPaths`: the breadcrumb crosses back out of
      -- the sealed body, so a rejection inside a `fn` reports at the statement
      -- inside the `fn` rather than at the declaration. The reference dropped it
      -- here; that left every error in a function body unlocalized, which is where
      -- most of the corpus is.
      let advanced ← auditAllPathsD fuel ret
        (exploreD fuel body st0) st0.ledgers st0
      -- `sealSites` crosses back out with the supplies, and for the same reason
      -- (M32 R3): it is a fact about which σ ids are spoken for, so restoring the
      -- caller's copy would let a later mint hand out a σ this audit already
      -- gave to a nested seal. It is also what makes a seal inside an audited
      -- body deterministic across two audits of that body.
      set { saved with nextLoan := advanced.nextLoan, nextSym := advanced.nextSym
                       nextGroup := advanced.nextGroup
                       sealSites := advanced.sealSites
                       -- Every diagnostic LEDGER, carried out as one thing
                       -- (docs/17). See `Ledgers`: three channels each learned
                       -- this door the hard way, so it is now a single name.
                       ledgers := advanced.ledgers }
  termination_by fuel _ _ _ => (fuel, 6, 0)
  /-- **The seal, at either arrow** (M32 R3, suspensions.md §2.4). One rule, two
      callers: `readR`'s `.seal` arm and the `let` arrow's ⇝ reader
      (`readComptimeVal`). That there is one rule is the content of "the seal
      becomes ⇝-evaluable" — not a second ⇝ rule beside the ⇒ one, which would be
      two things to keep in step, but the same rule reached from both sides.

      **CHECK half, unchanged, dispatched `.lam`-shaped** (M32 R2): a spine may
      be a recursor over runtime arms (§7's `fn` elaboration), a λ whose body is a
      BODY takes §5.4's audit, and everything else takes phase A's `hasType`.
      Nothing here is arrow-sensitive, and that is the observation §2.4 rests on:
      the audit already runs in its own fresh store, and `hasType` is a comptime
      judgment, so neither half ever needed the caller's arrow.

      **FORGET half, site-keyed.** The σ comes from `sealSym` at (site, inputs),
      so reading one seal twice yields the same value — the property whose
      absence was the whole reason ⇝ refused the node. A HIT skips the check as
      well as the mint: the inputs are what the check consults, so its answer is
      already known. -/
  def sealNode : Nat → Nat → Term → Term → M Val
    | fuel, site, t, u => do
      let inputs ← sealInputs (.seal site t u)
      let key : SealKey := (site, inputs)
      match (← get).sealSites.find? (fun e => e.1.1 == site && e.1.2 == inputs) with
      | some e => pure (.know (Term.sym e.2))
      | none =>
        match t with
        -- A spine MAY be a recursor over runtime arms — §7's `fn` elaboration —
        -- in which case sealing it is arms-as-bodies checking. Any other spine
        -- is an ordinary term and takes phase A's rule.
        | .app _ _ => sealApp fuel key t u
        -- **Asked of a λ, and only of a λ** (M32 R2 finding 7). A nullary `fn`
        -- binds the unwritable `U§ : ⇝Unit`, so there is always a λ here when
        -- there is a function here, and `(match n { … } : Nat)` is not diverted
        -- into frame isolation and an audit by having a body.
        | .lam _ _ _ =>
          if Term.lamImperative t then
            let (tel, body) := Term.peelLams t
            sealFn fuel key tel body u
          else sealValue fuel key t u
        | _ => sealValue fuel key t u
  termination_by fuel _ _ _ => (fuel, 14, 0)
  /-- **⇝ at a binding** (M32 R3, suspensions.md §2.4): what a capital `let`
      reads its right-hand side with.

      `readComptimeArg` — plain `readC` — is not enough on its own, because ⇝
      produces two things that are not knowledge and therefore have no `Term` to
      be read back to: a CLOSURE (a λ, either fragment) and a SEALED σ. Both are
      values whose formation is a ⇝ event, which is what §2.4's "λ formation is
      ⇝-only" and "the seal is ⇝-evaluable" say between them. This is the one
      place they are said in code.

      **The three cases are the whole comptime fragment at a binding**, and the
      third is the old rule verbatim: anything that is not a λ and not a seal is
      knowledge, read by `readC` and stored as a leaf.

      Note what is NOT here: `reflectC` still refuses the seal by name, so a seal
      inside a TYPE is as unwritable as it ever was. The seal became readable at
      an EVENT under ⇝, not readable everywhere — a type is consumed at its own
      event (§2.4) and has no binding to be the event of. -/
  def readComptimeVal : Nat → Term → M Val
    | fuel, t =>
      match t with
      | .lam _ _ _ => mkClosure fuel t
      -- **The seal, and the executing machine keeps EXACTLY the transparency it
      -- had** (M32 R3). Concrete evaluation does not verify and does not
      -- generalize: the body exists and runs, which is why a sealed value costs
      -- nothing at runtime. The read is `readR`'s, byte for byte the call this
      -- node made before R3 moved the capital `let` onto ⇝ — no site lookup, no
      -- comparison, no ⇝ detour. It is not a ⇝ rule wearing a disguise: under
      -- concrete evaluation there is one arrow, because erasure has nothing left
      -- to be about.
      --
      -- Spelling it `readComptimeArg` was tried and is WRONG, in a way worth
      -- leaving recorded: a RECURSIVE `fn` seals an `.app` — §7's `natRec P z s`
      -- over runtime arms — not a λ, and ⇝ refuses that spine by name. Three
      -- executing-mode differentials found it (`runSplit`, `swapBody`).
      | .seal site a b => do
        if (← get).executing then sealExec fuel a b else sealNode fuel site a b
      | _ => do pure (.know (← readComptimeArg fuel t))
  termination_by fuel _ => (fuel, 15, 0)
  /-- **The seal, executing: transparent, and since M33 not FORGETFUL** (Σ0's
      prerequisite, suspensions.md §2.7).

      Concrete evaluation reads a seal through — the body exists and runs, no
      check, no site lookup, no ⇝ detour, which is why a sealed value costs
      nothing at runtime. What changed is that the ASCRIPTION no longer stops
      here. `u` is the contract the seal checked the λ against, and it is the only
      place a function's return type exists in executing mode: `St.retTyVal` is
      `checkRFnBody`'s, and `applyClosure` entered every callee with nothing to
      read a tail's mode from (M33a, nine executing differentials). A λ therefore
      leaves this rule carrying its Π.

      A NON-λ sealed term keeps the plain read, and the reason is recorded at
      `readComptimeVal`: a recursive `fn` seals an `.app` (§7's `natRec P z s`
      over runtime arms), which has no closure to carry anything. -/
  def sealExec : Nat → Term → Term → M Val
    | fuel, t, u =>
      match t with
      | .lam _ _ _ => mkClosure fuel t (some u)
      -- A recursive `fn` seals a `natRec P z s` over runtime arms, and the ARMS
      -- are the bodies. `ascribeRecArms` gives each the contract §7 derives for
      -- it, which is the road quicksort's own tail takes.
      | _ => do
        let v ← readR fuel t
        pure (if (runtimeRecSpine? t).isSome then ascribeRecArms u v else v)
  termination_by fuel _ _ => (fuel, 14, 0)
  /-- Sealing a VALUE — phase A's rule, verbatim, in its own definition since
      M26-C so that `readR`'s seal arm is a two-line dispatch.

      This is what preserves §12-open-4's identity: sealing a borrow-free term at
      `u` still costs precisely `readC`-then-`hasType`, with no premise of its
      own, over the whole 16-pair battery. The function-checking rule is reached
      by the sealed TERM being a runtime λ, never by the ascription happening to
      have a `&mut` in it — so nothing that used to take this path can be
      diverted onto the other one. -/
  def sealValue : Nat → SealKey → Term → Term → M Val
    | fuel, key, t, u => do
      if hasBorrowT u then
        throwErr "seal: this term cannot be sealed at a borrow-moded type. A Π with `&mut` binders is a FUNCTION signature, and §5.4's audit is what checks a function against one — so the sealed term must be a runtime λ (`λ(v : τ, …){ … }`) whose binders match it. Sealing anything else at such a Π would be asking `hasType` a question §5.4 does not ask."
      -- The type is read FIRST, while the body's free variables are still live:
      -- `u` may mention a slot that evaluating `t` then consumes, and a type
      -- re-read afterwards would find a ⊥. §5.3's entry-pinning lesson, arriving
      -- at the seal for the same reason it arrived at a dependent return type.
      let uV ← readC fuel u
      -- **A λ here is FORMED, not ⇒-read** (M32 R3). `readR`'s λ arm refuses on
      -- the checking side now, and it is right to: this is the one caller that
      -- wants a closure rather than a refusal, because the sealed term of a
      -- value-seal is exactly a comptime λ. Everything else — an ascribed match,
      -- a spine — is ⇒'s as it was.
      let v ← match t with
              | .lam _ _ _ => mkClosure fuel t
              | _ => readR fuel t
      if ← hasType fuel v uV then do
        -- …then FORGET. The σ is the one this SITE has at these inputs (M32 R3):
        -- `.seal` is generalization, so what the caller keeps is exactly what the
        -- programmer wrote (§5 point 4), and WHICH σ that is is a function of the
        -- node and its inputs rather than of when the node was reached. That is
        -- what replaced "the mint is coherent because this is an EVENT, which is
        -- the property ⇝ lacks": ⇝ still lacks the event, and no longer needs one.
        let σ ← sealSym key
        modify (fun s => { s with sctx := (σ, uV) :: s.sctx })
        pure (.know (Term.sym σ))
      else
        throwErr s!"seal: the sealed term ({v.pretty}) does not have its ascribed type ({uV.pretty})"
  termination_by fuel _ _ _ => (fuel, 9, 0)
  /-- A sealed application spine: a recursor over runtime arms takes the
      arms-as-bodies rule, anything else takes phase A's. -/
  def sealApp : Nat → SealKey → Term → Term → M Val
    | fuel, key, t, u =>
      match runtimeRecSpine? t with
      | some (c, as) => sealRec fuel key c as u
      | none => sealValue fuel key t u
  termination_by fuel _ _ _ => (fuel, 13, 0)
  /-- Check ONE recursor arm as a body (§7 cost 1, "the one real kernel
      addition"): its leading binders are the ones the recursor's premise gives —
      the predecessor and `ih` — and the rest are the motive instantiated at this
      constructor. Then it is an ordinary function body, and `checkRFnBody` is the
      ordinary audit.

      Since M27 the arm ANNOTATES all of them, so both halves are agreements
      rather than supplies: the leading binders against `pre`, the rest against
      `ty` through `piAgree`.

      "The content of that judgment is exactly today's guard-checking (a body with
      only the sealed self-view available); the plumbing is new" — and that is
      literally what this is: `pre` carries `ih`'s type, which `seedTelescopeV`
      turns into a σ with a signature and no body. -/
  def checkArm : Nat → Term → List (Var × Term) → List (Var × Term) → Term → M Unit
    | fuel, body, pre, binders, ty => do
      -- **The premise binders are CHECKED, not supplied** (M27 α.1b), and this is
      -- the one place in α where getting it wrong would be unsound rather than
      -- merely wrong. `ih`'s type is the motive at the PREDECESSOR — the whole
      -- content of §7's "the guard evaporates" (M26-C: wrong-level `ih` is a type
      -- error rather than a check). Now that the arm ANNOTATES `ih`, an annotation
      -- taken on trust would let a body state the recursion at its own level and
      -- get it, which is `bad()` arriving through the door the guard used to hold.
      -- So `pre` is what the recursor's premise gives, and the arm must agree.
      if binders.length < pre.length then
        throwErr s!"seal: this recursor arm binds {binders.length} argument(s) but its premise gives it {pre.length} before the motive's own — the predecessor and `ih` are the arm's leading binders, not optional."
      match (List.zip (binders.take pre.length) pre).find?
              (fun p => !(Term.alphaEq p.1.2.stripCmp p.2.2.stripCmp)) with
      | some (b, _) =>
        throwErr s!"seal: recursor arm binder '{b.1.name}' is annotated with a domain the recursor's premise does not give it. The leading binders of an arm are the predecessor and `ih` — the sealed self-view AT THE PREDECESSOR (§7) — and their types are derived from the motive, not chosen: an `ih` annotated at the arm's own level would be the recursion available where §8's guard used to forbid it."
      | none =>
        -- **THE UNIT BINDER IS PART OF THE CONTRACT** (M33b). An arm the motive
        -- owes nothing binds `U§ : ⇝Unit` so that it is a suspension at all
        -- (`Syntax.unitBinder`), and the contract the seal checks it against has
        -- to grow the same binder or `piAgree` would be asked to peel a Π off a
        -- `List Nat`. Derived here rather than transcribed, from the arm's own
        -- spelling — the binder is unwritable, so its presence is the elaboration
        -- saying "nothing was owed" and nothing else can say it. `recArmPis` does
        -- the same thing on the executing side, and the two agree because they
        -- both call `Term.unitPi`.
        -- **EVERY ARM IS A λ** (M33b), and a bare term in arm position is refused
        -- rather than silently wrapped. It is not a shorthand for the λ: an arm
        -- that is not a suspension is ⇒-READ when the spine is FORMED, so its body
        -- runs before ι has selected anything and every ι thereafter shares the one
        -- value it produced. Wrapping it here would also have to be done again on
        -- the executing side, and a form that two machines wrap independently is
        -- the asymmetry M33a and Σ0 spent two stages closing — so the wrap is the
        -- ELABORATION's, and one spelling reaches both machines.
        -- Measured cost of refusing over the corpus: one hand-written term
        -- (`Tests.S27Dispose.deepBaseArm`), already written as `Term.lamTel []`.
        if binders.isEmpty then
          throwErr s!"seal: this recursor arm is a bare term, not a λ. Every arm is a λ, because an arm is a BODY and a body that is not suspended runs when the spine is formed rather than when ι selects it. An arm the motive owes nothing binds the unit binder — write it `Term.lamTel [(unitBinder, .cmpT (.const \"Unit\"))] ⟨body⟩`, which is what `fn`'s elaboration writes for you."
        let owed := binders.drop pre.length
        let ty := if Term.telTakesUnit owed then Term.unitPi ty else ty
        match piAgree owed ty with
        | .error e => throwErr e
        | .ok (tel, ret) => checkRFnBody fuel (pre ++ tel) ret body
  termination_by fuel _ _ _ _ => (fuel, 10, 0)
  /-- **Sealing a RECURSOR whose arms are bodies** (§7): the checking side of the
      rule part 1 gave the executing machine.

      **The motive is derived from the signature**, exactly as §7 says the macro
      derives it: peel one Π off the ascription and the codomain IS the motive's
      body, with the scrutinee as its binder. The written motive is then compared
      against the derived one — syntactically UP TO α, and the syntactic part is
      forced rather than lazy: the motive contains borrow types, which have no
      `Val` and therefore no conversion to be compared up to. (The α part was free
      while binders were indices and is stated explicitly since M30 step 2 — a
      motive written `λ (f : Nat). …` against an ascription binding `fuel` is the
      same motive.) Since phase D's macro derives
      it, they agree by construction; a hand-written mismatch is told what was
      expected.

      **Each arm is checked once, at its own constructor.** There is no symbolic
      scrutinee to split on and there does not need to be: `Z` and `S k` ARE the
      split, the motive instantiated at each is the goal, and the induction is the
      arms. That is why this needed no new driver — `exploreMatch` forks paths
      because a runtime match does not know its scrutinee, while a recursor's arms
      come labelled.

      **`ih` is the sealed self-view at the predecessor** — typed `P k` where the
      arm proves `P (S k)` — and §7's convergence argument is what makes that the
      whole story: a recursive occurrence never sees the body, so self-ensures is
      FORCED, not stipulated. The `[k]` guard evaporates with it: `ih` is a
      binder, a binder cannot be a self-call, and there is no rule left to police. -/
  def sealRec : Nat → SealKey → String → List Term → Term → M Val
    | fuel, key, c, args, u => do
      match u with
      | .pi sn scrutDom R => do
        let mi := match recLayout c with | some (_, m, _) => m | none => 0
        let derived : Term := .lam sn scrutDom R
        match args[mi]? with
        | none => throwErr s!"seal: {c} spine has no motive argument"
        | some written =>
          if !(Term.alphaEq written derived) then
            throwErr s!"seal: the recursor's motive is not the one its ascription derives. §7 derives the motive from the signature — the sealed Π with the scrutinee peeled off — so a `{c}` sealed at `Π (n : τ) → R` must be written with the motive `λ (n : τ). R` and this one is not."
          else
            match c, args with
            | "natRec", [_, z, s] => do
              match Term.peelLams z, Term.peelLams s with
              | (zn, zbody), (k :: ihv :: rest, sbody) => do
                checkArm fuel zbody [] zn (Term.substP sn (.ctorApp "Z" []) R)
                checkArm fuel sbody [(k.1, scrutDom), (ihv.1, Term.substP sn (.var k.1) R)]
                  (k :: ihv :: rest)
                  (Term.substP sn (.ctorApp "S" [.var k.1]) R)
                sealMint fuel key (piBinderNames u) u
              | _, _ => throwErr "seal: natRec's arms must be runtime λs, and the step arm must bind at least the predecessor and `ih` (§7's `λ f'. λ ih. λ v Hfuel. …`)"
            | "listRec", [_, _, pn, pc] => do
              match Term.peelLams pn, Term.peelLams pc with
              | (nn, nbody), (h :: tl :: ihv :: rest, cbody) => do
                checkArm fuel nbody [] nn (Term.substP sn (.ctorApp "Nil" []) R)
                -- `h`'s type is the element type, read off the scrutinee's own
                -- `List A`; anything else and the arm is not this recursor's.
                let elemTy : Term := match scrutDom with
                  | .app (.const "List") a => a
                  | _ => .const "Nat"
                checkArm fuel cbody
                  [(h.1, elemTy), (tl.1, scrutDom), (ihv.1, Term.substP sn (.var tl.1) R)]
                  (h :: tl :: ihv :: rest)
                  (Term.substP sn (.ctorApp "Cons" [.var h.1, .var tl.1]) R)
                sealMint fuel key (piBinderNames u) u
              | _, _ => throwErr "seal: listRec's arms must be runtime λs, and the Cons arm must bind at least the head, the tail and `ih`"
            | "boolRec", [_, tArm, fArm] => do
              match Term.peelLams tArm, Term.peelLams fArm with
              -- `fbs`, not `fn`: `fn` is a SURFACE keyword and the surface is
              -- below the kernel since M33 macro-top.
              | (tn, tbody), (fbs, fbody) => do
                checkArm fuel tbody [] tn (Term.substP sn (.ctorApp "True" []) R)
                checkArm fuel fbody [] fbs (Term.substP sn (.ctorApp "False" []) R)
                sealMint fuel key (piBinderNames u) u
            | _, _ => throwErr s!"seal: `{c}` is not a recursor this phase checks as a sealed function, or its spine is not the bare `{c} P ⟨arms⟩` (the scrutinee is the SEALED Π's own binder, so it must not be applied)"
      | _ => throwErr "seal: a recursor sealed as a function must be ascribed a Π — its first binder is the scrutinee the recursion is on (§7's derived motive)"
  termination_by fuel _ _ _ _ => (fuel, 11, 0)
  /-- The forgetting half, shared by both sealed-function rules: a fresh σ whose
      signature is the ascribed Π peeled at the given binders — which must be
      POSITIONAL, the convention `processArgs`/`buildResult` read a telescope by.
      What a caller sees is a callee indistinguishable from a table entry.

      **And a `Val` type too, whenever the Π has one.** A sealed function is a
      value like any other — it can be returned, or passed — and that means
      `hasType` may be asked about it, which needs `sctx`. A borrow-moded Π has no
      `Val`, so such a σ lives in `fsig` alone and is callable but not otherwise
      typeable; a borrow-free one gets both, and the two agree by construction
      since they are peeled and read from the same term. (Found by a seal in
      return position: `hasType: σ has no type in sctx`, from a function whose
      result IS a sealed function.) -/
  def sealMint : Nat → SealKey → List Var → Term → M Val
    | fuel, key, _names, u => do
        -- **The Π itself goes into `fsig`** (M27-δ). It used to be peeled here
        -- into a record at POSITIONAL binders, which is the convention
        -- `processArgs`/`buildResult` read a telescope by — but the peel is
        -- `piPeel` at `piBinderNames`, which the call site can do for itself, and
        -- doing it there means there is one representation of a signature rather
        -- than two kept in step by hand. The binder MODES survive the round trip,
        -- since `piBinderNames` encodes each one in the name it synthesizes; what
        -- does not survive is the λ's own display names, which cost a call-site
        -- message its programmer-written parameter name and nothing else.
        let σ ← sealSym key
        modify (fun s => { s with fsig := (σ, u) :: s.fsig })
        if !hasBorrowT u then do
          let uV ← readC fuel u
          modify (fun s => { s with sctx := (σ, uV) :: s.sctx })
        pure (.know (Term.sym σ))
  termination_by fuel _ _ _ => (fuel, 12, 0)
  /-- Sealing a runtime λ: check it, then forget it.

      The two halves are §5's two sentences. The check is ONE conversion (M27
      α.1b) — the Π the λ states against the Π that was ascribed, `piAgree` —
      followed by `checkRFnBody` on the telescope that agreement yields, at the λ's
      OWN binder ids, which are the ids its body reaches Ω through.
      The forgetting mints a σ carrying the same Π peeled at POSITIONAL binders,
      which is the convention `processArgs`/`buildResult` read a telescope by, so
      what a caller sees is a callee indistinguishable from a table entry. Both
      peels come from the same `u`, so they cannot disagree. -/
  def sealFn : Nat → SealKey → List (Var × Term) → Term → Term → M Val
    | fuel, key, binders, body, u => do
      -- **ONE CONVERSION** (M27 α.1b). The λ states its own telescope, so the seal
      -- compares that against the ascription rather than descending the ascription
      -- to supply it. The return type still comes from `u`, and that is not an
      -- exception to synthesis — it is the one thing a BODY cannot synthesize
      -- (§5 point 4: the ascription is the contract, and a contract is about what
      -- comes back).
      match piAgree binders u with
      | .error e => throwErr e
      | .ok (tel, ret) => do
        checkRFnBody fuel tel ret body
        -- The caller-visible signature keeps the λ's own binder NAMES (so a
        -- rejection at a call site names what the programmer wrote) at POSITIONAL
        -- ids (so `processArgs` reads it like any telescope).
        sealMint fuel key (binders.zipIdx.map (fun p => Var.mk p.2 p.1.1.name)) u
  termination_by fuel _ _ _ _ => (fuel, 7, 0)
  /-- **The checking-mode call rule** (§5.3/§6.1), factored out of `.call` (M26-C)
      because a SEALED function is called by exactly the same rule: a σ whose
      signature is a borrow-moded Π is a callee whose telescope and return type
      are known and whose body is not, which is what a table entry already was.
      §3 says this in advance — "today's call rule is not a separate concept from
      application; it is abstract application at a moded Π" — and factoring is
      what turns that from a remark into a fact about the code.

      The `[k]` guard used to ride along here and be inert for a seal. It is gone
      (M27-δ) — §7's `ih` is a binder and a binder cannot be a self-call, and §8's
      let-chain cannot reference downward, so there is no premise left for a side
      condition to guard. -/
  def callDeclC : Nat → List (String × Term) → Term → List Term → M Val
    | fuel, telescope, retType, args => do
          -- CHECKING (§5.3/§6.1): signature only, mint one loan group. The
          -- instantiation `inst` (decl var → actual, §5.3) instantiates the
          -- return and owed types at the actuals this call was given.
          -- An argument may itself be a call, whose own `processArgs` moves the
          -- breadcrumb inwards. Put back the enclosing call's argument on the way
          -- out, so a failure after the nested call points at the argument it
          -- belongs to. Success path only: a rejection inside keeps its own key.
          let outerArg := (← get).argKey
          let (captured, inst) ← processArgs fuel 0 [] telescope args
          modify (fun st => { st with argKey := outerArg })
          -- **§8's [k] GUARD IS GONE** (M27-δ), and it left with the path that
          -- fed it. The guard was a side condition on signature-only checking: a
          -- self-call is admitted at the function's own declared return type, so
          -- something had to be required to decrease. §7 replaced the premise
          -- rather than the check — a recursive occurrence is the `ih` BINDER, and
          -- a binder cannot be a self-call — and §8 replaced what is left: scope
          -- is the let-chain, and a let-chain cannot reference downward, so a
          -- self-call resolves to nothing at all.
          --
          -- It had to die in `checkFn`'s own commit and not before. `selfRec` was
          -- set by exactly one place, `checkFn`'s seeding, so removing the guard
          -- alone would have left the declaration path admitting `recBad` —
          -- `fn recBad () -> Id Nat Z (S Z) { recBad() }` — and proving `Z = S Z`.
          -- `S23Direct`'s battery now asserts the replacement from both sides:
          -- `recBad` and `recMutA` MIGRATE and are refused as "unknown function",
          -- and `recSame`/`recWrongIdx`/`recGrow` are refused one layer earlier by
          -- `fnElab`, which will not elaborate a self-call at a non-predecessor.
          -- Build the result and the loans it issues from the return type (a
          -- single borrow, a Pair/Σ of borrows for a multi-issued group, or a
          -- plain existential wire). One group ties captured to issued.
          -- §5.4 caller-side σ-sharing: mint one σ' per captured borrow (typed at
          -- its owed type). The retType's bare `*v` (marked `@exit`) reflects to
          -- σ', and the group PINS that captured loan's release to σ' — so the
          -- returned evidence and the recovered owner are the same σ'. `old *v`
          -- clears through to the actual entry payload (entrySyms emptied for the
          -- reflect, so callee/caller var-id collisions can't shadow it). Empty
          -- when there are no borrow args (a no-op) and dead under a `back` (which
          -- releases via the spec instead of the pinned σ').
          let borrowIds := borrowParamIds telescope
          let sigmas ← (captured.map (·.2.1)).mapM (fun owed => do
            let σ ← freshSym
            modify (fun s => { s with sctx := (σ, owed) :: s.sctx })
            pure σ)
          let exitMap := borrowIds.zip sigmas
          let savedE := (← get).exitSyms
          let savedO := (← get).entrySyms
          modify (fun s => { s with exitSyms := exitMap, entrySyms := [] })
          let (resultVal, issued) ← buildResult fuel inst [] (markExit borrowIds retType)
          modify (fun s => { s with exitSyms := savedE, entrySyms := savedO })
          let ρ ← freshGroup
          -- §6.2's declared backward spec used to be reflected here, so the group
          -- could compute each captured release from the surrendered values instead
          -- of minting an existential. M27 retired the mechanism — the ensures IS
          -- the contract (§5 point 4) — and the PIN is its checked successor: a
          -- release the SIGNATURE declares (per loan, optional) and both ends
          -- check, where `back` was a second declaration nobody checked.
          --
          -- **D6/D5: a caller may never strengthen at a call.** The debt a call
          -- registers comes from the CALLEE's parameter type; if the loan already
          -- carries a debt (its own signature's, on a pass-through), the new debt
          -- must ENTAIL it — two pins must convert, and a pinned loan may not be
          -- handed to a callee that promises no pin, because an opaque release
          -- (a fresh existential) can never pay a pinned debt (§2.2: to pin a
          -- loan, every group that transitively holds it must pin it).
          captured.forM (fun (ℓ, _, upin) => do
            ((← get).debts.filter (·.loan == ℓ)).forM (fun dOld => do
              match dOld.pin with
              | some pOld =>
                match upin with
                | some pNew =>
                  if Pure.convert fuel pOld pNew then pure ()
                  else throwErr s!"call: loan ℓ{subNat ℓ} already owes the pin ({pOld.pretty}) and this callee pins its parameter to ({pNew.pretty}), which does not convert with it — at most one pin may be effective on a loan (D5), and a call may neither strengthen nor silently weaken one (D6)"
                | none => throwErr s!"call: loan ℓ{subNat ℓ} owes the pin ({pOld.pretty}) but this callee's parameter states none — an opaque callee releases a fresh existential, which cannot pay a pinned debt. To pin a loan, every group that holds it must pin it (12-design §2.2)."
              | none => pure ()))
          -- The group is the ORDERING; the contracts are debts (12-design §2.1):
          -- one per captured loan, pinned to the CALLEE's declared pin when the
          -- signature writes one, else to §5.4's exit σ′ (`some (sym σ′)` — the
          -- release the exitRelease table used to name); one per issued loan,
          -- carrying the result's own pin when the signature writes one (§5).
          let callDebts := (captured.zip sigmas).map (fun ((ℓ, owed, upin), σ') =>
            { loan := ℓ, owed := owed, pin := upin.orElse (fun _ => some (Term.sym σ')),
              site := .call ρ : Debt })
          let issueDebts := issued.map (fun (ℓ, owed, ipin) =>
            { loan := ℓ, owed := owed, pin := ipin, site := .issue ρ : Debt })
          let grp : Group := { id := ρ, captured := captured.map (·.1), issued := issued.map (·.1) }
          modify (fun s => { s with groups := grp :: s.groups,
                                    debts := s.debts ++ callDebts ++ issueDebts })
          pure resultVal
  termination_by fuel _ _ => (fuel, 5, 0)
  -- Walk the statement spine as written (docs/19 v2: no pre-normalization),
  -- returning one result per execution path. Non-match steps delegate to the
  -- single-path `M` machinery; a STATEMENT-position match is JOINED
  -- (`exploreJoin`); a terminal match forks per branch on a symbolic
  -- scrutinee, stays single-path on a concrete one. Fuel bounds spine depth.
  -- The lexicographic `(fuel, tag, len)` measure admits the same-fuel handoffs
  -- (match → per-branch loop → branch body). -/
  def exploreD : Nat → Term → St → List (Except Diag (Val × St))
    | 0, _, _ => [.error { msg := "explore: out of fuel" }]
    | fuel + 1, t, st =>
      match t with
      -- A TERMINAL match: nothing follows it, so there is nothing to join —
      -- one audited path per arm, exactly as ever (a tail match's arms each
      -- end the body, and the fork and the join coincide with no continuation).
      | .matchE scrut eqn branches => exploreMatch fuel scrut eqn branches st
      -- **THE JOIN, UNCONDITIONALLY** (docs/19 v2): a STATEMENT-position match
      -- — both shapes — checks its arms terminally under their refinements and
      -- then the continuation ONCE, from the pre-split state, per-slot by the
      -- conservative ladder. No annotation, no fork.
      | .letIn x (.matchE scrut eqn branches) rest =>
        exploreJoin fuel (some x) scrut eqn branches rest st
      | .seq (.matchE scrut eqn branches) rest =>
        exploreJoin fuel none scrut eqn branches rest st
      -- §6's comptime `let`, HERE as well as in `readR`. The explore driver does
      -- not route statement-spine steps through `readR`'s own `.letIn` case, so a
      -- rule that lives only there would be dead for every real body. Since
      -- M33's Σ0 prerequisite that is not two copies of the rule but ONE
      -- (`letStep`), for the reason the third driver made unignorable.
      | .letIn x rhs rest =>
        match (letStep fuel x rhs).run st with
        | .error e sErr => [.error (Diag.of e sErr)]
        | .ok _ st' => exploreD fuel rest st'
      | .seq e rest =>
        match (seqStep fuel e).run st with
        | .error e sErr => [.error (Diag.of e sErr)]
        | .ok _ st' => exploreD fuel rest st'
      | .assign p rhs rest =>
        match (assignStep fuel p rhs).run st with
        | .error e sErr => [.error (Diag.of e sErr)]
        | .ok _ st' => exploreD fuel rest st'
      | other =>                                     -- final expression
        match (do noteStmt other; readResult fuel st.retTyVal other).run st with
        | .error e sErr => [.error (Diag.of e sErr)]
        | .ok v st' => [.ok (v, st')]
  termination_by fuel _ _ => (fuel, 0, 0)
  /-- **The tail of a body is read AGAINST its return type** (M32 R3b,
      suspensions.md §2.1/§2.5), and this is the one place a Σ component's binder
      MODE becomes operative rather than decorative.

      §2.1 makes every binder's case its mode, Σ binders included. Until here that
      was true of the name and of nothing else: `Uni`'s Σ rows emit `.sigmaT x τ b`
      with no `binderDom`, so `Σ (H : Le a b)` and `Σ (h : Le a b)` were the same
      term to every judgment, and a Σ was BUILT by `readArgs`, which reads a
      `ctorApp`'s arguments with no type in hand and therefore ⇒-reads all of them.

      That is precisely §2.5's wall. A proof of a ∀-statement is a λ, the corpus
      returns one in a Σ tail, and capitalising the binding that holds it (which
      §2.5 requires) then fails at the RETURN — `fence: 'Cnt' … cannot be ⇒-moved`
      — because the `Pair` that carries it out is a ⇒-read of a capital binding.
      R3 measured that wall and named the fix: a Σ component's binder mode has to
      move first.

      This is that move, at the smallest site that carries it. A `Pair` checked
      against a `Σ` reads each component by that component's binder: a CAPITAL Σ
      binder names a comptime component, so its value is ⇝-read — non-consuming,
      and the erasure fence is not in the way because nothing is being moved; a
      lowercase one is ⇒-read exactly as before. Everywhere else — a non-`Pair`
      tail, a non-`Σ` return type, an unpinned return type — this is `readR`, so
      the change reaches nothing that does not return a dependent pair.

      The second component is read against `B[a]`, the Σ's tail instantiated at
      what the first component turned out to be, which is what makes the chain
      `Σ (hi : List Nat). Σ (Hub : …). … → Π n. Id …` decide each of its
      components separately rather than all of them by the outermost binder. -/
  def readResult : Nat → Option Term → Term → M Val
    | 0, _, t => readR 0 t
    | fuel + 1, some ty, t =>
      match Pure.whnf fuel ty with
      -- **A COMPTIME POSITION, whichever end of the pair marked it** (M33's Σ0).
      -- One sentence covers all four now: a position is comptime iff its type
      -- carries `⇝`. A capital Σ binder puts it on the domain (R3b) and `Σ0` puts
      -- it on the codomain, and this arm is what both of them route to — ⇝, so
      -- non-consuming, so the erasure fence is not in the way and a λ here is
      -- legal because it lands in a ⇝ channel. R3b's `domComptime` test at the
      -- first component is gone as a special case: it is this rule, one level
      -- down.
      | .cmpT _ => do pure (.know (← readComptimeArg fuel t))
      | .sigmaT x dom cod =>
        match t with
        | .ctorApp "Pair" [a, b] => do
          let va ← readResult fuel (some dom) a
          let cod' := Pure.openBinder fuel x cod (subsKnowledge va)
          -- The tail is a POSITION, and it gets to be told when it is the wrong
          -- one (see `tailFence`).
          tailFence fuel cod' b
          let vb ← readResult fuel (some cod') b
          pure (.ctor "Pair" [va, vb])
        | _ => readR (fuel + 1) t
      | _ => readR (fuel + 1) t
    | fuel + 1, _, t => readR (fuel + 1) t
  termination_by fuel _ t => (fuel, 1, sizeOf t)
  def exploreMatch : Nat → Var → Option Var → List Branch → St → List (Except Diag (Val × St))
    | fuel, scrut, eqn, branches, st =>
      -- §6's fence at the OTHER match site. `readR`'s `.matchE` case only ever
      -- sees an expression-position match; a statement-position one — the only
      -- kind that may split a symbolic scrutinee, and therefore the only kind a
      -- real body writes — arrives here instead. Fencing one and not the other
      -- would have left the headline rejection (`match Fuel`) unreachable, which
      -- is how this was found: the test failed, not the reasoning.
      match (do noteStmt (.matchE scrut eqn branches)
                fenceComptime scrut "cannot be the scrutinee of a runtime match").run st with
      | .error e sErr => [.error (Diag.of e sErr)]
      | .ok _ st =>
      match (reorgScrut fuel scrut).run st with
      | .error e sErr => [.error (Diag.of e sErr)]
      | .ok disp st' =>
        match disp with
        | .ownedCtor name fields =>
          match (ownedSelect scrut eqn branches name fields).run st' with
          | .error e sErr => [.error (Diag.of e sErr)]
          | .ok body st'' => exploreD fuel body st''
        | .borrowCtor ℓ name fields =>
          match (borrowSelect scrut eqn branches ℓ name fields).run st' with
          | .error e sErr => [.error (Diag.of e sErr)]
          | .ok body st'' => exploreD fuel body st''
        | .ownedSym σ stuck =>
          match (checkExhaustive fuel σ branches).run st' with
          | .error e sErr => [.error (Diag.of e sErr)]
          | .ok _ st'' => exploreSymBranches fuel scrut false 0 σ stuck eqn branches st''
        | .borrowSym ℓ σ =>
          match (checkExhaustive fuel σ branches).run st' with
          | .error e sErr => [.error (Diag.of e sErr)]
          | .ok _ st'' => exploreSymBranches fuel scrut true ℓ σ none eqn branches st''
  termination_by fuel _ _ _ _ => (fuel, 2, 0)
  /-- One symbolic path per branch, in declaration order. `borrow` selects the
      setup; `ℓ` is the parent loan (borrow mode only); `σ` is the scrutinee's
      symbolic id (used to type the field σ's); `stuck` is the pre-abstraction
      spine, when the σ came from one; `eqn` the declared equation binder. -/
  def exploreSymBranches : Nat → Var → Bool → Nat → Nat → Option Term → Option Var →
      List Branch → St → List (Except Diag (Val × St))
    | _, _, _, _, _, _, _, [], _ => []
    | fuel, scrut, borrow, ℓ, σ, stuck, eqn, br :: rest, st =>
      (match ((if borrow then symBorrowSetup fuel scrut ℓ σ eqn br
               else symOwnedSetup fuel scrut σ stuck eqn br)).run st with
       | .error e sErr => [.error (Diag.of e sErr)]
       | .ok body st' => exploreD fuel body st')
      ++ exploreSymBranches fuel scrut borrow ℓ σ stuck eqn rest st
  termination_by fuel _ _ _ _ _ _ branches _ => (fuel, 1, branches.length)
  /-- **The join driver, unconditional** (docs/19 v2): a STATEMENT-position
      match, either shape. `x?` is the `let` binder (`none` for `seq`, whose
      result is discarded). A CONCRETE scrutinee and the ONE-BRANCH match are
      walked single-path in the fork shape — with one arm the fork and the join
      are the same walk, so field knowledge and arm scoping are kept losslessly
      — and every genuinely branching symbolic match is joined. -/
  def exploreJoin : Nat → Option Var → Var → Option Var → List Branch → Term → St →
      List (Except Diag (Val × St))
    | fuel, x?, scrut, eqn, branches, rest, st =>
      let rebuilt := match x? with
        | some x => pushJoinArms x rest branches
        | none => pushJoinArmsSeq rest branches
      if branches.length == 1 then
        exploreMatch fuel scrut eqn rebuilt st
      else
      match (do noteStmt (.matchE scrut eqn branches)
                fenceComptime scrut "cannot be the scrutinee of a runtime match"
                reorgScrut fuel scrut).run st with
      | .error e sErr => [.error (Diag.of e sErr)]
      | .ok disp stR =>
        match disp with
        | .ownedCtor _ _ | .borrowCtor _ _ _ =>
          -- Delegate on the ORIGINAL state: `exploreMatch` re-runs the fence
          -- and the reorganization itself.
          exploreMatch fuel scrut eqn rebuilt st
        | .ownedSym σ stuck =>
          joinSym fuel x? scrut false 0 σ stuck eqn branches rest stR
        | .borrowSym ℓ σ =>
          joinSym fuel x? scrut true ℓ σ none eqn branches rest stR
  termination_by fuel _ _ _ _ _ _ => (fuel, 3, 0)
  /-- The symbolic join: every arm from the same pre-split `St₀` (checked
      exactly as today — refinement, branch equations, modes), then ONE
      continuation from `St₀` with every slot joined by the ladder and the
      result bound by it too. Per-arm knowledge dies at the seam; obligations
      carry from `St₀` (loan-keyed); the fn's audit runs once, on the joined
      path. -/
  def joinSym : Nat → Option Var → Var → Bool → Nat → Nat → Option Term → Option Var →
      List Branch → Term → St → List (Except Diag (Val × St))
    | fuel, x?, scrut, borrow, ℓ, σ, stuck, eqn, branches, rest, stR =>
      match (checkExhaustive fuel σ branches).run stR with
      | .error e sErr => [.error (Diag.of e sErr)]
      | .ok _ st0 =>
        let armPaths := exploreJoinArms fuel scrut borrow ℓ σ stuck eqn st0.nextLoan branches st0
        match armPaths.foldr (fun p acc => do pure ((← p) :: (← acc)))
                (Except.ok [] : Except Diag (List (Val × St))) with
        | .error d => [.error d]
        | .ok exits =>
          let stM := mergeArmMints st0 (exits.map (·.2))
          let ctors := branches.map (·.ctor)
          let armCtx := exits.map (fun (_, stA) => (stA.sctx, stA.nextSym))
          let joinAct : M Unit := do
            -- Ω, slot by slot: the ladder decides each one. A slot an arm
            -- dropped is gone (⊥). The scrutinee needs no special case — an
            -- owned split leaves it ⊥ in every arm (rule 2), and a borrow
            -- split leaves the same loan whose collapsed payload the ladder
            -- re-types at the owed source (rule 3).
            let baseEnv := (← get).env
            let newEnv ← baseEnv.mapM (fun kv => do
              let armVs := (exits.zip armCtx).map (fun ((_, stA), (sctxA, hiA)) =>
                (((stA.env.find? (fun e => e.1.id == kv.1.id)).map (·.2)).getD .bot, sctxA, hiA))
              let v ← joinVal s!"'{kv.1.name}'" ctors st0.sctx st0.nextSym fuel (some kv.2) armVs none
              pure (kv.1, v))
            modify fun stJ => { stJ with env := newEnv }
            -- the result: the ladder again, with no base — bound only for the
            -- `let` shape; a `seq` match's result is discarded, disagreements
            -- and all
            match x? with
            | none => pure ()
            | some x => do
              let armRs := (exits.zip armCtx).map (fun ((v, _), (sctxA, hiA)) => (v, sctxA, hiA))
              let rv ← joinVal s!"the result bound to '{x.name}'" ctors st0.sctx st0.nextSym fuel none armRs none
              bindSlot x rv
          match joinAct.run stM with
          | .error e sErr => [.error (Diag.of e sErr)]
          | .ok _ stJ => exploreD fuel rest stJ
  termination_by fuel _ _ _ _ _ _ _ _ _ _ => (fuel, 2, 1)
  /-- One arm of a joining match: setup exactly as the fork's (`symOwnedSetup`/
      `symBorrowSetup` — refinement, branch equations, modes), explored
      TERMINALLY with no result type (`retTyVal := none`; the seam's ladder is
      what judges the values), then the arm's own loans ended
      (`collapseArmLoansFrom`) so a borrow scrutinee's payload is a VALUE at
      the seam. -/
  def exploreJoinArms : Nat → Var → Bool → Nat → Nat → Option Term → Option Var →
      Nat → List Branch → St → List (Except Diag (Val × St))
    | _, _, _, _, _, _, _, _, [], _ => []
    | fuel, scrut, borrow, ℓ, σ, stuck, eqn, loanLo, br :: rest, st =>
      (match ((if borrow then symBorrowSetup fuel scrut ℓ σ eqn br
               else symOwnedSetup fuel scrut σ stuck eqn br)).run st with
       | .error e sErr => [.error (Diag.of e sErr)]
       | .ok body st' =>
         (exploreD fuel body { st' with retTyVal := none }).map (fun p =>
           match p with
           | .error d => .error d
           | .ok (v, stA) =>
             match (collapseArmLoansFrom fuel loanLo).run stA with
             | .error e sErr => .error (Diag.of e sErr)
             | .ok _ stA' => .ok (v, stA')))
      ++ exploreJoinArms fuel scrut borrow ℓ σ stuck eqn loanLo rest st
  termination_by fuel _ _ _ _ _ _ _ branches _ => (fuel, 1, branches.length)
end

/-- The path explorer as everything outside the diagnostics path sees it: the
    breadcrumb dropped, errors plain `String`s. `exploreD` is the same function
    with the breadcrumb kept. -/
def explore (fuel : Nat) (t : Term) (st : St) : List (Except String (Val × St)) :=
  (exploreD fuel t st).map (Except.mapError Diag.msg)

/-! ## Running programs -/

/-- The initial machine state: empty Ω, fresh supplies at 0. -/
def initSt : St := { env := [], nextLoan := 0, nextVar := 0, nextSym := 0 }

/-- Generous default fuel; §2 programs use only a handful. -/
def defaultFuel : Nat := 1000

/-- **The program boundary** (M32 R3): number the seals, then normalize the
    statement spine. Every entry point that turns a `Term` into a run goes
    through here, and nothing else does.

    Numbering is all that remains here since docs/19 v2: the statement spine is
    NOT rewritten — continuations stay where the program wrote them, the seam
    shape is built lazily where a match is walked (`pushJoinArms` at `readR`/
    `readRTail`'s statement-match rows and `exploreD`'s concrete delegation),
    and the checking walk joins instead of duplicating. The old pre-pass
    duplicated continuations into arms, which is why numbering had to come
    first; with no duplication the order constraint is vacuous, and bodies
    entered later (`checkRFnBody`, a callee frame) are simply walked as they
    are, their seals already carrying their sites. -/
def atBoundary (t : Term) : Term := (Term.numberSeals t).2

/-- Run a program with a fresh state: ⇒-read it, then return the final
    canonicalized Ω (loan ids renumbered to first-appearance order), or the
    error. The return value of the read is discarded — §2 tests inspect Ω. -/
def runProg (t : Term) (fuel : Nat := defaultFuel) : Except String Env :=
  -- The seam markers that close a match arm's scope are built where the match
  -- is walked (`pushJoinArms` at `readR`'s statement-match rows), so the raw
  -- term is the right thing to hand over — `atBoundary` numbers seals and
  -- nothing else since docs/19 v2.
  match (readR fuel (atBoundary t)).run initSt with
  | .ok _ st => .ok (canonicalize st.env)
  | .error e _ => .error e

/-- Whether `needle` occurs as a substring of `hay`. -/
def strContains (hay needle : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- Test helper: the program succeeds with the given final environment. -/
def expectEnv (t : Term) (expected : Env) : Bool :=
  match runProg t with
  | .ok env => env == expected
  | .error _ => false

/-- Test helper: the program is rejected with an error containing `needle`. -/
def expectErr (t : Term) (needle : String) : Bool :=
  match runProg t with
  | .ok _ => false
  | .error e => strContains e needle


/-! ## Running symbolic programs -/

/-- Largest element of a `Nat` list, or 0 if empty. -/
def maxNat (xs : List Nat) : Nat := xs.foldl Nat.max 0

/-- Build a machine state from a seed Ω, with fresh supplies set safely above
    every id already present (loan, sym, var). Stands in for a telescope entry
    until §5 gives borrow arguments a real frame. -/
def seedSt (seed : Omega) : St :=
  { env := seed
    nextLoan := maxNat (seed.flatMap (fun kv => kv.2.loanIds)) + 1
    nextVar := maxNat (seed.map (fun kv => kv.1.id)) + 1
    nextSym := maxNat (seed.flatMap (fun kv => kv.2.symIds)) + 1 }

/-- Explore a program from a seeded Ω, returning one canonicalized final
    environment (or error) per execution path, in branch-declaration order. -/
def runExplore (seed : Omega) (t : Term) (fuel : Nat := defaultFuel) : List (Except String Env) :=
  (explore fuel (atBoundary t) (seedSt seed)).map
    (fun r => r.map (fun p => canonicalize p.2.env))

/-- Test helper: the program has exactly the given paths (each an `Env`), in
    order, all succeeding. -/
def expectPaths (seed : Omega) (t : Term) (expected : List Env) : Bool :=
  let rs := runExplore seed t
  rs.length == expected.length &&
    (rs.zip expected).all (fun pr => match pr.1 with | .ok env => env == pr.2 | .error _ => false)

/-- Test helper: some path is rejected with an error containing `needle`. -/
def expectSomePathErr (seed : Omega) (t : Term) (needle : String) : Bool :=
  (runExplore seed t).any (fun r => match r with | .error e => strContains e needle | .ok _ => false)

/-- Run an `M` action against a seeded Ω, projecting to `Except String Unit`
    (for direct arrow tests such as `writeC` on a non-symbolic place). -/
def expectMErr (seed : Omega) (m : M Unit) (needle : String) : Bool :=
  match m.run (seedSt seed) with
  | .ok _ _ => false
  | .error e _ => strContains e needle

/-! ## Pure test helpers -/

/-- Seed a state with an Ω and a σ-context. -/
def seedPure (env : Omega) (sctx : List (Nat × Term)) : St := { seedSt env with sctx := sctx }

/-- Test helper: `readC t` equals `expected` (by structural value equality). -/
def expectReadC (env : Omega) (sctx : List (Nat × Term)) (t : Term) (expected : Term)
    (fuel : Nat := defaultFuel) : Bool :=
  match (readC fuel t).run (seedPure env sctx) with
  | .ok v _ => v == expected
  | .error _ _ => false

/-- Test helper: `readC t₁` and `readC t₂` are convertible. -/
def expectConv (env : Omega) (sctx : List (Nat × Term)) (t1 t2 : Term)
    (fuel : Nat := defaultFuel) : Bool :=
  match (do let a ← readC fuel t1; let b ← readC fuel t2; pure (Pure.convert fuel a b)).run
      (seedPure env sctx) with
  | .ok r _ => r
  | .error _ _ => false

/-- Test helper: value `v` has type `ty` under the σ-context. -/
def expectHasType (env : Omega) (sctx : List (Nat × Term)) (v ty : Term)
    (fuel : Nat := defaultFuel) : Bool :=
  match (hasTypeT fuel v ty).run (seedPure env sctx) with
  | .ok r _ => r
  | .error _ _ => false

end Dllbc
