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

/-- A function declaration (§1.2). Lives here so the checking context (`St`)
    can carry a table of them — a call is checked against a *signature only*,
    never another body (recursion forces this, §5.3). Full construction/audit
    is in `Boundary.lean`. -/
structure Decl where
  name : String
  telescope : List (String × Term)
  retType : Term
  body : Term
  /-- §6.2 declared backward spec: a pure function from the issued borrows'
      surrendered values (in issued order) to the captured borrow's release
      value. `none` = opaque parameter-end (a fresh existential on release, the
      default, §6.1). DECLARED here and CHECKED against the body (the sound
      reincarnation of M8's removed inferred `constrained` wire): a caller of a
      spec'd fn recovers the COMPUTED release, not a fresh σ. Written over the
      telescope's snapshots and `%rᵢ` for the surrendered values (via pure de
      Bruijn: `rᵢ` are the leading λ binders). -/
  back : Option Term := none
  /-- §1.2's `[k]` — the **decreasing-argument index**, made operational by M23.
      A self-call is admitted at this function's declared return type only if the
      actual at index `k` is a strict structural predecessor of that parameter's
      current snapshot (§8's snapshot-subterm guard; the rule lives in the call
      rule below). `none` means the function does not recurse — a self-call in a
      body with no `[k]` is REJECTED, because admitting a call at its own declared
      postcondition with nothing decreasing is the Hoare rule without its side
      condition, and proves anything: `fn bad () -> Id Nat Z (S Z) { bad() }`. -/
  dec : Option Nat := none

/-- What an argument borrow owes at the boundary: its slot variable, its loan
    id, and the owed type (§5.1's `S`, instantiated at the entry snapshot).
    Lives in `St` (not just returned by `seedTelescope`) so that a §10 Refl
    refinement — which substitutes a σ everywhere — reaches the owed types too:
    a through-borrow `p : &mut (Id A a b)` matched against `Refl` refines the
    σ that its *own* owed type mentions, and the audit must see the refined
    type, not the frozen entry snapshot. -/
structure Obligation where
  arg : Var
  loan : Nat
  owed : Val

/-- A **loan group** (§6.1): the node a call mints, tying the loans it
    **captured** (the argument borrows' loans, with their owed types) to the
    borrows it **issued** (loans of any borrows in the result, owed-typed from
    the return type). The ending discipline is the group's whole content —
    every issued borrow ends first, then the group ends atomically, releasing
    each captured loan. A §5.3 wire is the degenerate `issued = []` group; an
    identity wire (`constrained`) releases its one captured loan with the
    issued borrow's surrendered payload rather than a fresh existential. -/
structure Group where
  id : Nat                      -- the group node's ρ, its identity in the table
  captured : List (Nat × Val)   -- (ℓ, owed type)
  issued : List (Nat × Val)     -- (ℓ, owed type)
  /-- Identity-wire flag (§6.2). DEAD in real checking (inferring it is unsound);
      the test-only `forceConstrained` flag flips it to validate the differential
      harness goes RED under the removed inference. -/
  constrained : Bool
  /-- §6.2 declared backward spec, reflected and instantiated at the call
      (`Decl.back`): a function `surrendered values → captured release`. Some ⇒
      `endGroup` releases the COMPUTED value; none ⇒ opaque (fresh existential).
      Refined with the caller's σ's like the owed types. -/
  backSpec : Option Val := none
  /-- §5.4 caller-side exit-snapshot σ-sharing: per captured loan, the σ its release
      is PINNED to — the same σ the callee's return type reads as the exit `*v`
      (`buildResult`'s `@exit`). So the caller holds the owner recovering σ′ AND the
      returned evidence about the same σ′. Overrides the opaque fresh-existential
      release (`none`/opaque case) for those loans; empty for a plain call. -/
  exitRelease : List (Nat × Nat) := []

/-- Machine state: the environment Ω plus fresh-supply counters. `nextVar` is
    unused by §2 (all runtime var ids are minted by the macro) but is here for
    the runtime-binder minting later milestones (match) will need. -/
structure St where
  env : Omega
  nextLoan : Nat
  nextVar : Nat
  nextSym : Nat
  /-- The σ-context (§3.2's seam, §4): each symbolic id's type. -/
  sctx : List (Nat × Val) := []
  /-- Loan groups (§6.1). A call mints one; ending a captured loan ends the
      whole group. Replaces M6's flat owed map — a wire is the degenerate
      `issued = []` group. -/
  groups : List Group := []
  /-- Fresh-supply for group ρ ids. -/
  nextGroup : Nat := 0
  /-- The function table, for the call rule. -/
  decls : List Decl := []
  /-- The argument-borrow obligations (§5.1), seeded from the telescope and
      audited at return. Held in state (not just returned by `seedTelescope`)
      so a §10 Refl refinement propagates into the owed types — see
      `Obligation`. Each explored path carries (and refines) its own copy. -/
  obligations : List Obligation := []
  /-- The return type, evaluated ONCE at function entry (where the telescope
      params are live) and pinned. A dependent return type (§5.3) may mention a
      param the body then consumes — re-reading it at return would find a ⊥ — so
      it is fixed at entry and refined per-path with the σ's (like obligations).
      `none` for a borrow-returning body, whose owed type is read at return
      against the surrendered payload. -/
  retTyVal : Option Val := none
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
  /-- §6.2: this function's OWN declared backward spec, reflected at entry (over
      the telescope snapshots). The callee audit checks the body against it — the
      captured borrow's payload-with-issued-holes must convert with the spec
      applied to fresh hole variables. Refined per-path like the owed types. -/
  selfBack : Option Val := none
  /-- §8's snapshot-subterm guard (M23): while a body is checked, the name of the
      function being checked, and — when it declares `[k]` — that parameter's index
      together with its CURRENT snapshot. The snapshot rides `refineSym`/
      `generalizeStuck` like every other σ-bearing piece of state (the M10
      invariant), which is the whole trick: after `match fuel { S(f2) => … }` the
      parameter's slot holds ⊥ (owned match consumes it) but this value reads
      `S σ_f2`, so `f(…, f2, …)` is visibly a strict predecessor. `none` outside
      `checkFn` (executing mode runs real bodies and needs no guard). -/
  selfRec : Option (String × Option (Nat × Val)) := none
  /-- Execution mode (§8/§9 differential). `false` = CHECKING (the call rule
      uses the §5.3/§6.1 signature rule — groups, existentials); `true` =
      EXECUTING (a call runs the callee's actual body concretely). checkFn is
      always checking; the differential's concrete side is executing. -/
  executing : Bool := false
  /-- Base var id for inlined-callee frames in executing mode; caller-own vars
      stay below it, so a body's own environment is `env.filter (·.1.id < this)`. -/
  nextFrame : Nat := 10000
  /-- TEST-ONLY: force the (unsound, removed) constrained wire on, to validate
      the differential harness actually goes RED under the bug. Never set by the
      call rule; only a validation test flips it. -/
  forceConstrained : Bool := false
deriving Inhabited

/-- The machine monad: errors are `String`s, state is `St`. -/
abbrev M := EStateM String St

/-- Raise a machine error. Errors are rich and stably-shaped (operation +
    variable/loan + reason); tests assert on distinctive substrings. -/
def throwErr {α : Type} (msg : String) : M α := fun s => EStateM.Result.error msg s

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

/-- Look up a slot by variable id. Errors if the id is not an entry. -/
def lookupSlot (x : Var) : M Val := do
  match (← getEnv).find? (fun kv => kv.1.id == x.id) with
  | some kv => pure kv.2
  | none => throwErr s!"lookupSlot: {x.name}#{x.id} is not an entry of Ω (unbound at runtime)"

/-- Append a fresh binding to Ω (insertion-ordered). -/
def bindSlot (x : Var) (v : Val) : M Unit :=
  modify (fun s => { s with env := s.env ++ [(x, v)] })

/-- Overwrite an existing slot in place, preserving order. Errors if absent. -/
def setSlot (x : Var) (v : Val) : M Unit := do
  let ω ← getEnv
  if ω.any (fun kv => kv.1.id == x.id) then
    setEnv (ω.map (fun kv => if kv.1.id == x.id then (kv.1, v) else kv))
  else
    throwErr s!"setSlot: {x.name}#{x.id} is not an entry of Ω"

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
    | .ctor _ args => firstOwnNodeList args
    | _ => none                    -- sym and pure values hold no ownership nodes
  termination_by v => sizeOf v
  def firstOwnNodeList : List Val → Option (Nat × OwnKind)
    | [] => none
    | v :: vs =>
      match firstOwnNode v with
      | some r => some r
      | none => firstOwnNodeList vs
  termination_by vs => sizeOf vs
end

/-! The payload of the `borrowM ℓ _` node in `v`, if present. -/
mutual
  def findBorrowPayload (ℓ : Nat) : Val → Option Val
    | .borrowM ℓ' p => if ℓ' == ℓ then some p else findBorrowPayload ℓ p
    | .ctor _ args => findBorrowPayloadList ℓ args
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
    | .ctor n args => .ctor n (replaceLoanMarkerList ℓ newV args)
    | v => v                       -- ⊥, sym, pure values: no loan markers
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
    | .ctor n args => .ctor n (replaceBorrowWithBotList ℓ args)
    | v => v                       -- ⊥, sym, pure values: no borrow to kill
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
    | .ctor _ args => containsLoanList ℓ args
    | _ => false                   -- ⊥, sym, pure values: no loan markers
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
    | .ctor _ args => firstLoanMarkerList args
    | _ => none                    -- ⊥, sym, pure values: no owned loan marker
  termination_by v => sizeOf v
  def firstLoanMarkerList : List Val → Option Nat
    | [] => none
    | v :: vs =>
      match firstLoanMarker v with
      | some ℓ => some ℓ
      | none => firstLoanMarkerList vs
  termination_by vs => sizeOf vs
end

/-! Is a **type** index-kind (§2.1) — `Nat`/`Bool`/`Unit`, or a pure-former type
    (an `Id` proof type, a `Type`, a function type)? A σ of such a type reads by
    copy. `List`/`Σ`/user types are data. -/
def indexKindTy : Val → Bool
  | .const "Nat" => true
  | .const "Bool" => true
  | .const "Unit" => true
  | .idT _ _ _ => true
  | .type => true
  | .pi _ _ => true
  | _ => false

/-! Is a **value** index-kind, so §2.1's copy-on-read applies? A concrete
    `Nat`/`Bool`/`Unit` tree, a pure-former value (a proof — `Refl` or a neutral
    proof spine — a type, a λ), or a σ whose `sctx` type is index-kind. Data
    proper (`Cons`-trees, pairs, user constructors) MOVES even when marker-free:
    silent aggregate duplication is the cost-opacity Rust's move discipline
    prevents, so the calculus keeps Rust's line (§2.1). Copy-or-move is decided by
    value shape — the σ-context's type for symbolic values — not a declared trait.
    A σ with NO sctx entry moves (the conservative default). DEFERRED (until
    measured pain, per team-lead): tuple-of-copyables (a `Pair Nat Nat` as Copy,
    Rust-style) — a data ctor all of whose fields are index-kind stays a MOVE for
    now. -/
def indexKindV (fuel : Nat) (sctx : List (Nat × Val)) : Val → Bool
  | .ctor "Z" [] => true
  | .ctor "S" [n] => indexKindV fuel sctx n
  | .ctor "True" [] => true
  | .ctor "False" [] => true
  | .ctor "unit" [] => true
  | .ctor "Refl" _ => true                                  -- a proof
  | .ctor _ _ => false                                      -- data → move
  -- whnf the σ's type before classifying: a redex-headed type that reduces to
  -- Nat should copy, not be mistaken for data. Misclassification is otherwise
  -- only ever toward MOVE (conservative), but the whnf hardens the σ side.
  | .sym σ => match sctx.lookup σ with | some τ => indexKindTy (Val.whnfV fuel τ) | none => false
  | .type => true
  | .const _ => true
  | .pi _ _ => true
  | .lam _ _ => true
  | .idT _ _ _ => true
  | .app _ _ => true                                        -- a pure-former spine (proof/type)
  | .pvar _ => true
  | .sigmaT _ _ => true                                     -- a type
  | .borrowM _ _ => false
  | .loanM _ => false
  | .bot => false

/-! Substitute `newV` for every `sym σ` occurrence in `v` — the value-tree
    core of ⇜ (§3.2 refinement substitutes σ *everywhere*). -/
mutual
  def substSym (σ : Nat) (newV : Val) : Val → Val
    | .sym σ' => if σ' == σ then newV else .sym σ'
    | .borrowM ℓ p => .borrowM ℓ (substSym σ newV p)
    | .ctor n args => .ctor n (substSymList σ newV args)
    | .loanM ℓ => .loanM ℓ
    | .bot => .bot
    | .pvar k => .pvar k
    | .type => .type
    | .const c => .const c
    | .pi d c => .pi (substSym σ newV d) (substSym σ newV c)
    | .sigmaT d c => .sigmaT (substSym σ newV d) (substSym σ newV c)
    | .lam d c => .lam (substSym σ newV d) (substSym σ newV c)
    | .app d c => .app (substSym σ newV d) (substSym σ newV c)
    | .idT a b c => .idT (substSym σ newV a) (substSym σ newV b) (substSym σ newV c)
  termination_by v => sizeOf v
  def substSymList (σ : Nat) (newV : Val) : List Val → List Val
    | [] => []
    | v :: vs => substSym σ newV v :: substSymList σ newV vs
  termination_by vs => sizeOf vs
end

/-! Abstract a whole sub-value `target` into `sym σb` **everywhere** — the
    inverse of `substSym`, keyed on structural identity of the whole subterm
    rather than a σ id. It is the value-level core of the §19 stuck-spine split:
    a Bool scrutinee that reduced to a stuck spine (`leb σ σp`, not a bare σ) is
    generalized to a fresh σb, so the ordinary True/False refinement can fire.
    `target` must be pvar-free (a spine over σ's — no bound variables to shift),
    which the Bool spines it is used on always are; NF it before abstracting so
    the match is up to conversion-stable syntactic identity. -/
mutual
  def abstractInto (target : Val) (σb : Nat) (v : Val) : Val :=
    if v == target then .sym σb
    else match v with
      | .borrowM ℓ p => .borrowM ℓ (abstractInto target σb p)
      | .ctor n args => .ctor n (abstractIntoList target σb args)
      | .pi d c => .pi (abstractInto target σb d) (abstractInto target σb c)
      | .sigmaT d c => .sigmaT (abstractInto target σb d) (abstractInto target σb c)
      | .lam d c => .lam (abstractInto target σb d) (abstractInto target σb c)
      | .app d c => .app (abstractInto target σb d) (abstractInto target σb c)
      | .idT a b c => .idT (abstractInto target σb a) (abstractInto target σb b) (abstractInto target σb c)
      | v' => v'
  termination_by sizeOf v
  def abstractIntoList (target : Val) (σb : Nat) (vs : List Val) : List Val :=
    match vs with
    | [] => []
    | v :: rest => abstractInto target σb v :: abstractIntoList target σb rest
  termination_by sizeOf vs
end

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
    throwErr s!"end: borrow of ℓ{ℓ} is not an entry of Ω (its other end is in flight — cannot end)"
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
    throwErr s!"end: loan ℓ{ℓ} is not an entry of Ω (cannot plug payload back)"

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
  | idx : Val → Option Val → Step
  /-- `[lo ; cnt | ev]` — the range step, in OFFSET-AND-COUNT (¶2.1), so that
      `a[lo ; cnt] : Array cnt T` is read straight off the syntax with no arithmetic
      and no rule below ever produces a `sub`. -/
  | rng : Val → Val → Option Val → Step

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
def arrExtent (fuel : Nat) (v : Val) : M Val := do
  match Val.arrExtentPure? v with
  | some c => pure (Val.nfV fuel c)
  | none =>
    match v with
    | .sym σ =>
      match (← get).sctx.lookup σ with
      | some τ =>
        match Val.asArrayTy? (Val.whnfV fuel τ) with
        | some (n, _) => pure (Val.nfV fuel n)
        | none => throwErr s!"array: σ{σ} is not of array type (its sctx type is {τ.pretty})"
      | none => throwErr s!"array: σ{σ} has no type in sctx — cannot read its extent"
    | _ => throwErr s!"array: {v.pretty} is not an array value (no extent to read)"

/-- One entry of ¶3.1's **extent map**: an offset, a count, and the body sitting
    there. `Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ⟩` induces `[(0,1,owned), (1,2,loaned ℓ)]`.

    The map IS the aliasing invariant, and it is maintained by construction rather
    than checked: segments partition the array, so **no two loans of one array can
    overlap, ever, because two segments cannot overlap**. There is no disjointness
    *test* anywhere below — only the question of whether a requested range can be
    MADE into a segment, which is what the carve answers. -/
structure Leaf where
  base : Val
  count : Val
  body : Val

/-- The range's exclusive end, `lo + cnt`, spelled the way a program can write it.

    `add` recurses on its FIRST argument, so `add lo cnt` is stuck whenever `lo` is
    symbolic — including at every `a[i]`, where `cnt` is literally 1 and the obligation
    would read `Le (add i (S Z)) n`. No program writes that. `S i` denotes the same
    number and is what M13/M14's cursor bound already is (`p : Le (S i) (len *v)`) —
    which is ¶3.5's own observation that range places "take the same terms" the swap
    sites have been threading since M13. So a CONCRETE count is unrolled into
    successors and a symbolic one keeps `add`, where it computes. -/
def rangeEnd (fuel : Nat) (lo cnt : Val) : Val :=
  match Val.natOfVal? (Val.nfV fuel cnt) with
  | some k => (List.range k).foldl (fun acc _ => .ctor "S" [acc]) lo
  | none => Val.kAdd lo cnt

def extentMapGo (fuel : Nat) (b : Val) : List Val → M (List Leaf)
  | [] => pure []
  | s :: rest =>
    match Val.asSeg? s with
    | none => throwErr "array: malformed segment node (expected §seg [c, body])"
    | some (c, body) => do
      let tl ← extentMapGo fuel (Val.nfV fuel (rangeEnd fuel b c)) rest
      pure (⟨b, c, body⟩ :: tl)

/-- The sum of a leaf list's extents, RIGHT-NESTED and with no trailing `Z`.

    The shape matters and is not cosmetic. `add` recurses on its first argument, so a
    trailing `add c Z` is STUCK the moment `c` is symbolic — and then the audit's
    `Array (add k (add rest Z))` never converts with the owed `Array (add k rest)`,
    which is the one conversion premise (3)'s residue transition exists to make
    definitional. Right-nesting also matches the `arrCat` spine the ⇝ fold builds and
    the `m ≡ add lo' (add cnt rest)` the transition solves, so all three agree. -/
def sumExtents : List Leaf → Val
  | [] => Val.zero
  | [l] => l.count
  | l :: rest => Val.kAdd l.count (sumExtents rest)

/-- The extent map of an array node. An UNCARVED array is a single leaf spanning it. -/
def extentMap (fuel : Nat) (v : Val) : M (List Leaf) :=
  match v with
  | .ctor "§segs" segs => extentMapGo fuel Val.zero segs
  | _ => do pure [⟨Val.zero, ← arrExtent fuel v, v⟩]

/-- Locate the segment a step designates, by its (base, count) rather than by its
    position in the list — so navigation survives a sibling's body changing under it
    (a drop that ends a loan elsewhere in the same node, a merge that ran in between).
    Returns the segment's index and its leaf. -/
def findSeg (fuel : Nat) (lo cnt : Val) (v : Val) : M (Nat × Leaf) := do
  let leaves ← extentMap fuel v
  match leaves.findIdx? (fun l => Val.convert fuel l.base lo && Val.convert fuel l.count cnt) with
  | some i =>
    match leaves.get? i with
    | some l => pure (i, l)
    | none => throwErr "array: internal — segment index out of range"
  | none =>
    throwErr s!"array: no segment at [{lo.pretty} ; {cnt.pretty}] in {v.pretty} (the place was never carved there)"

/-- Read through one step. -/
def navStep (fuel : Nat) : Step → Val → M Val
  | .peel, v =>
    match v with
    | .borrowM _ p => pure p
    | .bot => throwErr "*: cannot peel a vacant slot (⊥)"
    | .loanM ℓ => throwErr s!"*: cannot peel loanₘ ℓ{ℓ} (suspended borrow)"
    | .ctor n _ => throwErr s!"*: cannot peel constructor '{n}' (not a borrow)"
    | .sym σ => throwErr s!"*: cannot peel symbolic value σ{σ} (not a borrow)"
    | _ => throwErr "*: cannot peel a pure value (not a borrow)"
  | .rng lo cnt _, v => do pure (← findSeg fuel lo cnt v).2.body
  | .idx i _, v => do
    -- ¶2.1: `a[i]` is NOT `a[i ; 1]`. They carve identically, but the range place's
    -- payload is an `Array 1 T` while the index place's is the ELEMENT itself, of
    -- type `T` — which is what spares every element access a coercion.
    let (_, l) ← findSeg fuel i (Val.nat 1) v
    match l.body with
    | .ctor "Arr" [e] => pure e
    | b => throwErr s!"a[i]: the one-slot segment at {i.pretty} holds {b.pretty}, not a single-element run"

/-- Write `inner` back through one step, rebuilding the node around it. -/
def setStep (fuel : Nat) : Step → Val → Val → M Val
  | .peel, v, inner =>
    match v with
    | .borrowM ℓ _ => pure (.borrowM ℓ inner)
    | .bot => throwErr "*: cannot peel a vacant slot (⊥)"
    | .loanM ℓ => throwErr s!"*: cannot peel loanₘ ℓ{ℓ} (suspended borrow)"
    | .ctor n _ => throwErr s!"*: cannot peel constructor '{n}' (not a borrow)"
    | .sym σ => throwErr s!"*: cannot peel symbolic value σ{σ} (not a borrow)"
    | _ => throwErr "*: cannot peel a pure value (not a borrow)"
  | .rng lo cnt _, v, inner => do
    let (i, _) ← findSeg fuel lo cnt v
    match v with
    | .ctor "§segs" segs =>
      pure (Val.segsNode (segs.enum.map (fun (j, s) =>
        if j == i then (match Val.asSeg? s with
                        | some (c, _) => Val.segNode c inner
                        | none => s)
        else s)))
    | _ => pure inner                              -- degenerate: the node IS the request
  | .idx i _, v, inner => do
    let (j, _) ← findSeg fuel i (Val.nat 1) v
    match v with
    | .ctor "§segs" segs =>
      pure (Val.segsNode (segs.enum.map (fun (k, s) =>
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
    state into entry-knowledge — the etiology of the M21 `partIdxL n ⊥` bug. -/
def refineSym (σ : Nat) (v : Val) : M Unit := do
  if Val.hasStateMarker v then
    throwErr s!"refineSym: σ{σ} := {v.pretty} carries a state marker (⊥/loan/borrow) — knowledge/state violation (§3.2)"
  modify (fun s => { s with
    env := s.env.map (fun kv => (kv.1, substSym σ v kv.2)),
    sctx := s.sctx.map (fun p => (p.1, substSym σ v p.2)),
    obligations := s.obligations.map (fun ob => { ob with owed := substSym σ v ob.owed }),
    -- A dependent call's captured/issued owed types may mention a caller σ (via
    -- an instantiated actual, §5.3); they live in group state, so a refinement
    -- must reach them too — the "refinement reaches all σ-bearing state"
    -- invariant (§3.2), of which §5.3 instantiation is the first consumer.
    groups := s.groups.map (fun g => { g with
      captured := g.captured.map (fun p => (p.1, substSym σ v p.2)),
      issued := g.issued.map (fun p => (p.1, substSym σ v p.2)),
      backSpec := g.backSpec.map (substSym σ v) }),
    retTyVal := s.retTyVal.map (substSym σ v),
    selfBack := s.selfBack.map (substSym σ v),
    -- The decreasing parameter's snapshot refines with everything else — this is
    -- how `match fuel { S(f2) => … }` makes the guard's comparison possible.
    selfRec := s.selfRec.map (fun sr => (sr.1, sr.2.map (fun d => (d.1, substSym σ v d.2)))) })

/-- **Generalize a stuck Bool spine** (§19) — the inverse of `refineSym`, and the
    two-layer principle at the machine level. When a match/`if` scrutinee reduces
    to a stuck spine `leb σ σp` (a neutral, not a bare σ), the ⇜ split cannot fire
    (it needs a substitutable σ). So NF the spine, mint a fresh `σb : Bool`, and
    `abstractInto` it across ALL σ-bearing state — the SAME targets `refineSym`
    reaches (Ω, sctx, obligations, groups, retTyVal, selfBack: the M10 invariant).
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
def generalizeStuck (fuel : Nat) (spine : Val) : M (Nat × Val) := do
  let sp := Val.nfV fuel spine
  let σb ← freshSym
  modify (fun s => { s with
    env := s.env.map (fun kv => (kv.1, abstractInto sp σb kv.2)),
    sctx := (σb, .const "Bool") :: s.sctx.map (fun p => (p.1, abstractInto sp σb p.2)),
    obligations := s.obligations.map (fun ob => { ob with owed := abstractInto sp σb ob.owed }),
    groups := s.groups.map (fun g => { g with
      captured := g.captured.map (fun p => (p.1, abstractInto sp σb p.2)),
      issued := g.issued.map (fun p => (p.1, abstractInto sp σb p.2)),
      backSpec := g.backSpec.map (abstractInto sp σb) }),
    retTyVal := s.retTyVal.map (abstractInto sp σb),
    selfBack := s.selfBack.map (abstractInto sp σb),
    selfRec := s.selfRec.map (fun sr => (sr.1, sr.2.map (fun d => (d.1, abstractInto sp σb d.2)))) })
  pure (σb, sp)

/-- **Refl-match — the solution transition** (§10). Matching against `Refl` at
    scrutinee type `Id A a b` unifies the endpoints: whnf both; if one is a
    substitutable σ not occurring on the other side, ⇜-refine it to the other,
    everywhere; if already equal, nothing; if BOTH are rigid, the match is
    STUCK — no unification beyond solution (no injectivity/conflict/cycle in the
    kernel; those are the fording library's job via j/k). -/
def reflUnify (fuel : Nat) (a b : Val) : M Unit := do
  let a' := Val.whnfV fuel a
  let b' := Val.whnfV fuel b
  if Val.convert fuel a' b' then pure ()                         -- endpoints already equal
  else match a', b' with
    | .sym σa, _ =>
      if b'.symIds.contains σa then
        throwErr s!"Refl: occurs check — endpoint σ{σa} occurs in the other endpoint ({b'.pretty})"
      else refineSym σa b'
    | _, .sym σb =>
      if a'.symIds.contains σb then
        throwErr s!"Refl: occurs check — endpoint σ{σb} occurs in the other endpoint ({a'.pretty})"
      else refineSym σb a'
    | _, _ =>
      throwErr s!"Refl: both endpoints are rigid ({a'.pretty} vs {b'.pretty}) — no solution by refinement; use j/k to eliminate the identity"

/-- **⇜ (comptime write / refinement)** — the doc's ⇜, signature parallel to
    `writeR`. Defined on the same place shapes (a variable under peels). The
    place must currently hold a symbolic value `sym σ`; the effect is global
    refinement `σ := refined` (Ω and sctx). Errors distinctively otherwise. -/
def writeC (place : Term) (refined : Val) : M Unit := do
  let pos ← placeToPosRaw place
  match ← getAtPos 1000 pos with
  | .sym σ => refineSym σ refined
  | v => throwErr s!"writeC (⇜): place holds {v.pretty}, expected a symbolic value (sym σ)"

/-! ## ⇝ (comptime read) and value typing (§4)

    `readC` is the ⇝ column: it evaluates a term in the borrow-free fragment.
    Discipline (to be a lemma later): it NEVER writes a slot. Reflection reads
    Ω only for snapshots — a variable reads its slot non-destructively, `*x`
    projects a borrow's payload — and `&mut`, assignment, and consumption
    through a loan are all outside the fragment (errors). Reflected pure terms
    are then normalized by `nfV`. -/

/-! Reflect a comptime term into a value, resolving Ω snapshot reads. Pure
    formers map to their `Val` counterparts; runtime-only constructs error. -/
mutual
  def reflectC : Term → M Val
    | .var x => do
      -- snapshot read (non-destructive) — but §2.1: every read-shaped rule
      -- excludes ⊥. A comptime read of a moved/uninitialized slot is a
      -- use-after-move; rejecting it here stops a silent ⊥ from riding into a
      -- pure value and surfacing layers later as an opaque untypeable ⊥ (the
      -- M21 `partIdxL n ⊥` etiology: reading the owned-consumed scrutinee).
      match ← lookupSlot x with
      | .bot => throwErr s!"readC (⇝): {x.name}#{x.id} holds ⊥ (use-after-move or uninitialized in a comptime read)"
      | v => pure v
    | .deref t => do
      match ← reflectC t with
      | .borrowM _ p => pure p                       -- *(borrowₘ ℓ v) ⇝ v
      | _ => throwErr "readC (⇝ *): dereferenced value is not a borrow"
    | .ctorApp n args => do pure (.ctor n (← reflectCList args))
    | .type => pure .type
    | .const c => pure (.const c)
    | .pvar k => pure (.pvar k)
    | .pi d c => do pure (.pi (← reflectC d) (← reflectC c))
    | .sigmaT d c => do pure (.sigmaT (← reflectC d) (← reflectC c))
    | .lam d b => do pure (.lam (← reflectC d) (← reflectC b))
    -- §5.4 exit-snapshot marker: `markExit` stamps a bare borrow-param `*v` in a
    -- return type as `@exit(*v)`; here it pins to that borrow's fresh σ_exit (the
    -- audit later defines it as the collapsed final payload). Unmarked bare `*v`
    -- and `old *v` both fall to the plain `.deref` read (the entry snapshot).
    | .app (.const "@exit") (.deref (.var v)) => do
      match (← get).exitSyms.lookup v.id with
      | some σ => pure (.sym σ)
      | none => reflectC (.deref (.var v))
    -- §5.4 `old *v`: the ENTRY snapshot σ (recorded at seed) — a non-consuming read
    -- of the entry value, in the return type OR the body (where `*v`'s live payload
    -- has since been mutated). Falls back to the live deref outside a borrow-param.
    | .app (.const "old") (.deref (.var v)) => do
      match (← get).entrySyms.lookup v.id with
      | some σ => pure (.sym σ)
      | none => reflectC (.deref (.var v))
    | .app f a => do pure (.app (← reflectC f) (← reflectC a))
    | .idT a b c => do pure (.idT (← reflectC a) (← reflectC b) (← reflectC c))
    | .unit => pure (.ctor "unit" [])
    | .letIn x rhs rest => do
      -- Pure `let` (§1.3): reflect the rhs and bind it as a fresh Ω entry, then
      -- reflect the body. The fresh pure entry is the comptime read's *only*
      -- sanctioned footprint on Ω (the doc's §1.3 "no side effects at the type
      -- level" is stated modulo exactly these let entries). Proof terms name
      -- intermediates constantly, so this is un-deferred here.
      let v ← reflectC rhs
      bindSlot x v
      reflectC rest
    -- ¶2.2's ⇝ column at the two new steps. The snapshot of an array place is the
    -- snapshot of the SEGMENT sitting there — exact, and needing no new constant.
    -- Read-only, as ⇝ must be: it merges a local copy to find the segment but never
    -- carves, so a place the program has not carved is honestly stuck here rather
    -- than silently reorganized inside a type.
    | .index t i _ => do
      let a := Val.mergeArrays (← reflectC t)
      navStep 1000 (.idx (Val.nfV 1000 (← reflectC i)) none) a
    | .range t lo (some cnt) _ _ _ => do
      let a := Val.mergeArrays (← reflectC t)
      navStep 1000 (.rng (Val.nfV 1000 (← reflectC lo)) (Val.nfV 1000 (← reflectC cnt)) none) a
    | .range _ _ none _ _ _ =>
      -- `a[lo ; ..]` reads its count off the extent map, which is STATE; ⇝ is the
      -- read-only projection and may not consult it. Write the count in a type.
      throwErr "readC (⇝): `a[lo ; ..]` has no comptime reading — its count is read off the extent map, which is state (§3.2)"
    | .assign _ _ _ => throwErr "readC (⇝): `:=` is excluded from the comptime fragment"
    | .borrow _ => throwErr "readC (⇝): `&mut` is not in the comptime fragment"
    | .seq _ _ => throwErr "readC (⇝): statement sequencing is not a comptime read"
    | .matchE _ _ _ => throwErr "readC (⇝): match not implemented in the comptime fragment this milestone"
    | .borrowT _ _ => throwErr "readC (⇝): borrow type `&mut (τ ↝ S)` is only valid at a telescope position"
    | .call _ _ => throwErr "readC (⇝): a call is not in the comptime fragment (its result is a fresh existential)"
  def reflectCList : List Term → M (List Val)
    | [] => pure []
    | t :: ts => do pure ((← reflectC t) :: (← reflectCList ts))
end

/-- ⇝: reflect, FOLD, then normalize. Ω is read-only throughout.

    The fold is ¶1.3's bridge, and putting it here rather than at the audit is the
    doc's own preference ("the latter is cleaner, since merge is then part of what
    *the snapshot of an array* means rather than a step the audit remembers to
    take"). A collapsed segment list becomes its `arrCat` spine — knowledge, never
    mentioning a marker — and `arrCat`'s ι then computes it back to a run when the
    bodies are runs, so a carved-and-rejoined array has the SAME snapshot as one that
    was never carved. A still-suspended one is left as the state form it is and is
    rejected at the one place that judges. -/
def readC (fuel : Nat) (t : Term) : M Val := do
  pure (Val.nfV fuel (Val.arrFoldDeep (← reflectC t)))

/-- ⇝ against extra bindings prepended to Ω — how a dependent call instantiates a
    callee telescope type (§5.3): the decl's parameter vars are bound to the
    caller's actuals in `extra`, so a `.var`-reference to an earlier parameter
    (the §5.2 convention) reflects to the value passed for it. The decl's types
    mention only decl vars, so `extra` shadows any id clash with caller slots.
    Env is restored afterward (the reflection's let-footprint is discarded). -/
def readCWith (fuel : Nat) (extra : Omega) (t : Term) : M Val := do
  let saved := (← get).env
  modify (fun s => { s with env := extra ++ s.env })
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
    | .pi d c => .pi (markExit borrowIds d) (markExit borrowIds c)
    | .sigmaT d c => .sigmaT (markExit borrowIds d) (markExit borrowIds c)
    | .lam d b => .lam (markExit borrowIds d) (markExit borrowIds b)
    | .idT a b c => .idT (markExit borrowIds a) (markExit borrowIds b) (markExit borrowIds c)
    | t => t
  termination_by t => sizeOf t
  def markExitList (borrowIds : List Nat) : List Term → List Term
    | [] => []
    | t :: ts => markExit borrowIds t :: markExitList borrowIds ts
  termination_by ts => sizeOf ts
end

/-- The telescope's borrow-parameter var ids (param `i` gets var id `i`). -/
def borrowParamIds (telescope : List (String × Term)) : List Nat :=
  telescope.enum.filterMap (fun (i, p) => match p.2 with | .borrowT _ _ => some i | _ => none)

/-- Build a call's fresh result value from the (instantiated) return type, and
    collect the loans it ISSUES (§6.1). Each `&mut (τ ↝ S)` position mints a
    fresh issued reborrow `borrowₘ ℓ σ` with `σ : τ` in `sctx` and owed type
    `S[s := σ]`; a `Pair`/`Σ` of results issues one loan PER borrow component
    (the multi-issued group — `nth2`); a non-borrow leaf is a plain fresh
    existential `σ` with no issued loan (the §5.3 wire).

    **Σ is DEPENDENT here** (M23): the tail's type may mention the components
    already built — that is the whole point of a pinned result (`Σ (r : List Nat)
    → Id (List Nat) r (drop i (old *v))`, split_off's ensures), and with declared
    backs removed it is a caller's only route to knowing anything about a returned
    value. `subs` carries the built components for the enclosing Σ binders,
    innermost first; a leaf substitutes them into its type before minting the σ.
    Substituting one at a time from the head is correct because `substPure 0`
    shifts the outer binders down as it goes. (Before M23 the tail was built
    independently, leaving a dangling `pvar` in the σ's sctx type, so the pin was
    unusable at the call site — `useIt(a, h)` failed with `argument (σ1) does not
    have its parameter type (Id σ0 (S Z))`.) -/
def buildResult (fuel : Nat) (inst : Omega) (subs : List Val) : Term → M (Val × List (Nat × Val))
  | .borrowT τ S => do
    let τVal := (subs.foldl (fun t v => Val.substPure 0 v t) (← readCWith fuel inst τ))
    let σ ← freshSym
    let ℓr ← freshLoan
    -- `S` binds the snapshot at pvar 0, so the enclosing Σ binders sit at 1+.
    let sVal ← readCWith fuel inst S
    let sVal := Val.substPure 0 (Val.sym σ) sVal
    let owedR := Val.nfV fuel (subs.foldl (fun t v => Val.substPure 0 v t) sVal)
    modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
    pure (.borrowM ℓr (.sym σ), [(ℓr, owedR)])
  | .sigmaT a b => do
    let (vA, issA) ← buildResult fuel inst subs a
    let (vB, issB) ← buildResult fuel inst (vA :: subs) b
    pure (.ctor "Pair" [vA, vB], issA ++ issB)
  | rt => do
    let retTy := (subs.foldl (fun t v => Val.substPure 0 v t) (← readCWith fuel inst rt))
    let σ ← freshSym
    modify (fun s => { s with sctx := (σ, retTy) :: s.sctx })
    pure (.sym σ, [])
  termination_by t => sizeOf t

/-! ## §8's snapshot-subterm guard — what makes a self-call admissible

    A call is checked against a signature alone (§5.3), so a self-call is admitted
    at the function's own declared return type. With declared backs removed that
    return type IS the postcondition, and admitting it unconditionally is the Hoare
    rule for recursion without its side condition — every false statement proves
    itself (`fn bad () -> Id Nat Z (S Z) { bad() }`). The side condition is
    structural decrease, and the checker being a symbolic interpreter makes it
    cheap to state: compare the actual against the parameter's *current snapshot*,
    which the enclosing matches have already refined. -/

/-- Is `act` a STRICT structural subterm of `cur`? Only constructor fields count as
    subterms — a fuel argument is a `Nat`/`List` snapshot, and the strictness is
    what forbids the same-fuel self-call. Both sides are snapshots (σ's and
    constructors), so structural equality is the right comparison: inside
    `match fuel { S(f2) => … }` the parameter reads `S σ_f2` and the actual `σ_f2`.
    Deliberately NOT extended to application spines: a `Le`-headed neutral has no
    well-founded subterm order we could appeal to. -/
partial def strictSubterm (act cur : Val) : Bool :=
  match cur with
  | .ctor _ args => args.any (fun a => a == act || strictSubterm act a)
  | _ => false

/-- The function names a body calls directly. -/
partial def calleeNames : Term → List String
  | .call f args => f :: (args.flatMap calleeNames)
  | .letIn _ a b => calleeNames a ++ calleeNames b
  | .assign a b c => calleeNames a ++ calleeNames b ++ calleeNames c
  | .seq a b => calleeNames a ++ calleeNames b
  | .ctorApp _ args => args.flatMap calleeNames
  | .borrow t | .deref t => calleeNames t
  | .matchE _ _ bs => bs.flatMap (fun b => calleeNames b.body)
  | .app f a => calleeNames f ++ calleeNames a
  | .lam d b | .pi d b | .sigmaT d b => calleeNames d ++ calleeNames b
  | .idT a b c => calleeNames a ++ calleeNames b ++ calleeNames c
  | _ => []

/-- Can `f` reach `target` through the table's call graph? Used to reject MUTUAL
    recursion, which the `[k]` guard does not cover: the guard is per-declaration,
    so `f → g → f` would let each admit the other's postcondition with nothing
    decreasing anywhere — the same hole through two doors. Rejected rather than
    supported; §8's measures are where a general story would live. -/
partial def reachesFn (table : List Decl) (seen : List String) (f target : String) : Bool :=
  if seen.contains f then false
  else match table.find? (fun d => d.name == f) with
    | none => false
    | some d =>
      let cs := calleeNames d.body
      cs.contains target || cs.any (fun c => reachesFn table (f :: seen) c target)

/-! Value typing (§4), the future audit's engine. `sym σ` is typed by `sctx`
    and conversion; a constructor value by the signature table, checking each
    field against its (dependently instantiated) type; a type former inhabits
    the universe. Cases no test forces error distinctively (M5 grows them). -/
mutual
  def hasType : Nat → Val → Val → M Bool
    | 0, _, _ => throwErr "hasType: out of fuel"
    | fuel + 1, v, ty => do
      -- Whnf the value first: a β-redex or stuck recursor (e.g. `eqb m a`,
      -- a λ-headed spine) must reduce to its weak head before we can type it.
      let v := Val.whnfV fuel v
      match v with
      | .sym σ =>
        match (← get).sctx.lookup σ with
        | some vty => pure (Val.convert fuel vty ty)
        | none => throwErr s!"hasType: σ{σ} has no type in sctx"
      -- ¶1.1's carved array node, and ruling 2's **extent-consistency invariant**,
      -- machine-asserted here: the segments' extents must sum to the array's own
      -- length index, and each body must hold its own extent's worth. This is the
      -- guard on the representation's one redundancy (extents are carried in the
      -- tree AND implied by the type), and it is exactly the conversion that
      -- premise (3)'s residue transition arranges to be definitional — ¶3.4's "this
      -- is the single place where the residue-transition decision pays out, and it
      -- pays out at every array-mutating function in the program".
      | .ctor "§segs" segs =>
        match Val.asArrayTy? (Val.whnfV fuel ty) with
        | none => pure false
        | some (n, t) => do
          let leaves ← extentMap fuel v
          if !(Val.convert fuel (sumExtents leaves) n) then pure false
          else leaves.allM (fun l => do
            if !Val.segOwned l.body then
              throwErr s!"hasType: array segment at [{l.base.pretty} ; {l.count.pretty}) holds {l.body.pretty} — a suspended array has no value of its type (§5.2)"
            else hasType fuel l.body (Val.arrayTy l.count t))
      | .ctor name args =>
        match Val.ctorSig name with
        | none => throwErr s!"hasType: unknown constructor '{name}'"
        | some sig =>
          match sig.fieldTypes (Val.whnfV fuel ty) with
          | none => pure false                       -- constructor does not inhabit this type
          | some ftys => checkFields fuel args ftys
      | .type => pure (Val.convert fuel ty .type)     -- Type : Type (type-in-type)
      | .pi _ _ => pure (Val.convert fuel ty .type)
      | .sigmaT _ _ => pure (Val.convert fuel ty .type)
      | .idT _ _ _ => pure (Val.convert fuel ty .type)   -- Id A a b : Type
      | .app _ _ =>
        -- A neutral spine. We synthesize a type only for the eliminator
        -- constants (§10 elaboration of `match` to eliminators): their result
        -- type is the motive applied to the target(s), and their premises are
        -- checked recursively. This is what lets the *library* fording terms
        -- (`natNoConf` via `j`, `botElim` on a derived ⊥) type-check as ordinary
        -- terms — no new machine rule, just the eliminators' typing.
        let (head, args) := Val.collectSpine v
        -- An eliminator may be OVER-applied (its result is a function further
        -- applied — `natRec … n` returning `P n = A → B`, then given the `A`):
        -- type the fixed part to its base result, then `synthSpine` the extras.
        let finish (baseTy : Val) (rest : List Val) (premises : Bool) : M Bool := do
          match ← synthSpine fuel baseTy rest with
          | some resTy => pure (Val.convert fuel ty resTy && premises)
          | none => pure false
        match head, args with
        | .const "botElim", t :: x :: rest =>            -- botElim T x : T   (x : ⊥)
          let xOk ← hasType fuel x (.const "Bot")
          finish t rest xOk
        | .const "j", a :: aa :: p :: d :: b :: pf :: rest =>   -- j A a P d b p : P b p
          let dOk ← hasType fuel d (Val.nfV fuel (.app (.app p aa) (.ctor "Refl" [])))
          let pOk ← hasType fuel pf (.idT a aa b)
          finish (Val.nfV fuel (.app (.app p b) pf)) rest (dOk && pOk)
        | .const "k", a :: aa :: p :: d :: pf :: rest =>        -- k A a P d p : P p
          let dOk ← hasType fuel d (Val.nfV fuel (.app p (.ctor "Refl" [])))
          let pOk ← hasType fuel pf (.idT a aa aa)
          finish (Val.nfV fuel (.app p pf)) rest (dOk && pOk)
        | .const "natRec", p :: z :: s :: n :: rest =>   -- natRec P z s n : P n
          let zOk ← hasType fuel z (Val.nfV fuel (.app p (.ctor "Z" [])))
          let sTy : Val := .pi (.const "Nat") (.pi (.app p (.pvar 0)) (.app p (.ctor "S" [.pvar 1])))
          let sOk ← hasType fuel s sTy
          let nOk ← hasType fuel n (.const "Nat")
          finish (Val.nfV fuel (.app p n)) rest (zOk && sOk && nOk)
        | .const "boolRec", p :: t :: f :: b :: rest =>  -- boolRec P t f b : P b
          let tOk ← hasType fuel t (Val.nfV fuel (.app p (.ctor "True" [])))
          let fOk ← hasType fuel f (Val.nfV fuel (.app p (.ctor "False" [])))
          let bOk ← hasType fuel b (.const "Bool")
          finish (Val.nfV fuel (.app p b)) rest (tOk && fOk && bOk)
        | .const "listRec", a :: p :: pn :: pc :: l :: rest =>  -- listRec A P pn pc l : P l
          let listA : Val := .app (.const "List") a
          let pnOk ← hasType fuel pn (Val.nfV fuel (.app p (.ctor "Nil" [])))
          let pcTy : Val := .pi a (.pi listA (.pi (.app p (.pvar 0)) (.app p (.ctor "Cons" [.pvar 2, .pvar 1]))))
          let pcOk ← hasType fuel pc pcTy
          let lOk ← hasType fuel l listA
          finish (Val.nfV fuel (.app p l)) rest (pnOk && pcOk && lOk)
        | .const "sigmaRec", a :: b :: p :: f :: s :: rest =>  -- sigmaRec A B P f s : P s
          -- Σ's parameters are a type `A` and a FAMILY `B : A → Type`, so unlike
          -- List's uniform parameter both premises cross binders and `B`/`P` must be
          -- shifted to be read there. (`shiftPure` is the identity on the pvar-free
          -- values every call site actually passes; correctness under an open motive
          -- is why it is written rather than assumed.)
          let sigTy : Val := .sigmaT a (.app (Val.shiftPure 1 0 b) (.pvar 0))
          let fTy : Val :=
            .pi a (.pi (.app (Val.shiftPure 1 0 b) (.pvar 0))
              (.app (Val.shiftPure 2 0 p) (.ctor "Pair" [.pvar 1, .pvar 0])))
          let fOk ← hasType fuel f fTy
          let sOk ← hasType fuel s sigTy
          finish (Val.nfV fuel (.app p s)) rest (fOk && sOk)
        -- ¶1.3's array basis. `arrCat`/`acons` are CHECKED rather than synthesized —
        -- their element type is recovered from the expected type, which is why
        -- neither carries a `T` argument (Pure.lean's deviation note). `aget` and
        -- `arrRec` synthesize, so they keep theirs.
        | .const "arrCat", [m, k, a, b] =>
          match Val.asArrayTy? (Val.whnfV fuel ty) with
          | none => pure false
          | some (n, t) =>
            if !(Val.convert fuel n (Val.kAdd m k)) then pure false
            else do
              let aOk ← hasType fuel a (Val.arrayTy m t)
              let bOk ← hasType fuel b (Val.arrayTy k t)
              pure (aOk && bOk)
        | .const "acons", [n, x, xs] =>
          match Val.asArrayTy? (Val.whnfV fuel ty) with
          | none => pure false
          | some (n', t) =>
            if !(Val.convert fuel n' (.ctor "S" [n])) then pure false
            else do
              let xOk ← hasType fuel x t
              let xsOk ← hasType fuel xs (Val.arrayTy n t)
              pure (xOk && xsOk)
        | .const "aget", tt :: n :: i :: a :: rest =>       -- aget T n i a : T
          let iOk ← hasType fuel i (.const "Nat")
          let aOk ← hasType fuel a (Val.arrayTy n tt)
          finish tt rest (iOk && aOk)
        | .const "arrRec", tt :: p :: pn :: pc :: n :: a :: rest =>   -- arrRec T P pn pc n a : P n a
          -- The cons view's recursor, so the pure library over arrays is written
          -- exactly like the one over lists (¶1.3). Its step crosses four binders,
          -- so `T` and `P` are shifted at each use — identity on the pvar-free values
          -- every call site passes, written out for correctness under an open motive
          -- (the same care `sigmaRec` takes, and for the same reason).
          let pnOk ← hasType fuel pn (Val.nfV fuel (.app (.app p Val.zero) (.ctor "Arr" [])))
          let pcTy : Val :=
            .pi (.const "Nat")
              (.pi (Val.shiftPure 1 0 tt)
                (.pi (Val.arrayTy (.pvar 1) (Val.shiftPure 2 0 tt))
                  (.pi (.app (.app (Val.shiftPure 3 0 p) (.pvar 2)) (.pvar 0))
                    (.app (.app (Val.shiftPure 4 0 p) (.ctor "S" [.pvar 3]))
                      (.app (.app (.app (.const "acons") (.pvar 3)) (.pvar 2)) (.pvar 1))))))
          let pcOk ← hasType fuel pc pcTy
          let nOk ← hasType fuel n (.const "Nat")
          let aOk ← hasType fuel a (Val.arrayTy n tt)
          finish (Val.nfV fuel (.app (.app p n) a)) rest (pnOk && pcOk && nOk && aOk)
        | .sym σ, args =>
          -- A bound function variable applied (`ih b c hab hbc`): synthesize by
          -- iterating Π-instantiation from its `sctx` type, checking each argument
          -- against the domain. This is ordinary application typing — what a
          -- surface lemma application (§15) or a proof reused under a binder needs.
          match (← get).sctx.lookup σ with
          | none => throwErr s!"hasType: σ{σ} (applied) has no type in sctx"
          | some hty =>
            match ← synthSpine fuel hty args with
            | some resTy => pure (Val.convert fuel ty resTy)
            | none => pure false
        | _, _ => throwErr s!"hasType: cannot type neutral {v.pretty}"
      | .lam d b =>
        -- λ against Π: check the domains convert, then the body under a fresh σ
        -- witness for the binder (a checking-time hypothesis added to `sctx`).
        -- This is what lets a Π-typed lemma (`le_refl : Π n. Le n n`) and the
        -- recursors' step arguments — both λs — type-check. No arrow of its own;
        -- it is the elaboration of dependent elimination (§10/§11).
        match Val.whnfV fuel ty with
        | .pi d' c =>
          if Val.convert fuel d d' then do
            let σ ← freshSym
            modify (fun st => { st with sctx := (σ, d') :: st.sctx })
            hasType fuel (Val.substPure 0 (.sym σ) b) (Val.substPure 0 (.sym σ) c)
          else pure false
        | _ => pure false
      | _ => throwErr s!"hasType: cannot type value {v.pretty} (λ/neutral typing deferred to M5)"
  termination_by fuel _ _ => (fuel, 0, 0)
  /-- Synthesize the result type of applying a value of type `hty` to `args`:
      each argument's domain (a Π) is checked, and the codomain is instantiated at
      the argument. `none` if an argument mistypes or a non-Π is applied. -/
  def synthSpine : Nat → Val → List Val → M (Option Val)
    | _, hty, [] => pure (some hty)
    | fuel, hty, a :: rest => do
      match Val.whnfV fuel hty with
      | .pi dom cod =>
        if ← hasType fuel a dom then synthSpine fuel (Val.substPure 0 a cod) rest
        else pure none
      | _ => pure none                                 -- applied a non-function
  termination_by fuel _ args => (fuel, 2, args.length)
  /-- Check a constructor's fields against its field-type telescope, threading
      each checked field value into the remaining (dependent) field types. -/
  def checkFields : Nat → List Val → List Val → M Bool
    | _, [], [] => pure true
    | fuel, v :: vs, ty :: tys => do
      if ← hasType fuel v ty then
        checkFields fuel vs (tys.map (Val.substPure 0 v))
      else pure false
    | _, _, _ => pure false                          -- arity mismatch
  termination_by fuel _ tys => (fuel, 1, tys.length)
end

/-! ## Loan groups (§6.1): the ending cascade

    A call mints a `Group`. Ending a captured loan does not end it alone — it
    triggers the whole group's end: **every issued borrow ends first** (locate
    it, audit its payload against its owed type, surrender it), **then the
    group ends atomically**, releasing each captured loan. A constrained
    (identity-wire) group releases its one captured loan with the single
    surrendered payload; otherwise each captured loan gets a fresh, unconstrained
    existential at its owed type. The ordering *is* the soundness argument
    (§6.1): a captured owner cannot recover while an issued borrow lives. -/

/-- End one issued borrow: locate it in Ω, audit its (collapsed) payload against
    its owed type, kill it, and return the surrendered payload. -/
def endIssued (fuel : Nat) (ℓ : Nat) (owed : Val) : M Val := do
  match (← getEnv).findSome? (fun kv => findBorrowPayload ℓ kv.2) with
  | none => throwErr s!"group end: issued borrow ℓ{ℓ} is not locatable in Ω (cannot end the group)"
  | some payload => do
    match payload with
    | .bot => throwErr s!"group end: issued borrow ℓ{ℓ} holds a hole (⊥) — nothing surrendered"
    | _ =>
      if ← hasType fuel payload owed then do
        setEnv ((← getEnv).map (fun kv => (kv.1, replaceBorrowWithBot ℓ kv.2)))   -- kill
        pure payload
      else
        throwErr s!"group end: issued borrow ℓ{ℓ}'s payload ({payload.pretty}) does not have its owed type ({owed.pretty})"

/-- Release one captured loan: plug `v` where its marker sits. -/
def releaseCaptured (ℓ : Nat) (v : Val) : M Unit := sendPayloadToLoan ℓ v

/-- End a whole loan group (§6.1): issued borrows first, then captured atomically. -/
def endGroup (fuel : Nat) (grp : Group) : M Unit := do
  -- 1. end every issued borrow, collecting surrendered payloads (in order)
  let surrendered ← grp.issued.mapM (fun (ℓ, owed) => endIssued fuel ℓ owed)
  -- 2. remove the group from the table (by its ρ id)
  modify (fun s => { s with groups := s.groups.filter (fun g => g.id != grp.id) })
  -- 3. release captured loans atomically
  match grp.backSpec, grp.constrained, grp.captured, surrendered with
  | some f, _, [(ℓc, _)], _ =>
    -- §6.2 spec end: the captured release is the declared backward function
    -- applied to the surrendered values (in issued order) — the COMPUTED value,
    -- not a fresh existential. Precision recovered soundly (the spec was checked
    -- against the body at the callee's return).
    releaseCaptured ℓc (Val.nfV fuel (Val.rebuildSpine f surrendered))
  | none, true, [(ℓc, _)], [p] => releaseCaptured ℓc p    -- test-only identity wire (harness)
  | _, _, _, _ =>
    grp.captured.forM (fun (ℓc, owed) => do
      match grp.exitRelease.lookup ℓc with
      | some σ' => releaseCaptured ℓc (.sym σ')            -- §5.4: pinned exit-snapshot release (σ' already in sctx)
      | none => do                                        -- opaque: fresh existential each
        let σ ← freshSym
        modify (fun s => { s with sctx := (σ, owed) :: s.sctx })
        releaseCaptured ℓc (.sym σ))

/-- **End loan** ℓ (§6.1-aware). If ℓ is a group's captured loan, ending it
    ends the whole group (issued first, then captured). Otherwise it is an
    ordinary loan: kill its borrow and plug the payload home (§2.2 End-Mut). -/
def endLoan (fuel : Nat) (ℓ : Nat) : M Unit := do
  match (← get).groups.find? (fun g => g.captured.any (·.1 == ℓ)) with
  | some grp => endGroup fuel grp
  | none => sendPayloadToLoan ℓ (← killBorrowInΩ ℓ)

/-- **Scope-aware release at call return** (EXECUTING mode only, ledger G5 probe). -/
partial def releaseFrameLoans (fuel : Nat) (offset : Nat) (keep : List Nat) : M Unit := do
  match fuel with
  | 0 => pure ()
  | f + 1 => do
    let env ← getEnv
    let held := env.filterMap (fun kv =>
      if kv.1.id ≥ offset then
        match kv.2 with
        | .borrowM ℓ _ => if keep.contains ℓ then none else some ℓ
        | _ => none
      else none)
    match held.head? with
    | none => pure ()
    | some ℓ => do endLoan fuel ℓ; releaseFrameLoans f offset keep

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
def carveObligation (fuel : Nat) (b m lo cnt : Val) : Val :=
  -- LEAF-RELATIVE wherever the leaf-relative offset is already known, which is both
  -- cases the design's programs actually produce. `Le` computes by double `natRec`,
  -- so `Le (add b cnt) (add b m)` is STUCK on a symbolic `b` and never converts with
  -- the `Le cnt m` a program can supply — stating the obligation absolutely would
  -- demand evidence about the leaf's absolute end that nothing can produce. Premise
  -- (3)'s own logic says the offsets are leaf-relative; premise (2) should be too.
  if Val.convert fuel lo b then Val.kLe cnt m                       -- base-aligned: lo' = Z
  else if Val.convert fuel b Val.zero then Val.kLe (rangeEnd fuel lo cnt) m  -- leaf at the node base
  else
    let low := Val.kLe b lo
    let high := Val.kLe (rangeEnd fuel lo cnt) (Val.kAdd b m)
    .sigmaT low (Val.shiftPure 1 0 high)

/-- Is the cited evidence good for this leaf? With no evidence cited we try the
    canonical inhabitant of ⊤ — ¶3.2's supply route 1, "conversion alone", which is
    what makes every literal-indexed access free. Route 3 is that there is no route
    3: no inference, no decision procedure, no `omega`. -/
def carveEvidenceOk (fuel : Nat) (ev : Option Val) (oblig : Val) : M Bool := do
  match ev with
  | some e => hasType fuel e oblig
  | none =>
    let star : Val := .ctor "unit" []
    if ← hasType fuel star oblig then pure true
    else hasType fuel (.ctor "Pair" [star, star]) oblig

/-- Split an owned body into the three pieces the carve's extents name. Only the two
    forms ¶3.2 defines the split on: a literal run (split positionally, which needs
    concrete extents — one cannot cut a run at an offset one does not know) and a σ
    (refined to the `arrCat` spine, which is ordinary ⇜, marker-free, and true of the
    value timelessly). Returns the three bodies. -/
def carveBody (fuel : Nat) (body : Val) (loN cntN restN : Nat) (lo' cnt rest : Val)
    : M (Val × Val × Val) := do
  match body with
  | .ctor "Arr" vs =>
    pure (.ctor "Arr" (vs.take loN),
          .ctor "Arr" ((vs.drop loN).take cntN),
          .ctor "Arr" (vs.drop (loN + cntN)))
  | .sym σ =>
    match (← get).sctx.lookup σ with
    | none => throwErr s!"carve: σ{σ} has no type in sctx"
    | some τ =>
      match Val.asArrayTy? (Val.whnfV fuel τ) with
      | none => throwErr s!"carve: σ{σ} is not of array type ({τ.pretty})"
      | some (_, t) => do
        let mk : Val → M Val := fun c => do
          let s ← freshSym
          modify (fun st => { st with sctx := (s, Val.arrayTy c t) :: st.sctx })
          pure (.sym s)
        let b₁ ← mk lo'; let b₂ ← mk cnt; let b₃ ← mk rest
        -- The spine is built over the NONEMPTY pieces only. A zero-extent σ would be
        -- a name for the empty array that nothing can ever compute away (`arrCat`'s
        -- ι absorbs an empty RUN, not an empty σ), and it would leave every rejoin
        -- conversion needing a lemma. `restN`/`loN` are meaningful only in the
        -- concrete case; the symbolic test is `convert c Z`, below.
        let isZ : Val → Bool := fun c => Val.convert fuel c Val.zero
        let spine :=
          if isZ lo' then (if isZ rest then b₂ else Val.arrCatS cnt rest b₂ b₃)
          else if isZ rest then Val.arrCatS lo' cnt b₁ b₂
          else Val.arrCatS lo' (Val.kAdd cnt rest) b₁ (Val.arrCatS cnt rest b₂ b₃)
        refineSym σ spine
        pure (b₁, b₂, b₃)
  | b =>
    throwErr s!"carve: leaf body {b.pretty} cannot be split (¶3.2 defines the split on an owned run or a σ; a compound neutral is stuck)"

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
  match body with
  | .ctor "Arr" [_] => pure body
  | .sym σ =>
    match (← get).sctx.lookup σ with
    | none => throwErr s!"a[i]: σ{σ} has no type in sctx"
    | some τ =>
      match Val.asArrayTy? (Val.whnfV fuel τ) with
      | none => throwErr s!"a[i]: σ{σ} is not of array type ({τ.pretty})"
      | some (_, t) => do
        let e ← freshSym
        modify (fun st => { st with sctx := (e, t) :: st.sctx })
        refineSym σ (.ctor "Arr" [.sym e])
        pure (.ctor "Arr" [.sym e])
  | b => throwErr s!"a[i]: the one-slot segment holds {b.pretty}, which is not a single-element run"

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
partial def carveAt (fuel : Nat) (pos : Pos) (lo cnt : Val) (given : Option Val)
    (ev : Option Val) (eqc : Option Val) (isIdx : Bool) : M Unit := do
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
  if (← get).executing && !isIdx && Val.convert fuel cnt Val.zero then do
    setAtPos fuel pos (Val.mergeArrays (← getAtPos fuel pos))
    let leaves ← extentMap fuel (← getAtPos fuel pos)
    if (leaves.any (fun l => Val.convert fuel l.base lo && Val.convert fuel l.count Val.zero))
    then pure ()
    else do
      let segs := leaves.map (fun l => Val.segNode l.count l.body)
      let rec place (acc : List Val) (bse : Val) : List Val → List Val
        | [] => acc ++ [Val.segNode Val.zero (.ctor "Arr" [])]
        | sg :: rest =>
          if Val.convert fuel bse lo then acc ++ [Val.segNode Val.zero (.ctor "Arr" [])] ++ (sg :: rest)
          else match Val.asSeg? sg with
            | some (c, _) => place (acc ++ [sg]) (Val.kAdd bse c) rest
            | none => acc ++ (sg :: rest)
      setAtPos fuel pos (.ctor "§segs" (place [] Val.zero segs))
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
    let aligned := leaves.filter (fun l => Val.convert fuel l.base lo)
    let pick :=
      (aligned.find? (fun l => Val.convert fuel l.count (Val.kAdd cnt rest)))
        <|> (aligned.find? (fun l => !(Val.convert fuel l.count Val.zero)))
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
      if Val.convert fuel l.count (Val.kAdd cnt rest) then pure ()
      else
        let owed := Val.idT (.const "Nat") l.count (Val.kAdd cnt rest)
        match eqc with
        | some q =>
          if ← hasType fuel q owed then reflUnify fuel l.count (Val.kAdd cnt rest)
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
  -- `le_refl`, so demanding evidence would be friction with no content. This is the
  -- asymmetry ¶3.4 says IS the design: an exhaustive split costs ONE proof, not two.
  let degenerate := leaves.find? (fun l => Val.convert fuel l.base lo && Val.convert fuel l.count cnt)
  -- Premise (2): form each candidate leaf's obligation and check the evidence against
  -- it; the first that types SELECTS the leaf — "the evidence's type is the selector".
  -- Deterministic without a tie-break, because leaves are disjoint. A degenerate
  -- request needs no evidence at all: its two `Le`s are `le_refl`, so demanding a term
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
          if Val.convert fuel lo l.base then pure Val.zero
          else if Val.convert fuel l.base Val.zero then pure lo
          else do
            let d ← freshSym
            modify (fun st => { st with sctx := (d, .const "Nat") :: st.sctx })
            reflUnify fuel lo (Val.kAdd l.base (.sym d))
            pure (.sym d)
        -- Then the residue. Concrete extents COMPUTE (¶3.3's trace: "n = 3 concrete,
        -- both sides compute — nothing refined"), and the arithmetic is meta-level on
        -- numerals, never a `sub` in the object language. Symbolic extents mint `rest`
        -- and solve `m ≡ add lo' (add cnt rest)` — the equation ¶3.2 reaches with
        -- `le_split` twice plus `add_cancel_l`, asserted here in its cancelled form
        -- because the checker unpacks the witnesses itself and no program term ever
        -- projects them.
        let lo'N := Val.natOfVal? (Val.nfV fuel lo')
        let cntN := Val.natOfVal? (Val.nfV fuel cnt)
        let mN := Val.natOfVal? (Val.nfV fuel l.count)
        let rest ←
          match given, lo'N, cntN, mN with
          -- ROUTE (a), step two: premise (3)'s residue is the term the program wrote.
          -- Its equation was already solved above, so nothing is minted and nothing is
          -- left nameless.
          | some r, _, _, _ => pure r
          | none, some a, some c, some m =>
            if a + c ≤ m then pure (Val.valOfNat (m - a - c))
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
            (do reflUnify fuel l.count (Val.kAdd lo' (Val.kAdd cnt (.sym r)))) <|>
              throwErr s!"carve: premise (3) is stuck — the leaf's extent ({l.count.pretty}) is a compound neutral, not a flexible σ, so `m ≡ add lo' (add cnt rest)` has no solution by refinement. Take the length as a telescope PARAMETER rather than an expression (¶3.2, ¶8.4's rigid-length restriction)"
            pure (.sym r)
        -- The bodies. Positional on a run (which needs concrete extents — one cannot
        -- cut a literal at an offset one does not know), ⇜ on a σ.
        let restN := Val.natOfVal? (Val.nfV fuel rest)
        let (b₁, b₂, b₃) ←
          match body, lo'N, cntN, restN with
          | .ctor "Arr" _, none, _, _ =>
            throwErr s!"carve: cannot split the literal run {body.pretty} at a symbolic offset"
          | .ctor "Arr" _, _, none, _ =>
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
        let isZ : Val → Bool := fun c => Val.convert fuel c Val.zero
        let ex := (← get).executing
        let pieces := (if isZ lo' && !ex then [] else [Val.segNode lo' b₁])
                   ++ [Val.segNode cnt b₂]
                   ++ (if isZ rest && !ex then [] else [Val.segNode rest b₃])
        let node' ← getAtPos fuel pos                    -- re-read: (3) may have refined
        match node' with
        | .ctor "§segs" segs => do
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
def restOfLeaf (fuel : Nat) (pos : Pos) (lo : Val) : M Val := do
  let node := Val.mergeArrays (← getAtPos fuel pos)
  let leaves ← extentMap fuel node
  match leaves.find? (fun l => Val.convert fuel l.base lo) with
  | some l => pure l.count
  | none =>
    let loN := Val.natOfVal? (Val.nfV fuel lo)
    let hit := leaves.findSome? (fun l =>
      match loN, Val.natOfVal? (Val.nfV fuel l.base), Val.natOfVal? (Val.nfV fuel l.count) with
      | some i, some b, some m => if b ≤ i && i < b + m then some (Val.valOfNat (b + m - i)) else none
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
    carveAt fuel p iv (Val.nat 1) none evv none true
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
  match (← getEnv).find? (fun kv => kv.1.id == root.id) with
  | some kv => setSlot root (Val.mergeArrays kv.2)
  | none => pure ()

/-- **⇐ (write)** — the fill-only write arrow, defined only on places. Its
    premise is a vacant (⊥) target; when the target is live a **drop** is
    forced first (§2.3), vacating it, then the value drops in. We vacate the
    slot *before* dropping so drop's Ω-scans never see a stale copy of the
    displaced value. -/
def writeR (fuel : Nat) (place : Term) (newval : Val) : M Unit := do
  let pos ← placeToPos fuel place
  let old ← getAtPos fuel pos
  match old with
  | .bot => do setAtPos fuel pos newval; mergeRoot pos.root          -- fill
  | _ => do
    setAtPos fuel pos .bot                         -- vacate first (no stale copy in Ω scans)
    drop fuel old                                  -- drop the displaced value
    setAtPos fuel pos newval                       -- fill
    mergeRoot pos.root                             -- rejoin is merge (¶3.3)

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
    match (← getEnv).find? (fun kv => kv.1.id == x.id) with
    | some ⟨_, .loanM ℓ⟩ => do endLoan fuel ℓ; collapseCDerefs fuel (.var x)
    | _ => pure ()
  | .deref inner => do
    collapseCDerefs fuel inner
    match placeOf? (.deref inner) with
    | none => pure ()
    | some (root, d) =>
      match (← getEnv).find? (fun kv => kv.1.id == root.id) with
      | none => pure ()
      | some kv =>
        match peek? d kv.2 with
        | some (.loanM ℓ) => do endLoan fuel ℓ; collapseCDerefs fuel (.deref inner)
        | _ => pure ()
  | .app f a => do collapseCDerefs fuel f; collapseCDerefs fuel a
  | .ctorApp _ args => args.forM (collapseCDerefs fuel)
  | .idT a b c => do collapseCDerefs fuel a; collapseCDerefs fuel b; collapseCDerefs fuel c
  | .lam d b => do collapseCDerefs fuel d; collapseCDerefs fuel b
  | .pi d b => do collapseCDerefs fuel d; collapseCDerefs fuel b
  | .sigmaT d b => do collapseCDerefs fuel d; collapseCDerefs fuel b
  | .letIn _ rhs rest => do collapseCDerefs fuel rhs; collapseCDerefs fuel rest
  | _ => pure ()

/-- Find the branch whose constructor name matches `name`. -/
def findBranch (branches : List Branch) (name : String) : Option Branch :=
  branches.find? (fun b => b.ctor == name)

/-- Bind constructor fields to fresh binder entries (owned mode: the fields
    move in as owned values). Errors on arity mismatch. -/
def bindFields : List Var → List Val → M Unit
  | [], [] => pure ()
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
    if br.binders.length != fields.length then
      throwErr "match: constructor arity mismatch (borrow mode)"
    let ℓs ← fields.mapM (fun _ => freshLoan)
    setSlot scrut (.borrowM ℓ (.ctor name (ℓs.map Val.loanM)))   -- suspend the parent
    bindBorrowFields br.binders ℓs fields
    bindEqnRefl eqn
    pure br.body

/-! Shift every runtime `Var` id in a term (and its match binders) up by `d`.
    Used to inline a callee body under a fresh id window in executing mode
    (§9 differential), so its frame cannot collide with the caller's ids. Pure
    formers hold no runtime vars (the pool's types are closed), so they are
    left as-is. -/
mutual
  def shiftVars (d : Nat) : Term → Term
    | .var x => .var ⟨x.id + d, x.name⟩
    | .letIn x rhs rest => .letIn ⟨x.id + d, x.name⟩ (shiftVars d rhs) (shiftVars d rest)
    | .assign p e rest => .assign (shiftVars d p) (shiftVars d e) (shiftVars d rest)
    | .ctorApp n args => .ctorApp n (shiftVarsList d args)
    | .borrow t => .borrow (shiftVars d t)
    | .deref t => .deref (shiftVars d t)
    -- The `Option` is matched inline rather than `.map`ped: a recursive call under
    -- `Option.map` is opaque to the structural-recursion checker.
    | .index t i ev => .index (shiftVars d t) (shiftVars d i)
        (match ev with | some e => some (shiftVars d e) | none => none)
    | .range t lo cnt rest ev eqc =>
      .range (shiftVars d t) (shiftVars d lo)
        (match cnt with | some c => some (shiftVars d c) | none => none)
        (match rest with | some r => some (shiftVars d r) | none => none)
        (match ev with | some e => some (shiftVars d e) | none => none)
        (match eqc with | some e => some (shiftVars d e) | none => none)
    | .matchE scrut eqn brs =>
      .matchE ⟨scrut.id + d, scrut.name⟩ (eqn.map (fun v => ⟨v.id + d, v.name⟩)) (shiftBranches d brs)
    | .seq a b => .seq (shiftVars d a) (shiftVars d b)
    | .call f args => .call f (shiftVarsList d args)
    -- Pure formers can EMBED runtime vars (a §19 body computes `leb (nth j (*v))`
    -- — a pure spine over the runtime `v`, `i`, `g`). Their `.var` leaves must
    -- shift with the executing-mode frame too; `.pvar`/`.type`/`.const` (no
    -- runtime vars) stay in the catch-all.
    | .app f a => .app (shiftVars d f) (shiftVars d a)
    | .idT a b c => .idT (shiftVars d a) (shiftVars d b) (shiftVars d c)
    | .pi a b => .pi (shiftVars d a) (shiftVars d b)
    | .lam a b => .lam (shiftVars d a) (shiftVars d b)
    | .sigmaT a b => .sigmaT (shiftVars d a) (shiftVars d b)
    | t => t                                            -- unit / pure formers: no runtime vars
  termination_by t => sizeOf t
  def shiftVarsList (d : Nat) : List Term → List Term
    | [] => []
    | t :: ts => shiftVars d t :: shiftVarsList d ts
  termination_by ts => sizeOf ts
  def shiftBranches (d : Nat) : List Branch → List Branch
    | [] => []
    | (.mk c bs body) :: rest => .mk c (bs.map (fun v => ⟨v.id + d, v.name⟩)) (shiftVars d body) :: shiftBranches d rest
  termination_by bs => sizeOf bs
end

/-! ## ⇒ (read): the move arrow

    `readR` evaluates a term to a value with move semantics. Fuel decreases on
    every recursive call (including the End-Mut retry and the constructor-args
    loop), so the machine is total; the list helper `readArgs` keeps the
    constructor case structural. -/
mutual
  def readR : Nat → Term → M Val
    | 0, _ => throwErr "readR: out of fuel"
    | fuel + 1, t =>
      match t with
      | .var x => do
        match ← lookupSlot x with
        | .bot => throwErr s!"readR: {x.name}#{x.id} holds ⊥ (use-after-move or uninitialized)"
        | v =>
          -- A value with a loan marker in owned position cannot be moved: end
          -- it first (End-Mut), then retry. This is the lazy chain-collapse —
          -- a top-level loanM (§2.2/§2.5) and a Cons of field-loans left by a
          -- borrow-mode match (§3.3) are the same case.
          match firstLoanMarker v with
          | some ℓ => do endLoan fuel ℓ; readR fuel (.var x)
          | none =>
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
      | .letIn x rhs rest => do
        let v ← readR fuel rhs
        bindSlot x v
        readR fuel rest
      | .assign place rhs rest => do
        let v ← readR fuel rhs                           -- RHS by ⇒ first (§2.5 ordering)
        writeR fuel place v                              -- target by ⇐
        readR fuel rest
      | .matchE scrut eqn branches => do
        -- Mode is chosen by what the scrutinee's slot holds, after the usual
        -- lazy reorganization. Both retries decrease fuel.
        match ← lookupSlot scrut with
        | .bot => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} holds ⊥ (use-after-move)"
        | .borrowM ℓ payload =>
          match payload with
          | .ctor name fields => do readR fuel (← borrowSelect scrut eqn branches ℓ name fields)
          | .loanM ℓ' => do endLoan fuel ℓ'; readR fuel (.matchE scrut eqn branches)  -- reborrowed payload: end, retry
          | .bot => throwErr s!"match: matching through a hole (⊥) at {scrut.name}#{scrut.id}"
          | .sym _ => throwErr s!"match: symbolic scrutinee {scrut.name}#{scrut.id} in expression position — only a statement-position match may split (use the explore driver)"
          | .borrowM _ _ => throwErr s!"match: scrutinee payload is a nested borrow (unsupported in §3)"
          | _ => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} payload is not a constructor"
        | v =>
          match firstLoanMarker v with
          | some ℓ => do endLoan fuel ℓ; readR fuel (.matchE scrut eqn branches)  -- suspended owner: end, retry
          | none =>
            match v with
            | .ctor name fields => do readR fuel (← ownedSelect scrut eqn branches name fields)
            | .sym _ => throwErr s!"match: symbolic scrutinee {scrut.name}#{scrut.id} in expression position — only a statement-position match may split (use the explore driver)"
            | _ => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} is not a constructor value"
      | .seq e rest => do
        let _ ← readR fuel e                             -- evaluate for effect, discard
        readR fuel rest
      | .call f args => do
        match (← get).decls.find? (fun d => d.name == f) with
        | none => throwErr s!"call: unknown function '{f}'"
        | some decl =>
          if (← get).executing then do
            -- EXECUTING (§9 differential): run the callee's ACTUAL body under a
            -- fresh var-id window, so shared borrows propagate naturally.
            let offset ← (do let s ← get; set { s with nextFrame := s.nextFrame + 128 }; pure s.nextFrame)
            bindActuals fuel offset 0 decl.telescope args
            let res ← readR fuel (shiftVars offset decl.body)
            releaseFrameLoans fuel offset res.loanIds
            pure res
          else do
            -- CHECKING (§5.3/§6.1): signature only, mint one loan group. The
            -- instantiation `inst` (decl var → actual, §5.3) instantiates the
            -- return and owed types at the actuals this call was given.
            let (captured, inst) ← processArgs fuel 0 [] decl.telescope args
            -- §8's snapshot-subterm guard. Signature-only checking means a self-call
            -- is admitted at this function's own declared return type — its
            -- POSTCONDITION, once declared backs are gone — so it needs the side
            -- condition every recursion rule has: something strictly decreases.
            -- Checked here, after `processArgs`, because the actual's VALUE is what
            -- the comparison needs and `inst` is where it lands.
            match (← get).selfRec with
            | some (selfName, dk) =>
              if f == selfName then
                match dk with
                | none =>
                  throwErr s!"recursion: '{f}' calls itself but declares no decreasing argument ([k], §1.2) — a self-call admitted at its own return type with nothing decreasing proves any postcondition"
                | some (k, cur) =>
                  match inst.find? (fun kv => kv.1.id == k) with
                  | none => throwErr s!"recursion: '{f}' declares decreasing argument [{k}] but the call passes no such argument"
                  | some (_, act) =>
                    -- Unwrap a borrow on both sides: what decreases is the payload
                    -- snapshot, not the loan wrapping it.
                    let peel : Val → Val := fun v => match v with | .borrowM _ p => p | v => v
                    let a := Val.nfV fuel (peel act)
                    let c := Val.nfV fuel (peel cur)
                    if strictSubterm a c then pure ()
                    else throwErr s!"recursion: self-call's argument [{k}] ({a.pretty}) is not a strict structural predecessor of the parameter's snapshot ({c.pretty})"
              else if reachesFn (← get).decls [] f selfName then
                throwErr s!"recursion: mutual recursion ('{selfName}' → '{f}' → … → '{selfName}') is not supported — the [k] guard is per-declaration (§8)"
              else pure ()
            | none => pure ()
            -- Build the result and the loans it issues from the return type (a
            -- single borrow, a Pair/Σ of borrows for a multi-issued group, or a
            -- plain existential wire). One group ties captured to issued. The
            -- `constrained` flag stays false in real checking — inferring it is
            -- unsound (`through` vs `advance` share a signature); the test-only
            -- `forceConstrained` flag reintroduces the bug for harness validation.
            -- §5.4 caller-side σ-sharing: mint one σ' per captured borrow (typed at
            -- its owed type). The retType's bare `*v` (marked `@exit`) reflects to
            -- σ', and the group PINS that captured loan's release to σ' — so the
            -- returned evidence and the recovered owner are the same σ'. `old *v`
            -- clears through to the actual entry payload (entrySyms emptied for the
            -- reflect, so callee/caller var-id collisions can't shadow it). Empty
            -- when there are no borrow args (a no-op) and dead under a `back` (which
            -- releases via the spec instead of the pinned σ').
            let borrowIds := borrowParamIds decl.telescope
            let sigmas ← (captured.map (·.2)).mapM (fun owed => do
              let σ ← freshSym
              modify (fun s => { s with sctx := (σ, owed) :: s.sctx })
              pure σ)
            let exitMap := borrowIds.zip sigmas
            let exitRel := (captured.map (·.1)).zip sigmas
            let savedE := (← get).exitSyms
            let savedO := (← get).entrySyms
            modify (fun s => { s with exitSyms := exitMap, entrySyms := [] })
            let (resultVal, issued) ← buildResult fuel inst [] (markExit borrowIds decl.retType)
            modify (fun s => { s with exitSyms := savedE, entrySyms := savedO })
            let ρ ← freshGroup
            let fc := (← get).forceConstrained
            let cons := fc && captured.length == 1 && issued.length == 1
            -- §6.2: reflect the DECLARED backward spec (if any) at the actuals, so
            -- the group can compute the captured release from the surrendered
            -- values instead of a fresh existential.
            let backV ← match decl.back with
              | some b => do pure (some (← readCWith fuel inst b))
              | none => pure none
            let grp : Group := { id := ρ, captured := captured, issued := issued, constrained := cons, backSpec := backV, exitRelease := exitRel }
            modify (fun s => { s with groups := grp :: s.groups })
            pure resultVal
      | .unit => pure (.ctor "unit" [])
      -- The pure lift (§1.3): on the borrow-free fragment ⇒ coincides with ⇝ up
      -- to variable consumption. A comptime-only former (a proof term — an
      -- eliminator application, a Π-typed λ, `Id A a b`, a type) is an
      -- unrestricted value, so ⇒ delegates to ⇝ (`readC`) and hands back the
      -- result as an ordinary runtime datum: it can be stored in a constructor
      -- field, passed to a call, or returned. (Snapshot reads are
      -- non-destructive; that is the "up to consumption" — these values are
      -- copyable/erasable, so nothing is moved out.) `Refl` needs no lift (it is
      -- an ordinary `ctorApp`, handled above); `borrowT` is a telescope-position
      -- type, never a value.
      -- Before projecting, demand-end the loans parked at the places this read
      -- goes through (§5.2's "proper payload" premise; see `collapseCDerefs`).
      -- Only on the lift, where a body reads live places — `readC` proper is used
      -- on types/specs too and stays the read-only projection it is documented as.
      | .type => readC fuel t
      | .const _ => readC fuel t
      | .pvar _ => readC fuel t
      | .pi _ _ => readC fuel t
      | .sigmaT _ _ => readC fuel t
      | .lam _ _ => do collapseCDerefs fuel t; readC fuel t
      | .app _ _ => do collapseCDerefs fuel t; readC fuel t
      | .idT _ _ _ => do collapseCDerefs fuel t; readC fuel t
      -- ¶2.2's ⇒ column at the two new steps, and the regularity §1.3 asks the
      -- reader to notice: each behaves the way the corresponding column behaves at
      -- `*`. `t[i]` moves the element out (a hole in the slot) or copies it under
      -- §2.1's index-kind refinement; `t[lo ; cnt]` moves the whole run out, leaving
      -- a hole of known extent whose one legal successor is the ⇐-refill — §2.4's
      -- take-and-refill generalized from "the payload of a borrow" to "a run of an
      -- array", which is how a rotation or a memmove is written without a copy.
      | .index _ _ _ | .range _ _ _ _ _ _ => do
        let pos ← placeToPos fuel t
        match ← getAtPos fuel pos with
        | .bot => throwErr "readR: array place holds a hole (⊥) — take without refill"
        | p =>
          match firstLoanMarker p with
          | some ℓ => do endLoan fuel ℓ; readR fuel t     -- §5.2: every demand collapses first
          | none =>
            if indexKindV fuel (← get).sctx p then do mergeRoot pos.root; pure p  -- §2.1 copy-on-read
            else do setAtPos fuel pos .bot; mergeRoot pos.root; pure p
      | .borrowT _ _ => throwErr "readR (⇒): borrow type `&mut (τ ↝ S)` is a telescope-position form, not a movable value"
  termination_by fuel _ => (fuel, 0, 0)
  def readArgs : Nat → List Term → M (List Val)
    | _, [] => pure []
    | fuel, a :: as => do
      let v ← readR fuel a
      pure (v :: (← readArgs fuel as))
  termination_by fuel as => (fuel, 1, as.length)
  /-- Consume a call's arguments left-to-right, checking each against its
      telescope entry, and RETURN the captured loans (§6.1): each argument
      borrow's loan ℓ with its owed type `S[s := v]`. A pure argument must
      `hasType` its parameter type; a borrow argument must be a `borrowM ℓ v`
      whose payload `v` has the parameter type τ, and is consumed. -/
  def processArgs : Nat → Nat → Omega → List (String × Term) → List Term → M (List (Nat × Val) × Omega)
    | _, _, inst, [], [] => pure ([], inst)
    | fuel, i, inst, (name, tyTerm) :: tRest, arg :: aRest => do
      -- Parameter `i`'s runtime var (the §5.2 convention: a later type mentions
      -- it as `.var ⟨i, name⟩`). `inst` binds parameters `0 … i-1` to the
      -- actuals already checked, so this type is read at those actuals.
      let declVar : Var := ⟨i, name⟩
      match tyTerm with
      | .borrowT τ S => do
        match ← readR fuel arg with
        | .borrowM ℓ payload => do
          let τVal ← readCWith fuel inst τ
          if ← hasType fuel payload τVal then do
            let SVal ← readCWith fuel inst S
            let owed := Val.nfV fuel (Val.substPure 0 payload SVal)
            -- A borrow parameter is bound to the actual borrow itself, so a later
            -- type mentioning `*b` (§5.2's comptime-deref at the call site)
            -- reflects the peel to the payload snapshot just passed.
            let (rest, inst') ← processArgs fuel (i + 1) ((declVar, .borrowM ℓ payload) :: inst) tRest aRest
            pure ((ℓ, owed) :: rest, inst')
          else
            throwErr s!"call: borrow argument's payload ({payload.pretty}) does not have its parameter type ({τVal.pretty})"
        | v => throwErr s!"call: expected a borrow argument (&mut …), got {v.pretty}"
      -- ¶4's runtime-length slice at a CALL SITE (M24 STEP 1's probe). The actual is a
      -- genuine pair — a length and a borrow — so the capture is the borrow's loan and
      -- the length is checked like any other argument. See `docs/DELTAS.md` G2.
      | .sigmaT aTy (.borrowT τ S) => do
        match ← readR fuel arg with
        | .ctor "Pair" [cv, .borrowM ℓ payload] => do
          let aVal ← readCWith fuel inst aTy
          if !(← hasType fuel cv aVal) then
            throwErr s!"call: slice length ({cv.pretty}) does not have its parameter type ({aVal.pretty})"
          else
            let τVal := Val.substPure 0 cv (← readCWith fuel inst τ)
            if ← hasType fuel payload τVal then do
              let SVal ← readCWith fuel inst S
              let owed := Val.nfV fuel (Val.substPure 0 cv (Val.substPure 0 payload SVal))
              let pairV : Val := .ctor "Pair" [cv, .borrowM ℓ payload]
              let (rest, inst') ← processArgs fuel (i + 1) ((declVar, pairV) :: inst) tRest aRest
              pure ((ℓ, owed) :: rest, inst')
            else
              throwErr s!"call: slice payload ({payload.pretty}) does not have its parameter type ({τVal.pretty})"
        | v => throwErr s!"call: expected a Σ-typed slice (a Pair of a length and a borrow), got {v.pretty}"
      | tyTerm => do
        let argVal ← readR fuel arg
        let τVal ← readCWith fuel inst tyTerm
        if ← hasType fuel argVal τVal then
          processArgs fuel (i + 1) ((declVar, argVal) :: inst) tRest aRest
        else throwErr s!"call: argument ({argVal.pretty}) does not have its parameter type ({τVal.pretty})"
    | _, _, _, _, _ => throwErr "call: arity mismatch (arguments vs telescope)"
  termination_by fuel _ _ _ args => (fuel, 1, args.length)
  /-- Executing mode (§9): ⇒-read each actual and bind it to the callee's
      argument var, shifted into the fresh frame window at `offset`. -/
  def bindActuals (fuel offset : Nat) : Nat → List (String × Term) → List Term → M Unit
    | _, [], [] => pure ()
    | i, (name, _) :: tRest, arg :: aRest => do
      let v ← readR fuel arg
      bindSlot ⟨i + offset, name⟩ v
      bindActuals fuel offset (i + 1) tRest aRest
    | _, _, _ => throwErr "executeCall: arity mismatch (actuals vs telescope)"
  termination_by _ _ args => (fuel, 1, args.length)
end

/-! ## Running programs -/

/-- The initial machine state: empty Ω, fresh supplies at 0. -/
def initSt : St := { env := [], nextLoan := 0, nextVar := 0, nextSym := 0 }

/-- Generous default fuel; §2 programs use only a handful. -/
def defaultFuel : Nat := 1000

/-- Run a program with a fresh state: ⇒-read it, then return the final
    canonicalized Ω (loan ids renumbered to first-appearance order), or the
    error. The return value of the read is discarded — §2 tests inspect Ω. -/
def runProg (t : Term) (fuel : Nat := defaultFuel) : Except String Env :=
  match (readR fuel t).run initSt with
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
  | ownedSym   : Nat → Option Val → Dispatch
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
      match payload with
      | .ctor name fields => pure (.borrowCtor ℓ name fields)
      | .sym σ => pure (.borrowSym ℓ σ)
      | .loanM ℓ' => do endLoan fuel ℓ'; reorgScrut fuel scrut
      | .bot => throwErr s!"match: matching through a hole (⊥) at {scrut.name}#{scrut.id}"
      | .borrowM _ _ => throwErr s!"match: scrutinee payload is a nested borrow (unsupported in §3)"
      | _ => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} payload is not a constructor"
    | v =>
      match firstLoanMarker v with
      | some ℓ => do endLoan fuel ℓ; reorgScrut fuel scrut
      | none =>
        match v with
        | .ctor name fields => pure (.ownedCtor name fields)
        | .sym σ => pure (.ownedSym σ none)
        -- §19: a stuck spine (`leb σ σp`, a neutral application). Generalize it to
        -- a fresh σb : Bool across all σ-bearing state, then split on σb as an
        -- ordinary owned sym — the True/False refinement rewrites the spine per path.
        -- The spine itself rides along so the branch can bind an equation about it.
        | .app _ _ => do let (σb, sp) ← generalizeStuck fuel v; pure (.ownedSym σb (some sp))
        | _ => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} is not a constructor or symbolic value"

/-- Mint fresh σ's for the given field types, typing each in `sctx`
    (dependent positions instantiated at earlier fresh σ's — a real telescope).
    Returns the fresh σ ids. -/
def typeFieldSyms : List Var → List Val → M (List Nat)
  | [], [] => pure []
  | _ :: bs, ty :: tys => do
    let σ ← freshSym
    modify (fun s => { s with sctx := (σ, ty) :: s.sctx })
    let rest ← typeFieldSyms bs (tys.map (Val.substPure 0 (Val.sym σ)))
    pure (σ :: rest)
  | _, _ => throwErr "match: constructor arity mismatch (σ-typing)"


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
    if br.ctor == "Refl" then
      match Val.whnfV fuel τ with
      | .idT _ a b => do reflUnify fuel a b; pure []            -- unify endpoints, no fields
      | _ => throwErr "match: Refl branch on a non-Id scrutinee"
    else match Val.ctorSig br.ctor with
    | none => throwErr s!"match: unknown constructor '{br.ctor}'"
    | some sig =>
      match sig.fieldTypes (Val.whnfV fuel τ) with
      | none => throwErr s!"match: constructor '{br.ctor}' does not belong to the scrutinee's type"
      | some ftys => typeFieldSyms br.binders ftys

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
def mintStuckEqn (scrutσ : Nat) (spine : Val) (ctor : String) (σs : List Nat) : M Nat := do
  let σe ← freshSym
  match (← get).sctx.lookup scrutσ with
  | none => pure σe                                      -- untyped scrutinee: untyped equation
  | some τ =>
    modify (fun s => { s with
      sctx := (σe, .idT τ spine (.ctor ctor (σs.map Val.sym))) :: s.sctx })
    pure σe

/-- Symbolic **owned** branch entry (§3.2): mint (σ-typed) fresh σ's for the
    pattern fields, ⇜-refine the scrutinee to `C (sym σ₁) … (sym σₙ)`
    *everywhere*, then destructure as owned match (scrutinee → ⊥, binders ↦
    `sym σᵢ`). Returns the branch body. `stuck` carries the pre-abstraction spine
    when there was one; the declared equation binder (M23) is bound to its
    hypothesis, or to `Refl` when refinement has already equated the endpoints. -/
def symOwnedSetup (fuel : Nat) (scrut : Var) (scrutσ : Nat) (stuck : Option Val)
    (eqn : Option Var) (br : Branch) : M Term := do
  let σs ← mintFieldSyms fuel scrutσ br
  let eqv : Option Val ← match eqn, stuck with
    | none, _ => pure none
    | some _, none => pure (some (.ctor "Refl" []))
    | some _, some spine => do pure (some (.sym (← mintStuckEqn scrutσ spine br.ctor σs)))
  writeC (.var scrut) (.ctor br.ctor (σs.map Val.sym))   -- ⇜ everywhere (refinement first)
  setSlot scrut .bot                                     -- owned consume
  bindFields br.binders (σs.map Val.sym)
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
  let σs ← mintFieldSyms fuel scrutσ br
  writeC (.deref (.var scrut)) (.ctor br.ctor (σs.map Val.sym))   -- ⇜ at payload, everywhere
  let ℓs ← br.binders.mapM (fun _ => freshLoan)
  setSlot scrut (.borrowM ℓ (.ctor br.ctor (ℓs.map Val.loanM)))   -- suspend the parent
  bindBorrowFields br.binders ℓs (σs.map Val.sym)
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
    match Val.typeCtors (Val.whnfV fuel τ) with
    | none => pure ()                                 -- unknown type: nothing to check against
    | some ctors =>
      let covered := branches.map (·.ctor)
      match ctors.find? (fun c => !covered.contains c) with
      | some missing =>
        throwErr s!"match: non-exhaustive — no branch for constructor '{missing}' of the scrutinee's type"
      | none => pure ()


/-! Move each statement-spine match into tail position by pushing the
    continuation into every branch (duplicating it): `seq (matchE) k` and
    `let y = matchE; k` become terminal matches. Match in *expression*
    position is left where it is — `explore`/`readR` reject it clearly. -/
mutual
  def pushContinuations : Term → Term
    | .letIn x rhs rest =>
      match pushContinuations rhs with
      | .matchE s eqn bs =>
        let k := pushContinuations rest
        .matchE s eqn (bs.map (fun br => Branch.mk br.ctor br.binders (.letIn x br.body k)))
      | rhs' => .letIn x rhs' (pushContinuations rest)
    | .seq e rest =>
      match pushContinuations e with
      | .matchE s eqn bs =>
        let k := pushContinuations rest
        .matchE s eqn (bs.map (fun br => Branch.mk br.ctor br.binders (.seq br.body k)))
      | e' => .seq e' (pushContinuations rest)
    | .assign p rhs rest => .assign p rhs (pushContinuations rest)
    | .matchE s eqn bs => .matchE s eqn (pushBranches bs)
    | t => t
  termination_by t => sizeOf t
  def pushBranches : List Branch → List Branch
    | [] => []
    | (.mk c bs body) :: rest => Branch.mk c bs (pushContinuations body) :: pushBranches rest
  termination_by bs => sizeOf bs
end

/-! Walk the (already `pushContinuations`-normalized) statement spine,
    returning one result per execution path. Non-match steps delegate to the
    single-path `M` machinery; a terminal match forks per branch on a symbolic
    scrutinee, stays single-path on a concrete one. Fuel bounds spine depth.
    The lexicographic `(fuel, tag, len)` measure admits the same-fuel handoffs
    (match → per-branch loop → branch body). -/
mutual
  def explore : Nat → Term → St → List (Except String (Val × St))
    | 0, _, _ => [.error "explore: out of fuel"]
    | fuel + 1, t, st =>
      match t with
      | .matchE scrut eqn branches => exploreMatch fuel scrut eqn branches st
      | .letIn x rhs rest =>
        match (do let v ← readR fuel rhs; bindSlot x v).run st with
        | .error e _ => [.error e]
        | .ok _ st' => explore fuel rest st'
      | .seq e rest =>
        match (do let _ ← readR fuel e; pure ()).run st with
        | .error e _ => [.error e]
        | .ok _ st' => explore fuel rest st'
      | .assign p rhs rest =>
        match (do let v ← readR fuel rhs; writeR fuel p v).run st with
        | .error e _ => [.error e]
        | .ok _ st' => explore fuel rest st'
      | other =>                                     -- final expression
        match (readR fuel other).run st with
        | .error e _ => [.error e]
        | .ok v st' => [.ok (v, st')]
  termination_by fuel _ _ => (fuel, 0, 0)
  def exploreMatch : Nat → Var → Option Var → List Branch → St → List (Except String (Val × St))
    | fuel, scrut, eqn, branches, st =>
      match (reorgScrut fuel scrut).run st with
      | .error e _ => [.error e]
      | .ok disp st' =>
        match disp with
        | .ownedCtor name fields =>
          match (ownedSelect scrut eqn branches name fields).run st' with
          | .error e _ => [.error e]
          | .ok body st'' => explore fuel body st''
        | .borrowCtor ℓ name fields =>
          match (borrowSelect scrut eqn branches ℓ name fields).run st' with
          | .error e _ => [.error e]
          | .ok body st'' => explore fuel body st''
        | .ownedSym σ stuck =>
          match (checkExhaustive fuel σ branches).run st' with
          | .error e _ => [.error e]
          | .ok _ st'' => exploreSymBranches fuel scrut false 0 σ stuck eqn branches st''
        | .borrowSym ℓ σ =>
          match (checkExhaustive fuel σ branches).run st' with
          | .error e _ => [.error e]
          | .ok _ st'' => exploreSymBranches fuel scrut true ℓ σ none eqn branches st''
  termination_by fuel _ _ _ _ => (fuel, 2, 0)
  /-- One symbolic path per branch, in declaration order. `borrow` selects the
      setup; `ℓ` is the parent loan (borrow mode only); `σ` is the scrutinee's
      symbolic id (used to type the field σ's); `stuck` is the pre-abstraction
      spine, when the σ came from one; `eqn` the declared equation binder. -/
  def exploreSymBranches : Nat → Var → Bool → Nat → Nat → Option Val → Option Var →
      List Branch → St → List (Except String (Val × St))
    | _, _, _, _, _, _, _, [], _ => []
    | fuel, scrut, borrow, ℓ, σ, stuck, eqn, br :: rest, st =>
      (match ((if borrow then symBorrowSetup fuel scrut ℓ σ eqn br
               else symOwnedSetup fuel scrut σ stuck eqn br)).run st with
       | .error e _ => [.error e]
       | .ok body st' => explore fuel body st')
      ++ exploreSymBranches fuel scrut borrow ℓ σ stuck eqn rest st
  termination_by fuel _ _ _ _ _ _ branches _ => (fuel, 1, branches.length)
end

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
  (explore fuel (pushContinuations t) (seedSt seed)).map
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
def seedPure (env : Omega) (sctx : List (Nat × Val)) : St := { seedSt env with sctx := sctx }

/-- Test helper: `readC t` equals `expected` (by structural value equality). -/
def expectReadC (env : Omega) (sctx : List (Nat × Val)) (t : Term) (expected : Val)
    (fuel : Nat := defaultFuel) : Bool :=
  match (readC fuel t).run (seedPure env sctx) with
  | .ok v _ => v == expected
  | .error _ _ => false

/-- Test helper: `readC t₁` and `readC t₂` are convertible. -/
def expectConv (env : Omega) (sctx : List (Nat × Val)) (t1 t2 : Term)
    (fuel : Nat := defaultFuel) : Bool :=
  match (do let a ← readC fuel t1; let b ← readC fuel t2; pure (Val.convert fuel a b)).run
      (seedPure env sctx) with
  | .ok r _ => r
  | .error _ _ => false

/-- Test helper: value `v` has type `ty` under the σ-context. -/
def expectHasType (env : Omega) (sctx : List (Nat × Val)) (v ty : Val)
    (fuel : Nat := defaultFuel) : Bool :=
  match (hasType fuel v ty).run (seedPure env sctx) with
  | .ok r _ => r
  | .error _ _ => false

end Dllbc
