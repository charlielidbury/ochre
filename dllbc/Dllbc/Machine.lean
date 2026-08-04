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
  /-- **The moded-Π context** (M26-C): for a σ minted by sealing a function, the
      signature it was sealed at — as a `Decl`, which is precisely "a telescope
      and a return type with no body".

      Why this is not `sctx`. A borrow-moded Π has **no `Val`** — `readC` refuses
      `borrowT`, and rightly, since a borrow type is a telescope-position marker
      and not a type anything inhabits. So the sealed view of a function that
      takes a `&mut` cannot be recorded where `sctx` records types, and the
      honest place is one that keeps it as a `Term` telescope: exactly the shape
      the call rule already reads. That is what makes `.callV` on such a σ the
      SAME rule as `.call` on a table entry (`callDeclC`) rather than a second
      one — §3's "abstract application at a moded Π", with nothing new under it.

      `sctx` still holds the borrow-free case (phase A's `σ : Π`), so the two
      contexts partition abstract callees by whether their type has a value. -/
  fsig : List (Nat × Decl) := []
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
  -- A runtime function value is closed and marker-free, so the ownership
  -- machinery is doubly vacuous on it exactly as it is on a λ — and `ih` is read
  -- once per recursive call site, so copy-on-read is what makes a body able to
  -- recurse twice (`quicksort`'s two halves). §7 cost 2's "never partially
  -- applied, closed" is what earns this.
  | .rfn _ _ => true
  | .idT _ _ _ => true
  | .app _ _ => true                                        -- a pure-former spine (proof/type)
  | .pvar _ => true
  | .sigmaT _ _ => true                                     -- a type
  | .borrowM _ _ => false
  | .loanM _ => false
  -- A binder-mode marker is not a value and never stands in a slot (§6); it
  -- reaches here only through a malformed term, and the conservative answer is
  -- the one every unclassifiable shape gets.
  | .cmpT _ => false
  | .bot => false

/-! Substitute `newV` for every `sym σ` occurrence in `v` — the value-tree
    core of ⇜ (§3.2 refinement substitutes σ *everywhere*). -/
mutual
  def substSym (σ : Nat) (newV : Val) : Val → Val
    | .sym σ' => if σ' == σ then newV else .sym σ'
    | .rfn xs b => .rfn xs b                             -- closed: no σ inside
    | .borrowM ℓ p => .borrowM ℓ (substSym σ newV p)
    | .cmpT τ => .cmpT (substSym σ newV τ)
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
    -- The mode marker reflects structurally. ⇝ carries it without ever reading
    -- it: `beq` is mode-blind, so no comptime judgment can branch on a mode
    -- (§6, "case is inert under ⇝"). It is here so that ⇒ can read it off a
    -- value callee's Π — the one arrow that is entitled to ask.
    | .cmpT τ => do pure (.cmpT (← reflectC τ))
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
    -- The seal is a ⇒-form and only a ⇒-form (combining-fns §5). Minting needs an
    -- EVENT; ⇝ is a pure judgment with none, so a seal reduced twice under ⇝ would
    -- disagree with itself. It is listed here with the other five runtime-only
    -- forms because that list IS this calculus's definition of the pure
    -- sub-grammar (§1.3) — and, unlike a mode flag, the exclusion is structural
    -- twice over: `.seal` is its own constructor (⇝'s `.app` rule cannot see it)
    -- and `Val` has no seal former (no comptime RULE for it can be written).
    | .seal _ _ => throwErr "readC (⇝): `seal` is not in the comptime fragment — the seal is a ⇒-form, because minting a fresh σ needs an event and ⇝ has none (§5)"
    | .callV _ _ => throwErr "readC (⇝): a value-callee call is not in the comptime fragment — comptime application of an abstract function is the structured neutral `f a`, written as an application (§2.1)"
    -- The runtime λ joins the same list, and for the same structural reason as
    -- the seal: it is its own constructor, and its body is a BODY. ⇝'s λ is
    -- `.lam` — domain-annotated, de Bruijn, body a pure term — and a `.lamR`
    -- would have to be reduced by binding named slots, which is ⇒'s move.
    | .lamR _ _ => throwErr "readC (⇝): a runtime λ (`λ(x, …){ … }`) is not in the comptime fragment — its body is a body (writes, calls, borrows) and its binders are Ω slots. The comptime λ is `λ (x : τ). e` (§1.3)"
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
  -- A seal's body is ordinary runtime code and may call; a value-callee call
  -- names no DECLARATION (that is the point of it), but its arguments may.
  | .seal t u => calleeNames t ++ calleeNames u
  | .callV _ args => args.flatMap calleeNames
  -- A runtime λ's body is ordinary runtime code and may call declared functions;
  -- the reachability check must see through it or a recursion routed through an
  -- arm would be invisible to it.
  | .lamR _ body => calleeNames body
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
      -- `⇝τ` is a binder MODE, not a type (§6): a value inhabits it exactly when
      -- it inhabits `τ`. Stripped once here rather than at each of the rules that
      -- consult a binder's domain, so no path can accidentally ask `Z : ⇝Nat` and
      -- get `false` for the wrong reason.
      let ty := Val.stripCmp ty
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
    throwErr s!"fence: '{x.name}' is a COMPTIME binder (capitalized — §6) and {what}. A comptime binder is erased: it is never moved, never scrutinized, never borrowed or written through, and exists only in ⇝-positions (types, proofs, and the capital argument positions of other calls). If it must exist at runtime, lower-case it."
  else pure ()

/-- …and the same at a place expression, keyed on the place's root. -/
def fencePlace (t : Term) (what : String) : M Unit :=
  match placeRoot? t with
  | some x => fenceComptime x what
  | none => pure ()

/-- **⇐ (write)** — the fill-only write arrow, defined only on places. Its
    premise is a vacant (⊥) target; when the target is live a **drop** is
    forced first (§2.3), vacating it, then the value drops in. We vacate the
    slot *before* dropping so drop's Ω-scans never see a stale copy of the
    displaced value. -/
def writeR (fuel : Nat) (place : Term) (newval : Val) : M Unit := do
  -- §6's fence, before the place is navigated: a write through a comptime binder
  -- would make an erased thing observable, and `placeToPos` may carve.
  fencePlace place "cannot be written through (⇐)"
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
    -- A seal's BODY is a runtime term (it may name the frame's slots); its TYPE is
    -- a type, whose runtime-var occurrences (`*v` in an ensures, §5.2) shift for
    -- the same reason the pure formers below do.
    | .seal t u => .seal (shiftVars d t) (shiftVars d u)
    -- The callee is a slot, so it shifts exactly as a `.matchE` scrutinee does.
    | .callV x args => .callV ⟨x.id + d, x.name⟩ (shiftVarsList d args)
    -- A runtime λ's binders shift WITH its body, which is the property that makes
    -- frames compose: applying a `lamR` shifts the whole node into a fresh
    -- window, so binder ids and their occurrences stay in step no matter how many
    -- frames a nested one has already been carried through.
    | .lamR xs body => .lamR (xs.map (fun v => ⟨v.id + d, v.name⟩)) (shiftVars d body)
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

/-! ## Peeling a borrow-moded Π into a telescope (M26-C)

    §5's audit relocation needs the sealed type as a **telescope plus a return
    type**, because that is the shape `seedTelescope` seeds and `auditAction`
    audits. Deriving one from a Π is ordinary binder-peeling — except that it has
    to happen on `Term`s, since a borrow-moded Π has no `Val` (see `St.fsig`).
    `Term.substPure` is what that costs. -/

/-- Peel one Π binder per name, instantiating the rest at that name. Returns the
    telescope and the residual return type.

    **The mode agreement check lives here**, and it is the one place §6 could be
    stated twice and disagree: a runtime λ's binders carry their mode in their
    NAMES, the ascribed Π carries its in its DOMAINS (`⇝τ`), and a lowercase
    binder under a capital-bindered Π would let the body observe at runtime what
    the caller was promised is erased. Phase B settled that "the ascription is the
    contract" for CALLERS (F3); this is the callee-side half of the same
    sentence, and it is a rejection rather than a coercion because the two claims
    are about different people. -/
def piPeel : List Var → Term → Except String (List (Var × Term) × Term)
  | [], u => .ok ([], u)
  | x :: xs, u =>
    match u with
    | .pi dom cod =>
      if Term.domComptime dom != x.isComptime then
        .error s!"seal: binder '{x.name}' is {if x.isComptime then "capitalized (comptime, §6)" else "lowercase (runtime, §6)"} but the ascribed type binds it as {if Term.domComptime dom then "comptime (⇝τ)" else "runtime"}. A binder's mode is a claim about whether the body may observe its argument at runtime, and the ascription is what callers are promised — the two cannot differ."
      else
        match piPeel xs (Term.substPure 0 (.var x) cod) with
        | .ok (rest, ret) => .ok ((x, dom.stripCmp) :: rest, ret)
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
    | fuel + 1, i, .pi dom cod =>
      Var.mk i (if Term.domComptime dom then s!"A{i}" else s!"a{i}") :: go fuel (i + 1) cod
    | _, _, _ => []
  go 64 0 t

/-- A Var-keyed telescope's borrow parameters, by var id (`borrowParamIds`'
    counterpart for a telescope that brought its own names). -/
def borrowVarIds (tel : List (Var × Term)) : List Nat :=
  tel.filterMap (fun p => match p.2 with | .borrowT _ _ => some p.1.id | _ => none)

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

/-- Seed the telescope into Ω and `sctx`, returning the borrow obligations.
    Argument `i` gets runtime var id `i`. A pure (unrestricted) type τ →
    `x ↦ sym σ`, `sctx[σ : τ]`. A borrow type `&mut (s : τ ↝ S)` → fresh ℓ and
    σ, `x ↦ borrowM ℓ (sym σ)`, `sctx[σ : τ]`, and an obligation carrying `S`
    instantiated at `s := σ`. Crucially there is NO owner entry for an argument
    borrow's loan — the caller holds it; nothing in the body can collapse the
    borrow by owner-demand, only the audit can.

    **Var-keyed** since M26-C, because the seal seeds one too: a `Decl` names its
    parameters positionally (argument `i` ↦ var id `i`, which is what the corpus's
    types reference), while a runtime λ brings its own binder `Var`s and its body
    reaches them by those ids. Same seeding either way; only who supplies the
    names differs. -/
def seedTelescopeV (fuel : Nat) : List (Var × Term) → M (List Obligation)
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
      | .borrowT _ _ | .sigmaT _ (.borrowT _ _) =>
        throwErr s!"telescope: parameter '{name}' is capitalized (comptime, §6) but its type is a borrow — a ⇝-read of `&mut` is meaningless, so borrow-typed binders must be lowercase"
      | _ => pure ()
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
      pure (⟨x, ℓ, owed⟩ :: (← seedTelescopeV fuel rest))
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
      pure (⟨x, ℓ, owed⟩ :: (← seedTelescopeV fuel rest))
    -- **`ih` — a parameter whose type is a borrow-moded Π** (M26-C, §7 cost 1).
    -- It has no `Val` (`readC` refuses `borrowT`), so it cannot be a σ in `sctx`;
    -- it is a σ whose signature lives in `fsig`, which is what makes calling it
    -- the ordinary call rule. §7's convergence argument arrives here as one
    -- branch: "the only available view of the function is the σ-side, so the
    -- recursive call is abstract application at `u` — self-ensures FORCED rather
    -- than stipulated". Nothing about this branch knows it is for a recursor.
    | .pi _ _ => do
      if hasBorrowT tyTerm then do
        let σ ← freshSym
        bindSlot x (.sym σ)
        let names := piBinderNames tyTerm
        match piPeel names tyTerm with
        | .error e => throwErr e
        | .ok (tel, ret) => do
          let sig : Decl :=
            { name := "@ih"
              telescope := tel.map (fun p => (p.1.name, p.2))
              retType := ret
              body := .unit }
          modify (fun s => { s with fsig := (σ, sig) :: s.fsig })
          seedTelescopeV fuel rest
      else do
        let τVal ← readC fuel tyTerm
        let σ ← freshSym
        bindSlot x (.sym σ)
        modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
        seedTelescopeV fuel rest
    | tyTerm => do
      let τVal ← readC fuel tyTerm
      let σ ← freshSym
      bindSlot x (.sym σ)
      modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
      seedTelescopeV fuel rest

/-- The `Decl` view: parameter `i` gets runtime var id `i` — the §5.2 convention a
    declaration's own types are written against. -/
def seedTelescope (fuel : Nat) (i : Nat) (tel : List (String × Term)) : M (List Obligation) :=
  seedTelescopeV fuel ((tel.enum.map (fun p => (Var.mk (p.1 + i) p.2.1, p.2.2))))

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
def readComptimeArg (fuel : Nat) (t : Term) : M Val := do
  collapseCDerefs fuel t
  readC fuel t

/-- The binder modes of a callee, one per argument the spine supplies (§6).

    Peels λ- or Π-binders left to right, reading `domComptime` off each domain.
    A callee with fewer binders than arguments pads with runtime and lets the
    existing over-application rejection fire — this function decides *which
    arrow reads an argument*, never whether the arity is right. -/
def binderModes : Nat → Val → Nat → List Bool
  | _, _, 0 => []
  | 0, _, n => List.replicate n false
  | fuel + 1, v, n + 1 =>
    match Val.whnfV fuel v with
    | .lam dom body => Val.domComptime dom :: binderModes fuel body n
    | .pi dom cod => Val.domComptime dom :: binderModes fuel cod n
    | _ => List.replicate (n + 1) false

/-! ## Value-callee application (combining-fns §7 cost 2, M26-A)

    `.callV x [a₁ … aₙ]` applies whatever slot `x` holds. The two rules are §2's
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
def erasedMotive : Val := .const "@motive"

/-- Collect a `Term` application spine into head and arguments (the mirror of
    `Val.collectSpine`, needed because ⇒ meets recursors as terms first). -/
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
    if (recLayout c).isSome && args.any (fun a => match a with | .lamR _ _ => true | _ => false)
    then some (c, args) else none
  | _ => none

/-- Mint a fresh frame window for an inlined body's slots (the executing call
    rule's device, now shared with runtime-λ application). -/
def freshFrame : M Nat := do
  let s ← get
  set { s with nextFrame := s.nextFrame + 128 }
  pure s.nextFrame

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
    let (head, args) := Val.collectSpine v
    match head with
    | .rfn names _ => pure ((names.map Var.isComptime ++ List.replicate (n + 1) false).take (n + 1))
    | .const c =>
      match recLayout c with
      | none => pure (binderModes fuel v (n + 1))
      | some (k, _, b) =>
        if args.length == k then pure (false :: (← valBinderModes fuel (args.getD b .bot) n))
        else if args.length == k + 1 then valBinderModes fuel (args.getD b .bot) (n + 1)
        else pure (List.replicate (n + 1) false)
    | .sym σ =>
      match (← get).sctx.lookup σ with
      | some σty => pure (binderModes fuel σty (n + 1))
      | none => pure (List.replicate (n + 1) false)
    | _ => pure (binderModes fuel v (n + 1))

/-- Instantiate an abstract callee's Π-type at the arguments, returning the result
    type. This is `synthSpine` with the errors kept apart: a mistyped argument and
    an over-applied callee are different rejections, and `synthSpine`'s `none`
    collapses them. -/
def instantiatePi : Nat → Val → List Val → M Val
  | 0, _, _ => throwErr "callV: out of fuel (Π instantiation)"
  | _, ty, [] => pure ty
  | fuel + 1, ty, a :: rest =>
    match Val.whnfV fuel ty with
    | .pi dom cod => do
      if ← hasType fuel a dom then instantiatePi fuel (Val.substPure 0 a cod) rest
      else throwErr s!"callV: argument ({a.pretty}) does not have its parameter type ({dom.pretty})"
    | other => throwErr s!"callV: too many arguments — the callee's type is {other.pretty}, not a function type"

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
                   nextGroup := max acc.nextGroup st'.nextGroup
                   nextFrame := max acc.nextFrame st'.nextFrame }

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
      | .letIn x rhs rest => do
        -- **`let X = e` is a comptime binding** (§6): `e` is evaluated under ⇝,
        -- `X` is erased and non-consuming, and the fence confines it to
        -- ⇝-positions. Local spec abbreviations and locally-derived certificates
        -- without a new form — and without the capture-before-call staging that
        -- a runtime `let` of a proof forces. `let x = e` is unchanged.
        let v ← if x.isComptime then readComptimeArg fuel rhs else readR fuel rhs
        bindSlot x v
        readR fuel rest
      | .assign place rhs rest => do
        let v ← readR fuel rhs                           -- RHS by ⇒ first (§2.5 ordering)
        writeR fuel place v                              -- target by ⇐
        readR fuel rest
      | .matchE scrut eqn branches => do
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
          else callDeclC fuel decl args
      -- **The seal** (combining-fns §5): opacity as one node. The two readings
      -- are the two machines'.
      | .seal t u => do
        if (← get).executing then
          -- Concrete evaluation is always transparent: the body exists and runs.
          -- No check here — execution does not verify, it computes (and the
          -- checker has already accepted the node, or this program was never
          -- admitted). This is why a sealed value costs nothing at runtime.
          readR fuel t
        else do
          -- **SEALING A FUNCTION** (M26-C): the shape of the sealed TERM picks the
          -- rule, not the shape of the type. A runtime λ has no value the pure
          -- fragment could type — its body is a body — so the check that `t : u`
          -- is not `hasType` at all, it is §5.4's audit: seed `u`'s telescope,
          -- explore the body, audit each path. That is `sealFn`, and it is what
          -- phase A deferred when it rejected borrow-moded `u` by name.
          --
          -- Everything else keeps phase A's rule EXACTLY, which is what preserves
          -- §12-open-4's identity (a borrow-free sealed λ costs precisely
          -- `hasType`, over the whole 16-pair battery) — the new rule is reached
          -- by being a `.lamR`, never by the ascription happening to have a
          -- `&mut` in it.
          match t with
          | .lamR names body => sealFn fuel names body u
          -- A spine MAY be a recursor over runtime arms — §7's `fn` elaboration —
          -- in which case sealing it is arms-as-bodies checking. Any other spine
          -- is an ordinary term and takes phase A's rule.
          | .app _ _ => sealApp fuel t u
          | _ => sealValue fuel t u
      -- **Application of a value callee** (§7 cost 2). The callee is LOCATED, not
      -- consumed: reading a function to call it is a place read, like a match
      -- scrutinee's, so a slot can be called twice. (§2.1's copy-on-read would
      -- reach the same conclusion for the λ and σ:Π values phase A admits — both
      -- are index-kind — but stating it as location keeps the rule true of the
      -- borrow-capturing closures §7 defers, which are NOT copyable.)
      | .callV x args => do
        -- §6.3's distinction, made mechanical. A capital function-typed binder —
        -- `map_spec (G : Nat → Nat, v)` — is a SPEC parameter: the caller may
        -- supply an abstract or sealed function with no runtime existence, so the
        -- body may cite `G a` in a type (⇝ gives the structured neutral) but may
        -- not CALL it. `map_apply (g : …)` is the lowercase twin, and calling it
        -- is exactly what the lowercase buys.
        fenceComptime x "cannot be CALLED under ⇒ (a capital function-typed binder is a SPEC parameter — cite it in a type or a proof, where ⇝ gives its applications as structured neutrals; a caller need not supply anything with a runtime existence)"
        match ← lookupSlot x with
        | .bot => throwErr s!"callV: callee {x.name}#{x.id} holds ⊥ (use-after-move or uninitialized)"
        | callee =>
          -- §5.2's "every demand collapses first": a call is a demand on its
          -- callee slot, so a parked loan there ends before we look at what the
          -- slot holds. Vacuous for the closed function values of phase A, and
          -- listed rather than omitted — every UNLISTED demand site in this
          -- calculus has so far turned out to be a bug waiting for its first
          -- program (§5.2's own account of how that rule was earned).
          match firstLoanMarker callee with
          | some ℓ => do endLoan fuel ℓ; readR fuel (.callV x args)
          -- **A SEALED FUNCTION is called by the table's own rule** (M26-C).
          -- Its σ carries a moded signature rather than a `Val` type (see
          -- `St.fsig`), and `callDeclC` is what reads one: telescope in,
          -- ensures out, one loan group, borrow payloads re-minted. Dispatched
          -- HERE, before the arguments are read, because `processArgs` does its
          -- own §6 mode routing off the telescope — pre-reading them would
          -- consume a comptime argument the callee promised never to touch.
          | none =>
            match callee with
            | .sym σ =>
              match (← get).fsig.lookup σ with
              | some decl => callDeclC fuel decl args
              | none => callVValue fuel x callee args
            | _ => callVValue fuel x callee args
      -- **The runtime λ** (§7 cost 2). Evaluating one is only forming its value:
      -- the body is a suspension until the binders have arguments.
      --
      -- CLOSEDNESS IS CHECKED HERE, at the one point the value is formed. §7's
      -- "arms reference only their own binders and globals" is a real premise,
      -- not a description: a body is entered under a fresh id window, so a free
      -- variable would not dangle — it would be silently rebound to whatever the
      -- shift lands on, which is environment capture arriving by accident in the
      -- phase that defers it (constraint 5). Rejecting is the honest option, and
      -- the rejection names the variable.
      | .lamR names body => do
        -- A NULLARY runtime λ is refused, and the reason is a genuine ambiguity
        -- rather than tidiness: `λ(){ e }` is a thunk, and at ι there is no way
        -- to tell "the arm applied to no arguments" (force it) from "the arm with
        -- nothing owed" (it IS the value) — `applyRest` has to answer one way.
        -- Nothing in §7 wants a thunk: a recursor whose motive is not a function
        -- type has no trailing binders, so its arms are ordinary terms and the
        -- pure recursor already computes them.
        if names.isEmpty then
          throwErr "λr: a runtime λ must bind at least one argument. `λ(){ … }` is a thunk, and a thunk makes ι ambiguous — an arm applied to no arguments and an arm with nothing owed become the same spine. A recursor arm at a non-functional motive is an ordinary term; write it as one."
        match (Term.freeRVars (names.map (·.id)) body).head? with
        | some x =>
          throwErr s!"λr: the runtime λ's body mentions {x.name}#{x.id}, which is none of its {names.length} binder(s). §7 cost 2 admits only the CLOSED kind of function value — its body may name its own binders and globals, nothing else — and environment capture stays deferred (constraint 5). Make what it needs a parameter."
        | none => pure (.rfn names body)
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
          applyR fuel (Val.rebuildSpine (.const c) vs) []
        | none => do collapseCDerefs fuel t; readC fuel t
      | .idT _ _ _ => do collapseCDerefs fuel t; readC fuel t
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
      | .borrowT _ _ => throwErr "readR (⇒): borrow type `&mut (τ ↝ S)` is a telescope-position form, not a movable value"
      -- `⇝τ` outside a λ/Π domain is a mode marker that escaped its binder. Same
      -- standing as `borrowT` on the line above, and the same rejection.
      | .cmpT _ => throwErr "readR (⇒): `⇝τ` is a binder-mode marker (§6), legal only as a λ/Π domain — not a term and not a movable value"
  termination_by fuel _ => (fuel, 0, 0)
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
        | some true => readComptimeArg fuel a
        | _ => readR fuel a
      pure (v :: (← readArgsModed fuel (ms.drop 1) as))
  termination_by fuel _ as => (fuel, 1, as.length)
  /-- A runtime recursor spine's arguments: everything ⇒-read, except the motive,
      which is not read at all (`erasedMotive` — a borrow-moded Π has no ⇝
      reading, and ι has no use for one). -/
  def readRecArgs : Nat → Nat → Nat → List Term → M (List Val)
    | _, _, _, [] => pure []
    | fuel, mi, i, a :: as => do
      let v ← if i == mi then pure erasedMotive else readR fuel a
      pure (v :: (← readRecArgs fuel mi (i + 1) as))
  termination_by fuel _ _ as => (fuel, 1, as.length)
  /-- β for a literal λ callee: check each argument against its binder's domain,
      substitute, repeat. Domain-checking is CHECKING-mode only — executing mode
      runs already-accepted programs and `bindActuals` sets that precedent — so
      the two machines perform the same reduction and differ only in what they
      verify. (In the mutual block since M26-C: a residual that is not a `.lam`
      may be a runtime function, and application composes through `applyR`.) -/
  def applyLam : Nat → Val → List Val → M Val
    | 0, _, _ => throwErr "callV: out of fuel (λ application)"
    | fuel + 1, f, [] =>
      match Val.whnfV fuel f with
      | .lam d _ => throwErr s!"callV: partial application — the callee still expects an argument of type {d.pretty}, and runtime application is saturated (§12 decision 4). A function-VALUED result is refused here too, and M26-B confirms binder modes do NOT separate the two cases: `Π (x : A) → (Π (y : B) → C)` and `Π (x : A) → Π (y : B) → C` are the same term, so the residual binder's own mode says nothing about whose it is. The separating fact is elsewhere — a residual telescope with no borrow-moded binder could be curried soundly — and that is a phase C/D decision against §12 decision 4, not a mode question."
      | v => pure v
    | fuel + 1, f, a :: rest =>
      match Val.whnfV fuel f with
      | .lam dom body => do
        if (← get).executing then applyLam fuel (Val.substPure 0 a body) rest
        -- `hasType` strips the mode marker: which arrow READ the argument was
        -- settled before this call (`valBinderModes`), and what remains is the
        -- ordinary domain check.
        else if ← hasType fuel a dom then applyLam fuel (Val.substPure 0 a body) rest
        else throwErr s!"callV: argument ({a.pretty}) does not have its parameter type ({dom.pretty})"
      -- A pure λ whose body turns out to be a runtime function (or a recursor):
      -- hand the remaining spine to the ⇒-application rule rather than calling it
      -- an arity error. One application story, two reduction rules.
      | other => applyR fuel other (a :: rest)
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
    | fuel + 1, f, args => do
      let (head, sargs) := Val.collectSpine f
      let all := sargs ++ args
      match head, all with
      | .rfn names body, _ =>
        if all.length == names.length then applyRFn fuel names body all
        else if all.length < names.length then
          throwErr s!"callV: partial application — the runtime λ {(Val.rfn names body).pretty} binds {names.length} argument(s) and was given {all.length}. Runtime application is saturated (§12 decision 4): a partial application at runtime is a closure holding its arguments — including, in general, borrows — while it waits."
        else
          throwErr s!"callV: too many arguments — the runtime λ {(Val.rfn names body).pretty} binds {names.length} argument(s) and was given {all.length}"
      | .const "natRec", motive :: z :: s :: n :: rest =>
        match Val.whnfV fuel n with
        | .ctor "Z" [] => applyRest fuel z rest
        | .ctor "S" [m] =>
          applyRest fuel s (m :: Val.rebuildSpine (.const "natRec") [motive, z, s, m] :: rest)
        | n' => stuckRec fuel (.const "natRec") [motive, z, s, n'] rest
      | .const "boolRec", motive :: t :: e :: b :: rest =>
        match Val.whnfV fuel b with
        | .ctor "True" [] => applyRest fuel t rest
        | .ctor "False" [] => applyRest fuel e rest
        | b' => stuckRec fuel (.const "boolRec") [motive, t, e, b'] rest
      | .const "listRec", a :: motive :: pn :: pc :: l :: rest =>
        match Val.whnfV fuel l with
        | .ctor "Nil" [] => applyRest fuel pn rest
        | .ctor "Cons" [h, tl] =>
          applyRest fuel pc (h :: tl :: Val.rebuildSpine (.const "listRec") [a, motive, pn, pc, tl] :: rest)
        | l' => stuckRec fuel (.const "listRec") [a, motive, pn, pc, l'] rest
      | .lam _ _, _ => applyLam fuel head all
      -- Not a redex. Applied to nothing — the under-applied `natRec P z s` a seal
      -- ascribes, or a recursor stuck on a σ — it is a VALUE; applied to
      -- something it cannot consume, it is over-application.
      | _, _ =>
        if args.isEmpty then pure (Val.whnfV fuel f)
        else throwErr s!"callV: too many arguments — {head.pretty} is not a function (expected a λ, a runtime λ, or a recursor spine)"
  termination_by fuel _ _ => (fuel, 2, 0)
  /-- ι's continuation: the selected arm, applied to whatever the caller still
      owed. **With nothing owed the arm IS the value** — `natRec P z s Z` at a
      motive that computes a function type is that function, not a call of it —
      and keeping that distinct from `applyR arm []` is what lets a zero-argument
      value-callee call (`f()`) still be the partial application it is. -/
  def applyRest : Nat → Val → List Val → M Val
    | fuel, arm, [] => pure (Val.whnfV fuel arm)
    | fuel, arm, rest => applyR fuel arm rest
  termination_by fuel _ _ => (fuel, 3, 0)
  /-- A recursor that did not ι. With nothing owed it is a VALUE — the abstract
      self-view `ih` at a symbolic predecessor, which is precisely what §7's
      convergence argument says a recursive occurrence must be. With arguments
      owed it is arms-as-bodies checking at a symbolic scrutinee. -/
  def stuckRec : Nat → Val → List Val → List Val → M Val
    | _, head, spine, [] => pure (Val.rebuildSpine head spine)
    | _, head, spine, _ =>
      throwErr s!"applyR: {head.pretty} is stuck on a symbolic scrutinee ({(spine.getD (spine.length - 1) .bot).pretty}) and cannot ι. Applying a recursor at a symbolic scrutinee is arms-as-bodies CHECKING (§7 cost 1) — reachable through a seal, not through a call."
  /-- Apply a runtime function: bind its named binders in a **fresh frame** and
      ⇒-evaluate its body.

      The frame is what makes recursion work at all — the same body is entered
      once per level, and its binders are the same `Var` ids every time — and
      `shiftVars` moves the binders WITH the body, so a nested runtime λ that has
      already been carried through one frame stays consistent in the next. The
      body's own borrows are released on the way out, exactly as an inlined
      callee's are (`releaseFrameLoans`), so a frame's loans cannot outlive it. -/
  def applyRFn : Nat → List Var → Term → List Val → M Val
    | fuel, names, body, args => do
      let offset ← freshFrame
      let shifted := shiftVars offset body
      (names.zip args).forM (fun p => bindSlot ⟨p.1.id + offset, p.1.name⟩ p.2)
      let res ← readR fuel shifted
      releaseFrameLoans fuel offset res.loanIds
      pure res
  termination_by fuel _ _ _ => (fuel, 4, 0)
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
        | .borrowT _ _ | .sigmaT _ (.borrowT _ _) =>
          throwErr s!"call: parameter '{name}' is capitalized (comptime, §6) but its type is a borrow — a ⇝-read of `&mut` is meaningless, so borrow-typed binders must be lowercase"
        | _ => do
          let argVal ← readComptimeArg fuel arg
          let τVal ← readCWith fuel inst tyTerm.stripCmp
          if ← hasType fuel argVal τVal then
            processArgs fuel (i + 1) ((declVar, argVal) :: inst) tRest aRest
          else throwErr s!"call: comptime argument ({argVal.pretty}) does not have its parameter type ({τVal.pretty})"
      else
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
      -- The executing machine takes §6's comptime-argument rule too, in lockstep
      -- (constraint 6). A capital parameter's actual is ⇝-read here as well, so
      -- the two machines agree on what the CALLER still holds afterwards — which
      -- is the observable the differential compares. Erasure is enforced by the
      -- fence on the callee's uses, not by declining to bind the slot: a body
      -- that never observes it is indistinguishable from one that cannot.
      let x : Var := ⟨i, name⟩
      let v ← if x.isComptime then readComptimeArg fuel arg else readR fuel arg
      bindSlot ⟨i + offset, name⟩ v
      bindActuals fuel offset (i + 1) tRest aRest
    | _, _, _ => throwErr "executeCall: arity mismatch (actuals vs telescope)"
  termination_by _ _ args => (fuel, 1, args.length)
  /-- Application of a value callee that is NOT a sealed function: the phase-A
      rules (β for a λ, abstract application at a `Val` Π) plus M26-C's
      ⇒-application (`applyR`) for a runtime λ or a recursor spine. Split out
      of `.callV` only so the sealed case can be dispatched before the
      arguments are read; the rules themselves are unchanged. -/
  def callVValue : Nat → Var → Val → List Term → M Val
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
          | .lam _ _ => applyLam fuel callee argVals   -- body known ⟹ β
          -- A runtime function, or a recursor over runtime arms: ⇒-application
          -- (bind-and-run, and ι with the arm as a body). `ih` arrives here.
          | .rfn _ _ => applyR fuel callee argVals
          | .app _ _ => applyR fuel callee argVals
          | .const _ => applyR fuel callee argVals
          | .sym σ =>
            match (← get).sctx.lookup σ with
            | none => throwErr s!"callV: callee {x.name} is σ{σ}, which has no type in sctx"
            | some σty => do
              let resTy ← instantiatePi fuel σty argVals
              match Val.whnfV fuel resTy with
              | .pi d _ => throwErr s!"callV: partial application — σ{σ} still expects an argument of type {d.pretty}, and runtime application is saturated (§12 decision 4)"
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
                pure (.sym σ')
          | v => throwErr s!"callV: {x.name}#{x.id} holds {v.pretty}, which is not a function value (expected a λ or a σ : Π)"
  termination_by fuel _ _ _ => (fuel, 8, 0)
  /-- **§5.4's audit, relocated to the seal** (M26-C, phase A's deferral).

      Checking a runtime λ against a borrow-moded Π *is* `checkFn`'s content, and
      this is that content reached from the node instead of from a declaration:
      seed the telescope, pin the return type at entry (§5.3 — a dependent return
      type may mention a parameter the body consumes), explore the body one path
      per symbolic branch, and audit each path at return with exit snapshots and
      obligations. `checkFn` is untouched and still checks every `Decl` in the
      corpus (J1): what moved is content, and nothing was deleted.

      **FRAME ISOLATION.** The sealed body gets a fresh Ω, fresh obligations,
      fresh groups and no `selfRec`/`selfBack` — because it is a function being
      defined, not code running in the caller's world. Phase A evaluated a seal's
      body IN PLACE ("correct for phase A, and a sealed FUNCTION body will want
      frame isolation") and this is that debt paid. What crosses the boundary in
      each direction is exactly one thing: the ascribed type comes IN (already
      peeled, so it was read while the enclosing slots were live), and the fresh
      supplies go OUT advanced, so no later mint can collide with a σ the check
      put into a type. -/
  def checkRFnBody : Nat → List (Var × Term) → Term → Term → M Unit
    | fuel, tel, ret, body => do
      let saved ← get
      modify (fun s => { s with env := [], obligations := [], groups := [],
                                exitSyms := [], entrySyms := [], retTyVal := none,
                                selfBack := none, selfRec := none })
      let obs ← seedTelescopeV fuel tel
      -- §5.4 exit snapshots: one σ per borrow parameter, recorded ONLY here until
      -- the audit defines it as that borrow's collapsed final payload.
      let borrowIds := borrowVarIds tel
      let exits ← borrowIds.mapM (fun i => do pure (i, ← freshSym))
      modify (fun s => { s with exitSyms := exits, obligations := obs })
      if !hasBorrowT ret then do
        let rv ← readC fuel (markExit borrowIds ret)
        modify (fun s => { s with retTyVal := some rv })
      let st0 ← get
      let advanced ← auditAllPaths fuel ret (explore fuel (pushContinuations body) st0) st0
      set { saved with nextLoan := advanced.nextLoan, nextSym := advanced.nextSym
                       nextGroup := advanced.nextGroup, nextFrame := advanced.nextFrame }
  termination_by fuel _ _ _ => (fuel, 6, 0)
  /-- Sealing a VALUE — phase A's rule, verbatim, in its own definition since
      M26-C so that `readR`'s seal arm is a two-line dispatch.

      This is what preserves §12-open-4's identity: sealing a borrow-free term at
      `u` still costs precisely `readC`-then-`hasType`, with no premise of its
      own, over the whole 16-pair battery. The function-checking rule is reached
      by the sealed TERM being a runtime λ, never by the ascription happening to
      have a `&mut` in it — so nothing that used to take this path can be
      diverted onto the other one. -/
  def sealValue : Nat → Term → Term → M Val
    | fuel, t, u => do
      if hasBorrowT u then
        throwErr "seal: this term cannot be sealed at a borrow-moded type. A Π with `&mut` binders is a FUNCTION signature, and §5.4's audit is what checks a function against one — so the sealed term must be a runtime λ (`λ(v, …){ … }`) whose binders match it. Sealing anything else at such a Π would be asking `hasType` a question §5.4 does not ask."
      -- The type is read FIRST, while the body's free variables are still live:
      -- `u` may mention a slot that evaluating `t` then consumes, and a type
      -- re-read afterwards would find a ⊥. §5.3's entry-pinning lesson, arriving
      -- at the seal for the same reason it arrived at a dependent return type.
      let uV ← readC fuel u
      let v ← readR fuel t
      if ← hasType fuel v uV then do
        -- …then FORGET. A fresh σ at the ascribed type is the whole downstream
        -- view: `.seal` is generalization, so what the caller keeps is exactly
        -- what the programmer wrote (§5 point 4). The mint is coherent because
        -- this is an EVENT — ⇒ evaluates it once, in order — which is the
        -- property ⇝ lacks and the reason the node is a ⇒-form (§2.1).
        let σ ← freshSym
        modify (fun s => { s with sctx := (σ, uV) :: s.sctx })
        pure (.sym σ)
      else
        throwErr s!"seal: the sealed term ({v.pretty}) does not have its ascribed type ({uV.pretty})"
  termination_by fuel _ _ => (fuel, 9, 0)
  /-- A sealed application spine: a recursor over runtime arms takes the
      arms-as-bodies rule, anything else takes phase A's. -/
  def sealApp : Nat → Term → Term → M Val
    | fuel, t, u =>
      match runtimeRecSpine? t with
      | some (c, as) => sealRec fuel c as u
      | none => sealValue fuel t u
  termination_by fuel _ _ => (fuel, 13, 0)
  /-- Check ONE recursor arm as a body (§7 cost 1, "the one real kernel
      addition"): its leading binders take the types the recursor's premise gives
      them — the predecessor and `ih` — and the rest are peeled from the motive
      instantiated at this constructor. Then it is an ordinary function body, and
      `checkRFnBody` is the ordinary audit.

      "The content of that judgment is exactly today's guard-checking (a body with
      only the sealed self-view available); the plumbing is new" — and that is
      literally what this is: `pre` carries `ih`'s type, which `seedTelescopeV`
      turns into a σ with a signature and no body. -/
  def checkArm : Nat → Term → List (Var × Term) → List Var → Term → M Unit
    | fuel, body, pre, restNames, ty => do
      match piPeel restNames ty with
      | .error e => throwErr e
      | .ok (tel, ret) => checkRFnBody fuel (pre ++ tel) ret body
  termination_by fuel _ _ _ _ => (fuel, 10, 0)
  /-- **Sealing a RECURSOR whose arms are bodies** (§7): the checking side of the
      rule part 1 gave the executing machine.

      **The motive is derived from the signature**, exactly as §7 says the macro
      derives it: peel one Π off the ascription and the codomain IS the motive's
      body, with the scrutinee as its de Bruijn binder. The written motive is then
      compared against the derived one — syntactically, and that is forced rather
      than lazy: the motive contains borrow types, which have no `Val` and
      therefore no conversion to be compared up to. Since phase D's macro derives
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
  def sealRec : Nat → String → List Term → Term → M Val
    | fuel, c, args, u => do
      match u with
      | .pi scrutDom R => do
        let mi := match recLayout c with | some (_, m, _) => m | none => 0
        let derived : Term := .lam scrutDom R
        match args.get? mi with
        | none => throwErr s!"seal: {c} spine has no motive argument"
        | some written =>
          if !(Term.beq written derived) then
            throwErr s!"seal: the recursor's motive is not the one its ascription derives. §7 derives the motive from the signature — the sealed Π with the scrutinee peeled off — so a `{c}` sealed at `Π (n : τ) → R` must be written with the motive `λ (n : τ). R` and this one is not."
          else
            match c, args with
            | "natRec", [_, z, s] => do
              match z, s with
              | .lamR zn zbody, .lamR (k :: ihv :: rest) sbody => do
                checkArm fuel zbody [] zn (Term.substPure 0 (.ctorApp "Z" []) R)
                checkArm fuel sbody [(k, scrutDom), (ihv, Term.substPure 0 (.var k) R)] rest
                  (Term.substPure 0 (.ctorApp "S" [.var k]) R)
                sealMint fuel (piBinderNames u) u
              | _, _ => throwErr "seal: natRec's arms must be runtime λs, and the step arm must bind at least the predecessor and `ih` (§7's `λ f'. λ ih. λ v Hfuel. …`)"
            | "listRec", [_, _, pn, pc] => do
              match pn, pc with
              | .lamR nn nbody, .lamR (h :: tl :: ihv :: rest) cbody => do
                checkArm fuel nbody [] nn (Term.substPure 0 (.ctorApp "Nil" []) R)
                -- `h`'s type is the element type, read off the scrutinee's own
                -- `List A`; anything else and the arm is not this recursor's.
                let elemTy : Term := match scrutDom with
                  | .app (.const "List") a => a
                  | _ => .const "Nat"
                checkArm fuel cbody
                  [(h, elemTy), (tl, scrutDom), (ihv, Term.substPure 0 (.var tl) R)] rest
                  (Term.substPure 0 (.ctorApp "Cons" [.var h, .var tl]) R)
                sealMint fuel (piBinderNames u) u
              | _, _ => throwErr "seal: listRec's arms must be runtime λs, and the Cons arm must bind at least the head, the tail and `ih`"
            | "boolRec", [_, tArm, fArm] => do
              match tArm, fArm with
              | .lamR tn tbody, .lamR fn fbody => do
                checkArm fuel tbody [] tn (Term.substPure 0 (.ctorApp "True" []) R)
                checkArm fuel fbody [] fn (Term.substPure 0 (.ctorApp "False" []) R)
                sealMint fuel (piBinderNames u) u
              | _, _ => throwErr "seal: boolRec's arms must be runtime λs"
            | _, _ => throwErr s!"seal: `{c}` is not a recursor this phase checks as a sealed function, or its spine is not the bare `{c} P ⟨arms⟩` (the scrutinee is the SEALED Π's own binder, so it must not be applied)"
      | _ => throwErr "seal: a recursor sealed as a function must be ascribed a Π — its first binder is the scrutinee the recursion is on (§7's derived motive)"
  termination_by fuel _ _ _ => (fuel, 11, 0)
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
  def sealMint : Nat → List Var → Term → M Val
    | fuel, names, u => do
      match piPeel names u with
      | .error e => throwErr e
      | .ok (ctel, cret) => do
        let σ ← freshSym
        let sig : Decl :=
          { name := "@seal"
            telescope := ctel.map (fun p => (p.1.name, p.2))
            retType := cret
            body := .unit }
        modify (fun s => { s with fsig := (σ, sig) :: s.fsig })
        if !hasBorrowT u then do
          let uV ← readC fuel u
          modify (fun s => { s with sctx := (σ, uV) :: s.sctx })
        pure (.sym σ)
  termination_by fuel _ _ => (fuel, 12, 0)
  /-- Sealing a runtime λ: check it, then forget it.

      The two halves are §5's two sentences. The check is `checkRFnBody` against
      the Π peeled at the λ's OWN binders — the ids its body reaches Ω through.
      The forgetting mints a σ carrying the same Π peeled at POSITIONAL binders,
      which is the convention `processArgs`/`buildResult` read a telescope by, so
      what a caller sees is a callee indistinguishable from a table entry. Both
      peels come from the same `u`, so they cannot disagree. -/
  def sealFn : Nat → List Var → Term → Term → M Val
    | fuel, names, body, u => do
      match piPeel names u with
      | .error e => throwErr e
      | .ok (tel, ret) => do
        checkRFnBody fuel tel ret body
        -- The caller-visible signature keeps the λ's own binder NAMES (so a
        -- rejection at a call site names what the programmer wrote) at POSITIONAL
        -- ids (so `processArgs` reads it like any telescope).
        sealMint fuel (names.enum.map (fun p => Var.mk p.1 p.2.name)) u
  termination_by fuel _ _ _ => (fuel, 7, 0)
  /-- **The checking-mode call rule** (§5.3/§6.1), factored out of `.call` (M26-C)
      because a SEALED function is called by exactly the same rule: a σ whose
      signature is a borrow-moded Π is a callee whose telescope and return type
      are known and whose body is not, which is what a table entry already was.
      §3 says this in advance — "today's call rule is not a separate concept from
      application; it is abstract application at a moded Π" — and factoring is
      what turns that from a remark into a fact about the code.

      The `[k]` guard rides along and is inert for a seal, which is the right
      answer rather than a lucky one: a sealed signature is not in the table, so
      `selfRec`/`reachesFn` cannot match it, and §7 says the guard EVAPORATES for
      recursor-expressed functions anyway — `ih` is a binder, and a binder cannot
      be a self-call. -/
  def callDeclC : Nat → Decl → List Term → M Val
    | fuel, decl, args => do
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
            if decl.name == selfName then
              match dk with
              | none =>
                throwErr s!"recursion: '{decl.name}' calls itself but declares no decreasing argument ([k], §1.2) — a self-call admitted at its own return type with nothing decreasing proves any postcondition"
              | some (k, cur) =>
                match inst.find? (fun kv => kv.1.id == k) with
                | none => throwErr s!"recursion: '{decl.name}' declares decreasing argument [{k}] but the call passes no such argument"
                | some (_, act) =>
                  -- Unwrap a borrow on both sides: what decreases is the payload
                  -- snapshot, not the loan wrapping it.
                  let peel : Val → Val := fun v => match v with | .borrowM _ p => p | v => v
                  let a := Val.nfV fuel (peel act)
                  let c := Val.nfV fuel (peel cur)
                  if strictSubterm a c then pure ()
                  else throwErr s!"recursion: self-call's argument [{k}] ({a.pretty}) is not a strict structural predecessor of the parameter's snapshot ({c.pretty})"
            else if reachesFn (← get).decls [] decl.name selfName then
              throwErr s!"recursion: mutual recursion ('{selfName}' → '{decl.name}' → … → '{selfName}') is not supported — the [k] guard is per-declaration (§8)"
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
  termination_by fuel _ _ => (fuel, 5, 0)
  -- Walk the (already `pushContinuations`-normalized) statement spine,
  -- returning one result per execution path. Non-match steps delegate to the
  -- single-path `M` machinery; a terminal match forks per branch on a symbolic
  -- scrutinee, stays single-path on a concrete one. Fuel bounds spine depth.
  -- The lexicographic `(fuel, tag, len)` measure admits the same-fuel handoffs
  -- (match → per-branch loop → branch body). -/
  def explore : Nat → Term → St → List (Except String (Val × St))
    | 0, _, _ => [.error "explore: out of fuel"]
    | fuel + 1, t, st =>
      match t with
      | .matchE scrut eqn branches => exploreMatch fuel scrut eqn branches st
      | .letIn x rhs rest =>
        -- §6's comptime `let`, HERE as well as in `readR`. The explore driver
        -- does not route statement-spine steps through `readR`'s own `.letIn`
        -- case, so a rule that lives only there would be dead for every real
        -- body — which is what `pushContinuations` normalizes a body into. The
        -- duplication is two lines; a mode that silently stopped applying at the
        -- top level of a function body would have been a phantom.
        match (do
            let v ← if x.isComptime then readComptimeArg fuel rhs else readR fuel rhs
            bindSlot x v).run st with
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
      -- §6's fence at the OTHER match site. `readR`'s `.matchE` case only ever
      -- sees an expression-position match; a statement-position one — the only
      -- kind that may split a symbolic scrutinee, and therefore the only kind a
      -- real body writes — arrives here instead. Fencing one and not the other
      -- would have left the headline rejection (`match Fuel`) unreachable, which
      -- is how this was found: the test failed, not the reasoning.
      match (fenceComptime scrut "cannot be the scrutinee of a runtime match").run st with
      | .error e _ => [.error e]
      | .ok _ st =>
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
