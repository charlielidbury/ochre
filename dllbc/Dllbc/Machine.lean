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
  /-- §6.2: this function's OWN declared backward spec, reflected at entry (over
      the telescope snapshots). The callee audit checks the body against it — the
      captured borrow's payload-with-issued-holes must convert with the spec
      applied to fresh hole variables. Refined per-path like the owed types. -/
  selfBack : Option Val := none
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
    setEnv (ω.map (fun kv => (kv.1, replaceLoanMarker ℓ p kv.2)))
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

    A place is a variable under zero or more `*` peels (`x`, `*x`, `**x`, …) —
    the only shapes ⇐ and `&mut` are *defined* on (doc §1.1). A `Pos` records
    the root variable and the peel count; navigation descends through borrow
    payloads. `&mut`, the ⇒-take of `*p`, and ⇐-fill all share this. -/

/-- A resolved place: a root variable and a number of `*` peels. -/
structure Pos where
  root : Var
  derefs : Nat
deriving Repr

/-- Resolve a place term to a `Pos`. Errors on any non-place shape, which is
    exactly how ⇐/`&mut` reject writes/borrows of arbitrary expressions. -/
def placeToPos : Term → M Pos
  | .var x => pure ⟨x, 0⟩
  | .deref t => do let p ← placeToPos t; pure ⟨p.root, p.derefs + 1⟩
  | _ => throwErr "place: target is not a place (must be a variable under * peels)"

/-- Peel `n` borrow layers off `v`, returning the value at that depth. -/
def navRead : Nat → Val → M Val
  | 0, v => pure v
  | n + 1, .borrowM _ p => navRead n p
  | _ + 1, .bot => throwErr "*: cannot peel a vacant slot (⊥)"
  | _ + 1, .loanM ℓ => throwErr s!"*: cannot peel loanₘ ℓ{ℓ} (suspended borrow)"
  | _ + 1, .ctor n _ => throwErr s!"*: cannot peel constructor '{n}' (not a borrow)"
  | _ + 1, .sym σ => throwErr s!"*: cannot peel symbolic value σ{σ} (not a borrow)"
  | _ + 1, _ => throwErr "*: cannot peel a pure value (not a borrow)"

/-- Functionally set the value `n` borrow layers deep inside `v` to `newLeaf`. -/
def navWrite : Nat → Val → Val → M Val
  | 0, _, newLeaf => pure newLeaf
  | n + 1, .borrowM ℓ p, newLeaf => do
    let p' ← navWrite n p newLeaf
    pure (.borrowM ℓ p')
  | _ + 1, .bot, _ => throwErr "*: cannot peel a vacant slot (⊥)"
  | _ + 1, .loanM ℓ, _ => throwErr s!"*: cannot peel loanₘ ℓ{ℓ} (suspended borrow)"
  | _ + 1, .ctor n _, _ => throwErr s!"*: cannot peel constructor '{n}' (not a borrow)"
  | _ + 1, .sym σ, _ => throwErr s!"*: cannot peel symbolic value σ{σ} (not a borrow)"
  | _ + 1, _, _ => throwErr "*: cannot peel a pure value (not a borrow)"

/-- Read the value at a resolved position (peeks; no side effect). -/
def getAtPos (pos : Pos) : M Val := do
  navRead pos.derefs (← lookupSlot pos.root)

/-- Overwrite the value at a resolved position, threading the update back
    through the borrow payloads to the root slot. -/
def setAtPos (pos : Pos) (newLeaf : Val) : M Unit := do
  let v ← lookupSlot pos.root
  setSlot pos.root (← navWrite pos.derefs v newLeaf)

/-- **⇐ (write)** — the fill-only write arrow, defined only on places. Its
    premise is a vacant (⊥) target; when the target is live a **drop** is
    forced first (§2.3), vacating it, then the value drops in. We vacate the
    slot *before* dropping so drop's Ω-scans never see a stale copy of the
    displaced value. -/
def writeR (fuel : Nat) (place : Term) (newval : Val) : M Unit := do
  let pos ← placeToPos place
  let old ← getAtPos pos
  match old with
  | .bot => setAtPos pos newval                    -- fill
  | _ => do
    setAtPos pos .bot                              -- vacate first (no stale copy in Ω scans)
    drop fuel old                                  -- drop the displaced value
    setAtPos pos newval                            -- fill

/-- Refine `σ := v` **everywhere** — in every Ω slot AND every `sctx` type
    (§3.2's "everywhere", now including the type layer: a snapshot type that
    mentions the refined σ, e.g. `Id Nat σ 2`, is substituted like anything
    else — the seam §10 exercises). -/
def refineSym (σ : Nat) (v : Val) : M Unit :=
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
    selfBack := s.selfBack.map (substSym σ v) })

/-- **Generalize a stuck Bool spine** (§19) — the inverse of `refineSym`, and the
    two-layer principle at the machine level. When a match/`if` scrutinee reduces
    to a stuck spine `leb σ σp` (a neutral, not a bare σ), the ⇜ split cannot fire
    (it needs a substitutable σ). So NF the spine, mint a fresh `σb : Bool`, and
    `abstractInto` it across ALL σ-bearing state — the SAME targets `refineSym`
    reaches (Ω, sctx, obligations, groups, retTyVal, selfBack: the M10 invariant).
    Every occurrence of the spine in values AND types now reads `σb`, so the
    ordinary owned-sym split (`symOwnedSetup`'s `writeC`/`refineSym`) refines the
    spine to `True`/`False` per branch — including inside a declared spec's
    instantiation, which is exactly what the per-path back-spec conversion needs. -/
def generalizeStuck (fuel : Nat) (spine : Val) : M Nat := do
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
    selfBack := s.selfBack.map (abstractInto sp σb) })
  pure σb

/-- **⇜ (comptime write / refinement)** — the doc's ⇜, signature parallel to
    `writeR`. Defined on the same place shapes (a variable under peels). The
    place must currently hold a symbolic value `sym σ`; the effect is global
    refinement `σ := refined` (Ω and sctx). Errors distinctively otherwise. -/
def writeC (place : Term) (refined : Val) : M Unit := do
  let pos ← placeToPos place
  match ← getAtPos pos with
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
    | .var x => lookupSlot x                        -- snapshot read (non-destructive)
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
    | .assign _ _ _ => throwErr "readC (⇝): `:=` is excluded from the comptime fragment"
    | .borrow _ => throwErr "readC (⇝): `&mut` is not in the comptime fragment"
    | .seq _ _ => throwErr "readC (⇝): statement sequencing is not a comptime read"
    | .matchE _ _ => throwErr "readC (⇝): match not implemented in the comptime fragment this milestone"
    | .borrowT _ _ => throwErr "readC (⇝): borrow type `&mut (τ ↝ S)` is only valid at a telescope position"
    | .call _ _ => throwErr "readC (⇝): a call is not in the comptime fragment (its result is a fresh existential)"
  def reflectCList : List Term → M (List Val)
    | [] => pure []
    | t :: ts => do pure ((← reflectC t) :: (← reflectCList ts))
end

/-- ⇝: reflect then normalize. Ω is read-only throughout. -/
def readC (fuel : Nat) (t : Term) : M Val := do pure (Val.nfV fuel (← reflectC t))

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

/-- Build a call's fresh result value from the (instantiated) return type, and
    collect the loans it ISSUES (§6.1). Each `&mut (τ ↝ S)` position mints a
    fresh issued reborrow `borrowₘ ℓ σ` with `σ : τ` in `sctx` and owed type
    `S[s := σ]`; a `Pair`/`Σ` of results issues one loan PER borrow component
    (the multi-issued group — `nth2`); a non-borrow leaf is a plain fresh
    existential `σ` with no issued loan (the §5.3 wire). The second Σ component
    is built independently (a dependent product over the first is not supported;
    no test needs it). -/
def buildResult (fuel : Nat) (inst : Omega) : Term → M (Val × List (Nat × Val))
  | .borrowT τ S => do
    let τVal ← readCWith fuel inst τ
    let σ ← freshSym
    let ℓr ← freshLoan
    let sVal ← readCWith fuel inst S
    let owedR := Val.nfV fuel (Val.substPure 0 (Val.sym σ) sVal)
    modify (fun s => { s with sctx := (σ, τVal) :: s.sctx })
    pure (.borrowM ℓr (.sym σ), [(ℓr, owedR)])
  | .sigmaT a b => do
    let (vA, issA) ← buildResult fuel inst a
    let (vB, issB) ← buildResult fuel inst b
    pure (.ctor "Pair" [vA, vB], issA ++ issB)
  | rt => do
    let retTy ← readCWith fuel inst rt
    let σ ← freshSym
    modify (fun s => { s with sctx := (σ, retTy) :: s.sctx })
    pure (.sym σ, [])
  termination_by t => sizeOf t

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
    grp.captured.forM (fun (ℓc, owed) => do               -- opaque: fresh existential each
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

/-! ## Match branch selection (§3)

    These set up Ω for a branch and return the body term to evaluate; they do
    not call `readR`, so they stay outside the read recursion. `readR`'s match
    case reorganizes the scrutinee, then calls one of these, then reads the
    returned body. -/

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

/-- **Owned mode** (§3.1): ⇒-consume the scrutinee (slot → ⊥), select the
    branch by head constructor, move the fields into fresh binders, and return
    the branch body. -/
def ownedSelect (scrut : Var) (branches : List Branch) (name : String)
    (fields : List Val) : M Term := do
  match findBranch branches name with
  | none => throwErr s!"match: no branch for constructor '{name}' (scrutinee {scrut.name}#{scrut.id})"
  | some br => do
    setSlot scrut .bot                         -- ⇒-consume
    bindFields br.binders fields
    pure br.body

/-- **Borrow mode** (§3.3): the binders become reborrows of the fields. Mint a
    fresh loan ℓᵢ per field, park a `loanM ℓᵢ` in the parent's payload (which
    suspends the parent — no rule reads through a loan), bind each binder to
    `borrowM ℓᵢ fieldᵢ`, and return the branch body. -/
def borrowSelect (scrut : Var) (branches : List Branch) (ℓ : Nat) (name : String)
    (fields : List Val) : M Term := do
  match findBranch branches name with
  | none => throwErr s!"match: no branch for constructor '{name}' (scrutinee {scrut.name}#{scrut.id})"
  | some br => do
    if br.binders.length != fields.length then
      throwErr "match: constructor arity mismatch (borrow mode)"
    let ℓs ← fields.mapM (fun _ => freshLoan)
    setSlot scrut (.borrowM ℓ (.ctor name (ℓs.map Val.loanM)))   -- suspend the parent
    bindBorrowFields br.binders ℓs fields
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
    | .matchE scrut brs => .matchE ⟨scrut.id + d, scrut.name⟩ (shiftBranches d brs)
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
        -- take: read the payload through the borrow, leaving a hole (⊥) in it
        let pos ← placeToPos (.deref t')
        match ← getAtPos pos with
        | .bot => throwErr "readR(*): borrow payload is already a hole (⊥) — nothing to take"
        | p => do setAtPos pos .bot; pure p
      | .ctorApp name args => do
        pure (.ctor name (← readArgs fuel args))
      | .borrow t' => do
        let pos ← placeToPos t'
        match ← getAtPos pos with
        | .bot => throwErr "&mut: target place holds ⊥ (nothing to borrow)"
        | .loanM ℓ => throwErr s!"&mut: target place holds loanₘ ℓ{ℓ} (already borrowed / suspended)"
        | v => do
          let ℓ ← freshLoan
          setAtPos pos (.loanM ℓ)                        -- park the loan marker
          pure (.borrowM ℓ v)                            -- ownership of v moves into the borrow
      | .letIn x rhs rest => do
        let v ← readR fuel rhs
        bindSlot x v
        readR fuel rest
      | .assign place rhs rest => do
        let v ← readR fuel rhs                           -- RHS by ⇒ first (§2.5 ordering)
        writeR fuel place v                              -- target by ⇐
        readR fuel rest
      | .matchE scrut branches => do
        -- Mode is chosen by what the scrutinee's slot holds, after the usual
        -- lazy reorganization. Both retries decrease fuel.
        match ← lookupSlot scrut with
        | .bot => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} holds ⊥ (use-after-move)"
        | .borrowM ℓ payload =>
          match payload with
          | .ctor name fields => do readR fuel (← borrowSelect scrut branches ℓ name fields)
          | .loanM ℓ' => do endLoan fuel ℓ'; readR fuel (.matchE scrut branches)  -- reborrowed payload: end, retry
          | .bot => throwErr s!"match: matching through a hole (⊥) at {scrut.name}#{scrut.id}"
          | .sym _ => throwErr s!"match: symbolic scrutinee {scrut.name}#{scrut.id} in expression position — only a statement-position match may split (use the explore driver)"
          | .borrowM _ _ => throwErr s!"match: scrutinee payload is a nested borrow (unsupported in §3)"
          | _ => throwErr s!"match: scrutinee {scrut.name}#{scrut.id} payload is not a constructor"
        | v =>
          match firstLoanMarker v with
          | some ℓ => do endLoan fuel ℓ; readR fuel (.matchE scrut branches)      -- suspended owner: end, retry
          | none =>
            match v with
            | .ctor name fields => do readR fuel (← ownedSelect scrut branches name fields)
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
            readR fuel (shiftVars offset decl.body)
          else do
            -- CHECKING (§5.3/§6.1): signature only, mint one loan group. The
            -- instantiation `inst` (decl var → actual, §5.3) instantiates the
            -- return and owed types at the actuals this call was given.
            let (captured, inst) ← processArgs fuel 0 [] decl.telescope args
            -- Build the result and the loans it issues from the return type (a
            -- single borrow, a Pair/Σ of borrows for a multi-issued group, or a
            -- plain existential wire). One group ties captured to issued. The
            -- `constrained` flag stays false in real checking — inferring it is
            -- unsound (`through` vs `advance` share a signature); the test-only
            -- `forceConstrained` flag reintroduces the bug for harness validation.
            let (resultVal, issued) ← buildResult fuel inst decl.retType
            let ρ ← freshGroup
            let fc := (← get).forceConstrained
            let cons := fc && captured.length == 1 && issued.length == 1
            -- §6.2: reflect the DECLARED backward spec (if any) at the actuals, so
            -- the group can compute the captured release from the surrendered
            -- values instead of a fresh existential.
            let backV ← match decl.back with
              | some b => do pure (some (← readCWith fuel inst b))
              | none => pure none
            let grp : Group := { id := ρ, captured := captured, issued := issued, constrained := cons, backSpec := backV }
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
      | .type => readC fuel t
      | .const _ => readC fuel t
      | .pvar _ => readC fuel t
      | .pi _ _ => readC fuel t
      | .sigmaT _ _ => readC fuel t
      | .lam _ _ => readC fuel t
      | .app _ _ => readC fuel t
      | .idT _ _ _ => readC fuel t
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
  | ownedSym   : Nat → Dispatch                      -- owned symbolic value sym σ
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
        | .sym σ => pure (.ownedSym σ)
        -- §19: a stuck spine (`leb σ σp`, a neutral application). Generalize it to
        -- a fresh σb : Bool across all σ-bearing state, then split on σb as an
        -- ordinary owned sym — the True/False refinement rewrites the spine per path.
        | .app _ _ => do let σb ← generalizeStuck fuel v; pure (.ownedSym σb)
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

/-- Symbolic **owned** branch entry (§3.2): mint (σ-typed) fresh σ's for the
    pattern fields, ⇜-refine the scrutinee to `C (sym σ₁) … (sym σₙ)`
    *everywhere*, then destructure as owned match (scrutinee → ⊥, binders ↦
    `sym σᵢ`). Returns the branch body. -/
def symOwnedSetup (fuel : Nat) (scrut : Var) (scrutσ : Nat) (br : Branch) : M Term := do
  let σs ← mintFieldSyms fuel scrutσ br
  writeC (.var scrut) (.ctor br.ctor (σs.map Val.sym))   -- ⇜ everywhere (refinement first)
  setSlot scrut .bot                                     -- owned consume
  bindFields br.binders (σs.map Val.sym)
  pure br.body

/-- Symbolic **borrow** branch entry (§3.3): mint fresh σ's, ⇜-refine the
    payload to `C (sym σ₁) … (sym σₙ)` *everywhere* (refinement first), THEN
    reborrow the fields — the scrutinee payload becomes `C (loanM ℓ₁) …`
    (suspended parent), each binder ↦ `borrowM ℓᵢ (sym σᵢ)`. Order matters:
    ⇜ hits every occurrence of σ across Ω; only the scrutinee payload is then
    rewritten to markers (§3.2 "everywhere"; M5 depends on this). -/
def symBorrowSetup (fuel : Nat) (scrut : Var) (ℓ : Nat) (scrutσ : Nat) (br : Branch) : M Term := do
  let σs ← mintFieldSyms fuel scrutσ br
  writeC (.deref (.var scrut)) (.ctor br.ctor (σs.map Val.sym))   -- ⇜ at payload, everywhere
  let ℓs ← br.binders.mapM (fun _ => freshLoan)
  setSlot scrut (.borrowM ℓ (.ctor br.ctor (ℓs.map Val.loanM)))   -- suspend the parent
  bindBorrowFields br.binders ℓs (σs.map Val.sym)
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
      | .matchE s bs =>
        let k := pushContinuations rest
        .matchE s (bs.map (fun br => Branch.mk br.ctor br.binders (.letIn x br.body k)))
      | rhs' => .letIn x rhs' (pushContinuations rest)
    | .seq e rest =>
      match pushContinuations e with
      | .matchE s bs =>
        let k := pushContinuations rest
        .matchE s (bs.map (fun br => Branch.mk br.ctor br.binders (.seq br.body k)))
      | e' => .seq e' (pushContinuations rest)
    | .assign p rhs rest => .assign p rhs (pushContinuations rest)
    | .matchE s bs => .matchE s (pushBranches bs)
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
      | .matchE scrut branches => exploreMatch fuel scrut branches st
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
  def exploreMatch : Nat → Var → List Branch → St → List (Except String (Val × St))
    | fuel, scrut, branches, st =>
      match (reorgScrut fuel scrut).run st with
      | .error e _ => [.error e]
      | .ok disp st' =>
        match disp with
        | .ownedCtor name fields =>
          match (ownedSelect scrut branches name fields).run st' with
          | .error e _ => [.error e]
          | .ok body st'' => explore fuel body st''
        | .borrowCtor ℓ name fields =>
          match (borrowSelect scrut branches ℓ name fields).run st' with
          | .error e _ => [.error e]
          | .ok body st'' => explore fuel body st''
        | .ownedSym σ =>
          match (checkExhaustive fuel σ branches).run st' with
          | .error e _ => [.error e]
          | .ok _ st'' => exploreSymBranches fuel scrut false 0 σ branches st''
        | .borrowSym ℓ σ =>
          match (checkExhaustive fuel σ branches).run st' with
          | .error e _ => [.error e]
          | .ok _ st'' => exploreSymBranches fuel scrut true ℓ σ branches st''
  termination_by fuel _ _ _ => (fuel, 2, 0)
  /-- One symbolic path per branch, in declaration order. `borrow` selects the
      setup; `ℓ` is the parent loan (borrow mode only); `σ` is the scrutinee's
      symbolic id (used to type the field σ's). -/
  def exploreSymBranches : Nat → Var → Bool → Nat → Nat → List Branch → St → List (Except String (Val × St))
    | _, _, _, _, _, [], _ => []
    | fuel, scrut, borrow, ℓ, σ, br :: rest, st =>
      (match ((if borrow then symBorrowSetup fuel scrut ℓ σ br else symOwnedSetup fuel scrut σ br)).run st with
       | .error e _ => [.error e]
       | .ok body st' => explore fuel body st')
      ++ exploreSymBranches fuel scrut borrow ℓ σ rest st
  termination_by fuel _ _ _ _ branches _ => (fuel, 1, branches.length)
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
