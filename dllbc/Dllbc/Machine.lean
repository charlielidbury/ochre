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
  /-- Identity-wire flag (§6.2). DEAD under opaque calls: signature-only
      checking cannot tell `through` from an `advance` that returns a field
      reborrow, so inferring it is UNSOUND — no call sets it. Kept, with its
      `endGroup` branch, for §6.2's transparent/spec group ends. -/
  constrained : Bool

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
  termination_by v => sizeOf v
  def substSymList (σ : Nat) (newV : Val) : List Val → List Val
    | [] => []
    | v :: vs => substSym σ newV v :: substSymList σ newV vs
  termination_by vs => sizeOf vs
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

/-- **⇜ (comptime write / refinement)** — the doc's ⇜, signature parallel to
    `writeR`. Defined on the same place shapes (a variable under peels). The
    place must currently hold a symbolic value `sym σ` (reached through borrow
    payloads by the peels); the effect is **global substitution** — every
    occurrence of `sym σ` in *every* slot of Ω is replaced by `refined`
    (§3.2's "everywhere"). Minting fresh σ's is the caller's job. Errors
    distinctively if the place holds anything other than a `sym`. -/
def writeC (place : Term) (refined : Val) : M Unit := do
  let pos ← placeToPos place
  match ← getAtPos pos with
  | .sym σ => modify (fun s => { s with env := s.env.map (fun kv => (kv.1, substSym σ refined kv.2)) })
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
    | .unit => pure (.ctor "unit" [])
    | .letIn _ _ _ => throwErr "readC (⇝): pure `let` not implemented (no test needs it this milestone)"
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

/-! Value typing (§4), the future audit's engine. `sym σ` is typed by `sctx`
    and conversion; a constructor value by the signature table, checking each
    field against its (dependently instantiated) type; a type former inhabits
    the universe. Cases no test forces error distinctively (M5 grows them). -/
mutual
  def hasType : Nat → Val → Val → M Bool
    | 0, _, _ => throwErr "hasType: out of fuel"
    | fuel + 1, v, ty => do
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
      | _ => throwErr s!"hasType: cannot type value {v.pretty} (λ/neutral typing deferred to M5)"
  termination_by fuel _ _ => (fuel, 0, 0)
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
  match grp.constrained, grp.captured, surrendered with
  | true, [(ℓc, _)], [p] => releaseCaptured ℓc p          -- identity wire: recover the written value
  | _, _, _ =>
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
          | none => do setSlot x .bot; pure v            -- move out, leave ⊥
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
        -- §5.3/§6.1: check the call against the SIGNATURE alone (never another
        -- body), and mint one loan group tying captured to issued.
        match (← get).decls.find? (fun d => d.name == f) with
        | none => throwErr s!"call: unknown function '{f}'"
        | some decl => do
          let captured ← processArgs fuel decl.telescope args   -- (ℓ × owed) per argument borrow
          match decl.retType with
          | .borrowT τ S => do
            -- borrow-returning (§6.1): result is a fresh reborrow; its loan is
            -- issued, owed the return type. OPAQUE — `constrained := false`
            -- always: signature-only checking cannot see whether the callee is
            -- the identity, so inferring the constrained wire would be unsound
            -- (`through` vs `advance` share this signature). §6.2 recovers it.
            let τVal ← readC fuel τ
            let σ ← freshSym
            let ℓr ← freshLoan
            let ρ ← freshGroup
            let owedR := Val.nfV fuel (Val.substPure 0 (Val.sym σ) (← readC fuel S))
            let grp : Group := { id := ρ, captured := captured, issued := [(ℓr, owedR)], constrained := false }
            modify (fun s => { s with sctx := (σ, τVal) :: s.sctx, groups := grp :: s.groups })
            pure (.borrowM ℓr (.sym σ))
          | _ => do
            -- value-returning: a fresh σ at the return type; degenerate group.
            let retTy ← readC fuel decl.retType
            let σ ← freshSym
            let ρ ← freshGroup
            let grp : Group := { id := ρ, captured := captured, issued := [], constrained := false }
            modify (fun s => { s with sctx := (σ, retTy) :: s.sctx, groups := grp :: s.groups })
            pure (.sym σ)
      | .unit => pure (.ctor "unit" [])
      | _ => throwErr "readR (⇒): pure formers (λ/app/Π/Σ/Type/const) are read by ⇝ (readC), not ⇒"
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
  def processArgs : Nat → List (String × Term) → List Term → M (List (Nat × Val))
    | _, [], [] => pure []
    | fuel, (_, tyTerm) :: tRest, arg :: aRest => do
      match tyTerm with
      | .borrowT τ S => do
        match ← readR fuel arg with
        | .borrowM ℓ payload => do
          let τVal ← readC fuel τ
          if ← hasType fuel payload τVal then do
            let owed := Val.nfV fuel (Val.substPure 0 payload (← readC fuel S))
            pure ((ℓ, owed) :: (← processArgs fuel tRest aRest))
          else
            throwErr s!"call: borrow argument's payload ({payload.pretty}) does not have its parameter type ({τVal.pretty})"
        | v => throwErr s!"call: expected a borrow argument (&mut …), got {v.pretty}"
      | tyTerm => do
        let argVal ← readR fuel arg
        let τVal ← readC fuel tyTerm
        if ← hasType fuel argVal τVal then processArgs fuel tRest aRest
        else throwErr s!"call: argument ({argVal.pretty}) does not have its parameter type ({τVal.pretty})"
    | _, _, _ => throwErr "call: arity mismatch (arguments vs telescope)"
  termination_by fuel _ args => (fuel, 1, args.length)
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

/-- Mint the field σ's for a symbolic branch. When the scrutinee's σ has a type
    in `sctx` (§3.2's seam, closed in §5): require the branch constructor to be
    a constructor of that type (per the signature table) and type each field σ
    by the instantiated field types. When it has no type (an untyped testing
    scrutinee, pre-telescope), fall back to fresh untyped σ's (M3 behavior). -/
def mintFieldSyms (fuel : Nat) (scrutσ : Nat) (br : Branch) : M (List Nat) := do
  match (← get).sctx.lookup scrutσ with
  | none => br.binders.mapM (fun _ => freshSym)     -- untyped scrutinee (M3)
  | some τ =>
    match Val.ctorSig br.ctor with
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
        | .ownedSym σ => exploreSymBranches fuel scrut false 0 σ branches st'
        | .borrowSym ℓ σ => exploreSymBranches fuel scrut true ℓ σ branches st'
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
