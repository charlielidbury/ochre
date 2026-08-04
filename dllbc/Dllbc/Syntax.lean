/-!
# DLLBC Syntax (concrete runtime, §2)

One inductive `Term` for the whole grammar of the doc (§1.1), but we declare
only the forms the §2 concrete machine needs right now:

  * variable occurrence,
  * `let x = t ; rest`,
  * `t := t' ; rest` (assignment),
  * constructor application (constructor names as `String` for now —
    `inductive` declarations arrive in a later milestone),
  * `&mut t` (mutable borrow),
  * `*t` (dereference),
  * a unit / terminal form for statement sequences.

The λ / application / Π / `Type` / `match` forms of §1.1 join in later
milestones (§3 match, §5 boundaries, §7 inductives).

## Runtime variables carry globally-unique ids

A runtime variable is a `Nat` id (globally unique, minted by the `dllbc{…}`
macro at elaboration time) paired with a display `String`. There is **no**
de Bruijn indexing in the machine layer and **no** shifting anywhere — the
macro resolves names to ids while elaborating, and an unresolved name is an
elaboration-time error (mirroring `Och/Macro.lean`'s discipline that killed
the silent-999 sentinel bug). The environment Ω is then keyed by these ids,
so shadowing is a fresh id, never a name clash.
-/

namespace Dllbc

/-- A runtime variable: a globally-unique `id` plus a display `name`. -/
structure Var where
  id : Nat
  name : String
deriving DecidableEq, BEq, Repr, Inhabited

/-- Does this identifier start with an uppercase letter? **The mode marker**
    (combining-fns §6): a capitalized binder is COMPTIME, a lowercase one is
    RUNTIME. Lives here rather than in the macro layer because the kernel reads
    it — see `Var.isComptime`. -/
def isUpperInit (s : String) : Bool :=
  match s.data with
  | c :: _ => c.isUpper
  | [] => false

/-- **The mode of a runtime binder is its name's case** (combining-fns §6).

    A capitalized binder — a telescope parameter `Hfuel`, a `let X = …`, a match
    field binder — is **comptime**: its argument is ⇝-read at the call (pure,
    non-consuming), it is erased, and it is usable only in ⇝-positions. A
    lowercase binder is runtime, as everything was before.

    Why the name and not a field: this calculus's runtime binders are `(id,
    name)` pairs with globally-unique ids, so the name is *where the binder
    records its identity* — and §6's surface convention IS the case, backed by
    reserving the constructor names (`Val.ctorNames`) so that capitalisation
    cannot mean anything else. A `mode` field would be a second source of truth
    that a hand-written `⟨0, "Hfuel"⟩` could silently contradict; derived from
    the name there is only one, and `shiftVars`/`renumber` preserve it for free.
    Pure (de Bruijn) binders have no name, so they carry their mode on the
    domain instead — `Term.cmpT` below. -/
def Var.isComptime (x : Var) : Bool := isUpperInit x.name

/-! Core term syntax of DLLBC's concrete fragment (§2 forms plus §3 `match`).

    Constructor names are `String`s (a placeholder until `inductive`
    declarations arrive). Numeric literals are macro-level sugar for
    `S (S (… Z))` and so need no dedicated term form.

    `Term` is mutual with `Branch` for the `match` case. The scrutinee of a
    match is a `Var` (grammar-enforced, §3: "the scrutinee must be a
    variable"); patterns are one constructor deep. -/
mutual
inductive Term where
  /-- Variable occurrence. Under ⇒ this is a *move*. -/
  | var    : Var → Term
  /-- `let x = rhs ; rest` — bind `x` to the ⇒-value of `rhs`, then run `rest`. -/
  | letIn  : Var → Term → Term → Term
  /-- `place := rhs ; rest` — ⇒-read `rhs`, ⇐-write it into `place`, then `rest`.
      `place` is syntactically an arbitrary `Term`; ⇐ is only *defined* on
      place shapes (a variable under zero or more `*` peels). -/
  | assign : Term → Term → Term → Term
  /-- Constructor application `C(a, b, …)`; nullary `C` is `ctorApp C []`. -/
  | ctorApp : String → List Term → Term
  /-- `&mut t` — mint a loan; `&mut *x` is reborrow. -/
  | borrow : Term → Term
  /-- `*t` — the peel. Arrow-generic in the doc; here used under ⇒ (take)
      and ⇐ (write-through / locate). -/
  | deref  : Term → Term
  /-- `t[i | ev]` — the **index step** (¶2.1), arrow-generic exactly as `*` is. The
      payload at an index place is the ELEMENT (type `T`), not an `Array 1 T`, which
      is what spares every element access a coercion. `ev` is the cited containment
      evidence, `none` when the bound computes (¶3.2's supply route 1). -/
  | index  : Term → Term → Option Term → Term
  /-- `t[lo ; cnt | ev]` — the **range step** (¶2.1). Offset-and-count, never
      lower-and-upper: `a[lo ; cnt]` has type `Array cnt T` read straight off the
      syntax, so no rule below ever produces a `sub`.

      The count is OPTIONAL: `a[lo ; ..]` means "to the end of the segment starting
      at `lo`". That is not sugar for a subtraction — it NAMES the residue the carve
      already minted (premise (3)'s `rest`, sitting in the extent map as a given)
      rather than computing `sub n lo`. ¶3.4 and ¶5 both write `rest` as if it were a
      surface name for that σ, and it is not one; this is how a program says it.

      The **residue** is optional too: `a[lo ; cnt ; rest | h]` SUPPLIES the extent of
      what is left over instead of letting premise (3) mint an unnameable σ for it.
      Same solution transition, same absence of `sub`; the equation is simply solved
      against a term the program wrote. Omit it and the checker mints, exactly as
      before. This is the third instance of a house pattern — an optional surface
      element reifying something the checker already knows, declared rather than
      inferred, free when absent — after §1.2's `[k]` naming the decreasing position
      and §3.2's `match h :` naming the branch equation.

      The last slot is the **decomposition citation**, `a[lo ; cnt ; rest | h | heq]`.
      A supplied residue asserts a specific decomposition of the leaf's extent, and
      when that extent is a telescope parameter's σ the assertion is a constraint on
      the function's CALLERS. Premise (3) may not impose it by unification — that is
      M7/M8's signature-inferred constrained wire, whose lesson (M17) is that
      cross-boundary constraints must be DECLARED and checked. So the program cites
      `heq : Id Nat ⟨leaf extent⟩ (add cnt rest)` and premise (3) solves along it: a
      checked identity with recorded provenance is legitimate ⇜ knowledge, where an
      unrecorded unification against a universal is not. Needed only when the
      decomposition does not already hold by conversion. -/
  | range  : Term → Term → Option Term → Option Term → Option Term → Option Term → Term
  /-- `match x { … }` — one-constructor-deep pattern match on a variable
      scrutinee (§3). Owned or borrow mode is chosen at runtime by what the
      scrutinee's slot holds.

      The `Option Var` is the **branch-equation binder** (M23), the surface
      `match h : x { … }`: when present, every branch additionally binds `h` to
      a proof of `Id τ ⟨the scrutinee's pre-split value⟩ ⟨this branch's
      constructor⟩`. One name for the whole match (its *type* is what varies per
      branch), exactly as in Lean's `match h : x with`. `none` is the plain
      form — nothing extra is bound and nothing is minted. -/
  | matchE : Var → Option Var → List Branch → Term
  /-- `e ; rest` — expression statement: ⇒-evaluate `e` for effect, discard
      its value, then run `rest`. Sequences a `match` (or any effectful term)
      used in statement position without binding a throwaway slot. -/
  | seq    : Term → Term → Term
  /-- `f(a, …)` — a call to a declared function (§5.3), checked against the
      signature alone. Unifying `fn` with λ is deferred (§10). -/
  | call   : String → List Term → Term
  /-- `.seal t u` — **opacity as syntax** (combining-fns §5). Programmer-invoked
      generalization: "forget everything about this value except its type".

        * EXECUTING (⇒, concrete): evaluate `t`. Execution is always transparent.
        * CHECKING (⇒, symbolic): verify `t : u` ONCE, at the node — this check
          *is* the audit — then yield a fresh `σ : u`. Everything downstream sees
          only the type.

      **Absent from the comptime fragment by construction, in the two places that
      carry the risk.** (i) It is its OWN constructor, not an `.app` of a magic
      `.const` (the route `@exit`/`old` take): ⇝'s application rule can therefore
      never meet it, and no check inside that rule distinguishes it. (ii) There is
      no `Val.seal` — every comptime rule (`whnfV`, `nfV`, `convert`, `substPure`,
      `hasType`) is a function on `Val`, so *no comptime rule for the seal exists
      or can be written* without adding a value former. That is what makes §2.1's
      question unaskable: minting needs an event, ⇝ has none, and ⇝ has no seal to
      mint at. `reflectC` rejects the node in the one uniform way it already
      rejects `&mut`, `:=`, `;` and `f(…)` — "not in the comptime fragment" — which
      is this calculus's standing definition of the pure sub-grammar (§1.3), not a
      mode flag consulted at runtime. -/
  | seal   : Term → Term → Term
  /-- `x(a, …)` — **application of a value callee** (combining-fns §7 cost 2):
      the callee is resolved from a runtime SLOT, not the declaration table. The
      slot's contents decide the rule (`readR`):

        * a literal λ — bind and run (β), both modes: body known ⟹ unfold;
        * a `σ : Π` — checking only: abstract application at the Π, minting the
          result from the instantiated return type (§2.3's runtime column, §12
          decision 5 — runtime calls do not opt into remembered-spine semantics).

      Application is **saturated** (§12 decision 4): a spine, consumed whole like
      a telescope, so no partial application ever holds a borrow while awaiting an
      argument. Under-application is rejected distinctively, not curried. The
      callee is a `Var` because that is all §7 needs (`ih` is a bound variable) and
      it keeps the form's shape identical to `.matchE`'s scrutinee. -/
  | callV  : Var → List Term → Term
  /-- Terminal form, the value a statement sequence returns when it has no
      final expression. -/
  | unit   : Term
  -- Pure fragment (§4): the comptime type theory's formers. Pure binders use
  -- de Bruijn indices (`pvar`); `readC` (⇝) reflects these into the matching
  -- `Val` forms and reduces. Runtime `var`/`let` (named ids) are unaffected.
  | pvar   : Nat → Term              -- pure de Bruijn variable
  | type   : Term                    -- the universe
  | pi     : Term → Term → Term      -- Π (dom) (cod); cod binds var 0
  | sigmaT : Term → Term → Term      -- Σ (fst-type) (snd-type); snd binds var 0
  | lam    : Term → Term → Term      -- λ (dom) (body); body binds var 0
  | app    : Term → Term → Term      -- application
  | const  : String → Term           -- a built-in constant (recursor or type former)
  | idT    : Term → Term → Term → Term  -- Id A a b (§10): the identity type
  /-- The borrow type `&mut (s : τ ↝ S)` (§5.1): exclusive access to a `τ`,
      owing an `S` at the boundary. `S` is under one pure de Bruijn binder for
      the entry snapshot `s`. Plain `&mut τ` is `borrowT τ (weaken τ)`. Only
      valid at a telescope position — interpreted by `checkFn`'s seeding, never
      reflected as a value. -/
  | borrowT : Term → Term → Term
  /-- `⇝τ` — the **comptime binder-mode marker on a domain** (combining-fns §6),
      and the pure-binder counterpart of `Var.isComptime`.

      `Π (X : τ) → …` elaborates to `.pi (.cmpT τ) …` and `λ (X : τ). …` to
      `.lam (.cmpT τ) …`. It is legal ONLY as a λ/Π domain — the same standing
      as `borrowT`, which is likewise a binder-mode marker written in type
      position and not a type. `&mut τ` says "this binder is a runtime borrow";
      `⇝τ` says "this binder is comptime"; a bare `τ` says "runtime owned". Three
      modes, one syntactic place, and the two that are not the default are
      marked.

      **Case is inert under ⇝** (§6), and that is mechanical here rather than
      incidental: `Val.beq` unwraps `cmpT` on either side, so conversion — and
      therefore every comptime judgment built on it — cannot see a mode at all.
      What CAN see it is ⇒: the application rules read the binder's mode off the
      callee's λ/Π to decide which arrow evaluates the argument. Same room, two
      doors (§2.3). -/
  | cmpT   : Term → Term
/-- A match branch: a constructor name, one-level-deep field binders (display
    names carrying fresh runtime ids), and a body term. -/
inductive Branch where
  | mk : (ctor : String) → (binders : List Var) → (body : Term) → Branch
end

-- Manual instances: `deriving` can't cross the `List Term`/`List Branch`
-- nesting, and nothing in the machine needs term equality (the macro produces
-- terms; tests compare *values*).
instance : Inhabited Term := ⟨.unit⟩
instance : Inhabited Branch := ⟨.mk "" [] .unit⟩

/-- The branch's constructor name. -/
def Branch.ctor : Branch → String | .mk c _ _ => c
/-- The branch's field binders. -/
def Branch.binders : Branch → List Var | .mk _ b _ => b
/-- The branch's body. -/
def Branch.body : Branch → Term | .mk _ _ t => t

/-! ## Structural term equality (manual; `deriving` can't cross the nesting) -/

mutual
  def Term.beq : Term → Term → Bool
    | .var x, .var y => x == y
    | .letIn x a b, .letIn y c d => x == y && Term.beq a c && Term.beq b d
    | .assign a b c, .assign d e f => Term.beq a d && Term.beq b e && Term.beq c f
    | .ctorApp n as, .ctorApp m bs => n == m && Term.beqList as bs
    | .borrow a, .borrow b => Term.beq a b
    | .deref a, .deref b => Term.beq a b
    | .index a i e, .index b j f => Term.beq a b && Term.beq i j && Term.beqOpt e f
    | .range a l c r e eq1, .range b m d q f eq2 =>
      Term.beq a b && Term.beq l m && Term.beqOpt c d && Term.beqOpt r q
        && Term.beqOpt e f && Term.beqOpt eq1 eq2
    | .matchE x e as, .matchE y f bs => x == y && e == f && Term.beqBranches as bs
    | .seq a b, .seq c d => Term.beq a c && Term.beq b d
    | .call f as, .call g bs => f == g && Term.beqList as bs
    | .seal a b, .seal c d => Term.beq a c && Term.beq b d
    | .callV x as, .callV y bs => x == y && Term.beqList as bs
    | .unit, .unit => true
    | .pvar k, .pvar j => k == j
    | .type, .type => true
    | .pi a b, .pi c d => Term.beq a c && Term.beq b d
    | .sigmaT a b, .sigmaT c d => Term.beq a c && Term.beq b d
    | .lam a b, .lam c d => Term.beq a c && Term.beq b d
    | .app a b, .app c d => Term.beq a c && Term.beq b d
    | .const n, .const m => n == m
    | .idT a b c, .idT d e f => Term.beq a d && Term.beq b e && Term.beq c f
    | .borrowT a b, .borrowT c d => Term.beq a c && Term.beq b d
    -- STRUCTURAL, unlike `Val.beq` — the asymmetry is deliberate. `Val.beq` is
    -- mode-blind because `convert` is built on it and §6 says case is inert
    -- under ⇝. `Term.beq` is not a conversion: its clients are `absOcc` (§18's
    -- occurrence abstraction) and `Decl.alphaEq` (the macro-vs-corpus round-trip
    -- criterion), and BOTH want to see a mode. A mode-blind `alphaEq` would let
    -- phase D's `fn` macro emit a differently-moded `Decl` and still report
    -- equivalence; a mode-blind `absOcc` would match `⇝τ` against `τ` and
    -- abstract away the marker along with the domain.
    | .cmpT a, .cmpT b => Term.beq a b
    | _, _ => false
  termination_by t u => sizeOf t + sizeOf u
  def Term.beqList : List Term → List Term → Bool
    | [], [] => true
    | a :: as, b :: bs => Term.beq a b && Term.beqList as bs
    | _, _ => false
  termination_by ts us => sizeOf ts + sizeOf us
  def Term.beqOpt : Option Term → Option Term → Bool
    | none, none => true
    | some a, some b => Term.beq a b
    | _, _ => false
  termination_by ts us => sizeOf ts + sizeOf us
  def Term.beqBranches : List Branch → List Branch → Bool
    | [], [] => true
    | .mk c bs a :: r, .mk d es b :: s => c == d && bs == es && Term.beq a b && Term.beqBranches r s
    | _, _ => false
  termination_by ts us => sizeOf ts + sizeOf us
end

instance : BEq Term := ⟨Term.beq⟩

/-! ## Pure de Bruijn shift on `Term` (mirror of `Val.shiftPure`), and syntactic
    subterm abstraction — the §18 rewriting layer's mechanism. -/

mutual
  def Term.shiftPure (d c : Nat) : Term → Term
    | .pvar k => if k < c then .pvar k else .pvar (k + d)
    | .lam dom b => .lam (Term.shiftPure d c dom) (Term.shiftPure d (c + 1) b)
    | .pi dom cod => .pi (Term.shiftPure d c dom) (Term.shiftPure d (c + 1) cod)
    | .sigmaT dom cod => .sigmaT (Term.shiftPure d c dom) (Term.shiftPure d (c + 1) cod)
    | .app f a => .app (Term.shiftPure d c f) (Term.shiftPure d c a)
    | .ctorApp n args => .ctorApp n (Term.shiftPureList d c args)
    | .idT a b b' => .idT (Term.shiftPure d c a) (Term.shiftPure d c b) (Term.shiftPure d c b')
    | .cmpT τ => .cmpT (Term.shiftPure d c τ)            -- a domain: same binder depth
    | t => t                                             -- runtime forms / leaves
  termination_by t => sizeOf t
  def Term.shiftPureList (d c : Nat) : List Term → List Term
    | [] => []
    | t :: ts => Term.shiftPure d c t :: Term.shiftPureList d c ts
  termination_by ts => sizeOf ts
end

/-! Abstract every occurrence of `e` at binder `depth` (mutual with the ctor-arg
    list helper). `e` is shifted under each binder crossed; a match replaces it
    with `pvar depth`; a free pure variable is lifted to make room. -/
mutual
  def absOcc (e : Term) (depth : Nat) : Term → Term
    | .lam dom b =>
      if Term.beq (.lam dom b) (Term.shiftPure depth 0 e) then .pvar depth
      else .lam (absOcc e depth dom) (absOcc e (depth + 1) b)
    | .pi dom cod =>
      if Term.beq (.pi dom cod) (Term.shiftPure depth 0 e) then .pvar depth
      else .pi (absOcc e depth dom) (absOcc e (depth + 1) cod)
    | .sigmaT dom cod =>
      if Term.beq (.sigmaT dom cod) (Term.shiftPure depth 0 e) then .pvar depth
      else .sigmaT (absOcc e depth dom) (absOcc e (depth + 1) cod)
    | .app f a =>
      if Term.beq (.app f a) (Term.shiftPure depth 0 e) then .pvar depth
      else .app (absOcc e depth f) (absOcc e depth a)
    | .idT a b c =>
      if Term.beq (.idT a b c) (Term.shiftPure depth 0 e) then .pvar depth
      else .idT (absOcc e depth a) (absOcc e depth b) (absOcc e depth c)
    | .ctorApp n args =>
      if Term.beq (.ctorApp n args) (Term.shiftPure depth 0 e) then .pvar depth
      else .ctorApp n (absOccList e depth args)
    -- A mode marker is never itself an abstraction target (it is not a term),
    -- so recurse straight through rather than testing it.
    | .cmpT τ => .cmpT (absOcc e depth τ)
    | .pvar k =>
      if Term.beq (.pvar k) (Term.shiftPure depth 0 e) then .pvar depth
      else .pvar (if k < depth then k else k + 1)
    | s => if Term.beq s (Term.shiftPure depth 0 e) then .pvar depth else s   -- leaves
  termination_by s => sizeOf s
  def absOccList (e : Term) (depth : Nat) : List Term → List Term
    | [] => []
    | s :: ss => absOcc e depth s :: absOccList e depth ss
  termination_by ss => sizeOf ss
end

/-- Abstract every occurrence of `e` in `t` by a fresh de Bruijn binder.
    `Term.lam τ (abstractOccurrences e t)` applied to `e` β-reduces back to `t`.
    The §18 motive-generalization mechanism: no matching by eye, no missed
    occurrence. -/
def abstractOccurrences (e t : Term) : Term := absOcc e 0 t

/-- Does a type contain a borrow anywhere? A borrow-carrying return type (a
    `&mut`, or a `Pair` of them) is audited structurally by
    `collectResultBorrows`, never reflected, so it must NOT be pinned/`readC`'d
    (which rejects `borrowT`). The seal rule (M26-A) asks the same question of its
    ascribed type, which is why this sits in the syntax layer rather than in
    `Boundary` where it was born — `Machine` cannot import `Boundary`. -/
def hasBorrowT : Term → Bool
  | .borrowT _ _ => true
  | .sigmaT a b => hasBorrowT a || hasBorrowT b
  | .pi a b => hasBorrowT a || hasBorrowT b
  | .app a b => hasBorrowT a || hasBorrowT b
  | .lam a b => hasBorrowT a || hasBorrowT b
  | .idT a b c => hasBorrowT a || hasBorrowT b || hasBorrowT c
  | .cmpT τ => hasBorrowT τ
  | _ => false

/-! ## Reading a binder's mode off its domain (combining-fns §6)

    Three modes at one syntactic place: `&mut τ` runtime-borrow, `⇝τ` comptime,
    bare `τ` runtime-owned. These two are how every ⇒-rule asks which it has. -/

/-- Is this λ/Π domain a COMPTIME binder's — i.e. written with a capital name? -/
def Term.domComptime : Term → Bool
  | .cmpT _ => true
  | _ => false

/-- The domain proper, with the mode marker peeled. `⇝τ` is not a type; a value
    inhabits it exactly when it inhabits `τ`, so every rule that *types* an
    argument strips first and every rule that *routes* one asks `domComptime`. -/
def Term.stripCmp : Term → Term
  | .cmpT τ => τ
  | t => t

end Dllbc
