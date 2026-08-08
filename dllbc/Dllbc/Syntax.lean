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

A runtime variable is a `Nat` id (globally unique, minted by the surface macros
at elaboration time) paired with a display `String`. There is **no**
de Bruijn indexing in the machine layer and **no** shifting anywhere — the
macro resolves names to ids while elaborating, and an unresolved name is an
elaboration-time error (mirroring `Och/Macro.lean`'s discipline that killed
the silent-999 sentinel bug). The environment Ω is then keyed by these ids,
so shadowing is a fresh id, never a name clash.

## Pure variables carry SOURCE NAMES (M30 step 2, `docs/nbe.md` §5)

And so, since M30 step 2, does the comptime fragment: `lam`/`pi`/`sigmaT` and
`borrowT`'s snapshot binder each carry the name they were written with, an
occurrence is `pvar "x"`, and lookup-the-nearest-binding is the scope rule.
Shadowing is that mechanism rather than a hazard — `λ (x : τ). λ (x : υ). x`
means the inner one — and nothing gensyms.

The de Bruijn indices this replaces were a compensation for SUBSTITUTION, which
M30 step 1 deleted: an evaluator that carries an environment to a body never
transplants one, so there is no capture to arithmetic away. What is left of the
compensation — `shiftPure`, and `substPure`'s index juggling — is deleted here.
-/

namespace Dllbc

/-! ## The reserved binder namespace

    Names beginning with `§` are the machine's. A Lean `ident` cannot contain
    `§` (it is neither a letter nor letter-like), and every surface binder is an
    `ident`, so **no program can write one** — which is what lets the kernel mint
    binders (readback's canonical names, `abstractOccurrences`' fresh variable,
    a plain `&mut τ`'s unused snapshot binder) without a freshness search and
    without a capture check. The surface already relied on this for
    `Surface.shadowedName`; M30 step 2 makes it a stated convention. -/

/-- Is this a machine-minted binder name — one no source program can write? -/
def isReservedName (s : String) : Bool := s.startsWith "§"

/-- **Readback's binder at level `d`.** Deterministic in the level and nothing
    else, which is what keeps readback output CANONICAL: two α-variant functions
    read back to literally the same tree, so conversion stays structural equality
    on normal forms (`Val.convert`). A gensym counter here would be correct and
    would destroy that. -/
def readbackName (d : Nat) : String := "§" ++ toString d

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
  /-- `λ(x : τ, y : υ, …) { body }` — **the runtime λ** (combining-fns §7 cost 2), the
      form phase A filed and could not build: a λ whose body is a *body* (writes,
      calls, borrows, matches) rather than a pure term.

      Its binders are **named runtime `Var`s**, not de Bruijn, and that is forced
      rather than chosen: a body reaches its binders through Ω — `.matchE`
      scrutinizes a `Var`, `&mut x` roots a place at a `Var`, `.callV` calls a
      `Var` — and a de Bruijn index names no slot. So the pure λ (`.lam`, domain-
      annotated, body a `Val`) and this one are the two halves §7 cost 5 predicts:
      same former in the document, two representations in the machine, because
      one substitutes and the other binds.

      **Church-style: every binder carries its domain** (M27, the ratified
      function model), which is what the document's grammar said all along —
      `λ (x : τ). t`. M26-C built the Curry form on the argument that an
      annotation would be a second source of truth for the contract, since a
      runtime λ is checked against an *ascription* (the seal's Π, §5) and §5
      point 4 makes the ascription the contract. That argument is sound about the
      CONTRACT and wrong about the CHECK: without domains the seal has to descend
      the ascription bidirectionally, handing each binder the type the Π supplies,
      and with them the seal is ONE conversion — synthesize the λ's Π, compare it
      against what was written. The ascription stays the contract; what changes is
      that the λ can now be read on its own.

      The `Val` side does NOT follow (`Val.rfn`, `Value.lean`), and the asymmetry
      is the erasure principle rather than an oversight: `readR` drops the domains
      when it forms the value, because the executing machine binds and runs and
      never converts. Types are for the seal, which happens once, at formation.

      **Saturated** (§12 decision 4) and **closed** (§7 cost 2's "arms reference
      only their own binders and globals"). Closedness is CHECKED where the value
      is formed, not assumed: an escaping free variable would otherwise be
      silently captured by the frame shift. -/
  | lamR   : List (Var × Term) → Term → Term
  /-- Terminal form, the value a statement sequence returns when it has no
      final expression. -/
  | unit   : Term
  -- Pure fragment (§4): the comptime type theory's formers. Pure binders carry
  -- their SOURCE NAME (M30 step 2); `readC` (⇝) reflects these into the matching
  -- `Val` forms and reduces. Runtime `var`/`let` (named ids) are unaffected.
  | pvar   : String → Term           -- pure variable occurrence, by name
  | type   : Term                    -- the universe
  | pi     : String → Term → Term → Term      -- Π (x : dom) → cod
  | sigmaT : String → Term → Term → Term      -- Σ (x : fst-type) → snd-type
  | lam    : String → Term → Term → Term      -- λ (x : dom). body
  | app    : Term → Term → Term      -- application
  | const  : String → Term           -- a built-in constant (recursor or type former)
  | idT    : Term → Term → Term → Term  -- Id A a b (§10): the identity type
  /-- The borrow type `&mut (s : τ ↝ S)` (§5.1): exclusive access to a `τ`,
      owing an `S` at the boundary. `S` is under one pure binder named `s`, the
      entry snapshot. Plain `&mut τ` is `borrowT ⟨a reserved name⟩ τ τ` — under
      names the weakening the de Bruijn spelling needed is the identity. Only
      valid at a telescope position — interpreted by the seeding that
      `checkRFnBody` runs (`seedTelescopeV`), never reflected as a value. -/
  | borrowT : String → Term → Term → Term
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
    -- The binder DOMAINS are compared by `Term.beq`, not by `==`: the `BEq Term`
    -- instance is declared below this mutual block, so `==` on a
    -- `List (Var × Term)` would not resolve to this function even if it resolved
    -- at all. Recursing explicitly also keeps the mode marker visible, which is
    -- the property the `.cmpT` note at the foot of this function is about.
    | .lamR xs a, .lamR ys b => Term.beqBinders xs ys && Term.beq a b
    | .unit, .unit => true
    | .pvar x, .pvar y => x == y
    | .type, .type => true
    -- Binder NAMES are compared, which makes this equality up-to-nothing rather
    -- than up-to-α. That is what its clients want: `absOcc` (§18's occurrence
    -- abstraction) matches a subterm written in one scope against the same scope,
    -- and two terms that differ only in a binder's spelling are two different
    -- pieces of source. Conversion, which must be up to α, is `Val.convert` —
    -- `nfV a == nfV b` — and readback canonicalizes every binder to its level
    -- before that comparison ever happens.
    | .pi x a b, .pi y c d => x == y && Term.beq a c && Term.beq b d
    | .sigmaT x a b, .sigmaT y c d => x == y && Term.beq a c && Term.beq b d
    | .lam x a b, .lam y c d => x == y && Term.beq a c && Term.beq b d
    | .app a b, .app c d => Term.beq a c && Term.beq b d
    | .const n, .const m => n == m
    | .idT a b c, .idT d e f => Term.beq a d && Term.beq b e && Term.beq c f
    | .borrowT x a b, .borrowT y c d => x == y && Term.beq a c && Term.beq b d
    -- STRUCTURAL, unlike `Val.beq` — the asymmetry is deliberate. `Val.beq` is
    -- mode-blind because `convert` is built on it and §6 says case is inert
    -- under ⇝. `Term.beq` is not a conversion: its client is `absOcc` (§18's
    -- occurrence abstraction), which wants to see a mode — a mode-blind version
    -- would match `⇝τ` against `τ` and abstract away the marker along with the
    -- domain. (`FnDef.alphaEq`, the macro-vs-corpus round-trip criterion, was the
    -- second client and wanted the same thing for the same reason; it retired in
    -- M28 cluster C with its one consumer. The argument is unchanged, it just has
    -- one witness now instead of two.)
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
  /-- An annotated runtime λ's binders: names by `==`, domains structurally. -/
  def Term.beqBinders : List (Var × Term) → List (Var × Term) → Bool
    | [], [] => true
    | (x, τ) :: as, (y, υ) :: bs => x == y && Term.beq τ υ && Term.beqBinders as bs
    | _, _ => false
  termination_by ts us => sizeOf ts + sizeOf us
end

instance : BEq Term := ⟨Term.beq⟩

/-! ## α-equality on `Term` (M30 step 2)

    `Term.beq` compares binder names, and for its own client (`absOcc`, matching a
    subterm against the scope it was written in) that is right. Three OTHER
    comparisons are between types written INDEPENDENTLY of each other — a λ's
    annotation against the ascription that binds it (`piAgree`, `checkArm`), a
    sealed recursor's written motive against the one its ascription derives
    (`sealRec`), a borrow's owed type against its payload type (`trivialOwedT`) —
    and for those, two spellings of the same type must not be two types.

    **This function exists because the de Bruijn representation was giving those
    three α-insensitivity for free**, and deleting the indices deleted the gift
    along with the arithmetic. It is stated rather than inherited now, which is
    also the honest version: nothing about the comparisons said they were up to α;
    they simply could not tell. (Measured, not assumed: without it, `S26Seal.f1` —
    a `natRec` sealed at `Π (fuel : Nat) → …` with the motive written
    `λ (f : Nat). …` — is rejected as a motive mismatch.)

    Standard de-Bruijn-on-the-fly: each side carries its own binder stack, two
    bound variables match when their innermost-first positions agree, and two free
    variables match when their names do. -/

/-- Innermost-first position of `x` in `l`. -/
def bndPos? (l : List String) (x : String) : Option Nat :=
  let rec go : List String → Nat → Option Nat
    | [], _ => none
    | y :: ys, i => if y == x then some i else go ys (i + 1)
  go l 0

mutual
  def Term.alphaEqGo (lc rc : List String) : Term → Term → Bool
    | .pvar x, .pvar y =>
      match bndPos? lc x, bndPos? rc y with
      | some i, some j => i == j                       -- both bound: same binder
      | none, none => x == y                           -- both free: same name
      | _, _ => false
    | .var x, .var y => x == y
    | .type, .type => true
    | .const n, .const m => n == m
    | .unit, .unit => true
    | .cmpT a, .cmpT b => Term.alphaEqGo lc rc a b
    | .lam x da ba, .lam y db bb =>
      Term.alphaEqGo lc rc da db && Term.alphaEqGo (x :: lc) (y :: rc) ba bb
    | .pi x da ba, .pi y db bb =>
      Term.alphaEqGo lc rc da db && Term.alphaEqGo (x :: lc) (y :: rc) ba bb
    | .sigmaT x da ba, .sigmaT y db bb =>
      Term.alphaEqGo lc rc da db && Term.alphaEqGo (x :: lc) (y :: rc) ba bb
    | .borrowT x da ba, .borrowT y db bb =>
      Term.alphaEqGo lc rc da db && Term.alphaEqGo (x :: lc) (y :: rc) ba bb
    | .app fa aa, .app fb ab => Term.alphaEqGo lc rc fa fb && Term.alphaEqGo lc rc aa ab
    | .idT a b c, .idT d e f =>
      Term.alphaEqGo lc rc a d && Term.alphaEqGo lc rc b e && Term.alphaEqGo lc rc c f
    | .ctorApp n as, .ctorApp m bs => n == m && Term.alphaEqListGo lc rc as bs
    | .deref a, .deref b => Term.alphaEqGo lc rc a b
    | .borrow a, .borrow b => Term.alphaEqGo lc rc a b
    -- Everything else is a runtime STATEMENT form. It cannot occur in the types
    -- these comparisons are about, and falling back to `beq` keeps the function
    -- total without inventing a scoping rule for bodies.
    | a, b => Term.beq a b
  termination_by t u => sizeOf t + sizeOf u
  def Term.alphaEqListGo (lc rc : List String) : List Term → List Term → Bool
    | [], [] => true
    | a :: as, b :: bs => Term.alphaEqGo lc rc a b && Term.alphaEqListGo lc rc as bs
    | _, _ => false
  termination_by ts us => sizeOf ts + sizeOf us
end

/-- Are these two terms equal up to the names of their pure binders? -/
def Term.alphaEq (t u : Term) : Bool := Term.alphaEqGo [] [] t u

/-! ## Pure substitution on `Term` (M26-C; renamed and de-arithmetized in M30 step 2)

    It exists for one reason, and since M30 step 1 deleted `Val.substPure` this is
    the only reason left: **a borrow-moded Π has no `Val` form.** `borrowT` is a
    telescope-position marker that `readC` refuses to reflect, so
    `Π (v : &mut List Nat) → …` — the type a sealed function is ascribed (§5) and
    the type a recursor arm is checked at (§7) — can only ever be manipulated as a
    `Term`. Peeling such a Π into a telescope therefore needs substitution at the
    `Term` level, which is this.

    **`Term.shiftPure` is gone and there is no lifting here** (M30 step 2). Under
    de Bruijn a substitution had to renumber the substituend at every binder
    crossed and renumber the term's own free indices on the way out; under names
    both moves are the identity, and the only rule left is the one that was always
    the real content — *stop at a binder that rebinds the name*, because inside it
    the name means something else.

    Nor is capture a hazard at the four sites that remain (`piPeel` and `piAgree`
    in `Machine`, `fnElab`'s arm annotations): every substituend is a runtime
    variable or a constructor spine over runtime variables — `.var x`,
    `S(.var k)`, `Cons(.var h, .var t)` — and a term with no free PURE names
    cannot be captured by a pure binder. Where that stops being true this needs
    a freshening pass, and the reserved namespace (`isReservedName`) is where one
    would draw from. -/
mutual
  def Term.substP : String → Term → Term → Term
    | x, s, .pvar y => if y == x then s else .pvar y
    | x, s, .cmpT τ => .cmpT (Term.substP x s τ)           -- a domain: outside the binder
    -- The three pure binders and `borrowT`'s snapshot binder: the domain is
    -- outside the binder, the body inside it — so a body whose binder rebinds `x`
    -- is left alone, which is the whole of the scope discipline.
    | x, s, .lam y dom b =>
      .lam y (Term.substP x s dom) (if y == x then b else Term.substP x s b)
    | x, s, .pi y dom cod =>
      .pi y (Term.substP x s dom) (if y == x then cod else Term.substP x s cod)
    | x, s, .sigmaT y dom cod =>
      .sigmaT y (Term.substP x s dom) (if y == x then cod else Term.substP x s cod)
    | x, s, .borrowT y τ S =>
      .borrowT y (Term.substP x s τ) (if y == x then S else Term.substP x s S)
    | x, s, .app f a => .app (Term.substP x s f) (Term.substP x s a)
    | x, s, .ctorApp n args => .ctorApp n (Term.substPList x s args)
    | x, s, .idT a b c => .idT (Term.substP x s a) (Term.substP x s b) (Term.substP x s c)
    -- A type may read a live place (`*v`, `a[i]`, `a[lo ; cnt]` — §5.2/¶2.1), and
    -- those subterms can carry pure variables in their index positions.
    | x, s, .deref t => .deref (Term.substP x s t)
    | x, s, .index t i ev => .index (Term.substP x s t) (Term.substP x s i)
        (match ev with | some e => some (Term.substP x s e) | none => none)
    | x, s, .range t lo cnt rest ev eqc =>
      .range (Term.substP x s t) (Term.substP x s lo)
        (match cnt with | some c => some (Term.substP x s c) | none => none)
        (match rest with | some r => some (Term.substP x s r) | none => none)
        (match ev with | some e => some (Term.substP x s e) | none => none)
        (match eqc with | some e => some (Term.substP x s e) | none => none)
    | _, _, t => t                                         -- runtime statement forms / leaves
  termination_by _ _ t => sizeOf t
  def Term.substPList : String → Term → List Term → List Term
    | _, _, [] => []
    | x, s, t :: ts => Term.substP x s t :: Term.substPList x s ts
  termination_by _ _ ts => sizeOf ts
end

/-! The **free pure names** of a term: the names an occurrence of it depends on
    its surroundings for. One client, `absOcc` below, which needs to know which
    binders it may not carry a subterm under — so this walks exactly the forms
    `absOcc` walks (the pure fragment plus the place reads a type may contain),
    and treats a runtime statement form as a leaf for the same reason it does. -/
mutual
  def Term.freePNamesGo (bound : List String) : Term → List String
    | .pvar x => if bound.contains x then [] else [x]
    | .cmpT τ => Term.freePNamesGo bound τ
    | .lam y dom b | .pi y dom b | .sigmaT y dom b | .borrowT y dom b =>
      Term.freePNamesGo bound dom ++ Term.freePNamesGo (y :: bound) b
    | .app f a => Term.freePNamesGo bound f ++ Term.freePNamesGo bound a
    | .idT a b c =>
      Term.freePNamesGo bound a ++ Term.freePNamesGo bound b ++ Term.freePNamesGo bound c
    | .ctorApp _ args => Term.freePNamesListGo bound args
    | .deref t | .borrow t => Term.freePNamesGo bound t
    | .index t i ev =>
      Term.freePNamesGo bound t ++ Term.freePNamesGo bound i
        ++ (match ev with | some e => Term.freePNamesGo bound e | none => [])
    | .range t lo cnt rest ev eqc =>
      Term.freePNamesGo bound t ++ Term.freePNamesGo bound lo
        ++ (match cnt with | some c => Term.freePNamesGo bound c | none => [])
        ++ (match rest with | some r => Term.freePNamesGo bound r | none => [])
        ++ (match ev with | some e => Term.freePNamesGo bound e | none => [])
        ++ (match eqc with | some e => Term.freePNamesGo bound e | none => [])
    | _ => []
  termination_by t => sizeOf t
  def Term.freePNamesListGo (bound : List String) : List Term → List String
    | [] => []
    | t :: ts => Term.freePNamesGo bound t ++ Term.freePNamesListGo bound ts
  termination_by ts => sizeOf ts
end

def Term.freePNames (t : Term) : List String := Term.freePNamesGo [] t

/-! ## Free runtime variables (M26-C)

    §7 cost 2 says a runtime λ is the *boring* kind of function value: "closed —
    arms reference only their own binders and globals". This is what makes that
    **checked rather than assumed**. A body is entered under a fresh id window
    (`shiftVars`), so a free variable escaping into a `.lamR` would not dangle —
    it would be silently rebound to whatever the frame shift lands on, which is
    environment capture arriving by accident in the one phase that defers it
    (constraint 5). Rejecting at the point the value is formed is the honest
    alternative. -/
mutual
  def Term.freeRVars (bound : List Nat) : Term → List Var
    | .var x => if bound.contains x.id then [] else [x]
    | .letIn x rhs rest => Term.freeRVars bound rhs ++ Term.freeRVars (x.id :: bound) rest
    | .assign p e rest => Term.freeRVars bound p ++ Term.freeRVars bound e ++ Term.freeRVars bound rest
    | .ctorApp _ args => Term.freeRVarsList bound args
    | .borrow t | .deref t => Term.freeRVars bound t
    | .index t i ev =>
      Term.freeRVars bound t ++ Term.freeRVars bound i
        ++ (match ev with | some e => Term.freeRVars bound e | none => [])
    | .range t lo cnt rest ev eqc =>
      Term.freeRVars bound t ++ Term.freeRVars bound lo
        ++ (match cnt with | some c => Term.freeRVars bound c | none => [])
        ++ (match rest with | some r => Term.freeRVars bound r | none => [])
        ++ (match ev with | some e => Term.freeRVars bound e | none => [])
        ++ (match eqc with | some e => Term.freeRVars bound e | none => [])
    | .matchE scrut eqn brs =>
      (if bound.contains scrut.id then [] else [scrut])
        ++ Term.freeRVarsBranches (match eqn with | some h => h.id :: bound | none => bound) brs
    | .seq a b => Term.freeRVars bound a ++ Term.freeRVars bound b
    | .call _ args => Term.freeRVarsList bound args
    | .seal t u => Term.freeRVars bound t ++ Term.freeRVars bound u
    | .callV x args =>
      (if bound.contains x.id then [] else [x]) ++ Term.freeRVarsList bound args
    -- The DOMAINS are traversed too (M27), and as a TELESCOPE: a runtime λ's
    -- binder types are dependent — `ih`'s mentions the predecessor bound to its
    -- left, `hfuel : Le (len *v) fuel` mentions the borrow bound to its left — so
    -- each domain is read under the binders before it and nothing else. Treating
    -- them as closed would let a genuinely free variable into a type and past the
    -- closedness check the whole traversal exists to feed.
    | .lamR xs body =>
      Term.freeRVarsBinders bound xs
        ++ Term.freeRVars (xs.map (·.1.id) ++ bound) body
    | .app a b => Term.freeRVars bound a ++ Term.freeRVars bound b
    | .pi _ a b | .lam _ a b | .sigmaT _ a b | .borrowT _ a b =>
      Term.freeRVars bound a ++ Term.freeRVars bound b
    | .idT a b c => Term.freeRVars bound a ++ Term.freeRVars bound b ++ Term.freeRVars bound c
    | .cmpT τ => Term.freeRVars bound τ
    | _ => []
  termination_by t => sizeOf t
  def Term.freeRVarsList (bound : List Nat) : List Term → List Var
    | [] => []
    | t :: ts => Term.freeRVars bound t ++ Term.freeRVarsList bound ts
  termination_by ts => sizeOf ts
  def Term.freeRVarsBranches (bound : List Nat) : List Branch → List Var
    | [] => []
    | (.mk _ bs body) :: rest =>
      Term.freeRVars (bs.map (·.id) ++ bound) body ++ Term.freeRVarsBranches bound rest
  termination_by bs => sizeOf bs
  /-- A runtime λ's annotated binders, scoped as a telescope: each domain sees the
      binders to its left. -/
  def Term.freeRVarsBinders (bound : List Nat) : List (Var × Term) → List Var
    | [] => []
    | (x, τ) :: rest => Term.freeRVars bound τ ++ Term.freeRVarsBinders (x.id :: bound) rest
  termination_by xs => sizeOf xs
end

/-! Abstract every occurrence of `e` into the pure variable `x` (mutual with the
    ctor-arg list helper).

    **No shifting, and one guard instead** (M30 step 2). The de Bruijn version
    re-shifted `e` at every binder crossed so the comparison happened at the right
    depth, and lifted the term's own free indices to make room for the binder
    being introduced. Both moves are the identity under names; what survives is
    the fact they were implementing — *a binder that rebinds one of `e`'s free
    names ends `e`'s meaning*, so occurrences inside it are not occurrences of
    `e` and the traversal stops. `shadowed` is that name set, computed once. -/
mutual
  def absOcc (e : Term) (x : String) (shadowed : List String) : Term → Term
    | .lam y dom b =>
      if Term.beq (.lam y dom b) e then .pvar x
      else .lam y (absOcc e x shadowed dom)
        (if shadowed.contains y then b else absOcc e x shadowed b)
    | .pi y dom cod =>
      if Term.beq (.pi y dom cod) e then .pvar x
      else .pi y (absOcc e x shadowed dom)
        (if shadowed.contains y then cod else absOcc e x shadowed cod)
    | .sigmaT y dom cod =>
      if Term.beq (.sigmaT y dom cod) e then .pvar x
      else .sigmaT y (absOcc e x shadowed dom)
        (if shadowed.contains y then cod else absOcc e x shadowed cod)
    | .app f a =>
      if Term.beq (.app f a) e then .pvar x
      else .app (absOcc e x shadowed f) (absOcc e x shadowed a)
    | .idT a b c =>
      if Term.beq (.idT a b c) e then .pvar x
      else .idT (absOcc e x shadowed a) (absOcc e x shadowed b) (absOcc e x shadowed c)
    | .ctorApp n args =>
      if Term.beq (.ctorApp n args) e then .pvar x
      else .ctorApp n (absOccList e x shadowed args)
    -- A mode marker is never itself an abstraction target (it is not a term),
    -- so recurse straight through rather than testing it.
    | .cmpT τ => .cmpT (absOcc e x shadowed τ)
    | s => if Term.beq s e then .pvar x else s   -- leaves, `pvar` among them
  termination_by s => sizeOf s
  def absOccList (e : Term) (x : String) (shadowed : List String) : List Term → List Term
    | [] => []
    | s :: ss => absOcc e x shadowed s :: absOccList e x shadowed ss
  termination_by ss => sizeOf ss
end

/-- The binder `abstractOccurrences` introduces. Reserved (`isReservedName`), so
    it can neither capture a source name nor be captured by one, which is what
    replaces the de Bruijn version's lifting. -/
def genName : String := "§gen"

/-- Abstract every occurrence of `e` in `t` by the fresh pure binder `genName`.
    `Term.lam genName τ (abstractOccurrences e t)` applied to `e` β-reduces back
    to `t`. The §18 motive-generalization mechanism: no matching by eye, no
    missed occurrence. -/
def abstractOccurrences (e t : Term) : Term := absOcc e genName (Term.freePNames e) t

/-- Does a type contain a borrow anywhere? A borrow-carrying return type (a
    `&mut`, or a `Pair` of them) is audited structurally by
    `collectResultBorrows`, never reflected, so it must NOT be pinned/`readC`'d
    (which rejects `borrowT`). The seal rule (M26-A) asks the same question of its
    ascribed type, which is why this sits in the syntax layer rather than in
    `Boundary` where it was born — `Machine` cannot import `Boundary`. -/
def hasBorrowT : Term → Bool
  | .borrowT _ _ _ => true
  | .sigmaT _ a b => hasBorrowT a || hasBorrowT b
  | .pi _ a b => hasBorrowT a || hasBorrowT b
  | .app a b => hasBorrowT a || hasBorrowT b
  | .lam _ a b => hasBorrowT a || hasBorrowT b
  | .idT a b c => hasBorrowT a || hasBorrowT b || hasBorrowT c
  | .cmpT τ => hasBorrowT τ
  | _ => false

/-- The components of a return type, flattened along its Σ spine. `Σ a → Σ b → c`
    is `[a, b, c]`; anything else is a single component. This is the same walk
    `collectResultBorrows` makes when it issues one loan per borrow position. -/
partial def retComponents : Term → List Term
  | .sigmaT _ d b => d :: retComponents b
  | t => [t]

/-- Does a return type MIX borrow and non-borrow components?

    **A soundness containment** (M27, found by `dllbc-b1`'s back-probe). A
    borrow-carrying return type is audited STRUCTURALLY — `collectResultBorrows`
    walks it and checks each issued borrow's owed type — and is deliberately never
    pinned or `readC`'d, because `readC` rejects `borrowT`. Both audit sites gate
    the value check on `hasBorrowT` being false (`checkRFnBody`, for a seal — the
    declaration path was the other one and is gone), so a NON-BORROW component of a
    borrow-carrying return type is judged by nothing at all.

    That is not vacuous, it is unsound: the caller's `buildResult` mints a σ at the
    stated leaf type regardless, so the caller RECEIVES the unearned claim as a
    proof and may return it at its own value return type, where the pin-and-check
    path does run and passes — the σ genuinely carries that `sctx` type. b1's
    witness closes it: `fn closedBot () -> Bot`, no hypotheses, checking.

    Nothing was ever bitten because no corpus declaration is both borrow-returning
    AND ensures-carrying — cursor content rode in `back`, and backs ARE checked —
    but M27 removes backs and points the whole language at ensures, which walks
    straight into it.

    The containment refuses the mixture rather than teaching the audit to judge
    value components in a borrow-carrying position. A cursor's sayable contract is
    its issued borrows' owed types; a value claim belongs on a value-returning
    function, where §5 point 4's "what you keep is what you ascribe" is already
    enforced by a check that looks. -/
def retMixesBorrow (t : Term) : Bool :=
  let cs := retComponents t
  cs.any hasBorrowT && cs.any (fun c => !hasBorrowT c)

/-- Is a borrow parameter's OWED type trivial — i.e. does the boundary owe nothing
    beyond the payload type it was lent?

    `&mut τ` elaborates to `.borrowT ⟨reserved⟩ τ τ` (Uni.lean), so triviality is
    exactly that shape: the owed type is the payload type. It used to be the
    payload type WEAKENED over the entry-snapshot binder, and under names the
    weakening is the identity — which is the whole of what M30 step 2 did to this
    function. `&mut (s : Bool ~> Nat)` and
    `&mut (s : List Nat ~> Σ (l : List Nat) → Id Nat (len l) (len s))` are the two
    non-trivial owed types in the corpus, and both are load-bearing claims the
    audit checks.

    Used by the M27 containment below: a non-trivial owed type is a claim, and a
    claim on a parameter CONSUMED INTO THE RESULT is checked by nobody. -/
def trivialOwedT : Term → Bool
  | .borrowT _ τ s => Term.alphaEq s τ
  | .sigmaT _ _ (.borrowT _ τ s) => Term.alphaEq s τ
  | _ => true

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
