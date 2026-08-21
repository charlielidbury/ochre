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

/-! ### σ's, as reserved names (M32 R1)

    At rest, knowledge is a canonical `Term` (suspensions.md §2.3), so a symbolic
    value — which used to be its own value former, `Val.sym σ` — is a `pvar` in
    the reserved namespace. One atom former instead of two, and the payoff is
    that ⇜'s refinement becomes literally `Term.substP` at a name and §19's
    generalization becomes an occurrence rewrite: the two sweeps stop being
    value-tree machinery and become the substitution the pure fragment already
    has.

    `§σ<digits>` is disjoint from every binder the kernel mints — `§<digits>`
    (readback), `§gen`, `§let<digits>`, `§p<digits>`, `§_`, and the hand-written
    recursor premise binders (`§k §ih §h §t §x §y §n §xs §lo`) — which is what
    makes `substP`'s "stop at a binder that rebinds the name" guard vacuous for
    them (suspensions.md §6, first sharp edge). Nothing rebinds a σ, so nothing
    can shadow one. -/

/-- A number in SUBSCRIPT digits — how loan and σ indices display (`ℓ₀`,
    `σ₁₂`). Display only: the internal name (`symName`) stays ASCII, so
    recognition (`symOfName?`) is untouched; only what a reader sees changes. -/
def subNat (n : Nat) : String :=
  (toString n).map fun c => Char.ofNat (0x2080 + (c.toNat - '0'.toNat))

/-- The reserved pure name a σ is written as. -/
def symName (σ : Nat) : String := "§σ" ++ toString σ

/-- Recognize one. -/
def symOfName? (s : String) : Option Nat :=
  if s.startsWith "§σ" then (s.drop 2).toNat? else none

/-- A runtime variable: a globally-unique `id` plus a display `name`. -/
structure Var where
  id : Nat
  name : String
deriving DecidableEq, BEq, Repr, Inhabited

/-- **A pure binder is a `Var` with no slot** (M32 R2). One λ former means one
    binder type, and a `Var` is the one that carries both things a binder can
    need: the NAME, which is what every resolution keys on since M32 R1, and the
    `id`, which only a binder whose argument lands in Ω has any use for.

    So a comptime binder is written `"x"` and read as `⟨noSlot, "x"⟩`. The id is
    the residue of the runtime half and it leaves with the rest of E2's id
    machinery at R4; until then this coercion is what keeps the ~150 hand-written
    pure λs spelled the way they were written.

    **`noSlot` is a real sentinel and not a zero**, because `Term.freeRVars` asks
    which of a term's binders bind a `.var` occurrence and it asks by id: a pure
    binder must bind NOTHING there (its argument lands in the comptime
    environment, not in Ω, and `.var` names an Ω slot), while an imperative λ's
    binder must bind its own id exactly as `lamR`'s telescope did. Zero would have
    silently bound every occurrence of runtime slot `#0`. -/
def noSlot : Nat := 0xFFFF_FFFF_FFFF

/-- **A program-level DECLARATION's slot** (M32 R4) — the `let` a `fn` statement
    becomes (§8: "a declaration is a `let`, and the binding IS the name").

    A TAG, and that is the whole change from what it replaces. `FnMacro.progBase`
    was an arithmetic base: declaration `i` bound at `900 + i`, so declarations
    were distinguishable from locals by being ABOVE a number, from each other by
    their index, and a body was checked not to mint an id that reached the base.
    Every one of those three jobs was about ID resolution, and R1 made Ω resolve
    by NAME — `findSlot?` never reads an id — so what is left is the one question
    the arithmetic was also answering: *is this Ω entry a declaration?* The two
    consumers are the harness projections that report "what this code leaves in
    Ω" without the program's own function bindings in the way.

    A single constant rather than `900 + i` also removes the collision the
    arithmetic created: two `%`-spliced chains both numbered from `900`, so
    `withA (withB …)` had `A` and `B` at the SAME id under DIFFERENT names, and
    `bindFn` refused it. Under name-keying nothing was ever going to confuse
    them, which is why that check retired here rather than being re-expressed. -/
def declSlot : Nat := 0xFFFF_FFFF_FFFE

instance : Coe String Var := ⟨fun s => ⟨noSlot, s⟩⟩

/-- Does this identifier start with an uppercase letter? **The mode marker**
    (combining-fns §6): a capitalized binder is COMPTIME, a lowercase one is
    RUNTIME. Lives here rather than in the macro layer because the kernel reads
    it — see `Var.isComptime`. -/
def isUpperInit (s : String) : Bool :=
  match s.toList with
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
    A pure binder has a name too since M30 step 2, but it does NOT carry its mode
    there: the two namespaces are separate, and a pure binder's mode stays on the
    domain — `Term.cmpT` below. -/
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
  /-- `let x = rhs` — bind `x` to the ⇒-value of `rhs`. A statement is an
      ordinary unit-valued EXPRESSION (detach-tails): it carries no continuation
      of its own, and a statement spine is a right-nested `.seq` chain ending in
      the block's final expression. The binding a `let` makes is visible
      left-to-right until a binder boundary (λ/Π/Σ entry, a match arm) — a
      `.seq (.letIn x rhs) rest` spine scopes `x` over `rest`, which is what the
      tail used to spell structurally. -/
  | letIn  : Var → Term → Term
  /-- `place := rhs` — ⇒-read `rhs`, ⇐-write it into `place`; unit-valued, tail
      detached exactly as `letIn`'s. `place` is syntactically an arbitrary
      `Term`; ⇐ is only *defined* on place shapes (a variable under zero or more
      `*` peels). -/
  | assign : Term → Term → Term
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
  /-- `e ; rest` — **the one sequencing form** (detach-tails): ⇒-evaluate `e`
      for effect, discard its value, then run `rest`. Every statement spine is a
      right-nested chain of these — `let x = e ; rest` is `.seq (.letIn x e) rest`,
      `p := e ; rest` is `.seq (.assign p e) rest` — ending in the block's final
      expression (`.unit` when there is none). A `.letIn` head scopes its binder
      over the chain's tail; traversals with binder awareness carry a dedicated
      `.seq (.letIn …) rest` case for exactly that. -/
  | seq    : Term → Term → Term
  /-- `f(a, …)` — a call to a declared function (§5.3), checked against the
      signature alone. Unifying `fn` with λ is deferred (§10). -/
  | call   : String → List Term → Term
  /-- `.seal s t u` — **opacity as syntax** (combining-fns §5). Programmer-invoked
      generalization: "forget everything about this value except its type".

        * EXECUTING (⇒, concrete): evaluate `t`. Execution is always transparent.
        * CHECKING (⇒, symbolic): verify `t : u` ONCE, at the node — this check
          *is* the audit — then yield a σ : u. Everything downstream sees only the
          type.

      **`s` is the SEAL SITE** (M32 R3, suspensions.md §2.4), and it is what makes
      the second bullet's "a σ" a definite article rather than an indefinite one.
      A site is a `Nat` assigned by `Term.numberSeals`, a pass at the program
      boundary that walks the elaborated term in evaluation order — so it is
      stable across macro expansion (it runs after every macro) and across
      α-canonicalization (it reads structure, never names). What the site buys is
      that the seal has an identity independent of WHEN it is evaluated, which is
      exactly what ⇝ needs: the old refusal below said minting a fresh σ needs an
      event and ⇝ has none, and a site-keyed σ needs no event because it is not
      fresh — it is the σ this site at these inputs always has (`St.sealSites`).

      **Absent from the comptime fragment by construction** — this WAS the reading,
      and R3 replaced it with a rule rather than deleting the reasoning, because
      the reasoning is what the rule had to answer. (i) It is its OWN constructor,
      not an `.app` of a magic `.const` (the route `@exit`/`old` take): ⇝'s
      application rule can therefore never meet it, and no check inside that rule
      distinguishes it — still true, and still what keeps the seal from arriving
      anywhere by accident. (ii) There is no `Val.seal`, so a seal never sits at
      rest as a suspension; ⇝'s rule for it (`readComptimeVal`) is a rule at the
      NODE, which reduces it to the σ its site names. -/
  | seal   : Nat → Term → Term → Term
  /-- `.marker name e` — a NAMED CLAIM SITE, and TEST SCAFFOLDING ONLY (docs/21).
      Semantics: identity — `@name(e)` IS `e`. A marked honest program declares
      where its lying twins will attack, and `Term.replaceMarked?` mutates
      exactly there (exactly-one contract). The machine NEVER sees one:
      `Machine.atBoundary` strips markers before seal numbering, the
      `numberSeals` precedent — no eval rule, no checking rule, no `Val` form.
      Ruled scaffolding-only at spec time; using this as a general annotation
      mechanism re-opens the kernel-surface-for-tests question and must not
      happen by drift. -/
  | marker : String → Term → Term
  /-- Terminal form, the value a statement sequence returns when it has no
      final expression. -/
  | unit   : Term
  -- Pure fragment (§4): the comptime type theory's formers. Pure binders carry
  -- their SOURCE NAME (M30 step 2); `readC` (⇝) reflects these into the matching
  -- `Val` forms and reduces. Runtime `var`/`let` (named ids) are unaffected.
  | pvar   : String → Term           -- pure variable occurrence, by name
  | type   : Term                    -- the universe
  | pi     : String → Term → Term → Term      -- Π (x : dom) → cod
  | sigmaT : String → Term → Term → Term      -- Σ (x : fst-type). snd-type
  /-- `λ (x : dom). body` — **the λ, and there is only one** (M32 R2,
      suspensions.md §2.4).

      Until R2 there were two: this one, whose body is a pure term ⇝ reduces, and
      `lamR`, whose body is a *body* (writes, calls, borrows, matches) and whose
      binders name Ω slots. They were "the same former in the document, two
      representations in the machine". They are one former now, and what the two
      species carried is redistributed onto things that were already there:

        * the **arity** was `lamR`'s binder LIST; it is nesting now, and
          `λ(x : τ, y : υ){ … }` is sugar for `λ(x : τ). λ(y : υ). …`
          (`Term.lamTel` builds it, `Term.peelLams` reads it back);
        * the **binder's mode** — whether its argument is ⇝-snapshot-read or
          ⇒-moved — is the domain's `⇝` marker and the binder's case, as it
          already was for every other binder (§2.1);
        * the **fragment** — whether evaluating the body means pure reduction or
          the effectful walk — is `Term.imperative` below, recomputed at every
          application and at the seal. A property, never a species tag.

      **Church-style: the binder carries its domain** (M27, the ratified function
      model), which is what the document's grammar said all along. -/
  | lam    : Var → Term → Term → Term
  /-- **Application, and there is only one form of it** (M32 R4). `callV` — the
      n-ary `x(a, …)` the declaration era's telescope left behind — retired here,
      so `f(a, b)` is surface sugar for the spine `.app (.app f a) b` and the
      document's grammar (`t t′`) is the machine's.

      What retiring it must NOT lose is the **mint-vs-remember split**, and that
      split is ARROW-keyed rather than node-keyed (§12 decision 5): ⇒ applied to a
      spine whose head holds a function MINTS a fresh existential at the
      instantiated codomain, while ⇝ applied to the same spine REMEMBERS the
      structured neutral. `callV` used to carry that distinction in the syntax,
      which made it look node-keyed; with one node the arrows carry it alone,
      which is what the decision always said. Asserted in `S32Spine` §A/§B. -/
  | app    : Term → Term → Term      -- application
  | const  : String → Term           -- a built-in constant (recursor or type former)
  | idT    : Term → Term → Term → Term  -- Id A a b (§10): the identity type
  /-- The borrow type `&mut (s : τ ↝ τ')` (§5.1): exclusive access to a `τ`,
      owing a `τ'` at the boundary. `τ'` is under one pure binder named `s`, the
      entry snapshot. Plain `&mut τ` is `borrowT ⟨a reserved name⟩ τ τ` — under
      names the weakening the de Bruijn spelling needed is the identity. Only
      valid at a telescope position — interpreted by the seeding that
      `checkRFnBody` runs (`seedTelescopeV`), never reflected as a value. -/
  | borrowT : String → Term → Term → Term
  /-- `⇝τ` — the **comptime binder-mode marker on a domain** (combining-fns §6),
      and the pure-binder counterpart of `Var.isComptime`.

      `Π (X : τ) → …` elaborates to `.pi (.cmpT τ) …` and `λ (X : τ). …` to
      `.lam (.cmpT τ) …`. It is legal at a λ/Π/Σ DOMAIN and at a Σ CODOMAIN —
      the same standing as `borrowT`, which is likewise a binder-mode marker
      written in type position and not a type. `&mut τ` says "this binder is a
      runtime borrow"; `⇝τ` says "this binder is comptime"; a bare `τ` says
      "runtime owned". Three modes, one syntactic place, and the two that are not
      the default are marked.

      **The CODOMAIN position is Σ0** (M33, suspensions.md §2.7), and it is the
      same marker doing the same job from the other end of the pair. A Σ's binder
      spells its first component's mode on the domain; its TAIL has no binder, so
      `Σ0 (x : A). P` puts the marker on `P`. A position is comptime iff its
      type carries this marker — which is now one sentence covering a λ's
      argument, a Π's, a Σ's component and a Σ's tail, where it used to cover
      three and leave the fourth silently runtime.

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

/-! ## Application spines (M32 R4) -/

/-- `f a₁ … aₙ` — the spine `callV` used to spell as one node. Left-nested, so
    `collectAppT`/`appSpineVar?` read it back in the order it was written. -/
def Term.appSpine (head : Term) : List Term → Term
  | [] => head
  | a :: rest => Term.appSpine (.app head a) rest

/-- A spine whose HEAD is a runtime variable, i.e. what `.callV x args` was.

    This is the one structural fact that survived `callV`'s retirement, and it is
    needed in `Syntax.lean` rather than only in the machine because
    `Term.imperative` consults it: a `.var` head names an Ω SLOT, so applying one
    is ⇒-entry, exactly as the `.callV` case said. A `.const`/`.pvar` head is a
    pure spine and stays comptime — which is why `fn UseTrans (…) { LeTransRaw a b c
    p q }` is still classified by its BINDERS (M32 R2's second half) and not by
    this. -/
def Term.appSpineVar? : Term → Option (Var × List Term)
  | .app f a =>
    match Term.appSpineVar? f with
    | some (x, as) => some (x, as ++ [a])
    | none => none
  | .var x => some (x, [])
  | _ => none

/-! ## The λ telescope, and the property that replaces the second species (M32 R2) -/

/-- `λ(x : τ, y : υ){ b }` — the comma list, as the nesting it abbreviates. -/
def Term.lamTel : List (Var × Term) → Term → Term
  | [], b => b
  | (x, τ) :: rest, b => .lam x τ (Term.lamTel rest b)

/-- …and reading one back off a λ chain: every leading binder, then what is under
    them. The inverse of `lamTel`, and what every site that used to match
    `.lamR xs body` asks for. -/
def Term.peelLams : Term → List (Var × Term) × Term
  | .lam x τ b => let (tel, body) := Term.peelLams b; ((x, τ) :: tel, body)
  | t => ([], t)

/-! **Is this term outside the comptime fragment?** (M32 R2, suspensions.md §2.2.)

    The one irreducible difference between the two λ species was what evaluating
    the body MEANS — pure reduction, or the effectful walk — and this is that
    difference stated as a property of the body instead of carried as a tag on the
    former. It is recomputed wherever it matters (application, the seal, the
    `let` arrow, rendering), so nothing can go stale and no substitution can lose
    it.

    The forms it names are exactly the ones `reflectC` refuses BY NAME — writes,
    borrows, sequencing, matching, calls, the seal — which is this calculus's
    standing definition of the pure sub-grammar (§1.3). `.var`, `.letIn`, `.deref`
    and the index steps are absent on purpose: ⇝ has rules for all of them (a
    snapshot read, β, a payload projection, a segment read), so a body built from
    those is one both arrows agree about. -/
mutual
  def Term.imperative : Term → Bool
    -- A let-headed `.seq` is the statement spine a `let x = e ; rest` block
    -- elaborates to (detach-tails), and it classifies by its PARTS — exactly as
    -- the tail-carrying `.letIn x rhs rest` did — because ⇝ has a rule for it
    -- (`eval` binds and threads). Any OTHER `.seq` head is effect sequencing and
    -- stays imperative unconditionally, matching `reflectC`'s refusal.
    | .seq (.letIn _ rhs) rest => Term.imperative rhs || Term.imperative rest
    | .assign _ _ | .borrow _ | .seq _ _ | .matchE _ _ _
    | .call _ _ | .seal _ _ _ => true
    -- A marker is its body (identity semantics, docs/21).
    | .marker _ e => Term.imperative e
    -- `a[lo ; ..]` reads its count off the extent map, which is state.
    | .range _ _ none _ _ _ => true
    | .letIn _ rhs => Term.imperative rhs
    | .lam _ d b | .pi _ d b | .sigmaT _ d b | .borrowT _ d b =>
      Term.imperative d || Term.imperative b
    -- **A `.var`-headed spine is what `.callV` was** (M32 R4), and keeping it
    -- named here is the whole of what retiring the node costs. Without this the
    -- classification would be read off the ARGUMENTS alone, and a nullary
    -- `fn F () { g() }` — whose only binder is the Unit-desugar's comptime `U§`,
    -- and whose body is now `.app (.var g) .unit` — would classify PURE. A
    -- `.const`/`.pvar` head stays comptime, which is the pure spine `readC`
    -- remembers.
    | .app f a =>
      (Term.appSpineVar? (.app f a)).isSome || Term.imperative f || Term.imperative a
    | .idT a b c => Term.imperative a || Term.imperative b || Term.imperative c
    | .ctorApp _ args => Term.imperativeList args
    | .deref t | .cmpT t => Term.imperative t
    | .index t i ev =>
      Term.imperative t || Term.imperative i
        || (match ev with | some e => Term.imperative e | none => false)
    | .range t lo (some cnt) rest ev eqc =>
      Term.imperative t || Term.imperative lo || Term.imperative cnt
        || (match rest with | some r => Term.imperative r | none => false)
        || (match ev with | some e => Term.imperative e | none => false)
        || (match eqc with | some e => Term.imperative e | none => false)
    | _ => false
  termination_by t => sizeOf t
  def Term.imperativeList : List Term → Bool
    | [] => false
    | t :: ts => Term.imperative t || Term.imperativeList ts
  termination_by ts => sizeOf ts
end

/-- **Does this binder name an Ω SLOT?** — i.e. does its argument arrive by ⇒, at
    entry, into the store, rather than by ⇝ into the comptime environment?

    This is `noSlot`'s other half and the one fact that separates the two λ
    fragments at the BINDER. A comptime λ binder is coerced from a name and has
    no slot; a TELESCOPE binder — a `fn` parameter, a runtime λ's — is minted by
    the surface or by `teleVars` and has one.

    **R4 was to make this the CASE test, and the corpus says NO** (M32 R4). The
    plan reads: §2.1's migration makes capitalisation reach every binder, so
    "binds a slot" becomes "is lowercase" and the id goes with E2's machinery.
    R3b measured the residue at four binders in the flagship and R4 named them —
    all four are `Hf`, one `fn`'s proof parameter, capital, `⇝`-domained, and
    holding an Ω slot.

    **THE RULE IS ABOUT TELESCOPES: a telescope binder binds a slot regardless of
    case.** Capital marks the READ MODE — the argument arrives by ⇝, erased and
    non-consuming — and says nothing about the LOCATION, which is where the
    argument lands. `seedTelescopeV` slots every parameter because every
    parameter is something the body cites by name, comptime or not. So the case
    test and this one answer DIFFERENT QUESTIONS, and swapping them would flip a
    `fn` all of whose parameters are capital from imperative to pure — the exact
    regression R3b's number was measuring the exposure to.

    What R4 does deliver is that this is no longer E2's machinery: `noSlot` is a
    TAG, alongside `declSlot`, and nothing in the kernel compares, orders or
    offsets an id any more. The test survives; the arithmetic it used to sit
    among does not. -/
def Var.bindsSlot (x : Var) : Bool := x.id != noSlot

/-- Is this λ an IMPERATIVE one — is applying it ⇒-ENTRY rather than ⇝ reduction?

    Two ways to be, and they are the two halves of what §2.2 calls "the effectful
    walk": what sits under the binders is a BODY (writes, calls, borrows), or a
    binder names an Ω slot, so entering means binding one. The second is not
    redundant — `fn Identity (n : Nat) -> Nat { n }` has a body both arrows can
    read, and it is still a function whose argument is ⇒-read into a slot and
    whose contract is checked by §5.4's audit rather than by `hasType`.

    **The second half is LOCATION and not case** (M32 R4, the telescope rule —
    see `Var.bindsSlot`). A `fn` all of whose parameters are capital is still
    entered: its arguments still land in Ω, its contract is still the audit's.
    Reading this half off the binders' CASE instead would classify such a `fn`
    pure and take its audit away, which is what R3b's `keyDisagree` was
    measuring the exposure to.

    Asked of the whole node, so `λ(x : τ, y : υ){ … }` is judged by all its
    binders and by what is under them, rather than by the inner λ it is sugar
    for. -/
def Term.lamImperative : Term → Bool
  | t =>
    let (tel, body) := Term.peelLams t
    Term.imperative body || tel.any (fun p => p.1.bindsSlot)

/-! ## The unit binder — what a λ with nothing to bind binds

    **One λ former means a λ has a binder**, so `Term.lamTel [] body` IS `body`
    and a suspension with nothing to suspend on cannot be spelled. Two places in
    the language need one anyway, and they need the same one:

      * a **nullary `fn`** (M32 R2, suspensions.md §1) — without it `fn F () -> T
        { … }` and the ascription `(e : T)` are the same term and the seal cannot
        tell a function from an ascribed expression;
      * a **recursor arm with an empty residual telescope** (M33b) — `fn Build
        [n] (n : Nat) -> List Nat` gives its `Z` arm no binders, and a bare term
        in arm position is not a suspension at all: `readRecArgs` ⇒-READS it when
        the spine is formed, so its body runs before ι has selected anything and
        every ι thereafter shares the one value it produced. The wrapper is what
        makes an arm a body that waits, which is the property every OTHER arm has
        for free.

    It is **comptime and unwritable**: capitalized, so its `⇝Unit` domain and
    `piPeel`'s mode check agree and the argument is ⇝-read (nothing is consumed by
    applying a λ that binds nothing); and spelled with a `§`, which no Lean `ident`
    can contain, so no program can bind, shadow or cite it.

    That unwritability is what answers the ambiguity `S26Rec` §A4 records — "`λ(){
    e }` is a thunk, and at ι there is no way to tell *the arm applied to no
    arguments* from *the arm with nothing owed*". There is now: the arm SAYS which
    it is, in a binder only the elaboration can write. -/

/-- The unit binder's name. Reserved: `§` is not an `ident` character. -/
def unitBinderName : String := "U§"

/-- The unit binder. Its id is `0` — the positional convention a one-parameter
    telescope has, and harmless for an arm because an arm that takes this binder
    is by construction one whose residual telescope is EMPTY, so there is no
    sibling parameter for `0` to collide with. It BINDS A SLOT, which is what
    routes such an arm through ⇒-entry (a fresh frame per ι) rather than through
    β. -/
def unitBinder : Var := ⟨0, unitBinderName⟩

/-- Is this the unit binder? Asked of an arm's leading binder by ι (does it owe a
    `()`?) and by the two contract derivations (does its Π gain a `Unit`?). -/
def Var.isUnitBinder (x : Var) : Bool := x.name == unitBinderName

/-- Does this peeled telescope lead with the unit binder? -/
def Term.telTakesUnit (tel : List (Var × Term)) : Bool :=
  match tel with | (x, _) :: _ => x.isUnitBinder | _ => false

/-- The contract a unit-binding λ takes: its own return type behind one `⇝Unit`
    Π. The binder name is a `§`-name because `piPeel` substitutes the λ's own
    binder for it and nothing ever reads this one. -/
def Term.unitPi (ret : Term) : Term := .pi "§u" (.cmpT (.const "Unit")) ret

/-- **A suspension, spelled as a term** (M32 R2): the raw body under the bindings
    it captured, as the `let`-chain the evaluator already knows how to perform.

    This is the whole of cooking's syntax half, and it is a `foldr` rather than a
    traversal for a reason worth stating: ρ binds KNOWLEDGE, and `eval`'s `letIn`
    rule binds a runtime slot's reserved pure name and resolves `.var` through it
    (`Pure.letName`). So "evaluate the body under ρ" is already a rule this
    calculus has — no `.var`-substitution had to be written, and no second scoping
    story exists to disagree with the first.

    Innermost-last, so an earlier ρ entry is visible to a later one's knowledge,
    which is the order Ω records them in. -/
def Term.underRho (ρ : List (Var × Term)) (node : Term) : Term :=
  ρ.foldr (fun p acc => .seq (.letIn p.1 p.2) acc) node

/-! ## Structural term equality (manual; `deriving` can't cross the nesting) -/

mutual
  def Term.beq : Term → Term → Bool
    | .var x, .var y => x == y
    | .letIn x a, .letIn y c => x == y && Term.beq a c
    | .assign a b, .assign d e => Term.beq a d && Term.beq b e
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
    -- **The SITE is decoration here** (M32 R3), for the reason R2 gave for a λ's
    -- binder id: comparison is what readback canonicality and `abstractInto` are
    -- built on, and two seals that differ only in when the numbering pass reached
    -- them are the same term to every judgment. The site is what the STORE keys a
    -- sealed σ by, and that is a question about identity over time rather than
    -- about equality of syntax.
    | .seal _ a b, .seal _ c d => Term.beq a c && Term.beq b d
    | .marker n a, .marker m b => n == m && Term.beq a b
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
    -- **By NAME, not by `Var`** (M32 R2). The binder of the one λ former carries
    -- an id, and comparing it would make two λs written in different frames
    -- unequal for a reason no judgment means: resolution is by name (M32 R1), so
    -- the name is the binder's identity and the id is decoration. This is also
    -- what keeps readback CANONICAL — `readbackName` mints a name, and the id it
    -- coerces to is the same zero for every level.
    | .lam x a b, .lam y c d => x.name == y.name && Term.beq a c && Term.beq b d
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
      Term.alphaEqGo lc rc da db && Term.alphaEqGo (x.name :: lc) (y.name :: rc) ba bb
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
      .lam y (Term.substP x s dom) (if y.name == x then b else Term.substP x s b)
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
    | .lam y dom b => Term.freePNamesGo bound dom ++ Term.freePNamesGo (y.name :: bound) b
    | .pi y dom b | .sigmaT y dom b | .borrowT y dom b =>
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

/-! ## Free runtime variables (M26-C; keyed by NAME since M32 R2)

    §7 cost 2 says a runtime λ is the *boring* kind of function value: "closed —
    arms reference only their own binders and globals". This is what makes that
    **checked rather than assumed** — and since R2 it is what computes ρ, because
    the free variables of a λ node ARE its capture (`admitGlobals`).

    **The bound set is NAMES, not ids** (M32 R2). R1 made Ω resolve by name,
    newest wins, so a name IS a binder's identity and asking "does one of this
    term's binders bind this occurrence" by id asks a question the store stopped
    answering. It is not a widening either: within one elaboration the macro
    mints unique ids, so id-keying and name-keying agree — EXCEPT where they
    genuinely disagree, and there the name is right, because an occurrence under
    a rebinding of its name resolves to the inner binder in the store too. What
    it unblocks is §2.6: a `fn` body may now be elaborated in the enclosing
    scope, whose bindings are numbered from the block's own counter and therefore
    collide with the telescope's positional ids `0 … n-1`.

    A λ binder binds here only when it BINDS A SLOT: a comptime binder's argument
    lands in the comptime environment, and `.var` names an Ω slot, so a pure
    `λ (N : Nat). …` must not shadow a citation of the runtime slot `N`. -/
mutual
  def Term.freeRVars (bound : List String) : Term → List Var
    | .var x => if bound.contains x.name then [] else [x]
    -- The SPINE case first: a let-headed `.seq` scopes its binder over the
    -- chain's tail (detach-tails), which is what the tail-carrying `.letIn`
    -- spelled structurally. A bare `.letIn` binds nothing outside itself.
    | .seq (.letIn x rhs) rest =>
      Term.freeRVars bound rhs ++ Term.freeRVars (x.name :: bound) rest
    | .letIn _ rhs => Term.freeRVars bound rhs
    | .assign p e => Term.freeRVars bound p ++ Term.freeRVars bound e
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
      (if bound.contains scrut.name then [] else [scrut])
        ++ Term.freeRVarsBranches (match eqn with | some h => h.name :: bound | none => bound) brs
    | .seq a b => Term.freeRVars bound a ++ Term.freeRVars bound b
    | .call _ args => Term.freeRVarsList bound args
    | .seal _ t u => Term.freeRVars bound t ++ Term.freeRVars bound u
    | .marker _ e => Term.freeRVars bound e
    -- **The one λ, scoped as the telescope it is** (M32 R2). The domain is read
    -- OUTSIDE the binder and the body inside it, which is exactly what
    -- `freeRVarsBinders` did to `lamR`'s list — a binder type is dependent (`ih`'s
    -- mentions the predecessor bound to its left, `hfuel : Le (len *v) fuel`
    -- mentions the borrow bound to its left), and nesting says so without a
    -- second traversal. A comptime binder's `noSlot` id binds nothing here, which
    -- is the whole of why it is a sentinel.
    | .lam x d b =>
      Term.freeRVars bound d
        ++ Term.freeRVars (if x.bindsSlot then x.name :: bound else bound) b
    | .app a b => Term.freeRVars bound a ++ Term.freeRVars bound b
    | .pi _ a b | .sigmaT _ a b | .borrowT _ a b =>
      Term.freeRVars bound a ++ Term.freeRVars bound b
    | .idT a b c => Term.freeRVars bound a ++ Term.freeRVars bound b ++ Term.freeRVars bound c
    | .cmpT τ => Term.freeRVars bound τ
    | _ => []
  termination_by t => sizeOf t
  def Term.freeRVarsList (bound : List String) : List Term → List Var
    | [] => []
    | t :: ts => Term.freeRVars bound t ++ Term.freeRVarsList bound ts
  termination_by ts => sizeOf ts
  def Term.freeRVarsBranches (bound : List String) : List Branch → List Var
    | [] => []
    | (.mk _ bs body) :: rest =>
      Term.freeRVars (bs.map (·.name) ++ bound) body ++ Term.freeRVarsBranches bound rest
  termination_by bs => sizeOf bs
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
        (if shadowed.contains y.name then b else absOcc e x shadowed b)
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
    `&mut (s : List Nat ~> Σ (l : List Nat). Id Nat (len l) (len s))` are the two
    non-trivial owed types in the corpus, and both are load-bearing claims the
    audit checks.

    Used by the M27 containment below: a non-trivial owed type is a claim, and a
    claim on a parameter CONSUMED INTO THE RESULT is checked by nobody. -/
def trivialOwedT : Term → Bool
  | .borrowT _ τ s => Term.alphaEq s τ
  | .sigmaT _ _ (.borrowT _ τ s) => Term.alphaEq s τ
  | _ => true

/-! ## The σ atom and the two sweeps, at `Term` level (M32 R1)

    ⇜'s refinement and §19's generalization used to be `Val`-tree traversals
    (`substSym`, `abstractInto`). With knowledge at rest being a canonical `Term`
    they are `Term` traversals, and one of them stops being a traversal at all:
    **refinement is `substP` at a σ's reserved name.** Only generalization needs
    its own function, because it is keyed on a COMPOUND (a whole spine) rather
    than on an atom — which is the same fact that makes it the one non-commuting
    sweep in the system (suspensions.md §3). -/

/-- A σ as a term. -/
def Term.sym (σ : Nat) : Term := .pvar (symName σ)

/-- The σ a term IS, if it is a bare one. -/
def Term.symOf? : Term → Option Nat
  | .pvar x => symOfName? x
  | _ => none

/-! Symbolic ids occurring in `t`, in pre-order of first appearance.

    It walks exactly the forms `Term.substP` walks, and that agreement is
    load-bearing rather than tidy: canonicalization reads the σ order off this
    traversal and applies it with `renumberSyms`, so a σ visible to one and
    untouched by the other would be renumbered out of existence. -/
mutual
  def Term.symIds : Term → List Nat
    | .pvar x => match symOfName? x with | some σ => [σ] | none => []
    | .cmpT τ => Term.symIds τ
    | .lam _ d b | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => Term.symIds d ++ Term.symIds b
    | .app f a => Term.symIds f ++ Term.symIds a
    | .idT a b c => Term.symIds a ++ Term.symIds b ++ Term.symIds c
    | .ctorApp _ args => Term.symIdsList args
    | .deref t => Term.symIds t
    | .index t i ev =>
      Term.symIds t ++ Term.symIds i ++ (match ev with | some e => Term.symIds e | none => [])
    | .range t lo cnt rest ev eqc =>
      Term.symIds t ++ Term.symIds lo
        ++ (match cnt with | some c => Term.symIds c | none => [])
        ++ (match rest with | some r => Term.symIds r | none => [])
        ++ (match ev with | some e => Term.symIds e | none => [])
        ++ (match eqc with | some e => Term.symIds e | none => [])
    | _ => []
  termination_by t => sizeOf t
  def Term.symIdsList : List Term → List Nat
    | [] => []
    | t :: ts => Term.symIds t ++ Term.symIdsList ts
  termination_by ts => sizeOf ts
end

/-! Rewrite every σ id by `f` — canonicalization's other half. -/
mutual
  def Term.renumberSyms (f : Nat → Nat) : Term → Term
    | .pvar x => match symOfName? x with | some σ => .pvar (symName (f σ)) | none => .pvar x
    | .cmpT τ => .cmpT (Term.renumberSyms f τ)
    | .lam y d b => .lam y (Term.renumberSyms f d) (Term.renumberSyms f b)
    | .pi y d b => .pi y (Term.renumberSyms f d) (Term.renumberSyms f b)
    | .sigmaT y d b => .sigmaT y (Term.renumberSyms f d) (Term.renumberSyms f b)
    | .borrowT y d b => .borrowT y (Term.renumberSyms f d) (Term.renumberSyms f b)
    | .app g a => .app (Term.renumberSyms f g) (Term.renumberSyms f a)
    | .idT a b c => .idT (Term.renumberSyms f a) (Term.renumberSyms f b) (Term.renumberSyms f c)
    | .ctorApp n args => .ctorApp n (Term.renumberSymsList f args)
    | .deref t => .deref (Term.renumberSyms f t)
    | .index t i ev => .index (Term.renumberSyms f t) (Term.renumberSyms f i)
        (match ev with | some e => some (Term.renumberSyms f e) | none => none)
    | .range t lo cnt rest ev eqc =>
      .range (Term.renumberSyms f t) (Term.renumberSyms f lo)
        (match cnt with | some c => some (Term.renumberSyms f c) | none => none)
        (match rest with | some r => some (Term.renumberSyms f r) | none => none)
        (match ev with | some e => some (Term.renumberSyms f e) | none => none)
        (match eqc with | some e => some (Term.renumberSyms f e) | none => none)
    | t => t
  termination_by t => sizeOf t
  def Term.renumberSymsList (f : Nat → Nat) : List Term → List Term
    | [] => []
    | t :: ts => Term.renumberSyms f t :: Term.renumberSymsList f ts
  termination_by ts => sizeOf ts
end

/-- **Refine `σ := repl` in a term** — ⇜'s substitution half. It is `substP` at
    the σ's name and nothing else: the rebinding guard `substP` carries is vacuous
    here (nothing binds a `§σ`-name), so the whole of refinement is the
    substitution the pure fragment already had. -/
def Term.substSym (σ : Nat) (repl : Term) (t : Term) : Term :=
  Term.substP (symName σ) repl t

/-! **Abstract a whole subterm `target` into the σ `σb`, everywhere** — §19's
    generalization at `Term` level, the inverse of `substSym` and keyed on a
    compound rather than an atom.

    No shadowing guard, and the reason is the reserved namespace rather than an
    omission: the targets are stuck spines over σ's, whose free names are all
    `§σ`-names, and no binder anywhere rebinds one. `absOcc`'s `shadowed` set
    would therefore be permanently empty.

    The comparison is `Term.alphaEq`, and it is MODE-SENSITIVE, where the `Val`
    sweep this replaces was mode-blind (`Val.beq` unwrapped `cmpT`). That is the
    house pattern rather than a change of heart: `absOcc` wants to see a marker,
    and the sites that must not — `piAgree`, `checkArm`, `sealRec`,
    `trivialOwedT` — strip with `.stripCmp` AT THE SITE and leave the equality
    honest. `alphaEq` keeps that: it has no case that unwraps `cmpT` on one side
    only, and it compares a binder's DOMAIN, which is where a mode lives. Stage V
    measured the difference unreachable by the corpus (zero divergences over the
    whole suite).

    **Why α and not names** (M33, closing M32's residual 4). The key was
    `Term.beq`, which compares binder NAMES, and `Pure.readback` names every
    binder it opens by its LEVEL. `generalizeStuck` normalizes the needle at depth
    0, so the needle's own binders are numbered from 0 — and an occurrence sitting
    one binder deeper reads back with them numbered from 1. Under a name key those
    are two terms, so a spine that itself BINDS missed its own occurrences under
    every λ, `cookForGen`'s cooked bodies included. Corpus spines bind routinely:
    `Leb a b` alone unfolds to a `natRec` over λ arms.

    The needle is a stuck spine over σ's; its free names are all `§σ`-names, which
    no binder rebinds, so comparing with EMPTY contexts on both sides is exact —
    a free name in the needle can only meet a free name in the occurrence. What α
    adds is that the needle's OWN binders are matched positionally, which is the
    whole of the fix.

    Two alternatives were considered and are recorded at the M33 commit: shifting
    the needle's `§`-names as the traversal descends (rejected — it assumes every
    binder the traversal crosses was counted by readback, and the swept state
    mixes declared syntax with normalized spines, so the assumption is false); and
    a de-Bruijn key computed on the fly (that IS this function, since `alphaEq` is
    de-Bruijn-on-the-fly, with no second representation to keep in step). -/
mutual
  def Term.abstractInto (target : Term) (σb : Nat) : Term → Term
    | .ctorApp n args =>
      if Term.alphaEq (.ctorApp n args) target then Term.sym σb
      else .ctorApp n (Term.abstractIntoList target σb args)
    | .app f a =>
      if Term.alphaEq (.app f a) target then Term.sym σb
      else .app (Term.abstractInto target σb f) (Term.abstractInto target σb a)
    | .idT a b c =>
      if Term.alphaEq (.idT a b c) target then Term.sym σb
      else .idT (Term.abstractInto target σb a) (Term.abstractInto target σb b)
        (Term.abstractInto target σb c)
    | .lam x d b =>
      if Term.alphaEq (.lam x d b) target then Term.sym σb
      else .lam x (Term.abstractInto target σb d) (Term.abstractInto target σb b)
    | .pi x d c =>
      if Term.alphaEq (.pi x d c) target then Term.sym σb
      else .pi x (Term.abstractInto target σb d) (Term.abstractInto target σb c)
    | .sigmaT x d c =>
      if Term.alphaEq (.sigmaT x d c) target then Term.sym σb
      else .sigmaT x (Term.abstractInto target σb d) (Term.abstractInto target σb c)
    | .borrowT x d c =>
      if Term.alphaEq (.borrowT x d c) target then Term.sym σb
      else .borrowT x (Term.abstractInto target σb d) (Term.abstractInto target σb c)
    -- A mode marker is never itself an abstraction target (it is not a term), so
    -- recurse straight through rather than testing it — `absOcc`'s precedent.
    | .cmpT τ => .cmpT (Term.abstractInto target σb τ)
    | .deref u =>
      if Term.alphaEq (.deref u) target then Term.sym σb
      else .deref (Term.abstractInto target σb u)
    | s => if Term.alphaEq s target then Term.sym σb else s
  termination_by t => sizeOf t
  def Term.abstractIntoList (target : Term) (σb : Nat) : List Term → List Term
    | [] => []
    | t :: ts => Term.abstractInto target σb t :: Term.abstractIntoList target σb ts
  termination_by ts => sizeOf ts
end

/-! ## Conversion equality: structural, and MODE-BLIND (M32 R1)

    `convert` is `nf a == nf b`, and `Val.beq` — the equality it used to be built
    on — unwrapped `cmpT` on either side so that no comptime judgment could
    observe a binder's mode (§6, "case is inert under ⇝"). `Term.beq` is
    deliberately mode-SENSITIVE (`absOcc` must see a marker), so conversion needs
    its own equality rather than inheriting one, and this is it: `Term.beq` plus
    the three `cmpT` arms.

    The alternative — modes part of type identity — was rejected on the calculus's
    own evidence and the evidence has not moved: the machine builds recursor
    premise types with no modes, and `ty{}`'s motive binders are capitalised by
    convention, so under a mode-sensitive conversion every one of those would have
    to agree on a mode that ⇝ has no use for. -/
mutual
  def Term.convEq : Term → Term → Bool
    | .cmpT a, .cmpT b => Term.convEq a b
    | .cmpT a, b => Term.convEq a b
    | a, .cmpT b => Term.convEq a b
    | .pvar x, .pvar y => x == y
    | .type, .type => true
    | .const n, .const m => n == m
    | .unit, .unit => true
    | .var x, .var y => x == y
    | .ctorApp n as, .ctorApp m bs => n == m && Term.convEqList as bs
    | .app a b, .app c d => Term.convEq a c && Term.convEq b d
    | .idT a b c, .idT d e f => Term.convEq a d && Term.convEq b e && Term.convEq c f
    | .lam x a b, .lam y c d => x == y && Term.convEq a c && Term.convEq b d
    | .pi x a b, .pi y c d => x == y && Term.convEq a c && Term.convEq b d
    | .sigmaT x a b, .sigmaT y c d => x == y && Term.convEq a c && Term.convEq b d
    | .borrowT x a b, .borrowT y c d => x == y && Term.convEq a c && Term.convEq b d
    | .deref a, .deref b => Term.convEq a b
    | .borrow a, .borrow b => Term.convEq a b
    -- Everything else is a runtime statement form, which cannot occur in a normal
    -- form; `beq` keeps the function total without a second scoping story.
    | a, b => Term.beq a b
  termination_by t u => sizeOf t + sizeOf u
  def Term.convEqList : List Term → List Term → Bool
    | [], [] => true
    | a :: as, b :: bs => Term.convEq a b && Term.convEqList as bs
    | _, _ => false
  termination_by ts us => sizeOf ts + sizeOf us
end

/-! ## Rendering (M32 R1)

    Knowledge prints where values used to, so this reproduces `Val.prettyPrec`
    case for case — including the two renderings that are about the ARRAY layer
    (`Arr` as `[…]`, `§segs` as `Arr⟨…⟩`) and the σ sigil, which is why a `pvar`
    asks `symOfName?` before falling back to `#name`. Rejections quote values, and
    a suite that asserts on distinctive substrings is what holds this to it. -/

/-- The literal index under an `@res` marker (a `Z`/`S` chain). Local to the
    renderer's pre-pass; `Term.natOf?` lives below the printer and cannot be
    reached from here. -/
private def resIdxOf? : Term → Option Nat
  | .ctorApp "Z" [] => some 0
  | .ctorApp "S" [t] => (resIdxOf? t).map (· + 1)
  | _ => none

/-- **`@res k` prints the way the programmer writes it** (M35 addendum). The
    kernel form of `*res` is the marker spine `@res k`, and a diagnostic that
    leaks it (a pin the discharge could not substitute — a value-returning pinned
    parameter, a D6 entailment mismatch quoting the raw pins) should speak the
    surface's language: `*res` when the term cites only the whole-result form,
    `*(fst res)`/`*(snd res)` when it cites a pair's components. The arity proxy
    is the term itself — a citation of index ≥ 1 is what says a pair is meant —
    since a printer has no signature in hand. Display-only: the rewrite emits a
    `.const` carrying the surface spelling, and it runs inside `Term.pretty`, so
    no stored term is touched. -/
partial def Term.resIndices : Term → List Nat
  | .app (.const "@res") idx => (resIdxOf? idx).toList
  | .app f a => Term.resIndices f ++ Term.resIndices a
  | .deref t => Term.resIndices t
  | .ctorApp _ args => args.flatMap Term.resIndices
  | .pi _ d c | .sigmaT _ d c | .borrowT _ d c => Term.resIndices d ++ Term.resIndices c
  | .lam _ d b => Term.resIndices d ++ Term.resIndices b
  | .idT a b c => Term.resIndices a ++ Term.resIndices b ++ Term.resIndices c
  | .cmpT τ => Term.resIndices τ
  | _ => []

partial def Term.resSugarGo (paired : Bool) : Term → Term
  | .app (.const "@res") idx =>
    (match resIdxOf? idx with
     | some k =>
       if !paired then .const "*res"
       else if k == 0 then .const "*(fst res)"
       else if k == 1 then .const "*(snd res)"
       else .const s!"*(res {k})"
     | none => .app (.const "@res") idx)
  | .app f a => .app (Term.resSugarGo paired f) (Term.resSugarGo paired a)
  | .deref t => .deref (Term.resSugarGo paired t)
  | .ctorApp n args => .ctorApp n (args.map (Term.resSugarGo paired))
  | .pi x d c => .pi x (Term.resSugarGo paired d) (Term.resSugarGo paired c)
  | .sigmaT x d c => .sigmaT x (Term.resSugarGo paired d) (Term.resSugarGo paired c)
  | .borrowT n d c => .borrowT n (Term.resSugarGo paired d) (Term.resSugarGo paired c)
  | .lam x d b => .lam x (Term.resSugarGo paired d) (Term.resSugarGo paired b)
  | .idT a b c => .idT (Term.resSugarGo paired a) (Term.resSugarGo paired b) (Term.resSugarGo paired c)
  | .cmpT τ => .cmpT (Term.resSugarGo paired τ)
  | t => t

/-- The renderer's pre-pass: identity for any `@res`-free term. -/
def Term.resSugar (t : Term) : Term :=
  match Term.resIndices t with
  | [] => t
  | ks => Term.resSugarGo (ks.any (· ≥ 1)) t

mutual
  def Term.prettyPrec (prec : Nat) : Term → String
    | .pvar x => match symOfName? x with | some σ => s!"σ{subNat σ}" | none => s!"#{x}"
    | .type => "Type"
    | .const c => c
    | .unit => "()"
    | .var x => s!"{x.name}#{x.id}"
    | .cmpT τ => "⇝" ++ Term.prettyPrec 1 τ
    | .ctorApp "Arr" vs => "[" ++ Term.prettyCommas vs ++ "]"
    | .ctorApp "§segs" segs => "Arr⟨" ++ Term.prettyCommas segs ++ "⟩"
    | .ctorApp "§seg" [c, b] => Term.prettyPrec 1 c ++ " ▷ " ++ Term.prettyPrec 0 b
    | .ctorApp name [] => name
    | .ctorApp name args =>
      let s := name ++ Term.prettyArgs args
      if prec > 0 then s!"({s})" else s
    | .pi x d c =>
      let s := s!"Π({x} : {Term.prettyPrec 1 d}). {Term.prettyPrec 0 c}"
      if prec > 0 then s!"({s})" else s
    | .sigmaT x d c =>
      let s := s!"Σ({x} : {Term.prettyPrec 1 d}). {Term.prettyPrec 0 c}"
      if prec > 0 then s!"({s})" else s
    -- **One former, two renderings, and the same property picks them** (M32 R2).
    -- A comptime λ prints as the term it is. An imperative one prints its BINDERS
    -- and elides what is under them — a rejection naming a function wants to say
    -- WHICH function, and the body is a whole program — which is what `lamR`/`rfn`
    -- printed and is why `slotOf`'s goldens are unchanged.
    | .lam x d b =>
      if Term.lamImperative (.lam x d b) then
        -- No paren guard, exactly as `lamR`/`rfn` had none: the form brackets
        -- itself, and `slotOf`'s golden spells it unparenthesized in argument
        -- position.
        "λr(" ++ String.intercalate ", " ((Term.peelLams (.lam x d b)).1.map (·.1.name)) ++ "){…}"
      else
        let s := s!"λ({x.name} : {Term.prettyPrec 1 d}). {Term.prettyPrec 0 b}"
        if prec > 0 then s!"({s})" else s
    | .app f a =>
      let s := Term.prettyPrec 0 f ++ " " ++ Term.prettyPrec 1 a
      if prec > 0 then s!"({s})" else s
    | .idT _ a b =>
      let s := s!"Id {Term.prettyPrec 1 a} {Term.prettyPrec 1 b}"
      if prec > 0 then s!"({s})" else s
    | .borrowT x τ S =>
      let s := s!"&mut ({x} : {Term.prettyPrec 0 τ} ↝ {Term.prettyPrec 0 S})"
      if prec > 0 then s!"({s})" else s
    | .deref t => "*" ++ Term.prettyPrec 1 t
    | .borrow t => "&mut " ++ Term.prettyPrec 1 t
    | .seal _ t _ => "(" ++ Term.prettyPrec 0 t ++ " : …)"
    | .marker n e => "@" ++ n ++ "(" ++ Term.prettyPrec 0 e ++ ")"
    | .call f _ => f ++ "(…)"
    | .index t i _ => Term.prettyPrec 1 t ++ "[" ++ Term.prettyPrec 0 i ++ "]"
    | .range t lo _ _ _ _ => Term.prettyPrec 1 t ++ "[" ++ Term.prettyPrec 0 lo ++ " ; …]"
    | .letIn x _ => s!"let {x.name} = …"
    | .assign _ _ => "… := …"
    | .seq _ _ => "… ; …"
    | .matchE x _ _ => s!"match {x.name} " ++ "{…}"
  termination_by t => sizeOf t
  def Term.prettyArgs : List Term → String
    | [] => ""
    | a :: as => " " ++ Term.prettyPrec 1 a ++ Term.prettyArgs as
  termination_by as => sizeOf as
  def Term.prettyCommas : List Term → String
    | [] => ""
    | [a] => Term.prettyPrec 0 a
    | a :: as => Term.prettyPrec 0 a ++ ", " ++ Term.prettyCommas as
  termination_by as => sizeOf as
end

/-- Doc-trace rendering of a term (top level, no surrounding parens). -/
def Term.pretty (t : Term) : String := Term.prettyPrec 0 (Term.resSugar t)

/-! ## Numerals and the small constructor vocabulary, at `Term` level

    The twins of `Val.zero`/`succ`/`nat`/`nil`/`cons`, which now build knowledge
    leaves through the skeleton's smart constructor while these build the
    knowledge itself. Numerals abbreviate `Nat` (doc §1.1), so they are sugar
    rather than a form. -/

/-- `Z`, the numeral zero. -/
def Term.zero : Term := .ctorApp "Z" []
/-- Successor. -/
def Term.succ (t : Term) : Term := .ctorApp "S" [t]
/-- Church-style `Nat` numeral abbreviation. -/
def Term.nat : Nat → Term
  | 0 => Term.zero
  | n + 1 => Term.succ (Term.nat n)
/-- The empty list. -/
def Term.nil : Term := .ctorApp "Nil" []
/-- List cons. -/
def Term.cons (h t : Term) : Term := .ctorApp "Cons" [h, t]

/-- Read a `Nat` term as a Lean numeral, if it is concrete. -/
def Term.natOf? : Term → Option Nat
  | .ctorApp "Z" [] => some 0
  | .ctorApp "S" [n] => (Term.natOf? n).map (· + 1)
  | _ => none

/-! ## Seal sites (M32 R3, suspensions.md §2.4)

    A seal's SITE is its identity as a program point, and `numberSeals` is what
    assigns one. It runs at the program boundary — after every macro, on the
    finished term — and numbers the seals in the order a left-to-right traversal
    meets them, which for a `let`-chain is the order they are evaluated in.

    **Why a pass and not a counter in the elaborator.** §6's sharp edge asks for
    a site identity stable across macro expansion and α-canonicalization. A pass
    over the elaborated term gets both by construction rather than by argument:
    it runs after expansion, so nothing a macro does can move a site; and it
    reads STRUCTURE, never a name, so renaming a binder cannot move one either.
    A counter threaded through `Uni.elabUTerm` would have neither property —
    `fnElab` is not in that monad at all, and it is where most seals come from.

    The field the elaborators write is therefore not the site: they write `0` and
    this pass overwrites it. That is deliberate — a `Term` that has not been
    through the boundary has no sites, and giving it fake ones would let a
    hand-written term silently share an identity with a real one. -/

mutual
  /-- Number the seals in `t`, starting at `n`; returns the next free site. -/
  def Term.numberSealsGo (n : Nat) : Term → (Nat × Term)
    -- Markers are stripped BEFORE this pass at the program boundary
    -- (`Machine.atBoundary`); the row exists for totality and for direct calls
    -- on unstripped terms, and numbers through the marker transparently.
    | .marker nm e =>
      let (n1, e') := Term.numberSealsGo n e
      (n1, .marker nm e')
    | .seal _ t u =>
      -- The site is taken BEFORE the children are numbered, so a seal's own
      -- number is smaller than any seal nested inside it — which is the order
      -- evaluation reaches them (the outer node is entered first) and the order
      -- a reader of `§σ` ids would expect.
      let (n1, t') := Term.numberSealsGo (n + 1) t
      let (n2, u') := Term.numberSealsGo n1 u
      (n2, .seal n t' u')
    | .letIn x a =>
      let (n1, a') := Term.numberSealsGo n a
      (n1, .letIn x a')
    | .assign a b =>
      let (n1, a') := Term.numberSealsGo n a
      let (n2, b') := Term.numberSealsGo n1 b
      (n2, .assign a' b')
    | .ctorApp c args =>
      let (n1, args') := Term.numberSealsList n args
      (n1, .ctorApp c args')
    | .call f args =>
      let (n1, args') := Term.numberSealsList n args
      (n1, .call f args')
    | .matchE x eqn brs =>
      let (n1, brs') := Term.numberSealsBranches n brs
      (n1, .matchE x eqn brs')
    | .seq a b =>
      let (n1, a') := Term.numberSealsGo n a
      let (n2, b') := Term.numberSealsGo n1 b
      (n2, .seq a' b')
    | .app a b =>
      let (n1, a') := Term.numberSealsGo n a
      let (n2, b') := Term.numberSealsGo n1 b
      (n2, .app a' b')
    | .lam x d b =>
      let (n1, d') := Term.numberSealsGo n d
      let (n2, b') := Term.numberSealsGo n1 b
      (n2, .lam x d' b')
    | .pi x d c =>
      let (n1, d') := Term.numberSealsGo n d
      let (n2, c') := Term.numberSealsGo n1 c
      (n2, .pi x d' c')
    | .sigmaT x d c =>
      let (n1, d') := Term.numberSealsGo n d
      let (n2, c') := Term.numberSealsGo n1 c
      (n2, .sigmaT x d' c')
    | .borrowT x d c =>
      let (n1, d') := Term.numberSealsGo n d
      let (n2, c') := Term.numberSealsGo n1 c
      (n2, .borrowT x d' c')
    | .idT a b c =>
      let (n1, a') := Term.numberSealsGo n a
      let (n2, b') := Term.numberSealsGo n1 b
      let (n3, c') := Term.numberSealsGo n2 c
      (n3, .idT a' b' c')
    | .borrow a => let (n1, a') := Term.numberSealsGo n a; (n1, .borrow a')
    | .deref a => let (n1, a') := Term.numberSealsGo n a; (n1, .deref a')
    | .cmpT a => let (n1, a') := Term.numberSealsGo n a; (n1, .cmpT a')
    | .index a i k =>
      let (n1, a') := Term.numberSealsGo n a
      let (n2, i') := Term.numberSealsGo n1 i
      (n2, .index a' i' k)
    | .range a lo cnt p q r =>
      let (n1, a') := Term.numberSealsGo n a
      let (n2, lo') := Term.numberSealsGo n1 lo
      let (n3, cnt') := Term.numberSealsOpt n2 cnt
      (n3, .range a' lo' cnt' p q r)
    | t => (n, t)
  def Term.numberSealsList (n : Nat) : List Term → (Nat × List Term)
    | [] => (n, [])
    | t :: ts =>
      let (n1, t') := Term.numberSealsGo n t
      let (n2, ts') := Term.numberSealsList n1 ts
      (n2, t' :: ts')
  def Term.numberSealsOpt (n : Nat) : Option Term → (Nat × Option Term)
    | none => (n, none)
    | some t => let (n1, t') := Term.numberSealsGo n t; (n1, some t')
  def Term.numberSealsBranches (n : Nat) : List Branch → (Nat × List Branch)
    | [] => (n, [])
    | .mk c bs body :: rest =>
      let (n1, body') := Term.numberSealsGo n body
      let (n2, rest') := Term.numberSealsBranches n1 rest
      (n2, .mk c bs body' :: rest')
end

/-- The boundary pass: number every seal in a program, and report how many there
    were. The count is not a supply the machine has to start above — sites live
    in their own space and are `St.sealSites`' key, never a σ id — it is there so
    a test can say "this program has a seal" before asserting about the seal. -/
def Term.numberSeals (t : Term) : (Nat × Term) := Term.numberSealsGo 0 t

/-! ## Markers: the one traversal, and what is derived from it (docs/21)

    A marker names a claim site and means its body. Everything marker-shaped —
    the boundary strip, the twin-minting replacement — is one full traversal
    with a different action at the marker node, so the row list lives ONCE
    (`mapMarkersGo`) and mirrors `numberSealsGo`'s exactly: same rows, same
    left-to-right order, an accumulator threaded the same way. A row added to
    one traversal without the other is a bug this comment is trying to make
    findable. -/

mutual
  /-- Walk `t` and apply `f` at every marker node — the accumulator, the
      marker's name, and its already-mapped BODY (children first, so nested
      markers are resolved inside-out). `f`'s result replaces the whole marker
      node and is NOT re-traversed: a replacement is an output, and re-walking
      it would let a replacement body containing the target name loop or
      double-count. -/
  def Term.mapMarkersGo {σ : Type} (f : σ → String → Term → (σ × Term)) (s : σ) : Term → (σ × Term)
    | .marker nm e =>
      let (s1, e') := Term.mapMarkersGo f s e
      f s1 nm e'
    | .seal k t u =>
      let (s1, t') := Term.mapMarkersGo f s t
      let (s2, u') := Term.mapMarkersGo f s1 u
      (s2, .seal k t' u')
    | .letIn x a b =>
      let (s1, a') := Term.mapMarkersGo f s a
      let (s2, b') := Term.mapMarkersGo f s1 b
      (s2, .letIn x a' b')
    | .assign a b c =>
      let (s1, a') := Term.mapMarkersGo f s a
      let (s2, b') := Term.mapMarkersGo f s1 b
      let (s3, c') := Term.mapMarkersGo f s2 c
      (s3, .assign a' b' c')
    | .ctorApp c args =>
      let (s1, args') := Term.mapMarkersList f s args
      (s1, .ctorApp c args')
    | .call fn args =>
      let (s1, args') := Term.mapMarkersList f s args
      (s1, .call fn args')
    | .matchE x eqn brs =>
      let (s1, brs') := Term.mapMarkersBranches f s brs
      (s1, .matchE x eqn brs')
    | .seq a b =>
      let (s1, a') := Term.mapMarkersGo f s a
      let (s2, b') := Term.mapMarkersGo f s1 b
      (s2, .seq a' b')
    | .app a b =>
      let (s1, a') := Term.mapMarkersGo f s a
      let (s2, b') := Term.mapMarkersGo f s1 b
      (s2, .app a' b')
    | .lam x d b =>
      let (s1, d') := Term.mapMarkersGo f s d
      let (s2, b') := Term.mapMarkersGo f s1 b
      (s2, .lam x d' b')
    | .pi x d c =>
      let (s1, d') := Term.mapMarkersGo f s d
      let (s2, c') := Term.mapMarkersGo f s1 c
      (s2, .pi x d' c')
    | .sigmaT x d c =>
      let (s1, d') := Term.mapMarkersGo f s d
      let (s2, c') := Term.mapMarkersGo f s1 c
      (s2, .sigmaT x d' c')
    | .borrowT x d c =>
      let (s1, d') := Term.mapMarkersGo f s d
      let (s2, c') := Term.mapMarkersGo f s1 c
      (s2, .borrowT x d' c')
    | .idT a b c =>
      let (s1, a') := Term.mapMarkersGo f s a
      let (s2, b') := Term.mapMarkersGo f s1 b
      let (s3, c') := Term.mapMarkersGo f s2 c
      (s3, .idT a' b' c')
    | .borrow a => let (s1, a') := Term.mapMarkersGo f s a; (s1, .borrow a')
    | .deref a => let (s1, a') := Term.mapMarkersGo f s a; (s1, .deref a')
    | .cmpT a => let (s1, a') := Term.mapMarkersGo f s a; (s1, .cmpT a')
    | .index a i k =>
      let (s1, a') := Term.mapMarkersGo f s a
      let (s2, i') := Term.mapMarkersGo f s1 i
      (s2, .index a' i' k)
    | .range a lo cnt p q r =>
      let (s1, a') := Term.mapMarkersGo f s a
      let (s2, lo') := Term.mapMarkersGo f s1 lo
      let (s3, cnt') := Term.mapMarkersOpt f s2 cnt
      (s3, .range a' lo' cnt' p q r)
    | t => (s, t)
  def Term.mapMarkersList {σ : Type} (f : σ → String → Term → (σ × Term)) (s : σ) : List Term → (σ × List Term)
    | [] => (s, [])
    | t :: ts =>
      let (s1, t') := Term.mapMarkersGo f s t
      let (s2, ts') := Term.mapMarkersList f s1 ts
      (s2, t' :: ts')
  def Term.mapMarkersOpt {σ : Type} (f : σ → String → Term → (σ × Term)) (s : σ) : Option Term → (σ × Option Term)
    | none => (s, none)
    | some t => let (s1, t') := Term.mapMarkersGo f s t; (s1, some t')
  def Term.mapMarkersBranches {σ : Type} (f : σ → String → Term → (σ × Term)) (s : σ) : List Branch → (σ × List Branch)
    | [] => (s, [])
    | .mk c bs body :: rest =>
      let (s1, body') := Term.mapMarkersGo f s body
      let (s2, rest') := Term.mapMarkersBranches f s1 rest
      (s2, .mk c bs body' :: rest')
end

/-- Erase every marker: `@name(e)` becomes `e`. Runs FIRST at the program
    boundary (`Machine.atBoundary`), before seal numbering — the ordering
    docs/21 §6 states once — so the machine provably never sees a marker. -/
def Term.stripMarkers (t : Term) : Term :=
  (Term.mapMarkersGo (fun _ _ e => ((), e)) () t).2

/-- Swap the BODY of the marker named `name` for `repl`, keeping the marker
    node — the twin stays addressable, and strip-transparency covers the
    replacement. Fails unless EXACTLY ONE marker of that name exists (the
    Edit-tool contract, docs/21 §3): zero hits and multiple hits are loud
    errors that also say which markers the term DOES have, so a renamed claim
    site can never make a twin silently test nothing. -/
def Term.replaceMarked? (name : String) (repl : Term) (t : Term) : Except String Term :=
  let ((hits, seen), t') := Term.mapMarkersGo
    (fun (acc : Nat × List String) nm e =>
      let (hits, seen) := acc
      if nm == name then ((hits + 1, seen ++ [nm]), .marker nm repl)
      else ((hits, seen ++ [nm]), .marker nm e))
    (0, []) t
  let present := if seen.isEmpty then "none" else String.intercalate ", " (seen.map (fun n => s!"'{n}'"))
  match hits with
  | 1 => .ok t'
  | 0 => .error s!"marker '{name}' not found — markers present: {present}"
  | n => .error s!"marker '{name}' occurs {n} times (must be exactly one) — markers present: {present}"

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

/-! ### `Term.clam`/`Term.cpi` — RETIRED at M33 macro-top, having run out of work

    §2.1 makes a binder's NAME its mode and `binderDom`/`markDom` puts the
    matching `⇝` on its domain, so the two halves of a comptime binder must be
    written together. R3b built `clam`/`cpi` to make that unforgettable in the one
    place there was no elaborator to enforce it: the kernel's own library terms
    (`Std.lenFn`, `Pure.kLeFn`, …) were hand-written `Term`s with no macro between
    them and the datatype.

    **There are none left.** With the surface below the kernel, `Pure` and `Std`
    are written in `ty{ }` and every comptime binder in them goes through
    `binderDom` like every other binder in the language. The constructors' call
    count went to zero and they are gone with it — measured, not assumed. If a
    hand-written comptime binder ever comes back, this paragraph is the reason to
    reconsider whether it should.

    The UNUSED binder is the other half of the convention and needs no marker:
    `Surface.unusedSnapName` is what the surface mints for a non-dependent arrow's
    domain, for a non-dependent pair's, and for a motive nothing refers to, and a
    name in the reserved namespace carries no mode because nothing can cite it. -/

/-! ## Peeling a Π into a telescope (M26-C; moved here at M33 macro-top)

    §5's audit relocation needs a sealed type as a **telescope plus a return
    type**, because that is the shape `seedTelescopeV` seeds and `auditAction`
    audits. Deriving one from a Π is ordinary binder-peeling — except that it has
    to happen on `Term`s, since a borrow-moded Π has no `Val` (see `St.fsig`).
    `Term.substP` is what that costs, and since M30 step 2 that is a name-keyed
    substitution with no lifting, because every substituend here is a runtime
    variable and a term with no free PURE names cannot be captured.

    **It lives in `Syntax.lean` because it is a function of `Term` and nothing
    else** — `domComptime`, `substP`, `stripCmp` and a `Var`'s case are its whole
    vocabulary. It sat in `Machine.lean` for eleven milestones, and the only cost
    of that was structural: `FnMacro` needed it, so the SURFACE had to import the
    kernel, and the one real edge from the macro layer up into the machine was
    this function's address. -/

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
    | .pi y dom cod =>
      if Term.domComptime dom != x.isComptime then
        .error s!"seal: binder '{x.name}' is {if x.isComptime then "capitalized (comptime, §6)" else "lowercase (runtime, §6)"} but the ascribed type binds it as {if Term.domComptime dom then "comptime (⇝τ)" else "runtime"}. A binder's mode is a claim about whether the body may observe its argument at runtime, and the ascription is what callers are promised — the two cannot differ."
      else
        match piPeel xs (Term.substP y (.var x) cod) with
        | .ok (rest, ret) => .ok ((x, dom.stripCmp) :: rest, ret)
        | .error e => .error e
    | _ =>
      .error s!"seal: the runtime λ binds '{x.name}' but the ascribed type has no Π binder left for it. Runtime application is saturated (§12 decision 4), so a λ and its ascription must have the same arity — either the λ binds too much or the ascription promises too little."

/-! ## The let-arrow invariant (M31 Stage A; exceptionless since M32 R3)

    **A capital `let` ⇝-reads its right-hand side; a lowercase `let` ⇒-reads it.**

    That sentence is the whole rule, and `Var.comptimeRhs` — the predicate that
    used to carry its exceptions — is gone, because `Var.isComptime` at the two
    reading sites says it with nothing left over. The two carve-outs it held were
    both of the same shape: a right-hand side that was not a READING at all but a
    ⇒-FORMATION EVENT, producing a value ⇝ had no rule to produce. R3 gave ⇝ the
    rules instead of giving the invariant exceptions —

      * `(t : T)` was ⇒ because the seal mints a fresh σ and minting needs an
        event. It is ⇝'s now because the σ is no longer fresh: it is the one the
        seal's SITE has at its inputs (`sealNode`, suspensions.md §2.4).
      * `λ(x : τ, …){ … }` was ⇒ because a runtime λ's formation is where its
        closedness is checked and where its value comes into being. It is ⇝'s
        now because formation IS a ⇝ event and always was — R2 made both
        fragments one closure, and R3 moved the one arm that built it out of ⇒
        (`readComptimeVal`), which is what leaves ⇒ unable to construct a
        function at all (§2.5).

    — so the arrow is a property of the BINDER, and of nothing else. -/

end Dllbc
