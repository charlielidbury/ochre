import Lean
import Dllbc.FnMacro

/-!
# `uterm` / `ublk` — THE term grammar

One grammar, and there is one way in: `prog{ }` (ProgMacro.lean) is `ublk`,
elaborated in the empty context. `fn` is a STATEMENT of `ublk` (M28 θ), so a
declaration is written where a `let` is written and there is no separate
declaration surface to learn.

**THERE IS EXACTLY ONE MACRO** (M29 γ). There were two — `prog{ }` and `pure{ }`,
the same call to this elaborator differing by one boolean, "is this position
consumed by ⇒ or ⇝". The flag had two readers, `let` and `&mut`, and M29 α and β
removed both; with no readers it deleted, and the two macros became the same
function of the same argument. (`decl{ }`, the legacy declaration former, went in
M28 D9.) The elaborator's namespace is `Surface`, which is what it always was.

**A term's fragment is not a property of where it was written.** It is a property
of which arrow CONSUMES it, and the same term can be consumed by both — `len *v`
is a legal body and a legal type. Two macros made that unsayable at the surface
even though the kernel had always known it. What remains of the distinction is
`reflectC`'s refusal list (⇝'s, and this calculus's definition of the pure
sub-grammar) and `readR`'s (⇒'s), each of which names the form it refuses and
gives the reason — which a mode flag could not do.

## Type positions

Telescope entry types, the return type, and the `↝` right-hand side elaborate
through the same `uterm` as everything else — Σ/Π/λ/→/Id/application/`Type` —
extended with two things the boundary needs:

  * a **runtime-var context**: the names of EARLIER telescope parameters resolve
    to `.var ⟨i, name⟩` with positional 0-based ids — the exact convention
    `seedTelescope` seeds (argument `i` ↦ var id `i`) and the corpus's `V i "…"`
    references use. Runtime vars are absolute ids, so crossing a Σ/Π/λ binder
    does NOT shift them (matching §5.2: a runtime var in a type is resolved by ⇝
    to its snapshot, never a pure binder).
  * `*x` in type position → `.deref (.var ⟨i, name⟩)` — the comptime deref the
    corpus writes as `dv`/`lenT (.deref (.var vv))`.

`&mut τ` (the borrow TYPE — the OPERATION is `&m e`, M29 β) is
`borrowT τ (weaken τ)` (the corpus's plain-borrow encoding; for the
closed telescope types in the corpus `weaken τ` computes to `τ`, so the produced
value is identical). `&mut (τ ~> S)` gives an S that ignores the snapshot;
`&mut (s : τ ~> S)` binds `s` as pure var 0 in `S` — the `borrowT`/`seedTelescope`
convention in Syntax.lean.

## Resolution discipline (och's law)

Every identifier resolves or errors: pure binder → `pvar`; earlier telescope
param → `var`; known constructor → `ctorApp`; kernel const → `const`; a friendly
reified-function alias (`Le`, `Len`, `Add`, …) → its `…FnT` Term constant; else
the **Lean identifier** of that name, which must denote a `Dllbc.Term` in scope
(a library lemma like `SwapL`, `Set`, `SortRangeL`) — the documented fallback.

## Body

A function's body is `ublk` with the telescope names pre-bound in
order at ids `0 .. n-1` and fresh binders minted from `n`, the `seedTelescope`
convention. That is the only place in the surface where a name arrives pre-bound.
Bodies laden with pure proof terms (a `botElim` ex-falso branch, a `LeRwR` bound
derivation) can be spliced whole with `%term`, which is a `uterm` and therefore a
block's final expression — the escape hatch `decl{ … = %t }` used to provide,
available uniformly wherever an expression is.
-/

open Lean

namespace Dllbc

/-! ## The unified `uterm` / `ublk` grammar (§ phase-3 point 1 — ONE term grammar)

A single expression grammar spanning BOTH fragments, elaborated by one function
with no mode parameter. The flag it used to carry had exactly two readers, and
each was removed by giving the kernel the rule the surface had been standing in
for:

  * **`let`** (M29 α) emitted a `.letIn` in one mode and a β-redex over a fresh
    binder in the other. One row emits `.letIn` and the kernel reads it under both
    arrows; ⇝'s reading of it IS that β, built at reflection.
  * **`&mut`** (M29 β) was the borrow OPERATION in one mode and the borrow TYPE in
    the other. They are spelled `&m` and `&mut` now, so each row emits its own
    node whatever surrounds it.

Every form is therefore shared: application spines, λ/Π/Σ/→/Id/`Type`, `*e`, `Id`,
`let`, `&m`, `&mut`, `fn`, constructor/const/lemma references. `ublk` is the
statement layer.

**The one disambiguation rule (§ point 2):** `f(a, b)` — an identifier with a
**no-whitespace** paren argument list — is a runtime **call** (lowercase head) or
**ctorApp** (uppercase). Space-separated **juxtaposition** `f a b` (incl.
`f (a) b`) is **pure application** (`ctorApp` when the head is a known ctor). So
`Nth(&m *tl, k, p)` is a call, `botElim Unit p` and `LeRwR (S x) y` are
application spines, `S(*l)` / `S *l` both mean `ctorApp "S" [*l]`. -/

declare_syntax_cat uterm
declare_syntax_cat ublk
declare_syntax_cat uarm
declare_syntax_cat uarmBody

syntax:max ident : uterm
syntax:max num : uterm
syntax:max "(" ")" : uterm                                    -- unit
syntax:max "(" uterm ")" : uterm                             -- grouping
syntax:max "Type" : uterm
syntax:max "%" term:max : uterm                              -- splice a Lean `Term`
syntax:max "*" uterm:max : uterm                            -- deref / peel
syntax:max "old" "*" uterm:max : uterm                      -- §5.4 old *v: entry snapshot of a borrow-param deref
syntax:max "Id" uterm:max uterm:max uterm:max : uterm        -- Id A a b
syntax:max ident noWs "(" uterm,* ")" : uterm                -- call / ctorApp (NO space before `(`)
-- ¶2.1's two new place steps. They bind TIGHTER than the peel, so a reborrow of a
-- range through a borrow is written `&m (*v)[lo ; cnt]` and `*v[i]` would mean
-- `*(v[i])` — peel the borrow stored AT slot `i`, which is how an `Array n (&mut T)`
-- is reached. `| h` cites the containment evidence (¶3.2's supply route 2); without
-- it the bound must compute (route 1). Offset-and-count, never lower-and-upper.
syntax:max uterm:max noWs "[" uterm "]" : uterm                         -- a[i]
syntax:max uterm:max noWs "[" uterm "|" uterm "]" : uterm               -- a[i | h]
syntax:max uterm:max noWs "[" uterm ";" uterm "]" : uterm               -- a[lo ; cnt]
syntax:max uterm:max noWs "[" uterm ";" uterm "|" uterm "]" : uterm     -- a[lo ; cnt | h]
-- `a[lo ; ..]` — to the end of the segment starting at `lo`. NAMES premise (3)'s
-- residue rather than computing `sub n lo`; without it ¶3.4's second borrow is
-- unwritable, since the doc spells it `[k ; rest]` and `rest` is a machine-minted σ.
syntax:max uterm:max noWs "[" uterm ";" ".." "]" : uterm                -- a[lo ; ..]
-- ROUTE (a): `a[lo ; cnt ; rest | h]` SUPPLIES the residue's extent instead of letting
-- premise (3) mint a σ no binder can name. Same solution transition, still no `sub`;
-- omit it and the checker mints, exactly as before. Third instance of the house
-- pattern after `[k]` and `match h :` — an optional surface element reifying a fact
-- the checker already has, declared rather than inferred, free when absent.
syntax:max uterm:max noWs "[" uterm ";" uterm ";" uterm "]" : uterm            -- a[lo ; cnt ; rest]
syntax:max uterm:max noWs "[" uterm ";" uterm ";" uterm "|" uterm "]" : uterm  -- a[lo ; cnt ; rest | h]
-- …and the DECOMPOSITION CITATION. A supplied residue asserts a decomposition of the
-- leaf's extent; when that extent is a telescope parameter's σ, the assertion is a
-- constraint on the function's CALLERS, and premise (3) may not impose it by
-- unification (M7/M8's inferred constrained wire; M17's lesson that cross-boundary
-- constraints are DECLARED and checked). The program cites the equation and premise (3)
-- solves along it. Free when the decomposition already holds by conversion.
syntax:max uterm:max noWs "[" uterm ";" uterm ";" uterm "|" uterm "|" uterm "]" : uterm
-- **THE OPERATION AND THE TYPE ARE SPELLED DIFFERENTLY** (M29 β). `&m e` mints a
-- loan on the place `e`; `&mut τ` is the type of a borrow of a `τ`. They used to
-- share the spelling `&mut` and be told apart by the elaboration mode, which was
-- the second and last of the two things that flag decided.
--
-- Conflating them was an ARROW dispatch on what are genuinely two operations, and
-- the borrowed spelling is what made it look otherwise: Rust writes `&mut` for
-- both because in Rust a type and a term can never occupy the same position, and
-- in a dependently-typed language they can. A future ⇝-construction of a mutable
-- reference — building a borrow type's inhabitant in the comptime fragment — is
-- conceivable, and under the old rule it would have been unwritable, because the
-- only spelling for the operation was the one the arrow had already claimed for
-- the type. The attachment to Rust's spelling for the OP was aesthetic.
syntax:70 "&m" uterm:65 : uterm                              -- &m e : the borrow OPERATION
syntax:70 "&mut" uterm:65 : uterm                            -- &mut τ : the borrow TYPE
syntax:70 "&mut" "(" uterm "~>" uterm ")" : uterm            -- borrow type &mut (τ ↝ S)
syntax:70 "&mut" "(" ident ":" uterm "~>" uterm ")" : uterm  -- borrow type &mut (s : τ ↝ S)
syntax:65 uterm:65 uterm:66 : uterm                          -- application (juxtaposition)
syntax:10 "λ" "(" ident ":" uterm ")" "." uterm:10 : uterm   -- lambda
-- M26-C's runtime λ (combining-fns §7 cost 2). Written `λ(x : τ, y : υ) { … }` —
-- a comma-separated binder TELESCOPE and a braced BODY, against the pure λ's
-- single binder and dotted term. The two are told apart by shape alone, which is
-- the right marker: what differs is not the arity but the fragment — the pure λ's
-- body is a term ⇝ reduces by substitution, this one's is a body ⇒ runs by
-- binding Ω slots.
--
-- **The binders carry types** (M27). M26-C wrote them bare on the argument that
-- the ascription is the contract (§5 point 4) and an annotation would be a second
-- source of truth; that is right about the contract and wrong about the check,
-- which without domains has to descend the ascription bidirectionally and with
-- them is one conversion. The document's grammar wrote `λ (x : τ). t` from the
-- start — this is the surface returning to it, not a new decision.
declare_syntax_cat ulamb
syntax ident ":" uterm : ulamb
syntax:max "λ" "(" ulamb,* ")" "{" ublk "}" : uterm          -- an imperative λ
syntax:10 "Π" "(" ident ":" uterm ")" "→" uterm:10 : uterm   -- Pi
syntax:10 "Σ" "(" ident ":" uterm ")" "→" uterm:10 : uterm   -- Sigma (arrow form)
syntax:10 "Σ" "(" ident ":" uterm ")" "." uterm:10 : uterm   -- Sigma (dot form)
-- **Σ0 — the COMPTIME TAIL** (M33, suspensions.md §2.7). Same pair, same
-- constructor, same eliminator: the only difference from `Σ` is that the
-- CODOMAIN is marked `⇝`, which makes the second projection comptime. DLLBC's
-- subset type, with the standard precedent (Lean's `{x : A // P}`, Coq's `sig`,
-- NuPRL/PVS set types) and comptime where those use Prop/irrelevance.
syntax:10 "Σ0" "(" ident ":" uterm ")" "→" uterm:10 : uterm  -- Sigma0 (arrow form)
syntax:10 "Σ0" "(" ident ":" uterm ")" "." uterm:10 : uterm  -- Sigma0 (dot form)
syntax:10 uterm:11 "→" uterm:10 : uterm                      -- non-dependent arrow
-- **The non-dependent PAIR** (M33 macro-top), which is to `Σ` what `→` is to `Π`
-- and which the grammar simply did not have. Every Σ row above demands a binder,
-- so a pair whose second component does not depend on its first had to invent a
-- name — and inventing one is not neutral: a NAMED binder has a case, a case is a
-- mode, and a mode on a Σ domain routes the component's read (§2.7). There was no
-- spelling for "this component's mode is nobody's business", which is exactly
-- what the kernel's own `Sorted` says by writing `§_` — the reserved binder the
-- surface already mints for `→`, carrying no mode because nothing can cite it.
-- Found by respelling `Std.SortedFn`, whose `Bound h t × Sorted t` is the
-- corpus's one non-dependent Σ.
syntax:20 uterm:21 "×" uterm:20 : uterm                      -- non-dependent Σ
-- M26-A's seal (combining-fns §5), written as ASCRIPTION (M28 ξ). Still a
-- parenthesized NODE, not a juxtaposition spine, so it can never be mistaken for
-- (or produced by) an application: the grammar keeps the seal apart at the surface
-- for the same reason `Term.seal` is its own constructor rather than a magic
-- `.const`. What the new spelling adds is that **ascription IS this language's
-- seal** — §5's definition of a declaration is "a λ with its signature ascribed",
-- and this row is that sentence as grammar rather than as a comment beside a
-- two-argument former named after the implementation.
syntax:max "(" uterm ":" uterm ")" : uterm                   -- .seal t u — `(t : T)`
-- The one confusable neighbour, refused ON PURPOSE. `&mut (s : τ ~> S)` is the
-- borrow type with a snapshot binder; drop the `~> S` and the ascription row above
-- would take it, making `&mut (v : List Nat)` a BORROW OF A SEAL — which is never
-- meaningful (a seal is not a place) and is certainly not what someone writing that
-- meant. Measured before deciding: without this row it parses, silently, and fails
-- downstream as an unrelated unbound-identifier error.
syntax:70 "&mut" "(" ident ":" uterm ")" : uterm             -- always an error
syntax:max "match" ident "{" uarm,* "}" : uterm              -- runtime match (§3)
syntax:max "match" ident ":" ident "{" uarm,* "}" : uterm    -- …with a branch equation (M23)
syntax:max "if" uterm "{" ublk "}" "else" "{" ublk "}" : uterm  -- §12 sugar over a Bool match
syntax:max "if" ident ":" uterm "{" ublk "}" "else" "{" ublk "}" : uterm  -- …with a branch equation

-- Pure eliminator sugar (§15b) — for `prog{}` / comptime positions. Arm bodies are
-- `ublk` so a `let x = e ; …` proof-let sequence (StdLemmas) works uniformly.
declare_syntax_cat uelimArm
syntax ident ("(" ident ")")* (ident)? "=>" ublk : uelimArm
syntax:max "elim" uterm:max "return" uterm:max "{" uelimArm,* "}" : uterm
syntax:max "elim" uterm:max "generalizing" uterm:max "{" uelimArm,* "}" : uterm

syntax "{" ublk "}" : uarmBody                               -- braced block arm body
syntax uterm : uarmBody                                      -- bare expression arm body
syntax ident "=>" uarmBody : uarm                            -- nullary pattern
syntax ident "(" ident,* ")" "=>" uarmBody : uarm            -- applied pattern C(x, y)

-- **`fn` is a STATEMENT** (M28 θ). §8 says a declaration is a `let`, and §7 says
-- what its right-hand side is — a seal over a recursor or a runtime λ. Put those
-- together and there is nothing for a separate top-level declaration macro to do:
-- `fn f (…) -> R { … } ; rest` is that `let`, written where a `let` is written.
-- The binder telescope reuses `ulamb`, the runtime λ's binder category, because it
-- is the same thing — a list of `x : τ` — and a second category for it would be a
-- second thing to keep in step.
syntax "fn" ident ("[" ident "]")? "(" ulamb,* ")" "->" uterm "{" ublk "}" ";" ublk : ublk
syntax "let" ident "=" uterm ";" ublk : ublk                 -- runtime let (→ letIn)
syntax uterm ":=" uterm ";" ublk : ublk                      -- assignment
syntax uterm ";" ublk : ublk                                 -- expression statement (seq)
syntax uterm : ublk                                          -- final expression

namespace Surface
open Lean

/-- The binder a pure form gets when NOTHING can refer to it: a plain `&mut τ`'s
    entry snapshot, and the non-dependent arrow's domain. Reserved, so it is not
    merely unused but unwritable. -/
def unusedSnapName : String := "§_"

-- (`shadowedName` and `idxOf?` were deleted in M30 step 2. The first existed so
-- that a `let` shadowing a pure binder could occupy that binder's `pctx` slot —
-- every de Bruijn INDEX below it had to keep its level — while being unwritable as
-- source. Under names there is no level to keep, so the shadowed binder is simply
-- dropped from the scope, which is what the mask was simulating. The second was the
-- index lookup itself: `pctx` is now a set of names in scope and the question asked
-- of it is membership.)

/-- Build the `Term` syntax for the numeral `k` as `S (S (… Z))`. -/
partial def buildNat : Nat → MacroM (TSyntax `term)
  | 0 => `(Dllbc.Term.ctorApp "Z" [])
  | k + 1 => do let inner ← buildNat k; `(Dllbc.Term.ctorApp "S" [$inner])

/-- Mint fresh runtime ids for a list of pattern binders, extending `rctx` and
    returning the extended context, the next free id, and the binder `Var`
    syntaxes (in order). Binder ids are ABSOLUTE and globally unique — minted
    from one counter threaded through every elaborator — which is why they stay
    distinct across the arms of a single match. -/
partial def mintBinders (rctx : List (String × Nat)) (next : Nat) :
    List Ident → MacroM (List (String × Nat) × Nat × Array (TSyntax `term))
  | [] => pure (rctx, next, #[])
  | b :: bs => do
    let name := b.getId.toString
    let vSyntax ← `((⟨$(quote next), $(quote name)⟩ : Dllbc.Var))
    let (rctx', next', rest) ← mintBinders ((name, next) :: rctx) (next + 1) bs
    pure (rctx', next', #[vSyntax] ++ rest)

/-- Kernel constructors → `ctorApp`. **Sourced from the kernel's own basis**
    (`Val.ctorNames`, which `Pure.ctorSig` must track) rather than repeated here,
    because
    M26-B gives the list a second job — reserving these names as binder keywords
    — and two lists that must agree is one list too many. -/
def ctorSet : List String := Dllbc.Val.ctorNames
/-- Kernel constants (type formers / recursors / eliminators) → `const`. -/
def constSet : List String := ["Nat", "Bool", "List", "Bot", "Unit", "natRec", "boolRec", "listRec", "sigmaRec", "botElim", "j", "k",
  -- ¶1.1/¶1.3's array basis: the former, the split view, the cons view, the read.
  "Array", "arrCat", "acons", "arrRec", "aget"]
/-- Friendly aliases for the reified library functions whose surface name differs
    from their `…FnT` Term-constant (`Le` ↦ `LeFnT`, etc.). Everything else falls
    through to the raw-Lean-identifier resolution, so lemma Terms (`SwapL`, `Set`,
    `SortRangeL`, …) are referenced by their own names via the use-site `open`s.

    **The keys are PascalCase since M31 Stage A** (§2.1): "the standard
    vocabulary capitalises with everything else — `Len`, `Add`, `Count`, `Take`
    join the already-capital `Le`, `Sorted` — one rule for every name that denotes
    a function, library or user's." The `…FnT` Terms they map to keep their Lean
    names, because a Lean identifier is not a DLLBC binder and carries no mode.

    **Stage C completed the rule at the lemmas** (§2.1's "library or user's").
    Stage A had left them lowercase on the same carries-no-mode argument; that
    argument is sound about the KERNEL and wrong about the READER, who sees one
    surface vocabulary in which `SwapL` and `Quicksort` are both functions. So
    the lemma Terms below the alias table are PascalCase too, and the abbrevs
    here — `Add`, `Count`, `Take`, … — now merely restate their alias key. -/
def aliasMap : List (String × Name) :=
  [("Le", `Dllbc.Std.LeFnT), ("Len", `Dllbc.Std.lenFnT), ("Add", `Dllbc.Std.addFnT),
   ("Leb", `Dllbc.Std.lebFnT), ("Count", `Dllbc.Std.countFnT), ("Eqb", `Dllbc.Std.eqbFnT),
   ("Take", `Dllbc.Std.takeFnT), ("Drop", `Dllbc.Std.dropFnT),
   ("Sorted", `Dllbc.Std.SortedFnT), ("Bound", `Dllbc.Std.BoundFnT)]

/-! ## Binder names, and what capitalisation may mean (combining-fns §6)

    §6 makes **capitalisation the binder-mode marker** — a capital binder is
    comptime, a lowercase one runtime — and pays for it with one prescription:
    "constructor names are special-cased as keywords, the fixed basis makes the
    set closed and small". This is that prescription.

    What must be reserved is exactly the **capitalized** names the resolver
    already answers for: the constructors (`S`, `Z`, `Cons`, `Nil`, `True`,
    `False`, `Pair`, `Refl`, `Arr`) and the capitalized kernel constants (`Nat`,
    `Bool`, `List`, `Bot`, `Unit`, `Array`). Those are the ones for which
    "capital ⟹ comptime binder" would otherwise be ambiguous. The LOWERCASE
    entries (`unit`, `j`, `k`, `natRec`, `aget`, …) are deliberately NOT
    reserved: they were always shadowable, shadowing them is ordinary scoping,
    and reserving `j`/`k` would cost every program its loop indices for no
    disambiguation at all. Reserve what the marker needs, and nothing else. -/

/-- May this identifier be a binder?

    Two families are refused. The capitalized basis names above, for §6's reason.
    And the **reserved namespace** (M30 step 2): `§`-prefixed names are what the
    kernel mints for binders no program wrote — readback's canonical `§0`, `§1`,
    `abstractOccurrences`' `§gen`, a plain `&mut τ`'s unused snapshot binder — and
    the whole point of them is that nothing can collide with one. An ordinary Lean
    `ident` cannot contain `§`, so it would take an ESCAPED identifier (`«§0»`) to
    offer one; that is exactly the sort of gap that is closed cheaply now and found
    expensively later. -/
def reservedBinder (s : String) : Bool :=
  Dllbc.isReservedName s || (Dllbc.isUpperInit s && (ctorSet.contains s || constSet.contains s))

/-- Reject a reserved name in binder position. Called at every binder the
    unified grammar has: λ, Π, Σ, `let`, match arms and their equation binder,
    and a `fn`'s parameters. -/
def checkBinder (x : Ident) : MacroM Unit := do
  let s := x.getId.toString
  if reservedBinder s then
    if Dllbc.isReservedName s then
      Macro.throwErrorAt x s!"'{s}' is in the kernel's reserved binder namespace (names beginning with '§'), which is where readback's canonical binders and the machine's minted ones live. A program may not write one, because the guarantee those names carry is that nothing else can be called that."
    else
      Macro.throwErrorAt x s!"'{s}' is a reserved name (a constructor or a kernel type/constant) and cannot be a binder. §6 makes capitalisation the binder-mode marker — capital = comptime — which is unambiguous only if the capitalized names of the fixed basis are keywords."

/-- The λ/Π domain for a binder named `nm`: `⇝τ` when the name is capitalized
    (a COMPTIME binder — its argument is ⇝-read at ⇒-calls, and the fence keeps
    it in ⇝-positions), plain `τ` otherwise. The whole of the surface's part in
    §6 for pure binders; runtime binders need nothing, because their mode is
    their `Var`'s name. -/
def binderDom (nm : String) (τ : TSyntax `term) : MacroM (TSyntax `term) :=
  if Dllbc.isUpperInit nm then `(Dllbc.Term.cmpT $τ) else pure τ

/-! ## Locals and `fn` slots in one context (M31 Stage A)

    A `fn` statement's name now goes into `rctx` alongside the ordinary runtime
    locals, because §2.1 makes a function an ordinary comptime BINDING and a
    binding is something a bare name may denote (`let F = Main`). They are told
    apart by the id, which since M32 R4 is the TAG `Var.declSlot` rather than a
    position above `progBase` — same question, no arithmetic to keep in step.

    Separate they must stay, because two rows want the LOCALS only:

      * `f(a, b)` must keep falling through to `.call`, whose rewrite into the
        app SPINE is `retarget`'s — and `retarget` also PERMUTES the arguments of
        a `[k]`-hoisted callee (E8). Resolving the name here instead would build
        the spine in declaration order against a telescope that has been
        reordered, which is silent: it passes a borrow where a `Nat` is expected,
        and it was found once already, by a migration disagreement list rather
        than by a test.
      * `match x { … }` wants a runtime scrutinee, and a function is not one. -/

/-- An ordinary runtime local — a `fn` slot is not one. -/
def localId (rctx : List (String × Nat)) (s : String) : Option Nat :=
  match rctx.lookup s with
  | some id => if id == Dllbc.declSlot then none else some id
  | none => none

/-- A `fn` slot bound above this point, by the name it was declared with.

    Every such name is capital, because the `fn` row refuses a lowercase one
    (§2.1).

    **Stage A's safety argument for this lookup expired at Stage C, and M32 R1
    turns the replacement convention into a CHECK.** Stage A could say the names
    this answers for are exactly the ones the raw-Lean fallthrough never had a
    reading for, because every lemma Term was lowercase. Stage C capitalised the
    lemmas, so the two families now share one namespace and this lookup —
    consulted BEFORE the fallthrough — shadows a lemma of the same name. Two names
    collided and both took the **`L` suffix on the lemma** (`swapL`'s
    L-for-list-spec, generalised): `fn Nth` against the cursor lemma, now `NthL`;
    `fn SplitA` against the split predicate, now `SplitAL`. The invariant was
    stated in the corpus and enforced nowhere; `lemmaShadowCheck` below enforces
    it, at the one place both names are in view. -/
def fnSlotId (rctx : List (String × Nat)) (s : String) : Option Nat :=
  match rctx.lookup s with
  | some id => if id == Dllbc.declSlot then some id else none
  | none => none

/-- **The L-suffix condition, checked** (M32 R1).

    A `fn` slot wins over the raw-Lean fallthrough, so a `fn` whose name spells a
    `StdLemmas` lemma makes that lemma unreachable in every block the `fn` is
    above — silently, since both readings are well-typed. Under M32's name-keyed Ω
    the same spelling additionally resolves the same STORE entry, so what was a
    surface-level shadowing is now a store-level one too, and a convention nobody
    checks is the wrong size of guarantee for it.

    The test is asked of the collision family the convention is about — a
    `Dllbc.StdLemmas` definition of that exact name — rather than of any Lean
    global, because "is this identifier bound somewhere in Lean" answers yes for
    reasons that have nothing to do with the corpus (a `List` combinator, an
    opened namespace) and would refuse `fn` names that shadow nothing anyone can
    write here. The fix named in the message is the one the corpus already took
    twice: the LEMMA takes the suffix, because the function is the user-facing
    name (Stage C addendum item 2). -/
def lemmaShadowCheckAt (ref : Syntax) (s : String) : MacroM Unit := do
  let cands ← Macro.resolveGlobalName (`Dllbc.StdLemmas ++ Name.mkSimple s)
  if !cands.isEmpty then
    Macro.throwErrorAt ref s!"fn: '{s}' shadows the library lemma `Dllbc.StdLemmas.{s}`. A `fn` slot is resolved before the raw-Lean fallthrough, so no block below this declaration can name the lemma, and under M32's name-keyed Ω the two spellings resolve one store entry. Give the LEMMA the `L` suffix ({s} → {s}L) — the function is the user-facing name and does not move."

/-- Resolve a bare identifier in a type/back position. Pure binder in scope →
    `pvar` at that very name; earlier telescope param → `var`; constructor →
    nullary `ctorApp`; kernel const → `const`; reified-function alias → its `…FnT`
    Term; a `fn` slot above it → `var` at that slot; else the Lean identifier of
    that name (a `Term` in scope).

    The `fn` slot is consulted LAST but one, after the alias table and before the
    raw fallthrough, so that adding it changes the answer for no name that already
    had one. -/
def resolveName (rctx : List (String × Nat)) (pctx : List String) (x : Ident) : MacroM (TSyntax `term) := do
  let s := x.getId.toString
  if pctx.contains s then `(Dllbc.Term.pvar $(quote s))
  else
    match localId rctx s with
    | some id => `(Dllbc.Term.var ⟨$(quote id), $(quote s)⟩)
    | none =>
      if ctorSet.contains s then `(Dllbc.Term.ctorApp $(quote s) [])
      else if constSet.contains s then `(Dllbc.Term.const $(quote s))
      else match aliasMap.lookup s with
        | some n => pure ⟨(mkIdent n).raw⟩
        | none =>
          match fnSlotId rctx s with
          | some id => `(Dllbc.Term.var ⟨$(quote id), $(quote s)⟩)
          | none => pure ⟨x.raw⟩

/-! ## Unified `uterm` / `ublk` elaborators (§ points 1–3)

Runtime binders (let, match patterns) mint fresh absolute ids threaded through
`next`: a `let` binds at the post-RHS counter value and continues at `+1`, and a
match's arm binders are minted from one counter across ALL arms, so no two
binders in a body ever share an id. This is the id discipline of the retired
runtime-body grammar, reproduced here exactly — every one of its 70 sites in the
suite was checked byte-for-byte against this elaborator before it was deleted
(M28 α–δ).
Pure binders (λ/Π/Σ/→) push their NAME onto `pctx` and never touch `next`; a
runtime var referenced from inside a pure spine stays `.var`. -/

partial def collectAppU : TSyntax `uterm → TSyntax `uterm × Array (TSyntax `uterm)
  | `(uterm| $f:uterm $a:uterm) => let (h, as) := collectAppU f; (h, as.push a)
  | t => (t, #[])

mutual

partial def elabUTerm (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `uterm) : MacroM (TSyntax `term × Nat) := do
  match stx with
  | `(uterm| ()) => return (← `(Dllbc.Term.unit), next)
  | `(uterm| ($e:uterm)) => elabUTerm rctx pctx next e
  | `(uterm| Type) => return (← `(Dllbc.Term.type), next)
  | `(uterm| % $e:term) => return (← `(($e : Dllbc.Term)), next)
  | `(uterm| $n:num) => return (← buildNat n.getNat, next)
  | `(uterm| old * $e:uterm) => do
    -- §5.4 `old *v`: the ENTRY snapshot, sugar over the telescope's existing
    -- payload snapshot. Elaborates to `@old(*v)`; `markExit` strips the marker to
    -- a plain `*v` read at seed (entry), so it never reaches the kernel.
    let (e', n) ← elabUTerm rctx pctx next e
    return (← `(Dllbc.Term.app (Dllbc.Term.const "old") (Dllbc.Term.deref $e')), n)
  | `(uterm| * $e:uterm) => do
    let (e', n) ← elabUTerm rctx pctx next e
    return (← `(Dllbc.Term.deref $e'), n)
  | `(uterm| $a:uterm[$i:uterm]) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (i', n2) ← elabUTerm rctx pctx n1 i
    return (← `(Dllbc.Term.index $a' $i' none), n2)
  | `(uterm| $a:uterm[$i:uterm | $h:uterm]) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (i', n2) ← elabUTerm rctx pctx n1 i
    let (h', n3) ← elabUTerm rctx pctx n2 h
    return (← `(Dllbc.Term.index $a' $i' (some $h')), n3)
  | `(uterm| $a:uterm[$lo:uterm ; ..]) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (lo', n2) ← elabUTerm rctx pctx n1 lo
    return (← `(Dllbc.Term.range $a' $lo' none none none none), n2)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm]) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (lo', n2) ← elabUTerm rctx pctx n1 lo
    let (c', n3) ← elabUTerm rctx pctx n2 c
    let (r', n4) ← elabUTerm rctx pctx n3 r
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') none none), n4)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm | $h:uterm]) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (lo', n2) ← elabUTerm rctx pctx n1 lo
    let (c', n3) ← elabUTerm rctx pctx n2 c
    let (r', n4) ← elabUTerm rctx pctx n3 r
    let (h', n5) ← elabUTerm rctx pctx n4 h
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') (some $h') none), n5)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm | $h:uterm | $q:uterm]) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (lo', n2) ← elabUTerm rctx pctx n1 lo
    let (c', n3) ← elabUTerm rctx pctx n2 c
    let (r', n4) ← elabUTerm rctx pctx n3 r
    let (h', n5) ← elabUTerm rctx pctx n4 h
    let (q', n6) ← elabUTerm rctx pctx n5 q
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') (some $h') (some $q')), n6)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm]) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (lo', n2) ← elabUTerm rctx pctx n1 lo
    let (c', n3) ← elabUTerm rctx pctx n2 c
    return (← `(Dllbc.Term.range $a' $lo' (some $c') none none none), n3)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm | $h:uterm]) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (lo', n2) ← elabUTerm rctx pctx n1 lo
    let (c', n3) ← elabUTerm rctx pctx n2 c
    let (h', n4) ← elabUTerm rctx pctx n3 h
    return (← `(Dllbc.Term.range $a' $lo' (some $c') none (some $h') none), n4)
  | `(uterm| &mut ( $x:ident : $τ:uterm ~> $s:uterm )) => do     -- borrow type, snapshot binder
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (s', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 s
    return (← `(Dllbc.Term.borrowT $(quote (x.getId.toString)) $τ' $s'), n2)
  -- The two spellings whose snapshot binder is UNUSED get a reserved name, and no
  -- weakening: `shiftPure 1 0` used to sit on both of these lines and is the
  -- identity under names (M30 step 2). `trivialOwedT` reads the second shape and
  -- was simplified with them.
  | `(uterm| &mut ( $τ:uterm ~> $s:uterm )) => do                -- borrow type, S ignores s
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (s', n2) ← elabUTerm rctx pctx n1 s
    return (← `(Dllbc.Term.borrowT $(quote unusedSnapName) $τ' $s'), n2)
  | `(uterm| &mut $e:uterm) => do                                -- the borrow TYPE, in any position
    let (e', n) ← elabUTerm rctx pctx next e
    return (← `(Dllbc.Term.borrowT $(quote unusedSnapName) $e' $e'), n)
  | `(uterm| &m $e:uterm) => do                                  -- the borrow OPERATION, in any position
    -- M29 β. This row and the one above are the two spellings, and neither asks
    -- which arrow it is under: `&m` in a ⇝ position is a `.borrow`, which
    -- `reflectC` refuses by name ("`&mut` is not in the comptime fragment"), and
    -- `&mut` in a ⇒ position is a `.borrowT`, which `readR` refuses by name
    -- ("a telescope-position form, not a movable value"). Both refusals already
    -- existed and neither was reachable while the surface was deciding; the
    -- exclusions are the KERNEL's, and this is what it takes for the surface to
    -- stop making them on its behalf.
    let (e', n) ← elabUTerm rctx pctx next e
    return (← `(Dllbc.Term.borrow $e'), n)
  | `(uterm| Id $a:uterm $b:uterm $c:uterm) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (b', n2) ← elabUTerm rctx pctx n1 b
    let (c', n3) ← elabUTerm rctx pctx n2 c
    return (← `(Dllbc.Term.idT $a' $b' $c'), n3)
  | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.lam $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') $b'), n2)
  | `(uterm| λ ($bs:ulamb,*) { $b:ublk }) => do
    -- Runtime binders, so fresh absolute ids threaded through `next` exactly as
    -- `let` and match patterns mint them — and pushed onto `rctx`, not `pctx`:
    -- the body reaches them through Ω. The body is a ⇒ position whatever
    -- surrounds the node, which is the same asymmetry the seal has.
    let parsed ← bs.getElems.toList.mapM fun (p : TSyntax `ulamb) => match p with
      | `(ulamb| $x:ident : $τ:uterm) => pure (x, τ)
      | _ => Macro.throwErrorAt p "λ: malformed binder (expected `x : τ`)"
    -- **The nullary refusal moved HERE** (M32 R2). `λ(){ … }` used to be refused
    -- by the kernel, at the point `Term.lamR []` became a value; under one λ
    -- former there is no such term to refuse — the comma list is a TELESCOPE, and
    -- an empty telescope elaborates to the body itself. The reason is unchanged
    -- and so is the sentence: a thunk makes ι ambiguous, and nothing in §7 wants
    -- one.
    if parsed.isEmpty then
      Macro.throwErrorAt stx "λr: a runtime λ must bind at least one argument. `λ(){ … }` is a thunk, and a thunk makes ι ambiguous — an arm applied to no arguments and an arm with nothing owed become the same spine. A recursor arm at a non-functional motive is an ordinary term; write it as one."
    parsed.forM (fun p => checkBinder p.1)
    let (rctx', next', binderSyns) ← elabLamBinders rctx pctx next parsed
    let (b', n) ← elabUBlk rctx' pctx next' b
    return (← `(Dllbc.Term.lamTel [$binderSyns,*] $b'), n)
  | `(uterm| Π ($x:ident : $τ:uterm) → $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.pi $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') $b'), n2)
  -- Σ binders are name-checked but carry NO mode. §6 gives modes to "λ, Π, and
  -- `let` alike" — the binders of *parameters* — and a Σ's binder names a
  -- projection, not a parameter: erasing one component of a pair is QTT
  -- **A Σ BINDER CARRIES ITS MODE ON ITS DOMAIN, exactly as λ and Π do** (M32
  -- R3b). It used not to, and the sentence that stood here — "a capital Σ binder
  -- is legal and inert" — was true and was the whole problem: §2.1 makes a
  -- binder's case its mode, and a Σ whose case lived only in the NAME lost it at
  -- the first normalization, because `Pure.readback` names every binder it
  -- reaches by its LEVEL (`§0`). λ and Π survive that because `binderDom` puts a
  -- `⇝` on the domain and readback preserves it; a Σ had no domain marker and so
  -- had nothing to survive with. That is why §2.5's wall could not be taken down
  -- by renaming alone — the mode was gone before anything could read it.
  | `(uterm| Σ ($x:ident : $τ:uterm) → $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') $b'), n2)
  | `(uterm| Σ ($x:ident : $τ:uterm). $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') $b'), n2)
  -- **Σ0 — THE COMPTIME TAIL** (M33, suspensions.md §2.7), and it is NOT a new
  -- former. A Σ's binder has always spelled its own component's mode; the TAIL
  -- has no binder, so until here it had no way to say anything and was silently
  -- ⇒-read — §2.5's second surviving spelling, and exactly where quicksort's
  -- count proof sits. Σ0 says it on the CODOMAIN, which is the same place λ and
  -- Π say it (their domains) seen from the other end of the pair: one marker,
  -- `Term.cmpT`, routed by the machinery R3b already built. Same `sigmaT`, same
  -- `Pair`, same `sigmaRec` — the marker lives on the type and the read routes
  -- off it.
  | `(uterm| Σ0 ($x:ident : $τ:uterm) → $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') (Dllbc.Term.cmpT $b')), n2)
  | `(uterm| Σ0 ($x:ident : $τ:uterm). $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') (Dllbc.Term.cmpT $b')), n2)
  -- The non-dependent arrow's binder is reserved and is NOT pushed onto `pctx`:
  -- nothing can refer to it, which is what "non-dependent" means. (The de Bruijn
  -- version had to push a placeholder, because every binder crossed moved the
  -- indices below it.)
  | `(uterm| $a:uterm → $b:uterm) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (b', n2) ← elabUTerm rctx pctx n1 b
    return (← `(Dllbc.Term.pi $(quote unusedSnapName) $a' $b'), n2)
  -- …and the same for the pair. The binder is the arrow's — reserved, unpushed,
  -- and UNMARKED, which is the point rather than an omission: `⇝` on a Σ domain
  -- is a claim about how that component is read, and a component nothing can
  -- name makes no such claim.
  | `(uterm| $a:uterm × $b:uterm) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (b', n2) ← elabUTerm rctx pctx n1 b
    return (← `(Dllbc.Term.sigmaT $(quote unusedSnapName) $a' $b'), n2)
  | `(uterm| &mut ( $x:ident : $τ:uterm )) =>
    Macro.throwErrorAt x s!"&mut ({x.getId} : τ) is not a borrow type — the snapshot-binder spelling is `&mut ({x.getId} : τ ~> S)`, where `S` is what the borrow OWES back and `{x.getId}` is its entry snapshot, bound as pure var 0 in `S`. Without the `~> S` this would read as `&mut` applied to the ascription `({x.getId} : τ)`, which is a borrow of a SEAL — never meaningful, since a seal is not a place. If you meant a plain borrow of the type, write `&mut τ`."
  | `(uterm| ($t:uterm : $u:uterm)) => do
    -- The body is a ⇒ position (term mode) whatever surrounds the node; the
    -- ascribed type is a ⇝ position. That asymmetry is the seal itself.
    let (t', n1) ← elabUTerm rctx pctx next t
    let (u', n2) ← elabUTerm rctx pctx n1 u
    return (← `(Dllbc.Term.seal 0 $t' $u'), n2)
  | `(uterm| $c:ident($args,*)) => do                 -- no-space paren: call / ctorApp
    let (args', n) ← elabUList rctx pctx next args.getElems.toList
    let name := c.getId.toString
    -- **A known CONSTRUCTOR, not merely a capital head** (M26-B). §6 makes
    -- capitalisation the binder-mode marker, so `G(n)` — a capital *binder*
    -- applied — must not silently become `ctorApp "G"`. Keying on `ctorSet`
    -- instead of on case is precisely what "constructor names are reserved
    -- keywords, and any other capitalized identifier is unambiguously a comptime
    -- variable" buys: the basis is closed, so the test is exact. (This changes
    -- nothing for existing programs — every constructor they write is in the
    -- basis — and it turns what used to be "unknown constructor 'G'" into the
    -- call it was always meant to be.)
    if ctorSet.contains name then
      return (← `(Dllbc.Term.ctorApp $(quote name) [$args',*]), n)
    else
      -- **Scope beats the table** (§8's direction, arriving early because M26-A
      -- needs it): a head that names a BOUND RUNTIME VARIABLE is a value-callee
      -- call, and only a head that names nothing in scope falls through to the
      -- declaration table. No new token and no annotation — the same `f(x)`
      -- surface means both, which is what "one application form" has to mean.
      -- `localId`, not `rctx.lookup`: a `fn` slot deliberately falls through to
      -- `.call`, because `retarget` is what rewrites those — and permutes a
      -- `[k]`-hoisted callee's arguments on the way (see `localId`'s header).
      -- The SPINE (M32 R4): `f(a, b)` is sugar for `.app (.app (.var f) a) b`.
      match localId rctx name with
      | some id =>
        return (← `(Dllbc.Term.appSpine (.var ⟨$(quote id), $(quote name)⟩) [$args',*]), n)
      | none => return (← `(Dllbc.Term.call $(quote name) [$args',*]), n)
  | `(uterm| match $x:ident { $arms,* }) => do
    let s := x.getId.toString
    match localId rctx s with
    | none => Macro.throwErrorAt x s!"decl: match scrutinee '{s}' is not a bound runtime variable"
    | some id =>
      let (arms', n) ← elabUArms rctx pctx next arms.getElems.toList
      return (← `(Dllbc.Term.matchE ⟨$(quote id), $(quote s)⟩ none [$arms',*]), n)
  -- M23: `match h : x { … }` — the branch-equation form. One binder for the whole
  -- match (its TYPE is what varies per arm), as in Lean's `match h : x with`.
  | `(uterm| match $h:ident : $x:ident { $arms,* }) => do
    checkBinder h
    let s := x.getId.toString
    match localId rctx s with
    | none => Macro.throwErrorAt x s!"decl: match scrutinee '{s}' is not a bound runtime variable"
    | some id =>
      let hName := h.getId.toString
      let (arms', n) ← elabUArms ((hName, next) :: rctx) pctx (next + 1) arms.getElems.toList
      return (← `(Dllbc.Term.matchE ⟨$(quote id), $(quote s)⟩
        (some ⟨$(quote next), $(quote hName)⟩) [$arms',*]), n)
  | `(uterm| if $c:uterm { $t:ublk } else { $f:ublk }) => do  -- §12 sugar → Bool match
    let (c', n1) ← elabUTerm rctx pctx next c
    let scrutId := n1
    let (t', n2) ← elabUBlk rctx pctx (n1 + 1) t
    let (f', n3) ← elabUBlk rctx pctx n2 f
    return (← `(Dllbc.Term.letIn ⟨$(quote scrutId), "__if"⟩ $c'
      (Dllbc.Term.matchE ⟨$(quote scrutId), "__if"⟩ none
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])), n3)
  | `(uterm| if $h:ident : $c:uterm { $t:ublk } else { $f:ublk }) => do
    let (c', n1) ← elabUTerm rctx pctx next c
    let hName := h.getId.toString
    let rctx' := (hName, n1 + 1) :: rctx
    let (t', n2) ← elabUBlk rctx' pctx (n1 + 2) t
    let (f', n3) ← elabUBlk rctx' pctx n2 f
    return (← `(Dllbc.Term.letIn ⟨$(quote n1), "__if"⟩ $c'
      (Dllbc.Term.matchE ⟨$(quote n1), "__if"⟩ (some ⟨$(quote (n1 + 1)), $(quote hName)⟩)
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])), n3)
  | `(uterm| elim $scrut:uterm return $motive:uterm { $arms,* }) =>
    elabUElim rctx pctx next scrut motive arms.getElems
  | `(uterm| elim $scrut:uterm generalizing $goal:uterm { $arms,* }) =>
    elabUGenElim rctx pctx next scrut goal arms.getElems
  | `(uterm| $_:uterm $_:uterm) => do                 -- application spine (juxtaposition)
    let (head, args) := collectAppU stx
    match head with
    | `(uterm| $h:ident) =>
      let hs := h.getId.toString
      let (argTerms, n) ← elabUList rctx pctx next args.toList
      if ctorSet.contains hs && !pctx.contains hs && (localId rctx hs).isNone then
        return (← `(Dllbc.Term.ctorApp $(quote hs) [$argTerms,*]), n)
      -- **JUXTAPOSITION IS ALREADY ONE FORM, and β leaves the surface alone**
      -- (M27). `f a b` elaborates to a `.app` spine over the head's resolution,
      -- and when that head is a runtime slot the spine is exactly what a call is
      -- written as. Which ARROW applies it is not something the surface can know
      -- — `let finish = (λ (e : List Nat). …)` and `let f = (… : …)` are both
      -- lowercase slots holding functions, and the first must be substituted by ⇝
      -- while the second binds Ω slots under ⇒ — so the decision is the kernel's,
      -- at `readR`'s `.app` case, where `runtimeRecSpine?` already makes the same
      -- kind of choice. See `appSpineVar?` in `Machine.lean`.
      else
        let hterm ← resolveName rctx pctx h
        let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
        return (out, n)
    | _ => do
      let (hterm, n0) ← elabUTerm rctx pctx next head
      let (argTerms, n) ← elabUList rctx pctx n0 args.toList
      let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
      return (out, n)
  | `(uterm| $x:ident) => return (← resolveName rctx pctx x, next)
  | _ => Macro.throwErrorAt stx "decl: unexpected term syntax"

partial def elabUList (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (TSyntax `uterm) → MacroM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (rest, n2) ← elabUList rctx pctx n1 as
    pure (#[a'] ++ rest, n2)

/-- A runtime λ's annotated binders (M27), elaborated as a TELESCOPE: each domain
    is read under the binders to its left and not its own, which is what lets
    `λ(v : &mut List Nat, hfuel : Le (len *v) fuel){ … }` mention `v` in the type
    after it. `&mut τ` there is the borrow TYPE because that is what `&mut`
    SPELLS (M29 β) — the domain no longer has to be elaborated in a distinguished
    mode to make it one, which is what let the flag go. `binderDom` puts §6's
    comptime marker on a capitalized binder's domain, which is what makes the
    annotation agree with the ascription `piPeel` checks it against. -/
partial def elabLamBinders (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (Ident × TSyntax `uterm) → MacroM (List (String × Nat) × Nat × Array (TSyntax `term))
  | [] => pure (rctx, next, #[])
  | (x, τ) :: rest => do
    let name := x.getId.toString
    let (τT, n1) ← elabUTerm rctx pctx (next + 1) τ
    let τD ← binderDom name τT
    let entry ← `(((⟨$(quote next), $(quote name)⟩ : Dllbc.Var), $τD))
    let (rctx', n2, more) ← elabLamBinders ((name, next) :: rctx) pctx n1 rest
    pure (rctx', n2, #[entry] ++ more)

/-- Build the telescope entry syntaxes, threading the runtime-var context so that
    parameter `i`'s type sees exactly params `0 .. i-1` (each at its positional
    id) — the `seedTelescope` convention. Types elaborate in type mode (⇝). -/
partial def buildTele (rctx : List (String × Nat)) (i : Nat) :
    List (String × TSyntax `uterm) → MacroM (Array (TSyntax `term))
  | [] => pure #[]
  | (nm, τ) :: rest => do
    let (τT, _) ← elabUTerm rctx [] 0 τ
    let entry ← `((($(quote nm), $τT) : String × Dllbc.Term))
    let rest' ← buildTele (rctx ++ [(nm, i)]) (i + 1) rest
    pure (#[entry] ++ rest')

partial def elabUArms (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (TSyntax `uarm) → MacroM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← elabUArm rctx pctx next a
    let (rest, n2) ← elabUArms rctx pctx n1 as
    pure (#[a'] ++ rest, n2)

partial def elabUArm (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (arm : TSyntax `uarm) : MacroM (TSyntax `term × Nat) := do
  match arm with
  | `(uarm| $c:ident => $body:uarmBody) => do
    let (body', n) ← elabUArmBody rctx pctx next body
    return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [] $body'), n)
  | `(uarm| $c:ident ($binders,*) => $body:uarmBody) => do
    binders.getElems.forM checkBinder
    let (rctx', next', binderVars) ← mintBinders rctx next binders.getElems.toList
    let (body', n) ← elabUArmBody rctx' pctx next' body
    return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [$binderVars,*] $body'), n)
  | _ => Macro.throwErrorAt arm "decl: unexpected match arm"

partial def elabUArmBody (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (body : TSyntax `uarmBody) : MacroM (TSyntax `term × Nat) := do
  match body with
  | `(uarmBody| { $b:ublk }) => elabUBlk rctx pctx next b
  | `(uarmBody| $e:uterm) => elabUTerm rctx pctx next e
  | _ => Macro.throwErrorAt body "decl: unexpected arm body"

partial def elabUBlk (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `ublk) : MacroM (TSyntax `term × Nat) := do
  match stx with
  -- **`fn` — the declaration statement** (M28 θ). This is `FnMacro.progOf` unrolled
  -- one binding at a time, and reusing its two moving parts rather than
  -- reimplementing them is what makes the two paths agree by construction:
  --
  --   * the right-hand side is `fnElabOrFail`, i.e. `fnElab` — the §7 lowering,
  --     with a refusal turned into a term the checker refuses distinctively;
  --   * the REST is passed through `bindFn`, i.e. `retarget` — which is how a call
  --     written in the tail finds the binding. That is not an optimisation over
  --     putting the name in `rctx`: `retarget` also PERMUTES a call's arguments to
  --     match a `[k]`-hoisted callee's telescope, and a spine minted at the
  --     surface would skip the permutation. Eight functions in this corpus have a
  --     `[k]` that is not parameter 0, so the difference is real and silent.
  --     `bindFn` adds the one check the surface cannot make for itself — that the
  --     rest does not already bind this slot, which is what two `%`-spliced chains
  --     would do.
  --
  -- Passing `rest` through `retarget` rather than binding the name in `rctx` also
  -- reproduces §8's scoping exactly: the name is not in scope in its own
  -- right-hand side (a self-call becomes `ih` or is refused), and it cannot be
  -- referenced upward, because `retarget` only ever sees what comes after.
  --
  -- **The ⇝ refusal moved to the kernel** (M29 γ). This row used to reject a `fn`
  -- outright when the mode flag said the block was a ⇝ position — "a declaration
  -- is a runtime binding and cannot appear in a ⇝ position". With one macro there
  -- is no flag to ask, and there is also nothing left to say: what the row emits
  -- is a `let` of a `.seal`, and `reflectC` refuses a `.seal` by name and for the
  -- reason that actually holds — minting a fresh σ needs an EVENT, and ⇝ is a
  -- pure judgment with none (§5). The surface's version was a restatement of the
  -- kernel's, made one layer early and phrased in terms of a flag rather than in
  -- terms of the arrow; deleting it loses no rejection, only a duplicate.
  | `(ublk| fn $name:ident $[[$dec:ident]]? ( $ps,* ) -> $ret:uterm { $body:ublk } ; $rest:ublk) => do
    checkBinder name
    -- **A FUNCTION NAME IS CAPITALISED** (M31 Stage A, §2.1). A `fn` desugars to
    -- a `let` of a λ ascribed its Π, and a function is comptime knowledge — so
    -- the binding that holds one must be a capital binding, by the same one rule
    -- that makes every other capital binder comptime. There is no carve-out and
    -- no second marker.
    --
    -- Stated here, at the row that writes the binder, because this is where a
    -- reader can be told the fix. The kernel says it again from below
    -- (`fenceComptime`, since M33b deleted the last mode backstop as derivable),
    -- where it catches what the surface cannot see: a lowercase binding that
    -- receives a function from somewhere the surface cannot read.
    --
    -- The divergence from Rust's snake_case is deliberate and tracks a real
    -- semantic difference — a Rust function is a runtime item, a DLLBC function
    -- is a comptime value — so the surface says so rather than hiding it.
    if !Dllbc.isUpperInit (name.getId.toString) then
      Macro.throwErrorAt name s!"fn: '{name.getId}' must be capitalised. A function is COMPTIME knowledge (§2.1) — ⇝-read, erased, never ⇒-consumed — and §6 makes capitalisation the mode marker, so a function name is a capital name. Write `fn {(name.getId.toString).capitalize} …`."
    -- **The L-suffix condition** (M32 R1), asked at the DECLARATION rather than at
    -- `resolveName`'s slot hit, because a `fn` that is never referenced shadows
    -- the lemma just as thoroughly and would go unasked there.
    lemmaShadowCheckAt name (name.getId.toString)
    let parsed ← ps.getElems.toList.mapM fun (p : TSyntax `ulamb) => match p with
      | `(ulamb| $x:ident : $τ:uterm) => pure (x.getId.toString, τ)
      | _ => Macro.throwErrorAt p "fn: malformed parameter (expected `x : τ`)"
    let names := parsed.map (·.1)
    let n := names.length
    -- The telescope's own §5.2 positional context, and the body's: parameter `i`
    -- at runtime id `i`, fresh binders from `n`. Identical to what `decl{ }` builds
    -- — deliberately, since the `FnDef` this produces has to BE the one it builds.
    let fullRctx : List (String × Nat) := names.zip (List.range n)
    let teleSyns ← buildTele [] 0 parsed
    -- **THE BODY SEES THE ENCLOSING SCOPE** (M32 R2, suspensions.md §2.6). The
    -- `decl{}`-era params-only context retires here: a `fn` body may cite the
    -- comptime bindings lexically above it — a sibling `fn`'s name, a `let H0 =
    -- *hd` snapshot, a proof — and the kernel's citation rule (`admitGlobals`) is
    -- what decides which of them are admissible, as it always was. Its parameters
    -- come FIRST, so a parameter shadows an enclosing binding of the same name.
    --
    -- **What gated this was an id collision, and R1 voided it.** The telescope is
    -- numbered `0 … n-1` by §5.2's positional convention while the enclosing
    -- block numbers its bindings from its own counter, so the two spaces overlap
    -- — and `Term.freeRVars`, which computes the capture, asked by id. It asks by
    -- NAME now (R2, Syntax.lean), which is the question the store has answered
    -- since R1, and the overlap stops meaning anything. Verified rather than
    -- assumed: with id-keying the citation is bound by whichever parameter shares
    -- its number, drops out of ρ, and the sealed body's fresh Ω has nothing to
    -- resolve it against.
    let (retT, _) ← elabUTerm (fullRctx ++ rctx) pctx 0 ret
    let (bodyT, _) ← elabUBlk (fullRctx ++ rctx) pctx n body
    let decT ← match dec with
      | none => `((none : Option Nat))
      | some d =>
        match names.findIdx? (· == d.getId.toString) with
        | some i => `(some $(quote i))
        | none => Macro.throwErrorAt d s!"fn: decreasing argument '{d.getId}' is not a parameter of '{name.getId}'"
    let nm := name.getId.toString
    -- The slot: the TAG `declSlot` (M32 R4). It used to be `progBase + next`,
    -- distinct per declaration, because a function's OWN body numbers its
    -- parameters from 0 and an id-keyed lookup would read a colliding binding as
    -- that parameter. Ω resolves by NAME (M32 R1), so distinctness bought
    -- nothing and the shared tag says the one thing still asked of it: this
    -- entry is a declaration. `next` is no longer consumed here.
    let slot ← `((⟨Dllbc.declSlot, $(quote nm)⟩ : Dllbc.Var))
    -- **The name goes into scope for the rest of the block** (M31 Stage A). A
    -- function is an ordinary comptime binding now (§2.1), so a bare `Main` is a
    -- name-use of one and `let F = Main` is the ⇝ copy of knowledge the model says
    -- it is. `retarget` below still owns the `f(…)` rewrite — `localId` keeps this
    -- entry out of the call row for exactly that reason — so what this adds is the
    -- BARE-name reading `retarget` never had, and nothing it did have is removed.
    let (rest', n2) ← elabUBlk ((nm, Dllbc.declSlot) :: rctx) pctx next rest
    return (← `(Dllbc.Term.letIn $slot
                  (Dllbc.FnMacro.fnElabOrFail
                    (Dllbc.FnDef.mk $(quote nm) [$teleSyns,*] $retT $bodyT $decT))
                  (Dllbc.FnMacro.bindFn $slot $decT $rest')), n2)
  | `(ublk| let $x:ident = $e:uterm ; $rest:ublk) => do
    checkBinder x
    let (e', n1) ← elabUTerm rctx pctx next e
    -- **`let X = e` is a comptime binding** (§6) and needs no macro support: the
    -- mode of a runtime binder IS its `Var`'s name, so the kernel reads it off
    -- the `letIn` this line already emits. Recorded here because the absence of
    -- code is the point — the convention is load-bearing exactly once.
    let name := x.getId.toString
    -- **ONE `let`, both fragments** (M29 α). This row used to branch on the mode:
    -- ⇒ minted a runtime slot and emitted `.letIn`, ⇝ emitted the β-redex
    -- `(λ. rest) e` over an anonymous binder. The kernel now reads `.letIn` under
    -- BOTH arrows — ⇝'s reading is that same β, built at reflection (`reflectC`)
    -- — so the surface has nothing left to decide, and this was the first of the
    -- two branches the mode flag had.
    --
    -- The old spelling was not merely a second encoding, it was a second
    -- SCOPE: a `let` used to push `pctx` in one fragment and `rctx` in the other,
    -- so the same source bound a name in two different places depending on which
    -- macro it sat in. One `rctx` push is now the whole rule.
    --
    -- **And a `let` may shadow a pure binder**, which the merged form has to say
    -- out loud because `resolveName` consults `pctx` FIRST. Left alone,
    -- `λ (x : τ). let x = e ; x` would resolve the tail's `x` to the λ's binder —
    -- the outer one — which is capture by the sort of silent margin this project
    -- keeps finding. Dropping the name from `pctx` makes the innermost binder win,
    -- which is what shadowing means. (It was a MASK until M30 step 2, because the
    -- entry had to stay to keep every index below it at its level; under names
    -- there is nothing below it to keep.) ⇒ bodies had the same hole and are fixed
    -- with it.
    let pctx' := pctx.filter (fun s => s != name)
    let (rest', n2) ← elabUBlk ((name, n1) :: rctx) pctx' (n1 + 1) rest
    return (← `(Dllbc.Term.letIn ⟨$(quote n1), $(quote name)⟩ $e' $rest'), n2)
  | `(ublk| $p:uterm := $e:uterm ; $rest:ublk) => do
    let (p', n1) ← elabUTerm rctx pctx next p
    let (e', n2) ← elabUTerm rctx pctx n1 e
    let (rest', n3) ← elabUBlk rctx pctx n2 rest
    return (← `(Dllbc.Term.assign $p' $e' $rest'), n3)
  | `(ublk| $e:uterm ; $rest:ublk) => do
    let (e', n1) ← elabUTerm rctx pctx next e
    let (rest', n2) ← elabUBlk rctx pctx n1 rest
    return (← `(Dllbc.Term.seq $e' $rest'), n2)
  | `(ublk| $e:uterm) => elabUTerm rctx pctx next e
  | _ => Macro.throwErrorAt stx "decl: unexpected block syntax"

/-- `elim scrut return motive { arms }` → the matching recursor (§15b). Pure — the
    arm binders (k/ih/h/t) push `pctx`, never `next`. The arm binder DOMAINS are
    DERIVED from the recursor scheme and the motive rather than inferred: a natRec
    `S` step is `λ (k : Nat). λ (ih : P k). …`, and `P k` is built by re-elaborating
    the motive BODY and renaming the motive's own binder to the arm's.

    **Every one of those domains goes through `binderDom`** (M33 macro-top), for
    the same reason every other binder in this file does: §2.1's rule is that a
    binder's mode lives on its DOMAIN, and an arm binder is a binder. It did not,
    for eleven milestones, and the cost was invisible because conversion is
    mode-blind — but `Term.alphaEq` is not, and it is the key `abstractInto`
    generalizes with. It was also the reason the same function written twice, once
    here and once as a hand-written `Term`, was two terms: `Term.clam "A'"` writes
    both halves of a comptime binder and a bare `Term.lam` here wrote one.

    That renaming is what the de Bruijn version got by ARITHMETIC (M30 step 2): it
    elaborated the body in a context contrived to put the motive's binder at the
    index the arm's binder would occupy — hence `pOf`'s `leading` argument, whose
    entries existed only to be counted. Under names the arm's binder is named and
    the substitution says so. -/
partial def elabUElim (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (scrut motive : TSyntax `uterm) (arms : Array (TSyntax `uelimArm)) : MacroM (TSyntax `term × Nat) := do
  let (scrutT, n1) ← elabUTerm rctx pctx next scrut
  let (motiveT, n2) ← elabUTerm rctx pctx n1 motive
  let motiveBare := match motive with | `(uterm| ($e:uterm)) => e | _ => motive
  let (mName, mTy, mBody) ← match motiveBare with
    | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => pure (x.getId.toString, τ, b)
    | _ => Macro.throwError "elim: motive must be a λ `(x : τ). …`"
  let armFor (c : String) : MacroM (Option (Array Ident × Option Ident × TSyntax `ublk)) := do
    for arm in arms do
      match arm with
      | `(uelimArm| $ctor:ident $[($bs:ident)]* $[$ih:ident]? => $body:ublk) =>
        if ctor.getId.toString == c then return some (bs, ih, body)
      | _ => pure ()
    return none
  let getArm (c : String) : MacroM (Array Ident × Option Ident × TSyntax `ublk) := do
    match ← armFor c with
    | some r => pure r
    | none => Macro.throwError s!"elim: missing arm for constructor '{c}'"
  let names := arms.filterMap (fun a => match a with
    | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $_:ublk) => some ctor.getId.toString
    | _ => none)
  -- `P ⟨target⟩`: the motive body with the motive's binder renamed to the arm's.
  let pOf (target : String) : MacroM (TSyntax `term) := do
    let b := (← elabUTerm rctx (mName :: pctx) n2 mBody).1
    `(Dllbc.Term.substP $(quote mName) (Dllbc.Term.pvar $(quote target)) $b)
  if names.contains "Z" || names.contains "S" then
    let (_, _, zb) ← getArm "Z"; let z := (← elabUBlk rctx pctx n2 zb).1
    let (sb, sih, sbody) ← getArm "S"
    let kName := (sb.get! 0).getId.toString
    let ihName := (sih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf kName
    let body := (← elabUBlk rctx (ihName :: kName :: pctx) n2 sbody).1
    let kDom ← binderDom kName (← `(Dllbc.Term.const "Nat"))
    let ihDomM ← binderDom ihName ihDom
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "natRec") $motiveT) $z)
        (Dllbc.Term.lam $(quote kName) $kDom
          (Dllbc.Term.lam $(quote ihName) $ihDomM $body))) $scrutT), n2)
  else if names.contains "True" || names.contains "False" then
    let (_, _, tb) ← getArm "True"; let t := (← elabUBlk rctx pctx n2 tb).1
    let (_, _, fb) ← getArm "False"; let f := (← elabUBlk rctx pctx n2 fb).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motiveT) $t) $f) $scrutT), n2)
  else if names.contains "Nil" || names.contains "Cons" then
    let (_, _, nb) ← getArm "Nil"; let n := (← elabUBlk rctx pctx n2 nb).1
    let (cb, cih, cbody) ← getArm "Cons"
    let hName := (cb.get! 0).getId.toString
    let tName := (cb.get! 1).getId.toString
    let ihName := (cih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf tName
    let body := (← elabUBlk rctx (ihName :: tName :: hName :: pctx) n2 cbody).1
    let hDom ← binderDom hName (← `(Dllbc.Term.const "Nat"))
    let tDom ← binderDom tName (← `(Dllbc.Term.app (Dllbc.Term.const "List") (Dllbc.Term.const "Nat")))
    let ihDomM ← binderDom ihName ihDom
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "listRec") (Dllbc.Term.const "Nat")) $motiveT) $n)
        (Dllbc.Term.lam $(quote hName) $hDom
          (Dllbc.Term.lam $(quote tName) $tDom
            (Dllbc.Term.lam $(quote ihName) $ihDomM $body)))) $scrutT), n2)
  else if names.contains "Pair" then
    -- Σ elimination (§9). `sigmaRec` takes Σ's two parameters — the domain `A` and
    -- the FAMILY `λ x. B` — so the motive's binder type must be written as the Σ
    -- itself, `λ (p : Σ (x : A) → B). goal`. Determined from what is written, never
    -- inferred: a wrong `A`/`B` fails at the use site like every other elim motive.
    -- No `ih`: Σ is not recursive, so the single arm binds exactly the two fields.
    let mTyBare := match mTy with | `(uterm| ($e:uterm)) => e | _ => mTy
    let (aSyn, bName, bSyn) ← match mTyBare with
      | `(uterm| Σ ($y:ident : $A:uterm) → $B:uterm) => pure (A, y.getId.toString, B)
      | `(uterm| Σ ($y:ident : $A:uterm). $B:uterm) => pure (A, y.getId.toString, B)
      -- **Σ0 elims by the SAME eliminator** (M33, §2.7's "no new eliminator"):
      -- `sigmaRec`'s second parameter is the type FAMILY `λ x. B`, and `⇝` is a
      -- mode marker rather than part of `B` — so a Σ0's family is the family its
      -- Σ twin has, and the two rows below are the whole of Σ0's elimination.
      | `(uterm| Σ0 ($y:ident : $A:uterm) → $B:uterm) => pure (A, y.getId.toString, B)
      | `(uterm| Σ0 ($y:ident : $A:uterm). $B:uterm) => pure (A, y.getId.toString, B)
      | _ => Macro.throwError "elim: a Pair motive's binder type must be written as `Σ (x : A) → B` (or `Σ0 (x : A) → B`)"
    let aT := (← elabUTerm rctx pctx n2 aSyn).1
    -- `B` under its own binder — correct for the family `λ x. B` as written, and
    -- renamed below for the arm's second binder domain, whatever the arm calls it.
    let bT := (← elabUTerm rctx (bName :: pctx) n2 bSyn).1
    let (pb, _, pbody) ← getArm "Pair"
    let xName := (pb.get! 0).getId.toString
    let yName := (pb.get! 1).getId.toString
    let body := (← elabUBlk rctx (yName :: xName :: pctx) n2 pbody).1
    -- `B` reaches the Σ's own binder, and the arm names that field itself — so the
    -- arm's second domain is `B` with the Σ binder renamed, the same move `pOf`
    -- makes for a recursor's `ih`.
    let xDom ← binderDom xName aT
    let yDom ← binderDom yName (← `(Dllbc.Term.substP $(quote bName) (Dllbc.Term.pvar $(quote xName)) $bT))
    -- The type FAMILY `λ x. B` is the Σ read back as a function, so its binder is
    -- the Σ's own binder and takes the Σ's own domain — marker included. Written
    -- unmarked, it was the one place a `Σ (Hu : A) → B` and the family
    -- `sigmaRec` takes for it disagreed about `Hu`'s mode.
    let famDom ← binderDom bName aT
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "sigmaRec") $aT)
        (Dllbc.Term.lam $(quote bName) $famDom $bT)) $motiveT)
        (Dllbc.Term.lam $(quote xName) $xDom
          (Dllbc.Term.lam $(quote yName) $yDom $body))) $scrutT), n2)
  else
    Macro.throwError "elim: arms do not match a known recursor (Nat/Bool/List/Σ)"

/-- `elim scrut generalizing goal { arms }` (§18): the motive is
    `λ x. abstractOccurrences scrut goal` — the natural goal with the computed
    subterm abstracted at all its occurrences, mechanically. Bool motives only (the
    count algebra's case-on-`eqb`); Nat/List use the `return` form. -/
partial def elabUGenElim (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (scrut goal : TSyntax `uterm) (arms : Array (TSyntax `uelimArm)) : MacroM (TSyntax `term × Nat) := do
  let (scrutT, n1) ← elabUTerm rctx pctx next scrut
  let (goalT, n2) ← elabUTerm rctx pctx n1 goal
  let armBody (c : String) : MacroM (TSyntax `term) := do
    for arm in arms do
      match arm with
      | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $body:ublk) =>
        if ctor.getId.toString == c then return (← elabUBlk rctx pctx n2 body).1
      | _ => pure ()
    Macro.throwError s!"elim generalizing: missing arm '{c}'"
  let names := arms.filterMap (fun a => match a with
    | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $_:ublk) => some ctor.getId.toString
    | _ => none)
  if names.contains "True" || names.contains "False" then
    let t ← armBody "True"
    let f ← armBody "False"
    let nf := Lean.mkIdent `Dllbc.Std.nfTerm
    let motive ← `(Dllbc.Term.lam Dllbc.genName (Dllbc.Term.const "Bool")
      (Dllbc.abstractOccurrences ($nf $scrutT) ($nf $goalT)))
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motive) $t) $f) $scrutT), n2)
  else
    Macro.throwError "elim generalizing: only Bool motives supported (§18); Nat/List use the `return` form"

end

end Surface

end Dllbc
