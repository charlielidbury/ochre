import Lean
import Dllbc.FnMacro

/-!
# `uterm` / `ublk` — THE term grammar

One grammar, and there is one way in: `ty{ }` (ProgMacro.lean) is `ublk`,
elaborated in the empty context. `fn` is a STATEMENT of `ublk` (M28 θ), so a
declaration is written where a `let` is written and there is no separate
declaration surface to learn.

**THERE IS EXACTLY ONE MACRO** (M29 γ). There were two — `ty{ }` and `pure{ }`,
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
value is identical). `&mut (τ ~> τ')` gives a `τ'` that ignores the snapshot;
`&mut (s : τ ~> τ')` binds `s` as pure var 0 in `τ'` — the `borrowT`/`seedTelescope`
convention in Syntax.lean.

## Resolution discipline (och's law)

Every identifier resolves or errors: pure binder → `pvar`; earlier telescope
param → `var`; known constructor → `ctorApp`; kernel const → `const`; a friendly
reified-function alias (`Le`, `Len`, `Add`, …) → its `…FnT` Term constant; else
the **Lean identifier** of that name, which must denote a `Dllbc.Term` in scope
(a library lemma like `SwapL` or `Set`) — the documented fallback.

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
-- **A PATTERN ARGUMENT** (M34 sugar (iii)) — a binder, or a constructor applied to
-- more of them. This category exists only for ARGUMENT position, and that is not
-- an oversight: at the head of an arm a bare identifier names a CONSTRUCTOR
-- (`Nil => …`), and in argument position the same identifier is a BINDER
-- (`Cons(h, t) => …`). One category cannot mean both, so `uarm` keeps its own two
-- rows for the head and uses `upat` for what sits inside the parens.
declare_syntax_cat upat

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
syntax:70 "&mut" "(" uterm "~>" uterm ")" : uterm            -- borrow type &mut (τ ↝ τ')
syntax:70 "&mut" "(" ident ":" uterm "~>" uterm ")" : uterm  -- borrow type &mut (s : τ ↝ τ')
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
-- **Σ BINDS WITH A DOT, and Π with an arrow** — the punctuation says which former
-- you are looking at before the head letter does. A Π *is* a function, so its
-- arrow is the thing itself; a Σ is a PAIR, and an arrow on a pair former reads
-- like a function it is not. The dot is not a new convention either: the surface's
-- λ has bound with a dot from the start (`λ (Q : Nat). Refl`), so a Σ that binds
-- with one is the grammar being consistent with itself rather than acquiring a
-- second style.
--
-- **The dot is the ONLY Σ spelling.** `Σ (x : A) → B` was the spelling until the
-- corpus was migrated wholesale (286 sites; see the `Σ` migration commits on
-- `sigma-dot-syntax`), and it briefly survived as a parsing alias so that branches
-- written against it could still land. That alias is GONE: an arrow after a Σ
-- binder is now a parse error, which is the point — an alias nobody is required to
-- use is an alias that gets used, and two spellings for one former is the thing
-- this change exists to remove. A branch carrying the old spelling is fixed by one
-- run of `dllbc/scripts/sigmadot.py` over its new files.
syntax:10 "Σ" "(" ident ":" uterm ")" "." uterm:10 : uterm   -- Sigma
-- **Σ0 — the COMPTIME TAIL** (M33, suspensions.md §2.7). Same pair, same
-- constructor, same eliminator: the only difference from `Σ` is that the
-- CODOMAIN is marked `⇝`, which makes the second projection comptime. DLLBC's
-- subset type, with the standard precedent (Lean's `{x : A // P}`, Coq's `sig`,
-- NuPRL/PVS set types) and comptime where those use Prop/irrelevance.
syntax:10 "Σ0" "(" ident ":" uterm ")" "." uterm:10 : uterm  -- Sigma0
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
-- The one confusable neighbour, refused ON PURPOSE. `&mut (s : τ ~> τ')` is the
-- borrow type with a snapshot binder; drop the `~> τ'` and the ascription row above
-- would take it, making `&mut (v : List Nat)` a BORROW OF A SEAL — which is never
-- meaningful (a seal is not a place) and is certainly not what someone writing that
-- meant. Measured before deciding: without this row it parses, silently, and fails
-- downstream as an unrelated unbound-identifier error.
syntax:70 "&mut" "(" ident ":" uterm ")" : uterm             -- always an error
-- **THE SCRUTINEE IS A TERM** (M34 sugar (i)). It used to be an `ident`, and the
-- elaborator then refused every ident that was not a bound runtime local — so
-- `match SplitA(f, m, h, p, &m *tl) { … }` was unwritable and every call whose
-- result is matched had to be spelled `let res = … ; match res { … }` by hand.
-- That hand-spelling is exactly what this row now performs, so the row adds a
-- shorthand and no semantics.
--
-- **A PLAIN VARIABLE STILL TAKES THE OLD PATH, byte for byte.** `elabScrut`
-- below matches a bare ident FIRST and emits the same `.matchE` header it always
-- did, with no `let` around it — which matters because a match on a BORROW
-- variable is the reborrow-mode match (`vecPush`, `zeroAll`), where the arm
-- binders are loans into the scrutinee's payload rather than copies of it.
-- Binding such a scrutinee to a fresh slot first would move it, and the money
-- test would stop being about the forgotten length update. The sugar fires only
-- where the old grammar rejected the scrutinee outright.
syntax:max "match" uterm "{" uarm,* "}" : uterm              -- runtime match (§3)
syntax:max "match" ident ":" uterm "{" uarm,* "}" : uterm    -- …with a branch equation (M23)
syntax:max "if" uterm "{" ublk "}" "else" "{" ublk "}" : uterm  -- §12 sugar over a Bool match
syntax:max "if" ident ":" uterm "{" ublk "}" "else" "{" ublk "}" : uterm  -- …with a branch equation

-- Pure eliminator sugar (§15b) — for `ty{}` / comptime positions. Arm bodies are
-- `ublk` so a `let x = e ; …` proof-let sequence (StdLemmas) works uniformly.
declare_syntax_cat uelimArm
syntax ident ("(" ident ")")* (ident)? "=>" ublk : uelimArm
syntax:max "elim" uterm:max "return" uterm:max "{" uelimArm,* "}" : uterm
syntax:max "elim" uterm:max "generalizing" uterm:max "{" uelimArm,* "}" : uterm

syntax "{" ublk "}" : uarmBody                               -- braced block arm body
syntax uterm : uarmBody                                      -- bare expression arm body
syntax ident "=>" uarmBody : uarm                            -- nullary pattern
-- **THE ARGUMENTS ARE PATTERNS** (M34 sugar (iii)). They used to be `ident,*`, so
-- reading a field of a field cost an explicit inner match and a name for the
-- intermediate; `Cons(Pair(k, v), tl) => …` is now written where it is meant.
-- The rewrite is 1:1 with that hand-spelling and nothing cleverer — see
-- `mintPatArgs`/`wrapPats`. DLLBC match stays ONE ARM PER HEAD CONSTRUCTOR:
-- there is no cross-arm grouping and no pattern matrix, so `Cons(Z, tl)` is not
-- a partial arm that some other arm completes — it is a one-branch inner match
-- on the head's payload, and §9 refuses it as non-exhaustive.
syntax ident "(" upat,* ")" "=>" uarmBody : uarm             -- applied pattern C(x, D(y))
-- `noWs` before `(`, matching the call/ctorApp row and the `let` row below:
-- `C(a, b)` is one token-run everywhere in this grammar.
syntax:max ident : upat                                      -- a binder
syntax:max ident noWs "(" upat,* ")" : upat                  -- a nested constructor

-- **`fn` is a STATEMENT** (M28 θ). §8 says a declaration is a `let`, and §7 says
-- what its right-hand side is — a seal over a recursor or a runtime λ. Put those
-- together and there is nothing for a separate top-level declaration macro to do:
-- `fn f (…) -> R { … } ; rest` is that `let`, written where a `let` is written.
-- The binder telescope reuses `ulamb`, the runtime λ's binder category, because it
-- is the same thing — a list of `x : τ` — and a second category for it would be a
-- second thing to keep in step.
-- **Named**, because the surface has to be able to ASK whether a block contains
-- one (`ElabCheck`, the information rule): a `fn` carries its own `-> retType`,
-- so a block containing one carries its own specification and can be checked
-- without any annotation. That question is asked by syntax kind rather than by
-- scanning for the atom `fn`, which would also match a binder spelled `fn`.
syntax (name := ublkFn)
  "fn" ident ("[" ident "]")? "(" ulamb,* ")" "->" uterm "{" ublk "}" ";" ublk : ublk
syntax "let" ident "=" uterm ";" ublk : ublk                 -- runtime let (→ letIn)
-- **THE SINGLETON-CONSTRUCTOR `let`** (M34 sugar (ii)). `let C(a, b) = e ; rest`
-- is `match e { C(a, b) => rest }` — the REST OF THE BLOCK moves inside the arm,
-- which is the whole of the transformation and the whole of the readability win:
-- a five-deep `match res { Pair(k2, z1) => match z1 { Pair(r2, z2) => … }}}}`
-- pyramid is a flat chain of `let Pair(…) = …;` lines that never indents.
--
-- **The macro asks nothing about the type, deliberately.** A pattern whose
-- constructor is not the scrutinee type's only one desugars anyway, to a
-- one-branch match, and §9's exhaustiveness check refuses it from the kernel
-- with the error it already has ("non-exhaustive — no branch for constructor
-- 'Nil'"). So `let Cons(h, t) = l ;` is rejected, and rejected for the reason
-- that is actually true of it, by the rule that was already there — no
-- constructor table at the surface, no second definition of which types have one
-- constructor, and nothing to keep in step when the basis grows.
--
-- `noWs` before `(`, matching the call/ctorApp row: `C(a, b)` is one token-run
-- everywhere in this grammar.
syntax "let" ident noWs "(" upat,* ")" "=" uterm ";" ublk : ublk
syntax uterm ":=" uterm ";" ublk : ublk                      -- assignment
syntax uterm ";" ublk : ublk                                 -- expression statement (seq)
syntax uterm : ublk                                          -- final expression
-- **`show x` — a value made visible where you put it** (docs/18). ERASED: this
-- row emits `rest` and nothing else, so the kernel never learns the word and a
-- program with `show`s is the same `Term` as one without. What it leaves behind
-- is an info diagnostic carrying exactly what hovering `x` here would say.
--
-- `show` is already a Lean keyword, so declaring it as a leading atom reserves
-- no token that was not reserved — the question `ElabCheck`'s invariant note says
-- to ask before adding one.
syntax "show" ident ";" ublk : ublk                          -- show (erased)

namespace Surface
open Lean

/-- The binder a pure form gets when NOTHING can refer to it: a plain `&mut τ`'s
    entry snapshot, and the non-dependent arrow's domain. Reserved, so it is not
    merely unused but unwritable. -/
def unusedSnapName : String := "§_"

/-- The slot a MATCHED EXPRESSION is bound to (M34 sugar (i)). `match e { … }`
    where `e` is not a plain local is `let §m = e ; match §m { … }`, and this is
    that binder's name.

    **Reserved, and that is what makes the sugar hygienic.** `checkBinder` refuses
    every `§`-prefixed name in source, so no program can write a binding this one
    could shadow or be shadowed by — which is the guarantee the reserved namespace
    exists to give (`isReservedName`, Syntax.lean). The `if` sugar's `"__if"` is the
    older spelling of the same idea and does NOT have that property: a program may
    write `let __if = …`, and since M32 R1 resolves Ω by name, it would be
    resolving the same slot. Fixing that is not this lane's, but the new sugar
    should not add a second instance of it.

    One name for every site is enough, for the reason nested `if`s already
    demonstrate: Ω is name-keyed with newest-wins (`findSlot?`), so an inner `§m`
    shadows an outer one exactly where an inner `let x` shadows an outer `x`, and
    the outer is dead by then — its only reader is the `.matchE` header that has
    already been entered. The ids are distinct regardless, since they come from the
    one counter every binder in this file mints from. -/
def scrutName : String := "§m"

/-- The slot a NESTED PATTERN's payload is bound to (M34 sugar (iii)).
    `Cons(Pair(k, v), tl) => …` is `Cons(§pN, tl) => match §pN { Pair(k, v) => … }`,
    and this is that binder's name. Reserved for `scrutName`'s reason: no program
    can write a `§`-prefixed binder, so nothing a program writes can collide.

    **The id is in the NAME, and that is a correctness requirement rather than a
    debugging convenience.** `§m` gets away with one name for every site because
    an outer `§m` is dead the moment the match it heads is entered. Sibling nested
    patterns are not: `C(A(x), B(y))` binds two of these AT ONCE, in one branch,
    and the match on the first runs while the second is live. Ω is name-keyed with
    newest-wins (`findSlot?` never reads an id), so two live slots sharing a name
    would send the first match's header to the SECOND payload — a silent wrong
    answer, not an error. Suffixing with the id the binder is minted at makes the
    names as distinct as the ids, which the one global counter already guarantees. -/
def patName (id : Nat) : String := "§p" ++ toString id

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

/-- Kernel constructors → `ctorApp`. **Sourced from the kernel's own basis**
    (`Val.ctorNames`, which `Pure.ctorSig` must track) rather than repeated here,
    because
    M26-B gives the list a second job — reserving these names as binder keywords
    — and two lists that must agree is one list too many. -/
def ctorSet : List String := Dllbc.Val.ctorNames
/-- Kernel constants (type formers / recursors / eliminators) → `const`. -/
def constSet : List String := ["Nat", "Bool", "List", "Bot", "Unit", "natRec", "boolRec", "listRec", "sigmaRec", "botElim", "j", "k",
  -- ¶1.1/¶1.3's array basis: the former, the split view, the cons view, the read,
  -- and the split view's two PROJECTIONS (`atake`/`adrop`), which are what lets a
  -- signature name the pieces a carve mints.
  "Array", "arrCat", "acons", "arrRec", "aget", "atake", "adrop"]
/-- Friendly aliases for the reified library functions whose surface name differs
    from their `…FnT` Term-constant (`Le` ↦ `LeFnT`, etc.). Everything else falls
    through to the raw-Lean-identifier resolution, so lemma Terms (`SwapL`, `Set`,
    `SwapL`, …) are referenced by their own names via the use-site `open`s.

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
  -- `res` joins the reserved namespace (12-design D3(a)): inside a borrow's
  -- `~>` RHS it denotes the function's result, so a program binder of that name
  -- would shadow a contract's vocabulary. Grepped before reserving: no in-tree
  -- program binds it.
  Dllbc.isReservedName s || s == "res"
    || (Dllbc.isUpperInit s && (ctorSet.contains s || constSet.contains s))

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

/-! ## Pattern arguments (M34 sugar (iii))

    `Cons(Pair(k, v), tl) => body` is **exactly** what the hand-written
    `Cons(§p, tl) => match §p { Pair(k, v) => body }` elaborates to — same ids,
    same names, same `Term` — and the two functions below are that rewrite and
    nothing cleverer. There is no cross-arm reasoning anywhere in them: each arm
    compiles on its own, DLLBC's match stays one arm per head constructor, and
    deeper discrimination stays an explicit inner match that §9 checks for
    exhaustiveness like any other. `Cons(Z, tl)` is therefore REJECTED (no branch
    for `S`), by the rule that was already there.

    The rewrite is in two passes because the id order demands it. Every argument
    of the head — binder or nested — occupies one slot, and all of them are minted
    BEFORE anything inside them, because that is what a match arm does: the arm's
    binders come from the counter first, and the body follows. Pass one
    (`mintPatArgs`) mints that row and hands back the nested arguments it deferred;
    pass two (`wrapPats`) turns each deferred one into a match around the body,
    recursively, which is where its own arguments are minted.

    **Depth first, which is source order.** `C(A(x, B(y)), D(z))` nests
    `§p₀ → A(x, §p₂) → §p₂ → B(y) → §p₁ → D(z) → body`: applying the one-step
    rewrite to the head produces `A`'s match then `D`'s, and rewriting `A`'s arm
    then pushes `B`'s inside `A`'s — ahead of `D`'s, because `D`'s match is part of
    `A`'s arm body by then. `pend' ++ rest` in `wrapPats` is that sentence. -/

/-- A nested pattern argument that has been given a slot and is waiting for its
    match: the slot's `Var` syntax, the constructor, and the arguments to match. -/
abbrev PendingPat := TSyntax `term × Ident × List (TSyntax `upat)

/-! ## The span side channel

The walker holds each statement's and each argument's `TSyntax` — that is where
`Macro.throwErrorAt` already gets its spans — so while it builds the term it also
accumulates, on the side, a **key term ↦ source syntax** table. `Term` and `Val`
are untouched by a single byte; the positions ride alongside the value, not
inside it.

The key is the term itself, in `stmtKeyOf` normal form, rather than a path.
`atBoundary`'s `pushContinuations` duplicates each continuation into every match
arm before the checker walks the program, so a statement's *position* in the
walked term is not its position in the source and differs per arm — while its
*term* is the same term in every copy. Matching on the term is invariant under
that normalization for free, and needs no second implementation of the fork
logic.

Assembling this costs nothing at check time: the entries are unelaborated syntax,
and the surface only elaborates and evaluates them when a check has actually
failed and a span is needed. -/

/-- One occurrence of a runtime binding, as the walker sees it.

    `stmt` is the statement it occurs in, filled in by `tagOccsFrom` once that
    statement's key is known. `none` means the occurrence sits somewhere the
    walker files no statement for — a telescope type, say — and the point join
    declines rather than guessing a nearby one. -/
structure OccNote where
  ref : Syntax
  id : Nat
  name : String
  stmt : Option Syntax := none
  /-- The S1 answer for this span, when there is one — a parameter's annotation.

      **Carried rather than pushed separately, because the two are not rivals.**
      docs/16 let S1 WIN for a parameter: its annotation is exact and S2 had only
      a binding-time fact to offer against it. Under point hovers that precedence
      hides the case the design exists for — a borrow parameter whose payload a
      match arm has narrowed still reports `v : &mut List Nat`, which is true and
      says nothing about what is in it here. The type and the contents are
      different questions, so the tooltip answers both. -/
  static? : Option String := none
deriving Inhabited

/-- Key-term syntax paired with the source syntax it was written at. -/
structure SpanAcc where
  /-- **Is anyone going to read this table?** (M35, the collection flag.)

      A block that CHECKS never looks at its spans — they exist to locate a
      rejection — so collecting them on the passing path is pure overhead, and it
      was measurable: threading the table through every `ty{ }` in the corpus
      cost +6.9% on a from-scratch suite build. v1 of this design promised "a
      declaration that passes pays nothing for its spans"; this flag is what makes
      that true rather than aspirational.

      **This is NOT the mode flag M29 γ deleted, and the distinction is the whole
      justification.** That flag had SEMANTIC readers — `let` and `&mut` branched
      on it, so the same source elaborated to different `Term`s depending on its
      value, which is exactly why it had to go. This one gates whether DIAGNOSTIC
      METADATA is collected. No rule reads it, no emitted `Term` depends on it,
      and the walker produces byte-identical output either way; it is the same
      class of thing as a trace level. Anyone tempted to relitigate M29 γ against
      it should check that property first — it is asserted by the corpus, since
      every `ty{ }` in the suite elaborates with collection OFF.

      The elaborator therefore walks twice on the rare failing path (once without
      spans, once with) rather than once-with-spans always. A second walk of a
      program that has already been rejected is free at human scale. -/
  collect : Bool := false
  /-- Statement keys, as raw `Syntax` (a `TSyntax` in an accumulator field trips
      the kernel through the `partial` mutual block below). -/
  stmts : Array (Syntax × Syntax) := #[]
  /-- Call-argument keys: the argument's own term, filed under its own span. -/
  args : Array (Syntax × Syntax) := #[]
  -- HOVER METADATA (docs/16). A SECOND collection flag rather than a second
  -- reader of `collect`, because the two are read on opposite paths: spans locate
  -- a REJECTION, hovers describe an ACCEPTED program. Sharing one flag would
  -- either collect spans on every passing elaboration (the +6.9% `collect` exists
  -- to avoid) or collect hovers only on failing ones, which is nobody's feature.
  /-- Is anyone going to read the hover tables? -/
  hover : Bool := false
  /-- Spans whose tooltip the WALKER already knows, rendered: a parameter binder
      or occurrence (its annotation is right there in the source) and a callee
      name (its signature is the `fn` above it). No checker involvement, so these
      work in `prog defer_check { }` too. -/
  hovers : Array (Syntax × String) := #[]
  /-- Spans whose tooltip only the CHECKER knows: an occurrence of a runtime
      binding, joined against the checker's tables by id AND name — and, for
      point hovers (docs/17), by the STATEMENT it occurs in. -/
  occs : Array OccNote := #[]
  /-- Lexically scoped, innermost first: `(name, runtime id, annotation text)` for
      every parameter binder in scope.

      **The id is in the key and is not decoration.** A body may shadow a
      parameter (`let v = …` under `(v : &mut List Nat)`), and a name-only lookup
      would then show the parameter's annotation on an occurrence of the `let`.
      Requiring the occurrence to resolve to the parameter's own id is what makes
      shadowing fall through to the checker's table instead of reporting a stale
      answer confidently. -/
  ptypes : List (String × Nat × String) := []
  /-- Occurrence indices that a `show` filed — the sites whose answer is printed
      EAGERLY as a diagnostic rather than waiting to be hovered (docs/18). -/
  showOccs : Array Nat := #[]
  /-- Occurrences awaiting a statement key — a `show`'s, filed before the
      statement it anchors to has been walked (docs/18 §3). `tagOccsFrom` drains
      these along with its own range. -/
  pendingOccs : Array Nat := #[]
  /-- Lexically scoped: `fn` name ↦ its signature's source text. This is what the
      plan called "the registry" — there is no registry (docs/05 §1.A: it was
      never built, because scope IS the call table), and scope answers the same
      question here for the same reason. -/
  fsigs : List (String × String) := []
deriving Inhabited

/-- The surface walker's monad: `MacroM` plus the span side channel. -/
abbrev UM := StateT SpanAcc MacroM

/-! ## Hover metadata: filing, scoping, and reading source text -/

/-- The source text a piece of syntax was written as. `reprint` is exact — it
    gives back what the author typed, not a pretty-printing of what it elaborated
    to — which is the whole of S1: a parameter's type needs no computation
    because it is already written down. -/
def srcText (stx : Syntax) : String :=
  match stx.reprint with
  | some s => s.trimAscii.toString
  | none => "?"

/-- File a tooltip the walker computed itself. -/
def noteHover (ref : Syntax) (text : String) : UM Unit :=
  modify fun a => if a.hover then { a with hovers := a.hovers.push (ref, text) } else a

/-- File an occurrence of a runtime binding, for the checker-side join. The
    statement is filled in afterwards by `tagOccsFrom`, because a statement's key
    is not known until it has been walked (a `let`'s binder id is the counter
    AFTER its right-hand side). -/
def noteOcc (ref : Syntax) (id : Nat) (name : String) : UM Unit :=
  modify fun a =>
    if a.hover then { a with occs := a.occs.push { ref, id, name } } else a

/-- Where the occurrence array stands before a statement is walked. -/
def occMark : UM Nat := return (← get).occs.size

/-- Tag every occurrence filed since `lo` with the statement they occur in.

    **Filed first and tagged after, because the key is not knowable first.** A
    `let`'s key is its binder, and the binder id is the counter AFTER the
    right-hand side has been walked — so the occurrences inside that right-hand
    side exist before the key that describes where they are. The walker knows the
    statement's extent, which is all this needs. -/
def tagOccsFrom (lo : Nat) (key : TSyntax `term) : UM Unit :=
  modify fun a =>
    if !a.hover then a else
      -- PENDING occurrences are tagged too, and then cleared. A `show`'s
      -- occurrence is filed before this statement exists, and this statement is
      -- the one it wants: `replayTo` gives the state ENTERING a statement, which
      -- is the state at a `show` written just above it (docs/18 §3).
      { a with
        occs := a.occs.mapIdx (fun i o =>
          if (i ≥ lo || a.pendingOccs.contains i) && o.stmt.isNone then
            { o with stmt := some key.raw } else o)
        pendingOccs := #[] }

/-- Render a binder's tooltip. One place, so a binder and its occurrences cannot
    drift into two spellings. -/
def hoverText (name : String) (ty : String) : String := s!"**{name} : `{ty}`**"

/-- Run `act` with extra parameter types and callee signatures in scope, and put
    the scope back afterwards.

    Save-and-restore on the accumulator rather than a new argument threaded
    through the walker: `ptypes`/`fsigs` are lexically scoped, the walker is a
    30-call mutual block, and the port's standing rule is to ride existing walker
    state rather than add a layer. The restore is skipped on the throwing path,
    which costs nothing — a block that failed to elaborate has no tooltips. -/
def withHoverScope {α : Type} (ps : List (String × Nat × String))
    (fs : List (String × String)) (act : UM α) : UM α := do
  let a ← get
  if !a.hover then act else do
    modify fun a => { a with ptypes := ps ++ a.ptypes, fsigs := fs ++ a.fsigs }
    let r ← act
    modify fun a' => { a' with ptypes := a.ptypes, fsigs := a.fsigs }
    pure r

/-- File a statement key at its source span. -/
def noteStmtSpan (key : TSyntax `term) (ref : Syntax) : UM Unit :=
  modify fun a => if a.collect then { a with stmts := a.stmts.push (key.raw, ref) } else a

/-- File a call argument's key at its source span. -/
def noteArgSpan (key : TSyntax `term) (ref : Syntax) : UM Unit :=
  modify fun a => if a.collect then { a with args := a.args.push (key.raw, ref) } else a

/-! The key builders live OUT here, not in the walker, because a quotation in
    argument position inside the walker's `partial mutual` block makes the kernel
    reject the whole block with "unknown free variable `_kernel_fresh.N`" — a Lean
    4.16 elaboration bug, not a design constraint. Keeping them out is better
    structure anyway: the walker states *what* it is filing, and the key normal
    forms are defined in one place.

    **`stmtKeyOf` is applied at LOOKUP, not here**, and that is forced by the
    import order rather than chosen: `stmtKeyOf` lives in `Machine.lean`, which is
    BELOW this file, so a quotation naming it here is an identifier that cannot be
    resolved where the key is finally elaborated — it survives as
    `Dllbc.stmtKeyOf✝` and fails with "unknown identifier". The consumer
    (`ElabCheck.spanFor`) normalizes instead, which costs nothing: `stmtKeyOf` is
    idempotent, so the two builders below that already emit a normal form are
    unaffected by being normalized again. -/

/-- File a statement under its own term, raw. -/
def spanOfStmt (t : TSyntax `term) (ref : Syntax) : UM Unit :=
  noteStmtSpan t ref

/-- File a `let` statement under its binder alone (runtime ids are unique). -/
def spanOfLet (id : Nat) (name : String) (ref : Syntax) : UM Unit := do
  noteStmtSpan (← `(Dllbc.Term.letIn ⟨$(quote id), $(quote name)⟩ Dllbc.Term.unit Dllbc.Term.unit)) ref

/-- File a `fn` statement. It is a `let` like any other, but every `fn` shares the
    `declSlot` TAG as its id (M32 R4), so the NAME is what distinguishes one from
    another here — which is exactly what `Ω` resolves by. -/
def spanOfFn (name : String) (ref : Syntax) : UM Unit := do
  noteStmtSpan (← `(Dllbc.Term.letIn ⟨Dllbc.declSlot, $(quote name)⟩ Dllbc.Term.unit
                      Dllbc.Term.unit)) ref

/-- File an assignment under its place and right-hand side. -/
def spanOfAssign (place rhs : TSyntax `term) (ref : Syntax) : UM Unit := do
  noteStmtSpan (← `(Dllbc.Term.assign $place $rhs Dllbc.Term.unit)) ref

/-- File each of a call's arguments under its own span. -/
def spanOfArgs (keys : Array (TSyntax `term)) (refs : Array Syntax) : UM Unit :=
  (keys.zip refs).forM fun kr => noteArgSpan kr.1 kr.2

/-- Is this argument a nested PATTERN rather than a BINDER? Either it is a
    constructor applied to arguments, or it is a NULLARY constructor spelled bare
    — `Cons(Z, tl)`, `Pair(True, x)`.

    **The bare form takes no new rule and cannot change an existing program**, for
    a reason worth stating because it is the whole justification: the names it
    claims are exactly `ctorSet`, and `checkBinder` ALREADY refuses every one of
    them in this position ("a constructor … cannot be a binder", §6's
    capitalisation rule). So each name this row now reads as a pattern is a name
    that was a hard macro error a line ago; nothing that parsed before parses
    differently now. `ctorSet` is the kernel's own basis (`Val.ctorNames`) and not
    a second list — the surface still has no table of its own to keep in step.

    `constSet` names (`Nat`, `List`, `natRec`, …) are NOT constructors and stay
    refused, with `checkBinder`'s message. -/
def upatParts (p : TSyntax `upat) : MacroM (Ident × Option (List (TSyntax `upat))) := do
  match p with
  | `(upat| $c:ident($args,*)) => pure (c, some args.getElems.toList)
  | `(upat| $x:ident) =>
    pure (x, if ctorSet.contains x.getId.toString then some [] else none)
  | _ => Macro.throwErrorAt p "decl: unexpected pattern argument"

/-- Mint fresh runtime ids for one row of pattern arguments, extending `rctx` and
    returning the extended context, the next free id, the argument `Var` syntaxes
    (in order) and the nested arguments deferred to `wrapPats`. Binder ids are
    ABSOLUTE and globally unique — minted from one counter threaded through every
    elaborator — which is why they stay distinct across the arms of a single match.

    A nested argument takes a slot like any other and puts NOTHING into `rctx`:
    its name is reserved, so no source can refer to it, and the only reader it
    will ever have is the `.matchE` header `wrapPats` builds from the `Var`
    returned here. -/
partial def mintPatArgs (rctx : List (String × Nat)) (next : Nat) :
    List (TSyntax `upat) →
    MacroM (List (String × Nat) × Nat × Array (TSyntax `term) × List PendingPat)
  | [] => pure (rctx, next, #[], [])
  | p :: ps => do
    -- The identifier comes back from `upatParts` and is not read off `p` directly:
    -- `upat`'s binder row WRAPS its ident in a node of its own, so `⟨p.raw⟩` is a
    -- `upat` wearing an `Ident`'s type and `getId` answers the anonymous name for
    -- it — a binder called "" that nothing can refer to, which is a silent
    -- unbound-variable error at every use site rather than a type error here.
    match ← upatParts p with
    | (x, none) => do
      checkBinder x
      let name := x.getId.toString
      let v ← `((⟨$(quote next), $(quote name)⟩ : Dllbc.Var))
      let (rctx', n, vs, pend) ← mintPatArgs ((name, next) :: rctx) (next + 1) ps
      pure (rctx', n, #[v] ++ vs, pend)
    | (c, some args) => do
      let v ← `((⟨$(quote next), $(quote (patName next))⟩ : Dllbc.Var))
      let (rctx', n, vs, pend) ← mintPatArgs rctx (next + 1) ps
      pure (rctx', n, #[v] ++ vs, (v, c, args) :: pend)

/-- Wrap `body` in the deferred nested matches, outermost first. `body` is a
    continuation rather than a syntax tree because the two rows that call this
    disagree about what a body IS — an arm's is a `uarmBody`, the `let` pattern's
    is the REST OF THE BLOCK — and they agree about everything else. -/
partial def wrapPats (rctx : List (String × Nat)) (next : Nat) (pend : List PendingPat)
    (body : List (String × Nat) → Nat → UM (TSyntax `term × Nat)) :
    UM (TSyntax `term × Nat) := do
  match pend with
  | [] => body rctx next
  | (v, c, args) :: rest => do
    let (rctx', n1, vars, pend') ← mintPatArgs rctx next args
    let (inner, n2) ← wrapPats rctx' n1 (pend' ++ rest) body
    return (← `(Dllbc.Term.matchE $v none
      [Dllbc.Branch.mk $(quote c.getId.toString) [$vars,*] $inner]), n2)

/-- The branch-equation form takes NO nested patterns in v1, and says so here.

    `match h : x { … }` binds one `h` for the whole match and its TYPE is what
    varies per arm — the equation between the scrutinee and this arm's
    constructor. A nested pattern is a second match, at a position where nobody
    has said what that equation would be: the payload's own equation, the outer
    one refined, or a conjunction. Refusing is cheap and reversible; answering it
    silently and wrongly is neither. The inner match is still writable by hand,
    with its own `match h2 : …` if an equation is wanted there. -/
def refuseNestedPat (p : TSyntax `upat) : MacroM Unit := do
  if (← upatParts p).2.isSome then
    Macro.throwErrorAt p "decl: the branch-equation form `match h : e { … }` does not take nested patterns. `h`'s type is the equation between the scrutinee and THIS arm's constructor, and no equation is defined at a nested position — write the inner match explicitly (with its own `match h2 : …` if it needs one)."
  else pure ()

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

/-- File a hover for one identifier OCCURRENCE (docs/16).

    **This mirrors `resolveName`'s precedence and must keep mirroring it.** A name
    that resolves to a pure binder is not a runtime variable, and `resolveName`
    decides that by consulting `pctx` FIRST; a tooltip that skipped the same test
    would describe a `let` the occurrence does not refer to. The two are separate
    functions because one is `MacroM` and produces a term while this is `UM` and
    produces metadata, so the shared discipline is stated rather than factored:
    **pure binder, then runtime slot, then `fn` slot, then nothing.**

    Nothing is the right answer for the rest. A constructor, a kernel constant and
    a Lean-level lemma all hover as themselves in the ordinary Lean way once they
    reach the emitted term, and inventing a DLLBC tooltip for them would replace
    real information with a guess. -/
def noteIdent (rctx : List (String × Nat)) (pctx : List String) (x : Ident) : UM Unit := do
  let a ← get
  if !a.hover then return
  let s := x.getId.toString
  if pctx.contains s then return
  match localId rctx s with
  | some id =>
    -- A parameter answers from its own annotation (S1) — but only when the
    -- occurrence resolves to THAT binder; see `SpanAcc.ptypes`.
    match a.ptypes.find? (fun p => p.1 == s && p.2.1 == id) with
    | some p =>
      -- BOTH: the annotation (always true) and the point-fact (what is in it
      -- here). See `OccNote.static?`.
      let note : OccNote :=
        { ref := x.raw, id := id, name := s, static? := some (hoverText s p.2.2) }
      modify fun acc => if acc.hover then { acc with occs := acc.occs.push note } else acc
    | none => noteOcc x.raw id s
  | none =>
    match fnSlotId rctx s with
    | some id =>
      match a.fsigs.lookup s with
      | some sig => noteHover x.raw (hoverText s sig)
      | none => noteOcc x.raw id s
    | none => pure ()

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

/-- Put a matched expression's `let` back around the match, or nothing at all when
    the scrutinee was already a place (M34). The two match rows and the
    `let C(…) = …` row all end this way, and each of them owes the SAME identity
    on the plain-variable path — so the wrapping is written once. -/
def wrapScrut (scrut : TSyntax `term) (pre? : Option (TSyntax `term))
    (body : TSyntax `term) : MacroM (TSyntax `term) :=
  match pre? with
  | none => pure body
  | some e => `(Dllbc.Term.letIn $scrut $e $body)

partial def collectAppU : TSyntax `uterm → TSyntax `uterm × Array (TSyntax `uterm)
  | `(uterm| $f:uterm $a:uterm) => let (h, as) := collectAppU f; (h, as.push a)
  | t => (t, #[])

mutual

partial def elabUTerm (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `uterm) : UM (TSyntax `term × Nat) := do
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
    -- **`*res` — the exit payload of the issued borrow** (12-design D1/D3(a)).
    -- `res` is a RESERVED name (reservedBinder refuses it as a binder, and the
    -- corpus was grepped clean before reserving), denoting the function's whole
    -- result inside a borrow's `~>` RHS. It lowers to the inert marker spine
    -- `@res k` (k = the issued-borrow index; the whole-result form is 0), which
    -- rides through readC/nf as a neutral and is substituted at the two
    -- discharge sites: the audit's pin check (fresh exit σ's) and the group
    -- end's pinned release (the actual surrendered payloads). The multi-issued
    -- navigation forms `*(fst res)` / `*(snd res)` are D3(a)'s follow-on and
    -- arrive with the split_at_mut stage, not here.
    match e with
    | `(uterm| res) =>
      return (← `(Dllbc.Term.app (Dllbc.Term.const "@res") (Dllbc.Term.ctorApp "Z" [])), next)
    | _ =>
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
  | `(uterm| &mut ( $τ:uterm ~> $s:uterm )) => do                -- borrow type, owed type ignores s
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
    parsed.forM (fun p => liftM (checkBinder p.1))
    -- `elabLamBinders` pushes each binder's annotation into scope as it mints it
    -- (a binder's type may mention the ones to its left, so the pushes have to be
    -- incremental); this is the matching pop, which is what keeps the scope
    -- lexical.
    let saved := (← get).ptypes
    let (rctx', next', binderSyns) ← elabLamBinders rctx pctx next parsed
    let (b', n) ← elabUBlk rctx' pctx next' b
    modify fun a => if a.hover then { a with ptypes := saved } else a
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
    Macro.throwErrorAt x s!"&mut ({x.getId} : τ) is not a borrow type — the snapshot-binder spelling is `&mut ({x.getId} : τ ~> τ')`, where `τ'` is what the borrow OWES back and `{x.getId}` is its entry snapshot, bound as pure var 0 in `τ'`. Without the `~> τ'` this would read as `&mut` applied to the ascription `({x.getId} : τ)`, which is a borrow of a SEAL — never meaningful, since a seal is not a place. If you meant a plain borrow of the type, write `&mut τ`."
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
      -- Argument granularity: `processArgs` checks actuals positionally against
      -- the telescope, threading the instantiation, so when argument `k` fails it
      -- holds `k` AND the expected type instantiated at the earlier actuals.
      -- Filing each argument's term at its own span is the whole cost of turning
      -- that into a squiggle on the offending argument alone.
      spanOfArgs args' (args.getElems.map (·.raw))
      -- The CALLEE NAME. `noteIdent` sends a `fn` slot to its signature and a
      -- value-callee slot to the checker's table, which is the same split the two
      -- lines below make for the emitted term.
      noteIdent rctx pctx c
      match localId rctx name with
      | some id =>
        return (← `(Dllbc.Term.appSpine (.var ⟨$(quote id), $(quote name)⟩) [$args',*]), n)
      | none => return (← `(Dllbc.Term.call $(quote name) [$args',*]), n)
  | `(uterm| match $e:uterm { $arms,* }) => do
    let (scrut, pre?, n1) ← elabScrut rctx pctx next e
    let (arms', n) ← elabUArms rctx pctx n1 arms.getElems.toList
    return (← wrapScrut scrut pre? (← `(Dllbc.Term.matchE $scrut none [$arms',*])), n)
  -- M23: `match h : x { … }` — the branch-equation form. One binder for the whole
  -- match (its TYPE is what varies per arm), as in Lean's `match h : x with`.
  --
  -- The scrutinee goes through the same `elabScrut` as the plain form, so the
  -- equation form composes with sugar (i) for free and — on the plain-variable
  -- path — the equation binder still lands at id `next`, since `elabScrut` does
  -- not touch the counter there.
  | `(uterm| match $h:ident : $e:uterm { $arms,* }) => do
    checkBinder h
    -- Nested patterns are refused HERE and nowhere else (M34 sugar (iii)): the
    -- equation binder has no meaning at a nested position, so the form that binds
    -- one does not take them. See `refuseNestedPat`.
    for arm in arms.getElems do
      match arm with
      | `(uarm| $_:ident ($args,*) => $_:uarmBody) => args.getElems.forM (fun p => liftM (refuseNestedPat p))
      | _ => pure ()
    let (scrut, pre?, n1) ← elabScrut rctx pctx next e
    let hName := h.getId.toString
    let (arms', n) ← elabUArms ((hName, n1) :: rctx) pctx (n1 + 1) arms.getElems.toList
    let m ← `(Dllbc.Term.matchE $scrut (some ⟨$(quote n1), $(quote hName)⟩) [$arms',*])
    return (← wrapScrut scrut pre? m, n)
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
        noteIdent rctx pctx h
        let hterm ← resolveName rctx pctx h
        let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
        return (out, n)
    | _ => do
      let (hterm, n0) ← elabUTerm rctx pctx next head
      let (argTerms, n) ← elabUList rctx pctx n0 args.toList
      let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
      return (out, n)
  | `(uterm| $x:ident) => do
    -- EVERY occurrence, not just the binder: the walker resolves each ident to
    -- its variable already, so filing the pair costs one lookup (docs/16 S1).
    noteIdent rctx pctx x
    return (← resolveName rctx pctx x, next)
  | _ => Macro.throwErrorAt stx "decl: unexpected term syntax"

/-- **The scrutinee half of every match row** (M34 sugar (i)). Returns the `Var`
    the match reads, the right-hand side to `let`-bind it to (`none` when there is
    nothing to bind), and the counter.

    A bare identifier naming a bound runtime local takes the FIRST branch, which
    is the pre-sugar path unchanged: the same `Var`, no `let`, and the counter
    untouched. That identity is not a nicety. A match on a borrow variable is the
    reborrow-mode match — the arm binders become loans INTO the scrutinee's
    payload, which is how `vecPush` writes both fields of a `Σ` through one `&mut`
    and how `zeroAll` walks a list — and binding the scrutinee to a fresh slot
    first would MOVE it, quietly turning those into matches on a copy.

    An identifier that is not a local still ERRORS, rather than falling through to
    the fresh-slot path. The names that reach here are `fn` slots, constructors and
    pure binders, and none of them is a runtime place; the sugar is for the forms
    the grammar could not spell at all, and an identifier was always spellable.

    **Parentheses are stripped before the question is asked**, as they are
    everywhere else in this elaborator (`elabUTerm`'s grouping row). Left in, they
    would be the sharpest edge the sugar has: `match (v) { … }` on a borrow would
    miss the ident row, take the fresh-slot path, and MOVE what `match v { … }`
    reborrows — the same program, differing by two characters, differing in
    ownership. -/
partial def elabScrut (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (e : TSyntax `uterm) : UM (TSyntax `term × Option (TSyntax `term) × Nat) := do
  match e with
  | `(uterm| ($inner:uterm)) => elabScrut rctx pctx next inner
  | `(uterm| $x:ident) => do
    -- **THE SCRUTINEE IS AN OCCURRENCE LIKE ANY OTHER** (docs/16). This row is why
    -- it needed saying: the plain-variable path answers here and never reaches
    -- `elabUTerm`'s ident row, so without this call a parameter would hover
    -- everywhere EXCEPT in `match n { … }` — and match scrutinees are everywhere.
    -- Found by probing rather than by reading: `n` reported `Nat` at its binder
    -- and nothing one line below it.
    noteIdent rctx pctx x
    let s := x.getId.toString
    match localId rctx s with
    | some id => return (← `((⟨$(quote id), $(quote s)⟩ : Dllbc.Var)), none, next)
    | none => Macro.throwErrorAt x s!"decl: match scrutinee '{s}' is not a bound runtime variable"
  | _ => do
    -- The fresh binder is minted at the POST-RHS counter and the block continues
    -- at `+1` — the `let` row's own discipline, because this is a `let`.
    let (e', n1) ← elabUTerm rctx pctx next e
    return (← `((⟨$(quote n1), $(quote scrutName)⟩ : Dllbc.Var)), some e', n1 + 1)

partial def elabUList (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (TSyntax `uterm) → UM (Array (TSyntax `term) × Nat)
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
    List (Ident × TSyntax `uterm) → UM (List (String × Nat) × Nat × Array (TSyntax `term))
  | [] => pure (rctx, next, #[])
  | (x, τ) :: rest => do
    let name := x.getId.toString
    let (τT, n1) ← elabUTerm rctx pctx (next + 1) τ
    let τD ← binderDom name τT
    let entry ← `(((⟨$(quote next), $(quote name)⟩ : Dllbc.Var), $τD))
    -- A runtime λ's binders are annotated exactly as a `fn`'s are, so they are
    -- the same S1 case (docs/16). Their ids come from the counter rather than
    -- from a position, which is why the entry carries `next` rather than an index.
    noteHover x.raw (hoverText name (srcText τ.raw))
    modify fun a =>
      if a.hover then { a with ptypes := (name, next, srcText τ.raw) :: a.ptypes } else a
    let (rctx', n2, more) ← elabLamBinders ((name, next) :: rctx) pctx n1 rest
    pure (rctx', n2, #[entry] ++ more)

/-- Build the telescope entry syntaxes, threading the runtime-var context so that
    parameter `i`'s type sees params `0 .. i-1` (each at its positional id) — the
    `seedTelescope` convention — and then the ENCLOSING scope, exactly as the
    return type and the body do (the `fn` row's R2 rule). Params come first in
    the lookup, so a parameter shadows an enclosing binding of its name. The
    positional ids collide with the enclosing block's counter and that is fine
    for the same reason it is fine for the body: Ω resolves by NAME (M32 R1).
    Types elaborate in type mode (⇝). -/
partial def buildTele (params : List (String × Nat)) (rctx : List (String × Nat))
    (pctx : List String) (i : Nat) :
    List (String × TSyntax `uterm) → UM (Array (TSyntax `term))
  | [] => pure #[]
  | (nm, τ) :: rest => do
    let (τT, _) ← elabUTerm (params ++ rctx) pctx 0 τ
    let entry ← `((($(quote nm), $τT) : String × Dllbc.Term))
    let rest' ← buildTele (params ++ [(nm, i)]) rctx pctx (i + 1) rest
    pure (#[entry] ++ rest')

partial def elabUArms (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (TSyntax `uarm) → UM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← elabUArm rctx pctx next a
    let (rest, n2) ← elabUArms rctx pctx n1 as
    pure (#[a'] ++ rest, n2)

partial def elabUArm (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (arm : TSyntax `uarm) : UM (TSyntax `term × Nat) := do
  match arm with
  | `(uarm| $c:ident => $body:uarmBody) => do
    let (body', n) ← elabUArmBody rctx pctx next body
    return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [] $body'), n)
  | `(uarm| $c:ident ($args,*) => $body:uarmBody) => do
    -- The head's arguments are minted first, ALL of them, and the nested ones
    -- then wrap the body from the counter the body would have started at — which
    -- is what makes this arm the same `Term` as its hand-written twin and not
    -- merely a convertible one (`Tests.Sugar`'s goldens).
    let (rctx', n1, argVars, pend) ← mintPatArgs rctx next args.getElems.toList
    let (body', n) ← wrapPats rctx' n1 pend (fun r k => elabUArmBody r pctx k body)
    return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [$argVars,*] $body'), n)
  | _ => Macro.throwErrorAt arm "decl: unexpected match arm"

partial def elabUArmBody (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (body : TSyntax `uarmBody) : UM (TSyntax `term × Nat) := do
  match body with
  | `(uarmBody| { $b:ublk }) => elabUBlk rctx pctx next b
  | `(uarmBody| $e:uterm) => do          -- a bare arm body IS the arm's final statement
    let (e', n) ← elabUTerm rctx pctx next e
    spanOfStmt e' e
    return (e', n)
  | _ => Macro.throwErrorAt body "decl: unexpected arm body"

partial def elabUBlk (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `ublk) : UM (TSyntax `term × Nat) := do
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
    -- The binder's IDENT is kept, not just its name: it is the span a parameter's
    -- tooltip is filed at (docs/16 S1).
    let parsedI ← ps.getElems.toList.mapM fun (p : TSyntax `ulamb) => match p with
      | `(ulamb| $x:ident : $τ:uterm) => pure (x, τ)
      | _ => Macro.throwErrorAt p "fn: malformed parameter (expected `x : τ`)"
    let parsed := parsedI.map fun (x, τ) => (x.getId.toString, τ)
    let names := parsed.map (·.1)
    let n := names.length
    -- The telescope's own §5.2 positional context, and the body's: parameter `i`
    -- at runtime id `i`, fresh binders from `n`. Identical to what `decl{ }` builds
    -- — deliberately, since the `FnDef` this produces has to BE the one it builds.
    let fullRctx : List (String × Nat) := names.zip (List.range n)
    -- **S1 — a parameter's type is ALREADY WRITTEN DOWN** (docs/16). The tooltip
    -- is the annotation's own source text: exact, no computation, and no checker
    -- involvement, which is why parameter hovers work in `prog defer_check { }`
    -- too. Keyed by the §5.2 positional id, so that a body-local `let` shadowing a
    -- parameter falls through to the checker's table instead of being answered
    -- confidently from the wrong binder.
    let pTypes : List (String × Nat × String) :=
      (parsedI.zip (List.range n)).map fun ((x, τ), i) =>
        (x.getId.toString, i, srcText τ.raw)
    parsedI.forM fun (x, τ) => noteHover x.raw (hoverText x.getId.toString (srcText τ.raw))
    let teleSyns ← withHoverScope pTypes [] (buildTele [] rctx pctx 0 parsed)
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
    let (retT, _) ← withHoverScope pTypes [] (elabUTerm (fullRctx ++ rctx) pctx 0 ret)
    let (bodyT, _) ← withHoverScope pTypes [] (elabUBlk (fullRctx ++ rctx) pctx n body)
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
    -- The `fn` statement's own span, at its name and signature. It is the
    -- fallback for a rejection raised inside the body whose own statement the
    -- audit could not carry out (see `auditAllPathsD`): the error lands on the
    -- declaration rather than on the whole program.
    spanOfFn nm (mkNullNode #[name, ret])
    -- **A CALLEE'S SIGNATURE, from scope** (docs/16 S1's cheap extension). The
    -- plan says "from the registry"; there is no registry — docs/05 §1.A deleted
    -- it before it was written, because a callee is a binding lexically above the
    -- call and so scope IS the call table. Scope answers this question too, and
    -- the entry is visible for exactly `rest`: not inside the body (a `fn` is not
    -- in scope in its own right-hand side, §8) and not after the block.
    let sigText := "(" ++ ", ".intercalate
        (parsedI.map fun (x, τ) => s!"{x.getId} : {srcText τ.raw}")
      ++ ") -> " ++ srcText ret.raw
    noteHover name.raw (hoverText nm sigText)
    let (rest', n2) ← withHoverScope [] [(nm, sigText)]
      (elabUBlk ((nm, Dllbc.declSlot) :: rctx) pctx next rest)
    return (← `(Dllbc.Term.letIn $slot
                  (Dllbc.FnMacro.fnElabOrFail
                    (Dllbc.FnDef.mk $(quote nm) [$teleSyns,*] $retT $bodyT $decT))
                  (Dllbc.FnMacro.bindFn $slot $decT $rest')), n2)
  | `(ublk| let $x:ident = $e:uterm ; $rest:ublk) => do
    checkBinder x
    let occLo ← occMark
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
    -- File this statement at `x = e`. The key is the BINDER alone: runtime ids
    -- are globally unique, so it identifies the statement outright and carries
    -- none of the right-hand side's bulk.
    spanOfLet n1 name (mkNullNode #[x, e])
    -- The `let` BINDER's own span, filed like an occurrence: its type comes from
    -- the checker (docs/16 S2), so it joins against `St.letTypes` exactly as the
    -- uses below it do, under the same id.
    noteOcc x.raw n1 name
    -- Every occurrence in this statement — the right-hand side's and the binder's
    -- — is filed under this statement's key, which is the POINT a hover on any of
    -- them asks about (docs/17).
    tagOccsFrom occLo (← `(Dllbc.Term.letIn ⟨$(quote n1), $(quote name)⟩
                             Dllbc.Term.unit Dllbc.Term.unit))
    let (rest', n2) ← elabUBlk ((name, n1) :: rctx) pctx' (n1 + 1) rest
    return (← `(Dllbc.Term.letIn ⟨$(quote n1), $(quote name)⟩ $e' $rest'), n2)
  -- **`let C(a, b) = e ; rest` = `match e { C(a, b) => rest }`** (M34 sugar (ii)).
  --
  -- The elaboration is the `uarm` path with the arm body supplied by the ENCLOSING
  -- block rather than by a brace of its own: `elabScrut`, then `mintBinders` at the
  -- counter the arms would have started from, then the REST of the block under
  -- those binders. Getting that order right is what makes the two spellings the
  -- same `Term` and not merely convertible ones — the binder ids are minted from
  -- the same counter at the same point, so a `let Pair(k2, z1) = res ;
  -- let Pair(r2, z2) = z1 ; …` chain is literally the pyramid it replaces.
  --
  -- `pctx` is passed through UNFILTERED, which is what `elabUArm` does with a
  -- match's pattern binders and is therefore what this row must do: a pattern
  -- binder does not shadow a pure binder of its name here, because it does not
  -- there. (`let x = e` DOES filter, and the asymmetry between the two is
  -- pre-existing — see the `let` row above. Whichever way it is settled, it should
  -- be settled for both at once, since these desugar to each other's forms.)
  | `(ublk| let $c:ident($args,*) = $e:uterm ; $rest:ublk) => do
    let (scrut, pre?, n1) ← elabScrut rctx pctx next e
    let (rctx', n2, argVars, pend) ← mintPatArgs rctx n1 args.getElems.toList
    -- Nested arguments (M34 sugar (iii)) wrap the rest of the block in their
    -- matches, which is the same rewrite `elabUArm` performs — and has to be, since
    -- this row IS an arm whose body is the enclosing block. `let Pair(a, Pair(b, c))
    -- = p ;` and the two-line chain that spells it out are one `Term`.
    let (rest', n3) ← wrapPats rctx' n2 pend (fun r k => elabUBlk r pctx k rest)
    let m ← `(Dllbc.Term.matchE $scrut none
                [Dllbc.Branch.mk $(quote c.getId.toString) [$argVars,*] $rest'])
    return (← wrapScrut scrut pre? m, n3)
  | `(ublk| $p:uterm := $e:uterm ; $rest:ublk) => do
    let occLo ← occMark
    let (p', n1) ← elabUTerm rctx pctx next p
    let (e', n2) ← elabUTerm rctx pctx n1 e
    spanOfAssign p' e' (mkNullNode #[p, e])
    tagOccsFrom occLo (← `(Dllbc.Term.assign $p' $e' Dllbc.Term.unit))
    let (rest', n3) ← elabUBlk rctx pctx n2 rest
    return (← `(Dllbc.Term.assign $p' $e' $rest'), n3)
  -- **`show x ; rest` — ERASED** (docs/18). Emits `rest` and nothing else: no
  -- node, no read, no move, no borrow, no Ω. The identifier is resolved exactly
  -- as any other occurrence is (so an unknown name gets the ordinary
  -- unbound-identifier error, with no second message to keep in step), its
  -- occurrence is filed, and it is left PENDING for the next statement to key —
  -- because the state entering that statement is the state here.
  | `(ublk| show $x:ident ; $rest:ublk) => do
    let mark ← occMark
    noteIdent rctx pctx x
    modify fun a =>
      if a.hover && a.occs.size > mark then
        { a with pendingOccs := a.pendingOccs.push mark, showOccs := a.showOccs.push mark }
      else a
    -- `resolveName` for its ERROR only: an unbound name must fail here as it
    -- would anywhere else. The resolved term is discarded — that is the erasure.
    let _ ← resolveName rctx pctx x
    elabUBlk rctx pctx next rest
  | `(ublk| $e:uterm ; $rest:ublk) => do
    let occLo ← occMark
    let (e', n1) ← elabUTerm rctx pctx next e
    spanOfStmt e' e
    tagOccsFrom occLo e'
    let (rest', n2) ← elabUBlk rctx pctx n1 rest
    return (← `(Dllbc.Term.seq $e' $rest'), n2)
  | `(ublk| $e:uterm) => do
    let occLo ← occMark
    let (e', n) ← elabUTerm rctx pctx next e
    -- The block's final expression. `stmtKeyOf` is applied in the emitted
    -- expression rather than mirrored by hand: a final `match` files under the
    -- same `matchE s eqn []` the walker computes, without this walker knowing
    -- that rule.
    spanOfStmt e' e
    -- This row did NOT tag occurrences until docs/18 §3, so anything named in a
    -- block's final expression fell back to binder granularity. A pre-existing
    -- hole in docs/17's surface, fixed here because a trailing `show` anchors to
    -- this statement and there is always one.
    tagOccsFrom occLo e'
    return (e', n)
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
    (scrut motive : TSyntax `uterm) (arms : Array (TSyntax `uelimArm)) : UM (TSyntax `term × Nat) := do
  let (scrutT, n1) ← elabUTerm rctx pctx next scrut
  let (motiveT, n2) ← elabUTerm rctx pctx n1 motive
  let motiveBare := match motive with | `(uterm| ($e:uterm)) => e | _ => motive
  let (mName, mTy, mBody) ← match motiveBare with
    | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => pure (x.getId.toString, τ, b)
    | _ => Macro.throwError "elim: motive must be a λ `(x : τ). …`"
  let armFor (c : String) : UM (Option (Array Ident × Option Ident × TSyntax `ublk)) := do
    for arm in arms do
      match arm with
      | `(uelimArm| $ctor:ident $[($bs:ident)]* $[$ih:ident]? => $body:ublk) =>
        if ctor.getId.toString == c then return some (bs, ih, body)
      | _ => pure ()
    return none
  let getArm (c : String) : UM (Array Ident × Option Ident × TSyntax `ublk) := do
    match ← armFor c with
    | some r => pure r
    | none => Macro.throwError s!"elim: missing arm for constructor '{c}'"
  let names := arms.filterMap (fun a => match a with
    | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $_:ublk) => some ctor.getId.toString
    | _ => none)
  -- `P ⟨target⟩`: the motive body with the motive's binder renamed to the arm's.
  let pOf (target : String) : UM (TSyntax `term) := do
    let b := (← elabUTerm rctx (mName :: pctx) n2 mBody).1
    `(Dllbc.Term.substP $(quote mName) (Dllbc.Term.pvar $(quote target)) $b)
  if names.contains "Z" || names.contains "S" then
    let (_, _, zb) ← getArm "Z"; let z := (← elabUBlk rctx pctx n2 zb).1
    let (sb, sih, sbody) ← getArm "S"
    let kName := (sb[0]!).getId.toString
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
    let hName := (cb[0]!).getId.toString
    let tName := (cb[1]!).getId.toString
    let ihName := (cih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf tName
    let body := (← elabUBlk rctx (ihName :: tName :: hName :: pctx) n2 cbody).1
    -- **The ELEMENT TYPE is read out of the motive's binder type**, exactly as the
    -- `Pair` branch below reads `A`/`B` out of `Σ (y : A). B`. It used to be the
    -- literal `Nat` in all three places this needs it — `listRec`'s `A` argument
    -- and the Cons arm's head and tail domains — which made the surface's list
    -- elim monomorphic at `List Nat` while `Machine`'s `listRec` rule (which
    -- takes `A` and builds `List A` from it) was general all along. An `elim` over
    -- a `List (Σ (k : Nat). Nat)` — a hashmap's bucket — checked only when the
    -- spine was written out by hand. (Ported from `hm-probe-opt` commit 6b5a724e;
    -- value-preserving for every existing call site, since a `List Nat` motive
    -- elaborates `Nat` to the same `Term.const "Nat"` the literal wrote.)
    let mTyBare := match mTy with | `(uterm| ($e:uterm)) => e | _ => mTy
    let (elemHd, elemArgs) := collectAppU mTyBare
    let elemSyn : Option (TSyntax `uterm) :=
      if elemArgs.size != 1 then none
      else match elemHd with
        | `(uterm| $x:ident) => if x.getId.toString == "List" then some elemArgs[0]! else none
        | _ => none
    let elemT ← match elemSyn with
      | some a => pure (← elabUTerm rctx pctx n2 a).1
      | none => `(Dllbc.Term.const "Nat")
    let hDom ← binderDom hName elemT
    let tDom ← binderDom tName (← `(Dllbc.Term.app (Dllbc.Term.const "List") $elemT))
    let ihDomM ← binderDom ihName ihDom
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "listRec") $elemT) $motiveT) $n)
        (Dllbc.Term.lam $(quote hName) $hDom
          (Dllbc.Term.lam $(quote tName) $tDom
            (Dllbc.Term.lam $(quote ihName) $ihDomM $body)))) $scrutT), n2)
  else if names.contains "Pair" then
    -- Σ elimination (§9). `sigmaRec` takes Σ's two parameters — the domain `A` and
    -- the FAMILY `λ x. B` — so the motive's binder type must be written as the Σ
    -- itself, `λ (p : Σ (x : A). B). goal`. Determined from what is written, never
    -- inferred: a wrong `A`/`B` fails at the use site like every other elim motive.
    -- No `ih`: Σ is not recursive, so the single arm binds exactly the two fields.
    let mTyBare := match mTy with | `(uterm| ($e:uterm)) => e | _ => mTy
    let (aSyn, bName, bSyn) ← match mTyBare with
      | `(uterm| Σ ($y:ident : $A:uterm). $B:uterm) => pure (A, y.getId.toString, B)
      -- **Σ0 elims by the SAME eliminator** (M33, §2.7's "no new eliminator"):
      -- `sigmaRec`'s second parameter is the type FAMILY `λ x. B`, and `⇝` is a
      -- mode marker rather than part of `B` — so a Σ0's family is the family its
      -- Σ twin has, and the row below is the whole of Σ0's elimination.
      | `(uterm| Σ0 ($y:ident : $A:uterm). $B:uterm) => pure (A, y.getId.toString, B)
      | _ => Macro.throwError "elim: a Pair motive's binder type must be written as `Σ (x : A). B` (or `Σ0 (x : A). B`)"
    let aT := (← elabUTerm rctx pctx n2 aSyn).1
    -- `B` under its own binder — correct for the family `λ x. B` as written, and
    -- renamed below for the arm's second binder domain, whatever the arm calls it.
    let bT := (← elabUTerm rctx (bName :: pctx) n2 bSyn).1
    let (pb, _, pbody) ← getArm "Pair"
    let xName := (pb[0]!).getId.toString
    let yName := (pb[1]!).getId.toString
    let body := (← elabUBlk rctx (yName :: xName :: pctx) n2 pbody).1
    -- `B` reaches the Σ's own binder, and the arm names that field itself — so the
    -- arm's second domain is `B` with the Σ binder renamed, the same move `pOf`
    -- makes for a recursor's `ih`.
    let xDom ← binderDom xName aT
    let yDom ← binderDom yName (← `(Dllbc.Term.substP $(quote bName) (Dllbc.Term.pvar $(quote xName)) $bT))
    -- The type FAMILY `λ x. B` is the Σ read back as a function, so its binder is
    -- the Σ's own binder and takes the Σ's own domain — marker included. Written
    -- unmarked, it was the one place a `Σ (Hu : A). B` and the family
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
    (scrut goal : TSyntax `uterm) (arms : Array (TSyntax `uelimArm)) : UM (TSyntax `term × Nat) := do
  let (scrutT, n1) ← elabUTerm rctx pctx next scrut
  let (goalT, n2) ← elabUTerm rctx pctx n1 goal
  let armBody (c : String) : UM (TSyntax `term) := do
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
