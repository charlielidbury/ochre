import Lean
import Dllbc.FnMacro

/-!
# `uterm` — THE term grammar

**ONE CATEGORY.** A term, a statement and a block are the same thing here, because
they are the same thing in the AST: `Term` is one type and `.seq : Term → Term →
Term` is one of its constructors. `ty{ }` (ProgMacro.lean) is a `uterm`,
elaborated in the empty context, and so is every body, arm and block. `fn` is a
STATEMENT (M28 θ), so a declaration is written where a `let` is written and there
is no separate declaration surface to learn.

`ublk` used to be a second category — "uterm plus sequencing" — and `ustmt` was
briefly a third between them. Both are gone; the merge was inward, and what holds
the layers apart now is PRECEDENCE, not category (see the `;` row's note).

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

  * the names of EARLIER telescope parameters are in scope, and resolve to
    `.var name` — ONE constructor for a pure binder and an Ω slot (docs/22):
    which it is, the term's scope says, where `reflectC` reads it. A parameter
    cited in a type is an Ω read of its snapshot (§5.2) because no pure binder
    of that name encloses the citation.
  * `*x` in type position → `.deref (.var "x")` — the comptime deref.

`&mut τ` (the borrow TYPE — the OPERATION is `&m e`, M29 β) is
`borrowT τ (weaken τ)` (the corpus's plain-borrow encoding; for the
closed telescope types in the corpus `weaken τ` computes to `τ`, so the produced
value is identical). `&mut (τ ~> τ')` gives a `τ'` that ignores the snapshot;
`&mut (s : τ ~> τ')` binds `s` as pure var 0 in `τ'` — the `borrowT`/`seedTelescope`
convention in Syntax.lean.

## Resolution discipline (och's law)

Every identifier resolves or errors: a binder in scope (pure, slot or `fn`)
→ `var`; known constructor → `ctorApp`; kernel const → `const`; a friendly
reified-function alias (`Le`, `Len`, `Add`, …) → its `…FnT` Term constant; else
the **Lean identifier** of that name, which must denote a `Dllbc.Term` in scope
(a library lemma like `SwapL` or `Set`) — the documented fallback. In
`prog_parse { }` the last step has one more rung: a name Lean does not know is
a free `var`, for the splice site to bind (docs/22 §5).

## Body

A function's body is a `uterm` with the telescope names pre-bound in
order at ids `0 .. n-1` and fresh binders minted from `n`, the `seedTelescope`
convention. That is the only place in the surface where a name arrives pre-bound.
Bodies laden with pure proof terms (a `botElim` ex-falso branch, a `LeRwRRaw` bound
derivation) can be spliced whole with `%term`, which is a `uterm` and therefore a
block's final expression — the escape hatch `decl{ … = %t }` used to provide,
available uniformly wherever an expression is.
-/

open Lean

namespace Dllbc

/-! ## The unified `uterm` grammar (§ phase-3 point 1 — ONE term grammar)

A single expression grammar spanning BOTH fragments, elaborated by one function
with no mode parameter. The flag it used to carry had exactly two readers, and
each was removed by giving the kernel the rule the surface had been standing in
for:

  * **`let`** (M29 α) emitted a `.letIn` in one mode and a β-redex over a fresh
    binder in the other. One row emits the `let` — since detach-tails as the
    spine `.seq (.letIn x e) rest` — and the kernel reads it under both arrows.
    (⇝'s reading was a β built at reflection when M29 α landed; since M32 R1 no
    redex is built anywhere — `Pure.eval` binds `Pure.letName x.id` in its
    environment and the `.seq` tail evaluates under it, see `Machine.lean`'s
    "`let` is read by β, and `eval` performs it" note.)
  * **`&mut`** (M29 β) was the borrow OPERATION in one mode and the borrow TYPE in
    the other. They are spelled `&m` and `&mut` now, so each row emits its own
    node whatever surrounds it.

Every form is therefore shared: application spines, λ/Π/Σ/→/Id/`Type`, `*e`, `Id`,
`let`, `&m`, `&mut`, `fn`, constructor/const/lemma references — and the statements
and the sequencer are rows of the same category, held apart from the expressions
by precedence alone.

**The one disambiguation rule (§ point 2):** `f(a, b)` — an identifier with a
**no-whitespace** paren argument list — is a runtime **call** (lowercase head) or
**ctorApp** (uppercase). Space-separated **juxtaposition** `f a b` (incl.
`f (a) b`) is **pure application** (`ctorApp` when the head is a known ctor). So
`Nth(&m *tl, k, p)` is a call, `botElim Unit p` and `LeRwRRaw (S x) y` are
application spines, `S(*l)` / `S *l` both mean `ctorApp "S" [*l]`. -/

-- **ONE CATEGORY FOR TERMS, STATEMENTS AND BLOCKS.** `Term` is one type and
-- `.seq : Term → Term → Term` is one of its constructors, so a statement is a
-- term, a block is a term, and the surface says so with one category. See the
-- precedence note at `;` below for the discipline that makes that safe. (`ublk`
-- and `ustmt` are gone. `ublk` was "uterm plus sequencing" — the merge is inward.)
declare_syntax_cat uterm
declare_syntax_cat uarm
-- **A PATTERN ARGUMENT** (M34 sugar (iii)) — a binder, or a constructor applied to
-- more of them. This category exists only for ARGUMENT position, and that is not
-- an oversight: at the head of an arm a bare identifier names a CONSTRUCTOR
-- (`Nil => …`), and in argument position the same identifier is a BINDER
-- (`Cons(h, t) => …`). One category cannot mean both, so `uarm` spells its head as
-- an `ident` and uses `upat` for what sits inside the parens. It is the one arm
-- category left: `uarmBody` and `uelimArm` are gone, and `upat` stays for this
-- reason, which is about MEANING rather than about shape.
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
-- `@name E` — a claim-site marker (docs/21), identity on `E`. LOOSE binding, the
-- λ-style prefix: the marker takes the MAXIMAL term to its right (application
-- spines, arrows — anything a level-10 parse absorbs), stopping only at a real
-- delimiter (`,` `)` `;` `{`), so `-> @claim Id Nat r (S Z) {` marks the whole
-- spine bare. `@name(E)` is the SAME row through ordinary grouping — the uterm
-- after the ident is `(E)` — so both spellings exist without a second row.
syntax:10 "@" noWs ident uterm:10 : uterm                    -- @name E — marker
-- ¶2.1's two new place steps. They bind TIGHTER than the peel, so a reborrow of a
-- range through a borrow is written `&m (*v)[lo ; cnt]` and `*v[i]` would mean
-- `*(v[i])` — peel the borrow stored AT slot `i`, which is how an `Array n (&mut T)`
-- is reached. `| h` cites the containment evidence (¶3.2's supply route 2); without
-- it the bound must compute (route 1). Offset-and-count, never lower-and-upper.
-- **EVERY OPERAND IS `uterm:6`, and that is load-bearing rather than tidy.** These
-- rows spell `;` as a LITERAL SEPARATOR, and since the categories merged `;` is
-- also the sequencer's token — so an operand parsed at the open level would take
-- `lo ; cnt` as one sequenced term, and `a[lo ; cnt]` would either misparse as
-- `a[seq(lo, cnt)]` through the single-operand row or go ambiguous between the
-- two. `:6` sits above the sequencer (1) and above the statement rows (5) and
-- below everything an index can actually be, so what these accept is unchanged.
syntax:max uterm:max noWs "[" uterm:6 "]" : uterm                         -- a[i]
syntax:max uterm:max noWs "[" uterm:6 "|" uterm:6 "]" : uterm             -- a[i | h]
syntax:max uterm:max noWs "[" uterm:6 ";" uterm:6 "]" : uterm             -- a[lo ; cnt]
syntax:max uterm:max noWs "[" uterm:6 ";" uterm:6 "|" uterm:6 "]" : uterm -- a[lo ; cnt | h]
-- `a[lo ; ..]` — to the end of the segment starting at `lo`. NAMES premise (3)'s
-- residue rather than computing `sub n lo`; without it ¶3.4's second borrow is
-- unwritable, since the doc spells it `[k ; rest]` and `rest` is a machine-minted σ.
syntax:max uterm:max noWs "[" uterm:6 ";" ".." "]" : uterm              -- a[lo ; ..]
-- ROUTE (a): `a[lo ; cnt ; rest | h]` SUPPLIES the residue's extent instead of letting
-- premise (3) mint a σ no binder can name. Same solution transition, still no `sub`;
-- omit it and the checker mints, exactly as before. Third instance of the house
-- pattern after `[k]` and `match h :` — an optional surface element reifying a fact
-- the checker already has, declared rather than inferred, free when absent.
syntax:max uterm:max noWs "[" uterm:6 ";" uterm:6 ";" uterm:6 "]" : uterm            -- a[lo ; cnt ; rest]
syntax:max uterm:max noWs "[" uterm:6 ";" uterm:6 ";" uterm:6 "|" uterm:6 "]" : uterm -- a[lo ; cnt ; rest | h]
-- …and the DECOMPOSITION CITATION. A supplied residue asserts a decomposition of the
-- leaf's extent; when that extent is a telescope parameter's σ, the assertion is a
-- constraint on the function's CALLERS, and premise (3) may not impose it by
-- unification (M7/M8's inferred constrained wire; M17's lesson that cross-boundary
-- constraints are DECLARED and checked). The program cites the equation and premise (3)
-- solves along it. Free when the decomposition already holds by conversion.
syntax:max uterm:max noWs "[" uterm:6 ";" uterm:6 ";" uterm:6 "|" uterm:6 "|" uterm:6 "]" : uterm
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
syntax ident ":" uterm:6 : ulamb
syntax:max "λ" "(" ulamb,* ")" "{" uterm "}" : uterm         -- an imperative λ
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
syntax:max "match" uterm:6 "{" uarm,* "}" : uterm            -- runtime match (§3)
syntax:max "match" ident ":" uterm:6 "{" uarm,* "}" : uterm  -- …with a branch equation (M23)
syntax:max "if" uterm:6 "{" uterm "}" "else" "{" uterm "}" : uterm  -- §12 sugar over a Bool match
syntax:max "if" ident ":" uterm:6 "{" uterm "}" "else" "{" uterm "}" : uterm  -- …with a branch equation

-- Pure eliminator sugar (§15b) — for `ty{}` / comptime positions. `elim`'s arms
-- are `uarm`s, the SAME arms a `match` takes: `uelimArm` is gone.
syntax:max "elim" uterm:max "return" uterm:max "{" uarm,* "}" : uterm
syntax:max "elim" uterm:max "generalizing" uterm:max "{" uarm,* "}" : uterm

/-! ### ONE ARM

    Two rows, differing only in whether the body is braced:

        syntax ident ("(" upat,* ")")* (ident)? "=>" "{" uterm "}" : uarm
        syntax ident ("(" upat,* ")")* (ident)? "=>" uterm : uarm

    **`uarmBody` AND `uelimArm` ARE BOTH GONE**, and the second is the interesting
    one. There were two arm notations in this grammar and they were two categories:

        Cons(h, t) => …          a `match` arm: the fields, comma-separated
        Cons (H) (T) R => …      an `elim` arm: a paren per field, then the IH

    The head is `ident`, then ANY NUMBER OF PAREN GROUPS, then an optional
    identifier. The groups are CONCATENATED, so `Cons(h, t)`, `Cons (h) (t)` and
    `Cons(h) (t)` are one arm written three ways — "a constructor's fields, however
    you choose to group the parens" is a coherent reading, and it is what lets both
    corpus notations keep parsing with nothing migrated. `Cons(H, T) R => …`, the
    spelling nobody could write before, is legal too.

    **The genuine difference between the two arm kinds is SEMANTIC and is now
    checked as one**: an `elim` arm binds an INDUCTION HYPOTHESIS and a `match` arm
    has nothing to bind one from, so a trailing identifier in a `match` is refused
    by `elabUArm` — with a message that can say what an `elim` is — rather than by
    the absence of a row. Conversely an `elim` arm's fields must be plain binders,
    so a nested pattern there is refused by `elimBinders`. A difference in meaning
    belongs to the elaborator; a second category was the surface guessing at it.

    **THE ARGUMENTS ARE PATTERNS** (M34 sugar (iii)). They used to be `ident,*`, so
    reading a field of a field cost an explicit inner match and a name for the
    intermediate; `Cons(Pair(k, v), tl) => …` is now written where it is meant.
    The rewrite is 1:1 with that hand-spelling and nothing cleverer — see
    `mintPatArgs`/`wrapPats`. DLLBC match stays ONE ARM PER HEAD CONSTRUCTOR:
    there is no cross-arm grouping and no pattern matrix, so `Cons(Z, tl)` is not
    a partial arm that some other arm completes — it is a one-branch inner match
    on the head's payload, and §9 refuses it as non-exhaustive.

    **TWO ROWS AND NOT ONE, because a general `{ uterm }` term row does not work.**
    That would have made the body just a `uterm` and left one arm row; it was built
    and it fails, for the reason a reader would guess and at a site they might not:
    `{ … }` at `:max` is a valid application ARGUMENT (`uterm:65 uterm:66`), and the
    first thing in this file that is a term followed by a brace is the `match` row's
    SCRUTINEE. `match x { Nil => … }` parses `x { Nil` as an application spine and
    then meets `,` — measured, and it does not merely mis-parse a program: it stops
    `Uni.lean` compiling, because `elabUTerm`'s own `match` quotation is the first
    casualty ("unexpected token ',*'; expected '}'"). Braces stay attached to the
    constructs that use them.

    **A BRACED body is a BLOCK and a bare one is ONE STATEMENT**, which is the only
    thing the two rows differ by and is not merely bracketing. A bare body is keyed
    as a single statement (docs/23) and must not let an enclosing `show`'s pending
    drain inside the arm (ShowSpans S6); a braced body goes to `elabUBlk` and each
    of its statements keys itself. Since the category merge a bare body could have
    been a `;` chain — nothing in the grammar stops it, the arm list's `,` would
    end it — and it is `elabArmBody` that sends such a body down the block route,
    so the distinction survives as a fact about what was written rather than as a
    restriction on what can be. -/
syntax ident ("(" upat,* ")")* (ident)? "=>" "{" uterm "}" : uarm
syntax ident ("(" upat,* ")")* (ident)? "=>" uterm : uarm
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
--
-- **`-> R` IS OPTIONAL, AND OMITTING IT OMITS THE SEAL.** `fn F (x : Nat) { x }`
-- is `let F = λ (x : Nat) { x }` and nothing else — a bare λ, unascribed. That is
-- not shorthand for an inferred signature; it is a different program, because the
-- SEAL is what makes a function opaque and what makes its body audited once, at
-- the declaration. Without one the λ is TRANSPARENT: it β-reduces at each call
-- site, the checker sees the body there, and so the body is checked once PER CALL
-- SITE — and an uncalled one is never checked at all. Verified against the
-- kernel: `let F = λ (x : Nat) { Bogus(x) }; ()` is ACCEPTED, and the same body
-- ascribed `Π (x : Nat) → Nat` is REJECTED with `call: unknown function 'Bogus'`.
--
-- That difference is a feature, not a hole, and it is already pinned as a rule:
-- Tests/Functions §C states the two callee readings — "body known, so unfold: a
-- literal λ callee β-reduces" against "body withheld, so only the type's
-- promise". An omitted `-> R` picks the first, deliberately, and a `fn` that
-- wants to be checked against a signature says so by writing one.
--
-- A `[k]` still requires a return type. §7 derives the recursor's motive from the
-- sealed Π with the scrutinee peeled off the front, so with nothing to seal there
-- is no motive to derive; the row below refuses that pairing by name, at Lean
-- elaboration, because it is decidable from the syntax alone.
--
-- **THE TAIL IS GONE FROM THE ROW.** `fn` was the first statement allowed to end
-- a block and for a while it carried its own `(";" ublk)?` to say so; the `;` row
-- below says it for every statement now, so there is nothing left here to write.
-- What `fn` still does with a tail it HAS — pass it through `bindFn` — happens in
-- the walker, and the walker's `fn` row is where that is argued.
--
-- (The row used to be `(name := ublkFn)`. It was named for a query that no longer
-- exists — `ElabCheck`'s information rule, "a `fn` carries its own `-> retType`,
-- so a block containing one carries its own specification and needs no
-- annotation" — and that reason had already lapsed twice: nothing asks the kind,
-- and with `-> R` optional the premise is not true of every `fn`. Nothing in the
-- tree referred to the name, so it went rather than being renamed for a category
-- that has since been deleted too.)
syntax:5 "fn" ident ("[" ident "]")? "(" ulamb,* ")" ("->" uterm:6)? "{" uterm "}" : uterm
-- **`uterm:6` ON THE RIGHT-HAND SIDE IS WHAT KEEPS THE `;` OUT OF IT.** At the open
-- level the sequencer (level 1) is a production the right-hand side would accept,
-- and `let x = a ; b` would bind `x` to `seq(a, b)` — silently, since that is a
-- term. `:6` sits above the sequencer and above the statement rows, so the
-- right-hand side is exactly the expression it was when `uterm` and `ublk` were
-- two categories; `let x = (let y = a ; y)` is how the other reading is written,
-- through the grouping row, which since the merge IS block-bracketing.
syntax:5 "let" ident "=" uterm:6 : uterm                     -- runtime let (→ letIn)
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
syntax:5 "let" ident noWs "(" upat,* ")" "=" uterm:6 : uterm
-- Both sides at `:6`, for the right-hand side's reason above and for the place's:
-- at the open level a place would try to extend itself through this very row.
syntax:5 uterm:6 ":=" uterm:6 : uterm                        -- assignment
-- (THE EXPRESSION-STATEMENT ROW IS GONE, and it did not need replacing. It read
-- `syntax uterm : ustmt` — a coercion whose only content was "an expression may
-- stand where a statement stands", which is a THEOREM of one category rather than
-- a rule to write down. `elabUBlk`'s fallthrough is where it lives now.)
-- **`show x` — a value made visible where you put it** (docs/18). ERASED: this
-- row emits `rest` and nothing else, so the kernel never learns the word and a
-- program with `show`s is the same `Term` as one without. What it leaves behind
-- is an info diagnostic carrying exactly what hovering `x` here would say.
--
-- `show` is already a Lean keyword, so declaring it as a leading atom reserves
-- no token that was not reserved — the question `ElabCheck`'s invariant note says
-- to ask before adding one.
syntax:5 "show" ident : uterm                                -- show (erased)

/-! ## THE ONE `;`

    One row, and it builds `.seq`:

        syntax:1 uterm:2 ";" uterm:1 : uterm

    **`uterm:2` ON THE LEFT IS WHAT MAKES A STATEMENT A STATEMENT.** The row sits
    at level 1, so a left operand demanded at level 2 cannot itself be a `;` node —
    the left of every `;` is exactly one statement, and the nesting goes right.
    That is the guarantee a separate `ustmt` category would have bought by
    duplication, bought here by precedence instead. `uterm:1` on the right admits
    another `;`, which is what makes the chain right-associative and gives
    `a ; b ; c` the shape `.seq a (.seq b c)` the kernel reads.

    **THE PRECEDENCE DISCIPLINE, since it is the whole risk of one category.**
    Three levels are reserved below everything that was here before (the lowest
    pre-existing level was 10, for `λ`/`Π`/`Σ`/`→`/`@`):

      * **1** — the sequencer.
      * **5** — the statements: `let`, `let C(…)`, `:=`, `show`, `fn`.
      * **6** — the threshold a position asks for when it must stay an EXPRESSION,
        i.e. must not swallow a `;` and must not admit a statement.

    Every site that embeds a term where a `;` could follow it, or that spells `;`
    itself, asks for `:6`: the two `let` right-hand sides, both sides of `:=`,
    `fn`'s `-> R`, the `match`/`if` scrutinee, and — the one that would have failed
    loudly — every operand of the `a[…]` index and range rows, which use `;` as a
    literal separator. Everything else stays at the open level and thereby BECOMES
    block-capable, which is the merge paying for itself: `( … )` grouping is now
    also block-bracketing, arm bodies and `{ … }` bodies take a statement chain
    with no row of their own saying so, and none of it took a new rule.

    **This is the AST's shape, and it stopped being the grammar's at
    detach-tails.** `Term.letIn x rhs tail` used to carry its own tail, so a `let`
    structurally WAS a binder over the rest of its block and a row that swallowed
    `";" ublk` was reading the node it built. Detach-tails split that into a
    tail-less `.letIn` and a `.seq` and made `.seq` the sole sequencer — but every
    statement row kept its hardcoded tail, so the surface went on spelling six
    sequencers for a kernel with one. Six `;`s, six recursions into `elabUBlk`,
    six places to get the scope threading right, and a seventh row (`uterm : ublk`)
    whose whole content was "the same thing, without a `;` after it".

    A block ending in a statement is a block whose value is `()` — a term of the
    calculus already rather than a shape the kernel had to be taught. `readR`
    returns `.ctor "unit" []` from a bare `.letIn` and from a bare `.assign`,
    `exploreD`'s final-expression arm reaches both through `readResult`,
    `Pure.eval` reads a bare `.letIn` on ⇝, and `stmtKeyOf` keys both (its
    `.letIn` arm; its catch-all for `.assign`, landing on the same key the seq'd
    form gets). Verified against the built kernel: `let v = 0; v := 1` checks and
    runs to `[(v, 1)]`, and `let x = 0` alone checks and runs to `[(x, 0)]`.

    **Three of the six statements own their continuation rather than being
    sequenced before it**, and the split is honest rather than hidden: `elabUBlk`
    hands the tail to `elabUStmt`, `seqStmt` is the one place a `.seq` is built
    from it, and the three rows that do not call `seqStmt` each argue at their own
    row why they cannot. `fn` passes the tail through `bindFn` (a rewrite of the
    tail, including an argument permutation the surface would otherwise skip),
    `let C(a, b) = e` moves the tail INSIDE a match arm (which is the whole of the
    sugar), and `show x` IS its tail (the row is erased). What the restructure
    buys is not that those three vanish — they are real — but that they are named
    as the exceptions to one rule instead of being six independent rules. -/
syntax:1 uterm:2 ";" uterm:1 : uterm

namespace Surface
open Lean

/-! ## Scope (docs/22 §5)

    ONE list of the names in scope, innermost first — what `rctx` (runtime
    locals and `fn` slots, at their ids) and `pctx` (pure binders) used to be
    as two. Under one `var` the emitted term is `.var name` whatever kind of
    binder the name resolved to; the kind is read only where the emitted term
    differs by it (a call on a slot head is an app spine, on a `fn` slot a
    `.call` for `retarget`; a match refuses a non-slot head; hovers file for
    slots). The walker mints nothing: a binder's identity is its name. -/

/-- One name in scope. -/
structure Scoped where
  name : String
  kind : BinderKind
  /-- For a `let`-bound slot, the key syntax of the statement that bound it —
      see `OccNote.bindKey`. -/
  key : Option Syntax := none
deriving Inhabited

abbrev Scope := List Scoped

/-- The innermost binding of a name, if any. -/
def Scope.find? (sc : Scope) (s : String) : Option Scoped := List.find? (·.name == s) sc

/-- Bind a pure (λ/Π/Σ) binder over a scope. -/
def pushPure (x : String) (sc : Scope) : Scope := ⟨x, .pure, none⟩ :: sc
/-- Bind an Ω slot — a parameter, a `let` (with its statement key), a pattern
    binder — over a scope. -/
def pushSlot (x : String) (sc : Scope) (key : Option Syntax := none) : Scope :=
  ⟨x, .slot, key⟩ :: sc

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
def patName (n : Nat) : String := "§p" ++ toString n


-- (`shadowedName` and `idxOf?` were deleted in M30 step 2. The first existed so
-- that a `let` shadowing a pure binder could occupy that binder's `pctx` slot —
-- every de Bruijn INDEX below it had to keep its level — while being unwritable as
-- source. Under names there is no level to keep, so the shadowed binder is simply
-- dropped from the scope, which is what the mask was simulating. The second was the
-- index lookup itself: `pctx` is now a set of names in scope and the question asked
-- of it is membership.)

/-- Build the `Term` syntax for the numeral `k`: ONE node, `Dllbc.Term.nat k`,
    which IS the `S (S (… Z))` chain by definition (`Term.nat` unfolds to
    `ctorApp "S" [… ctorApp "Z" []]`, so the emitted `Term` is unchanged).

    It used to emit the chain as k nested `ctorApp` syntax nodes. That made a
    surface numeral cost k in elaboration depth: `ty{ 1056 }` hit
    `maxRecDepth` at the default 512 and only elaborated with the limit raised,
    which is why the corpus spliced large dividends as `%(Term.nat k)` instead
    of writing them (EagerRec's `modOf`, HashMap's keys). That reason is gone;
    the `%` splice remains only where `k` is a Lean parameter. -/
def buildNat (k : Nat) : MacroM (TSyntax `term) :=
  `(Dllbc.Term.nat $(Syntax.mkNumLit (toString k)))

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
abbrev PendingPat := String × Ident × List (TSyntax `upat)

/-! ## The span side channel

The walker holds each statement's and each argument's `TSyntax` — that is where
`Macro.throwErrorAt` already gets its spans — so while it builds the term it also
accumulates, on the side, a **key term ↦ source syntax** table. `Term` and `Val`
are untouched by a single byte; the positions ride alongside the value, not
inside it.

The key is the term itself, in `stmtKeyOf` normal form, rather than a path.
A statement inside a match arm (or a terminal match's arms) is still walked
once per path, and single-path walks rebuild the arm seam lazily
(`pushJoinArms`), so a statement's *position* in the walked term is not its
position in the source — while its *term* is the same term in every copy.
Matching on the term is invariant under all of that for free, and needs no
second implementation of the walk
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
  name : String
  stmt : Option Syntax := none
  /-- The statement key of the `let` this occurrence resolved to, when it
      resolved to one (docs/22 §3 item 2): what lets the binder-granularity
      fallback join an occurrence to ITS binder under shadowing, rather than to
      whichever `let` of that name was filed first. `none` for a parameter, a
      pattern binder, a `fn` slot — those have no `let` note to join to. -/
  bindKey : Option Syntax := none
  /-- An ENTRY occurrence — a telescope position: a parameter binder, an
      occurrence inside a parameter's type, or the return type. Its point is
      "entering the body" — the state at the END of `stmt`'s seeding run —
      rather than "entering `stmt`", so the join reads it through
      `factsAtEntry` instead of `factsAt`. This replaced the static annotation
      channel (`static?`, deleted 2026-08-21): under strong updates nothing
      about a slot is timeless, so a parameter answers from the checker's own
      seeds like every other binder. -/
  entry : Bool := false
  /-- A SECOND, coarser point this occurrence may fall back to (docs/23): the
      key of the enclosing match, for an occurrence that already has a statement
      of its own.

      **It exists because a bare arm body is two points at once**, and the two
      answer through different doors. `Cons(hd, tl) => IdJ(tl)` is a statement —
      the machine files deltas under its key — so `tl` wants `factsAt` there. But
      the machine's key for that statement is the term it WALKS, which a call
      retarget or the `[k]` recursor rewrite can make a different term from the
      one the surface emitted; when the two disagree, `factsAt` finds no run and
      the arm's own seed is still the honest coarser answer. So the tail key is
      tried first and this is what is left when it misses.

      `none` for everything the match row tags outright — a pattern binder has no
      statement of its own, so its entry key IS its `stmt`. -/
  entryKey : Option Syntax := none
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
      work in `prog_parse { }` too. -/
  hovers : Array (Syntax × String) := #[]
  /-- Spans whose tooltip only the CHECKER knows: an occurrence of a runtime
      binding, joined against the checker's tables by id AND name — and, for
      point hovers (docs/17), by the STATEMENT it occurs in. -/
  occs : Array OccNote := #[]
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
  /-- `fn` name ↦ the declaration-order index of its `[k]` scrutinee (docs/20
      stage 3). Filed UNGATED — behind neither `collect` nor `hover` — because
      it is not diagnostic: a module block persists it (`Ledgers.hints`), and a
      seeded consumer's call to the fn is permuted against the hoisted
      telescope by exactly this entry. The cost is one push per hinted
      declaration; the plain `prog{ }` forms simply never read it. Filed in
      elaboration order, so a nested `fn` files before the declaration
      enclosing it; `elabModule` keeps only names that survive to the module's
      ending Ω, which drops body-local declarations (their binding dies with
      the sealed body). -/
  fnHints : Array (String × Nat) := #[]
  /-- The `§pN` supply (`freshPat`). -/
  fresh : Nat := 0
  /-- **Och's law, switched off** (docs/22 §5): this is a `prog_parse { }`
      block, and a name that resolves to nothing is emitted as `.var name` for
      the splice site to bind, instead of as the Lean identifier that makes it an
      error. One reader — `resolveName`'s final fallthrough (and `elabScrut`'s,
      for a scrutinee) — and it turns an ERROR into a term: no source `prog{ }`
      accepts elaborates differently under it. -/
  parse : Bool := false
deriving Inhabited

/-- The surface walker's monad: `MacroM` plus the span side channel. -/
abbrev UM := StateT SpanAcc MacroM

/-- The fresh-name supply for `patName` (docs/22 §3 item 4): the one thing the
    walker still counts, because sibling nested patterns must bind DISTINCT
    reserved names. Per block; a spliced fragment's `§p0` cannot be live at the
    same time as the host's (`patName`'s own argument: the header reads the slot
    before any arm body — where a fragment can land — runs). -/
def freshPat : UM String := do
  let a ← get
  set { a with fresh := a.fresh + 1 }
  return patName a.fresh

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
def noteOcc (ref : Syntax) (name : String) (bindKey : Option Syntax := none) : UM Unit :=
  modify fun a =>
    if a.hover then { a with occs := a.occs.push { ref, name, bindKey } } else a

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

/-- Tag every occurrence filed since `lo` as an ENTRY occurrence of the body
    keyed `key` — telescope positions: parameter binders, occurrences inside
    parameter types, and the return type (see `OccNote.entry`). Pending
    occurrences are NOT drained: a `show` above a `fn` statement anchors to a
    statement, not to a body's inside.

    An occurrence that ALREADY has a statement keeps it and takes this key as its
    FALLBACK (`OccNote.entryKey`, docs/23) rather than being passed over. That is
    the whole of the arm-tail fix's safety: the tail row's key is more specific
    and is tried first, and where the machine files under a term the surface
    cannot reproduce — a retargeted call, the `[k]` recursor's `Ih` — the arm's
    own seed still answers, exactly as it did before the tail row existed. -/
def tagOccsEntry (lo : Nat) (key : TSyntax `term) : UM Unit :=
  modify fun a =>
    if !a.hover then a else
      { a with occs := a.occs.mapIdx (fun i o =>
          if i ≥ lo then
            if o.stmt.isNone then { o with stmt := some key.raw, entry := true }
            else if o.entryKey.isNone && !o.entry then { o with entryKey := some key.raw }
            else o
          else o) }

/-- Steal the pending `show` occurrences for the duration of a statement's own
    elaboration. **The drain is depth-blind and this is the correction**: a
    nested block inside the statement's parts (a match arm, an fn body) files
    and drains its OWN pendings through the same accumulator, so without the
    steal, an outer `show` is keyed by the first statement INSIDE the nested
    block — the state one arm deep, presented as the state here. Found live: a
    `show` above a statement-position match answered with the Cons arm's
    suspension. Every row that elaborates sub-terms before its `tagOccsFrom`
    steals first and restores just before tagging. -/
def takePendings : UM (Array Nat) := do
  let a ← get
  set { a with pendingOccs := (#[] : Array Nat) }
  return a.pendingOccs

/-- Put stolen pendings back, immediately before the stealing row's own
    `tagOccsFrom` — they drain there, at the depth they were filed. -/
def restorePendings (held : Array Nat) : UM Unit :=
  modify fun a => { a with pendingOccs := a.pendingOccs ++ held }

/-- Render a binder's tooltip. One place, so a binder and its occurrences cannot
    drift into two spellings. -/
def hoverText (name : String) (ty : String) : String := s!"**{name} : `{ty}`**"

/-- Run `act` with extra callee signatures in scope, and put the scope back
    afterwards.

    Save-and-restore on the accumulator rather than a new argument threaded
    through the walker: `fsigs` is lexically scoped, the walker is a 30-call
    mutual block, and the port's standing rule is to ride existing walker state
    rather than add a layer. The restore is skipped on the throwing path, which
    costs nothing — a block that failed to elaborate has no tooltips. -/
def withHoverScope {α : Type} (fs : List (String × String)) (act : UM α) : UM α := do
  let a ← get
  if !a.hover then act else do
    modify fun a => { a with fsigs := fs ++ a.fsigs }
    let r ← act
    modify fun a' => { a' with fsigs := a.fsigs }
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

/-- A `let` statement's key: its binder AND its right-hand side (docs/22 §4) —
    the shape `assign`'s key already has. The id that made the binder alone
    unique is gone; two `let x = e` with the same `e` are the same statement
    written twice, which the span lookup already reports as such. -/
def letKey (name : String) (rhs : TSyntax `term) : MacroM (TSyntax `term) :=
  `(Dllbc.Term.letIn (Dllbc.Var.slot $(quote name)) $rhs)

/-- File a `let` statement under its key. -/
def spanOfLet (key : TSyntax `term) (ref : Syntax) : UM Unit := noteStmtSpan key ref

/-- A `fn` statement's key: its binder alone. Every `fn` binder is a `decl`, so
    the NAME is what distinguishes one from another here — which is exactly
    what `Ω` resolves by. -/
def fnKey (name : String) : MacroM (TSyntax `term) :=
  `(Dllbc.Term.letIn (Dllbc.Var.decl $(quote name)) Dllbc.Term.unit)

/-- File a `fn` statement. -/
def spanOfFn (name : String) (ref : Syntax) : UM Unit := do
  noteStmtSpan (← fnKey name) ref

/-- File an assignment under its place and right-hand side. -/
def spanOfAssign (place rhs : TSyntax `term) (ref : Syntax) : UM Unit := do
  noteStmtSpan (← `(Dllbc.Term.assign $place $rhs)) ref

/-- File each of a call's arguments under its own span. -/
def spanOfArgs (keys : Array (TSyntax `term)) (refs : Array Syntax) : UM Unit :=
  (keys.zip refs).forM fun kr => noteArgSpan kr.1 kr.2

/-- **A key follows its term through `bindFn`.** The `fn` row emits
    `bindFn slot dec rest`, and `retarget` rewrites every `f(…)` in `rest` — a
    `.call` becomes an app spine on the binding, arguments permuted to the
    callee's hoist — so the term the WALKER notes as its breadcrumb is the
    retargeted one. A key filed from the surface syntax is the pre-retarget term,
    and the two differ exactly where a statement keyed by its own term (an
    expression statement, a body's final expression, an assignment's right-hand
    side, a call argument) mentions a sibling `fn`. That mismatch is what sent the
    pure reader's refusals to the "span-table gap" fallback.

    So every key filed while `rest` was elaborated is wrapped in the SAME
    `bindFn` the term goes through, and nothing is mirrored by hand: `bindFn`
    applied statement-wise is `bindFn` applied to the block, because `retarget`
    is structural. `let`/`fn` keys are binders and pass through unchanged. -/
def rekeySpansFrom (stmtLo argLo : Nat) (slot decT : TSyntax `term) : UM Unit := do
  let a ← get
  if !a.collect then return
  let wrap (k : Syntax) : UM Syntax := do
    let k' : TSyntax `term := ⟨k⟩
    return (← `(Dllbc.FnMacro.bindFn $slot $decT $k')).raw
  let mut stmts := a.stmts
  for i in [stmtLo : stmts.size] do
    let (k, r) := stmts[i]!
    stmts := stmts.set! i ((← wrap k), r)
  let mut args := a.args
  for i in [argLo : args.size] do
    let (k, r) := args[i]!
    args := args.set! i ((← wrap k), r)
  modify fun a => { a with stmts, args }

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

/-- One arm, taken apart, whichever of the two notations it was written in.

    The head constructor; its field patterns, with EVERY PAREN GROUP CONCATENATED,
    so `Cons(h, t)`, `Cons (h) (t)` and `Cons(h) (t)` come back the same; the
    trailing identifier, which is an `elim` arm's induction hypothesis and a
    `match` arm's error; the body; and whether the body was BRACED, which decides
    block-or-statement and nothing else.

    One reader for both arm kinds is the point: what used to be two grammar
    categories is one shape here, and the two differences that are real —
    the IH, and whether a field may be a nested pattern — are asked about
    downstream by the elaborator that cares. -/
def armParts (arm : TSyntax `uarm) :
    MacroM (Ident × List (TSyntax `upat) × Option Ident × TSyntax `uterm × Bool) := do
  match arm with
  | `(uarm| $c:ident $[($ps,*)]* $[$ih:ident]? => { $b:uterm }) =>
    pure (c, (ps.toList.flatMap (fun g => g.getElems.toList)), ih, b, true)
  | `(uarm| $c:ident $[($ps,*)]* $[$ih:ident]? => $b:uterm) =>
    pure (c, (ps.toList.flatMap (fun g => g.getElems.toList)), ih, b, false)
  | _ => Macro.throwErrorAt arm "decl: unexpected arm"

/-- An `elim` arm's field binders. A recursor's arm binds PLAIN NAMES — its
    domains come from the recursor scheme, so there is nothing for a nested
    pattern to be matched against — and refusing one here is the elaborator-level
    half of what a separate `uelimArm` category used to do by not having a row for
    it. The message names the fix, which the missing row could not. -/
def elimBinders (c : Ident) (ps : List (TSyntax `upat)) : MacroM (Array Ident) := do
  let mut out := #[]
  for p in ps do
    match p with
    | `(upat| $x:ident) => out := out.push x
    | _ => Macro.throwErrorAt p s!"elim: '{c.getId}' binds a nested pattern here, and a recursor's arm binds plain names — its binder types come from the recursor scheme, so there is nothing for a pattern to be matched against. Bind a name and `match` on it inside the arm."
  return out

/-- Bind one row of pattern arguments, extending the scope and returning the
    extended scope, the argument `Var` syntaxes (in order) and the nested
    arguments deferred to `wrapPats`.

    A nested argument takes a slot like any other and puts NOTHING into scope:
    its name is reserved and FRESH (`freshPat`), so no source can refer to it,
    and the only reader it will ever have is the `.matchE` header `wrapPats`
    builds from the name returned here. -/
partial def mintPatArgs (sc : Scope) :
    List (TSyntax `upat) →
    UM (Scope × Array (TSyntax `term) × List PendingPat)
  | [] => pure (sc, #[], [])
  | p :: ps => do
    -- The identifier comes back from `upatParts` and is not read off `p` directly:
    -- `upat`'s binder row WRAPS its ident in a node of its own, so `⟨p.raw⟩` is a
    -- `upat` wearing an `Ident`'s type and `getId` answers the anonymous name for
    -- it — a binder called "" that nothing can refer to, which is a silent
    -- unbound-variable error at every use site rather than a type error here.
    match ← liftM (upatParts p) with
    | (x, none) => do
      liftM (checkBinder x)
      let name := x.getId.toString
      -- The binder IS an occurrence (docs/17): filed here, and entry-tagged by
      -- the enclosing match/let-pattern row with that match's key — arm-entry
      -- binds file under it, so `replayEntry` answers with this arm's own seed,
      -- per path.
      noteOcc x.raw name
      let v ← `(Dllbc.Var.slot $(quote name))
      let (sc', vs, pend) ← mintPatArgs (pushSlot name sc) ps
      pure (sc', #[v] ++ vs, pend)
    | (c, some args) => do
      let nm ← freshPat
      let v ← `(Dllbc.Var.slot $(quote nm))
      let (sc', vs, pend) ← mintPatArgs sc ps
      pure (sc', #[v] ++ vs, (nm, c, args) :: pend)

/-- Wrap `body` in the deferred nested matches, outermost first. `body` is a
    continuation rather than a syntax tree because the two rows that call this
    disagree about what a body IS — an arm's is its own syntax, braced or bare
    (`elabArmBody`), and the `let` pattern's is the REST OF THE BLOCK — and they
    agree about everything else. -/
partial def wrapPats (sc : Scope) (pend : List PendingPat)
    (body : Scope → UM (TSyntax `term)) :
    UM (TSyntax `term) := do
  match pend with
  | [] => body sc
  | (nm, c, args) :: rest => do
    let occLo ← occMark
    let (sc', vars, pend') ← mintPatArgs sc args
    -- A nested pattern's binders belong to the GENERATED inner match, whose key
    -- this row is about to build — tagged here, before the outer row's sweep
    -- can hand them the outer key.
    tagOccsEntry occLo (← `(Dllbc.Term.matchE $(quote nm) none []))
    let inner ← wrapPats sc' (pend' ++ rest) body
    return (← `(Dllbc.Term.matchE $(quote nm) none
      [Dllbc.Branch.mk $(quote c.getId.toString) [$vars,*] $inner]))

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

/-! ## Locals and `fn` slots in one scope (M31 Stage A; one list since docs/22)

    A `fn` statement's name goes into scope alongside the ordinary runtime
    locals, because §2.1 makes a function an ordinary comptime BINDING and a
    binding is something a bare name may denote (`let F = Main`). They are told
    apart by the binder's KIND (`BinderKind.decl`, what the `declSlot` tag was),
    and two rows want the LOCALS only:

      * `f(a, b)` must keep falling through to `.call`, whose rewrite into the
        app SPINE is `retarget`'s — and `retarget` also PERMUTES the arguments of
        a `[k]`-hoisted callee (E8). Resolving the name here instead would build
        the spine in declaration order against a telescope that has been
        reordered, which is silent: it passes a borrow where a `Nat` is expected,
        and it was found once already, by a migration disagreement list rather
        than by a test.
      * `match x { … }` wants a runtime scrutinee, and a function is not one. -/

/-- An ordinary runtime local — a `fn` slot is not one, and nor is a pure binder. -/
def isLocal (sc : Scope) (s : String) : Bool :=
  match sc.find? s with
  | some e => e.kind == .slot
  | none => false

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
def isFnSlot (sc : Scope) (s : String) : Bool :=
  match sc.find? s with
  | some e => e.kind == .decl
  | none => false

/-- **The L-suffix condition, checked** (M32 R1).

    A `fn` slot wins over the raw-Lean fallthrough, so a `fn` whose name spells a
    library lemma makes that lemma unreachable in every block the `fn` is
    above — silently, since both readings are well-typed. Under M32's name-keyed Ω
    the same spelling additionally resolves the same STORE entry, so what was a
    surface-level shadowing is now a store-level one too, and a convention nobody
    checks is the wrong size of guarantee for it.

    The test is asked of the collision family the convention is about — a
    `Dllbc.StdChainRaw` definition of that exact name — rather than of any Lean
    global, because "is this identifier bound somewhere in Lean" answers yes for
    reasons that have nothing to do with the corpus (a `List` combinator, an
    opened namespace) and would refuse `fn` names that shadow nothing anyone can
    write here. The fix named in the message is the one the corpus already took
    twice: the LEMMA takes the suffix, because the function is the user-facing
    name (Stage C addendum item 2).

    The family is the chain's raw-term namespace: 110 `XRaw` proof terms and the
    25 spec formers, which is every name a block below a `fn` could want to cite
    from the library by the Lean fallthrough. -/
def lemmaShadowCheckAt (ref : Syntax) (s : String) : MacroM Unit := do
  let cands ← Macro.resolveGlobalName (`Dllbc.StdChainRaw ++ Name.mkSimple s)
  if !cands.isEmpty then
    Macro.throwErrorAt ref s!"fn: '{s}' shadows the library lemma `Dllbc.StdChainRaw.{s}`. A `fn` slot is resolved before the raw-Lean fallthrough, so no block below this declaration can name the lemma, and under M32's name-keyed Ω the two spellings resolve one store entry. Give the LEMMA the `L` suffix ({s} → {s}L) — the function is the user-facing name and does not move."

/-- **The Lean fallthrough, asked at elaboration** (docs/22 §5). `prog{ }`'s
    last resort for a name is the Lean identifier of that name, which must
    denote a `Dllbc.Term` in scope — a library lemma, or a Lean local of the
    enclosing `def`. A `prog_parse { }` block wants the SAME resort and one more
    below it: a name Lean does not know either is `.var name`, free, for the
    splice site to bind.

    Whether Lean knows a name is not a question a `MacroM` can answer — it sees
    globals (`resolveGlobalName`) and not the local context — so the walker
    emits this and the answer is given here, by a term elaborator with the full
    scope in hand. Known-or-not and nothing more: an ambiguous global (`Append`
    the Lean class against `StdChainRaw.Append`) is for `elabTerm`'s overload
    resolution against the expected type, exactly as the bare identifier always
    was. A dotted name is never a DLLBC binder, so it is elaborated as Lean
    would without asking. -/
syntax (name := identOrFree) "ident_or_free%" ident : term

open Lean.Elab Lean.Elab.Term in
elab_rules : term
  | `(ident_or_free% $x:ident) => do
    let termTy := Lean.mkConst ``Dllbc.Term
    let known := !x.getId.isAtomic
      || ((← getLCtx).findFromUserName? x.getId).isSome
      || !(← resolveGlobalName x.getId).isEmpty
    if known then elabTerm x (some termTy)
    else return mkApp (Lean.mkConst ``Dllbc.Term.var) (mkStrLit x.getId.toString)

/-- Resolve a bare identifier. A binder in scope — pure, slot or `fn` — is
    `.var` at that name (ONE constructor, docs/22; which it is, the term's
    scope says); a constructor → nullary `ctorApp`; a kernel const → `const`;
    a reified-function alias → its `…FnT` Term; else the Lean identifier of that
    name (a `Term` in scope) — or, in a `prog_parse { }` block (`parse`), that
    identifier if Lean knows it and a free `.var` otherwise (`ident_or_free%`).

    A binder shadows the table, as it always did (`pctx`-first, then `rctx`,
    before the constructor and constant tables): `λ (k : Nat). k` is the binder
    and not the `Id` eliminator. **The tables are resolved HERE, in parse mode
    too** — a name that is a constructor, a constant or an alias is that,
    whatever the splice site binds. Deferring the lowercase constants to the
    splice was tried and is recorded in docs/22 §7.1: every library proof is
    spliced somewhere, and `IdCongrRaw`'s `j A X …` was captured by a chain
    `fn`'s parameter named `j`. The cost is stated there: a fragment cannot
    cite a splice-site binder named `j`, `k`, `natRec`, …. -/
def resolveName (parse : Bool) (sc : Scope) (x : Ident) : MacroM (TSyntax `term) := do
  let s := x.getId.toString
  if (sc.find? s).isSome then `(Dllbc.Term.var $(quote s))
  else if ctorSet.contains s then `(Dllbc.Term.ctorApp $(quote s) [])
  else if constSet.contains s then `(Dllbc.Term.const $(quote s))
  else match aliasMap.lookup s with
    | some n => pure ⟨(mkIdent n).raw⟩
    | none => if parse then `(ident_or_free% $x) else pure ⟨x.raw⟩

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
def noteIdent (sc : Scope) (x : Ident) : UM Unit := do
  let a ← get
  if !a.hover then return
  let s := x.getId.toString
  match sc.find? s with
  | some ⟨_, .pure, _⟩ => return
  | some ⟨_, .slot, key⟩ => noteOcc x.raw s key
  | some ⟨_, .decl, _⟩ =>
    match a.fsigs.lookup s with
    | some sig => noteHover x.raw (hoverText s sig)
    | none => noteOcc x.raw s
  | none => pure ()

/-! ## Unified `uterm` elaborators (§ points 1–3)

A binder's identity is its NAME (docs/22): a `let`, a match's arm binders, a
runtime λ's telescope and a pure λ/Π/Σ binder all push their name onto the one
scope list, innermost first, and an occurrence is `.var name` whichever kind of
binder it resolved to. The walker mints nothing except the reserved `§pN`
names for nested patterns (`freshPat`). (The runtime-body grammar this replaced
minted a globally-unique id per binder; M32 R1 made Ω resolve by name and the
id was decoration from then on.) -/

/-- Put a matched expression's `let` back around the match, or nothing at all when
    the scrutinee was already a place (M34). The two match rows and the
    `let C(…) = …` row all end this way, and each of them owes the SAME identity
    on the plain-variable path — so the wrapping is written once. -/
def wrapScrut (scrut : TSyntax `term) (pre? : Option (TSyntax `term))
    (body : TSyntax `term) : MacroM (TSyntax `term) :=
  match pre? with
  | none => pure body
  | some e => `(Dllbc.Term.seq (Dllbc.Term.letIn $scrut $e) $body)

partial def collectAppU : TSyntax `uterm → TSyntax `uterm × Array (TSyntax `uterm)
  | `(uterm| $f:uterm $a:uterm) => let (h, as) := collectAppU f; (h, as.push a)
  | t => (t, #[])

mutual

partial def elabUTerm (sc : Scope)
    (stx : TSyntax `uterm) : UM (TSyntax `term) := do
  match stx with
  | `(uterm| ()) => return (← `(Dllbc.Term.unit))
  -- **`( … )` IS BLOCK-BRACKETING AS WELL AS GROUPING**, for free and with no row
  -- of its own: since the categories merged, an interior that SEQUENCES is a
  -- block, so `let x = (let y = a ; y)` is how a nested block is written.
  --
  -- Only a `;` interior takes that route, and the asymmetry is deliberate rather
  -- than lazy: `elabUBlk`'s fallthrough files a STATEMENT span and keys the
  -- occurrences under it, which is right for a statement and wrong for a
  -- parenthesised sub-expression — the machine files no deltas under `(f x)`, so
  -- keying `f` and `x` there would take away answers they get today from the
  -- enclosing statement.
  | `(uterm| ($e:uterm)) =>
    match e with
    | `(uterm| $_:uterm ; $_:uterm) => elabUBlk sc e
    | _ => elabUTerm sc e
  | `(uterm| Type) => return (← `(Dllbc.Term.type))
  | `(uterm| % $e:term) => return (← `(($e : Dllbc.Term)))
  | `(uterm| @$nm:ident $e:uterm) => do
    -- The marker row wraps and nothing else: occurrences inside `E` file as
    -- normal (spans, hovers), and the node is stripped at the program boundary.
    -- Parse mode included — a fragment may carry markers, and they mean their
    -- bodies wherever the fragment lands.
    --
    -- ONE name is REFUSED, loudly: `@res` is the kernel form of `*res`, and a
    -- marker named `res` would parse under this row and then silently mean its
    -- body's CURRENT value instead of the exit payload. `@old` needs no guard
    -- here — `old` is a KEYWORD of this grammar (the `old *v` row), so the
    -- parser itself refuses it as the row's ident; verified, not assumed
    -- (Tests/MarkedTwins pins both refusals as they actually read).
    let s := nm.getId.toString
    if s == "res" then
      Macro.throwErrorAt nm s!"'@res' cannot be a marker name: it collides with the kernel spelling `@res(…)` (the exit payload, written `*res`), and a marker named 'res' would silently mean its body's CURRENT value instead. Pick another name."
    let e' ← elabUTerm sc e
    return (← `(Dllbc.Term.marker $(quote s) $e'))
  | `(uterm| $n:num) => return (← buildNat n.getNat)
  | `(uterm| old * $e:uterm) => do
    -- §5.4 `old *v`: the ENTRY snapshot, sugar over the telescope's existing
    -- payload snapshot. Elaborates to `@old(*v)`; `markExit` strips the marker to
    -- a plain `*v` read at seed (entry), so it never reaches the kernel.
    let e' ← elabUTerm sc e
    return (← `(Dllbc.Term.app (Dllbc.Term.const "old") (Dllbc.Term.deref $e')))
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
      return (← `(Dllbc.Term.app (Dllbc.Term.const "@res") (Dllbc.Term.ctorApp "Z" [])))
    | _ =>
    let e' ← elabUTerm sc e
    return (← `(Dllbc.Term.deref $e'))
  | `(uterm| $a:uterm[$i:uterm]) => do
    let a' ← elabUTerm sc a
    let i' ← elabUTerm sc i
    return (← `(Dllbc.Term.index $a' $i' none))
  | `(uterm| $a:uterm[$i:uterm | $h:uterm]) => do
    let a' ← elabUTerm sc a
    let i' ← elabUTerm sc i
    let h' ← elabUTerm sc h
    return (← `(Dllbc.Term.index $a' $i' (some $h')))
  | `(uterm| $a:uterm[$lo:uterm ; ..]) => do
    let a' ← elabUTerm sc a
    let lo' ← elabUTerm sc lo
    return (← `(Dllbc.Term.range $a' $lo' none none none none))
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm]) => do
    let a' ← elabUTerm sc a
    let lo' ← elabUTerm sc lo
    let c' ← elabUTerm sc c
    let r' ← elabUTerm sc r
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') none none))
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm | $h:uterm]) => do
    let a' ← elabUTerm sc a
    let lo' ← elabUTerm sc lo
    let c' ← elabUTerm sc c
    let r' ← elabUTerm sc r
    let h' ← elabUTerm sc h
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') (some $h') none))
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm | $h:uterm | $q:uterm]) => do
    let a' ← elabUTerm sc a
    let lo' ← elabUTerm sc lo
    let c' ← elabUTerm sc c
    let r' ← elabUTerm sc r
    let h' ← elabUTerm sc h
    let q' ← elabUTerm sc q
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') (some $h') (some $q')))
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm]) => do
    let a' ← elabUTerm sc a
    let lo' ← elabUTerm sc lo
    let c' ← elabUTerm sc c
    return (← `(Dllbc.Term.range $a' $lo' (some $c') none none none))
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm | $h:uterm]) => do
    let a' ← elabUTerm sc a
    let lo' ← elabUTerm sc lo
    let c' ← elabUTerm sc c
    let h' ← elabUTerm sc h
    return (← `(Dllbc.Term.range $a' $lo' (some $c') none (some $h') none))
  | `(uterm| &mut ( $x:ident : $τ:uterm ~> $s:uterm )) => do     -- borrow type, snapshot binder
    let τ' ← elabUTerm sc τ
    let s' ← elabUTerm (pushPure x.getId.toString sc) s
    return (← `(Dllbc.Term.borrowT $(quote (x.getId.toString)) $τ' $s'))
  -- The two spellings whose snapshot binder is UNUSED get a reserved name, and no
  -- weakening: `shiftPure 1 0` used to sit on both of these lines and is the
  -- identity under names (M30 step 2). `trivialOwedT` reads the second shape and
  -- was simplified with them.
  | `(uterm| &mut ( $τ:uterm ~> $s:uterm )) => do                -- borrow type, owed type ignores s
    let τ' ← elabUTerm sc τ
    let s' ← elabUTerm sc s
    return (← `(Dllbc.Term.borrowT $(quote unusedSnapName) $τ' $s'))
  | `(uterm| &mut $e:uterm) => do                                -- the borrow TYPE, in any position
    let e' ← elabUTerm sc e
    return (← `(Dllbc.Term.borrowT $(quote unusedSnapName) $e' $e'))
  | `(uterm| &m $e:uterm) => do                                  -- the borrow OPERATION, in any position
    -- M29 β. This row and the one above are the two spellings, and neither asks
    -- which arrow it is under: `&m` in a ⇝ position is a `.borrow`, which
    -- `reflectC` refuses by name ("`&mut` is not in the comptime fragment"), and
    -- `&mut` in a ⇒ position is a `.borrowT`, which `readR` refuses by name
    -- ("a telescope-position form, not a movable value"). Both refusals already
    -- existed and neither was reachable while the surface was deciding; the
    -- exclusions are the KERNEL's, and this is what it takes for the surface to
    -- stop making them on its behalf.
    let e' ← elabUTerm sc e
    return (← `(Dllbc.Term.borrow $e'))
  | `(uterm| Id $a:uterm $b:uterm $c:uterm) => do
    let a' ← elabUTerm sc a
    let b' ← elabUTerm sc b
    let c' ← elabUTerm sc c
    return (← `(Dllbc.Term.idT $a' $b' $c'))
  | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => do
    checkBinder x
    let τ' ← elabUTerm sc τ
    let b' ← elabUTerm (pushPure x.getId.toString sc) b
    return (← `(Dllbc.Term.lam $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') $b'))
  | `(uterm| λ ($bs:ulamb,*) { $b:uterm }) => do
    -- Runtime binders — slots, exactly as `let` and match patterns bind them:
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
    let (sc', binderSyns) ← elabLamBinders sc parsed
    let b' ← elabUBlk sc' b
    return (← `(Dllbc.Term.lamTel [$binderSyns,*] $b'))
  | `(uterm| Π ($x:ident : $τ:uterm) → $b:uterm) => do
    checkBinder x
    let τ' ← elabUTerm sc τ
    let b' ← elabUTerm (pushPure x.getId.toString sc) b
    return (← `(Dllbc.Term.pi $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') $b'))
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
    let τ' ← elabUTerm sc τ
    let b' ← elabUTerm (pushPure x.getId.toString sc) b
    return (← `(Dllbc.Term.sigmaT $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') $b'))
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
    let τ' ← elabUTerm sc τ
    let b' ← elabUTerm (pushPure x.getId.toString sc) b
    return (← `(Dllbc.Term.sigmaT $(quote (x.getId.toString))
      $(← binderDom (x.getId.toString) τ') (Dllbc.Term.cmpT $b')))
  -- The non-dependent arrow's binder is reserved and is NOT pushed onto `pctx`:
  -- nothing can refer to it, which is what "non-dependent" means. (The de Bruijn
  -- version had to push a placeholder, because every binder crossed moved the
  -- indices below it.)
  | `(uterm| $a:uterm → $b:uterm) => do
    let a' ← elabUTerm sc a
    let b' ← elabUTerm sc b
    return (← `(Dllbc.Term.pi $(quote unusedSnapName) $a' $b'))
  -- …and the same for the pair. The binder is the arrow's — reserved, unpushed,
  -- and UNMARKED, which is the point rather than an omission: `⇝` on a Σ domain
  -- is a claim about how that component is read, and a component nothing can
  -- name makes no such claim.
  | `(uterm| $a:uterm × $b:uterm) => do
    let a' ← elabUTerm sc a
    let b' ← elabUTerm sc b
    return (← `(Dllbc.Term.sigmaT $(quote unusedSnapName) $a' $b'))
  | `(uterm| &mut ( $x:ident : $τ:uterm )) =>
    Macro.throwErrorAt x s!"&mut ({x.getId} : τ) is not a borrow type — the snapshot-binder spelling is `&mut ({x.getId} : τ ~> τ')`, where `τ'` is what the borrow OWES back and `{x.getId}` is its entry snapshot, bound as pure var 0 in `τ'`. Without the `~> τ'` this would read as `&mut` applied to the ascription `({x.getId} : τ)`, which is a borrow of a SEAL — never meaningful, since a seal is not a place. If you meant a plain borrow of the type, write `&mut τ`."
  | `(uterm| ($t:uterm : $u:uterm)) => do
    -- The body is a ⇒ position (term mode) whatever surrounds the node; the
    -- ascribed type is a ⇝ position. That asymmetry is the seal itself.
    let t' ← elabUTerm sc t
    let u' ← elabUTerm sc u
    return (← `(Dllbc.Term.seal 0 $t' $u'))
  | `(uterm| $c:ident($args,*)) => do                 -- no-space paren: call / ctorApp
    let args' ← elabUList sc args.getElems.toList
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
      return (← `(Dllbc.Term.ctorApp $(quote name) [$args',*]))
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
      noteIdent sc c
      if isLocal sc name then
        return (← `(Dllbc.Term.appSpine (.var $(quote name)) [$args',*]))
      else return (← `(Dllbc.Term.call $(quote name) [$args',*]))
  | `(uterm| match $e:uterm { $arms,* }) => do
    let (scrut, pre?) ← elabScrut sc e
    -- Pattern binders (and bare-arm-body stragglers no statement row keyed) are
    -- ENTRY occurrences of this match: arm-entry binds file under the match key,
    -- so `replayEntry` answers each from its own arm's seed, per path. Occs a
    -- body row already keyed keep their key (`stmt.isNone` guard); nested
    -- pattern binders were keyed by `wrapPats` with their inner match first.
    let occLo ← occMark
    let arms' ← elabUArms sc arms.getElems.toList
    tagOccsEntry occLo (← `(Dllbc.Term.matchE $scrut none []))
    return (← wrapScrut scrut pre? (← `(Dllbc.Term.matchE $scrut none [$arms',*])))
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
      let (_, ps, _, _, _) ← liftM (armParts arm)
      ps.forM (fun p => liftM (refuseNestedPat p))
    let (scrut, pre?) ← elabScrut sc e
    let hName := h.getId.toString
    -- The equation binder and the arms' binders are entry occurrences, exactly
    -- as in the plain row above.
    let occLo ← occMark
    noteOcc h.raw hName
    let arms' ← elabUArms (pushSlot hName sc) arms.getElems.toList
    tagOccsEntry occLo (← `(Dllbc.Term.matchE $scrut (some (Dllbc.Var.slot $(quote hName))) []))
    let m ← `(Dllbc.Term.matchE $scrut (some (Dllbc.Var.slot $(quote hName))) [$arms',*])
    return (← wrapScrut scrut pre? m)
  | `(uterm| if $c:uterm { $t:uterm } else { $f:uterm }) => do  -- §12 sugar → Bool match
    let c' ← elabUTerm sc c
    let t' ← elabUBlk sc t
    let f' ← elabUBlk sc f
    return (← `(Dllbc.Term.seq (Dllbc.Term.letIn (Dllbc.Var.slot "__if") $c')
      (Dllbc.Term.matchE "__if" none
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])))
  | `(uterm| if $h:ident : $c:uterm { $t:uterm } else { $f:uterm }) => do
    let c' ← elabUTerm sc c
    let hName := h.getId.toString
    let sc' := pushSlot hName sc
    let t' ← elabUBlk sc' t
    let f' ← elabUBlk sc' f
    return (← `(Dllbc.Term.seq (Dllbc.Term.letIn (Dllbc.Var.slot "__if") $c')
      (Dllbc.Term.matchE "__if" (some (Dllbc.Var.slot $(quote hName)))
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])))
  | `(uterm| elim $scrut:uterm return $motive:uterm { $arms,* }) =>
    elabUElim sc scrut motive arms.getElems
  | `(uterm| elim $scrut:uterm generalizing $goal:uterm { $arms,* }) =>
    elabUGenElim sc scrut goal arms.getElems
  | `(uterm| $_:uterm $_:uterm) => do                 -- application spine (juxtaposition)
    let (head, args) := collectAppU stx
    match head with
    | `(uterm| $h:ident) =>
      let hs := h.getId.toString
      let argTerms ← elabUList sc args.toList
      if ctorSet.contains hs && (sc.find? hs).isNone then
        return (← `(Dllbc.Term.ctorApp $(quote hs) [$argTerms,*]))
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
        noteIdent sc h
        let hterm ← resolveName (← get).parse sc h
        let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
        return out
    | _ => do
      let hterm ← elabUTerm sc head
      let argTerms ← elabUList sc args.toList
      let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
      return out
  | `(uterm| $x:ident) => do
    -- EVERY occurrence, not just the binder: the walker resolves each ident to
    -- its variable already, so filing the pair costs one lookup (docs/16 S1).
    noteIdent sc x
    return (← resolveName (← get).parse sc x)
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
partial def elabScrut (sc : Scope)
    (e : TSyntax `uterm) : UM (TSyntax `term × Option (TSyntax `term)) := do
  match e with
  | `(uterm| ($inner:uterm)) => elabScrut sc inner
  | `(uterm| $x:ident) => do
    -- **THE SCRUTINEE IS AN OCCURRENCE LIKE ANY OTHER** (docs/16). This row is why
    -- it needed saying: the plain-variable path answers here and never reaches
    -- `elabUTerm`'s ident row, so without this call a parameter would hover
    -- everywhere EXCEPT in `match n { … }` — and match scrutinees are everywhere.
    -- Found by probing rather than by reading: `n` reported `Nat` at its binder
    -- and nothing one line below it.
    noteIdent sc x
    let s := x.getId.toString
    if isLocal sc s then return (← `($(quote s)), none)
    -- **A free scrutinee in a `prog_parse { }` block** (docs/22 §5) is the name
    -- itself — it resolves where the block is spliced. Only a name that resolves
    -- to NOTHING here takes this path; a pure binder, a constructor, a constant
    -- or a `fn` slot is refused exactly as in a closed program, for the reason
    -- given above.
    else if (← get).parse && (sc.find? s).isNone && !ctorSet.contains s
        && !constSet.contains s && (aliasMap.lookup s).isNone then
      return (← `($(quote s)), none)
    else Macro.throwErrorAt x s!"decl: match scrutinee '{s}' is not a bound runtime variable"
  | _ => do
    -- The fresh binder is minted at the POST-RHS counter and the block continues
    -- at `+1` — the `let` row's own discipline, because this is a `let`.
    let e' ← elabUTerm sc e
    return (← `($(quote scrutName)), some e')

partial def elabUList (sc : Scope) :
    List (TSyntax `uterm) → UM (Array (TSyntax `term))
  | [] => pure (#[])
  | a :: as => do
    let a' ← elabUTerm sc a
    let rest ← elabUList sc as
    pure (#[a'] ++ rest)

/-- A runtime λ's annotated binders (M27), elaborated as a TELESCOPE: each domain
    is read under the binders to its left and not its own, which is what lets
    `λ(v : &mut List Nat, hfuel : Le (len *v) fuel){ … }` mention `v` in the type
    after it. `&mut τ` there is the borrow TYPE because that is what `&mut`
    SPELLS (M29 β) — the domain no longer has to be elaborated in a distinguished
    mode to make it one, which is what let the flag go. `binderDom` puts §6's
    comptime marker on a capitalized binder's domain, which is what makes the
    annotation agree with the ascription `piPeel` checks it against. -/
partial def elabLamBinders (sc : Scope) :
    List (Ident × TSyntax `uterm) → UM (Scope × Array (TSyntax `term))
  | [] => pure (sc, #[])
  | (x, τ) :: rest => do
    let name := x.getId.toString
    let τT ← elabUTerm sc τ
    let τD ← binderDom name τT
    let entry ← `((Dllbc.Var.slot $(quote name), $τD))
    -- A runtime λ's binder SITE keeps the annotation hover (reading the source
    -- at the annotation itself). Its occurrences ride the point machinery like
    -- any other binder — the ptypes/static channel is gone (2026-08-21 ruling).
    noteHover x.raw (hoverText name (srcText τ.raw))
    let (sc', more) ← elabLamBinders (pushSlot name sc) rest
    pure (sc', #[entry] ++ more)

/-- Build the telescope entry syntaxes, threading the scope so that parameter
    `i`'s type sees params `0 .. i-1` — the `seedTelescope` convention — and
    then the ENCLOSING scope, exactly as the return type and the body do (the
    `fn` row's R2 rule). Params come first in the lookup, so a parameter
    shadows an enclosing binding of its name. -/
partial def buildTele (params : Scope) (sc : Scope) :
    List (String × TSyntax `uterm) → UM (Array (TSyntax `term))
  | [] => pure #[]
  | (nm, τ) :: rest => do
    let τT ← elabUTerm (params ++ sc) τ
    let entry ← `((($(quote nm), $τT) : String × Dllbc.Term))
    let rest' ← buildTele (params ++ [⟨nm, .slot, none⟩]) sc rest
    pure (#[entry] ++ rest')

partial def elabUArms (sc : Scope) :
    List (TSyntax `uarm) → UM (Array (TSyntax `term))
  | [] => pure (#[])
  | a :: as => do
    let a' ← elabUArm sc a
    let rest ← elabUArms sc as
    pure (#[a'] ++ rest)

/-- A `match` arm. ONE path, where there were two rows: `mintPatArgs` on the empty
    field list returns the scope it was given and `wrapPats` on no deferrals is its
    continuation, so the nullary arm is the applied one with nothing in it — which
    it always was, spelled twice.

    **A TRAILING NAME IS REFUSED HERE**, and this is the elaborator-level half of
    what `uelimArm` used to be. The two arm notations are one grammar row now, so
    `Cons(h, t) ih => …` parses in a `match`; what makes it wrong is not the shape
    but the meaning — a `match` steps once and has no recursive result to hand
    over — and a refusal that can say so is worth more than a missing row that
    reports "unexpected match arm". -/
partial def elabUArm (sc : Scope)
    (arm : TSyntax `uarm) : UM (TSyntax `term) := do
  let (c, ps, ih, body, braced) ← liftM (armParts arm)
  if let some ihId := ih then
    Macro.throwErrorAt ihId s!"match: '{c.getId}' names '{ihId.getId}' after its fields, and a match arm has nothing to bind there. A trailing name is an `elim` arm's INDUCTION HYPOTHESIS — the recursive call's result — and a `match` steps once, so there is no such result to hand you. To recurse, write an `elim … return …` over the scrutinee, or give a `fn` a `[k]`."
  -- The head's arguments are minted first, ALL of them, and the nested ones
  -- then wrap the body from the counter the body would have started at — which
  -- is what makes this arm the same `Term` as its hand-written twin and not
  -- merely a convertible one (`Tests.Sugar`'s goldens).
  let (sc', argVars, pend) ← mintPatArgs sc ps
  let body' ← wrapPats sc' pend (fun r => elabArmBody r body braced)
  return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [$argVars,*] $body'))

/-- An arm's body. **BRACED IS A BLOCK, BARE IS ONE STATEMENT**, and that is the
    only thing the two arm rows differ by.

    A bare body that SEQUENCES goes down the block route too. Since the category
    merge nothing in the grammar stops one — the arm list's `,` ends it — so the
    distinction the hover plumbing needs is made HERE, on what was written, rather
    than by a precedence that would forbid the spelling. -/
partial def elabArmBody (sc : Scope)
    (body : TSyntax `uterm) (braced : Bool) : UM (TSyntax `term) := do
  if braced then return (← elabUBlk sc body)
  match body with
  | `(uterm| $_:uterm ; $_:uterm) => elabUBlk sc body
  | e => do                              -- a bare arm body IS the arm's final statement
    -- **AND SO IT TAGS ITS OCCURRENCES, exactly as a block's final expression
    -- does** (docs/23). This row filed a SPAN and no occurrence key, so an
    -- identifier named in a bare arm body fell through to the match row's
    -- `tagOccsEntry` — which answers only for names that arm's own seed BOUND.
    -- The consequence a reader meets: `Nil => dst` hovers as nothing, because the
    -- base arm seeds no binder at all, while `Cons(hd, tl) => tl` answers. The
    -- fix is the sibling row's, one function down and four lines long: the arm's
    -- tail IS a statement, the machine files deltas under its key, so the surface
    -- keys the occurrences there and `factsAt` replays to it. Pattern BINDERS are
    -- unaffected — `mintPatArgs` files them before this row's mark, so they keep
    -- the match's entry key, which is the point they are actually bound at.
    let occLo ← occMark
    -- Stolen and put back UNTAGGED, which is where this differs from the sibling
    -- row and why: a pending `show` above the enclosing statement belongs to that
    -- statement, not to one arm of a match inside it (ShowSpans S6's regression).
    -- The sibling row restores before tagging because there the pendings are its
    -- own block's; here they can only ever be an ancestor's.
    let held ← takePendings
    let e' ← elabUTerm sc e
    spanOfStmt e' e
    tagOccsFrom occLo e'
    restorePendings held
    return e'

/-- Read `stx` as a BLOCK: a statement, or a statement and a block.

    Two lines, because the grammar is two shapes — a `;` node, or anything else.
    There is no `ublk` category for this to dispatch on any more; what makes the
    left of a `;` exactly one statement is the sequencer's `uterm:2`, so this
    function may take the left operand as a statement without re-checking it.

    The tail is handed to the statement rather than elaborated here, because three
    of the five statements do something with it other than being sequenced before
    it — see the `;` row's header, and each of the three at its own row. `seqStmt`
    is what the rest call, and it is the one place a `.seq` is built from a `;`. -/
partial def elabUBlk (sc : Scope)
    (stx : TSyntax `uterm) : UM (TSyntax `term) := do
  match stx with
  | `(uterm| $st:uterm ; $rest:uterm) => elabUStmt sc st (some rest)
  | _ => elabUStmt sc stx none

/-- Sequence a statement before its block's tail — or BE the block, when there is
    none. **The `.seq` builder, and the only one.** A statement's term is the same
    node either way; what a `;` adds is a `.seq` and a continuation wrapped around
    it, which is exactly what detach-tails made `.seq` mean.

    `tailSc` is the scope the tail is read in: the statement's own scope, extended
    by whatever it binds. Threading it here rather than at each row is the other
    half of what the six hardcoded tails cost — six chances to extend the wrong
    scope, or to forget to. -/
partial def seqStmt (stmt : TSyntax `term) (tailSc : Scope)
    (rest : Option (TSyntax `uterm)) : UM (TSyntax `term) := do
  match rest with
  | some rest => return (← `(Dllbc.Term.seq $stmt $(← elabUBlk tailSc rest)))
  | none => return stmt

/-- One statement, plus the tail of the block it sits in — `none` when it ENDS
    that block.

    Most rows hand `rest` straight to `seqStmt` and never look at it. The three
    that do look at it own their continuation, and each says at its own row what
    it does with it and why nothing else would serve. -/
partial def elabUStmt (sc : Scope) (stx : TSyntax `uterm)
    (rest : Option (TSyntax `uterm)) : UM (TSyntax `term) := do
  match stx with
  -- **UNREACHABLE, and said out loud rather than left to a confusing failure.**
  -- `elabUBlk` peels a `;` before calling here, and the sequencer's left operand
  -- is demanded at `uterm:2` — above the `;` row's own level — so no `;` node can
  -- arrive. If one ever does, the precedence discipline has been broken and this
  -- says which invariant, rather than reporting some downstream symptom.
  | `(uterm| $_:uterm ; $_:uterm) =>
    Macro.throwErrorAt stx "decl: internal — a `;` reached the statement walker. The sequencer's left operand is `uterm:2`, above the `;` row's level, so a statement can never itself be one; a change to those precedences has broken that."

  -- **`fn` — the declaration statement** (M28 θ). It emits a `let` of the §7
  -- lowering, one binding at a time, out of the two moving parts that already
  -- exist rather than reimplementing either:
  --
  --   * the right-hand side is `fnElabOrFail`, i.e. `fnElab` — the §7 lowering,
  --     with a refusal turned into a term the checker refuses distinctively;
  --   * the REST is passed through `bindFn`, i.e. `retarget` — which is how a call
  --     written in the tail finds the binding. `retarget` also PERMUTES a call's
  --     arguments to match a `[k]`-hoisted callee's telescope; eight functions in
  --     this corpus have a `[k]` that is not parameter 0, so that part is real and
  --     silent.
  --
  -- **THE PERMUTATION IS NOT WHY THIS ROW OWNS ITS TAIL**, and the older comment
  -- here said it was. The permutation is available at the surface — put the `[k]`
  -- index on the `Scoped` entry the `fn` row already pushes, and the call row can
  -- build the permuted spine itself. That was built and measured: the full suite
  -- goes GREEN with the call row minting the spine, so a surface that only ever
  -- had to serve calls it can SEE would need no `bindFn` at all.
  --
  -- What it cannot see is a SPLICE, and that is the reason. A fragment is
  -- elaborated where it is written and bound where it is spliced (docs/22 §7, the
  -- `parse` flag), so a call inside one is a `.call` to a name that does not exist
  -- yet — and `bindFn`, running on the assembled `Term` at the splice site, is
  -- what binds it. The corpus is built on this: `Tests/Traces`' `withAny rest`
  -- and `Tests/Functions`' `withA rest` wrap a Lean-level fragment in a
  -- declaration and every test in those files calls through it, and
  -- `Tests/HashMap`'s `growArm` — a `prog_parse` fragment — calls `MoveSlots`,
  -- which is declared in a different `def` a thousand lines below it. With the
  -- call row doing everything it could, `bindFn` still rewrote calls under
  -- EIGHTEEN distinct names across five test files; each one is a call the
  -- surface had no way to resolve.
  --
  -- (`retarget` would not retire in any case: `Program.moduleRetarget` is its
  -- other caller, resolving an imported call against a seeded module's Ω from
  -- `ledgers.hints` — macro-layer state a consumer block's surface does not hold.
  -- Its docstring says why that matters: an imported call and a local call are
  -- ONE shape because they are one function. Moving the local half to the surface
  -- would make them two implementations of one rule.)
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
  --
  -- **BOTH TAILS ARE OPTIONAL**, and they are independent. `-> R` omitted drops
  -- the SEAL (see the syntax row: the λ goes in bare and stays transparent), and
  -- `; rest` omitted drops the `.seq` and the `bindFn` — with no tail there is
  -- nothing to retarget, and the statement is the block's last, a bare `.letIn`
  -- whose value is `()`.
  | `(uterm| fn $name:ident $[[$dec:ident]]? ( $ps,* ) $[-> $ret:uterm]? { $body:uterm }) => do
    checkBinder name
    -- **A RECURSIVE `fn` CANNOT BE TRANSPARENT**, which is why a `[k]` needs a
    -- return type. The missing `-> R` is the symptom; the incompatibility is the
    -- fact, and it is not a gap a later milestone could infer away:
    --
    --   * unsealed means the checker UNFOLDS the body at the call site, by β;
    --   * β alone does not terminate on a recursive body;
    --   * the reduction that does terminate is ι, which fires on a CONSTRUCTOR —
    --     and "fires on a constructor" is exactly a recursor with a motive.
    --
    -- So a recursive function is a recursor whether or not it is spelled as one,
    -- and §7 builds the motive from the sealed Π with the scrutinee peeled off
    -- the front. The return type is what there is to build it from. That is the
    -- SECOND thing to say, not the first, and the message below is ordered that
    -- way.
    --
    -- Refused here rather than in `fnElab` because the pairing is decidable from
    -- the SYNTAX — no telescope type is consulted — and `FnMacro`'s policy puts
    -- cheap syntactic refusals at Lean elaboration, where the fix can be named,
    -- routing only semantic ones through `fnElabOrFail`'s sentinel.
    if let some d := dec then
      if ret.isNone then
        Macro.throwErrorAt d s!"fn: '{name.getId}' recurses on '{d.getId}', and a recursive function cannot be transparent. With no return type there is no seal, and with no seal the checker unfolds the body at each call site by β — which on a recursive body never terminates. The reduction that does terminate is ι, which fires on a constructor, and firing on a constructor IS a recursor with a motive; §7 builds that motive from the sealed Π with the scrutinee peeled off the front, so the return type is what there is to build it from. No later inference can supply it. Give '{name.getId}' a `-> R`."
    -- A pending `show` above this `fn` must not drain inside its body (the
    -- depth-blind hazard `takePendings` documents); it keys at the statement
    -- AFTER the declaration instead.
    let held ← takePendings
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
    -- The telescope's own scope, and the body's: the parameters, by name, as
    -- slots. Two parameters of one telescope cannot share a name — the kernel
    -- seeds them by name and says so (`seedTelescope`); refused here too, at
    -- the header, where the fix can be named.
    match names.find? (fun nm => (names.filter (· == nm)).length > 1) with
    | some dup => Macro.throwErrorAt name s!"fn: '{name.getId}' binds the parameter '{dup}' twice. Parameters are bound by NAME (docs/22), so two of one name would be one slot."
    | none => pure ()
    let fullSc : Scope := names.map (fun nm => ⟨nm, .slot, none⟩)
    -- Parameter binders and every occurrence in the telescope are ENTRY
    -- occurrences (docs/17, `OccNote.entry`): they answer from the checker's own
    -- seeds, replayed to "entering the body". The annotation channel this
    -- replaced (`pTypes`/`static?`) is gone — under strong updates nothing about
    -- a slot is timeless, and a parameter's entry state IS its annotation,
    -- checked.
    let occLo ← occMark
    parsedI.forM fun (x, _) => noteOcc x.raw x.getId.toString
    let teleSyns ← buildTele [] sc parsed
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
    -- **NO `-> R` IS `none`, AND `none` IS NO SEAL** (`FnDef.retType`) — never an
    -- inferred one. What is elaborated here is only the written return type, in
    -- the telescope's scope so it may cite the parameters; with none written
    -- there is nothing to elaborate, nothing to cite, and nothing to seal at.
    let retT ← match ret with
      | none => `((none : Option Dllbc.Term))
      | some r => do
        let t ← elabUTerm (fullSc ++ sc) r
        `(some $t)
    let nm := name.getId.toString
    -- The entry key is this `fn`'s own `let`-statement key — the seeds file
    -- under it, because the cursor does not move between `letStep` and the seal
    -- check (`replayEntry`). Tagged BEFORE the body elaborates, so the range is
    -- exactly the telescope, the binders, and the return type.
    tagOccsEntry occLo (← fnKey nm)
    let bodyT ← elabUBlk (fullSc ++ sc) body
    let decIdx? : Option Nat ← match dec with
      | none => pure none
      | some d =>
        match names.findIdx? (· == d.getId.toString) with
        | some i => pure (some i)
        | none => Macro.throwErrorAt d s!"fn: decreasing argument '{d.getId}' is not a parameter of '{name.getId}'"
    let decT ← match decIdx? with
      | none => `((none : Option Nat))
      | some i => `(some $(quote i))
    -- The `[k]` hint, filed as plain data (docs/20 stage 3). `bindFn` below
    -- consumes the hint for THIS block's own calls; this entry is for the
    -- blocks that come later — a module block persists it, and an imported
    -- call is permuted by it. See `SpanAcc.fnHints`.
    if let some i := decIdx? then
      modify fun a => { a with fnHints := a.fnHints.push (nm, i) }
    -- The slot: the TAG `declSlot` (M32 R4). It used to be `progBase + next`,
    -- distinct per declaration, because a function's OWN body numbers its
    -- parameters from 0 and an id-keyed lookup would read a colliding binding as
    -- that parameter. Ω resolves by NAME (M32 R1), so distinctness bought
    -- nothing and the shared tag says the one thing still asked of it: this
    -- entry is a declaration. `next` is no longer consumed here.
    let slot ← `(Dllbc.Var.decl $(quote nm))
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
    -- The span is the name plus the return type when one is written, and the
    -- name alone when it is not — there is no third thing to point at.
    spanOfFn nm (mkNullNode (match ret with | some r => #[name, r] | none => #[name]))
    -- **A CALLEE'S SIGNATURE, from scope** (docs/16 S1's cheap extension). The
    -- plan says "from the registry"; there is no registry — docs/05 §1.A deleted
    -- it before it was written, because a callee is a binding lexically above the
    -- call and so scope IS the call table. Scope answers this question too, and
    -- the entry is visible for exactly `rest`: not inside the body (a `fn` is not
    -- in scope in its own right-hand side, §8) and not after the block.
    -- The hover reads back what was WRITTEN, so an omitted return type is omitted
    -- here too rather than filled in with a guess: a `fn` with no `-> R` has no
    -- signature to show, and showing one would claim a seal that is not there.
    let sigText := "(" ++ ", ".intercalate
        (parsedI.map fun (x, τ) => s!"{x.getId} : {srcText τ.raw}")
      ++ ")" ++ (match ret with | some r => " -> " ++ srcText r.raw | none => "")
    noteHover name.raw (hoverText nm sigText)
    restorePendings held
    let rhs ← `(Dllbc.Term.letIn $slot
                  (Dllbc.FnMacro.fnElabOrFail
                    (Dllbc.FnDef.mk $(quote nm) [$teleSyns,*] $retT $bodyT $decT)))
    match rest with
    -- WITH A TAIL, the ordinary shape: the `let` sequenced before the rest, and
    -- the rest passed through `bindFn` so a call written in it finds the binding
    -- (and is permuted by the `[k]` hint). The keys `rest` files are re-keyed
    -- through that `bindFn`, because that is what the walker's breadcrumb sees
    -- (`rekeySpansFrom`).
    | some rest => do
      let stmtLo := (← get).stmts.size
      let argLo := (← get).args.size
      let rest' ← withHoverScope [(nm, sigText)]
        (elabUBlk (⟨nm, .decl, none⟩ :: sc) rest)
      rekeySpansFrom stmtLo argLo slot decT
      return (← `(Dllbc.Term.seq $rhs (Dllbc.FnMacro.bindFn $slot $decT $rest')))
    -- WITHOUT ONE, the `let` IS the block: no `.seq`, because there is no second
    -- statement to sequence, and no `bindFn`, because retargeting is a rewrite of
    -- the tail and there is no tail — a declaration nothing can call. Nor is
    -- there anything to re-key or any hover scope to open, both of which exist
    -- only for what `rest` would have filed.
    --
    -- A bare `.letIn` in tail position is meaningful under BOTH arrows already
    -- (`readR` and `exploreD`'s final-expression arm via `readResult` on ⇒,
    -- `Pure.eval` on ⇝, and `stmtKeyOf` has its arm), so this row emits an
    -- existing shape rather than a new one and the kernel is untouched. The
    -- block's value is `()`.
    | none => return rhs
  | `(uterm| let $x:ident = $e:uterm) => do
    checkBinder x
    let occLo ← occMark
    let held ← takePendings
    let e' ← elabUTerm sc e
    -- **`let X = e` is a comptime binding** (§6) and needs no macro support: the
    -- mode of a runtime binder IS its `Var`'s name, so the kernel reads it off
    -- the `letIn` this line already emits. Recorded here because the absence of
    -- code is the point — the convention is load-bearing exactly once.
    let name := x.getId.toString
    -- **ONE `let`, both fragments** (M29 α). This row used to branch on the mode:
    -- ⇒ minted a runtime slot and emitted `.letIn`, ⇝ emitted the β-redex
    -- `(λ. rest) e` over an anonymous binder. The kernel now reads `.letIn` under
    -- BOTH arrows — so the surface has nothing left to decide, and this was the
    -- first of the two branches the mode flag had. (⇝'s reading was a β built at
    -- reflection until M32 R1; now `reflectC` carries the `letIn` through as
    -- itself and `Pure.eval` binds `Pure.letName x.id` in its environment — no
    -- redex is constructed.)
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

    -- File this statement at `x = e`, under its key — binder and right-hand
    -- side (`letKey`, docs/22 §4).
    let key ← letKey name e'
    spanOfLet key (mkNullNode #[x, e])
    -- The `let` BINDER's own span, filed like an occurrence: its type comes from
    -- the checker (docs/16 S2), so it joins against `St.letTypes` exactly as the
    -- uses below it do, under the same id.
    noteOcc x.raw name (some key.raw)
    -- Every occurrence in this statement — the right-hand side's and the binder's
    -- — is filed under this statement's key, which is the POINT a hover on any of
    -- them asks about (docs/17).
    restorePendings held
    tagOccsFrom occLo key
    -- The tail is DETACHED (detach-tails), so this row emits the tail-less
    -- `.letIn` and nothing else — `seqStmt` decides whether a `.seq` goes around
    -- it, and the kernel scopes the binder over that seq's tail. The scope handed
    -- on is this one plus the name, which is the whole of what a `let` contributes
    -- to the rest of its block.
    seqStmt (← `(Dllbc.Term.letIn (Dllbc.Var.slot $(quote name)) $e'))
      (pushSlot name sc (some key.raw)) rest
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
  | `(uterm| let $c:ident($args,*) = $e:uterm) => do
    let occLo0 ← occMark
    let held ← takePendings
    let (scrut, pre?) ← elabScrut sc e
    -- This row IS an arm whose body is the enclosing block, so its binders are
    -- entry occurrences of the match it emits — tagged before the block
    -- elaborates, so the range is the pattern alone.
    let occLo ← occMark
    let (sc', argVars, pend) ← mintPatArgs sc args.getElems.toList
    tagOccsEntry occLo (← `(Dllbc.Term.matchE $scrut none []))
    -- The scrutinee's occurrences and any pending `show` above this row key at
    -- the emitted match — the statement this row is.
    restorePendings held
    tagOccsFrom occLo0 (← `(Dllbc.Term.matchE $scrut none []))
    -- Nested arguments (M34 sugar (iii)) wrap the rest of the block in their
    -- matches, which is the same rewrite `elabUArm` performs — and has to be, since
    -- this row IS an arm whose body is the enclosing block. `let Pair(a, Pair(b, c))
    -- = p ;` and the two-line chain that spells it out are one `Term`.
    let rest' ← wrapPats sc' pend (fun r =>
      match rest with
      | some rest => elabUBlk r rest
      | none => `(Dllbc.Term.unit))
    let m ← `(Dllbc.Term.matchE $scrut none
                [Dllbc.Branch.mk $(quote c.getId.toString) [$argVars,*] $rest'])
    return (← wrapScrut scrut pre? m)
  | `(uterm| $p:uterm := $e:uterm) => do
    let occLo ← occMark
    let held ← takePendings
    let p' ← elabUTerm sc p
    let e' ← elabUTerm sc e
    spanOfAssign p' e' (mkNullNode #[p, e])
    restorePendings held
    tagOccsFrom occLo (← `(Dllbc.Term.assign $p' $e'))
    -- An assignment BINDS NOTHING, so the scope it hands on is the one it was
    -- given. `readR` gives the bare `.assign` `.ctor "unit" []` exactly as it
    -- gives the seq'd one, and `stmtKeyOf`'s catch-all keys the two identically —
    -- `let v = 0; v := 1` runs to `[(v, 1)]`.
    seqStmt (← `(Dllbc.Term.assign $p' $e')) sc rest
  -- **`show x ; rest` — ERASED** (docs/18). Emits `rest` and nothing else: no
  -- node, no read, no move, no borrow, no Ω. The identifier is resolved exactly
  -- as any other occurrence is (so an unknown name gets the ordinary
  -- unbound-identifier error, with no second message to keep in step), its
  -- occurrence is filed, and it is left PENDING for the next statement to key —
  -- because the state entering that statement is the state here.
  --
  -- **A TAIL-LESS `show x` EMITS `()`.** It is the one statement row whose
  -- tail-less form is not just "the statement, unwrapped", because there is no
  -- statement — the row's whole output is its tail, so with no tail there is
  -- nothing to emit and something has to be. `()` is what a block that ends in a
  -- statement is worth everywhere else in this grammar, so `show` ending one
  -- agrees with `let` and `:=` ending one rather than inventing a third answer.
  --
  -- **`show x` and `show x ; ()` are then the same program AND the same
  -- occurrence.** The `()` is emitted, its span is filed at this row (the only
  -- source there is to point at), and the pending occurrence DRAINS at it — which
  -- is what the written form's own final-expression row would have done, at the
  -- identical key. So the tail-less spelling is not a second path through the
  -- hover plumbing; it is the same one with the `()` supplied.
  --
  -- **The honest limit, which is INHERITED and not introduced**: a `show` whose
  -- next statement is `()` gets the BINDER fact rather than the point fact,
  -- because `replayTo` answers only where a delta is filed under the key and a
  -- `()` changes nothing, so it files none. That is already true of a written
  -- `; ()` — verified, on this grammar and on the one before it: with
  -- `*b := Cons(2, Nil); show b;` the answer is `borrowₘ ℓ₀ (Cons 2 Nil)` when a
  -- real statement follows the `show` and `borrowₘ ℓ₀ (Cons 1 Nil)`, the value at
  -- `b`'s binding, when `()` does. The tail-less form gives the second, which is
  -- what the `; ()` it replaced gave.
  --
  -- The drain is still not optional. `pendingOccs` is depth-blind — the hazard
  -- `takePendings` exists for — so an undrained pending is one an enclosing
  -- block's next statement can claim, keying a `show` written inside a match arm
  -- at a statement one level out.
  | `(uterm| show $x:ident) => do
    let mark ← occMark
    noteIdent sc x
    modify fun a =>
      if a.hover && a.occs.size > mark then
        { a with pendingOccs := a.pendingOccs.push mark, showOccs := a.showOccs.push mark }
      else a
    -- `resolveName` for its ERROR only: an unbound name must fail here as it
    -- would anywhere else. The resolved term is discarded — that is the erasure.
    let _ ← resolveName (← get).parse sc x
    match rest with
    | some rest => elabUBlk sc rest
    | none => do
      let u ← `(Dllbc.Term.unit)
      spanOfStmt u stx
      tagOccsFrom mark u
      return u
  -- **AN EXPRESSION IS A STATEMENT** — and since the merge that is not a row at
  -- all, it is this walker's FALLTHROUGH.
  --
  -- There were three spellings of it. `uterm ";" ublk` and `uterm : ublk`
  -- ("expression statement" and "final expression") had byte-identical bodies and
  -- differed only in what they did with a tail, which is `seqStmt`'s question;
  -- they merged into one row. Then `syntax uterm : ustmt` was a coercion whose
  -- whole content was "an expression may stand where a statement stands" — a
  -- THEOREM of one category, not a rule to write. What is left is: whatever is not
  -- one of the five statement forms above is an expression, run for its effect
  -- when something follows it and for its VALUE when nothing does.
  --
  -- `stmtKeyOf` is applied in the emitted expression rather than mirrored by hand,
  -- so a final `match` files under the same `matchE s eqn []` the walker computes
  -- without this walker knowing that rule. And occurrences ARE tagged here — the
  -- final-expression case did not tag them until docs/18 §3, so anything named in
  -- a block's last expression fell back to binder granularity; a pre-existing hole
  -- in docs/17's surface, and now there is one place that can have it rather than
  -- three that must agree not to.
  | _ => do
    let e := stx
    let occLo ← occMark
    let held ← takePendings
    let e' ← elabUTerm sc e
    spanOfStmt e' e
    restorePendings held
    tagOccsFrom occLo e'
    seqStmt e' sc rest

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
partial def elabUElim (sc : Scope)
    (scrut motive : TSyntax `uterm) (arms : Array (TSyntax `uarm)) : UM (TSyntax `term) := do
  let scrutT ← elabUTerm sc scrut
  let motiveT ← elabUTerm sc motive
  let motiveBare := match motive with | `(uterm| ($e:uterm)) => e | _ => motive
  let (mName, mTy, mBody) ← match motiveBare with
    | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => pure (x.getId.toString, τ, b)
    | _ => Macro.throwError "elim: motive must be a λ `(x : τ). …`"
  -- The arms are `uarm`s — the same arms a `match` takes (`uelimArm` is gone) —
  -- read through `armParts`, which concatenates the paren groups so `S (k) ih`
  -- and `S(k) ih` are one arm. `elimBinders` is the other half of what the second
  -- category used to do by construction: a recursor's arm binds PLAIN NAMES, so a
  -- nested pattern is refused by name here rather than by a missing row.
  let armFor (c : String) : UM (Option (Array Ident × Option Ident × TSyntax `uterm)) := do
    for arm in arms do
      let (ctor, ps, ih, body, _) ← liftM (armParts arm)
      if ctor.getId.toString == c then
        return some (← liftM (elimBinders ctor ps), ih, body)
    return none
  let getArm (c : String) : UM (Array Ident × Option Ident × TSyntax `uterm) := do
    match ← armFor c with
    | some r => pure r
    | none => Macro.throwError s!"elim: missing arm for constructor '{c}'"
  let names ← arms.mapM (fun a => do
    let (ctor, _, _, _, _) ← liftM (armParts a); pure ctor.getId.toString)
  -- `P ⟨target⟩`: the motive body with the motive's binder renamed to the arm's.
  let pOf (target : String) : UM (TSyntax `term) := do
    let b := (← elabUTerm (pushPure mName sc) mBody)
    `(Dllbc.Term.substP $(quote mName) (Dllbc.Term.var $(quote target)) $b)
  if names.contains "Z" || names.contains "S" then
    let (_, _, zb) ← getArm "Z"; let z := (← elabUBlk sc zb)
    let (sb, sih, sbody) ← getArm "S"
    let kName := (sb[0]!).getId.toString
    let ihName := (sih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf kName
    let body := (← elabUBlk (pushPure ihName (pushPure kName sc)) sbody)
    let kDom ← binderDom kName (← `(Dllbc.Term.const "Nat"))
    let ihDomM ← binderDom ihName ihDom
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "natRec") $motiveT) $z)
        (Dllbc.Term.lam $(quote kName) $kDom
          (Dllbc.Term.lam $(quote ihName) $ihDomM $body))) $scrutT))
  else if names.contains "True" || names.contains "False" then
    let (_, _, tb) ← getArm "True"; let t := (← elabUBlk sc tb)
    let (_, _, fb) ← getArm "False"; let f := (← elabUBlk sc fb)
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motiveT) $t) $f) $scrutT))
  else if names.contains "Nil" || names.contains "Cons" then
    let (_, _, nb) ← getArm "Nil"; let n := (← elabUBlk sc nb)
    let (cb, cih, cbody) ← getArm "Cons"
    let hName := (cb[0]!).getId.toString
    let tName := (cb[1]!).getId.toString
    let ihName := (cih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf tName
    let body := (← elabUBlk (pushPure ihName (pushPure tName (pushPure hName sc))) cbody)
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
      | some a => pure (← elabUTerm sc a)
      | none => `(Dllbc.Term.const "Nat")
    let hDom ← binderDom hName elemT
    let tDom ← binderDom tName (← `(Dllbc.Term.app (Dllbc.Term.const "List") $elemT))
    let ihDomM ← binderDom ihName ihDom
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "listRec") $elemT) $motiveT) $n)
        (Dllbc.Term.lam $(quote hName) $hDom
          (Dllbc.Term.lam $(quote tName) $tDom
            (Dllbc.Term.lam $(quote ihName) $ihDomM $body)))) $scrutT))
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
    let aT := (← elabUTerm sc aSyn)
    -- `B` under its own binder — correct for the family `λ x. B` as written, and
    -- renamed below for the arm's second binder domain, whatever the arm calls it.
    let bT := (← elabUTerm (pushPure bName sc) bSyn)
    let (pb, _, pbody) ← getArm "Pair"
    let xName := (pb[0]!).getId.toString
    let yName := (pb[1]!).getId.toString
    let body := (← elabUBlk (pushPure yName (pushPure xName sc)) pbody)
    -- `B` reaches the Σ's own binder, and the arm names that field itself — so the
    -- arm's second domain is `B` with the Σ binder renamed, the same move `pOf`
    -- makes for a recursor's `ih`.
    let xDom ← binderDom xName aT
    let yDom ← binderDom yName (← `(Dllbc.Term.substP $(quote bName) (Dllbc.Term.var $(quote xName)) $bT))
    -- The type FAMILY `λ x. B` is the Σ read back as a function, so its binder is
    -- the Σ's own binder and takes the Σ's own domain — marker included. Written
    -- unmarked, it was the one place a `Σ (Hu : A). B` and the family
    -- `sigmaRec` takes for it disagreed about `Hu`'s mode.
    let famDom ← binderDom bName aT
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "sigmaRec") $aT)
        (Dllbc.Term.lam $(quote bName) $famDom $bT)) $motiveT)
        (Dllbc.Term.lam $(quote xName) $xDom
          (Dllbc.Term.lam $(quote yName) $yDom $body))) $scrutT))
  else
    Macro.throwError "elim: arms do not match a known recursor (Nat/Bool/List/Σ)"

/-- `elim scrut generalizing goal { arms }` (§18): the motive is
    `λ x. abstractOccurrences scrut goal` — the natural goal with the computed
    subterm abstracted at all its occurrences, mechanically. Bool motives only (the
    count algebra's case-on-`eqb`); Nat/List use the `return` form. -/
partial def elabUGenElim (sc : Scope)
    (scrut goal : TSyntax `uterm) (arms : Array (TSyntax `uarm)) : UM (TSyntax `term) := do
  let scrutT ← elabUTerm sc scrut
  let goalT ← elabUTerm sc goal
  let armBody (c : String) : UM (TSyntax `term) := do
    for arm in arms do
      let (ctor, ps, _, body, _) ← liftM (armParts arm)
      if ctor.getId.toString == c then
        let _ ← liftM (elimBinders ctor ps)
        return (← elabUBlk sc body)
    Macro.throwError s!"elim generalizing: missing arm '{c}'"
  let names ← arms.mapM (fun a => do
    let (ctor, _, _, _, _) ← liftM (armParts a); pure ctor.getId.toString)
  if names.contains "True" || names.contains "False" then
    let t ← armBody "True"
    let f ← armBody "False"
    let nf := Lean.mkIdent `Dllbc.Std.nfTerm
    let motive ← `(Dllbc.Term.lam Dllbc.genName (Dllbc.Term.const "Bool")
      (Dllbc.abstractOccurrences ($nf $scrutT) ($nf $goalT)))
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motive) $t) $f) $scrutT))
  else
    Macro.throwError "elim generalizing: only Bool motives supported (§18); Nat/List use the `return` form"

end

end Surface

end Dllbc
