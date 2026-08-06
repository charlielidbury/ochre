import Lean
import Dllbc.Machine
import Dllbc.FnMacro

/-!
# `uterm` / `ublk` — THE term grammar

One grammar, and everything else is it entered somewhere. `prog{ }`
(ProgMacro.lean) is `ublk` in ⇒ mode, `pure{ }` (PureMacro.lean) is the same call
in ⇝ mode, and the two differ by exactly the `isTy` flag — this calculus's
"one grammar, four arrows" showing up at elaboration time. `fn` is a STATEMENT of
`ublk` (M28 θ), so a declaration is written where a `let` is written and there is
no separate declaration surface to learn.

**There are exactly two macros**, and they are the two above (M28 D9). `decl{ }`,
the legacy declaration former that produced an `FnDef` *value*, is deleted: `fn`
is a statement, so the value it produced has no consumer that is not the statement
itself. The elaborator's namespace is `Surface`, which is what it always was.

## Type positions

Telescope entry types, the return type, and the `↝` right-hand side all elaborate
through `uterm` in TYPE mode (`isTy := true`) — Σ/Π/λ/→/
Id/application/`Type` — extended with two things the boundary needs:

  * a **runtime-var context**: the names of EARLIER telescope parameters resolve
    to `.var ⟨i, name⟩` with positional 0-based ids — the exact convention
    `seedTelescope` seeds (argument `i` ↦ var id `i`) and the corpus's `V i "…"`
    references use. Runtime vars are absolute ids, so crossing a Σ/Π/λ binder
    does NOT shift them (matching §5.2: a runtime var in a type is resolved by ⇝
    to its snapshot, never de Bruijn).
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
reified-function alias (`Le`, `len`, `add`, …) → its `…FnT` Term constant; else
the **Lean identifier** of that name, which must denote a `Dllbc.Term` in scope
(a library lemma like `swapL`, `set`, `sortRangeL`) — the documented fallback.

## Body

A function's body is `ublk` in TERM mode with the telescope names pre-bound in
order at ids `0 .. n-1` and fresh binders minted from `n`, the `seedTelescope`
convention. That is the only place in the surface where a name arrives pre-bound.
Bodies laden with pure proof terms (a `botElim` ex-falso branch, a `le_rw_r` bound
derivation) can be spliced whole with `%term`, which is a `uterm` and therefore a
block's final expression — the escape hatch `decl{ … = %t }` used to provide,
available uniformly wherever an expression is.
-/

open Lean

namespace Dllbc

/-! ## The unified `uterm` / `ublk` grammar (§ phase-3 point 1 — ONE term grammar)

A single expression grammar spanning BOTH fragments. It used to be elaborated
under a **mode flag** — "is this position consumed by ⇒ or ⇝" — and that flag had
exactly two readers. Both are gone:

  * **`let`** (M29 α) emitted a `.letIn` in one mode and a de Bruijn β-redex in
    the other. One row emits `.letIn` and the kernel reads it under both arrows;
    ⇝'s reading of it IS that β, performed where the binder depth is known.
  * **`&mut`** (M29 β) was the borrow OPERATION in one mode and the borrow TYPE in
    the other. They are spelled `&m` and `&mut` now, so each row emits its own
    node whatever surrounds it.

What is left of the difference between the fragments is in the KERNEL, which is
where it was always a fact about the arrows rather than about the elaborator: a
form with no comptime reading is refused by `reflectC` (whose refusal list IS this
calculus's definition of the pure sub-grammar), and a form with no runtime reading
is refused by `readR`. The surface makes neither exclusion on their behalf.

Every form is therefore shared: application spines, λ/Π/Σ/→/Id/`Type`, `*e`, `Id`,
`let`, `&m`, `&mut`, constructor/const/lemma references. `ublk` is the statement
layer.

**The one disambiguation rule (§ point 2):** `f(a, b)` — an identifier with a
**no-whitespace** paren argument list — is a runtime **call** (lowercase head) or
**ctorApp** (uppercase). Space-separated **juxtaposition** `f a b` (incl.
`f (a) b`) is **pure application** (`ctorApp` when the head is a known ctor). So
`nth(&m *tl, k, p)` is a call, `botElim Unit p` and `le_rw_r (S x) y` are
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
syntax:max "λ" "(" ulamb,* ")" "{" ublk "}" : uterm          -- .lamR
syntax:10 "Π" "(" ident ":" uterm ")" "→" uterm:10 : uterm   -- Pi
syntax:10 "Σ" "(" ident ":" uterm ")" "→" uterm:10 : uterm   -- Sigma (arrow form)
syntax:10 "Σ" "(" ident ":" uterm ")" "." uterm:10 : uterm   -- Sigma (dot form)
syntax:10 uterm:11 "→" uterm:10 : uterm                      -- non-dependent arrow
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

-- Pure eliminator sugar (§15b) — for `pure{}` / comptime positions. Arm bodies are
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

/-- The name a `pctx` entry is masked to when a `let` shadows a pure binder
    (M29 α). It occupies the entry so that every de Bruijn INDEX below it keeps
    its level, while being unwritable as source — so the masked binder is exactly
    unreachable by name, which is what shadowing is. -/
def shadowedName : String := "§shadowed"

/-- Innermost-first de Bruijn index of `s` in `l`. -/
def idxOf? (l : List String) (s : String) : Option Nat :=
  let rec go : List String → Nat → Option Nat
    | [], _ => none
    | x :: xs, i => if x == s then some i else go xs (i + 1)
  go l 0

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
    (`Val.ctorNames`, adjacent to `ctorSig`) rather than repeated here, because
    M26-B gives the list a second job — reserving these names as binder keywords
    — and two lists that must agree is one list too many. -/
def ctorSet : List String := Dllbc.Val.ctorNames
/-- Kernel constants (type formers / recursors / eliminators) → `const`. -/
def constSet : List String := ["Nat", "Bool", "List", "Bot", "Unit", "natRec", "boolRec", "listRec", "sigmaRec", "botElim", "j", "k",
  -- ¶1.1/¶1.3's array basis: the former, the split view, the cons view, the read.
  "Array", "arrCat", "acons", "arrRec", "aget"]
/-- Friendly aliases for the reified library functions whose surface name differs
    from their `…FnT` Term-constant (`Le` ↦ `LeFnT`, etc.). Everything else falls
    through to the raw-Lean-identifier resolution, so lemma Terms (`swapL`, `set`,
    `sortRangeL`, …) are referenced by their own names via the use-site `open`s. -/
def aliasMap : List (String × Name) :=
  [("Le", `Dllbc.Std.LeFnT), ("len", `Dllbc.Std.lenFnT), ("add", `Dllbc.Std.addFnT),
   ("leb", `Dllbc.Std.lebFnT), ("count", `Dllbc.Std.countFnT), ("eqb", `Dllbc.Std.eqbFnT),
   ("take", `Dllbc.Std.takeFnT), ("drop", `Dllbc.Std.dropFnT),
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

/-- May this identifier be a binder? -/
def reservedBinder (s : String) : Bool :=
  Dllbc.isUpperInit s && (ctorSet.contains s || constSet.contains s)

/-- Reject a reserved name in binder position. Called at every binder the
    unified grammar has: λ, Π, Σ, `let`, match arms and their equation binder,
    and a `fn`'s parameters. -/
def checkBinder (x : Ident) : MacroM Unit := do
  let s := x.getId.toString
  if reservedBinder s then
    Macro.throwErrorAt x s!"'{s}' is a reserved name (a constructor or a kernel type/constant) and cannot be a binder. §6 makes capitalisation the binder-mode marker — capital = comptime — which is unambiguous only if the capitalized names of the fixed basis are keywords."

/-- The λ/Π domain for a binder named `nm`: `⇝τ` when the name is capitalized
    (a COMPTIME binder — its argument is ⇝-read at ⇒-calls, and the fence keeps
    it in ⇝-positions), plain `τ` otherwise. The whole of the surface's part in
    §6 for pure binders; runtime binders need nothing, because their mode is
    their `Var`'s name. -/
def binderDom (nm : String) (τ : TSyntax `term) : MacroM (TSyntax `term) :=
  if Dllbc.isUpperInit nm then `(Dllbc.Term.cmpT $τ) else pure τ

/-- Resolve a bare identifier in a type/back position. Pure binder (innermost) →
    `pvar`; earlier telescope param → `var`; constructor → nullary `ctorApp`;
    kernel const → `const`; reified-function alias → its `…FnT` Term; else the
    Lean identifier of that name (a `Term` in scope). -/
def resolveName (rctx : List (String × Nat)) (pctx : List String) (x : Ident) : MacroM (TSyntax `term) := do
  let s := x.getId.toString
  match idxOf? pctx s with
  | some i => `(Dllbc.Term.pvar $(quote i))
  | none =>
    match rctx.lookup s with
    | some id => `(Dllbc.Term.var ⟨$(quote id), $(quote s)⟩)
    | none =>
      if ctorSet.contains s then `(Dllbc.Term.ctorApp $(quote s) [])
      else if constSet.contains s then `(Dllbc.Term.const $(quote s))
      else match aliasMap.lookup s with
        | some n => pure ⟨(mkIdent n).raw⟩
        | none => pure ⟨x.raw⟩

/-! ## Unified `uterm` / `ublk` elaborators (§ points 1–3)

Runtime binders (let, match patterns) mint fresh absolute ids threaded through
`next`: a `let` binds at the post-RHS counter value and continues at `+1`, and a
match's arm binders are minted from one counter across ALL arms, so no two
binders in a body ever share an id. This is the id discipline of the retired
runtime-body grammar, reproduced here exactly — every one of its 70 sites in the
suite was checked byte-for-byte against this elaborator before it was deleted
(M28 α–δ).
Pure binders (λ/Π/Σ/→) push the de Bruijn `pctx` and never touch `next`; a
runtime var referenced from inside a pure spine stays `.var` (absolute, unshifted). -/

partial def collectAppU : TSyntax `uterm → TSyntax `uterm × Array (TSyntax `uterm)
  | `(uterm| $f:uterm $a:uterm) => let (h, as) := collectAppU f; (h, as.push a)
  | t => (t, #[])

mutual

partial def elabUTerm (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `uterm) : MacroM (TSyntax `term × Nat) := do
  match stx with
  | `(uterm| ()) => return (← `(Dllbc.Term.unit), next)
  | `(uterm| ($e:uterm)) => elabUTerm isTy rctx pctx next e
  | `(uterm| Type) => return (← `(Dllbc.Term.type), next)
  | `(uterm| % $e:term) => return (← `(($e : Dllbc.Term)), next)
  | `(uterm| $n:num) => return (← buildNat n.getNat, next)
  | `(uterm| old * $e:uterm) => do
    -- §5.4 `old *v`: the ENTRY snapshot, sugar over the telescope's existing
    -- payload snapshot. Elaborates to `@old(*v)`; `markExit` strips the marker to
    -- a plain `*v` read at seed (entry), so it never reaches the kernel.
    let (e', n) ← elabUTerm isTy rctx pctx next e
    return (← `(Dllbc.Term.app (Dllbc.Term.const "old") (Dllbc.Term.deref $e')), n)
  | `(uterm| * $e:uterm) => do
    let (e', n) ← elabUTerm isTy rctx pctx next e
    return (← `(Dllbc.Term.deref $e'), n)
  | `(uterm| $a:uterm[$i:uterm]) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (i', n2) ← elabUTerm isTy rctx pctx n1 i
    return (← `(Dllbc.Term.index $a' $i' none), n2)
  | `(uterm| $a:uterm[$i:uterm | $h:uterm]) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (i', n2) ← elabUTerm isTy rctx pctx n1 i
    let (h', n3) ← elabUTerm isTy rctx pctx n2 h
    return (← `(Dllbc.Term.index $a' $i' (some $h')), n3)
  | `(uterm| $a:uterm[$lo:uterm ; ..]) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (lo', n2) ← elabUTerm isTy rctx pctx n1 lo
    return (← `(Dllbc.Term.range $a' $lo' none none none none), n2)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm]) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (lo', n2) ← elabUTerm isTy rctx pctx n1 lo
    let (c', n3) ← elabUTerm isTy rctx pctx n2 c
    let (r', n4) ← elabUTerm isTy rctx pctx n3 r
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') none none), n4)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm | $h:uterm]) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (lo', n2) ← elabUTerm isTy rctx pctx n1 lo
    let (c', n3) ← elabUTerm isTy rctx pctx n2 c
    let (r', n4) ← elabUTerm isTy rctx pctx n3 r
    let (h', n5) ← elabUTerm isTy rctx pctx n4 h
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') (some $h') none), n5)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm ; $r:uterm | $h:uterm | $q:uterm]) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (lo', n2) ← elabUTerm isTy rctx pctx n1 lo
    let (c', n3) ← elabUTerm isTy rctx pctx n2 c
    let (r', n4) ← elabUTerm isTy rctx pctx n3 r
    let (h', n5) ← elabUTerm isTy rctx pctx n4 h
    let (q', n6) ← elabUTerm isTy rctx pctx n5 q
    return (← `(Dllbc.Term.range $a' $lo' (some $c') (some $r') (some $h') (some $q')), n6)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm]) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (lo', n2) ← elabUTerm isTy rctx pctx n1 lo
    let (c', n3) ← elabUTerm isTy rctx pctx n2 c
    return (← `(Dllbc.Term.range $a' $lo' (some $c') none none none), n3)
  | `(uterm| $a:uterm[$lo:uterm ; $c:uterm | $h:uterm]) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (lo', n2) ← elabUTerm isTy rctx pctx n1 lo
    let (c', n3) ← elabUTerm isTy rctx pctx n2 c
    let (h', n4) ← elabUTerm isTy rctx pctx n3 h
    return (← `(Dllbc.Term.range $a' $lo' (some $c') none (some $h') none), n4)
  | `(uterm| &mut ( $x:ident : $τ:uterm ~> $s:uterm )) => do     -- borrow type, snapshot binder
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (s', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 s
    return (← `(Dllbc.Term.borrowT $τ' $s'), n2)
  | `(uterm| &mut ( $τ:uterm ~> $s:uterm )) => do                -- borrow type, S ignores s
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (s', n2) ← elabUTerm isTy rctx pctx n1 s
    return (← `(Dllbc.Term.borrowT $τ' (Dllbc.Term.shiftPure 1 0 $s')), n2)
  | `(uterm| &mut $e:uterm) => do                                -- the borrow TYPE, in any position
    let (e', n) ← elabUTerm isTy rctx pctx next e
    return (← `(Dllbc.Term.borrowT $e' (Dllbc.Term.shiftPure 1 0 $e')), n)
  | `(uterm| &m $e:uterm) => do                                  -- the borrow OPERATION, in any position
    -- M29 β. This row and the one above are the two spellings, and neither asks
    -- which arrow it is under: `&m` in a ⇝ position is a `.borrow`, which
    -- `reflectC` refuses by name ("`&mut` is not in the comptime fragment"), and
    -- `&mut` in a ⇒ position is a `.borrowT`, which `readR` refuses by name
    -- ("a telescope-position form, not a movable value"). Both refusals already
    -- existed and neither was reachable while the surface was deciding; the
    -- exclusions are the KERNEL's, and this is what it takes for the surface to
    -- stop making them on its behalf.
    let (e', n) ← elabUTerm isTy rctx pctx next e
    return (← `(Dllbc.Term.borrow $e'), n)
  | `(uterm| Id $a:uterm $b:uterm $c:uterm) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (b', n2) ← elabUTerm isTy rctx pctx n1 b
    let (c', n3) ← elabUTerm isTy rctx pctx n2 c
    return (← `(Dllbc.Term.idT $a' $b' $c'), n3)
  | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (b', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.lam $(← binderDom (x.getId.toString) τ') $b'), n2)
  | `(uterm| λ ($bs:ulamb,*) { $b:ublk }) => do
    -- Runtime binders, so fresh absolute ids threaded through `next` exactly as
    -- `let` and match patterns mint them — and pushed onto `rctx`, not `pctx`:
    -- the body reaches them through Ω. The body is a ⇒ position whatever
    -- surrounds the node, which is the same asymmetry the seal has.
    let parsed ← bs.getElems.toList.mapM fun (p : TSyntax `ulamb) => match p with
      | `(ulamb| $x:ident : $τ:uterm) => pure (x, τ)
      | _ => Macro.throwErrorAt p "λ: malformed binder (expected `x : τ`)"
    parsed.forM (fun p => checkBinder p.1)
    let (rctx', next', binderSyns) ← elabLamBinders rctx pctx next parsed
    let (b', n) ← elabUBlk false rctx' pctx next' b
    return (← `(Dllbc.Term.lamR [$binderSyns,*] $b'), n)
  | `(uterm| Π ($x:ident : $τ:uterm) → $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (b', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.pi $(← binderDom (x.getId.toString) τ') $b'), n2)
  -- Σ binders are name-checked but carry NO mode. §6 gives modes to "λ, Π, and
  -- `let` alike" — the binders of *parameters* — and a Σ's binder names a
  -- projection, not a parameter: erasing one component of a pair is QTT
  -- territory this phase does not enter. A capital Σ binder is therefore legal
  -- and inert, exactly as a capital binder is inert everywhere under ⇝.
  | `(uterm| Σ ($x:ident : $τ:uterm) → $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (b', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $τ' $b'), n2)
  | `(uterm| Σ ($x:ident : $τ:uterm). $b:uterm) => do
    checkBinder x
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (b', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $τ' $b'), n2)
  | `(uterm| $a:uterm → $b:uterm) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (b', n2) ← elabUTerm isTy rctx ("_" :: pctx) n1 b
    return (← `(Dllbc.Term.pi $a' $b'), n2)
  | `(uterm| &mut ( $x:ident : $τ:uterm )) =>
    Macro.throwErrorAt x s!"&mut ({x.getId} : τ) is not a borrow type — the snapshot-binder spelling is `&mut ({x.getId} : τ ~> S)`, where `S` is what the borrow OWES back and `{x.getId}` is its entry snapshot, bound as pure var 0 in `S`. Without the `~> S` this would read as `&mut` applied to the ascription `({x.getId} : τ)`, which is a borrow of a SEAL — never meaningful, since a seal is not a place. If you meant a plain borrow of the type, write `&mut τ`."
  | `(uterm| ($t:uterm : $u:uterm)) => do
    -- The body is a ⇒ position (term mode) whatever surrounds the node; the
    -- ascribed type is a ⇝ position. That asymmetry is the seal itself.
    let (t', n1) ← elabUTerm false rctx pctx next t
    let (u', n2) ← elabUTerm true rctx pctx n1 u
    return (← `(Dllbc.Term.seal $t' $u'), n2)
  | `(uterm| $c:ident($args,*)) => do                 -- no-space paren: call / ctorApp
    let (args', n) ← elabUList isTy rctx pctx next args.getElems.toList
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
      match rctx.lookup name with
      | some id => return (← `(Dllbc.Term.callV ⟨$(quote id), $(quote name)⟩ [$args',*]), n)
      | none => return (← `(Dllbc.Term.call $(quote name) [$args',*]), n)
  | `(uterm| match $x:ident { $arms,* }) => do
    let s := x.getId.toString
    match rctx.lookup s with
    | none => Macro.throwErrorAt x s!"decl: match scrutinee '{s}' is not a bound runtime variable"
    | some id =>
      let (arms', n) ← elabUArms rctx pctx next arms.getElems.toList
      return (← `(Dllbc.Term.matchE ⟨$(quote id), $(quote s)⟩ none [$arms',*]), n)
  -- M23: `match h : x { … }` — the branch-equation form. One binder for the whole
  -- match (its TYPE is what varies per arm), as in Lean's `match h : x with`.
  | `(uterm| match $h:ident : $x:ident { $arms,* }) => do
    checkBinder h
    let s := x.getId.toString
    match rctx.lookup s with
    | none => Macro.throwErrorAt x s!"decl: match scrutinee '{s}' is not a bound runtime variable"
    | some id =>
      let hName := h.getId.toString
      let (arms', n) ← elabUArms ((hName, next) :: rctx) pctx (next + 1) arms.getElems.toList
      return (← `(Dllbc.Term.matchE ⟨$(quote id), $(quote s)⟩
        (some ⟨$(quote next), $(quote hName)⟩) [$arms',*]), n)
  | `(uterm| if $c:uterm { $t:ublk } else { $f:ublk }) => do  -- §12 sugar → Bool match
    let (c', n1) ← elabUTerm false rctx pctx next c
    let scrutId := n1
    let (t', n2) ← elabUBlk false rctx pctx (n1 + 1) t
    let (f', n3) ← elabUBlk false rctx pctx n2 f
    return (← `(Dllbc.Term.letIn ⟨$(quote scrutId), "__if"⟩ $c'
      (Dllbc.Term.matchE ⟨$(quote scrutId), "__if"⟩ none
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])), n3)
  | `(uterm| if $h:ident : $c:uterm { $t:ublk } else { $f:ublk }) => do
    let (c', n1) ← elabUTerm false rctx pctx next c
    let hName := h.getId.toString
    let rctx' := (hName, n1 + 1) :: rctx
    let (t', n2) ← elabUBlk false rctx' pctx (n1 + 2) t
    let (f', n3) ← elabUBlk false rctx' pctx n2 f
    return (← `(Dllbc.Term.letIn ⟨$(quote n1), "__if"⟩ $c'
      (Dllbc.Term.matchE ⟨$(quote n1), "__if"⟩ (some ⟨$(quote (n1 + 1)), $(quote hName)⟩)
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])), n3)
  | `(uterm| elim $scrut:uterm return $motive:uterm { $arms,* }) =>
    elabUElim isTy rctx pctx next scrut motive arms.getElems
  | `(uterm| elim $scrut:uterm generalizing $goal:uterm { $arms,* }) =>
    elabUGenElim isTy rctx pctx next scrut goal arms.getElems
  | `(uterm| $_:uterm $_:uterm) => do                 -- application spine (juxtaposition)
    let (head, args) := collectAppU stx
    match head with
    | `(uterm| $h:ident) =>
      let hs := h.getId.toString
      let (argTerms, n) ← elabUList isTy rctx pctx next args.toList
      if ctorSet.contains hs && (idxOf? pctx hs).isNone && (rctx.lookup hs).isNone then
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
      let (hterm, n0) ← elabUTerm isTy rctx pctx next head
      let (argTerms, n) ← elabUList isTy rctx pctx n0 args.toList
      let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
      return (out, n)
  | `(uterm| $x:ident) => return (← resolveName rctx pctx x, next)
  | _ => Macro.throwErrorAt stx "decl: unexpected term syntax"

partial def elabUList (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (TSyntax `uterm) → MacroM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (rest, n2) ← elabUList isTy rctx pctx n1 as
    pure (#[a'] ++ rest, n2)

/-- A runtime λ's annotated binders (M27), elaborated as a TELESCOPE: each domain
    is read under the binders to its left and not its own, which is what lets
    `λ(v : &mut List Nat, hfuel : Le (len *v) fuel){ … }` mention `v` in the type
    after it. The domain is a TYPE position (`isTy := true`), so `&mut τ` there is
    the borrow TYPE rather than a borrow expression — the same reading a
    declaration's telescope entry gets from `buildTele`. `binderDom` puts §6's
    comptime marker on a capitalized binder's domain, which is what makes the
    annotation agree with the ascription `piPeel` checks it against. -/
partial def elabLamBinders (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (Ident × TSyntax `uterm) → MacroM (List (String × Nat) × Nat × Array (TSyntax `term))
  | [] => pure (rctx, next, #[])
  | (x, τ) :: rest => do
    let name := x.getId.toString
    let (τT, n1) ← elabUTerm true rctx pctx (next + 1) τ
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
    let (τT, _) ← elabUTerm true rctx [] 0 τ
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
  | `(uarmBody| { $b:ublk }) => elabUBlk false rctx pctx next b
  | `(uarmBody| $e:uterm) => elabUTerm false rctx pctx next e
  | _ => Macro.throwErrorAt body "decl: unexpected arm body"

partial def elabUBlk (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
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
  --     match a `[k]`-hoisted callee's telescope, and a `.callV` minted at the
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
  | `(ublk| fn $name:ident $[[$dec:ident]]? ( $ps,* ) -> $ret:uterm { $body:ublk } ; $rest:ublk) => do
    if isTy then
      Macro.throwErrorAt name "fn: a declaration is a runtime binding (§8: a declaration is a `let`) and cannot appear in a ⇝ position — `pure{ }`, a telescope entry, a return type. Bind it in the program and pass what the ⇝ position needs."
    checkBinder name
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
    let (retT, _) ← elabUTerm true fullRctx [] 0 ret
    let (bodyT, _) ← elabUBlk false fullRctx [] n body
    let decT ← match dec with
      | none => `((none : Option Nat))
      | some d =>
        match idxOf? names.reverse d.getId.toString with     -- reverse: idxOf? is innermost-first
        | some i => `(some $(quote (n - 1 - i)))
        | none => Macro.throwErrorAt d s!"fn: decreasing argument '{d.getId}' is not a parameter of '{name.getId}'"
    let nm := name.getId.toString
    -- The slot. `progBase + next` rather than `next` itself, because a function's
    -- OWN body numbers its parameters from 0 and a binding that collided with one
    -- of its callees' parameters would be read as that parameter. `next` is
    -- consumed here so two `fn`s in a block cannot land on one slot; the arithmetic
    -- is emitted rather than computed, so `progBase` stays the single definition of
    -- where globals live.
    let slot ← `((⟨Dllbc.FnMacro.progBase + $(quote next), $(quote nm)⟩ : Dllbc.Var))
    let (rest', n2) ← elabUBlk isTy rctx pctx (next + 1) rest
    return (← `(Dllbc.Term.letIn $slot
                  (Dllbc.FnMacro.fnElabOrFail
                    (Dllbc.FnDef.mk $(quote nm) [$teleSyns,*] $retT $bodyT $decT))
                  (Dllbc.FnMacro.bindFn $slot $decT $rest')), n2)
  | `(ublk| let $x:ident = $e:uterm ; $rest:ublk) => do
    checkBinder x
    let (e', n1) ← elabUTerm isTy rctx pctx next e
    -- **`let X = e` is a comptime binding** (§6) and needs no macro support: the
    -- mode of a runtime binder IS its `Var`'s name, so the kernel reads it off
    -- the `letIn` this line already emits. Recorded here because the absence of
    -- code is the point — the convention is load-bearing exactly once.
    let name := x.getId.toString
    -- **ONE `let`, both fragments** (M29 α). This row used to branch on the mode:
    -- ⇒ minted a runtime slot and emitted `.letIn`, ⇝ emitted the β-redex
    -- `(λ. rest) e` over a de Bruijn binder. The kernel now reads `.letIn` under
    -- BOTH arrows — ⇝'s reading is that same β, performed at reflection where the
    -- binder depth is known (`reflectC`) — so the surface has nothing left to
    -- decide and the first of the two `isTy` branches is gone.
    --
    -- The de Bruijn spelling was not merely a second encoding, it was a second
    -- SCOPE: a `let` used to push `pctx` in one fragment and `rctx` in the other,
    -- so the same source bound a name in two different places depending on which
    -- macro it sat in. One `rctx` push is now the whole rule.
    --
    -- **And a `let` may shadow a pure binder**, which the merged form has to say
    -- out loud because `resolveName` consults `pctx` FIRST. Left alone,
    -- `λ (x : τ). let x = e ; x` would resolve the tail's `x` to the λ's binder —
    -- the outer one — which is capture by the sort of silent margin this project
    -- keeps finding. Masking the name in `pctx` (the INDEX stays, so every other
    -- de Bruijn reference keeps its level) makes the innermost binder win, which
    -- is what shadowing means. ⇒ bodies had the same hole and are fixed with it.
    let pctx' := pctx.map (fun s => if s == name then shadowedName else s)
    let (rest', n2) ← elabUBlk isTy ((name, n1) :: rctx) pctx' (n1 + 1) rest
    return (← `(Dllbc.Term.letIn ⟨$(quote n1), $(quote name)⟩ $e' $rest'), n2)
  | `(ublk| $p:uterm := $e:uterm ; $rest:ublk) => do
    let (p', n1) ← elabUTerm isTy rctx pctx next p
    let (e', n2) ← elabUTerm isTy rctx pctx n1 e
    let (rest', n3) ← elabUBlk isTy rctx pctx n2 rest
    return (← `(Dllbc.Term.assign $p' $e' $rest'), n3)
  | `(ublk| $e:uterm ; $rest:ublk) => do
    let (e', n1) ← elabUTerm isTy rctx pctx next e
    let (rest', n2) ← elabUBlk isTy rctx pctx n1 rest
    return (← `(Dllbc.Term.seq $e' $rest'), n2)
  | `(ublk| $e:uterm) => elabUTerm isTy rctx pctx next e
  | _ => Macro.throwErrorAt stx "decl: unexpected block syntax"

/-- `elim scrut return motive { arms }` → the matching recursor (§15b). Pure — the
    arm binders (k/ih/h/t) push `pctx`, never `next`. The arm binder DOMAINS are
    DERIVED from the recursor scheme and the motive rather than inferred: a natRec
    `S` step is `λ (k : Nat). λ (ih : P k). …`, and `P k` is built by re-elaborating
    the motive BODY with the motive's own binder at position 0 — de Bruijn-correct
    whatever the arm names its binders. -/
partial def elabUElim (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (scrut motive : TSyntax `uterm) (arms : Array (TSyntax `uelimArm)) : MacroM (TSyntax `term × Nat) := do
  let (scrutT, n1) ← elabUTerm isTy rctx pctx next scrut
  let (motiveT, n2) ← elabUTerm isTy rctx pctx n1 motive
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
  let pOf (leading : List String) : MacroM (TSyntax `term) := do
    pure (← elabUTerm isTy rctx (mName :: leading ++ pctx) n2 mBody).1
  if names.contains "Z" || names.contains "S" then
    let (_, _, zb) ← getArm "Z"; let z := (← elabUBlk isTy rctx pctx n2 zb).1
    let (sb, sih, sbody) ← getArm "S"
    let kName := (sb.get! 0).getId.toString
    let ihName := (sih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf []
    let body := (← elabUBlk isTy rctx (ihName :: kName :: pctx) n2 sbody).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "natRec") $motiveT) $z)
        (Dllbc.Term.lam (Dllbc.Term.const "Nat") (Dllbc.Term.lam $ihDom $body))) $scrutT), n2)
  else if names.contains "True" || names.contains "False" then
    let (_, _, tb) ← getArm "True"; let t := (← elabUBlk isTy rctx pctx n2 tb).1
    let (_, _, fb) ← getArm "False"; let f := (← elabUBlk isTy rctx pctx n2 fb).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motiveT) $t) $f) $scrutT), n2)
  else if names.contains "Nil" || names.contains "Cons" then
    let (_, _, nb) ← getArm "Nil"; let n := (← elabUBlk isTy rctx pctx n2 nb).1
    let (cb, cih, cbody) ← getArm "Cons"
    let hName := (cb.get! 0).getId.toString
    let tName := (cb.get! 1).getId.toString
    let ihName := (cih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf [hName]
    let body := (← elabUBlk isTy rctx (ihName :: tName :: hName :: pctx) n2 cbody).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "listRec") (Dllbc.Term.const "Nat")) $motiveT) $n)
        (Dllbc.Term.lam (Dllbc.Term.const "Nat") (Dllbc.Term.lam (Dllbc.Term.app (Dllbc.Term.const "List") (Dllbc.Term.const "Nat")) (Dllbc.Term.lam $ihDom $body)))) $scrutT), n2)
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
      | _ => Macro.throwError "elim: a Pair motive's binder type must be written as `Σ (x : A) → B`"
    let aT := (← elabUTerm isTy rctx pctx n2 aSyn).1
    -- `B` under its own binder at position 0 — de Bruijn-correct for BOTH uses (the
    -- family `λ x. B` and the arm's second binder domain), whatever the arm names it.
    let bT := (← elabUTerm isTy rctx (bName :: pctx) n2 bSyn).1
    let (pb, _, pbody) ← getArm "Pair"
    let xName := (pb.get! 0).getId.toString
    let yName := (pb.get! 1).getId.toString
    let body := (← elabUBlk isTy rctx (yName :: xName :: pctx) n2 pbody).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "sigmaRec") $aT)
        (Dllbc.Term.lam $aT $bT)) $motiveT)
        (Dllbc.Term.lam $aT (Dllbc.Term.lam $bT $body))) $scrutT), n2)
  else
    Macro.throwError "elim: arms do not match a known recursor (Nat/Bool/List/Σ)"

/-- `elim scrut generalizing goal { arms }` (§18): the motive is
    `λ x. abstractOccurrences scrut goal` — the natural goal with the computed
    subterm abstracted at all its occurrences, mechanically. Bool motives only (the
    count algebra's case-on-`eqb`); Nat/List use the `return` form. -/
partial def elabUGenElim (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (scrut goal : TSyntax `uterm) (arms : Array (TSyntax `uelimArm)) : MacroM (TSyntax `term × Nat) := do
  let (scrutT, n1) ← elabUTerm isTy rctx pctx next scrut
  let (goalT, n2) ← elabUTerm isTy rctx pctx n1 goal
  let armBody (c : String) : MacroM (TSyntax `term) := do
    for arm in arms do
      match arm with
      | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $body:ublk) =>
        if ctor.getId.toString == c then return (← elabUBlk isTy rctx pctx n2 body).1
      | _ => pure ()
    Macro.throwError s!"elim generalizing: missing arm '{c}'"
  let names := arms.filterMap (fun a => match a with
    | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $_:ublk) => some ctor.getId.toString
    | _ => none)
  if names.contains "True" || names.contains "False" then
    let t ← armBody "True"
    let f ← armBody "False"
    let nf := Lean.mkIdent `Dllbc.Std.nfTerm
    let motive ← `(Dllbc.Term.lam (Dllbc.Term.const "Bool")
      (Dllbc.abstractOccurrences ($nf $scrutT) ($nf $goalT)))
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motive) $t) $f) $scrutT), n2)
  else
    Macro.throwError "elim generalizing: only Bool motives supported (§18); Nat/List use the `return` form"

end

end Surface

end Dllbc
