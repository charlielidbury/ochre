import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# Arrays — the carve, the elementization, and the transferred library

Tests for array machinery: the formers (`arrCat`, `aget`, `acons`/`arrRec`, segment
nodes), carving a `&mut Array` into disjoint element/range borrows at concrete and
symbolic indices, and the rejections when a carve's premises fail. In-place array
programs need simultaneous disjoint borrows into one array, and the carve plus
disjointness demands are how the checker grants them soundly.
-/

section

/-!
# Arrays, range places, and proof-licensed carving

The representation layer has no semantic content of its own: every generic `Val`
walker traverses an array node unchanged, because an array node is an ordinary
`ctor`. Only the carve itself is semantic; everything else here is representation.

## The four value forms

    Arr [v₁ … v_c]              an owned flat RUN — value form AND knowledge form
    sym σ                       opaque
    an `arrCat` spine           a stuck neutral
    §segs [§seg [c, b], …]      CARVED (state only; k ≥ 2)

An UNCARVED array carries no wrapper: a single segment is abbreviated to its body,
since the two are the same state. `§segs`/`§seg` are reserved names with no
`ctorSig` entry, so no program can write or match one.

## Element `i` is a subterm

`Arr`'s fields are the elements, flat, so `a[i]` reaches child `i` and `a[lo ; cnt]`
reaches a segment — both subterms. That is what makes a range borrow an ordinary
`&mut` rather than a new aliasing judgment.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd)

namespace Dllbc.Tests.S24Arrays

/-- Type-check a closed term against a closed type in the pure seed. -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasTypeT 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- Normalize a closed pure term to a value. -/
def pv (t : Term) : Term := Pure.nf 4000 t

/-! ## The array former and its literal

    `ctorSig "Arr"`'s field telescope is `T` repeated `n` times at a CONCRETE `n`,
    and `none` at a symbolic one: one cannot write an array literal of unknown
    length. -/

def arr3 : Term := prog defer_check { Arr(3, 1, 2) }
example : chk arr3 prog defer_check { Array 3 Nat } = true := by native_decide
example : chk prog defer_check { Arr() } prog defer_check { Array 0 Nat } = true := by native_decide

-- Arity is the length index: `Arr(3,1,2)` does not inhabit `Array 2 Nat`. This is
-- `checkFields`'s arity branch, reached through the replicated telescope.
example : chk arr3 prog defer_check { Array 2 Nat } = false := by native_decide
example : chk arr3 prog defer_check { Array 4 Nat } = false := by native_decide

-- The ELEMENT type is checked per field, so a `Bool` in a `Nat` array is rejected.
example : chk prog defer_check { Arr(3, True) } prog defer_check { Array 2 Nat } = false := by native_decide

-- A symbolic length has no constructor signature at all — the honest `none`, not a
-- guess. (`n` here is a Π-bound σ, so `natOfVal?` fails on it.)
def arrSymLen : Term := prog defer_check { λ (N : Nat). Arr(3) }
example : chk arrSymLen prog defer_check { Π (N : Nat) → Array N Nat } = false := by native_decide

/-! ## `arrCat` — the split view

    The segment list is state; it lives in Ω. The `arrCat` neutral is knowledge; it
    lives in types and snapshots and never mentions a marker or a hole. So `arrCat`
    computes on run-headed arguments and is a legitimate stuck neutral on σ's. -/

example : (pv prog defer_check { arrCat 2 1 Arr(3, 1) Arr(2) } == pv arr3) = true := by native_decide
example : (pv prog defer_check { arrCat 0 3 Arr() Arr(3, 1, 2) } == pv arr3) = true := by native_decide
example : (pv prog defer_check { arrCat 3 0 Arr(3, 1, 2) Arr() } == pv arr3) = true := by native_decide

-- Associativity is NOT definitional; the carve therefore always produces
-- right-nested spines, and nothing downstream may assume otherwise.
example : (pv prog defer_check { arrCat 2 1 (arrCat 1 1 Arr(3) Arr(1)) Arr(2) } ==
           pv prog defer_check { arrCat 1 2 Arr(3) (arrCat 1 1 Arr(1) Arr(2)) }) = true := by native_decide

-- The stuck case: two σ's have no name for their concatenation, but they do have a
-- term for it, which is all merge and the ⇝ fold need.
def catSyms : Term := prog defer_check { arrCat %(Term.nat 2) %(Term.nat 1) %(Term.sym 0) %(Term.sym 1) }
example : (Pure.nf 100 catSyms == catSyms) = true := by native_decide

-- `arrCat m k a b : Array (Add m k) T` — the empty-run absorption is what makes a
-- DEGENERATE carve's rejoin conversion definitional instead of lemma-mediated.
example : (Pure.nf 200 prog defer_check { arrCat %(Term.nat 0) %(Term.nat 2) %(Term.ctorApp "Arr" []) %(Term.sym 0) } ==
           Term.sym 0) = true := by native_decide

/-! ## `aget` — the ⇝ column at an index place -/

example : (pv prog defer_check { aget Nat 3 0 Arr(3, 1, 2) } == Term.nat 3) = true := by native_decide
example : (pv prog defer_check { aget Nat 3 2 Arr(3, 1, 2) } == Term.nat 2) = true := by native_decide

-- Stuck on a symbolic index and on a symbolic array — a legal neutral either way, so
-- a type may mention `aget i (*v)` while `i` is unknown.
def agetSymIdx : Term := Pure.nf 200 (pv prog defer_check { λ (I : Nat). aget Nat 3 I Arr(3, 1, 2) })
example : (agetSymIdx == Pure.nf 200 agetSymIdx) = true := by native_decide

/-! ## The cons view: `acons` and `arrRec`

    The second view exists so that the quicksort library (`Count`, `Sorted`,
    `Bound`, the order stack) transfers to arrays by replacing `listRec` with
    `arrRec` and `Cons` with `acons`. What is checked here is that the recursor
    computes. -/

example : (pv prog defer_check { acons 2 3 Arr(1, 2) } == pv arr3) = true := by native_decide

-- `alen` by `arrRec` — deliberately, since an array's length is read off its TYPE
-- and never computed from its contents. This exists only to exercise ι.
def alen : Term := prog defer_check {
  λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Nat) Z
      (λ (K : Nat). λ (X : Nat). λ (Xs : Array K Nat). λ (Ih : Nat). S Ih) N A }
example : (pv prog defer_check { alen 3 Arr(3, 1, 2) } == Term.nat 3) = true := by native_decide
example : (pv prog defer_check { alen 0 Arr() } == Term.nat 0) = true := by native_decide

-- A sum, so the recursive arm's element binder is exercised too.
def asum : Term := prog defer_check {
  λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Nat) Z
      (λ (K : Nat). λ (X : Nat). λ (Xs : Array K Nat). λ (Ih : Nat). Add X Ih) N A }
example : (pv prog defer_check { asum 3 Arr(3, 1, 2) } == Term.nat 6) = true := by native_decide

-- Stuck on a symbolic target: no `Arr` to fire on, so the spine is a legal value
-- rather than an error — which is what lets a predicate family over arrays be stated
-- about a σ at all.
def arrRecStuck : Term := Pure.nf 500 (pv prog defer_check { λ (N : Nat). λ (A : Array N Nat). alen N A })
example : (arrRecStuck == Pure.nf 500 arrRecStuck) = true := by native_decide

/-! ## Segments: merge, drop-empty, and the ⇝ fold

    `§segs`/`§seg` have no surface syntax, so these are built as values directly —
    which is the point: they are STATE. -/

def segsOf (l : List (Nat × Val)) : Val :=
  Val.segsNode (l.map (fun p => Val.segNode (Term.nat p.1) p.2))

-- There is no explicit rejoin rule. When the last marker under an array node is
-- gone, the merge normalization collapses the segments and the array is a run
-- again, indistinguishable from one that was never carved. That is what keeps
-- `canonicalize` a decision procedure for Ω-equality.
example : (Val.mergeArrays (segsOf [(1, .ctor "Arr" [Val.nat 3]),
                                    (2, .ctor "Arr" [Val.nat 7, Val.nat 2])])
           == .ctor "Arr" [Val.nat 3, Val.nat 7, Val.nat 2]) = true := by native_decide

-- A three-way split rejoins the same way, and through a nested node: merge is a
-- normalization on the whole value tree, not a top-level step.
example : (Val.mergeArrays (.borrowM 0 (segsOf [(1, .ctor "Arr" [Val.nat 3]),
                                                (1, .ctor "Arr" [Val.nat 1]),
                                                (1, .ctor "Arr" [Val.nat 2])]))
           == .borrowM 0 (.ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2])) = true := by native_decide

-- Drop-empty: a segment of extent Z is deleted, and a single remaining segment is
-- unwrapped to its body — so a carve whose residue is empty leaves NO wrapper behind.
example : (Val.segsNode [Val.segNode (Term.nat 3) (.ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2])]
           == .ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2]) = true := by native_decide

-- A LOANED segment blocks the merge, which is what keeps a carved-and-borrowed array
-- distinguishable from a whole one for exactly as long as the borrow lives.
example : (Val.mergeArrays (segsOf [(1, .ctor "Arr" [Val.nat 3]), (2, .loanM 0)])
           == segsOf [(1, .ctor "Arr" [Val.nat 3]), (2, .loanM 0)]) = true := by native_decide

-- The ⇝ bridge: the fold of a collapsed segment list is its `arrCat` spine.
example : (Val.arrFoldSegs? [Val.segNode (Term.nat 1) (.sym 0), Val.segNode (Term.nat 2) (.sym 1)]
           == some prog defer_check { arrCat %(Term.nat 1) %(Term.nat 2) %(Term.sym 0) %(Term.sym 1) }) = true := by native_decide

-- A suspended array has no snapshot; only a collapsed one does. Both marker
-- kinds are rejected.
example : (Val.arrFoldSegs? [Val.segNode (Term.nat 1) (.loanM 0),
                             Val.segNode (Term.nat 2) (.sym 1)]).isNone = true := by native_decide
example : (Val.arrFoldSegs? [Val.segNode (Term.nat 1) (.bot),
                             Val.segNode (Term.nat 2) (.sym 1)]).isNone = true := by native_decide

-- Folding a run-only split gives back the run itself, by `arrCat`'s ι-rule — the
-- knowledge form of a rejoined array IS the uncarved one, definitionally.
example : (Val.arrFoldSegs? [Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 3]),
                             Val.segNode (Term.nat 2) (.ctor "Arr" [Val.nat 7, Val.nat 2])]
           == some prog defer_check { arrCat %(Term.nat 1) %(Term.nat 2) %(Term.ctorApp "Arr" [Term.nat 3])
                          %(Term.ctorApp "Arr" [Term.nat 7, Term.nat 2]) }) = true := by native_decide
example : (Pure.nf 200 prog defer_check { arrCat %(Term.nat 1) %(Term.nat 2) %(Term.ctorApp "Arr" [Term.nat 3])
                            %(Term.ctorApp "Arr" [Term.nat 7, Term.nat 2]) }
           == .ctorApp "Arr" [Term.nat 3, Term.nat 7, Term.nat 2]) = true := by native_decide

/-! ## Extents read off the value

    A carve's containment premise needs the extent map, which needs the node's
    total extent. Every array-shaped value determines it EXCEPT a bare σ, whose
    extent lives in its `sctx` type instead — so `arrExtentPure?` is partial by
    design and the machine wrapper consults `sctx`. -/

example : (Val.arrExtentPure? (.ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2])
           == some (Term.nat 3)) = true := by native_decide
example : (Pure.nf 100 ((Val.arrExtentPure? (segsOf [(1, .sym 0), (2, .sym 1)])).getD Term.zero)
           == Term.nat 3) = true := by native_decide
example : (Pure.nf 100 ((Val.arrExtentPure? (Val.know
             prog defer_check { arrCat %(Term.nat 1) %(Term.nat 2) %(Term.sym 0) %(Term.sym 1) })).getD Term.zero)
           == Term.nat 3) = true := by native_decide
example : (Val.arrExtentPure? (.sym 0)).isNone = true := by native_decide

/-! ## Every generic walker traverses an array node unchanged

    An array node is an ordinary `ctor`, so `loanIds`, `symIds`, `renumber`,
    `hasStateMarker` and `beq` need no case and MUST NOT get one. A segment list
    with a loan in it is found by the existing traversals — the same code path
    that handles a field-loan collapse, and the reason `refineSym`'s
    knowledge/state assertion is already live at the carve's refinement site. -/

def carvedWithLoan : Val :=
  segsOf [(1, .sym 0), (2, .loanM 7), (1, .sym 1)]

example : (carvedWithLoan.loanIds == [7]) = true := by native_decide
example : (carvedWithLoan.symIds == [0, 1]) = true := by native_decide
-- The marker is in OWNED position of the array node (a segment body is a `ctor`
-- field), so a demand for the owner ends it — the existing rule, no new case.
example : (firstLoanMarker carvedWithLoan == some 7) = true := by native_decide
-- …and it is STATE, so no σ may ever be refined to this tree.
example : Val.hasStateMarker carvedWithLoan = true := by native_decide
example : Val.hasStateMarker (segsOf [(1, .sym 0), (2, .sym 1)]) = false := by native_decide
-- A hole in a segment is state too: `⇒` at a range place leaves one, generalizing
-- take-and-refill from a borrow's payload to a run of an array.
example : Val.hasStateMarker (segsOf [(1, .sym 0), (2, .bot)]) = true := by native_decide

-- `Arr`'s fields are ELEMENTS, flat — so element `i` is child `i`, a subterm.
example : ((.ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2] : Val).symIds == []) = true := by native_decide
example : (Val.renumber id (· + 10) carvedWithLoan == segsOf [(1, .sym 10), (2, .loanM 7), (1, .sym 11)])
    = true := by native_decide

/-! ## `Le` and `Add` live in the kernel

    `Le` and `Add` were library terms (`Std`), but the carve rule's premises are
    stated against them — the containment premise IS a `Le`, and the residue
    premise decomposes an extent with `Add` — and a kernel rule cannot cite a
    library it does not import. Two syntactically different `Add`s would never
    convert, which would break the definitional conversion the residue transition
    relies on. So both moved to `Pure.lean`, with `Std` aliasing them; these two
    tests are the single-source-of-truth check. -/

example : (Pure.kAddFn == Dllbc.Std.addFn) = true := by native_decide
example : (Pure.kLeFn == Dllbc.Std.LeFn) = true := by native_decide
example : (Pure.nf 200 prog defer_check { %(Pure.kAddFn) %(Term.nat 2) %(Term.nat 3) } == Term.nat 5) = true := by native_decide
example : (Pure.nf 200 prog defer_check { %(Pure.kLeFn) %(Term.nat 2) %(Term.nat 3) } == .const "Unit") = true := by native_decide
example : (Pure.nf 200 prog defer_check { %(Pure.kLeFn) %(Term.nat 3) %(Term.nat 2) } == .const "Bot") = true := by native_decide

/-! ## CARVE, at concrete indices

    At concrete indices the containment `Le`s compute to ⊤ — free by conversion —
    so the containment premise needs no annotation and the residue premise is a
    no-op: both sides compute, nothing is refined. -/

/-! ### A carve-and-write lifecycle

    ```rust
    let a = [3, 1, 2];
    let m = &mut a[1 ; 2];
    (*m)[0] := 7;
    ```

    Every step after the carve is a rule that already existed. The carve puts a loan
    marker in a segment body, which is OWNED POSITION of `a`'s value, so the existing
    rule reaches it unchanged; the write through `m` is an ordinary ⇐-fill at an index
    place under a peel. -/

def carveMid : Term := prog{ let a = Arr(3, 1, 2); let m = &m a[1 ; 2]; () }

example : expectEnv carveMid
  [("a", Val.segsNode [Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 3]),
                       Val.segNode (Term.nat 2) (.loanM 0)]),
   ("m", .borrowM 0 (.ctor "Arr" [Val.nat 1, Val.nat 2]))] = true := by native_decide

def carveWritten : Term := prog{
  let a = Arr(3, 1, 2); let m = &m a[1 ; 2]; (*m)[0] := 7; () }

example : expectEnv carveWritten
  [("a", Val.segsNode [Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 3]),
                       Val.segNode (Term.nat 2) (.loanM 0)]),
   ("m", .borrowM 0 (.ctor "Arr" [Val.nat 7, Val.nat 2]))] = true := by native_decide

/-- Rejoin is merge: demand the whole array and the loan ends, the payload plugs
    into its marker, and the segments collapse. `b` is a plain run —
    indistinguishable from one that was never carved. -/
example : expectEnv prog{
    let a = Arr(3, 1, 2); let m = &m a[1 ; 2]; (*m)[0] := 7; let b = a; () }
  [("a", .bot), ("m", .bot),
   ("b", .ctor "Arr" [Val.nat 3, Val.nat 7, Val.nat 2])] = true := by native_decide

/-! ### An element read does not demand the whole array

    A ⇒-read ends every loan marker in owned position within the value it is
    about to move. Reading `a[0]` moves one element, and that element carries no
    marker, so the whole array's loan is not demanded. `m` stays live, holding its
    disjoint half — an element and a disjoint range of one array, both live at
    once, because they are different subterms. -/

example : expectEnv prog{
    let a = Arr(3, 1, 2); let m = &m a[1 ; 2]; (*m)[0] := 7; let x = a[0]; () }
  [("a", Val.segsNode [Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 3]),
                       Val.segNode (Term.nat 2) (.loanM 0)]),
   ("m", .borrowM 0 (.ctor "Arr" [Val.nat 7, Val.nat 2])),
   ("x", Val.nat 3)] = true := by native_decide

/-! ### `get` and `Set` are not primitives

    They are the two arrows at the index place. No kernel primitive is added for
    either. -/

-- ⇐ at an index place: write the element (with the drop of the displaced value
-- forced first — a Nat, so discard).
example : expectEnv prog{ let a = Arr(3, 1, 2); a[0] := 9; () }
  [("a", .ctor "Arr" [Val.nat 9, Val.nat 1, Val.nat 2])] = true := by native_decide

-- ⇒ at an index place: read the element. Copy-on-read applies (Nat is
-- index-kind), so the array keeps it.
example : expectEnv prog defer_check { let a = Arr(3, 1, 2); let x = a[2]; () }
  [("a", .ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2]), ("x", Val.nat 2)]
    = true := by native_decide

-- `&mut a[i]`: an element cursor, an ordinary borrow. The marker parks INSIDE the
-- one-slot run, so the segment body stays at `Array 1 T` while the borrow's payload
-- is the element at `T` — `a[i]` is not `a[i ; 1]`, made structural.
example : expectEnv prog{ let a = Arr(3, 1, 2); let e = &m a[1]; *e := 8; let y = a[1]; () }
  [("a", .ctor "Arr" [Val.nat 3, Val.nat 8, Val.nat 2]), ("e", .bot), ("y", Val.nat 8)]
    = true := by native_decide

/-! ### Take-and-refill at a range place

    Generalized from "the payload of a borrow" to "a run of an array": between the
    take and the refill the array holds a hole of known extent, no rule reads it,
    and the refill is its one legal successor. That is how a rotation or a memmove
    is written without a copy. -/

example : expectEnv prog{ let a = Arr(3, 1, 2);
                           let run = a[1 ; 2];
                           a[1 ; 2] := run;
                           let w = a[0]; () }
  [("a", .ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2]), ("run", .bot), ("w", Val.nat 3)]
    = true := by native_decide

/-! ### Carve of carve collapses definitionally

    `carve_carve : (a[lo₁ ; cnt₁])[lo₂ ; cnt₂] ≡ a[Add lo₁ lo₂ ; cnt₂]` holds with
    no lemma at all: without it, every sub-slice of a sub-slice would accumulate a
    chain of offsets no conversion sees through. It holds because the residue
    premise hands back LEAF-RELATIVE offsets, so a nested carve is an ordinary
    carve inside the segment it landed in, and the offsets never compose into a
    chain. Needing a lemma here would mean the residue premise is implemented
    wrong — so this passing is evidence about that premise, not about nesting. -/

example : expectEnv
    prog{ let a = Arr(3, 1, 2, 7, 5);
           let m = &m a[1 ; 3];
           let inner = &m (*m)[1 ; 2];
           (*inner)[0] := 9;
           let b = a;
           () }
  [("a", .bot), ("m", .bot), ("inner", .bot),
   ("b", .ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 9, Val.nat 7, Val.nat 5])]
    = true := by native_decide

/-! ### The rejections, each falling out of a premise rather than a check -/

-- OVERLAP — premise (1), and the shape it actually takes. After `&mut a[0 ; 3]` the
-- extent map is `[(0,3,loaned ℓ₁), (3,rest,owned)]`, and [2,5) is contained in NEITHER
-- leaf: it straddles the boundary. So the rejection needs no owned-versus-loaned test
-- at all — two segments cannot overlap, so a range crossing a segment boundary has no
-- leaf, full stop. No arithmetic was performed and no proof could have helped.
example : expectErr prog defer_check { let a = Arr(3, 1, 2, 7, 5);
                           let p = &m a[0 ; 3];
                           let q = &m a[2 ; 3];
                           () }
  "no leaf" = true := by native_decide

-- OUT OF RANGE — premise (2) has no inhabitant and none can be supplied, because
-- `Le (Add lo cnt) n` computes to ⊥.
example : expectErr prog defer_check { let a = Arr(3, 1, 2); let m = &m a[1 ; 3]; () }
  "containment obligation" = true := by native_decide
example : expectErr prog defer_check { let a = Arr(3, 1, 2); let x = a[3]; () }
  "containment obligation" = true := by native_decide

-- A HOLE is not owned. `⇒` at a range place takes the run out and leaves one, and
-- until the ⇐-refill closes it no carve may split across it.
example : expectErr prog defer_check { let a = Arr(3, 1, 2);
                           let run = a[1 ; 2];
                           let x = a[1];
                           () }
  "meets a hole" = true := by native_decide

/-! ### A contained request demand-ends rather than rejecting

    Two cases hide under "a loaned leaf", and they behave differently for a reason
    that predates arrays. A request that STRADDLES a boundary has no leaf and is
    rejected (above). A request CONTAINED in a loaned leaf is the situation
    `&mut x` twice already creates, and the existing whole-place rule resolves it
    by ending: `let p = &mut x; let q = &mut x;` is accepted, with `p` killed and
    any later use of it stuck. The array rule follows suit: every demand collapses
    first. Two live overlapping mutable borrows remain unrepresentable; the second
    one is rejected at the first use of the dead borrow, not at its creation. -/

example : expectEnv prog{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &m a[0 ; 3];
                           let q = &m a[1];
                           *q := 6;
                           let b = a;
                           () }
  [("a", .bot), ("p", .bot), ("q", .bot),
   ("b", .ctor "Arr" [Val.nat 3, Val.nat 6, Val.nat 2, Val.nat 7, Val.nat 5])]
    = true := by native_decide

-- …and the killed borrow is stuck at its next use, which is where the rejection
-- actually lands.
example : expectErr prog defer_check { let a = Arr(3, 1, 2, 7, 5);
                           let p = &m a[0 ; 3];
                           let q = &m a[1];
                           (*p)[0] := 4;
                           () }
  "⊥" = true := by native_decide


/-! ## The symbolic carve

    Two range borrows of one array, live at once, with a symbolic length. They coexist
    not because the checker believes an aliasing argument but because, after the carve,
    they are literally different subterms of one value tree — and the suspension
    machinery already knows what to do with those. -/

/-- `halves`, checked end to end.

    ```rust
    fn halves (a : &mut Array n Nat, k : Nat, h : Le k n) = {
      let l = &mut (*a)[Z ; k];
      let r = &mut (*a)[k ; rest];
    }
    ```

    Read the two carves against each other, because the contrast IS the design. The
    FIRST does everything: its obligation is `Le Z Z × Le (Add Z k) (Add Z n)`, which
    computes to `⊤ × Le k n` and is discharged by `h`; its residue transition solves
    `n ≡ Add k rest` with `n` flex, refining the LENGTH INDEX everywhere; and its body
    split refines `σ := arrCat k rest σ_l σ_r`. The SECOND does nothing at all — its
    request IS the leaf, so no split and no refinement fire, and no evidence is
    demanded because `Le b b` and `Le x x` are `LeRefl`. That asymmetry is the general
    shape of an exhaustive split, and it is why this costs ONE proof rather than two. -/
def halves : Term := prog{
  fn Halves (n : Nat, k : Nat, H : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k | H];
    let r = &m (*a)[k ; ..];
    () };
  () }

example : progOk halves = true := by native_decide

/-! ### Disjointness as a demand rather than an observation

    Disjointness is asserted by what a body can DO under the invariant, rather
    than by reading the machine's internal loan ids. Both sub-borrows stay LIVE:
    a second borrow of an overlapping place demand-ends the first, so using `l`
    after `r` has been taken is possible exactly when the two do not overlap. The
    pair below says the segments are SIMULTANEOUSLY USABLE. -/

def halvesBoth : Term := prog{
  fn HalvesBoth (n : Nat, k : Nat, H : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k | H];
    let r = &m (*a)[k ; ..];
    let y = *r;
    *r := y;
    let x = *l;
    *l := x;
    () };
  () }
example : progOk halvesBoth = true := by native_decide

-- THE TWIN, one character of range apart: carve the SAME segment twice. The
-- second demand-ends the first, so the later use of `l` peels a vacant slot —
-- which is the invariant biting, and what says the acceptance above is about the
-- ranges being disjoint and not about carving twice being allowed.
def halvesSame : Term := prog defer_check {
  fn HalvesSame (n : Nat, k : Nat, H : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k | H];
    let r = &m (*a)[Z ; k | H];
    let y = *r;
    *r := y;
    let x = *l;
    *l := x;
    () };
  () }
example : progRejects halvesSame "cannot peel a vacant slot" = true := by
  native_decide

-- The final Ω of a single-path body is not directly observable: entering a body
-- with a TELESCOPE requires seeding it, and such a body is entered only inside
-- an isolated frame whose Ω is discarded by design. So an invariant once read
-- off Ω is restated as a demand form where one exists (`halvesBoth`/`halvesSame`,
-- `threeWayAll`), or recorded lost with the reason where none does (`readSame`).

/-! ### Why the exit-type audit converts, and what it cost

    The obligation type for `a` is `Array n Nat`; the collapsed payload's
    snapshot is `arrCat σ_l′ σ_r′` at `Array (Add σₖ rest) Nat`; and these convert
    DEFINITIONALLY, because the residue transition refined `σₙ := Add σₖ rest` at
    the carve. Had the carve computed `rest := Sub n k` instead, this final
    conversion would have needed `Add k (Sub n k) ≡ n`, which is not definitional
    and would have required a cited lemma at every audit of every array-mutating
    function in the program.

    The `progOk` above IS that conversion succeeding. One implementation detail is
    load-bearing: the extent sum must be RIGHT-NESTED with no trailing `Z`. `Add`
    recurses on its first argument, so `Add rest Z` is stuck the moment `rest` is
    symbolic, and `Array (Add k (Add rest Z))` never converts with
    `Array (Add k rest)`. A version of the audit with the trailing zero failed
    this exact test, not because the residue premise was wrong but because the
    sum was shaped wrong. -/

/-! ### Negative controls, one per premise -/

-- Premise (2), UNPROVED BOUND — the interesting rejection: the program is not
-- wrong, it is unjustified. Same body, evidence not cited.
def noEvidence : Term := prog defer_check {
  fn NoEvidence (n : Nat, k : Nat, H : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k]; () };
  () }
example : progRejects noEvidence "containment obligation" = true := by native_decide

-- Premise (2), WRONG EVIDENCE. `h : Le n k` is a perfectly good term of a perfectly
-- good type; it is just not the obligation. The evidence's TYPE is the selector, so a
-- term of the wrong type selects no leaf.
def wrongEvidence : Term := prog defer_check {
  fn WrongEvidence (n : Nat, k : Nat, H : Le n k, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k | H]; () };
  () }
example : progRejects wrongEvidence "containment obligation" = true := by native_decide

-- Premise (3), RIGID LENGTH. The leaf's extent is a compound neutral rather than
-- a flexible σ, so `m ≡ Add lo' (Add cnt rest)` has no solution by refinement.
-- Rejected with the remedy in the message: take the length as a parameter.
def rigidLength : Term := prog defer_check {
  fn RigidLength (p : Nat, q : Nat, k : Nat, H : Le k (Add p q),
                  a : &mut (Array (Add p q) Nat)) -> Unit {
    let l = &m (*a)[Z ; k | H]; () };
  () }
example : progRejects rigidLength "premise (3) is stuck" = true := by native_decide
example : progRejects rigidLength "Take the length as a telescope PARAMETER"
    = true := by native_decide

/-! ### `refineSym`'s target list is the checklist

    The carve's index refinement must reach every σ-bearing component. A carve
    whose refinement reached every component except one would not fail loudly;
    it would silently corrupt whatever depends on that component. The warning
    applies to every σ-bearing field `refineSym` sweeps.

    A function that recurses on fuel and carves on the way checks. -/

def walk : Term := prog{
  fn Walk [fuel] (fuel : Nat, n : Nat, k : Nat, H : Le k n, a : &mut (Array n Nat)) -> Unit {
    match fuel {
      Z => (),
      S(f2) => { let l = &m (*a)[Z ; k | H]; Walk(f2, k, k, LeRefl k, l) }
    } };
  () }
example : progOk walk = true := by native_decide

/-! ### Recursing on a carved sub-slice, declined at the hint

    Declaring the array itself (rather than fuel) as the decreasing argument and
    recursing on a carved sub-slice is refused by the macro at the hint: a hint
    naming a BORROW has no recursor form, and the lowering declines it. -/

def walkArr : Term := prog defer_check {
  fn WalkArr [a] (fuel : Nat, n : Nat, k : Nat, H : Le k n, a : &mut (Array n Nat)) -> Unit {
    match fuel {
      Z => (),
      S(f2) => { let l = &m (*a)[Z ; k | H]; WalkArr(f2, k, k, LeRefl k, l) }
    } };
  () }
-- The twin differs from `walk` in the HINT ALONE — `[a]` where `walk` says
-- `[fuel]`, same telescope, same body, character for character — so what these two
-- verdicts isolate is the hint and nothing else.
example : progRejects walkArr FnMacro.fnRefusedNeedle = true := by native_decide
example : progRejects walkArr "§12 decision 8" = true := by native_decide
-- …and it can never pass green: the sentinel fires at the BINDING, so a refused
-- function that nothing calls still fails.
example : progOk walkArr = false := by native_decide

/-! ### Recursion cannot decrease through a CARVED array payload

    The guard compares the actual against the parameter's current snapshot by
    `strictSubterm`, which counts only CONSTRUCTOR fields as subterms and
    deliberately refuses application spines. A carve's body split refines the
    payload σ to an `arrCat` SPINE, so from that moment no sub-slice is a
    structural predecessor of its parent. Recursion over sub-slices with no fuel
    is therefore closed: either the guard learns that `arrCat`'s array arguments
    are subterms of their concatenation, or array recursion stays fuel-carried. -/

/-! ### A segment's loan captured by a call, without the parent riding along

    `processArgs` captures per-argument-borrow loans and nothing in it walks to a
    parent or a sibling. Here that property meets an array segment: the callee
    receives the left half; the right half stays borrowed by the caller; the
    parent `a` is audited normally and its untouched segment never entered the
    call. The frame is not described — it is simply still there. -/

def touch : Term := prog{
  fn Touch (p : Nat, l : &mut (Array p Nat)) -> Unit { () };
  () }
example : progOk touch = true := by native_decide

def callSeg : Term := prog{
  fn Touch (p : Nat, l : &mut (Array p Nat)) -> Unit { () };
  fn CallSeg (n : Nat, k : Nat, H : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k | H];
    let r = &m (*a)[k ; ..];
    Touch(k, l);
    () };
  () }
example : progOk callSeg = true := by native_decide

/-! ### The residue has no surface name

    The second borrow after a carve, `&mut (*a)[k ; rest]`, mentions a `rest`
    that is a σ the CHECKER minted inside the residue premise — machine-internal,
    with no binder any program can write.

    `a[lo ; ..]` names the residue as a place: it reads the residue's extent off
    the extent map, where the residue premise already parked it as a GIVEN. No
    arithmetic, no new obligation, and not the `Sub` that index premises ban.

    What `..` does NOT solve is a CALL that must pass the residue's length as an
    argument — a callee like `merge_into (l : &mut Array p Nat, r : &mut Array q
    Nat)` needs a `q`, and `q` is that same unnameable σ. `callSeg` above passes
    only the left half for exactly this reason. Three routes, none free: let a
    place's extent be a comptime term (but the extent map is state, so ⇝ would be
    reading state); let the carve BIND its residue in the surface (`let (l, rest)
    = …`, a real binder form); or have such callees take a Σ-typed slice,
    `Σ (c : Nat). &mut (Array c T)`. The third needs no new machinery and is
    probably the answer; it is untested here. -/

/-! ## Multi-marker collapse, and the differential over array bodies

    A segment list can hold several markers at once, so a partial collapse is
    easy to write by accident. Each executing former must preserve full
    collapse, and a negative test per rule branch should cover the multi-marker
    case specifically. -/

/-! ### Three markers in one node, collapsed by one demand

    A group's release touches TWO markers in one owner's tree at arity two;
    owner demand is the same story at arity three: `readR`'s move ends the
    leftmost marker and retries until none is left, so the collapse is total by
    construction rather than by a loop someone wrote. Both granularities are
    exercised, because they park markers in different places — a range marker IS
    the segment body, an element marker sits INSIDE the one-slot run. -/

example : expectEnv prog{
    let a = Arr(3, 1, 2);
    let p = &m a[0 ; 1]; let q = &m a[1 ; 1]; let r = &m a[2 ; 1];
    (*p)[0] := 7; (*q)[0] := 8; (*r)[0] := 9;
    let b = a; () }
  [("a", .bot), ("p", .bot), ("q", .bot), ("r", .bot),
   ("b", .ctor "Arr" [Val.nat 7, Val.nat 8, Val.nat 9])] = true := by native_decide

example : expectEnv prog{
    let a = Arr(3, 1, 2);
    let p = &m a[0]; let q = &m a[1]; let r = &m a[2];
    *p := 7; *q := 8; *r := 9;
    let b = a; () }
  [("a", .bot), ("p", .bot), ("q", .bot), ("r", .bot),
   ("b", .ctor "Arr" [Val.nat 7, Val.nat 8, Val.nat 9])] = true := by native_decide

/-! ### A marker in the middle of three segments must block the fold

    A node still holding a marker must not fold: it has no snapshot, so `hasType`
    rejects it at the one place that judges. An earlier `foldr`-over-`Option`
    implementation of `arrFoldSegs?` conflated "this body is not owned" with
    "there is no accumulator yet" — both are `none` — so a marker followed by an
    owned segment had its `none` silently overwritten by the earlier segment, and
    the fold returned a SHORTER array as if it were the whole one. A marker LAST
    or FIRST does not expose this; only a marker in the MIDDLE of three does. Now
    a structural recursion where the two `none`s cannot be confused. -/

example : (Val.arrFoldSegs? [Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 7]),
                             Val.segNode (Term.nat 1) (.loanM 0),
                             Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 9])]).isNone
    = true := by native_decide

-- …and the three positions a marker can take, so the branch cannot be lost again.
example : (Val.arrFoldSegs? [Val.segNode (Term.nat 1) (.loanM 0),
                             Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 9])]).isNone
    = true := by native_decide
example : (Val.arrFoldSegs? [Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 7]),
                             Val.segNode (Term.nat 1) (.bot)]).isNone
    = true := by native_decide

-- The positive control the bug would also have broken: three owned segments fold to
-- the full three-element run, not a prefix of it.
example : ((Val.arrFoldSegs? [Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 7]),
                              Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 8]),
                              Val.segNode (Term.nat 1) (.ctor "Arr" [Val.nat 9])]).map
             (Pure.nf 200)
           == some (.ctorApp "Arr" [Term.nat 7, Term.nat 8, Term.nat 9])) = true := by native_decide

/-! ### The differential harness, given array bodies

    The multi-marker collapse is precisely the bug class a per-rule-branch
    negative test exists to catch, so the differential harness needs array
    bodies too: for a `checkFn`-accepted caller, its CONCRETE final environment
    (executing mode — calls run the callee's real body) is a σ-instance of some
    accepted SYMBOLIC path's final environment (checking mode — calls use the
    signature rule). -/

/-- A carved segment handed to a call, then the whole array demanded back. -/
def arrCaller1 : Term := prog{
  fn Fill1 (l : &mut (Array 1 Nat)) -> Unit { (*l)[0] := 9; () };
  let a = Arr(3, 1, 2); let s = &m a[1 ; 1]; Fill1(s); let b = a; () }

/-- TWO carved segments, one passed to each of two calls, then rejoined: several
    captured loans in one owner. -/
def arrCaller2 : Term := prog{
  fn Bump (l : &mut (Array 2 Nat)) -> Unit { (*l)[0] := 7; (*l)[1] := 8; () };
  let a = Arr(3, 1, 2, 7);
  let s = &m a[0 ; 2]; let t = &m a[2 ; 2];
  Bump(s); Bump(t);
  let b = a; () }

/-- Inline carving with no call at all: the residues never leave, so there is nothing
    for a group to forget. -/
def arrCaller3 : Term := prog{
  let a = Arr(3, 1, 2);
  let p = &m a[0 ; 1]; let q = &m a[1 ; 2];
  (*p)[0] := 5; (*q)[1] := 6;
  let b = a; () }

def arrCallers : List Term := [arrCaller1, arrCaller2, arrCaller3]

example : arrCallers.all (fun b => progOk b) = true := by native_decide

example : arrCallers.all (fun b => Dllbc.Tests.S9Diff.diffV2 b)
    = true := by native_decide

/-! ### The simulation relation needed an array case

    Checking mode ends with

        b ↦ Arr⟨1 ▷ [3], 1 ▷ σ₀, 1 ▷ [2]⟩

    where executing mode ends with `b ↦ [3, 9, 2]`. Both are right. Merge
    concatenates runs but leaves a σ body alone — it must, since two σ's have no
    run to concatenate — so a checking-mode group release, which mints a fresh
    existential at the segment's owed type, blocks exactly the rejoin the
    concrete run performs. The values agree; the TREES do not.

    So the relation learns the fold: an array is compared up to its snapshot,
    which means splitting the concrete run by the symbolic extents and matching
    segment-wise (`matchVal`'s `§segs`-vs-run case, S9Diff). This is the known
    over-approximation of a group releasing atomically where the concrete
    machine ends lazily, arriving for arrays — the old relation was structural,
    and arrays are the first values in the calculus whose state form is coarser
    than their value. -/

/-! ## Symbolic element access, the exhaustive split, and where it stops

    What range places replace: evidence threaded through every swap site as
    `Le (S i) j`-shaped bounds. Range places take the same terms and give them
    their real job, so the obligation at `a[i]` had better BE that term. -/

/-! ### Premise (2) must be spelled the way a program writes it

    Two adjustments, neither changing what the premise MEANS, both required for it to
    be dischargeable at all.

    First, the end of the range. `Add` recurses on its FIRST argument, so `Add lo cnt`
    is stuck whenever `lo` is symbolic — and at every `a[i]` the count is literally 1,
    making the obligation read `Le (Add i (S Z)) n`. No program writes that, and no
    lemma in the library produces it. `S i` denotes the same number and is
    definitionally a constructor tree. A concrete count is therefore unrolled
    into successors; a symbolic one keeps `Add`, where it computes.

    Second, the containment is stated LEAF-RELATIVELY when the leaf-relative offset is
    already known. `Le` computes by double `natRec`, so `Le (Add b cnt) (Add b m)` is
    stuck on a symbolic `b` and never converts with the `Le cnt m` a program can
    supply. Premise (3)'s own logic is that offsets are leaf-relative; premise (2)
    should be too. -/

def idxCited : Term := prog{
  fn IdxCited (n : Nat, i : Nat, H : Le (S i) n, a : &mut (Array n Nat)) -> Unit {
    let e = &m (*a)[i | H]; () };
  () }
example : progOk idxCited = true := by native_decide

-- The same bound serves a width-1 RANGE, so the two spellings of "one slot" agree on
-- what they demand even though they differ on what they hand back.
def rng1Cited : Term := prog{
  fn Rng1Cited (n : Nat, i : Nat, H : Le (S i) n, a : &mut (Array n Nat)) -> Unit {
    let e = &m (*a)[i ; 1 | H]; () };
  () }
example : progOk rng1Cited = true := by native_decide

-- Not vacuous: the bound is the one thing being checked, and a weaker one fails.
def idxWeakBound : Term := prog defer_check {
  fn IdxWeakBound (n : Nat, i : Nat, H : Le i n, a : &mut (Array n Nat)) -> Unit {
    let e = &m (*a)[i | H]; () };
  () }
example : progRejects idxWeakBound "containment obligation" = true := by native_decide

/-! ### The exhaustive two-way split, with a call

    A `split_at_mut` shape: carve the left half against a cited bound, take the
    rest with `..`, and hand one half to a callee. The residues never leave —
    `σ_r` is the same σ before and after the call — so the frame is not
    described, it is simply still there. -/

def threeWayTouch : Term := prog{
  fn ThreeWayTouch (p : Nat, l : &mut (Array p Nat)) -> Unit { () };
  () }
example : progOk threeWayTouch = true := by native_decide

def splitTwo : Term := prog{
  fn ThreeWayTouch (p : Nat, l : &mut (Array p Nat)) -> Unit { () };
  fn SplitTwo (n : Nat, i : Nat, H1 : Le i n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i | H1];
    let r = &m (*a)[i ; ..];
    ThreeWayTouch(i, l);
    () };
  () }
example : progOk splitTwo = true := by native_decide

/-! ### A three-way split does not check, because the residue has no name

    A three-way carve — left half, pivot slot, right half — needs the partition
    leaf to produce its pivot index together with two carve licenses:

    ```
    let l = &mut (*v)[Z    ; i | h];   -- obligation `Le i n`        — writable
    let p = &mut (*v)[i];             -- obligation `Le 1 rest`     — NOT writable
    let r = &mut (*v)[S i ; ..];
    ```

    The second carve is base-aligned into the residue leaf, so the containment
    premise asks for `Le 1 rest` — leaf-relative and correct, the sharpest
    possible statement of the obligation. But `rest` is the σ the residue
    premise minted inside the FIRST carve. It has no binder, so no term of that
    type can be written, and no license the partition returns can mention it
    either.

    So `..` is not enough: it names the residue as a PLACE, which is what a
    second borrow needs, but not the residue's LENGTH, which any evidence about
    the residue, and any call taking the residue, both need. The same wall stops
    a callee like `merge_into (r : &mut Array q Nat)` from being callable.

    Three routes. (a) Let the program SUPPLY the residue rather than have the
    checker mint it — `a[lo ; cnt ; rest | h]`, with the residue premise solving
    `m ≡ add lo' (add cnt rest)` against the supplied term instead of a fresh σ.
    This keeps that premise exactly as it is (still a solution transition, still
    no `Sub`) and reduces to the current behaviour when omitted. (b) Let the
    carve BIND its residue in the surface. (c) Σ-typed slices,
    `Σ (c : Nat). &mut (Array c T)` — needs new machinery: `seedTelescope` has no
    case for a borrow under a type constructor, so the parameter is rejected by
    `readC`, and `collectResultBorrows` has no dependent-Σ case for returning
    one.

    (a) is the smallest and the one that fits the existing rule. Recorded rather
    than built, since it changes the surface of the checker's one new rule. -/

def pivotCarve : Term := prog defer_check {
  fn PivotCarve (n : Nat, i : Nat, H1 : Le i n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i | H1];
    let p = &m (*a)[i];
    let r = &m (*a)[S i ; ..];
    () };
  () }
example : progRejects pivotCarve "containment obligation" = true := by native_decide

/-! ## The Σ-typed slice, a runtime-length slice

    `Σ (c : Nat). &mut (Array c T)` is an ordinary Σ over a borrow, well-formed
    as a TYPE. But a borrow stored under a type constructor had never reached a
    telescope entry, so the machine needed two attempts.

    ATTEMPT 1, the callee side (`seedTelescope`): the slot holds a genuine pair,
    so the length is a σ the body can name and the borrow carries an ordinary
    obligation.

    ATTEMPT 2, the caller side (`processArgs`): the actual is a pair, the
    capture is the borrow's loan, the length is checked like any other
    argument.

    Both work, and neither solves the residue problem: a caller must PRODUCE the
    length to construct the pair, so the Σ-slice serves exactly the slices whose
    length was already nameable — the case that never needed it. -/

def sigSlice : Term := prog{
  fn SigSlice (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit { () };
  () }
example : progOk sigSlice = true := by native_decide

-- The callee can DESTRUCTURE it: an owned match hands back the length and the borrow,
-- and inside the body the length is an ordinary nameable term.
def useSlice : Term := prog{
  fn UseSlice (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit {
    let Pair(c, sl) = s;
    () };
  () }
example : progOk useSlice = true := by native_decide

-- The `let Pair(c, sl) = s;` sugar desugars to exactly the `match` below — same
-- ids, same names, same `Term` — which is what `rfl` says here. `Tests.Sugar`
-- proves the desugaring rule in general; this checks it on real corpus code.
example : useSlice = prog{
  fn UseSlice (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit {
    match s { Pair(c, sl) => () } };
  () } := by rfl

def sliceTouch : Term := prog{
  fn SliceTouch (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit { () };
  () }
example : progOk sliceTouch = true := by native_decide

-- A caller passing a slice whose length it can NAME: green, end to end.
def sigCallerOk : Term := prog{
  fn SliceTouch (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit { () };
  fn SigCallerOk (n : Nat, i : Nat, H1 : Le i n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i | H1];
    let r = &m (*a)[i ; ..];
    SliceTouch(Pair(i, l));
    () };
  () }
example : progOk sigCallerOk = true := by native_decide

/-! ### …and the residue still cannot be passed, which settles route (c)

    The only length in scope is `i`, and for the residue it is the wrong one. The
    checker says so rather than silently accepting — so there is no smuggling the
    residue through with a length that happens to be nameable. And there is no right
    term to write, because the residue's length is the σ premise (3) minted. -/

def sigCallerWrong : Term := prog defer_check {
  fn SliceTouch (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit { () };
  fn SigCallerWrong (n : Nat, i : Nat, H1 : Le i n, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i | H1];
    let r = &m (*a)[i ; ..];
    SliceTouch(Pair(i, r));
    () };
  () }
example : progRejects sigCallerWrong "does not have its parameter type"
    = true := by native_decide

-- A second, independent wall for route (c): a RECURSIVE slice-taking callee needs a
-- fuel bound ABOUT the slice's length, and that length lives inside the Σ where no
-- telescope entry can mention it. Nesting the proof inside too is where it goes, and
-- that is a second level the machinery does not have.
def recSlice : Term := prog defer_check {
  fn RecSlice [fuel] (fuel : Nat, s : Σ (c : Nat). Σ (H : Le c fuel). &mut (Array c Nat)) -> Unit {
    () };
  () }
example : progRejects recSlice "only valid at a telescope position" = true := by native_decide

/-! ### Route (a)'s payoff, verified on the arithmetic alone

    Supplying the residue does not merely NAME it — it makes the obligation that could
    not be written disappear. After `σ_rest := S j` the pivot carve's leaf-relative
    obligation `Le 1 σ_rest` reduces to `Le Z j`, which is ⊤ and needs no evidence at
    all. Stuck while the residue is a bare σ; free the moment it has a shape. -/

example : (Pure.nf 300 prog defer_check { %(Pure.kLeFn) %(Term.nat 1) %(Term.ctorApp "S" [.sym 0]) } == .const "Unit")
    = true := by native_decide
example : (Pure.nf 300 prog defer_check { %(Pure.kLeFn) %(Term.nat 1) %(Term.sym 0) } == .const "Unit")
    = false := by native_decide

/-! ## Route (a) — the program supplies the residue, and the three-way carve unblocks

    `a[lo ; cnt ; rest | h]` supplies the residue premise's extent instead of
    letting the checker mint a σ no binder can name. That premise is otherwise
    untouched — the same solution transition, still no `Sub` — and omitting the
    slot restores the minting behaviour exactly.

    This is an OPTIONAL surface element that reifies something the checker
    already knows, declared rather than inferred, costing nothing when absent —
    the same house pattern as naming a decreasing position or a branch equation.

    The ordering is the trick: the supplied equation is solved BEFORE the
    containment premise is formed, so the obligation is stated over a decomposed
    extent — and then it often computes away entirely, since `Le a b` is
    precisely the assertion that `b` decomposes as `a` plus something. -/

/-- THREE-WAY carve: left half | pivot slot | right half, all three live at once.

    ```rust
    let l = &mut (*v)[Z    ; i ; S j | LeAdd i (S j)];
    let p = &mut (*v)[i    ; 1 ; j];        -- obligation ⊤; no evidence needed
    let r = &mut (*v)[S i  ; ..];           -- degenerate
    ```

    The pivot element sits between two live borrows as a third segment that
    neither call can see. The pivot is in its final position and must not move;
    the calculus enforces that, for free, by the same mechanism that keeps the
    halves apart.

    The two obligations are the two predicted. The first is `Le i (Add i (S j))`
    — `LeAdd`, already in the library. The second is `Le 1 (S j)`, which
    reduces to `Le Z j` and then to ⊤, so **the carve that could not be written at all
    now needs no evidence whatsoever**. -/
def threeWay : Term := prog{
  fn ThreeWay (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
               a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let p = &m (*a)[i ; 1 ; j];
    let r = &m (*a)[S i ; ..];
    () };
  () }
example : progOk threeWay = true := by native_decide

-- …and the same conversion at THREE segments, which is where the invariant is
-- doing real work: `[Z ; i ; S j]`, `[i ; 1 ; j]` and `[S i ; ..]` are pairwise
-- disjoint by the decomposition the carves cite, and all three stay usable.
def threeWayAll : Term := prog{
  fn ThreeWayAll (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                  a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let p = &m (*a)[i ; 1 ; j];
    let r = &m (*a)[S i ; ..];
    let z = *r;
    *r := z;
    let w = *p;
    *p := w;
    let x = *l;
    *l := x;
    () };
  () }
example : progOk threeWayAll = true := by native_decide

-- The pivot carve needs NO cited evidence, which is route (a)'s second payoff and the
-- reason it beats merely naming the residue: `Le 1 rest` was unwritable, and after
-- `rest := S j` the obligation is ⊤. Dropping `LeAdd` from the FIRST carve, whose
-- obligation does not compute away, is still rejected.
def threeWayNoFirstEv : Term := prog defer_check {
  fn ThreeWayNoFirstEv (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                        a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeRefl i | Heq];
    let p = &m (*a)[i ; 1 ; j];
    () };
  () }
example : progRejects threeWayNoFirstEv "containment obligation" = true := by native_decide

/-- The decomposition citation's negative control. Supplying a residue asserts
    that the leaf's extent decomposes as `Add cnt rest`. When the extent is a
    telescope parameter's σ that assertion is a constraint on this function's
    CALLERS, and the residue premise refuses to impose it by unification — the
    program must CITE the equation, like every other cross-boundary constraint.
    Without the check, a caller instantiating `n = 2` with `i = j = 5` would
    check and then get STUCK when executed. -/
def threeWayUncited : Term := prog defer_check {
  fn ThreeWayUncited (n : Nat, i : Nat, j : Nat, a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeAdd i (S j)];
    () };
  () }
example : progRejects threeWayUncited "may not impose it by refining" = true := by
  native_decide

-- …and the citation's TYPE is what licenses: a well-typed equation about the wrong
-- decomposition selects nothing.
def threeWayWrongEq : Term := prog defer_check {
  fn ThreeWayWrongEq (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S (S j))),
                      a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeAdd i (S j) | Heq];
    () };
  () }
example : progRejects threeWayWrongEq "cited decomposition does not have type" = true := by
  native_decide

-- A LYING residue is rejected: the supplied extent must actually decompose the leaf,
-- and premise (3) is the thing that checks it. Here `j` is claimed where `S j` is
-- needed, so the solution transition has no solution.
def threeWayLyingResidue : Term := prog defer_check {
  fn ThreeWayLyingResidue (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i j),
                           a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; j | LeAdd i j | Heq];
    let p = &m (*a)[i ; 1 ; j];
    () };
  () }
example : progOk threeWayLyingResidue = false := by native_decide

-- …and the residue is genuinely CONSUMED, not decoration: with it supplied the right
-- half's extent is the program's `j`, so a callee taking `Array j Nat` receives it
-- with no coercion and no unnameable σ in sight. This is the call that finding (a)
-- said was unwritable.
def sliceTake : Term := prog{
  fn SliceTake (q : Nat, s : &mut (Array q Nat)) -> Unit { () };
  () }
example : progOk sliceTake = true := by native_decide

def threeWayCall : Term := prog{
  fn SliceTake (q : Nat, s : &mut (Array q Nat)) -> Unit { () };
  fn ThreeWayCall (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                   a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let p = &m (*a)[i ; 1 ; j];
    let r = &m (*a)[S i ; ..];
    SliceTake(i, l);
    SliceTake(j, r);
    () };
  () }
example : progOk threeWayCall = true := by native_decide

/-! ### The extent map's running base is spelled `S^k b` too

    Same reason as the range end: the segment after a width-1 pivot has base
    `Add i 1`, which is stuck on a symbolic `i` and never converts with the `S i`
    a program writes. A concrete count advances the base by successors; a
    symbolic one keeps `Add`, where it computes. Without this, `(*a)[S i ; ..]`
    cannot find the segment it just created. -/

example : progOk (prog{
  fn BaseSpelling (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                   a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let p = &m (*a)[i ; 1 ; j];
    let r = &m (*a)[S i ; j];
    () };
  () }) = true := by native_decide


/-! ## The array library

    Every lemma in the quicksort library — `Count`, `Sorted`, `Bound`, the order
    stack — transfers to arrays by replacing `listRec` with `arrRec` and `Cons`
    with `acons`, with nothing about the migration requiring the mathematics to
    be re-derived. The glue lemma sets `Append ↦ arrCat` and
    `Cons p b ↦ arrCat (Asingle p) r`, and it IS the array lemma, hypothesis for
    hypothesis — the same statement modulo the container, so the migration
    INHERITS that proof rather than opening a new one.

    Both claims are checkable and both check. The definitions and proofs in
    `StdLemmas` are their list counterparts with that substitution applied and
    nothing else. -/

def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

open Dllbc.StdLemmas (CountA SortedA UbA LbA BoundA Asingle
  SortedHeadA SortedHeadATy SortedTailA SortedTailATy
  UbHeadA UbHeadATy UbTailA UbTailATy LbBoundA LbBoundATy
  BoundArrCat BoundArrCatTy SortedArrCat SortedArrCatTy
  CountArrCat CountArrCatTy
  CountAconsHit CountAconsHitTy CountAconsMiss CountAconsMissTy
  NoAboveOfUbA NoAboveOfUbATy UbOfNoAboveA UbOfNoAboveATy
  UbPermA UbPermATy NoBelowOfLbA NoBelowOfLbATy
  LbOfNoBelowA LbOfNoBelowATy LbPermA LbPermATy
  CountSwap2 CountSwap2Ty LebTrueLe LebFalseGt LePredL)

-- The predicates COMPUTE, on a run and on the cons view alike.
example : (pv prog defer_check { CountA 2 4 Arr(1, 2, 2, 3) } == Term.nat 2) = true := by native_decide
example : (pv prog defer_check { SortedA 3 Arr(1, 2, 3) } == pv prog defer_check { SortedA 3 Arr(1, 2, 3) })
    = true := by native_decide
example : chk prog defer_check { Pair(unit, Pair(unit, Pair(unit, unit))) } prog defer_check { SortedA 3 Arr(1, 2, 3) }
    = true := by native_decide
-- …and an unsorted array's `SortedA` is uninhabited, so the predicate is not vacuous.
example : chk prog defer_check { Pair(unit, Pair(unit, Pair(unit, unit))) } prog defer_check { SortedA 3 Arr(3, 2, 1) }
    = false := by native_decide

-- `arrCat (Asingle p) b` IS the array `Cons p b`: the pivot splice reaches the
-- cons view by computation, with no lemma relating them.
example : (pv prog defer_check { arrCat 1 2 (Asingle 9) Arr(1, 2) } == pv prog defer_check { Arr(9, 1, 2) })
    = true := by native_decide

/-! ### The five helpers and the glue, each its list proof with the container swapped -/

example : chkL SortedHeadA SortedHeadATy = true := by native_decide
example : chkL SortedTailA SortedTailATy = true := by native_decide
example : chkL UbHeadA UbHeadATy = true := by native_decide
example : chkL UbTailA UbTailATy = true := by native_decide
example : chkL LbBoundA LbBoundATy = true := by native_decide
example : chkL BoundArrCat BoundArrCatTy = true := by native_decide

/-- **The crux.** `SortedAppendPivot` with `Append ↦ arrCat` and `Cons p b ↦
    arrCat (asingle p) r`, hypothesis for hypothesis, and nothing else changed. -/
example : chkL SortedArrCat SortedArrCatTy = true := by native_decide

/-- `CountArrCat` replaces `CountAppend`/`Take`/`Drop`, and it is the same
    induction — the dependent Bool-elim on `Eqb x h` transfers unchanged, because
    `CountA` unfolds on an `acons` exactly as `Count` unfolds on a `Cons`. -/
example : chkL CountArrCat CountArrCatTy = true := by native_decide

/-! ### The permutation keystone, transferred

    `Ub`/`Lb` (Σ-chains over the spine) are not natively permutation-invariant.
    The route crosses to the multiset instead, where the property is
    `Π x. x > p → Count x l = Z` and permutation-invariance is a one-line
    `IdTrans`. The crossing transfers with the container like everything else —
    all eight lemmas, first try. -/

example : chkL CountAconsHit CountAconsHitTy = true := by native_decide
example : chkL CountAconsMiss CountAconsMissTy = true := by native_decide
example : chkL NoAboveOfUbA NoAboveOfUbATy = true := by native_decide
example : chkL UbOfNoAboveA UbOfNoAboveATy = true := by native_decide
example : chkL UbPermA UbPermATy = true := by native_decide
example : chkL NoBelowOfLbA NoBelowOfLbATy = true := by native_decide
example : chkL LbOfNoBelowA LbOfNoBelowATy = true := by native_decide
example : chkL LbPermA LbPermATy = true := by native_decide

/-! ### The transfer needed three ι-rules to be mechanical

    The mathematics transfers verbatim, but the array constants also have to
    compute the way the list constructors do, or every step of a transferred
    proof wants a transport lemma the list proof needs none of.

    Two rules, both in `Pure.lean`. `arrCat` computes on an `acons`-headed left
    argument (`arrCat (acons x xs) b ⇝ acons x (arrCat xs b)`), which is
    `append (Cons h t) u ⇝ Cons h (append t u)`; and `arrRec` fires on the cons
    view, so a predicate over arrays unfolds on an `acons` exactly as its
    counterpart unfolds on a `Cons`. Without them `SortedA (arrCat (acons h t) …)`
    does not UNFOLD, and `SortedAppendPivot`'s proof turns entirely on that
    unfolding — both components are definitional, so no transport lemma appears
    anywhere in the proof.

    A third rule was invisible until the glue was written: a nonempty RUN on the
    left with a non-run on the right peels its head into an `acons`. `Asingle p`
    COMPUTES to the run `[p]`, so the spelling `arrCat (Asingle p) r` was stuck
    for symbolic `r` — the notation could not reach the cons view it is notation
    FOR. The rule is the same one read through the other view: a literal is a
    cons spine that happens to be written flat. -/

/-! ## A verified in-place array sort

    Everything above composes here: index places, the carve on a SYMBOLIC array,
    branch equations, the transferred library, `old *v`, and the exit-snapshot
    audit. The postcondition is the quicksort signature at width two —

        Σ (hs : SortedA 2 (*a)). (Π x. Id Nat (CountA x 2 (*a)) (CountA x 2 (old *a)))

    — sortedness AND count-preservation over the exit snapshot, with zero
    declared backs. It is not the full quicksort, but it is the whole stack end
    to end on a real in-place mutation. -/

-- Writing known values through index places, then proving sortedness of the exit.
def setSorted : Term := prog{
  fn SetSorted (a : &mut (Array 2 Nat)) -> SortedA 2 (*a) {
    (*a)[0] := 1;
    (*a)[1] := 2;
    Pair(unit, Pair(unit, unit)) };
  () }
example : progOk setSorted = true := by native_decide

-- …and the same body with the writes the wrong way round is rejected: `SortedA` unfolds
-- to `Σ Bot. …`, so the predicate is not vacuous.
def setSortedLie : Term := prog defer_check {
  fn SetSortedLie (a : &mut (Array 2 Nat)) -> SortedA 2 (*a) {
    (*a)[0] := 2;
    (*a)[1] := 1;
    Pair(unit, Pair(unit, unit)) };
  () }
example : progOk setSortedLie = false := by native_decide

/-- Reading a SYMBOLIC array's elements turns it into a run of named elements. This is
    the step that makes an in-place algorithm provable at all: `σ_a : Array 2 Nat` is
    opaque, and after two index reads the payload is `[σ₀, σ₁]` with both elements in
    scope — carve, then `elementize`, then the ordinary copy-on-read. -/
def readTwo : Term := prog{
  fn ReadTwo (a : &mut (Array 2 Nat)) -> Unit {
    let x = (*a)[0];
    let y = (*a)[1];
    () };
  () }
example : progOk readTwo = true := by native_decide

/-! ### At INDEX places, the two-segment conversion fails, for a reason worth having

    A hypothetical Ω-level assertion would read `a`'s payload back as a
    two-segment node with the takes at distinct positions. The conversion
    attempted here — take both, refill both, and let the obligation audit
    demand that the takes were disjoint — does not work, and the twin below is
    what says so rather than a hunch.

    Taking index 0 TWICE is ACCEPTED. Copy-on-read is why: a concrete `Nat`
    element is INDEX-KIND, so a take COPIES and leaves no hole, and there is
    no linearity at a copyable element type for a body to observe. The segment
    structure such an assertion would read is therefore an implementation
    detail at this element type — unobservable through the language, with the
    behaviour covered by the executing differential.

    The disjointness invariant itself is not lost: `halvesBoth`/`halvesSame` and
    `threeWayAll` above demand it at SEGMENT places, where the payload is an array
    rather than an element and the linearity is real. -/

def readSame : Term := prog{
  fn ReadSame (a : &mut (Array 2 Nat)) -> Unit {
    let x = (*a)[0];
    let y = (*a)[0];
    (*a)[0] := y;
    () };
  () }
-- The record of why the conversion fails, asserted rather than described.
example : progOk readSame = true := by native_decide

/-- An in-place two-element sort over a symbolic borrow, verified
    `Sorted ∧ Perm` over the exit snapshot, zero backs. Both paths mutate or not through
    index places, and the audit judges the collapsed payload against a postcondition that
    names `*a` (exit) and `old *a` (entry). -/
def sort2 : Term := prog{
  fn Sort2 (a : &mut (Array 2 Nat))
      -> Σ0 (Hs : SortedA 2 (*a)). (Π (X : Nat) → Id Nat (CountA X 2 (*a)) (CountA X 2 (old *a))) {
    let x = (*a)[0];
    let y = (*a)[1];
    if h : Leb x y {
      Pair(Pair(LebTrueLe x y h, Pair(unit, unit)), λ (N : Nat). Refl)
    } else {
      (*a)[0] := y;
      (*a)[1] := x;
      -- The count λ cites the two swapped elements, which is a snapshot of
      -- values that are about to be nowhere in particular. Naming them says which
      -- pair the equation is about — and it does NOT matter that the writes
      -- happened above, because `x` and `y` are index-kind and were copied, not
      -- moved.
      let X0 = x;
      let Y0 = y;
      Pair(Pair(LePredL y x (LebFalseGt x y h), Pair(unit, unit)),
           λ (N : Nat). CountSwap2 N X0 Y0)
    } };
  () }
example : progOk sort2 = true := by native_decide

/-! ### Lying twins, one per conjunct -/

-- Forget the swap and still claim sortedness. The False branch's goal is `Le x y`,
-- which is exactly what the branch equation says is FALSE.
def sort2LieSorted : Term := prog defer_check {
  fn Sort2LieSorted (a : &mut (Array 2 Nat)) -> SortedA 2 (*a) {
    let x = (*a)[0];
    let y = (*a)[1];
    if h : Leb x y {
      Pair(LebTrueLe x y h, Pair(unit, unit))
    } else {
      Pair(LePredL y x (LebFalseGt x y h), Pair(unit, unit))
    } };
  () }
example : progOk sort2LieSorted = false := by native_decide

-- Do the swap, then claim the counts did not move. `CountSwap2` is genuinely load-
-- bearing: `Refl` in its place is rejected.
def sort2LieCount : Term := prog defer_check {
  fn Sort2LieCount (a : &mut (Array 2 Nat))
      -> Σ0 (Hs : SortedA 2 (*a)). (Π (X : Nat) → Id Nat (CountA X 2 (*a)) (CountA X 2 (old *a))) {
    let x = (*a)[0];
    let y = (*a)[1];
    if h : Leb x y {
      Pair(Pair(LebTrueLe x y h, Pair(unit, unit)), λ (N : Nat). Refl)
    } else {
      (*a)[0] := y;
      (*a)[1] := x;
      Pair(Pair(LePredL y x (LebFalseGt x y h), Pair(unit, unit)), λ (N : Nat). Refl)
    } };
  () }
example : progOk sort2LieCount = false := by native_decide

end Dllbc.Tests.S24Arrays
end
