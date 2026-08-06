import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.StdLemmas
import Dllbc.Tests.S9Diff
import Dllbc.Migrate

/-!
# §24 test suite — arrays, range places, and proof-licensed carving

The mechanization of `docs/design-arrays-slices.md`. Stage (i) here is the
representation layer, which the note is explicit has no semantic content (¶8.1: of
five additions "exactly one — CARVE — has semantic content. The rest is
representation"). What that buys is checked rather than assumed: every generic `Val`
walker traverses an array node unchanged, because an array node is an ordinary `ctor`.

## The four value forms (¶1.1)

    Arr [v₁ … v_c]              an owned flat RUN — value form AND knowledge form
    sym σ                       opaque
    an `arrCat` spine           a stuck neutral
    §segs [§seg [c, b], …]      CARVED (state only; k ≥ 2)

An UNCARVED array carries no wrapper: ¶1.1's "a single segment is abbreviated to its
body, since the two are the same state". `§segs`/`§seg` are reserved names with no
`ctorSig` entry, so no program can write or match one.

## Element `i` is a subterm, which is the whole point

¶1.2's argument for basis membership over §7's declaration scheme is that every
CIC-scheme inductive with a length index is right-nested, and a spine's prefixes and
middles are not subterms. `Arr`'s fields are the elements, flat, so `a[i]` reaches
child `i` and `a[lo ; cnt]` reaches a segment — both subterms. That is what makes a
range borrow an ordinary `&mut` rather than a new aliasing judgment.
-/

open Dllbc
open Dllbc.StdLemmas (le_refl le_add)

namespace Dllbc.Tests.S24Arrays

/-- Type-check a closed term against a closed type in the pure seed (as §18/§19/§23). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- Normalize a closed pure term to a value (§23's `pv`). -/
def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)

/-! ## (i.a) The former and its literal

    `ctorSig "Arr"`'s field telescope is `T` repeated `n` times at a CONCRETE `n`,
    and `none` at a symbolic one — "one cannot write an array literal of unknown
    length" (¶1.4). Hand-written rather than §7-generated, which is the concrete cost
    of basis membership (¶9c) and the place a drift would start. -/

def arr3 : Term := pure{ Arr(3, 1, 2) }
example : chk arr3 pure{ Array 3 Nat } = true := by native_decide
example : chk pure{ Arr() } pure{ Array 0 Nat } = true := by native_decide

-- Arity is the length index: `Arr(3,1,2)` does not inhabit `Array 2 Nat`. This is
-- `checkFields`'s arity branch, reached through the replicated telescope.
example : chk arr3 pure{ Array 2 Nat } = false := by native_decide
example : chk arr3 pure{ Array 4 Nat } = false := by native_decide

-- The ELEMENT type is checked per field, so a `Bool` in a `Nat` array is rejected.
example : chk pure{ Arr(3, True) } pure{ Array 2 Nat } = false := by native_decide

-- A symbolic length has no constructor signature at all — the honest `none`, not a
-- guess. (`n` here is a Π-bound σ, so `natOfVal?` fails on it.)
def arrSymLen : Term := pure{ λ (n : Nat). Arr(3) }
example : chk arrSymLen pure{ Π (n : Nat) → Array n Nat } = false := by native_decide

/-! ## (i.b) `arrCat` — the split view, and §3.2's knowledge/state line

    "The segment list is **state**. It lives in Ω… The `arrCat` neutral is
    **knowledge**. It lives in types and snapshots, and it never mentions a marker or
    a hole." So `arrCat` computes on run-headed arguments and is a legitimate stuck
    neutral on σ's — the two halves of that sentence, mechanized. -/

example : (pv pure{ arrCat 2 1 Arr(3, 1) Arr(2) } == pv arr3) = true := by native_decide
example : (pv pure{ arrCat 0 3 Arr() Arr(3, 1, 2) } == pv arr3) = true := by native_decide
example : (pv pure{ arrCat 3 0 Arr(3, 1, 2) Arr() } == pv arr3) = true := by native_decide

-- Associativity is NOT definitional; the carve therefore always produces
-- right-nested spines, and nothing downstream may assume otherwise.
example : (pv pure{ arrCat 2 1 (arrCat 1 1 Arr(3) Arr(1)) Arr(2) } ==
           pv pure{ arrCat 1 2 Arr(3) (arrCat 1 1 Arr(1) Arr(2)) }) = true := by native_decide

-- The stuck case: two σ's have no name for their concatenation, but they do have a
-- term for it (¶1.1), which is all merge and the ⇝ fold need.
def catSyms : Val := Val.arrCatS (Val.nat 2) (Val.nat 1) (.sym 0) (.sym 1)
example : (Val.nfV 100 catSyms == catSyms) = true := by native_decide

-- `arrCat m k a b : Array (add m k) T` — the empty-run absorption is what makes a
-- DEGENERATE carve's rejoin conversion definitional instead of lemma-mediated.
example : (Val.nfV 200 (Val.arrCatS (Val.nat 0) (Val.nat 2) (.ctor "Arr" []) (.sym 0)) ==
           Val.sym 0) = true := by native_decide

/-! ## (i.c) `aget` — the ⇝ column at an index place -/

example : (pv pure{ aget Nat 3 0 Arr(3, 1, 2) } == Val.nat 3) = true := by native_decide
example : (pv pure{ aget Nat 3 2 Arr(3, 1, 2) } == Val.nat 2) = true := by native_decide

-- Stuck on a symbolic index and on a symbolic array — a legal neutral either way, so
-- a type may mention `aget i (*v)` while `i` is unknown.
def agetSymIdx : Val := Val.nfV 200 (pv pure{ λ (i : Nat). aget Nat 3 i Arr(3, 1, 2) })
example : (agetSymIdx == Val.nfV 200 agetSymIdx) = true := by native_decide

/-! ## (i.d) The cons view: `acons` and `arrRec`

    ¶1.3's reason for the second view: "Every lemma in the quicksort library —
    `count`, `Sorted`, `Bound`, the order stack — transfers to arrays by replacing
    `listRec` with `arrRec` and `Cons` with `acons`." The library transfer itself is
    ¶6's migration; what is checked here is that the recursor computes. -/

example : (pv pure{ acons 2 3 Arr(1, 2) } == pv arr3) = true := by native_decide

-- `alen` by `arrRec` — deliberately, since ¶1.1 says an array's length is read off
-- its TYPE and never computed from its contents. This exists only to exercise ι.
def alen : Term := pure{
  λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Nat) Z
      (λ (k : Nat). λ (x : Nat). λ (xs : Array k Nat). λ (ih : Nat). S ih) n a }
example : (pv pure{ alen 3 Arr(3, 1, 2) } == Val.nat 3) = true := by native_decide
example : (pv pure{ alen 0 Arr() } == Val.nat 0) = true := by native_decide

-- A sum, so the recursive arm's element binder is exercised too.
def asum : Term := pure{
  λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Nat) Z
      (λ (k : Nat). λ (x : Nat). λ (xs : Array k Nat). λ (ih : Nat). add x ih) n a }
example : (pv pure{ asum 3 Arr(3, 1, 2) } == Val.nat 6) = true := by native_decide

-- Stuck on a symbolic target: no `Arr` to fire on, so the spine is a legal value
-- rather than an error — which is what lets a predicate family over arrays be stated
-- about a σ at all.
def arrRecStuck : Val := Val.nfV 500 (pv pure{ λ (n : Nat). λ (a : Array n Nat). alen n a })
example : (arrRecStuck == Val.nfV 500 arrRecStuck) = true := by native_decide

/-! ## (i.e) Segments: merge, drop-empty, and the ⇝ fold

    ¶1.1's two normalizations and ¶1.3's bridge. `§segs`/`§seg` have no surface
    syntax, so these are built as values — which is the point: they are STATE. -/

def segsOf (l : List (Nat × Val)) : Val :=
  Val.segsNode (l.map (fun p => Val.segNode (Val.nat p.1) p.2))

-- ¶3.3's rejoin: "There is no rejoin rule. When the last marker under an array node
-- is gone, the merge normalization collapses the segments, and the array is a run
-- again — indistinguishable from one that was never carved." That indistinguishability
-- is ¶8.2's obligation 4 (merge is value-preserving) and is what keeps
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
example : (Val.segsNode [Val.segNode (Val.nat 3) (.ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2])]
           == .ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2]) = true := by native_decide

-- A LOANED segment blocks the merge, which is what keeps a carved-and-borrowed array
-- distinguishable from a whole one for exactly as long as the borrow lives.
example : (Val.mergeArrays (segsOf [(1, .ctor "Arr" [Val.nat 3]), (2, .loanM 0)])
           == segsOf [(1, .ctor "Arr" [Val.nat 3]), (2, .loanM 0)]) = true := by native_decide

-- The ⇝ bridge (¶1.3): the fold of a collapsed segment list is its `arrCat` spine.
example : (Val.arrFoldSegs? [Val.segNode (Val.nat 1) (.sym 0), Val.segNode (Val.nat 2) (.sym 1)]
           == some (Val.arrCatS (Val.nat 1) (Val.nat 2) (.sym 0) (.sym 1))) = true := by native_decide

-- "A suspended array has no snapshot; only a collapsed one does" — §5.2's
-- proper-payload premise, arriving at an array node. Both markers are rejected.
example : (Val.arrFoldSegs? [Val.segNode (Val.nat 1) (.loanM 0),
                             Val.segNode (Val.nat 2) (.sym 1)]).isNone = true := by native_decide
example : (Val.arrFoldSegs? [Val.segNode (Val.nat 1) (.bot),
                             Val.segNode (Val.nat 2) (.sym 1)]).isNone = true := by native_decide

-- Folding a run-only split gives back the run itself, by `arrCat`'s ι-rule — the
-- knowledge form of a rejoined array IS the uncarved one, definitionally.
example : (Val.arrFoldSegs? [Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 3]),
                             Val.segNode (Val.nat 2) (.ctor "Arr" [Val.nat 7, Val.nat 2])]
           == some (Val.arrCatS (Val.nat 1) (Val.nat 2) (.ctor "Arr" [Val.nat 3])
                     (.ctor "Arr" [Val.nat 7, Val.nat 2]))) = true := by native_decide
example : (Val.nfV 200 (Val.arrCatS (Val.nat 1) (Val.nat 2) (.ctor "Arr" [Val.nat 3])
             (.ctor "Arr" [Val.nat 7, Val.nat 2]))
           == .ctor "Arr" [Val.nat 3, Val.nat 7, Val.nat 2]) = true := by native_decide

/-! ## (i.f) Extents read off the value

    A carve's premise (1) needs the extent map, which needs the node's total extent.
    Every array-shaped value determines it EXCEPT a bare σ, whose extent lives in its
    `sctx` type — so `arrExtentPure?` is partial by design and the machine wrapper
    consults `sctx`. This is what let the design keep ¶1.1's abbreviation (no wrapper
    on an uncarved array) instead of stamping every array value with its length. -/

example : (Val.arrExtentPure? (.ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2])
           == some (Val.nat 3)) = true := by native_decide
example : (Val.nfV 100 ((Val.arrExtentPure? (segsOf [(1, .sym 0), (2, .sym 1)])).getD Val.zero)
           == Val.nat 3) = true := by native_decide
example : (Val.nfV 100 ((Val.arrExtentPure?
             (Val.arrCatS (Val.nat 1) (Val.nat 2) (.sym 0) (.sym 1))).getD Val.zero)
           == Val.nat 3) = true := by native_decide
example : (Val.arrExtentPure? (.sym 0)).isNone = true := by native_decide

/-! ## (i.g) Every generic walker traverses an array node unchanged

    Appendix A's load-bearing claim, and the reason ¶8.1 can say four of the five
    additions are representation: an array node is an ordinary `ctor`, so `loanIds`,
    `symIds`, `renumber`, `hasStateMarker` and `beq` need no case and MUST NOT get
    one. A segment list with a loan in it is found by the existing traversals — which
    is why ¶3.3's range-loan collapse and §3.3's field-loan collapse are one code
    path, and why `refineSym`'s knowledge/state assertion is already live at the
    carve's refinement site. -/

def carvedWithLoan : Val :=
  segsOf [(1, .sym 0), (2, .loanM 7), (1, .sym 1)]

example : (carvedWithLoan.loanIds == [7]) = true := by native_decide
example : (carvedWithLoan.symIds == [0, 1]) = true := by native_decide
-- The marker is in OWNED position of the array node (a segment body is a `ctor`
-- field), so a demand for the owner ends it — §2.2's rule verbatim, no new case.
example : (firstLoanMarker carvedWithLoan == some 7) = true := by native_decide
-- …and it is STATE, so no σ may ever be refined to this tree (§3.2's invariant, the
-- assertion the carve inherits by going through `refineSym`).
example : Val.hasStateMarker carvedWithLoan = true := by native_decide
example : Val.hasStateMarker (segsOf [(1, .sym 0), (2, .sym 1)]) = false := by native_decide
-- A hole in a segment is state too: `⇒` at a range place leaves one (¶2.2's
-- take-and-refill generalized from a borrow's payload to a run of an array).
example : Val.hasStateMarker (segsOf [(1, .sym 0), (2, .bot)]) = true := by native_decide

-- `Arr`'s fields are ELEMENTS, flat — so element `i` is child `i`, a subterm. This is
-- ¶1.2's entire argument for the basis over the declaration scheme, and it is the
-- property the place grammar of ¶2 is defined against.
example : ((.ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2] : Val).symIds == []) = true := by native_decide
example : (Val.renumber id (· + 10) carvedWithLoan == segsOf [(1, .sym 10), (2, .loanM 7), (1, .sym 11)])
    = true := by native_decide

/-! ## (i.h) `Le` and `add` moved into the kernel

    A DEVIATION worth flagging: `Le` and `add` were library terms (`Std`), but the
    CARVE rule's premises are *stated* against them — premise (2) IS a `Le`, premise
    (3) decomposes an extent with `add` — and a kernel rule cannot cite a library it
    does not import. Two syntactically different `add`s would never convert, which
    would break the one conversion the whole residue-transition decision exists to
    make definitional (¶3.4's audit). So both moved to `Pure.lean` and `Std` aliases
    them; these two tests are the single-source-of-truth check. -/

example : (Val.kAddFn == Dllbc.Std.addFn) = true := by native_decide
example : (Val.kLeFn == Dllbc.Std.LeFn) = true := by native_decide
example : (Val.nfV 200 (Val.kAdd (Val.nat 2) (Val.nat 3)) == Val.nat 5) = true := by native_decide
example : (Val.nfV 200 (Val.kLe (Val.nat 2) (Val.nat 3)) == .const "Unit") = true := by native_decide
example : (Val.nfV 200 (Val.kLe (Val.nat 3) (Val.nat 2)) == .const "Bot") = true := by native_decide

/-! ## (ii) CARVE, at concrete indices

    ¶3's rule, and the design's only new one. At concrete indices "the containment
    `Le`s compute to ⊤ — free by conversion", so premise (2) needs no annotation and
    premise (3) is a no-op: ¶3.3's trace says exactly that, "residue transition: n = 3
    concrete, both sides compute — nothing refined". -/

/-! ### ¶3.3's lifecycle

    ```rust
    let a = [3, 1, 2];
    let m = &mut a[1 ; 2];
    (*m)[0] := 7;
    ```

    Every step after the carve is a rule that already existed. The carve puts a loan
    marker in a segment body, which is OWNED POSITION of `a`'s value, so §2.2's rule
    reaches it unchanged; the write through `m` is an ordinary ⇐-fill at an index
    place under a peel. -/

def carveMid : Term := dllbc{ let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; () }

example : expectEnv carveMid
  [("a", Val.segsNode [Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 3]),
                       Val.segNode (Val.nat 2) (.loanM 0)]),
   ("m", .borrowM 0 (.ctor "Arr" [Val.nat 1, Val.nat 2]))] = true := by native_decide

def carveWritten : Term := dllbc{
  let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; () }

example : expectEnv carveWritten
  [("a", Val.segsNode [Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 3]),
                       Val.segNode (Val.nat 2) (.loanM 0)]),
   ("m", .borrowM 0 (.ctor "Arr" [Val.nat 7, Val.nat 2]))] = true := by native_decide

/-- **Rejoin is merge** (¶3.3), and here it is: demand the whole array and the loan
    ends, the payload plugs into its marker, and the segments collapse. `b` is a plain
    run — indistinguishable from one that was never carved, which is the property the
    segment representation was chosen for and what keeps `canonicalize` a decision
    procedure for Ω-equality. -/
example : expectEnv dllbc{
    let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; let b = a; () }
  [("a", .bot), ("m", .bot),
   ("b", .ctor "Arr" [Val.nat 3, Val.nat 7, Val.nat 2])] = true := by native_decide

/-! ### FINDING — ¶3.3's trace ends the loan one step too eagerly, and it should not

    The design note's own lifecycle finishes `let x = a[0];` with the comment "the read
    demands a's node; a loan marker is in owned position, so §2.2 forces End-Mut ℓ
    first: the payload plugs into the marker, m dies". That is written as though the
    element read demands the WHOLE array. It does not, and §2.2's own wording is the
    reason: what a ⇒-read ends is "every loan marker in owned position **within the
    value it is about to move**". Reading `a[0]` moves one element, and that element
    carries no marker.

    Implementing §2.2 precisely rather than the trace literally gives strictly more:
    the read succeeds and `m` STAYS LIVE, holding its disjoint half. Which is the
    design's own headline — an element and a disjoint range of one array, both live,
    coexisting because they are different subterms — arriving one paragraph before ¶3.4
    claims it. The looser reading would have thrown that away for the trace's
    convenience. Nothing else in the note depends on the eager ending; ¶3.3's point is
    rejoin, which the test above shows on the demand that genuinely wants the array. -/

example : expectEnv dllbc{
    let a = Arr(3, 1, 2); let m = &mut a[1 ; 2]; (*m)[0] := 7; let x = a[0]; () }
  [("a", Val.segsNode [Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 3]),
                       Val.segNode (Val.nat 2) (.loanM 0)]),
   ("m", .borrowM 0 (.ctor "Arr" [Val.nat 7, Val.nat 2])),
   ("x", Val.nat 3)] = true := by native_decide

/-! ### `get` and `set` are not primitives (¶2.3)

    They are the two arrows at the index place. No kernel primitive is added for
    either, and the M22 `nth`/`nth2`/`set` library — 26 lines of recursive cursor plus
    a pure `set` model — is what this DELETES rather than ports. -/

-- ⇐ at an index place: write the element (with §2.3's drop of the displaced value
-- forced first — a Nat, so discard).
example : expectEnv dllbc{ let a = Arr(3, 1, 2); a[0] := 9; () }
  [("a", .ctor "Arr" [Val.nat 9, Val.nat 1, Val.nat 2])] = true := by native_decide

-- ⇒ at an index place: read the element. §2.1's copy-on-read applies (Nat is
-- index-kind), so the array keeps it — the doc's trace comment, mechanized.
example : expectEnv dllbc{ let a = Arr(3, 1, 2); let x = a[2]; () }
  [("a", .ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2]), ("x", Val.nat 2)]
    = true := by native_decide

-- `&mut a[i]`: an element cursor, an ordinary borrow. The marker parks INSIDE the
-- one-slot run, so the segment body stays at `Array 1 T` while the borrow's payload
-- is the element at `T` — ¶2.1's "`a[i]` is not `a[i ; 1]`", made structural.
example : expectEnv dllbc{ let a = Arr(3, 1, 2); let e = &mut a[1]; *e := 8; let y = a[1]; () }
  [("a", .ctor "Arr" [Val.nat 3, Val.nat 8, Val.nat 2]), ("e", .bot), ("y", Val.nat 8)]
    = true := by native_decide

/-! ### Take-and-refill at a range place (¶2.2)

    §2.4's idiom generalized from "the payload of a borrow" to "a run of an array":
    between the take and the refill the array holds a hole of known extent, no rule
    reads it, and the refill is its one legal successor. That is how a rotation or a
    memmove is written without a copy. -/

example : expectEnv dllbc{ let a = Arr(3, 1, 2);
                           let run = a[1 ; 2];
                           a[1 ; 2] := run;
                           let w = a[0]; () }
  [("a", .ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 2]), ("run", .bot), ("w", Val.nat 3)]
    = true := by native_decide

/-! ### Carve of carve collapses definitionally (¶3.2's fourth Low\* lemma)

    `carve_carve : (a[lo₁ ; cnt₁])[lo₂ ; cnt₂] ≡ a[add lo₁ lo₂ ; cnt₂]` is the one the
    doc says "a DLLBC implementer will underestimate", because without it every
    sub-slice of a sub-slice accumulates a chain of offsets no conversion sees through.
    It holds with no lemma at all, and for the reason the doc predicts: premise (3)
    hands back LEAF-RELATIVE offsets, so a nested carve is an ordinary carve inside the
    segment it landed in, and the offsets never compose into a chain. **The doc's own
    diagnostic is that needing a lemma here would mean premise 3 is implemented wrong**
    — so this passing is evidence about premise 3, not about nesting. -/

example : expectEnv
    dllbc{ let a = Arr(3, 1, 2, 7, 5);
           let m = &mut a[1 ; 3];
           let inner = &mut (*m)[1 ; 2];
           (*inner)[0] := 9;
           let b = a;
           () }
  [("a", .bot), ("m", .bot), ("inner", .bot),
   ("b", .ctor "Arr" [Val.nat 3, Val.nat 1, Val.nat 9, Val.nat 7, Val.nat 5])]
    = true := by native_decide

/-! ### The rejections (¶3.5), each falling out of a premise rather than a check -/

-- OVERLAP — premise (1), and the shape it actually takes. After `&mut a[0 ; 3]` the
-- extent map is `[(0,3,loaned ℓ₁), (3,rest,owned)]`, and [2,5) is contained in NEITHER
-- leaf: it straddles the boundary. So the rejection needs no owned-versus-loaned test
-- at all — two segments cannot overlap, so a range crossing a segment boundary has no
-- leaf, full stop. No arithmetic was performed and no proof could have helped.
example : expectErr dllbc defer_check { let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[2 ; 3];
                           () }
  "no leaf" = true := by native_decide

-- OUT OF RANGE — premise (2) has no inhabitant and none can be supplied, because
-- `Le (add lo cnt) n` computes to ⊥.
example : expectErr dllbc defer_check { let a = Arr(3, 1, 2); let m = &mut a[1 ; 3]; () }
  "containment obligation" = true := by native_decide
example : expectErr dllbc defer_check { let a = Arr(3, 1, 2); let x = a[3]; () }
  "containment obligation" = true := by native_decide

-- A HOLE is not owned. `⇒` at a range place takes the run out and leaves one, and
-- until the ⇐-refill closes it no carve may split across it.
example : expectErr dllbc defer_check { let a = Arr(3, 1, 2);
                           let run = a[1 ; 2];
                           let x = a[1];
                           () }
  "meets a hole" = true := by native_decide

/-! ### FINDING — a contained request DEMAND-ENDS rather than rejecting, and that is
    the calculus's existing character rather than a new decision

    ¶3.5 reads as though any loaned leaf rejects. Two cases hide under that, and they
    behave differently for a reason that predates arrays. A request that STRADDLES a
    boundary has no leaf and is rejected (above). A request CONTAINED in a loaned leaf
    is the situation `&mut x` twice already creates, and the existing whole-place rule
    resolves it by ending: `let p = &mut x; let q = &mut x;` is accepted today, with
    `p` killed and any later use of it stuck. Probed directly rather than assumed —

        x ↦ loanₘ ℓ0,  p ↦ ⊥,  q ↦ borrowₘ ℓ0 3

    — so the array rule follows suit, which is also what makes ¶3.6's group trace work
    (`let z = a[0]` must end the group to read across it) and what §5.2 states as one
    rule with several sites: every demand collapses first. Two live overlapping mutable
    borrows remain unrepresentable; what differs from the note is only WHEN the second
    one is rejected — at the first use of the dead borrow, not at its creation. -/

example : expectEnv dllbc{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[1];
                           *q := 6;
                           let b = a;
                           () }
  [("a", .bot), ("p", .bot), ("q", .bot),
   ("b", .ctor "Arr" [Val.nat 3, Val.nat 6, Val.nat 2, Val.nat 7, Val.nat 5])]
    = true := by native_decide

-- …and the killed borrow is stuck at its next use, which is where the rejection
-- actually lands.
example : expectErr dllbc defer_check { let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[1];
                           (*p)[0] := 4;
                           () }
  "⊥" = true := by native_decide


/-! ## (iii) The symbolic carve — ¶3.4, the case the whole design exists for

    Two range borrows of one array, live at once, with a symbolic length. They coexist
    not because the checker believes an aliasing argument but because, after the carve,
    they are literally different subterms of one value tree — and §3.3's suspension
    machinery already knows what to do with those. -/

/-- ¶3.4's `halves`, checked end to end.

    ```rust
    fn halves (a : &mut Array n Nat, k : Nat, h : Le k n) = {
      let l = &mut (*a)[Z ; k];
      let r = &mut (*a)[k ; rest];
    }
    ```

    Read the two carves against each other, because the contrast IS the design. The
    FIRST does everything: its obligation is `Le Z Z × Le (add Z k) (add Z n)`, which
    computes to `⊤ × Le k n` and is discharged by `h`; its residue transition solves
    `n ≡ add k rest` with `n` flex, refining the LENGTH INDEX everywhere; and its body
    split refines `σ := arrCat k rest σ_l σ_r`. The SECOND does nothing at all — its
    request IS the leaf, so no split and no refinement fire, and no evidence is
    demanded because `Le b b` and `Le x x` are `le_refl`. That asymmetry is the general
    shape of an exhaustive split, and it is why this costs ONE proof rather than two. -/
def halves : FnDef := decl{
  fn halves (n : Nat, k : Nat, h : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; k | h];
    let r = &mut (*a)[k ; ..];
    () } }

example : Migrate.progOkOf halves = true := by native_decide

-- PROBE (M27-δ): is disjointness DEMANDABLE rather than only observable?
/-! ### DISJOINTNESS, converted from an Ω observation to a DEMAND (M27-δ)

    `halvesSegLoans` asserted the aliasing invariant by reading the loan ids out
    of the final Ω — `[1, 2]`, two distinct loans over one array. That assertion
    could not survive `checkFn`, so it is restated as what a body can DO under the
    invariant rather than what the machine happens to hold.

    The observable consequence of disjointness is that both sub-borrows stay LIVE.
    A second borrow of an overlapping place demand-ends the first (§5.2), so using
    `l` after `r` has been taken is possible exactly when the two do not overlap.
    The pair below is that, and it is a better assertion than the one it replaces:
    it says the segments are SIMULTANEOUSLY USABLE, where the loan-id reading only
    said they were separately recorded. -/

def halvesBoth : FnDef := decl{
  fn halvesBoth (n : Nat, k : Nat, h : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; k | h];
    let r = &mut (*a)[k ; ..];
    let y = *r;
    *r := y;
    let x = *l;
    *l := x;
    () } }
example : Migrate.progOkOf halvesBoth = true := by native_decide

-- THE TWIN, one character of range apart: carve the SAME segment twice. The
-- second demand-ends the first, so the later use of `l` peels a vacant slot —
-- which is the invariant biting, and what says the acceptance above is about the
-- ranges being disjoint and not about carving twice being allowed.
def halvesSame : FnDef := decl{
  fn halvesSame (n : Nat, k : Nat, h : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; k | h];
    let r = &mut (*a)[Z ; k | h];
    let y = *r;
    *r := y;
    let x = *l;
    *l := x;
    () } }
example : Migrate.progRejectsOf halvesSame "cannot peel a vacant slot" = true := by
  native_decide

-- `fnEnv` (the final Ω of a single-path body) went with `checkFn` (M27-δ):
-- entering a body with a TELESCOPE requires seeding it, and on the program path
-- such a body is entered only inside the seal's isolated frame, whose Ω is
-- discarded by design. Its three assertions were CONVERTED rather than dropped
-- where a demand form exists (`halvesBoth`/`halvesSame`, `threeWayAll`) and
-- recorded lost with the reason where none does (`readSame`).


-- (the loan-id reading it replaced is above, CONVERTED to the demand pair.)

/-! ### Why the audit converts, and what it cost

    ¶3.4: "the obligation type for `a` is `Array n Nat`; the collapsed payload's
    snapshot is `arrCat σ_l′ σ_r′` at `Array (add σₖ rest) Nat`; and these convert
    DEFINITIONALLY, because the residue transition refined `σₙ := add σₖ rest` at the
    carve. Had the carve computed `rest := sub n k` instead, this final conversion
    would have needed `add k (sub n k) ≡ n`, which is not definitional and would have
    required a cited lemma at every audit of every array-mutating function in the
    program. That is the entire argument for premise (3)."

    The `Migrate.progOkOf` above IS that conversion succeeding. One implementation detail
    turned out to be load-bearing and is worth naming, because getting it wrong looks
    like the design failing: the extent sum must be RIGHT-NESTED with no trailing `Z`.
    `add` recurses on its first argument, so `add rest Z` is stuck the moment `rest` is
    symbolic, and `Array (add k (add rest Z))` never converts with `Array (add k rest)`.
    The first version of the audit had the trailing zero and this exact test failed —
    not because premise (3) was wrong but because the sum was shaped wrong. -/

/-! ### Negative controls, one per premise -/

-- Premise (2), UNPROVED BOUND — "the *interesting* rejection: the program is not
-- wrong, it is unjustified". Same body, evidence not cited.
def noEvidence : FnDef := decl{
  fn noEvidence (n : Nat, k : Nat, h : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; k]; () } }
example : Migrate.progRejectsOf noEvidence "containment obligation" = true := by native_decide

-- Premise (2), WRONG EVIDENCE. `h : Le n k` is a perfectly good term of a perfectly
-- good type; it is just not the obligation. The evidence's TYPE is the selector, so a
-- term of the wrong type selects no leaf.
def wrongEvidence : FnDef := decl{
  fn wrongEvidence (n : Nat, k : Nat, h : Le n k, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; k | h]; () } }
example : Migrate.progRejectsOf wrongEvidence "containment obligation" = true := by native_decide

-- Premise (3), RIGID LENGTH (¶8.4's named restriction). The leaf's extent is a
-- compound neutral rather than a flexible σ, so `m ≡ add lo' (add cnt rest)` has no
-- solution by refinement. Rejected with the remedy in the message, which is the one
-- the north star already uses: take the length as a parameter.
def rigidLength : FnDef := decl{
  fn rigidLength (p : Nat, q : Nat, k : Nat, h : Le k (add p q),
                  a : &mut (Array (add p q) Nat)) -> Unit {
    let l = &mut (*a)[Z ; k | h]; () } }
example : Migrate.progRejectsOf rigidLength "premise (3) is stuck" = true := by native_decide
example : Migrate.progRejectsOf rigidLength "Take the length as a telescope PARAMETER"
    = true := by native_decide

/-! ### `refineSym`'s target list is the checklist

    ¶3.2's sharpest warning: the carve's index refinement must reach every σ-bearing
    component. Its named example was `St.selfRec` — "a carve whose index refinement
    reached every component EXCEPT `St.selfRec` would not fail loudly; it would
    silently corrupt the termination guard for **any function recursing on an
    array**". **That component is gone with the guard** (M27-δ), so the example is
    history; the WARNING is not, and it applies unchanged to every σ-bearing field
    `refineSym` still sweeps.

    A function that recurses on fuel and carves on the way checks. -/

def walk : FnDef := decl{
  fn walk [fuel] (fuel : Nat, n : Nat, k : Nat, h : Le k n, a : &mut (Array n Nat)) -> Unit {
    match fuel {
      Z => (),
      S(f2) => { let l = &mut (*a)[Z ; k | h]; walk(f2, k, k, le_refl k, l) }
    } } }
example : Migrate.progOkOf walk = true := by native_decide

/-! ### The regression test the doc asks for

    ~~Declaring the ARRAY as the decreasing argument and recursing on a carved
    sub-slice is rejected, and the rejection's message names the snapshot the guard
    compared against — `arrCat σ σ σ σ` after the carve, so asserting on the word
    `arrCat` is a live check that `refineSym` swept `selfRec`.~~ **OVERTAKEN by
    M27-δ**: there is no guard, no `selfRec`, and no message naming a snapshot. What
    is left is the macro's own refusal, which declines `[a]`-on-a-borrow at §12
    decision 8 — the same fact from the other side, and the one `S26Fuel` §B
    asserts. The sweep itself is still exercised by every carve in this file that
    checks; what is gone is this particular witness to it. -/

def walkArr : FnDef := decl{
  fn walkArr [a] (fuel : Nat, n : Nat, k : Nat, h : Le k n, a : &mut (Array n Nat)) -> Unit {
    match fuel {
      Z => (),
      S(f2) => { let l = &mut (*a)[Z ; k | h]; walkArr(f2, k, k, le_refl k, l) }
    } } }
-- **STAYS ON THE DECLARATION PATH, and dies with it** (M27-γ). `walkArr` declares
-- `[a]` on a BORROW, so `fnElab` declines it at §12 decision 8 and there is no
-- program to reject — the two paths refuse it for the same fact from two sides,
-- which `S26Fuel` §B asserts as a pair. Its honest twin `walk` differs in the
-- hint alone and was paid in M24, before decision 8 existed; `bothWays walk` is
-- the carrier. A δ casualty, not a coverage loss.
-- (assertion deleted with `checkFn`, M27-δ — see the disposition above)

/-! ### FINDING — recursion cannot decrease through a CARVED array payload

    The rejection above is not a bug, and it is worth stating as a restriction because
    ¶6's migration is a recursion over sub-slices. §8's guard compares the actual
    against the parameter's current snapshot by `strictSubterm`, which counts only
    CONSTRUCTOR fields as subterms and deliberately refuses application spines ("a
    `Le`-headed neutral has no well-founded subterm order we could appeal to"). A
    carve's body split refines the payload σ to an `arrCat` SPINE, so from that moment
    no sub-slice is a structural predecessor of its parent.

    ¶6's quicksort is unaffected — it decreases on `fuel`, and `walk` above is that
    shape checking. But "recurse on the sub-slice, no fuel needed" is closed, and the
    doc nowhere says so. Either the guard learns that `arrCat`'s array arguments are
    subterms of their concatenation (true, and specific to this former), or array
    recursion stays fuel-carried. -/

/-! ### ¶3.6 — a segment's loan captured by a call, WITHOUT the parent riding along

    The load-bearing step of ¶3.6's precision claim, which the doc says "was checked
    rather than hoped": `processArgs` captures per-argument-borrow loans and nothing in
    it walks to a parent or a sibling. Here that property meets an array segment for
    the first time. The callee receives the left half; the right half stays borrowed by
    the caller; the parent `a` is audited normally and its untouched segment never
    entered the call. The frame is not described — it is simply still there. -/

def touch : FnDef := decl{ fn touch (p : Nat, l : &mut (Array p Nat)) -> Unit { () } }

def callSeg : FnDef := decl{
  fn callSeg (n : Nat, k : Nat, h : Le k n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; k | h];
    let r = &mut (*a)[k ; ..];
    touch(k, l);
    () } }
example : Migrate.progOkOf callSeg [callSeg, touch] = true := by native_decide

/-! ### FINDING — the residue has no surface name, and ¶3.4/¶5/¶6 all assume it does

    ¶3.4 writes the second borrow as `&mut (*a)[k ; rest]`, ¶5's `split_at_mut` returns
    `&mut (Array rest T)`, and ¶6's quicksort writes `&mut (*v)[S(i) ; rest]`. In every
    case `rest` is a σ the CHECKER minted inside premise (3) — machine-internal, with
    no binder any program can write. The doc notices the tension at ¶5 ("more honestly
    written after the carve has run") but never resolves it.

    `a[lo ; ..]` is the resolution, and it is not the `sub` ¶2.1 bans: it reads the
    residue's extent off the extent map, where premise (3) already parked it as a
    GIVEN. No arithmetic, no new obligation.

    What `..` does NOT solve is a CALL that must pass the residue's length as an
    argument — ¶3.6's own `merge_into (l : &mut Array p Nat, r : &mut Array q Nat)`
    needs a `q`, and `q` is that same unnameable σ. `callSeg` above passes only the
    left half for exactly this reason. Three routes, none free: let a place's extent be
    a comptime term (`alen (a[k ; ..])` — but the extent map is state, so ⇝ would be
    reading state); let the carve BIND its residue in the surface (`let (l, rest) = …`,
    which is a real binder form and the honest one); or have such callees take a Σ-typed
    slice, `Σ (c : Nat). &mut (Array c T)`, which ¶4 already declares well-formed. The
    third needs no new machinery and is probably the answer; it is untested here. -/

/-! ## (iv) Multi-marker collapse, and the differential over array bodies

    ¶8.2's obligation 3, which the doc singles out: "a segment list can hold several
    markers at once, so a partial collapse is now easy to write by accident. Each
    executing former must preserve full collapse, and a negative test per rule branch —
    the M20 lesson — should cover the multi-marker case specifically." -/

/-! ### Three markers in one node, collapsed by one demand

    ¶3.6 already notes that a group's release "touches TWO markers in one owner's
    tree, which is new only in arity". Owner demand is the same story at arity three:
    `readR`'s move ends the leftmost marker and retries until none is left, so the
    collapse is total by construction rather than by a loop someone wrote. Both
    granularities are exercised, because they park markers in different places — a
    range marker IS the segment body, an element marker sits INSIDE the one-slot
    run. -/

example : expectEnv dllbc{
    let a = Arr(3, 1, 2);
    let p = &mut a[0 ; 1]; let q = &mut a[1 ; 1]; let r = &mut a[2 ; 1];
    (*p)[0] := 7; (*q)[0] := 8; (*r)[0] := 9;
    let b = a; () }
  [("a", .bot), ("p", .bot), ("q", .bot), ("r", .bot),
   ("b", .ctor "Arr" [Val.nat 7, Val.nat 8, Val.nat 9])] = true := by native_decide

example : expectEnv dllbc{
    let a = Arr(3, 1, 2);
    let p = &mut a[0]; let q = &mut a[1]; let r = &mut a[2];
    *p := 7; *q := 8; *r := 9;
    let b = a; () }
  [("a", .bot), ("p", .bot), ("q", .bot), ("r", .bot),
   ("b", .ctor "Arr" [Val.nat 7, Val.nat 8, Val.nat 9])] = true := by native_decide

/-! **FINDING — this test found the bug the doc predicted, on its first run.**

    A node still holding a marker must not fold (¶1.3): it has no snapshot, so
    `hasType` rejects it at the one place that judges. `arrFoldSegs?` was written as a
    `foldr` over `Option (extent × body)`, and that shape CONFLATES "this body is not
    owned" with "there is no accumulator yet" — both are `none`. So a marker followed
    by an owned segment had its `none` silently overwritten by the earlier segment,
    and the fold returned a SHORTER array as if it were the whole one.

    It survived every earlier test because those put the marker LAST or first. It
    takes a marker in the MIDDLE of three to see it — which is exactly ¶8.2's
    obligation 3 ("a segment list can hold several markers at once, so a partial
    collapse is now easy to write by accident") and exactly the M20 lesson about a
    negative test per rule branch. Rewritten as a structural recursion where the two
    `none`s cannot be confused. -/

example : (Val.arrFoldSegs? [Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 7]),
                             Val.segNode (Val.nat 1) (.loanM 0),
                             Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 9])]).isNone
    = true := by native_decide

-- …and the three positions a marker can take, so the branch cannot be lost again.
example : (Val.arrFoldSegs? [Val.segNode (Val.nat 1) (.loanM 0),
                             Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 9])]).isNone
    = true := by native_decide
example : (Val.arrFoldSegs? [Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 7]),
                             Val.segNode (Val.nat 1) (.bot)]).isNone
    = true := by native_decide

-- The positive control the bug would also have broken: three owned segments fold to
-- the full three-element run, not a prefix of it.
example : ((Val.arrFoldSegs? [Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 7]),
                              Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 8]),
                              Val.segNode (Val.nat 1) (.ctor "Arr" [Val.nat 9])]).map
             (Val.nfV 200)
           == some (.ctor "Arr" [Val.nat 7, Val.nat 8, Val.nat 9])) = true := by native_decide

/-! ### The differential harness, given array bodies

    Appendix A: "The differential harness (M8/M9) should gain array bodies before
    anything else is believed: the multi-marker collapse of ¶8.2's obligation 3 is
    precisely the bug class a per-rule-branch negative test exists to catch."

    The property is M9's, unchanged: for a `checkFn`-accepted caller, its CONCRETE
    final environment (executing mode — calls run the callee's real body) is a
    σ-instance of some accepted SYMBOLIC path's final environment (checking mode —
    calls use the §5.3/§6.1 signature rule). -/

def fill1 : FnDef := decl{ fn fill1 (l : &mut (Array 1 Nat)) -> Unit { (*l)[0] := 9; () } }

def bump : FnDef := decl{
  fn bump (l : &mut (Array 2 Nat)) -> Unit { (*l)[0] := 7; (*l)[1] := 8; () } }

def arrPool : List FnDef := [fill1, bump]

/-- A carved segment handed to a call, then the whole array demanded back. -/
def arrCaller1 : Term := dllbc defer_check {
  let a = Arr(3, 1, 2); let s = &mut a[1 ; 1]; fill1(s); let b = a; () }

/-- TWO carved segments, one passed to each of two calls, then rejoined — ¶3.6's
    "several captured loans in one owner" at the arity the doc calls new. -/
def arrCaller2 : Term := dllbc defer_check {
  let a = Arr(3, 1, 2, 7);
  let s = &mut a[0 ; 2]; let t = &mut a[2 ; 2];
  bump(s); bump(t);
  let b = a; () }

/-- Inline carving with no call at all: the residues never leave, so there is nothing
    for a group to forget. -/
def arrCaller3 : Term := dllbc{
  let a = Arr(3, 1, 2);
  let p = &mut a[0 ; 1]; let q = &mut a[1 ; 2];
  (*p)[0] := 5; (*q)[1] := 6;
  let b = a; () }

def arrCallers : List Term := [arrCaller1, arrCaller2, arrCaller3]

example : arrCallers.all (fun b => Migrate.progOkOf (Dllbc.Tests.S9Diff.callerDecl b) arrPool)
    = true := by native_decide

example : arrCallers.all (fun b => Dllbc.Tests.S9Diff.diffV2 false arrPool b)
    = true := by native_decide

/-! ### FINDING — the simulation relation needed an array case, and the harness said so

    The first array body handed to `diffV2` reported a counterexample, and it was a
    FALSE one. Checking mode ends with

        b ↦ Arr⟨1 ▷ [3], 1 ▷ σ₀, 1 ▷ [2]⟩

    where executing mode ends with `b ↦ [3, 9, 2]`. Both are right. Merge concatenates
    runs but leaves a σ body alone — it must, since two σ's have no run to concatenate
    — so a checking-mode group release, which mints a fresh existential at the
    segment's owed type, blocks exactly the rejoin the concrete run performs. The
    values agree; the TREES do not.

    So the relation had to learn ¶1.3's fold: an array is compared up to its snapshot,
    which means splitting the concrete run by the symbolic extents and matching
    segment-wise (`matchVal`'s `§segs`-vs-run case, S9Diff). This is §6.1's
    already-flagged over-approximation — "a group releases atomically where the
    concrete machine ends lazily" — arriving for arrays, and ¶3.6 predicts exactly
    that: "any simulation relation that reconciled the old case reconciles this one".
    It does, but not for free: the old relation was structural, and arrays are the
    first values in the calculus whose state form is coarser than their value. Worth
    knowing before the metatheory is written, since obligation 4 (merge is
    value-preserving) is what the new case silently assumes. -/

/-! ## (v) Symbolic element access, the exhaustive split, and where it stops

    ¶3.5's note on what range places replace: M13's `nth2` carries
    `pij : Le (S i) j` and `p2 : Le (S j) (len *v)`, and "the evidence has been
    threaded through every swap site since M13 … Range places take the same terms and
    give them their real job". So the obligation at `a[i]` had better BE that term. -/

/-! ### Premise (2) must be spelled the way a program writes it

    Two adjustments, neither changing what the premise MEANS, both required for it to
    be dischargeable at all.

    First, the end of the range. `add` recurses on its FIRST argument, so `add lo cnt`
    is stuck whenever `lo` is symbolic — and at every `a[i]` the count is literally 1,
    making the obligation read `Le (add i (S Z)) n`. No program writes that, and no
    lemma in the library produces it. `S i` denotes the same number, is definitionally
    a constructor tree, and is exactly M14's cursor bound. A concrete count is
    therefore unrolled into successors; a symbolic one keeps `add`, where it computes.

    Second, the containment is stated LEAF-RELATIVELY when the leaf-relative offset is
    already known. `Le` computes by double `natRec`, so `Le (add b cnt) (add b m)` is
    stuck on a symbolic `b` and never converts with the `Le cnt m` a program can
    supply. Premise (3)'s own logic is that offsets are leaf-relative; premise (2)
    should be too. -/

def idxCited : FnDef := decl{
  fn idxCited (n : Nat, i : Nat, h : Le (S i) n, a : &mut (Array n Nat)) -> Unit {
    let e = &mut (*a)[i | h]; () } }
example : Migrate.progOkOf idxCited = true := by native_decide

-- The same bound serves a width-1 RANGE, so the two spellings of "one slot" agree on
-- what they demand even though they differ on what they hand back (¶2.1).
def rng1Cited : FnDef := decl{
  fn rng1Cited (n : Nat, i : Nat, h : Le (S i) n, a : &mut (Array n Nat)) -> Unit {
    let e = &mut (*a)[i ; 1 | h]; () } }
example : Migrate.progOkOf rng1Cited = true := by native_decide

-- Not vacuous: the bound is the one thing being checked, and a weaker one fails.
def idxWeakBound : FnDef := decl{
  fn idxWeakBound (n : Nat, i : Nat, h : Le i n, a : &mut (Array n Nat)) -> Unit {
    let e = &mut (*a)[i | h]; () } }
example : Migrate.progRejectsOf idxWeakBound "containment obligation" = true := by native_decide

/-! ### The exhaustive two-way split, with a call

    ¶5's `split_at_mut` shape: carve the left half against a cited bound, take the rest
    with `..`, and hand one half to a callee. The residues never leave — `σ_r` is the
    same σ before and after the call — so the frame is not described, it is simply
    still there (¶3.6). -/

def threeWayTouch : FnDef := decl{ fn threeWayTouch (p : Nat, l : &mut (Array p Nat)) -> Unit { () } }

def splitTwo : FnDef := decl{
  fn splitTwo (n : Nat, i : Nat, h1 : Le i n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i | h1];
    let r = &mut (*a)[i ; ..];
    threeWayTouch(i, l);
    () } }
example : Migrate.progOkOf splitTwo [splitTwo, threeWayTouch] = true := by native_decide

/-! ### FINDING — the THREE-way split ¶6's quicksort needs does not check, and the
    reason is the residue's namelessness rather than anything about the carve

    ¶6 writes the migrated quicksort as a three-way carve — left half, pivot slot,
    right half — and lists its cost honestly as "the partition leaf must now produce
    its pivot index TOGETHER WITH the two carve licenses". That understates it. Write
    it out:

    ```
    let l = &mut (*v)[Z    ; i | h];   -- obligation `Le i n`        — writable
    let p = &mut (*v)[i];             -- obligation `Le 1 rest`     — NOT writable
    let r = &mut (*v)[S i ; ..];
    ```

    The second carve is base-aligned into the residue leaf, so premise (2) asks for
    `Le 1 rest` — leaf-relative and correct, and the sharpest possible statement of
    the obligation. But `rest` is the σ premise (3) minted inside the FIRST carve. It
    has no binder, so no term of that type can be written, and no license the partition
    returns can mention it either.

    So `..` is not enough. It names the residue as a PLACE, which is what ¶3.4's second
    borrow needs; it does not name the residue's LENGTH, which is what any evidence
    about the residue, and any call taking the residue, both need. The same wall stops
    ¶3.6's `merge_into (r : &mut Array q Nat)` from being callable.

    Three routes. (a) Let the program SUPPLY the residue rather than have the checker
    mint it — `a[lo ; cnt ; rest | h]`, with premise (3) solving `m ≡ add lo' (add cnt
    rest)` against the supplied term instead of a fresh σ. This keeps premise (3)
    exactly as it is (still a solution transition, still no `sub`), reduces to the
    current behaviour when omitted, and is ¶8.4's own escape hatch: "name the equation
    and carry it, rather than solving it". (b) Let the carve BIND its residue in the
    surface. (c) Σ-typed slices, `Σ (c : Nat). &mut (Array c T)`, which ¶4 claims needs
    "no new type" — true, but PROBED here and it needs new machinery: `seedTelescope`
    has no case for a borrow under a type constructor, so the parameter is rejected by
    `readC`, and `collectResultBorrows` has no dependent-Σ case for returning one.

    (a) is the smallest and the one that fits the existing rule. Recorded rather than
    built: it changes the surface of the design's one new rule, which is the team
    lead's call, not this milestone's. -/

def pivotCarve : FnDef := decl{
  fn pivotCarve (n : Nat, i : Nat, h1 : Le i n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i | h1];
    let p = &mut (*a)[i];
    let r = &mut (*a)[S i ; ..];
    () } }
example : Migrate.progRejectsOf pivotCarve "containment obligation" = true := by native_decide

/-! ## (vi) The Σ-typed slice, PROBED — ¶4's runtime-length slice, built and settled

    ¶4 says `Σ (c : Nat). &mut (Array c T)` is "an ordinary Σ over a borrow, which §5.2
    already declares well-formed. **No new type.**" That is true of the TYPE. It is not
    true of the machine: §5's second opacity, "borrows stored under a type constructor",
    had never reached a telescope entry. Two serious attempts, both landed, so the
    question is answered by a working implementation rather than by argument.

    ATTEMPT 1, the callee side (`seedTelescope`): the slot holds a genuine pair, so the
    length is a σ the body can name and the borrow carries an ordinary obligation.

    ATTEMPT 2, the caller side (`processArgs`): the actual is a pair, the capture is the
    borrow's loan, the length is checked like any other argument.

    Both work. **And it does not solve the residue problem**, which is the point of the
    probe: a caller must PRODUCE the length to construct the pair, so the Σ-slice serves
    exactly the slices whose length was already nameable — the case that never needed
    it. The tests below are the settlement, not a feature demo. -/

def sigSlice : FnDef := decl{
  fn sigSlice (s : Σ (c : Nat) → &mut (Array c Nat)) -> Unit { () } }
example : Migrate.progOkOf sigSlice = true := by native_decide

-- The callee can DESTRUCTURE it: an owned match hands back the length and the borrow,
-- and inside the body the length is an ordinary nameable term.
def useSlice : FnDef := decl{
  fn useSlice (s : Σ (c : Nat) → &mut (Array c Nat)) -> Unit {
    match s { Pair(c, sl) => () } } }
example : Migrate.progOkOf useSlice = true := by native_decide

def sliceTouch : FnDef := decl{
  fn sliceTouch (s : Σ (c : Nat) → &mut (Array c Nat)) -> Unit { () } }

-- A caller passing a slice whose length it can NAME: green, end to end.
def sigCallerOk : FnDef := decl{
  fn sigCallerOk (n : Nat, i : Nat, h1 : Le i n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i | h1];
    let r = &mut (*a)[i ; ..];
    sliceTouch(Pair(i, l));
    () } }
example : Migrate.progOkOf sigCallerOk [sigCallerOk, sliceTouch] = true := by native_decide

/-! ### …and the residue still cannot be passed, which settles route (c)

    The only length in scope is `i`, and for the residue it is the wrong one. The
    checker says so rather than silently accepting — so there is no smuggling the
    residue through with a length that happens to be nameable. And there is no right
    term to write, because the residue's length is the σ premise (3) minted. -/

def sigCallerWrong : FnDef := decl{
  fn sigCallerWrong (n : Nat, i : Nat, h1 : Le i n, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i | h1];
    let r = &mut (*a)[i ; ..];
    sliceTouch(Pair(i, r));
    () } }
example : Migrate.progRejectsOf sigCallerWrong "does not have its parameter type" [sigCallerWrong, sliceTouch]
    = true := by native_decide

-- A second, independent wall for route (c): a RECURSIVE slice-taking callee needs a
-- fuel bound ABOUT the slice's length, and that length lives inside the Σ where no
-- telescope entry can mention it. Nesting the proof inside too is where it goes, and
-- that is a second level the machinery does not have.
def recSlice : FnDef := decl{
  fn recSlice [fuel] (fuel : Nat, s : Σ (c : Nat) → Σ (h : Le c fuel) → &mut (Array c Nat)) -> Unit {
    () } }
example : Migrate.progRejectsOf recSlice "only valid at a telescope position" = true := by native_decide

/-! ### Route (a)'s payoff, verified on the arithmetic alone

    Supplying the residue does not merely NAME it — it makes the obligation that could
    not be written disappear. After `σ_rest := S j` the pivot carve's leaf-relative
    obligation `Le 1 σ_rest` reduces to `Le Z j`, which is ⊤ and needs no evidence at
    all. Stuck while the residue is a bare σ; free the moment it has a shape. -/

example : (Val.nfV 300 (Val.kLe (Val.nat 1) (.ctor "S" [.sym 0])) == .const "Unit")
    = true := by native_decide
example : (Val.nfV 300 (Val.kLe (Val.nat 1) (.sym 0)) == .const "Unit")
    = false := by native_decide

/-! ## (vii) ROUTE (a) — the program supplies the residue, and ¶6's carve unblocks

    `a[lo ; cnt ; rest | h]` supplies premise (3)'s residue extent instead of letting
    the checker mint a σ no binder can name. Premise (3) is otherwise untouched — the
    same solution transition, still no `sub` — and omitting the slot restores the
    minting behaviour exactly.

    This is the third instance of a house pattern: an OPTIONAL surface element that
    reifies something the checker already knows, declared rather than inferred, costing
    nothing when absent. §1.2's `[k]` names the decreasing position; §3.2's `match h :`
    names the branch equation; `a[lo ; cnt ; rest]` names the residue extent. In all
    three the checker had the fact and the program could not cite it, and in all three
    the fix is a binder-free naming rather than new semantics.

    **The ordering is the trick.** The supplied equation is solved BEFORE premise (2)
    is formed, so the obligation is stated over a decomposed extent — and then it often
    computes away entirely. ¶3.2 says `Le a b` "is precisely the assertion that `b`
    decomposes as `a` plus something", so supplying the decomposition supplies most of
    the proof. -/

/-- ¶6's THREE-WAY carve: left half | pivot slot | right half, all three live at once.

    ```rust
    let l = &mut (*v)[Z    ; i ; S j | le_add i (S j)];
    let p = &mut (*v)[i    ; 1 ; j];        -- obligation ⊤; no evidence needed
    let r = &mut (*v)[S i  ; ..];           -- degenerate
    ```

    Exactly the shape ¶6 writes, and exactly the state it describes: "the pivot element
    sits between two live borrows as a third segment that neither call can see. (Which
    is correct: the pivot is in its final position and must not move. The calculus is
    enforcing that, for free, by the same mechanism that keeps the halves apart.)"

    The two obligations are the two the design predicts. The first is `Le i (add i (S j))`
    — `le_add`, which the library already had for M22. The second is `Le 1 (S j)`, which
    reduces to `Le Z j` and then to ⊤, so **the carve that could not be written at all
    now needs no evidence whatsoever**. -/
def threeWay : FnDef := decl{
  fn threeWay (n : Nat, i : Nat, j : Nat, heq : Id Nat n (add i (S j)),
               a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; S j | le_add i (S j) | heq];
    let p = &mut (*a)[i ; 1 ; j];
    let r = &mut (*a)[S i ; ..];
    () } }
example : Migrate.progOkOf threeWay = true := by native_decide

-- …and the same conversion at THREE segments, which is where the invariant is
-- doing real work: `[Z ; i ; S j]`, `[i ; 1 ; j]` and `[S i ; ..]` are pairwise
-- disjoint by the decomposition the carves cite, and all three stay usable.
def threeWayAll : FnDef := decl{
  fn threeWayAll (n : Nat, i : Nat, j : Nat, heq : Id Nat n (add i (S j)),
                  a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; S j | le_add i (S j) | heq];
    let p = &mut (*a)[i ; 1 ; j];
    let r = &mut (*a)[S i ; ..];
    let z = *r;
    *r := z;
    let w = *p;
    *p := w;
    let x = *l;
    *l := x;
    () } }
example : Migrate.progOkOf threeWayAll = true := by native_decide


-- (the loan-id reading it replaced is above, CONVERTED to `threeWayAll`.)

-- The pivot carve needs NO cited evidence, which is route (a)'s second payoff and the
-- reason it beats merely naming the residue: `Le 1 rest` was unwritable, and after
-- `rest := S j` the obligation is ⊤. Dropping `le_add` from the FIRST carve, whose
-- obligation does not compute away, is still rejected.
def threeWayNoFirstEv : FnDef := decl{
  fn threeWayNoFirstEv (n : Nat, i : Nat, j : Nat, heq : Id Nat n (add i (S j)),
                        a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; S j | le_refl i | heq];
    let p = &mut (*a)[i ; 1 ; j];
    () } }
example : Migrate.progRejectsOf threeWayNoFirstEv "containment obligation" = true := by native_decide

/-- **The DECOMPOSITION CITATION's negative control**, and the one the M25 ruling turns
    on. Supplying a residue asserts that the leaf's extent decomposes as `add cnt rest`.
    When the extent is a telescope parameter's σ that assertion is a constraint on this
    function's CALLERS, and premise (3) refuses to impose it by unification — the
    program must CITE the equation, exactly as M17 requires of every other cross-boundary
    constraint. Before the ruling this checked, and a caller instantiating `n = 2` with
    `i = j = 5` checked with it and then got STUCK when executed. -/
def threeWayUncited : FnDef := decl{
  fn threeWayUncited (n : Nat, i : Nat, j : Nat, a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; S j | le_add i (S j)];
    () } }
example : Migrate.progRejectsOf threeWayUncited "may not impose it by refining" = true := by
  native_decide

-- …and the citation's TYPE is what licenses: a well-typed equation about the wrong
-- decomposition selects nothing.
def threeWayWrongEq : FnDef := decl{
  fn threeWayWrongEq (n : Nat, i : Nat, j : Nat, heq : Id Nat n (add i (S (S j))),
                      a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; S j | le_add i (S j) | heq];
    () } }
example : Migrate.progRejectsOf threeWayWrongEq "cited decomposition does not have type" = true := by
  native_decide

-- A LYING residue is rejected: the supplied extent must actually decompose the leaf,
-- and premise (3) is the thing that checks it. Here `j` is claimed where `S j` is
-- needed, so the solution transition has no solution.
def threeWayLyingResidue : FnDef := decl{
  fn threeWayLyingResidue (n : Nat, i : Nat, j : Nat, heq : Id Nat n (add i j),
                           a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; j | le_add i j | heq];
    let p = &mut (*a)[i ; 1 ; j];
    () } }
example : Migrate.progOkOf threeWayLyingResidue = false := by native_decide

-- …and the residue is genuinely CONSUMED, not decoration: with it supplied the right
-- half's extent is the program's `j`, so a callee taking `Array j Nat` receives it
-- with no coercion and no unnameable σ in sight. This is the call that finding (a)
-- said was unwritable.
def sliceTake : FnDef := decl{ fn sliceTake (q : Nat, s : &mut (Array q Nat)) -> Unit { () } }

def threeWayCall : FnDef := decl{
  fn threeWayCall (n : Nat, i : Nat, j : Nat, heq : Id Nat n (add i (S j)),
                   a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; S j | le_add i (S j) | heq];
    let p = &mut (*a)[i ; 1 ; j];
    let r = &mut (*a)[S i ; ..];
    sliceTake(i, l);
    sliceTake(j, r);
    () } }
example : Migrate.progOkOf threeWayCall [threeWayCall, sliceTake] = true := by native_decide

/-! ### The extent map's running base is spelled `S^k b` too

    Same reason as R7's range end, found by the third carve: the segment after a
    width-1 pivot has base `add i 1`, which is stuck on a symbolic `i` and never
    converts with the `S i` a program writes. A concrete count advances the base by
    successors; a symbolic one keeps `add`, where it computes. Without this,
    `(*a)[S i ; ..]` cannot find the segment it just created. -/

example : Migrate.progOkOf (decl{
  fn baseSpelling (n : Nat, i : Nat, j : Nat, heq : Id Nat n (add i (S j)),
                   a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; S j | le_add i (S j) | heq];
    let p = &mut (*a)[i ; 1 ; j];
    let r = &mut (*a)[S i ; j];
    () } }) = true := by native_decide


/-! ## (viii) The ARRAY LIBRARY — ¶1.3's promise, and ¶6's crux claim

    ¶1.3: "Every lemma in the quicksort library — `count`, `Sorted`, `Bound`, the order
    stack — transfers to arrays by replacing `listRec` with `arrRec` and `Cons` with
    `acons`. Nothing about the migration requires re-deriving that mathematics."

    ¶6, on the glue: "Set `append ↦ arrCat` and `Cons p b ↦ arrCat (asingle p) r` and it
    IS the array lemma, hypothesis for hypothesis — not merely the same shape but the
    same statement modulo the container … So the migration INHERITS that proof rather
    than opening a stratum. Claim exactly that and no wider: **one stratum deleted
    outright** (locality), **one inherited** (the pivot glue), **none invented**."

    Both claims are checkable and both check. The definitions and proofs in `StdLemmas`
    are their list counterparts with that substitution applied and nothing else. -/

def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasType 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

open Dllbc.StdLemmas (countA SortedA UbA LbA BoundA asingle
  sorted_headA sorted_headA_ty sorted_tailA sorted_tailA_ty
  ub_headA ub_headA_ty ub_tailA ub_tailA_ty lb_boundA lb_boundA_ty
  bound_arrCat bound_arrCat_ty sorted_arrCat sorted_arrCat_ty
  count_arrCat count_arrCat_ty
  count_acons_hit count_acons_hit_ty count_acons_miss count_acons_miss_ty
  noAbove_of_ubA noAbove_of_ubA_ty ub_of_noAboveA ub_of_noAboveA_ty
  ub_permA ub_permA_ty noBelow_of_lbA noBelow_of_lbA_ty
  lb_of_noBelowA lb_of_noBelowA_ty lb_permA lb_permA_ty
  count_swap2 count_swap2_ty leb_true_le leb_false_gt le_pred_l)

-- The predicates COMPUTE, on a run and on the cons view alike.
example : (pv pure{ countA 2 4 Arr(1, 2, 2, 3) } == Val.nat 2) = true := by native_decide
example : (pv pure{ SortedA 3 Arr(1, 2, 3) } == pv pure{ SortedA 3 Arr(1, 2, 3) })
    = true := by native_decide
example : chk pure{ Pair(unit, Pair(unit, Pair(unit, unit))) } pure{ SortedA 3 Arr(1, 2, 3) }
    = true := by native_decide
-- …and an unsorted array's `SortedA` is uninhabited, so the predicate is not vacuous.
example : chk pure{ Pair(unit, Pair(unit, Pair(unit, unit))) } pure{ SortedA 3 Arr(3, 2, 1) }
    = false := by native_decide

-- `arrCat (asingle p) b` IS the array `Cons p b`: the doc's spelling of the pivot
-- splice reaches the cons view by computation, with no lemma relating them.
example : (pv pure{ arrCat 1 2 (asingle 9) Arr(1, 2) } == pv pure{ Arr(9, 1, 2) })
    = true := by native_decide

/-! ### The five helpers and the glue, each its list proof with the container swapped -/

example : chkL sorted_headA sorted_headA_ty = true := by native_decide
example : chkL sorted_tailA sorted_tailA_ty = true := by native_decide
example : chkL ub_headA ub_headA_ty = true := by native_decide
example : chkL ub_tailA ub_tailA_ty = true := by native_decide
example : chkL lb_boundA lb_boundA_ty = true := by native_decide
example : chkL bound_arrCat bound_arrCat_ty = true := by native_decide

/-- **The crux.** `sorted_append_pivot` with `append ↦ arrCat` and `Cons p b ↦
    arrCat (asingle p) r`, hypothesis for hypothesis, and nothing else changed. -/
example : chkL sorted_arrCat sorted_arrCat_ty = true := by native_decide

/-- ¶6's other named survivor: "the one lemma that replaces `count_append`/`take`/`drop`
    is `count_arrCat`, which is the same induction". It is the same induction — the
    dependent Bool-elim on `eqb x h` transfers unchanged, because `countA` unfolds on an
    `acons` exactly as `count` unfolds on a `Cons`. First try. -/
example : chkL count_arrCat count_arrCat_ty = true := by native_decide

/-! ### The permutation keystone, transferred

    M23's hardest single step: "`Ub`/`Lb` (Σ-chains over the spine) are not natively
    permutation-invariant. M22 named the route at the positional encoding: cross to the
    multiset, where the property is `Π x. x > p → count x l = Z` and permutation-
    invariance is a one-line `id_trans`." The crossing transfers with the container like
    everything else — all eight lemmas, first try. -/

example : chkL count_acons_hit count_acons_hit_ty = true := by native_decide
example : chkL count_acons_miss count_acons_miss_ty = true := by native_decide
example : chkL noAbove_of_ubA noAbove_of_ubA_ty = true := by native_decide
example : chkL ub_of_noAboveA ub_of_noAboveA_ty = true := by native_decide
example : chkL ub_permA ub_permA_ty = true := by native_decide
example : chkL noBelow_of_lbA noBelow_of_lbA_ty = true := by native_decide
example : chkL lb_of_noBelowA lb_of_noBelowA_ty = true := by native_decide
example : chkL lb_permA lb_permA_ty = true := by native_decide

/-! ### FINDING — the transfer needed three ι-rules to be MECHANICAL rather than merely possible

    ¶1.3's promise is about the mathematics, and the mathematics did transfer verbatim.
    What it does not mention is that the array constants have to compute the way the list
    constructors do, or every step of a transferred proof wants a transport lemma the
    list proof needs none of.

    Two rules, both in `Pure.lean`. `arrCat` computes on an `acons`-headed left argument
    (`arrCat (acons x xs) b ⇝ acons x (arrCat xs b)`), which is `append (Cons h t) u ⇝
    Cons h (append t u)`; and `arrRec` fires on the cons view, so a predicate over arrays
    unfolds on an `acons` exactly as its counterpart unfolds on a `Cons`. Without them
    `SortedA (arrCat (acons h t) …)` does not UNFOLD, and `sorted_append_pivot`'s proof
    turns entirely on that unfolding — its own docstring says "Both components are
    definitional … which is why no `list_rw` transport appears anywhere in this proof."

    A third rule was needed and is the one worth recording, because it was invisible
    until the glue was written: a nonempty RUN on the left with a non-run on the right
    peels its head into an `acons`. `asingle p` COMPUTES to the run `[p]`, so ¶6's own
    spelling `arrCat (asingle p) r` was stuck for symbolic `r` — the doc's chosen
    notation could not reach the cons view it is notation FOR. The rule is the same one
    read through the other view: a literal is a cons spine that happens to be written
    flat. -/



/-! ## (ix) THE CONVERSION IN MINIATURE — a verified in-place array sort

    Everything above composes here: index places, the carve on a SYMBOLIC array, branch
    equations, the transferred library, `old *v`, and the §5.4 exit-snapshot audit. The
    postcondition is M23's quicksort signature at width two —

        Σ (hs : SortedA 2 (*a)) → (Π x. Id Nat (countA x 2 (*a)) (countA x 2 (old *a)))

    — sortedness AND count-preservation over the exit snapshot, with **zero declared
    backs**. It is not the full quicksort (¶6's partition is a new program, ledger G4),
    but it is the whole stack end to end on a real in-place mutation, which is what the
    full one will be made of. -/

-- Writing known values through index places, then proving sortedness of the exit.
def setSorted : FnDef := decl{
  fn setSorted (a : &mut (Array 2 Nat)) -> SortedA 2 (*a) {
    (*a)[0] := 1;
    (*a)[1] := 2;
    Pair(unit, Pair(unit, unit)) } }
example : Migrate.progOkOf setSorted = true := by native_decide

-- …and the same body with the writes the wrong way round is rejected: `SortedA` unfolds
-- to `Σ Bot. …`, so the predicate is not vacuous.
def setSortedLie : FnDef := decl{
  fn setSortedLie (a : &mut (Array 2 Nat)) -> SortedA 2 (*a) {
    (*a)[0] := 2;
    (*a)[1] := 1;
    Pair(unit, Pair(unit, unit)) } }
example : Migrate.progOkOf setSortedLie = false := by native_decide

/-- Reading a SYMBOLIC array's elements turns it into a run of named elements. This is
    the step that makes an in-place algorithm provable at all: `σ_a : Array 2 Nat` is
    opaque, and after two index reads the payload is `[σ₀, σ₁]` with both elements in
    scope — carve, then `elementize`, then the ordinary copy-on-read. -/
def readTwo : FnDef := decl{
  fn readTwo (a : &mut (Array 2 Nat)) -> Unit {
    let x = (*a)[0];
    let y = (*a)[1];
    () } }

/-! ### …and at INDEX places the conversion FAILS, for a reason worth having

    The deleted Ω assertion read `a`'s payload back as a two-segment node with the
    takes at distinct positions. The conversion attempted here — take both, refill
    both, and let the obligation audit demand that the takes were disjoint — does
    not work, and the twin below is what says so rather than a hunch.

    **Taking index 0 TWICE is ACCEPTED.** §2.1's copy-on-read is why: a concrete
    `Nat` element is INDEX-KIND, so a take COPIES and leaves no hole, and there is
    no linearity at a copyable element type for a body to observe. The segment
    structure the Ω assertion read is therefore an implementation detail at this
    element type — unobservable through the language, with the behaviour covered by
    the executing differential — and the assertion is recorded LOST on exactly that
    rationale rather than replaced by something weaker that would still be green.

    The disjointness invariant itself is not lost: `halvesBoth`/`halvesSame` and
    `threeWayAll` above demand it at SEGMENT places, where the payload is an array
    rather than an element and the linearity is real. -/

def readSame : FnDef := decl{
  fn readSame (a : &mut (Array 2 Nat)) -> Unit {
    let x = (*a)[0];
    let y = (*a)[0];
    (*a)[0] := y;
    () } }
-- The record of why the conversion fails, asserted rather than described.
example : Migrate.progOkOf readSame = true := by native_decide

/-- **The miniature.** An in-place two-element sort over a symbolic borrow, verified
    `Sorted ∧ Perm` over the exit snapshot, zero backs. Both paths mutate or not through
    index places, and the audit judges the collapsed payload against a postcondition that
    names `*a` (exit) and `old *a` (entry). -/
def sort2 : FnDef := decl{
  fn sort2 (a : &mut (Array 2 Nat))
      -> Σ (hs : SortedA 2 (*a)) → (Π (x : Nat) → Id Nat (countA x 2 (*a)) (countA x 2 (old *a))) {
    let x = (*a)[0];
    let y = (*a)[1];
    if h : leb x y {
      Pair(Pair(leb_true_le x y h, Pair(unit, unit)), λ (n : Nat). Refl)
    } else {
      (*a)[0] := y;
      (*a)[1] := x;
      Pair(Pair(le_pred_l y x (leb_false_gt x y h), Pair(unit, unit)),
           λ (n : Nat). count_swap2 n x y)
    } } }
example : Migrate.progOkOf sort2 = true := by native_decide

/-! ### Lying twins, one per conjunct — M23's discipline, applied here -/

-- Forget the swap and still claim sortedness. The False branch's goal is `Le x y`,
-- which is exactly what the branch equation says is FALSE.
def sort2LieSorted : FnDef := decl{
  fn sort2LieSorted (a : &mut (Array 2 Nat)) -> SortedA 2 (*a) {
    let x = (*a)[0];
    let y = (*a)[1];
    if h : leb x y {
      Pair(leb_true_le x y h, Pair(unit, unit))
    } else {
      Pair(le_pred_l y x (leb_false_gt x y h), Pair(unit, unit))
    } } }
example : Migrate.progOkOf sort2LieSorted = false := by native_decide

-- Do the swap, then claim the counts did not move. `count_swap2` is genuinely load-
-- bearing: `Refl` in its place is rejected.
def sort2LieCount : FnDef := decl{
  fn sort2LieCount (a : &mut (Array 2 Nat))
      -> Σ (hs : SortedA 2 (*a)) → (Π (x : Nat) → Id Nat (countA x 2 (*a)) (countA x 2 (old *a))) {
    let x = (*a)[0];
    let y = (*a)[1];
    if h : leb x y {
      Pair(Pair(leb_true_le x y h, Pair(unit, unit)), λ (n : Nat). Refl)
    } else {
      (*a)[0] := y;
      (*a)[1] := x;
      Pair(Pair(le_pred_l y x (leb_false_gt x y h), Pair(unit, unit)), λ (n : Nat). Refl)
    } } }
example : Migrate.progOkOf sort2LieCount = false := by native_decide


end Dllbc.Tests.S24Arrays
