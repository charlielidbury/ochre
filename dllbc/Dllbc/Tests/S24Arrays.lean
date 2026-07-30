import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.PureMacro
import Dllbc.DeclMacro

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
example : hasStateMarker carvedWithLoan = true := by native_decide
example : hasStateMarker (segsOf [(1, .sym 0), (2, .sym 1)]) = false := by native_decide
-- A hole in a segment is state too: `⇒` at a range place leaves one (¶2.2's
-- take-and-refill generalized from a borrow's payload to a run of an array).
example : hasStateMarker (segsOf [(1, .sym 0), (2, .bot)]) = true := by native_decide

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

end Dllbc.Tests.S24Arrays
