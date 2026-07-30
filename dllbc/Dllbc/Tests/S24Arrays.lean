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
example : expectErr dllbc{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[2 ; 3];
                           () }
  "no leaf" = true := by native_decide

-- OUT OF RANGE — premise (2) has no inhabitant and none can be supplied, because
-- `Le (add lo cnt) n` computes to ⊥.
example : expectErr dllbc{ let a = Arr(3, 1, 2); let m = &mut a[1 ; 3]; () }
  "containment obligation" = true := by native_decide
example : expectErr dllbc{ let a = Arr(3, 1, 2); let x = a[3]; () }
  "containment obligation" = true := by native_decide

-- A HOLE is not owned. `⇒` at a range place takes the run out and leaves one, and
-- until the ⇐-refill closes it no carve may split across it.
example : expectErr dllbc{ let a = Arr(3, 1, 2);
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
example : expectErr dllbc{ let a = Arr(3, 1, 2, 7, 5);
                           let p = &mut a[0 ; 3];
                           let q = &mut a[1];
                           (*p)[0] := 4;
                           () }
  "⊥" = true := by native_decide


end Dllbc.Tests.S24Arrays
