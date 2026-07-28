import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S17Spec

/-!
# §19 test suite — partition (model + imperative), built on the M18 stack

This milestone assembles the crystallized architecture into its first real
algorithm: an in-place Lomuto partition through a mutable borrow, whose declared
backward spec is the pure `partitionL` model, checked by conversion per path.

It opens with the smallest complete instance of the architecture — a `swapS`
caller that recovers the precise `swapL i j s` (M17) and certifies its count with
`count_swapL'` (M18) — and gates the imperative body on a machine probe: splitting
the driver on a STUCK Bool spine (`leb x pivot`, x symbolic), which the current
substitution-based ⇜ cannot do without generalizing the spine first.
-/

open Dllbc
open Dllbc.StdLemmas (swapL count_swapL' set nth partScanL partScanRangeL partIdxL
  partIdxRangeL partGapRangeL partScanSizeL len_partitionRangeL len_sortRangeL sortRangeL
  partitionRangeL partitionL le_up_r le_add le_add_l le_add_succ le_rw_r le_rw_l le_add_mono_l
  add_succ le_trans id_sym id_trans id_congr hshift_true hshift_false len_swapL add_zero add_assoc)

namespace Dllbc.Tests.S19Partition

/-- Type-check a closed term against a closed type in the pure seed (as in §18). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## M19-A: the `count_swapL'` corollary and its `le_up_r` glue -/

example : chk StdLemmas.le_up_r StdLemmas.le_up_r_ty = true := by native_decide
example : chk StdLemmas.count_swapL' StdLemmas.count_swapL'_ty = true := by native_decide

-- M20-2 length-equation plumbing: the bound-derivation glue.
example : chk StdLemmas.le_add StdLemmas.le_add_ty = true := by native_decide
example : chk StdLemmas.le_add_l StdLemmas.le_add_l_ty = true := by native_decide
example : chk StdLemmas.le_add_succ StdLemmas.le_add_succ_ty = true := by native_decide
example : chk StdLemmas.le_rw_r StdLemmas.le_rw_r_ty = true := by native_decide
example : chk StdLemmas.hshift_true StdLemmas.hshift_true_ty = true := by native_decide
example : chk StdLemmas.hshift_false StdLemmas.hshift_false_ty = true := by native_decide

/-! ## M19-A opener — the architecture's smallest complete instance

    A `swapS` caller over a SYMBOLIC list: it borrows `s`, swaps positions `i`/`j`
    in place (imperative mutation), and its result is the count-preservation
    CERTIFICATE `count_swapL' m i j s pij p2`. After the swap the M17 spec-end
    recovers `s = swapL i j σ` precisely; the certificate — computed over the entry
    snapshot, whose subject `swapL i j s` is definitionally that recovered value —
    proves `count m (swapL i j s) = count m s` in the caller's own environment.
    Imperative mutation + precise recovery (M17) + pure lemma (M18), end to end. -/

-- s=0, m=1, i=2, j=3, pij=4, p2=5; body binders cert=6, b=7.
def certSwapCount : Decl :=
  decl{ fn certSwapCount (s : List Nat, m : Nat, i : Nat, j : Nat,
        pij : Le (S i) j, p2 : Le (S j) (len s)) -> Id Nat (count m (swapL i j s)) (count m s)
        { let cert = count_swapL' m i j s pij p2;
          let b = &mut s;
          swapS(b, i, j, pij, p2);
          cert } }

def openerTable : List Decl := [Dllbc.Tests.S17Spec.nthS, Dllbc.Tests.S17Spec.nth2S, Dllbc.Tests.S17Spec.swapSN, certSwapCount]
example : checkFnOk certSwapCount openerTable = true := by native_decide

-- Negative control: claim the count GREW by one across the swap. The certificate
-- proves equality, so the value-returning audit rejects the lying return type —
-- the opener's acceptance is a real check of a real certificate.
def certSwapCountLie : Decl :=
  decl{ fn certSwapCountLie (s : List Nat, m : Nat, i : Nat, j : Nat,
        pij : Le (S i) j, p2 : Le (S j) (len s)) -> Id Nat (count m (swapL i j s)) (S (count m s))
        = %certSwapCount.body }
example : checkFnErr certSwapCountLie "does not have return type" [Dllbc.Tests.S17Spec.nthS, Dllbc.Tests.S17Spec.nth2S, Dllbc.Tests.S17Spec.swapSN, certSwapCountLie] = true := by native_decide

/-! ## M20-2 (conformance, base case) — the pivot placement, checked against its spec

    The base of partition's recursion, isolated: place the pivot at the boundary
    `i` with a final swap, declared `back = baseBack` (partScanL's base — cased on
    `i` so the `i = Z` no-op is literally `*v`, not the stuck `swapL Z Z *v`). Cased
    on `i` because swapS cannot self-swap. The bound `pib : Le (S i) (len *v)`
    discharges swapS's `p2` after `i` refines to `S i'` (its `pij` is `Le Z i' = ⊤`,
    `unit`). Per path the declared spec refines with the scrutinee (`*v` on the
    no-op path, `swapL Z (S i') (*v)` on the swap path) and converts with swapS's
    composed backward tree — the §6.2 callee check now firing for a Unit-returning
    in-place body (the M20 auditAction extension). The mechanism partScan builds on. -/

open Dllbc.Tests.S17Spec (nthS nth2S swapSN)

-- The pivot-placement back-spec, CASED on i so the no-op path (i = Z) is literally
-- `*v` (not `swapL Z Z *v`, which is stuck on a symbolic list). Mirrors partScanL's
-- base. v=0, i=1. Used by the pivotPlace scaffolding fns' declared backs.
-- v=0, i=1, pib=2; body binder i2=3.
def pivotPlace : Decl :=
  decl{ fn pivotPlace (v : &mut List Nat, i : Nat, pib : Le (S i) (len *v)) -> Unit
        back = natRec (λ (a : Nat). List Nat) (*v) (λ (a : Nat). λ (l : List Nat). swapL Z (S a) (*v)) i
        { match i {
            Z => (),
            S(i2) => { swapS(v, Z, S(i2), (), pib); () }
        } } }
def confTable : List Decl := [nthS, nth2S, swapSN, pivotPlace]
example : checkFnOk pivotPlace confTable = true := by native_decide

/-! ## M20-2 (bound derivation) — the base swap's `p2` derived from the length eqn

    Same pivot placement, but the bound is DERIVED from the length equation the
    recursion carries (`hlen : len *v = S (add i g)`, the k=Z instance) rather than
    handed in directly. In the `S i'` branch the equation reduces definitionally to
    `len *v = S (S (add i' g))` (add on a constructor head), so `le_add i' g`
    (whose type is `Le (S (S i')) (S (S (add i' g)))` up to Le reduction) transports
    onto `len *v` via `le_rw_r (id_sym hlen)`. This validates the full
    length-equation → swapS-bound chain the recursive partScan threads. -/

-- v=0, i=1, g=2, hlen=3; body binder i2=4.
def pivotPlaceH : Decl :=
  decl{ fn pivotPlaceH (v : &mut List Nat, i : Nat, g : Nat,
        hlen : Id Nat (len *v) (S (add i g))) -> Unit
        back = natRec (λ (a : Nat). List Nat) (*v) (λ (a : Nat). λ (l : List Nat). swapL Z (S a) (*v)) i
        { match i {
            Z => (),
            -- Derive the bound in a `let` FIRST, while `v` is still live (the `len *v`
            -- read is comptime/non-consuming); THEN call swapS (which consumes `v`).
            S(i2) => {
              -- p2 = le_rw_r (S(S i')) (S(S(add i' g))) (len *v) (id_sym hlen) (le_add i' g)
              let p2 = le_rw_r (S (S i2)) (S (S (add i2 g))) (len *v)
                         (id_sym Nat (len *v) (S (S (add i2 g))) hlen)
                         (le_add i2 g);
              swapS(v, Z, S(i2), (), p2);
              ()
            }
        } } }
example : checkFnOk pivotPlaceH confTable = true := by native_decide

/-! ## M20-2 (the recursive partScan) — partition's scan loop, checked against partScanL

    The full recursive scan, declared `back = partScanL pivot k i g (*v)`. Telescope
    carries the length equation `hlen : len *v = S (add k (add i g))` (k-first, so the
    step reduces definitionally). Body mirrors the M19 executing partition; the three
    step cases each derive their swapS bound (let-FIRST, per the §5.3 finding) and
    recurse with an UPDATED hlen (an hshift arithmetic transport — definitional total,
    plus a len_swapL bridge in the swap case). resolveTree composes the recursive
    call's back-spec with swapS's, exactly as pivotPlace proved for one swap. -/

-- partScanLT survives the conversion: it builds the pure model the executing
-- differential `runScan` (below, a test SUBJECT) recovers against.
def partScanLT (pivot k i g l : Term) : Term := .app (.app (.app (.app (.app StdLemmas.partScanL pivot) k) i) g) l

-- v=0, k=1, i=2, g=3, pivot=4, hlen=5; binders k'=6, c/i'=7, g'/hlenX=8, pij=9, p2=10, hlenTSg=11.
def partScan : Decl :=
  decl{ fn partScan (v : &mut List Nat, k : Nat, i : Nat, g : Nat, pivot : Nat,
        hlen : Id Nat (len *v) (S (add k (add i g)))) -> Unit
        back = partScanL pivot k i g (*v)
        { match k {
            -- BASE (k = Z): place the pivot (pivotPlaceH's validated body; hlen reduces to k=Z form).
            Z => match i {
              Z => (),
              S(i2) => {
                let p2b = le_rw_r (S (S i2)) (S (S (add i2 g))) (len *v)
                            (id_sym Nat (len *v) (S (S (add i2 g))) hlen)
                            (le_add i2 g);
                swapS(v, Z, S(i2), (), p2b);
                ()
              }
            },
            -- STEP (k = S k'): the scan.
            S(k2) => {
              let c = leb (nth (S (add i g)) (*v)) pivot;
              match c {
                True => match g {
                  -- True, g = Z: advance boundary, no swap.
                  Z => {
                    let hlZ = id_trans Nat (len *v) (S (add (S k2) (add i Z))) (S (add k2 (add (S i) Z)))
                                hlen
                                (id_congr Nat Nat (λ (a : Nat). S a) (add (S k2) (add i Z)) (add k2 (add (S i) Z))
                                  (hshift_true k2 i Z));
                    partScan(v, k2, S(i), Z, pivot, hlZ)
                  },
                  -- True, g = S g': swap boundary↔scan, then advance.
                  S(g2) => {
                    let pij = le_add_succ i g2;
                    let p2 = le_rw_r (S (S (add i (S g2)))) (S (S (add k2 (add i (S g2))))) (len *v)
                               (id_sym Nat (len *v) (S (S (add k2 (add i (S g2))))) hlen)
                               (le_add_l (add i (S g2)) k2);
                    let hlS = id_trans Nat (len (swapL (S i) (S (add i (S g2))) (*v))) (len *v)
                                (S (add k2 (add (S i) (S g2))))
                                (len_swapL (S i) (S (add i (S g2))) (*v))
                                (id_trans Nat (len *v) (S (add (S k2) (add i (S g2)))) (S (add k2 (add (S i) (S g2))))
                                  hlen
                                  (id_congr Nat Nat (λ (a : Nat). S a) (add (S k2) (add i (S g2))) (add k2 (add (S i) (S g2)))
                                    (hshift_true k2 i (S g2))));
                    swapS(&mut *v, S(i), S(add i (S(g2))), pij, p2);
                    partScan(v, k2, S(i), S(g2), pivot, hlS)
                  }
                },
                -- False: grow gap, no swap.
                False => {
                  let hlF = id_trans Nat (len *v) (S (add (S k2) (add i g))) (S (add k2 (add i (S g))))
                              hlen
                              (id_congr Nat Nat (λ (a : Nat). S a) (add (S k2) (add i g)) (add k2 (add i (S g)))
                                (hshift_false k2 i g));
                  partScan(v, k2, i, S(g), pivot, hlF)
                }
              }
            }
        } } }
def scanTable : List Decl := [nthS, nth2S, swapSN, partScan]
example : checkFnOk partScan scanTable = true := by native_decide

/-! ## M21-3 — partScanRange: the subrange scan (partScan shifted by `lo`)

    `partScanRange(v, lo, k, i, g, pivot, hle)` — partScan over the range `[lo, …)`.
    Every position is `add lo`-shifted; the boundary `i` and gap `g` are RELATIVE
    to `lo`. The bound is now an INEQUALITY `hle : Le (add lo (S (add k (add i g))))
    (len *v)` — a sub-range does not span to the end, so the old equation is false;
    the Le is the honest invariant (the top scan/swap position stays < len). The
    M20 Id-toolkit ports through the new `le_rw_l`/`le_add_mono_l`/`add_succ`
    bridges: swap bounds are `le_trans` of a `le_add_mono_l` lifted from the entry
    bound, and each recursion threads `hle` via `le_rw_l` + `id_congr` through
    `λx. add lo (S x)` over the SAME hshift identities partScan uses. -/

def partScanRange : Decl :=
  decl{ fn partScanRange (v : &mut List Nat, lo : Nat, k : Nat, i : Nat, g : Nat, pivot : Nat,
        hle : Le (add lo (S (add k (add i g)))) (len *v)) -> Unit
        back = partScanRangeL pivot lo k i g (*v)
        { match k {
            -- BASE (k = Z): place the pivot at lo → lo+i (no-op when relative i = 0).
            Z => match i {
              Z => (),
              S(i2) => {
                let pij = le_add_succ lo i2;
                let p2 = le_trans (S (add lo (S i2))) (add lo (S (S (add i2 g)))) (len *v)
                           (le_rw_l (add lo (S (S (add i2 g)))) (add lo (S (S i2))) (S (add lo (S i2)))
                             (add_succ lo (S i2))
                             (le_add_mono_l lo (S (S i2)) (S (S (add i2 g))) (le_add i2 g)))
                           hle;
                swapS(v, lo, add lo (S(i2)), pij, p2);
                ()
              }
            },
            -- STEP (k = S k2): the scan at position lo + 1 + i + g.
            S(k2) => {
              let c = leb (nth (add lo (S (add i g))) (*v)) pivot;
              match c {
                True => match g {
                  -- True, g = Z: advance boundary, no swap.
                  Z => {
                    let hlZ = le_rw_l (len *v)
                                (add lo (S (add (S k2) (add i Z))))
                                (add lo (S (add k2 (add (S i) Z))))
                                (id_congr Nat Nat (λ (a : Nat). add lo (S a))
                                  (add (S k2) (add i Z))
                                  (add k2 (add (S i) Z))
                                  (hshift_true k2 i Z))
                                hle;
                    partScanRange(v, lo, k2, S(i), Z, pivot, hlZ)
                  },
                  -- True, g = S g2: swap boundary↔scan, then advance.
                  S(g2) => {
                    let pij = le_rw_l (add lo (S (add i (S g2))))
                                (add lo (S (S i)))
                                (S (add lo (S i)))
                                (add_succ lo (S i))
                                (le_add_mono_l lo (S (S i)) (S (add i (S g2))) (le_add_succ i g2));
                    let p2 = le_trans (S (add lo (S (add i (S g2)))))
                               (add lo (S (S (add k2 (add i (S g2))))))
                               (len *v)
                               (le_rw_l (add lo (S (S (add k2 (add i (S g2))))))
                                 (add lo (S (S (add i (S g2)))))
                                 (S (add lo (S (add i (S g2)))))
                                 (add_succ lo (S (add i (S g2))))
                                 (le_add_mono_l lo (S (S (add i (S g2)))) (S (S (add k2 (add i (S g2)))))
                                   (le_add_l (add i (S g2)) k2)))
                               hle;
                    let hlS = le_rw_r (add lo (S (add k2 (add (S i) (S g2)))))
                                (len *v)
                                (len (swapL (add lo (S i)) (add lo (S (add i (S g2)))) (*v)))
                                (id_sym Nat (len (swapL (add lo (S i)) (add lo (S (add i (S g2)))) (*v))) (len *v)
                                  (len_swapL (add lo (S i)) (add lo (S (add i (S g2)))) (*v)))
                                (le_rw_l (len *v)
                                  (add lo (S (add (S k2) (add i (S g2)))))
                                  (add lo (S (add k2 (add (S i) (S g2)))))
                                  (id_congr Nat Nat (λ (a : Nat). add lo (S a))
                                    (add (S k2) (add i (S g2)))
                                    (add k2 (add (S i) (S g2)))
                                    (hshift_true k2 i (S g2)))
                                  hle);
                    swapS(&mut *v, add lo (S(i)), add lo (S(add i (S(g2)))), pij, p2);
                    partScanRange(v, lo, k2, S(i), S(g2), pivot, hlS)
                  }
                },
                -- False: grow gap, no swap.
                False => {
                  let hlF = le_rw_l (len *v)
                              (add lo (S (add (S k2) (add i g))))
                              (add lo (S (add k2 (add i (S g)))))
                              (id_congr Nat Nat (λ (a : Nat). add lo (S a))
                                (add (S k2) (add i g))
                                (add k2 (add i (S g)))
                                (hshift_false k2 i g))
                              hle;
                  partScanRange(v, lo, k2, i, S(g), pivot, hlF)
                }
              }
            }
        } } }
def scanRangeTable : List Decl := [nthS, nth2S, swapSN, partScanRange]
example : checkFnOk partScanRange scanRangeTable = true := by native_decide

/-! ## M21-1 — the partition wrapper (back = partitionL, the partScanL composition)

    partition fixes the public interface: pivot placement + the scan, over a
    segment of length `n` (`hlenW : len *v = n`). Declared `back = partitionL n
    (*v)` — authored (in StdLemmas) as exactly `n = Z ⇒ *v`, `n = S n' ⇒ partScanL
    (nth 0 *v) n' 0 0 *v`, the raw composition of partScan's declared back. The
    scan call's hlen is hlenW transported by add_zero (the wrapper's `i = g = 0`,
    so partScan's `S (add n' (add 0 0))` is `S (add n' Z)`, bridged to `S n'`). -/

-- v=0, n=1, hlenW=2; body binders n'=3, pivot=4, hlen=5.
def partition : Decl :=
  decl{ fn partition (v : &mut List Nat, n : Nat, hlenW : Id Nat (len *v) n) -> Unit
        back = partitionL n (*v)
        { match n {
            Z => (),
            S(n2) => {
              let pivot = nth Z (*v);
              -- hlen : Id (len *v) (S (add n' Z)), from hlenW : Id (len *v) (S n') via add_zero.
              let hlen = id_trans Nat (len *v) (S n2) (S (add n2 Z))
                           hlenW
                           (id_sym Nat (S (add n2 Z)) (S n2)
                             (id_congr Nat Nat (λ (a : Nat). S a) (add n2 Z) n2 (add_zero n2)));
              partScan(v, n2, Z, Z, pivot, hlen)
            }
        } } }
def partTable2 : List Decl := [nthS, nth2S, swapSN, partScan, partition]
example : checkFnOk partition partTable2 = true := by native_decide

-- Not vacuous: a back that swaps unconditionally (≠ identity at n = Z) is rejected
-- on the untouched-borrow n = Z path, where `partitionL Z *v = *v`.
def partitionLie : Decl :=
  decl{ fn partitionLie (v : &mut List Nat, n : Nat, hlenW : Id Nat (len *v) n) -> Unit
        back = swapL Z (S Z) (*v)
        = %partition.body }
example : checkFnErr partitionLie "does not match" [nthS, nth2S, swapSN, partScan, partitionLie] = true := by native_decide


-- Not vacuous: a lying spec (i and g swapped in the declared back) is rejected —
-- the body's composed backward tree does not converge with the wrong partScanL.
def partScanLie : Decl :=
  decl{ fn partScanLie (v : &mut List Nat, k : Nat, i : Nat, g : Nat, pivot : Nat,
        hlen : Id Nat (len *v) (S (add k (add i g)))) -> Unit
        back = partScanL pivot k g i (*v)
        = %partScan.body }
example : checkFnErr partScanLie "does not match" [nthS, nth2S, swapSN, partScan, partScanLie] = true := by native_decide

/-! ## The lying-back sweep — one lie per CALLEE-CHECKED declared-spec branch

    A negative test per rule branch, not per feature (the M20 lesson). The §6.2
    callee convert-check catches a lie only where the declared back is authored as
    the raw suspension TREE (so tree ≡ back definitionally). Two such branches
    beyond the ones already covered:
    - borrow-returning multi-issued  → nth2Lie   (below)
    - borrow-returning single-issued → throughLie (S17Spec — the M8 arc)
    - Unit-returning recursive        → partScanLie (above; caught where an
      untouched argument-borrow path exposes the swapped spec)

    NOT callee-checked, by design: a back that is a higher-level REFORMULATION of
    the raw tree — swapS's `swapL i j *v` vs its set-based nth2 composition, and
    pivotPlace's swapL-based `baseBack` — never converts and is validated by the
    DIFFERENTIAL (executing recovery = checking recovery), as M17 established. The
    M20 auditAction extension checks in-place backs authored AS the tree (partScan);
    reformulated backs remain the differential's job. -/

-- Borrow-returning multi-issued: nth2 with i and j swapped in the two sets.
def nth2Lie : Decl :=
  decl{ fn nth2Lie (v : &mut List Nat, i : Nat, j : Nat,
        pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Σ (x : &mut Nat) → &mut Nat
        back = λ (a : Nat). λ (b : Nat). set j a (set i b (*v))
        = %Dllbc.Tests.S17Spec.nth2S.body }
example : checkFnErr nth2Lie "does not match" [nthS, nth2Lie] = true := by native_decide

/-! ## M19-B (the gate) — splitting the driver on a STUCK Bool spine

    The imperative partition branches on `if leb x pivot` with `x` symbolic; the
    scrutinee reduces to a stuck spine `leb σ σp`, NOT a bare σ, and the ⇜ split
    (M3) needs a substitutable variable. The machine now GENERALIZES: on an owned
    stuck spine, `generalizeStuck` NF's it and `abstractInto`s it to a fresh
    `σb : Bool` across all σ-bearing state (the M10 invariant's targets), then the
    ordinary owned-sym split refines σb → True/False per branch.

    The probe: a fn whose RETURN TYPE mentions the same `leb n 2` spine, with two
    `boolRec` sides that converge ONLY per branch (`add Z x ≡ x`). Without the
    split the two stuck `boolRec`s differ and neither `Refl` checks; with it, both
    paths reduce and check. Both the spine-in-the-value (the scrutinee) and the
    spine-in-the-type (the pinned return) must refine together — which is exactly
    what generalizing across ALL σ-bearing state delivers. -/

-- SUBJECT machinery: `tS`/`zt` build Nat terms for the pure-eval and executing
-- test subjects below (tnat/tlist/partLT/runScan…); no converted Decl uses them.
def tS (t : Term) : Term := .ctorApp "S" [t]   -- SUBJECT
def zt : Term := .ctorApp "Z" []               -- SUBJECT
def tnat : Nat → Term | 0 => zt | k + 1 => tS (tnat k)
-- n = 0; the `if` binds a fresh scrutinee (id 1).
def stuckProbe : Decl :=
  decl{ fn stuckProbe (n : Nat) -> Id Nat
          (boolRec (λ (b : Bool). Nat) (S Z) Z (leb n 2))
          (boolRec (λ (b : Bool). Nat) (add Z (S Z)) (add Z Z) (leb n 2))
        { let c = leb n 2;
          match c { True => Refl, False => Refl } } }
example : checkFnOk stuckProbe = true := by native_decide

-- Not vacuous (a): the True side does NOT converge (`S Z` vs `S (S Z)`). The
-- generalized σb refines to True in that path and the `boolRec` reduces to two
-- distinct values, so `Refl` fails — proving the per-branch refinement is real.
def stuckProbeLie : Decl :=
  decl{ fn stuckProbeLie (n : Nat) -> Id Nat
          (boolRec (λ (b : Bool). Nat) (S Z) Z (leb n 2))
          (boolRec (λ (b : Bool). Nat) (S (S Z)) Z (leb n 2))
        = %stuckProbe.body }
example : checkFnErr stuckProbeLie "does not have return type" = true := by native_decide

-- Not vacuous (b): a one-armed match is rejected as non-exhaustive — the
-- generalized σb is genuinely Bool-typed, so exhaustiveness demands True AND False.
def stuckProbeNonExh : Decl :=
  decl{ fn stuckProbeNonExh (n : Nat) -> Id Nat
          (boolRec (λ (b : Bool). Nat) (S Z) Z (leb n 2))
          (boolRec (λ (b : Bool). Nat) (add Z (S Z)) (add Z Z) (leb n 2))
        { let c = leb n 2;
          match c { True => Refl } } }
example : checkFnErr stuckProbeNonExh "non-exhaustive" = true := by native_decide

/-! ## M19-C (model) — `partitionL` computes the Lomuto partition

    Concrete validation of the pure model before wiring the imperative body to it:
    first-element pivot, `≤`-elements moved before it, `>`-elements after, pivot
    landing at the boundary. Covers an already-partitioned input (pivot smallest,
    no swaps), a reverse-sorted input (all `≤`, boundary walks to the end), and a
    mixed input that exercises the `g = S g'` swap branch. -/

-- SUBJECT machinery: the Val/Term generators the pure-model native_decide tests
-- consume as expected values and inputs (they check the surface-authored StdLemmas
-- models directly, so they stay raw — not decl{} declarations).
def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)
def vnat : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnat k]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | x :: xs => .ctor "Cons" [vnat x, vlist xs]
def tlist : List Nat → Term | [] => .ctorApp "Nil" [] | x :: xs => .ctorApp "Cons" [tnat x, tlist xs]  -- SUBJECT
def partLT (n : Nat) (l : List Nat) : Term := .app (.app StdLemmas.partitionL (tnat n)) (tlist l)

example : (pv (partLT 3 [3,1,2]) == vlist [2,1,3]) = true := by native_decide
example : (pv (partLT 3 [1,2,3]) == vlist [1,2,3]) = true := by native_decide          -- already partitioned
example : (pv (partLT 3 [3,2,1]) == vlist [1,2,3]) = true := by native_decide          -- reverse sorted
example : (pv (partLT 5 [3,5,1,2,4]) == vlist [2,1,3,5,4]) = true := by native_decide   -- exercises the swap

/-! ## M21-2 — partIdxL (the boundary index) and sortL (the quicksort model) -/

def idxLT (n : Nat) (l : List Nat) : Term := .app (.app StdLemmas.partIdxL (tnat n)) (tlist l)
def sortLT (fuel n : Nat) (l : List Nat) : Term := .app (.app (.app StdLemmas.sortL (tnat fuel)) (tnat n)) (tlist l)

-- partIdxL = the pivot's final position (matches where the partition run lands it):
example : (pv (idxLT 3 [3,1,2]) == vnat 2) = true := by native_decide    -- pivot 3 → index 2
example : (pv (idxLT 3 [1,2,3]) == vnat 0) = true := by native_decide     -- pivot 1 stays at 0
example : (pv (idxLT 3 [3,2,1]) == vnat 2) = true := by native_decide
example : (pv (idxLT 5 [3,5,1,2,4]) == vnat 2) = true := by native_decide -- [2,1,3,5,4], pivot at 2

-- sortL sorts (fuel = length). Small cases only — sortL's toValPure inlines the
-- whole partition/scan stack, so pv/nfV on it is heavy; the executing quicksort
-- (M21-3) validates it on the larger input classes far more cheaply.
example : (pv (sortLT 2 2 [2,1]) == vlist [1,2]) = true := by native_decide          -- the smallest sort
example : (pv (sortLT 1 1 [7]) == vlist [7]) = true := by native_decide              -- singleton
example : (pv (sortLT 0 0 []) == vlist []) = true := by native_decide                -- empty

/-! ## M21-3 — sortRangeL (the index-bounded quicksort spec, plan of record) -/

def sortRangeLT (fuel lo cnt : Nat) (l : List Nat) : Term :=
  .app (.app (.app (.app StdLemmas.sortRangeL (tnat fuel)) (tnat lo)) (tnat cnt)) (tlist l)

-- Full-range (lo=0, cnt=len): sortRangeL 0 (len l) l is a full sort — the top-
-- level shape the imperative quicksort's back carries.
example : (pv (sortRangeLT 2 0 2 [2,1]) == vlist [1,2]) = true := by native_decide
example : (pv (sortRangeLT 1 0 1 [7]) == vlist [7]) = true := by native_decide
example : (pv (sortRangeLT 0 0 0 []) == vlist []) = true := by native_decide
example : (pv (sortRangeLT 3 0 3 [3,2,1]) == vlist [1,2,3]) = true := by native_decide   -- recursion fires
-- Sub-range (lo>0): sort only [lo, lo+cnt), leaving the rest untouched — the new
-- capability the recursion rides. [5,3,2,9] sorting [3,2] at offset 1 → [5,2,3,9].
example : (pv (sortRangeLT 2 1 2 [5,3,2,9]) == vlist [5,2,3,9]) = true := by native_decide
example : (pv (sortRangeLT 3 1 3 [9,3,1,2,7]) == vlist [9,1,2,3,7]) = true := by native_decide

/-! ## M19-C (imperative, executing mode) — the body computes `partitionL`

    The in-place Lomuto partition through a mutable borrow, mirroring `partitionL`
    exactly. `partScanE` recurses on the scan counter `k`; each step reads the scan
    element with the PURE `nth` on `*v` (a comptime read, the `leb` condition), and
    branches: the `g = S g'` case does an in-place `swapS` then recurses; the base
    places the pivot with a final `swapS` (guarded on `i = S i'` — swapS cannot
    self-swap). Run in executing mode (bounds proofs are placeholders `()`, which
    the run does not type-check) to confirm the imperative algorithm agrees with the
    pure model on concrete inputs — the conformance the checking mode will prove. -/

open Dllbc.Tests.S17Spec (nthS nth2S swapSN)

-- v=0, k=1, i=2, g=3, pivot=4; body binders k2=5, c/i2=6, g2=7.
def partScanE : Decl :=
  decl{ fn partScanE (v : &mut List Nat, k : Nat, i : Nat, g : Nat, pivot : Nat) -> Unit
        { match k {
            Z => match i {
              Z => (),
              S(i2) => { swapS(v, Z, S(i2), (), ()); () }
            },
            S(k2) => {
              let c = leb (nth (S (add i g)) (*v)) pivot;
              match c {
                True => match g {
                  Z => partScanE(v, k2, S(i), Z, pivot),
                  -- `i` and `g2` are read MULTIPLE times here (boundary + scan position
                  -- + the recursion), and §2.1 copy-on-read now makes that natural: an
                  -- `S(…)` ctor arg reads its var by copy (marker-free Nat), so the
                  -- indices are the plain `S i`, `S (add i (S g2))`, `S g2` — no
                  -- add-spine workaround, and these convert with the model's forms.
                  S(g2) => { swapS(&mut *v, S(i), S(add i (S(g2))), (), ());
                             partScanE(v, k2, S(i), S(g2), pivot) }
                },
                False => partScanE(v, k2, i, S(g), pivot)
              }
            }
        } } }

-- v=0, n=1; body binders n2=5, pivot=6.
def partitionE : Decl :=
  decl{ fn partitionE (v : &mut List Nat, n : Nat) -> Unit
        { match n {
            Z => (),
            S(n2) => {
              let pivot = nth Z (*v);
              partScanE(v, n2, Z, Z, pivot)
            }
        } } }

def partTable : List Decl := [nthS, nth2S, swapSN, partScanE, partitionE]

-- Executing-mode caller: create a concrete list, borrow, partition in place, recover.
def partCaller (lst : List Nat) (n : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlist lst)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.seq (.call "partitionE" [.var ⟨1, "b"⟩, tnat n])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "x"⟩) .unit)))

def runPart (lst : List Nat) (n : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec partTable (partCaller lst n) with
  | .ok env => env.lookup "y" == some (pv (partLT n lst))
  | .error _ => false

-- The executing-mode partition agrees with the pure model on every input class:
-- already-partitioned (no swaps), reverse-sorted (all ≤, boundary walks to the
-- end), and mixed inputs that exercise the interior `g = S g'` swap (the reborrow
-- `&mut *v` path). Getting here surfaced and fixed three machine gaps (see the M19
-- report): shiftVars now shifts runtime vars inside pure spines; readR's var-move
-- ends a suspended reborrow in a borrow's payload; and a reused comptime index is
-- authored as a pure `add` spine so readR delegates to (non-consuming) readC.
example : runPart [3,1,2] 3 = true := by native_decide
example : runPart [1,2,3] 3 = true := by native_decide          -- already partitioned (no swaps)
example : runPart [3,2,1] 3 = true := by native_decide          -- reverse sorted
example : runPart [3,5,1,2,4] 5 = true := by native_decide      -- interior g=S g' swap
example : runPart [5,3,8,1,9,2] 6 = true := by native_decide    -- mixed, multiple interior swaps
example : runPart [2,2,1,3,2] 5 = true := by native_decide      -- duplicates around the pivot

/-! ## M20-3 differential — the CHECKING partScan Decl, run EXECUTING, = partScanL

    The load-bearing conformance validator (the callee convert-check reaches the
    back only where it's authored as the tree; the swapS leaf's reformulated back
    is the differential's job). We run the SAME partScan Decl that checkFnOk
    accepts — bounds, hlen proofs and all — in EXECUTING mode on concrete lists,
    and confirm its recovered list equals `partScanL pivot k 0 0 l`. So the body's
    actual effect matches the declared back on every input class: since checkFnOk
    accepts `back = partScanL`, executing = partScanL = the recovered value. -/

-- SUBJECT: the executing-differential caller/harness (generator-style machinery,
-- run through runExec) — a raw Term program, not a decl{} declaration.
def partScanCaller (lst : List Nat) (k pivot : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlist lst)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.seq (.call "partScan" [.var ⟨1, "b"⟩, tnat k, tnat 0, tnat 0, tnat pivot, .ctorApp "Refl" []])  -- SUBJECT
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "x"⟩) .unit)))

def runScan (lst : List Nat) (k pivot : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [nthS, nth2S, swapSN, partScan] (partScanCaller lst k pivot) with
  | .ok env => env.lookup "y" == some (pv (partScanLT (tnat pivot) (tnat k) (.ctorApp "Z" []) (.ctorApp "Z" []) (tlist lst)))  -- SUBJECT
  | .error _ => false

example : runScan [3,1,2] 2 3 = true := by native_decide        -- [2,1,3]
example : runScan [1,2,3] 2 1 = true := by native_decide         -- already partitioned
example : runScan [3,2,1] 2 3 = true := by native_decide         -- reverse sorted → [1,2,3]
example : runScan [3,5,1,2,4] 4 3 = true := by native_decide     -- interior g=S g' swap
example : runScan [5,3,8,1,9,2] 5 5 = true := by native_decide   -- mixed, multiple swaps


def partitionQ : Decl :=
  decl{ fn partitionQ (v : &mut List Nat, n : Nat, hlenW : Id Nat (len *v) n)
        -> Σ (i : Nat) → Id Nat i (partIdxL n (*v))
        back = partitionL n (*v)
        { match n {
            Z => Pair(Z, Refl),
            S(n2) => {
              let i = partIdxL (S n2) (*v);
              let pivot = nth Z (*v);
              let hlen = id_trans Nat (len *v) (S n2) (S (add n2 Z))
                           hlenW
                           (id_sym Nat (S (add n2 Z)) (S n2)
                             (id_congr Nat Nat (λ (a : Nat). S a) (add n2 Z) n2 (add_zero n2)));
              partScan(v, n2, Z, Z, pivot, hlen);
              Pair(i, Refl)
            }
        } } }
#eval (match Dllbc.checkFn [nthS, nth2S, swapSN, partScan, partitionQ] partitionQ with | .ok _ => "OK" | .error e => "ERR: " ++ (e.take 200))

/-! ## M21-3 — partitionRange: the subrange partition wrapper (Σ-pinned relative index)

    partitions the range [lo, lo+cnt) in place and returns the pivot's RELATIVE
    offset `i` (absolute = add lo i), Σ-pinned to `partIdxRangeL lo cnt *v`. The
    precondition is the range-fits inequality `hbnd : Le (add lo cnt) (len *v)`;
    the partScanRange call's entry bound (i = g = 0) is hbnd bridged by add_zero
    (`add cnt2 Z = cnt2`), mirroring partition's (M21-1) hlenW-via-add_zero. -/

def partitionRange : Decl :=
  decl{ fn partitionRange (v : &mut List Nat, lo : Nat, cnt : Nat,
        hbnd : Le (add lo cnt) (len *v))
        -> Σ (i : Nat) → Id Nat i (partIdxRangeL lo cnt (*v))
        back = partitionRangeL lo cnt (*v)
        { match cnt {
            Z => Pair(Z, Refl),
            S(cnt2) => {
              let i = partIdxRangeL lo (S cnt2) (*v);
              let pivot = nth lo (*v);
              let hle = le_rw_l (len *v)
                          (add lo (S cnt2))
                          (add lo (S (add cnt2 Z)))
                          (id_congr Nat Nat (λ (a : Nat). add lo (S a)) cnt2 (add cnt2 Z)
                            (id_sym Nat (add cnt2 Z) cnt2 (add_zero cnt2)))
                          hbnd;
              partScanRange(v, lo, cnt2, Z, Z, pivot, hle);
              Pair(i, Refl)
            }
        } } }
#eval (match Dllbc.checkFn [nthS, nth2S, swapSN, partScanRange, partitionRange] partitionRange with | .ok _ => "partitionRange OK" | .error e => "ERR: " ++ (e.take 200))

/-! ## M21-3 — quicksort: the imperative in-place quicksort (back = sortRangeL)

    THE NORTH STAR. `quicksort(v, fuel, lo, cnt, hbnd)` sorts the `cnt` elements at
    offset `lo` in place. Fuel-structural (mirrors sortRangeL): out of fuel / cnt ≤
    1 is a no-op; otherwise pick the pivot, compute the pivot's relative index `i`
    and the right-count `g` from the ENTRY list (before mutating), scan-partition
    the range (partScanRange, whose back IS partitionRangeL lo cnt *v), then recurse
    on [lo, lo+i) and [lo+i+1, …) — sequential reborrows of the one `*v`. Because
    `i`/`g` are the pure `partIdxRangeL`/`partGapRangeL` of the entry list, the
    body's suspension tree (partScanRange's back, then the two quicksort backs
    composed) is DEFINITIONALLY sortRangeL's own unfold — conformance is conversion.

    The two range bounds come from partScanSizeL (i + g + 1 = cnt) and the three
    length-preservation lemmas (the partition and each recursive sort keep len *v,
    so the bounds, stated over the live *v, transport back to len entry = hbnd). -/

def quicksort : Decl :=
  decl{ fn quicksort (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat,
        hbnd : Le (add lo cnt) (len *v)) -> Unit
        back = sortRangeL fuel lo cnt (*v)
        { match fuel {
            Z => (),
            S(f2) => match cnt {
              Z => (),
              S(cnt2) => match cnt2 {
                Z => (),
                S(cnt3) => {
                  let pivot = nth lo (*v);
                  let i = partIdxRangeL lo (S (S cnt3)) (*v);
                  let g = partGapRangeL lo (S (S cnt3)) (*v);
                  let sizeE = partScanSizeL (nth lo (*v)) lo (S cnt3) Z Z (*v);
                  let sSize = id_congr Nat Nat (λ (a : Nat). S a) (add i g) (S cnt3)
                                (id_trans Nat (add i g) (S (add cnt3 Z)) (S cnt3)
                                  sizeE
                                  (id_congr Nat Nat (λ (a : Nat). S a) (add cnt3 Z) cnt3 (add_zero cnt3)));
                  let hle = le_rw_l (len *v)
                              (add lo (S (S cnt3)))
                              (add lo (S (S (add cnt3 Z))))
                              (id_congr Nat Nat (λ (a : Nat). add lo a) (S (S cnt3)) (S (S (add cnt3 Z)))
                                (id_congr Nat Nat (λ (a : Nat). S a) (S cnt3) (S (add cnt3 Z))
                                  (id_congr Nat Nat (λ (a : Nat). S a) cnt3 (add cnt3 Z)
                                    (id_sym Nat (add cnt3 Z) cnt3 (add_zero cnt3)))))
                              hbnd;
                  let bl = le_rw_r (add lo i) (len *v) (len (partitionRangeL lo (S (S cnt3)) (*v)))
                             (id_sym Nat (len (partitionRangeL lo (S (S cnt3)) (*v))) (len *v)
                               (len_partitionRangeL lo (S (S cnt3)) (*v)))
                             (le_trans (add lo i) (add lo (S (S cnt3))) (len *v)
                               (le_rw_r (add lo i) (add lo (S (add i g))) (add lo (S (S cnt3)))
                                 (id_congr Nat Nat (λ (a : Nat). add lo a) (S (add i g)) (S (S cnt3)) sSize)
                                 (le_add_mono_l lo i (S (add i g)) (le_up_r i (add i g) (le_add i g))))
                               hbnd);
                  let br = le_rw_r (add (S (add lo i)) g) (len *v)
                             (len (sortRangeL f2 lo i (partitionRangeL lo (S (S cnt3)) (*v))))
                             (id_sym Nat (len (sortRangeL f2 lo i (partitionRangeL lo (S (S cnt3)) (*v)))) (len *v)
                               (id_trans Nat (len (sortRangeL f2 lo i (partitionRangeL lo (S (S cnt3)) (*v))))
                                 (len (partitionRangeL lo (S (S cnt3)) (*v))) (len *v)
                                 (len_sortRangeL f2 lo i (partitionRangeL lo (S (S cnt3)) (*v)))
                                 (len_partitionRangeL lo (S (S cnt3)) (*v))))
                             (le_rw_l (len *v) (add lo (S (S cnt3))) (add (S (add lo i)) g)
                               (id_sym Nat (add (S (add lo i)) g) (add lo (S (S cnt3)))
                                 (id_trans Nat (add (S (add lo i)) g) (S (add lo (add i g))) (add lo (S (S cnt3)))
                                   (id_congr Nat Nat (λ (a : Nat). S a) (add (add lo i) g) (add lo (add i g))
                                     (add_assoc lo i g))
                                   (id_trans Nat (S (add lo (add i g))) (add lo (S (add i g))) (add lo (S (S cnt3)))
                                     (id_sym Nat (add lo (S (add i g))) (S (add lo (add i g))) (add_succ lo (add i g)))
                                     (id_congr Nat Nat (λ (a : Nat). add lo a) (S (add i g)) (S (S cnt3)) sSize))))
                               hbnd);
                  partScanRange(&mut *v, lo, S(cnt3), Z, Z, pivot, hle);
                  quicksort(&mut *v, f2, lo, i, bl);
                  quicksort(&mut *v, f2, S(add lo i), g, br)
                }
              }
            }
        } } }
-- THE NORTH STAR, GREEN: the imperative in-place quicksort type-checks as an
-- implementation of its pure model `sortRangeL` (conformance = conversion, §6.2).
-- Measured from-scratch elaboration: 38m49s wall / 2326s CPU (native_decide,
-- 2026-07-27) — the conformance conversion blows up in unfold depth because
-- normalisation has no term sharing; cached (replayed) thereafter until this
-- file changes. Kept enabled as the milestone result; the checker-perf
-- milestone (incremental convert + memoised whnf) is the standing fix.
example : checkFnOk quicksort [nthS, nth2S, swapSN, partScanRange, quicksort] = true := by native_decide

-- Sequential reborrow (the quicksort recursion shape): a self-recursive fn that
-- reborrows *v twice in sequence for two recursive calls. This only checks
-- because `&mut` on a place holding a parked `loanₘ` now DEMAND-ENDS the prior
-- call's loan group (releasing *v with its back applied) before reborrowing —
-- the concrete demand-driven ending (§6.1, dllbc-arrows.md:508) rather than the
-- atomic-at-audit over-approximation, which suspended *v for the whole body and
-- blocked the second reborrow. back = identity (the recursion mutates nothing).
def twoRec : Decl :=
  decl{ fn twoRec (v : &mut List Nat, f : Nat) -> Unit
        back = *v
        { match f {
            Z => (),
            S(f2) => { twoRec(&mut *v, f2); twoRec(&mut *v, f2); () }
        } } }
example : checkFnOk twoRec [twoRec] = true := by native_decide

end Dllbc.Tests.S19Partition

