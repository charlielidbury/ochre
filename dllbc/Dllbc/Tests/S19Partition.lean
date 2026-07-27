import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
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

namespace Dllbc.Tests.S19Partition

def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def listNatT : Term := .app (.const "List") (.const "Nat")
def natT : Term := .const "Nat"

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

def tS (t : Term) : Term := .ctorApp "S" [t]
def LeT (a b : Term) : Term := Std.LeT a b
def lenT (l : Term) : Term := Std.lenT l
def countT (m l : Term) : Term := .app (.app Std.countFnT m) l
def swapLT (i j l : Term) : Term := .app (.app (.app StdLemmas.swapL i) j) l
def cslP (m i j l pij p2 : Term) : Term :=
  .app (.app (.app (.app (.app (.app StdLemmas.count_swapL' m) i) j) l) pij) p2

-- The pivot-placement back-spec, CASED on i so the no-op path (i = Z) is literally
-- `*v` (not `swapL Z Z *v`, which is stuck on a symbolic list). Mirrors partScanL's
-- base. v=0, i=1. Used by the pivotPlace scaffolding fns' declared backs.
def baseBack : Term :=
  .app (.app (.app (.app (.const "natRec") (.lam natT listNatT)) (.deref (V 0 "v")))
    (.lam natT (.lam listNatT (swapLT (.ctorApp "Z" []) (tS (.pvar 1)) (.deref (V 0 "v")))))) (V 1 "i")

-- s=0, m=1, i=2, j=3, pij=4, p2=5; body binders cert=6, b=7.
def certSwapCount : Decl :=
  { name := "certSwapCount",
    retType := .idT natT (countT (V 1 "m") (swapLT (V 2 "i") (V 3 "j") (V 0 "s"))) (countT (V 1 "m") (V 0 "s")),
    telescope := [
      ("s", listNatT), ("m", natT), ("i", natT), ("j", natT),
      ("pij", LeT (tS (V 2 "i")) (V 3 "j")),
      ("p2", LeT (tS (V 3 "j")) (lenT (V 0 "s")))],
    body := .letIn ⟨6, "cert"⟩ (cslP (V 1 "m") (V 2 "i") (V 3 "j") (V 0 "s") (V 4 "pij") (V 5 "p2"))
      (.letIn ⟨7, "b"⟩ (.borrow (.var ⟨0, "s"⟩))
        (.seq (.call "swapS" [.var ⟨7, "b"⟩, V 2 "i", V 3 "j", V 4 "pij", V 5 "p2"])
          (.var ⟨6, "cert"⟩))) }

def openerTable : List Decl := [Dllbc.Tests.S17Spec.nthS, Dllbc.Tests.S17Spec.nth2S, Dllbc.Tests.S17Spec.swapSN, certSwapCount]
example : checkFnOk certSwapCount openerTable = true := by native_decide

-- Negative control: claim the count GREW by one across the swap. The certificate
-- proves equality, so the value-returning audit rejects the lying return type —
-- the opener's acceptance is a real check of a real certificate.
def certSwapCountLieRet : Term := .idT natT (countT (V 1 "m") (swapLT (V 2 "i") (V 3 "j") (V 0 "s"))) (tS (countT (V 1 "m") (V 0 "s")))
def certSwapCountLie : Decl := { certSwapCount with name := "certSwapCountLie", retType := certSwapCountLieRet }
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

-- v=0, i=1, pib=2; body binder i2=3.
def pivotPlace : Decl :=
  { name := "pivotPlace", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT),
      ("pib", LeT (tS (V 1 "i")) (lenT (.deref (V 0 "v"))))],
    body := .matchE ⟨1, "i"⟩ [
      .mk "Z" [] .unit,
      .mk "S" [⟨3, "i2"⟩] (.seq (.call "swapS" [.var ⟨0, "v"⟩, .ctorApp "Z" [], tS (V 3 "i2"), .unit, V 2 "pib"]) .unit) ],
    back := some baseBack }
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

def addTmH (a b : Term) : Term := .app (.app Std.addFnT a) b

-- v=0, i=1, g=2, hlen=3; body binder i2=4.
def pivotPlaceH : Decl :=
  { name := "pivotPlaceH", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("g", natT),
      ("hlen", .idT natT (lenT (.deref (V 0 "v"))) (tS (addTmH (V 1 "i") (V 2 "g"))))],
    body := .matchE ⟨1, "i"⟩ [
      .mk "Z" [] .unit,
      -- Derive the bound in a `let` FIRST, while `v` is still live (the `len *v`
      -- read is comptime/non-consuming); THEN call swapS (which consumes `v`).
      .mk "S" [⟨4, "i2"⟩] (.letIn ⟨5, "p2"⟩
        -- p2 = le_rw_r (S(S i')) (S(S(add i' g))) (len *v) (id_sym hlen) (le_add i' g)
        (.app (.app (.app (.app (.app StdLemmas.le_rw_r
          (tS (tS (V 4 "i2"))))
          (tS (tS (addTmH (V 4 "i2") (V 2 "g")))))
          (lenT (.deref (V 0 "v"))))
          (.app (.app (.app (.app StdLemmas.id_sym natT) (lenT (.deref (V 0 "v"))))
            (tS (tS (addTmH (V 4 "i2") (V 2 "g"))))) (V 3 "hlen")))
          (.app (.app StdLemmas.le_add (V 4 "i2")) (V 2 "g")))
        (.seq (.call "swapS" [.var ⟨0, "v"⟩, .ctorApp "Z" [], tS (V 4 "i2"), .unit, V 5 "p2"]) .unit)) ],
    back := some baseBack }
example : checkFnOk pivotPlaceH confTable = true := by native_decide

/-! ## M20-2 (the recursive partScan) — partition's scan loop, checked against partScanL

    The full recursive scan, declared `back = partScanL pivot k i g (*v)`. Telescope
    carries the length equation `hlen : len *v = S (add k (add i g))` (k-first, so the
    step reduces definitionally). Body mirrors the M19 executing partition; the three
    step cases each derive their swapS bound (let-FIRST, per the §5.3 finding) and
    recurse with an UPDATED hlen (an hshift arithmetic transport — definitional total,
    plus a len_swapL bridge in the swap case). resolveTree composes the recursive
    call's back-spec with swapS's, exactly as pivotPlace proved for one swap. -/

def partScanLT (pivot k i g l : Term) : Term := .app (.app (.app (.app (.app StdLemmas.partScanL pivot) k) i) g) l
def nthP (k l : Term) : Term := .app (.app StdLemmas.nth k) l
def lebP (a b : Term) : Term := .app (.app Std.lebFnT a) b
def dv : Term := .deref (V 0 "v")
def sLam : Term := .lam natT (tS (.pvar 0))
def idTr (x y z p q : Term) : Term := .app (.app (.app (.app (.app (.app StdLemmas.id_trans natT) x) y) z) p) q
def idCgS (x y p : Term) : Term := .app (.app (.app (.app (.app (.app StdLemmas.id_congr natT) natT) sLam) x) y) p
def idSy (x y p : Term) : Term := .app (.app (.app (.app StdLemmas.id_sym natT) x) y) p
def hsF (k i g : Term) : Term := .app (.app (.app StdLemmas.hshift_false k) i) g
def hsT (k i g : Term) : Term := .app (.app (.app StdLemmas.hshift_true k) i) g
def leAdd (i g : Term) : Term := .app (.app StdLemmas.le_add i) g
def leAddL (b a : Term) : Term := .app (.app StdLemmas.le_add_l b) a
def leAddS (i g : Term) : Term := .app (.app StdLemmas.le_add_succ i) g
def leRwR (a x y h p : Term) : Term := .app (.app (.app (.app (.app StdLemmas.le_rw_r a) x) y) h) p
def lenSwapL (i j l : Term) : Term := .app (.app (.app StdLemmas.len_swapL i) j) l

-- Le-toolkit for the range partition (§21): the left-transport, left-add
-- monotonicity, add_succ bridge, le_trans, and id_congr through `λx. add lo (S x)`.
def leRwL (b x y h p : Term) : Term := .app (.app (.app (.app (.app StdLemmas.le_rw_l b) x) y) h) p
def leAddMonoL (lo a b h : Term) : Term := .app (.app (.app (.app StdLemmas.le_add_mono_l lo) a) b) h
def addSuccT (a b : Term) : Term := .app (.app StdLemmas.add_succ a) b
def leTrans (a b c hab hbc : Term) : Term := .app (.app (.app (.app (.app StdLemmas.le_trans a) b) c) hab) hbc
def loSLam (lo : Term) : Term := .lam natT (addTmH lo (tS (.pvar 0)))
def idCgLoS (lo x y p : Term) : Term := .app (.app (.app (.app (.app (.app StdLemmas.id_congr natT) natT) (loSLam lo)) x) y) p

-- Quicksort-Decl toolkit (§21): the gap wrapper, the size/length lemmas, the
-- successor-monotone Le, associativity, and id_congr through `λx. add lo x`.
def partGapRangeLT (lo cnt l : Term) : Term := .app (.app (.app StdLemmas.partGapRangeL lo) cnt) l
def partScanSizeLT (pivot lo k i g l : Term) : Term := .app (.app (.app (.app (.app (.app StdLemmas.partScanSizeL pivot) lo) k) i) g) l
def lenPartRangeLT (lo cnt l : Term) : Term := .app (.app (.app StdLemmas.len_partitionRangeL lo) cnt) l
def lenSortRangeLT (fuel lo cnt l : Term) : Term := .app (.app (.app (.app StdLemmas.len_sortRangeL fuel) lo) cnt) l
def sortRangeLT2 (fuel lo cnt l : Term) : Term := .app (.app (.app (.app StdLemmas.sortRangeL fuel) lo) cnt) l
def leUpR (a b h : Term) : Term := .app (.app (.app StdLemmas.le_up_r a) b) h
def addAssocT (a b c : Term) : Term := .app (.app (.app StdLemmas.add_assoc a) b) c
def loLam (lo : Term) : Term := .lam natT (addTmH lo (.pvar 0))
def idCgAddLo (lo x y p : Term) : Term := .app (.app (.app (.app (.app (.app StdLemmas.id_congr natT) natT) (loLam lo)) x) y) p

-- Abbreviations for the current-branch index expressions (i2/g2 are the peeled
-- successors; kk is k'). Built with addTmH (defined above).
-- v=0, k=1, i=2, g=3, pivot=4, hlen=5; binders k'=6, c/i'=7, g'/hlenX=8, pij=9, p2=10, hlenTSg=11.
def partScan : Decl :=
  { name := "partScan", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("k", natT), ("i", natT), ("g", natT), ("pivot", natT),
      ("hlen", .idT natT (lenT dv) (tS (addTmH (V 1 "k") (addTmH (V 2 "i") (V 3 "g")))))],
    body := .matchE ⟨1, "k"⟩ [
      -- BASE (k = Z): place the pivot (pivotPlaceH's validated body; hlen reduces to k=Z form).
      .mk "Z" [] (.matchE ⟨2, "i"⟩ [
        .mk "Z" [] .unit,
        .mk "S" [⟨7, "i2"⟩] (.letIn ⟨8, "p2b"⟩
          (leRwR (tS (tS (V 7 "i2"))) (tS (tS (addTmH (V 7 "i2") (V 3 "g")))) (lenT dv)
            (idSy (lenT dv) (tS (tS (addTmH (V 7 "i2") (V 3 "g")))) (V 5 "hlen"))
            (leAdd (V 7 "i2") (V 3 "g")))
          (.seq (.call "swapS" [.var ⟨0, "v"⟩, .ctorApp "Z" [], tS (V 7 "i2"), .unit, V 8 "p2b"]) .unit)) ]),
      -- STEP (k = S k'): the scan.
      .mk "S" [⟨6, "k2"⟩] (.letIn ⟨7, "c"⟩ (lebP (nthP (tS (addTmH (V 2 "i") (V 3 "g"))) dv) (V 4 "pivot"))
        (.matchE ⟨7, "c"⟩ [
          .mk "True" [] (.matchE ⟨3, "g"⟩ [
            -- True, g = Z: advance boundary, no swap.
            .mk "Z" [] (.letIn ⟨8, "hlZ"⟩
              (idTr (lenT dv) (tS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (.ctorApp "Z" []))))
                (tS (addTmH (V 6 "k2") (addTmH (tS (V 2 "i")) (.ctorApp "Z" []))))
                (V 5 "hlen")
                (idCgS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (.ctorApp "Z" [])))
                  (addTmH (V 6 "k2") (addTmH (tS (V 2 "i")) (.ctorApp "Z" [])))
                  (hsT (V 6 "k2") (V 2 "i") (.ctorApp "Z" []))))
              (.call "partScan" [.var ⟨0, "v"⟩, V 6 "k2", tS (V 2 "i"), .ctorApp "Z" [], V 4 "pivot", V 8 "hlZ"])),
            -- True, g = S g': swap boundary↔scan, then advance.
            .mk "S" [⟨8, "g2"⟩] (.letIn ⟨9, "pij"⟩ (leAddS (V 2 "i") (V 8 "g2"))
              (.letIn ⟨10, "p2"⟩
                (leRwR (tS (tS (addTmH (V 2 "i") (tS (V 8 "g2")))))
                  (tS (tS (addTmH (V 6 "k2") (addTmH (V 2 "i") (tS (V 8 "g2"))))))
                  (lenT dv)
                  (idSy (lenT dv) (tS (tS (addTmH (V 6 "k2") (addTmH (V 2 "i") (tS (V 8 "g2")))))) (V 5 "hlen"))
                  (leAddL (addTmH (V 2 "i") (tS (V 8 "g2"))) (V 6 "k2")))
                (.letIn ⟨11, "hlS"⟩
                  (idTr (lenT (swapLT (tS (V 2 "i")) (tS (addTmH (V 2 "i") (tS (V 8 "g2")))) dv)) (lenT dv)
                    (tS (addTmH (V 6 "k2") (addTmH (tS (V 2 "i")) (tS (V 8 "g2")))))
                    (lenSwapL (tS (V 2 "i")) (tS (addTmH (V 2 "i") (tS (V 8 "g2")))) dv)
                    (idTr (lenT dv) (tS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (tS (V 8 "g2")))))
                      (tS (addTmH (V 6 "k2") (addTmH (tS (V 2 "i")) (tS (V 8 "g2")))))
                      (V 5 "hlen")
                      (idCgS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (tS (V 8 "g2"))))
                        (addTmH (V 6 "k2") (addTmH (tS (V 2 "i")) (tS (V 8 "g2"))))
                        (hsT (V 6 "k2") (V 2 "i") (tS (V 8 "g2"))))))
                  (.seq (.call "swapS" [.borrow dv, tS (V 2 "i"), tS (addTmH (V 2 "i") (tS (V 8 "g2"))), V 9 "pij", V 10 "p2"])
                    (.call "partScan" [.var ⟨0, "v"⟩, V 6 "k2", tS (V 2 "i"), tS (V 8 "g2"), V 4 "pivot", V 11 "hlS"]))))) ]),
          -- False: grow gap, no swap.
          .mk "False" [] (.letIn ⟨8, "hlF"⟩
            (idTr (lenT dv) (tS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (V 3 "g"))))
              (tS (addTmH (V 6 "k2") (addTmH (V 2 "i") (tS (V 3 "g")))))
              (V 5 "hlen")
              (idCgS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (V 3 "g")))
                (addTmH (V 6 "k2") (addTmH (V 2 "i") (tS (V 3 "g"))))
                (hsF (V 6 "k2") (V 2 "i") (V 3 "g"))))
            (.call "partScan" [.var ⟨0, "v"⟩, V 6 "k2", V 2 "i", tS (V 3 "g"), V 4 "pivot", V 8 "hlF"])) ])) ],
    back := some (partScanLT (V 4 "pivot") (V 1 "k") (V 2 "i") (V 3 "g") dv) }
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

def partScanRangeLT (pivot lo k i g l : Term) : Term :=
  .app (.app (.app (.app (.app (.app StdLemmas.partScanRangeL pivot) lo) k) i) g) l

def partScanRange : Decl :=
  { name := "partScanRange", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("lo", natT), ("k", natT), ("i", natT), ("g", natT), ("pivot", natT),
      ("hle", LeT (addTmH (V 1 "lo") (tS (addTmH (V 2 "k") (addTmH (V 3 "i") (V 4 "g"))))) (lenT dv))],
    body := .matchE ⟨2, "k"⟩ [
      -- BASE (k = Z): place the pivot at lo → lo+i (no-op when relative i = 0).
      .mk "Z" [] (.matchE ⟨3, "i"⟩ [
        .mk "Z" [] .unit,
        .mk "S" [⟨7, "i2"⟩] (.letIn ⟨8, "pij"⟩ (leAddS (V 1 "lo") (V 7 "i2"))
          (.letIn ⟨9, "p2"⟩
            (leTrans (tS (addTmH (V 1 "lo") (tS (V 7 "i2"))))
              (addTmH (V 1 "lo") (tS (tS (addTmH (V 7 "i2") (V 4 "g")))))
              (lenT dv)
              (leRwL (addTmH (V 1 "lo") (tS (tS (addTmH (V 7 "i2") (V 4 "g")))))
                (addTmH (V 1 "lo") (tS (tS (V 7 "i2"))))
                (tS (addTmH (V 1 "lo") (tS (V 7 "i2"))))
                (addSuccT (V 1 "lo") (tS (V 7 "i2")))
                (leAddMonoL (V 1 "lo") (tS (tS (V 7 "i2"))) (tS (tS (addTmH (V 7 "i2") (V 4 "g")))) (leAdd (V 7 "i2") (V 4 "g"))))
              (V 6 "hle"))
            (.seq (.call "swapS" [.var ⟨0, "v"⟩, V 1 "lo", addTmH (V 1 "lo") (tS (V 7 "i2")), V 8 "pij", V 9 "p2"]) .unit))) ]),
      -- STEP (k = S k2): the scan at position lo + 1 + i + g.
      .mk "S" [⟨7, "k2"⟩] (.letIn ⟨8, "c"⟩ (lebP (nthP (addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (V 4 "g")))) dv) (V 5 "pivot"))
        (.matchE ⟨8, "c"⟩ [
          .mk "True" [] (.matchE ⟨4, "g"⟩ [
            -- True, g = Z: advance boundary, no swap.
            .mk "Z" [] (.letIn ⟨9, "hlZ"⟩
              (leRwL (lenT dv)
                (addTmH (V 1 "lo") (tS (addTmH (tS (V 7 "k2")) (addTmH (V 3 "i") (.ctorApp "Z" [])))))
                (addTmH (V 1 "lo") (tS (addTmH (V 7 "k2") (addTmH (tS (V 3 "i")) (.ctorApp "Z" [])))))
                (idCgLoS (V 1 "lo")
                  (addTmH (tS (V 7 "k2")) (addTmH (V 3 "i") (.ctorApp "Z" [])))
                  (addTmH (V 7 "k2") (addTmH (tS (V 3 "i")) (.ctorApp "Z" [])))
                  (hsT (V 7 "k2") (V 3 "i") (.ctorApp "Z" [])))
                (V 6 "hle"))
              (.call "partScanRange" [.var ⟨0, "v"⟩, V 1 "lo", V 7 "k2", tS (V 3 "i"), .ctorApp "Z" [], V 5 "pivot", V 9 "hlZ"])),
            -- True, g = S g2: swap boundary↔scan, then advance.
            .mk "S" [⟨9, "g2"⟩] (.letIn ⟨10, "pij"⟩
              (leRwL (addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (tS (V 9 "g2")))))
                (addTmH (V 1 "lo") (tS (tS (V 3 "i"))))
                (tS (addTmH (V 1 "lo") (tS (V 3 "i"))))
                (addSuccT (V 1 "lo") (tS (V 3 "i")))
                (leAddMonoL (V 1 "lo") (tS (tS (V 3 "i"))) (tS (addTmH (V 3 "i") (tS (V 9 "g2")))) (leAddS (V 3 "i") (V 9 "g2"))))
              (.letIn ⟨11, "p2"⟩
                (leTrans (tS (addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (tS (V 9 "g2"))))))
                  (addTmH (V 1 "lo") (tS (tS (addTmH (V 7 "k2") (addTmH (V 3 "i") (tS (V 9 "g2")))))))
                  (lenT dv)
                  (leRwL (addTmH (V 1 "lo") (tS (tS (addTmH (V 7 "k2") (addTmH (V 3 "i") (tS (V 9 "g2")))))))
                    (addTmH (V 1 "lo") (tS (tS (addTmH (V 3 "i") (tS (V 9 "g2"))))))
                    (tS (addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (tS (V 9 "g2"))))))
                    (addSuccT (V 1 "lo") (tS (addTmH (V 3 "i") (tS (V 9 "g2")))))
                    (leAddMonoL (V 1 "lo") (tS (tS (addTmH (V 3 "i") (tS (V 9 "g2"))))) (tS (tS (addTmH (V 7 "k2") (addTmH (V 3 "i") (tS (V 9 "g2")))))) (leAddL (addTmH (V 3 "i") (tS (V 9 "g2"))) (V 7 "k2"))))
                  (V 6 "hle"))
                (.letIn ⟨12, "hlS"⟩
                  (leRwR (addTmH (V 1 "lo") (tS (addTmH (V 7 "k2") (addTmH (tS (V 3 "i")) (tS (V 9 "g2"))))))
                    (lenT dv)
                    (lenT (swapLT (addTmH (V 1 "lo") (tS (V 3 "i"))) (addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (tS (V 9 "g2"))))) dv))
                    (idSy (lenT (swapLT (addTmH (V 1 "lo") (tS (V 3 "i"))) (addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (tS (V 9 "g2"))))) dv)) (lenT dv)
                      (lenSwapL (addTmH (V 1 "lo") (tS (V 3 "i"))) (addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (tS (V 9 "g2"))))) dv))
                    (leRwL (lenT dv)
                      (addTmH (V 1 "lo") (tS (addTmH (tS (V 7 "k2")) (addTmH (V 3 "i") (tS (V 9 "g2"))))))
                      (addTmH (V 1 "lo") (tS (addTmH (V 7 "k2") (addTmH (tS (V 3 "i")) (tS (V 9 "g2"))))))
                      (idCgLoS (V 1 "lo")
                        (addTmH (tS (V 7 "k2")) (addTmH (V 3 "i") (tS (V 9 "g2"))))
                        (addTmH (V 7 "k2") (addTmH (tS (V 3 "i")) (tS (V 9 "g2"))))
                        (hsT (V 7 "k2") (V 3 "i") (tS (V 9 "g2"))))
                      (V 6 "hle")))
                  (.seq (.call "swapS" [.borrow dv, addTmH (V 1 "lo") (tS (V 3 "i")), addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (tS (V 9 "g2")))), V 10 "pij", V 11 "p2"])
                    (.call "partScanRange" [.var ⟨0, "v"⟩, V 1 "lo", V 7 "k2", tS (V 3 "i"), tS (V 9 "g2"), V 5 "pivot", V 12 "hlS"]))))) ]),
          -- False: grow gap, no swap.
          .mk "False" [] (.letIn ⟨9, "hlF"⟩
            (leRwL (lenT dv)
              (addTmH (V 1 "lo") (tS (addTmH (tS (V 7 "k2")) (addTmH (V 3 "i") (V 4 "g")))))
              (addTmH (V 1 "lo") (tS (addTmH (V 7 "k2") (addTmH (V 3 "i") (tS (V 4 "g"))))))
              (idCgLoS (V 1 "lo")
                (addTmH (tS (V 7 "k2")) (addTmH (V 3 "i") (V 4 "g")))
                (addTmH (V 7 "k2") (addTmH (V 3 "i") (tS (V 4 "g"))))
                (hsF (V 7 "k2") (V 3 "i") (V 4 "g")))
              (V 6 "hle"))
            (.call "partScanRange" [.var ⟨0, "v"⟩, V 1 "lo", V 7 "k2", V 3 "i", tS (V 4 "g"), V 5 "pivot", V 9 "hlF"])) ])) ],
    back := some (partScanRangeLT (V 5 "pivot") (V 1 "lo") (V 2 "k") (V 3 "i") (V 4 "g") dv) }
def scanRangeTable : List Decl := [nthS, nth2S, swapSN, partScanRange]
example : checkFnOk partScanRange scanRangeTable = true := by native_decide

/-! ## M21-1 — the partition wrapper (back = partitionL, the partScanL composition)

    partition fixes the public interface: pivot placement + the scan, over a
    segment of length `n` (`hlenW : len *v = n`). Declared `back = partitionL n
    (*v)` — authored (in StdLemmas) as exactly `n = Z ⇒ *v`, `n = S n' ⇒ partScanL
    (nth 0 *v) n' 0 0 *v`, the raw composition of partScan's declared back. The
    scan call's hlen is hlenW transported by add_zero (the wrapper's `i = g = 0`,
    so partScan's `S (add n' (add 0 0))` is `S (add n' Z)`, bridged to `S n'`). -/

def partitionLT2 (n l : Term) : Term := .app (.app StdLemmas.partitionL n) l
def addZeroT (n : Term) : Term := .app StdLemmas.add_zero n

-- v=0, n=1, hlenW=2; body binders n'=3, pivot=4, hlen=5.
def partition : Decl :=
  { name := "partition", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("n", natT),
      ("hlenW", .idT natT (lenT dv) (V 1 "n"))],
    body := .matchE ⟨1, "n"⟩ [
      .mk "Z" [] .unit,
      .mk "S" [⟨3, "n2"⟩] (.letIn ⟨4, "pivot"⟩ (nthP (.ctorApp "Z" []) dv)
        (.letIn ⟨5, "hlen"⟩
          -- hlen : Id (len *v) (S (add n' Z)), from hlenW : Id (len *v) (S n') via add_zero.
          (idTr (lenT dv) (tS (V 3 "n2")) (tS (addTmH (V 3 "n2") (.ctorApp "Z" [])))
            (V 2 "hlenW")
            (idSy (tS (addTmH (V 3 "n2") (.ctorApp "Z" []))) (tS (V 3 "n2"))
              (idCgS (addTmH (V 3 "n2") (.ctorApp "Z" [])) (V 3 "n2") (addZeroT (V 3 "n2")))))
          (.call "partScan" [.var ⟨0, "v"⟩, V 3 "n2", .ctorApp "Z" [], .ctorApp "Z" [], V 4 "pivot", V 5 "hlen"]))) ],
    back := some (partitionLT2 (V 1 "n") dv) }
def partTable2 : List Decl := [nthS, nth2S, swapSN, partScan, partition]
example : checkFnOk partition partTable2 = true := by native_decide

-- Not vacuous: a back that swaps unconditionally (≠ identity at n = Z) is rejected
-- on the untouched-borrow n = Z path, where `partitionL Z *v = *v`.
def partitionLieBack : Term := swapLT (.ctorApp "Z" []) (tS (.ctorApp "Z" [])) dv
def partitionLie : Decl := { partition with name := "partitionLie", back := some partitionLieBack }
example : checkFnErr partitionLie "does not match" [nthS, nth2S, swapSN, partScan, partitionLie] = true := by native_decide


-- Not vacuous: a lying spec (i and g swapped in the declared back) is rejected —
-- the body's composed backward tree does not converge with the wrong partScanL.
def partScanLieBack : Term := partScanLT (V 4 "pivot") (V 1 "k") (V 3 "g") (V 2 "i") dv
def partScanLie : Decl := { partScan with name := "partScanLie", back := some partScanLieBack }
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

def setL (k v l : Term) : Term := .app (.app (.app StdLemmas.set k) v) l

-- Borrow-returning multi-issued: nth2 with i and j swapped in the two sets.
def nth2LieBack : Term := .lam natT (.lam natT (setL (V 2 "j") (.pvar 1) (setL (V 1 "i") (.pvar 0) (.deref (V 0 "v")))))
def nth2Lie : Decl := { nth2S with name := "nth2Lie", back := some nth2LieBack }
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

def zt : Term := .ctorApp "Z" []
def tnat : Nat → Term | 0 => zt | k + 1 => tS (tnat k)
def lebSp (n : Term) : Term := .app (.app Std.lebFnT n) (tnat 2)
def addT (a b : Term) : Term := .app (.app Std.addFnT a) b
def boolRecNat (t f sp : Term) : Term :=
  .app (.app (.app (.app (.const "boolRec") (.lam (.const "Bool") natT)) t) f) sp
def Refl : Term := .ctorApp "Refl" []

-- n = 0; the `if` binds a fresh scrutinee (id 1).
def stuckProbe : Decl :=
  { name := "stuckProbe",
    retType := .idT natT
      (boolRecNat (tS zt) zt (lebSp (V 0 "n")))
      (boolRecNat (addT zt (tS zt)) (addT zt zt) (lebSp (V 0 "n"))),
    telescope := [("n", natT)],
    body := .letIn ⟨1, "c"⟩ (lebSp (V 0 "n"))
      (.matchE ⟨1, "c"⟩ [.mk "True" [] Refl, .mk "False" [] Refl]) }
example : checkFnOk stuckProbe = true := by native_decide

-- Not vacuous (a): the True side does NOT converge (`S Z` vs `S (S Z)`). The
-- generalized σb refines to True in that path and the `boolRec` reduces to two
-- distinct values, so `Refl` fails — proving the per-branch refinement is real.
def stuckProbeLieRet : Term := .idT natT
  (boolRecNat (tS zt) zt (lebSp (V 0 "n"))) (boolRecNat (tS (tS zt)) zt (lebSp (V 0 "n")))
def stuckProbeLie : Decl := { stuckProbe with name := "stuckProbeLie", retType := stuckProbeLieRet }
example : checkFnErr stuckProbeLie "does not have return type" = true := by native_decide

-- Not vacuous (b): a one-armed match is rejected as non-exhaustive — the
-- generalized σb is genuinely Bool-typed, so exhaustiveness demands True AND False.
def stuckProbeNonExhBody : Term := .letIn ⟨1, "c"⟩ (lebSp (V 0 "n")) (.matchE ⟨1, "c"⟩ [.mk "True" [] Refl])
def stuckProbeNonExh : Decl := { stuckProbe with name := "stuckProbeNonExh", body := stuckProbeNonExhBody }
example : checkFnErr stuckProbeNonExh "non-exhaustive" = true := by native_decide

/-! ## M19-C (model) — `partitionL` computes the Lomuto partition

    Concrete validation of the pure model before wiring the imperative body to it:
    first-element pivot, `≤`-elements moved before it, `>`-elements after, pivot
    landing at the boundary. Covers an already-partitioned input (pivot smallest,
    no swaps), a reverse-sorted input (all `≤`, boundary walks to the end), and a
    mixed input that exercises the `g = S g'` swap branch. -/

def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)
def vnat : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnat k]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | x :: xs => .ctor "Cons" [vnat x, vlist xs]
def tlist : List Nat → Term | [] => .ctorApp "Nil" [] | x :: xs => .ctorApp "Cons" [tnat x, tlist xs]
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

def nthPureT (k l : Term) : Term := .app (.app StdLemmas.nth k) l
def lebPureT (a b : Term) : Term := .app (.app Std.lebFnT a) b
def addTm (a b : Term) : Term := .app (.app Std.addFnT a) b
def dV (i : Nat) (n : String) : Term := .deref (.var ⟨i, n⟩)
def u : Term := .unit

-- v=0, k=1, i=2, g=3, pivot=4; body binders k2=5, c/i2=6, g2=7.
def partScanE : Decl :=
  { name := "partScanE", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("k", natT), ("i", natT), ("g", natT), ("pivot", natT)],
    body := .matchE ⟨1, "k"⟩ [
      .mk "Z" [] (.matchE ⟨2, "i"⟩ [
        .mk "Z" [] u,
        .mk "S" [⟨6, "i2"⟩] (.seq (.call "swapS" [.var ⟨0, "v"⟩, tnat 0, tS (V 6 "i2"), u, u]) u) ]),
      .mk "S" [⟨5, "k2"⟩]
        (.letIn ⟨6, "c"⟩ (lebPureT (nthPureT (tS (addTm (V 2 "i") (V 3 "g"))) (dV 0 "v")) (V 4 "pivot"))
          (.matchE ⟨6, "c"⟩ [
            .mk "True" [] (.matchE ⟨3, "g"⟩ [
              .mk "Z" [] (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", tS (V 2 "i"), tnat 0, V 4 "pivot"]),
              -- `i` and `g2` are read MULTIPLE times here (boundary + scan position
              -- + the recursion), and §2.1 copy-on-read now makes that natural: a
              -- `.ctorApp "S"` arg reads its var by copy (marker-free Nat), so the
              -- indices are the plain `S i`, `S (add i (S g2))`, `S g2` — no
              -- add-spine workaround, and these convert with the model's forms.
              .mk "S" [⟨7, "g2"⟩] (.seq (.call "swapS" [.borrow (dV 0 "v"), tS (V 2 "i"), tS (addTm (V 2 "i") (tS (V 7 "g2"))), u, u])
                (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", tS (V 2 "i"), tS (V 7 "g2"), V 4 "pivot"])) ]),
            .mk "False" [] (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", V 2 "i", tS (V 3 "g"), V 4 "pivot"]) ])) ] }

-- v=0, n=1; body binders n2=5, pivot=6.
def partitionE : Decl :=
  { name := "partitionE", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("n", natT)],
    body := .matchE ⟨1, "n"⟩ [
      .mk "Z" [] u,
      .mk "S" [⟨5, "n2"⟩] (.letIn ⟨6, "pivot"⟩ (nthPureT (tnat 0) (dV 0 "v"))
        (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "n2", tnat 0, tnat 0, V 6 "pivot"])) ] }

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

def partScanCaller (lst : List Nat) (k pivot : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlist lst)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.seq (.call "partScan" [.var ⟨1, "b"⟩, tnat k, tnat 0, tnat 0, tnat pivot, .ctorApp "Refl" []])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "x"⟩) .unit)))

def runScan (lst : List Nat) (k pivot : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [nthS, nth2S, swapSN, partScan] (partScanCaller lst k pivot) with
  | .ok env => env.lookup "y" == some (pv (partScanLT (tnat pivot) (tnat k) (.ctorApp "Z" []) (.ctorApp "Z" []) (tlist lst)))
  | .error _ => false

example : runScan [3,1,2] 2 3 = true := by native_decide        -- [2,1,3]
example : runScan [1,2,3] 2 1 = true := by native_decide         -- already partitioned
example : runScan [3,2,1] 2 3 = true := by native_decide         -- reverse sorted → [1,2,3]
example : runScan [3,5,1,2,4] 4 3 = true := by native_decide     -- interior g=S g' swap
example : runScan [5,3,8,1,9,2] 5 5 = true := by native_decide   -- mixed, multiple swaps


def partitionQ : Decl :=
  { name := "partitionQ",
    retType := .sigmaT natT (.idT natT (.pvar 0) (.app (.app StdLemmas.partIdxL (V 1 "n")) dv)),
    telescope := [("v", .borrowT listNatT listNatT), ("n", natT), ("hlenW", .idT natT (lenT dv) (V 1 "n"))],
    body := .matchE ⟨1, "n"⟩ [
      .mk "Z" [] (.ctorApp "Pair" [.ctorApp "Z" [], .ctorApp "Refl" []]),
      .mk "S" [⟨3, "n2"⟩] (.letIn ⟨4, "i"⟩ (.app (.app StdLemmas.partIdxL (.ctorApp "S" [V 3 "n2"])) dv)
        (.letIn ⟨5, "pivot"⟩ (nthP (.ctorApp "Z" []) dv)
          (.letIn ⟨6, "hlen"⟩
            (idTr (lenT dv) (tS (V 3 "n2")) (tS (addTmH (V 3 "n2") (.ctorApp "Z" [])))
              (V 2 "hlenW")
              (idSy (tS (addTmH (V 3 "n2") (.ctorApp "Z" []))) (tS (V 3 "n2"))
                (idCgS (addTmH (V 3 "n2") (.ctorApp "Z" [])) (V 3 "n2") (addZeroT (V 3 "n2")))))
            (.seq (.call "partScan" [.var ⟨0, "v"⟩, V 3 "n2", .ctorApp "Z" [], .ctorApp "Z" [], V 5 "pivot", V 6 "hlen"])
              (.ctorApp "Pair" [V 4 "i", .ctorApp "Refl" []]))))) ],
    back := some (partitionLT2 (V 1 "n") dv) }
#eval (match Dllbc.checkFn [nthS, nth2S, swapSN, partScan, partitionQ] partitionQ with | .ok _ => "OK" | .error e => "ERR: " ++ (e.take 200))

/-! ## M21-3 — partitionRange: the subrange partition wrapper (Σ-pinned relative index)

    partitions the range [lo, lo+cnt) in place and returns the pivot's RELATIVE
    offset `i` (absolute = add lo i), Σ-pinned to `partIdxRangeL lo cnt *v`. The
    precondition is the range-fits inequality `hbnd : Le (add lo cnt) (len *v)`;
    the partScanRange call's entry bound (i = g = 0) is hbnd bridged by add_zero
    (`add cnt2 Z = cnt2`), mirroring partition's (M21-1) hlenW-via-add_zero. -/

def partIdxRangeLT (lo cnt l : Term) : Term := .app (.app (.app StdLemmas.partIdxRangeL lo) cnt) l
def partitionRangeLT (lo cnt l : Term) : Term := .app (.app (.app StdLemmas.partitionRangeL lo) cnt) l

def partitionRange : Decl :=
  { name := "partitionRange",
    retType := .sigmaT natT (.idT natT (.pvar 0) (partIdxRangeLT (V 1 "lo") (V 2 "cnt") dv)),
    telescope := [("v", .borrowT listNatT listNatT), ("lo", natT), ("cnt", natT),
      ("hbnd", LeT (addTmH (V 1 "lo") (V 2 "cnt")) (lenT dv))],
    body := .matchE ⟨2, "cnt"⟩ [
      .mk "Z" [] (.ctorApp "Pair" [.ctorApp "Z" [], .ctorApp "Refl" []]),
      .mk "S" [⟨4, "cnt2"⟩] (.letIn ⟨5, "i"⟩ (partIdxRangeLT (V 1 "lo") (tS (V 4 "cnt2")) dv)
        (.letIn ⟨6, "pivot"⟩ (nthP (V 1 "lo") dv)
          (.letIn ⟨7, "hle"⟩
            (leRwL (lenT dv)
              (addTmH (V 1 "lo") (tS (V 4 "cnt2")))
              (addTmH (V 1 "lo") (tS (addTmH (V 4 "cnt2") (.ctorApp "Z" []))))
              (idCgLoS (V 1 "lo") (V 4 "cnt2") (addTmH (V 4 "cnt2") (.ctorApp "Z" []))
                (idSy (addTmH (V 4 "cnt2") (.ctorApp "Z" [])) (V 4 "cnt2") (addZeroT (V 4 "cnt2"))))
              (V 3 "hbnd"))
            (.seq (.call "partScanRange" [.var ⟨0, "v"⟩, V 1 "lo", V 4 "cnt2", .ctorApp "Z" [], .ctorApp "Z" [], V 6 "pivot", V 7 "hle"])
              (.ctorApp "Pair" [V 5 "i", .ctorApp "Refl" []]))))) ],
    back := some (partitionRangeLT (V 1 "lo") (V 2 "cnt") dv) }
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
  { name := "quicksort", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("fuel", natT), ("lo", natT), ("cnt", natT),
      ("hbnd", LeT (addTmH (V 2 "lo") (V 3 "cnt")) (lenT dv))],
    body := .matchE ⟨1, "fuel"⟩ [
      .mk "Z" [] .unit,
      .mk "S" [⟨5, "f2"⟩] (.matchE ⟨3, "cnt"⟩ [
        .mk "Z" [] .unit,
        .mk "S" [⟨6, "cnt2"⟩] (.matchE ⟨6, "cnt2"⟩ [
          .mk "Z" [] .unit,
          .mk "S" [⟨7, "cnt3"⟩]
            (.letIn ⟨8, "pivot"⟩ (nthP (V 2 "lo") dv)
            (.letIn ⟨9, "i"⟩ (partIdxRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv)
            (.letIn ⟨10, "g"⟩ (partGapRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv)
            (.letIn ⟨11, "sizeE"⟩ (partScanSizeLT (nthP (V 2 "lo") dv) (V 2 "lo") (tS (V 7 "cnt3")) (.ctorApp "Z" []) (.ctorApp "Z" []) dv)
            (.letIn ⟨12, "sSize"⟩
              (idCgS (addTmH (V 9 "i") (V 10 "g")) (tS (V 7 "cnt3"))
                (idTr (addTmH (V 9 "i") (V 10 "g")) (tS (addTmH (V 7 "cnt3") (.ctorApp "Z" []))) (tS (V 7 "cnt3"))
                  (V 11 "sizeE")
                  (idCgS (addTmH (V 7 "cnt3") (.ctorApp "Z" [])) (V 7 "cnt3") (addZeroT (V 7 "cnt3")))))
            (.letIn ⟨13, "hle"⟩
              (leRwL (lenT dv)
                (addTmH (V 2 "lo") (tS (tS (V 7 "cnt3"))))
                (addTmH (V 2 "lo") (tS (tS (addTmH (V 7 "cnt3") (.ctorApp "Z" [])))))
                (idCgAddLo (V 2 "lo") (tS (tS (V 7 "cnt3"))) (tS (tS (addTmH (V 7 "cnt3") (.ctorApp "Z" []))))
                  (idCgS (tS (V 7 "cnt3")) (tS (addTmH (V 7 "cnt3") (.ctorApp "Z" [])))
                    (idCgS (V 7 "cnt3") (addTmH (V 7 "cnt3") (.ctorApp "Z" [])) (idSy (addTmH (V 7 "cnt3") (.ctorApp "Z" [])) (V 7 "cnt3") (addZeroT (V 7 "cnt3"))))))
                (V 4 "hbnd"))
            (.letIn ⟨14, "bl"⟩
              (leRwR (addTmH (V 2 "lo") (V 9 "i")) (lenT dv) (lenT (partitionRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv))
                (idSy (lenT (partitionRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv)) (lenT dv) (lenPartRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv))
                (leTrans (addTmH (V 2 "lo") (V 9 "i")) (addTmH (V 2 "lo") (tS (tS (V 7 "cnt3")))) (lenT dv)
                  (leRwR (addTmH (V 2 "lo") (V 9 "i")) (addTmH (V 2 "lo") (tS (addTmH (V 9 "i") (V 10 "g")))) (addTmH (V 2 "lo") (tS (tS (V 7 "cnt3"))))
                    (idCgAddLo (V 2 "lo") (tS (addTmH (V 9 "i") (V 10 "g"))) (tS (tS (V 7 "cnt3"))) (V 12 "sSize"))
                    (leAddMonoL (V 2 "lo") (V 9 "i") (tS (addTmH (V 9 "i") (V 10 "g"))) (leUpR (V 9 "i") (addTmH (V 9 "i") (V 10 "g")) (leAdd (V 9 "i") (V 10 "g")))))
                  (V 4 "hbnd")))
            (.letIn ⟨15, "br"⟩
              (leRwR (addTmH (tS (addTmH (V 2 "lo") (V 9 "i"))) (V 10 "g")) (lenT dv)
                (lenT (sortRangeLT2 (V 5 "f2") (V 2 "lo") (V 9 "i") (partitionRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv)))
                (idSy (lenT (sortRangeLT2 (V 5 "f2") (V 2 "lo") (V 9 "i") (partitionRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv))) (lenT dv)
                  (idTr (lenT (sortRangeLT2 (V 5 "f2") (V 2 "lo") (V 9 "i") (partitionRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv)))
                    (lenT (partitionRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv)) (lenT dv)
                    (lenSortRangeLT (V 5 "f2") (V 2 "lo") (V 9 "i") (partitionRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv))
                    (lenPartRangeLT (V 2 "lo") (tS (tS (V 7 "cnt3"))) dv)))
                (leRwL (lenT dv) (addTmH (V 2 "lo") (tS (tS (V 7 "cnt3")))) (addTmH (tS (addTmH (V 2 "lo") (V 9 "i"))) (V 10 "g"))
                  (idSy (addTmH (tS (addTmH (V 2 "lo") (V 9 "i"))) (V 10 "g")) (addTmH (V 2 "lo") (tS (tS (V 7 "cnt3"))))
                    (idTr (addTmH (tS (addTmH (V 2 "lo") (V 9 "i"))) (V 10 "g")) (tS (addTmH (V 2 "lo") (addTmH (V 9 "i") (V 10 "g")))) (addTmH (V 2 "lo") (tS (tS (V 7 "cnt3"))))
                      (idCgS (addTmH (addTmH (V 2 "lo") (V 9 "i")) (V 10 "g")) (addTmH (V 2 "lo") (addTmH (V 9 "i") (V 10 "g"))) (addAssocT (V 2 "lo") (V 9 "i") (V 10 "g")))
                      (idTr (tS (addTmH (V 2 "lo") (addTmH (V 9 "i") (V 10 "g")))) (addTmH (V 2 "lo") (tS (addTmH (V 9 "i") (V 10 "g")))) (addTmH (V 2 "lo") (tS (tS (V 7 "cnt3"))))
                        (idSy (addTmH (V 2 "lo") (tS (addTmH (V 9 "i") (V 10 "g")))) (tS (addTmH (V 2 "lo") (addTmH (V 9 "i") (V 10 "g")))) (addSuccT (V 2 "lo") (addTmH (V 9 "i") (V 10 "g"))))
                        (idCgAddLo (V 2 "lo") (tS (addTmH (V 9 "i") (V 10 "g"))) (tS (tS (V 7 "cnt3"))) (V 12 "sSize")))))
                  (V 4 "hbnd")))
            (.seq (.call "partScanRange" [.borrow dv, V 2 "lo", tS (V 7 "cnt3"), .ctorApp "Z" [], .ctorApp "Z" [], V 8 "pivot", V 13 "hle"])
              (.seq (.call "quicksort" [.borrow dv, V 5 "f2", V 2 "lo", V 9 "i", V 14 "bl"])
                (.call "quicksort" [.borrow dv, V 5 "f2", tS (addTmH (V 2 "lo") (V 9 "i")), V 10 "g", V 15 "br"]))))))))))) ]) ]) ],
    back := some (sortRangeLT2 (V 1 "fuel") (V 2 "lo") (V 3 "cnt") dv) }
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
  { name := "twoRec",
    retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("f", natT)],
    body := .matchE ⟨1, "f"⟩ [
      .mk "Z" [] .unit,
      .mk "S" [⟨2, "f2"⟩]
        (.seq (.call "twoRec" [.borrow (.deref (V 0 "v")), V 2 "f2"])
          (.seq (.call "twoRec" [.borrow (.deref (V 0 "v")), V 2 "f2"]) .unit)) ],
    back := some dv }
example : checkFnOk twoRec [twoRec] = true := by native_decide

end Dllbc.Tests.S19Partition

