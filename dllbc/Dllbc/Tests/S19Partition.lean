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

end Dllbc.Tests.S19Partition
