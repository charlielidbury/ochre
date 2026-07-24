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

end Dllbc.Tests.S19Partition
