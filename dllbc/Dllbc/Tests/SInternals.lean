import Dllbc.DeclMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `SInternals` — the gathered round-trip corpora (raw Terms ARE the subject here)

SUBJECT FILE. Everything below is a hand-built raw `Term`/`Decl` — the "old way" a
`decl{ }` surface Decl is compared AGAINST in the round-trip suites (SDeclUnified,
SDeclMacroCrown). Per the compat policy, the gatherable round-trip corpora live
here, in one clearly-marked place, so the round-trip TEST files read as modern
surface plus an `== SInternals.corpus` assertion. The raw `.ctorApp`/`V i`/`LeT`
constructions are the point of this file — it is the reference the macro reproduces.

The assertion-adjacent subjects (lying specs, differential harnesses, per-file
local builders) stay inline in their own files under `-- SUBJECT:` banners.
-/

open Dllbc

namespace Dllbc.Tests.SInternals

/-! ## Shared corpus builders (the corpus's exact constructors, transcribed) -/

def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def natT : Term := .const "Nat"
def listNatT : Term := .app (.const "List") (.const "Nat")
def tS (t : Term) : Term := .ctorApp "S" [t]
def zt : Term := .ctorApp "Z" []
def dv : Term := .deref (V 0 "v")
def dV (i : Nat) (n : String) : Term := .deref (.var ⟨i, n⟩)
def u : Term := .unit
def addTm (a b : Term) : Term := .app (.app Std.addFnT a) b
def lebT (a b : Term) : Term := .app (.app Std.lebFnT a) b
def nthT (k l : Term) : Term := .app (.app StdLemmas.nth k) l
def LeT (a b : Term) : Term := Std.LeT a b
def lenT (l : Term) : Term := Std.lenT l
def leRwR (a b c d e : Term) : Term := .app (.app (.app (.app (.app StdLemmas.le_rw_r a) b) c) d) e
def idSym (t a b h : Term) : Term := .app (.app (.app (.app StdLemmas.id_sym t) a) b) h
def leAdd (a b : Term) : Term := .app (.app StdLemmas.le_add a) b
def sortRangeLT2 (fuel lo cnt l : Term) : Term :=
  .app (.app (.app (.app StdLemmas.sortRangeL fuel) lo) cnt) l

/-! ## SDeclUnified corpora — `partScanE` and `pivotPlaceH`, transcribed S19-free
    (verbatim from S19Partition.lean's pre-conversion hand ids). -/

-- Verbatim transcription of the pre-conversion partScanE (exact hand ids).
def partScanEExpected : Decl :=
  { name := "partScanE", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("k", natT), ("i", natT), ("g", natT), ("pivot", natT)],
    body := .matchE ⟨1, "k"⟩ [
      .mk "Z" [] (.matchE ⟨2, "i"⟩ [
        .mk "Z" [] u,
        .mk "S" [⟨6, "i2"⟩] (.seq (.call "swapS" [.var ⟨0, "v"⟩, zt, tS (V 6 "i2"), u, u]) u) ]),
      .mk "S" [⟨5, "k2"⟩]
        (.letIn ⟨6, "c"⟩ (lebT (nthT (tS (addTm (V 2 "i") (V 3 "g"))) (dV 0 "v")) (V 4 "pivot"))
          (.matchE ⟨6, "c"⟩ [
            .mk "True" [] (.matchE ⟨3, "g"⟩ [
              .mk "Z" [] (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", tS (V 2 "i"), zt, V 4 "pivot"]),
              .mk "S" [⟨7, "g2"⟩] (.seq (.call "swapS" [.borrow (dV 0 "v"), tS (V 2 "i"), tS (addTm (V 2 "i") (tS (V 7 "g2"))), u, u])
                (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", tS (V 2 "i"), tS (V 7 "g2"), V 4 "pivot"])) ]),
            .mk "False" [] (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", V 2 "i", tS (V 3 "g"), V 4 "pivot"]) ])) ] }

-- pivotPlaceH's `back` (a natRec baseBack spine), shared by the surface Decl (spliced) and its corpus.
def baseBackDef : Term :=
  .app (.app (.app (.app (.const "natRec") (.lam natT listNatT)) (dV 0 "v"))
    (.lam natT (.lam listNatT (.app (.app (.app StdLemmas.swapL zt) (tS (.pvar 1))) (dV 0 "v"))))) (V 1 "i")

-- Built via `Decl.mk` positionally: the surface keyword `back` reserves the token,
-- so a `{ … back := … }` structure literal cannot name the field here.
def pivotPlaceHExpected : Decl :=
  Dllbc.Decl.mk "pivotPlaceH"
    [("v", .borrowT listNatT listNatT), ("i", natT), ("g", natT),
     ("hlen", .idT natT (lenT (dV 0 "v")) (tS (addTm (V 1 "i") (V 2 "g"))))]
    (.const "Unit")
    (.matchE ⟨1, "i"⟩ [
      .mk "Z" [] .unit,
      .mk "S" [⟨4, "i2"⟩] (.letIn ⟨5, "p2"⟩
        (leRwR (tS (tS (V 4 "i2"))) (tS (tS (addTm (V 4 "i2") (V 2 "g")))) (lenT (dV 0 "v"))
          (idSym natT (lenT (dV 0 "v")) (tS (tS (addTm (V 4 "i2") (V 2 "g")))) (V 3 "hlen"))
          (leAdd (V 4 "i2") (V 2 "g")))
        (.seq (.call "swapS" [.var ⟨0, "v"⟩, .ctorApp "Z" [], tS (V 4 "i2"), .unit, V 5 "p2"]) .unit)) ])
    (some baseBackDef)
    none                                  -- `dec` (§1.2's [k]): pivotPlaceH does not recurse

/-! ## SDeclMacroCrown corpus — quicksort's telescope and back
    (character-for-character the corpus's expressions, S19Partition.lean's crown). -/

def quicksortExpTele : List (String × Term) :=
  [("v", .borrowT listNatT listNatT), ("fuel", natT), ("lo", natT), ("cnt", natT),
   ("hbnd", LeT (addTm (V 2 "lo") (V 3 "cnt")) (lenT dv))]
def quicksortExpBack : Term := sortRangeLT2 (V 1 "fuel") (V 2 "lo") (V 3 "cnt") dv

end Dllbc.Tests.SInternals
