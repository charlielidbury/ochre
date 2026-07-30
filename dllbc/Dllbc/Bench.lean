import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro

/-!
# `bench` — compiled timing harness for the checker (perf lane)

`checkFn` on the §17/§19/§21 Decls, as a `lean_exe`, so the expensive checks run
compiled (~30× faster than in-elaboration `native_decide`) and can be timed per
phase (seed / explore / per-path audit). The Decls are verbatim copies of the
test-file definitions — importing `Dllbc.Tests.*` would elaborate their
`native_decide` examples, which is exactly the cost this harness exists to avoid.
Copies MUST stay in sync with the test files (the `check` output cross-validates:
every benchmark also prints the plain `checkFn` verdict).

Usage: `lake exe bench <name>` where name ∈
  {twoRec, partScan, partScanRange, partition, partitionQ, partitionRange,
   quicksort, sizes, all}.
-/

open Dllbc

namespace Dllbc.Bench

/-! ## Term abbreviations (copied from S17Spec/S19Partition) -/

def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def listNatT : Term := .app (.const "List") (.const "Nat")
def natT : Term := .const "Nat"
def mutNat : Term := .borrowT natT natT
def tS (t : Term) : Term := .ctorApp "S" [t]
def LeT (a b : Term) : Term := Std.LeT a b
def lenT (l : Term) : Term := Std.lenT l
def setT (k v l : Term) : Term := .app (.app (.app StdLemmas.set k) v) l
def bE (x : Term) : Term := .app (.app (.const "botElim") (.const "Unit")) x
def rb (x : Var) : Term := .borrow (.deref (.var x))
def pairMut : Term := .sigmaT mutNat mutNat

def addTmH (a b : Term) : Term := .app (.app Std.addFnT a) b
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
def swapLT (i j l : Term) : Term := .app (.app (.app StdLemmas.swapL i) j) l

def leRwL (b x y h p : Term) : Term := .app (.app (.app (.app (.app StdLemmas.le_rw_l b) x) y) h) p
def leAddMonoL (lo a b h : Term) : Term := .app (.app (.app (.app StdLemmas.le_add_mono_l lo) a) b) h
def addSuccT (a b : Term) : Term := .app (.app StdLemmas.add_succ a) b
def leTrans (a b c hab hbc : Term) : Term := .app (.app (.app (.app (.app StdLemmas.le_trans a) b) c) hab) hbc
def loSLam (lo : Term) : Term := .lam natT (addTmH lo (tS (.pvar 0)))
def idCgLoS (lo x y p : Term) : Term := .app (.app (.app (.app (.app (.app StdLemmas.id_congr natT) natT) (loSLam lo)) x) y) p

def partGapRangeLT (lo cnt l : Term) : Term := .app (.app (.app StdLemmas.partGapRangeL lo) cnt) l
def partScanSizeLT (pivot lo k i g l : Term) : Term := .app (.app (.app (.app (.app (.app StdLemmas.partScanSizeL pivot) lo) k) i) g) l
def lenPartRangeLT (lo cnt l : Term) : Term := .app (.app (.app StdLemmas.len_partitionRangeL lo) cnt) l
def lenSortRangeLT (fuel lo cnt l : Term) : Term := .app (.app (.app (.app StdLemmas.len_sortRangeL fuel) lo) cnt) l
def sortRangeLT2 (fuel lo cnt l : Term) : Term := .app (.app (.app (.app StdLemmas.sortRangeL fuel) lo) cnt) l
def leUpR (a b h : Term) : Term := .app (.app (.app StdLemmas.le_up_r a) b) h
def addAssocT (a b c : Term) : Term := .app (.app (.app StdLemmas.add_assoc a) b) c
def loLam (lo : Term) : Term := .lam natT (addTmH lo (.pvar 0))
def idCgAddLo (lo x y p : Term) : Term := .app (.app (.app (.app (.app (.app StdLemmas.id_congr natT) natT) (loLam lo)) x) y) p

def partScanRangeLT (pivot lo k i g l : Term) : Term :=
  .app (.app (.app (.app (.app (.app StdLemmas.partScanRangeL pivot) lo) k) i) g) l
def partIdxRangeLT (lo cnt l : Term) : Term := .app (.app (.app StdLemmas.partIdxRangeL lo) cnt) l
def partitionRangeLT (lo cnt l : Term) : Term := .app (.app (.app StdLemmas.partitionRangeL lo) cnt) l
def partitionLT2 (n l : Term) : Term := .app (.app StdLemmas.partitionL n) l
def addZeroT (n : Term) : Term := .app StdLemmas.add_zero n

/-! ## Decl copies (S17Spec) -/

def nthS : Decl :=
  { name := "nth", retType := mutNat,
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("p", LeT (tS (V 1 "i")) (lenT (.deref (V 0 "v"))))],
    body := .matchE ⟨0, "v"⟩ none [ .mk "Nil" [] (bE (V 2 "p")),
      .mk "Cons" [⟨3, "hd"⟩, ⟨4, "tl"⟩] (.matchE ⟨1, "i"⟩ none [ .mk "Z" [] (rb ⟨3, "hd"⟩),
        .mk "S" [⟨5, "k"⟩] (.call "nth" [rb ⟨4, "tl"⟩, V 5 "k", V 2 "p"]) ]) ],
    back := some (.lam natT (setT (V 1 "i") (.pvar 0) (.deref (V 0 "v")))) }

def nth2S : Decl :=
  { name := "nth2", retType := pairMut,
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("j", natT),
      ("pij", LeT (tS (V 1 "i")) (V 2 "j")), ("p2", LeT (tS (V 2 "j")) (lenT (.deref (V 0 "v"))))],
    body := .matchE ⟨0, "v"⟩ none [ .mk "Nil" [] (bE (V 4 "p2")),
      .mk "Cons" [⟨5, "hd"⟩, ⟨6, "tl"⟩] (.matchE ⟨1, "i"⟩ none [
        .mk "Z" [] (.matchE ⟨2, "j"⟩ none [ .mk "Z" [] (bE (V 3 "pij")),
          .mk "S" [⟨7, "jjv"⟩] (.ctorApp "Pair" [rb ⟨5, "hd"⟩, .call "nth" [rb ⟨6, "tl"⟩, V 7 "jjv", V 4 "p2"]]) ]),
        .mk "S" [⟨8, "k"⟩] (.matchE ⟨2, "j"⟩ none [ .mk "Z" [] (bE (V 3 "pij")),
          .mk "S" [⟨9, "jj2"⟩] (.call "nth2" [rb ⟨6, "tl"⟩, V 8 "k", V 9 "jj2", V 3 "pij", V 4 "p2"]) ]) ]) ],
    back := some (.lam natT (.lam natT (setT (V 1 "i") (.pvar 1) (setT (V 2 "j") (.pvar 0) (.deref (V 0 "v")))))) }

def swapSN : Decl :=
  { name := "swapS", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("j", natT),
      ("pij", LeT (tS (V 1 "i")) (V 2 "j")), ("p2", LeT (tS (V 2 "j")) (lenT (.deref (V 0 "v"))))],
    body := .letIn ⟨5, "pr"⟩ (.call "nth2" [V 0 "v", V 1 "i", V 2 "j", V 3 "pij", V 4 "p2"])
      (.matchE ⟨5, "pr"⟩ none [ .mk "Pair" [⟨6, "ei"⟩, ⟨7, "ej"⟩]
        (.letIn ⟨8, "t"⟩ (.deref (V 6 "ei"))
          (.assign (.deref (V 6 "ei")) (.deref (V 7 "ej"))
            (.assign (.deref (V 7 "ej")) (V 8 "t") .unit))) ]),
    back := some (.app (.app (.app StdLemmas.swapL (V 1 "i")) (V 2 "j")) (.deref (V 0 "v"))) }

/-! ## Decl copies (S19Partition) -/

def partScan : Decl :=
  { name := "partScan", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("k", natT), ("i", natT), ("g", natT), ("pivot", natT),
      ("hlen", .idT natT (lenT dv) (tS (addTmH (V 1 "k") (addTmH (V 2 "i") (V 3 "g")))))],
    body := .matchE ⟨1, "k"⟩ none [
      .mk "Z" [] (.matchE ⟨2, "i"⟩ none [
        .mk "Z" [] .unit,
        .mk "S" [⟨7, "i2"⟩] (.letIn ⟨8, "p2b"⟩
          (leRwR (tS (tS (V 7 "i2"))) (tS (tS (addTmH (V 7 "i2") (V 3 "g")))) (lenT dv)
            (idSy (lenT dv) (tS (tS (addTmH (V 7 "i2") (V 3 "g")))) (V 5 "hlen"))
            (leAdd (V 7 "i2") (V 3 "g")))
          (.seq (.call "swapS" [.var ⟨0, "v"⟩, .ctorApp "Z" [], tS (V 7 "i2"), .unit, V 8 "p2b"]) .unit)) ]),
      .mk "S" [⟨6, "k2"⟩] (.letIn ⟨7, "c"⟩ (lebP (nthP (tS (addTmH (V 2 "i") (V 3 "g"))) dv) (V 4 "pivot"))
        (.matchE ⟨7, "c"⟩ none [
          .mk "True" [] (.matchE ⟨3, "g"⟩ none [
            .mk "Z" [] (.letIn ⟨8, "hlZ"⟩
              (idTr (lenT dv) (tS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (.ctorApp "Z" []))))
                (tS (addTmH (V 6 "k2") (addTmH (tS (V 2 "i")) (.ctorApp "Z" []))))
                (V 5 "hlen")
                (idCgS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (.ctorApp "Z" [])))
                  (addTmH (V 6 "k2") (addTmH (tS (V 2 "i")) (.ctorApp "Z" [])))
                  (hsT (V 6 "k2") (V 2 "i") (.ctorApp "Z" []))))
              (.call "partScan" [.var ⟨0, "v"⟩, V 6 "k2", tS (V 2 "i"), .ctorApp "Z" [], V 4 "pivot", V 8 "hlZ"])),
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
          .mk "False" [] (.letIn ⟨8, "hlF"⟩
            (idTr (lenT dv) (tS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (V 3 "g"))))
              (tS (addTmH (V 6 "k2") (addTmH (V 2 "i") (tS (V 3 "g")))))
              (V 5 "hlen")
              (idCgS (addTmH (tS (V 6 "k2")) (addTmH (V 2 "i") (V 3 "g")))
                (addTmH (V 6 "k2") (addTmH (V 2 "i") (tS (V 3 "g"))))
                (hsF (V 6 "k2") (V 2 "i") (V 3 "g"))))
            (.call "partScan" [.var ⟨0, "v"⟩, V 6 "k2", V 2 "i", tS (V 3 "g"), V 4 "pivot", V 8 "hlF"])) ])) ],
    back := some (partScanLT (V 4 "pivot") (V 1 "k") (V 2 "i") (V 3 "g") dv) }

def partScanRange : Decl :=
  { name := "partScanRange", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("lo", natT), ("k", natT), ("i", natT), ("g", natT), ("pivot", natT),
      ("hle", LeT (addTmH (V 1 "lo") (tS (addTmH (V 2 "k") (addTmH (V 3 "i") (V 4 "g"))))) (lenT dv))],
    body := .matchE ⟨2, "k"⟩ none [
      .mk "Z" [] (.matchE ⟨3, "i"⟩ none [
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
      .mk "S" [⟨7, "k2"⟩] (.letIn ⟨8, "c"⟩ (lebP (nthP (addTmH (V 1 "lo") (tS (addTmH (V 3 "i") (V 4 "g")))) dv) (V 5 "pivot"))
        (.matchE ⟨8, "c"⟩ none [
          .mk "True" [] (.matchE ⟨4, "g"⟩ none [
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

def partition : Decl :=
  { name := "partition", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("n", natT),
      ("hlenW", .idT natT (lenT dv) (V 1 "n"))],
    body := .matchE ⟨1, "n"⟩ none [
      .mk "Z" [] .unit,
      .mk "S" [⟨3, "n2"⟩] (.letIn ⟨4, "pivot"⟩ (nthP (.ctorApp "Z" []) dv)
        (.letIn ⟨5, "hlen"⟩
          (idTr (lenT dv) (tS (V 3 "n2")) (tS (addTmH (V 3 "n2") (.ctorApp "Z" [])))
            (V 2 "hlenW")
            (idSy (tS (addTmH (V 3 "n2") (.ctorApp "Z" []))) (tS (V 3 "n2"))
              (idCgS (addTmH (V 3 "n2") (.ctorApp "Z" [])) (V 3 "n2") (addZeroT (V 3 "n2")))))
          (.call "partScan" [.var ⟨0, "v"⟩, V 3 "n2", .ctorApp "Z" [], .ctorApp "Z" [], V 4 "pivot", V 5 "hlen"]))) ],
    back := some (partitionLT2 (V 1 "n") dv) }

def partitionQ : Decl :=
  { name := "partitionQ",
    retType := .sigmaT natT (.idT natT (.pvar 0) (.app (.app StdLemmas.partIdxL (V 1 "n")) dv)),
    telescope := [("v", .borrowT listNatT listNatT), ("n", natT), ("hlenW", .idT natT (lenT dv) (V 1 "n"))],
    body := .matchE ⟨1, "n"⟩ none [
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

def partitionRange : Decl :=
  { name := "partitionRange",
    retType := .sigmaT natT (.idT natT (.pvar 0) (partIdxRangeLT (V 1 "lo") (V 2 "cnt") dv)),
    telescope := [("v", .borrowT listNatT listNatT), ("lo", natT), ("cnt", natT),
      ("hbnd", LeT (addTmH (V 1 "lo") (V 2 "cnt")) (lenT dv))],
    body := .matchE ⟨2, "cnt"⟩ none [
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

def quicksort : Decl :=
  { name := "quicksort", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("fuel", natT), ("lo", natT), ("cnt", natT),
      ("hbnd", LeT (addTmH (V 2 "lo") (V 3 "cnt")) (lenT dv))],
    body := .matchE ⟨1, "fuel"⟩ none [
      .mk "Z" [] .unit,
      .mk "S" [⟨5, "f2"⟩] (.matchE ⟨3, "cnt"⟩ none [
        .mk "Z" [] .unit,
        .mk "S" [⟨6, "cnt2"⟩] (.matchE ⟨6, "cnt2"⟩ none [
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

def twoRec : Decl :=
  { name := "twoRec",
    retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("f", natT)],
    body := .matchE ⟨1, "f"⟩ none [
      .mk "Z" [] .unit,
      .mk "S" [⟨2, "f2"⟩]
        (.seq (.call "twoRec" [.borrow (.deref (V 0 "v")), V 2 "f2"])
          (.seq (.call "twoRec" [.borrow (.deref (V 0 "v")), V 2 "f2"]) .unit)) ],
    back := some dv }

/-! ## Tables -/

def partScanTable : List Decl := [nthS, nth2S, swapSN, partScan]
def partScanRangeTable : List Decl := [nthS, nth2S, swapSN, partScanRange]
def partitionTable : List Decl := [nthS, nth2S, swapSN, partScan, partition]
def partitionQTable : List Decl := [nthS, nth2S, swapSN, partScan, partitionQ]
def partitionRangeTable : List Decl := [nthS, nth2S, swapSN, partScanRange, partitionRange]
def quicksortTable : List Decl := [nthS, nth2S, swapSN, partScanRange, quicksort]

/-! ## Measurement helpers -/

partial def vsize : Val → Nat
  | .ctor _ args => 1 + (args.map vsize).foldl (·+·) 0
  | .borrowM _ p => 1 + vsize p
  | .pi d c => 1 + vsize d + vsize c
  | .sigmaT d c => 1 + vsize d + vsize c
  | .lam d c => 1 + vsize d + vsize c
  | .app d c => 1 + vsize d + vsize c
  | .idT a b c => 1 + vsize a + vsize b + vsize c
  | _ => 1

partial def vdepth : Val → Nat
  | .ctor _ args => 1 + (args.map vdepth).foldl Nat.max 0
  | .borrowM _ p => 1 + vdepth p
  | .pi d c => 1 + Nat.max (vdepth d) (vdepth c)
  | .sigmaT d c => 1 + Nat.max (vdepth d) (vdepth c)
  | .lam d c => 1 + Nat.max (vdepth d) (vdepth c)
  | .app d c => 1 + Nat.max (vdepth d) (vdepth c)
  | .idT a b c => 1 + Nat.max (vdepth a) (Nat.max (vdepth b) (vdepth c))
  | _ => 1

partial def tsize : Term → Nat
  | .app d c => 1 + tsize d + tsize c
  | .lam d c => 1 + tsize d + tsize c
  | .pi d c => 1 + tsize d + tsize c
  | .sigmaT d c => 1 + tsize d + tsize c
  | .idT a b c => 1 + tsize a + tsize b + tsize c
  | .ctorApp _ args => 1 + (args.map tsize).foldl (·+·) 0
  | .letIn _ a b => 1 + tsize a + tsize b
  | .assign a b c => 1 + tsize a + tsize b + tsize c
  | .seq a b => 1 + tsize a + tsize b
  | .borrow a => 1 + tsize a
  | .deref a => 1 + tsize a
  | .borrowT a b => 1 + tsize a + tsize b
  | .matchE _ _ brs => 1 + (brs.map (fun b => tsize b.body)).foldl (·+·) 0
  | .call _ args => 1 + (args.map tsize).foldl (·+·) 0
  | _ => 1

/-! ## Instrumented explore: per-statement wall timing (bench-local copy of
    `Machine.explore`; prints steps slower than 50 ms). -/

partial def exploreIO (fuel : Nat) (t : Term) (st : St) (lbl : String) : IO (List (Except String (Val × St))) := do
  match fuel with
  | 0 => pure [.error "explore: out of fuel"]
  | fuel + 1 =>
    match t with
    | .matchE scrut eqn branches =>
      match (reorgScrut fuel scrut).run st with
      | .error e _ => pure [.error e]
      | .ok disp st' =>
        match disp with
        | .ownedCtor name fields =>
          match (ownedSelect scrut eqn branches name fields).run st' with
          | .error e _ => pure [.error e]
          | .ok body st'' => exploreIO fuel body st'' lbl
        | .borrowCtor ℓ name fields =>
          match (borrowSelect scrut eqn branches ℓ name fields).run st' with
          | .error e _ => pure [.error e]
          | .ok body st'' => exploreIO fuel body st'' lbl
        | .ownedSym σ stuck =>
          match (checkExhaustive fuel σ branches).run st' with
          | .error e _ => pure [.error e]
          | .ok _ st'' => goBranches fuel scrut false 0 σ stuck eqn branches st'' lbl
        | .borrowSym ℓ σ =>
          match (checkExhaustive fuel σ branches).run st' with
          | .error e _ => pure [.error e]
          | .ok _ st'' => goBranches fuel scrut true ℓ σ none eqn branches st'' lbl
    | .letIn x rhs rest => do
      let t0 ← IO.monoMsNow
      let r := (do let v ← readR fuel rhs; bindSlot x v; pure v).run st
      let t1 ← IO.monoMsNow
      if t1 - t0 > 50 then
        let vs := match r with | .ok v _ => vsize v | _ => 0
        let vd := match r with | .ok v _ => vdepth v | _ => 0
        IO.println s!"    [{lbl}] let {x.name} := … : {t1 - t0} ms (val size {vs}, depth {vd}, rhs term {tsize rhs})"
      match r with
      | .error e _ => pure [.error e]
      | .ok _ st' => exploreIO fuel rest st' lbl
    | .seq e rest => do
      let t0 ← IO.monoMsNow
      let r := (do let _ ← readR fuel e; pure ()).run st
      let t1 ← IO.monoMsNow
      if t1 - t0 > 50 then
        IO.println s!"    [{lbl}] seq step ({tsize e}-node term): {t1 - t0} ms"
      match r with
      | .error e _ => pure [.error e]
      | .ok _ st' => exploreIO fuel rest st' lbl
    | .assign p rhs rest => do
      let t0 ← IO.monoMsNow
      let r := (do let v ← readR fuel rhs; writeR fuel p v).run st
      let t1 ← IO.monoMsNow
      if t1 - t0 > 50 then
        IO.println s!"    [{lbl}] assign: {t1 - t0} ms"
      match r with
      | .error e _ => pure [.error e]
      | .ok _ st' => exploreIO fuel rest st' lbl
    | other => do
      let t0 ← IO.monoMsNow
      let r := (readR fuel other).run st
      let t1 ← IO.monoMsNow
      if t1 - t0 > 50 then
        IO.println s!"    [{lbl}] final expr: {t1 - t0} ms"
      match r with
      | .error e _ => pure [.error e]
      | .ok v st' => pure [.ok (v, st')]
  where goBranches (fuel : Nat) (scrut : Var) (borrow : Bool) (ℓ σ : Nat) (stuck : Option Val)
      (eqn : Option Var) (branches : List Branch) (st : St) (lbl : String) : IO (List (Except String (Val × St))) := do
    match branches with
    | [] => pure []
    | br :: rest => do
      let head ← (match ((if borrow then symBorrowSetup 1000 scrut ℓ σ eqn br
                            else symOwnedSetup 1000 scrut σ stuck eqn br)).run st with
        | .error e _ => pure [.error e]
        | .ok body st' => exploreIO 1000 body st' s!"{lbl}.{br.ctor}")
      let tail ← goBranches fuel scrut borrow ℓ σ stuck eqn rest st lbl
      pure (head ++ tail)

/-- `benchCheck` but with the per-statement instrumented explore. -/
def benchTrace (name : String) (table : List Decl) (decl : Decl) : IO Unit := do
  IO.println s!"== {name} (trace) =="
  let t0 ← IO.monoMsNow
  -- Mirror of checkFn's seed (MUST stay in sync with Boundary.checkFn — §5.4
  -- exitSyms + markExit included).
  let seed : M (List Obligation) := do
    let obs ← seedTelescope defaultFuel 0 decl.telescope
    let borrowIds := borrowParamIds decl.telescope
    let exits ← borrowIds.mapM (fun i => do pure (i, ← freshSym))
    modify (fun s => { s with exitSyms := exits })
    if hasBorrowT decl.retType then pure ()
    else do
      let rv ← readC defaultFuel (markExit borrowIds decl.retType)
      modify (fun s => { s with retTyVal := some rv })
    match decl.back with
    | some b => do
      let bv ← readC defaultFuel b
      modify (fun s => { s with selfBack := some bv })
    | none => pure ()
    pure obs
  match seed.run { initSt with decls := table } with
  | .error e _ => IO.println s!"seed ERROR: {e}"
  | .ok obs st => do
    let t1 ← IO.monoMsNow
    let paths ← exploreIO defaultFuel (pushContinuations decl.body) { st with obligations := obs } "p"
    let t2 ← IO.monoMsNow
    IO.println s!"  explore: {t2 - t1} ms, {paths.length} paths (seed {t1 - t0} ms)"

/-- Mirror of `auditAction`'s VALUE-RETURNING arm with per-stage timing
    (obligations / selfBack skipped-if-none / §5.4 exit-substitution / final
    hasType). MUST stay in sync with Boundary.auditAction. Only for decls whose
    result is not a botElim and not borrow-returning. -/
def benchAudit (retType : Term) (v : Val) (st0 : St) : IO Unit := do
  let obs := st0.obligations
  let t0 ← IO.monoMsNow
  match (obs.forM (auditObligation defaultFuel [])).run st0 with
  | .error e _ => IO.println s!"      audit/obligations ERR: {(e.take 90)}"
  | .ok _ st1 => do
    let t1 ← IO.monoMsNow
    IO.println s!"      audit/obligations: {t1 - t0} ms"
    if st1.selfBack.isSome then
      IO.println "      audit/selfBack: PRESENT — benchAudit skips it (out of sync with auditAction!)"
    let retTy0 ← match st1.retTyVal with
      | some rv => pure rv
      | none => match (readC defaultFuel retType).run st1 with
        | .ok rv _ => pure rv
        | .error _ _ => pure .bot
    let sub : M Val := do
      let exits := (← get).exitSyms
      obs.foldlM (fun acc ob =>
        match exits.lookup ob.arg.id with
        | none => pure acc
        | some σ => do
          match (← getEnv).findSome? (fun kv => findBorrowPayload ob.loan kv.2) with
          | some payload => pure (Val.nfV defaultFuel (substSym σ payload acc))
          | none => pure acc) retTy0
    match sub.run st1 with
    | .error e _ => IO.println s!"      audit/exit-subst ERR: {(e.take 90)}"
    | .ok retTy st2 => do
      let t2 ← IO.monoMsNow
      IO.println s!"      audit/exit-subst: {t2 - t1} ms (retTy {vsize retTy0} -> {vsize retTy} nodes, result {vsize v} nodes)"
      match (hasType defaultFuel v retTy).run st2 with
      | .error e _ => IO.println s!"      audit/hasType ERR: {(e.take 120)}"
      | .ok ok st3 => do
        let t3 ← IO.monoMsNow
        IO.println s!"      audit/hasType: {t3 - t2} ms -> {ok} (sctx {st2.sctx.size} -> {st3.sctx.size})"

/-- seed → explore → per-path staged audit (via `benchAudit`). -/
def benchTraceAudit (name : String) (table : List Decl) (decl : Decl) : IO Unit := do
  IO.println s!"== {name} (audit trace) =="
  -- Mirror of checkFn's seed (MUST stay in sync with Boundary.checkFn — §5.4
  -- exitSyms + markExit included).
  let seed : M (List Obligation) := do
    let obs ← seedTelescope defaultFuel 0 decl.telescope
    let borrowIds := borrowParamIds decl.telescope
    let exits ← borrowIds.mapM (fun i => do pure (i, ← freshSym))
    modify (fun s => { s with exitSyms := exits })
    if hasBorrowT decl.retType then pure ()
    else do
      let rv ← readC defaultFuel (markExit borrowIds decl.retType)
      modify (fun s => { s with retTyVal := some rv })
    match decl.back with
    | some b => do
      let bv ← readC defaultFuel b
      modify (fun s => { s with selfBack := some bv })
    | none => pure ()
    pure obs
  match seed.run { initSt with decls := table } with
  | .error e _ => IO.println s!"seed ERROR: {e}"
  | .ok obs st => do
    let t1 ← IO.monoMsNow
    let paths := explore defaultFuel (pushContinuations decl.body) { st with obligations := obs }
    let t2 ← IO.monoMsNow
    IO.println s!"  explore: {t2 - t1} ms, {paths.length} paths"
    let mut i := 0
    for p in paths do
      match p with
      | .error e => IO.println s!"  path {i}: explore ERR: {(e.take 90)}"
      | .ok (v, stp) => do
        IO.println s!"  path {i}:"
        benchAudit decl.retType v stp
      i := i + 1

/-- Replicate `checkFn` with per-phase wall timing and per-path stats. -/
def benchCheck (name : String) (table : List Decl) (decl : Decl) : IO Unit := do
  IO.println s!"== {name} =="
  let t0 ← IO.monoMsNow
  -- Mirror of checkFn's seed (MUST stay in sync with Boundary.checkFn — §5.4
  -- exitSyms + markExit included).
  let seed : M (List Obligation) := do
    let obs ← seedTelescope defaultFuel 0 decl.telescope
    let borrowIds := borrowParamIds decl.telescope
    let exits ← borrowIds.mapM (fun i => do pure (i, ← freshSym))
    modify (fun s => { s with exitSyms := exits })
    if hasBorrowT decl.retType then pure ()
    else do
      let rv ← readC defaultFuel (markExit borrowIds decl.retType)
      modify (fun s => { s with retTyVal := some rv })
    match decl.back with
    | some b => do
      let bv ← readC defaultFuel b
      modify (fun s => { s with selfBack := some bv })
    | none => pure ()
    pure obs
  match seed.run { initSt with decls := table } with
  | .error e _ => IO.println s!"seed ERROR: {e}"
  | .ok obs st => do
    let t1 ← IO.monoMsNow
    IO.println s!"  seed: {t1 - t0} ms (selfBack size: {st.selfBack.map vsize |>.getD 0})"
    let paths := explore defaultFuel (pushContinuations decl.body) { st with obligations := obs }
    let n := paths.length
    let t2 ← IO.monoMsNow
    IO.println s!"  explore: {t2 - t1} ms, {n} paths"
    let mut i := 0
    let mut allOk := true
    for p in paths do
      let ta ← IO.monoMsNow
      match p with
      | .error e => do
        IO.println s!"  path {i}: explore ERR: {(e.take 90)}"
        allOk := false
      | .ok (v, stp) => do
        let r := (auditAction defaultFuel decl.retType v).run stp
        let tb ← IO.monoMsNow
        match r with
        | .ok _ _ =>
          IO.println s!"  path {i}: audit ok  {tb - ta} ms (res {vsize v}, env {stp.env.length}, sctx {stp.sctx.size}, groups {stp.groups.length})"
        | .error e _ => do
          IO.println s!"  path {i}: audit ERR {tb - ta} ms: {(e.take 90)}"
          allOk := false
      i := i + 1
    let t3 ← IO.monoMsNow
    IO.println s!"  audit total: {t3 - t2} ms | grand total {t3 - t0} ms | verdict: {if allOk then "OK" else "REJECTED"}"

def sizes : IO Unit := do
  let models : List (String × Term) := [
    ("swapL", StdLemmas.swapL), ("nth", StdLemmas.nth), ("set", StdLemmas.set),
    ("partScanL", StdLemmas.partScanL), ("partitionL", StdLemmas.partitionL),
    ("partIdxL", StdLemmas.partIdxL), ("sortL", StdLemmas.sortL),
    ("partScanRangeL", StdLemmas.partScanRangeL), ("partitionRangeL", StdLemmas.partitionRangeL),
    ("partIdxRangeL", StdLemmas.partIdxRangeL), ("partGapRangeL", StdLemmas.partGapRangeL),
    ("partScanSizeL", StdLemmas.partScanSizeL), ("len_partitionRangeL", StdLemmas.len_partitionRangeL),
    ("len_sortRangeL", StdLemmas.len_sortRangeL), ("sortRangeL", StdLemmas.sortRangeL)]
  for (n, t) in models do
    let v := Val.Term.toValPure t
    let nf := Val.nfV 1000 v
    IO.println s!"{n}: term {tsize t}, val {vsize v}, nf {vsize nf}"
  IO.println s!"quicksort body: term {tsize Bench.quicksort.body}"
  IO.println s!"partScanRange body: term {tsize Bench.partScanRange.body}"

def run (which : String) : IO Unit := do
  match which with
  | "twoRec" => benchCheck "twoRec" [twoRec] twoRec
  | "partScan" => benchCheck "partScan" partScanTable partScan
  | "partScanRange" => benchCheck "partScanRange" partScanRangeTable partScanRange
  | "partition" => benchCheck "partition" partitionTable partition
  | "partitionQ" => benchCheck "partitionQ" partitionQTable partitionQ
  | "partitionRange" => benchCheck "partitionRange" partitionRangeTable partitionRange
  | "quicksort" => benchCheck "quicksort" quicksortTable quicksort
  | "trace-quicksort" => benchTrace "quicksort" quicksortTable quicksort
  | "trace-partScanRange" => benchTrace "partScanRange" partScanRangeTable partScanRange
  | "sizes" => sizes
  | "all" => do
    sizes
    benchCheck "twoRec" [twoRec] twoRec
    benchCheck "partScan" partScanTable partScan
    benchCheck "partScanRange" partScanRangeTable partScanRange
    benchCheck "partition" partitionTable partition
    benchCheck "partitionQ" partitionQTable partitionQ
    benchCheck "partitionRange" partitionRangeTable partitionRange
    benchCheck "quicksort" quicksortTable quicksort
  | other => IO.println s!"unknown benchmark '{other}'"

end Dllbc.Bench
