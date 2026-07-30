import Dllbc.Bench
import Dllbc.DeclMacro

/-!
# `benchqs` — compiled timing harness for the M22 quicksortSorted check

Self-contained (core + macro closure only — NO test-module imports, so checker
edits iterate without re-running the suite's native_decides): verbatim copies of
the CURRENT S17/S19 `decl{}` Decls (nthS/nth2S/swapSN/partScanRange/quicksort)
plus the ScratchDecl `quicksortSorted` (full postcondition: Sorted ∧ Perm via the
staged `sorted_sortRangeL` / `count_sortRangeL` certificates and `old *v`).
Copies MUST stay in sync with the test files; the `qs` benchmark's verdict
cross-validates against the suite.

Usage: `lake exe benchqs <name>`, name ∈ {qs, trace-qs, audit-qs, qsizes, quicksort19}.
-/

open Dllbc
open Dllbc.StdLemmas (swapL set nth partScanRangeL partIdxRangeL partGapRangeL partScanSizeL
  len_partitionRangeL len_sortRangeL sortRangeL partitionRangeL le_up_r le_add le_add_l
  le_add_succ le_rw_r le_rw_l le_add_mono_l add_succ le_trans id_sym id_trans id_congr
  hshift_true hshift_false len_swapL add_zero add_assoc
  SortedR sorted_sortRangeL count_sortRangeL)

namespace Dllbc.BenchQS

/-! ## Decl copies (verbatim from S17Spec / S19Partition / ScratchDecl) -/

def nthS : Decl :=
  decl{ fn nth [v] (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat
        back = λ (r : Nat). set i r (*v)
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match i {
              Z => &mut *hd,
              S(k) => nth(&mut *tl, k, p)
            }
        } } }

def nth2S : Decl :=
  decl{ fn nth2 [v] (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Σ (x : &mut Nat) → &mut Nat
        back = λ (r1 : Nat). λ (r2 : Nat). set i r1 (set j r2 (*v))
        { match v {
            Nil => botElim Unit p2,
            Cons(hd, tl) => match i {
              Z => match j {
                Z => botElim Unit pij,
                S(jjv) => Pair(&mut *hd, nth(&mut *tl, jjv, p2))
              },
              S(k) => match j {
                Z => botElim Unit pij,
                S(jj2) => nth2(&mut *tl, k, jj2, pij, p2)
              }
            }
        } } }

def swapSN : Decl :=
  decl{ fn swapS (v : &mut List Nat, i : Nat, j : Nat,
                  pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Unit
        back = swapL i j (*v)
        { let pr = nth2(v, i, j, pij, p2);
          match pr { Pair(ei, ej) => {
            let t = *ei;
            *ei := *ej;
            *ej := t;
            () } } } }

def partScanRange : Decl :=
  decl{ fn partScanRange [k] (v : &mut List Nat, lo : Nat, k : Nat, i : Nat, g : Nat, pivot : Nat,
        hle : Le (add lo (S (add k (add i g)))) (len *v)) -> Unit
        back = partScanRangeL pivot lo k i g (*v)
        { match k {
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
            S(k2) => {
              let c = leb (nth (add lo (S (add i g))) (*v)) pivot;
              match c {
                True => match g {
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

def quicksort : Decl :=
  decl{ fn quicksort [fuel] (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat, hbnd : Le (add lo cnt) (len *v)) -> Unit
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
                                (id_trans Nat (add i g) (S (add cnt3 Z)) (S cnt3) sizeE
                                  (id_congr Nat Nat (λ (a : Nat). S a) (add cnt3 Z) cnt3 (add_zero cnt3)));
                  let hle = le_rw_l (len *v) (add lo (S (S cnt3))) (add lo (S (S (add cnt3 Z))))
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
                                   (id_congr Nat Nat (λ (a : Nat). S a) (add (add lo i) g) (add lo (add i g)) (add_assoc lo i g))
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

-- Verbatim from the main checkout's untracked Dllbc/Tests/ScratchDecl.lean.
def quicksortSorted : Decl :=
  decl{ fn quicksortSorted (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat, hfuel : Le cnt fuel, hbnd : Le (add lo cnt) (len *v))
        -> Σ (sortedpart : SortedR cnt lo (*v)) → (Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v)))
        { let permcert = (λ (n : Nat). count_sortRangeL n fuel lo cnt (old *v) hbnd);
          let sortedcert = sorted_sortRangeL fuel lo cnt (old *v) hfuel hbnd;
          quicksort(&mut *v, fuel, lo, cnt, hbnd);
          Pair(sortedcert, permcert) } }

def qsTable : List Decl := [nthS, nth2S, swapSN, partScanRange, quicksort, quicksortSorted]

def qsizes : IO Unit := do
  let models : List (String × Term) := [
    ("SortedR", SortedR),
    ("count_sortRangeL", count_sortRangeL),
    ("sorted_sortRangeL", sorted_sortRangeL)]
  for (n, t) in models do
    let sz := Bench.tsize t
    IO.println s!"{n}: term {sz} nodes"
  IO.println s!"quicksortSorted body: term {Bench.tsize quicksortSorted.body} nodes"
  IO.println s!"quicksortSorted retType: term {Bench.tsize quicksortSorted.retType} nodes"
  IO.println s!"S19 quicksort body: term {Bench.tsize quicksort.body} nodes"

def run (which : String) : IO Unit := do
  match which with
  | "qs" => Bench.benchCheck "quicksortSorted" qsTable quicksortSorted
  | "trace-qs" => Bench.benchTrace "quicksortSorted" qsTable quicksortSorted
  | "audit-qs" => Bench.benchTraceAudit "quicksortSorted" qsTable quicksortSorted
  | "quicksort19" => Bench.benchCheck "quicksort (current S19 decl)" [nthS, nth2S, swapSN, partScanRange, quicksort] quicksort
  | "qsizes" => qsizes
  | other => IO.println s!"unknown benchmark '{other}'"

end Dllbc.BenchQS

def main (args : List String) : IO Unit := do
  for a in (if args.isEmpty then ["qsizes"] else args) do
    Dllbc.BenchQS.run a
