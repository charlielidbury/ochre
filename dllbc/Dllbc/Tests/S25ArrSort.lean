import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.StdLemmas
import Dllbc.Tests.S9Diff

/-!
# §25 test suite — the in-place array partition, and the array quicksort

¶6's migration completed: the leaf program ledger G4 says does not transfer, and the
assembly it feeds. `S24Arrays` established that every PIECE works (the carve, the
elementization, the transferred library, `sort2` as the whole stack at width two);
this file is the two programs those pieces were for.
-/

open Dllbc
open Dllbc.StdLemmas (le_refl le_add le_add_l le_add_succ le_trans le_up_r le_pred_l
  leb_true_le leb_false_gt add_succ add_zero id_trans id_congr id_sym znots
  SortedA UbA LbA countA asingle sorted_arrCat count_arrCat ub_permA lb_permA
  nat_rw nat_rw_ty le_zero_eq le_zero_eq_ty sortedA_nil sortedA_nil_ty
  SplitA PartA splitA_nil splitA_nil_ty
  splitA0_lb splitA0_lb_ty splitA_cat_e1 splitA_cat_e1_ty
  splitA_cat_i0 splitA_cat_i0_ty partA_cat_i0 partA_cat_i0_ty
  partA_cat_e0 partA_cat_e0_ty
  bumpN count_acons_congr count_acons_congr_ty bump_comm bump_comm_ty
  count_swapA count_swapA_ty
  splitA_cat_ub splitA_cat_ub_ty splitA_cat_rest splitA_cat_rest_ty
  splitA1_head splitA1_head_ty splitA1_tail splitA1_tail_ty
  partA_cat_ub partA_cat_ub_ty partA_cat_rest partA_cat_rest_ty
  partA0_eq partA0_eq_ty partA0_lb partA0_lb_ty)

namespace Dllbc.Tests.S25ArrSort

/-- Type-check a closed term against a closed type in the pure seed (as §23/§24). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasType 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)

def checkFnMsg (d : Decl) (tbl : List Decl := [d]) : String :=
  match checkFn tbl d with | .ok _ => "OK" | .error e => e

/-! ## (i) The partition layer's predicates and their nil lemmas -/

example : chkL nat_rw nat_rw_ty = true := by native_decide
example : chkL le_zero_eq le_zero_eq_ty = true := by native_decide
example : chkL sortedA_nil sortedA_nil_ty = true := by native_decide
example : chkL splitA_nil splitA_nil_ty = true := by native_decide

-- The predicates COMPUTE on a run, at every skip count.
-- `SplitA 3 2 [1,2,7]`: first two ≤ 3, last ≥ 3.
example : chkL pure{ Pair(unit, Pair(unit, Pair(unit, unit))) }
               pure{ SplitA 3 2 3 Arr(1, 2, 7) } = true := by native_decide
-- …and it is NOT vacuous: the same array does not split at 1 (element 1 is `2 ≥ 3`? no).
example : chkL pure{ Pair(unit, Pair(unit, Pair(unit, unit))) }
               pure{ SplitA 3 1 3 Arr(1, 2, 7) } = false := by native_decide

-- `PartA 3 2 [1,2,3,7]`: first two ≤ 3, element 2 IS 3, the rest ≥ 3.
example : chkL pure{ Pair(unit, Pair(unit, Pair(Refl, Pair(unit, unit)))) }
               pure{ PartA 3 2 4 Arr(1, 2, 3, 7) } = true := by native_decide
-- The pivot-identity conjunct is load-bearing: element 2 is 4, not 3.
example : chkL pure{ Pair(unit, Pair(unit, Pair(Refl, Pair(unit, unit)))) }
               pure{ PartA 3 2 4 Arr(1, 2, 4, 7) } = false := by native_decide

/-! ### Crossing a concatenation — each an induction on the left array alone -/

example : chkL splitA0_lb splitA0_lb_ty = true := by native_decide
example : chkL splitA_cat_e1 splitA_cat_e1_ty = true := by native_decide
example : chkL splitA_cat_i0 splitA_cat_i0_ty = true := by native_decide
example : chkL partA_cat_i0 partA_cat_i0_ty = true := by native_decide
example : chkL partA_cat_e0 partA_cat_e0_ty = true := by native_decide

/-! ### One conclusion each, so the programs need no inline `elim` -/

example : chkL splitA_cat_ub splitA_cat_ub_ty = true := by native_decide
example : chkL splitA_cat_rest splitA_cat_rest_ty = true := by native_decide
example : chkL splitA1_head splitA1_head_ty = true := by native_decide
example : chkL splitA1_tail splitA1_tail_ty = true := by native_decide
example : chkL partA_cat_ub partA_cat_ub_ty = true := by native_decide
example : chkL partA_cat_rest partA_cat_rest_ty = true := by native_decide
example : chkL partA0_eq partA0_eq_ty = true := by native_decide
example : chkL partA0_lb partA0_lb_ty = true := by native_decide

/-! ### The count layer for the swap -/

example : chkL count_acons_congr count_acons_congr_ty = true := by native_decide
example : chkL bump_comm bump_comm_ty = true := by native_decide
example : chkL count_swapA count_swapA_ty = true := by native_decide

-- There IS no η at length zero, which is why the nil lemmas exist at all: `SortedA Z`
-- of an opaque payload is a stuck `arrRec`, not `Unit`.
example : (Val.nfV 2000 (Val.Term.toValPure pure{ SortedA Z Arr() }) == .const "Unit")
    = true := by native_decide

/-! ## (ii) `splitA` — the scan

    `splitA(p, t)` rearranges `*t` in place so that its first `k` elements are ≤ `p`
    and the rest are ≥ `p`, and returns `k` with the right part's length.

    THE PROGRAM, and why it is this one. Peel the head, split the tail recursively, and
    then place the head:

      * head ≤ p — it belongs at the front, where it already is. NO WRITE.
      * head > p and the tail's left part is empty — it belongs at the back, and
        everything after it is already ≥ p. NO WRITE.
      * head > p with a non-empty left part `L` — the head must cross `L`. Swap it with
        `L`'s LAST element, which is ≤ p and lands at the front legitimately, while the
        head lands exactly at the new boundary. ONE swap, and the only one.

    Every element access is at index 0 of a segment the program carved, because there is
    no other kind: two independent symbolic indices into one array cannot both be
    reached (measured — after the first carve no evidence a program can hold selects a
    leaf for the second), so Lomuto's two-cursor scan is not writable and this shape is.
    ¶6's "the right sub-slice is a segment with its own zero" is a hard constraint here,
    not a convenience.

    PAIN DIARY — the staging tax, in its M23 form and for the M23 reason. `mkC` exists
    because the count conjunct must name the tail AS IT WAS AT ENTRY, and `*tl` denotes
    that only until the recursive call replaces it. Built while it is still live and
    applied afterwards. One builder, four arguments; M23's quicksort needed four
    builders. It would disappear under the filed `old`-for-consumed-things feature and
    does no mathematical work. -/

def splitA : Decl := decl{
  fn splitA [fuel] (fuel : Nat, m : Nat, hfuel : Le m fuel, p : Nat, t : &mut (Array m Nat))
      -> Σ (k : Nat) → Σ (r : Nat)
           → Σ (hlen : Id Nat m (add k r))
           → Σ (hsp : SplitA p k m (*t))
           → Π (q : Nat) → Id Nat (countA q m (*t)) (countA q m (old *t))
      { match m {
          -- Empty. NOT `unit`: there is no η at length zero, so `SplitA p Z Z σ` is a
          -- stuck `arrRec` and needs the nil lemma.
          Z => Pair(Z, Pair(Z, Pair(Refl,
                 Pair(splitA_nil p Z Z (*t) Refl, λ (q : Nat). Refl)))),
          S(m2) => match fuel {
            -- Out of fuel on a non-empty array: `hfuel : Le (S m2) Z` IS `Bot`.
            Z => botElim Unit hfuel,
            S(f2) => {
              -- The head peel. The residue is SUPPLIED (`; m2`) rather than minted:
              -- after `match m` the leaf's extent is the rigid `S m2`, and only the
              -- supplied form converts (`add 1 m2 ⇝ S m2`). The index place `t[Z]`
              -- has no residue slot and is rejected here for exactly that reason.
              let hd = &mut (*t)[Z ; 1 ; m2];
              let x = (*hd)[0];
              let tl = &mut (*t)[S Z ; ..];
              -- Staged while `*tl` still denotes the ENTRY tail: rewrite the exit into
              -- the pre-swap state (`hsw`), then move that across the recursive call's
              -- own count evidence (`hc`). Both non-swap branches pass `Refl` for the
              -- first leg.
              let mkC = (λ (t2 : Array m2 Nat).
                  λ (hc : Π (q : Nat) → Id Nat (countA q m2 t2) (countA q m2 (*tl))).
                  λ (a2 : Array (S m2) Nat).
                  λ (hsw : Π (q : Nat) →
                        Id Nat (countA q (S m2) a2) (countA q (S m2) (acons m2 x t2))).
                    λ (q : Nat).
                      id_trans Nat (countA q (S m2) a2)
                                   (countA q (S m2) (acons m2 x t2))
                                   (countA q (S m2) (acons m2 x (*tl)))
                        (hsw q) (count_acons_congr q x m2 t2 (*tl) (hc q)));
              let res = splitA(f2, m2, hfuel, p, &mut *tl);
              match res { Pair(k2, z1) => match z1 { Pair(r2, z2) => match z2 { Pair(hlen2, z3) =>
              match z3 { Pair(hsp2, hcnt2) => {
                if e : leb x p {
                  -- x ≤ p: the head is already in the left part; the boundary moves up.
                  Pair(S k2, Pair(r2,
                    Pair(id_congr Nat Nat (λ (z : Nat). S z) m2 (add k2 r2) hlen2,
                    Pair(Pair(leb_true_le x p e, hsp2),
                         mkC (*tl) hcnt2 (acons m2 x (*tl)) (λ (q : Nat). Refl)))))
                } else {
                  match k2 {
                    -- x > p with nothing to its left: the whole array is ≥ p already.
                    Z => Pair(Z, Pair(S r2,
                           Pair(id_congr Nat Nat (λ (z : Nat). S z) m2 (add Z r2) hlen2,
                           Pair(Pair(le_pred_l p x (leb_false_gt x p e), hsp2),
                                mkC (*tl) hcnt2 (acons m2 x (*tl)) (λ (q : Nat). Refl))))),
                    -- x > p with a non-empty left part: THE SWAP. Three carves put the
                    -- left part, the boundary cell and the right part in three segments,
                    -- and the exchange is two writes at index 0 of two of them.
                    S(k3) => {
                      let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2)];
                      let mid = &mut (*tl)[k3 ; 1 ; r2];
                      let hi = &mut (*tl)[S k3 ; ..];
                      let y = (*mid)[0];
                      (*mid)[0] := x;
                      (*hd)[0] := y;
                      let hrest = splitA_cat_rest p k3 (S r2) (*lo) (acons r2 y (*hi)) hsp2;
                      let hy = splitA1_head p r2 (*hi) y hrest;
                      let hub = splitA_cat_ub p k3 (S r2) (*lo) (acons r2 y (*hi)) hsp2;
                      let hg = splitA1_tail p r2 (*hi) y hrest;
                      let hnew = splitA_cat_i0 p k3 (S r2) (*lo) (acons r2 x (*hi)) hub
                                   (Pair(le_pred_l p x (leb_false_gt x p e), hg));
                      let cnt = mkC (arrCat k3 (S r2) (*lo) (acons r2 y (*hi))) hcnt2
                                    (acons m2 y (arrCat k3 (S r2) (*lo) (acons r2 x (*hi))))
                                    (λ (q : Nat). count_swapA q x y k3 (*lo) r2 (*hi));
                      Pair(S k3, Pair(S r2, Pair(Refl, Pair(Pair(hy, hnew), cnt))))
                    }
                  }
                }
              } } } } }
            }
          }
        } } }
example : checkFnOk splitA = true := by native_decide

end Dllbc.Tests.S25ArrSort
