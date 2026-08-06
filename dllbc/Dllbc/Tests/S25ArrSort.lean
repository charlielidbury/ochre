import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.StdLemmas
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S23Direct
import Dllbc.Migrate

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
  partA0_eq partA0_eq_ty partA0_lb partA0_lb_ty s_inj)

namespace Dllbc.Tests.S25ArrSort

/-- Type-check a closed term against a closed type in the pure seed (as §23/§24). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasType 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)

def progMsg (d : FnDef) (tbl : List FnDef := [d]) : String :=
  match FnMacro.progOf (Migrate.cohort tbl d) .unit with
  | .error e => "ELAB: " ++ e
  | .ok t => match checkProgram t with | .ok _ => "OK" | .error e => e

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

def splitA : FnDef := decl{
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
              let tl = &mut (*t)[S Z ; m2];
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
                      -- The decomposition is DECLARED: premise (3) may not refine
                      -- `m2` by unification, so the equation the recursive call
                      -- returned is cited and solved along. `add_succ` is the whole
                      -- distance between what the callee proved and what the carve
                      -- asks for.
                      let hdec = id_trans Nat m2 (S (add k3 r2)) (add k3 (S r2)) hlen2
                                   (id_sym Nat (add k3 (S r2)) (S (add k3 r2))
                                      (add_succ k3 r2));
                      let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2) | hdec];
                      let mid = &mut (*tl)[k3 ; 1 ; r2];
                      let hi = &mut (*tl)[S k3 ; r2];
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
example : Migrate.progOkOf splitA = true := by native_decide

/-! ## (iii) `partitionA` — the leaf ¶6's ledger counts as surviving, and G4 says is new

    `partitionA(a)` picks `a[0]` as the pivot, splits the tail around it, and swaps the
    pivot into its final position — returning that position, the right part's length,
    and `PartA`.

    IT IS NOT RECURSIVE, and it exists as a separate declaration for a reason that is
    the lane's sharpest structural finding: **the function boundary is load-bearing.**
    A body that has matched its own length `n` to `S m2` — which the head peel requires,
    since only `(*a)[Z ; 1 ; m2]` converts against the rigid extent — can no longer
    carve at a symbolic offset, because T2's rigid-length restriction now applies to
    the whole array. So the sort cannot both select a pivot and carve at the returned
    index. §6.2's opacity is the way out: a call re-mints the caller's payload as a
    FRESH σ at the declared type, so the array comes back UNCARVED and with a FLEX
    length — exactly the state the three-way carve needs. ¶5 advises "carve inline;
    reach for the function only when you want the abstraction boundary". Here the
    boundary is what makes the program possible at all. -/

def partitionA : FnDef := decl{
  fn partitionA (fuel : Nat, n : Nat, hfuel : Le n fuel, hne : Le (S Z) n,
                 a : &mut (Array n Nat))
      -> Σ (pvv : Nat) → Σ (k : Nat) → Σ (jj : Nat)
           → Σ (hlen : Id Nat n (add k (S jj)))
           → Σ (hp : PartA pvv k n (*a))
           → Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a))
      { match n {
          -- An empty array has no pivot, so the caller owes `Le 1 n`; here it IS `Bot`.
          Z => botElim Unit hne,
          S(m2) => {
            let hd = &mut (*a)[Z ; 1 ; m2];
            let x = (*hd)[0];
            let tl = &mut (*a)[S Z ; m2];
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
            let res = splitA(fuel, m2, le_pred_l m2 fuel hfuel, x, &mut *tl);
            match res { Pair(k2, z1) => match z1 { Pair(r2, z2) => match z2 { Pair(hlen2, z3) =>
            match z3 { Pair(hsp2, hcnt2) => {
              match k2 {
                -- Nothing is ≤ the pivot, so the pivot is already in its final place at
                -- index 0. `PartA`'s identity conjunct is `Refl` and its lower bound is
                -- the split's own invariant, crossed by `splitA0_lb`.
                Z => Pair(x, Pair(Z, Pair(m2,
                       Pair(Refl,
                       Pair(Pair(Refl, splitA0_lb x m2 (*tl) hsp2),
                            mkC (*tl) hcnt2 (acons m2 x (*tl)) (λ (q : Nat). Refl)))))),
                -- The pivot must cross the left part: swap it with that part's LAST
                -- element. The displaced element is ≤ the pivot, so it may sit at the
                -- front; the pivot lands at index `S k3`, which is the boundary.
                S(k3) => {
                  let hdec = id_trans Nat m2 (S (add k3 r2)) (add k3 (S r2)) hlen2
                               (id_sym Nat (add k3 (S r2)) (S (add k3 r2))
                                  (add_succ k3 r2));
                  let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2) | hdec];
                  let mid = &mut (*tl)[k3 ; 1 ; r2];
                  let hi = &mut (*tl)[S k3 ; r2];
                  let y = (*mid)[0];
                  (*mid)[0] := x;
                  (*hd)[0] := y;
                  let hrest = splitA_cat_rest x k3 (S r2) (*lo) (acons r2 y (*hi)) hsp2;
                  let hy = splitA1_head x r2 (*hi) y hrest;
                  let hub = splitA_cat_ub x k3 (S r2) (*lo) (acons r2 y (*hi)) hsp2;
                  let hg = splitA1_tail x r2 (*hi) y hrest;
                  let hnew = partA_cat_i0 x k3 (S r2) (*lo) (acons r2 x (*hi)) hub
                               (Pair(Refl, splitA0_lb x r2 (*hi) hg));
                  let cnt = mkC (arrCat k3 (S r2) (*lo) (acons r2 y (*hi))) hcnt2
                                (acons m2 y (arrCat k3 (S r2) (*lo) (acons r2 x (*hi))))
                                (λ (q : Nat). count_swapA q x y k3 (*lo) r2 (*hi));
                  Pair(x, Pair(S k3, Pair(r2, Pair(Refl, Pair(Pair(hy, hnew), cnt)))))
                }
              }
            } } } } }
          }
        } } }
example : Migrate.progOkOf partitionA [partitionA, splitA] = true := by native_decide

/-! ## (iv) `quicksortA` — the headline

        fn quicksortA [fuel] (fuel : Nat, n : Nat, hfuel : Le n fuel, a : &mut (Array n Nat))
          -> Σ (hs : SortedA n (*a)) → Π x. Id Nat (countA x n (*a)) (countA x n (old *a))

    M23's quicksort signature, re-posed on arrays: sorted AND a permutation, over the
    exit snapshot, IN PLACE, with zero declared backs in the call tree. `partitionA`,
    `splitA` and the two recursive calls are each described only by their return type.

    EMPTINESS IS TESTED WITH `leb 1 n`, NOT BY MATCHING `n`, and that is forced twice
    over. Matching would refine the length to `S m2`, and T2's rigid-extent restriction
    then blocks the three-way carve outright ("premise (3) is stuck"). And the `Z` branch
    could not be discharged anyway: there is no η at length zero, so `SortedA Z σ` is a
    stuck `arrRec` rather than `Unit`. The False branch instead turns `Le n Z` into
    `Id Nat n Z` (`le_zero_eq`) and feeds `sortedA_nil`.

    THE ONE STRUCTURAL FACT beyond composition is M23's, unchanged: BOUND SURVIVAL.
    `sorted_arrCat` wants `UbA pv` of the SORTED left part, and the partition bounded it
    before the sort. `ub_permA`/`lb_permA` carry both bounds across their sorts' own
    count evidence. That is the keystone, transferred with the container in M24-ix, and
    it is the only place this proof is more than gluing.

    PAIN DIARY — three staged builders, and the reason is M23's exactly. `mkTop` is built
    BEFORE the partition call, because the count conjunct's far endpoint is `old *a` and a
    body cannot write that; capturing `*a` while it still IS the entry value is the dodge.
    `mkAD` and `mkS` are built after the carve and before the sorts, because both name the
    sub-slices AS THEY WERE when the partition bounded them, and the recursive calls
    replace those values. M23's list quicksort needed four builders for the same reason.
    Sixth filing for `old`-on-consumed-things; none of the three does mathematical work. -/

def quicksortA : FnDef := decl{
  fn quicksortA [fuel] (fuel : Nat, n : Nat, hfuel : Le n fuel, a : &mut (Array n Nat))
      -> Σ (hs : SortedA n (*a))
           → Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a))
      { if he : leb 1 n {
          match fuel {
            -- `Le 1 n` and `Le n Z` compose to `Le 1 Z`, which IS `Bot`.
            Z => botElim Unit (le_trans (S Z) n Z (leb_true_le 1 n he) hfuel),
            S(f2) => {
              -- Staged while `*a` still denotes the ENTRY array: the count chain's far
              -- endpoint is `old *a`, which no body term can name.
              let mkTop = (λ (dv : Array n Nat).
                  λ (hd : Π (q : Nat) → Id Nat (countA q n dv) (countA q n (*a))).
                  λ (av : Array n Nat).
                  λ (had : Π (q : Nat) → Id Nat (countA q n av) (countA q n dv)).
                    λ (q : Nat).
                      id_trans Nat (countA q n av) (countA q n dv) (countA q n (*a))
                        (had q) (hd q));
              -- `hfuel` is a PROOF, so passing it to the partition MOVES it. Both
              -- sufficiency bounds are therefore staged over it first — the same
              -- capture-before-consume dodge M23 uses for a consumed `rest`.
              let mkHf = (λ (kv : Nat). λ (h : Le (S kv) n).
                            le_trans (S kv) n (S f2) h hfuel);
              let pr = partitionA(S(f2), n, hfuel, leb_true_le 1 n he, &mut *a);
              match pr { Pair(pvv, w1) => match w1 { Pair(k, w2) => match w2 { Pair(jj, w3) =>
              match w3 { Pair(hlen, w4) => match w4 { Pair(hp, hcnt) => {
                -- ¶6's three-way carve, at the index the partition just returned. The
                -- first obligation is `le_add`; the second is `Le 1 (S jj)`, which route
                -- (a) reduces to ⊤; the third is degenerate.
                let l = &mut (*a)[Z ; k ; S jj | le_add k (S jj) | hlen];
                let pcell = &mut (*a)[k ; 1 ; jj];
                let e = (*pcell)[0];
                let r = &mut (*a)[S k ; jj];
                let hub = partA_cat_ub pvv k (S jj) (*l) (acons jj e (*r)) hp;
                let hrest = partA_cat_rest pvv k (S jj) (*l) (acons jj e (*r)) hp;
                let heq = partA0_eq pvv jj (*r) e hrest;
                let hlb = partA0_lb pvv jj (*r) e hrest;
                let top1 = mkTop (arrCat k (S jj) (*l) (acons jj e (*r))) hcnt;
                -- The glue, staged: both bounds are about to be invalidated as VALUES by
                -- the recursive sorts, so their transports are set up now.
                let mkS = (λ (l2 : Array k Nat). λ (r2 : Array jj Nat).
                    λ (h1 : Π (q : Nat) → Id Nat (countA q k l2) (countA q k (*l))).
                    λ (h2 : Π (q : Nat) → Id Nat (countA q jj r2) (countA q jj (*r))).
                    λ (hs1 : SortedA k l2). λ (hs2 : SortedA jj r2).
                      nat_rw (λ (z : Nat). SortedA (add k (S jj))
                                  (arrCat k (S jj) l2 (arrCat 1 jj (asingle z) r2)))
                        pvv e (id_sym Nat e pvv heq)
                        (sorted_arrCat pvv k l2 jj r2 hs1
                           (ub_permA pvv k l2 k (*l) h1 hub) hs2
                           (lb_permA pvv jj r2 jj (*r) h2 hlb)));
                let mkAD = (λ (l2 : Array k Nat). λ (r2 : Array jj Nat).
                    λ (h1 : Π (q : Nat) → Id Nat (countA q k l2) (countA q k (*l))).
                    λ (h2 : Π (q : Nat) → Id Nat (countA q jj r2) (countA q jj (*r))).
                      λ (q : Nat).
                        id_trans Nat
                          (countA q (add k (S jj)) (arrCat k (S jj) l2 (acons jj e r2)))
                          (add (countA q k (*l)) (countA q (S jj) (acons jj e (*r))))
                          (countA q (add k (S jj)) (arrCat k (S jj) (*l) (acons jj e (*r))))
                          (id_trans Nat
                            (countA q (add k (S jj)) (arrCat k (S jj) l2 (acons jj e r2)))
                            (add (countA q k l2) (countA q (S jj) (acons jj e r2)))
                            (add (countA q k (*l)) (countA q (S jj) (acons jj e (*r))))
                            (count_arrCat q k l2 (S jj) (acons jj e r2))
                            (id_trans Nat
                              (add (countA q k l2) (countA q (S jj) (acons jj e r2)))
                              (add (countA q k (*l)) (countA q (S jj) (acons jj e r2)))
                              (add (countA q k (*l)) (countA q (S jj) (acons jj e (*r))))
                              (id_congr Nat Nat
                                (λ (c : Nat). add c (countA q (S jj) (acons jj e r2)))
                                (countA q k l2) (countA q k (*l)) (h1 q))
                              (id_congr Nat Nat
                                (λ (c : Nat). add (countA q k (*l)) c)
                                (countA q (S jj) (acons jj e r2))
                                (countA q (S jj) (acons jj e (*r)))
                                (count_acons_congr q e jj r2 (*r) (h2 q)))))
                          (id_sym Nat
                            (countA q (add k (S jj)) (arrCat k (S jj) (*l) (acons jj e (*r))))
                            (add (countA q k (*l)) (countA q (S jj) (acons jj e (*r))))
                            (count_arrCat q k (*l) (S jj) (acons jj e (*r)))));
                -- Sufficiency: the pivot sits strictly inside, so both halves are
                -- strictly shorter. `le_add_succ` and `le_add_l` are the two sides of
                -- that, and each composes with this frame's own bound.
                let hf1 = mkHf k (le_add_succ k jj);
                let s1 = quicksortA(f2, k, hf1, &mut *l);
                match s1 { Pair(hs1, hc1) => {
                  let hf2 = mkHf jj (le_add_l (S jj) k);
                  let s2 = quicksortA(f2, jj, hf2, &mut *r);
                  match s2 { Pair(hs2, hc2) => {
                    Pair(mkS (*l) (*r) hc1 hc2 hs1 hs2,
                         top1 (arrCat k (S jj) (*l) (acons jj e (*r))) (mkAD (*l) (*r) hc1 hc2))
                  } }
                } }
              } } } } } }
            }
          }
        } else {
          -- `n` is zero: the array is empty, and BOTH conjuncts are about an opaque
          -- payload, so the count is `Refl` and the sortedness is the nil lemma.
          Pair(sortedA_nil n (*a) (le_zero_eq n (leb_false_gt (S Z) n he)),
               λ (q : Nat). Refl)
        } } }
example : Migrate.progOkOf quicksortA [quicksortA, partitionA, splitA] = true := by native_decide

def arrTbl : List FnDef := [quicksortA, partitionA, splitA]

/-! ## (v) Not vacuous — a lying twin per conjunct

    Each return type is the ONLY description of its function, so each conjunct gets a
    twin that changes exactly it, built by taking the `retType` off a lying header with
    the same telescope so the body is shared verbatim and the lie is the only variable.
    M23's discipline, applied to three declarations. -/

-- `splitA`, conjunct 1: the length accounting says the two parts overlap by one.
def splitALieLen : FnDef :=
  { splitA with retType := (decl{
      fn splitALieLen (fuel : Nat, m : Nat, hfuel : Le m fuel, p : Nat, t : &mut (Array m Nat))
        -> Σ (k : Nat) → Σ (r : Nat)
             → Σ (hlen : Id Nat m (add k (S r)))
             → Σ (hsp : SplitA p k m (*t))
             → Π (q : Nat) → Id Nat (countA q m (*t)) (countA q m (old *t))
        { () } }).retType }
example : Migrate.progOkOf splitALieLen = false := by native_decide

-- `splitA`, conjunct 2: the ordering claimed of the ENTRY array rather than the exit.
def splitALieSp : FnDef :=
  { splitA with retType := (decl{
      fn splitALieSp (fuel : Nat, m : Nat, hfuel : Le m fuel, p : Nat, t : &mut (Array m Nat))
        -> Σ (k : Nat) → Σ (r : Nat)
             → Σ (hlen : Id Nat m (add k r))
             → Σ (hsp : SplitA p k m (old *t))
             → Π (q : Nat) → Id Nat (countA q m (*t)) (countA q m (old *t))
        { () } }).retType }
example : Migrate.progOkOf splitALieSp = false := by native_decide

-- `splitA`, conjunct 3: the counts off by one, which no path can reach.
def splitALieCount : FnDef :=
  { splitA with retType := (decl{
      fn splitALieCount (fuel : Nat, m : Nat, hfuel : Le m fuel, p : Nat, t : &mut (Array m Nat))
        -> Σ (k : Nat) → Σ (r : Nat)
             → Σ (hlen : Id Nat m (add k r))
             → Σ (hsp : SplitA p k m (*t))
             → Π (q : Nat) → Id Nat (countA q m (*t)) (S (countA q m (old *t)))
        { () } }).retType }
example : Migrate.progOkOf splitALieCount = false := by native_decide

/-- **The BODY twin, and the one that matters most**: the swap is DELETED — the branch
    reads the two cells and writes neither, but claims the same postcondition. Every
    spec twin above can be blamed on some path; this one is wrong only on the swap
    path and only because the elements did not move. It isolates the single mutation
    the whole program performs. -/
def splitANoSwap : FnDef :=
  decl{ fn splitANoSwap [fuel]
          (fuel : Nat, m : Nat, hfuel : Le m fuel, p : Nat, t : &mut (Array m Nat))
      -> Σ (k : Nat) → Σ (r : Nat)
           → Σ (hlen : Id Nat m (add k r))
           → Σ (hsp : SplitA p k m (*t))
           → Π (q : Nat) → Id Nat (countA q m (*t)) (countA q m (old *t))
      { match m {
          Z => Pair(Z, Pair(Z, Pair(Refl,
                 Pair(splitA_nil p Z Z (*t) Refl, λ (q : Nat). Refl)))),
          S(m2) => match fuel {
            Z => botElim Unit hfuel,
            S(f2) => {
              let hd = &mut (*t)[Z ; 1 ; m2];
              let x = (*hd)[0];
              let tl = &mut (*t)[S Z ; m2];
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
              let res = splitANoSwap(f2, m2, hfuel, p, &mut *tl);
              match res { Pair(k2, z1) => match z1 { Pair(r2, z2) => match z2 { Pair(hlen2, z3) =>
              match z3 { Pair(hsp2, hcnt2) => {
                if e : leb x p {
                  Pair(S k2, Pair(r2,
                    Pair(id_congr Nat Nat (λ (z : Nat). S z) m2 (add k2 r2) hlen2,
                    Pair(Pair(leb_true_le x p e, hsp2),
                         mkC (*tl) hcnt2 (acons m2 x (*tl)) (λ (q : Nat). Refl)))))
                } else {
                  match k2 {
                    Z => Pair(Z, Pair(S r2,
                           Pair(id_congr Nat Nat (λ (z : Nat). S z) m2 (add Z r2) hlen2,
                           Pair(Pair(le_pred_l p x (leb_false_gt x p e), hsp2),
                                mkC (*tl) hcnt2 (acons m2 x (*tl)) (λ (q : Nat). Refl))))),
                    S(k3) => {
                      -- The decomposition is DECLARED: premise (3) may not refine
                      -- `m2` by unification, so the equation the recursive call
                      -- returned is cited and solved along. `add_succ` is the whole
                      -- distance between what the callee proved and what the carve
                      -- asks for.
                      let hdec = id_trans Nat m2 (S (add k3 r2)) (add k3 (S r2)) hlen2
                                   (id_sym Nat (add k3 (S r2)) (S (add k3 r2))
                                      (add_succ k3 r2));
                      let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2) | hdec];
                      let mid = &mut (*tl)[k3 ; 1 ; r2];
                      let hi = &mut (*tl)[S k3 ; r2];
                      let y = (*mid)[0];
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
example : Migrate.progOkOf splitANoSwap = false := by native_decide

-- `partitionA`, conjunct 1: the length accounting forgets the pivot cell.
def partALieLen : FnDef :=
  { partitionA with retType := (decl{
      fn partALieLen (fuel : Nat, n : Nat, hfuel : Le n fuel, hne : Le (S Z) n,
                      a : &mut (Array n Nat))
        -> Σ (pvv : Nat) → Σ (k : Nat) → Σ (jj : Nat)
             → Σ (hlen : Id Nat n (add k jj))
             → Σ (hp : PartA pvv k n (*a))
             → Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a))
        { () } }).retType }
example : Migrate.progRejectsOf partALieLen "does not have return type" [partALieLen, splitA]
    = true := by native_decide

-- `partitionA`, conjunct 2: the partition claimed of the ENTRY array.
def partALiePart : FnDef :=
  { partitionA with retType := (decl{
      fn partALiePart (fuel : Nat, n : Nat, hfuel : Le n fuel, hne : Le (S Z) n,
                       a : &mut (Array n Nat))
        -> Σ (pvv : Nat) → Σ (k : Nat) → Σ (jj : Nat)
             → Σ (hlen : Id Nat n (add k (S jj)))
             → Σ (hp : PartA pvv k n (old *a))
             → Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a))
        { () } }).retType }
example : Migrate.progRejectsOf partALiePart "does not have return type" [partALiePart, splitA]
    = true := by native_decide

-- `quicksortA`, conjunct 1: sortedness lied onto the ENTRY. True at the empty array,
-- so the base path still passes and only the recursive one is blamed.
def qsALieSorted : FnDef :=
  { quicksortA with retType := (decl{
      fn qsALieSorted (fuel : Nat, n : Nat, hfuel : Le n fuel, a : &mut (Array n Nat))
        -> Σ (hs : SortedA n (old *a))
             → Π (q : Nat) → Id Nat (countA q n (*a)) (countA q n (old *a))
        { () } }).retType }
example : Migrate.progRejectsOf qsALieSorted "does not have return type" [qsALieSorted, partitionA, splitA]
    = true := by native_decide

-- `quicksortA`, conjunct 2: the permutation lied by DIRECTION. Again `Refl` at the
-- empty array, and again the body's evidence points the other way once anything moves.
def qsALieCount : FnDef :=
  { quicksortA with retType := (decl{
      fn qsALieCount (fuel : Nat, n : Nat, hfuel : Le n fuel, a : &mut (Array n Nat))
        -> Σ (hs : SortedA n (*a))
             → Π (q : Nat) → Id Nat (countA q n (old *a)) (countA q n (*a))
        { () } }).retType }
example : Migrate.progRejectsOf qsALieCount "does not have return type" [qsALieCount, partitionA, splitA]
    = true := by native_decide

/-! ### Honest typing rejections, probed through `checkFn` -/

-- The three-way carve's ONE cited obligation is load-bearing: drop `le_add` and the
-- carve has nothing to select a leaf with. (The pivot carve needs no evidence at all —
-- route (a) reduces `Le 1 (S jj)` to ⊤ — so this is the only citation in the body.)
def carveNoEv : Term := prog{
  fn carveNoEv (n : Nat, k : Nat, jj : Nat, heq : Id Nat n (add k (S jj)),
                a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; k ; S jj];
    let pcell = &mut (*a)[k ; 1 ; jj];
    let r = &mut (*a)[S k ; ..];
    () };
  () }
example : progRejects carveNoEv "may not impose it by refining" = true := by native_decide

-- …and the positive control at the same shape, so the rejection is about the missing
-- citation and not about the carve. (`quicksortA` itself is the other positive control.)
def carveWithEv : Term := prog{
  fn carveWithEv (n : Nat, k : Nat, jj : Nat, heq : Id Nat n (add k (S jj)),
                  a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; k ; S jj | le_add k (S jj) | heq];
    let pcell = &mut (*a)[k ; 1 ; jj];
    let r = &mut (*a)[S k ; ..];
    () };
  () }
example : progOk carveWithEv = true := by native_decide

-- The sufficiency hypothesis is load-bearing, not decoration: keep the parameter (so
-- the body still elaborates and the rejection is about TYPING) and weaken it to `Unit`.
-- The out-of-fuel path then has no ⊥ to eliminate and stops being dead.
def qsANoSuff : FnDef :=
  { quicksortA with telescope := (decl{
      fn qsANoSuff (fuel : Nat, n : Nat, hfuel : Unit, a : &mut (Array n Nat)) -> Unit
        { () } }).telescope }
example : Migrate.progRejectsOf qsANoSuff "botElim" [qsANoSuff, partitionA, splitA]
    = true := by native_decide


/-! ## (vi) The EXECUTING differential — and the divergence it found

    `Migrate.progOkOf` proves `Sorted ∧ Perm` symbolically. Running the SAME declarations on
    concrete arrays is the control that can still indict them, and here it indicts the
    MACHINE instead: the concrete and symbolic executions of a carving callee diverge,
    for a reason no symbolic check can produce. Everything below is stated so that the
    day the gap closes, this section goes red and has to be updated.

    THE GAP, minimally: **a callee's segment borrows are never released when it
    returns**, so in executing mode the caller's array stays carved with the callee's
    dead markers. `mergeArrays` cannot rejoin it (a loan blocks the merge, ledger R4),
    so the caller's next carve sees the callee's leftover segmentation instead of one
    leaf, and premise (3) tries to unify the wrong extent.

    In CHECKING mode this is invisible, and invisible for a principled reason: §6.2's
    opacity re-mints the callee's payload as a fresh σ at the declared type, so the
    caller always sees an UNCARVED array. That re-minting is not merely an
    approximation of what the concrete machine does — it is a REPAIR of it. This is a
    new instance of the over-approximation §6.1 already flags ("a group releases
    atomically where the concrete machine ends lazily"), and it is the first one where
    the concrete side is the one that is wrong. -/

def tnatT : Nat → Term | 0 => .ctorApp "Z" [] | k + 1 => .ctorApp "S" [tnatT k]
def tarrT (l : List Nat) : Term := .ctorApp "Arr" (l.map tnatT)

def natOfV : Nat → Val → Option Nat
  | _, .ctor "Z" [] => some 0
  | (f + 1), .ctor "S" [v] => (natOfV f v).map (· + 1)
  | _, _ => none

def listOfV : Nat → Val → Option (List Nat)
  | _, .ctor "Nil" [] => some []
  | (f + 1), .ctor "Cons" [h, t] =>
    match natOfV 2000 h, listOfV f t with
    | some x, some xs => some (x :: xs)
    | _, _ => none
  | _, _ => none

def arrOfV : Val → Option (List Nat)
  | .ctor "Arr" vs => vs.mapM (natOfV 2000)
  | _ => none

/-- Build the array, borrow it, sort it in place, read it back. `hfuel` is `Le n n`,
    which computes to `Unit` at a concrete length. -/
def qsCallerA (l : List Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tarrT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "quicksortA" [tnatT l.length, tnatT l.length, .unit, .var ⟨1, "b"⟩])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))

/-- `splitA` alone, so the divergence can be exhibited one call deep instead of three. -/
def splCaller (l : List Nat) (pvt : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tarrT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.letIn ⟨2, "r"⟩ (.call "splitA"
          [tnatT l.length, tnatT l.length, .unit, tnatT pvt, .var ⟨1, "b"⟩])
        (.letIn ⟨3, "y"⟩ (.var ⟨0, "z"⟩) .unit)))

def runQsA (l : List Nat) : Option (List Nat) :=
  match Dllbc.Tests.S9Diff.runExec arrTbl (qsCallerA l) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

def runSplA (l : List Nat) (pvt : Nat) : Option (List Nat) :=
  match Dllbc.Tests.S9Diff.runExec [splitA] (splCaller l pvt) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

def sortedRef (l : List Nat) : List Nat := l.mergeSort (fun a b => a <= b)

/-- Did it run at all — used by the G7 probes below, where the point is acceptance and
    execution agreeing rather than the value. -/
def runsAtAll (tbl : List FnDef) (t : Term) : Bool :=
  match Dllbc.Tests.S9Diff.runExec tbl t with | .ok _ => true | .error _ => false

/-! ### (vi.a) It really sorts, in place, on concrete arrays

    The same declarations `Migrate.progOkOf` verified symbolically, run on real inputs and
    compared against a trusted sort. Duplicates, already-sorted and reverse-sorted
    included, since the empty-part paths are where a partition-based sort breaks. -/

/-! ### (vi.a) What DOES run, and it is not nothing

    Every execution that does not re-enter a carve after returning from a carving callee
    is correct — the programs really do move elements, in place, to the right places. -/

-- `splitA` on two elements: the pivot-crossing SWAP branch, EXECUTING. `[3,1]` at
-- `p = 2` must come back `[1,3]` — the head crossed the boundary and the boundary
-- element crossed back, which is the program's one mutation.
example : runSplA [3, 1] 2 == some [1, 3] := by native_decide
-- …and both no-write branches.
example : runSplA [1, 3] 2 == some [1, 3] := by native_decide
example : runSplA [1] 2 == some [1] := by native_decide
example : runSplA [3] 2 == some [3] := by native_decide
example : runSplA [] 2 == some [] := by native_decide

-- `quicksortA`, executing, at the sizes that do not re-enter a carve after a call.
example : runQsA [] == some (sortedRef []) := by native_decide
example : runQsA [1] == some (sortedRef [1]) := by native_decide

/-! ### (vi.b) G5 CLOSED — the executing differential, deep

    The divergence this section used to pin is gone. It was `drop-empty`, in THREE
    independent sites, and the ledger's G5 entry records each; the last of them is that a
    ZERO-WIDTH request must not select the leaf it abuts, because `Le (add lo Z) (add b m)`
    holds at a leaf's far end and the ordinary selection then demand-ends the live borrow
    pinned there. All three are unreachable symbolically — a residue σ is never known to be
    zero — and routine concretely, which is exactly why only an executing differential
    could find them and why the checking side was right all along.

    What used to be `runsAtAll … = false` is now the real thing. -/

example : runQsA [2, 1] == some (sortedRef [2, 1]) := by native_decide
example : runQsA [3, 1, 2] == some (sortedRef [3, 1, 2]) := by native_decide
example : runQsA [1, 2, 3] == some (sortedRef [1, 2, 3]) := by native_decide
example : runQsA [3, 2, 1] == some (sortedRef [3, 2, 1]) := by native_decide
example : runQsA [5, 5, 5] == some (sortedRef [5, 5, 5]) := by native_decide
example : runQsA [4, 1, 3, 2, 5] == some (sortedRef [4, 1, 3, 2, 5]) := by native_decide
example : runQsA [3, 1, 4, 1, 5, 9, 2] == some (sortedRef [3, 1, 4, 1, 5, 9, 2]) := by
  native_decide
example : runQsA [9, 8, 7, 6, 5, 4, 3, 2, 1] == some (sortedRef [9, 8, 7, 6, 5, 4, 3, 2, 1])
    := by native_decide

-- The leaf on its own, both branches and the pivot-crossing SWAP.
example : runSplA [3, 1] 2 == some [1, 3] := by native_decide
example : runSplA [1, 3] 2 == some [1, 3] := by native_decide
example : runSplA [3, 1, 4] 2 == some [1, 3, 4] := by native_decide
-- Order WITHIN each part is unspecified; the split point is what is claimed.
example : runSplA [4, 1, 3, 2] 2 == some [2, 1, 4, 3] := by native_decide
example : runSplA [] 2 == some [] := by native_decide

/-! ### (vi.c) THE CROSS-DIFFERENTIAL — wired, and green as far as it runs

    M23's `quicksort` is a relational take-and-rebuild over a LINKED LIST returning two
    lists by value; `quicksortA` is an in-place scan over an ARRAY returning an index.
    They share no code — not the program, not the predicates, not the partition, not the
    container — and they were written against the same postcondition. Comparing them
    elementwise is the control that catches a wrong SHARED reading of the spec, which
    neither type checker would see.

    It is set up here in full and asserted on the inputs the array side can execute. The
    remaining inputs are one bug away, and the moment the pinned tests above flip this
    becomes the lane's real acceptance. -/

def listTbl : List FnDef :=
  [Dllbc.Tests.S23Direct.partition, Dllbc.Tests.S23Direct.appendBack,
   Dllbc.Tests.S23Direct.quicksort]

def runQsL (l : List Nat) : Option (List Nat) :=
  match Dllbc.Tests.S9Diff.runExec listTbl (Dllbc.Tests.S23Direct.qsCaller l) with
  | .ok env => (env.lookup "y").bind (listOfV 2000)
  | .error _ => none

/-- Both implementations agree with each other AND with the trusted sort. One
    conjunction, so a two-way agreement on a wrong answer still goes red. -/
def cross (l : List Nat) : Bool :=
  match runQsL l, runQsA l with
  | some a, some b => a == b && a == sortedRef l
  | _, _ => false

example : (([[], [1], [2,1], [3,1,2], [1,2,3], [3,2,1], [5,5,5], [4,1,3,2,5],
             [3,1,4,1,5,9,2], [2,2,1,1], [7,3,7,3,7]] : List (List Nat)).all cross)
    = true := by native_decide

-- `cross` is not vacuously true: a `none` from either side cannot masquerade as
-- agreement, and a disagreement or a wrong answer is `false`.
example : cross [2, 1] = true := by native_decide
example : (match runQsA [2, 1] with | some a => a == [2, 1] | none => false) = false := by
  native_decide

/-! ### (vi.c) M9's simulation property, over the array bodies that do run -/

def qsCallers : List Term := [qsCallerA [3, 1, 2], qsCallerA [2, 1], qsCallerA [1]]

example : qsCallers.all (fun b => progOk b (.const "Unit") arrTbl)
    = true := by native_decide

example : qsCallers.all (fun b => Dllbc.Tests.S9Diff.diffV2 arrTbl b)
    = true := by native_decide

/-! ## (vii) The five probes that located C6, kept as its regression

    §5.2's demand-end reaching the carve (ledger C6) was found by bisection, and the
    bisection is the test: four shapes that always worked, and the one that did not.
    Each is the smallest program exhibiting its shape. If the node-level collapse is
    removed from `carveAt`, only `c6CarveAfterCall` goes red — which is what makes this
    a live check on the rule rather than a comment claiming one. -/

def c6Touch : Term := prog{
  fn c6Touch (q : Nat, s : &mut (Array q Nat)) -> Unit { () };
  () }
-- A callee, declared in each chain that calls it; the standalone form
-- keeps the verdict `S26Migrate.p25` was computing for it.
example : progOk c6Touch = true := by native_decide

-- (1) Peel a head and hand the tail to a call. Always worked.
def c6PeelCall : Term := prog{
  fn c6Touch (q : Nat, s : &mut (Array q Nat)) -> Unit { () };
  fn c6PeelCall (n : Nat, a : &mut (Array n Nat)) -> Unit {
    match n { Z => (),
      S(m) => { let hd = &mut (*a)[Z ; 1 ; m]; let x = (*hd)[0];
                let tl = &mut (*a)[S Z ; m]; c6Touch(m, &mut *tl); () } } };
  () }
example : progOk c6PeelCall = true := by native_decide

-- (2) Carve inside the tail, with NO call first. Always worked.
def c6CarveNoCall : Term := prog{
  fn c6CarveNoCall (n : Nat, k3 : Nat, r2 : Nat, hq : Id Nat n (S (add k3 (S r2))),
             a : &mut (Array n Nat)) -> Unit {
    match n { Z => (),
      S(m) => { let hd = &mut (*a)[Z ; 1 ; m]; let x = (*hd)[0];
                let tl = &mut (*a)[S Z ; m];
                let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2)
                                      | s_inj m (add k3 (S r2)) hq];
                let mid = &mut (*tl)[k3 ; 1 ; r2];
                let hi = &mut (*tl)[S k3 ; r2]; () } } };
  () }
example : progOk c6CarveNoCall = true := by native_decide

-- (3) …and the swap's writes on top of it. Always worked.
def c6Swap : Term := prog{
  fn c6Swap (n : Nat, k3 : Nat, r2 : Nat, hq : Id Nat n (S (add k3 (S r2))),
             a : &mut (Array n Nat)) -> Unit {
    match n { Z => (),
      S(m) => { let hd = &mut (*a)[Z ; 1 ; m]; let x = (*hd)[0];
                let tl = &mut (*a)[S Z ; m];
                let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2)
                                      | s_inj m (add k3 (S r2)) hq];
                let mid = &mut (*tl)[k3 ; 1 ; r2];
                let hi = &mut (*tl)[S k3 ; r2];
                let y = (*mid)[0]; (*mid)[0] := x; (*hd)[0] := y; () } } };
  () }
example : progOk c6Swap = true := by native_decide

-- (4) Self-recursion through a reborrowed tail. Always worked.
def c6Rec : Term := prog{
  fn c6Rec [fuel] (fuel : Nat, m : Nat, hfuel : Le m fuel, a : &mut (Array m Nat)) -> Unit {
    match m { Z => (),
      S(m2) => match fuel { Z => botElim Unit hfuel,
        S(f2) => { let hd = &mut (*a)[Z ; 1 ; m2]; let x = (*hd)[0];
                   let tl = &mut (*a)[S Z ; m2]; c6Rec(f2, m2, hfuel, &mut *tl); () } } } };
  () }
example : progOk c6Rec = true := by native_decide

/-- (5) THE RED ONE, before C6: carve inside a borrow AFTER handing it to a call. The
    reborrow parks a marker at the whole payload, and the carve consulted the extent map
    without collapsing it first — "`loanₘ ℓ` is not an array value (no extent to read)".
    Which is to say: a recursive array program carving the argument it just handed to
    its recursive call, i.e. every one of them. -/
def c6CarveAfterCall : Term := prog{
  fn c6Touch (q : Nat, s : &mut (Array q Nat)) -> Unit { () };
  fn c6CarveAfterCall (n : Nat, k3 : Nat, r2 : Nat, hq : Id Nat n (S (add k3 (S r2))),
             a : &mut (Array n Nat)) -> Unit {
    match n { Z => (),
      S(m) => { let hd = &mut (*a)[Z ; 1 ; m]; let x = (*hd)[0];
                let tl = &mut (*a)[S Z ; m];
                c6Touch(m, &mut *tl);
                let lo = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2)
                                      | s_inj m (add k3 (S r2)) hq];
                let mid = &mut (*tl)[k3 ; 1 ; r2];
                let hi = &mut (*tl)[S k3 ; r2]; () } } };
  () }
example : progOk c6CarveAfterCall = true := by native_decide

/-! ### Why the scan is not Lomuto — the rejection, with M13's evidence threaded

    Ledger R13. `(*a)[i | h]` on a symbolic array works; a SECOND index does not, and
    threading the ordering evidence does not rescue it. After the first carve the leaves
    are `[0,i)`, `[i,i+1)`, `[S i, rest)`, and the second request lands in the third — so
    premise (2) is formed LEAF-RELATIVELY against an offset `d` the machine minted while
    solving `j ≡ add (S i) d`. No program term has type `Le (S d) rest`, because `d` has
    no surface name. **That is G1's wall arriving at the OFFSET rather than the extent**,
    and route (a) closes only the extent half.

    So `swap(a[i], a[j])` at two runtime cursors is unwritable, and `splitA`'s shape —
    every access at index 0 of a segment the program carved — is forced rather than
    chosen. ¶6's "a segment with its own zero" is a constraint, not a convenience. -/

def twoCursor : Term := prog{
  fn twoCursor (n : Nat, i : Nat, j : Nat, pij : Le (S i) j, pjn : Le (S j) n,
                a : &mut (Array n Nat)) -> Unit {
    let x = (*a)[i | le_trans (S i) j n pij (le_pred_l j n pjn)];
    let y = (*a)[j | pjn];
    () };
  () }
example : progRejects twoCursor "no leaf" = true := by native_decide

-- Route (a) cannot rescue it either: the second request does not START a segment, so
-- there is no leaf for the supplied residue to decompose.
def twoCursorRes : Term := prog{
  fn twoCursorRes (n : Nat, i : Nat, j : Nat, r1 : Nat, r2 : Nat,
                   a : &mut (Array n Nat)) -> Unit {
    let x = &mut (*a)[i ; 1 ; r1 | le_add i (S r1)];
    let y = &mut (*a)[j ; 1 ; r2 | le_add j (S r2)];
    () };
  () }
example : progRejects twoCursorRes "no segment starts at" = true := by native_decide

/-! ## (viii) The G7 ruling, probed at the boundary it exists to protect

    Premise (3) may not refine a telescope parameter's σ to match a supplied residue;
    it may solve along a CITED equation. The three probes the ruling asks for. -/

def citedCarve : FnDef := decl{
  fn citedCarve (n : Nat, i : Nat, j : Nat, heq : Id Nat n (add i (S j)),
                 a : &mut (Array n Nat)) -> Unit {
    let l = &mut (*a)[Z ; i ; S j | le_add i (S j) | heq];
    () } }
example : Migrate.progOkOf citedCarve = true := by native_decide

/-- (1) A caller whose numbers are CONSISTENT: `n = 3, i = 1, j = 1`, and `Refl`
    inhabits `Id Nat 3 (add 1 (S 1))` because both sides compute to 3. -/
def citedCallerOk : Term := prog{
  let z = Arr(1, 2, 3); let b = &mut z; citedCarve(3, 1, 1, Refl, b); let y = z; () }
example : progOk citedCallerOk (.const "Unit") [citedCarve] = true := by native_decide

/-- (2) …and it RUNS, which is the half that was broken. Before the ruling the checker
    accepted callers the concrete machine got stuck on; now acceptance and execution
    agree on this shape, which is M8/M9's differential property restored for it. -/
example : runsAtAll [citedCarve] citedCallerOk = true := by native_decide

/-- (3) The caller that used to be the counterexample. `n = 2` with `i = j = 5` type-
    checked before the ruling and then got stuck executing; now `Refl` cannot inhabit
    `Id Nat 2 (add 5 (S 5))` and the CALLER is rejected, at its own boundary, with the
    constraint recorded in the signature it violated. -/
def citedCallerBad : Term := prog{
  let z = Arr(1, 2); let b = &mut z; citedCarve(2, 5, 5, Refl, b); let y = z; () }
example : progOk citedCallerBad (.const "Unit") [citedCarve] = false := by native_decide

end Dllbc.Tests.S25ArrSort
