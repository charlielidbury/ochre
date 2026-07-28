import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro

/-!
# §18 test suite — the rewriting layer

The next ergonomics layer after the M15 recursor sugar, and the fix for the M16
`count_swapL` wall: the count-preservation algebra needed motives that abstract a
computed subterm (`eqb m a`) at EVERY occurrence, hand-written and error-prone.
The mechanism is `abstractOccurrences` — syntactic subterm abstraction at the
`Term` level, post-elaboration, de Bruijn-correct under binders — with a
round-trip guarantee: `(λx. abstractOccurrences e t) e` β-reduces back to `t`.
No matching by eye, no missed occurrence, no tactic engine.
-/

open Dllbc

namespace Dllbc.Tests.S18Rewrite

-- SUBJECT: per-file local raw builders (eqbA/tnat/V/listNatT) for the rewrite Decls
-- and expected-value needles below — raw Terms are the subject here.
def eqbA (a b : Term) : Term := .app (.app Std.eqbFnT a) b
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]
def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def listNatT : Term := .app (.const "List") (.const "Nat")

/-- The round-trip property: abstracting `e` out of `t` and applying it back
    recovers `t` (by conversion). -/
def roundTrips (e t : Term) : Bool :=
  let applied := Term.app (Term.lam (.const "Bool") (abstractOccurrences e t)) e
  match (do let a ← readC 2000 applied; let b ← readC 2000 t; pure (Val.convert 2000 a b)).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## `abstractOccurrences` round-trips (the mechanism, unit-tested) -/

-- Two occurrences at the top level.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (eqbA (tnat 1) (tnat 2))) = true := by native_decide
-- An occurrence under a binder — `e` shifted, the bound var and free vars kept straight.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.lam (.const "Nat") (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (.pvar 0))) = true := by native_decide
-- No occurrence: `t` is unchanged (the binder is vacuous).
example : roundTrips (eqbA (tnat 1) (tnat 2)) (.idT (.const "Nat") (tnat 3) (tnat 3)) = true := by native_decide
-- The same subterm at DIFFERENT binder depths — both abstracted correctly.
example : roundTrips (eqbA (tnat 1) (tnat 2))
  (.idT (.const "Nat") (eqbA (tnat 1) (tnat 2)) (.lam (.const "Nat") (eqbA (tnat 1) (tnat 2)))) = true := by
  native_decide

/-! ## The `generalizing` surface form — motive by auto-abstraction

    `elim SCRUT generalizing GOAL { arms }` forms the motive by NF-ing the goal
    (so a computed subterm hidden in a definition — `eqb` inside `count` — is
    exposed) and abstracting SCRUT at every occurrence. The user writes the
    NATURAL goal; the macro places the holes, mechanically. -/

def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

open Dllbc.Std (eqbFnT addFnT countFnT) in
-- Casing on `eqb m a` makes two syntactically-different sides converge per branch
-- (`add Z X ≡ X`). The macro abstracts `eqb m a` at both occurrences; both Refl.
example : chk
  (pure{ λ (m : Nat). λ (a : Nat).
    elim (eqbFnT m a) generalizing
      (Id Nat (boolRec (λ (w : Bool). Nat) (S Z) Z (eqbFnT m a))
              (boolRec (λ (w : Bool). Nat) (addFnT Z (S Z)) (addFnT Z Z) (eqbFnT m a))) {
      True => Refl, False => Refl } })
  (pure{ Π (m : Nat) → Π (a : Nat) →
    Id Nat (boolRec (λ (w : Bool). Nat) (S Z) Z (eqbFnT m a))
           (boolRec (λ (w : Bool). Nat) (addFnT Z (S Z)) (addFnT Z Z) (eqbFnT m a)) }) = true := by native_decide

open Dllbc.Std (eqbFnT countFnT) in
-- The subterm hidden in `count`: the NATURAL goal (no unfolding) works because
-- the macro NF's it to expose `eqb m a` before abstracting.
example : chk
  (pure{ λ (m : Nat). λ (a : Nat). λ (l : List Nat).
    elim (eqbFnT m a) generalizing (Id Nat (countFnT m (Cons a l)) (countFnT m (Cons a l))) {
      True => Refl, False => Refl } })
  (pure{ Π (m : Nat) → Π (a : Nat) → Π (l : List Nat) →
    Id Nat (countFnT m (Cons a l)) (countFnT m (Cons a l)) }) = true := by native_decide

/-! ## cons2_comm — the report card (M16 ~18 hand-motive lines → ~8 here)

    Count is invariant under swapping two adjacent heads. The outer `generalizing`
    takes the NATURAL goal; the True arm nests a `generalizing` whose goal is the
    outer-True instance (a `boolRec` form — the residual is STRUCTURAL to
    nesting-by-casing, since the casing already delivers the knowledge a branch
    hypothesis would); every leaf is `Refl`; the False arm collapses to `Refl`
    outright. The macro abstracts `eqb` at every occurrence, so the M16
    missed-occurrence bug cannot recur. The ~8-line proof now lives in `StdLemmas`
    as the named `cons2_comm` the count_swapL stack consumes; this checks it. -/

example : chk StdLemmas.cons2_comm StdLemmas.cons2_comm_ty = true := by native_decide

/-! ## The bounded `count_swapL` stack (§18)

    `cons2_comm` (above) is the base; `count_cons_congr` lifts a tail equation
    through `Cons`; `count_headswap` is the bounded head-swap double-induction; and
    `count_swapL` is the top. All four are authored in `StdLemmas`; here we check
    each type-checks. See the `StdLemmas` header for why no rewrite-by-Id is needed
    (the eqb reasoning is localised in `cons2_comm` and `count_cons_congr`). -/

example : chk StdLemmas.count_cons_congr StdLemmas.count_cons_congr_ty = true := by native_decide
example : chk StdLemmas.count_headswap StdLemmas.count_headswap_ty = true := by native_decide
example : chk StdLemmas.count_swapL StdLemmas.count_swapL_ty = true := by native_decide
-- The §22 bridge: the set/nth exit form ≡ swapL under `Le (S i) j` (see StdLemmas
-- header). Lets `count_swapL'`/`len_swapL` transport to a swap Decl's exit reading.
example : chk StdLemmas.swapL_set StdLemmas.swapL_set_ty = true := by native_decide
-- §22 partition rung: count preservation of the range scan/partition (the Perm half
-- of partition's postcondition), threading the range bound to feed count_swapL'.
example : chk StdLemmas.count_partScanRangeL StdLemmas.count_partScanRangeL_ty = true := by native_decide
example : chk StdLemmas.count_partitionRangeL StdLemmas.count_partitionRangeL_ty = true := by native_decide
-- §22 quicksort rung: count preservation of the full sort (the Perm half of
-- quicksort's postcondition), with the two sub-range bounds sortRangeBL/sortRangeBR.
example : chk StdLemmas.sortRangeBL StdLemmas.sortRangeBL_ty = true := by native_decide
example : chk StdLemmas.sortRangeBR StdLemmas.sortRangeBR_ty = true := by native_decide
example : chk StdLemmas.count_sortRangeL StdLemmas.count_sortRangeL_ty = true := by native_decide
-- §22 M22-c: the range-order predicates (bounded-Π; the family isn't chk-able but its
-- applied forms are — exercised by head-extraction and the empty-range base).
example : chk StdLemmas.allLeR_head StdLemmas.allLeR_head_ty = true := by native_decide
example : chk StdLemmas.allGtR_head StdLemmas.allGtR_head_ty = true := by native_decide
example : chk StdLemmas.allLeR_empty StdLemmas.allLeR_empty_ty = true := by native_decide
example : chk StdLemmas.allGtR_empty StdLemmas.allGtR_empty_ty = true := by native_decide
-- segment count (the perm-invariant multiset vehicle): typechecks + computes.
example : chk StdLemmas.segCount StdLemmas.segCount_ty = true := by native_decide
-- range sortedness predicate (bounded-Π): head extraction + vacuous width ≤ 1 bases.
example : chk StdLemmas.sortedR_head StdLemmas.sortedR_head_ty = true := by native_decide
example : chk StdLemmas.sortedR_zero StdLemmas.sortedR_zero_ty = true := by native_decide
example : chk StdLemmas.sortedR_one StdLemmas.sortedR_one_ty = true := by native_decide
-- leb ↔ Le bridges (the Bool-comparison / order link) + the Bool discriminates.
example : chk StdLemmas.boolFT StdLemmas.boolFT_ty = true := by native_decide
example : chk StdLemmas.boolTF StdLemmas.boolTF_ty = true := by native_decide
example : chk StdLemmas.leb_true_le StdLemmas.leb_true_le_ty = true := by native_decide
example : chk StdLemmas.leb_false_gt StdLemmas.leb_false_gt_ty = true := by native_decide
example : chk StdLemmas.le_antisym StdLemmas.le_antisym_ty = true := by native_decide
example : chk StdLemmas.le_add_cancel_l StdLemmas.le_add_cancel_l_ty = true := by native_decide
example : chk StdLemmas.add_sub_cancel StdLemmas.add_sub_cancel_ty = true := by native_decide
-- §22 M22-c: the GLUE (sorted range from sorted halves) + its helpers, all kernel-green.
example : chk StdLemmas.le_pred_l StdLemmas.le_pred_l_ty = true := by native_decide
example : chk StdLemmas.gap_pos StdLemmas.gap_pos_ty = true := by native_decide
example : chk StdLemmas.reindex_pos StdLemmas.reindex_pos_ty = true := by native_decide
example : chk StdLemmas.reindex_pos_s StdLemmas.reindex_pos_s_ty = true := by native_decide
example : chk StdLemmas.reindex_bnd StdLemmas.reindex_bnd_ty = true := by native_decide
example : chk StdLemmas.glue_left_pivot StdLemmas.glue_left_pivot_ty = true := by native_decide
example : chk StdLemmas.glue_pivot_right StdLemmas.glue_pivot_right_ty = true := by native_decide
example : chk StdLemmas.glue_both_right StdLemmas.glue_both_right_ty = true := by native_decide
example : chk StdLemmas.glue StdLemmas.glue_ty = true := by native_decide
-- §22 M22-c positional stratum: nth-under-swapL locality. The two `set` helpers,
-- then the "outside {i,j}" pair (lt/gt) the range scan's locality consumes, then
-- the two swap endpoints (lo/hi). Minimal honest bounds (see StdLemmas header).
example : chk StdLemmas.nth_set_gt StdLemmas.nth_set_gt_ty = true := by native_decide
example : chk StdLemmas.nth_set_same StdLemmas.nth_set_same_ty = true := by native_decide
example : chk StdLemmas.nth_swapL_lt StdLemmas.nth_swapL_lt_ty = true := by native_decide
example : chk StdLemmas.nth_swapL_gt StdLemmas.nth_swapL_gt_ty = true := by native_decide
example : chk StdLemmas.nth_swapL_lo StdLemmas.nth_swapL_lo_ty = true := by native_decide
example : chk StdLemmas.nth_swapL_hi StdLemmas.nth_swapL_hi_ty = true := by native_decide
-- §22 M22-c locality: positions outside the operated range are unchanged by the range
-- scan / partition. `_lt` (below lo) and `_ge` (at/above the top) — the two directions
-- the quicksort recursion consumes; _ge threads count_partScanRangeL's invariant on a
-- position (no len_swapL). Wrappers pick the pivot then defer to the scan.
example : chk StdLemmas.nth_partScanRangeL_lt StdLemmas.nth_partScanRangeL_lt_ty = true := by native_decide
example : chk StdLemmas.nth_partScanRangeL_ge StdLemmas.nth_partScanRangeL_ge_ty = true := by native_decide
example : chk StdLemmas.nth_partitionRangeL_lt StdLemmas.nth_partitionRangeL_lt_ty = true := by native_decide
example : chk StdLemmas.nth_partitionRangeL_ge StdLemmas.nth_partitionRangeL_ge_ty = true := by native_decide
-- §22 M22-c locality culmination: the full sort. _lt/_ge over positions outside the
-- sorted range, plus the position sub-range bounds (partSizeCnt, sortRangeGeBL/BR —
-- the len-relative sortRangeBL/BR stripped of their len_* layers).
example : chk StdLemmas.nth_sortRangeL_lt StdLemmas.nth_sortRangeL_lt_ty = true := by native_decide
example : chk StdLemmas.partSizeCnt StdLemmas.partSizeCnt_ty = true := by native_decide
example : chk StdLemmas.sortRangeGeBL StdLemmas.sortRangeGeBL_ty = true := by native_decide
example : chk StdLemmas.sortRangeGeBR StdLemmas.sortRangeGeBR_ty = true := by native_decide
example : chk StdLemmas.nth_sortRangeL_ge StdLemmas.nth_sortRangeL_ge_ty = true := by native_decide
-- §22 Step C bridges: Nat no-confusion (Z≠S via large elim into Type), s_inj,
-- add_cancel_l, nth_drop, list_ext, take_ext_bounded, len_drop_cong, count_split.
example : chk StdLemmas.znots StdLemmas.znots_ty = true := by native_decide
example : chk StdLemmas.s_inj StdLemmas.s_inj_ty = true := by native_decide
example : chk StdLemmas.add_cancel_l StdLemmas.add_cancel_l_ty = true := by native_decide
example : chk StdLemmas.nth_drop StdLemmas.nth_drop_ty = true := by native_decide
example : chk StdLemmas.list_ext StdLemmas.list_ext_ty = true := by native_decide
example : chk StdLemmas.take_ext_bounded StdLemmas.take_ext_bounded_ty = true := by native_decide
example : chk StdLemmas.len_drop_cong StdLemmas.len_drop_cong_ty = true := by native_decide
example : chk StdLemmas.count_split StdLemmas.count_split_ty = true := by native_decide
-- §22 M22-c step 3: segment-count preservation. The cancellation glue
-- (count_rest/seg_preserved, seg_glue), the prefix/suffix list equalities from Step B
-- locality, and THE GOALS: segCount survives the range sort and partition.
example : chk StdLemmas.count_rest_preserved StdLemmas.count_rest_preserved_ty = true := by native_decide
example : chk StdLemmas.count_seg_preserved StdLemmas.count_seg_preserved_ty = true := by native_decide
example : chk StdLemmas.seg_glue StdLemmas.seg_glue_ty = true := by native_decide
example : chk StdLemmas.take_lo_sort StdLemmas.take_lo_sort_ty = true := by native_decide
example : chk StdLemmas.drop_suffix_sort StdLemmas.drop_suffix_sort_ty = true := by native_decide
example : chk StdLemmas.take_lo_partition StdLemmas.take_lo_partition_ty = true := by native_decide
example : chk StdLemmas.drop_suffix_partition StdLemmas.drop_suffix_partition_ty = true := by native_decide
example : chk StdLemmas.segCount_sortRangeL StdLemmas.segCount_sortRangeL_ty = true := by native_decide
example : chk StdLemmas.segCount_partitionRangeL StdLemmas.segCount_partitionRangeL_ty = true := by native_decide
-- §22 M22-c step 2: partition-invariant proofs. Gate: the middle-band swap locality
-- (nth_set_lt + nth_swapL_mid, Step A's unstated interior) and the pivot-tracking scan
-- invariant (partScanRangeL_pivot — pivot ends at add finalI lo).
example : chk StdLemmas.nth_set_lt StdLemmas.nth_set_lt_ty = true := by native_decide
example : chk StdLemmas.nth_swapL_mid StdLemmas.nth_swapL_mid_ty = true := by native_decide
example : chk StdLemmas.partScanRangeL_pivot StdLemmas.partScanRangeL_pivot_ty = true := by native_decide
-- §22 M22-c step 2: region-invariant growth/transport toolkit (consumed by the allLeR/
-- allGtR proofs): extend at the far end (leb/antisym decision), prepend the pivot,
-- transport across a pointwise nth-equality, and the index↔offset add-order bridge.
example : chk StdLemmas.allLeR_extend_far StdLemmas.allLeR_extend_far_ty = true := by native_decide
example : chk StdLemmas.allLeR_extend_lo StdLemmas.allLeR_extend_lo_ty = true := by native_decide
example : chk StdLemmas.allLeR_cong StdLemmas.allLeR_cong_ty = true := by native_decide
example : chk StdLemmas.add_swap_succ StdLemmas.add_swap_succ_ty = true := by native_decide
-- §22 M22-c step 2 headline #1: the ≤-region invariant. Supporting bridges (pos_bridge_ss,
-- bnd_sl) and the base/step region-growth pieces (allLeR_base_swap, allLeR_step_TZ/swap).
example : chk StdLemmas.pos_bridge_ss StdLemmas.pos_bridge_ss_ty = true := by native_decide
example : chk StdLemmas.bnd_sl StdLemmas.bnd_sl_ty = true := by native_decide
example : chk StdLemmas.allLeR_base_swap StdLemmas.allLeR_base_swap_ty = true := by native_decide
example : chk StdLemmas.allLeR_step_TZ StdLemmas.allLeR_step_TZ_ty = true := by native_decide
example : chk StdLemmas.allLeR_step_swap StdLemmas.allLeR_step_swap_ty = true := by native_decide
example : chk StdLemmas.partScanRangeL_allLeR StdLemmas.partScanRangeL_allLeR_ty = true := by native_decide
-- §22 M22-c step 2 wrappers: partitionRangeL = scan at i=g=0 (vacuous preconditions).
example : chk StdLemmas.partition_pivot StdLemmas.partition_pivot_ty = true := by native_decide
example : chk StdLemmas.partition_allLeR StdLemmas.partition_allLeR_ty = true := by native_decide
-- §22 M22-c step 2 headline #2: the gap (>-region) invariant + its wrapper. Mirror helpers
-- (allGtR_extend_far/cong, allGtR_base_swap, allGtR_step_false/swap) + offset bridges.
example : chk StdLemmas.allGtR_extend_far StdLemmas.allGtR_extend_far_ty = true := by native_decide
example : chk StdLemmas.allGtR_cong StdLemmas.allGtR_cong_ty = true := by native_decide
example : chk StdLemmas.off_bridge StdLemmas.off_bridge_ty = true := by native_decide
example : chk StdLemmas.allGtR_base_swap StdLemmas.allGtR_base_swap_ty = true := by native_decide
example : chk StdLemmas.pos_bridge_scan StdLemmas.pos_bridge_scan_ty = true := by native_decide
example : chk StdLemmas.allGtR_step_false StdLemmas.allGtR_step_false_ty = true := by native_decide
example : chk StdLemmas.bnd_gap_upper StdLemmas.bnd_gap_upper_ty = true := by native_decide
example : chk StdLemmas.allGtR_step_swap StdLemmas.allGtR_step_swap_ty = true := by native_decide
example : chk StdLemmas.partScanRangeL_allGtR StdLemmas.partScanRangeL_allGtR_ty = true := by native_decide
example : chk StdLemmas.partition_allGtR StdLemmas.partition_allGtR_ty = true := by native_decide
-- §22 M22-c step 3 keystone bridges: the two "positional → multiset (segCount) survives"
-- directions that ARE perm-invariant, + their count/segment helpers. (#1/#3/#5 pending a
-- statement fix — nth_seg_count_pos as committed is false off-end; see the finding.)
example : chk StdLemmas.eqb_gt_false StdLemmas.eqb_gt_false_ty = true := by native_decide
example : chk StdLemmas.eqb_lt_false StdLemmas.eqb_lt_false_ty = true := by native_decide
example : chk StdLemmas.count_cons_miss StdLemmas.count_cons_miss_ty = true := by native_decide
example : chk StdLemmas.count_zero_ext StdLemmas.count_zero_ext_ty = true := by native_decide
example : chk StdLemmas.nth_take StdLemmas.nth_take_ty = true := by native_decide
example : chk StdLemmas.len_take_le StdLemmas.len_take_le_ty = true := by native_decide
example : chk StdLemmas.allLeR_to_noAbove StdLemmas.allLeR_to_noAbove_ty = true := by native_decide
example : chk StdLemmas.allGtR_to_noBelow StdLemmas.allGtR_to_noBelow_ty = true := by native_decide

/-! ## rewrite-by-Id — the branch-equation / knowledge layer

    Given an equation as an ORDINARY Id hypothesis, transport a proof by it via J
    with the abstractOccurrences motive. The essential use (which the abstraction
    layer CANNOT do — the subterm hides behind the scrutinee's own reduction):
    resolve a STUCK `count m (Cons a l)` using a RECEIVED equation `eqb m a =
    True`. Named in `StdLemmas` as `count_cons_hit`; this checks it, and the
    imperative tie-in below returns it applied to its params. -/

example : chk StdLemmas.count_cons_hit StdLemmas.count_cons_hit_ty = true := by native_decide

/-! ## The imperative tie-in — a surface-rewritten proof through ⇒-lift + hasType

    `certConsHit` is an IMPERATIVE function: it holds a mutable borrow `v` and
    mutates through it (`*v := Nil`, exercising the ⇐ writeR arrow and the argument
    borrow's owed-type obligation). Its RESULT is the §18 rewrite-by-Id proof
    `count_cons_hit` applied to the pure params — a surface-authored proof term
    that, at the value-returning audit, must be read in the imperative regime and
    type-checked. The pure lift (⇒⊇⇝, §1.3) carries the proof through: the `count`
    /`j`/`Id` formers are comptime, so `readR` delegates to `readC`, and the audit
    discharges the return obligation with the same `hasType` that `chk` runs above.
    The tie-in thus proves surface-rewritten proofs flow through the borrow
    machinery — the shape the quicksort caller uses when it applies count lemmas to
    the M17-recovered result. -/

-- SUBJECT: hand-built raw Decl — its `.idT` return obligation and proof-carrying
-- `.assign` body exercise the rewrite/Id machinery that IS under test; the raw form
-- (not a surface `decl{}`) is the subject.
def certConsHit : Decl :=
  { name := "certConsHit",
    retType := .idT (.const "Nat")
      (.app (.app Std.countFnT (V 1 "m")) (.ctorApp "Cons" [V 2 "a", V 3 "l"]))
      (.ctorApp "S" [.app (.app Std.countFnT (V 1 "m")) (V 3 "l")]),
    telescope := [
      ("v", .borrowT listNatT listNatT),
      ("m", .const "Nat"), ("a", .const "Nat"), ("l", listNatT),
      ("hq", .idT (.const "Bool") (eqbA (V 1 "m") (V 2 "a")) (.ctorApp "True" []))],
    body := .assign (.deref (V 0 "v")) (.ctorApp "Nil" [])
      (.app (.app (.app (.app StdLemmas.count_cons_hit (V 1 "m")) (V 2 "a")) (V 3 "l")) (V 4 "hq")) }
example : checkFnOk certConsHit = true := by native_decide

-- Negative control: the same body, but the return type claims `S (S (count m l))`
-- — a count the rewrite-by-Id proof does NOT prove. The value-returning audit runs
-- `hasType` on the proof against the (lying) pinned return type and rejects it, so
-- the tie-in's acceptance above is not vacuous.
-- SUBJECT: a deliberately-lying return type (raw Term) for the negative control.
def certConsHitLieRet : Term := .idT (.const "Nat")
  (.app (.app Std.countFnT (V 1 "m")) (.ctorApp "Cons" [V 2 "a", V 3 "l"]))
  (.ctorApp "S" [.ctorApp "S" [.app (.app Std.countFnT (V 1 "m")) (V 3 "l")]])
def certConsHitLie : Decl := { certConsHit with name := "certConsHitLie", retType := certConsHitLieRet }
example : checkFnErr certConsHitLie "does not have return type" = true := by native_decide

end Dllbc.Tests.S18Rewrite
