module Quicksort

/// In-place quicksort in Low*, over a mutable `LowStar.Buffer` of machine
/// integers (UInt32), extracted to C via KaRaMeL.
///
/// Partition scheme: **Lomuto** (pivot = last element of the range).
///
/// THE FOCAL COMPARISON POINT (vs Idris uniqueness / Aeneas borrows): how the
/// disjoint-mutable-split is expressed. In Low* there are NO sub-buffer
/// *values* threaded through the recursion. The buffer `b` stays a single
/// value; the "two disjoint halves" are index ranges `[lo, p)` and `[p+1, hi)`
/// over the same `b`. Separation is discharged *logically* by the `modifies`
/// clause and the `loc_buffer` location algebra: each recursive call only
/// `modifies (loc_buffer b)`, and the framing of one range against the other
/// is what lets F* conclude the second recursive call leaves the first
/// (already-sorted) half untouched. That explicit `modifies`/`loc` bookkeeping
/// is exactly the cost that Ochre's borrow-based model aims to discharge for
/// free (the borrow checker would give disjointness structurally).

open FStar.HyperStack.ST
open LowStar.BufferOps

module B   = LowStar.Buffer
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST
module U32 = FStar.UInt32
module S   = FStar.Seq
module SP  = FStar.Seq.Properties

#set-options "--fuel 1 --ifuel 1 --z3rlimit 100"

(* The element type and its total order (a Tot, boolean total order). *)
unfold let elem = U32.t
unfold let le (x y:elem) : bool = U32.lte x y

(* -------------------------------------------------------------------------- *)
(* Spec-level predicates on the underlying sequence.                          *)
(* -------------------------------------------------------------------------- *)

unfold let contents (h:HS.mem) (b:B.buffer elem) : GTot (S.seq elem) = B.as_seq h b

(* A range [lo,hi) of `s` is sorted ascending. *)
let sorted_range (s:S.seq elem) (lo hi:nat) : prop =
  hi <= S.length s /\
  (forall (i j:nat). lo <= i /\ i <= j /\ j < hi ==> le (S.index s i) (S.index s j))

(* Every element of [lo1,hi1) is <= every element of [lo2,hi2). *)
let between_le (s:S.seq elem) (lo1 hi1 lo2 hi2:nat) : prop =
  hi1 <= S.length s /\ hi2 <= S.length s /\
  (forall (i j:nat). lo1 <= i /\ i < hi1 /\ lo2 <= j /\ j < hi2
                     ==> le (S.index s i) (S.index s j))

(* Every element of [lo,hi) is <= the scalar `x`. *)
unfold let all_le (s:S.seq elem) (lo hi:nat) (x:elem) : prop =
  hi <= S.length s /\
  (forall (i:nat). lo <= i /\ i < hi ==> le (S.index s i) x)

(* Every element of [lo,hi) is >= the scalar `x`. *)
unfold let all_ge (s:S.seq elem) (lo hi:nat) (x:elem) : prop =
  hi <= S.length s /\
  (forall (i:nat). lo <= i /\ i < hi ==> le x (S.index s i))

(* Every element of [lo,hi) is > the scalar `x` (strictly). *)
unfold let all_gt (s:S.seq elem) (lo hi:nat) (x:elem) : prop =
  hi <= S.length s /\
  (forall (i:nat). lo <= i /\ i < hi ==> not (le (S.index s i) x))

(* -------------------------------------------------------------------------- *)
(* swap: the single mutating primitive. Permutation of the whole buffer is    *)
(* built entirely from swaps, each a transposition (multiset-preserving).     *)
(* `lemma_swap_permutes` gives `permutation s (swap s i j)` for free.         *)
(* -------------------------------------------------------------------------- *)

val swap (b:B.buffer elem) (i j:U32.t)
  : Stack unit
    (requires fun h -> B.live h b /\ U32.v i < B.length b /\ U32.v j < B.length b)
    (ensures fun h0 _ h1 ->
      B.live h1 b /\
      B.modifies (B.loc_buffer b) h0 h1 /\
      contents h1 b == SP.swap (contents h0 b) (U32.v i) (U32.v j))
let swap b i j =
  let vi = b.(i) in
  let vj = b.(j) in
  b.(j) <- vi;
  b.(i) <- vj
  (* SP.swap s i j = upd (upd s j s.[i]) i s.[j], matched by the two upds. *)

(* swap preserves the whole-buffer multiset (permutation). *)
let swap_is_permutation (s:S.seq elem) (i:nat{i < S.length s}) (j:nat{j < S.length s})
  : Lemma (SP.permutation elem s (SP.swap s i j)) =
  if i <= j then SP.lemma_swap_permutes s i j
  else begin
    (* swap is symmetric in i,j up to seq-equality. *)
    SP.lemma_swap_permutes s j i;
    assert (S.equal (SP.swap s i j) (SP.swap s j i))
  end

(* -------------------------------------------------------------------------- *)
(* Multiset glue: a permutation preserves a uniform bound on its elements.     *)
(* This is exactly the "permutation needs Seq lemmas; Z3 won't do multisets    *)
(* unaided" obligation. We discharge it via counting: if some element of s2    *)
(* violated the bound, its count in s2 would be positive but its count in s1   *)
(* zero, contradicting count-equality.                                         *)
(* -------------------------------------------------------------------------- *)

(* `all_pred f s` : every element of s satisfies predicate f. *)
unfold let all_pred (f:elem -> bool) (s:S.seq elem) : prop =
  forall (i:nat). i < S.length s ==> f (S.index s i)

(* Bridge between the absolute-index range predicates and `all_pred` on a
   slice. `index (slice s a c) k == index s (a+k)`, so the two are equivalent. *)
let all_le_slice (s:S.seq elem) (a c:nat) (x:elem)
  : Lemma (requires a <= c /\ c <= S.length s)
          (ensures (all_le s a c x <==> all_pred (fun y -> le y x) (S.slice s a c))) =
  let sub = S.slice s a c in
  (* (->) every index i in [a,c) of s is index (i-a) of sub *)
  let fwd (i:nat{a <= i /\ i < c}) : Lemma (S.index sub (i - a) == S.index s i) =
    S.lemma_index_slice s a c (i - a) in
  FStar.Classical.forall_intro fwd;
  (* (<-) every index k of sub is index (a+k) of s *)
  let bwd (k:nat{k < S.length sub}) : Lemma (S.index sub k == S.index s (a + k)) =
    S.lemma_index_slice s a c k in
  FStar.Classical.forall_intro bwd

let all_ge_slice (s:S.seq elem) (a c:nat) (x:elem)
  : Lemma (requires a <= c /\ c <= S.length s)
          (ensures (all_ge s a c x <==> all_pred (fun y -> le x y) (S.slice s a c))) =
  let sub = S.slice s a c in
  let fwd (i:nat{a <= i /\ i < c}) : Lemma (S.index sub (i - a) == S.index s i) =
    S.lemma_index_slice s a c (i - a) in
  FStar.Classical.forall_intro fwd;
  let bwd (k:nat{k < S.length sub}) : Lemma (S.index sub k == S.index s (a + k)) =
    S.lemma_index_slice s a c k in
  FStar.Classical.forall_intro bwd

(* sorted_range depends only on the slice [a,c): if two seqs agree there, their
   sorted_range judgments coincide. *)
let sorted_range_frame (s s':S.seq elem) (a c:nat)
  : Lemma (requires a <= c /\ c <= S.length s /\ c <= S.length s' /\
                    S.slice s a c == S.slice s' a c)
          (ensures (sorted_range s a c <==> sorted_range s' a c)) =
  let fwd (i:nat{a <= i /\ i < c}) : Lemma (S.index s i == S.index s' i) =
    S.lemma_index_slice s a c (i - a);
    S.lemma_index_slice s' a c (i - a)
  in
  FStar.Classical.forall_intro fwd

(* If x sits at index i of s, then it is counted at least once. *)
let rec count_of_index (x:elem) (s:S.seq elem) (i:nat{i < S.length s})
  : Lemma (requires S.index s i == x)
          (ensures SP.count x s > 0)
          (decreases i) =
  if i = 0 then ()  (* head s = x => count = 1 + count x (tail s) *)
  else count_of_index x (S.tail s) (i - 1)

(* If s1,s2 are permutations and all of s1 satisfy f, then all of s2 satisfy f.
   Proof: `lemma_mem_count s1 f` lifts the pointwise bound to "every *member*
   of s1 satisfies f"; for any index i of s2, x = s2[i] has count x s2 > 0 =>
   (count-equality) count x s1 > 0 => mem x s1 => f x. *)
let perm_preserves_all_pred (f:elem -> bool) (s1 s2:S.seq elem)
  : Lemma (requires SP.permutation elem s1 s2 /\ all_pred f s1)
          (ensures all_pred f s2) =
  SP.lemma_mem_count s1 f;   (* forall x. mem x s1 ==> f x *)
  let aux (i:nat{i < S.length s2}) : Lemma (f (S.index s2 i)) =
    let x = S.index s2 i in
    (* x occurs in s2 at i, so count x s2 > 0; counts are equal, so mem x s1. *)
    count_of_index x s2 i;
    assert (SP.count x s1 == SP.count x s2);
    assert (SP.mem x s1)
  in
  FStar.Classical.forall_intro aux

(* -------------------------------------------------------------------------- *)
(* Lomuto partition over [lo, hi), pivot = b[hi-1].                           *)
(*                                                                            *)
(* The scan is a recursive helper `part_scan`. Loop state:                    *)
(*   - `store`: index where the next "<= pivot" element goes (boundary of the *)
(*      low region), lo <= store <= j;                                        *)
(*   - `j`:     current scan position, lo <= j <= hi-1.                       *)
(* Invariant maintained (functional part proven as far as Z3 allows):         *)
(*   - permutation of the whole buffer w.r.t. the entry heap;                 *)
(*   - only loc_buffer b is modified.                                         *)
(* -------------------------------------------------------------------------- *)

val part_scan
  (b:B.buffer elem)
  (lo hi store j:U32.t)
  (pivot:elem)
  : Stack U32.t
    (requires fun h ->
      B.live h b /\
      U32.v lo <= U32.v store /\ U32.v store <= U32.v j /\
      U32.v j <= U32.v hi - 1 /\ U32.v hi <= B.length b /\ U32.v lo < U32.v hi /\
      (* Lomuto loop invariant on entry: *)
      S.index (contents h b) (U32.v hi - 1) == pivot /\        (* pivot parked at hi-1 *)
      all_le (contents h b) (U32.v lo) (U32.v store) pivot /\   (* low region <= pivot *)
      all_gt (contents h b) (U32.v store) (U32.v j) pivot)      (* scanned region > pivot *)
    (ensures fun h0 store' h1 ->
      B.live h1 b /\
      U32.v lo <= U32.v store' /\ U32.v store' <= U32.v hi - 1 /\
      (* Only [lo, hi-1) is touched (every swap is at store or j, both in it). *)
      B.modifies (B.loc_buffer_from_to b lo (U32.sub hi 1ul)) h0 h1 /\
      SP.permutation elem (contents h0 b) (contents h1 b) /\
      (* On exit (j has reached hi-1): low region <= pivot, rest > pivot. *)
      S.index (contents h1 b) (U32.v hi - 1) == pivot /\
      all_le (contents h1 b) (U32.v lo) (U32.v store') pivot /\
      all_gt (contents h1 b) (U32.v store') (U32.v hi - 1) pivot)
    (decreases (U32.v hi - 1 - U32.v j))
let rec part_scan b lo hi store j pivot =
  let h0 = ST.get () in
  if U32.lt j (U32.sub hi 1ul) then begin
    let xj = b.(j) in
    if U32.lte xj pivot then begin
      swap_is_permutation (contents h0 b) (U32.v store) (U32.v j);
      swap b store j;
      let h1 = ST.get () in
      (* Lift this single swap's `loc_buffer b` modifies to the narrower
         `loc_buffer_from_to b lo (hi-1)`: indices < lo and >= hi-1 are
         untouched because the swap was at store,j in [lo, hi-1). *)
      SP.swap_frame_lo' (contents h0 b) 0 (U32.v lo) (U32.v store) (U32.v j);
      SP.swap_frame_hi (contents h0 b) (U32.v store) (U32.v j) (U32.v hi - 1) (B.length b);
      B.modifies_loc_buffer_from_to_intro b lo (U32.sub hi 1ul) B.loc_none h0 h1;
      let store' = U32.add store 1ul in
      (* Re-establish the invariant after `swap store j` (s1 = swap s0 store j):
         - index hi-1 untouched (store,j < hi-1)  => pivot still parked
         - [lo,store) untouched, plus new s1[store]=s0[j]<=pivot => all_le grows
         - s1[store..j) : old s0[store..j-1) shifted, all were > pivot,
           and the displaced s0[store] (>pivot, unless store=j) lands at j. *)
      assert (S.index (contents h1 b) (U32.v hi - 1) == pivot);
      assert (all_le (contents h1 b) (U32.v lo) (U32.v store') pivot);
      assert (all_gt (contents h1 b) (U32.v store') (U32.v j + 1) pivot);
      let r = part_scan b lo hi store' (U32.add j 1ul) pivot in
      r
    end else begin
      (* xj > pivot: no swap. [store,j) all > pivot and s[j] > pivot => grows. *)
      assert (all_gt (contents h0 b) (U32.v store) (U32.v j + 1) pivot);
      part_scan b lo hi store (U32.add j 1ul) pivot
    end
  end else
    store  (* j = hi-1: scanned region is [store, hi-1); modifies loc_none here *)

val partition (b:B.buffer elem) (lo hi:U32.t)
  : Stack U32.t
    (requires fun h ->
      B.live h b /\ U32.v lo < U32.v hi /\ U32.v hi <= B.length b)
    (ensures fun h0 p h1 ->
      B.live h1 b /\
      U32.v lo <= U32.v p /\ U32.v p < U32.v hi /\
      B.modifies (B.loc_buffer_from_to b lo hi) h0 h1 /\
      SP.permutation elem (contents h0 b) (contents h1 b) /\
      (* Partition property: low half <= pivot=b[p] <= high half. *)
      all_le (contents h1 b) (U32.v lo) (U32.v p) (S.index (contents h1 b) (U32.v p)) /\
      all_ge (contents h1 b) (U32.v p + 1) (U32.v hi) (S.index (contents h1 b) (U32.v p)))
let partition b lo hi =
  let h0 = ST.get () in
  let pivot = b.(U32.sub hi 1ul) in
  let store = part_scan b lo hi lo lo pivot in
  let h1 = ST.get () in
  swap_is_permutation (contents h1 b) (U32.v store) (U32.v hi - 1);
  swap b store (U32.sub hi 1ul);
  let h2 = ST.get () in
  (* part_scan touched [lo, hi-1); the final pivot-placing swap touches
     {store, hi-1} \subseteq [lo, hi). Both are inside [lo, hi), so the total
     effect is modifies (loc_buffer_from_to b lo hi). *)
  SP.swap_frame_lo' (contents h1 b) 0 (U32.v lo) (U32.v store) (U32.v hi - 1);
  B.modifies_loc_buffer_from_to_intro b lo hi B.loc_none h1 h2;
  B.loc_includes_loc_buffer_from_to b lo hi lo (U32.sub hi 1ul);
  (* After swap (store, hi-1): the pivot (was at hi-1) lands at `store`;
     [lo,store) is below both swapped indices so unchanged (still <= pivot);
     [store+1,hi-1) unchanged (still > pivot); index hi-1 now holds the old
     b[store], which was > pivot (or store=hi-1, vacuous). So [store+1,hi) is
     all >= pivot = b[store]. *)
  assert (S.index (contents h2 b) (U32.v store) == pivot);
  assert (all_le (contents h2 b) (U32.v lo) (U32.v store) pivot);
  assert (all_ge (contents h2 b) (U32.v store + 1) (U32.v hi) pivot);
  store

(* -------------------------------------------------------------------------- *)
(* Slice-permutation extraction: if two whole sequences are permutations and   *)
(* agree on the prefix [0,a) and the suffix [c, len), then the middle [a,c) is  *)
(* a permutation of itself. Pure count arithmetic via lemma_count_slice.       *)
(* -------------------------------------------------------------------------- *)

let middle_perm (s1 s2:S.seq elem) (a c:nat)
  : Lemma (requires
            S.length s1 == S.length s2 /\ a <= c /\ c <= S.length s1 /\
            SP.permutation elem s1 s2 /\
            S.slice s1 0 a == S.slice s2 0 a /\
            S.slice s1 c (S.length s1) == S.slice s2 c (S.length s2))
          (ensures SP.permutation elem (S.slice s1 a c) (S.slice s2 a c)) =
  let n = S.length s1 in
  let aux (x:elem) : Lemma (SP.count x (S.slice s1 a c) == SP.count x (S.slice s2 a c)) =
    (* count over [0,a) + [a,n) ; then split [a,n) into [a,c) + [c,n). *)
    SP.lemma_count_slice s1 a;
    SP.lemma_count_slice s2 a;
    SP.lemma_count_slice (S.slice s1 a n) (c - a);
    SP.lemma_count_slice (S.slice s2 a n) (c - a);
    (* slices of slices line up: *)
    assert (S.equal (S.slice (S.slice s1 a n) 0 (c - a)) (S.slice s1 a c));
    assert (S.equal (S.slice (S.slice s2 a n) 0 (c - a)) (S.slice s2 a c));
    assert (S.equal (S.slice (S.slice s1 a n) (c - a) (n - a)) (S.slice s1 c n));
    assert (S.equal (S.slice (S.slice s2 a n) (c - a) (n - a)) (S.slice s2 c n))
  in
  FStar.Classical.forall_intro aux

(* -------------------------------------------------------------------------- *)
(* The sortedness glue, assembled at the end of each quicksort call.          *)
(* Hypotheses (all established in the caller): both halves are sorted, the     *)
(* pivot pv sits at index p untouched, and each half was a permutation of a    *)
(* range respecting the pivot bound.                                          *)
(* -------------------------------------------------------------------------- *)

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let sortedness_glue
  (b:B.buffer elem) (lo p hi:U32.t) (pv:elem)
  (h1 h2 h3:HS.mem)
  : Lemma
    (requires (
      let s1 = B.as_seq h1 b in
      let s2 = B.as_seq h2 b in
      let s3 = B.as_seq h3 b in
      B.live h3 b /\
      U32.v lo <= U32.v p /\ U32.v p < U32.v hi /\ U32.v hi <= B.length b /\
      S.length s1 == B.length b /\ S.length s2 == B.length b /\ S.length s3 == B.length b /\
      (* partition output at h1 *)
      S.index s1 (U32.v p) == pv /\
      all_le s1 (U32.v lo) (U32.v p) pv /\
      all_ge s1 (U32.v p + 1) (U32.v hi) pv /\
      (* low recursion h1->h2: permutation, [p,n) frozen, low half sorted *)
      SP.permutation elem s1 s2 /\
      S.slice s1 (U32.v p) (B.length b) == S.slice s2 (U32.v p) (B.length b) /\
      S.slice s1 0 (U32.v lo) == S.slice s2 0 (U32.v lo) /\
      sorted_range s2 (U32.v lo) (U32.v p) /\
      (* high recursion h2->h3: permutation, [lo,p+1) and [hi,n) frozen *)
      SP.permutation elem s2 s3 /\
      S.slice s2 0 (U32.v p + 1) == S.slice s3 0 (U32.v p + 1) /\
      S.slice s2 (U32.v hi) (B.length b) == S.slice s3 (U32.v hi) (B.length b) /\
      sorted_range s3 (U32.v p + 1) (U32.v hi)))
    (ensures sorted_range (B.as_seq h3 b) (U32.v lo) (U32.v hi)) =
  let s1 = B.as_seq h1 b in
  let s2 = B.as_seq h2 b in
  let s3 = B.as_seq h3 b in
  let lo' = U32.v lo in let p' = U32.v p in let hi' = U32.v hi in
  let n = B.length b in
  (* (1) Low half at h2 still <= pv: it is a permutation of s1's [lo,p). *)
  middle_perm s1 s2 lo' p';
  all_le_slice s1 lo' p' pv;   (* all_le s1 lo p pv => all_pred on the slice *)
  perm_preserves_all_pred (fun x -> le x pv) (S.slice s1 lo' p') (S.slice s2 lo' p');
  all_le_slice s2 lo' p' pv;   (* lift slice-all_pred back to indices *)
  assert (all_le s2 lo' p' pv);
  (* (2) That bound, plus [lo,p) frozen across h2->h3, gives all_le s3 lo p pv.
     [lo,p) is a sub-slice of the frozen prefix [0,p+1). *)
  assert (S.equal (S.slice s2 lo' p') (S.slice (S.slice s2 0 (p'+1)) lo' p'));
  assert (S.equal (S.slice s3 lo' p') (S.slice (S.slice s3 0 (p'+1)) lo' p'));
  assert (S.slice s2 lo' p' == S.slice s3 lo' p');
  all_le_slice s3 lo' p' pv;
  assert (all_le s3 lo' p' pv);
  (* (3) pivot frozen through both: s1[p]=pv, frozen by low recursion (index p
     is the head of the frozen suffix [p,hi)) and by high recursion (index p is
     the last element of the frozen prefix [0,p+1)). *)
  S.lemma_index_slice s1 p' n 0;          (* s1[p] = (slice s1 p n)[0] *)
  S.lemma_index_slice s2 p' n 0;          (* s2[p] = (slice s2 p n)[0] *)
  assert (S.index s2 p' == pv);
  S.lemma_index_slice s2 0 (p'+1) p';     (* s2[p] = (slice s2 0 (p+1))[p] *)
  S.lemma_index_slice s3 0 (p'+1) p';     (* s3[p] = (slice s3 0 (p+1))[p] *)
  assert (S.index s3 p' == pv);
  (* (4) High half. Across h1->h2 (low recursion) the high half [p+1,hi) is
     FROZEN (low recursion only touched [lo,p)), so it is still >= pv at h2.
     The freeze is `slice s1 p n == slice s2 p n`, which restricts to [p+1,hi). *)
  assert (S.equal (S.slice s2 (p'+1) hi')
                  (S.slice (S.slice s2 p' n) 1 (hi' - p')));
  assert (S.equal (S.slice s1 (p'+1) hi')
                  (S.slice (S.slice s1 p' n) 1 (hi' - p')));
  assert (S.slice s1 (p'+1) hi' == S.slice s2 (p'+1) hi');
  all_ge_slice s1 (p'+1) hi' pv;
  all_ge_slice s2 (p'+1) hi' pv;
  assert (all_ge s2 (p' + 1) hi' pv);
  (* Across h2->h3 (high recursion) [p+1,hi) is permuted in place => still >= pv. *)
  middle_perm s2 s3 (p' + 1) hi';
  all_ge_slice s2 (p'+1) hi' pv;
  perm_preserves_all_pred (fun x -> le pv x) (S.slice s2 (p'+1) hi') (S.slice s3 (p'+1) hi');
  all_ge_slice s3 (p'+1) hi' pv;
  assert (all_ge s3 (p' + 1) hi' pv);
  (* (5) Both halves sorted; cross bounds [lo,p) <= pv = s3[p] <= [p+1,hi).
     Assemble sorted_range over [lo,hi) by case analysis on (i,j). U32.lte is a
     total order on integers, so Z3 handles the transitivity through pv. *)
  assert (all_le s3 lo' p' pv);
  assert (all_ge s3 (p'+1) hi' pv);
  assert (S.index s3 p' == pv);
  (* low half stayed sorted: [lo,p) frozen across the high recursion h2->h3 *)
  sorted_range_frame s2 s3 lo' p';
  assert (sorted_range s3 lo' p');
  (* high half: sorted_range s3 (p+1) hi is directly from the high recursion *)
  assert (sorted_range s3 (p'+1) hi');
  let prove_pair (i:nat{lo' <= i /\ i < hi'}) (j:nat{i <= j /\ j < hi'})
    : Lemma (le (S.index s3 i) (S.index s3 j)) =
    (* i,j each lie in [lo,p), {p}, or [p+1,hi). All cross-cases route through
       s3[p]=pv with [lo,p)<=pv<=[p+1,hi). le=U32.lte is a total order, so the
       chained inequality s3[i] <= pv <= s3[j] is discharged by Z3. *)
    if j < p' then
      ()                                   (* both low: sorted_range s3 lo p *)
    else if i > p' then
      ()                                   (* both high: sorted_range s3 (p+1) hi *)
    else if i < p' && j = p' then
      assert (le (S.index s3 i) pv)        (* s3[i] <= pv = s3[p] *)
    else if i = p' && j > p' then
      assert (le pv (S.index s3 j))        (* pv = s3[p] <= s3[j] *)
    else if i = p' && j = p' then
      ()                                   (* trivial *)
    else begin                             (* i < p < j *)
      assert (le (S.index s3 i) pv);
      assert (le pv (S.index s3 j))
    end
  in
  FStar.Classical.forall_intro_2 prove_pair
#pop-options

(* -------------------------------------------------------------------------- *)
(* quicksort over the range [lo, hi).                                         *)
(*                                                                            *)
(* The two recursive calls operate on the disjoint ranges [lo, p) and         *)
(* [p+1, hi). Their disjointness is *not* a typing obligation here (the       *)
(* buffer is a single value): instead each call's `modifies (loc_buffer b)`   *)
(* plus the permutation spec is threaded through. Permutation is transitive,  *)
(* which is how the two sub-permutations compose into a whole-buffer one.     *)
(* -------------------------------------------------------------------------- *)

val quicksort (b:B.buffer elem) (lo hi:U32.t)
  : Stack unit
    (requires fun h ->
      B.live h b /\ U32.v lo <= U32.v hi /\ U32.v hi <= B.length b)
    (ensures fun h0 _ h1 ->
      B.live h1 b /\
      (* ONLY the [lo,hi) range is touched. This is the disjoint-range claim:
         when the caller sorts the *other* half, this modifies-clause is what
         proves this (already-sorted) half is left intact. In Aeneas/Idris the
         analogous fact is structural (the borrow / unique view simply does not
         alias the other half); here it is an explicit location-algebra fact. *)
      B.modifies (B.loc_buffer_from_to b lo hi) h0 h1 /\
      SP.permutation elem (contents h0 b) (contents h1 b) /\
      (* SORTEDNESS of the sorted range. *)
      sorted_range (contents h1 b) (U32.v lo) (U32.v hi))
    (decreases (U32.v hi - U32.v lo))
let rec quicksort b lo hi =
  let h0 = ST.get () in
  if U32.lt lo hi && U32.lt (U32.add lo 1ul) hi then begin
    let p = partition b lo hi in
    let h1 = ST.get () in
    let pv = b.(p) in   (* the pivot value, now parked at index p *)
    (* sort the low half [lo, p) -- disjoint from the high half *)
    quicksort b lo p;
    let h2 = ST.get () in
    (* The low recursion only touched [lo,p); the prefix [0,lo) and suffix [p,n)
       are frozen, so the pivot and the high half (still >= pv) are intact. *)
    B.loc_disjoint_loc_buffer_from_to b lo p p (B.len b);
    B.modifies_buffer_from_to_elim b p (B.len b) (B.loc_buffer_from_to b lo p) h1 h2;
    B.loc_disjoint_loc_buffer_from_to b lo p 0ul lo;
    B.modifies_buffer_from_to_elim b 0ul lo (B.loc_buffer_from_to b lo p) h1 h2;
    (* sort the high half [p+1, hi) *)
    quicksort b (U32.add p 1ul) hi;
    let h3 = ST.get () in
    (* The high recursion only touched [p+1,hi); [0,p+1) and [hi,n) frozen. *)
    B.loc_disjoint_loc_buffer_from_to b (U32.add p 1ul) hi 0ul (U32.add p 1ul);
    B.modifies_buffer_from_to_elim b 0ul (U32.add p 1ul)
      (B.loc_buffer_from_to b (U32.add p 1ul) hi) h2 h3;
    B.loc_disjoint_loc_buffer_from_to b (U32.add p 1ul) hi hi (B.len b);
    B.modifies_buffer_from_to_elim b hi (B.len b)
      (B.loc_buffer_from_to b (U32.add p 1ul) hi) h2 h3;
    (* modifies + permutation compose as before. *)
    B.loc_includes_loc_buffer_from_to b lo hi lo p;
    B.loc_includes_loc_buffer_from_to b lo hi (U32.add p 1ul) hi;
    (* Sortedness glue. The two halves are individually sorted (recursive
       ensures). The cross-half bound [lo,p) <= pv <= [p+1,hi) is preserved
       because each half's post-sort content is a permutation of its pre-sort
       content, which respected the bound (perm_preserves_all_pred on slices). *)
    sortedness_glue b lo p hi pv h1 h2 h3
  end else
    ()  (* size 0/1: modifies loc_none; trivially a sorted permutation of itself *)
