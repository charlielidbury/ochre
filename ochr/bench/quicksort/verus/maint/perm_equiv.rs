//! Maintainer check (not copied into sandboxes): the skeleton's `perm`, stated with vstd
//! multisets, is SPEC's count-based `perm`. Run: `verus maint/perm_equiv.rs`.
use vstd::prelude::*;

verus! {

/// SPEC section 4: `count(x, a)`, the number of positions of `a` holding `x`, by
/// recursion over the positions.
pub open spec fn count(x: u64, s: Seq<u64>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(x, s.drop_last()) + if s.last() == x { 1nat } else { 0nat }
    }
}

/// SPEC section 4: `perm(a, b)`, every word occurs equally often.
pub open spec fn spec_perm(a: Seq<u64>, b: Seq<u64>) -> bool {
    forall|x: u64| count(x, a) == count(x, b)
}

/// The skeleton's FIXED `perm` (src/quicksort.rs), verbatim.
pub open spec fn perm(a: Seq<u64>, b: Seq<u64>) -> bool {
    a.to_multiset() == b.to_multiset()
}

proof fn lemma_multiset_count(x: u64, s: Seq<u64>)
    ensures
        s.to_multiset().count(x) == count(x, s),
    decreases s.len(),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;

    if s.len() > 0 {
        lemma_multiset_count(x, s.drop_last());
        assert(s =~= s.drop_last().push(s.last()));
    }
}

proof fn perm_is_spec_perm(a: Seq<u64>, b: Seq<u64>)
    ensures
        perm(a, b) <==> spec_perm(a, b),
{
    if spec_perm(a, b) {
        assert forall|x: u64| a.to_multiset().count(x) == b.to_multiset().count(x) by {
            lemma_multiset_count(x, a);
            lemma_multiset_count(x, b);
        }
        assert(a.to_multiset() =~= b.to_multiset());
    }
    if perm(a, b) {
        assert forall|x: u64| count(x, a) == count(x, b) by {
            lemma_multiset_count(x, a);
            lemma_multiset_count(x, b);
        }
    }
}

fn main() {
}

} // verus!
