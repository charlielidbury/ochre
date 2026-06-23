use vstd::prelude::*;

verus! {

/// arranges arr into
/// [<p, ...] ++ [p] ++ [>=p, ...]
fn partition(arr: &mut [i32]) -> (pivot: usize)
    requires arr.len() >= 1
    ensures
        0 <= pivot < final(arr).len(),
        final(arr).len() == old(arr).len()
{
    let p = arr[arr.len() - 1];

    let mut lo = 0; // index of first element NOT in low range
    let mut hi = 0;
    while hi < arr.len() - 1
        invariant
            lo <= hi < arr.len(),
            arr.len() == old(arr).len()
        decreases arr.len() - hi,
    {
        if arr[hi] < p {
            // hi is in the wrong place
            // move it into the low region
            let tmp = arr[hi]; //arr.swap(hi, lo);
            arr[hi] = arr[lo];
            arr[lo] = tmp;

            lo += 1;
        }
        hi += 1;
    }

    // arr = [<p, ...] ++ [>=p, ...] ++ [p]
    let pivot = arr[arr.len() - 1]; //arr.swap(arr.len() - 1, lo);
    arr[arr.len() - 1] = arr[lo];
    arr[lo] = pivot;
    // arr = [<p, ...] ++ [p] ++ [>=p, ...]

    lo
}


fn quicksort(arr: &mut [i32])
    decreases arr.len()
{
    if arr.len() <= 1 {
        return;
    }

    // Subdivide `arr` into `lo` and `hi`
    let p = partition(arr);
    let (lo, p_hi) = arr.split_at_mut(p);
    let (_p, hi) = p_hi.split_at_mut(1);

    // Sort each half
    quicksort(lo);
    quicksort(hi);
}

}

fn main() {
    let mut v: Vec<i32> = vec![4, 31, 22, 1, 12];
    println!("{:?}", &v);
    quicksort(&mut v);
    println!("{:?}", v);
}
