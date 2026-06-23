/// arranges arr into
/// [<p, ...] ++ [p] ++ [>=p, ...]
fn partition(arr: &mut [i32]) -> usize {
    let p = arr[arr.len() - 1];

    let mut lo = 0; // index of first element NOT in low range
    for hi in 0..arr.len() - 1 {
        if arr[hi] < p {
            // hi is in the wrong place
            // move it into the low region

            //arr.swap(hi, lo);
            let tmp = arr[hi];
            arr[hi] = arr[lo];
            arr[lo] = tmp;

            lo += 1;
        }
    }

    // arrr = [<p, ...] ++ [>=p, ...] ++ [p]
    let pivot = arr[arr.len() - 1];
    arr[arr.len() - 1] = arr[lo];
    arr[lo] = pivot;
    // arrr = [<p, ...] ++ [p] ++ [>=p, ...]

    lo
}

fn quicksort(arr: &mut [i32]) {
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

fn main() {
    let mut v: Vec<i32> = vec![4, 31, 22, 1, 12];
    println!("{:?}", &v);
    quicksort(&mut v);
    println!("{:?}", v);
}
