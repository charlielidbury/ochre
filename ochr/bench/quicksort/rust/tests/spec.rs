// FIXED-BEGIN tests
// Generated mechanically from the benchmark's test vectors. Do not edit.
// Each test sorts one input in place and checks it against the expected output.
use quicksort::quicksort;

#[test]
fn empty() {
    let mut a: [u64; 0] = [];
    quicksort(&mut a);
    assert_eq!(a, [0u64; 0]);
}

#[test]
fn one() {
    let mut a = [42u64];
    quicksort(&mut a);
    assert_eq!(a, [42u64]);
}

#[test]
fn two_sorted() {
    let mut a = [1u64, 2];
    quicksort(&mut a);
    assert_eq!(a, [1u64, 2]);
}

#[test]
fn two_reversed() {
    let mut a = [2u64, 1];
    quicksort(&mut a);
    assert_eq!(a, [1u64, 2]);
}

#[test]
fn duplicates() {
    let mut a = [3u64, 1, 3, 2, 1, 3, 0, 2];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 1, 1, 2, 2, 3, 3, 3]);
}

#[test]
fn sorted() {
    let mut a = [1u64, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    quicksort(&mut a);
    assert_eq!(a, [1u64, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
}

#[test]
fn reverse_sorted() {
    let mut a = [16u64, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
    quicksort(&mut a);
    assert_eq!(a, [1u64, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
}

#[test]
fn all_equal() {
    let mut a = [7u64, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7];
    quicksort(&mut a);
    assert_eq!(a, [7u64, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]);
}

#[test]
fn mixed() {
    let mut a = [5u64, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 0, 99];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 1, 1, 2, 3, 4, 5, 5, 5, 5, 6, 9, 99]);
}

#[test]
fn random_00() {
    let mut a = [70u64, 30, 15, 26, 27, 68, 94, 48, 69, 54, 87, 20, 36, 38, 0, 67, 65, 22, 80, 20, 62, 12, 97, 53];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 12, 15, 20, 20, 22, 26, 27, 30, 36, 38, 48, 53, 54, 62, 65, 67, 68, 69, 70, 80, 87, 94, 97]);
}

#[test]
fn random_01() {
    let mut a = [79u64, 68, 98, 29, 19, 78, 77, 1, 47, 79, 53, 91, 91, 83, 35, 41, 55, 25, 9, 96, 8, 76, 70];
    quicksort(&mut a);
    assert_eq!(a, [1u64, 8, 9, 19, 25, 29, 35, 41, 47, 53, 55, 68, 70, 76, 77, 78, 79, 79, 83, 91, 91, 96, 98]);
}

#[test]
fn random_02() {
    let mut a: [u64; 0] = [];
    quicksort(&mut a);
    assert_eq!(a, [0u64; 0]);
}

#[test]
fn random_03() {
    let mut a = [0u64, 2, 0, 3, 3, 0, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3]);
}

#[test]
fn random_04() {
    let mut a = [32u64, 15, 81, 46, 25, 65, 74, 57, 34, 50, 96, 34];
    quicksort(&mut a);
    assert_eq!(a, [15u64, 25, 32, 34, 34, 46, 50, 57, 65, 74, 81, 96]);
}

#[test]
fn random_05() {
    let mut a = [0u64, 3, 27, 77, 14, 37, 85, 5, 76, 0, 31, 87, 71, 11, 48, 37, 91, 56, 95, 85, 91, 71, 48];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 0, 3, 5, 11, 14, 27, 31, 37, 37, 48, 48, 56, 71, 71, 76, 77, 85, 85, 87, 91, 91, 95]);
}

#[test]
fn random_06() {
    let mut a = [29u64];
    quicksort(&mut a);
    assert_eq!(a, [29u64]);
}

#[test]
fn random_07() {
    let mut a = [1u64, 1, 0, 1, 0, 2, 2, 0, 3, 2, 1, 1, 2, 2, 2];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3]);
}

#[test]
fn random_08() {
    let mut a = [0u64];
    quicksort(&mut a);
    assert_eq!(a, [0u64]);
}

#[test]
fn random_09() {
    let mut a = [20u64, 25, 25, 62, 64, 98, 39, 57, 84, 29, 30];
    quicksort(&mut a);
    assert_eq!(a, [20u64, 25, 25, 29, 30, 39, 57, 62, 64, 84, 98]);
}

#[test]
fn random_10() {
    let mut a = [31u64, 30, 20, 2, 67, 70, 83, 63, 31, 51, 55, 13, 5, 53, 93, 57, 58, 36, 39, 93, 2, 51, 6];
    quicksort(&mut a);
    assert_eq!(a, [2u64, 2, 5, 6, 13, 20, 30, 31, 31, 36, 39, 51, 51, 53, 55, 57, 58, 63, 67, 70, 83, 93, 93]);
}

#[test]
fn random_11() {
    let mut a = [1u64, 3, 1, 1, 1, 0];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 1, 1, 1, 1, 3]);
}

#[test]
fn random_12() {
    let mut a = [32u64, 6, 18, 62, 15, 33, 90];
    quicksort(&mut a);
    assert_eq!(a, [6u64, 15, 18, 32, 33, 62, 90]);
}

#[test]
fn random_13() {
    let mut a = [81u64, 92, 71, 92, 35, 19, 18, 39, 3, 12, 94, 12, 73, 40, 99, 8, 71];
    quicksort(&mut a);
    assert_eq!(a, [3u64, 8, 12, 12, 18, 19, 35, 39, 40, 71, 71, 73, 81, 92, 92, 94, 99]);
}

#[test]
fn random_14() {
    let mut a = [92u64, 18, 32];
    quicksort(&mut a);
    assert_eq!(a, [18u64, 32, 92]);
}

#[test]
fn random_15() {
    let mut a = [0u64, 3, 1, 1, 0, 2];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 0, 1, 1, 2, 3]);
}

#[test]
fn random_16() {
    let mut a = [83u64, 33];
    quicksort(&mut a);
    assert_eq!(a, [33u64, 83]);
}

#[test]
fn random_17() {
    let mut a = [66u64, 41, 59, 84, 32, 11, 27, 32, 18, 96, 77, 21, 6, 73, 80, 92, 42, 91, 40, 3, 41];
    quicksort(&mut a);
    assert_eq!(a, [3u64, 6, 11, 18, 21, 27, 32, 32, 40, 41, 41, 42, 59, 66, 73, 77, 80, 84, 91, 92, 96]);
}

#[test]
fn random_18() {
    let mut a = [63u64, 26, 27, 90, 53, 58, 2, 13, 8, 30, 79, 39, 77, 24, 5, 32];
    quicksort(&mut a);
    assert_eq!(a, [2u64, 5, 8, 13, 24, 26, 27, 30, 32, 39, 53, 58, 63, 77, 79, 90]);
}

#[test]
fn random_19() {
    let mut a = [0u64, 1, 0, 0, 2, 0, 0, 1, 2, 1, 3, 0, 3, 0, 0];
    quicksort(&mut a);
    assert_eq!(a, [0u64, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3]);
}

// FIXED-END tests
