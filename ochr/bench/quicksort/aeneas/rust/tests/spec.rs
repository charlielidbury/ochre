// FIXED-BEGIN tests
// Transcribed mechanically from the benchmark's test vectors (tests.json). Do not edit.
use quicksort::quicksort;

#[test]
fn empty() {
    let mut a: Vec<u64> = vec![];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![];
    assert_eq!(a, expected);
}

#[test]
fn one() {
    let mut a: Vec<u64> = vec![42];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![42];
    assert_eq!(a, expected);
}

#[test]
fn two_sorted() {
    let mut a: Vec<u64> = vec![1, 2];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![1, 2];
    assert_eq!(a, expected);
}

#[test]
fn two_reversed() {
    let mut a: Vec<u64> = vec![2, 1];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![1, 2];
    assert_eq!(a, expected);
}

#[test]
fn duplicates() {
    let mut a: Vec<u64> = vec![3, 1, 3, 2, 1, 3, 0, 2];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 1, 1, 2, 2, 3, 3, 3];
    assert_eq!(a, expected);
}

#[test]
fn sorted() {
    let mut a: Vec<u64> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    assert_eq!(a, expected);
}

#[test]
fn reverse_sorted() {
    let mut a: Vec<u64> = vec![16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    assert_eq!(a, expected);
}

#[test]
fn all_equal() {
    let mut a: Vec<u64> = vec![7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7];
    assert_eq!(a, expected);
}

#[test]
fn mixed() {
    let mut a: Vec<u64> = vec![5, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 0, 99];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 1, 1, 2, 3, 4, 5, 5, 5, 5, 6, 9, 99];
    assert_eq!(a, expected);
}

#[test]
fn random_00() {
    let mut a: Vec<u64> = vec![70, 30, 15, 26, 27, 68, 94, 48, 69, 54, 87, 20, 36, 38, 0, 67, 65, 22, 80, 20, 62, 12, 97, 53];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 12, 15, 20, 20, 22, 26, 27, 30, 36, 38, 48, 53, 54, 62, 65, 67, 68, 69, 70, 80, 87, 94, 97];
    assert_eq!(a, expected);
}

#[test]
fn random_01() {
    let mut a: Vec<u64> = vec![79, 68, 98, 29, 19, 78, 77, 1, 47, 79, 53, 91, 91, 83, 35, 41, 55, 25, 9, 96, 8, 76, 70];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![1, 8, 9, 19, 25, 29, 35, 41, 47, 53, 55, 68, 70, 76, 77, 78, 79, 79, 83, 91, 91, 96, 98];
    assert_eq!(a, expected);
}

#[test]
fn random_02() {
    let mut a: Vec<u64> = vec![];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![];
    assert_eq!(a, expected);
}

#[test]
fn random_03() {
    let mut a: Vec<u64> = vec![0, 2, 0, 3, 3, 0, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3];
    assert_eq!(a, expected);
}

#[test]
fn random_04() {
    let mut a: Vec<u64> = vec![32, 15, 81, 46, 25, 65, 74, 57, 34, 50, 96, 34];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![15, 25, 32, 34, 34, 46, 50, 57, 65, 74, 81, 96];
    assert_eq!(a, expected);
}

#[test]
fn random_05() {
    let mut a: Vec<u64> = vec![0, 3, 27, 77, 14, 37, 85, 5, 76, 0, 31, 87, 71, 11, 48, 37, 91, 56, 95, 85, 91, 71, 48];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 0, 3, 5, 11, 14, 27, 31, 37, 37, 48, 48, 56, 71, 71, 76, 77, 85, 85, 87, 91, 91, 95];
    assert_eq!(a, expected);
}

#[test]
fn random_06() {
    let mut a: Vec<u64> = vec![29];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![29];
    assert_eq!(a, expected);
}

#[test]
fn random_07() {
    let mut a: Vec<u64> = vec![1, 1, 0, 1, 0, 2, 2, 0, 3, 2, 1, 1, 2, 2, 2];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3];
    assert_eq!(a, expected);
}

#[test]
fn random_08() {
    let mut a: Vec<u64> = vec![0];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0];
    assert_eq!(a, expected);
}

#[test]
fn random_09() {
    let mut a: Vec<u64> = vec![20, 25, 25, 62, 64, 98, 39, 57, 84, 29, 30];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![20, 25, 25, 29, 30, 39, 57, 62, 64, 84, 98];
    assert_eq!(a, expected);
}

#[test]
fn random_10() {
    let mut a: Vec<u64> = vec![31, 30, 20, 2, 67, 70, 83, 63, 31, 51, 55, 13, 5, 53, 93, 57, 58, 36, 39, 93, 2, 51, 6];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![2, 2, 5, 6, 13, 20, 30, 31, 31, 36, 39, 51, 51, 53, 55, 57, 58, 63, 67, 70, 83, 93, 93];
    assert_eq!(a, expected);
}

#[test]
fn random_11() {
    let mut a: Vec<u64> = vec![1, 3, 1, 1, 1, 0];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 1, 1, 1, 1, 3];
    assert_eq!(a, expected);
}

#[test]
fn random_12() {
    let mut a: Vec<u64> = vec![32, 6, 18, 62, 15, 33, 90];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![6, 15, 18, 32, 33, 62, 90];
    assert_eq!(a, expected);
}

#[test]
fn random_13() {
    let mut a: Vec<u64> = vec![81, 92, 71, 92, 35, 19, 18, 39, 3, 12, 94, 12, 73, 40, 99, 8, 71];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![3, 8, 12, 12, 18, 19, 35, 39, 40, 71, 71, 73, 81, 92, 92, 94, 99];
    assert_eq!(a, expected);
}

#[test]
fn random_14() {
    let mut a: Vec<u64> = vec![92, 18, 32];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![18, 32, 92];
    assert_eq!(a, expected);
}

#[test]
fn random_15() {
    let mut a: Vec<u64> = vec![0, 3, 1, 1, 0, 2];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 0, 1, 1, 2, 3];
    assert_eq!(a, expected);
}

#[test]
fn random_16() {
    let mut a: Vec<u64> = vec![83, 33];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![33, 83];
    assert_eq!(a, expected);
}

#[test]
fn random_17() {
    let mut a: Vec<u64> = vec![66, 41, 59, 84, 32, 11, 27, 32, 18, 96, 77, 21, 6, 73, 80, 92, 42, 91, 40, 3, 41];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![3, 6, 11, 18, 21, 27, 32, 32, 40, 41, 41, 42, 59, 66, 73, 77, 80, 84, 91, 92, 96];
    assert_eq!(a, expected);
}

#[test]
fn random_18() {
    let mut a: Vec<u64> = vec![63, 26, 27, 90, 53, 58, 2, 13, 8, 30, 79, 39, 77, 24, 5, 32];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![2, 5, 8, 13, 24, 26, 27, 30, 32, 39, 53, 58, 63, 77, 79, 90];
    assert_eq!(a, expected);
}

#[test]
fn random_19() {
    let mut a: Vec<u64> = vec![0, 1, 0, 0, 2, 0, 0, 1, 2, 1, 3, 0, 3, 0, 0];
    quicksort(&mut a);
    let expected: Vec<u64> = vec![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3];
    assert_eq!(a, expected);
}
// FIXED-END tests
