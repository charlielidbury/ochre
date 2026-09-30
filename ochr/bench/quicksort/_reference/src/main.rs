//! Sorts every case of tests.json with the reference and checks the result.
//! Usage: quicksort-reference [path/to/tests.json]

#[allow(dead_code)]
mod json;

use quicksort_reference::quicksort;

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| "../tests.json".into());
    let doc = json::parse(&std::fs::read_to_string(&path).expect("cannot read tests.json"));
    let cases = doc.field("cases").arr();
    let mut failures = 0;
    for case in cases {
        let name = case.field("name").str();
        let mut a: Vec<u64> = case.field("input").arr().iter().map(|j| j.num()).collect();
        let want: Vec<u64> = case.field("expected").arr().iter().map(|j| j.num()).collect();
        quicksort(&mut a);
        if a != want {
            failures += 1;
            println!("FAIL {name}: expected {want:?}, got {a:?}");
        }
    }
    if failures == 0 {
        println!("reference OK: {} cases, every output as expected", cases.len());
    } else {
        println!("reference FAILED: {failures} of {} cases", cases.len());
        std::process::exit(1);
    }
}
