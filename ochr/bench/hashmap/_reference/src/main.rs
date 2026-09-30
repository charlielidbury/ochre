//! Runs every op of tests.json against the reference and checks each expected
//! result and length. Usage: hashmap-reference [path/to/tests.json]

mod json;

use hashmap_reference::HashMap;

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| "../tests.json".into());
    let doc = json::parse(&std::fs::read_to_string(&path).expect("cannot read tests.json"));
    let (mut ops, mut failures) = (0, 0);
    for seq in doc.field("sequences").arr() {
        let name = seq.field("name").str();
        // The tests instantiate V := u64 (SPEC §6).
        let mut m: HashMap<u64> = HashMap::new(seq.field("cap").num());
        for (i, op) in seq.field("ops").arr().iter().enumerate() {
            let key = op.field("key").num();
            let kind = op.field("op").str();
            let got = match kind {
                "insert" => Some(m.insert(key, op.field("value").num())),
                "get" => Some(m.get(key).copied()),
                "remove" => Some(m.remove(key)),
                "get_mut" => {
                    *m.get_mut(key) = op.field("value").num();
                    None
                }
                other => panic!("{name}[{i}]: unknown op {other:?}"),
            };
            ops += 1;
            if let Some(got) = got {
                let want = op.field("expect").opt_num();
                if got != want {
                    failures += 1;
                    println!("FAIL {name}[{i}] {kind}({key}): expected {want:?}, got {got:?}");
                }
            }
            let want_len = op.field("len").num();
            if m.len() != want_len {
                failures += 1;
                println!("FAIL {name}[{i}] {kind}({key}): expected len {want_len}, got {}", m.len());
            }
        }
    }
    if failures == 0 {
        println!("reference OK: {ops} ops, every result and length as expected");
    } else {
        println!("reference FAILED: {failures} mismatches over {ops} ops");
        std::process::exit(1);
    }
}
