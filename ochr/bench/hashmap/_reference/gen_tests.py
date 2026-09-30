#!/usr/bin/env python3
"""Generate ../tests.json for the hashmap benchmark.

The expected results come from Python's dict, an oracle independent of the Rust
reference in this directory (which is then checked against them by run.sh).
The pseudo-random ops use splitmix64 so the sequences can be regenerated in any
language. Run from anywhere: python3 gen_tests.py > ../tests.json
"""
import json
import sys

MASK = (1 << 64) - 1


class SplitMix64:
    def __init__(self, seed):
        self.state = seed & MASK

    def next(self):
        self.state = (self.state + 0x9E3779B97F4A7C15) & MASK
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        return z ^ (z >> 31)

    def below(self, n):
        return self.next() % n


def run(cap, script):
    """Replay (op, key, value, note) tuples on a dict, recording expected results."""
    assert cap >= 1
    m = {}
    ops = []
    for op, key, value, note in script:
        rec = {"op": op, "key": key}
        if op == "insert":
            rec["value"] = value
            rec["expect"] = m.get(key)
            m[key] = value
        elif op == "get":
            rec["expect"] = m.get(key)
        elif op == "remove":
            rec["expect"] = m.pop(key, None)
        elif op == "get_mut":
            assert key in m, f"get_mut on absent key {key}"
            rec["value"] = value
            m[key] = value
        else:
            raise ValueError(op)
        rec["len"] = len(m)
        if note:
            rec["note"] = note
        ops.append(rec)
    return ops


# The scripted sequence, on new(4). Buckets: idx(k) = k mod 4.
SCRIPTED = [
    ("get", 0, None, "empty map"),
    ("remove", 3, None, "remove from an empty map"),
    ("insert", 1, 10, "bucket 1"),
    ("insert", 5, 50, "bucket 1 again: collision"),
    ("insert", 9, 90, "bucket 1: three keys"),
    ("get", 1, None, None),
    ("get", 5, None, None),
    ("get", 9, None, None),
    ("get", 13, None, "absent key in a non-empty bucket"),
    ("get", 2, None, "absent key in an empty bucket"),
    ("insert", 5, 55, "overwrite the middle key of bucket 1; returns the old value"),
    ("get", 5, None, None),
    ("get", 1, None, "neighbours unchanged"),
    ("get", 9, None, None),
    ("insert", 0, 0, "value 0 is distinct from None"),
    ("insert", 4, 40, "collision in bucket 0"),
    ("get", 0, None, None),
    ("remove", 5, None, "remove the middle key of bucket 1"),
    ("get", 5, None, None),
    ("get", 1, None, "neighbours survive the unlink"),
    ("get", 9, None, None),
    ("remove", 5, None, "remove twice: now absent"),
    ("remove", 13, None, "remove an absent key from a non-empty bucket"),
    ("remove", 1, None, "remove the first-inserted key of bucket 1"),
    ("remove", 9, None, "bucket 1 now empty"),
    ("get", 9, None, None),
    ("get_mut", 4, 44, "write through get_mut"),
    ("get", 4, None, "get sees the write"),
    ("get", 0, None, "the other key in bucket 0 is unchanged"),
    ("get_mut", 0, 7, None),
    ("get", 0, None, None),
    ("get", 4, None, None),
    ("insert", 4, 45, "insert returns the value written through get_mut"),
    ("insert", 1, 11, "re-insert a removed key"),
    ("get", 1, None, None),
    ("insert", 7, 70, "bucket 3"),
    ("insert", 3, 30, "collision in bucket 3"),
    ("insert", 11, 99, "bucket 3: three keys"),
    ("get_mut", 3, 33, "get_mut on the middle key of bucket 3"),
    ("get", 7, None, None),
    ("get", 3, None, None),
    ("get", 11, None, None),
    ("remove", 11, None, "remove the last-inserted key of bucket 3"),
    ("get", 3, None, None),
    ("remove", 0, None, None),
    ("get", 4, None, None),
    ("remove", 4, None, "bucket 0 now empty"),
    ("get", 0, None, None),
    ("get", 4, None, None),
    ("insert", 0, 1, "re-insert into an emptied bucket"),
    ("get", 0, None, None),
]


def random_script(rng, n_ops, key_space):
    script = []
    present = set()
    for _ in range(n_ops):
        r = rng.below(100)
        key = rng.below(key_space)
        if r < 40:
            op = "insert"
        elif r < 65:
            op = "get"
        elif r < 85:
            op = "remove"
        elif present:
            op = "get_mut"
            key = sorted(present)[rng.below(len(present))]
        else:
            op = "insert"
        value = rng.below(100) if op in ("insert", "get_mut") else None
        if op == "insert":
            present.add(key)
        elif op == "remove":
            present.discard(key)
        script.append((op, key, value, None))
    return script


SEED = 20260930
RANDOM = [(1, 8), (3, 12), (4, 16), (7, 24)]  # (cap, key space)


def main():
    rng = SplitMix64(SEED)
    sequences = [{"name": "scripted", "cap": 4, "ops": run(4, SCRIPTED)}]
    for cap, key_space in RANDOM:
        sequences.append({
            "name": f"random-cap{cap}",
            "cap": cap,
            "ops": run(cap, random_script(rng, 50, key_space)),
        })
    doc = {
        "about": "Hashmap test vectors; see SPEC.md section 6. Generated by _reference/gen_tests.py "
                 f"(splitmix64, seed {SEED}); expected results from Python's dict.",
        "sequences": sequences,
    }
    sys.stdout.write(dump(doc))


def dump(doc):
    """JSON with one op per line, so the file reads and diffs well."""
    out = ['{\n  "about": ' + json.dumps(doc["about"]) + ',\n  "sequences": [\n']
    for i, seq in enumerate(doc["sequences"]):
        out.append('    {"name": %s, "cap": %d, "ops": [\n' % (json.dumps(seq["name"]), seq["cap"]))
        out.append(",\n".join("      " + json.dumps(op) for op in seq["ops"]))
        out.append("\n    ]}" + ("," if i + 1 < len(doc["sequences"]) else "") + "\n")
    out.append("  ]\n}\n")
    return "".join(out)


if __name__ == "__main__":
    main()
