-- FIXED-BEGIN tests
import Solution

/-!
Generated mechanically from the benchmark's test vectors. Do not edit.

Each sequence of operations (see ASSIGNMENT.md) starts from `HashMap.new cap`
and applies its ops in order to one map, with values of type `UInt64`
(`V := UInt64`), checking the result of every op and `len` after it. An op is `(kind, key, value, expected result, expected len)`;
`get_mut k w` is run as `modify k w`, the pure counterpart of writing `w`
through `get_mut`.
-/

/-- Replays `ops` on `HashMap.new cap` and returns one message per mismatch. -/
def benchRunSequence (cap : UInt64)
    (ops : List (String × UInt64 × UInt64 × Option UInt64 × UInt64)) : Array String := Id.run do
  let mut m : Bench.HashMap UInt64 := Bench.HashMap.new cap
  let mut errs : Array String := #[]
  let mut i := 0
  for (kind, k, v, e, len) in ops do
    if kind == "insert" then
      let (m', r) := m.insert k v
      m := m'
      if r != e then errs := errs.push s!"op {i}: insert({k}, {v}) returned {r}, expected {e}"
    else if kind == "get" then
      let r := m.get k
      if r != e then errs := errs.push s!"op {i}: get({k}) returned {r}, expected {e}"
    else if kind == "remove" then
      let (m', r) := m.remove k
      m := m'
      if r != e then errs := errs.push s!"op {i}: remove({k}) returned {r}, expected {e}"
    else
      m := m.modify k v
    if m.len != len then errs := errs.push s!"op {i}: len is {m.len} after the op, expected {len}"
    i := i + 1
  return errs

def benchSeq_scripted : List (String × UInt64 × UInt64 × Option UInt64 × UInt64) := [  ("get", 0, 0, none, 0),
  ("remove", 3, 0, none, 0),
  ("insert", 1, 10, none, 1),
  ("insert", 5, 50, none, 2),
  ("insert", 9, 90, none, 3),
  ("get", 1, 0, some 10, 3),
  ("get", 5, 0, some 50, 3),
  ("get", 9, 0, some 90, 3),
  ("get", 13, 0, none, 3),
  ("get", 2, 0, none, 3),
  ("insert", 5, 55, some 50, 3),
  ("get", 5, 0, some 55, 3),
  ("get", 1, 0, some 10, 3),
  ("get", 9, 0, some 90, 3),
  ("insert", 0, 0, none, 4),
  ("insert", 4, 40, none, 5),
  ("get", 0, 0, some 0, 5),
  ("remove", 5, 0, some 55, 4),
  ("get", 5, 0, none, 4),
  ("get", 1, 0, some 10, 4),
  ("get", 9, 0, some 90, 4),
  ("remove", 5, 0, none, 4),
  ("remove", 13, 0, none, 4),
  ("remove", 1, 0, some 10, 3),
  ("remove", 9, 0, some 90, 2),
  ("get", 9, 0, none, 2),
  ("get_mut", 4, 44, none, 2),
  ("get", 4, 0, some 44, 2),
  ("get", 0, 0, some 0, 2),
  ("get_mut", 0, 7, none, 2),
  ("get", 0, 0, some 7, 2),
  ("get", 4, 0, some 44, 2),
  ("insert", 4, 45, some 44, 2),
  ("insert", 1, 11, none, 3),
  ("get", 1, 0, some 11, 3),
  ("insert", 7, 70, none, 4),
  ("insert", 3, 30, none, 5),
  ("insert", 11, 99, none, 6),
  ("get_mut", 3, 33, none, 6),
  ("get", 7, 0, some 70, 6),
  ("get", 3, 0, some 33, 6),
  ("get", 11, 0, some 99, 6),
  ("remove", 11, 0, some 99, 5),
  ("get", 3, 0, some 33, 5),
  ("remove", 0, 0, some 7, 4),
  ("get", 4, 0, some 45, 4),
  ("remove", 4, 0, some 45, 3),
  ("get", 0, 0, none, 3),
  ("get", 4, 0, none, 3),
  ("insert", 0, 1, none, 4),
  ("get", 0, 0, some 1, 4)]

def benchSeq_random_cap1 : List (String × UInt64 × UInt64 × Option UInt64 × UInt64) := [  ("remove", 2, 0, none, 0),
  ("insert", 2, 27, none, 1),
  ("remove", 2, 0, some 27, 0),
  ("get", 1, 0, none, 0),
  ("get", 3, 0, none, 0),
  ("insert", 0, 38, none, 1),
  ("insert", 7, 65, none, 2),
  ("insert", 4, 20, none, 3),
  ("get", 4, 0, some 20, 3),
  ("get_mut", 7, 79, none, 3),
  ("remove", 2, 0, none, 3),
  ("insert", 7, 78, some 79, 3),
  ("remove", 1, 0, none, 3),
  ("get", 7, 0, some 78, 3),
  ("get", 7, 0, some 78, 3),
  ("get_mut", 0, 41, none, 3),
  ("get", 5, 0, none, 3),
  ("insert", 0, 8, some 41, 3),
  ("remove", 6, 0, none, 3),
  ("insert", 2, 8, none, 4),
  ("get", 4, 0, some 20, 4),
  ("get", 7, 0, some 78, 4),
  ("remove", 6, 0, none, 4),
  ("get_mut", 4, 86, none, 4),
  ("get", 5, 0, none, 4),
  ("insert", 1, 19, none, 5),
  ("insert", 2, 12, some 8, 5),
  ("insert", 7, 81, some 78, 5),
  ("get", 5, 0, none, 5),
  ("remove", 6, 0, none, 5),
  ("get", 2, 0, some 12, 5),
  ("get", 0, 0, some 8, 5),
  ("insert", 4, 0, some 86, 5),
  ("insert", 7, 77, some 81, 5),
  ("insert", 5, 85, none, 6),
  ("insert", 0, 0, some 8, 6),
  ("insert", 3, 71, none, 7),
  ("insert", 0, 37, some 0, 7),
  ("get_mut", 4, 85, none, 7),
  ("get_mut", 2, 26, none, 7),
  ("insert", 3, 5, some 71, 7),
  ("insert", 0, 37, some 37, 7),
  ("remove", 6, 0, none, 7),
  ("insert", 0, 71, some 37, 7),
  ("insert", 5, 9, some 85, 7),
  ("insert", 2, 42, some 26, 7),
  ("insert", 0, 11, some 71, 7),
  ("insert", 1, 25, some 19, 7),
  ("get", 0, 0, some 11, 7),
  ("get_mut", 0, 84, none, 7)]

def benchSeq_random_cap3 : List (String × UInt64 × UInt64 × Option UInt64 × UInt64) := [  ("insert", 6, 48, none, 1),
  ("insert", 2, 20, none, 2),
  ("insert", 3, 70, none, 3),
  ("remove", 11, 0, none, 3),
  ("insert", 11, 55, none, 4),
  ("insert", 5, 53, none, 5),
  ("get_mut", 6, 36, none, 5),
  ("insert", 5, 2, some 53, 5),
  ("get", 10, 0, none, 5),
  ("remove", 5, 0, some 2, 4),
  ("insert", 1, 97, none, 5),
  ("insert", 0, 57, none, 6),
  ("insert", 6, 18, some 36, 6),
  ("get", 3, 0, some 70, 6),
  ("insert", 2, 42, some 20, 6),
  ("remove", 0, 0, some 57, 5),
  ("remove", 0, 0, none, 5),
  ("insert", 3, 18, some 70, 5),
  ("insert", 7, 12, none, 6),
  ("get_mut", 6, 40, none, 6),
  ("get_mut", 2, 53, none, 6),
  ("get_mut", 3, 31, none, 6),
  ("get", 7, 0, some 12, 6),
  ("insert", 9, 60, none, 7),
  ("insert", 8, 83, none, 8),
  ("insert", 7, 66, some 12, 8),
  ("get", 11, 0, some 55, 8),
  ("remove", 8, 0, some 83, 7),
  ("insert", 11, 32, some 55, 7),
  ("insert", 8, 77, none, 8),
  ("insert", 10, 73, none, 9),
  ("remove", 0, 0, none, 9),
  ("get", 11, 0, some 32, 9),
  ("get", 7, 0, some 66, 9),
  ("get", 4, 0, none, 9),
  ("get", 2, 0, some 53, 9),
  ("insert", 2, 53, some 53, 9),
  ("get", 2, 0, some 53, 9),
  ("insert", 4, 30, none, 10),
  ("remove", 11, 0, some 32, 9),
  ("remove", 0, 0, none, 9),
  ("insert", 0, 15, none, 10),
  ("insert", 1, 20, some 97, 10),
  ("insert", 10, 20, some 73, 10),
  ("insert", 5, 90, none, 11),
  ("remove", 7, 0, some 66, 10),
  ("get_mut", 4, 40, none, 10),
  ("get", 11, 0, none, 10),
  ("insert", 3, 75, some 31, 10),
  ("insert", 0, 29, some 15, 10)]

def benchSeq_random_cap4 : List (String × UInt64 × UInt64 × Option UInt64 × UInt64) := [  ("insert", 3, 6, none, 1),
  ("get_mut", 3, 19, none, 1),
  ("insert", 1, 39, none, 2),
  ("get_mut", 1, 3, none, 2),
  ("get_mut", 3, 73, none, 2),
  ("get", 1, 0, some 3, 2),
  ("insert", 12, 39, none, 3),
  ("insert", 3, 19, some 73, 3),
  ("insert", 7, 84, none, 4),
  ("get", 12, 0, some 39, 4),
  ("remove", 2, 0, none, 4),
  ("insert", 0, 26, none, 5),
  ("insert", 2, 10, none, 6),
  ("insert", 5, 40, none, 7),
  ("get_mut", 5, 86, none, 7),
  ("get", 4, 0, none, 7),
  ("get", 12, 0, some 39, 7),
  ("insert", 1, 59, some 3, 7),
  ("get", 4, 0, none, 7),
  ("get", 8, 0, none, 7),
  ("remove", 15, 0, none, 7),
  ("insert", 15, 68, none, 8),
  ("insert", 11, 80, none, 9),
  ("get", 10, 0, none, 9),
  ("remove", 4, 0, none, 9),
  ("insert", 13, 20, none, 10),
  ("insert", 9, 7, none, 11),
  ("get_mut", 5, 30, none, 11),
  ("get", 1, 0, some 59, 11),
  ("remove", 4, 0, none, 11),
  ("remove", 10, 0, none, 11),
  ("get", 13, 0, some 20, 11),
  ("remove", 9, 0, some 7, 10),
  ("get_mut", 7, 75, none, 10),
  ("get", 8, 0, none, 10),
  ("remove", 11, 0, some 80, 9),
  ("get_mut", 1, 32, none, 9),
  ("get", 6, 0, none, 9),
  ("get", 11, 0, none, 9),
  ("get", 4, 0, none, 9),
  ("remove", 6, 0, none, 9),
  ("insert", 8, 82, none, 10),
  ("insert", 3, 86, some 19, 10),
  ("get", 12, 0, some 39, 10),
  ("get_mut", 7, 17, none, 10),
  ("get", 10, 0, none, 10),
  ("get", 12, 0, some 39, 10),
  ("remove", 4, 0, none, 10),
  ("insert", 7, 79, some 17, 10),
  ("remove", 2, 0, some 10, 9)]

def benchSeq_random_cap7 : List (String × UInt64 × UInt64 × Option UInt64 × UInt64) := [  ("insert", 10, 82, none, 1),
  ("insert", 15, 33, none, 2),
  ("insert", 0, 14, none, 3),
  ("insert", 8, 60, none, 4),
  ("get", 4, 0, none, 4),
  ("get_mut", 0, 39, none, 4),
  ("get", 3, 0, none, 4),
  ("insert", 19, 57, none, 5),
  ("remove", 15, 0, some 33, 4),
  ("insert", 13, 82, none, 5),
  ("remove", 18, 0, none, 5),
  ("remove", 0, 0, some 39, 4),
  ("get", 13, 0, some 82, 4),
  ("insert", 5, 37, none, 5),
  ("insert", 7, 48, none, 6),
  ("remove", 7, 0, some 48, 5),
  ("insert", 23, 31, none, 6),
  ("get_mut", 19, 27, none, 6),
  ("get", 1, 0, none, 6),
  ("remove", 3, 0, none, 6),
  ("insert", 11, 18, none, 7),
  ("insert", 5, 67, some 37, 7),
  ("insert", 20, 96, none, 8),
  ("get", 12, 0, none, 8),
  ("get", 15, 0, none, 8),
  ("get", 5, 0, some 67, 8),
  ("remove", 9, 0, none, 8),
  ("insert", 13, 87, some 82, 8),
  ("get", 19, 0, some 27, 8),
  ("get_mut", 11, 84, none, 8),
  ("get", 16, 0, none, 8),
  ("insert", 3, 78, none, 9),
  ("remove", 4, 0, none, 9),
  ("get_mut", 20, 89, none, 9),
  ("get", 0, 0, none, 9),
  ("insert", 23, 28, some 31, 9),
  ("insert", 20, 74, some 89, 9),
  ("remove", 5, 0, some 67, 8),
  ("insert", 19, 32, some 27, 8),
  ("remove", 9, 0, none, 8),
  ("insert", 11, 98, some 84, 8),
  ("remove", 13, 0, some 87, 7),
  ("remove", 11, 0, some 98, 6),
  ("get", 15, 0, none, 6),
  ("get", 11, 0, none, 6),
  ("get_mut", 3, 16, none, 6),
  ("get", 13, 0, none, 6),
  ("get_mut", 19, 17, none, 6),
  ("get", 5, 0, none, 6),
  ("remove", 14, 0, none, 6)]

def benchSequences : List (String × UInt64 × List (String × UInt64 × UInt64 × Option UInt64 × UInt64)) := [
  ("scripted", 4, benchSeq_scripted),
  ("random-cap1", 1, benchSeq_random_cap1),
  ("random-cap3", 3, benchSeq_random_cap3),
  ("random-cap4", 4, benchSeq_random_cap4),
  ("random-cap7", 7, benchSeq_random_cap7)]

def main : IO UInt32 := do
  let mut failed := 0
  for (name, cap, ops) in benchSequences do
    let errs := benchRunSequence cap ops
    if errs.isEmpty then
      IO.println s!"PASS {name} ({ops.length} ops)"
    else
      failed := failed + 1
      IO.println s!"FAIL {name}"
      for e in errs do IO.println s!"  {e}"
  IO.println s!"tests: {benchSequences.length - failed}/{benchSequences.length} sequences passed"
  return if failed == 0 then 0 else 1
-- FIXED-END tests
