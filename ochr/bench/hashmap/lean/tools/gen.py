#!/usr/bin/env python3
"""Generate the two whole-file FIXED modules of this package.

- Tests.lean: ../../tests.json transcribed into Lean data, plus the runner
  (`lake env lean --run Tests.lean`).
- Check.lean: every FIXED definition and theorem of Solution.lean restated from
  its FIXED text in a fresh module, as `example : <statement> := @<name>`, plus
  an axiom check and a check that the solution declares no global instance
  about existing types.

Both files stay at the top level and never enter a namespace (not even through
a dotted `def A.b`): a solution can put declarations into any namespace, and a
name it declares there would silently shadow a name the grader's text uses.
Check.lean *opens* the skeleton's namespaces instead, so such a shadow makes
the restatement ambiguous, an error. Tests.lean opens nothing and names the
solution's declarations in full.

Run from anywhere: python3 tools/gen.py. Run it only on the pristine skeleton.
"""
import json
import pathlib
import re

PKG = pathlib.Path(__file__).resolve().parent.parent
SPEC_TESTS = PKG.parent / "tests.json"
NS = "Bench.HashMap"

HEADER_TESTS = """\
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
"""

FOOTER_TESTS = """\
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
"""

OP_TYPE = "List (String × UInt64 × UInt64 × Option UInt64 × UInt64)"


def opt(x):
    return "none" if x is None else f"some {x}"


def gen_tests():
    doc = json.loads(SPEC_TESTS.read_text())
    out = [HEADER_TESTS]
    names = []
    for seq in doc["sequences"]:
        ident = "benchSeq_" + seq["name"].replace("-", "_")
        names.append((seq["name"], seq["cap"], ident))
        out.append(f"\ndef {ident} : {OP_TYPE} := [")
        rows = []
        for op in seq["ops"]:
            kind = op["op"]
            if kind not in ("insert", "get", "remove", "get_mut"):
                raise ValueError(kind)
            value = op.get("value", 0)
            expect = opt(op.get("expect")) if kind != "get_mut" else "none"
            rows.append(f"  ({json.dumps(kind)}, {op['key']}, {value}, {expect}, {op['len']})")
        out.append(",\n".join(rows) + "]\n")
    out.append(f"\ndef benchSequences : List (String × UInt64 × {OP_TYPE}) := [\n")
    out.append(",\n".join(f"  ({json.dumps(n)}, {c}, {i})" for n, c, i in names) + "]\n\n")
    out.append(FOOTER_TESTS)
    (PKG / "Tests.lean").write_text("".join(out))
    print(f"wrote Tests.lean: {len(names)} sequences, {sum(len(s['ops']) for s in doc['sequences'])} ops")


REGION = re.compile(r"^-- FIXED-BEGIN (\S+)\n(.*?)^-- FIXED-END \1\n", re.S | re.M)
THEOREM = re.compile(r"^theorem (\S+) :(.*):=\s*$", re.S | re.M)

HEADER_CHECK = """\
-- FIXED-BEGIN check
import Solution

/-!
Generated mechanically from the FIXED regions of Solution.lean. Do not edit.
`lake build Check` (run by grade.sh) fails unless the FIXED definitions of
Solution.lean are the ones restated here, the solution declares no global
instance about existing types and no axiom, opaque constant or meta code, and
every FIXED theorem of Solution.lean

1. proves exactly its FIXED statement, restated here in a fresh module, and
2. depends on no axioms other than `propext`, `Classical.choice` and
   `Quot.sound` (so no `sorry`, no `axiom`, no `native_decide`).

This file opens the skeleton's namespaces rather than entering them: a
declaration of the solution that shadows a name used below makes the
restatement ambiguous, which is an error, instead of changing its meaning.
-/

open Lean Elab Command in
/-- `#assert_axioms n` fails if the constant `n` depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. -/
elab "#assert_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound])
  if bad.isEmpty then
    logInfo m!"{n}: ok, axioms {axs.toList}"
  else
    throwError "{n} depends on disallowed axioms {bad.toList}"

open Lean Elab Command in
/-- `#assert_no_solution_instances` fails if a module of the solution declares
a global instance that could apply to an existing type (say `LE UInt64`): one
could change what a FIXED statement means here. An instance is allowed only if
one of its class arguments, reduced at the transparency instance search uses,
still mentions an inductive type or structure the solution declares; that
covers the instances Lean generates for a new type (`SizeOf`, `deriving`), and
no abbreviation or other reducible definition can make it apply to an existing
type. -/
elab "#assert_no_solution_instances" : command => do
  let env ← getEnv
  let fromSolution (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some idx => (`Solution).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  let isSolutionType (c : Name) : Bool :=
    fromSolution c && (env.find? c).any (· matches .inductInfo _)
  let mut bad := #[]
  for (n, _) in (Meta.instanceExtension.getState env).instanceNames.toList do
    if fromSolution n then
      let some info := env.find? n | continue
      let ok ← liftTermElabM <| Meta.forallTelescopeReducing info.type fun _ body =>
        body.getAppArgs.anyM fun a => do
          let a ← Meta.withTransparency .instances <| Meta.reduce a (skipTypes := false)
          return a.getUsedConstants.any isSolutionType
      unless ok do
        bad := bad.push n
  unless bad.isEmpty do
    throwError "the solution declares instances that could apply to existing types: {bad.toList}"

open Lean Elab Command in
/-- `#assert_no_solution_meta` fails if a module of the solution declares an
axiom or an opaque constant, or a constant whose type mentions the elaborator,
the environment, the kernel, the parser or `IO`: meta code could add
declarations the kernel never checked. (`leanchecker`, run by grade.sh, replays
the solution through the kernel as well.) -/
elab "#assert_no_solution_meta" : command => do
  let env ← getEnv
  let metaPrefixes := [`Lean.Elab, `Lean.Meta, `Lean.Environment, `Lean.Kernel, `Lean.Parser,
    `Lean.Syntax, `Lean.Macro, `Lean.Core, `Lean.Declaration, `Lean.ConstantInfo, `Lean.Compiler,
    `IO, `EIO, `BaseIO, `EStateM]
  let mut bad := #[]
  for i in [0:env.header.moduleNames.size] do
    unless (`Solution).isPrefixOf env.header.moduleNames[i]! do continue
    for n in env.header.moduleData[i]!.constNames do
      let some info := env.find? n | continue
      let isMeta := info.type.getUsedConstants.any (fun c => metaPrefixes.any (·.isPrefixOf c))
      if info.isAxiom || info matches .opaqueInfo _ || isMeta then
        bad := bad.push n
  unless bad.isEmpty do
    throwError "the solution declares axioms, opaque constants or meta code: {bad.toList}"

#assert_no_solution_instances
#assert_no_solution_meta

open Bench Bench.HashMap

-- repr: the FIXED representation and `idx`, restated
example : ∀ {V : Type}, Array (List (UInt64 × V)) → UInt64 → HashMap V := @HashMap.mk
example : ∀ {V : Type} (m : HashMap V) (k : UInt64), m.idx k = k.toNat % m.slots.size :=
  fun _ _ => rfl
"""

FOOTER_CHECK = """\
-- FIXED-END check
"""


def gen_check():
    src = (PKG / "Solution.lean").read_text()
    out = [HEADER_CHECK]
    n = 0
    for rid, body in REGION.findall(src):
        m = THEOREM.search(body)
        if not m:
            continue
        name, stmt = m.group(1), m.group(2).strip()
        out.append(f"\n-- {rid}\nexample : {stmt} :=\n  @{NS}.{name}\n#assert_axioms {NS}.{name}\n")
        n += 1
    out.append("\n" + FOOTER_CHECK)
    (PKG / "Check.lean").write_text("".join(out))
    print(f"wrote Check.lean: {n} theorems")


if __name__ == "__main__":
    gen_tests()
    gen_check()
