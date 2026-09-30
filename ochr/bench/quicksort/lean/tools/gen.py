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
NS = "Bench"

HEADER_TESTS = """\
-- FIXED-BEGIN tests
import Solution

/-!
Generated mechanically from the benchmark's test vectors. Do not edit.

Each case (see ASSIGNMENT.md) sorts its input with `quicksort` and checks the
result against the expected output.
-/
"""

FOOTER_TESTS = """\
def main : IO UInt32 := do
  let mut failed := 0
  for (name, input, expected) in benchCases do
    let got := Bench.quicksort input
    if got == expected then
      IO.println s!"PASS {name}"
    else
      failed := failed + 1
      IO.println s!"FAIL {name}: quicksort {input} = {got}, expected {expected}"
  IO.println s!"tests: {benchCases.length - failed}/{benchCases.length} cases passed"
  return if failed == 0 then 0 else 1
-- FIXED-END tests
"""


def arr(xs):
    return "#[" + ", ".join(str(x) for x in xs) + "]"


def gen_tests():
    doc = json.loads(SPEC_TESTS.read_text())
    out = [HEADER_TESTS, "\ndef benchCases : List (String × Array UInt64 × Array UInt64) := [\n"]
    out.append(",\n".join(f"  ({json.dumps(c['name'])}, {arr(c['input'])},\n    {arr(c['expected'])})"
                          for c in doc["cases"]) + "]\n\n")
    out.append(FOOTER_TESTS)
    (PKG / "Tests.lean").write_text("".join(out))
    print(f"wrote Tests.lean: {len(doc['cases'])} cases")


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

open Bench

-- defs: the FIXED definitions of `sorted`, `count` and `perm`, restated
example : sorted = fun (a : Array UInt64) =>
    ∀ (i j : Nat) (hij : i < j) (hj : j < a.size), a[i]'(Nat.lt_trans hij hj) ≤ a[j] :=
  rfl
example : ∀ (x : UInt64), count x [] = 0 :=
  fun _ => rfl
example : ∀ (x y : UInt64) (ys : List UInt64), count x (y :: ys) = (if y = x then 1 else 0) + count x ys :=
  fun _ _ _ => rfl
example : perm = fun (a b : Array UInt64) => ∀ x : UInt64, count x a.toList = count x b.toList :=
  rfl
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
