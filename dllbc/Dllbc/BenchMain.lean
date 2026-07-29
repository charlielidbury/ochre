import Dllbc.Bench

/-! Exe entry for `lake exe bench` (the core-closure harness — see Bench.lean). -/

def main (args : List String) : IO Unit := do
  for a in (if args.isEmpty then ["sizes"] else args) do
    Dllbc.Bench.run a
