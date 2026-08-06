import Dllbc

/-!
# Phase C measurement harness — does repeated stdlib normalization cost anything?

Not a test. A compiled `lean_exe` so `perf(1)` can attribute time to symbols, per
the house rule that a cache is designed only after a profile (M22's four
architected cache layers measured wash-to-regression; `perf` on a compiled exe
then found the real hotspot in one run).

What it reports, in the order the question needs answering:

 1. **The static cost.** `Dllbc.Std` reifies its library by INLINING: `LeFnT` is
    `toTerm LeFn`, the whole definition body as a `Term`, so every `Le a b` in a
    spec carries a full copy of `Le`. This section sizes those copies and counts
    how many the flagship carries.
 2. **The dynamic cost.** Wall time of the heaviest checks in the suite. If the
    budget is already small, no cache is demanded whatever section 1 says.

## Running it

    lake build phasec && ./.lake/build/bin/phasec

It is NOT in the default target, so a plain `lake build` does not build it and
the suite pays nothing for its presence.

## Profiling it

    lake build phasec
    perf record -g --call-graph=dwarf -F 499 -e cpu_core/cycles/u \
      -o perf.data ./.lake/build/bin/phasec load
    perf report -i perf.data --no-children --sort symbol --stdio

`load` runs only the checking loop, so no sample lands in this file's own
traversals. **`-e cpu_core/cycles/u` is not optional on a hybrid CPU**: without
it `perf` records one event per PMU, the E-core event collects a handful of
samples, and `perf report` prints that handful FIRST — which reads exactly like a
profile and is noise. The M29 phase-C reading was taken from the noise once
before the sample counts were checked.

The finding this harness produced is in `DECISION-LOG.md` (2026-08-06, phase C):
the duplication is real (79% of the list flagship), the profile confirms the
mechanism (~83% in normalization and the allocation it drives), and it is parked
because the whole budget is 75 ms.
-/

open Dllbc

namespace Measure

/-! ## Term size, in nodes -/

mutual
partial def tsize : Term → Nat
  | .var _ | .pvar _ | .type | .unit | .const _ => 1
  | .letIn _ a b => 1 + tsize a + tsize b
  | .assign a b c => 1 + tsize a + tsize b + tsize c
  | .ctorApp _ as => 1 + tsizeL as
  | .borrow t | .deref t | .cmpT t => 1 + tsize t
  | .index a b c => 1 + tsize a + tsize b + tsizeO c
  | .range a b c d e f =>
    1 + tsize a + tsize b + tsizeO c + tsizeO d + tsizeO e + tsizeO f
  | .matchE _ _ bs => 1 + tsizeB bs
  | .seq a b => 1 + tsize a + tsize b
  | .call _ as => 1 + tsizeL as
  | .seal a b => 1 + tsize a + tsize b
  | .callV _ as => 1 + tsizeL as
  | .lamR xs b => 1 + tsizeBnd xs + tsize b
  | .pi a b | .sigmaT a b | .lam a b | .app a b | .borrowT a b => 1 + tsize a + tsize b
  | .idT a b c => 1 + tsize a + tsize b + tsize c
partial def tsizeL : List Term → Nat
  | [] => 0
  | t :: ts => tsize t + tsizeL ts
partial def tsizeO : Option Term → Nat
  | none => 0
  | some t => tsize t
partial def tsizeB : List Branch → Nat
  | [] => 0
  | .mk _ _ b :: rest => tsize b + tsizeB rest
partial def tsizeBnd : List (Var × Term) → Nat
  | [] => 0
  | (_, τ) :: rest => tsize τ + tsizeBnd rest
end

/-! ## Occurrence counting: how many copies of `needle` does a term carry?

    A hit is not descended into — an occurrence of `Le` inside `Le` would be the
    same copy counted twice.

    **These per-constant counts OVERLAP and must not be summed.** `count`'s body
    contains `eqb`, and `Sorted`'s contains `Le`, so a scan for `eqb` descends
    through every `count` copy (a `count` node is not an `eqb` hit) and finds the
    nested one. Summing the columns therefore double-counts the nesting — it gave
    "103% of the term" on the first run, which is how the overlap announced
    itself. `coverage` below is the honest total: ONE traversal that stops at the
    first library constant it meets, whichever that is. -/

mutual
partial def occ (needle : Term) : Term → Nat
  | t =>
    if Term.beq t needle then 1 else
    match t with
    | .var _ | .pvar _ | .type | .unit | .const _ => 0
    | .letIn _ a b => occ needle a + occ needle b
    | .assign a b c => occ needle a + occ needle b + occ needle c
    | .ctorApp _ as => occL needle as
    | .borrow x | .deref x | .cmpT x => occ needle x
    | .index a b c => occ needle a + occ needle b + occO needle c
    | .range a b c d e f =>
      occ needle a + occ needle b + occO needle c + occO needle d
        + occO needle e + occO needle f
    | .matchE _ _ bs => occB needle bs
    | .seq a b => occ needle a + occ needle b
    | .call _ as => occL needle as
    | .seal a b => occ needle a + occ needle b
    | .callV _ as => occL needle as
    | .lamR xs b => occBnd needle xs + occ needle b
    | .pi a b | .sigmaT a b | .lam a b | .app a b | .borrowT a b =>
      occ needle a + occ needle b
    | .idT a b c => occ needle a + occ needle b + occ needle c
partial def occL (needle : Term) : List Term → Nat
  | [] => 0
  | t :: ts => occ needle t + occL needle ts
partial def occO (needle : Term) : Option Term → Nat
  | none => 0
  | some t => occ needle t
partial def occB (needle : Term) : List Branch → Nat
  | [] => 0
  | .mk _ _ b :: rest => occ needle b + occB needle rest
partial def occBnd (needle : Term) : List (Var × Term) → Nat
  | [] => 0
  | (_, τ) :: rest => occ needle τ + occBnd needle rest
end

/-! ## Non-overlapping coverage

    One traversal. At each node, the first library constant that matches claims
    the subtree and the walk does not descend; nothing else can claim those nodes.
    So `coverage t ≤ tsize t` always, and the ratio is a real fraction of the
    term. -/

mutual
partial def cov (ns : List (String × Term)) : Term → Nat
  | t =>
    match ns.find? (fun p => Term.beq t p.2) with
    | some (_, hit) => tsize hit
    | none =>
    match t with
    | .var _ | .pvar _ | .type | .unit | .const _ => 0
    | .letIn _ a b => cov ns a + cov ns b
    | .assign a b c => cov ns a + cov ns b + cov ns c
    | .ctorApp _ as => covL ns as
    | .borrow x | .deref x | .cmpT x => cov ns x
    | .index a b c => cov ns a + cov ns b + covO ns c
    | .range a b c d e f =>
      cov ns a + cov ns b + covO ns c + covO ns d + covO ns e + covO ns f
    | .matchE _ _ bs => covB ns bs
    | .seq a b => cov ns a + cov ns b
    | .call _ as => covL ns as
    | .seal a b => cov ns a + cov ns b
    | .callV _ as => covL ns as
    | .lamR xs b => covBnd ns xs + cov ns b
    | .pi a b | .sigmaT a b | .lam a b | .app a b | .borrowT a b => cov ns a + cov ns b
    | .idT a b c => cov ns a + cov ns b + cov ns c
partial def covL (ns : List (String × Term)) : List Term → Nat
  | [] => 0
  | t :: ts => cov ns t + covL ns ts
partial def covO (ns : List (String × Term)) : Option Term → Nat
  | none => 0
  | some t => cov ns t
partial def covB (ns : List (String × Term)) : List Branch → Nat
  | [] => 0
  | .mk _ _ b :: rest => cov ns b + covB ns rest
partial def covBnd (ns : List (String × Term)) : List (Var × Term) → Nat
  | [] => 0
  | (_, τ) :: rest => cov ns τ + covBnd ns rest
end

/-! ## Timing -/

def verdict (t : Term) : String :=
  match checkProgram t with | .ok _ => "OK" | .error e => "ERR: " ++ e.take 60

/-- Run `f` `n` times, report total and mean. The result is forced through a
    `String` length before the clock is read, the same guard `Tests/Functions.lean`
    uses, so nothing is left as a thunk. -/
def timeN (label : String) (n : Nat) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut last := ""
  for _ in [0:n] do
    last := f ()
    let _ ← IO.mkRef last.length
  let t1 ← IO.monoMsNow
  let tot := t1 - t0
  IO.println s!"  {label}: {last} — {tot} ms total, {tot / n} ms mean (x{n})"

def libEntries : List (String × Term) :=
  [ ("Le",      Std.LeFnT),    ("count",  Std.countFnT),
    ("Bound",   Std.BoundFnT), ("Sorted", Std.SortedFnT),
    ("len",     Std.lenFnT),   ("take",   Std.takeFnT),
    ("drop",    Std.dropFnT),  ("eqb",    Std.eqbFnT),
    ("leb",     Std.lebFnT),   ("add",    Std.addFnT),
    ("append",  Std.appendFnT) ]

/-! ## The subjects — the heaviest checks in the suite -/

def subjects : List (String × Term) :=
  [ ("list flagship  (quicksort, Sorted ∧ Perm)", Tests.S23Direct.flagship),
    ("array flagship (quicksortA chain)",         Tests.S25ArrSort.arrChain) ]

/-- `phasec load` runs ONLY the checking loop, so a `perf record` over it
    attributes every sample to the checker and none to this file's own static
    analysis (`tsize`/`occ`/`cov` are traversals too, and would otherwise sit in
    the profile looking like kernel work). -/
def loadOnly : IO Unit := do
  for (nm, t) in subjects do
    timeN s!"{nm} [perf load]" 50 (fun _ => verdict t)

def main : IO Unit := do
  IO.println "=== 1. STATIC: the inlined library ==="
  IO.println "Each `Le a b` in a spec carries a whole copy of `Le`'s body."
  for (nm, t) in libEntries do
    IO.println s!"  {nm}: {tsize t} nodes"
  IO.println ""

  IO.println "=== 2. STATIC: what the flagship carries ==="
  for (nm, t) in subjects do
    let total := tsize t
    IO.println s!"  {nm}"
    IO.println s!"    whole program term: {total} nodes"
    for (lnm, lt) in libEntries do
      let c := occ lt t
      if c > 0 then
        IO.println s!"      {lnm}: {c} copies x {tsize lt} = {c * tsize lt} nodes \
(overlapping — do not sum)"
    let cvg := cov libEntries t
    IO.println s!"    NON-OVERLAPPING library coverage: {cvg} of {total} nodes \
({if total == 0 then 0 else cvg * 100 / total}% of the term)"
  IO.println ""

  IO.println "=== 3. DYNAMIC: wall time of the heaviest checks ==="
  for (nm, t) in subjects do
    timeN nm 5 (fun _ => verdict t)
  IO.println ""

  IO.println "=== 4. DYNAMIC: the same check, many times (for perf sampling) ==="
  for (nm, t) in subjects do
    timeN s!"{nm} [perf load]" 50 (fun _ => verdict t)

end Measure

def main (args : List String) : IO Unit :=
  if args.contains "load" then Measure.loadOnly else Measure.main
