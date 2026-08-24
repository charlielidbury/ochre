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
  | .var _ | .type | .unit | .const _ => 1
  | .marker _ a => 1 + tsize a
  | .letIn _ a => 1 + tsize a
  | .assign a b => 1 + tsize a + tsize b
  | .ctorApp _ as => 1 + tsizeL as
  | .borrow t | .deref t | .cmpT t => 1 + tsize t
  | .index a b c => 1 + tsize a + tsize b + tsizeO c
  | .range a b c d e f =>
    1 + tsize a + tsize b + tsizeO c + tsizeO d + tsizeO e + tsizeO f
  | .matchE _ _ bs => 1 + tsizeB bs
  | .seq a b => 1 + tsize a + tsize b
  | .call _ as => 1 + tsizeL as
  | .seal _ a b => 1 + tsize a + tsize b
  | .app a b => 1 + tsize a + tsize b
  | .pi _ a b | .sigmaT _ a b | .lam _ a b | .borrowT _ a b => 1 + tsize a + tsize b
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
end

/-! ## Occurrence counting: how many copies of `needle` does a term carry?

    A hit is not descended into — an occurrence of `Le` inside `Le` would be the
    same copy counted twice.

    **These per-constant counts OVERLAP and must not be summed.** `Count`'s body
    contains `Eqb`, and `Sorted`'s contains `Le`, so a scan for `Eqb` descends
    through every `Count` copy (a `Count` node is not an `Eqb` hit) and finds the
    nested one. Summing the columns therefore double-counts the nesting — it gave
    "103% of the term" on the first run, which is how the overlap announced
    itself. `coverage` below is the honest total: ONE traversal that stops at the
    first library constant it meets, whichever that is. -/

mutual
partial def occ (needle : Term) : Term → Nat
  | t =>
    if Term.beq t needle then 1 else
    match t with
    | .var _ | .type | .unit | .const _ => 0
    | .marker _ a => occ needle a
    | .letIn _ a => occ needle a
    | .assign a b => occ needle a + occ needle b
    | .ctorApp _ as => occL needle as
    | .borrow x | .deref x | .cmpT x => occ needle x
    | .index a b c => occ needle a + occ needle b + occO needle c
    | .range a b c d e f =>
      occ needle a + occ needle b + occO needle c + occO needle d
        + occO needle e + occO needle f
    | .matchE _ _ bs => occB needle bs
    | .seq a b => occ needle a + occ needle b
    | .call _ as => occL needle as
    | .seal _ a b => occ needle a + occ needle b
    | .app a b => occ needle a + occ needle b
    | .pi _ a b | .sigmaT _ a b | .lam _ a b | .borrowT _ a b =>
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
    | .var _ | .type | .unit | .const _ => 0
    | .marker _ a => cov ns a
    | .letIn _ a => cov ns a
    | .assign a b => cov ns a + cov ns b
    | .ctorApp _ as => covL ns as
    | .borrow x | .deref x | .cmpT x => cov ns x
    | .index a b c => cov ns a + cov ns b + covO ns c
    | .range a b c d e f =>
      cov ns a + cov ns b + covO ns c + covO ns d + covO ns e + covO ns f
    | .matchE _ _ bs => covB ns bs
    | .seq a b => cov ns a + cov ns b
    | .call _ as => covL ns as
    | .seal _ a b => cov ns a + cov ns b
    | .app a b => cov ns a + cov ns b
    | .pi _ a b | .sigmaT _ a b | .lam _ a b | .borrowT _ a b => cov ns a + cov ns b
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

/-! ## The split that decides what a tier could even address

    `sealValue` (Machine.lean) checks `hasType v uV` once and then **forgets** —
    "a fresh σ at the ascribed type is the whole downstream view". So a seal
    destroys computational content, and that sorts the library in two:

      * **DEFINITIONS** (`Le`, `Count`, `Eqb`, `Len`, `Add`, …) must stay
        TRANSPARENT. The corpus converts by ι-reducing them: `Le (S a) (S b)` IS
        `Le a b` (M14's bounds-cursor descent, which is what lets quicksort hand
        `hfuel` to its callee unchanged), and an ex-falso branch is exactly
        `Le (S n) Z` computing to `Bot`. Seal `Le` and both stop holding.
      * **PROOFS** (`LeTrans`, `CountConsL`, …) may be sealed, because nothing
        reduces them — they are cited at a type and never computed with.

    So the two censuses below are not two views of one number. The first is mass
    a seal-based tier CANNOT touch; the second is the mass it could. -/

def lemmaEntries : List (String × Term) :=
  [ ("LeRefl",      StdChainRaw.LeReflRaw),      ("LeTrans",     StdChainRaw.LeTransRaw),
    ("LeUpR",       StdChainRaw.LeUpRRaw),       ("IdTrans",     StdChainRaw.IdTransRaw),
    ("IdCongr",     StdChainRaw.IdCongrRaw),     ("LebTrueLe",   StdChainRaw.LebTrueLeRaw),
    ("LebFalseGt",  StdChainRaw.LebFalseGtRaw),  ("LePredL",     StdChainRaw.LePredLRaw),
    ("CountConsL",  StdChainRaw.CountConsLRaw),  ("CountConsR",  StdChainRaw.CountConsRRaw) ]

/-- `timeN`, but the subject depends on the iteration index, so a pure call
    cannot be hoisted out of the loop as a loop invariant. -/
def timeNi (label : String) (n : Nat) (f : Nat → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut last := ""
  for i in [0:n] do
    last := f i
    let _ ← IO.mkRef last.length
  let t1 ← IO.monoMsNow
  let tot := t1 - t0
  IO.println s!"  {label}: {last} — {tot} ms total, {tot * 1000 / n} µs mean (x{n})"

def libEntries : List (String × Term) :=
  [ ("Le",      Std.Le),    ("Count",  Std.Count),
    ("Bound",   Std.Bound), ("Sorted", Std.Sorted),
    ("Len",     Std.Len),   ("Take",   Std.Take),
    ("Drop",    Std.Drop),  ("Eqb",    Std.Eqb),
    ("Leb",     Std.Leb),   ("Add",    Std.Add),
    ("Append",  Std.Append) ]

/-! ## The subjects — the heaviest checks in the suite -/

-- Both flagships are SEEDED modules since the docs/21 train; their persisted
-- terms, markers stripped, are CLOSED (formers qualified, lemmas spliced), so
-- the classic corpus keeps both subjects. `arrVerdict` additionally measures
-- the SEEDED check — the walk the suite's twins actually pay for.
def subjects : List (String × Term) :=
  [ ("list flagship  (quicksort, Sorted ∧ Perm, stripped)", Term.stripMarkers Tests.S23Direct.qsM.term),
    ("array flagship (quicksortA chain, stripped)",         Term.stripMarkers Tests.S25ArrSort.arrSort.term) ]
def arrVerdict : Unit → String := fun _ =>
  match checkProgramFrom Dllbc.std Tests.S25ArrSort.arrSort.term with
  | .ok _ => "OK" | .error e => "ERR: " ++ (e.take 60).toString

/-- `phasec load` runs ONLY the checking loop, so a `perf record` over it
    attributes every sample to the checker and none to this file's own static
    analysis (`tsize`/`occ`/`cov` are traversals too, and would otherwise sit in
    the profile looking like kernel work). -/
def loadOnly : IO Unit := do
  for (nm, t) in subjects do
    timeN s!"{nm} [perf load]" 50 (fun _ => verdict t)
  timeN "array flagship (seeded) [perf load]" 50 arrVerdict

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
    IO.println s!"    DEFINITION mass (must stay transparent): {cvg} of {total} nodes \
({if total == 0 then 0 else cvg * 100 / total}%)"
    for (lnm, lt) in lemmaEntries do
      let c := occ lt t
      if c > 0 then
        IO.println s!"      [proof] {lnm}: {c} copies x {tsize lt} = {c * tsize lt} nodes"
    let pcvg := cov lemmaEntries t
    IO.println s!"    PROOF mass (sealable): {pcvg} of {total} nodes \
({if total == 0 then 0 else pcvg * 100 / total}%)"
    -- The two censuses above OVERLAP each other, and the trap is one level up
    -- from the first one: a PROOF body contains DEFINITIONS (`LeTrans` is 1373
    -- nodes of mostly `Le`), so the definition scan descends through lemmas and
    -- counts what the lemma scan already claimed whole. Summing them gave 113%.
    -- The partition below is one traversal over both lists with PROOFS taking
    -- priority, so each node is claimed once and the parts add up.
    let both := cov (lemmaEntries ++ libEntries) t
    let defsOutside := both - pcvg
    IO.println s!"    ── partition (each node claimed once) ──"
    IO.println s!"      sealable proof mass:            {pcvg} \
({if total == 0 then 0 else pcvg * 100 / total}%)"
    IO.println s!"      definitions OUTSIDE any proof:  {defsOutside} \
({if total == 0 then 0 else defsOutside * 100 / total}%)"
    IO.println s!"      neither (the program itself):   {total - both} \
({if total == 0 then 0 else (total - both) * 100 / total}%)"
  IO.println ""

  IO.println "=== 3. DYNAMIC: wall time of the heaviest checks ==="
  for (nm, t) in subjects do
    timeN nm 5 (fun _ => verdict t)
  timeN "array flagship (seeded check from std)" 5 arrVerdict
  IO.println ""

  IO.println "=== 4. DYNAMIC: the same check, many times (for perf sampling) ==="
  for (nm, t) in subjects do
    timeN s!"{nm} [perf load]" 50 (fun _ => verdict t)
  timeN "array flagship (seeded) [perf load]" 50 arrVerdict
  IO.println ""

  -- The suite's DLLBC time is dominated by ONE assertion, and it is not a check:
  -- `ArraySort.lean:786` RUNS the array quicksort concretely on the worst case for
  -- a Lomuto scan. Timed here independently of the `native_decide` → `sorry`
  -- differential that found it, because the whole verdict now leans on it.
  IO.println "=== 5. THE SUITE'S ACTUAL HOTSPOT — concrete EXECUTION, not checking ==="
  timeN "runQsA [1,2,3]           (Tests/ArraySort.lean:781)" 1
    (fun _ => toString (Tests.S25ArrSort.runQsA [1, 2, 3]))
  timeN "runQsA [3,1,4,1,5,9,2]   (Tests/ArraySort.lean:784)" 1
    (fun _ => toString (Tests.S25ArrSort.runQsA [3, 1, 4, 1, 5, 9, 2]))
  timeN "runQsA [9,8,7,6,5,4,3,2,1] (Tests/ArraySort.lean:786)" 1
    (fun _ => toString (Tests.S25ArrSort.runQsA [9, 8, 7, 6, 5, 4, 3, 2, 1]))
  -- x1000, because a single run rounds to 0 ms and the point needs a real number:
  -- the `native_decide` at that line costs 28.1 s of ELABORATION, so if the
  -- execution is microseconds then 28.1 s is Lean's machinery, not this calculus's.
  --
  -- **The input VARIES with the iteration.** A loop that calls a pure function on
  -- a constant literal is loop-invariant and Lean hoists it, so the naive x1000
  -- reports 0 ms whatever the function costs — which is the same class of mistake
  -- as an `IO.Ref` counter shim being compiled away. Threading `i` through the
  -- last element makes every call a distinct computation.
  timeNi "runQsA [9,8,7,6,5,4,3,2,i]  x3 (input varies — no hoisting)" 3
    (fun i => toString (Tests.S25ArrSort.runQsA [9, 8, 7, 6, 5, 4, 3, 2, i % 16]))
  timeNi "runQsA [3,1,4,1,5,9,2+i]     x3 (7 elements, for the slope)" 3
    (fun i => toString (Tests.S25ArrSort.runQsA [3, 1, 4, 1, 5, 9, 2 + i % 4]))

end Measure

def main (args : List String) : IO Unit :=
  if args.contains "load" then Measure.loadOnly else Measure.main
