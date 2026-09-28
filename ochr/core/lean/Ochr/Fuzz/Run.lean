import Ochr.Fuzz.Oracle

/-! # Fuzzer: checking one case against every oracle -/

namespace Ochr.Fuzz
open Ochr

structure Opts where
  cfg : Config := {}
  base : Option Config := none   -- attribute findings: report only those absent under these rules
  fuel : Nat := 200000
  nGround : Nat := 6
deriving Inhabited

def push (fs : Array Finding) (k : Kind) (comp w s d : String) : Array Finding :=
  -- one finding per (kind, component) is enough to report and shrink
  if fs.any (fun f => f.kind == k && f.comp == comp) then fs else fs.push ⟨k, comp, w, s, d⟩

def checkCase (o : Opts) (c : Case) (r : Rng) : CaseResult := Id.run do
  let prep ← match prepare o.cfg o.fuel c.decls with
    | .ok p => pure p
    | .error e => return { status := s!"invalid: {e}" }
  let .id A t u := prep.stmt.body | return { status := "invalid: not an Id statement" }
  let st0 : MState := { globals := prep.globals, inds := prep.inds, cfg := o.cfg, fuel := o.fuel }
  let (ps, st1) ← match runSt (setupParams prep.stmt) st0 with
    | .ok x => pure x
    | .error e => return { status := s!"invalid: parameters: {e}" }
  let ((refs, rng), st2) ← match runSt (buildRefinements ps o.nGround r) st1 with
    | .ok x => pure x
    | .error e => return { status := s!"invalid: refinements: {e}" }
  let W := obsPositions st2.env
  let pinned := List.range st2.nextAbs
  let G := [0, 1, 2].map fun k => obsRun st2 A t u W true k
  if G.all (!·.isOk) then return { status := "rejected" }
  let mut fs : Array Finding := #[]
  let mut synOnly := 0
  let mut incomplete := 0
  -- the generic values, with generalisations undone: nothing but parameters may remain
  let mut Gx : Array (Except String (Value × MState)) := #[]
  for (g, k) in G.zipIdx do
    match g with
    | .ok (v, s) =>
      match refineVal s s.neutrals [] v with
      | .ok v' =>
        let bad := (absIn v').filter (!pinned.contains ·)
        if !bad.isEmpty || !(loansIn v').isEmpty then
          fs := push fs .escape (compName k) "the generic call"
            s!"{v'.pp}  (not parameters: {bad.map (s!"σ{·}")}, loans: {loansIn v'})" ""
        Gx := Gx.push (.ok (v', s))
      | .error e => Gx := Gx.push (.error e)
    | .error e => Gx := Gx.push (.error e)
  for α in refs do
    let stα ← match runSt (α.subst.forM fun (σ, v) => refine σ v) st2 with
      | .ok (_, s) => pure s
      | .error _ => continue
    -- the direct path's values, with its own generalisations undone
    let D := [0, 1, 2].map fun k => (obsRun stα A t u W true k).bind fun (v, s) =>
      (refineVal s s.neutrals [] v).map (·, s)
    for k in [0:3] do
      match Gx[k]!, D[k]! with
      | .error _, .ok _ => incomplete := incomplete + 1
      | .error _, .error _ => pure ()
      | .ok (g, sg), dres =>
        let R := refineVal sg [] α.subst g
        match R, dres with
        | .ok rv, .ok (dv, sd) =>
          let (res, syn) := compareVals sg sd pinned rv dv rng
          if syn then synOnly := synOnly + 1
          if let some (kd, sv, dvs) := res then
            let kd := if k == 2 && canon [] g == .tTop && α.ground then Kind.falseProof else kd
            fs := push fs kd (compName k) α.label s!"{g.pp}  ⟶  {sv}" dvs
        | .ok rv, .error e =>
          if !isResource e then fs := push fs .verdict (compName k) α.label s!"{g.pp}  ⟶  {rv.pp}" s!"error: {e}"
        | .error e, .ok (dv, _) =>
          if !isResource e then fs := push fs .renorm (compName k) α.label s!"{g.pp}  ⟶  error: {e}" dv.pp
        | .error _, .error _ => pure ()
    -- adequacy: at a ground instance the typed run and the untyped machine agree
    if α.ground then
      for k in [0:2] do
        if let .ok (dv, _) := D[k]! then
          match obsRun stα A t u W false k with
          | .ok (uv, _) =>
            if canon [] dv != canon [] uv then
              fs := push fs .adequacy (compName k) α.label s!"typed run: {dv.pp}" s!"machine: {uv.pp}"
          | .error e =>
            if !isResource e then
              fs := push fs .adequacy (compName k) α.label s!"typed run: {dv.pp}" s!"machine: error: {e}"
  pure { status := "checked", findings := fs.toList, synOnly := synOnly, incomplete := incomplete }

/-- The generic observations, printed (for `--show`). -/
def debugCase (o : Opts) (c : Case) : List String := Id.run do
  let .ok prep := prepare o.cfg o.fuel c.decls | return ["prepare failed"]
  let mut out := prep.rejected.map fun (n, e) => s!"library {n} rejected: {e}"
  let .id A t u := prep.stmt.body | return out
  let st0 : MState := { globals := prep.globals, inds := prep.inds, cfg := o.cfg, fuel := o.fuel }
  let .ok (_, st1) := runSt (setupParams prep.stmt) st0 | return out ++ ["setup failed"]
  let W := obsPositions st1.env
  for k in [0:3] do
    out := out ++ [s!"generic {compName k}: {showE ((obsRun st1 A t u W true k).map (·.1))}"]
  pure out

end Ochr.Fuzz
