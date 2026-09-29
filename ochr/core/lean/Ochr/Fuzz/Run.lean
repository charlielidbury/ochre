import Ochr.Fuzz.Oracle

/-! # Fuzzer: checking one case against every oracle -/

namespace Ochr.Fuzz
open Ochr Ochr.Surface

structure Opts where
  cfg : Config := {}
  base : Option Config := none   -- attribute findings: report only those absent under these rules
  fuel : Nat := 200000
  nGround : Nat := 6
deriving Inhabited

def push (fs : Array Finding) (k : Kind) (comp w s d : String) (reason : String := "") : Array Finding :=
  -- one finding per (kind, reason, component) is enough to report and shrink
  if fs.any (fun f => f.kind == k && f.comp == comp && f.reason == reason) then fs
  else fs.push ⟨k, comp, w, s, d, reason⟩

/-- Observe a function value on ground inputs: its result (for a returned borrow, the
content, after which `7` is written through it, D38) and the final contents of the
cells its borrow arguments point into, after ending every borrow. -/
def callObs (fv T : Value) (inputs : List Value) : M Value := do
  let .tPi cs (.pi hs ds _) := T | err s!"not a function type: {T}"
  modify fun s => { s with env := #[{}] }
  pushFrame
  for v in cs do pushBind ⟨"κ"⟩ none v
  let mut args := #[]
  for ((d, h), v) in (ds.zip hs).zip inputs do
    let A ← evalType d
    let w ← match A with
      | .tRef T =>
        let l ← freshLoan
        modifyFrame 0 fun fr => { fr with binds := fr.binds.push ⟨⟨"c"⟩, some T, .loan l, false⟩ }
        pure (Value.borrow l v)
      | _ => pure v
    pushBind h (some A) w
    args := args.push w
  discard popFrameRaw
  let (r, _) ← callFn false fv none args (args.map fun _ => none) false
  let r ← match r with
    | .borrow k u => do pushTemp (.borrow k (Value.ofNat 7)); pure u
    | r => do pushTemp r; pure r
  endAll
  discard popTemp
  pure (obsVal r ((← get).env[0]!.binds.toList.map (·.val)))

/-- One-hole contexts that put a borrowed `T` inside a larger owner: `(K, owner type)`. -/
def contexts (inds : List IndDecl) (T : Value) : List ((Value → Value) × Value) :=
  let hasL := inds.any (·.name == "L")
  let hasBox := inds.any (·.name == "Box")
  match T with
  | .tNat => [(Value.succ, Value.tNat)] ++
      (if hasBox then [(fun h => Value.ind "Box" 0 ⟨"MkB"⟩ [] [h], Value.tInd "Box" [])] else []) ++
      (if hasL then [(fun h => Value.ind "L" 1 ⟨"Cons"⟩ [] [h, .ind "L" 0 ⟨"Nil"⟩ [] []], Value.tInd "L" [])] else [])
  | .tInd "L" [] => [(fun h => Value.ind "L" 1 ⟨"Cons"⟩ [] [.zero, h], Value.tInd "L" [])]
  | _ => []

/-- Conversion oracle: if the checker accepts `ConvEq : Eq T ConvF ConvG := refl`, the two
functions must observe the same on every ground input. -/
def convOracle (o : Opts) (prep : Prepared) : Option Finding := Id.run do
  if !(prep.globals.any (·.name == "ConvEq")) then return none
  let some f := prep.globals.find? (·.name == "ConvF") | return none
  let some g := prep.globals.find? (·.name == "ConvG") | return none
  let .tPi cs (.pi hs ds _) := f.ty | return none
  let st : MState := { globals := prep.globals, inds := prep.inds, cfg := o.cfg, fuel := o.fuel }
  -- the domains, to draw ground inputs (non-dependent function types only)
  let doms : List Value := match runSt (do
      pushFrame
      for v in cs do pushBind ⟨"κ"⟩ none v
      let mut out := #[]
      for (d, h) in ds.zip hs do
        let A ← evalType d
        out := out.push (match A with | .tRef T => T | A => A)
        pushBind h (some A) (.abs 0)
      pure out.toList) st with
    | .ok (xs, _) => xs
    | .error _ => []
  if doms.length != ds.length then return none
  let inputs := combos (doms.map fun T => (groundVals prep.inds T 1).take 3)
  for inp in inputs.take 12 do
    let lbl := ", ".intercalate (inp.map (·.pp))
    let a := (runSt (callObs f.val f.ty inp) st).map (·.1)
    let b := (runSt (callObs g.val f.ty inp) st).map (·.1)
    match a, b with
    | .ok x, .ok y =>
      if canon [] x != canon [] y then
        return some ⟨.conv, "ConvEq", s!"inputs ({lbl})", s!"ConvF observes {x.pp}", s!"ConvG observes {y.pp}", ""⟩
    | .ok x, .error e => if !isResource e then
        return some ⟨.conv, "ConvEq", s!"inputs ({lbl})", s!"ConvF observes {x.pp}", s!"ConvG errors: {e}", "error"⟩
    | .error e, .ok y => if !isResource e then
        return some ⟨.conv, "ConvEq", s!"inputs ({lbl})", s!"ConvF errors: {e}", s!"ConvG observes {y.pp}", "error"⟩
    | _, _ => pure ()
  pure none

/-- Candidate proofs of the statement: `refl`, a one-level split of each parameter, and
recursion on each Nat / list parameter (structural, and, to catch [Rec]/D31/L1 regressions,
non-decreasing with and without `by`). -/
def proofCands (c : Case) : List (STerm × Option String) := Id.run do
  let names := c.params.map (·.1)
  let arg (x y : String) (rep : STerm) : STerm :=
    if x == y then rep else
    match (c.params.lookup y) with
    | some (.amp _) => .ident y
    | _ => .ident y
  let call (x : String) (rep : STerm) : STerm := .call (.ident "Lie") (names.map fun y => arg x y rep)
  let mut out : Array (STerm × Option String) := #[(.ident "refl", none)]
  for (x, T) in c.params do
    match T with
    | .ident "Nat" =>
      out := out.push (.matchGen (.ident x) [("Z", [], .ident "refl"), ("S", ["_"], .ident "refl")], none)
      out := out.push (.matchGen (.ident x) [("Z", [], .ident "refl"), ("S", ["q"], call x (.ident "q"))], some x)
      out := out.push (call x (.ident x), some x)
      out := out.push (call x (.ident x), none)
    | .amp (.ident "Nat") =>
      out := out.push (.matchGen (.deref (.ident x)) [("Z", [], .ident "refl"), ("S", ["_"], .ident "refl")], none)
      out := out.push (.matchGen (.deref (.ident x)) [("Z", [], .ident "refl"), ("S", ["q"], call x (.amp (.ident "q")))], some x)
    | .ident "L" =>
      out := out.push (.matchGen (.ident x) [("Nil", [], .ident "refl"), ("Cons", ["_", "q"], call x (.ident "q"))], some x)
    | .ident "B2" =>
      out := out.push (.matchGen (.ident x) [("F", [], .ident "refl"), ("T", [], .ident "refl")], none)
    | _ => pure ()
  pure out.toList

/-- The first candidate proof the checker accepts, if any. -/
def acceptedProof (o : Opts) (c : Case) (prep : Prepared) : Option String := Id.run do
  for (body, dec) in proofCands c do
    let d : SDecl := { name := "Lie", params := c.params, ret := .app "Id" [c.ty, c.lhs, c.rhs],
                       body := body, dec := dec, expectAccept := true }
    match resolveProgram (c.decls ++ [d]) d with
    | .ok it =>
      match runSt (checkItem it) { globals := prep.globals, inds := prep.inds, cfg := o.cfg, fuel := o.fuel } with
      | .ok _ => return some (ppDecl d)
      | .error _ => pure ()
    | .error _ => pure ()
  pure none

def checkCase (o : Opts) (c : Case) (r : Rng) : CaseResult := Id.run do
  let prep ← match prepare o.cfg o.fuel c.decls with
    | .ok p => pure p
    | .error e => return { status := s!"invalid: {e}" }
  let convF := (convOracle o prep).toList
  let .id A t u := prep.stmt.body | return { status := "invalid: not an Id statement", findings := convF }
  let st0 : MState := { globals := prep.globals, inds := prep.inds, cfg := o.cfg, fuel := o.fuel }
  let (ps, st1) ← match runSt (setupParams prep.stmt) st0 with
    | .ok x => pure x
    | .error e => return { status := s!"invalid: parameters: {e}" }
  let ((refs, rng, fns), st2) ← match runSt (buildRefinements ps o.nGround r) st1 with
    | .ok x => pure x
    | .error e => return { status := s!"invalid: refinements: {e}" }
  let W := obsPositions st2.env
  let pinned := List.range st2.nextAbs
  let G := [0, 1, 2].map fun k => obsRun st2 A t u W true k
  if G.all (!·.isOk) then return { status := "rejected", findings := convF }
  let mut fs : Array Finding := convF.toArray
  let mut synOnly := 0
  let mut incomplete := 0
  let mut falseAt : Option (String × String) := none
  -- the generic values, with generalisations undone: nothing but parameters may remain
  let mut Gx : Array (Except String (Value × MState)) := #[]
  for (g, k) in G.zipIdx do
    match g with
    | .ok (v, s) =>
      match refineValS s s.neutrals [] v with
      | .ok (v', s') =>
        let rec' := s'.neutrals.map (·.2)
        let bad := (absIn v').filter fun σ => !pinned.contains σ && !rec'.contains σ
        if !bad.isEmpty || !(loansIn v').isEmpty then
          fs := push fs .escape (compName k) "the generic call"
            s!"{v'.pp}  (not parameters: {bad.map (s!"σ{·}")}, loans: {loansIn v'})" ""
        Gx := Gx.push (.ok (v', s'))
      | .error e => Gx := Gx.push (.error e)
    | .error e => Gx := Gx.push (.error e)
  for α in refs do
    let stα ← match runSt (α.subst.forM fun (σ, v) => refine σ v) st2 with
      | .ok (_, s) => pure s
      | .error _ => continue
    -- the direct path's values, with its own generalisations undone
    let D := [0, 1, 2].map fun k => (obsRun stα A t u W true k).bind fun (v, s) =>
      refineValS s s.neutrals [] v
    for k in [0:3] do
      match Gx[k]!, D[k]! with
      | .error _, .ok _ => incomplete := incomplete + 1
      | .error _, .error _ => pure ()
      | .ok (g, sg), dres =>
        let R := refineValS sg sg.neutrals α.subst g
        match R, dres with
        | .ok (rv, sr), .ok (dv, sd) =>
          let (res, syn) := compareVals sr sd pinned rv dv rng fns
          if syn then synOnly := synOnly + 1
          if let some (kd, sv, dvs) := res then
            -- a closed proof of a false proposition: the generic `Id` is ⊤, the instance's is
            -- not, and the instance's hypotheses (proof parameters) hold
            let isF := match dres with | .ok (dv, _) => isFalseV dv | _ => false
            let kd := if k == 2 && unitTop (canon [] g) == vTrue && α.ground && hypsHold stα ps && isF then Kind.falseProof else kd
            fs := push fs kd (compName k) α.label s!"{g.pp}  ⟶  {sv}" dvs
        | .ok (rv, _), .error e =>
          if !isResource e then fs := push fs .verdict (compName k) α.label s!"{g.pp}  ⟶  {rv.pp}" s!"error: {e}" (errKey e)
        | .error e, .ok (dv, _) =>
          if !isResource e then fs := push fs .renorm (compName k) α.label s!"{g.pp}  ⟶  error: {e}" dv.pp (errKey e)
        | .error _, .error _ => pure ()
    -- a false ground instance of the statement: remember it for the truth oracle
    if α.ground && hypsHold stα ps then
      if let .ok (dv, _) := D[2]! then
        if isFalseV dv && falseAt.isNone then falseAt := some (α.label, dv.pp)
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
              fs := push fs .adequacy (compName k) α.label s!"typed run: {dv.pp}" s!"machine: error: {e}" (errKey e)
  -- truth: a statement false at a ground instance must have no proof
  if let some (lbl, v) := falseAt then
    if fs.any (·.kind == .falseProof) then pure () else
    if let some pf := acceptedProof o c prep then
      fs := fs.push ⟨.truth, "Id", lbl, s!"accepted:\n  {pf}", s!"but at this instance the statement is {v}", ""⟩
  -- frame: a borrow parameter instantiated with a borrow into a larger structure; the
  -- observation must be the generic one with the cell's final content plugged into it
  for p in ps do
    let .borrow cell := p.kind | continue
    let some (Value.loan l) := (st2.env[0]!.binds[cell]?).map (fun (b : Binding) => b.val) | continue
    for (K, oT) in contexts st2.inds p.ty do
      let stK := { st2 with env := st2.env.modify 0 fun fr =>
        { fr with binds := fr.binds.modify cell fun b => { b with val := K (.loan l), ty := some oT } } }
      let lbl := s!"{p.name} := &(the hole of {(K (.abs 999)).pp.replace "σ999" "□"})"
      for k in [0:2] do
        match Gx[k]!, (obsRun stK A t u W true k).bind fun (v, s) => refineValS s s.neutrals [] v with
        | .ok (g, sg), .ok (d, sd) =>
          -- propositions formed about the owner are related through Ctx_O, not equal (frame
          -- lemma (3)): only observations without types inside are compared
          let hasTy : Value → Bool := fun v => v.anyAtom fun
            | .tEq .. | .tInd .. | .sort _ | .tPi .. | .proof => true | _ => false
          if hasTy g || hasTy d then continue
          let (r0, ws) := obsParts g
          let pred := obsVal r0 (ws.set cell (K (ws[cell]?.getD .bot)))
          let (res, _) := compareVals sg sd pinned pred d rng fns
          if let some (_, sv, dvs) := res then
            fs := push fs .frame (compName k) lbl s!"generic plugged: {sv}" dvs
        | .ok (g, _), .error e =>
          if !isResource e then fs := push fs .frame (compName k) lbl s!"generic: {g.pp}" s!"error: {e}" (errKey e)
        | _, _ => pure ()
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
