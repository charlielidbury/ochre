import Ochr.Fuzz.Oracle

/-! # Fuzzer: checking one case against every oracle -/

namespace Ochr.Fuzz
open Ochr Ochr.Surface

structure Opts where
  cfg : Config := {}
  base : Option Config := none   -- attribute findings: report only those absent under these rules
  fuel : Nat := 200000
  nGround : Nat := 6
  runtimeRefine : Bool := false  -- refine at runtime depth (D53: sealed re-runs move), not erased
deriving Inhabited

/-- A finding's reason at a refinement where some hypothesis is `False` (vacuous: no
instance satisfies the hypotheses, so the two paths may differ without harm). -/
def vacK (vac : Bool) (reason : String) : String :=
  if !vac then reason else if reason == "" then "vacuous" else s!"vacuous {reason}"

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
        modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨"c"⟩, ty := some T, val := .loan l } }
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
  | .tNat => [(Value.succ, Value.tNat),
      (fun h => Value.ind "Pair" 0 ⟨"Mk"⟩ [.tNat, .tNat] [h, .zero], Value.tInd "Pair" [.tNat, .tNat])] ++
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

/-- Execution oracle (D53): a data function the checker accepts must run at every ground
input without error at runtime depth, where reads move, and observe what its erased run,
where reads copy, observes. Checked for the random library functions and for the
statement's two sides declared as data functions `ExecL`/`ExecR` over its parameters
(when the checker accepts them). Returns the findings and how many sides were accepted. -/
def execOracle (o : Opts) (c : Case) (prep : Prepared) : List Finding × Nat := Id.run do
  let st0 : MState := { globals := prep.globals, inds := prep.inds, cfg := o.cfg, fuel := o.fuel }
  let sides : List SDecl := [("ExecL", c.lhs), ("ExecR", c.rhs)].map fun (n, b) =>
    { name := n, params := c.params, ret := c.ty, body := b, expectAccept := true }
  let mut globals := prep.globals
  let mut acc := 0
  for d in sides do
    let .ok it := resolveProgram (c.decls ++ sides) d | continue
    if let .ok ((), st') := runSt (checkItem it) { st0 with globals := globals } then
      globals := st'.globals; acc := acc + 1
  let st := { st0 with globals := globals }
  let names := c.extra.map (·.name) ++ ["ExecL", "ExecR"]
  let mut fs : Array Finding := #[]
  for g in globals do
    unless names.contains g.name do continue
    let .tPi cs (.pi hs ds cod) := g.ty | continue
    -- ground inputs (data from `groundVals`, `⋆` for a hypothesis that is `⊤`); a function
    -- whose result is a proof or a type is never run
    let doms : Option (List (List Value)) := match runSt (do
        pushFrame
        for v in cs do pushBind ⟨"κ"⟩ none v
        let mut out := #[]
        for (d, h) in ds.zip hs do
          let A ← evalType d
          -- a function parameter's inputs are the library functions of its type
          let vs ← if ← isPropV A then pure (if unitTop A == vTrue then [Value.proof] else [])
            else if A matches .tPi .. then pure ((← fnInstances A).take 3)
            -- D66: a borrowed function's inputs are the library functions of its type
            else if let .tRef T@(.tPi ..) := A then pure ((← fnInstances T).take 3)
            else pure ((groundVals prep.inds (match A with | .tRef T => T | A => A) 1).take 3)
          out := out.push vs
          pushBind h (some A) (.abs 0)
        let B ← evalType cod
        pure (if (← isPropV B) || (B matches .sort _) then none else some out.toList)) st with
      | .ok (xs, _) => xs
      | .error _ => none
    let some doms := doms | continue
    for inp in (combos doms).take 12 do
      let lbl := s!"{g.name}({", ".intercalate (inp.map (·.pp))})"
      let run := (runSt (callObs g.val g.ty inp) st).map (·.1)
      let ers := (runSt (withErased (callObs g.val g.ty inp)) st).map (·.1)
      match run, ers with
      | .error e, .ok y => if !isResource e then
          fs := push fs .exec g.name lbl s!"runtime run errors: {e}" s!"erased run observes {y.pp}" (errKey e)
      | .ok x, .ok y => if canon [] x != canon [] y then
          fs := push fs .exec g.name lbl s!"runtime run observes {x.pp}" s!"erased run observes {y.pp}"
      | .ok x, .error e => if !isResource e then
          fs := push fs .exec g.name lbl s!"runtime run observes {x.pp}" s!"erased run errors: {e}" s!"erased {errKey e}"
      -- an accepted function that goes wrong on a well-typed input, however it is run
      | .error e, .error e2 => if !isResource e && !isResource e2 then
          fs := push fs .exec g.name lbl s!"runtime run errors: {e}" s!"erased run errors: {e2}" s!"both {errKey e}"
  pure (fs.toList, acc)

/-- Rename the variable `x` to `y` in a generated term (generated binders never reuse a
parameter's name, so no shadowing is possible). -/
partial def renameT (x y : String) : STerm → STerm
  | .ident z => .ident (if z == x then y else z)
  | .app f as => .app f (as.map (renameT x y))
  | .call f as => .call (renameT x y f) (as.map (renameT x y))
  | .ctorP c ps as => .ctorP c (ps.map (renameT x y)) (as.map (renameT x y))
  | .deref t => .deref (renameT x y t)
  | .proj i t => .proj i (renameT x y t)
  | .amp t => .amp (renameT x y t)
  | .assign a b => .assign (renameT x y a) (renameT x y b)
  | .letIn z A t u => .letIn z (A.map (renameT x y)) (renameT x y t) (renameT x y u)
  | .seq a b => .seq (renameT x y a) (renameT x y b)
  | .matchGen sc arms => .matchGen (renameT x y sc) (arms.map fun (c, vs, b) => (c, vs, renameT x y b))
  | .pi bs c => .pi (bs.map fun (z, A) => (z, renameT x y A)) (renameT x y c)
  | .arrow a b => .arrow (renameT x y a) (renameT x y b)
  | .fix f bs r d b => .fix f (bs.map fun (z, A) => (z, renameT x y A)) (renameT x y r) d (renameT x y b)
  | .pair a b => .pair (renameT x y a) (renameT x y b)
  | .andI a b => .andI (renameT x y a) (renameT x y b)
  | .and a b => .and (renameT x y a) (renameT x y b)
  | .prod a b => .prod (renameT x y a) (renameT x y b)
  | .ascribe a b => .ascribe (renameT x y a) (renameT x y b)
  | .rewrite rev h t => .rewrite rev (renameT x y h) (renameT x y t)
  | .split f t => .split f (renameT x y t)
  | .splitArms f arms => .splitArms f (arms.map fun (c, vs, b) => (c, vs, renameT x y b))
  | t => t

/-- The names of the functions a term calls (for `split f in …` candidates). -/
partial def stermCalls : STerm → List String
  | .call (.ident f) as => f :: as.flatMap stermCalls
  | .call f as => stermCalls f ++ as.flatMap stermCalls
  | .app _ as | .ctorP _ _ as => as.flatMap stermCalls
  | .deref t | .proj _ t | .amp t | .ascribe t _ => stermCalls t
  | .assign a b | .seq a b | .pair a b | .andI a b | .and a b => stermCalls a ++ stermCalls b
  | .letIn _ _ t u => stermCalls t ++ stermCalls u
  | .matchGen sc arms => stermCalls sc ++ arms.flatMap (fun (_, _, b) => stermCalls b)
  | .fix _ _ _ _ b => stermCalls b
  | _ => []

/-- Candidate proofs of the statement: `refl`, a one-level split of each parameter, and
recursion on each Nat / list parameter (structural, and, to catch [Rec]/D31/L1/L3
regressions, non-decreasing with and without `by`, through a local, or inside a λ). -/
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
      -- L1: the function passed as a value to a function that calls it (Knot's shape):
      -- `(λ(f : Π(yy : Nat). T[yy]) (z : Nat) : T[z] => f(z))(Lie, x)`, for a statement over
      -- `x` alone (the callee's body runs untyped, so its call of `f` meets no [Rec] check)
      if c.params.length == 1 then
        let T (v : String) := STerm.app "Id" [c.ty, renameT x v c.lhs, renameT x v c.rhs]
        let app := STerm.fix "_" [("f", .pi [("yy", .ident "Nat")] (T "yy")), ("z", .ident "Nat")] (T "z") none
          (.call (.ident "f") [.ident "z"])
        out := out.push (.call app [.ident "Lie", .ident x], some x)
      -- L3: the recursive call inside a nested λ, on the λ's own argument (KnotL's shape);
      -- only when no parameter is a borrow (closures capture no borrows)
      if c.params.all (fun (_, T) => !(T matches .amp _)) then
        let T := STerm.app "Id" [c.ty, renameT x "yy" c.lhs, renameT x "yy" c.rhs]
        out := out.push (.letIn "g" none (.fix "_" [("yy", .ident "Nat")] T none (call x (.ident "yy")))
          (.call (.ident "g") [.ident x]), some x)
    | .amp (.ident "Nat") =>
      out := out.push (.matchGen (.deref (.ident x)) [("Z", [], .ident "refl"), ("S", ["_"], .ident "refl")], none)
      out := out.push (.matchGen (.deref (.ident x)) [("Z", [], .ident "refl"), ("S", ["q"], call x (.amp (.ident "q")))], some x)
    | .ident "L" =>
      out := out.push (.matchGen (.ident x) [("Nil", [], .ident "refl"), ("Cons", ["_", "q"], call x (.ident "q"))], some x)
    | .ident "B2" =>
      out := out.push (.matchGen (.ident x) [("F", [], .ident "refl"), ("T", [], .ident "refl")], none)
    -- the induction hypothesis at the call site through a borrowed list's tail (reviewer-6 W10)
    | .amp (.ident "L") =>
      out := out.push (.matchGen (.deref (.ident x)) [("Nil", [], .ident "refl"), ("Cons", ["_", "q"], call x (.amp (.ident "q")))], some x)
      out := out.push (.matchGen (.deref (.ident x)) [("Nil", [], .ident "refl"), ("Cons", ["_", "q"], .letIn "ih" none (call x (.amp (.ident "q"))) (.ident "refl"))], some x)
    -- D60: rewrite along a hypothesis
    | .app "Eq" _ =>
      out := out.push (.rewrite false (.ident x) (.ident "refl"), none)
      out := out.push (.rewrite true (.ident x) (.ident "refl"), none)
    | _ => pure ()
  -- the paper's central mechanism: the in-place lemma applied at the call site, to a
  -- parameter, to its predecessor field, or to a pair's field (a reborrowed field)
  if c.lib.contains "AddM" then
    let lem (p : STerm) : STerm := .call (.ident "AddMZeroL") [p]
    for (x, T) in c.params do
      match T with
      | .ident "Nat" =>
        out := out.push (lem (.amp (.ident x)), none)
        out := out.push (.matchGen (.ident x) [("Z", [], .ident "refl"), ("S", ["p"], lem (.amp (.ident "p")))], none)
      | .amp (.ident "Nat") =>
        out := out.push (lem (.ident x), none)
        out := out.push (.matchGen (.deref (.ident x)) [("Z", [], .ident "refl"), ("S", ["p"], lem (.amp (.ident "p")))], none)
      | .prod _ _ =>
        out := out.push (.matchGen (.ident x) [("Mk", ["a", "b"], lem (.amp (.ident "a")))], none)
        out := out.push (.matchGen (.ident x) [("Mk", ["a", "b"], lem (.amp (.ident "b")))], none)
      | .amp (.prod _ _) =>
        out := out.push (.matchGen (.deref (.ident x)) [("Mk", ["a", "b"], lem (.amp (.ident "a")))], none)
        out := out.push (.matchGen (.deref (.ident x)) [("Mk", ["a", "b"], lem (.amp (.ident "b")))], none)
      | _ => pure ()
  -- D61: split on a call of each library function the statement uses
  let lib := c.lib ++ c.extra.map (·.name)
  for f in ((stermCalls c.lhs ++ stermCalls c.rhs).filter lib.contains).eraseDups do
    out := out.push (.split f (.ident "refl"), none)
    out := out.push (.split f (.split f (.ident "refl")), none)
  pure (out.toList ++ c.extraProofs.map (·, none))

/-- The first candidate proof the checker accepts, if any. -/
def acceptedProof (o : Opts) (c : Case) (prep : Prepared) : Option String := Id.run do
  -- the in-place lemma for the call-site candidates, checked here only, so that the case's
  -- own checks (and their shared fuel) are the ones they were without it
  let lemma : List SDecl := if c.lib.contains "AddM" then (libDecl "AddMZeroL").toList else []
  let mut globals := prep.globals
  let mut inds := prep.inds
  for d in lemma do
    if let .ok it := resolveProgram (c.decls ++ lemma) d then
      if let .ok ((), st') := runSt (checkItem it) { globals := globals, inds := inds, cfg := o.cfg, fuel := o.fuel } then
        globals := st'.globals; inds := st'.inds
  for (body, dec) in proofCands c do
    let d : SDecl := { name := "Lie", params := c.params, ret := .app "Id" [c.ty, c.lhs, c.rhs],
                       body := body, dec := dec, expectAccept := true }
    match resolveProgram (c.decls ++ lemma ++ [d]) d with
    | .ok it =>
      match runSt (checkItem it) { globals := globals, inds := inds, cfg := o.cfg, fuel := o.fuel } with
      | .ok _ => return some (ppDecl d)
      | .error _ => pure ()
    | .error _ => pure ()
  pure none

def checkCase (o : Opts) (c : Case) (r : Rng) : CaseResult := Id.run do
  let er := !o.runtimeRefine
  let prep ← match prepare o.cfg o.fuel c.decls with
    | .ok p => pure p
    | .error e => return { status := if e.startsWith "rejected" then "rejected" else s!"invalid: {e}" }
  let (execF, execN) := execOracle o c prep
  -- rules oracle: a declaration a rule forbids must be rejected
  -- a rule declaration expected accepted (`expectAccept`) is a finding when rejected
  let ruleF : List Finding := c.ruleDecls.filterMap fun (why, d) =>
    let rej := prep.rejected.find? (·.1 == d.name)
    if d.expectAccept then
      match rej with
      | some (_, e) => some ⟨.rule, d.name, "its declaration", s!"rejected: {e}\n  {ppDecl d}", s!"but the rules accept it: {why}", why⟩
      | none => none
    else if rej.isSome then none
    else some ⟨.rule, d.name, "its declaration", s!"accepted:\n  {ppDecl d}", s!"but it breaks the rule: {why}", why⟩
  let agreeF : List Finding := c.agreeDecls.filterMap fun (why, a, b) =>
    let ra := prep.rejected.any (·.1 == a.name)
    let rb := prep.rejected.any (·.1 == b.name)
    if ra == rb then none
    else some ⟨.rule, a.name, "the pair", s!"{a.name} {if ra then "rejected" else "accepted"}:\n  {ppDecl a}",
      s!"{b.name} {if rb then "rejected" else "accepted"}:\n  {ppDecl b}", s!"decided differently: {why}"⟩
  let convF := (convOracle o prep).toList ++ execF ++ ruleF ++ agreeF
  let .id A t u := prep.stmt.body | return { status := "invalid: not an Id statement", findings := convF, execAccepted := execN }
  let st0 : MState := { globals := prep.globals, inds := prep.inds, cfg := o.cfg, fuel := o.fuel }
  let (ps, st1) ← match runSt (setupParams prep.stmt) st0 with
    | .ok x => pure x
    | .error e => return { status := s!"invalid: parameters: {e}" }
  let ((refs, rng, fns), st2) ← match runSt (buildRefinements ps o.nGround r) st1 with
    | .ok x => pure x
    | .error e => return { status := s!"invalid: refinements: {e}" }
  let W := obsPositions st2.env [t, u] o.cfg
  let pinned := List.range st2.nextAbs
  let G := [0, 1, 2].map fun k => obsRun st2 A t u W true k
  if G.all (!·.isOk) then return { status := "rejected", findings := convF, execAccepted := execN }
  let mut fs : Array Finding := convF.toArray
  let mut synOnly := 0
  let mut incomplete := 0
  let mut falseAt : Option (String × String) := none
  -- proof irrelevance (D55, reviewer-4 W2): a function parameter whose type is a proposition
  -- by computation but is bound as data; its instances must not be told apart
  let irrelPs : List (Nat × Nat) := Id.run do    -- (σ, position of its binding in W)
    let mut out := []
    for (p, j) in ps.toList.zipIdx do
      if p.kind == .data && (p.ty matches .tPi ..) then
        if let .ok (0, _) := runSt (sortOf p.ty) st2 then
          if let some w := W.findIdx? (· == Pos.bind 1 j) then out := out ++ [(p.σ, w)]
    pure out
  let mut irrelObs : Array (Nat × String × List Value) := #[]
  -- the generic values, with generalisations undone: nothing but parameters may remain
  let mut Gx : Array (Except String (Value × MState)) := #[]
  for (g, k) in G.zipIdx do
    match g with
    | .ok (v, s) =>
      match refineValS s s.neutrals [] v er with
      | .ok (v', s') =>
        -- D68: the fields of a parameter's η-refinement name parts of that parameter
        let rec' := s'.neutrals.map (·.2) ++ s.etaRefs.flatMap (absIn ·.2)
        let bad := (absIn v').filter fun σ => !pinned.contains σ && !rec'.contains σ
        if !bad.isEmpty || !(loansIn v').isEmpty then
          fs := push fs .escape (compName k) "the generic call"
            s!"{v'.pp}  (not parameters: {bad.map (s!"σ{·}")}, loans: {loansIn v'})" (vacK (hypsFalse st2 ps) "")
        Gx := Gx.push (.ok (v', s'))
      | .error e => Gx := Gx.push (.error e)
    | .error e => Gx := Gx.push (.error e)
  for α in refs do
    let stα ← match runSt (α.subst.forM fun (σ, v) => refine σ v) st2 with
      | .ok (_, s) => pure s
      | .error _ => continue
    -- a refinement at which some hypothesis is `False`: what it finds is vacuous
    let vac := hypsFalse stα ps
    -- the direct path's values, with its own generalisations undone
    let D := [0, 1, 2].map fun k => (obsRun stα A t u W true k).bind fun (v, s) =>
      refineValS s s.neutrals [] v er
    for k in [0:3] do
      match Gx[k]!, D[k]! with
      | .error _, .ok _ => incomplete := incomplete + 1
      | .error _, .error _ => pure ()
      | .ok (g, sg), dres =>
        let R := refineValS sg sg.neutrals α.subst g er
        match R, dres with
        | .ok (rv, sr), .ok (dv, sd) =>
          let (res, syn) := compareVals sr sd pinned rv dv rng fns er
          if syn then synOnly := synOnly + 1
          if let some (kd, sv, dvs, why) := res then
            -- a closed proof of a false proposition: the generic `Id` is ⊤, the instance's is
            -- not, and the instance's hypotheses (proof parameters) hold
            let isF := match dres with | .ok (dv, _) => isFalseV dv | _ => false
            let kd := if k == 2 && unitTop (canon [] g) == vTrue && α.ground && hypsHold stα ps && isF then Kind.falseProof else kd
            fs := push fs kd (compName k) α.label s!"{g.pp}  ⟶  {sv}" dvs (vacK vac why)
        | .ok (rv, _), .error e =>
          if !isResource e then fs := push fs .verdict (compName k) α.label s!"{g.pp}  ⟶  {rv.pp}" s!"error: {e}" (vacK vac (errKey e))
        | .error e, .ok (dv, _) =>
          if !isResource e then fs := push fs .renorm (compName k) α.label s!"{g.pp}  ⟶  error: {e}" dv.pp (vacK vac (errKey e))
        | .error _, .error _ => pure ()
    -- the observations at an instance of one proof-irrelevance parameter alone
    if let [(σ, _)] := α.subst then
      if let some w := irrelPs.lookup σ then
        let drop (v : Value) : Value :=
          let (r, ws) := obsParts v
          obsVal r (ws.eraseIdx w)
        let obs := [0, 1].filterMap fun k => match D[k]! with
          | .ok (v, _) => some (canon pinned (drop v))
          | .error _ => none
        if obs.length == 2 then irrelObs := irrelObs.push (σ, α.label, obs)
    -- a false instance of the statement: remember it for the truth oracle. A refinement that
    -- is not ground counts when the `Id` computes to `False` itself (so at every completion)
    if hypsHold stα ps then
      if let .ok (dv, _) := D[2]! then
        -- `Eq Prop False ⊤` (either way round) is false too: a proof of it casts ⊤ to False
        let propFalse := match unitTop dv with
          | .tEq (.sort 0) a b => (isFalseV (unitTop a) && unitTop b == vTrue) || (unitTop a == vTrue && isFalseV (unitTop b))
          | _ => false
        if (isFalseV dv || propFalse) && falseAt.isNone then falseAt := some (α.label, dv.pp)
    -- adequacy: at a ground instance the typed run and the untyped machine agree
    if α.ground then
      for k in [0:2] do
        if let .ok (dv, _) := D[k]! then
          match obsRun stα A t u W false k with
          | .ok (uv, _) =>
            if canon [] dv != canon [] uv then
              fs := push fs .adequacy (compName k) α.label s!"typed run: {dv.pp}" s!"machine: {uv.pp}" (vacK vac "")
          | .error e =>
            if !isResource e then
              fs := push fs .adequacy (compName k) α.label s!"typed run: {dv.pp}" s!"machine: error: {e}" (vacK vac (errKey e))
  for (σ, l1, o1) in irrelObs do
    for (σ', l2, o2) in irrelObs do
      if σ == σ' && l1 < l2 && o1 != o2 then
        fs := push fs .irrel "lhs, rhs" s!"{l1} and {l2}" s!"{l1}: {(o1.map (·.pp))}" s!"{l2}: {(o2.map (·.pp))}"
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
    -- the cell's index among the observed positions (all bindings before D68; the footprint since)
    let some ci := W.findIdx? (· == Pos.bind 0 cell) | continue
    for (K, oT) in contexts st2.inds p.ty do
      let stK := { st2 with env := st2.env.modify 0 fun fr =>
        { fr with binds := fr.binds.modify cell fun b => { b with val := K (.loan l), ty := some oT } } }
      let lbl := s!"{p.name} := &(the hole of {(K (.abs 999)).pp.replace "σ999" "□"})"
      for k in [0:2] do
        match Gx[k]!, (obsRun stK A t u W true k).bind fun (v, s) => refineValS s s.neutrals [] v er with
        | .ok (g, sg), .ok (d, sd) =>
          -- propositions formed about the owner are related through Ctx_O, not equal (frame
          -- lemma (3)): only observations without types inside are compared
          let hasTy : Value → Bool := fun v => v.anyAtom fun
            | .tEq .. | .tInd .. | .sort _ | .tPi .. | .proof => true | _ => false
          if hasTy g || hasTy d then continue
          let (r0, ws) := obsParts g
          let pred := obsVal r0 (ws.set ci (K (ws[ci]?.getD .bot)))
          let (res, _) := compareVals sg sd pinned pred d rng fns er
          if let some (_, sv, dvs, _) := res then
            fs := push fs .frame (compName k) lbl s!"generic plugged: {sv}" dvs
        | .ok (g, _), .error e =>
          if !isResource e then fs := push fs .frame (compName k) lbl s!"generic: {g.pp}" s!"error: {e}" (errKey e)
        | _, _ => pure ()
  pure { status := "checked", findings := fs.toList, synOnly := synOnly, incomplete := incomplete, execAccepted := execN }

/-- The generic observations, printed (for `--show`). -/
def debugCase (o : Opts) (c : Case) : List String := Id.run do
  let prep ← match prepare o.cfg o.fuel c.decls with
    | .ok p => pure p
    | .error e => return [s!"prepare failed: {e}"]
  let mut out := prep.rejected.map fun (n, e) => s!"library {n} rejected: {e}"
  let .id A t u := prep.stmt.body | return out
  let st0 : MState := { globals := prep.globals, inds := prep.inds, cfg := o.cfg, fuel := o.fuel }
  let .ok (_, st1) := runSt (setupParams prep.stmt) st0 | return out ++ ["setup failed"]
  let W := obsPositions st1.env [t, u] o.cfg
  for k in [0:3] do
    out := out ++ [s!"generic {compName k}: {showE ((obsRun st1 A t u W true k).map (·.1))}"]
  pure out

end Ochr.Fuzz
