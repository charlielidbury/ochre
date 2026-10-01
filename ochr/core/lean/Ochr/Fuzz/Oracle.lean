import Ochr.Fuzz.Refine

/-!
# Fuzzer: the oracles

For a statement `Id A t u` over parameters, with G the observations at the generic
call and D those at a refinement or instance α (the direct path), and R = G refined by
α and re-normalised (the symbolic path), the paper's Theorem (schedule independence
and naturality, part 2) says R = D exactly (observations are taken after resolution).
Findings:
* `nat`: R ≠ D (on the ground instances of any remaining abstract values);
* `false`: the generic `Id` type is `⊤` (so `refl` proves it) but an instance's is not:
  a closed proof of a false proposition;
* `verdict`: G succeeds but the direct path errors (a borrow error, a type error);
* `renorm`: re-normalising G at α errors, the direct path succeeds;
* `escape`: G mentions an abstract value that is neither a parameter nor recorded as a
  generalisation, or a loan survives resolution;
* `adequacy`: at a ground instance, the typed direct run and the untyped machine (what
  compiled code does) disagree, or the typed run succeeds and the machine errors.
-/

namespace Ochr.Fuzz
open Ochr

inductive Kind where
  | nat | falseProof | verdict | renorm | escape | adequacy | frame | conv | truth | irrel | exec | rule
deriving BEq, Inhabited, Repr

def Kind.name : Kind → String
  | .nat => "nat" | .falseProof => "false" | .verdict => "verdict" | .renorm => "renorm"
  | .escape => "escape" | .adequacy => "adequacy" | .frame => "frame" | .conv => "conv" | .truth => "truth"
  | .irrel => "irrel" | .exec => "exec" | .rule => "rule"

def Kind.all : List Kind := [.nat, .falseProof, .verdict, .renorm, .escape, .adequacy, .frame, .conv, .truth, .irrel, .exec, .rule]

structure Finding where
  kind : Kind
  comp : String
  where_ : String
  symbolic : String
  direct : String
  reason : String := ""     -- for errors: the message with numbers and names stripped
deriving Inhabited

/-- An error message as a class: digits, places and short names dropped. -/
def errKey (e : String) : String :=
  let e := String.ofList (e.toList.filter fun c => !c.isDigit)
  let ws := (e.splitOn " ").filter fun w =>
    w.length > 2 && !(w.any fun c => c == '*' || c == '(' || c == '.' || c == '⌈' || c == '_')
  " ".intercalate (ws.take 6)

def Finding.key (f : Finding) : String :=
  if f.reason == "" then f.kind.name else s!"{f.kind.name}: {f.reason}"

def Finding.show (f : Finding) : String :=
  s!"[{f.key}] {f.comp} at {f.where_}\n    symbolic path: {f.symbolic}\n    direct path:   {f.direct}"

structure CaseResult where
  status : String
  findings : List Finding := []
  synOnly : Nat := 0       -- syntactically different, equal on every ground completion
  incomplete : Nat := 0    -- the generic path errs where a direct path succeeds
  execAccepted : Nat := 0  -- how many of the statement's sides the checker accepts as data functions
deriving Inhabited

def Except.isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def showE : Except String Value → String
  | .ok v => v.pp
  | .error e => s!"error: {e}"

/-- Run one observation component, keeping the final state. -/
def obsRun (st : MState) (A t u : Term) (W : List Pos) (typed : Bool) (k : Nat) :
    Except String (Value × MState) :=
  -- the observations are what the statement's `Id` type is made of, and a type is evaluated as
  -- the checker evaluates a goal: erased, on a private copy (`evalType`). Under D53 this
  -- matters: erased reads copy, so a side of `Id` never moves out of an owner.
  let act : M Value := match k with
    | 0 => stmtCopy do let A' ← evalType A; let (r, ws) ← observe typed t A' W; pure (obsVal r ws)
    | 1 => stmtCopy do let A' ← evalType A; let (r, ws) ← observe typed u A' W; pure (obsVal r ws)
    | _ => stmtCopy do let (v, _) ← eval typed (.id A t u); pure v
  runSt act st

/-- D68: where the symbolic observation holds `⊥` (a place a stuck block took by move, which
the ground run's arm may not have moved), take the direct path's value. -/
partial def fillHoles (r d : Value) : Value :=
  match r, d with
  | .bot, _ => d
  | .succ a, .succ b => .succ (fillHoles a b)
  | .ind t c h ps fs, .ind t' c' _ _ gs =>
    if t == t' && c == c' && fs.length == gs.length then .ind t c h ps ((fs.zip gs).map fun (a, b) => fillHoles a b) else r
  | .borrow l a, .borrow _ b => .borrow l (fillHoles a b)
  | _, _ => r

/-- Compare the symbolic path's value `r` (from state `sR`) with the direct path's `d`
(from `sD`). Returns a finding kind with the two values printed and, for an error on
one side, the error's class, or `none`; the Bool says the two differ syntactically but
agree on every ground completion. -/
def compareVals (sR sD : MState) (pinned : List Nat) (r d : Value) (rng : Rng)
    (fns : List (Nat × List Value) := []) (erased : Bool := true) :
    Option (Kind × String × String × String) × Bool := Id.run do
  -- D68: the symbolic path's equations over a moved place are stuck (`mkEqM`), so it proves
  -- nothing about that place: fail-safe. Compare the rest; a hole left inside an equation
  -- (the `Id` component) is such a stuck equation
  let r := fillHoles r d
  if r.hasHole then return (none, false)
  if canon pinned r == canon pinned d then return (none, false)
  -- abstract values recorded as generalisations (by re-normalisation) are names, not escapes
  let recR := sR.neutrals.map (·.2) ++ sR.etaRefs.flatMap (absIn ·.2)
  let recD := sD.neutrals.map (·.2) ++ sD.etaRefs.flatMap (absIn ·.2)
  if (absIn r).any (fun σ => !pinned.contains σ && !recR.contains σ) ||
     (absIn d).any (fun σ => !pinned.contains σ && !recD.contains σ) then
    return (some (.escape, r.pp, d.pp, ""), false)
  if groundV r && groundV d then
    let why := if acNorm (canon pinned r) == acNorm (canon pinned d) then "conjunction order" else ""
    return (some (.nat, r.pp, d.pp, why), false)
  let recVals := sR.neutrals.map (·.1) ++ sD.neutrals.map (·.1)
  for γ in completions sR pinned ([r, d] ++ recVals) 4 rng fns do
    let lbl := ", ".intercalate (γ.map fun (σ, v) => s!"σ{σ} := {v}")
    match refineVal sR sR.neutrals γ r erased, refineVal sD sD.neutrals γ d erased with
    | .ok r', .ok d' =>
      -- D68: a completion that leaves the symbolic value with a moved place inside an equation
      -- is a stuck equation there (`mkEqM`): the symbolic path proves nothing: fail-safe
      if (fillHoles r' d').hasHole then continue
      -- a completion that leaves an abstract value (a function parameter with no instance in
      -- the library) can only compare normal forms, which may differ in where they are stuck
      if canon pinned r' != canon pinned d' && groundV r' && groundV d' then
        -- the same conjuncts in another order (`Id` lists owners in the order of Ω): class R6
        let why := if acNorm (canon pinned r') == acNorm (canon pinned d') then "conjunction order" else ""
        return (some (.nat, s!"{r.pp}  ⟶[{lbl}]  {r'.pp}", s!"{d.pp}  ⟶[{lbl}]  {d'.pp}", why), false)
    | .ok r', .error e => if !isResource e then
        return (some (.verdict, s!"{r.pp} ⟶[{lbl}] {r'.pp}", s!"{d.pp} ⟶[{lbl}] error: {e}", errKey e), false)
    -- the symbolic re-run errs at [Drop] of a block's own parameter: a known incompleteness
    -- that fails safe (notes/lean-checker.md §57)
    | .error e, .ok d' => if !isResource e && !isInFlightDrop e then
        return (some (.renorm, s!"{r.pp} ⟶[{lbl}] error: {e}", s!"{d.pp} ⟶[{lbl}] {d'.pp}", errKey e), false)
    | _, _ => pure ()
  pure (none, true)

end Ochr.Fuzz
