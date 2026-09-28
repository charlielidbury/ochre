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
  | nat | falseProof | verdict | renorm | escape | adequacy | frame | conv
deriving BEq, Inhabited, Repr

def Kind.name : Kind → String
  | .nat => "nat" | .falseProof => "false" | .verdict => "verdict" | .renorm => "renorm"
  | .escape => "escape" | .adequacy => "adequacy" | .frame => "frame" | .conv => "conv"

def Kind.all : List Kind := [.nat, .falseProof, .verdict, .renorm, .escape, .adequacy, .frame, .conv]

structure Finding where
  kind : Kind
  comp : String
  where_ : String
  symbolic : String
  direct : String
deriving Inhabited

def Finding.show (f : Finding) : String :=
  s!"[{f.kind.name}] {f.comp} at {f.where_}\n    symbolic path: {f.symbolic}\n    direct path:   {f.direct}"

structure CaseResult where
  status : String
  findings : List Finding := []
  synOnly : Nat := 0       -- syntactically different, equal on every ground completion
  incomplete : Nat := 0    -- the generic path errs where a direct path succeeds
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
  let act : M Value := match k with
    | 0 => do let A' ← evalType A; observe typed t A' W
    | 1 => do let A' ← evalType A; observe typed u A' W
    | _ => do let (v, _) ← eval typed (.id A t u); pure v
  runSt act st

/-- Compare the symbolic path's value `r` (from state `sR`) with the direct path's `d`
(from `sD`). Returns a finding kind with the two values printed, or `none`; the Bool
says the two differ syntactically but agree on every ground completion. -/
def compareVals (sR sD : MState) (pinned : List Nat) (r d : Value) (rng : Rng) :
    Option (Kind × String × String) × Bool := Id.run do
  if canon pinned r == canon pinned d then return (none, false)
  if (absIn r ++ absIn d).any (!pinned.contains ·) then
    return (some (.escape, r.pp, d.pp), false)
  if groundV r && groundV d then return (some (.nat, r.pp, d.pp), false)
  for γ in completions sR pinned [r, d] 4 rng do
    let lbl := ", ".intercalate (γ.map fun (σ, v) => s!"σ{σ} := {v}")
    match refineVal sR [] γ r, refineVal sD [] γ d with
    | .ok r', .ok d' =>
      if canon pinned r' != canon pinned d' then
        return (some (.nat, s!"{r.pp}  ⟶[{lbl}]  {r'.pp}", s!"{d.pp}  ⟶[{lbl}]  {d'.pp}"), false)
    | .ok r', .error e => if !isResource e then
        return (some (.renorm, s!"{r.pp} ⟶[{lbl}] {r'.pp}", s!"{d.pp} ⟶[{lbl}] error: {e}"), false)
    | .error e, .ok d' => if !isResource e then
        return (some (.renorm, s!"{r.pp} ⟶[{lbl}] error: {e}", s!"{d.pp} ⟶[{lbl}] {d'.pp}"), false)
    | _, _ => pure ()
  pure (none, true)

end Ochr.Fuzz
