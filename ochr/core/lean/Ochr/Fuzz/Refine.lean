import Ochr.Fuzz.Harness

/-!
# Fuzzer: refinements and instances

A refinement substitutes, for one parameter's abstract value, a constructor applied to
fresh abstract values (`σ := Z`, `σ := S σ'`, `σ := S (S σ')`, `σ := Cons(σ₁, σ₂)`, …): a
[Split] refinement. An instance substitutes ground values for every parameter: a call
site with concrete arguments (and, for the adequacy oracle, a concrete run).
-/

namespace Ochr.Fuzz
open Ochr

structure Refinement where
  label : String
  subst : List (Nat × Value)
  ground : Bool
deriving Inhabited

def combos {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (combos rest).map (x :: ·)

/-- Small ground values of a type, smallest first. -/
partial def groundVals (inds : List IndDecl) (T : Value) (depth : Nat) : List Value :=
  match T with
  | .tNat => (List.range (if depth == 0 then 2 else 4)).map Value.ofNat
  | .tUnit => [.unit]
  | .tInd n => match inds.find? (·.name == n) with
    | none => []
    | some d => d.ctors.zipIdx.flatMap fun ((cn, fs), c) =>
      if fs.isEmpty then [Value.ind n c ⟨cn⟩ []]
      else if depth == 0 then []
      else (combos (fs.map fun (_, FT) => (groundVals inds FT (depth - 1)).take 2)).map (Value.ind n c ⟨cn⟩)
  | _ => []

/-- The [Split] shapes of a type, with fresh abstract values for the fields. -/
def shapes (T : Value) : M (List Value) := do
  match T with
  | .tNat => pure [.zero, .succ (.abs (← freshAbs .tNat)), .succ (.succ (.abs (← freshAbs .tNat)))]
  | .tInd n =>
    let d ← lookupInd n
    (List.range d.ctors.length).mapM (ctorRefinement d)
  | _ => pure []

/-- Every partial refinement of one parameter, and `nGround` instances (the first two
take every parameter's smallest, then second-smallest, value). -/
def buildRefinements (ps : Array PInfo) (nGround : Nat) (r : Rng) : M (List Refinement × Rng) := do
  let inds := (← get).inds
  let mut out : Array Refinement := #[]
  for p in ps do
    if p.kind == .proof then continue
    for v in ← shapes p.ty do
      out := out.push ⟨s!"{p.name} := {v}", [(p.σ, v)], false⟩
  let ds := ps.toList.filter (·.kind != .proof)
  let mut rng := r
  for i in [0:nGround] do
    let mut sub := #[]
    for p in ds do
      let vs := groundVals inds p.ty 2
      if vs.isEmpty then continue
      let (x, r') := rng.next
      rng := r'
      let v := if i < 2 then vs[min i (vs.length - 1)]! else vs[x.toNat % vs.length]!
      sub := sub.push (p.σ, v)
    let label := ", ".intercalate ((ds.zip sub.toList).map fun (p, (_, v)) => s!"{p.name} := {v}")
    if !(out.any fun a => a.label == label) then
      out := out.push ⟨label, sub.toList, sub.size == ds.length⟩
  pure (out.toList, rng)

/-- Ground completions of the pinned abstract values occurring in some values. -/
def completions (st : MState) (pinned : List Nat) (vs : List Value) (n : Nat) (r : Rng) :
    List (List (Nat × Value)) := Id.run do
  let occ := (vs.flatMap absIn).eraseDups.filter pinned.contains
  let mut out := #[]
  let mut rng := r
  for i in [0:n] do
    let mut sub := #[]
    for σ in occ do
      let vs := groundVals st.inds (st.absTy[σ]?.getD .tNat) 2
      if vs.isEmpty then continue
      let (x, r') := rng.next
      rng := r'
      sub := sub.push (σ, if i < 2 then vs[min i (vs.length - 1)]! else vs[x.toNat % vs.length]!)
    out := out.push sub.toList
  pure out.toList

end Ochr.Fuzz
