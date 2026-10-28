import Ochr.Located

/-! Phase 1b probe (notes/totality-census.md): Machine.lean's `substV`, `substT`, `substEnv`,
`nfSealed`, converted by a regex to an explicit structurally decreasing `fuel`, with stubs for
`eval`, `mkEqM`, `canonNeutral`. `lake env lean Scratch/TotalProbe/Slice.lean`. -/
namespace Ochr.TotalProbe.Slice
open Ochr

mutual
def substV (fuel : Nat) (x r : Value) (v : Value) : M Value := do
  let fuel' + 1 := fuel | err "out of fuel"   -- FUEL-OUTCOME
  if !(v.anyAtom (· == x)) then return v
  if v == x then return r
  match v with
  | .abs _ | .loan _ => return (if v == x then r else v)
  | .succ w => return .succ (← substV fuel' x r w)
  | .borrow l w => return .borrow l (← substV fuel' x r w)
  | .clo cs t => return .clo (← cs.mapM (substV fuel' x r)) (← substT fuel' x r t)
  | .tPi cs t => return .tPi (← cs.mapM (substV fuel' x r)) (← substT fuel' x r t)
  | .sealed t => nfSealed fuel' (← substT fuel' x r t)
  | .tEq A a b => mkEqM fuel' (← substV fuel' x r A) (← substV fuel' x r a) (← substV fuel' x r b)
  | .tInd n as => return mkTInd n (← as.mapM (substV fuel' x r)) (← get).cfg.unitNorm
  | .tRef A => return .tRef (← substV fuel' x r A)
  | .ind t c h ps fs => return .ind t c h (← ps.mapM (substV fuel' x r)) (← fs.mapM (substV fuel' x r))
  | _ => return v
termination_by structural fuel


def substT (fuel : Nat) (x r : Value) (t : Term) : M Term := do
  let fuel' + 1 := fuel | err "out of fuel"   -- FUEL-OUTCOME
  if !(t.anyAtom (· == x)) then return t
  let go := substT fuel' x r
  match t with
  | .val v => return .val (← substV fuel' x r v)
  | .assign p u => return .assign p (← go u)
  | .letIn h u w => return .letIn h (← go u) (← go w)
  | .seq u w => return .seq (← go u) (← go w)
  | .matchNat p z s => return .matchNat p (← go z) (← go s)
  | .pi hs ds c => return .pi hs (← ds.mapM go) (← go c)
  | .fix h hs ds c d b => return .fix h hs (← ds.mapM go) (← go c) d (← go b)
  | .call f as hd => return .call (← go f) (← as.mapM go) hd
  | .succ u => return .succ (← go u)
  | .fst u => return .fst (← go u)
  | .snd u => return .snd (← go u)
  | .ref u => return .ref (← go u)
  | .cong a b => return .cong (← go a) (← go b)
  | .ascribe a b => return .ascribe (← go a) (← go b)
  | .eq a b c => return .eq (← go a) (← go b) (← go c)
  | .id a b c => return .id (← go a) (← go b) (← go c)
  | .prim n as => return .prim n (← as.mapM go)
  | .ctor ty c h ps as => return .ctor ty c h (← ps.mapM go) (← as.mapM go)
  | .tind n as => return .tind n (← as.mapM go)
  | .matchInd p ty as => return .matchInd p ty (← as.mapM fun (h, a) => do pure (h, ← go a))
  | _ => return t
termination_by structural fuel

/-- Substitute in every value of Ω; with `types`, also in the stored types, the types
of abstract values and the goal ([Split]: "applied to Ω, the goal and all stored
types"). -/

def substEnv (fuel : Nat) (x r : Value) (types : Bool) : M Unit := do
  let fuel' + 1 := fuel | err "out of fuel"   -- FUEL-OUTCOME
  for p in allPos (← get).env do
    setAt p (← substV fuel' x r (← getAt p))
    if types then
      if let .bind f i := p then
        if let some T := (← get).env[f]!.binds[i]!.ty then
          -- a type's sealed programs re-run as types: erased, reads copy (D53, fuzz-port RN)
          let T' ← withErased (substV fuel' x r T)
          modifyFrame f fun fr => { fr with binds := fr.binds.modify i ({ · with ty := some T' }) }
  if types then
    withErased do
      let tys := (← get).absTy
      let mut tys' := #[]
      for T in tys do tys' := tys'.push (← substV fuel' x r T)
      modify fun s => { s with absTy := tys' }
      if let some g := (← get).goal then
        let g' ← substV fuel' x r g
        modify fun s => { s with goal := some g' }
termination_by structural fuel

/-- [Seal] `nf(⌈t⌉)`: run `t` from the empty environment. Its head call is marked
(`Term.call _ _ true`) and is not eligible for [Close]; loans whose borrow is outside
the run are inert (they have no borrow in the run's Ω). If the run completes, the
result is its value; if it is stuck, `⌈t⌉` (its embedded values are already normal). -/

def nfSealed (fuel : Nat) (t : Term) : M Value := do
  let fuel' + 1 := fuel | err "out of fuel"   -- FUEL-OUTCOME
  let saved ← get
  -- bounded like calls, so that a normalisation loop (breaker-fresh-v16 X5 without D39)
  -- is an error rather than a stack overflow
  if saved.depth ≥ 2000 then err "normalisation depth exceeded (a sealed program that re-closes itself)"
  modify fun s => { s with env := #[{}], depth := s.depth + 1 }
  -- D53: a sealed program re-runs with runtime semantics (moves, ⊥ checks); only its final
  -- read of a cell (`peek`, closeCall's `K`) is an observation, and copies
  let r ← tryCatch (do let (v, _) ← eval fuel' false t; pure (some v)) fun e =>
    match e with
    | .stuck f _ => do modify (fun s => { s with fuel := f }); pure none
    | e@(.error ..) => throw e
  restoreKeep saved
  match r with
  | some v => pure v
  | none => canonNeutral fuel' (.sealed t)
termination_by structural fuel


def eval (fuel : Nat) (typed : Bool) (t : Term) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | err "out of fuel"
  match t with
  | .val v => return (← substV fuel' v v v, none)
  | _ => stuckNow
termination_by structural fuel

def mkEqM (fuel : Nat) (A a b : Value) : M Value := do
  let fuel' + 1 := fuel | err "out of fuel"
  return .tEq (← substV fuel' A A A) a b
termination_by structural fuel

def canonNeutral (fuel : Nat) (v : Value) : M Value := do
  let fuel' + 1 := fuel | err "out of fuel"
  match v with
  | .sealed t => return .sealed (← substT fuel' v v t)
  | v => pure v
termination_by structural fuel
end

end Ochr.TotalProbe.Slice
