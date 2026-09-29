import Ochr.Check

/-!
# Fuzzer: comparing values up to the names of fresh abstract values and loans

The two paths mint fresh abstract values (generalisations, field refinements) and
loans in different orders. Before comparing, each value is renamed canonically: pinned
abstract values (the parameters and the refinement's own fresh values) keep their
index; every other abstract value, and every loan, is renumbered by first occurrence.
The unit laws of `And` (D50, conversion rules) are applied everywhere.
-/

namespace Ochr.Fuzz
open Ochr

structure CanonSt where
  pinned : List Nat
  abs : List (Nat × Nat) := []
  loans : List (Nat × Nat) := []

abbrev CanonM := StateM CanonSt

def canonAbs (s : Nat) : CanonM Nat := do
  let st ← get
  if st.pinned.contains s then return s
  match st.abs.lookup s with
  | some k => pure k
  | none =>
    let k := 1000000 + st.abs.length
    set { st with abs := (s, k) :: st.abs }
    pure k

def canonLoan (l : Nat) : CanonM Nat := do
  let st ← get
  match st.loans.lookup l with
  | some k => pure k
  | none =>
    let k := 1000000 + st.loans.length
    set { st with loans := (l, k) :: st.loans }
    pure k

mutual
partial def canonV : Value → CanonM Value
  | .succ v => return .succ (← canonV v)
  | .pair a b => return .pair (← canonV a) (← canonV b)
  | .clo cs t => return .clo (← cs.mapM canonV) (← canonT t)
  | .borrow l v => return .borrow (← canonLoan l) (← canonV v)
  | .loan l => return .loan (← canonLoan l)
  | .abs s => return .abs (← canonAbs s)
  | .sealed t => return .sealed (← canonT t)
  | .tProd a b => return .tProd (← canonV a) (← canonV b)
  | .tEq A a b => return .tEq (← canonV A) (← canonV a) (← canonV b)
  | .tRef a => return .tRef (← canonV a)
  | .tPi cs t => return .tPi (← cs.mapM canonV) (← canonT t)
  | .ind t c h ps fs => return .ind t c h (← ps.mapM canonV) (← fs.mapM canonV)
  -- D50: the unit laws `And(True, P) ≡ P ≡ And(P, True)` are conversion, not normalisation,
  -- so a refined value may keep an `And(False, True)` that the direct path built as `False`
  | .tInd "And" [a, b] => return mkAnd (← canonV a) (← canonV b)
  | .tInd n as => return .tInd n (← as.mapM canonV)
  | v => pure v

partial def canonT (t : Term) : CanonM Term := do
  let go := canonT
  match t with
  | .val v => return .val (← canonV v)
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
  | .prod a b => return .prod (← go a) (← go b)
  | .pair a b => return .pair (← go a) (← go b)
  | .cong a b => return .cong (← go a) (← go b)
  | .ascribe a b => return .ascribe (← go a) (← go b)
  | .eq a b c => return .eq (← go a) (← go b) (← go c)
  | .id a b c => return .id (← go a) (← go b) (← go c)
  | .prim n as => return .prim n (← as.mapM go)
  | .ctor ty c h ps as => return .ctor ty c h (← ps.mapM go) (← as.mapM go)
  | .tind n as => return .tind n (← as.mapM go)
  | .matchInd p ty as => return .matchInd p ty (← as.mapM fun (h, a) => do pure (h, ← go a))
  | _ => pure t
end

def canon (pinned : List Nat) (v : Value) : Value := (canonV v |>.run { pinned := pinned }).1

/-- The abstract values occurring in a value (with repetition). -/
def absIn (v : Value) : List Nat := Id.run do
  let mut out := []
  let c := (canonV v |>.run { pinned := [] }).2
  for (s, _) in c.abs do out := s :: out
  pure out

/-- The loans occurring in a value. -/
def loansIn (v : Value) : List Nat := ((canonV v |>.run { pinned := [] }).2.loans.map (·.1))

/-- Is a value ground: no abstract values, loans or sealed programs? -/
def groundV (v : Value) : Bool :=
  !v.anyAtom fun | .abs _ | .loan _ | .sealed _ | .borrow .. => true | _ => false

end Ochr.Fuzz
