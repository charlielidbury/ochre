import OchrMeta.Syntax

/-! # Operations on values: loan substitution, renaming, occurrence, paths -/

namespace OchrMeta

mutual
def Term.substVar (y : Var) (q : Place) : Term → Term
  | .read p => .read (Place.substVar y q p)
  | .borrow p => .borrow (Place.substVar y q p)
  | .assign p t => .assign (Place.substVar y q p) (t.substVar y q)
  | .letIn x t u => .letIn x (t.substVar y q) (if x = y then u else u.substVar y q)
  | .seq t u => .seq (t.substVar y q) (u.substVar y q)
  | .zero => .zero
  | .succ t => .succ (t.substVar y q)
  | .unit => .unit
  | .pair t u => .pair (t.substVar y q) (u.substVar y q)
  | .mtch p tz z ts => .mtch (Place.substVar y q p) (tz.substVar y q) z (if z = y then ts else ts.substVar y q)
  | .call f args c => .call f (Term.substVarList y q args) c
  | .erase t => .erase (t.substVar y q)
def Term.substVarList (y : Var) (q : Place) : List Term → List Term
  | [] => []
  | t :: ts => t.substVar y q :: Term.substVarList y q ts
end

namespace Val

/-- `v[loan_l := w]`, everywhere, inside sealed programs too ([End]). -/
def substLoan (l : Nat) (w : Val) : Val → Val
  | zero => zero
  | succ v => succ (substLoan l w v)
  | unit => unit
  | pair a b => pair (substLoan l w a) (substLoan l w b)
  | star => star
  | borrow m v => borrow m (substLoan l w v)
  | loan m => if m = l then w else loan m
  | moved => moved
  | abs a => abs a
  | sealed f a k x => sealed f (substLoan l w a) k (substLoan l w x)

/-- Simultaneous substitution of loans (used for the frame lemma's ports). -/
def substSim (σ : Nat → Option Val) : Val → Val
  | zero => zero
  | succ v => succ (v.substSim σ)
  | unit => unit
  | pair a b => pair (a.substSim σ) (b.substSim σ)
  | star => star
  | borrow m v => borrow m (v.substSim σ)
  | loan m => (σ m).getD (loan m)
  | moved => moved
  | abs a => abs a
  | sealed f a k x => sealed f (a.substSim σ) k (x.substSim σ)

/-- Rename every loan name (in borrows and loans). -/
def rename (ρ : Nat → Nat) : Val → Val
  | zero => zero
  | succ v => succ (v.rename ρ)
  | unit => unit
  | pair a b => pair (a.rename ρ) (b.rename ρ)
  | star => star
  | borrow m v => borrow (ρ m) (v.rename ρ)
  | loan m => loan (ρ m)
  | moved => moved
  | abs a => abs a
  | sealed f a k x => sealed f (a.rename ρ) k (x.rename ρ)

/-- Loan occurrences, in preorder. -/
def loans : Val → List Nat
  | succ v => v.loans
  | pair a b => a.loans ++ b.loans
  | borrow _ v => v.loans
  | loan m => [m]
  | sealed _ a _ x => a.loans ++ x.loans
  | _ => []

/-- Borrow names occurring (at any depth). -/
def borrows : Val → List Nat
  | succ v => v.borrows
  | pair a b => a.borrows ++ b.borrows
  | borrow m v => m :: v.borrows
  | sealed _ a _ x => a.borrows ++ x.borrows
  | _ => []

/-- Number of `borrow` constructors: the termination measure of [Access]. -/
def nb : Val → Nat
  | succ v => v.nb
  | pair a b => a.nb + b.nb
  | borrow _ v => v.nb + 1
  | sealed _ a _ x => a.nb + x.nb
  | _ => 0

/-- The first loan (preorder) satisfying `live`. -/
def firstLive (live : Nat → Bool) : Val → Option Nat
  | succ v => v.firstLive live
  | pair a b => (a.firstLive live).or (b.firstLive live)
  | borrow _ v => v.firstLive live
  | loan m => if live m then some m else none
  | sealed _ a _ x => (a.firstLive live).or (x.firstLive live)
  | _ => none

/-- Abstract values occurring. -/
def absIds : Val → List Nat
  | succ v => v.absIds
  | pair a b => a.absIds ++ b.absIds
  | borrow _ v => v.absIds
  | abs a => [a]
  | sealed _ a _ x => a.absIds ++ x.absIds
  | _ => []

/-- A value is *neutral* at its head: an abstract value, a sealed program, or a loan
(when [Access] has not ended it, i.e. an inert loan). -/
def isNeutral : Val → Bool
  | abs _ | sealed .. | loan _ => true
  | _ => false

end Val

/-- Result of stepping one projection into a value. -/
inductive StepRes where
  | ok (v : Val)
  | stuck
  | err

def Proj.step : Proj → Val → StepRes
  | .deref, .borrow _ v => .ok v
  | .fst, .succ v => .ok v
  | .fst, .pair v _ => .ok v
  | .snd, .pair _ v => .ok v
  | _, v => if v.isNeutral then .stuck else .err

/-- Rebuild a value with its projection `pr` replaced by `new` (defined where `step` is `ok`). -/
def Proj.put : Proj → Val → Val → Option Val
  | .deref, .borrow l _, new => some (.borrow l new)
  | .fst, .succ _, new => some (.succ new)
  | .fst, .pair _ b, new => some (.pair new b)
  | .snd, .pair a _, new => some (.pair a new)
  | _, _, _ => none

def Val.get : Val → List Proj → Option Val
  | v, [] => some v
  | v, pr :: ps => match pr.step v with
    | .ok w => w.get ps
    | _ => none

def Val.set : Val → List Proj → Val → Option Val
  | _, [], new => some new
  | v, pr :: ps, new => match pr.step v with
    | .ok w => (w.set ps new).bind fun w' => pr.put v w'
    | _ => none

end OchrMeta

namespace OchrMeta
namespace Val

/-- Refinement of one abstract value: `v[σ_a := w]` (into sealed programs too). -/
def substAbs (a : Nat) (w : Val) : Val → Val
  | zero => zero
  | succ v => succ (substAbs a w v)
  | unit => unit
  | pair x y => pair (substAbs a w x) (substAbs a w y)
  | star => star
  | borrow m v => borrow m (substAbs a w v)
  | loan m => loan m
  | moved => moved
  | abs b => if b = a then w else abs b
  | sealed f x k y => sealed f (substAbs a w x) k (substAbs a w y)

/-- Loan/borrow names in order of first occurrence (preorder). -/
def names : Val → List Nat
  | succ v => v.names
  | pair a b => a.names ++ b.names
  | borrow m v => m :: v.names
  | loan m => [m]
  | sealed _ a _ x => a.names ++ x.names
  | _ => []

def toNat? : Val → Option Nat
  | zero => some 0
  | succ v => v.toNat?.map (· + 1)
  | _ => none

end Val
end OchrMeta
