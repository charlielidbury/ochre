import OchrMeta.Val

/-! # Environments, [End], [Access]

An environment is a stack of frames (head = top frame); a frame is a list of bindings (head =
most recent).  Source variables are looked up in the top frame only (there are no closures,
so a body only names its own frame).  A borrow is *held* by a binding whose content is
`borrow_ℓ v` at top level (no borrows inside data, RULES §1 scope).  The machine state also
carries the fresh-name counter for loans, so that fresh names do not depend on the part of
the environment a run cannot see (this is what makes the frame lemma an equation). -/

namespace OchrMeta

abbrev Frame := List (Var × Val)
abbrev Env := List Frame

structure St where
  env : Env
  next : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Machine results.  `stuck`: the run reached a match on a neutral (and was not closed off);
`oof`: out of fuel. -/
inductive Res where
  | ok (s : St) (v : Val)
  | stuck
  | err
  | oof
  deriving Repr, Inhabited, DecidableEq

namespace Res
def bind : Res → (St → Val → Res) → Res
  | ok s v, k => k s v
  | stuck, _ => stuck
  | err, _ => err
  | oof, _ => oof
def map (F : St → St) : Res → Res
  | ok s v => ok (F s) v
  | r => r
@[simp] theorem bind_ok (s : St) (v : Val) (k : St → Val → Res) : (ok s v).bind k = k s v := rfl
@[simp] theorem bind_stuck (k : St → Val → Res) : stuck.bind k = stuck := rfl
@[simp] theorem bind_err (k : St → Val → Res) : err.bind k = err := rfl
@[simp] theorem bind_oof (k : St → Val → Res) : oof.bind k = oof := rfl
@[simp] theorem map_ok (F : St → St) (s : St) (v : Val) : (ok s v).map F = ok (F s) v := rfl
@[simp] theorem map_stuck (F : St → St) : stuck.map F = stuck := rfl
@[simp] theorem map_err (F : St → St) : err.map F = err := rfl
@[simp] theorem map_oof (F : St → St) : oof.map F = oof := rfl
end Res

def Val.isBorrowOf (l : Nat) : Val → Bool
  | .borrow m _ => m == l
  | _ => false

/-- A holder of `borrow_ℓ` becomes `⊥`. -/
def Val.clearB (l : Nat) (v : Val) : Val := if v.isBorrowOf l then .moved else v

namespace Frame
def mapVals (g : Val → Val) (F : Frame) : Frame := F.map fun b => (b.1, g b.2)
def set (x : Var) (v : Val) : Frame → Frame
  | [] => []
  | (y, w) :: F => if y = x then (y, v) :: F else (y, w) :: set x v F
/-- Remove the first binding of `x`, returning its content. -/
def remove (x : Var) : Frame → Option (Val × Frame)
  | [] => none
  | (y, w) :: F => if y = x then some (w, F) else (remove x F).map fun (v, F') => (v, (y, w) :: F')
def holds (l : Nat) (F : Frame) : Bool := F.any fun b => b.2.isBorrowOf l
def holderContent (l : Nat) : Frame → Option Val
  | [] => none
  | (_, .borrow m w) :: F => if m = l then some w else holderContent l F
  | _ :: F => holderContent l F
def nb : Frame → Nat
  | [] => 0
  | (_, v) :: F => v.nb + nb F
def loans : Frame → List Nat
  | [] => []
  | (_, v) :: F => v.loans ++ loans F
def borrows : Frame → List Nat
  | [] => []
  | (_, v) :: F => v.borrows ++ borrows F
end Frame

namespace Env
def mapVals (g : Val → Val) (Ω : Env) : Env := Ω.map (Frame.mapVals g)
def holds (l : Nat) (Ω : Env) : Bool := Ω.any (Frame.holds l)
def holderContent (l : Nat) : Env → Option Val
  | [] => none
  | F :: Ω => (F.holderContent l).or (holderContent l Ω)
def clearHolder (l : Nat) : Env → Env := mapVals (Val.clearB l)
def substLoan (l : Nat) (w : Val) : Env → Env := mapVals (Val.substLoan l w)
def nb : Env → Nat
  | [] => 0
  | F :: Ω => F.nb + nb Ω
def loans : Env → List Nat
  | [] => []
  | F :: Ω => F.loans ++ loans Ω
def borrows : Env → List Nat
  | [] => []
  | F :: Ω => F.borrows ++ borrows Ω
/-- All loan and borrow names occurring. -/
def names (Ω : Env) : List Nat := Ω.flatten.flatMap fun b => b.2.names
end Env

namespace St
def lookup (s : St) (x : Var) : Option Val := s.env.head?.bind (·.lookup x)
def modTop (g : Frame → Frame) (s : St) : St :=
  match s.env with
  | [] => s
  | F :: Ω => { s with env := g F :: Ω }
def setVar (x : Var) (v : Val) (s : St) : St := s.modTop (Frame.set x v)
def bind (x : Var) (v : Val) (s : St) : St := s.modTop ((x, v) :: ·)
def unbind (x : Var) (s : St) : Option (Val × St) :=
  match s.env with
  | [] => none
  | F :: Ω => (F.remove x).map fun (v, F') => (v, { s with env := F' :: Ω })
def push (F : Frame) (s : St) : St := { s with env := F :: s.env }
def fresh (s : St) : Nat × St := (s.next, { s with next := s.next + 1 })
def live (s : St) (l : Nat) : Bool := s.env.holds l
end St

/-- [End ℓ] with a given content `w` (the holder already consumed): substitute `w` for every
`loan_ℓ`.  Refused (an error) if `w` contains a borrow, which cannot happen in a well-formed
environment (borrowed content is borrow-free) and makes [Access] terminate. -/
def endWith (l : Nat) (w : Val) (s : St) : Option St :=
  if w.nb = 0 then some { s with env := s.env.substLoan l w } else none

/-- [End ℓ]: the holder of `borrow_ℓ w` becomes `⊥` and `w` is substituted for `loan_ℓ`. -/
def endBorrow (l : Nat) (s : St) : Option St :=
  match s.env.holderContent l with
  | none => none
  | some w => endWith l w { s with env := s.env.clearHolder l }

inductive WalkRes where
  | found (l : Nat)
  | done (v : Val)
  | stuck
  | err

def headLoan (live : Nat → Bool) : Val → Option Nat
  | .loan l => if live l then some l else none
  | _ => none

/-- Walk the path from a root content, reporting the first live loan met on the path or as a
head, or (`deep`) anywhere inside the final content. -/
def walk (live : Nat → Bool) (deep : Bool) : Val → List Proj → WalkRes
  | v, [] => match headLoan live v with
    | some l => .found l
    | none => if deep then (match v.firstLive live with | some l => .found l | none => .done v) else .done v
  | v, pr :: ps => match headLoan live v with
    | some l => .found l
    | none => match pr.step v with
      | .ok w => walk live deep w ps
      | .stuck => .stuck
      | .err => .err

end OchrMeta
