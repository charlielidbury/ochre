/-!
# The first-order fragment "FO" of Ochr core v1.3: syntax and runtime values

Scope (meta-model-v1 §3.1): first-order data (`Nat`, `Unit`, pairs), places `x | *p | p.1 | p.2`,
`&p`, `:=`, `let`, `;`, `match p { Z ⇒ t | S y ⇒ u }` (with `y` an alias of the place `p.1`),
saturated calls to named n-ary definitions (possibly recursive, possibly *opaque* = no body,
standing in for abstract functions), results that are data or `&T`, and `erase t` for a
Prop-typed block.  There are no closures, no Π, no `Id`/`Eq` in the object language:
observations are meta-level functions.

Sealed programs are represented *structurally*: `⌈L; C; K⌉` is determined by the head function
`f`, the argument tuple (the contents `uᵢ` at borrow positions, the values `wⱼ` elsewhere),
the tail `K` (one of the four rows of the [Close] table) and, for the returned-borrow fill,
the value `w` written through the returned borrow (initially the hole `loan_k`).  The argument
list is encoded as a right-nested tuple of `Val.pair`s ending in `Val.unit`, so `Val` is a plain
(non-nested) inductive type.
-/

namespace OchrMeta

/-- Variable names.  `nm` are source names; the others are machine-generated and cannot clash
with source names: argument temporaries ([Call]), frame-lemma ports / generic-call owners,
and the fixed binders `cᵢ`, `h`, `r` of a sealed program. -/
inductive Var where
  | nm (s : String)
  | tmp (i : Nat)
  | port (l : Nat)
  | arg (i : Nat)
  | hole
  | rb
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : Coe String Var := ⟨Var.nm⟩

/-- One projection step of a place. `fst` is RULES' `p.1`: the predecessor of `S v`, or the first
component of a pair. -/
inductive Proj where
  | deref | fst | snd
  deriving DecidableEq, Repr, Inhabited

inductive Place where
  | var (x : Var)
  | deref (p : Place)
  | fst (p : Place)
  | snd (p : Place)
  deriving DecidableEq, Repr, Inhabited

namespace Place
def root : Place → Var
  | var x => x | deref p => p.root | fst p => p.root | snd p => p.root
/-- Projections from the root outwards. -/
def path : Place → List Proj
  | var _ => [] | deref p => p.path ++ [.deref] | fst p => p.path ++ [.fst] | snd p => p.path ++ [.snd]
/-- Replace the root variable `y` by the place `q` (the alias of a `match` arm). -/
def substVar (y : Var) (q : Place) : Place → Place
  | var x => if x = y then q else var x
  | deref p => deref (substVar y q p) | fst p => fst (substVar y q p) | snd p => snd (substVar y q p)
end Place

inductive Ty where
  | nat | unit | pair (a b : Ty) | ref (t : Ty) | prop
  deriving DecidableEq, Repr, Inhabited

inductive Term where
  | read (p : Place)
  | borrow (p : Place)
  | assign (p : Place) (t : Term)
  | letIn (x : Var) (t u : Term)
  | seq (t u : Term)
  | zero
  | succ (t : Term)
  | unit
  | pair (t u : Term)
  | mtch (p : Place) (tz : Term) (y : Var) (ts : Term)
  /-- A saturated call.  `canClose = false` only for the head call `C` of a sealed program
  being re-run by [Seal] (D9: the head call unfolds once and is not closed off again). -/
  | call (f : String) (args : List Term) (canClose : Bool := true)
  /-- A Prop-typed block (P2: erased; runs on a private copy, so it has no effect). -/
  | erase (t : Term)
  deriving Repr, Inhabited

/-- The tail of a sealed program `⌈L; C; K⌉`, one per row of the [Close] table.
* `res`    : `⌈L; C⌉`                      (result of a call with borrow-free result)
* `fin i`  : `⌈L; C; cᵢ⌉`                  (final content of the i-th borrowed place)
* `cur`    : `⌈L; let r = C; *r⌉`          (current content of a returned borrow)
* `back i` : `⌈L; let r = C; *r := w; cᵢ⌉` (final content of place i, `w` the value written back) -/
inductive SealK where
  | res | fin (i : Nat) | cur | back (i : Nat)
  deriving DecidableEq, Repr, Inhabited

inductive Val where
  | zero
  | succ (v : Val)
  | unit
  | pair (v w : Val)
  /-- the (irrelevant) value of a proof -/
  | star
  | borrow (l : Nat) (v : Val)
  | loan (l : Nat)
  /-- `⊥`: a place that has been moved out of -/
  | moved
  /-- `σ`: an abstract value -/
  | abs (a : Nat)
  /-- a sealed program; `w` is meaningful only for `SealK.back` (else `unit`) -/
  | sealed (f : String) (args : Val) (k : SealK) (w : Val)
  deriving DecidableEq, Repr, Inhabited

namespace Val
def ofList : List Val → Val
  | [] => unit
  | v :: vs => pair v (ofList vs)
def toList : Val → List Val
  | pair v vs => v :: toList vs
  | _ => []
def ofNat : Nat → Val
  | 0 => zero
  | n+1 => succ (ofNat n)
end Val

structure FunDef where
  params : List (Var × Ty)
  ret : Ty
  /-- `none`: an opaque (abstract) function; a call to it is stuck at once. -/
  body : Option Term
  /-- the declared decreasing parameter (`by xⱼ`), if recursive -/
  recPos : Option Nat := none
  deriving Repr, Inhabited

abbrev Prog := List (String × FunDef)

def Prog.find (P : Prog) (f : String) : Option FunDef := P.lookup f

end OchrMeta
