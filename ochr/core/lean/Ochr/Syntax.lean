/-!
# Ochr core: syntax and runtime values (RULES.md §1, §2)

Terms use de Bruijn indices. A variable is always the root of a *place*
(`x | *p | p.1 | p.2`), so reading a variable is `Term.place (.var i)`.
Binder names are kept only as `Hint`s, whose `BEq` is trivially true: two terms
that differ only in binder names are `==`. That is α-equivalence for free, and
it is what makes "same normal form" a structural `==` (RULES P1).

Index layout of the frames the machine pushes (oldest binding first):
* a function body runs in `[cap₁ … capₘ, self, x₁ … xₙ]`;
* the types of a Π / fix (domains, codomain) are evaluated in `[cap₁ … capₘ, x₁ … xₙ]`
  (the function itself is not in scope in its own type);
* `let x = t; u` pushes `x` for `u`. Match arms bind nothing: the surface resolver
  replaces a pattern variable `y` by the sub-place `p.1` it aliases (RULES §1).
-/

namespace Ochr

/-- A binder name, for printing only. Equality ignores it. -/
structure Hint where
  name : String
deriving Inhabited, Repr

instance : BEq Hint := ⟨fun _ _ => true⟩

/-- A constructor field, as a pattern variable denotes it: field `idx` of constructor
`ctor` of the inductive type `ty` (v2.0: the place knows its constructor, so its type
is known without inspecting the content, which for a proof is `⋆`). `name` is for
printing only. -/
structure FieldRef where
  ty : String
  ctor : Nat
  idx : Nat
  name : String
deriving Inhabited, Repr

instance : BEq FieldRef := ⟨fun a b => a.ty == b.ty && a.ctor == b.ctor && a.idx == b.idx⟩

/-- What a declared type says, read off its term without normalising (D55, and the
syntactic erasure pre-pass): the sort `l` itself (whatever has it is a type), a
proposition (whatever has it is a proof), a Π-type with what its codomain says, a borrow
type, or anything else (data). `any` is the type of a zero-arm match, which agrees with
every other.

D80: data is read further, for copy-or-move and η at `Unit` (`Decide.declCopy`): `Unit`
itself, a data inductive with what its type arguments say as types, or the alternatives a
type function's or a match's arms give when they differ (the type is one of them). `other` is
data the reader cannot see through (a type parameter, `Nat`, an unknown). These three are data
to every other decision: no erasure class, row or proof flag reads them. -/
inductive DeclInfo where
  | sort (l : Nat)
  | prop
  | pi (cod : DeclInfo)
  | ref (A : DeclInfo)
  | unit
  | ind (n : String) (args : List DeclInfo)
  | alt (ds : List DeclInfo)
  | other
  | any
  | conflict    -- a match whose arms disagree about being proofs: it has no declared type (D63)
deriving Inhabited

-- written out, not derived: a derived `BEq` of a nested inductive is `opaque` (all checker code
-- is total)
mutual
def DeclInfo.beq : DeclInfo → DeclInfo → Bool
  | .sort l, .sort m => l == m
  | .prop, .prop | .unit, .unit | .other, .other | .any, .any | .conflict, .conflict => true
  | .pi a, .pi b | .ref a, .ref b => a.beq b
  | .ind n as, .ind m bs => n == m && DeclInfo.beqList as bs
  | .alt as, .alt bs => DeclInfo.beqList as bs
  | _, _ => false
termination_by structural d => d

def DeclInfo.beqList : List DeclInfo → List DeclInfo → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && DeclInfo.beqList as bs
  | _, _ => false
termination_by structural as => as
end

instance : BEq DeclInfo := ⟨DeclInfo.beq⟩

/-- D80: a data reading the reader saw through (`Unit`, an inductive, alternatives), as opposed
to the readings the erasure decisions read. -/
def DeclInfo.isData : DeclInfo → Bool
  | .unit | .ind .. | .alt _ => true
  | _ => false

/-- D80: arms whose readings `ds` agree only on data (`d`, their agreement, is `other`) read as
their alternatives: a type function's call, or a match, whose arms are different data types
has one of their types. -/
def DeclInfo.joinAlt (ds : List DeclInfo) (d : DeclInfo) : DeclInfo :=
  if d != .other then d else
  let ds := ds.filter (· != .any)
  if ds.isEmpty || !ds.all DeclInfo.isData then d else
  .alt ((ds.flatMap fun | .alt es => es | e => [e]).foldl (fun acc e => if acc.contains e then acc else acc ++ [e]) [])

/-- A proof: a value of a proposition, or a function into proofs (impredicative `Prop`). -/
def DeclInfo.isProof : DeclInfo → Bool
  | .prop => true
  | .pi r => r.isProof
  | _ => false

mutual
/-- Places `p ::= x | *p | p.i | p.g`. `p.i` (D81) is field `i` of the one constructor of `p`'s
type, as written (`.0` of a `Nat` is its predecessor); `p.g` is a constructor field named with
its constructor (a pattern variable). Where both name the same part, they are one place
(`stepEq`). -/
inductive Place where
  | var (i : Nat)
  | deref (p : Place)
  | proj (i : Nat) (p : Place)               -- `p.i`, a field by position (D81)
  | field (f : FieldRef) (p : Place)         -- a field of a constructor value (a pattern variable)

inductive Term where
  | place (p : Place)                         -- read `p` ([Read])
  | borrow (p : Place)                        -- `&p` ([Borrow])
  | assign (p : Place) (t : Term)             -- `p := t` ([Assign])
  | letIn (h : Hint) (t u : Term)             -- `let x = t; u` ([Let])
  | seq (t u : Term)                          -- `t; u`
  | matchNat (p : Place) (z s : Term)         -- `match p { Z => z, S y => s }`, y ≡ p.1
  | const (n : String)                        -- a top-level definition
  | val (v : Value)                           -- an embedded value (inside sealed programs, closures)
  | sort (l : Nat)                            -- `sort 0 = Prop`, `sort (i+1) = Type_i`
  | pi (hs : List Hint) (doms : List Term) (cod : Term)
  | fix (self : Hint) (hs : List Hint) (doms : List Term) (cod : Term) (dec : Option Nat) (body : Term)
                                              -- `dec`: the parameter named by `by xⱼ` (none: non-recursive)
  | call (f : Term) (args : List Term) (head : Bool)   -- `head`: the head call of a sealed program ([Seal])
  | nat | zero | succ (t : Term) | unit | tt
  | eq (A t u : Term)                         -- `Eq A t u` (primitive, in Prop, §4)
  | cong (f h : Term)
  | ref (A : Term)                            -- the borrow type `&A`
  | id (A t u : Term)                         -- `Id A t u` (§4)
  | ascribe (t A : Term)                      -- `(t : A)`
  | prim (n : String) (args : List Term)      -- `J A P h t`, `trans h k`, `symm h` (derivable from J)
  | tind (n : String) (args : List Term)      -- a declared inductive type applied to its parameters, `D(ā)`
  | ctor (ty : String) (c : Nat) (h : Hint) (ps : List Term) (args : List Term)
                                              -- `C(ā; t̄)`: parameters, then fields (D49); `ps = []`
                                              -- for a parameterised type: inferred when typed
  | matchInd (p : Place) (ty : String) (arms : List (Hint × Term))  -- one arm per constructor, in order

/-- Runtime values (RULES §2). Types are values too. -/
inductive Value where
  | zero | succ (v : Value) | unit
  | gfn (n : String)                          -- a top-level function
  | clo (caps : List Value) (t : Term) (rd : List (DeclInfo × Value))
                                              -- closure: a `fix` term closed over captured values;
                                              -- `rd`, the declared types of the frame slots its code
                                              -- does not declare, with their readings (D80, D82):
                                              -- each capture's, its binding's; for a stuck block,
                                              -- each parameter's, the place it takes
  | borrow (l : Nat) (v : Value)              -- `borrow_ℓ v`: the borrowed content lives in the borrow
  | loan (l : Nat)                            -- `loan_ℓ`: a variable bound by borrow ℓ
  | bot                                       -- `⊥`: moved out / ended
  | abs (s : Nat)                             -- `σ`: an abstract value (Lean's fvar)
  | sealed (t : Term)                         -- `⌈t⌉`: a closed program whose run is stuck
  | proof                                     -- `⋆`: every value of a proposition (proof irrelevance)
  | tNat | tUnit | tEq (A a b : Value)
  | tRef (A : Value)
  | tPi (caps : List Value) (t : Term) (rd : List (DeclInfo × Value))
                                              -- Π-type: a closure over formation-time values (P2),
                                              -- `rd` its captures' declared types and readings, as a
                                              -- closure's
  | sort (l : Nat)
  | ind (ty : String) (c : Nat) (h : Hint) (ps : List Value) (fs : List Value)
                                              -- a constructor value `C(ā; v̄)` of a data type, recording
                                              -- its parameters when known (D49; `==` ignores them, the
                                              -- type determines them); a Prop inductive's value is ⋆ (D42)
  | tInd (n : String) (args : List Value)     -- `D(ā)`; `True`, `False`, `And(P, Q)` are library inductives
end

mutual
def Place.beq : Place → Place → Bool
  | .var i, .var j => i == j
  | .deref p, .deref q => p.beq q
  | .proj i p, .proj j q => i == j && p.beq q
  | .field f p, .field g q => f == g && p.beq q
  | _, _ => false
termination_by structural p => p

def Term.beqList : List Term → List Term → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Term.beqList as bs
  | _, _ => false
termination_by structural as => as

/-- The arms of two `matchInd`s, compared by their bodies (binder names are ignored). -/
def Term.beqArms : List (Hint × Term) → List (Hint × Term) → Bool
  | [], [] => true
  | (_, a) :: as, (_, b) :: bs => a.beq b && Term.beqArms as bs
  | _, _ => false
termination_by structural as => as

def Term.beq : Term → Term → Bool
  | .place p, .place q | .borrow p, .borrow q => p.beq q
  | .assign p t, .assign q u => p.beq q && t.beq u
  | .letIn _ t u, .letIn _ t' u' => t.beq t' && u.beq u'
  | .seq t u, .seq t' u' => t.beq t' && u.beq u'
  | .matchNat p z s, .matchNat q z' s' => p.beq q && z.beq z' && s.beq s'
  | .const n, .const m => n == m
  | .val v, .val w => v.beq w
  | .sort l, .sort m => l == m
  | .pi _ ds c, .pi _ ds' c' => Term.beqList ds ds' && c.beq c'
  | .fix _ _ ds c d b, .fix _ _ ds' c' d' b' => Term.beqList ds ds' && c.beq c' && d == d' && b.beq b'
  | .call f as h, .call g bs h' => f.beq g && Term.beqList as bs && h == h'
  | .nat, .nat | .zero, .zero | .unit, .unit | .tt, .tt => true
  | .succ t, .succ u | .ref t, .ref u => t.beq u
  | .cong a b, .cong c d | .ascribe a b, .ascribe c d => a.beq c && b.beq d
  | .eq a b c, .eq d e f | .id a b c, .id d e f => a.beq d && b.beq e && c.beq f
  | .prim n as, .prim m bs => n == m && Term.beqList as bs
  | .tind n as, .tind m bs => n == m && Term.beqList as bs
  | .ctor t c _ ps as, .ctor u d _ qs bs => t == u && c == d && Term.beqList ps qs && Term.beqList as bs
  | .matchInd p t as, .matchInd q u bs => p.beq q && t == u && Term.beqArms as bs
  | _, _ => false
termination_by structural t => t

def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Value.beqList as bs
  | _, _ => false
termination_by structural as => as

def Value.beqRd : List (DeclInfo × Value) → List (DeclInfo × Value) → Bool
  | [], [] => true
  | (d, a) :: as, (e, b) :: bs => d == e && a.beq b && Value.beqRd as bs
  | _, _ => false
termination_by structural as => as

def Value.beq : Value → Value → Bool
  | .zero, .zero | .unit, .unit | .bot, .bot | .proof, .proof
  | .tNat, .tNat | .tUnit, .tUnit => true
  | .succ v, .succ w | .tRef v, .tRef w => v.beq w
  | .gfn n, .gfn m => n == m
  | .clo cs t r, .clo ds u r' => Value.beqList cs ds && t.beq u && Value.beqRd r r'
  | .tPi cs t r, .tPi ds u r' => Value.beqList cs ds && t.beq u && Value.beqRd r r'
  | .borrow l v, .borrow m w => l == m && v.beq w
  | .loan l, .loan m | .abs l, .abs m | .sort l, .sort m => l == m
  | .sealed t, .sealed u => t.beq u
  | .tEq a b c, .tEq d e f => a.beq d && b.beq e && c.beq f
  | .ind t c _ _ fs, .ind u d _ _ gs => t == u && c == d && Value.beqList fs gs
  | .tInd n as, .tInd m bs => n == m && Value.beqList as bs
  | _, _ => false
termination_by structural v => v
end

instance : BEq Place := ⟨Place.beq⟩
instance : BEq Term := ⟨Term.beq⟩
instance : BEq Value := ⟨Value.beq⟩
instance : Inhabited Place := ⟨.var 0⟩
instance : Inhabited Term := ⟨.tt⟩
instance : Inhabited Value := ⟨.unit⟩

end Ochr
