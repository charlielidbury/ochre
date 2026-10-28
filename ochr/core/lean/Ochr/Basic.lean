import Ochr.Syntax

/-!
# Pure helpers: numerals, the `∧` smart constructor and constructor disjointness (§4 "`Eq` computes"),
and syntactic traversals (free places, loans and abstract values inside values).
-/

namespace Ochr

def Value.ofNat : Nat → Value
  | 0 => .zero
  | n + 1 => .succ (Value.ofNat n)

def Term.ofNat : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (Term.ofNat n)

/-- The library propositions (v2.0, D45): `False`, `True` and `And` are inductive
declarations (`Check.lean`'s prelude); `⊤`, `P ∧ Q`, `⟨h, k⟩` and `refl` are notation. -/
def vTrue : Value := .tInd "True" []
def vFalse : Value := .tInd "False" []

/-- `And(True, P) ≡ P ≡ And(P, True)` (RULES §4), as a smart constructor. Since D50 the
unit laws are conversion: `mkAnd` builds only the conjunctions `Eq` computes (so `Id`'s
observation is the single interesting equation), and `unitTop` applies the laws when two
types are compared; a stored type written `True ∧ P` keeps its `And`. -/
def mkAnd : Value → Value → Value
  | .tInd "True" [], q => q
  | p, .tInd "True" [] => p
  | p, q => .tInd "And" [p, q]

/-- The unit laws at the head of a type (D50: applied by conversion only). -/
def unitTop : Value → Value
  | .tInd "And" [p, q] => mkAnd (unitTop p) (unitTop q)
  | v => v
termination_by structural v => v

mutual
/-- Does a (first-order) field type term mention the inductive `n`? (D53 prototype: a copy
type is not recursive.) -/
def Term.mentionsTInd (n : String) : Term → Bool
  | .tind m as => m == n || Term.mentionsTIndList n as
  | _ => false
termination_by structural t => t

/-- `as.any (Term.mentionsTInd n)`. -/
def Term.mentionsTIndList (n : String) : List Term → Bool
  | [] => false
  | a :: as => a.mentionsTInd n || Term.mentionsTIndList n as
termination_by structural as => as
end

/-- `And(P₁, And(P₂, … Pₖ))` with the unit laws (`[]`: `True`), for `Eq` on constructor
values and for `Id` (D52). -/
def andList : List Value → Value
  | [] => .tInd "True" []
  | [p] => p
  | p :: ps => mkAnd p (andList ps)

/-- D47: two values headed by distinct constructors of the same type (`Z` and `S _`, or
`C(…)` and `C'(…)` with `C ≠ C'`). Values of a proposition are `⋆`, never distinct. -/
def distinctCtors : Value → Value → Bool
  | .zero, .succ _ | .succ _, .zero => true
  | .ind t c _ _ _, .ind u d _ _ _ => t == u && c != d
  | _, _ => false

def Place.root : Place → Nat
  | .var i => i
  | .deref p | .fst p | .snd p | .field _ p => p.root

/-- Replace the root variable of a place by a place. -/
def Place.mapRoot (f : Nat → Place) : Place → Place
  | .var i => f i
  | .deref p => .deref (p.mapRoot f)
  | .fst p => .fst (p.mapRoot f)
  | .snd p => .snd (p.mapRoot f)
  | .field g p => .field g (p.mapRoot f)

/-- How a place occurs in a term. -/
inductive PKind where
  | read | borrow | assign | scrut
deriving BEq, Inhabited

def mp (f : Nat → Nat → Place) (c : Nat) (p : Place) : Place :=
  p.mapRoot fun j => if j < c then .var j else f c (j - c)

mutual
/-- Rewrite every *free* place root: at binder depth `c`, a root `j ≥ c` is replaced by
`f c (j - c)` (the second argument is the index in the enclosing frame). -/
def Term.mapFree (f : Nat → Nat → Place) (c : Nat) : Term → Term
  | .place p => .place (mp f c p)
  | .borrow p => .borrow (mp f c p)
  | .assign p t => .assign (mp f c p) (t.mapFree f c)
  | .letIn h t u => .letIn h (t.mapFree f c) (u.mapFree f (c + 1))
  | .seq t u => .seq (t.mapFree f c) (u.mapFree f c)
  | .matchNat p z s => .matchNat (mp f c p) (z.mapFree f c) (s.mapFree f c)
  | .pi hs ds cod =>
      .pi hs (mapDoms f c ds) (cod.mapFree f (c + ds.length))
  | .fix h hs ds cod d b =>
      .fix h hs (mapDoms f c ds) (cod.mapFree f (c + ds.length)) d (b.mapFree f (c + ds.length + 1))
  | .call g as hd => .call (g.mapFree f c) (Term.mapFreeList f c as) hd
  | .succ t => .succ (t.mapFree f c)
  | .fst t => .fst (t.mapFree f c)
  | .snd t => .snd (t.mapFree f c)
  | .ref t => .ref (t.mapFree f c)
  | .cong a b => .cong (a.mapFree f c) (b.mapFree f c)
  | .ascribe a b => .ascribe (a.mapFree f c) (b.mapFree f c)
  | .eq a b d => .eq (a.mapFree f c) (b.mapFree f c) (d.mapFree f c)
  | .id a b d => .id (a.mapFree f c) (b.mapFree f c) (d.mapFree f c)
  | .prim n as => .prim n (Term.mapFreeList f c as)
  | .ctor t k h ps as => .ctor t k h (Term.mapFreeList f c ps) (Term.mapFreeList f c as)
  | .tind n as => .tind n (Term.mapFreeList f c as)
  | .matchInd p t as => .matchInd (mp f c p) t (Term.mapFreeArms f c as)
  | t => t
termination_by structural t => t

/-- `as.map (·.mapFree f c)`. -/
def Term.mapFreeList (f : Nat → Nat → Place) (c : Nat) : List Term → List Term
  | [] => []
  | a :: as => a.mapFree f c :: Term.mapFreeList f c as
termination_by structural as => as

/-- `as.map fun (h, a) => (h, a.mapFree f c)`. -/
def Term.mapFreeArms (f : Nat → Nat → Place) (c : Nat) : List (Hint × Term) → List (Hint × Term)
  | [] => []
  | (h, a) :: as => (h, a.mapFree f c) :: Term.mapFreeArms f c as
termination_by structural as => as

/-- A telescope's domains, the `i`-th at depth `c + i`. -/
def mapDoms (f : Nat → Nat → Place) (c : Nat) : List Term → List Term
  | [] => []
  | d :: ds => d.mapFree f c :: mapDoms f (c + 1) ds
termination_by structural ds => ds
end

/-- A place of `Term.mapFreePlace`: at depth `c`, a place whose root `j ≥ c` is replaced by
`f c p'`, with `p'` re-rooted at the enclosing frame's index `j - c`. -/
def Term.mapFreePlace.fp (f : Nat → Place → Place) (c : Nat) (p : Place) : Place :=
  if p.root < c then p else f c (p.mapRoot fun j => .var (j - c))

mutual
/-- Rewrite every place with a free root: at depth `c`, a place whose root `j ≥ c` is
replaced by `f c p'`, where `p'` is the place re-rooted at the enclosing frame's index
`j - c`. -/
def Term.mapFreePlace (f : Nat → Place → Place) (c : Nat) : Term → Term
  | .place p => .place (Term.mapFreePlace.fp f c p)
  | .borrow p => .borrow (Term.mapFreePlace.fp f c p)
  | .assign p t => .assign (Term.mapFreePlace.fp f c p) (t.mapFreePlace f c)
  | .letIn h t u => .letIn h (t.mapFreePlace f c) (u.mapFreePlace f (c + 1))
  | .seq t u => .seq (t.mapFreePlace f c) (u.mapFreePlace f c)
  | .matchNat p z s => .matchNat (Term.mapFreePlace.fp f c p) (z.mapFreePlace f c) (s.mapFreePlace f c)
  | .pi hs ds cod =>
      .pi hs (Term.mapFreePlaceDoms f c ds) (cod.mapFreePlace f (c + ds.length))
  | .fix h hs ds cod d b =>
      .fix h hs (Term.mapFreePlaceDoms f c ds) (cod.mapFreePlace f (c + ds.length)) d
        (b.mapFreePlace f (c + ds.length + 1))
  | .call g as hd => .call (g.mapFreePlace f c) (Term.mapFreePlaceList f c as) hd
  | .succ t => .succ (t.mapFreePlace f c)
  | .fst t => .fst (t.mapFreePlace f c)
  | .snd t => .snd (t.mapFreePlace f c)
  | .ref t => .ref (t.mapFreePlace f c)
  | .cong a b => .cong (a.mapFreePlace f c) (b.mapFreePlace f c)
  | .ascribe a b => .ascribe (a.mapFreePlace f c) (b.mapFreePlace f c)
  | .eq a b d => .eq (a.mapFreePlace f c) (b.mapFreePlace f c) (d.mapFreePlace f c)
  | .id a b d => .id (a.mapFreePlace f c) (b.mapFreePlace f c) (d.mapFreePlace f c)
  | .prim n as => .prim n (Term.mapFreePlaceList f c as)
  | .ctor t k h ps as => .ctor t k h (Term.mapFreePlaceList f c ps) (Term.mapFreePlaceList f c as)
  | .tind n as => .tind n (Term.mapFreePlaceList f c as)
  | .matchInd p t as => .matchInd (Term.mapFreePlace.fp f c p) t (Term.mapFreePlaceArms f c as)
  | t => t
termination_by structural t => t

def Term.mapFreePlaceList (f : Nat → Place → Place) (c : Nat) : List Term → List Term
  | [] => []
  | a :: as => a.mapFreePlace f c :: Term.mapFreePlaceList f c as
termination_by structural as => as

def Term.mapFreePlaceArms (f : Nat → Place → Place) (c : Nat) : List (Hint × Term) → List (Hint × Term)
  | [] => []
  | (h, a) :: as => (h, a.mapFreePlace f c) :: Term.mapFreePlaceArms f c as
termination_by structural as => as

/-- A telescope's domains, the `i`-th at depth `c + i`. -/
def Term.mapFreePlaceDoms (f : Nat → Place → Place) (c : Nat) : List Term → List Term
  | [] => []
  | d :: ds => d.mapFreePlace f c :: Term.mapFreePlaceDoms f (c + 1) ds
termination_by structural ds => ds
end

mutual
/-- D53: take a match's arm when its scrutinee (a free place, re-rooted at the enclosing
frame) is a place `sel` knows the constructor of (`some k` for an inductive's `k`, `none` for
`S`): a stuck block's capture split into its fields (`closeOffMatch`). -/
def Term.selectArms (sel : Place → Option (Option Nat)) (c : Nat) : Term → Term
  | .matchInd p t as =>
    match (if p.root < c then none else sel (p.mapRoot fun j => .var (j - c))) with
    | some (some k) => match Term.selectArmsNth sel c k as with
      | some a => a
      | none => .matchInd p t (Term.selectArmsArms sel c as)
    | _ => .matchInd p t (Term.selectArmsArms sel c as)
  | .matchNat p z s =>
    match (if p.root < c then none else sel (p.mapRoot fun j => .var (j - c))) with
    | some none => s.selectArms sel c
    | _ => .matchNat p (z.selectArms sel c) (s.selectArms sel c)
  | .assign p t => .assign p (t.selectArms sel c)
  | .letIn h t u => .letIn h (t.selectArms sel c) (u.selectArms sel (c + 1))
  | .seq t u => .seq (t.selectArms sel c) (u.selectArms sel c)
  | .pi hs ds cod =>
      .pi hs (Term.selectArmsDoms sel c ds) (cod.selectArms sel (c + ds.length))
  | .fix h hs ds cod d b =>
      .fix h hs (Term.selectArmsDoms sel c ds) (cod.selectArms sel (c + ds.length)) d
        (b.selectArms sel (c + ds.length + 1))
  | .call g as hd => .call (g.selectArms sel c) (Term.selectArmsList sel c as) hd
  | .succ t => .succ (t.selectArms sel c)
  | .fst t => .fst (t.selectArms sel c)
  | .snd t => .snd (t.selectArms sel c)
  | .ref t => .ref (t.selectArms sel c)
  | .cong a b => .cong (a.selectArms sel c) (b.selectArms sel c)
  | .ascribe a b => .ascribe (a.selectArms sel c) (b.selectArms sel c)
  | .eq a b d => .eq (a.selectArms sel c) (b.selectArms sel c) (d.selectArms sel c)
  | .id a b d => .id (a.selectArms sel c) (b.selectArms sel c) (d.selectArms sel c)
  | .prim n as => .prim n (Term.selectArmsList sel c as)
  | .ctor t k h ps as => .ctor t k h (Term.selectArmsList sel c ps) (Term.selectArmsList sel c as)
  | .tind n as => .tind n (Term.selectArmsList sel c as)
  | t => t
termination_by structural t => t

/-- The `k`-th arm, with `selectArms` applied (`as[k]?`). -/
def Term.selectArmsNth (sel : Place → Option (Option Nat)) (c : Nat) : Nat → List (Hint × Term) → Option Term
  | 0, (_, a) :: _ => some (a.selectArms sel c)
  | k + 1, _ :: as => Term.selectArmsNth sel c k as
  | _, [] => none
termination_by structural _ as => as

def Term.selectArmsArms (sel : Place → Option (Option Nat)) (c : Nat) : List (Hint × Term) → List (Hint × Term)
  | [] => []
  | (h, a) :: as => (h, a.selectArms sel c) :: Term.selectArmsArms sel c as
termination_by structural as => as

def Term.selectArmsList (sel : Place → Option (Option Nat)) (c : Nat) : List Term → List Term
  | [] => []
  | a :: as => a.selectArms sel c :: Term.selectArmsList sel c as
termination_by structural as => as

/-- A telescope's domains, the `i`-th at depth `c + i`. -/
def Term.selectArmsDoms (sel : Place → Option (Option Nat)) (c : Nat) : List Term → List Term
  | [] => []
  | d :: ds => d.selectArms sel c :: Term.selectArmsDoms sel (c + 1) ds
termination_by structural ds => ds
end

mutual
/-- Replace every read of the whole free variable `o` (at depth `c`, the variable
`o + c`) by the closed term `u`; other occurrences stay. Used to inline a captured proof
with its type (a proof's value is ⋆, so only its type needs keeping). -/
def Term.inlineReads (t : Term) (o : Nat) (u : Term) (c : Nat) : Term :=
  match t with
  | .place (.var j) => if j == o + c then u else .place (.var j)
  | .assign p t => .assign p (t.inlineReads o u c)
  | .letIn h t w => .letIn h (t.inlineReads o u c) (w.inlineReads o u (c + 1))
  | .seq t w => .seq (t.inlineReads o u c) (w.inlineReads o u c)
  | .matchNat p z s => .matchNat p (z.inlineReads o u c) (s.inlineReads o u c)
  | .pi hs ds cod =>
      .pi hs (Term.inlineReadsDoms o u c ds) (cod.inlineReads o u (c + ds.length))
  | .fix h hs ds cod d b =>
      .fix h hs (Term.inlineReadsDoms o u c ds) (cod.inlineReads o u (c + ds.length)) d
        (b.inlineReads o u (c + ds.length + 1))
  | .call g as hd => .call (g.inlineReads o u c) (Term.inlineReadsList o u c as) hd
  | .succ t => .succ (t.inlineReads o u c)
  | .fst t => .fst (t.inlineReads o u c)
  | .snd t => .snd (t.inlineReads o u c)
  | .ref t => .ref (t.inlineReads o u c)
  | .cong a b => .cong (a.inlineReads o u c) (b.inlineReads o u c)
  | .ascribe a b => .ascribe (a.inlineReads o u c) (b.inlineReads o u c)
  | .eq a b d => .eq (a.inlineReads o u c) (b.inlineReads o u c) (d.inlineReads o u c)
  | .id a b d => .id (a.inlineReads o u c) (b.inlineReads o u c) (d.inlineReads o u c)
  | .prim n as => .prim n (Term.inlineReadsList o u c as)
  | .ctor t k h ps as => .ctor t k h (Term.inlineReadsList o u c ps) (Term.inlineReadsList o u c as)
  | .tind n as => .tind n (Term.inlineReadsList o u c as)
  | .matchInd p t as => .matchInd p t (Term.inlineReadsArms o u c as)
  | t => t
termination_by structural t

def Term.inlineReadsList (o : Nat) (u : Term) (c : Nat) : List Term → List Term
  | [] => []
  | a :: as => a.inlineReads o u c :: Term.inlineReadsList o u c as
termination_by structural as => as

def Term.inlineReadsArms (o : Nat) (u : Term) (c : Nat) : List (Hint × Term) → List (Hint × Term)
  | [] => []
  | (h, a) :: as => (h, a.inlineReads o u c) :: Term.inlineReadsArms o u c as
termination_by structural as => as

/-- A telescope's domains, the `i`-th at depth `c + i`. -/
def Term.inlineReadsDoms (o : Nat) (u : Term) (c : Nat) : List Term → List Term
  | [] => []
  | d :: ds => d.inlineReads o u c :: Term.inlineReadsDoms o u (c + 1) ds
termination_by structural ds => ds
end

/-- Clear the head marks of a sealed program's calls (to type it as an ordinary term). -/
def Term.unHead : Term → Term
  | .call f as _ => .call f as false
  | .letIn h t u => .letIn h t.unHead u.unHead
  | .seq t u => .seq t.unHead u.unHead
  | t => t
termination_by structural t => t

mutual
/-- Every place occurrence `(depth, place, kind)`, in evaluation order. -/
def Term.placeOccs (c : Nat) : Term → List (Nat × Place × PKind)
  | .place p => [(c, p, .read)]
  | .borrow p => [(c, p, .borrow)]
  | .assign p t => t.placeOccs c ++ [(c, p, .assign)]
  | .letIn _ t u => t.placeOccs c ++ u.placeOccs (c + 1)
  | .seq t u => t.placeOccs c ++ u.placeOccs c
  | .matchNat p z s => (c, p, .scrut) :: (z.placeOccs c ++ s.placeOccs c)
  | .pi _ ds cod =>
      Term.placeOccsDoms c ds ++ cod.placeOccs (c + ds.length)
  | .fix _ _ ds cod _ b =>
      Term.placeOccsDoms c ds ++ cod.placeOccs (c + ds.length)
        ++ b.placeOccs (c + ds.length + 1)
  | .call g as _ => g.placeOccs c ++ Term.placeOccsList c as
  | .succ t | .fst t | .snd t | .ref t => t.placeOccs c
  | .cong a b | .ascribe a b =>
      a.placeOccs c ++ b.placeOccs c
  | .eq a b d | .id a b d => a.placeOccs c ++ b.placeOccs c ++ d.placeOccs c
  | .ctor _ _ _ ps as => Term.placeOccsList c ps ++ Term.placeOccsList c as
  | .prim _ as | .tind _ as => Term.placeOccsList c as
  | .matchInd p _ as => (c, p, .scrut) :: Term.placeOccsArms c as
  | _ => []
termination_by structural t => t

/-- `as.flatMap (·.placeOccs c)`. -/
def Term.placeOccsList (c : Nat) : List Term → List (Nat × Place × PKind)
  | [] => []
  | a :: as => a.placeOccs c ++ Term.placeOccsList c as
termination_by structural as => as

def Term.placeOccsArms (c : Nat) : List (Hint × Term) → List (Nat × Place × PKind)
  | [] => []
  | (_, a) :: as => a.placeOccs c ++ Term.placeOccsArms c as
termination_by structural as => as

/-- A telescope's domains, the `i`-th at depth `c + i`. -/
def Term.placeOccsDoms (c : Nat) : List Term → List (Nat × Place × PKind)
  | [] => []
  | d :: ds => d.placeOccs c ++ Term.placeOccsDoms (c + 1) ds
termination_by structural ds => ds
end

mutual
/-- The occurrences a stuck block's capture analysis sees: as `placeOccs`, except that an
occurrence inside a nested function or Π-type is a read, whatever it does there (a
closure captures a copy, and its writes are to that copy: fuzz-port R2). -/
def Term.blockOccs (inFn : Bool) (c : Nat) : Term → List (Nat × Place × PKind)
  | .place p => [(c, p, .read)]
  | .borrow p => [(c, p, if inFn then .read else .borrow)]
  | .assign p t => t.blockOccs inFn c ++ [(c, p, if inFn then .read else .assign)]
  | .letIn _ t u => t.blockOccs inFn c ++ u.blockOccs inFn (c + 1)
  | .seq t u => t.blockOccs inFn c ++ u.blockOccs inFn c
  | .matchNat p z s => (c, p, .scrut) :: (z.blockOccs inFn c ++ s.blockOccs inFn c)
  | .pi _ ds cod =>
      Term.blockOccsDoms c ds ++ cod.blockOccs true (c + ds.length)
  | .fix _ _ ds cod _ b =>
      Term.blockOccsDoms c ds ++ cod.blockOccs true (c + ds.length)
        ++ b.blockOccs true (c + ds.length + 1)
  | .call g as _ => g.blockOccs inFn c ++ Term.blockOccsList inFn c as
  | .succ t | .fst t | .snd t | .ref t => t.blockOccs inFn c
  | .cong a b | .ascribe a b => a.blockOccs inFn c ++ b.blockOccs inFn c
  | .eq a b d | .id a b d => a.blockOccs inFn c ++ b.blockOccs inFn c ++ d.blockOccs inFn c
  | .ctor _ _ _ ps as => Term.blockOccsList inFn c ps ++ Term.blockOccsList inFn c as
  | .prim _ as | .tind _ as => Term.blockOccsList inFn c as
  | .matchInd p _ as => (c, p, .scrut) :: Term.blockOccsArms inFn c as
  | _ => []
termination_by structural t => t

/-- `as.flatMap (·.blockOccs inFn c)`. -/
def Term.blockOccsList (inFn : Bool) (c : Nat) : List Term → List (Nat × Place × PKind)
  | [] => []
  | a :: as => a.blockOccs inFn c ++ Term.blockOccsList inFn c as
termination_by structural as => as

def Term.blockOccsArms (inFn : Bool) (c : Nat) : List (Hint × Term) → List (Nat × Place × PKind)
  | [] => []
  | (_, a) :: as => a.blockOccs inFn c ++ Term.blockOccsArms inFn c as
termination_by structural as => as

/-- A function's domains (inside a function: `inFn` is true), the `i`-th at depth `c + i`. -/
def Term.blockOccsDoms (c : Nat) : List Term → List (Nat × Place × PKind)
  | [] => []
  | d :: ds => d.blockOccs true c ++ Term.blockOccsDoms (c + 1) ds
termination_by structural ds => ds
end

mutual
/-- The free occurrences of a term that lie inside a function or Π-type it forms, the ones a
closure captures (enclosing-frame index and place, as `freeOccsBlock` gives them). -/
def Term.fnOccs (c : Nat) : Term → List (Nat × Place)
  | t@(.pi ..) | t@(.fix ..) =>
    (t.blockOccs true c).filterMap fun (c', p, _) => if p.root ≥ c' then some (p.root - c', p) else none
  | .letIn _ t u => t.fnOccs c ++ u.fnOccs (c + 1)
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.fnOccs c
  | .seq t u | .cong t u | .ascribe t u | .matchNat _ t u => t.fnOccs c ++ u.fnOccs c
  | .call g as _ => g.fnOccs c ++ Term.fnOccsList c as
  | .eq a b d | .id a b d => a.fnOccs c ++ b.fnOccs c ++ d.fnOccs c
  | .ctor _ _ _ ps as => Term.fnOccsList c ps ++ Term.fnOccsList c as
  | .prim _ as | .tind _ as => Term.fnOccsList c as
  | .matchInd _ _ as => Term.fnOccsArms c as
  | _ => []
termination_by structural t => t

def Term.fnOccsList (c : Nat) : List Term → List (Nat × Place)
  | [] => []
  | a :: as => a.fnOccs c ++ Term.fnOccsList c as
termination_by structural as => as

def Term.fnOccsArms (c : Nat) : List (Hint × Term) → List (Nat × Place)
  | [] => []
  | (_, a) :: as => a.fnOccs c ++ Term.fnOccsArms c as
termination_by structural as => as
end

mutual
/-- The term forms a function or Π-type somewhere (which may capture its free variables). -/
def Term.formsFn : Term → Bool
  | .pi .. | .fix .. => true
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.formsFn
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.formsFn || u.formsFn
  | .matchNat _ z s => z.formsFn || s.formsFn
  | .call f as _ => f.formsFn || Term.formsFnList as
  | .eq a b c | .id a b c => a.formsFn || b.formsFn || c.formsFn
  | .ctor _ _ _ ps as => Term.formsFnList ps || Term.formsFnList as
  | .prim _ as | .tind _ as => Term.formsFnList as
  | .matchInd _ _ as => Term.formsFnArms as
  | _ => false
termination_by structural t => t

def Term.formsFnList : List Term → Bool
  | [] => false
  | a :: as => a.formsFn || Term.formsFnList as
termination_by structural as => as

def Term.formsFnArms : List (Hint × Term) → Bool
  | [] => false
  | (_, a) :: as => a.formsFn || Term.formsFnArms as
termination_by structural as => as
end

/-- Free occurrences, with the root expressed as an index into the enclosing frame. -/
def Term.freeOccs (t : Term) : List (Nat × Place × PKind) :=
  (t.placeOccs 0).filterMap fun (c, p, k) =>
    if p.root ≥ c then some (p.root - c, p, k) else none

/-- Free occurrences for a stuck block's capture analysis (`blockOccs`). -/
def Term.freeOccsBlock (t : Term) : List (Nat × Place × PKind) :=
  (t.blockOccs false 0).filterMap fun (c, p, k) =>
    if p.root ≥ c then some (p.root - c, p, k) else none

/-- The free variables (enclosing-frame indices) of a term, without duplicates. -/
def Term.freeVars (t : Term) : List Nat :=
  t.freeOccs.foldl (fun acc (o, _, _) => if acc.contains o then acc else acc ++ [o]) []

mutual
/-- Does a predicate hold of some atom (sub-value) of a value? Looks inside sealed
programs, closures and Π-types too (loans may occur there: RULES §2). -/
def Value.anyAtom (P : Value → Bool) (v : Value) : Bool :=
  P v || match v with
  | .succ w | .tRef w | .borrow _ w => w.anyAtom P
  | .tEq A a b => A.anyAtom P || a.anyAtom P || b.anyAtom P
  | .clo cs t | .tPi cs t => Value.anyAtomList P cs || t.anyAtom P
  | .sealed t => t.anyAtom P
  | .ind _ _ _ ps fs => Value.anyAtomList P ps || Value.anyAtomList P fs
  | .tInd _ fs => Value.anyAtomList P fs
  | _ => false
termination_by structural v

def Value.anyAtomList (P : Value → Bool) : List Value → Bool
  | [] => false
  | a :: as => a.anyAtom P || Value.anyAtomList P as
termination_by structural as => as

def Term.anyAtom (P : Value → Bool) : Term → Bool
  | .val v => v.anyAtom P
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.anyAtom P
  | .letIn _ t u | .seq t u
  | .cong t u | .ascribe t u => t.anyAtom P || u.anyAtom P
  | .matchNat _ z s => z.anyAtom P || s.anyAtom P
  | .pi _ ds c => Term.anyAtomList P ds || c.anyAtom P
  | .fix _ _ ds c _ b => Term.anyAtomList P ds || c.anyAtom P || b.anyAtom P
  | .call f as _ => f.anyAtom P || Term.anyAtomList P as
  | .eq a b c | .id a b c => a.anyAtom P || b.anyAtom P || c.anyAtom P
  | .ctor _ _ _ ps as => Term.anyAtomList P ps || Term.anyAtomList P as
  | .prim _ as | .tind _ as => Term.anyAtomList P as
  | .matchInd _ _ as => Term.anyAtomArms P as
  | _ => false
termination_by structural t => t

def Term.anyAtomList (P : Value → Bool) : List Term → Bool
  | [] => false
  | a :: as => a.anyAtom P || Term.anyAtomList P as
termination_by structural as => as

def Term.anyAtomArms (P : Value → Bool) : List (Hint × Term) → Bool
  | [] => false
  | (_, a) :: as => a.anyAtom P || Term.anyAtomArms P as
termination_by structural as => as
end

/-- D53: part of the value was moved out or is gone (`⊥`). -/
def Value.hasHole (v : Value) : Bool := v.anyAtom fun a => a == .bot


mutual
/-- All loan labels occurring in a value (with repetition). -/
def Value.loans : Value → List Nat
  | .loan l => [l]
  | .succ w | .tRef w | .borrow _ w => w.loans
  | .tEq A a b => A.loans ++ a.loans ++ b.loans
  | .clo cs t | .tPi cs t => Value.loansList cs ++ t.loans
  | .sealed t => t.loans
  | .ind _ _ _ ps fs => Value.loansList ps ++ Value.loansList fs
  | .tInd _ fs => Value.loansList fs
  | _ => []
termination_by structural v => v

/-- `vs.flatMap Value.loans`. -/
def Value.loansList : List Value → List Nat
  | [] => []
  | v :: vs => v.loans ++ Value.loansList vs
termination_by structural vs => vs

def Term.loans : Term → List Nat
  | .val v => v.loans
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.loans
  | .letIn _ t u | .seq t u
  | .cong t u | .ascribe t u => t.loans ++ u.loans
  | .matchNat _ z s => z.loans ++ s.loans
  | .pi _ ds c => Term.loansList ds ++ c.loans
  | .fix _ _ ds c _ b => Term.loansList ds ++ c.loans ++ b.loans
  | .call f as _ => f.loans ++ Term.loansList as
  | .eq a b c | .id a b c => a.loans ++ b.loans ++ c.loans
  | .ctor _ _ _ ps as => Term.loansList ps ++ Term.loansList as
  | .prim _ as | .tind _ as => Term.loansList as
  | .matchInd _ _ as => Term.loansArms as
  | _ => []
termination_by structural t => t

/-- `ts.flatMap Term.loans`. -/
def Term.loansList : List Term → List Nat
  | [] => []
  | t :: ts => t.loans ++ Term.loansList ts
termination_by structural ts => ts

def Term.loansArms : List (Hint × Term) → List Nat
  | [] => []
  | (_, t) :: ts => t.loans ++ Term.loansArms ts
termination_by structural ts => ts
end

mutual
/-- D67: the loans in the part of a value that its place owns, i.e. not behind a borrow it
holds. A loan behind a held borrow (a reborrow `&(*x).f`, or a neutral's) travels back to the
borrow's owner when that borrow ends, and stays live there. -/
def Value.ownedLoans : Value → List Nat
  | .borrow _ _ => []
  | .succ w | .tRef w => w.ownedLoans
  | .ind _ _ _ ps fs => Value.ownedLoansList ps ++ Value.ownedLoansList fs
  | v => v.loans
termination_by structural v => v

/-- `vs.flatMap Value.ownedLoans`. -/
def Value.ownedLoansList : List Value → List Nat
  | [] => []
  | v :: vs => v.ownedLoans ++ Value.ownedLoansList vs
termination_by structural vs => vs
end

def Value.hasLoan (l : Nat) (v : Value) : Bool := v.anyAtom (· == .loan l)
def Value.hasAbs (s : Nat) (v : Value) : Bool := v.anyAtom (· == .abs s)
def Value.hasBorrow (v : Value) : Bool := v.anyAtom fun | .borrow _ _ => true | _ => false
def Value.isBorrow : Value → Bool
  | .borrow _ _ => true
  | _ => false

/-- A type is borrow-free when no `&` occurs in it (RULES §1: `&A` needs `A` borrow-free). -/
def Value.typeHasRef (T : Value) : Bool := T.anyAtom fun | .tRef _ => true | _ => false

end Ochr

namespace Ochr

mutual
/-- D48 (2): every `&A` in `t` stands at the top of a declared type (a parameter's
domain, a declared result, an annotation), never inside another type, so no computation
produces a borrow type. With `top`, `t` is itself a declared type, which may be `&A` (with
no `&` inside `A`). -/
def Term.refsOkAt (top : Bool) : Term → Bool
  | .ref A => top && A.refsOkAt false
  | .pi _ ds c => Term.refTopOkList ds && c.refsOkAt true
  | .fix _ _ ds c _ b => Term.refTopOkList ds && c.refsOkAt true && b.refsOkAt false
  | .ascribe t A => t.refsOkAt false && A.refsOkAt true
  | .assign _ t | .succ t | .fst t | .snd t => t.refsOkAt false
  | .letIn _ t u | .seq t u | .cong t u => t.refsOkAt false && u.refsOkAt false
  | .matchNat _ z s => z.refsOkAt false && s.refsOkAt false
  | .call f as _ => f.refsOkAt false && Term.refsOkList as
  | .eq a b c | .id a b c => a.refsOkAt false && b.refsOkAt false && c.refsOkAt false
  | .ctor _ _ _ ps as => Term.refsOkList ps && Term.refsOkList as
  | .prim _ as | .tind _ as => Term.refsOkList as
  | .matchInd _ _ as => Term.refsOkArms as
  | _ => true
termination_by structural t => t

/-- `ts.all Term.refsOk`. -/
def Term.refsOkList : List Term → Bool
  | [] => true
  | t :: ts => t.refsOkAt false && Term.refsOkList ts
termination_by structural ts => ts

/-- `ts.all Term.refTopOk`. -/
def Term.refTopOkList : List Term → Bool
  | [] => true
  | t :: ts => t.refsOkAt true && Term.refTopOkList ts
termination_by structural ts => ts

def Term.refsOkArms : List (Hint × Term) → Bool
  | [] => true
  | (_, t) :: ts => t.refsOkAt false && Term.refsOkArms ts
termination_by structural ts => ts
end

/-- D48 (2): every `&A` in `t` stands at the top of a declared type, never inside another
type (`Term.refsOkAt`). -/
def Term.refsOk (t : Term) : Bool := t.refsOkAt false

/-- A declared type: `&A` at its top (with no `&` inside `A`), or a type with `&` only
in allowed positions. -/
def Term.refTopOk (t : Term) : Bool := t.refsOkAt true

end Ochr
