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
partial def unitTop : Value → Value
  | .tInd "And" [p, q] => mkAnd (unitTop p) (unitTop q)
  | v => v

/-- Does a (first-order) field type term mention the inductive `n`? (D53 prototype: a copy
type is not recursive.) -/
partial def Term.mentionsTInd (n : String) : Term → Bool
  | .tind m as => m == n || as.any (Term.mentionsTInd n)
  | _ => false

/-- `And(P₁, And(P₂, … Pₖ))` with the unit laws (`[]`: `True`), for `Eq` on constructor
values and for `Id` (D52). -/
def andList : List Value → Value
  | [] => .tInd "True" []
  | [p] => p
  | p :: ps => mkAnd p (andList ps)

/-- `D(ā)`, kept as written (D50); `norm` is the counterfactual normalising reading. -/
def mkTInd (n : String) (as : List Value) (norm : Bool := false) : Value :=
  match n, as, norm with
  | "And", [p, q], true => mkAnd p q
  | _, _, _ => .tInd n as

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

mutual
/-- Rewrite every *free* place root: at binder depth `c`, a root `j ≥ c` is replaced by
`f c (j - c)` (the second argument is the index in the enclosing frame). -/
partial def Term.mapFree (f : Nat → Nat → Place) (c : Nat) : Term → Term
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
  | .call g as hd => .call (g.mapFree f c) (as.map (·.mapFree f c)) hd
  | .succ t => .succ (t.mapFree f c)
  | .fst t => .fst (t.mapFree f c)
  | .snd t => .snd (t.mapFree f c)
  | .ref t => .ref (t.mapFree f c)
  | .cong a b => .cong (a.mapFree f c) (b.mapFree f c)
  | .ascribe a b => .ascribe (a.mapFree f c) (b.mapFree f c)
  | .eq a b d => .eq (a.mapFree f c) (b.mapFree f c) (d.mapFree f c)
  | .id a b d => .id (a.mapFree f c) (b.mapFree f c) (d.mapFree f c)
  | .prim n as => .prim n (as.map (·.mapFree f c))
  | .ctor t k h ps as => .ctor t k h (ps.map (·.mapFree f c)) (as.map (·.mapFree f c))
  | .tind n as => .tind n (as.map (·.mapFree f c))
  | .matchInd p t as => .matchInd (mp f c p) t (as.map fun (h, a) => (h, a.mapFree f c))
  | t => t

partial def mapDoms (f : Nat → Nat → Place) (c : Nat) (ds : List Term) : List Term :=
  (ds.zipIdx).map fun (d, i) => d.mapFree f (c + i)

partial def mp (f : Nat → Nat → Place) (c : Nat) (p : Place) : Place :=
  p.mapRoot fun j => if j < c then .var j else f c (j - c)
end

/-- Rewrite every place with a free root: at depth `c`, a place whose root `j ≥ c` is
replaced by `f c p'`, where `p'` is the place re-rooted at the enclosing frame's index
`j - c`. -/
partial def Term.mapFreePlace (f : Nat → Place → Place) (c : Nat) : Term → Term
  | .place p => .place (fp f c p)
  | .borrow p => .borrow (fp f c p)
  | .assign p t => .assign (fp f c p) (t.mapFreePlace f c)
  | .letIn h t u => .letIn h (t.mapFreePlace f c) (u.mapFreePlace f (c + 1))
  | .seq t u => .seq (t.mapFreePlace f c) (u.mapFreePlace f c)
  | .matchNat p z s => .matchNat (fp f c p) (z.mapFreePlace f c) (s.mapFreePlace f c)
  | .pi hs ds cod =>
      .pi hs ((ds.zipIdx).map fun (d, i) => d.mapFreePlace f (c + i)) (cod.mapFreePlace f (c + ds.length))
  | .fix h hs ds cod d b =>
      .fix h hs ((ds.zipIdx).map fun (d, i) => d.mapFreePlace f (c + i)) (cod.mapFreePlace f (c + ds.length)) d
        (b.mapFreePlace f (c + ds.length + 1))
  | .call g as hd => .call (g.mapFreePlace f c) (as.map (·.mapFreePlace f c)) hd
  | .succ t => .succ (t.mapFreePlace f c)
  | .fst t => .fst (t.mapFreePlace f c)
  | .snd t => .snd (t.mapFreePlace f c)
  | .ref t => .ref (t.mapFreePlace f c)
  | .cong a b => .cong (a.mapFreePlace f c) (b.mapFreePlace f c)
  | .ascribe a b => .ascribe (a.mapFreePlace f c) (b.mapFreePlace f c)
  | .eq a b d => .eq (a.mapFreePlace f c) (b.mapFreePlace f c) (d.mapFreePlace f c)
  | .id a b d => .id (a.mapFreePlace f c) (b.mapFreePlace f c) (d.mapFreePlace f c)
  | .prim n as => .prim n (as.map (·.mapFreePlace f c))
  | .ctor t k h ps as => .ctor t k h (ps.map (·.mapFreePlace f c)) (as.map (·.mapFreePlace f c))
  | .tind n as => .tind n (as.map (·.mapFreePlace f c))
  | .matchInd p t as => .matchInd (fp f c p) t (as.map fun (h, a) => (h, a.mapFreePlace f c))
  | t => t
where
  fp (f : Nat → Place → Place) (c : Nat) (p : Place) : Place :=
    if p.root < c then p else f c (p.mapRoot fun j => .var (j - c))

/-- D53: take a match's arm when its scrutinee (a free place, re-rooted at the enclosing
frame) is a place `sel` knows the constructor of (`some k` for an inductive's `k`, `none` for
`S`): a stuck block's capture split into its fields (`closeOffMatch`). -/
partial def Term.selectArms (sel : Place → Option (Option Nat)) (c : Nat) : Term → Term
  | .matchInd p t as =>
    match (if p.root < c then none else sel (p.mapRoot fun j => .var (j - c))) with
    | some (some k) => match as[k]? with
      | some (_, a) => a.selectArms sel c
      | none => .matchInd p t (as.map fun (h, a) => (h, a.selectArms sel c))
    | _ => .matchInd p t (as.map fun (h, a) => (h, a.selectArms sel c))
  | .matchNat p z s =>
    match (if p.root < c then none else sel (p.mapRoot fun j => .var (j - c))) with
    | some none => s.selectArms sel c
    | _ => .matchNat p (z.selectArms sel c) (s.selectArms sel c)
  | .assign p t => .assign p (t.selectArms sel c)
  | .letIn h t u => .letIn h (t.selectArms sel c) (u.selectArms sel (c + 1))
  | .seq t u => .seq (t.selectArms sel c) (u.selectArms sel c)
  | .pi hs ds cod =>
      .pi hs ((ds.zipIdx).map fun (d, i) => d.selectArms sel (c + i)) (cod.selectArms sel (c + ds.length))
  | .fix h hs ds cod d b =>
      .fix h hs ((ds.zipIdx).map fun (d, i) => d.selectArms sel (c + i)) (cod.selectArms sel (c + ds.length)) d
        (b.selectArms sel (c + ds.length + 1))
  | .call g as hd => .call (g.selectArms sel c) (as.map (·.selectArms sel c)) hd
  | .succ t => .succ (t.selectArms sel c)
  | .fst t => .fst (t.selectArms sel c)
  | .snd t => .snd (t.selectArms sel c)
  | .ref t => .ref (t.selectArms sel c)
  | .cong a b => .cong (a.selectArms sel c) (b.selectArms sel c)
  | .ascribe a b => .ascribe (a.selectArms sel c) (b.selectArms sel c)
  | .eq a b d => .eq (a.selectArms sel c) (b.selectArms sel c) (d.selectArms sel c)
  | .id a b d => .id (a.selectArms sel c) (b.selectArms sel c) (d.selectArms sel c)
  | .prim n as => .prim n (as.map (·.selectArms sel c))
  | .ctor t k h ps as => .ctor t k h (ps.map (·.selectArms sel c)) (as.map (·.selectArms sel c))
  | .tind n as => .tind n (as.map (·.selectArms sel c))
  | t => t

/-- Replace every read of the whole free variable `o` (at depth `c`, the variable
`o + c`) by the closed term `u`; other occurrences stay. Used to inline a captured proof
with its type (a proof's value is ⋆, so only its type needs keeping). -/
partial def Term.inlineReads (t : Term) (o : Nat) (u : Term) (c : Nat) : Term :=
  match t with
  | .place (.var j) => if j == o + c then u else .place (.var j)
  | .assign p t => .assign p (t.inlineReads o u c)
  | .letIn h t w => .letIn h (t.inlineReads o u c) (w.inlineReads o u (c + 1))
  | .seq t w => .seq (t.inlineReads o u c) (w.inlineReads o u c)
  | .matchNat p z s => .matchNat p (z.inlineReads o u c) (s.inlineReads o u c)
  | .pi hs ds cod =>
      .pi hs ((ds.zipIdx).map fun (d, i) => d.inlineReads o u (c + i)) (cod.inlineReads o u (c + ds.length))
  | .fix h hs ds cod d b =>
      .fix h hs ((ds.zipIdx).map fun (d, i) => d.inlineReads o u (c + i)) (cod.inlineReads o u (c + ds.length)) d
        (b.inlineReads o u (c + ds.length + 1))
  | .call g as hd => .call (g.inlineReads o u c) (as.map (·.inlineReads o u c)) hd
  | .succ t => .succ (t.inlineReads o u c)
  | .fst t => .fst (t.inlineReads o u c)
  | .snd t => .snd (t.inlineReads o u c)
  | .ref t => .ref (t.inlineReads o u c)
  | .cong a b => .cong (a.inlineReads o u c) (b.inlineReads o u c)
  | .ascribe a b => .ascribe (a.inlineReads o u c) (b.inlineReads o u c)
  | .eq a b d => .eq (a.inlineReads o u c) (b.inlineReads o u c) (d.inlineReads o u c)
  | .id a b d => .id (a.inlineReads o u c) (b.inlineReads o u c) (d.inlineReads o u c)
  | .prim n as => .prim n (as.map (·.inlineReads o u c))
  | .ctor t k h ps as => .ctor t k h (ps.map (·.inlineReads o u c)) (as.map (·.inlineReads o u c))
  | .tind n as => .tind n (as.map (·.inlineReads o u c))
  | .matchInd p t as => .matchInd p t (as.map fun (h, a) => (h, a.inlineReads o u c))
  | t => t

/-- Clear the head marks of a sealed program's calls (to type it as an ordinary term). -/
partial def Term.unHead : Term → Term
  | .call f as _ => .call f as false
  | .letIn h t u => .letIn h t.unHead u.unHead
  | .seq t u => .seq t.unHead u.unHead
  | t => t

/-- Every place occurrence `(depth, place, kind)`, in evaluation order. -/
partial def Term.placeOccs (c : Nat) : Term → List (Nat × Place × PKind)
  | .place p => [(c, p, .read)]
  | .borrow p => [(c, p, .borrow)]
  | .assign p t => t.placeOccs c ++ [(c, p, .assign)]
  | .letIn _ t u => t.placeOccs c ++ u.placeOccs (c + 1)
  | .seq t u => t.placeOccs c ++ u.placeOccs c
  | .matchNat p z s => (c, p, .scrut) :: (z.placeOccs c ++ s.placeOccs c)
  | .pi _ ds cod =>
      (ds.zipIdx.flatMap fun (d, i) => d.placeOccs (c + i)) ++ cod.placeOccs (c + ds.length)
  | .fix _ _ ds cod _ b =>
      (ds.zipIdx.flatMap fun (d, i) => d.placeOccs (c + i)) ++ cod.placeOccs (c + ds.length)
        ++ b.placeOccs (c + ds.length + 1)
  | .call g as _ => g.placeOccs c ++ as.flatMap (·.placeOccs c)
  | .succ t | .fst t | .snd t | .ref t => t.placeOccs c
  | .cong a b | .ascribe a b =>
      a.placeOccs c ++ b.placeOccs c
  | .eq a b d | .id a b d => a.placeOccs c ++ b.placeOccs c ++ d.placeOccs c
  | .ctor _ _ _ ps as => (ps ++ as).flatMap (·.placeOccs c)
  | .prim _ as | .tind _ as => as.flatMap (·.placeOccs c)
  | .matchInd p _ as => (c, p, .scrut) :: as.flatMap (·.2.placeOccs c)
  | _ => []

/-- The occurrences a stuck block's capture analysis sees: as `placeOccs`, except that an
occurrence inside a nested function or Π-type is a read, whatever it does there (a
closure captures a copy, and its writes are to that copy: fuzz-port R2). -/
partial def Term.blockOccs (inFn : Bool) (c : Nat) : Term → List (Nat × Place × PKind)
  | .place p => [(c, p, .read)]
  | .borrow p => [(c, p, if inFn then .read else .borrow)]
  | .assign p t => t.blockOccs inFn c ++ [(c, p, if inFn then .read else .assign)]
  | .letIn _ t u => t.blockOccs inFn c ++ u.blockOccs inFn (c + 1)
  | .seq t u => t.blockOccs inFn c ++ u.blockOccs inFn c
  | .matchNat p z s => (c, p, .scrut) :: (z.blockOccs inFn c ++ s.blockOccs inFn c)
  | .pi _ ds cod =>
      (ds.zipIdx.flatMap fun (d, i) => d.blockOccs true (c + i)) ++ cod.blockOccs true (c + ds.length)
  | .fix _ _ ds cod _ b =>
      (ds.zipIdx.flatMap fun (d, i) => d.blockOccs true (c + i)) ++ cod.blockOccs true (c + ds.length)
        ++ b.blockOccs true (c + ds.length + 1)
  | .call g as _ => g.blockOccs inFn c ++ as.flatMap (·.blockOccs inFn c)
  | .succ t | .fst t | .snd t | .ref t => t.blockOccs inFn c
  | .cong a b | .ascribe a b => a.blockOccs inFn c ++ b.blockOccs inFn c
  | .eq a b d | .id a b d => a.blockOccs inFn c ++ b.blockOccs inFn c ++ d.blockOccs inFn c
  | .ctor _ _ _ ps as => (ps ++ as).flatMap (·.blockOccs inFn c)
  | .prim _ as | .tind _ as => as.flatMap (·.blockOccs inFn c)
  | .matchInd p _ as => (c, p, .scrut) :: as.flatMap (·.2.blockOccs inFn c)
  | _ => []

/-- The free occurrences of a term that lie inside a function or Π-type it forms, the ones a
closure captures (enclosing-frame index and place, as `freeOccsBlock` gives them). -/
partial def Term.fnOccs (c : Nat) : Term → List (Nat × Place)
  | t@(.pi ..) | t@(.fix ..) =>
    (t.blockOccs true c).filterMap fun (c', p, _) => if p.root ≥ c' then some (p.root - c', p) else none
  | .letIn _ t u => t.fnOccs c ++ u.fnOccs (c + 1)
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.fnOccs c
  | .seq t u | .cong t u | .ascribe t u | .matchNat _ t u => t.fnOccs c ++ u.fnOccs c
  | .call g as _ => g.fnOccs c ++ as.flatMap (·.fnOccs c)
  | .eq a b d | .id a b d => a.fnOccs c ++ b.fnOccs c ++ d.fnOccs c
  | .ctor _ _ _ ps as => (ps ++ as).flatMap (·.fnOccs c)
  | .prim _ as | .tind _ as => as.flatMap (·.fnOccs c)
  | .matchInd _ _ as => as.flatMap (·.2.fnOccs c)
  | _ => []

/-- The term forms a function or Π-type somewhere (which may capture its free variables). -/
partial def Term.formsFn : Term → Bool
  | .pi .. | .fix .. => true
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.formsFn
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.formsFn || u.formsFn
  | .matchNat _ z s => z.formsFn || s.formsFn
  | .call f as _ => f.formsFn || as.any (·.formsFn)
  | .eq a b c | .id a b c => a.formsFn || b.formsFn || c.formsFn
  | .ctor _ _ _ ps as => ps.any (·.formsFn) || as.any (·.formsFn)
  | .prim _ as | .tind _ as => as.any (·.formsFn)
  | .matchInd _ _ as => as.any (·.2.formsFn)
  | _ => false

/-- A place whose first step from its root goes through a borrow (`*x…`). -/
def Place.derefsRoot : Place → Bool
  | .deref (.var _) => true
  | .deref p | .fst p | .snd p | .field _ p => p.derefsRoot
  | .var _ => false

/-- The same place with that first `*` removed. -/
def Place.stripDeref : Place → Place
  | .deref (.var i) => .var i
  | .deref p => .deref p.stripDeref
  | .fst p => .fst p.stripDeref
  | .snd p => .snd p.stripDeref
  | .field g p => .field g p.stripDeref
  | .var i => .var i

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
partial def Value.anyAtom (P : Value → Bool) (v : Value) : Bool :=
  P v || match v with
  | .succ w | .tRef w | .borrow _ w | .ghost w => w.anyAtom P
  | .tEq A a b => A.anyAtom P || a.anyAtom P || b.anyAtom P
  | .clo cs t | .tPi cs t => cs.any (·.anyAtom P) || t.anyAtom P
  | .sealed t => t.anyAtom P
  | .ind _ _ _ ps fs => ps.any (·.anyAtom P) || fs.any (·.anyAtom P)
  | .tInd _ fs => fs.any (·.anyAtom P)
  | _ => false

partial def Term.anyAtom (P : Value → Bool) : Term → Bool
  | .val v => v.anyAtom P
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.anyAtom P
  | .letIn _ t u | .seq t u
  | .cong t u | .ascribe t u => t.anyAtom P || u.anyAtom P
  | .matchNat _ z s => z.anyAtom P || s.anyAtom P
  | .pi _ ds c => ds.any (·.anyAtom P) || c.anyAtom P
  | .fix _ _ ds c _ b => ds.any (·.anyAtom P) || c.anyAtom P || b.anyAtom P
  | .call f as _ => f.anyAtom P || as.any (·.anyAtom P)
  | .eq a b c | .id a b c => a.anyAtom P || b.anyAtom P || c.anyAtom P
  | .ctor _ _ _ ps as => ps.any (·.anyAtom P) || as.any (·.anyAtom P)
  | .prim _ as | .tind _ as => as.any (·.anyAtom P)
  | .matchInd _ _ as => as.any (·.2.anyAtom P)
  | _ => false
end

/-- D53: the value with every ghost replaced by the value it keeps (an erased read). -/
partial def Value.unghost : Value → Value
  | .ghost w => w.unghost
  | .succ w => .succ w.unghost
  | .ind t c h ps fs => .ind t c h ps (fs.map Value.unghost)
  | .borrow l w => .borrow l w.unghost
  | v => v

/-- D53: part of the value was moved out (a ghost) or is gone (`⊥`). -/
def Value.hasHole (v : Value) : Bool := v.anyAtom fun a => a == .bot || a matches .ghost _


mutual
/-- All loan labels occurring in a value (with repetition). -/
partial def Value.loans : Value → List Nat
  | .loan l => [l]
  | .succ w | .tRef w | .borrow _ w | .ghost w => w.loans
  | .tEq A a b => A.loans ++ a.loans ++ b.loans
  | .clo cs t | .tPi cs t => cs.flatMap Value.loans ++ t.loans
  | .sealed t => t.loans
  | .ind _ _ _ ps fs => ps.flatMap Value.loans ++ fs.flatMap Value.loans
  | .tInd _ fs => fs.flatMap Value.loans
  | _ => []

partial def Term.loans : Term → List Nat
  | .val v => v.loans
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.loans
  | .letIn _ t u | .seq t u
  | .cong t u | .ascribe t u => t.loans ++ u.loans
  | .matchNat _ z s => z.loans ++ s.loans
  | .pi _ ds c => ds.flatMap Term.loans ++ c.loans
  | .fix _ _ ds c _ b => ds.flatMap Term.loans ++ c.loans ++ b.loans
  | .call f as _ => f.loans ++ as.flatMap Term.loans
  | .eq a b c | .id a b c => a.loans ++ b.loans ++ c.loans
  | .ctor _ _ _ ps as => (ps ++ as).flatMap Term.loans
  | .prim _ as | .tind _ as => as.flatMap Term.loans
  | .matchInd _ _ as => as.flatMap (·.2.loans)
  | _ => []
end

/-- D67: the loans in the part of a value that its place owns, i.e. not behind a borrow it
holds. A loan behind a held borrow (a reborrow `&(*x).f`, or a neutral's) travels back to the
borrow's owner when that borrow ends, and stays live there. -/
partial def Value.ownedLoans : Value → List Nat
  | .borrow _ _ => []
  | .succ w | .tRef w | .ghost w => w.ownedLoans
  | .ind _ _ _ ps fs => ps.flatMap Value.ownedLoans ++ fs.flatMap Value.ownedLoans
  | v => v.loans

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
produces a borrow type. -/
partial def Term.refsOk : Term → Bool
  | .ref _ => false
  | .pi _ ds c => ds.all Term.refTopOk && c.refTopOk
  | .fix _ _ ds c _ b => ds.all Term.refTopOk && c.refTopOk && b.refsOk
  | .ascribe t A => t.refsOk && A.refTopOk
  | .assign _ t | .succ t | .fst t | .snd t => t.refsOk
  | .letIn _ t u | .seq t u | .cong t u => t.refsOk && u.refsOk
  | .matchNat _ z s => z.refsOk && s.refsOk
  | .call f as _ => f.refsOk && as.all Term.refsOk
  | .eq a b c | .id a b c => a.refsOk && b.refsOk && c.refsOk
  | .ctor _ _ _ ps as => (ps ++ as).all Term.refsOk
  | .prim _ as | .tind _ as => as.all Term.refsOk
  | .matchInd _ _ as => as.all (·.2.refsOk)
  | _ => true

/-- A declared type: `&A` at its top (with no `&` inside `A`), or a type with `&` only
in allowed positions. -/
partial def Term.refTopOk : Term → Bool
  | .ref A => A.refsOk
  | t => t.refsOk
end

end Ochr
