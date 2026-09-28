import Ochr.Syntax

/-!
# Pure helpers: numerals, the `Eq`/`∧` smart constructors (§4 "`Eq` computes"),
and syntactic traversals (free places, loans and abstract values inside values).
-/

namespace Ochr

def Value.ofNat : Nat → Value
  | 0 => .zero
  | n + 1 => .succ (Value.ofNat n)

def Term.ofNat : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (Term.ofNat n)

/-- `⊤ ∧ P ≡ P ≡ P ∧ ⊤` (RULES §4). -/
def mkAnd : Value → Value → Value
  | .tTop, q => q
  | p, .tTop => p
  | p, q => .tAnd p q

/-- `Eq` computes (RULES §4): pairs split, reflexive equations are `⊤`.
Proofs are all `⋆`, so an equation between proofs is reflexive. -/
partial def mkEq (A a b : Value) : Value :=
  match A, a, b with
  | .tProd A₁ A₂, .pair a₁ a₂, .pair b₁ b₂ => mkAnd (mkEq A₁ a₁ b₁) (mkEq A₂ a₂ b₂)
  | _, _, _ => if a == b then .tTop else .tEq A a b

def Place.root : Place → Nat
  | .var i => i
  | .deref p | .fst p | .snd p => p.root

/-- Replace the root variable of a place by a place. -/
def Place.mapRoot (f : Nat → Place) : Place → Place
  | .var i => f i
  | .deref p => .deref (p.mapRoot f)
  | .fst p => .fst (p.mapRoot f)
  | .snd p => .snd (p.mapRoot f)

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
  | .fix h hs ds cod b =>
      .fix h hs (mapDoms f c ds) (cod.mapFree f (c + ds.length)) (b.mapFree f (c + ds.length + 1))
  | .call g as hd => .call (g.mapFree f c) (as.map (·.mapFree f c)) hd
  | .succ t => .succ (t.mapFree f c)
  | .fst t => .fst (t.mapFree f c)
  | .snd t => .snd (t.mapFree f c)
  | .ref t => .ref (t.mapFree f c)
  | .prod a b => .prod (a.mapFree f c) (b.mapFree f c)
  | .pair a b => .pair (a.mapFree f c) (b.mapFree f c)
  | .and a b => .and (a.mapFree f c) (b.mapFree f c)
  | .andI a b => .andI (a.mapFree f c) (b.mapFree f c)
  | .cong a b => .cong (a.mapFree f c) (b.mapFree f c)
  | .ascribe a b => .ascribe (a.mapFree f c) (b.mapFree f c)
  | .eq a b d => .eq (a.mapFree f c) (b.mapFree f c) (d.mapFree f c)
  | .id a b d => .id (a.mapFree f c) (b.mapFree f c) (d.mapFree f c)
  | .prim n as => .prim n (as.map (·.mapFree f c))
  | t => t

partial def mapDoms (f : Nat → Nat → Place) (c : Nat) (ds : List Term) : List Term :=
  (ds.zipIdx).map fun (d, i) => d.mapFree f (c + i)

partial def mp (f : Nat → Nat → Place) (c : Nat) (p : Place) : Place :=
  p.mapRoot fun j => if j < c then .var j else f c (j - c)
end

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
  | .fix _ _ ds cod b =>
      (ds.zipIdx.flatMap fun (d, i) => d.placeOccs (c + i)) ++ cod.placeOccs (c + ds.length)
        ++ b.placeOccs (c + ds.length + 1)
  | .call g as _ => g.placeOccs c ++ as.flatMap (·.placeOccs c)
  | .succ t | .fst t | .snd t | .ref t => t.placeOccs c
  | .prod a b | .pair a b | .and a b | .andI a b | .cong a b | .ascribe a b =>
      a.placeOccs c ++ b.placeOccs c
  | .eq a b d | .id a b d => a.placeOccs c ++ b.placeOccs c ++ d.placeOccs c
  | .prim _ as => as.flatMap (·.placeOccs c)
  | _ => []

/-- Free occurrences, with the root expressed as an index into the enclosing frame. -/
def Term.freeOccs (t : Term) : List (Nat × Place × PKind) :=
  (t.placeOccs 0).filterMap fun (c, p, k) =>
    if p.root ≥ c then some (p.root - c, p, k) else none

/-- The free variables (enclosing-frame indices) of a term, without duplicates. -/
def Term.freeVars (t : Term) : List Nat :=
  t.freeOccs.foldl (fun acc (o, _, _) => if acc.contains o then acc else acc ++ [o]) []

mutual
/-- Does a predicate hold of some atom (sub-value) of a value? Looks inside sealed
programs, closures and Π-types too (loans may occur there: RULES §2). -/
partial def Value.anyAtom (P : Value → Bool) (v : Value) : Bool :=
  P v || match v with
  | .succ w | .tRef w | .borrow _ w => w.anyAtom P
  | .pair a b | .tProd a b | .tAnd a b => a.anyAtom P || b.anyAtom P
  | .tEq A a b => A.anyAtom P || a.anyAtom P || b.anyAtom P
  | .clo cs t | .tPi cs t => cs.any (·.anyAtom P) || t.anyAtom P
  | .sealed t => t.anyAtom P
  | _ => false

partial def Term.anyAtom (P : Value → Bool) : Term → Bool
  | .val v => v.anyAtom P
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.anyAtom P
  | .letIn _ t u | .seq t u | .prod t u | .pair t u | .and t u | .andI t u
  | .cong t u | .ascribe t u => t.anyAtom P || u.anyAtom P
  | .matchNat _ z s => z.anyAtom P || s.anyAtom P
  | .pi _ ds c => ds.any (·.anyAtom P) || c.anyAtom P
  | .fix _ _ ds c b => ds.any (·.anyAtom P) || c.anyAtom P || b.anyAtom P
  | .call f as _ => f.anyAtom P || as.any (·.anyAtom P)
  | .eq a b c | .id a b c => a.anyAtom P || b.anyAtom P || c.anyAtom P
  | .prim _ as => as.any (·.anyAtom P)
  | _ => false
end

mutual
/-- All loan labels occurring in a value (with repetition). -/
partial def Value.loans : Value → List Nat
  | .loan l => [l]
  | .succ w | .tRef w | .borrow _ w => w.loans
  | .pair a b | .tProd a b | .tAnd a b => a.loans ++ b.loans
  | .tEq A a b => A.loans ++ a.loans ++ b.loans
  | .clo cs t | .tPi cs t => cs.flatMap Value.loans ++ t.loans
  | .sealed t => t.loans
  | _ => []

partial def Term.loans : Term → List Nat
  | .val v => v.loans
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => t.loans
  | .letIn _ t u | .seq t u | .prod t u | .pair t u | .and t u | .andI t u
  | .cong t u | .ascribe t u => t.loans ++ u.loans
  | .matchNat _ z s => z.loans ++ s.loans
  | .pi _ ds c => ds.flatMap Term.loans ++ c.loans
  | .fix _ _ ds c b => ds.flatMap Term.loans ++ c.loans ++ b.loans
  | .call f as _ => f.loans ++ as.flatMap Term.loans
  | .eq a b c | .id a b c => a.loans ++ b.loans ++ c.loans
  | .prim _ as => as.flatMap Term.loans
  | _ => []
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
