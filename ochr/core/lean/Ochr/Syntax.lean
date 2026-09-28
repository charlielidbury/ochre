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

mutual
/-- Places `p ::= x | *p | p.1 | p.2` (`.1` is the predecessor of `S v` or the first
component of a pair). -/
inductive Place where
  | var (i : Nat)
  | deref (p : Place)
  | fst (p : Place)
  | snd (p : Place)

inductive Term where
  | place (p : Place)                         -- read `p` ([Read])
  | borrow (p : Place)                        -- `&p` ([Borrow])
  | assign (p : Place) (t : Term)             -- `p := t` ([Assign])
  | letIn (h : Hint) (t u : Term)             -- `let x = t; u` ([Let])
  | seq (t u : Term)                          -- `t; u`
  | matchNat (p : Place) (z s : Term)         -- `match p { Z => z | S y => s }`, y ≡ p.1
  | const (n : String)                        -- a top-level definition
  | val (v : Value)                           -- an embedded value (inside sealed programs, closures)
  | sort (l : Nat)                            -- `sort 0 = Prop`, `sort (i+1) = Type_i`
  | pi (hs : List Hint) (doms : List Term) (cod : Term)
  | fix (self : Hint) (hs : List Hint) (doms : List Term) (cod : Term) (body : Term)
  | call (f : Term) (args : List Term) (head : Bool)   -- `head`: the head call of a sealed program ([Seal])
  | nat | zero | succ (t : Term) | unit | tt
  | prod (A B : Term) | pair (t u : Term) | fst (t : Term) | snd (t : Term)
  | eq (A t u : Term) | refl | top | and (P Q : Term) | andI (h k : Term)
  | cong (f h : Term)
  | ref (A : Term)                            -- the borrow type `&A`
  | id (A t u : Term)                         -- `Id A t u` (§4)
  | ascribe (t A : Term)                      -- `(t : A)`
  | prim (n : String) (args : List Term)      -- `J A P h t`, `trans h k`, `symm h` (derivable from J)

/-- Runtime values (RULES §2). Types are values too. -/
inductive Value where
  | zero | succ (v : Value) | unit | pair (v w : Value)
  | gfn (n : String)                          -- a top-level function
  | clo (caps : List Value) (t : Term)        -- closure: a `fix` term closed over captured values
  | borrow (l : Nat) (v : Value)              -- `borrow_ℓ v`: the borrowed content lives in the borrow
  | loan (l : Nat)                            -- `loan_ℓ`: a variable bound by borrow ℓ
  | bot                                       -- `⊥`: moved out / ended
  | abs (s : Nat)                             -- `σ`: an abstract value (Lean's fvar)
  | sealed (t : Term)                         -- `⌈t⌉`: a closed program whose run is stuck
  | proof                                     -- `⋆`: every value of a proposition (proof irrelevance)
  | tNat | tUnit | tProd (A B : Value) | tEq (A a b : Value) | tTop | tAnd (P Q : Value)
  | tRef (A : Value)
  | tPi (caps : List Value) (t : Term)        -- Π-type: a closure over formation-time values (P2)
  | sort (l : Nat)
end

mutual
partial def Place.beq : Place → Place → Bool
  | .var i, .var j => i == j
  | .deref p, .deref q | .fst p, .fst q | .snd p, .snd q => p.beq q
  | _, _ => false

partial def Term.beqList : List Term → List Term → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Term.beqList as bs
  | _, _ => false

partial def Term.beq : Term → Term → Bool
  | .place p, .place q | .borrow p, .borrow q => p.beq q
  | .assign p t, .assign q u => p.beq q && t.beq u
  | .letIn _ t u, .letIn _ t' u' => t.beq t' && u.beq u'
  | .seq t u, .seq t' u' => t.beq t' && u.beq u'
  | .matchNat p z s, .matchNat q z' s' => p.beq q && z.beq z' && s.beq s'
  | .const n, .const m => n == m
  | .val v, .val w => v.beq w
  | .sort l, .sort m => l == m
  | .pi _ ds c, .pi _ ds' c' => Term.beqList ds ds' && c.beq c'
  | .fix _ _ ds c b, .fix _ _ ds' c' b' => Term.beqList ds ds' && c.beq c' && b.beq b'
  | .call f as h, .call g bs h' => f.beq g && Term.beqList as bs && h == h'
  | .nat, .nat | .zero, .zero | .unit, .unit | .tt, .tt | .refl, .refl | .top, .top => true
  | .succ t, .succ u | .fst t, .fst u | .snd t, .snd u | .ref t, .ref u => t.beq u
  | .prod a b, .prod c d | .pair a b, .pair c d | .and a b, .and c d
  | .andI a b, .andI c d | .cong a b, .cong c d | .ascribe a b, .ascribe c d => a.beq c && b.beq d
  | .eq a b c, .eq d e f | .id a b c, .id d e f => a.beq d && b.beq e && c.beq f
  | .prim n as, .prim m bs => n == m && Term.beqList as bs
  | _, _ => false

partial def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Value.beqList as bs
  | _, _ => false

partial def Value.beq : Value → Value → Bool
  | .zero, .zero | .unit, .unit | .bot, .bot | .proof, .proof
  | .tNat, .tNat | .tUnit, .tUnit | .tTop, .tTop => true
  | .succ v, .succ w | .tRef v, .tRef w => v.beq w
  | .pair a b, .pair c d | .tProd a b, .tProd c d | .tAnd a b, .tAnd c d => a.beq c && b.beq d
  | .gfn n, .gfn m => n == m
  | .clo cs t, .clo ds u | .tPi cs t, .tPi ds u => Value.beqList cs ds && t.beq u
  | .borrow l v, .borrow m w => l == m && v.beq w
  | .loan l, .loan m | .abs l, .abs m | .sort l, .sort m => l == m
  | .sealed t, .sealed u => t.beq u
  | .tEq a b c, .tEq d e f => a.beq d && b.beq e && c.beq f
  | _, _ => false
end

instance : BEq Place := ⟨Place.beq⟩
instance : BEq Term := ⟨Term.beq⟩
instance : BEq Value := ⟨Value.beq⟩
instance : Inhabited Place := ⟨.var 0⟩
instance : Inhabited Term := ⟨.tt⟩
instance : Inhabited Value := ⟨.unit⟩

end Ochr
