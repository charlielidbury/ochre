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

mutual
/-- Places `p ::= x | *p | p.1 | p.2 | p.g` (`.1` is the predecessor of `S v` or field 1 of
a pair, `.2` field 2 of a pair: v2.1, D52, pairs are the library inductive `Pair`; `p.g`
a constructor field). -/
inductive Place where
  | var (i : Nat)
  | deref (p : Place)
  | fst (p : Place)
  | snd (p : Place)
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
  | fst (t : Term) | snd (t : Term)          -- `t.1`, `t.2`: field 1 or 2 of a pair (D52)
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
  | clo (caps : List Value) (t : Term)        -- closure: a `fix` term closed over captured values
  | borrow (l : Nat) (v : Value)              -- `borrow_ℓ v`: the borrowed content lives in the borrow
  | loan (l : Nat)                            -- `loan_ℓ`: a variable bound by borrow ℓ
  | bot                                       -- `⊥`: moved out / ended
  | abs (s : Nat)                             -- `σ`: an abstract value (Lean's fvar)
  | sealed (t : Term)                         -- `⌈t⌉`: a closed program whose run is stuck
  | proof                                     -- `⋆`: every value of a proposition (proof irrelevance)
  | tNat | tUnit | tEq (A a b : Value)
  | tRef (A : Value)
  | tPi (caps : List Value) (t : Term)        -- Π-type: a closure over formation-time values (P2)
  | sort (l : Nat)
  | ind (ty : String) (c : Nat) (h : Hint) (ps : List Value) (fs : List Value)
                                              -- a constructor value `C(ā; v̄)` of a data type, recording
                                              -- its parameters when known (D49; `==` ignores them, the
                                              -- type determines them); a Prop inductive's value is ⋆ (D42)
  | tInd (n : String) (args : List Value)     -- `D(ā)`; `True`, `False`, `And(P, Q)` are library inductives
end

mutual
partial def Place.beq : Place → Place → Bool
  | .var i, .var j => i == j
  | .deref p, .deref q | .fst p, .fst q | .snd p, .snd q => p.beq q
  | .field f p, .field g q => f == g && p.beq q
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
  | .fix _ _ ds c d b, .fix _ _ ds' c' d' b' => Term.beqList ds ds' && c.beq c' && d == d' && b.beq b'
  | .call f as h, .call g bs h' => f.beq g && Term.beqList as bs && h == h'
  | .nat, .nat | .zero, .zero | .unit, .unit | .tt, .tt => true
  | .succ t, .succ u | .fst t, .fst u | .snd t, .snd u | .ref t, .ref u => t.beq u
  | .cong a b, .cong c d | .ascribe a b, .ascribe c d => a.beq c && b.beq d
  | .eq a b c, .eq d e f | .id a b c, .id d e f => a.beq d && b.beq e && c.beq f
  | .prim n as, .prim m bs => n == m && Term.beqList as bs
  | .tind n as, .tind m bs => n == m && Term.beqList as bs
  | .ctor t c _ ps as, .ctor u d _ qs bs => t == u && c == d && Term.beqList ps qs && Term.beqList as bs
  | .matchInd p t as, .matchInd q u bs => p.beq q && t == u && Term.beqList (as.map (·.2)) (bs.map (·.2))
  | _, _ => false

partial def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Value.beqList as bs
  | _, _ => false

partial def Value.beq : Value → Value → Bool
  | .zero, .zero | .unit, .unit | .bot, .bot | .proof, .proof
  | .tNat, .tNat | .tUnit, .tUnit => true
  | .succ v, .succ w | .tRef v, .tRef w => v.beq w
  | .gfn n, .gfn m => n == m
  | .clo cs t, .clo ds u | .tPi cs t, .tPi ds u => Value.beqList cs ds && t.beq u
  | .borrow l v, .borrow m w => l == m && v.beq w
  | .loan l, .loan m | .abs l, .abs m | .sort l, .sort m => l == m
  | .sealed t, .sealed u => t.beq u
  | .tEq a b c, .tEq d e f => a.beq d && b.beq e && c.beq f
  | .ind t c _ _ fs, .ind u d _ _ gs => t == u && c == d && Value.beqList fs gs
  | .tInd n as, .tInd m bs => n == m && Value.beqList as bs
  | _, _ => false
end

instance : BEq Place := ⟨Place.beq⟩
instance : BEq Term := ⟨Term.beq⟩
instance : BEq Value := ⟨Value.beq⟩
instance : Inhabited Place := ⟨.var 0⟩
instance : Inhabited Term := ⟨.tt⟩
instance : Inhabited Value := ⟨.unit⟩

end Ochr
