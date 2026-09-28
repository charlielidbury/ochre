import Ochr.Examples.V15

/-! # Rules v1.7 regressions: erasure is purely syntactic (D35)

The formal appendix's notes 1 and 2 (BoomL, BoomB) are closed proofs of `False` that the
v1.6 checker accepted; P1 is a third one, found while implementing v1.7, caused by this
checker's reading of sequencing forms. Row tests show [Close]'s row read from the
declared codomain. The counterfactual ledger (Registry.lean) shows each switch. -/

open Ochr.Test

ochr V17 {
  def U (n : Nat) : Type := match n { Z => Prop | S _ => Prop }
  def V (n : Nat) : U(n) := match n { Z => ⊤ | S _ => ⊤ }

  -- Note 1 (BoomL): a local function's class read from its codomain evaluated with the
  -- captured n: data at the generic n (⌈U(σ)⌉), types at n = Z (U(Z) = Prop). v1.7 reads
  -- the codomain term U(n): not a sort, of sort Type₀, so h(&c) runs on both paths.
  def LieL (n : Nat) : Id Nat (let h = (λ(x : &Nat) : U(n) => (*x := S Z; V(n))); let c = Z; h(&c); c) (S Z) := refl
  reject def BoomL : Eq Nat Z (S Z) := LieL(Z)

  -- Note 2 (BoomB): a stuck block of type Prop (a sort) was erased as a call returning
  -- types; the same match run directly is not erased. v1.7 erases a block exactly when
  -- its match would be, so the write to c is kept, and the statement is not ⊤ ...
  reject def LieB (n : Nat) : Id Nat (let c = Z; let T = match n { Z => (c := S Z; ⊤) | S _ => (c := S Z; ⊤) }; c) Z := refl
  reject def BoomB : Eq Nat (S Z) Z := LieB(Z)
  -- ... while the true statement is proved by splitting on n
  def TruthB (n : Nat) : Id Nat (let c = Z; let T = match n { Z => (c := S Z; ⊤) | S _ => (c := S Z; ⊤) }; c) (S Z) :=
    match n { Z => refl | S _ => refl }

  -- P1 (this checker, found implementing v1.7): a block of type ⊤ is erased (sort
  -- Prop), but the checker erased a sequence only when its tail is erased, and a place
  -- holding a proof was not, so at n = Z the match ran for real. A place, constant or λ
  -- holding a proof is now erased, so a proof-typed tail is erased on every path.
  def LieP (n : Nat) : Id Nat (let c = Z; let h : ⊤ = refl; let T = match n { Z => (c := S Z; h) | S _ => (c := S Z; h) }; c) Z := refl
  reject def BoomP : Eq Nat (S Z) Z := LieP(Z)

  -- P2 (this checker, found implementing v1.7): a block erased when its *computed* type
  -- has sort Prop disagrees with the direct path, where the arms' calls are classed by
  -- syntax: f's codomain V(Z) computes to ⊤ but is not declared of sort Prop, so f(&c)
  -- runs. The block is erased only when every arm is a proof, so it is not erased here.
  reject def LieG (m : Nat) (g : Π(y : Nat). V(Z)) :
    Id Nat (let c = Z; let f = (λ(x : &Nat) : V(Z) => (*x := S Z; g(0))); let T = match m { Z => f(&c) | S _ => f(&c) }; c) Z := refl
  reject def BoomG : Eq Nat (S Z) Z := LieG(Z, (λ(y : Nat) : V(Z) => refl))
  def TruthG (m : Nat) (g : Π(y : Nat). V(Z)) :
    Id Nat (let c = Z; let f = (λ(x : &Nat) : V(Z) => (*x := S Z; g(0))); let T = match m { Z => f(&c) | S _ => f(&c) }; c) (S Z) :=
    match m { Z => refl | S _ => refl }

  -- A sequence whose tail returns types is not a proof, so it is not erased (v1.7); only
  -- the call F(&c) itself runs on a private copy. v1.6 erased the whole sequence.
  def F (x : &Nat) : Prop := *x := S Z; ⊤
  def SeqT : Id Nat (let c = Z; let T = (c := S Z; F(&c)); c) (S Z) := refl

  -- [Close]'s row from the declared codomain: G's codomain UU(n) computes to Unit at
  -- n = Z, but only a codomain that is syntactically Unit gets the Unit row (v1.6 took the
  -- Unit row at the instance and the data row at the generic call)
  def UU (n : Nat) : Type := match n { Z => Unit | S _ => Unit }
  def AddU (x : &Nat) : Unit by x := match *x { Z => () | S p => AddU(&p) }
  def G (x : &Nat) (n : Nat) : UU(n) by x :=
    match n { Z => match *x { Z => () | S p => G(&p, n) } | S _ => AddU(x) }
  def RowUnit (x : &Nat) : Id Unit (let c = *x; AddU(&c)) () := refl
  reject def RowI (x : &Nat) : Id Unit (let c = *x; G(&c, Z)) () := refl
  def RowIInd (x : &Nat) : Id Unit (let c = *x; G(&c, Z)) () by x :=
    match *x { Z => refl | S p => RowIInd(&p) }
}

#eval IO.println (run "V17" V17).show

-- every verdict as expected, and exactly 20 assertions (a truncated file changes the count)
#guard (run "V17" V17).allAsExpected
#guard (run "V17" V17).count == 20
