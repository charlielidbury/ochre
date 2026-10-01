import Ochr.Examples.«00Std»
open Ochr Ochr.Test
set_option ochr.uninitTypes true in
set_option ochr.lentProofs true in
ochr LentBox uses Std {
  untagged inductive Uninit (E : Type) := Empty | Full(x : E)
  def Init (E : Type) (u : Uninit(E)) : Prop := (
    match u {
      Empty => False,
      Full(x) => ⊤,
    }
  )
  def UGet (E : Type) (u : &Uninit(E)) (h : Init(E, *u)) : &E := (
    match *u {
      Full(x) => &x,
      Empty => match h {},
    }
  )
  -- writing back through UGet's borrow leaves the cell full, whatever is written
  def UGetPut (E : Type) (u : Uninit(E)) (h : Init(E, u)) (w : E) :
      Eq(Uninit(E), (let c = u; let r = UGet(E, &c, h); *r := w; c), Full(w)) := (
    match u {
      Full(x) => refl,
      Empty => match h {},
    }
  )
  def UGetPutAll (E : Type) (u : Uninit(E)) (h : Init(E, u)) :
      (Π(y : E). Eq(Uninit(E), (let c = u; let r = UGet(E, &c, h); *r := y; c), Full(y))) := (
    λ(y : E) : Eq(Uninit(E), (let c = u; let r = UGet(E, &c, h); *r := y; c), Full(y)) => UGetPut(E, u, h, y)
  )
  inductive PBox := MkP(x : Uninit(Word), h : Init(Word, x))
  -- an element borrow out of a value with an invariant: re-proved for whatever the borrow writes
  def GetP (b : &PBox) : &Word := (
    match *b {
      MkP(x, h) => (
        let h0 = h;
        let hp = UGetPutAll(Word, x, h0);
        let res = UGet(Word, &x, h0);
        h := (rewrite ← hp(*res) in refl);
        res
      ),
    }
  )
  def UseP : Id(Word, (let b = MkP(Full(Zero), refl); let r = GetP(&b); *r := Succ(Zero); match b { MkP(x, h) => (let k : Init(Word, x) = h; let g = UGet(Word, &x, k); *g) }), Succ(Zero)) := refl
  -- the D64 hole, closed: a proof that holds only of what the borrow holds now is refused
  def IsZ (n : Word) : Prop := (
    match n {
      Zero => ⊤,
      Succ(m) => False,
    }
  )
  inductive ZBox := MkZ(x : Word, h : IsZ(x))
  reject def Lie (b : &ZBox) : Unit := (
    match *b {
      MkZ(x, h) => (
        let h0 = h;
        let r = &x;
        h := h0;
        *r := Succ(Zero)
      ),
    }
  )
  reject def GetX (b : &ZBox) : &Word := (
    match *b {
      MkZ(x, h) => (
        let h0 = h;
        let r = &x;
        h := h0;
        r
      ),
    }
  )
}
#eval (run "LentBox" LentBox { uninitTypes := true, lentProofs := true }).rows.map fun r => (r.name, r.expectAccept == r.verdict.ok, match r.verdict with | .accepted => "" | .rejected m _ => m)
#eval IO.println ((run "LentBox" LentBox { uninitTypes := true, lentProofs := true, derivation := true }).showTrace "Lie")
