import Ochr.Examples.Bool
import Ochr.Examples.Logic

/-! # Word: the numbers code computes with

The library for code that computes with `Word`s: the order `Le` and `Lt` as propositions,
which index bounds and invariants are stated with; the comparisons that return the proof,
`LeDec` and `LtDec`; boolean comparisons, each named for the proposition it decides with a
`B` (`EqB`, `LeB`, `LtB`); addition `WAdd`, truncated subtraction `Sub` and the predecessor
`Pred`; `W(n)`, the `Word` for the numeral `n` (numerals are `Nat`s); and facts about them.
Also `ModS(k, c)`, `k mod c`, with its bound `ModLt`, for a hash map's bucket index. The
arrays library and the case studies use it. A tour program that defines its own `Le` or `Pred`
on `Nat` (`CurrentState`, `Numbers`) is about that definition and does not use it. The type
itself is the block `WordType`, which `Words` uses: a program that needs only the type uses
that. -/

open Ochr.Test

-- The type on its own, for a program that only needs the type and defines its own order or
-- numerals (`Trees`' `Lt`, as the paper prints it, and `Borrows`' witness `W`).
ochr WordType {
  -- A number that code only computes with (a key, an index, a length, a counter) is a
  -- `Word`: unary in the logic, a machine word in the cost model. It is declared `copy`, so
  -- reading one copies it, while reading a `Nat`, the structure in-place code walks and
  -- changes, moves it (D53).
  copy inductive Word := Zero | Succ(pred : Word)
}

ochr Words uses WordType, Bools, Logic {
  -- ## The order
  def Le (a : Word) (b : Word) : Prop by a := (
    match a {
      Zero => ⊤,
      Succ(a') => match b {
        Zero => False,
        Succ(b') => Le(a', b'),
      },
    }
  )

  def Lt (a : Word) (b : Word) : Prop := Le(Succ(a), b)

  -- ## Arithmetic and numerals
  -- Addition, by recursion on the first number.
  def WAdd (a : Word) (b : Word) : Word by a := (
    match a {
      Zero => b,
      Succ(a') => Succ(WAdd(a', b)),
    }
  )

  -- `W(n)`, the `Word` for the numeral `n` (for the runs).
  def W (n : Nat) : Word by n := (
    match n {
      Z => Zero,
      S m => Succ(W(m)),
    }
  )

  -- Subtraction, truncated at zero, and the predecessor (`Pred(Zero)` is `Zero`).
  def Sub (a : Word) (b : Word) : Word by b := (
    match b {
      Zero => a,
      Succ(b') => match a {
        Zero => Zero,
        Succ(a') => Sub(a', b'),
      },
    }
  )

  def Pred (n : Word) : Word := (
    match n {
      Zero => Zero,
      Succ(m) => m,
    }
  )

  -- ## Comparisons
  -- Booleans, for code that only branches (a key comparison, a load-factor test).
  def EqB (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b {
        Zero => true,
        Succ(_) => false,
      },
      Succ(a') => match b {
        Zero => false,
        Succ(b') => EqB(a', b'),
      },
    }
  )

  def LeB (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => true,
      Succ(a') => match b {
        Zero => false,
        Succ(b') => LeB(a', b'),
      },
    }
  )

  def LtB (a : Word) (b : Word) : Bool by a := (
    match a {
      Zero => match b {
        Zero => false,
        Succ(_) => true,
      },
      Succ(a') => match b {
        Zero => false,
        Succ(b') => LtB(a', b'),
      },
    }
  )

  -- Decisions that carry their evidence: a comparison at runtime yields the proof an index
  -- needs.
  def LeDec (a : Word) (b : Word) : Dec(Le(a, b), Lt(b, a)) by a := (
    match a {
      Zero => Yes(refl),
      Succ(a') => match b {
        Zero => No(refl),
        Succ(b') => LeDec(a', b'),
      },
    }
  )

  def LtDec (i : Word) (n : Word) : Dec(Lt(i, n), Le(n, i)) := LeDec(Succ(i), n)

  -- ## Facts, each by recursion on a number
  def LeRefl (a : Word) : Le(a, a) by a := (
    match a {
      Zero => refl,
      Succ(a') => LeRefl(a'),
    }
  )

  def LeStep (a : Word) (b : Word) (h : Le(a, b)) : Le(a, Succ(b)) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match h {},
        Succ(b') => LeStep(a', b', h),
      },
    }
  )

  def LeTrans (a : Word) (b : Word) (c : Word) (h1 : Le(a, b)) (h2 : Le(b, c)) : Le(a, c) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match h1 {},
        Succ(b') => match c {
          Zero => match h2 {},
          Succ(c') => LeTrans(a', b', c', h1, h2),
        },
      },
    }
  )

  def LeOfLt (a : Word) (b : Word) (h : Lt(a, b)) : Le(a, b) by a := (
    match a {
      Zero => refl,
      Succ(a') => match b {
        Zero => match h {},
        Succ(b') => LeOfLt(a', b', h),
      },
    }
  )

  def LeAddL (r : Word) (j : Word) : Le(j, WAdd(r, j)) by r := (
    match r {
      Zero => LeRefl(j),
      Succ(r') => LeStep(j, WAdd(r', j), LeAddL(r', j)),
    }
  )

  def AddRS (r : Word) (j : Word) : Eq(Word, Succ(WAdd(r, j)), WAdd(r, Succ(j))) by r := (
    match r {
      Zero => refl,
      Succ(r') => AddRS(r', j),
    }
  )

  def AddZeroR (m : Word) : Eq(Word, WAdd(m, Zero), m) by m := (
    match m {
      Zero => refl,
      Succ(m') => AddZeroR(m'),
    }
  )

  def AddOneR (m : Word) : Eq(Word, WAdd(m, Succ(Zero)), Succ(m)) by m := (
    match m {
      Zero => refl,
      Succ(m') => AddOneR(m'),
    }
  )

  def SubPos (m : Word) (k : Word) (h : Le(k, m)) : Le(Succ(Zero), Sub(Succ(m), k)) by k := (
    match k {
      Zero => refl,
      Succ(k') => match m {
        Zero => match h {},
        Succ(m') => SubPos(m', k', h),
      },
    }
  )

  -- What is left after a pivot at `k` is at most `m` long.
  def SubOneLe (m : Word) (k : Word) : Le(Sub(Sub(Succ(m), k), Succ(Zero)), m) by k := (
    match k {
      Zero => LeRefl(m),
      Succ(k') => match m {
        Zero => match k' {
          Zero => refl,
          Succ(_) => refl,
        },
        Succ(m') => LeStep(Sub(Sub(Succ(m'), k'), Succ(Zero)), m', SubOneLe(m', k')),
      },
    }
  )

  -- a < b gives a ≠ b
  def LtNe (a : Word) (b : Word) (h : Lt(a, b)) (e : Eq(Word, a, b)) : False by a := (
    match a {
      Zero => match b {
        Zero => match h {},
        Succ(_) => match e {},
      },
      Succ(a') => match b {
        Zero => match e {},
        Succ(b') => LtNe(a', b', h, e),
      },
    }
  )

  def LeAntisym (a : Word) (b : Word) (h1 : Le(a, b)) (h2 : Le(b, a)) : Eq(Word, a, b) by a := (
    match a {
      Zero => match b {
        Zero => refl,
        Succ(_) => match h2 {},
      },
      Succ(a') => match b {
        Zero => match h1 {},
        Succ(b') => LeAntisym(a', b', h1, h2),
      },
    }
  )

  -- What is left after `k < n` is not empty.
  def SubPosLt (n : Word) (k : Word) (h : Lt(k, n)) : Le(Succ(Zero), Sub(n, k)) by k := (
    match k {
      Zero => match n {
        Zero => match h {},
        Succ(_) => refl,
      },
      Succ(k') => match n {
        Zero => match h {},
        Succ(m) => SubPosLt(m, k', h),
      },
    }
  )

  -- The key comparison says a key equals itself.
  def EqBRefl (k : Word) : Eq(Bool, EqB(k, k), true) by k := (
    match k {
      Zero => refl,
      Succ(k') => EqBRefl(k'),
    }
  )

  -- ## The bucket index
  -- `k mod c`, counting up with a remainder that wraps round at `c`, and its bound.
  def ModS (k : Word) (c : Word) : Word by k := (
    match k {
      Zero => Zero,
      Succ(k') => (
        let r = Succ(ModS(k', c));
        let e = EqB(r, c);
        match e {
          true => Zero,
          false => r,
        }
      ),
    }
  )

  def LeNext (a : Word) (c : Word) (h : Le(a, c)) (e : Eq(Bool, EqB(a, c), false)) : Le(Succ(a), c) by a := (
    match a {
      Zero => match c {
        Zero => match e {},
        Succ(_) => refl,
      },
      Succ(a') => match c {
        Zero => match h {},
        Succ(c') => LeNext(a', c', h, e),
      },
    }
  )

  def ModLt (k : Word) (c : Word) (hc : Lt(Zero, c)) : Lt(ModS(k, c), c) by k := (
    match k {
      Zero => hc,
      Succ(k') => (
        let e = EqB(Succ(ModS(k', c)), c);
        match e {
          true => hc,
          false => LeNext(Succ(ModS(k', c)), c, ModLt(k', c, hc), refl),
        }
      ),
    }
  )
}
