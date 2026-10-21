import Ochr.Test

/-! # 0. Std, Words and Fixtures: the definitions the other files share

An `ochr` block may use other blocks: `ochr Numbers uses Std { … }` checks `Std`'s
declarations first, then its own, in one namespace. Only declarations that `Std` expects to
be accepted, and that are accepted, are visible to its users; they are checked again in
each block that uses them, so switching a rule off re-decides them there too, and each one's
verdict is asserted here, in its home block.

`Std` holds the paper's first example, in-place addition `AddM` and pure addition `Add`
defined by running `AddM` on a copy, with the first proof, that adding zero in place does
nothing, and that adding a successor adds one (`AddS`); the returned borrow `TailM`; and the
data types the other files share (`Bool`, `List`, `Box`, `Opt`, `Dec`, `Void`, `Word`).
`Words`, below, is the library for `Word`s: the order, comparisons, arithmetic and numerals.
`Fixtures` holds definitions that only tests need. These are the one copy of each: no other
file redefines them, except a test whose subject is its own definition, which says so where
it declares it. The library proper, `Pair`, `False`, `True` and `And` (RULES §1, §8), is the
`Prelude` block (`Ochr/Prelude.lean`), which every block uses implicitly; `Nat` and `Unit` are
built into the checker.

Defined in RULES §1 (syntax), §3 (the machine) and §7 (examples). -/

open Ochr.Test

-- The library block, `Prelude` (`Ochr/Prelude.lean`), which every block uses implicitly, is
-- asserted here, since that file cannot run the checker's tests itself.
#guard Prelude.decls.length == 4

ochr Std {
  -- In-place addition: walk down to the `Z` at the bottom of `*x` and replace it with `y`.
  -- `by x` says that `x` gets smaller at each recursive call.
  def AddM (x : &Nat) (y : Nat) : Unit by x := (
    match *x {
      Z => *x := y,
      S p => AddM(&p, y),
    }
  )

  -- Pure addition, by running the in-place version on the local `x`.
  def Add (x : Nat) (y : Nat) : Nat := (
    AddM(&x, y);
    x
  )

  -- An effect as a statement: adding zero in place leaves `*x` as it was. The proof is by
  -- recursion on `*x`: in the `S(p)` arm, the recursive call about `&p` proves the goal about
  -- the whole of `*x`, because the borrow of `p` sits inside `*x`.
  def AddMZero (x : &Nat) : Id(Unit, AddM(x, 0), ()) by x := (
    match *x {
      Z => refl,
      S p => AddMZero(&p),
    }
  )

  -- `x + S(y) = S(x + y)`, proved in place by the same bare recursion, and transferred to
  -- `Add` by lending it the local `x` (the trees of `10Inductives` use it).
  def AddMS (x : &Nat) (y : Nat) : Id(Unit, AddM(x, S(y)), AddM(&*x, y); *x := S(*x)) by x := (
    match *x {
      Z => refl,
      S p => AddMS(&p, y),
    }
  )

  def AddS (x : Nat) (y : Nat) : Id(Nat, Add(x, S(y)), S(Add(x, y))) := AddMS(&x, y)

  -- A borrow of the final `Z` of `*x` (a function that returns a borrow; see
  -- `ReturnedBorrows`).
  def TailM (x : &Nat) : &Nat by x := (
    match *x {
      Z => x,
      S p => TailM(&p),
    }
  )

  -- Data types: booleans, and lists and boxes with a parameter.
  inductive Bool := false | true
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  inductive Box (A : Type) := MkBox(x : A)

  -- A boolean as a proposition: `⊤` when it is `true`.
  def IsTrue (b : Bool) : Prop := (
    match b {
      false => False,
      true => ⊤,
    }
  )

  -- An optional value (Rust's `Option`), and whether one holds a value, as propositions.
  inductive Opt (A : Type) := None | Some(v : A)

  def IsSome (A : Type) (o : Opt(A)) : Prop := (
    match o {
      None => False,
      Some(_) => ⊤,
    }
  )

  def IsNone (A : Type) (o : Opt(A)) : Prop := (
    match o {
      None => ⊤,
      Some(_) => False,
    }
  )

  -- A decision that carries its evidence: `Yes` with a proof of `P`, or `No` with a proof of
  -- `Q` (`LeDec` in `Words` decides the order on `Word`). At runtime `Dec` is a boolean; its
  -- fields are proofs, which are erased.
  inductive Dec (P : Prop) (Q : Prop) := Yes(h : P) | No(k : Q)

  -- A type with no values, and a proof of `False` from one.
  inductive Void : Type
  def absurdV (v : Void) : False := match v {}

  -- A number that code only computes with (a key, an index, a length, a counter) is a
  -- `Word`: unary in the logic, a machine word in the cost model. It is declared `copy`, so
  -- reading one copies it, while reading a `Nat`, the structure in-place code walks and
  -- changes, moves it (D53).
  copy inductive Word := Zero | Succ(pred : Word)
}

-- the exact number of declarations (a truncated file changes it)
#guard Std.decls.length == 17

/-! ## Words: the order, comparisons and arithmetic on `Word`

The library for code that computes with `Word`s: the order `Le` and `Lt` as propositions,
which index bounds and invariants are stated with; the comparisons that return the proof,
`LeDec` and `LtDec`; boolean comparisons, each named for the proposition it decides with a
`B` (`EqB`, `LeB`, `LtB`); addition `WAdd`, truncated subtraction `Sub` and the predecessor
`Pred`; `W(n)`, the `Word` for the numeral `n` (numerals are `Nat`s); and facts about them.
The arrays library and the case studies use it. A tour program that defines its own `Le` or
`Pred` on `Nat` (`CurrentState`, `Numbers`) is about that definition and does not use it. -/

ochr Words uses Std {
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
}

-- the exact number of declarations (a truncated file changes it)
#guard Words.decls.length == 25

/-! ## Fixtures

Definitions that only the tests need: a choice of a borrow by a number, a type with no
closed values other than `False`, and a type computed by a program. -/

ochr Fixtures {
  -- A borrow into `x` or `y`, chosen by `n`: at an abstract `n`, which one is not known.
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := (
    match n {
      Z => x,
      S _ => y,
    }
  )

  -- A type with no closed values: its only constructor needs one already.
  inductive Empty := E(e : Empty)

  -- A type computed by a program: `U(n)` is `Prop` for every `n`, but only after computing
  -- it; at an abstract `n` it is stuck. `V(n)` proves it. The erasure examples use them.
  -- (`Prop` lives in `Type₁`, beside `Type`: D66.)
  def U (n : Nat) : Type₁ := (
    match n {
      Z => Prop,
      S _ => Prop,
    }
  )

  def V (n : Nat) : U(n) := (
    match n {
      Z => ⊤,
      S _ => ⊤,
    }
  )
}

-- the exact number of declarations (a truncated file changes it)
#guard Fixtures.decls.length == 4
