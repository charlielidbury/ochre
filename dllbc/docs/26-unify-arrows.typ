#set document(title: "One Interpreter")
#set text(font: "New Computer Modern", size: 9.5pt)
#set page(margin: (x: 1.6cm, y: 1.8cm), numbering: "1")
#set par(justify: true)
#set heading(numbering: "1.")
#show raw: set text(size: 8pt)
#show raw.where(block: true): it => block(
  breakable: false,
  inset: (x: 0.7em, y: 0.55em),
  fill: luma(245),
  radius: 3pt,
  width: 100%,
  it,
)
#let row(prose, code, breakable: false) = block(breakable: breakable, width: 100%, grid(
  columns: (0.85fr, 1.15fr),
  column-gutter: 1.4em,
  prose, code,
))

#align(center, text(size: 16pt, weight: "bold")[One Interpreter])
#align(center)[Running programs, and proving things about them, by the same steps]
#v(0.6em)

DLLBC has one interpreter. It runs a program by stepping it and updating a store; it checks a program by stepping it on inputs it knows nothing about. This document shows the interpreter on small programs, printing the store $Omega$ after each step, and ends by proving $a + 0 = a$ about an addition that works by mutating memory. Nothing is used before it has been shown.

_Conventions._ Numerals abbreviate constructor chains: `0` is `Z`, `2` is `S(S(Z))`; patterns are written with the constructors. Statements end in `;`. A `//` comment after a step lists only the mappings of $Omega$ that changed; a parenthesised note names an event that is not a statement. A call is shown at the call site, before and after, and then _within_ the call: the callee's body with the store as the callee sees it. A `λ`'s body, where it is defined, is annotated with the store of its _check_ — its parameters symbolic (§4) — since that is when the body is stepped.

= Values and the store
#row[
  A value is a constructor tree: `2`, `S(σ)`, `()`. The store $Omega$ maps names to values. `let` binds a name; reading a name by value _moves_ its value out and leaves `⊥` behind.
][
  ```rust
  let a = 2;
  // a ↦ 2
  let b = a;
  // a ↦ ⊥, b ↦ 2
  ```
]

= Borrows
#row[
  `&m a` lends `a`'s value instead of moving it. `a` is left holding a _loan_ `ℓ`; the new name holds a _borrow_ of `ℓ` carrying the value. `*b` reads or writes the value inside the borrow. When `b` is no longer used the borrow _ends_ and the value returns to `a`. While the loan is out, `a` cannot be read.
][
  ```rust
  let a = 1;
  // a ↦ 1
  let b = &m a;
  // a ↦ loan ℓ, b ↦ borrow ℓ 1
  *b := 2;
  // b ↦ borrow ℓ 2
  // (b ends)
  // a ↦ 2
  ```
]

= Matching
#row[
  `match` selects the arm whose constructor is at the scrutinee. On a value it binds the constructor's fields. On a borrow it does not take the fields out: it lends them again, so each pattern name is a borrow _into_ the payload, and a write through it is a write into the outer borrow, and through that into `a`.
][
  ```rust
  let a = 2;
  let b = &m a;
  // a ↦ loan ℓ, b ↦ borrow ℓ 2
  match b {
      Z => (),
      S(pb) => {
          // b ↦ borrow ℓ S(loan ℓ'), pb ↦ borrow ℓ' 1
          *pb := 0;
          // pb ↦ borrow ℓ' 0
          // (pb ends)
          // b ↦ borrow ℓ 1
      },
  };
  // (b ends)
  // a ↦ 1
  ```
]

= Functions
#row[
  A function is a `λ` carrying its full signature — every binder's type and its codomain — and its type `Π(x₁: A₁, …, xₙ: Aₙ) -> R` is read off that signature before its body is examined. `λ` and `Π` take a telescope, not one binder at a time: an application supplies every argument at once, and there is no partial application. A `λ` captures no runtime value from its surroundings; everything it uses arrives as an argument.

  Evaluating a `λ` — reaching its `let` — _checks_ it. Its body is run once with each parameter bound to a _symbolic_ value `σ`, standing for any value of the parameter's type; a borrow parameter is a borrow of a symbol. The body's value is compared against the codomain. What the body does to symbols is what it does to every input. The `λ` itself is a value, and `let` stores it as written.

  A call binds the parameters in a new _frame_, and the callee sees only its frame. On return the frame pops: every name in it is dropped, and every borrow in it ends, returning its value to the caller's store. So a call's only effect on the caller is what it did through its borrows.
][
  ```rust
  let Zero = λ(x: &mut Nat) -> Unit {
      // x ↦ borrow ℓ σ;
      *x := 0;
      // x ↦ borrow ℓ 0
  };
  // Zero ↦ λ(x: &mut Nat) -> Unit { … }
  ```
  ```rust
  let a = 1;
  // a ↦ 1
  Zero(&m a);
  // a ↦ 0

  // within Zero(&m a)
  // x ↦ borrow ℓ 1
  *x := 0;
  // x ↦ borrow ℓ 0
  // (frame pops; the borrow ends)
  ```
]

= Recursion
#row(breakable: true)[
  `fix F. e` binds `F` inside `e` to `e` itself, and a `fix` over a `λ` is a value like the `λ`. Three rules govern it.

  _Typing._ `fix F. e` has the type of `e` — its signature — and inside `e` so does `F`.

  _Reduction._ `fix F. e` applied to arguments unfolds to `e` with `F` replaced by `fix F. e` — but only when the structural argument (below) is a constructor; for a borrow, when the borrowed cell holds one. Otherwise the application does not step. The replacement is realised as a binding in the new frame: `F ↦ fix F. e`, beside the parameters. It is not capture, since the `fix` term is closed.

  _Guard._ Some parameter of `e` is _structural_: at that position, every call of `F` inside `e` passes a name bound by a pattern that matched the parameter, or a sub-pattern of it. No annotation marks the position; the condition is checked.

  Addition by mutation: walk to the bottom of `x` and overwrite the `Z` there with `y`. The structural parameter is `x`, and `px` is bound by a pattern that matched it.

  Checking `AddM` meets two forms a symbol stops. A `match` on a symbol _splits_: it is checked arm by arm, with `σ` replaced everywhere — in the store and in whatever is being checked against — by that arm's constructor over fresh symbols, so names bound by the pattern are symbols. An application of a `fix` whose structural argument is a symbol _sticks_: by the reduction rule it does not unfold. What it would have produced is unknown but determinate. A call can observe only its arguments and the contents of the cells it borrowed, and can change only those cells — that is what ownership buys — so each of its outputs is a value in its own right, a _neutral_ named by the call and the output. The return is written `F(…)`; the new contents of the cell behind a borrowed parameter `x` are written `F(…).x`. In the name, a borrowed argument stands for what its cell held on entry, since that is all the call could see. Read `AddM(σ', σ₂).x` as "what `AddM` leaves in `x`'s cell when it held `σ'` and `y` was `σ₂`". It sits in a cell, is returned, is compared, like any value; and if `σ'` is later refined to a constructor, it reduces by running the call.

  The two rules are what the guard buys. In the `S` arm `px` holds a fresh symbol, and the self-call — the same `fix` term, looked up in the frame — sticks on it. A self-call in checking never unfolds, not by a rule about `F`, but because the guard puts a pattern-bound name at the structural position and a pattern-bound name is a symbol. Were the `fix` to split instead, it would unfold into a `match` on a fresh symbol, whose `S` arm would call it again, without end.

  One plus one, last. The outer call takes the `S` arm and lends the payload to a recursive call; that call takes the `Z` arm and writes. Each unfolds because its cell holds a constructor.
][
  ```rust
  let AddM = fix AddM.
      // AddM ↦ fix AddM. λ…
      λ(x: &mut Nat, y: Nat) -> Unit {
          // x ↦ borrow ℓ σ, y ↦ σ₂
          match x {
              Z => {
                  // x ↦ borrow ℓ 0
                  *x := y;
                  // x ↦ borrow ℓ σ₂
              },
              S(px) => {
                  // x ↦ borrow ℓ S(loan ℓ'),
                  // px ↦ borrow ℓ' σ'
                  AddM(px, y);
                  // (sticks: σ' is no constructor)
                  // px ↦ borrow ℓ' AddM(σ', σ₂).x
                  // (px ends)
                  // x ↦ borrow ℓ S(AddM(σ', σ₂).x)
              },
          }
      };
  // AddM ↦ fix AddM. λ(x: &mut Nat, y: Nat) -> Unit { … }
  ```
  ```rust
  let a = 1;
  // a ↦ 1
  AddM(&m a, 1);
  // a ↦ 2

  // within AddM(&m a, 1) — the S arm
  // AddM ↦ fix AddM. λ…, x ↦ borrow ℓ 1, y ↦ 1
  match x {
      Z => { *x := y; },
      S(px) => {
          // x ↦ borrow ℓ S(loan ℓ'), px ↦ borrow ℓ' 0
          AddM(px, y);
          // px ↦ borrow ℓ' 1
          // (px ends)
          // x ↦ borrow ℓ 2
      },
  }

  // within AddM(px, y) — the Z arm
  // AddM ↦ fix AddM. λ…, x ↦ borrow ℓ' 0, y ↦ 1
  match x {
      Z => {
          *x := y;
          // x ↦ borrow ℓ' 1
      },
      S(px) => { AddM(px, y); },
  }
  ```
]

= Addition on values
#row[
  `Add` takes its first argument by value, lends it to `AddM` for the duration of one call, and returns it. Checking it, the call to `AddM` sticks at once — the cell holds a symbol — so `x` comes back holding `AddM(σ, σ₂).x`, and that is the value.

  At a concrete call site nothing changes: the frame pops and the caller's store is as it was. `Add`'s whole effect is its return value.
][
  ```rust
  let Add = λ(x: Nat, y: Nat) -> Nat {
      // x ↦ σ, y ↦ σ₂
      AddM(&m x, y);
      // (sticks: σ is no constructor)
      // x ↦ AddM(σ, σ₂).x
      x
      // value AddM(σ, σ₂).x
  };
  // Add ↦ λ(x: Nat, y: Nat) -> Nat { … }
  ```
  ```rust
  Add(1, 1);
  // (nothing changes)   value 2

  // within Add(1, 1)
  // x ↦ 1, y ↦ 1
  AddM(&m x, y);
  // x ↦ 2                (§5)
  x
  // value 2; (frame pops)
  ```
]

= Equality
#row[
  `Id(A, a, b)` is a type. `Refl` inhabits it when `a` and `b`, each run from a copy of $Omega$ in which reading a name copies rather than moves, produce the same value _and_ leave the same store. An expression with effects is equal to another only if the effects are equal too. Any two inhabitants of one `Id` type are themselves equal.

  One further rule, and it is the one that makes proofs short. *A variable of type `Id(A, a, b)` in scope makes `a` and `b` interchangeable.* When the two sides of a goal are being compared, either may be replaced by the other. This is equality reflection restricted to hypotheses: extensional type theory reflects every _provable_ equality and is undecidable for it; reflecting only the `Id`-typed _variables_ in scope is a lookup.
][
  ```rust
  Id(Unit, (*c := 1), (*c := 1))
  // Refl: both (); both leave c ↦ borrow ℓ 1

  Id(Unit, (*c := 1), (*c := 0))
  // no: both (); the stores differ

  Id(Nat, Add(1, 0), 1)
  // Refl: the left runs to 1 and its frame
  // pops (§6); the right is 1; Ω untouched
  ```
]

= The theorem
#row(breakable: true)[
  The structural parameter is `n`, and `AddZero(n')` passes a name bound by a pattern that matched it, so the guard holds.

  Checking the `fix` is §5 again: run the body with `n ↦ σ` and `AddZero ↦ fix AddZero. λ…` in the frame, against the codomain. The `match` splits. In the `S` arm, `n' ↦ σ'`, and the self-call sticks; its value is `AddZero(σ')`, and its type is the signature's codomain at `σ'` — so `ih : Id(Nat, Add(σ', 0), σ')`, the induction hypothesis, by nothing more than the type of an application. It is used by the reflection rule, not by name.

  *The `Z` arm.* `σ := 0`. `Refl` must have type `Id(Nat, Add(0, 0), 0)`. Within `Add(0, 0)`, `AddM` takes its `Z` arm and writes `0` over `0`; the value is `0` and the store is untouched. `Refl`.

  *The `S` arm.* `Refl` must have type `Id(Nat, Add(S(σ'), 0), S(σ'))`. The left side is run on the right: `AddM` takes its `S` arm, lends the payload `σ'`, and the recursive call sticks. The value is `S(AddM(σ', 0).x)`.

  Now the hypothesis. Within `Add(σ', 0)` the very first `AddM` sticks — its cell holds `σ'` — so the value is `AddM(σ', 0).x`, and `ih : Id(Nat, AddM(σ', 0).x, σ')`. By reflection `AddM(σ', 0).x` and `σ'` are interchangeable, so the goal is `Id(Nat, S(σ'), S(σ'))`. `Refl`.

  `AddM(σ', 0).x` is the same value in both runs because it names the same output of the same call on the same contents. A call that could not step remembers what it was given; that is all the proof needed.
][
  ```rust
  let AddZero = fix AddZero.
      // AddZero ↦ fix AddZero. λ…
      λ(n: Nat) -> Id(Nat, Add(n, 0), n) {
          // n ↦ σ;  goal Id(Nat, Add(σ, 0), σ)
          match n {
              // n ↦ 0;  goal Id(Nat, Add(0, 0), 0)
              Z => Refl,
              S(n') => {
                  // n ↦ S(σ'), n' ↦ σ'
                  // goal Id(Nat, Add(S(σ'), 0), S(σ'))
                  let ih = AddZero(n');
                  // (sticks)
                  // ih ↦ AddZero(σ')
                  //    : Id(Nat, Add(σ', 0), σ')
                  Refl
              },
          }
      };
  // AddZero ↦ fix AddZero. λ(n: Nat) -> Id(…) { … }
  ```
  ```rust
  // S arm: run the left side, Add(S(σ'), 0)

  // within Add(S(σ'), 0)
  // x ↦ S(σ'), y ↦ 0
  AddM(&m x, y);
  // x ↦ S(AddM(σ', 0).x)
  x
  // value S(AddM(σ', 0).x); (frame pops)

  // within AddM(&m x, 0) — the S arm
  // AddM ↦ fix AddM. λ…, x ↦ borrow ℓ S(σ'), y ↦ 0
  match x {
      Z => { *x := y; },
      S(px) => {
          // x ↦ borrow ℓ S(loan ℓ'), px ↦ borrow ℓ' σ'
          AddM(px, y);
          // (sticks)
          // px ↦ borrow ℓ' AddM(σ', 0).x
          // (px ends)
          // x ↦ borrow ℓ S(AddM(σ', 0).x)
      },
  }
  ```
  ```rust
  // ih: run its left side, Add(σ', 0)

  // within Add(σ', 0)
  // x ↦ σ', y ↦ 0
  AddM(&m x, y);
  // (sticks)
  // x ↦ AddM(σ', 0).x
  x
  // value AddM(σ', 0).x; (frame pops)
  // so  ih : Id(Nat, AddM(σ', 0).x, σ')
  ```
]

= The alternative: recursors
#row[
  Instead of `fix` and a guard, a kernel may provide one _recursor_ per type — a constant whose arms are closed functions, terminating by construction. For `Nat`, `natRec` on the right; the theorem becomes an application of it, with the motive `P` spelled out and the hypothesis a binder of the `S` arm rather than a self-call.

  This is Lean's kernel, and for the theorem it is as good as `fix`. It stops fitting at `AddM`, for two reasons that are the same reason. A recursor's arms are closed `λ`s and a `λ` captures nothing (§4): so an arm cannot see the cell `x` it must write, nor the argument `y` it must write into it, and both have to be threaded through the motive as parameters — `P = λ(_: &mut Nat) -> Type { Π(y: Nat) -> Unit }`, every arm taking `y`. And the scrutinee is a borrow, so a second recursor is needed whose arms receive the cell and the payload borrow rather than fields — `natRecM`, right — with `rec` the recursive result, computed before the arm runs whether the arm uses it or not.

  One recursor per type former, doubled for borrows, with the arms' free variables routed through the motive: that is the price of arms being closed terms, and `match` on a borrow (§3) is an operation on $Omega$ that no constant can express in any case. `fix` and `match` are in the kernel regardless; the recursor is what can be omitted.
][
  ```rust
  natRec : Π(P: Π(n: Nat) -> Type,
             z: P(0),
             s: Π(n': Nat, ih: P(n')) -> P(S(n')),
             n: Nat) -> P(n)
  natRec(P, z, s, 0)      ⟶  z
  natRec(P, z, s, S(n'))  ⟶  s(n', natRec(P, z, s, n'))
  ```
  ```rust
  let AddZero = λ(n: Nat) -> Id(Nat, Add(n, 0), n) {
      natRec(
          λ(m: Nat) -> Type { Id(Nat, Add(m, 0), m) },
          Refl,
          λ(n': Nat, ih: Id(Nat, Add(n', 0), n'))
              -> Id(Nat, Add(S(n'), 0), S(n')) { Refl },
          n,
      )
  };
  ```
  ```rust
  natRecM : Π(P: Π(x: &mut Nat) -> Type,
              z: Π(x: &mut Nat) -> P(x),
              s: Π(x: &mut Nat, px: &mut Nat, rec: P(px))
                   -> P(x),
              x: &mut Nat) -> P(x)
  ```
]

= What intensional kernels do here

Lean, Agda and Coq each reject the `S` arm's `Refl`. With `add` recursing on its first argument, the goal `add (S n') 0 = S n'` unfolds to `S (add n' 0) = S n'`, and `add n' 0` is a stuck neutral; the errors say so (Lean: _`add (n + 1) 0` is not definitionally equal to `n + 1`_; Agda: _`add n zero != n`_; Coq: _unable to unify `S n` with `S (add n 0)`_). The smallest proof in each is the congruence of `S` over the hypothesis — `congrArg Nat.succ ih`, `cong suc (add-zero n)`, `f_equal S IHn` — and a rewrite with `ih` fails until the goal is unfolded by hand, because rewriting matches syntax and `add n' 0` is not written anywhere in `add (S n') 0`.

The `Refl` in §8 is that congruence and that unfolding together. Reflection compares the sides after the interpreter has run them, so `AddM(σ', 0).x` is already present on both, and the hypothesis matches it without anyone naming the step.

#v(0.5em)
_Ingredients:_ values and $Omega$; moves; borrows and loans; `match`, which lends on a borrow and splits on a symbol; `λ` with a signature and saturated application, checked on symbols when defined; frames; `fix` with a structural guard, stepping only at a constructor; the outputs of a stuck `fix` as values; `Id` as sameness of value and store, with reflection of hypotheses.
