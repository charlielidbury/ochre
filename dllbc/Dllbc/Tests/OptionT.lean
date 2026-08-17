import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.ProgMacro
import Dllbc.FnMacro
import Dllbc.Tests.Diff

/-!
# `Option T` — the second parametric type in the fixed basis

`Option` is `List`'s parameter and `Bool`'s shape, and every site it touches was
already occupied by one of those two. It is parametric, so its constructors read
their field types off the expected type's argument (`Nil`/`Cons`); it is NOT
recursive, so its `Some` arm binds the payload and no `ih` (`True`/`False`).
Nothing here is a new kind of rule — this file is the evidence that the kernel's
tables are the whole of what a type in the basis costs.

## What the type is

    Option : Type → Type
    None : Option A
    Some : A → Option A
    optRec : Π (A : Type) (P : Option A → Type)
           → P None → (Π (x : A) → P (Some x)) → Π (o : Option A) → P o

The spine order is `listRec`'s — element type, motive, base arm, step arm,
scrutinee — because the alternative is a second convention to remember.

## What `Option` tests that `List` never did

`List`'s two constructors differ in ARITY *and* in recursiveness at once, so
every site that reads a constructor's fields off the scrutinee's type was
exercised only in the shape "the recursive field has the scrutinee's own type".
`Some`'s single field is at the PARAMETER type, which is the case `Cons`' head
covers and `Cons`' tail hides. The two places where that distinction is real are
`Pure.ctorSig` (`Some` has a one-entry telescope, not a two-entry one ending in
the type former) and the arm contracts (`recArmPis`/`sealRec`), where `Some`'s
arm has no `ih` to type. Both are asserted below.
-/

namespace Dllbc.Tests.OptionT
open Dllbc Dllbc.Pure Dllbc.Surface

/-! ## The pure layer: ι under `nf`, and the tables

    The recursor computes at both constructors, stays stuck on a neutral, and the
    field-type/exhaustiveness tables answer for `Option` the way they answer for
    `List`. -/

-- `optSucc : Option Nat → Option Nat` — the smallest function that is not a
-- projection, written in the `elim` surface (§15b) so that the surface's own
-- `optRec` emission is what is under test and not a hand-built spine.
def OptSucc : Term := prog{
  λ (O : Option Nat). elim O return (λ (Om : Option Nat). Option Nat) {
    None => None,
    Some (X) => Some(S(X)) } }

-- `optOr : Nat → Option Nat → Nat` — a LARGE arm asymmetry: the two arms return
-- the same type by different routes, which is what a `getD` is.
def OptOr : Term := prog{
  λ (D : Nat). λ (O : Option Nat). elim O return (λ (Om : Option Nat). Nat) {
    None => D,
    Some (X) => X } }

-- ι at each constructor.
example : (Pure.nf 1000 prog{ OptSucc (Some(4)) } == prog{ Some(5) }) = true := by native_decide
example : (Pure.nf 1000 prog{ OptSucc None } == prog{ None }) = true := by native_decide
example : (Pure.nf 1000 prog{ OptOr 9 (Some(4)) } == Term.nat 4) = true := by native_decide
example : (Pure.nf 1000 prog{ OptOr 9 None } == Term.nat 9) = true := by native_decide

-- Stuck on a neutral scrutinee: the spine comes back with the scrutinee whnf'd
-- and nothing else done, which is what makes an `Option` σ behave like a `List`
-- one under a symbolic match.
-- (Stated on the SPINE rather than against a hand-written term: readback renames
-- every binder to its level, so a literal comparison would be asserting
-- `readbackName` and not the ι rule.)
example : (match Pure.collectSpineT (Pure.nf 1000 prog{ OptSucc %(Term.sym 3) }) with
  | (.const "optRec", args) => args.length == 5 && args.get? 4 == some (Term.sym 3)
  | _ => false) = true := by native_decide

-- The two tables, directly. `Some`'s telescope has ONE entry at the PARAMETER
-- type — the distinction `Cons` cannot state, since its second field is at the
-- type former itself.
example : ((Pure.ctorSig "Some").bind (fun s => s.fieldTypes prog{ Option Nat })
  == some [("_", prog{ Nat })]) = true := by native_decide
example : ((Pure.ctorSig "None").bind (fun s => s.fieldTypes prog{ Option Nat })
  == some []) = true := by native_decide
-- …and neither inhabits a type it does not belong to.
example : ((Pure.ctorSig "Some").bind (fun s => s.fieldTypes prog{ List Nat })).isNone = true := by
  native_decide
example : (Pure.typeCtors prog{ Option Nat } == some ["None", "Some"]) = true := by native_decide

/-! ## The spec-style equation

    `Id (Option Nat) x y` at equal concretes closes by `Refl` — the conversion
    that backs it is `nf`'s, so this is the ι rule above reached through the
    checker rather than through `native_decide` on `nf`. -/

example : progOk (prog{
  fn OptEq () -> Id (Option Nat) (OptSucc (Some(4))) (Some(5)) { Refl };
  () }) = true := by native_decide

-- The control: unequal concretes do NOT close, so the line above is a claim
-- about `optRec` computing and not about `Refl` being admitted anywhere.
example : progRejects (prog{
  fn OptEq () -> Id (Option Nat) (OptSucc (Some(4))) (Some(4)) { Refl };
  () }) "does not have return type" = true := by native_decide

/-! ## Construction: the field telescope, reached through the checker

    `ctorSig` is asserted directly above; these are the same three facts arriving
    where a program meets them. -/

example : progOk (prog{ fn MkSome () -> Option Nat { Some(5) }; () }) = true := by native_decide
example : progOk (prog{ fn MkNone () -> Option Nat { None }; () }) = true := by native_decide

-- `Some(True)` against `Option Nat`: the payload is checked at the PARAMETER,
-- which is the whole content of `Some`'s one-entry telescope.
example : progRejects (prog{ fn MkBad () -> Option Nat { Some(True) }; () })
  "does not have return type" = true := by native_decide

-- …and the type former is not interchangeable with `List`'s: `Nil` does not
-- inhabit an `Option`, `None` does not inhabit a `List`. Two rejections rather
-- than one, because they fail at different halves of `fieldTypes`.
example : progRejects (prog{ fn MkBad () -> Option Nat { Nil }; () })
  "does not have return type" = true := by native_decide
example : progRejects (prog{ fn MkBad () -> List Nat { None }; () })
  "does not have return type" = true := by native_decide

/-! ## Match: owned, borrowed, and §9 exhaustiveness

    The machine's `match` is driven by `ctorSig`/`typeCtors` and knows no
    constructor by name, so all three of these were supposed to come free from the
    two table rows. That is a claim, and these are it. -/

-- Owned: the scrutinee is consumed, each arm binds its fields.
def unwrapProg : Term := prog{
  fn UnwrapOr (d : Nat, o : Option Nat) -> Nat { match o { None => d, Some(x) => x } };
  () }
example : progOk unwrapProg = true := by native_decide

-- Borrow mode (§3.3): the arm binds a field BORROW, and writing through it
-- updates the owner's payload in place. `Push`'s shape over `Option`.
def bumpProg : Term := prog{
  fn Bump (o : &mut Option Nat) -> Unit {
    match o { None => (), Some(x) => { *x := 7; () } } };
  () }
example : progOk bumpProg = true := by native_decide

-- §9: a match missing `None` is rejected on a SYMBOLIC scrutinee, by the
-- constructor set `typeCtors` reports and nothing else.
example : progRejects (prog{
  fn Half (o : Option Nat) -> Nat { match o { Some(x) => x } };
  () }) "no branch for constructor 'None'" = true := by native_decide

-- The other direction, so the line above is about the SET and not about arity.
example : progRejects (prog{
  fn Half (o : Option Nat) -> Nat { match o { None => 0 } };
  () }) "no branch for constructor 'Some'" = true := by native_decide

-- A branch for a constructor of another type is refused by `fieldTypes`
-- returning `none` at this scrutinee's type — the same rule, read the other way.
example : progRejects (prog{
  fn Wrong (o : Option Nat) -> Nat { match o { None => 0, Some(x) => x, Cons(h, t) => h } };
  () }) "does not belong to the scrutinee's type" = true := by native_decide

/-! ## `Option Nat` in return position, and through a `&mut` -/

-- Both branches return an `Option Nat`, by different constructors. This is the
-- shape that made `Option` worth adding: a function whose result is "a `Nat`, or
-- not" needs no sentinel and no `Bool` beside it.
def findProg : Term := prog{
  fn Pick (b : Bool) -> Option Nat { match b { True => Some(1), False => None } };
  fn Caller () -> Nat {
    let o = Pick(True);
    let r = match o { None => 0, Some(x) => x };
    r };
  () }
example : progOk findProg = true := by native_decide

-- Take-and-rebuild through a `&mut (Option Nat)`: the payload is moved OUT of the
-- borrow, inspected, and a new one written back. `Push`'s `let tail = *v; *v :=
-- Cons(e, tail)` with `Option`'s constructors, which is the test that the borrow
-- machinery reads nothing about `List` in particular.
def rebuildProg : Term := prog{
  fn Step (o : &mut Option Nat) -> Unit {
    let cur = *o;
    match cur { None => { *o := Some(0); () }, Some(x) => { *o := Some(S(x)); () } } };
  () }
example : progOk rebuildProg = true := by native_decide

/-! ## Executing: the concrete run, and the two machines agreeing

    `runExec` runs a body concretely (callees run their bodies); `diffC` is the
    corpus's simulation relation — the concrete final Ω is a σ-instance of some
    accepted symbolic path's. The second is the interesting one: it is the
    statement that `Option`'s ι rule on the executing side and its match rule on
    the checking side describe the same function. -/

open Dllbc.Tests.S9Diff (runExec diffC)

-- Borrow an `Option Nat`, mutate it through the borrow, read the owner back.
def stepBody : Term := prog{
  fn Step (o : &mut Option Nat) -> Unit {
    let cur = *o;
    match cur { None => { *o := Some(0); () }, Some(x) => { *o := Some(S(x)); () } } };
  let a = Some(4);
  let p = &m a;
  Step(p);
  let r = a;
  () }

-- The owner recovers `Some 5`: the borrow was mutated in place and given back.
-- `a` and `p` are ⊥ — the owner was lent and the borrow was consumed by the call.
example : (match runExec stepBody with
  | .ok env => env == [("a", .bot), ("p", .bot), ("r", .ctor "Some" [Val.nat 5])]
  | .error _ => false) = true := by native_decide

-- The other arm, so the run above is ι selecting on the constructor rather than
-- one arm being taken unconditionally.
def stepNoneBody : Term := prog{
  fn Step (o : &mut Option Nat) -> Unit {
    let cur = *o;
    match cur { None => { *o := Some(0); () }, Some(x) => { *o := Some(S(x)); () } } };
  let a = None;
  let p = &m a;
  Step(p);
  let r = a;
  () }

example : (match runExec stepNoneBody with
  | .ok env => env == [("a", .bot), ("p", .bot), ("r", .ctor "Some" [Val.nat 0])]
  | .error _ => false) = true := by native_decide

-- Both bodies check…
example : progOk stepBody = true := by native_decide
example : progOk stepNoneBody = true := by native_decide

-- …and the two machines agree on them: the concrete final Ω is a σ-instance of
-- an accepted symbolic path's. This is the statement that `Option`'s executing ι
-- rule (`applyR`) and its checking match rule (`symBorrowSetup` + `typeCtors`)
-- describe one function and not two.
example : diffC stepBody = true := by native_decide
example : diffC stepNoneBody = true := by native_decide

/-! ## The SEALED recursor, hand-built

    `optRec` has `sealRec`/`recArmPis` cases because every recursor in
    `recLayout` does, and uniformity is the house rule — but no surface form
    emits one. `fn [k]` emits `natRec` and `listRec` only, and `Option` is not
    recursive, so a decreasing argument of that type does not exist. `boolRec` is
    in exactly the same position and its `sealRec` case has no surface producer
    either.

    So the spine is written by hand here, which is the only way to reach the code.
    The motive is a Π — `Π (o : Option Nat) → Π (d : Nat) → Nat`, the default
    arriving AFTER the scrutinee — because that is what makes the residual
    telescope non-empty and spares both arms M33b's unit binder; the shape is
    `fn`'s `listRec` output with the tail and the `ih` removed. -/

def dV : Var := ⟨901, "d"⟩
def xV : Var := ⟨902, "x"⟩

/-- `Π (o : Option Nat) → Π (d : Nat) → Nat`. -/
def unwrapU : Term := .pi "o" prog{ Option Nat } (.pi "d" prog{ Nat } prog{ Nat })

/-- `optRec Nat (λ o. Π (d : Nat) → Nat) (λ d. d) (λ x d. x)`, sealed at
    `unwrapU`. The arms are runtime λs — their binders carry slots — which is
    what makes this a recursor over BODIES rather than a pure spine. -/
def unwrapSeal : Term :=
  .seal 0
    (.app (.app (.app (.app (.const "optRec") prog{ Nat })
      (.lam "o" prog{ Option Nat } (.pi "d" prog{ Nat } prog{ Nat })))
      (Term.lamTel [(dV, prog{ Nat })] (.var dV)))
      (Term.lamTel [(xV, prog{ Nat }), (dV, prog{ Nat })] (.var xV)))
    unwrapU

/-- A caller of the sealed spine, parameterized by the `Option Nat` it passes. -/
def unwrapCaller (o : Term) : Term := prog{
  let F = %unwrapSeal;
  let r = F(%o, 9);
  let z = r;
  () }

-- The seal is ACCEPTED: `sealRec` derived the motive from the ascription, agreed
-- with the written one, and checked each arm at the motive instantiated at its
-- own constructor.
example : progOk (unwrapCaller prog{ Some(4) }) = true := by native_decide
example : progOk (unwrapCaller prog{ None }) = true := by native_decide

-- …and the executing side ι's on the constructor: `Some(4)` takes the payload,
-- `None` takes the default. This is `applyR`'s `optRec` case over runtime arms.
example : (match runExec (unwrapCaller prog{ Some(4) }) with
  | .ok env => env.lookup "z" == some (Val.nat 4)
  | .error _ => false) = true := by native_decide
example : (match runExec (unwrapCaller prog{ None }) with
  | .ok env => env.lookup "z" == some (Val.nat 9)
  | .error _ => false) = true := by native_decide

-- The arms are really CHECKED, not carried: a `Some` arm returning a `Bool`
-- where the motive says `Nat` is rejected at the seal.
def badArmSeal : Term :=
  .seal 0
    (.app (.app (.app (.app (.const "optRec") prog{ Nat })
      (.lam "o" prog{ Option Nat } (.pi "d" prog{ Nat } prog{ Nat })))
      (Term.lamTel [(dV, prog{ Nat })] (.var dV)))
      (Term.lamTel [(xV, prog{ Nat }), (dV, prog{ Nat })] prog{ True }))
    unwrapU

example : progRejects (prog{ let F = %badArmSeal; let z = F(Some(4), 9); () })
  "result (True) does not have return type (Nat)" = true := by native_decide

-- And the motive is compared against the one the ascription derives (§7): a
-- written motive that is not `λ o. R` is refused by name.
def badMotiveSeal : Term :=
  .seal 0
    (.app (.app (.app (.app (.const "optRec") prog{ Nat })
      (.lam "o" prog{ Option Nat } prog{ Nat }))
      (Term.lamTel [(dV, prog{ Nat })] (.var dV)))
      (Term.lamTel [(xV, prog{ Nat }), (dV, prog{ Nat })] (.var xV)))
    unwrapU

example : progRejects (prog{ let F = %badMotiveSeal; let z = F(Some(4), 9); () })
  "the recursor's motive is not the one its ascription derives" = true := by native_decide

end Dllbc.Tests.OptionT
