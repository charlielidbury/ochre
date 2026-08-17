import Dllbc.Value
import Dllbc.Syntax
import Dllbc.Pure

/-!
# `Dllbc.Std` — the quicksort pure library (§11)

The verification vocabulary the north-star quicksort needs, derived *inside*
the calculus as ordinary comptime terms: the order type `Le`, its Boolean
reflections `eqb`/`leb`, the multiset counter `count`, and the predicates
`Bound`/`Sorted`. All are large-elimination recursors — double `natRec` for the
`Nat → Nat → _` shapes, `listRec` for the list-recursive predicates — so they
*compute*: `Le 1 2` whnf's to `⊤`, `Sorted [1,2]` to a product of `⊤`s,
`count 1 [1,2,1]` to `2`.

**Every definition below is written in the SURFACE** (M33 macro-top commit 4).
They were hand-built `Term`s for as long as this file has existed, because the
macro layer sat above the kernel and this module is below it; commit 2 inverted
that, and the library is now written in the language it is a library for. The
migration was gated per definition on an equivalence against the hand form —
conversion on both normal forms, and `alphaEq` where the two spellings can agree
at all. Two of the eleven came out α-IDENTICAL (`le_refl` and its type), which is
what says the respell reproduces the hand term rather than merely something that
computes the same; the other nine differ in exactly one place, the recursor
motive's binder, because the hand form wrote the unwritable reserved `§_` there.

`le_refl : Π n. Le n n` is the first checked lemma (by `natRec`); it goes
through by the §11 recursor-neutral synthesis and λ-vs-Π typing in `hasType`.
`le_trans` is deliberately *not* here — see the milestone report: as a raw
de Bruijn term it was a three-level nested dependent induction, the concrete
motivation for exactly the surface syntax this file is now written in.

## Definition order is dependency order, and it is load-bearing

Each `…FnT` alias sits immediately after its `…Fn`. That is not tidiness: the
surface resolves the friendly names `Le`, `Eqb`, `Bound`, … through
`Surface.aliasMap`, which maps them to `Dllbc.Std.…FnT` — so a definition citing
`Le` needs `LeFnT` to already exist. The file therefore reads in the order the
library actually depends on itself, and a cycle would be a Lean error rather
than a subtlety.
-/

namespace Dllbc.Std
open Dllbc.Pure

/-! ## Lifting Lean data into terms

    The one job the surface has no spelling for: a `prog{ }` is a FIXED term, and
    these are functions of a runtime `Nat`/`List`. So the recursion is Lean's and
    each step is a `prog{ }`.

    **Their leaves are gone** (M33 macro-top commit 7). `zero`, `suc`, `consV` and
    `nilV` were not merely assembly shorthands — they were a SECOND COPY of
    `Term.zero`/`succ`/`nil`/`cons`, which have lived in `Syntax.lean` all along,
    and `ofNat` was a second copy of `Term.nat`'s recursion. One numeral builder
    is better than two; `ofNat` delegates to the one that already existed, exactly
    as `Pure.ofNat` has since M32 R1, and `ofList` writes its step in the
    surface. -/

def ofNat (n : Nat) : Term := Term.nat n
def ofList : List Term → Term
  | [] => prog{ Nil }
  | h :: t => prog{ Cons(%h, %(ofList t)) }

/-! ## `Le : Nat → Nat → Type`  (Z ≤ _ ↦ ⊤ ; S ≤ Z ↦ ⊥ ; S ≤ S ↦ recurse)

    `Le` LIVES in the kernel (`Pure.kLeFn`) and is aliased here. The CARVE rule's
    premise (2) IS a `Le`, and a kernel rule cannot cite a library it does not
    import; two syntactically different `Le`s would never convert, which would
    break the one conversion the residue transition exists to make definitional.
    Single source of truth, asserted in S24Arrays (i.h). -/

def LeFn : Term := kLeFn
def LeFnT : Dllbc.Term := LeFn

/-! ## `eqb, leb : Nat → Nat → Bool` — runtime-usable decision procedures -/

def eqbFn : Term := prog{
  λ (A : Nat). elim A return (λ (Am : Nat). Nat → Bool) {
    Z => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => True, S (B') Rec => False },
    S (A') RecA => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => False, S (B') Rec => RecA B' } } }
def eqbFnT : Dllbc.Term := eqbFn

def lebFn : Term := prog{
  λ (A : Nat). elim A return (λ (Am : Nat). Nat → Bool) {
    Z => λ (B : Nat). True,
    S (A') RecA => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => False, S (B') Rec => RecA B' } } }
def lebFnT : Dllbc.Term := lebFn

/-! ## `len` — the segment vocabulary's length (§14) -/

def lenFn : Term := prog{
  λ (L : List Nat). elim L return (λ (Lm : List Nat). Nat) {
    Nil => Z,
    Cons (H) (T) Rec => S(Rec) } }
def lenFnT : Dllbc.Term := lenFn

/-! ## `count : Nat → List Nat → Nat` — the multiset counter (`listRec` + `boolRec`)

    The `Cons` arm is OPEN in `N`, deliberately: an arm is the body of the
    recursion it belongs to and reaches the outer parameter the recursion is
    about. That was `pvar 4` and had to be counted; under names it says which
    variable it means, and `λ (N : Nat)` binding it is visible one line up. -/

def countFn : Term := prog{
  λ (N : Nat). λ (L : List Nat). elim L return (λ (Lm : List Nat). Nat) {
    Nil => Z,
    Cons (H) (T) Rec => elim (Eqb N H) return (λ (Bm : Bool). Nat) { True => S(Rec), False => Rec } } }
def countFnT : Dllbc.Term := countFn

/-! ## `Bound : Nat → List Nat → Type` and `Sorted : List Nat → Type` -/

-- `Bound h l` : the head of `l` is ≥ `h` (Nil ↦ ⊤, Cons h' _ ↦ Le h h').
def BoundFn : Term := prog{
  λ (H : Nat). λ (L : List Nat). elim L return (λ (Lm : List Nat). Type) {
    Nil => Unit,
    Cons (H') (T) Rec => Le H H' } }
def BoundFnT : Dllbc.Term := BoundFn

-- `Sorted l` : Nil ↦ ⊤ ; Cons h t ↦ Bound h t × Sorted t. The `×` is the
-- non-dependent Σ (M33 macro-top): the second component does not mention the
-- first, so the pair has no binder and therefore no component MODE — which is
-- what the hand form's reserved `§_` said and what a named binder could not.
def SortedFn : Term := prog{
  λ (L : List Nat). elim L return (λ (Lm : List Nat). Type) {
    Nil => Unit,
    Cons (H) (T) Rec => Bound H T × Rec } }
def SortedFnT : Dllbc.Term := SortedFn

/-! ## `take`, `drop` — the prefix and suffix a segment-scoped spec talks about

    By `natRec` on the count, giving a `List Nat → List Nat` (a `listRec` inside
    the successor arm): the double-recursion shape. -/

def takeFn : Term := prog{
  λ (N : Nat). elim N return (λ (Nm : Nat). List Nat → List Nat) {
    Z => λ (L : List Nat). Nil,
    S (N') RecN => λ (L : List Nat). elim L return (λ (Lm : List Nat). List Nat) {
      Nil => Nil,
      Cons (H) (T) R => Cons(H, RecN T) } } }
def takeFnT : Dllbc.Term := takeFn

def dropFn : Term := prog{
  λ (N : Nat). elim N return (λ (Nm : Nat). List Nat → List Nat) {
    Z => λ (L : List Nat). L,
    S (N') RecN => λ (L : List Nat). elim L return (λ (Lm : List Nat). List Nat) {
      Nil => Nil,
      Cons (H) (T) R => RecN T } } }
def dropFnT : Dllbc.Term := dropFn

/-- `add a b` by recursion on `a`. Aliased from the kernel for the same reason as
    `Le`: premise (3) of CARVE decomposes an extent with `add`, so the kernel
    needs it. -/
def addFn : Term := kAddFn
def addFnT : Dllbc.Term := addFn

/-- `append a b` by recursion on `a` (`Nil ↦ b`, `Cons h t ↦ Cons h (append t b)`). -/
def appendFn : Term := prog{
  λ (A : List Nat). λ (B : List Nat). elim A return (λ (Lm : List Nat). List Nat) {
    Nil => B,
    Cons (H) (T) R => Cons(H, R) } }
def appendFnT : Dllbc.Term := appendFn

/-! ## `mul`, `mod`, `div` — the slot arithmetic (the hashmap flagship's `Mod key cap`)

    Ported from the `hm-probe-mod` branch, whose two findings are what the shapes
    below are FOR, and which are worth restating here because a later editor's first
    instinct will be to "simplify" them back.

    **`mod` and `div` must mention their recursive result exactly ONCE.** The
    textbook step — `let r = Mod a' b; if S r = b then Z else S r` — tests the
    recursive result and then also returns it, and the pure normalizer substitutes
    WITHOUT SHARING, so each second occurrence re-derives the whole recursion beneath
    it: the cost doubles per unit of dividend. Measured on that branch: `Mod 20 32`
    took 87 s and `Mod 32 32` would have taken days, and three different spellings of
    that same shape measured identically, which is what says the cost belongs to the
    normalizer rather than to the spelling. It presents as a build that never
    finishes, not as an error. `language.md`'s closing performance rule is this
    paragraph's general form.

    The fix is the accumulator: carry the would-be-duplicated value as an ARGUMENT
    and ask the question of the argument. The state is `(R, C)` — `R` is the residue
    so far, `C` is how many more increments fit before wrapping — with `R + C = B`
    the invariant. `NextR`/`NextC`/`NextQ` are the three non-recursive answers to
    "what does this component do at one increment", each an `elim` on `C`, so
    `ModC`'s step mentions `Rec` once and the whole thing is linear: `Mod 1056 32` in
    73 ms.

    At `B = Z` the wrapper answers `Z` rather than the dividend (Lean's `%` answers
    the dividend). Nothing divides by zero — every lemma downstream is stated over a
    `Le (S Z) n` hypothesis or an `S b` pattern — so the choice is arbitrary and this
    one keeps the `Z` arm from mentioning `A`. -/

/-- `mul a b` by recursion on `a`. `Rec` occurs once, as everything in this block must. -/
def mulFn : Term := prog{
  λ (A : Nat). λ (B : Nat). elim A return (λ (Am : Nat). Nat) {
    Z => Z,
    S (A') Rec => Add B Rec } }
def mulFnT : Dllbc.Term := mulFn

/-- One increment's effect on the residue: it grows, except at the wrap, where it resets. -/
def nextRFn : Term := prog{
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C') Rc => S(R) } }
def nextRFnT : Dllbc.Term := nextRFn

/-- One increment's effect on the room left: it shrinks, except at the wrap, where it
    refills to `B`. -/
def nextCFn : Term := prog{
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C') Rc => C' } }
def nextCFnT : Dllbc.Term := nextCFn

/-- One increment's effect on the quotient: it ticks exactly when the residue wraps. -/
def nextQFn : Term := prog{
  λ (Q : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => S(Q), S (C') Rc => Q } }
def nextQFnT : Dllbc.Term := nextQFn

/-- `ModC a b r c` — `a` increments of the `(r, c)` state, answering the residue. -/
def modCFn : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }
def modCFnT : Dllbc.Term := modCFn

/-- `Mod a b` — start the state at `(Z, b-1)` and run `a` increments. -/
def modFn : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B') Rb => ModC A B' Z B' } }
def modFnT : Dllbc.Term := modFn

/-- `DivC` rides the same state with a quotient that ticks exactly when `C` wraps. -/
def divCFn : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat).
        Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Π (Q : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat). Q,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat).
        Rec B (NextR R C) (NextC B C) (NextQ Q C) } }
def divCFnT : Dllbc.Term := divCFn

/-- `Div a b`, by the same walk as `Mod` with the quotient carried alongside. -/
def divFn : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B') Rb => DivC A B' Z B' Z } }
def divFnT : Dllbc.Term := divFn

/-! ## First lemma: `le_refl : Π n. Le n n`, by `natRec`

    The base is `⋆ : Le Z Z = ⊤`; the step returns the IH unchanged, because
    `Le (S m) (S m)` and `Le m m` are definitionally equal.

    **These two are the respell's own control.** They are the only definitions in
    this file whose hand form named every binder it bound — no reserved `§_`
    motive anywhere — and they are the two that come out `Term.alphaEq`-IDENTICAL
    to it, mode markers included. The other nine differ in exactly the position
    the hand form could write and the surface cannot. -/

def le_refl : Term := prog{
  λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
    Z => unit,
    S (M) Rec => Rec } }
def le_reflT : Dllbc.Term := le_refl
def le_refl_ty : Term := prog{ Π (N : Nat) → Le N N }

/-! ## Normalizing a term, for the generalize-elim macro

    §18: exposes a computed subterm (e.g. an `eqb`-spine hidden in a `count`
    unfolding) so `abstractOccurrences` can find it in a natural goal. Emitted by
    the macro BY NAME, which is why it lives here — the macro is below this
    module and resolves the name at its use site. -/
def nfTerm (t : Dllbc.Term) : Dllbc.Term := Dllbc.Pure.nf 1000 t

end Dllbc.Std
