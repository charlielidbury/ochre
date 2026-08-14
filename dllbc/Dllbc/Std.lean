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
def Le (a b : Term) : Term := prog{ %LeFn %a %b }
def LeT (a b : Dllbc.Term) : Dllbc.Term := prog{ %LeFnT %a %b }

/-! ## `eqb, leb : Nat → Nat → Bool` — runtime-usable decision procedures -/

def eqbFn : Term := prog{
  λ (A : Nat). elim A return (λ (Am : Nat). Nat → Bool) {
    Z => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => True, S (B') Rec => False },
    S (A') RecA => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => False, S (B') Rec => RecA B' } } }
def eqbFnT : Dllbc.Term := eqbFn
def eqb (a b : Term) : Term := prog{ %eqbFn %a %b }

def lebFn : Term := prog{
  λ (A : Nat). elim A return (λ (Am : Nat). Nat → Bool) {
    Z => λ (B : Nat). True,
    S (A') RecA => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => False, S (B') Rec => RecA B' } } }
def lebFnT : Dllbc.Term := lebFn
def leb (a b : Term) : Term := prog{ %lebFn %a %b }

/-! ## `len` — the segment vocabulary's length (§14) -/

def lenFn : Term := prog{
  λ (L : List Nat). elim L return (λ (Lm : List Nat). Nat) {
    Nil => Z,
    Cons (H) (T) Rec => S(Rec) } }
def lenFnT : Dllbc.Term := lenFn
def len (l : Term) : Term := prog{ %lenFn %l }
def lenT (l : Dllbc.Term) : Dllbc.Term := prog{ %lenFnT %l }

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
def count (n l : Term) : Term := prog{ %countFn %n %l }
def countT (n l : Dllbc.Term) : Dllbc.Term := prog{ %countFnT %n %l }

/-! ## `Bound : Nat → List Nat → Type` and `Sorted : List Nat → Type` -/

-- `Bound h l` : the head of `l` is ≥ `h` (Nil ↦ ⊤, Cons h' _ ↦ Le h h').
def BoundFn : Term := prog{
  λ (H : Nat). λ (L : List Nat). elim L return (λ (Lm : List Nat). Type) {
    Nil => Unit,
    Cons (H') (T) Rec => Le H H' } }
def BoundFnT : Dllbc.Term := BoundFn
def Bound (h l : Term) : Term := prog{ %BoundFn %h %l }
def BoundT (h l : Dllbc.Term) : Dllbc.Term := prog{ %BoundFnT %h %l }

-- `Sorted l` : Nil ↦ ⊤ ; Cons h t ↦ Bound h t × Sorted t. The `×` is the
-- non-dependent Σ (M33 macro-top): the second component does not mention the
-- first, so the pair has no binder and therefore no component MODE — which is
-- what the hand form's reserved `§_` said and what a named binder could not.
def SortedFn : Term := prog{
  λ (L : List Nat). elim L return (λ (Lm : List Nat). Type) {
    Nil => Unit,
    Cons (H) (T) Rec => Bound H T × Rec } }
def SortedFnT : Dllbc.Term := SortedFn
def Sorted (l : Term) : Term := prog{ %SortedFn %l }
def SortedT (l : Dllbc.Term) : Dllbc.Term := prog{ %SortedFnT %l }

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
def take (n l : Term) : Term := prog{ %takeFn %n %l }
def takeT (n l : Dllbc.Term) : Dllbc.Term := prog{ %takeFnT %n %l }

def dropFn : Term := prog{
  λ (N : Nat). elim N return (λ (Nm : Nat). List Nat → List Nat) {
    Z => λ (L : List Nat). L,
    S (N') RecN => λ (L : List Nat). elim L return (λ (Lm : List Nat). List Nat) {
      Nil => Nil,
      Cons (H) (T) R => RecN T } } }
def dropFnT : Dllbc.Term := dropFn
def drop (n l : Term) : Term := prog{ %dropFn %n %l }
def dropT (n l : Dllbc.Term) : Dllbc.Term := prog{ %dropFnT %n %l }

/-- `add a b` by recursion on `a`. Aliased from the kernel for the same reason as
    `Le`: premise (3) of CARVE decomposes an extent with `add`, so the kernel
    needs it. -/
def addFn : Term := kAddFn
def addFnT : Dllbc.Term := addFn
def add (a b : Term) : Term := prog{ %addFn %a %b }
def addT (a b : Dllbc.Term) : Dllbc.Term := prog{ %addFnT %a %b }

/-- `append a b` by recursion on `a` (`Nil ↦ b`, `Cons h t ↦ Cons h (append t b)`). -/
def appendFn : Term := prog{
  λ (A : List Nat). λ (B : List Nat). elim A return (λ (Lm : List Nat). List Nat) {
    Nil => B,
    Cons (H) (T) R => Cons(H, R) } }
def appendFnT : Dllbc.Term := appendFn
def append (a b : Term) : Term := prog{ %appendFn %a %b }
def appendT (a b : Dllbc.Term) : Dllbc.Term := prog{ %appendFnT %a %b }

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
