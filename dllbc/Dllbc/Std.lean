import Dllbc.Value
import Dllbc.Syntax
import Dllbc.Pure

/-!
# `Dllbc.Std` — the surface vocabulary

The eleven names a DLLBC program may write without defining them: the order type
`Le`, its Boolean reflections `Eqb`/`Leb`, the arithmetic `Add`, the list
functions `Len`/`Count`/`Take`/`Drop`/`Append`, and the predicates
`Bound`/`Sorted`. They are derived *inside* the calculus as ordinary comptime
terms — large-elimination recursors, double `natRec` for the `Nat → Nat → _`
shapes and `listRec` for the list-recursive ones — so they *compute*: `Le 1 2`
whnf's to `⊤`, `Sorted [1,2]` to a product of `⊤`s, `Count 1 [1,2,1]` to `2`.

## Each name here IS its surface spelling, and that is the whole mechanism

`Surface.resolveName` ends in a fallthrough: a bare identifier that is not a
binder, a constructor or a kernel constant is **the Lean identifier of that
name**, which must denote a `Dllbc.Term` in scope. A file that writes
`open Dllbc.Std` therefore gets `Le`, `Add`, `Count`, … in its `ty{ }` blocks for
free, resolving to the constants below.

That fallthrough is the only mechanism there is. Until this commit series there
was a second one — `Surface.aliasMap`, a ten-entry table in `Uni.lean` mapping
`Le ↦ Dllbc.Std.LeFnT` and so on — and it existed for exactly one reason: the
constants were spelled `LeFnT`, `addFnT`, `countFnT`, and a table was needed to
bridge the name to the spelling. Spelling them `Le`, `Add`, `Count` retires the
table, because there is no longer a gap for it to bridge. The `…Fn`/`…FnT` pairs
collapsed with it: `Term` in this file *is* `Dllbc.Term`, so the two were the
same definition written twice.

## Why the header no longer says "the quicksort pure library"

It said that because that is where the file came from, and it stopped being true
some time ago. `Le` and `Add` are **aliased from the kernel** (`Pure.kLeFn`,
`Pure.kAddFn`) because premises (2) and (3) of the CARVE rule cite them, and a
kernel rule cannot import a library that sits above it — two syntactically
different `Le`s would never convert, which would break the one conversion the
residue transition exists to make definitional. `Len`, `Count`, `Eqb` and `Leb`
are the general vocabulary that `StdChain`'s lemma types are written in and that
most of the test suite depends on. Nothing here is about quicksort.

## Why it is not merged into `StdChain.lean`, and not in the test suite

Both were asked. Neither survives the import graph.

Nine modules import `Dllbc.Std` and **not** `Dllbc.StdChain` — `Tests/HashMap`,
`Tests/Functions`, `Tests/Boundaries`, `Tests/KernelFloor`, `Tests/OpaqueFill`,
`Tests/Universe`, `Tests/EagerRec`, `Tests/AuditExemption`,
`Tests/ProbeModuleStates`. They want the vocabulary and not the 1900-line lemma
chain, and merging would hand them the chain anyway. The dependency runs the
other way round: `StdChain` is *built out of* these names, which is why it
imports this file and not the reverse.

The test suite is refused for a harder reason: `Uni.lean` — the macro layer —
emits `Dllbc.Std.nfTerm` **by name** from the `elim … generalizing` sugar
(`Uni.lean:2210`), resolved at the use site. A module the macro layer names
cannot live in the tests, and it has to sit below every consumer of that sugar.

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

## Definition order is dependency order, and it still is

`Count` cites `Eqb`, `Sorted` cites `Bound`, `Bound` cites `Le` — and each of
those citations is now an ordinary Lean identifier resolving inside this
namespace, so a definition citing `Le` needs `Le` to already exist. The file
reads in the order the library depends on itself and a cycle is a Lean error,
exactly as before; what changed is that the reason is Lean's scoping rather than
a table in another module.
-/

namespace Dllbc.Std
open Dllbc.Pure

/-! ## Lifting Lean data into terms

    The one job the surface has no spelling for: a `ty{ }` is a FIXED term, and
    these are functions of a runtime `Nat`/`List`. So the recursion is Lean's and
    each step is a `ty{ }`.

    **Their leaves are gone** (M33 macro-top commit 7). `zero`, `suc`, `consV` and
    `nilV` were not merely assembly shorthands — they were a SECOND COPY of
    `Term.zero`/`succ`/`nil`/`cons`, which have lived in `Syntax.lean` all along,
    and `ofNat` was a second copy of `Term.nat`'s recursion. One numeral builder
    is better than two; `ofNat` delegates to the one that already existed, exactly
    as `Pure.ofNat` has since M32 R1, and `ofList` writes its step in the
    surface. -/

def ofNat (n : Nat) : Term := Term.nat n
def ofList : List Term → Term
  | [] => ty{ Nil }
  | h :: t => ty{ Cons(%h, %(ofList t)) }

/-! ## `Le`, `Eqb`, `Bound`, … each carry a `…FnT` twin for ONE commit

    `Surface.aliasMap` — the ten-entry table in `Uni.lean` this series retires —
    still maps the surface names to `Dllbc.Std.…FnT`, and it is consulted BEFORE
    the Lean-identifier fallthrough. So while it lives, a `ty{ }` in this very
    file citing `Le` reaches `LeFnT` and not `Le`, and `Bound`, `Count` and
    `Sorted` all cite their predecessors that way. The twins keep the tree green
    until `Uni.lean` (owned by another lane this session) can be touched; they are
    deleted in the same commit as the table, and the interleaving goes with
    them. -/

/-! ## `Le : Nat → Nat → Type`  (Z ≤ _ ↦ ⊤ ; S ≤ Z ↦ ⊥ ; S ≤ S ↦ recurse)

    `Le` LIVES in the kernel (`Pure.kLeFn`) and is aliased here. The CARVE rule's
    premise (2) IS a `Le`, and a kernel rule cannot cite a library it does not
    import; two syntactically different `Le`s would never convert, which would
    break the one conversion the residue transition exists to make definitional.
    Single source of truth, asserted in S24Arrays (i.h). -/

def Le : Dllbc.Term := kLeFn
abbrev LeFnT : Dllbc.Term := Le

/-! ## `Eqb`, `Leb : Nat → Nat → Bool` — runtime-usable decision procedures -/

def Eqb : Dllbc.Term := ty{
  λ (A : Nat). elim A return (λ (Am : Nat). Nat → Bool) {
    Z => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => True, S (B') Rec => False },
    S (A') RecA => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => False, S (B') Rec => RecA B' } } }
abbrev eqbFnT : Dllbc.Term := Eqb

def Leb : Dllbc.Term := ty{
  λ (A : Nat). elim A return (λ (Am : Nat). Nat → Bool) {
    Z => λ (B : Nat). True,
    S (A') RecA => λ (B : Nat). elim B return (λ (Bm : Nat). Bool) { Z => False, S (B') Rec => RecA B' } } }
abbrev lebFnT : Dllbc.Term := Leb

/-! ## `Len` — the segment vocabulary's length (§14) -/

def Len : Dllbc.Term := ty{
  λ (L : List Nat). elim L return (λ (Lm : List Nat). Nat) {
    Nil => Z,
    Cons (H) (T) Rec => S(Rec) } }
abbrev lenFnT : Dllbc.Term := Len

/-! ## `Count : Nat → List Nat → Nat` — the multiset counter (`listRec` + `boolRec`)

    The `Cons` arm is OPEN in `N`, deliberately: an arm is the body of the
    recursion it belongs to and reaches the outer parameter the recursion is
    about. That was `pvar 4` and had to be counted; under names it says which
    variable it means, and `λ (N : Nat)` binding it is visible one line up. -/

def Count : Dllbc.Term := ty{
  λ (N : Nat). λ (L : List Nat). elim L return (λ (Lm : List Nat). Nat) {
    Nil => Z,
    Cons (H) (T) Rec => elim (Eqb N H) return (λ (Bm : Bool). Nat) { True => S(Rec), False => Rec } } }
abbrev countFnT : Dllbc.Term := Count

/-! ## `Bound : Nat → List Nat → Type` and `Sorted : List Nat → Type` -/

-- `Bound h l` : the head of `l` is ≥ `h` (Nil ↦ ⊤, Cons h' _ ↦ Le h h').
def Bound : Dllbc.Term := ty{
  λ (H : Nat). λ (L : List Nat). elim L return (λ (Lm : List Nat). Type) {
    Nil => Unit,
    Cons (H') (T) Rec => Le H H' } }
abbrev BoundFnT : Dllbc.Term := Bound

-- `Sorted l` : Nil ↦ ⊤ ; Cons h t ↦ Bound h t × Sorted t. The `×` is the
-- non-dependent Σ (M33 macro-top): the second component does not mention the
-- first, so the pair has no binder and therefore no component MODE — which is
-- what the hand form's reserved `§_` said and what a named binder could not.
def Sorted : Dllbc.Term := ty{
  λ (L : List Nat). elim L return (λ (Lm : List Nat). Type) {
    Nil => Unit,
    Cons (H) (T) Rec => Bound H T × Rec } }
abbrev SortedFnT : Dllbc.Term := Sorted

/-! ## `Take`, `Drop` — the prefix and suffix a segment-scoped spec talks about

    By `natRec` on the count, giving a `List Nat → List Nat` (a `listRec` inside
    the successor arm): the double-recursion shape. -/

def Take : Dllbc.Term := ty{
  λ (N : Nat). elim N return (λ (Nm : Nat). List Nat → List Nat) {
    Z => λ (L : List Nat). Nil,
    S (N') RecN => λ (L : List Nat). elim L return (λ (Lm : List Nat). List Nat) {
      Nil => Nil,
      Cons (H) (T) R => Cons(H, RecN T) } } }
abbrev takeFnT : Dllbc.Term := Take

def Drop : Dllbc.Term := ty{
  λ (N : Nat). elim N return (λ (Nm : Nat). List Nat → List Nat) {
    Z => λ (L : List Nat). L,
    S (N') RecN => λ (L : List Nat). elim L return (λ (Lm : List Nat). List Nat) {
      Nil => Nil,
      Cons (H) (T) R => RecN T } } }
abbrev dropFnT : Dllbc.Term := Drop

/-- `Add a b` by recursion on `a`. Aliased from the kernel for the same reason as
    `Le`: premise (3) of CARVE decomposes an extent with `add`, so the kernel
    needs it. -/
def Add : Dllbc.Term := kAddFn
abbrev addFnT : Dllbc.Term := Add

/-- `Append a b` by recursion on `a` (`Nil ↦ b`, `Cons h t ↦ Cons h (Append t b)`). -/
def Append : Dllbc.Term := ty{
  λ (A : List Nat). λ (B : List Nat). elim A return (λ (Lm : List Nat). List Nat) {
    Nil => B,
    Cons (H) (T) R => Cons(H, R) } }

/-! ## First lemma: `le_refl : Π n. Le n n`, by `natRec`

    The base is `⋆ : Le Z Z = ⊤`; the step returns the IH unchanged, because
    `Le (S m) (S m)` and `Le m m` are definitionally equal.

    **These two are the respell's own control.** They are the only definitions in
    this file whose hand form named every binder it bound — no reserved `§_`
    motive anywhere — and they are the two that come out `Term.alphaEq`-IDENTICAL
    to it, mode markers included. The other nine differ in exactly the position
    the hand form could write and the surface cannot. -/

def le_refl : Term := ty{
  λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
    Z => unit,
    S (M) Rec => Rec } }
def le_reflT : Dllbc.Term := le_refl
def le_refl_ty : Term := ty{ Π (N : Nat) → Le N N }

/-! ## Normalizing a term, for the generalize-elim macro

    §18: exposes a computed subterm (e.g. an `eqb`-spine hidden in a `count`
    unfolding) so `abstractOccurrences` can find it in a natural goal. Emitted by
    the macro BY NAME, which is why it lives here — the macro is below this
    module and resolves the name at its use site. -/
def nfTerm (t : Dllbc.Term) : Dllbc.Term := Dllbc.Pure.nf 1000 t

end Dllbc.Std
