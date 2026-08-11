import Dllbc.Value
import Dllbc.Syntax
import Dllbc.Pure

/-!
# `Dllbc.Std` — the quicksort pure library (§11)

The verification vocabulary the north-star quicksort needs, derived *inside*
the calculus as ordinary comptime terms (`Val`s): the order type `Le`, its
Boolean reflections `eqb`/`leb`, the multiset counter `count`, and the
predicates `Bound`/`Sorted`. All are large-elimination recursors — double
`natRec` for the `Nat → Nat → _` shapes, `listRec` for the list-recursive
predicates — so they *compute*: `Le 1 2` whnf's to `⊤`, `Sorted [1,2]` to a
product of `⊤`s, `count 1 [1,2,1]` to `2`. Types are values here (reflected
comptime terms), so the library lives in the `Val` world; a program that needs
one at a telescope position reflects it with `readC`.

`le_refl : Π n. Le n n` is the first checked lemma (by `natRec`); it goes
through by the §11 recursor-neutral synthesis and λ-vs-Π typing in `hasType`.
`le_trans` is deliberately *not* here — see the milestone report: as a raw
de Bruijn term it is a three-level nested dependent induction, the concrete
motivation for a later dependent-elimination surface syntax.
-/

namespace Dllbc.Std
open Dllbc.Pure

/-! ## Value constructors and recursor spines -/

def natTy : Term := .const "Nat"
def listNatTy : Term := .app (.const "List") natTy
def boolTy : Term := .const "Bool"
def unitTy : Term := .const "Unit"
def botTy : Term := .const "Bot"
def zero : Term := .ctorApp "Z" []
def suc (v : Term) : Term := .ctorApp "S" [v]
def ofNat : Nat → Term | 0 => zero | n + 1 => suc (ofNat n)
def tt : Term := .ctorApp "True" []
def ff : Term := .ctorApp "False" []
def star : Term := .ctorApp "unit" []                     -- the ⊤ inhabitant
def consV (h t : Term) : Term := .ctorApp "Cons" [h, t]
def nilV : Term := .ctorApp "Nil" []
def ofList : List Term → Term | [] => nilV | h :: t => consV h (ofList t)
def pairV (a b : Term) : Term := .ctorApp "Pair" [a, b]

def natRecS (P z s n : Term) : Term := .app (.app (.app (.app (.const "natRec") P) z) s) n
def boolRecS (P t f b : Term) : Term := .app (.app (.app (.app (.const "boolRec") P) t) f) b
def listRecS (A P pn pc l : Term) : Term := .app (.app (.app (.app (.app (.const "listRec") A) P) pn) pc) l

/-- The successor-recurse arm shared by `Le`/`NatCode`-shaped double recursions:
    `λa'. λrecA. λb. natRec (λ_.Type) falseCase (λb'. λ_. recA b') b`. -/
def sucArm (falseCase : Term) : Term :=
  Term.clam "A'" natTy (Term.clam "RecA" (.pi "§_" natTy .type) (Term.clam "B" natTy
    (natRecS (.lam "§_" natTy .type) falseCase
      (Term.clam "B'" natTy (.lam "§_" .type (.app (.pvar "RecA") (.pvar "B'")))) (.pvar "B"))))

/-! ## `Le : Nat → Nat → Type`  (Z ≤ _ ↦ ⊤ ; S ≤ Z ↦ ⊥ ; S ≤ S ↦ recurse) -/

-- `Le` now LIVES in the kernel (`Pure.lean`'s `kLeFn`) and is aliased here. The CARVE
-- rule's premise (2) IS a `Le`, and a kernel rule cannot cite a library it does not
-- import; two syntactically different `Le`s would never convert, which would break
-- the one conversion the residue transition exists to make definitional. Single
-- source of truth, asserted in S24Arrays (i.h).
def LeFn : Term := kLeFn
def Le (a b : Term) : Term := .app (.app LeFn a) b

/-! ## `eqb, leb : Nat → Nat → Bool` — runtime-usable decision procedures -/

def eqbFn : Term := Term.clam "A" natTy (natRecS (.lam "§_" natTy (.pi "§_" natTy boolTy))
  (Term.clam "B" natTy (natRecS (.lam "§_" natTy boolTy) tt (.lam "§_" natTy (.lam "§_" boolTy ff)) (.pvar "B")))
  (Term.clam "A'" natTy (Term.clam "RecA" (.pi "§_" natTy boolTy) (Term.clam "B" natTy
    (natRecS (.lam "§_" natTy boolTy) ff
      (Term.clam "B'" natTy (.lam "§_" boolTy (.app (.pvar "RecA") (.pvar "B'")))) (.pvar "B")))))
  (.pvar "A"))
def eqb (a b : Term) : Term := .app (.app eqbFn a) b

def lebFn : Term := Term.clam "A" natTy (natRecS (.lam "§_" natTy (.pi "§_" natTy boolTy)) (.lam "§_" natTy tt)
  (Term.clam "A'" natTy (Term.clam "RecA" (.pi "§_" natTy boolTy) (Term.clam "B" natTy
    (natRecS (.lam "§_" natTy boolTy) ff
      (Term.clam "B'" natTy (.lam "§_" boolTy (.app (.pvar "RecA") (.pvar "B'")))) (.pvar "B")))))
  (.pvar "A"))
def leb (a b : Term) : Term := .app (.app lebFn a) b

/-! ## `count : Nat → List Nat → Nat` — the multiset counter (`listRec` + `boolRec`) -/

-- OPEN in `n`, deliberately: an arm is the body of the recursion it belongs to and
-- reaches the outer parameter the recursion is about. That was `pvar 4` and had to
-- be counted; under names it says which variable it means, and `countFn` binding it
-- is visible one line down.
def countArm : Term := Term.clam "H" natTy (Term.clam "T" listNatTy (Term.clam "Rec" natTy
  (boolRecS (.lam "§_" boolTy natTy) (suc (.pvar "Rec")) (.pvar "Rec")
    (eqb (.pvar "N") (.pvar "H")))))
def countFn : Term :=
  Term.clam "N" natTy (Term.clam "L" listNatTy
    (listRecS natTy (.lam "§_" listNatTy natTy) zero countArm (.pvar "L")))
def count (n l : Term) : Term := .app (.app countFn n) l

/-! ## `Bound : Nat → List Nat → Type` and `Sorted : List Nat → Type` -/

-- Bound h l : the head of l is ≥ h (Nil ↦ ⊤, Cons h' _ ↦ Le h h').
def boundArm : Term :=                                    -- OPEN in `h`, like `countArm`
  Term.clam "H'" natTy (Term.clam "T" listNatTy (.lam "§_" .type (Le (.pvar "H") (.pvar "H'"))))
def BoundFn : Term :=
  Term.clam "H" natTy (Term.clam "L" listNatTy
    (listRecS natTy (.lam "§_" listNatTy .type) unitTy boundArm (.pvar "L")))
def Bound (h l : Term) : Term := .app (.app BoundFn h) l

-- Sorted l : Nil ↦ ⊤ ; Cons h t ↦ Bound h t × Sorted t.
def sortedArm : Term :=
  Term.clam "H" natTy (Term.clam "T" listNatTy (Term.clam "Rec" .type
    (.sigmaT "§_" (Bound (.pvar "H") (.pvar "T")) (.pvar "Rec"))))
def SortedFn : Term :=
  Term.clam "L" listNatTy (listRecS natTy (.lam "§_" listNatTy .type) unitTy sortedArm (.pvar "L"))
def Sorted (l : Term) : Term := .app SortedFn l

/-! ## `len`, `take`, `drop` — the segment vocabulary (§14)

    `len` by `listRec`; `take`/`drop` by `natRec` on the count giving a
    `List Nat → List Nat` (a `listRec` inside the successor arm), the double-
    recursion shape. These are the length bound and the prefix/suffix a
    segment-scoped spec talks about. -/

def lenArm : Term := Term.clam "H" natTy (Term.clam "T" listNatTy (Term.clam "Rec" natTy (suc (.pvar "Rec"))))
def lenFn : Term :=
  Term.clam "L" listNatTy (listRecS natTy (.lam "§_" listNatTy natTy) zero lenArm (.pvar "L"))
def len (l : Term) : Term := .app lenFn l

def takeArm : Term :=
  Term.clam "N'" natTy (Term.clam "RecN" (.pi "§_" listNatTy listNatTy) (Term.clam "L" listNatTy
    (listRecS natTy (.lam "§_" listNatTy listNatTy) nilV
      (Term.clam "H" natTy (Term.clam "T" listNatTy (Term.clam "R" listNatTy
        (consV (.pvar "H") (.app (.pvar "RecN") (.pvar "T"))))))
      (.pvar "L"))))
def takeFn : Term :=
  Term.clam "N" natTy (natRecS (.lam "§_" natTy (.pi "§_" listNatTy listNatTy))
    (.lam "§_" listNatTy nilV) takeArm (.pvar "N"))
def take (n l : Term) : Term := .app (.app takeFn n) l

def dropArm : Term :=
  Term.clam "N'" natTy (Term.clam "RecN" (.pi "§_" listNatTy listNatTy) (Term.clam "L" listNatTy
    (listRecS natTy (.lam "§_" listNatTy listNatTy) nilV
      (Term.clam "H" natTy (Term.clam "T" listNatTy (Term.clam "R" listNatTy (.app (.pvar "RecN") (.pvar "T")))))
      (.pvar "L"))))
def dropFn : Term :=
  Term.clam "N" natTy (natRecS (.lam "§_" natTy (.pi "§_" listNatTy listNatTy))
    (Term.clam "L" listNatTy (.pvar "L")) dropArm (.pvar "N"))
def drop (n l : Term) : Term := .app (.app dropFn n) l

/-- `add a b` by recursion on `a` (`add Z b = b`, `add (S a') b = S (add a' b)`).
    Aliased from the kernel for the same reason as `Le`: premise (3) of CARVE
    decomposes an extent with `add`, so the kernel needs it. -/
def addFn : Term := kAddFn
def add (a b : Term) : Term := .app (.app addFn a) b

/-- `append a b` by recursion on `a` (`Nil ↦ b`, `Cons h t ↦ Cons h (append t b)`). -/
def appendFn : Term :=
  Term.clam "A" listNatTy (Term.clam "B" listNatTy
    (listRecS natTy (.lam "§_" listNatTy listNatTy) (.pvar "B")
      (Term.clam "H" natTy (Term.clam "T" listNatTy (Term.clam "R" listNatTy (consV (.pvar "H") (.pvar "R")))))
      (.pvar "A")))
def append (a b : Term) : Term := .app (.app appendFn a) b

/-! ## First lemma: `le_refl : Π n. Le n n`, by `natRec`

    `λn. natRec (λm. Le m m) ⋆ (λm. λrec. rec) n`. The base is `⋆ : Le Z Z = ⊤`;
    the step returns the IH unchanged, because `Le (S m) (S m)` and `Le m m` are
    definitionally equal. -/

def le_refl : Term :=
  Term.clam "N" natTy (natRecS (Term.clam "M" natTy (Le (.pvar "M") (.pvar "M"))) star
    (Term.clam "M" natTy (Term.clam "Rec" (Le (.pvar "M") (.pvar "M")) (.pvar "Rec"))) (.pvar "N"))
def le_refl_ty : Term := Term.cpi "N" natTy (Le (.pvar "N") (.pvar "N"))

/-! ## Term-level Std (§12): the library at telescope/return/owed positions

    **The `toTerm` bridge is GONE** (M32 R1). It existed because a program's
    telescope, return and owed types were `Term`s while the library above was
    `Val`s, and it reified one into the other so there was a single source of
    truth. With knowledge at rest BEING a `Term`, the two are the same
    representation and the reification is the identity — so the `…T` names below
    are the library terms themselves, kept because 400 call sites spell them that
    way and because the distinction they marked (a library value versus the term
    that denotes it) no longer exists to be marked. -/

def LeFnT : Dllbc.Term := LeFn
def LeT (a b : Dllbc.Term) : Dllbc.Term := .app (.app LeFnT a) b
def countFnT : Dllbc.Term := countFn
def countT (n l : Dllbc.Term) : Dllbc.Term := .app (.app countFnT n) l
def BoundFnT : Dllbc.Term := BoundFn
def BoundT (h l : Dllbc.Term) : Dllbc.Term := .app (.app BoundFnT h) l
def SortedFnT : Dllbc.Term := SortedFn
def SortedT (l : Dllbc.Term) : Dllbc.Term := .app SortedFnT l
def le_reflT : Dllbc.Term := le_refl

/-- Normalize a pure `Term` (reflect → `nfV` → reify). §18: exposes a computed
    subterm (e.g. an `eqb`-spine hidden in a `count`-unfolding) so
    `abstractOccurrences` can find it in a natural goal. Emitted by the
    generalize-elim macro by NAME, so no import cycle with the macro layer. -/
def nfTerm (t : Dllbc.Term) : Dllbc.Term := Dllbc.Pure.nf 1000 t
def lenFnT : Dllbc.Term := lenFn
def lenT (l : Dllbc.Term) : Dllbc.Term := .app lenFnT l
def takeFnT : Dllbc.Term := takeFn
def takeT (n l : Dllbc.Term) : Dllbc.Term := .app (.app takeFnT n) l
def dropFnT : Dllbc.Term := dropFn
def dropT (n l : Dllbc.Term) : Dllbc.Term := .app (.app dropFnT n) l
def eqbFnT : Dllbc.Term := eqbFn
def lebFnT : Dllbc.Term := lebFn
def addFnT : Dllbc.Term := addFn
def addT (a b : Dllbc.Term) : Dllbc.Term := .app (.app addFnT a) b
def appendFnT : Dllbc.Term := appendFn
def appendT (a b : Dllbc.Term) : Dllbc.Term := .app (.app appendFnT a) b

end Dllbc.Std
