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
open Dllbc.Val

/-! ## Value constructors and recursor spines -/

def natTy : Val := .const "Nat"
def listNatTy : Val := .app (.const "List") natTy
def boolTy : Val := .const "Bool"
def unitTy : Val := .const "Unit"
def botTy : Val := .const "Bot"
def zero : Val := .ctor "Z" []
def suc (v : Val) : Val := .ctor "S" [v]
def ofNat : Nat → Val | 0 => zero | n + 1 => suc (ofNat n)
def tt : Val := .ctor "True" []
def ff : Val := .ctor "False" []
def star : Val := .ctor "unit" []                     -- the ⊤ inhabitant
def consV (h t : Val) : Val := .ctor "Cons" [h, t]
def nilV : Val := .ctor "Nil" []
def ofList : List Val → Val | [] => nilV | h :: t => consV h (ofList t)
def pairV (a b : Val) : Val := .ctor "Pair" [a, b]

def natRecS (P z s n : Val) : Val := .app (.app (.app (.app (.const "natRec") P) z) s) n
def boolRecS (P t f b : Val) : Val := .app (.app (.app (.app (.const "boolRec") P) t) f) b
def listRecS (A P pn pc l : Val) : Val := .app (.app (.app (.app (.app (.const "listRec") A) P) pn) pc) l

/-- The successor-recurse arm shared by `Le`/`NatCode`-shaped double recursions:
    `λa'. λrecA. λb. natRec (λ_.Type) falseCase (λb'. λ_. recA b') b`. -/
def sucArm (falseCase : Val) : Val :=
  .lam "a'" natTy (.lam "recA" (.pi "_" natTy .type) (.lam "b" natTy
    (natRecS (.lam "_" natTy .type) falseCase
      (.lam "b'" natTy (.lam "_" .type (.app (.pvar "recA") (.pvar "b'")))) (.pvar "b"))))

/-! ## `Le : Nat → Nat → Type`  (Z ≤ _ ↦ ⊤ ; S ≤ Z ↦ ⊥ ; S ≤ S ↦ recurse) -/

-- `Le` now LIVES in the kernel (`Pure.lean`'s `kLeFn`) and is aliased here. The CARVE
-- rule's premise (2) IS a `Le`, and a kernel rule cannot cite a library it does not
-- import; two syntactically different `Le`s would never convert, which would break
-- the one conversion the residue transition exists to make definitional. Single
-- source of truth, asserted in S24Arrays (i.h).
def LeFn : Val := kLeFn
def Le (a b : Val) : Val := .app (.app LeFn a) b

/-! ## `eqb, leb : Nat → Nat → Bool` — runtime-usable decision procedures -/

def eqbFn : Val := .lam "a" natTy (natRecS (.lam "_" natTy (.pi "_" natTy boolTy))
  (.lam "b" natTy (natRecS (.lam "_" natTy boolTy) tt (.lam "_" natTy (.lam "_" boolTy ff)) (.pvar "b")))
  (.lam "a'" natTy (.lam "recA" (.pi "_" natTy boolTy) (.lam "b" natTy
    (natRecS (.lam "_" natTy boolTy) ff
      (.lam "b'" natTy (.lam "_" boolTy (.app (.pvar "recA") (.pvar "b'")))) (.pvar "b")))))
  (.pvar "a"))
def eqb (a b : Val) : Val := .app (.app eqbFn a) b

def lebFn : Val := .lam "a" natTy (natRecS (.lam "_" natTy (.pi "_" natTy boolTy)) (.lam "_" natTy tt)
  (.lam "a'" natTy (.lam "recA" (.pi "_" natTy boolTy) (.lam "b" natTy
    (natRecS (.lam "_" natTy boolTy) ff
      (.lam "b'" natTy (.lam "_" boolTy (.app (.pvar "recA") (.pvar "b'")))) (.pvar "b")))))
  (.pvar "a"))
def leb (a b : Val) : Val := .app (.app lebFn a) b

/-! ## `count : Nat → List Nat → Nat` — the multiset counter (`listRec` + `boolRec`) -/

-- OPEN in `n`, deliberately: an arm is the body of the recursion it belongs to and
-- reaches the outer parameter the recursion is about. That was `pvar 4` and had to
-- be counted; under names it says which variable it means, and `countFn` binding it
-- is visible one line down.
def countArm : Val := .lam "h" natTy (.lam "t" listNatTy (.lam "rec" natTy
  (boolRecS (.lam "_" boolTy natTy) (suc (.pvar "rec")) (.pvar "rec")
    (eqb (.pvar "n") (.pvar "h")))))
def countFn : Val :=
  .lam "n" natTy (.lam "l" listNatTy
    (listRecS natTy (.lam "_" listNatTy natTy) zero countArm (.pvar "l")))
def count (n l : Val) : Val := .app (.app countFn n) l

/-! ## `Bound : Nat → List Nat → Type` and `Sorted : List Nat → Type` -/

-- Bound h l : the head of l is ≥ h (Nil ↦ ⊤, Cons h' _ ↦ Le h h').
def boundArm : Val :=                                    -- OPEN in `h`, like `countArm`
  .lam "h'" natTy (.lam "t" listNatTy (.lam "_" .type (Le (.pvar "h") (.pvar "h'"))))
def BoundFn : Val :=
  .lam "h" natTy (.lam "l" listNatTy
    (listRecS natTy (.lam "_" listNatTy .type) unitTy boundArm (.pvar "l")))
def Bound (h l : Val) : Val := .app (.app BoundFn h) l

-- Sorted l : Nil ↦ ⊤ ; Cons h t ↦ Bound h t × Sorted t.
def sortedArm : Val :=
  .lam "h" natTy (.lam "t" listNatTy (.lam "rec" .type
    (.sigmaT "_" (Bound (.pvar "h") (.pvar "t")) (.pvar "rec"))))
def SortedFn : Val :=
  .lam "l" listNatTy (listRecS natTy (.lam "_" listNatTy .type) unitTy sortedArm (.pvar "l"))
def Sorted (l : Val) : Val := .app SortedFn l

/-! ## `len`, `take`, `drop` — the segment vocabulary (§14)

    `len` by `listRec`; `take`/`drop` by `natRec` on the count giving a
    `List Nat → List Nat` (a `listRec` inside the successor arm), the double-
    recursion shape. These are the length bound and the prefix/suffix a
    segment-scoped spec talks about. -/

def lenArm : Val := .lam "h" natTy (.lam "t" listNatTy (.lam "rec" natTy (suc (.pvar "rec"))))
def lenFn : Val :=
  .lam "l" listNatTy (listRecS natTy (.lam "_" listNatTy natTy) zero lenArm (.pvar "l"))
def len (l : Val) : Val := .app lenFn l

def takeArm : Val :=
  .lam "n'" natTy (.lam "recN" (.pi "_" listNatTy listNatTy) (.lam "l" listNatTy
    (listRecS natTy (.lam "_" listNatTy listNatTy) nilV
      (.lam "h" natTy (.lam "t" listNatTy (.lam "r" listNatTy
        (consV (.pvar "h") (.app (.pvar "recN") (.pvar "t"))))))
      (.pvar "l"))))
def takeFn : Val :=
  .lam "n" natTy (natRecS (.lam "_" natTy (.pi "_" listNatTy listNatTy))
    (.lam "_" listNatTy nilV) takeArm (.pvar "n"))
def take (n l : Val) : Val := .app (.app takeFn n) l

def dropArm : Val :=
  .lam "n'" natTy (.lam "recN" (.pi "_" listNatTy listNatTy) (.lam "l" listNatTy
    (listRecS natTy (.lam "_" listNatTy listNatTy) nilV
      (.lam "h" natTy (.lam "t" listNatTy (.lam "r" listNatTy (.app (.pvar "recN") (.pvar "t")))))
      (.pvar "l"))))
def dropFn : Val :=
  .lam "n" natTy (natRecS (.lam "_" natTy (.pi "_" listNatTy listNatTy))
    (.lam "l" listNatTy (.pvar "l")) dropArm (.pvar "n"))
def drop (n l : Val) : Val := .app (.app dropFn n) l

/-- `add a b` by recursion on `a` (`add Z b = b`, `add (S a') b = S (add a' b)`).
    Aliased from the kernel for the same reason as `Le`: premise (3) of CARVE
    decomposes an extent with `add`, so the kernel needs it. -/
def addFn : Val := kAddFn
def add (a b : Val) : Val := .app (.app addFn a) b

/-- `append a b` by recursion on `a` (`Nil ↦ b`, `Cons h t ↦ Cons h (append t b)`). -/
def appendFn : Val :=
  .lam "a" listNatTy (.lam "b" listNatTy
    (listRecS natTy (.lam "_" listNatTy listNatTy) (.pvar "b")
      (.lam "h" natTy (.lam "t" listNatTy (.lam "r" listNatTy (consV (.pvar "h") (.pvar "r")))))
      (.pvar "a")))
def append (a b : Val) : Val := .app (.app appendFn a) b

/-! ## First lemma: `le_refl : Π n. Le n n`, by `natRec`

    `λn. natRec (λm. Le m m) ⋆ (λm. λrec. rec) n`. The base is `⋆ : Le Z Z = ⊤`;
    the step returns the IH unchanged, because `Le (S m) (S m)` and `Le m m` are
    definitionally equal. -/

def le_refl : Val :=
  .lam "n" natTy (natRecS (.lam "m" natTy (Le (.pvar "m") (.pvar "m"))) star
    (.lam "m" natTy (.lam "rec" (Le (.pvar "m") (.pvar "m")) (.pvar "rec"))) (.pvar "n"))
def le_refl_ty : Val := .pi "n" natTy (Le (.pvar "n") (.pvar "n"))

/-! ## Term-level Std (§12): the library at telescope/return/owed positions

    A program's telescope, return, and owed types are `Term`s; the library above
    is `Val`s. `toTerm` reifies the (pure) library `Val`s back to `Term`s once —
    single source of truth — so `LeT`/`SortedT`/`countT`/`BoundT`/`le_reflT` can
    sit in a `FnDef`. Runtime `Val` forms (`sym`/`loanM`/`borrowM`/`bot`) never
    occur in the pure library, so `toTerm`'s fallback is unreachable here. -/

mutual
  def toTerm : Val → Dllbc.Term
    | .type => .type
    | .const c => .const c
    | .pvar x => .pvar x
    | .lam x d b => .lam x (toTerm d) (toTerm b)
    | .pi x d c => .pi x (toTerm d) (toTerm c)
    | .sigmaT x d c => .sigmaT x (toTerm d) (toTerm c)
    | .app f a => .app (toTerm f) (toTerm a)
    | .idT a b c => .idT (toTerm a) (toTerm b) (toTerm c)
    | .ctor n args => .ctorApp n (toTermList args)
    | _ => .unit                                   -- runtime forms: unreachable in the pure library
  termination_by v => sizeOf v
  def toTermList : List Val → List Dllbc.Term
    | [] => []
    | v :: vs => toTerm v :: toTermList vs
  termination_by vs => sizeOf vs
end

def LeFnT : Dllbc.Term := toTerm LeFn
def LeT (a b : Dllbc.Term) : Dllbc.Term := .app (.app LeFnT a) b
def countFnT : Dllbc.Term := toTerm countFn
def countT (n l : Dllbc.Term) : Dllbc.Term := .app (.app countFnT n) l
def BoundFnT : Dllbc.Term := toTerm BoundFn
def BoundT (h l : Dllbc.Term) : Dllbc.Term := .app (.app BoundFnT h) l
def SortedFnT : Dllbc.Term := toTerm SortedFn
def SortedT (l : Dllbc.Term) : Dllbc.Term := .app SortedFnT l
def le_reflT : Dllbc.Term := toTerm le_refl

/-- Normalize a pure `Term` (reflect → `nfV` → reify). §18: exposes a computed
    subterm (e.g. an `eqb`-spine hidden in a `count`-unfolding) so
    `abstractOccurrences` can find it in a natural goal. Emitted by the
    generalize-elim macro by NAME, so no import cycle with the macro layer. -/
def nfTerm (t : Dllbc.Term) : Dllbc.Term := toTerm (Dllbc.Val.nfV 1000 (Dllbc.Val.Term.toValPure t))
def lenFnT : Dllbc.Term := toTerm lenFn
def lenT (l : Dllbc.Term) : Dllbc.Term := .app lenFnT l
def takeFnT : Dllbc.Term := toTerm takeFn
def takeT (n l : Dllbc.Term) : Dllbc.Term := .app (.app takeFnT n) l
def dropFnT : Dllbc.Term := toTerm dropFn
def dropT (n l : Dllbc.Term) : Dllbc.Term := .app (.app dropFnT n) l
def eqbFnT : Dllbc.Term := toTerm eqbFn
def lebFnT : Dllbc.Term := toTerm lebFn
def addFnT : Dllbc.Term := toTerm addFn
def addT (a b : Dllbc.Term) : Dllbc.Term := .app (.app addFnT a) b
def appendFnT : Dllbc.Term := toTerm appendFn
def appendT (a b : Dllbc.Term) : Dllbc.Term := .app (.app appendFnT a) b

end Dllbc.Std
