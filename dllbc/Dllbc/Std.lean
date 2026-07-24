import Dllbc.Value

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
  .lam natTy (.lam (.pi natTy .type) (.lam natTy
    (natRecS (.lam natTy .type) falseCase (.lam natTy (.lam .type (.app (.pvar 3) (.pvar 1)))) (.pvar 0))))

/-! ## `Le : Nat → Nat → Type`  (Z ≤ _ ↦ ⊤ ; S ≤ Z ↦ ⊥ ; S ≤ S ↦ recurse) -/

def LeFn : Val := .lam natTy (natRecS (.lam natTy (.pi natTy .type)) (.lam natTy unitTy) (sucArm botTy) (.pvar 0))
def Le (a b : Val) : Val := .app (.app LeFn a) b

/-! ## `eqb, leb : Nat → Nat → Bool` — runtime-usable decision procedures -/

def eqbFn : Val := .lam natTy (natRecS (.lam natTy (.pi natTy boolTy))
  (.lam natTy (natRecS (.lam natTy boolTy) tt (.lam natTy (.lam boolTy ff)) (.pvar 0)))
  (.lam natTy (.lam (.pi natTy boolTy) (.lam natTy
    (natRecS (.lam natTy boolTy) ff (.lam natTy (.lam boolTy (.app (.pvar 3) (.pvar 1)))) (.pvar 0)))))
  (.pvar 0))
def eqb (a b : Val) : Val := .app (.app eqbFn a) b

def lebFn : Val := .lam natTy (natRecS (.lam natTy (.pi natTy boolTy)) (.lam natTy tt)
  (.lam natTy (.lam (.pi natTy boolTy) (.lam natTy
    (natRecS (.lam natTy boolTy) ff (.lam natTy (.lam boolTy (.app (.pvar 3) (.pvar 1)))) (.pvar 0)))))
  (.pvar 0))
def leb (a b : Val) : Val := .app (.app lebFn a) b

/-! ## `count : Nat → List Nat → Nat` — the multiset counter (`listRec` + `boolRec`) -/

def countArm : Val := .lam natTy (.lam listNatTy (.lam natTy
  (boolRecS (.lam boolTy natTy) (suc (.pvar 0)) (.pvar 0) (eqb (.pvar 4) (.pvar 2)))))
def countFn : Val := .lam natTy (.lam listNatTy (listRecS natTy (.lam listNatTy natTy) zero countArm (.pvar 0)))
def count (n l : Val) : Val := .app (.app countFn n) l

/-! ## `Bound : Nat → List Nat → Type` and `Sorted : List Nat → Type` -/

-- Bound h l : the head of l is ≥ h (Nil ↦ ⊤, Cons h' _ ↦ Le h h').
def boundArm : Val := .lam natTy (.lam listNatTy (.lam .type (Le (.pvar 4) (.pvar 2))))
def BoundFn : Val := .lam natTy (.lam listNatTy (listRecS natTy (.lam listNatTy .type) unitTy boundArm (.pvar 0)))
def Bound (h l : Val) : Val := .app (.app BoundFn h) l

-- Sorted l : Nil ↦ ⊤ ; Cons h t ↦ Bound h t × Sorted t.
def sortedArm : Val := .lam natTy (.lam listNatTy (.lam .type (.sigmaT (Bound (.pvar 2) (.pvar 1)) (.pvar 1))))
def SortedFn : Val := .lam listNatTy (listRecS natTy (.lam listNatTy .type) unitTy sortedArm (.pvar 0))
def Sorted (l : Val) : Val := .app SortedFn l

/-! ## First lemma: `le_refl : Π n. Le n n`, by `natRec`

    `λn. natRec (λm. Le m m) ⋆ (λm. λrec. rec) n`. The base is `⋆ : Le Z Z = ⊤`;
    the step returns the IH unchanged, because `Le (S m) (S m)` and `Le m m` are
    definitionally equal. -/

def le_refl : Val :=
  .lam natTy (natRecS (.lam natTy (Le (.pvar 0) (.pvar 0))) star
    (.lam natTy (.lam (Le (.pvar 0) (.pvar 0)) (.pvar 0))) (.pvar 0))
def le_refl_ty : Val := .pi natTy (Le (.pvar 0) (.pvar 0))

end Dllbc.Std
