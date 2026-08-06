import Dllbc.Machine

/-!
# §4 test suite — the pure fragment (⇝, conversion, value typing)

β/ι reduction via `readC` (the ⇝ arrow), stuck neutrals and conversion, the
large-elimination flagship (`VecF` — a `Vec`-shaped type family computed by
`natRec`, converting under a stuck index), and value typing (`hasType`) against
the fixed constructor basis. Prior suites are untouched and green.

Pure terms have no surface syntax, so the library (`add`, `VecF`, recursor
applications) is built directly from the pure `Term`/`Val` formers; σ's are
seeded via a variable slot (`readC` reads the snapshot).
-/

open Dllbc
open Dllbc.Val (nat)

namespace Dllbc.Tests.S4Pure

-- SUBJECT FILE: the pure fragment (⇝, conversion, value typing) has no runtime surface,
-- so the whole library here is built directly from raw Term/Val formers — these raw
-- constructions ARE the subject under test (reduction, hasType, convert), not a surface
-- form. Every raw constructor below is intentional test machinery.

/-! ## Pure library (built from the raw formers) — SUBJECT: raw pure Terms under test -/

def natT : Term := .const "Nat"
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]

/-- `add m n = natRec (λ_.Nat) n (λ_. λr. S r) m` (m = #1, n = #0). -/
def addT : Term :=
  .lam natT (.lam natT
    (.app (.app (.app (.app (.const "natRec") (.lam natT natT)) (.pvar 0))
      (.lam natT (.lam natT (.ctorApp "S" [.pvar 0])))) (.pvar 1)))

/-- `VecF T n = natRec (λ_.Type) Unit (λn'. λrec. Σ(_:T). rec) n` — a `Vec`-shaped
    family by large elimination (§4.2's `VecF Nat Z = Unit`, `VecF Nat (S n) =
    Σ (_:Nat). VecF Nat n`). `T = #1`, `n = #0`. -/
def vecFT : Term :=
  .lam .type (.lam natT
    (.app (.app (.app (.app (.const "natRec") (.lam natT .type)) (.const "Unit"))
      (.lam natT (.lam .type (.sigmaT (.pvar 3) (.pvar 1))))) (.pvar 0)))

/-- `boolRec (λ_.Nat) t f b`. -/
def boolRecNat (t f b : Term) : Term :=
  .app (.app (.app (.app (.const "boolRec") (.lam (.const "Bool") natT)) t) f) b

/-- A slot holding `σ0`, and the term reading it. -/
def sVar : Term := .var ⟨0, "s"⟩
def seedS : Omega := [(⟨0, "s"⟩, .sym 0)]

/-! ## β / ι reduction (⇝) — SUBJECT: raw pure Terms under reduction test -/

-- add 2 3 ⇝ 5.
example : expectReadC [] [] (.app (.app addT (tnat 2)) (tnat 3)) (nat 5) = true := by native_decide

-- boolRec both ways.
example : expectReadC [] [] (boolRecNat (tnat 7) (tnat 9) (.ctorApp "True" [])) (nat 7) = true := by
  native_decide
example : expectReadC [] [] (boolRecNat (tnat 7) (tnat 9) (.ctorApp "False" [])) (nat 9) = true := by
  native_decide

-- botElim never fires (⊥ has no constructors): `botElim Nat σ` is a stuck value.
example : expectReadC seedS [] (.app (.app (.const "botElim") natT) sVar)
  (.app (.app (.const "botElim") (.const "Nat")) (.sym 0)) = true := by native_decide

/-! ## Stuck neutrals and conversion -/

-- add σ 1 evaluates to the canonical stuck spine `natRec (λ_.Nat) 1 step σ`.
example : expectReadC seedS [] (.app (.app addT sVar) (tnat 1))
  (.app (.app (.app (.app (.const "natRec") (.lam (.const "Nat") (.const "Nat"))) (nat 1))
    (.lam (.const "Nat") (.lam (.const "Nat") (.ctor "S" [.pvar 0])))) (.sym 0)) = true := by
  native_decide

-- Conversion of stuck neutrals: reflexive, and sensitive to the argument.
example : expectConv seedS [] (.app (.app addT sVar) (tnat 1)) (.app (.app addT sVar) (tnat 1))
  = true := by native_decide
example : expectConv seedS [] (.app (.app addT sVar) (tnat 1)) (.app (.app addT sVar) (tnat 2))
  = false := by native_decide

/-! ## Large elimination (the flagship): computation under a stuck index
    SUBJECT: raw pure Terms (VecF etc.) under the conversion test. -/

-- `VecF Nat (S σ)` CONVERTS to `Σ (_:Nat). VecF Nat σ` — natRec proceeding past a
-- stuck index, the property §4.2's dependent push stands on.
example : expectConv seedS []
  (.app (.app vecFT natT) (.ctorApp "S" [sVar]))
  (.sigmaT natT (.app (.app vecFT natT) sVar)) = true := by native_decide

/-! ## Value typing -/

-- Val-level library (hasType works on values).
def natV : Val := .const "Nat"
def listNat : Val := .app (.const "List") natV
def vecFV : Val :=
  .lam .type (.lam natV
    (.app (.app (.app (.app (.const "natRec") (.lam natV .type)) (.const "Unit"))
      (.lam natV (.lam .type (.sigmaT (.pvar 3) (.pvar 1))))) (.pvar 0)))
/-- `Σ (l : Nat). VecF Nat l` (the l is a genuine de Bruijn dependency). -/
def sigVecF : Val := .sigmaT natV (.app (.app vecFV natV) (.pvar 0))

-- Positives: `Cons σₑ σ : List Nat` under sctx = {σₑ : Nat, σ : List Nat};
-- `Pair 1 p : Σ (l:Nat). VecF Nat l` with `p = Pair 5 unit : VecF Nat 1` — the
-- second field's type is instantiated at the first field's value.
example : expectHasType [] [(0, natV), (1, listNat)]
  (.ctor "Cons" [.sym 0, .sym 1]) listNat = true := by native_decide

example : expectHasType [] []
  (.ctor "Pair" [nat 1, .ctor "Pair" [nat 5, .ctor "unit" []]]) sigVecF = true := by native_decide

-- Negatives: wrong constructor for the type; a `Pair` whose second field fails
-- the instantiated type (`True` does not inhabit `VecF Nat 1`).
example : expectHasType [] [(0, natV), (1, listNat)]
  (.ctor "Cons" [.sym 0, .sym 1]) (.const "Bool") = false := by native_decide

example : expectHasType [] []
  (.ctor "Pair" [nat 1, .ctor "True" []]) sigVecF = false := by native_decide

/-! ## Conversion negative under a binder -/

-- Two λ's that differ only in their bodies are not convertible (no eta; de
-- Bruijn bodies compared structurally after normalization).
example : Val.convert 1000 (.lam natV (.pvar 0)) (.lam natV (.ctor "Z" [])) = false := by
  native_decide

end Dllbc.Tests.S4Pure
