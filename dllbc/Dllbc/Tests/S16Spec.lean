import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# §16 test suite — the count-preservation proof stack (and, later, swapS)

The campaign's verification heart. This file checks the pure lemma stack that a
spec-carrying swap's `↝`-obligation consumes: the arithmetic warm-ups (the first
real double-inductions after the M11 wall — `add_comm`/`add_assoc` are the
calibration data), then the count/append/take/drop lemmas building to
`count_swapL` (swap preserves the multiset).

Calibration finding: every arithmetic lemma below — including the classic
commutativity and associativity proofs — was authored in the §15 surface and
checked on the FIRST attempt. The surface layer's payoff is not just `le_trans`;
routine nested inductions are now routine.
-/

open Dllbc

namespace Dllbc.Tests.S16Spec

/-- Check a pure lemma `Term` against its type `Term` (deep fuel). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

open Dllbc.StdLemmas in
/-! ## The arithmetic warm-ups -/

example : chk StdLemmas.id_sym StdLemmas.id_sym_ty = true := by native_decide
example : chk StdLemmas.add_zero StdLemmas.add_zero_ty = true := by native_decide
example : chk StdLemmas.add_succ StdLemmas.add_succ_ty = true := by native_decide
example : chk StdLemmas.add_comm StdLemmas.add_comm_ty = true := by native_decide
example : chk StdLemmas.add_assoc StdLemmas.add_assoc_ty = true := by native_decide
example : chk StdLemmas.count_cons StdLemmas.count_cons_ty = true := by native_decide

/-! ## The count/append/take/drop lemmas -/

example : chk StdLemmas.count_append StdLemmas.count_append_ty = true := by native_decide
example : chk StdLemmas.take_drop_id StdLemmas.take_drop_id_ty = true := by native_decide

/-! ## `swapL` computes (the pure swap specification) -/

def rd (t : Term) : Val := match (readC 3000 t).run (seedPure [] []) with | .ok v _ => v | .error _ _ => .const "ERR"
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]
def tlist : List Nat → Term | [] => .ctorApp "Nil" [] | h :: t => .ctorApp "Cons" [tnat h, tlist t]
def swapLApp (i j l : Term) : Term := .app (.app (.app StdLemmas.swapL i) j) l

example : (rd (swapLApp (tnat 0) (tnat 2) (tlist [1, 2, 3])) == Std.ofList [Std.ofNat 3, Std.ofNat 2, Std.ofNat 1]) = true := by
  native_decide
example : (rd (swapLApp (tnat 1) (tnat 2) (tlist [1, 2, 3])) == Std.ofList [Std.ofNat 1, Std.ofNat 3, Std.ofNat 2]) = true := by
  native_decide

/-! ## Length preservation (the spec swapS carries) — unconditional, no bounds -/

example : chk StdLemmas.len_set StdLemmas.len_set_ty = true := by native_decide
example : chk StdLemmas.len_swapL StdLemmas.len_swapL_ty = true := by native_decide

/-! ## swapS01 — the inlined spec-carrying swap (the M16 headline)

    A spec-carrying in-place swap of positions 0,1, its `↝`-obligation the Σ
    `Σ (l : List Nat). Id Nat (len l) (len s)`. The cursor work stays inside ONE
    body (the contract-free interior, where collapse is transparent): the entry
    proof `len_swapL 0 1 (*v)` is captured non-destructively; the two element
    cursors (h0 from v, h1 from its tail — disjoint by the suspension tree) swap
    by take-and-fill; `let l = *v` collapses the field loans TRANSPARENTLY to the
    swapped list; `*v := Pair(l, proof)` fills the Σ. The proof's type refines
    with the match (σ-bearing-state invariant), and the cursor output converges
    with `swapL 0 1 s` by computation — so it type-checks against `Id (len l)
    (len s)`. The cursor writes and the pure specification agree, verified. -/

def natT : Term := .const "Nat"
def listNatT : Term := .app (.const "List") natT
def lenTr (l : Term) : Term := Std.lenT l
def LeTr (a b : Term) : Term := Std.LeT a b
def bE (x : Term) : Term := .app (.app (.const "botElim") (.const "Unit")) x
def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def Dv (i : Nat) (n : String) : Term := .deref (V i n)
def owedS : Term := .sigmaT listNatT (.idT natT (lenTr (.pvar 0)) (lenTr (.pvar 1)))
def proofTerm : Term := .app (.app (.app StdLemmas.len_swapL (tnat 0)) (tnat 1)) (Dv 0 "v")
def swapS01Tele : List (String × Term) := [("v", .borrowT listNatT owedS), ("p", LeTr (tnat 2) (lenTr (Dv 0 "v")))]
def innerSwap : Term :=
  .letIn ⟨7, "tmp"⟩ (Dv 3 "h0")
    (.assign (Dv 3 "h0") (Dv 5 "h1")
      (.assign (Dv 5 "h1") (V 7 "tmp")
        (.letIn ⟨8, "l"⟩ (Dv 0 "v")
          (.assign (Dv 0 "v") (.ctorApp "Pair" [V 8 "l", V 2 "proof"]) .unit))))
def swapS01Body : Term :=
  .letIn ⟨2, "proof"⟩ proofTerm
  (.matchE ⟨0, "v"⟩ [
    .mk "Nil" [] (bE (V 1 "p")),
    .mk "Cons" [⟨3, "h0"⟩, ⟨4, "t0"⟩] (.matchE ⟨4, "t0"⟩ [
      .mk "Nil" [] (bE (V 1 "p")),
      .mk "Cons" [⟨5, "h1"⟩, ⟨6, "t1"⟩] innerSwap ]) ])
def swapS01 : Decl := { name := "swapS01", retType := .const "Unit", telescope := swapS01Tele, body := swapS01Body }

example : checkFnOk swapS01 = true := by native_decide

-- Caller: borrow, call swapS01, demand the owner (recovering the Σ), open it to
-- l + the carried proof `pf : Id (len l) (len [1,2,3])`. The evidence survives the
-- opaque group-end — pf is in scope downstream though l itself is opaque.
def callerBody : Term :=
  .letIn ⟨0, "x"⟩ (.ctorApp "Cons" [tnat 1, .ctorApp "Cons" [tnat 2, .ctorApp "Cons" [tnat 3, .ctorApp "Nil" []]]])
  (.letIn ⟨1, "b"⟩ (.borrow (V 0 "x"))
  (.seq (.call "swapS01" [V 1 "b", .unit])
  (.letIn ⟨2, "sig"⟩ (V 0 "x")
  (.matchE ⟨2, "sig"⟩ [ .mk "Pair" [⟨3, "l"⟩, ⟨4, "pf"⟩] (.letIn ⟨5, "m"⟩ (V 3 "l") .unit) ]))))
def swapCaller : Decl := { name := "caller", retType := .const "Unit", telescope := [], body := callerBody }

example : checkFnOk swapCaller ([swapS01, swapCaller]) = true := by native_decide
-- The proof survives to the final env (pf ↦ a σ : Id (len l) (len [1,2,3])).
example : (match runFn [swapS01, swapCaller] swapCaller with
  | [.ok env] => (env.lookup "pf").isSome
  | _ => false) = true := by native_decide

end Dllbc.Tests.S16Spec
