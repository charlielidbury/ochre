import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.DeclMacro

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

open Dllbc.StdLemmas (len_swapL) in
def swapS01 : Decl :=
  decl{ fn swapS01 (v : &mut (s : List Nat ~> Σ (l : List Nat) → Id Nat (len l) (len s)),
                    p : Le 2 (len *v)) -> Unit {
    let proof = len_swapL 0 1 (*v);
    match v {
      Nil => botElim Unit p,
      Cons(h0, t0) => match t0 {
        Nil => botElim Unit p,
        Cons(h1, t1) => {
          let tmp = *h0;
          *h0 := *h1;
          *h1 := tmp;
          let l = *v;
          *v := Pair(l, proof);
          ()
        }
      }
    } } }

example : checkFnOk swapS01 = true := by native_decide

-- Caller: borrow, call swapS01, demand the owner (recovering the Σ), open it to
-- l + the carried proof `pf : Id (len l) (len [1,2,3])`. The evidence survives the
-- opaque group-end — pf is in scope downstream though l itself is opaque.
def swapCaller : Decl :=
  decl{ fn caller () -> Unit {
    let x = Cons(1, Cons(2, Cons(3, Nil)));
    let b = &mut x;
    swapS01(b, ());
    let sig = x;
    match sig { Pair(l, pf) => { let m = l; () } }
  } }

example : checkFnOk swapCaller ([swapS01, swapCaller]) = true := by native_decide
-- The proof survives to the final env (pf ↦ a σ : Id (len l) (len [1,2,3])).
example : (match runFn [swapS01, swapCaller] swapCaller with
  | [.ok env] => (env.lookup "pf").isSome
  | _ => false) = true := by native_decide

end Dllbc.Tests.S16Spec
