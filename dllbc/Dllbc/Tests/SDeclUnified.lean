import Dllbc.DeclMacro
import Dllbc.AlphaEq
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.S17Spec

/-!
# Unified-grammar round-trips — splice-free bodies (§ points 1–4)

The previous phase could express `nthS`'s telescope/back in the surface but had to
splice its body (`= %term`), because the `Nil` branch `botElim Unit p` — a pure
application spine — was outside the runtime `dllb` grammar. With the unified
`uterm`/`ublk` grammar the body is now written DIRECTLY:

  * `botElim Unit p` — a juxtaposition application spine (const `botElim` applied
    to const `Unit` and runtime var `p`);
  * `&mut *hd`, `nth(&mut *tl, k, p)` — runtime borrow and call, in the same body.

The disambiguation rule at work: `nth(&mut *tl, k, p)` (identifier + comma-paren)
is a runtime **call**; `botElim Unit p` (space-separated juxtaposition) is a pure
**application**.

`nthS`'s hand-numbered ids happen to coincide with the macro's linear pre-order
threading, so the produced body is EXACTLY the corpus body (not merely alphaEq) —
demonstrated by the exact `body ==` below and confirmed by `alphaEq` over the
whole Decl. (The multi-branch bodies whose ids genuinely diverge — partScanE,
quicksort — are the stretch; `Decl.alphaEq` is the machinery that reaches them.)
-/

open Dllbc
open Dllbc.StdLemmas (set nth le_rw_r id_sym le_add)

namespace Dllbc.Tests.SDeclUnified

def nthU : Decl :=
  decl{ fn nth (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat
        back = λ (r : Nat). set i r (*v)
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match i {
              Z => &mut *hd,
              S(k) => nth(&mut *tl, k, p)
            }
        } } }

-- The body is now written splice-free and is EXACTLY the corpus body:
example : (nthU.body == Dllbc.Tests.S17Spec.nthS.body) = true := by native_decide
-- ...and the whole Decl is alphaEq (here: exactly equal) to the corpus nthS:
example : Decl.alphaEq nthU Dllbc.Tests.S17Spec.nthS = true := by native_decide

-- alphaEq sanity: reflexive, and it sees through a body-id permutation. `permuted`
-- is nthS with two branch-binder ids renamed to fresh values — exact BEq of the
-- bodies fails, alphaEq holds.
def permuted : Decl :=
  { Dllbc.Tests.S17Spec.nthS with
    body := .matchE ⟨0, "v"⟩ [
      .mk "Nil" [] (.app (.app (.const "botElim") (.const "Unit")) (.var ⟨2, "p"⟩)),
      .mk "Cons" [⟨30, "hd"⟩, ⟨40, "tl"⟩] (
        .matchE ⟨1, "i"⟩ [
          .mk "Z" [] (.borrow (.deref (.var ⟨30, "hd"⟩))),
          .mk "S" [⟨50, "k"⟩] (.call "nth" [.borrow (.deref (.var ⟨40, "tl"⟩)), .var ⟨50, "k"⟩, .var ⟨2, "p"⟩]) ]) ] }
example : (permuted.body == Dllbc.Tests.S17Spec.nthS.body) = false := by native_decide
example : Decl.alphaEq permuted Dllbc.Tests.S17Spec.nthS = true := by native_decide

/-! ## The stretch: `partScanE` — a multi-branch body whose ids genuinely diverge

`partScanE` (the executing Lomuto scan, S19Partition.lean) is the first body where
the corpus's hand-numbering does NOT coincide with pre-order threading: it numbers
`k2`=5 in the `S`-arm of `match k` but `i2`=6 in the `Z`-arm, and reuses id 6 for
`c` — so the macro's linear ids (i2=5, k2=6, c=7, g2=8) differ, and exact BEq is
out of reach. `Decl.alphaEq` is exactly the criterion that reaches it.

The body is proof-free but full of PURE application spines (`leb (nth (S (add i g))
*v) pivot`) sitting beside runtime calls (`swapS(…)`, `partScanE(…)`) — the case
the no-whitespace rule exists for: `nth (S x) *v` (spaces) is a pure application,
`swapS(v, …)` (no space) is a runtime call.

`expected` is transcribed verbatim from S19Partition.lean:556-575 (its exact
constructors and hand ids), so `alphaEq surface expected` is `alphaEq surface
S19.partScanE` without the 39-minute S19 import; the literal `== S19.partScanE`
runs in SDeclUnifiedS19.lean, gated to the final full build. -/

private def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
private def listNatT' : Term := .app (.const "List") (.const "Nat")
private def natT' : Term := .const "Nat"
private def tS (t : Term) : Term := .ctorApp "S" [t]
private def zt : Term := .ctorApp "Z" []
private def dV (i : Nat) (n : String) : Term := .deref (.var ⟨i, n⟩)
private def addTm (a b : Term) : Term := .app (.app Dllbc.Std.addFnT a) b
private def lebT (a b : Term) : Term := .app (.app Dllbc.Std.lebFnT a) b
private def nthT (k l : Term) : Term := .app (.app Dllbc.StdLemmas.nth k) l
private def u : Term := .unit

-- Surface partScanE, splice-free — pure `leb`/`nth`/`add` spines beside runtime calls.
def partScanEU : Decl :=
  decl{ fn partScanE (v : &mut List Nat, k : Nat, i : Nat, g : Nat, pivot : Nat) -> Unit
        { match k {
            Z => match i {
              Z => (),
              S(i2) => { swapS(v, Z, S(i2), (), ()); () }
            },
            S(k2) => {
              let c = leb (nth (S (add i g)) (*v)) pivot;
              match c {
                True => match g {
                  Z => partScanE(v, k2, S(i), Z, pivot),
                  S(g2) => { swapS(&mut *v, S(i), S(add i (S(g2))), (), ());
                             partScanE(v, k2, S(i), S(g2), pivot) }
                },
                False => partScanE(v, k2, i, S(g), pivot)
              }
            }
        } } }

-- Verbatim transcription of S19Partition.lean:556-575 (exact hand ids).
def partScanEExpected : Decl :=
  { name := "partScanE", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT' listNatT'), ("k", natT'), ("i", natT'), ("g", natT'), ("pivot", natT')],
    body := .matchE ⟨1, "k"⟩ [
      .mk "Z" [] (.matchE ⟨2, "i"⟩ [
        .mk "Z" [] u,
        .mk "S" [⟨6, "i2"⟩] (.seq (.call "swapS" [.var ⟨0, "v"⟩, zt, tS (V 6 "i2"), u, u]) u) ]),
      .mk "S" [⟨5, "k2"⟩]
        (.letIn ⟨6, "c"⟩ (lebT (nthT (tS (addTm (V 2 "i") (V 3 "g"))) (dV 0 "v")) (V 4 "pivot"))
          (.matchE ⟨6, "c"⟩ [
            .mk "True" [] (.matchE ⟨3, "g"⟩ [
              .mk "Z" [] (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", tS (V 2 "i"), zt, V 4 "pivot"]),
              .mk "S" [⟨7, "g2"⟩] (.seq (.call "swapS" [.borrow (dV 0 "v"), tS (V 2 "i"), tS (addTm (V 2 "i") (tS (V 7 "g2"))), u, u])
                (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", tS (V 2 "i"), tS (V 7 "g2"), V 4 "pivot"])) ]),
            .mk "False" [] (.call "partScanE" [.var ⟨0, "v"⟩, V 5 "k2", V 2 "i", tS (V 3 "g"), V 4 "pivot"]) ])) ] }

-- Exact BEq is out of reach (linear ids ≠ hand ids), but alphaEq reaches it:
example : (partScanEU.body == partScanEExpected.body) = false := by native_decide
example : Decl.alphaEq partScanEU partScanEExpected = true := by native_decide

/-! ## A proof-carrying body: `pivotPlaceH`'s `let p2 = le_rw_r … ;` (§ point 1)

The exact shape the brief names — `let p2b = le_rw_r … ; …`. Here the `S i`
branch derives its bound `p2 : Le (S (S i2)) (len *v)` by a `le_rw_r`/`id_sym`/
`le_add` proof spine, entirely in the unified body grammar (no splice). The
telescope carries an `Id`-typed hypothesis and the `back` is `baseBack` (a `natRec`
spine, spliced here via `%` — its surface expressibility was covered in the prior
phase). pivotPlaceH's ids coincide with pre-order, so this round-trips EXACTLY. -/

private def baseBackDef : Term :=
  .app (.app (.app (.app (.const "natRec") (.lam natT' listNatT')) (dV 0 "v"))
    (.lam natT' (.lam listNatT' (.app (.app (.app Dllbc.StdLemmas.swapL zt) (tS (.pvar 1))) (dV 0 "v"))))) (V 1 "i")

def pivotPlaceHU : Decl :=
  decl{ fn pivotPlaceH (v : &mut List Nat, i : Nat, g : Nat,
                        hlen : Id Nat (len *v) (S (add i g))) -> Unit
        back = %(baseBackDef)
        { match i {
            Z => (),
            S(i2) => {
              let p2 = le_rw_r (S (S i2)) (S (S (add i2 g))) (len *v)
                         (id_sym Nat (len *v) (S (S (add i2 g))) hlen)
                         (le_add i2 g);
              swapS(v, Z, S(i2), (), p2);
              ()
            }
        } } }

private def leRwR (a b c d e : Term) : Term := .app (.app (.app (.app (.app Dllbc.StdLemmas.le_rw_r a) b) c) d) e
private def idSym (t a b h : Term) : Term := .app (.app (.app (.app Dllbc.StdLemmas.id_sym t) a) b) h
private def leAdd (a b : Term) : Term := .app (.app Dllbc.StdLemmas.le_add a) b
private def lenT' (l : Term) : Term := Dllbc.Std.lenT l

-- Built via `Decl.mk` positionally: the surface keyword `back` reserves the token,
-- so a `{ … back := … }` structure literal cannot name the field here.
def pivotPlaceHExpected : Decl :=
  Dllbc.Decl.mk "pivotPlaceH"
    [("v", .borrowT listNatT' listNatT'), ("i", natT'), ("g", natT'),
     ("hlen", .idT natT' (lenT' (dV 0 "v")) (tS (addTm (V 1 "i") (V 2 "g"))))]
    (.const "Unit")
    (.matchE ⟨1, "i"⟩ [
      .mk "Z" [] .unit,
      .mk "S" [⟨4, "i2"⟩] (.letIn ⟨5, "p2"⟩
        (leRwR (tS (tS (V 4 "i2"))) (tS (tS (addTm (V 4 "i2") (V 2 "g")))) (lenT' (dV 0 "v"))
          (idSym natT' (lenT' (dV 0 "v")) (tS (tS (addTm (V 4 "i2") (V 2 "g")))) (V 3 "hlen"))
          (leAdd (V 4 "i2") (V 2 "g")))
        (.seq (.call "swapS" [.var ⟨0, "v"⟩, .ctorApp "Z" [], tS (V 4 "i2"), .unit, V 5 "p2"]) .unit)) ])
    (some baseBackDef)

-- Proof-carrying body, splice-free, EXACTLY the corpus (ids coincide with pre-order):
example : (pivotPlaceHU.body == pivotPlaceHExpected.body) = true := by native_decide
example : (pivotPlaceHU.telescope == pivotPlaceHExpected.telescope) = true := by native_decide
example : (pivotPlaceHU.back == pivotPlaceHExpected.back) = true := by native_decide
example : Decl.alphaEq pivotPlaceHU pivotPlaceHExpected = true := by native_decide

end Dllbc.Tests.SDeclUnified
