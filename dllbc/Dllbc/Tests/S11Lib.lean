import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.Migrate

/-!
# §11 test suite — the pure lift, `listRec`, and the quicksort pure library

Three kernel moves this milestone, then the library they exist to serve:

* **The pure lift (§1.3).** On the borrow-free fragment ⇒ coincides with ⇝ up to
  consumption: a body may ⇒-produce a comptime-only term (a proof — an
  eliminator application, `Refl`, a Π-typed λ) and store, pass, or return it as
  an ordinary datum. This finally expresses the M10 conflict discharge in the
  shape the fording spec wanted — a dead branch whose body is
  `botElim T (natNoConf p)`.
* **`listRec`** as the next recursor (ι-rules in the pure layer, `hasType`
  synthesis for its neutrals) — plus `natRec`/`boolRec` neutral synthesis and
  λ-vs-Π typing, which together let a Π-typed lemma type-check.
* **Pure `let` in `readC`** — un-deferred; proof terms name intermediates.

Then `Dllbc.Std`: `Le`, `eqb`/`leb`, `count`, `Bound`/`Sorted`, and the first
checked lemma `le_refl`. The predicates *compute* (smoke tests by conversion and
inhabitation), which is the whole point of large elimination.
-/

open Dllbc
open Dllbc.Std

namespace Dllbc.Tests.S11Lib

/-! ## §11.1 The pure lift — ⇒ produces proof terms

    Term-level fording vocabulary (the bodies below are hand-built `Term`s; the
    surface macro has no syntax for `j`/`app`/`const`). -/

-- SUBJECT: the §11 fording vocabulary and proofs (tZ/tS/natNoConfT/retRefl/jReflProof/
-- storeProof) are hand-built raw Terms — the surface has no syntax for `j`/`app`/`const`
-- and the j-spine `.pvar` motives cannot be reproduced by a named binder, so the raw
-- Terms are the subject (an accepted finding).
def natT : Term := .const "Nat"
def tZ : Term := .ctorApp "Z" []
def tS (t : Term) : Term := .ctorApp "S" [t]
def natRecT (P z s n : Term) : Term := .app (.app (.app (.app (.const "natRec") P) z) s) n
def jT (a aa P d b p : Term) : Term := .app (.app (.app (.app (.app (.app (.const "j") a) aa) P) d) b) p
def botElimT (t x : Term) : Term := .app (.app (.const "botElim") t) x
def zCaseT : Term := .lam natT (natRecT (.lam natT .type) (.const "Unit") (.lam natT (.lam .type (.const "Bot"))) (.pvar 0))
def sCaseT : Term := .lam natT (.lam (.pi natT .type) (.lam natT (natRecT (.lam natT .type) (.const "Bot") (.lam natT (.lam .type (.app (.pvar 3) (.pvar 1)))) (.pvar 0))))
def natCodeT : Term := .lam natT (natRecT (.lam natT (.pi natT .type)) zCaseT sCaseT (.pvar 0))
def natCodeApp (a b : Term) : Term := .app (.app natCodeT a) b
def nncMotiveT : Term := .lam natT (.lam (.idT natT tZ (.pvar 0)) (natCodeApp tZ (.pvar 1)))
-- SUBJECT: the no-confusion j-spine (raw Term; `.pvar` motive, no surface).
def natNoConfT (nE pE : Term) : Term := jT natT tZ nncMotiveT (.ctorApp "unit" []) (tS nE) pE

-- SUBJECT (raw proof Decl): Returning a proof — `Refl` at an Id-typed return (a `ctorApp`, lifts trivially).
def retRefl : Decl :=
  { name := "retRefl", retType := .idT natT (.var ⟨0, "a"⟩) (.var ⟨0, "a"⟩),
    telescope := [("a", natT)], body := .ctorApp "Refl" [] }
example : Migrate.progOkOf retRefl = true := by native_decide

-- SUBJECT (raw proof Decls): Storing a proof — a J-application (which ⇝-reduces to
-- `Refl`) is ⇒-lifted into a `Pair`'s dependent second field, audited against `Id Nat a a`.
def jReflProof (aE : Term) : Term :=
  jT natT aE (.lam natT (.lam (.idT natT aE (.pvar 1)) (.idT natT aE (.pvar 1)))) (.ctorApp "Refl" []) aE (.ctorApp "Refl" [])
def sigDiag : Term := .sigmaT natT (.idT natT (.pvar 0) (.pvar 0))     -- Σ(x:Nat). Id Nat x x
def storeProof : Decl :=
  { name := "storeProof", retType := sigDiag, telescope := [("a", natT)],
    body := .ctorApp "Pair" [.var ⟨0, "a"⟩, jReflProof (.var ⟨0, "a"⟩)] }
example : Migrate.progOkOf storeProof = true := by native_decide

-- The M10 conflict discharge, now as a dead branch in a checked fn (the shape
-- the fording spec originally wanted). The `False` arm holds `p : Id Nat Z (S n)`,
-- derives ⊥ via `natNoConf`, and ⇒-lifts `botElim Nat (…)` to close the branch.
def discharge : Decl :=
  { name := "discharge", retType := natT,
    telescope := [("n", natT), ("p", .idT natT tZ (tS (.var ⟨0, "n"⟩))), ("b", .const "Bool")],
    body := .matchE ⟨2, "b"⟩ none [ .mk "True" [] tZ,
              .mk "False" [] (botElimT natT (natNoConfT (.var ⟨0, "n"⟩) (.var ⟨1, "p"⟩))) ] }
example : Migrate.progOkOf discharge = true := by native_decide

/-! ## §11.2 The library computes (`listRec`/`natRec`/`boolRec` ι-rules) -/

example : (Val.convert 2000 (Le (ofNat 1) (ofNat 2)) unitTy) = true := by native_decide   -- 1 ≤ 2 ↦ ⊤
example : (Val.convert 2000 (Le (ofNat 2) (ofNat 1)) botTy) = true := by native_decide     -- 2 ≤ 1 ↦ ⊥
example : (Val.nfV 2000 (eqb (ofNat 2) (ofNat 2)) == tt) = true := by native_decide
example : (Val.nfV 2000 (eqb (ofNat 1) (ofNat 2)) == ff) = true := by native_decide
example : (Val.nfV 2000 (leb (ofNat 2) (ofNat 3)) == tt) = true := by native_decide
example : (Val.nfV 2000 (leb (ofNat 3) (ofNat 2)) == ff) = true := by native_decide
-- count 1 [1,2,1] ⇝ 2 (listRec threading a boolRec on eqb)
example : (Val.nfV 2000 (count (ofNat 1) (ofList [ofNat 1, ofNat 2, ofNat 1])) == ofNat 2) = true := by native_decide

/-! ## §11.3 The predicates by inhabitation, and the first lemma -/

-- `Le` decides order by inhabitation: ⋆ inhabits `Le 1 2` (= ⊤), not `Le 2 1` (= ⊥).
example : expectHasType [] [] star (Le (ofNat 1) (ofNat 2)) = true := by native_decide
example : expectHasType [] [] star (Le (ofNat 2) (ofNat 1)) = false := by native_decide

-- Sorted [1,2] whnf's to a product of ⊤s — a hand-built nest of unit-pairs
-- inhabits it; Sorted [2,1] contains ⊥ at the first bound, so the same term fails.
example : expectHasType [] [] (pairV star (pairV star star)) (Sorted (ofList [ofNat 1, ofNat 2])) = true := by
  native_decide
example : expectHasType [] [] (pairV star (pairV star star)) (Sorted (ofList [ofNat 2, ofNat 1])) = false := by
  native_decide

-- `le_refl : Π n. Le n n` — the first checked lemma, by `natRec`. Goes through by
-- the §11 recursor-neutral synthesis and λ-vs-Π typing.
example : expectHasType [] [] le_refl le_refl_ty = true := by native_decide

/-! ## §11.4 The naturalness probe — the quicksort program we WANT

    Per the north-star iteration policy: write the desired surface program first,
    annotate every line the current calculus/macro cannot yet express. This is
    the M12+ work-list. `NONE` = expressible today; `GAP[..]` = a missing rule or
    sugar, tagged with what it needs.

    ```
    -- A "mutable slice" is a fat pointer: a &mut List T plus a comptime length n.
    -- Element i lives at depth i; access/swap are nested reborrow cursors.

    fn swap (v : &mut List Nat, i : Nat, j : Nat)                 -- GAP[slice sig]: no fat-pointer/segment type; must be
        -> ()  { ... }                                           --   passed as (&mut List, Nat, Nat) with ↝-specs by hand
      -- body: walk two reborrow cursors to depths i and j, take both, cross-write
      -- NONE for the cursor walk itself (zero_all shows two live cursors work), BUT
      -- GAP[index-by-Nat]: no `v[i]` / "cursor at depth i"; each depth is a manual
      --   match Cons(h,t) => match t { ... } chain — no recursion-to-depth-n idiom.
      -- spec: Perm (count n) preserved. GAP[dependent call]: stating & USING
      --   count_swap : Π n. Id (count n before) (count n after) needs §5.3
      --   call-site instantiation (unimplemented) to apply the lemma at return.

    fn partition (v : &mut List Nat, n : Nat, pivot : Nat)       -- Lomuto, segment-scoped
        -> (k : Nat)  { ... }
      -- for i in 0..n: if leb v[i] pivot { swap(v, store, i); store += 1 }
      -- GAP[bounded loop]: no `for`/recursion-on-a-bound sugar; must be a manual
      --   recursive fn on the suffix reborrow with a decreasing Nat index [k] (§8).
      -- if leb a b { .. }:  GAP[bool guard]: `leb` reflects to Bool (have it), but
      --   there is no `if`; must be `match (leb a b) { True => .., False => .. }`
      --   — expressible, just unsugared.
      -- spec: SortedUpto/partitioned + Perm. GAP[segment specs]: `Bound`/`Sorted`
      --   restricted to `take n` and a ↝-obligation pinning `drop n` to entry —
      --   need Term-level Std at telescope positions (Std is Val-only today) and
      --   dependent instantiation to thread the counts.

    fn quicksort (v : &mut List Nat, n : Nat)                    -- the assembly
        -> ()  { if leb n 1 { () } else {
                   let k = partition(v, n, v[0]);
                   quicksort(&mut take k v, k);                  -- prefix: rides the bound
                   quicksort(&mut drop (k+1) v, n-k-1); } }      -- suffix: tail reborrow
      -- GAP[slice split]: `take k` / `drop (k+1)` as sub-slice reborrows are the
      --   core missing operation — a prefix rides the length bound (no borrow),
      --   a suffix is a reborrow at depth k+1. Neither has surface form yet.
      -- retType: Sorted (take n) × Perm entry. GAP[dependent call] again for the
      --   two recursive calls' specs to compose by transitivity.
    ```

    HEADLINE GAPS for M12+ (in dependency order): (1) dependent call-site
    instantiation (§5.3) — every lemma application and every spec-carrying call
    needs it; nothing downstream works without it. (2) Term-level `Std` at
    telescope positions (mechanical — reflect the Val library, or re-author as
    `Term`). (3) the two-cursor swap / access-at-depth-i idiom — the naturalness
    make-or-break. (4) sub-slice `take`/`drop` reborrows. (5) unsugared but
    present: `if` (bool-guard over `match`), bounded recursion.
-/

end Dllbc.Tests.S11Lib
