import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# The array flagship — an in-place quicksort over `Array n Nat`

**A consolidation bucket** (M28 D10). The suite grew one file per milestone, which
made a test's home a fact about WHEN it was written rather than about what it is
about. These files were merged here, in the order below, with their content moved
VERBATIM — every namespace kept, so every cross-file reference in the tree still
resolves, and each former file is fenced by a comment naming it so the git-log
archaeology survives:

  * `S25ArrSort.lean`

Each former file's `open`s are scoped by a `section`, so nothing leaks across the
seams.
-/

-- ┌── was `Dllbc/Tests/S25ArrSort.lean` ──────────────────────────────────────────────
section
/-!
# §25 test suite — the in-place array partition, and the array quicksort

¶6's migration completed: the leaf program ledger G4 says does not transfer, and the
assembly it feeds. `S24Arrays` established that every PIECE works (the carve, the
elementization, the transferred library, `sort2` as the whole stack at width two);
this file is the two programs those pieces were for.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeAddSucc LeTrans LeUpR LePredL
  LebTrueLe LebFalseGt AddSucc AddZero IdTrans IdCongr IdSym Znots
  SortedA UbA LbA CountA Asingle SortedArrCat CountArrCat UbPermA LbPermA
  NatRw NatRwTy LeZeroEq LeZeroEqTy SortedANil SortedANilTy
  SplitAL PartA SplitANil SplitANilTy
  SplitA0Lb SplitA0LbTy SplitACatE1 SplitACatE1Ty
  SplitACatI0 SplitACatI0Ty PartACatI0 PartACatI0Ty
  PartACatE0 PartACatE0Ty
  BumpN CountAconsCongr CountAconsCongrTy BumpComm BumpCommTy
  CountSwapA CountSwapATy
  SplitACatUb SplitACatUbTy SplitACatRest SplitACatRestTy
  SplitA1Head SplitA1HeadTy SplitA1Tail SplitA1TailTy
  PartACatUb PartACatUbTy PartACatRest PartACatRestTy
  PartA0Eq PartA0EqTy PartA0Lb PartA0LbTy SInj)

namespace Dllbc.Tests.S25ArrSort

/-- Type-check a closed term against a closed type in the pure seed (as §23/§24). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000 t

-- (`progMsg`, the debugging helper that printed a declaration's check message,
-- retired in M28 D9 with `Migrate.cohort`.)

/-! ## (i) The partition layer's predicates and their nil lemmas -/

example : chkL NatRw NatRwTy = true := by native_decide
example : chkL LeZeroEq LeZeroEqTy = true := by native_decide
example : chkL SortedANil SortedANilTy = true := by native_decide
example : chkL SplitANil SplitANilTy = true := by native_decide

-- The predicates COMPUTE on a run, at every skip count.
-- `SplitAL 3 2 [1,2,7]`: first two ≤ 3, last ≥ 3.
example : chkL prog{ Pair(unit, Pair(unit, Pair(unit, unit))) }
               prog{ SplitAL 3 2 3 Arr(1, 2, 7) } = true := by native_decide
-- …and it is NOT vacuous: the same array does not split at 1 (element 1 is `2 ≥ 3`? no).
example : chkL prog{ Pair(unit, Pair(unit, Pair(unit, unit))) }
               prog{ SplitAL 3 1 3 Arr(1, 2, 7) } = false := by native_decide

-- `PartA 3 2 [1,2,3,7]`: first two ≤ 3, element 2 IS 3, the rest ≥ 3.
example : chkL prog{ Pair(unit, Pair(unit, Pair(Refl, Pair(unit, unit)))) }
               prog{ PartA 3 2 4 Arr(1, 2, 3, 7) } = true := by native_decide
-- The pivot-identity conjunct is load-bearing: element 2 is 4, not 3.
example : chkL prog{ Pair(unit, Pair(unit, Pair(Refl, Pair(unit, unit)))) }
               prog{ PartA 3 2 4 Arr(1, 2, 4, 7) } = false := by native_decide

/-! ### Crossing a concatenation — each an induction on the left array alone -/

example : chkL SplitA0Lb SplitA0LbTy = true := by native_decide
example : chkL SplitACatE1 SplitACatE1Ty = true := by native_decide
example : chkL SplitACatI0 SplitACatI0Ty = true := by native_decide
example : chkL PartACatI0 PartACatI0Ty = true := by native_decide
example : chkL PartACatE0 PartACatE0Ty = true := by native_decide

/-! ### One conclusion each, so the programs need no inline `elim` -/

example : chkL SplitACatUb SplitACatUbTy = true := by native_decide
example : chkL SplitACatRest SplitACatRestTy = true := by native_decide
example : chkL SplitA1Head SplitA1HeadTy = true := by native_decide
example : chkL SplitA1Tail SplitA1TailTy = true := by native_decide
example : chkL PartACatUb PartACatUbTy = true := by native_decide
example : chkL PartACatRest PartACatRestTy = true := by native_decide
example : chkL PartA0Eq PartA0EqTy = true := by native_decide
example : chkL PartA0Lb PartA0LbTy = true := by native_decide

/-! ### The count layer for the swap -/

example : chkL CountAconsCongr CountAconsCongrTy = true := by native_decide
example : chkL BumpComm BumpCommTy = true := by native_decide
example : chkL CountSwapA CountSwapATy = true := by native_decide

-- There IS no η at length zero, which is why the nil lemmas exist at all: `SortedA Z`
-- of an opaque payload is a stuck `arrRec`, not `Unit`.
example : (Pure.nf 2000 prog{ SortedA Z Arr() } == .const "Unit")
    = true := by native_decide

/-! ## (ii) `splitA` — the scan

    `splitA(p, t)` rearranges `*t` in place so that its first `k` elements are ≤ `p`
    and the rest are ≥ `p`, and returns `k` with the right part's length.

    THE PROGRAM, and why it is this one. Peel the head, split the tail recursively, and
    then place the head:

      * head ≤ p — it belongs at the front, where it already is. NO WRITE.
      * head > p and the tail's left part is empty — it belongs at the back, and
        everything after it is already ≥ p. NO WRITE.
      * head > p with a non-empty left part `L` — the head must cross `L`. Swap it with
        `L`'s LAST element, which is ≤ p and lands at the front legitimately, while the
        head lands exactly at the new boundary. ONE swap, and the only one.

    Every element access is at index 0 of a segment the program carved, because there is
    no other kind: two independent symbolic indices into one array cannot both be
    reached (measured — after the first carve no evidence a program can hold selects a
    leaf for the second), so Lomuto's two-cursor scan is not writable and this shape is.
    ¶6's "the right sub-slice is a segment with its own zero" is a hard constraint here,
    not a convenience.

    PAIN DIARY — the staging tax, in its M23 form and for the M23 reason. `mkC` exists
    because the count conjunct must name the tail AS IT WAS AT ENTRY, and `*tl` denotes
    that only until the recursive call replaces it. Built while it is still live and
    applied afterwards. One builder, four arguments; M23's quicksort needed four
    builders. It would disappear under the filed `old`-for-consumed-things feature and
    does no mathematical work. -/

/-! ### The three telescopes' positional vocabulary and their return types

    A return type written outside its own header names parameters as `.var ⟨i, name⟩`
    (§5.2). Written out per twin rather than through a skeleton, which is M28 ψ's
    rule: for a SPEC lie the type IS the readable content, and each of these is one
    conjunct of a five-conjunct chain away from the honest form. -/

-- splitA:     fuel=0, m=1, hfuel=2, p=3, t=4
def mS : Term := .var ⟨1, "m"⟩
def pS : Term := .var ⟨3, "p"⟩
def tS : Term := .var ⟨4, "t"⟩
-- partitionA: fuel=0, n=1, hfuel=2, hne=3, a=4
def nP : Term := .var ⟨1, "n"⟩
def aP : Term := .var ⟨4, "a"⟩
-- quicksortA: fuel=0, n=1, hfuel=2, a=3
def nQ : Term := .var ⟨1, "n"⟩
def aQ : Term := .var ⟨3, "a"⟩
def fuelQ : Term := .var ⟨0, "fuel"⟩

def sHonest : Term := prog{
  Σ (k : Nat) → Σ (r : Nat)
    → Σ (Hlen : Id Nat %mS (Add k r))
    → Σ0 (Hsp : SplitAL %pS k %mS (*%tS))
    → Π (Q : Nat) → Id Nat (CountA Q %mS (*%tS)) (CountA Q %mS (old *%tS)) }

def pHonest : Term := prog{
  Σ (pvv : Nat) → Σ (k : Nat) → Σ (jj : Nat)
    → Σ (Hlen : Id Nat %nP (Add k (S jj)))
    → Σ0 (Hp : PartA pvv k %nP (*%aP))
    → Π (Q : Nat) → Id Nat (CountA Q %nP (*%aP)) (CountA Q %nP (old *%aP)) }

def qHonest : Term := prog{
  Σ0 (Hs : SortedA %nQ (*%aQ))
    → Π (Q : Nat) → Id Nat (CountA Q %nQ (*%aQ)) (CountA Q %nQ (old *%aQ)) }

def qSuffHonest : Term := prog{ Le %nQ %fuelQ }

/-! ## (iii) `partitionA` — the leaf ¶6's ledger counts as surviving, and G4 says is new

    `partitionA(a)` picks `a[0]` as the pivot, splits the tail around it, and swaps the
    pivot into its final position — returning that position, the right part's length,
    and `PartA`.

    IT IS NOT RECURSIVE, and it exists as a separate declaration for a reason that is
    the lane's sharpest structural finding: **the function boundary is load-bearing.**
    A body that has matched its own length `n` to `S m2` — which the head peel requires,
    since only `(*a)[Z ; 1 ; m2]` converts against the rigid extent — can no longer
    carve at a symbolic offset, because T2's rigid-length restriction now applies to
    the whole array. So the sort cannot both select a pivot and carve at the returned
    index. §6.2's opacity is the way out: a call re-mints the caller's payload as a
    FRESH σ at the declared type, so the array comes back UNCARVED and with a FLEX
    length — exactly the state the three-way carve needs. ¶5 advises "carve inline;
    reach for the function only when you want the abstraction boundary". Here the
    boundary is what makes the program possible at all. -/
/-! ## (iv) `quicksortA` — the headline

        fn quicksortA [fuel] (fuel : Nat, n : Nat, hfuel : Le n fuel, a : &mut (Array n Nat))
          -> Σ (hs : SortedA n (*a)) → Π x. Id Nat (CountA x n (*a)) (CountA x n (old *a))

    M23's quicksort signature, re-posed on arrays: sorted AND a permutation, over the
    exit snapshot, IN PLACE, with zero declared backs in the call tree. `partitionA`,
    `splitA` and the two recursive calls are each described only by their return type.

    EMPTINESS IS TESTED WITH `Leb 1 n`, NOT BY MATCHING `n`, and that is forced twice
    over. Matching would refine the length to `S m2`, and T2's rigid-extent restriction
    then blocks the three-way carve outright ("premise (3) is stuck"). And the `Z` branch
    could not be discharged anyway: there is no η at length zero, so `SortedA Z σ` is a
    stuck `arrRec` rather than `Unit`. The False branch instead turns `Le n Z` into
    `Id Nat n Z` (`LeZeroEq`) and feeds `SortedANil`.

    THE ONE STRUCTURAL FACT beyond composition is M23's, unchanged: BOUND SURVIVAL.
    `SortedArrCat` wants `UbA pv` of the SORTED left part, and the partition bounded it
    before the sort. `UbPermA`/`LbPermA` carry both bounds across their sorts' own
    count evidence. That is the keystone, transferred with the container in M24-ix, and
    it is the only place this proof is more than gluing.

    PAIN DIARY — three staged builders, and the reason is M23's exactly. `mkTop` is built
    BEFORE the partition call, because the count conjunct's far endpoint is `old *a` and a
    body cannot write that; capturing `*a` while it still IS the entry value is the dodge.
    `mkAD` and `mkS` are built after the carve and before the sorts, because both name the
    sub-slices AS THEY WERE when the partition bounded them, and the recursive calls
    replace those values. M23's list quicksort needed four builders for the same reason.
    Sixth filing for `old`-on-consumed-things; none of the three does mathematical work. -/

/-! ### THE CHAIN

    Three sealed `let`s and a tail (§8): `partitionA` calls `splitA`, `quicksortA`
    calls both, and each is in scope by being written above its caller. Four things
    vary — the three return types and `quicksortA`'s sufficiency hypothesis — which
    is every twin in this file except the BODY twin below, and that one cannot be
    shared at all (M28 D1's rule: a difference inside a body, at a subterm naming a
    binder the `fn` lowering mints an id for, has no splice that can reach it). -/

def arrUnder (sret pret qret qsuff tail : Term) : Term := prog{
  fn SplitA [fuel] (fuel : Nat, m : Nat, hfuel : Le m fuel, p : Nat, t : &mut (Array m Nat))
      -> %sret
      { match m {
          -- Empty. NOT `unit`: there is no η at length zero, so `SplitAL p Z Z σ` is a
          -- stuck `arrRec` and needs the nil lemma.
          Z => Pair(Z, Pair(Z, Pair(Refl,
                 Pair(SplitANil p Z Z (*t) Refl, λ (Q : Nat). Refl)))),
          S(m2) => match fuel {
            -- Out of fuel on a non-empty array: `hfuel : Le (S m2) Z` IS `Bot`.
            Z => botElim Unit hfuel,
            S(f2) => {
              -- The head peel. The residue is SUPPLIED (`; m2`) rather than minted:
              -- after `match m` the leaf's extent is the rigid `S m2`, and only the
              -- supplied form converts (`Add 1 m2 ⇝ S m2`). The index place `t[Z]`
              -- has no residue slot and is rejected here for exactly that reason.
              let hd = &m (*t)[Z ; 1 ; m2];
              let x = (*hd)[0];
              let tl = &m (*t)[S Z ; m2];
              -- Staged while `*tl` still denotes the ENTRY tail: rewrite the exit into
              -- the pre-swap state (`hsw`), then move that across the recursive call's
              -- own Count evidence (`hc`). Both non-swap branches pass `Refl` for the
              -- first leg.
              -- §2.4: the snapshots this builder was taking implicitly, named. The
              -- comment above already dates them ("staged while … still denotes"); the
              -- citation rule turns the date into a binding.
              let Tl0 = *tl;
              let X0 = x;
              let M2 = m2;
              let MkC = (λ (T2 : Array M2 Nat).
                  λ (Hc : Π (Q : Nat) → Id Nat (CountA Q M2 T2) (CountA Q M2 Tl0)).
                  λ (A2 : Array (S M2) Nat).
                  λ (Hsw : Π (Q : Nat) →
                        Id Nat (CountA Q (S M2) A2) (CountA Q (S M2) (acons M2 X0 T2))).
                    λ (Q : Nat).
                      IdTrans Nat (CountA Q (S M2) A2)
                                   (CountA Q (S M2) (acons M2 X0 T2))
                                   (CountA Q (S M2) (acons M2 X0 Tl0))
                        (Hsw Q) (CountAconsCongr Q X0 M2 T2 Tl0 (Hc Q)));
              let res = SplitA(f2, m2, hfuel, p, &m *tl);
              match res { Pair(k2, z1) => match z1 { Pair(r2, z2) => match z2 { Pair(Hlen2, z3) =>
              match z3 { Pair(Hsp2, Hcnt2) => {
                if e : Leb x p {
                  -- x ≤ p: the head is already in the left part; the boundary moves up.
                  Pair(S k2, Pair(r2,
                    Pair(IdCongr Nat Nat (λ (Z0 : Nat). S Z0) m2 (Add k2 r2) Hlen2,
                    Pair(Pair(LebTrueLe x p e, Hsp2),
                         MkC (*tl) Hcnt2 (acons m2 x (*tl)) (λ (Q : Nat). Refl)))))
                } else {
                  match k2 {
                    -- x > p with nothing to its left: the whole array is ≥ p already.
                    Z => Pair(Z, Pair(S r2,
                           Pair(IdCongr Nat Nat (λ (Z0 : Nat). S Z0) m2 (Add Z r2) Hlen2,
                           Pair(Pair(LePredL p x (LebFalseGt x p e), Hsp2),
                                MkC (*tl) Hcnt2 (acons m2 x (*tl)) (λ (Q : Nat). Refl))))),
                    -- x > p with a non-empty left part: THE SWAP. Three carves put the
                    -- left part, the boundary cell and the right part in three segments,
                    -- and the exchange is two writes at index 0 of two of them.
                    S(k3) => {
                      -- The decomposition is DECLARED: premise (3) may not refine
                      -- `m2` by unification, so the equation the recursive call
                      -- returned is cited and solved along. `AddSucc` is the whole
                      -- distance between what the callee proved and what the carve
                      -- asks for.
                      let Hdec = IdTrans Nat m2 (S (Add k3 r2)) (Add k3 (S r2)) Hlen2
                                   (IdSym Nat (Add k3 (S r2)) (S (Add k3 r2))
                                      (AddSucc k3 r2));
                      let lo = &m (*tl)[Z ; k3 ; S r2 | LeAdd k3 (S r2) | Hdec];
                      let mid = &m (*tl)[k3 ; 1 ; r2];
                      let hi = &m (*tl)[S k3 ; r2];
                      let y = (*mid)[0];
                      (*mid)[0] := x;
                      (*hd)[0] := y;
                      let Hrest = SplitACatRest p k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                      let Hy = SplitA1Head p r2 (*hi) y Hrest;
                      let Hub = SplitACatUb p k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                      let Hg = SplitA1Tail p r2 (*hi) y Hrest;
                      let Hnew = SplitACatI0 p k3 (S r2) (*lo) (acons r2 x (*hi)) Hub
                                   (Pair(LePredL p x (LebFalseGt x p e), Hg));
                      let cnt = MkC (arrCat k3 (S r2) (*lo) (acons r2 y (*hi))) Hcnt2
                                    (acons m2 y (arrCat k3 (S r2) (*lo) (acons r2 x (*hi))))
                                    (λ (Q : Nat). CountSwapA Q x y k3 (*lo) r2 (*hi));
                      Pair(S k3, Pair(S r2, Pair(Refl, Pair(Pair(Hy, Hnew), cnt))))
                    }
                  }
                }
              } } } } }
            }
          }
        } };
  fn PartitionA (fuel : Nat, n : Nat, hfuel : Le n fuel, Hne : Le (S Z) n,
                 a : &mut (Array n Nat))
      -> %pret
      { match n {
          -- An empty array has no pivot, so the caller owes `Le 1 n`; here it IS `Bot`.
          Z => botElim Unit Hne,
          S(m2) => {
            let hd = &m (*a)[Z ; 1 ; m2];
            let x = (*hd)[0];
            let tl = &m (*a)[S Z ; m2];
            -- §2.4: the snapshots this builder was taking implicitly, named. The
            -- comment above already dates them ("staged while … still denotes"); the
            -- citation rule turns the date into a binding.
            let Tl0 = *tl;
            let X0 = x;
            let M2 = m2;
            let MkC = (λ (T2 : Array M2 Nat).
                λ (Hc : Π (Q : Nat) → Id Nat (CountA Q M2 T2) (CountA Q M2 Tl0)).
                λ (A2 : Array (S M2) Nat).
                λ (Hsw : Π (Q : Nat) →
                      Id Nat (CountA Q (S M2) A2) (CountA Q (S M2) (acons M2 X0 T2))).
                  λ (Q : Nat).
                    IdTrans Nat (CountA Q (S M2) A2)
                                 (CountA Q (S M2) (acons M2 X0 T2))
                                 (CountA Q (S M2) (acons M2 X0 Tl0))
                      (Hsw Q) (CountAconsCongr Q X0 M2 T2 Tl0 (Hc Q)));
            let res = SplitA(fuel, m2, LePredL m2 fuel hfuel, x, &m *tl);
            match res { Pair(k2, z1) => match z1 { Pair(r2, z2) => match z2 { Pair(Hlen2, z3) =>
            match z3 { Pair(Hsp2, Hcnt2) => {
              match k2 {
                -- Nothing is ≤ the pivot, so the pivot is already in its final place at
                -- index 0. `PartA`'s identity conjunct is `Refl` and its lower bound is
                -- the split's own invariant, crossed by `SplitA0Lb`.
                Z => Pair(x, Pair(Z, Pair(m2,
                       Pair(Refl,
                       Pair(Pair(Refl, SplitA0Lb x m2 (*tl) Hsp2),
                            MkC (*tl) Hcnt2 (acons m2 x (*tl)) (λ (Q : Nat). Refl)))))),
                -- The pivot must cross the left part: swap it with that part's LAST
                -- element. The displaced element is ≤ the pivot, so it may sit at the
                -- front; the pivot lands at index `S k3`, which is the boundary.
                S(k3) => {
                  let Hdec = IdTrans Nat m2 (S (Add k3 r2)) (Add k3 (S r2)) Hlen2
                               (IdSym Nat (Add k3 (S r2)) (S (Add k3 r2))
                                  (AddSucc k3 r2));
                  let lo = &m (*tl)[Z ; k3 ; S r2 | LeAdd k3 (S r2) | Hdec];
                  let mid = &m (*tl)[k3 ; 1 ; r2];
                  let hi = &m (*tl)[S k3 ; r2];
                  let y = (*mid)[0];
                  (*mid)[0] := x;
                  (*hd)[0] := y;
                  let Hrest = SplitACatRest x k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                  let Hy = SplitA1Head x r2 (*hi) y Hrest;
                  let Hub = SplitACatUb x k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                  let Hg = SplitA1Tail x r2 (*hi) y Hrest;
                  let Hnew = PartACatI0 x k3 (S r2) (*lo) (acons r2 x (*hi)) Hub
                               (Pair(Refl, SplitA0Lb x r2 (*hi) Hg));
                  let cnt = MkC (arrCat k3 (S r2) (*lo) (acons r2 y (*hi))) Hcnt2
                                (acons m2 y (arrCat k3 (S r2) (*lo) (acons r2 x (*hi))))
                                (λ (Q : Nat). CountSwapA Q x y k3 (*lo) r2 (*hi));
                  Pair(x, Pair(S k3, Pair(r2, Pair(Refl, Pair(Pair(Hy, Hnew), cnt)))))
                }
              }
            } } } } }
          }
        } };
  fn QuicksortA [fuel] (fuel : Nat, n : Nat, hfuel : %qsuff, a : &mut (Array n Nat))
      -> %qret
      { if he : Leb 1 n {
          match fuel {
            -- `Le 1 n` and `Le n Z` compose to `Le 1 Z`, which IS `Bot`.
            Z => botElim Unit (LeTrans (S Z) n Z (LebTrueLe 1 n he) hfuel),
            S(f2) => {
              -- Staged while `*a` still denotes the ENTRY array: the Count chain's far
              -- endpoint is `old *a`, which no body term can name.
              -- §2.4: the snapshots this builder was taking implicitly, named. The
              -- comment above already dates them ("staged while … still denotes"); the
              -- citation rule turns the date into a binding.
              let A0 = *a;
              let N0 = n;
              let MkTop = (λ (Dv : Array N0 Nat).
                  λ (Hd : Π (Q : Nat) → Id Nat (CountA Q N0 Dv) (CountA Q N0 A0)).
                  λ (Av : Array N0 Nat).
                  λ (Had : Π (Q : Nat) → Id Nat (CountA Q N0 Av) (CountA Q N0 Dv)).
                    λ (Q : Nat).
                      IdTrans Nat (CountA Q N0 Av) (CountA Q N0 Dv) (CountA Q N0 A0)
                        (Had Q) (Hd Q));
              -- `hfuel` is a PROOF, so passing it to the partition MOVES it. Both
              -- sufficiency bounds are therefore staged over it first — the same
              -- capture-before-consume dodge M23 uses for a consumed `rest`.
              -- §2.4: the snapshots this builder was taking implicitly, named. The
              -- comment above already dates them ("staged while … still denotes"); the
              -- citation rule turns the date into a binding.
              let Hfuel0 = hfuel;
              let N0 = n;
              let F2 = f2;
              let MkHf = (λ (Kv : Nat). λ (H : Le (S Kv) N0).
                            LeTrans (S Kv) N0 (S F2) H Hfuel0);
              let pr = PartitionA(S(f2), n, hfuel, LebTrueLe 1 n he, &m *a);
              match pr { Pair(pvv, w1) => match w1 { Pair(k, w2) => match w2 { Pair(jj, w3) =>
              match w3 { Pair(Hlen, w4) => match w4 { Pair(Hp, Hcnt) => {
                -- ¶6's three-way carve, at the index the partition just returned. The
                -- first obligation is `LeAdd`; the second is `Le 1 (S jj)`, which route
                -- (a) reduces to ⊤; the third is degenerate.
                let l = &m (*a)[Z ; k ; S jj | LeAdd k (S jj) | Hlen];
                let pcell = &m (*a)[k ; 1 ; jj];
                let e = (*pcell)[0];
                let r = &m (*a)[S k ; jj];
                let Hub = PartACatUb pvv k (S jj) (*l) (acons jj e (*r)) Hp;
                let Hrest = PartACatRest pvv k (S jj) (*l) (acons jj e (*r)) Hp;
                let Heq = PartA0Eq pvv jj (*r) e Hrest;
                let Hlb = PartA0Lb pvv jj (*r) e Hrest;
                let top1 = MkTop (arrCat k (S jj) (*l) (acons jj e (*r))) Hcnt;
                -- The glue, staged: both bounds are about to be invalidated as VALUES by
                -- the recursive sorts, so their transports are set up now.
                -- §2.4: the snapshots this builder was taking implicitly, named. The
                -- comment above already dates them ("staged while … still denotes"); the
                -- citation rule turns the date into a binding.
                let L0 = *l;
                let R0 = *r;
                let Pvv0 = pvv;
                let E0 = e;
                let Heq0 = Heq;
                let Hub0 = Hub;
                let Hlb0 = Hlb;
                let K0 = k;
                let Jj0 = jj;
                let MkS = (λ (L2 : Array K0 Nat). λ (R2 : Array Jj0 Nat).
                    λ (H1 : Π (Q : Nat) → Id Nat (CountA Q K0 L2) (CountA Q K0 L0)).
                    λ (H2 : Π (Q : Nat) → Id Nat (CountA Q Jj0 R2) (CountA Q Jj0 R0)).
                    λ (Hs1 : SortedA K0 L2). λ (Hs2 : SortedA Jj0 R2).
                      NatRw (λ (Z0 : Nat). SortedA (Add K0 (S Jj0))
                                  (arrCat K0 (S Jj0) L2 (arrCat 1 Jj0 (Asingle Z0) R2)))
                        Pvv0 E0 (IdSym Nat E0 Pvv0 Heq0)
                        (SortedArrCat Pvv0 K0 L2 Jj0 R2 Hs1
                           (UbPermA Pvv0 K0 L2 K0 L0 H1 Hub0) Hs2
                           (LbPermA Pvv0 Jj0 R2 Jj0 R0 H2 Hlb0)));
                -- §2.4: the snapshots this builder was taking implicitly, named. The
                -- comment above already dates them ("staged while … still denotes"); the
                -- citation rule turns the date into a binding.
                let L0 = *l;
                let R0 = *r;
                let E0 = e;
                let K0 = k;
                let Jj0 = jj;
                let MkAD = (λ (L2 : Array K0 Nat). λ (R2 : Array Jj0 Nat).
                    λ (H1 : Π (Q : Nat) → Id Nat (CountA Q K0 L2) (CountA Q K0 L0)).
                    λ (H2 : Π (Q : Nat) → Id Nat (CountA Q Jj0 R2) (CountA Q Jj0 R0)).
                      λ (Q : Nat).
                        IdTrans Nat
                          (CountA Q (Add K0 (S Jj0)) (arrCat K0 (S Jj0) L2 (acons Jj0 E0 R2)))
                          (Add (CountA Q K0 L0) (CountA Q (S Jj0) (acons Jj0 E0 R0)))
                          (CountA Q (Add K0 (S Jj0)) (arrCat K0 (S Jj0) L0 (acons Jj0 E0 R0)))
                          (IdTrans Nat
                            (CountA Q (Add K0 (S Jj0)) (arrCat K0 (S Jj0) L2 (acons Jj0 E0 R2)))
                            (Add (CountA Q K0 L2) (CountA Q (S Jj0) (acons Jj0 E0 R2)))
                            (Add (CountA Q K0 L0) (CountA Q (S Jj0) (acons Jj0 E0 R0)))
                            (CountArrCat Q K0 L2 (S Jj0) (acons Jj0 E0 R2))
                            (IdTrans Nat
                              (Add (CountA Q K0 L2) (CountA Q (S Jj0) (acons Jj0 E0 R2)))
                              (Add (CountA Q K0 L0) (CountA Q (S Jj0) (acons Jj0 E0 R2)))
                              (Add (CountA Q K0 L0) (CountA Q (S Jj0) (acons Jj0 E0 R0)))
                              (IdCongr Nat Nat
                                (λ (C : Nat). Add C (CountA Q (S Jj0) (acons Jj0 E0 R2)))
                                (CountA Q K0 L2) (CountA Q K0 L0) (H1 Q))
                              (IdCongr Nat Nat
                                (λ (C : Nat). Add (CountA Q K0 L0) C)
                                (CountA Q (S Jj0) (acons Jj0 E0 R2))
                                (CountA Q (S Jj0) (acons Jj0 E0 R0))
                                (CountAconsCongr Q E0 Jj0 R2 R0 (H2 Q)))))
                          (IdSym Nat
                            (CountA Q (Add K0 (S Jj0)) (arrCat K0 (S Jj0) L0 (acons Jj0 E0 R0)))
                            (Add (CountA Q K0 L0) (CountA Q (S Jj0) (acons Jj0 E0 R0)))
                            (CountArrCat Q K0 L0 (S Jj0) (acons Jj0 E0 R0))));
                -- Sufficiency: the pivot sits strictly inside, so both halves are
                -- strictly shorter. `LeAddSucc` and `LeAddL` are the two sides of
                -- that, and each composes with this frame's own bound.
                let hf1 = MkHf k (LeAddSucc k jj);
                let s1 = QuicksortA(f2, k, hf1, &m *l);
                match s1 { Pair(Hs1, Hc1) => {
                  let hf2 = MkHf jj (LeAddL (S jj) k);
                  let s2 = QuicksortA(f2, jj, hf2, &m *r);
                  match s2 { Pair(Hs2, Hc2) => {
                    Pair(MkS (*l) (*r) Hc1 Hc2 Hs1 Hs2,
                         top1 (arrCat k (S jj) (*l) (acons jj e (*r))) (MkAD (*l) (*r) Hc1 Hc2))
                  } }
                } }
              } } } } } }
            }
          }
        } else {
          -- `n` is zero: the array is empty, and BOTH conjuncts are about an opaque
          -- payload, so the Count is `Refl` and the sortedness is the nil lemma.
          Pair(SortedANil n (*a) (LeZeroEq n (LebFalseGt (S Z) n he)),
               λ (Q : Nat). Refl)
        } };
  %tail }

/-- THE HEADLINE: the array flagship checks as ONE program, against no table.
    `quicksortA` is the array era's in-place scan — it carves, swaps through element
    borrows, and returns an index. It shares no code with `S23Direct`'s list
    quicksort: not the program, not the predicates, not the partition, not the
    container. -/
def arrChain : Term := arrUnder sHonest pHonest qHonest qSuffHonest .unit
example : progOk arrChain = true := by native_decide


/-! ## (v) Not vacuous — a lying twin per conjunct

    Each return type is the ONLY description of its function, so each conjunct gets a
    twin that changes exactly it, built by taking the `retType` off a lying header with
    the same telescope so the body is shared verbatim and the lie is the only variable.
    M23's discipline, applied to three declarations. -/

-- `splitA`, conjunct 1: the length accounting says the two parts overlap by one.
example : progOk (arrUnder (prog{
    Σ (k : Nat) → Σ (r : Nat)
      → Σ (Hlen : Id Nat %mS (Add k (S r)))
      → Σ0 (Hsp : SplitAL %pS k %mS (*%tS))
      → Π (Q : Nat) → Id Nat (CountA Q %mS (*%tS)) (CountA Q %mS (old *%tS)) })
    pHonest qHonest qSuffHonest .unit) = false := by native_decide

-- `splitA`, conjunct 2: the ordering claimed of the ENTRY array rather than the exit.
example : progOk (arrUnder (prog{
    Σ (k : Nat) → Σ (r : Nat)
      → Σ (Hlen : Id Nat %mS (Add k r))
      → Σ0 (Hsp : SplitAL %pS k %mS (old *%tS))
      → Π (Q : Nat) → Id Nat (CountA Q %mS (*%tS)) (CountA Q %mS (old *%tS)) })
    pHonest qHonest qSuffHonest .unit) = false := by native_decide

-- `splitA`, conjunct 3: the counts off by one, which no path can reach.
example : progOk (arrUnder (prog{
    Σ (k : Nat) → Σ (r : Nat)
      → Σ (Hlen : Id Nat %mS (Add k r))
      → Σ0 (Hsp : SplitAL %pS k %mS (*%tS))
      → Π (Q : Nat) → Id Nat (CountA Q %mS (*%tS)) (S (CountA Q %mS (old *%tS))) })
    pHonest qHonest qSuffHonest .unit) = false := by native_decide

/-- **The BODY twin, and the one that matters most**: the swap is DELETED — the branch
    reads the two cells and writes neither, but claims the same postcondition. Every
    spec twin above can be blamed on some path; this one is wrong only on the swap
    path and only because the elements did not move. It isolates the single mutation
    the whole program performs.

    Transcribed rather than shared through the chain, and that is M28 D1's rule
    rather than a choice: what varies is inside the body, at a statement naming
    binders the `fn` lowering mints ids for. It carries only `splitA`, since nothing
    else is needed to refuse it. -/
def splitANoSwap : Term := prog{
  fn SplitA [fuel] (fuel : Nat, m : Nat, hfuel : Le m fuel, p : Nat, t : &mut (Array m Nat))
      -> %sHonest
      { match m {
          Z => Pair(Z, Pair(Z, Pair(Refl,
                 Pair(SplitANil p Z Z (*t) Refl, λ (Q : Nat). Refl)))),
          S(m2) => match fuel {
            Z => botElim Unit hfuel,
            S(f2) => {
              let hd = &m (*t)[Z ; 1 ; m2];
              let x = (*hd)[0];
              let tl = &m (*t)[S Z ; m2];
              -- §2.4: the snapshots this builder was taking implicitly, named. The
              -- comment above already dates them ("staged while … still denotes"); the
              -- citation rule turns the date into a binding.
              let Tl0 = *tl;
              let X0 = x;
              let M2 = m2;
              let MkC = (λ (T2 : Array M2 Nat).
                  λ (Hc : Π (Q : Nat) → Id Nat (CountA Q M2 T2) (CountA Q M2 Tl0)).
                  λ (A2 : Array (S M2) Nat).
                  λ (Hsw : Π (Q : Nat) →
                        Id Nat (CountA Q (S M2) A2) (CountA Q (S M2) (acons M2 X0 T2))).
                    λ (Q : Nat).
                      IdTrans Nat (CountA Q (S M2) A2)
                                   (CountA Q (S M2) (acons M2 X0 T2))
                                   (CountA Q (S M2) (acons M2 X0 Tl0))
                        (Hsw Q) (CountAconsCongr Q X0 M2 T2 Tl0 (Hc Q)));
              let res = splitANoSwap(f2, m2, hfuel, p, &m *tl);
              match res { Pair(k2, z1) => match z1 { Pair(r2, z2) => match z2 { Pair(Hlen2, z3) =>
              match z3 { Pair(Hsp2, Hcnt2) => {
                if e : Leb x p {
                  Pair(S k2, Pair(r2,
                    Pair(IdCongr Nat Nat (λ (Z0 : Nat). S Z0) m2 (Add k2 r2) Hlen2,
                    Pair(Pair(LebTrueLe x p e, Hsp2),
                         MkC (*tl) Hcnt2 (acons m2 x (*tl)) (λ (Q : Nat). Refl)))))
                } else {
                  match k2 {
                    Z => Pair(Z, Pair(S r2,
                           Pair(IdCongr Nat Nat (λ (Z0 : Nat). S Z0) m2 (Add Z r2) Hlen2,
                           Pair(Pair(LePredL p x (LebFalseGt x p e), Hsp2),
                                MkC (*tl) Hcnt2 (acons m2 x (*tl)) (λ (Q : Nat). Refl))))),
                    S(k3) => {
                      -- The decomposition is DECLARED: premise (3) may not refine
                      -- `m2` by unification, so the equation the recursive call
                      -- returned is cited and solved along. `AddSucc` is the whole
                      -- distance between what the callee proved and what the carve
                      -- asks for.
                      let Hdec = IdTrans Nat m2 (S (Add k3 r2)) (Add k3 (S r2)) Hlen2
                                   (IdSym Nat (Add k3 (S r2)) (S (Add k3 r2))
                                      (AddSucc k3 r2));
                      let lo = &m (*tl)[Z ; k3 ; S r2 | LeAdd k3 (S r2) | Hdec];
                      let mid = &m (*tl)[k3 ; 1 ; r2];
                      let hi = &m (*tl)[S k3 ; r2];
                      let y = (*mid)[0];
                      let Hrest = SplitACatRest p k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                      let Hy = SplitA1Head p r2 (*hi) y Hrest;
                      let Hub = SplitACatUb p k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                      let Hg = SplitA1Tail p r2 (*hi) y Hrest;
                      let Hnew = SplitACatI0 p k3 (S r2) (*lo) (acons r2 x (*hi)) Hub
                                   (Pair(LePredL p x (LebFalseGt x p e), Hg));
                      let cnt = MkC (arrCat k3 (S r2) (*lo) (acons r2 y (*hi))) Hcnt2
                                    (acons m2 y (arrCat k3 (S r2) (*lo) (acons r2 x (*hi))))
                                    (λ (Q : Nat). CountSwapA Q x y k3 (*lo) r2 (*hi));
                      Pair(S k3, Pair(S r2, Pair(Refl, Pair(Pair(Hy, Hnew), cnt))))
                    }
                  }
                }
              } } } } }
            }
          }
        } };
  () }
example : progOk splitANoSwap = false := by native_decide

-- `partitionA`, conjunct 1: the length accounting forgets the pivot cell.
example : progRejects (arrUnder sHonest (prog{
    Σ (pvv : Nat) → Σ (k : Nat) → Σ (jj : Nat)
      → Σ (Hlen : Id Nat %nP (Add k jj))
      → Σ0 (Hp : PartA pvv k %nP (*%aP))
      → Π (Q : Nat) → Id Nat (CountA Q %nP (*%aP)) (CountA Q %nP (old *%aP)) })
    qHonest qSuffHonest .unit) "does not have return type" = true := by native_decide

-- `partitionA`, conjunct 2: the partition claimed of the ENTRY array.
example : progRejects (arrUnder sHonest (prog{
    Σ (pvv : Nat) → Σ (k : Nat) → Σ (jj : Nat)
      → Σ (Hlen : Id Nat %nP (Add k (S jj)))
      → Σ0 (Hp : PartA pvv k %nP (old *%aP))
      → Π (Q : Nat) → Id Nat (CountA Q %nP (*%aP)) (CountA Q %nP (old *%aP)) })
    qHonest qSuffHonest .unit) "does not have return type" = true := by native_decide

-- `quicksortA`, conjunct 1: sortedness lied onto the ENTRY. True at the empty array,
-- so the base path still passes and only the recursive one is blamed.
--
-- **The needle MOVED at M33a** (both of these), and the verdict did not. With
-- `Hs` capital the sortedness component is ⇝-read at `readResult`, so the lie is
-- caught where it is WRITTEN — at this body's own return — instead of one call
-- later, where the caller found the argument ill-typed. Was "does not have its
-- parameter type"; the two Direct.lean twins of these did not move, because
-- quicksort's own caller re-checks the conjunct either way.
example : progRejects (arrUnder sHonest pHonest (prog{
    Σ0 (Hs : SortedA %nQ (old *%aQ))
      → Π (Q : Nat) → Id Nat (CountA Q %nQ (*%aQ)) (CountA Q %nQ (old *%aQ)) })
    qSuffHonest .unit) "does not have return type" = true := by native_decide

-- `quicksortA`, conjunct 2: the permutation lied by DIRECTION. Again `Refl` at the
-- empty array, and again the body's evidence points the other way once anything moves.
example : progRejects (arrUnder sHonest pHonest (prog{
    Σ0 (Hs : SortedA %nQ (*%aQ))
      → Π (Q : Nat) → Id Nat (CountA Q %nQ (old *%aQ)) (CountA Q %nQ (*%aQ)) })
    qSuffHonest .unit) "does not have return type" = true := by native_decide

/-! ### Honest typing rejections, probed through `checkFn` -/

-- The three-way carve's ONE cited obligation is load-bearing: drop `LeAdd` and the
-- carve has nothing to select a leaf with. (The pivot carve needs no evidence at all —
-- route (a) reduces `Le 1 (S jj)` to ⊤ — so this is the only citation in the body.)
def carveNoEv : Term := prog{
  fn CarveNoEv (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k ; S jj];
    let pcell = &m (*a)[k ; 1 ; jj];
    let r = &m (*a)[S k ; ..];
    () };
  () }
example : progRejects carveNoEv "may not impose it by refining" = true := by native_decide

-- …and the positive control at the same shape, so the rejection is about the missing
-- citation and not about the carve. (`quicksortA` itself is the other positive control.)
def carveWithEv : Term := prog{
  fn CarveWithEv (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                  a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k ; S jj | LeAdd k (S jj) | Heq];
    let pcell = &m (*a)[k ; 1 ; jj];
    let r = &m (*a)[S k ; ..];
    () };
  () }
example : progOk carveWithEv = true := by native_decide

-- The sufficiency hypothesis is load-bearing, not decoration: keep the parameter (so
-- the body still elaborates and the rejection is about TYPING) and weaken it to `Unit`.
-- The out-of-fuel path then has no ⊥ to eliminate and stops being dead.
example : progRejects (arrUnder sHonest pHonest qHonest (prog{ Unit }) .unit)
  "botElim" = true := by native_decide


/-! ## (vi) The EXECUTING differential — and the divergence it found

    `Migrate.progOkOf` proves `Sorted ∧ Perm` symbolically. Running the SAME declarations on
    concrete arrays is the control that can still indict them, and here it indicts the
    MACHINE instead: the concrete and symbolic executions of a carving callee diverge,
    for a reason no symbolic check can produce. Everything below is stated so that the
    day the gap closes, this section goes red and has to be updated.

    THE GAP, minimally: **a callee's segment borrows are never released when it
    returns**, so in executing mode the caller's array stays carved with the callee's
    dead markers. `mergeArrays` cannot rejoin it (a loan blocks the merge, ledger R4),
    so the caller's next carve sees the callee's leftover segmentation instead of one
    leaf, and premise (3) tries to unify the wrong extent.

    In CHECKING mode this is invisible, and invisible for a principled reason: §6.2's
    opacity re-mints the callee's payload as a fresh σ at the declared type, so the
    caller always sees an UNCARVED array. That re-minting is not merely an
    approximation of what the concrete machine does — it is a REPAIR of it. This is a
    new instance of the over-approximation §6.1 already flags ("a group releases
    atomically where the concrete machine ends lazily"), and it is the first one where
    the concrete side is the one that is wrong. -/

def tnatT : Nat → Term | 0 => .ctorApp "Z" [] | k + 1 => .ctorApp "S" [tnatT k]
def tarrT (l : List Nat) : Term := .ctorApp "Arr" (l.map tnatT)

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

def listOfV : Nat → Val → Option (List Nat)
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Nil", []), _ => some []
    | some ("Cons", [h, t]), f' + 1 =>
      match natOfV 2000 h, listOfV f' t with
      | some x, some xs => some (x :: xs)
      | _, _ => none
    | _, _ => none

def arrOfV : Val → Option (List Nat)
  | v => match Val.asCtor? v with
    | some ("Arr", vs) => vs.mapM (natOfV 2000)
    | _ => none

/-- Build the array, borrow it, sort it in place, read it back. `hfuel` is `Le n n`,
    which computes to `Unit` at a concrete length. -/
def qsCallerA (l : List Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tarrT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "QuicksortA" [tnatT l.length, tnatT l.length, .unit, .var ⟨1, "b"⟩])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))

/-- `splitA` alone, so the divergence can be exhibited one call deep instead of three. -/
def splCaller (l : List Nat) (pvt : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tarrT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.letIn ⟨2, "r"⟩ (.call "SplitA"
          [tnatT l.length, tnatT l.length, .unit, tnatT pvt, .var ⟨1, "b"⟩])
        (.letIn ⟨3, "y"⟩ (.var ⟨0, "z"⟩) .unit)))

def runQsA (l : List Nat) : Option (List Nat) :=
  match Dllbc.Tests.S9Diff.runExec (arrUnder sHonest pHonest qHonest qSuffHonest (qsCallerA l)) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

def runSplA (l : List Nat) (pvt : Nat) : Option (List Nat) :=
  match Dllbc.Tests.S9Diff.runExec (arrUnder sHonest pHonest qHonest qSuffHonest (splCaller l pvt)) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

def sortedRef (l : List Nat) : List Nat := l.mergeSort (fun a b => a <= b)

/-- Did it run at all — used by the G7 probes below, where the point is acceptance and
    execution agreeing rather than the value. -/
def runsAtAll (t : Term) : Bool :=
  match Dllbc.Tests.S9Diff.runExec t with | .ok _ => true | .error _ => false

/-! ### (vi.a) It really sorts, in place, on concrete arrays

    The same declarations `Migrate.progOkOf` verified symbolically, run on real inputs and
    compared against a trusted sort. Duplicates, already-sorted and reverse-sorted
    included, since the empty-part paths are where a partition-based sort breaks. -/

/-! ### (vi.a) What DOES run, and it is not nothing

    Every execution that does not re-enter a carve after returning from a carving callee
    is correct — the programs really do move elements, in place, to the right places. -/

-- `splitA` on two elements: the pivot-crossing SWAP branch, EXECUTING. `[3,1]` at
-- `p = 2` must come back `[1,3]` — the head crossed the boundary and the boundary
-- element crossed back, which is the program's one mutation.
example : runSplA [3, 1] 2 == some [1, 3] := by native_decide
-- …and both no-write branches.
example : runSplA [1, 3] 2 == some [1, 3] := by native_decide
example : runSplA [1] 2 == some [1] := by native_decide
example : runSplA [3] 2 == some [3] := by native_decide
example : runSplA [] 2 == some [] := by native_decide

-- `quicksortA`, executing, at the sizes that do not re-enter a carve after a call.
example : runQsA [] == some (sortedRef []) := by native_decide
example : runQsA [1] == some (sortedRef [1]) := by native_decide

/-! ### (vi.b) G5 CLOSED — the executing differential, deep

    The divergence this section used to pin is gone. It was `Drop-empty`, in THREE
    independent sites, and the ledger's G5 entry records each; the last of them is that a
    ZERO-WIDTH request must not select the leaf it abuts, because `Le (Add lo Z) (Add b m)`
    holds at a leaf's far end and the ordinary selection then demand-ends the live borrow
    pinned there. All three are unreachable symbolically — a residue σ is never known to be
    zero — and routine concretely, which is exactly why only an executing differential
    could find them and why the checking side was right all along.

    What used to be `runsAtAll … = false` is now the real thing. -/

example : runQsA [2, 1] == some (sortedRef [2, 1]) := by native_decide
example : runQsA [3, 1, 2] == some (sortedRef [3, 1, 2]) := by native_decide
example : runQsA [1, 2, 3] == some (sortedRef [1, 2, 3]) := by native_decide
example : runQsA [3, 2, 1] == some (sortedRef [3, 2, 1]) := by native_decide
example : runQsA [5, 5, 5] == some (sortedRef [5, 5, 5]) := by native_decide
example : runQsA [4, 1, 3, 2, 5] == some (sortedRef [4, 1, 3, 2, 5]) := by native_decide
example : runQsA [3, 1, 4, 1, 5, 9, 2] == some (sortedRef [3, 1, 4, 1, 5, 9, 2]) := by
  native_decide
example : runQsA [9, 8, 7, 6, 5, 4, 3, 2, 1] == some (sortedRef [9, 8, 7, 6, 5, 4, 3, 2, 1])
    := by native_decide

-- The leaf on its own, both branches and the pivot-crossing SWAP.
example : runSplA [3, 1] 2 == some [1, 3] := by native_decide
example : runSplA [1, 3] 2 == some [1, 3] := by native_decide
example : runSplA [3, 1, 4] 2 == some [1, 3, 4] := by native_decide
-- Order WITHIN each part is unspecified; the split point is what is claimed.
example : runSplA [4, 1, 3, 2] 2 == some [2, 1, 4, 3] := by native_decide
example : runSplA [] 2 == some [] := by native_decide

/-! ### (vi.c) THE CROSS-DIFFERENTIAL — wired, and green as far as it runs

    M23's `quicksort` is a relational take-and-rebuild over a LINKED LIST returning two
    lists by value; `quicksortA` is an in-place scan over an ARRAY returning an index.
    They share no code — not the program, not the predicates, not the partition, not the
    container — and they were written against the same postcondition. Comparing them
    elementwise is the control that catches a wrong SHARED reading of the spec, which
    neither type checker would see.

    It is set up here in full and asserted on the inputs the array side can execute. The
    remaining inputs are one bug away, and the moment the pinned tests above flip this
    becomes the lane's real acceptance. -/

-- The list side is `S23Direct.qsRun` — the flagship cohort's own chain with a
-- caller as its tail (M28 D3), so the sort that runs here is the one checked
-- there, rather than three `FnDef`s handed over as a table.
def runQsL (l : List Nat) : Option (List Nat) :=
  match Dllbc.Tests.S9Diff.runExec (Dllbc.Tests.S23Direct.qsRun l) with
  | .ok env => (env.lookup "y").bind (listOfV 2000)
  | .error _ => none

/-- Both implementations agree with each other AND with the trusted sort. One
    conjunction, so a two-way agreement on a wrong answer still goes red. -/
def cross (l : List Nat) : Bool :=
  match runQsL l, runQsA l with
  | some a, some b => a == b && a == sortedRef l
  | _, _ => false

example : (([[], [1], [2,1], [3,1,2], [1,2,3], [3,2,1], [5,5,5], [4,1,3,2,5],
             [3,1,4,1,5,9,2], [2,2,1,1], [7,3,7,3,7]] : List (List Nat)).all cross)
    = true := by native_decide

-- `cross` is not vacuously true: a `none` from either side cannot masquerade as
-- agreement, and a disagreement or a wrong answer is `false`.
example : cross [2, 1] = true := by native_decide
example : (match runQsA [2, 1] with | some a => a == [2, 1] | none => false) = false := by
  native_decide

/-! ### (vi.c) M9's simulation property, over the array bodies that do run -/

def qsCallers : List Term := [qsCallerA [3, 1, 2], qsCallerA [2, 1], qsCallerA [1]]

example : qsCallers.all (fun b => progOk (arrUnder sHonest pHonest qHonest qSuffHonest b))
    = true := by native_decide

example : qsCallers.all (fun b => Dllbc.Tests.S9Diff.diffV2 (arrUnder sHonest pHonest qHonest qSuffHonest b))
    = true := by native_decide

/-! ## (vii) The five probes that located C6, kept as its regression

    §5.2's demand-end reaching the carve (ledger C6) was found by bisection, and the
    bisection is the test: four shapes that always worked, and the one that did not.
    Each is the smallest program exhibiting its shape. If the node-level collapse is
    removed from `carveAt`, only `c6CarveAfterCall` goes red — which is what makes this
    a live check on the rule rather than a comment claiming one. -/

def c6Touch : Term := prog{
  fn C6Touch (q : Nat, s : &mut (Array q Nat)) -> Unit { () };
  () }
-- A callee, declared in each chain that calls it; the standalone form is its own
-- verdict.
example : progOk c6Touch = true := by native_decide

-- (1) Peel a head and hand the tail to a call. Always worked.
def c6PeelCall : Term := prog{
  fn C6Touch (q : Nat, s : &mut (Array q Nat)) -> Unit { () };
  fn C6PeelCall (n : Nat, a : &mut (Array n Nat)) -> Unit {
    match n { Z => (),
      S(m) => { let hd = &m (*a)[Z ; 1 ; m]; let x = (*hd)[0];
                let tl = &m (*a)[S Z ; m]; C6Touch(m, &m *tl); () } } };
  () }
example : progOk c6PeelCall = true := by native_decide

-- (2) Carve inside the tail, with NO call first. Always worked.
def c6CarveNoCall : Term := prog{
  fn C6CarveNoCall (n : Nat, k3 : Nat, r2 : Nat, Hq : Id Nat n (S (Add k3 (S r2))),
             a : &mut (Array n Nat)) -> Unit {
    match n { Z => (),
      S(m) => { let hd = &m (*a)[Z ; 1 ; m]; let x = (*hd)[0];
                let tl = &m (*a)[S Z ; m];
                let lo = &m (*tl)[Z ; k3 ; S r2 | LeAdd k3 (S r2)
                                      | SInj m (Add k3 (S r2)) Hq];
                let mid = &m (*tl)[k3 ; 1 ; r2];
                let hi = &m (*tl)[S k3 ; r2]; () } } };
  () }
example : progOk c6CarveNoCall = true := by native_decide

-- (3) …and the swap's writes on top of it. Always worked.
def c6Swap : Term := prog{
  fn C6Swap (n : Nat, k3 : Nat, r2 : Nat, Hq : Id Nat n (S (Add k3 (S r2))),
             a : &mut (Array n Nat)) -> Unit {
    match n { Z => (),
      S(m) => { let hd = &m (*a)[Z ; 1 ; m]; let x = (*hd)[0];
                let tl = &m (*a)[S Z ; m];
                let lo = &m (*tl)[Z ; k3 ; S r2 | LeAdd k3 (S r2)
                                      | SInj m (Add k3 (S r2)) Hq];
                let mid = &m (*tl)[k3 ; 1 ; r2];
                let hi = &m (*tl)[S k3 ; r2];
                let y = (*mid)[0]; (*mid)[0] := x; (*hd)[0] := y; () } } };
  () }
example : progOk c6Swap = true := by native_decide

-- (4) Self-recursion through a reborrowed tail. Always worked.
def c6Rec : Term := prog{
  fn C6Rec [fuel] (fuel : Nat, m : Nat, hfuel : Le m fuel, a : &mut (Array m Nat)) -> Unit {
    match m { Z => (),
      S(m2) => match fuel { Z => botElim Unit hfuel,
        S(f2) => { let hd = &m (*a)[Z ; 1 ; m2]; let x = (*hd)[0];
                   let tl = &m (*a)[S Z ; m2]; C6Rec(f2, m2, hfuel, &m *tl); () } } } };
  () }
example : progOk c6Rec = true := by native_decide

/-- (5) THE RED ONE, before C6: carve inside a borrow AFTER handing it to a call. The
    reborrow parks a marker at the whole payload, and the carve consulted the extent map
    without collapsing it first — "`loanₘ ℓ` is not an array value (no extent to read)".
    Which is to say: a recursive array program carving the argument it just handed to
    its recursive call, i.e. every one of them. -/
def c6CarveAfterCall : Term := prog{
  fn C6Touch (q : Nat, s : &mut (Array q Nat)) -> Unit { () };
  fn C6CarveAfterCall (n : Nat, k3 : Nat, r2 : Nat, Hq : Id Nat n (S (Add k3 (S r2))),
             a : &mut (Array n Nat)) -> Unit {
    match n { Z => (),
      S(m) => { let hd = &m (*a)[Z ; 1 ; m]; let x = (*hd)[0];
                let tl = &m (*a)[S Z ; m];
                C6Touch(m, &m *tl);
                let lo = &m (*tl)[Z ; k3 ; S r2 | LeAdd k3 (S r2)
                                      | SInj m (Add k3 (S r2)) Hq];
                let mid = &m (*tl)[k3 ; 1 ; r2];
                let hi = &m (*tl)[S k3 ; r2]; () } } };
  () }
example : progOk c6CarveAfterCall = true := by native_decide

/-! ### Why the scan is not Lomuto — the rejection, with M13's evidence threaded

    Ledger R13. `(*a)[i | h]` on a symbolic array works; a SECOND index does not, and
    threading the ordering evidence does not rescue it. After the first carve the leaves
    are `[0,i)`, `[i,i+1)`, `[S i, rest)`, and the second request lands in the third — so
    premise (2) is formed LEAF-RELATIVELY against an offset `d` the machine minted while
    solving `j ≡ Add (S i) d`. No program term has type `Le (S d) rest`, because `d` has
    no surface name. **That is G1's wall arriving at the OFFSET rather than the extent**,
    and route (a) closes only the extent half.

    So `swap(a[i], a[j])` at two runtime cursors is unwritable, and `splitA`'s shape —
    every access at index 0 of a segment the program carved — is forced rather than
    chosen. ¶6's "a segment with its own zero" is a constraint, not a convenience. -/

def twoCursor : Term := prog{
  fn TwoCursor (n : Nat, i : Nat, j : Nat, Pij : Le (S i) j, Pjn : Le (S j) n,
                a : &mut (Array n Nat)) -> Unit {
    let x = (*a)[i | LeTrans (S i) j n Pij (LePredL j n Pjn)];
    let y = (*a)[j | Pjn];
    () };
  () }
example : progRejects twoCursor "no leaf" = true := by native_decide

-- Route (a) cannot rescue it either: the second request does not START a segment, so
-- there is no leaf for the supplied residue to decompose.
def twoCursorRes : Term := prog{
  fn TwoCursorRes (n : Nat, i : Nat, j : Nat, r1 : Nat, r2 : Nat,
                   a : &mut (Array n Nat)) -> Unit {
    let x = &m (*a)[i ; 1 ; r1 | LeAdd i (S r1)];
    let y = &m (*a)[j ; 1 ; r2 | LeAdd j (S r2)];
    () };
  () }
example : progRejects twoCursorRes "no segment starts at" = true := by native_decide

/-! ## (viii) The G7 ruling, probed at the boundary it exists to protect

    Premise (3) may not refine a telescope parameter's σ to match a supplied residue;
    it may solve along a CITED equation. The three probes the ruling asks for. -/

/-- The subject, as a prefix: its three callers below ride the same chain, so the
    callee is in scope by being declared above the code that calls it. -/
def withCitedCarve (rest : Term) : Term := prog{
  fn CitedCarve (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                 a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeAdd i (S j) | Heq];
    () };
  %rest }
example : progOk (withCitedCarve prog{ () }) = true := by native_decide

/-- (1) A caller whose numbers are CONSISTENT: `n = 3, i = 1, j = 1`, and `Refl`
    inhabits `Id Nat 3 (Add 1 (S 1))` because both sides compute to 3. -/
def citedCallerOk : Term := withCitedCarve prog{
  let z = Arr(1, 2, 3); let b = &m z; CitedCarve(3, 1, 1, Refl, b); let y = z; () }
example : progOk citedCallerOk = true := by native_decide

/-- (2) …and it RUNS, which is the half that was broken. Before the ruling the checker
    accepted callers the concrete machine got stuck on; now acceptance and execution
    agree on this shape, which is M8/M9's differential property restored for it. -/
example : runsAtAll citedCallerOk = true := by native_decide

/-- (3) The caller that used to be the counterexample. `n = 2` with `i = j = 5` type-
    checked before the ruling and then got stuck executing; now `Refl` cannot inhabit
    `Id Nat 2 (Add 5 (S 5))` and the CALLER is rejected, at its own boundary, with the
    constraint recorded in the signature it violated. -/
def citedCallerBad : Term := withCitedCarve prog{
  let z = Arr(1, 2); let b = &m z; CitedCarve(2, 5, 5, Refl, b); let y = z; () }
example : progOk citedCallerBad = false := by native_decide

end Dllbc.Tests.S25ArrSort
end
-- └── end of what was `S25ArrSort.lean` ───────────────────────────────────────────────
