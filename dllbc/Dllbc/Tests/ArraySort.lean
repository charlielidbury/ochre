import Dllbc.ElabCheck
import Dllbc.Program
import Dllbc.StdChain
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# The array flagship — an in-place quicksort over `Array n Nat`, HONEST FORM

An in-place quicksort whose signature carries the functional spec — sorted, and a
permutation of the input (checked via element counts) — proved by the checker and
confirmed by running the machine on concrete arrays.

**The honest program is written ONCE, closed, and the liars are mutations of it**
(docs/21, the marked-twins pilot; this file is what that plan calls the flagship
rewrite). The chain is a MODULE seeded from the standard library
(`prog (Dllbc.std) { … }`), so it is walked and checked AT ELABORATION, hovers and
`show` answer inside its bodies, and rejections land on statements. Its claim
sites are NAMED with `@marker`s, each lying twin is minted by editing the
marked claim on the persisted `Checked.term`, and every twin assertion runs
from the same seed (`progRejectsFrom`/`progOkFrom`). What the old twin-template
(`arrUnder`, five spliced return types) bought by construction — same body, one
lie — is now a value-level fact: the twin IS the honest term but for the one
marked site. The `fn` lowering FANS OUT a hoisted fn's types (return type →
motive/ih/seal, 3 copies; the hoisted parameter's type, 5), so twins here use
`Term.editMarked` — every copy of the one site edited in place, the fan-out
count pinned — while `replaceMarked?`'s exactly-one contract remains the
default and is pinned refusing the fanned site loudly.

The `#guard_msgs` show pin below is deliberately brittle: `σ₃₇₈₃` numbers from
the END of the std seed's supply, so it re-pins (trivially) whenever the chain
grows. It is the canary that hover/`show` keep answering INSIDE the flagship —
the user report that started docs/21.

**Twin minting is extract-and-edit**: a replacement is built FROM the honest
marker's own body (wrap it in `old`/`S`, swap an `Id`'s sides), so no minted
binder id and no seed Ω id is ever written by hand. A minting failure yields
`.unit`, which cannot satisfy any paired pin — the twins are self-guarding.

**Why the recovered coverage is stronger than what it replaces**: the old file's
body twin (`splitANoSwap`, "the one that matters most") was VACUOUS — its
recursive call named the Lean def (`splitANoSwap(…)`) instead of the `fn`
(`SplitA`), an unresolvable `.call`, so its `progOk = false` passed on
`call: unknown function 'splitANoSwap'` and the deleted swap was never what was
tested (probed 2026-08-24 before deletion). The marker form cannot fail that
way: the twin differs from a CHECKED program at exactly the marked site, and the
pinned needle says why it rejects.

E2E standing: alongside accepted/rejected assertions this file pins Term-value
equalities and runs-to values by `native_decide` — the sanctioned
mutation-ledger style (S4Pure-class exemption), because "the twin is the honest
term but for one site" is precisely a fact about `Term` values.

Lemma resolution follows StdChain's own LINK pattern, both halves, and one half
is a measured finding rather than the plan: the raw PROOF terms are applied as
`StdChainRaw` constants (`open Dllbc.StdChainRaw` below — a proof term applied
through a bound name is ⇒-application, where a recursor stuck on a symbolic
scrutinee is refused; a spliced constant is a pure literal lifted under ⇝), and
the predicate FORMERS in this block's types are QUALIFIED `StdChainRaw`
constants too, exactly as the chain's own links write their types. The plan
wanted the formers resolving from the seed's Ω bindings, and for simple
consumer types they do (ModuleStates §7) — but an IMPERATIVE fn's audit walks
them against carve/loan state, and there a seed-var former dies where the
spliced constant checks ("readC (⇝): a call is not in the comptime fragment",
isolated by switching only the resolution mode, 2026-08-24). That is a
module-states residual, not a marker one; until it lands, the flagship is a
LINK, and links qualify. The old file's selective 14-line
`open Dllbc.StdLemmas (…)` list is gone either way.
-/

section

open Dllbc
open Dllbc.StdChainRaw

namespace Dllbc.Tests.S25ArrSort

/-- Type-check a closed term against a closed type in the pure seed. -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000 t

/-! ## Partition predicates and their nil lemmas

    The predicates COMPUTE on a run, at every skip count. These cite the
    `StdChainRaw` constants directly — closed pure terms checked in the pure
    seed, no module state involved. -/

-- `SplitAL 3 2 [1,2,7]`: first two ≤ 3, last ≥ 3.
example : chkL prog_parse { Pair(unit, Pair(unit, Pair(unit, unit))) }
               prog_parse { SplitAL 3 2 3 Arr(1, 2, 7) } = true := by native_decide
-- …and it is NOT vacuous: the same array does not split at 1 (element 1 is `2 ≥ 3`? no).
example : chkL prog_parse { Pair(unit, Pair(unit, Pair(unit, unit))) }
               prog_parse { SplitAL 3 1 3 Arr(1, 2, 7) } = false := by native_decide

-- `PartA 3 2 [1,2,3,7]`: first two ≤ 3, element 2 IS 3, the rest ≥ 3.
example : chkL prog_parse { Pair(unit, Pair(unit, Pair(Refl, Pair(unit, unit)))) }
               prog_parse { PartA 3 2 4 Arr(1, 2, 3, 7) } = true := by native_decide
-- The pivot-identity conjunct is load-bearing: element 2 is 4, not 3.
example : chkL prog_parse { Pair(unit, Pair(unit, Pair(Refl, Pair(unit, unit)))) }
               prog_parse { PartA 3 2 4 Arr(1, 2, 4, 7) } = false := by native_decide

-- There IS no η at length zero, which is why the nil lemmas exist at all: `SortedA Z`
-- of an opaque payload is a stuck `arrRec`, not `Unit`.
example : (Pure.nf 2000 prog_parse { SortedA Z Arr() } == .const "Unit")
    = true := by native_decide

/-! ## `splitA` — the scan

    `splitA(p, t)` rearranges `*t` in place so that its first `k` elements are ≤ `p`
    and the rest are ≥ `p`, and returns `k` with the right part's length.

    Peel the head, split the tail recursively, and then place the head:

      * head ≤ p — it belongs at the front, where it already is. NO WRITE.
      * head > p and the tail's left part is empty — it belongs at the back, and
        everything after it is already ≥ p. NO WRITE.
      * head > p with a non-empty left part `L` — the head must cross `L`. Swap it with
        `L`'s LAST element, which is ≤ p and lands at the front legitimately, while the
        head lands exactly at the new boundary. ONE swap, and the only one.

    Every element access is at index 0 of a segment the program carved, because there is
    no other kind: two independent symbolic indices into one array cannot both be
    reached, so Lomuto's two-cursor scan is not writable and this shape is — the right
    sub-slice must be a segment with its own zero.

    `MkC` stages the count conjunct: it must name the tail AS IT WAS AT ENTRY, and `*tl`
    denotes that only until the recursive call replaces it, so it is built while `*tl`
    is still live and applied afterwards.

## `partitionA` — the partition leaf

    `partitionA(a)` picks `a[0]` as the pivot, splits the tail around it, and swaps the
    pivot into its final position — returning that position, the right part's length,
    and `PartA`.

    IT IS NOT RECURSIVE, and it exists as a separate declaration because the function
    boundary is load-bearing here. A body that has matched its own length `n` to `S m2`
    — which the head peel requires, since only `(*a)[Z ; 1 ; m2]` converts against the
    rigid extent — can no longer carve at a symbolic offset, because the rigid-length
    restriction now applies to the whole array. So the sort cannot both select a pivot
    and carve at the returned index. A call's opacity is the way out: it re-mints the
    caller's payload as a FRESH σ at the declared type, so the array comes back
    UNCARVED and with a FLEX length — exactly the state the three-way carve needs.

## `quicksortA` — the array quicksort

    Sorted AND a permutation, over the exit snapshot, IN PLACE, with zero declared
    backs in the call tree. `partitionA`, `splitA` and the two recursive calls are each
    described only by their return type.

    EMPTINESS IS TESTED WITH `Leb 1 n`, NOT BY MATCHING `n`, and that is forced twice
    over. Matching would refine the length to `S m2`, and the rigid-extent restriction
    then blocks the three-way carve outright. And the `Z` branch could not be
    discharged anyway: there is no η at length zero, so `SortedA Z σ` is a stuck
    `arrRec` rather than `Unit`. The False branch instead turns `Le n Z` into
    `Id Nat n Z` (`LeZeroEqRaw`) and feeds `SortedANilRaw`.

    THE ONE STRUCTURAL FACT beyond composition: BOUND SURVIVAL. `SortedArrCatRaw` wants
    `UbA pv` of the SORTED left part, and the partition bounded it before the sort.
    `UbPermARaw`/`LbPermARaw` carry both bounds across their sorts' own count evidence.
    That is the keystone; it is the only place this proof is more than gluing.

    Three staged builders. `MkTop` is built BEFORE the partition call, because the
    count conjunct's far endpoint is `old *a` and a body cannot write that; capturing
    `*a` while it still IS the entry value is the dodge. `MkAD` and `MkS` are built
    after the carve and before the sorts, because both name the sub-slices AS THEY
    WERE when the partition bounded them, and the recursive calls replace those
    values.

## The markers — the chain's declared attack surface (docs/21)

    Eight claim sites, each the smallest subterm a twin lies about, so every
    replacement is closed, a bare name, or the marked body edited structurally:

      @slen    the `r` in SplitA's length accounting (lie: `S r` — parts overlap)
      @ssp     the `*t` SplitAL is claimed of      (lie: `old *t` — entry, not exit)
      @scnt    SplitA's count RHS                  (lie: `S (…)` — off by one)
      @wmid    the value written to the boundary cell in THE SWAP
      @whd     the value written to the head cell in THE SWAP
               (lie: cross the two — every element stays where it was)
      @plen    the `S jj` in PartitionA's length   (lie: `jj` — the pivot cell forgotten)
      @ppart   the `*a` PartA is claimed of        (lie: `old *a`)
      @qsorted the `*a` SortedA is claimed of      (lie: `old *a`)
      @qcount  QuicksortA's whole count conjunct   (lie: sides swapped — direction)
      @qsuff   the sufficiency hypothesis `Le n fuel` (lie: `Unit` — fuel unjustified)
-/

/--
info: e ↦ (σ₃₇₈₃ : Nat)
-/
#guard_msgs in
set_option maxHeartbeats 0 in
def arrSort : Checked := prog (Dllbc.std) {
  fn SplitA [fuel] (fuel : Nat, m : Nat, hfuel : Le m fuel, p : Nat, t : &mut (Array m Nat))
      -> Σ (k : Nat). Σ (r : Nat).
         Σ (Hlen : Id Nat m (Add k (@slen r))).
         Σ0 (Hsp : Dllbc.StdChainRaw.SplitAL p k m (@ssp *t)).
         Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q m (*t)) (@scnt Dllbc.StdChainRaw.CountA Q m (old *t))
      { match m {
          -- Empty. NOT `unit`: there is no η at length zero, so `Dllbc.StdChainRaw.SplitAL p Z Z σ` is a
          -- stuck `arrRec` and needs the nil lemma.
          Z => Pair(Z, Pair(Z, Pair(Refl,
                 Pair(SplitANilRaw p Z Z (*t) Refl, λ (Q : Nat). Refl)))),
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
              -- the pre-swap state (`Hsw`), then move that across the recursive call's
              -- own Count evidence (`Hc`). Both non-swap branches pass `Refl` for the
              -- first leg.
              let Tl0 = *tl;
              let X0 = x;
              let M2 = m2;
              let MkC = (λ (T2 : Array M2 Nat).
                  λ (Hc : Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q M2 T2) (Dllbc.StdChainRaw.CountA Q M2 Tl0)).
                  λ (A2 : Array (S M2) Nat).
                  λ (Hsw : Π (Q : Nat) →
                        Id Nat (Dllbc.StdChainRaw.CountA Q (S M2) A2) (Dllbc.StdChainRaw.CountA Q (S M2) (acons M2 X0 T2))).
                    λ (Q : Nat).
                      IdTransRaw Nat (Dllbc.StdChainRaw.CountA Q (S M2) A2)
                                   (Dllbc.StdChainRaw.CountA Q (S M2) (acons M2 X0 T2))
                                   (Dllbc.StdChainRaw.CountA Q (S M2) (acons M2 X0 Tl0))
                        (Hsw Q) (CountAconsCongrRaw Q X0 M2 T2 Tl0 (Hc Q)));
              let Pair(k2, Pair(r2, Pair(Hlen2, Pair(Hsp2, Hcnt2)))) = SplitA(f2, m2, hfuel, p, &m *tl);
              if e : Leb x p {
                -- x ≤ p: the head is already in the left part; the boundary moves up.
                Pair(S k2, Pair(r2,
                  Pair(IdCongrRaw Nat Nat (λ (Z0 : Nat). S Z0) m2 (Add k2 r2) Hlen2,
                  Pair(Pair(LebTrueLeRaw x p e, Hsp2),
                       MkC (*tl) Hcnt2 (acons m2 x (*tl)) (λ (Q : Nat). Refl)))))
              } else {
                match k2 {
                  -- x > p with nothing to its left: the whole array is ≥ p already.
                  Z => Pair(Z, Pair(S r2,
                         Pair(IdCongrRaw Nat Nat (λ (Z0 : Nat). S Z0) m2 (Add Z r2) Hlen2,
                         Pair(Pair(LePredLRaw p x (LebFalseGtRaw x p e), Hsp2),
                              MkC (*tl) Hcnt2 (acons m2 x (*tl)) (λ (Q : Nat). Refl))))),
                  -- x > p with a non-empty left part: THE SWAP. Three carves put the
                  -- left part, the boundary cell and the right part in three segments,
                  -- and the exchange is two writes at index 0 of two of them.
                  S(k3) => {
                    -- The decomposition is DECLARED: premise (3) may not refine
                    -- `m2` by unification, so the equation the recursive call
                    -- returned is cited and solved along. `AddSuccRaw` is the whole
                    -- distance between what the callee proved and what the carve
                    -- asks for.
                    let Hdec = IdTransRaw Nat m2 (S (Add k3 r2)) (Add k3 (S r2)) Hlen2
                                 (IdSymRaw Nat (Add k3 (S r2)) (S (Add k3 r2))
                                    (AddSuccRaw k3 r2));
                    let lo = &m (*tl)[Z ; k3 ; S r2 | LeAddRaw k3 (S r2) | Hdec];
                    let mid = &m (*tl)[k3 ; 1 ; r2];
                    let hi = &m (*tl)[S k3 ; r2];
                    let y = (*mid)[0];
                    -- THE one mutation of the whole program, its two writes marked:
                    -- the no-swap twin crosses the two marker bodies, so each cell is
                    -- written back the value it already held — same statements, same
                    -- claims, elements unmoved.
                    (*mid)[0] := (@wmid x);
                    (*hd)[0] := (@whd y);
                    let Hrest = SplitACatRestRaw p k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                    let Hy = SplitA1HeadRaw p r2 (*hi) y Hrest;
                    let Hub = SplitACatUbRaw p k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                    let Hg = SplitA1TailRaw p r2 (*hi) y Hrest;
                    let Hnew = SplitACatI0Raw p k3 (S r2) (*lo) (acons r2 x (*hi)) Hub
                                 (Pair(LePredLRaw p x (LebFalseGtRaw x p e), Hg));
                    let Cnt = MkC (arrCat k3 (S r2) (*lo) (acons r2 y (*hi))) Hcnt2
                                  (acons m2 y (arrCat k3 (S r2) (*lo) (acons r2 x (*hi))))
                                  (λ (Q : Nat). CountSwapARaw Q x y k3 (*lo) r2 (*hi));
                    Pair(S k3, Pair(S r2, Pair(Refl, Pair(Pair(Hy, Hnew), Cnt))))
                  }
                }
              }
            }
          }
        } };
  fn PartitionA (fuel : Nat, n : Nat, hfuel : Le n fuel, Hne : Le (S Z) n,
                 a : &mut (Array n Nat))
      -> Σ (pvv : Nat). Σ (k : Nat). Σ (jj : Nat).
         Σ (Hlen : Id Nat n (Add k (@plen S jj))).
         Σ0 (Hp : Dllbc.StdChainRaw.PartA pvv k n (@ppart *a)).
         Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q n (*a)) (Dllbc.StdChainRaw.CountA Q n (old *a))
      { match n {
          -- An empty array has no pivot, so the caller owes `Le 1 n`; here it IS `Bot`.
          Z => botElim Unit Hne,
          S(m2) => {
            let hd = &m (*a)[Z ; 1 ; m2];
            let x = (*hd)[0];
            let tl = &m (*a)[S Z ; m2];
            let Tl0 = *tl;
            let X0 = x;
            let M2 = m2;
            let MkC = (λ (T2 : Array M2 Nat).
                λ (Hc : Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q M2 T2) (Dllbc.StdChainRaw.CountA Q M2 Tl0)).
                λ (A2 : Array (S M2) Nat).
                λ (Hsw : Π (Q : Nat) →
                      Id Nat (Dllbc.StdChainRaw.CountA Q (S M2) A2) (Dllbc.StdChainRaw.CountA Q (S M2) (acons M2 X0 T2))).
                  λ (Q : Nat).
                    IdTransRaw Nat (Dllbc.StdChainRaw.CountA Q (S M2) A2)
                                 (Dllbc.StdChainRaw.CountA Q (S M2) (acons M2 X0 T2))
                                 (Dllbc.StdChainRaw.CountA Q (S M2) (acons M2 X0 Tl0))
                      (Hsw Q) (CountAconsCongrRaw Q X0 M2 T2 Tl0 (Hc Q)));
            let Pair(k2, Pair(r2, Pair(Hlen2, Pair(Hsp2, Hcnt2)))) = SplitA(fuel, m2, LePredLRaw m2 fuel hfuel, x, &m *tl);
            match k2 {
              -- Nothing is ≤ the pivot, so the pivot is already in its final place at
              -- index 0. `Dllbc.StdChainRaw.PartA`'s identity conjunct is `Refl` and its lower bound is
              -- the split's own invariant, crossed by `SplitA0LbRaw`.
              Z => Pair(x, Pair(Z, Pair(m2,
                     Pair(Refl,
                     Pair(Pair(Refl, SplitA0LbRaw x m2 (*tl) Hsp2),
                          MkC (*tl) Hcnt2 (acons m2 x (*tl)) (λ (Q : Nat). Refl)))))),
              -- The pivot must cross the left part: swap it with that part's LAST
              -- element. The displaced element is ≤ the pivot, so it may sit at the
              -- front; the pivot lands at index `S k3`, which is the boundary.
              S(k3) => {
                let Hdec = IdTransRaw Nat m2 (S (Add k3 r2)) (Add k3 (S r2)) Hlen2
                             (IdSymRaw Nat (Add k3 (S r2)) (S (Add k3 r2))
                                (AddSuccRaw k3 r2));
                let lo = &m (*tl)[Z ; k3 ; S r2 | LeAddRaw k3 (S r2) | Hdec];
                let mid = &m (*tl)[k3 ; 1 ; r2];
                let hi = &m (*tl)[S k3 ; r2];
                let y = (*mid)[0];
                (*mid)[0] := x;
                (*hd)[0] := y;
                let Hrest = SplitACatRestRaw x k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                let Hy = SplitA1HeadRaw x r2 (*hi) y Hrest;
                let Hub = SplitACatUbRaw x k3 (S r2) (*lo) (acons r2 y (*hi)) Hsp2;
                let Hg = SplitA1TailRaw x r2 (*hi) y Hrest;
                let Hnew = PartACatI0Raw x k3 (S r2) (*lo) (acons r2 x (*hi)) Hub
                             (Pair(Refl, SplitA0LbRaw x r2 (*hi) Hg));
                let Cnt = MkC (arrCat k3 (S r2) (*lo) (acons r2 y (*hi))) Hcnt2
                              (acons m2 y (arrCat k3 (S r2) (*lo) (acons r2 x (*hi))))
                              (λ (Q : Nat). CountSwapARaw Q x y k3 (*lo) r2 (*hi));
                Pair(x, Pair(S k3, Pair(r2, Pair(Refl, Pair(Pair(Hy, Hnew), Cnt)))))
              }
            }
          }
        } };
  fn QuicksortA [fuel] (fuel : Nat, n : Nat, hfuel : @qsuff Le n fuel, a : &mut (Array n Nat))
      -> Σ0 (Hs : Dllbc.StdChainRaw.SortedA n (@qsorted *a)).
         Π (Q : Nat) → (@qcount Id Nat (Dllbc.StdChainRaw.CountA Q n (*a)) (Dllbc.StdChainRaw.CountA Q n (old *a)))
      { if he : Leb 1 n {
          match fuel {
            -- `Le 1 n` and `Le n Z` compose to `Le 1 Z`, which IS `Bot`.
            Z => botElim Unit (LeTransRaw (S Z) n Z (LebTrueLeRaw 1 n he) hfuel),
            S(f2) => {
              -- Staged while `*a` still denotes the ENTRY array: the Count chain's far
              -- endpoint is `old *a`, which no body term can name.
              let A0 = *a;
              let N0 = n;
              let MkTop = (λ (Dv : Array N0 Nat).
                  λ (Hd : Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q N0 Dv) (Dllbc.StdChainRaw.CountA Q N0 A0)).
                  λ (Av : Array N0 Nat).
                  λ (Had : Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q N0 Av) (Dllbc.StdChainRaw.CountA Q N0 Dv)).
                    λ (Q : Nat).
                      IdTransRaw Nat (Dllbc.StdChainRaw.CountA Q N0 Av) (Dllbc.StdChainRaw.CountA Q N0 Dv) (Dllbc.StdChainRaw.CountA Q N0 A0)
                        (Had Q) (Hd Q));
              -- `hfuel` is a PROOF, so passing it to the partition MOVES it. Both
              -- sufficiency bounds are therefore staged over it first — the same
              -- capture-before-consume dodge used for a consumed `rest`.
              let Hfuel0 = hfuel;
              let N0 = n;
              let F2 = f2;
              let MkHf = (λ (Kv : Nat). λ (H : Le (S Kv) N0).
                            LeTransRaw (S Kv) N0 (S F2) H Hfuel0);
              let Pair(pvv, Pair(k, Pair(jj, Pair(Hlen, Pair(Hp, Hcnt))))) = PartitionA(S(f2), n, hfuel, LebTrueLeRaw 1 n he, &m *a);
              -- The three-way carve, at the index the partition just returned. The
              -- first obligation is `LeAddRaw`; the second is `Le 1 (S jj)`, which route
              -- (a) reduces to ⊤; the third is degenerate.
              let l = &m (*a)[Z ; k ; S jj | LeAddRaw k (S jj) | Hlen];
              let pcell = &m (*a)[k ; 1 ; jj];
              let e = (*pcell)[0];
              -- The probe the whole rewrite exists to make possible: a `show` INSIDE
              -- the flagship's main content, answering (docs/21 §1 — the spliced
              -- template was silently deferred and had nothing to say here).
              show e;
              let r = &m (*a)[S k ; jj];
              let Hub = PartACatUbRaw pvv k (S jj) (*l) (acons jj e (*r)) Hp;
              let Hrest = PartACatRestRaw pvv k (S jj) (*l) (acons jj e (*r)) Hp;
              let Heq = PartA0EqRaw pvv jj (*r) e Hrest;
              let Hlb = PartA0LbRaw pvv jj (*r) e Hrest;
              let Top1 = MkTop (arrCat k (S jj) (*l) (acons jj e (*r))) Hcnt;
              -- The glue, staged: both bounds are about to be invalidated as VALUES by
              -- the recursive sorts, so their transports are set up now.
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
                  λ (H1 : Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q K0 L2) (Dllbc.StdChainRaw.CountA Q K0 L0)).
                  λ (H2 : Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q Jj0 R2) (Dllbc.StdChainRaw.CountA Q Jj0 R0)).
                  λ (Hs1 : Dllbc.StdChainRaw.SortedA K0 L2). λ (Hs2 : Dllbc.StdChainRaw.SortedA Jj0 R2).
                    NatRwRaw (λ (Z0 : Nat). Dllbc.StdChainRaw.SortedA (Add K0 (S Jj0))
                                (arrCat K0 (S Jj0) L2 (arrCat 1 Jj0 (Dllbc.StdChainRaw.Asingle Z0) R2)))
                      Pvv0 E0 (IdSymRaw Nat E0 Pvv0 Heq0)
                      (SortedArrCatRaw Pvv0 K0 L2 Jj0 R2 Hs1
                         (UbPermARaw Pvv0 K0 L2 K0 L0 H1 Hub0) Hs2
                         (LbPermARaw Pvv0 Jj0 R2 Jj0 R0 H2 Hlb0)));
              let L0 = *l;
              let R0 = *r;
              let E0 = e;
              let K0 = k;
              let Jj0 = jj;
              let MkAD = (λ (L2 : Array K0 Nat). λ (R2 : Array Jj0 Nat).
                  λ (H1 : Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q K0 L2) (Dllbc.StdChainRaw.CountA Q K0 L0)).
                  λ (H2 : Π (Q : Nat) → Id Nat (Dllbc.StdChainRaw.CountA Q Jj0 R2) (Dllbc.StdChainRaw.CountA Q Jj0 R0)).
                    λ (Q : Nat).
                      IdTransRaw Nat
                        (Dllbc.StdChainRaw.CountA Q (Add K0 (S Jj0)) (arrCat K0 (S Jj0) L2 (acons Jj0 E0 R2)))
                        (Add (Dllbc.StdChainRaw.CountA Q K0 L0) (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R0)))
                        (Dllbc.StdChainRaw.CountA Q (Add K0 (S Jj0)) (arrCat K0 (S Jj0) L0 (acons Jj0 E0 R0)))
                        (IdTransRaw Nat
                          (Dllbc.StdChainRaw.CountA Q (Add K0 (S Jj0)) (arrCat K0 (S Jj0) L2 (acons Jj0 E0 R2)))
                          (Add (Dllbc.StdChainRaw.CountA Q K0 L2) (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R2)))
                          (Add (Dllbc.StdChainRaw.CountA Q K0 L0) (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R0)))
                          (CountArrCatRaw Q K0 L2 (S Jj0) (acons Jj0 E0 R2))
                          (IdTransRaw Nat
                            (Add (Dllbc.StdChainRaw.CountA Q K0 L2) (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R2)))
                            (Add (Dllbc.StdChainRaw.CountA Q K0 L0) (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R2)))
                            (Add (Dllbc.StdChainRaw.CountA Q K0 L0) (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R0)))
                            (IdCongrRaw Nat Nat
                              (λ (C : Nat). Add C (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R2)))
                              (Dllbc.StdChainRaw.CountA Q K0 L2) (Dllbc.StdChainRaw.CountA Q K0 L0) (H1 Q))
                            (IdCongrRaw Nat Nat
                              (λ (C : Nat). Add (Dllbc.StdChainRaw.CountA Q K0 L0) C)
                              (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R2))
                              (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R0))
                              (CountAconsCongrRaw Q E0 Jj0 R2 R0 (H2 Q)))))
                        (IdSymRaw Nat
                          (Dllbc.StdChainRaw.CountA Q (Add K0 (S Jj0)) (arrCat K0 (S Jj0) L0 (acons Jj0 E0 R0)))
                          (Add (Dllbc.StdChainRaw.CountA Q K0 L0) (Dllbc.StdChainRaw.CountA Q (S Jj0) (acons Jj0 E0 R0)))
                          (CountArrCatRaw Q K0 L0 (S Jj0) (acons Jj0 E0 R0))));
              -- Sufficiency: the pivot sits strictly inside, so both halves are
              -- strictly shorter. `LeAddSuccRaw` and `LeAddLRaw` are the two sides of
              -- that, and each composes with this frame's own bound.
              let hf1 = MkHf k (LeAddSuccRaw k jj);
              let Pair(Hs1, Hc1) = QuicksortA(f2, k, hf1, &m *l);
              let hf2 = MkHf jj (LeAddLRaw (S jj) k);
              let Pair(Hs2, Hc2) = QuicksortA(f2, jj, hf2, &m *r);
              Pair(MkS (*l) (*r) Hc1 Hc2 Hs1 Hs2,
                   Top1 (arrCat k (S jj) (*l) (acons jj e (*r))) (MkAD (*l) (*r) Hc1 Hc2))
            }
          }
        } else {
          -- `n` is zero: the array is empty, and BOTH conjuncts are about an opaque
          -- payload, so the Count is `Refl` and the sortedness is the nil lemma.
          Pair(SortedANilRaw n (*a) (LeZeroEqRaw n (LebFalseGtRaw (S Z) n he)),
               λ (Q : Nat). Refl)
        } };
  () }

/-! ## Minting the twins (docs/21 §3)

    Extract-and-edit: `markedBody?` reads the honest claim out of the marker,
    the edit reshapes it, `replaceMarked?` puts the lie back under the SAME
    marker with the exactly-one contract. Any failure yields `.unit`, which is
    a program the seed happily accepts — so a broken mint fails its paired
    rejection pin rather than passing it vacuously. -/

/-- A twin of the honest chain: every copy of the marked claim edited in place
    (`Term.editMarked`), provided the fan-out is exactly the pinned `copies` —
    the `fn` lowering copies a hoisted fn's return type into motive/ih/arms/seal
    (3 copies here) and a hoisted parameter type wider still (5), so the count
    is part of the twin's statement. A count mismatch yields `.unit`, which no
    rejection pin accepts. -/
def mint (name : String) (copies : Nat) (edit : Term → Term) : Term :=
  let (hits, t) := Term.editMarked name edit arrSort.term
  if hits == copies then t else .unit

/-- The entry-snapshot lie: claim of `old e` what the honest form claims of `e`. -/
def oldOf (b : Term) : Term := .app (.const "old") b

-- The positive control for every rejection below: the UNMUTATED term, checked
-- from the same seed by the same helper the twins go through. (The chain was
-- already checked once, at its own definition site, by elaboration.)
example : progOkFrom Dllbc.std arrSort.term = true := by native_decide

-- The exactly-one contract stays the DEFAULT and stays loud: asked to treat the
-- fanned-out `qsuff` as a single site, `replaceMarked?` refuses with the count.
example : (match Term.replaceMarked? "qsuff" Term.unit arrSort.term with
           | .ok _ => false
           | .error e => strContains e "marker 'qsuff' occurs 5 times") = true := by
  native_decide

/-! ## The twin table — marker × copies × edit × needle

    One row per conjunct of the old file's twin battery, every row minted from
    the honest term. The `[fuel]`-hoisted fns fan a return-type claim into 3
    copies (motive, ih, seal) and the hoisted `hfuel` PARAMETER type into 5;
    `PartitionA` is unhoisted, so its sites are single-copy. The audit message
    unfolds the seed's formers into recursor spines, so the pinned needles are
    the stable verdict phrases — the same two the old file pinned. -/

-- `splitA`, conjunct 1: the length accounting says the two parts overlap by one.
example : progRejectsFrom Dllbc.std (mint "slen" 3 (fun r => .ctorApp "S" [r]))
  "does not have return type" = true := by native_decide

-- `splitA`, conjunct 2: the ordering claimed of the ENTRY array rather than the exit.
example : progRejectsFrom Dllbc.std (mint "ssp" 3 oldOf)
  "does not have return type" = true := by native_decide

-- `splitA`, conjunct 3: the counts off by one, which no path can reach.
example : progRejectsFrom Dllbc.std (mint "scnt" 3 (fun c => .ctorApp "S" [c]))
  "does not have return type" = true := by native_decide

-- `partitionA`, conjunct 1: the length accounting forgets the pivot cell.
example : progRejectsFrom Dllbc.std (mint "plen" 1 (fun _ => Term.var "jj"))
  "does not have return type" = true := by native_decide

-- `partitionA`, conjunct 2: the partition claimed of the ENTRY array.
example : progRejectsFrom Dllbc.std (mint "ppart" 1 oldOf)
  "does not have return type" = true := by native_decide

-- `quicksortA`, conjunct 1: sortedness lied onto the ENTRY. True at the empty
-- array, so the base path still passes and only the recursive one is blamed.
example : progRejectsFrom Dllbc.std (mint "qsorted" 3 oldOf)
  "does not have return type" = true := by native_decide

-- `quicksortA`, conjunct 2: the permutation lied by DIRECTION. Again `Refl` at
-- the empty array, and again the body's evidence points the other way once
-- anything moves.
example : progRejectsFrom Dllbc.std
  (mint "qcount" 3 (fun b => match b with | .idT t l r => .idT t r l | t => t))
  "does not have return type" = true := by native_decide

-- The sufficiency hypothesis is load-bearing, not decoration: weaken it to
-- `Unit` (the parameter stays, so the body still elaborates and the rejection
-- is about TYPING) and the out-of-fuel path has no ⊥ to eliminate.
example : progRejectsFrom Dllbc.std (mint "qsuff" 5 (fun _ => Term.const "Unit"))
  "botElim" = true := by native_decide

/-- The no-swap twin: cross the two marked write values, so each cell is
    written back the value it already held — same statements, same claims,
    elements unmoved. -/
def noSwapTwin : Term :=
  match Term.replaceMarked? "wmid" (Term.var "§noswap-probe") arrSort.term,
        Term.replaceMarked? "whd" (Term.var "§noswap-probe") arrSort.term with
  | .ok _, .ok _ =>
    -- Both sites are single-copy (the body is fanned per ARM, and each write
    -- sits in exactly one arm), so the cross is two exact replacements: read
    -- each marker's honest body, plant it under the other's marker.
    let bx := (Term.mapMarkersGo (fun a nm e => (if nm == "wmid" then some e else a, Term.marker nm e)) (none : Option Term) arrSort.term).1
    let byy := (Term.mapMarkersGo (fun a nm e => (if nm == "whd" then some e else a, Term.marker nm e)) (none : Option Term) arrSort.term).1
    match bx, byy with
    | some bx, some byy =>
      (match Term.replaceMarked? "wmid" byy arrSort.term with
       | .ok t1 =>
         match Term.replaceMarked? "whd" bx t1 with
         | .ok t2 => t2
         | .error _ => .unit
       | .error _ => .unit)
    | _, _ => .unit
  | _, _ => .unit

-- The mutation landed (a `.unit` fallback or an unchanged term cannot pass
-- both this and the rejection): the twin differs from the honest term, and it
-- is refused at the swap branch's own result audit — the claims cite the
-- crossed placement while Ω holds the uncrossed one. The old file's version of
-- this twin ("the one that matters most") asserted only `progOk = false` and
-- was in fact rejected as `call: unknown function 'splitANoSwap'` — a
-- transcription slip in its recursive call no needle ever caught.
example : (noSwapTwin == arrSort.term) = false := by native_decide
example : progRejectsFrom Dllbc.std noSwapTwin
  "does not have return type" = true := by native_decide

/-! ### Honest typing rejections, probed as closed programs (unchanged) -/

-- The three-way carve's ONE cited obligation is load-bearing: drop `LeAddRaw` and the
-- carve has nothing to select a leaf with. (The pivot carve needs no evidence at all —
-- route (a) reduces `Le 1 (S jj)` to ⊤ — so this is the only citation in the body.)
def carveNoEv : Term := prog_parse {
  fn CarveNoEv (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k ; S jj];
    let pcell = &m (*a)[k ; 1 ; jj];
    let r = &m (*a)[S k ; ..];
    () };
  () }
example : progRejects carveNoEv "may not impose it by refining" = true := by native_decide

-- …and the positive control at the same shape, so the rejection is about the missing
-- citation and not about the carve. (`QuicksortA` itself is the other positive control.)
def carveWithEv : Term := prog{
  fn CarveWithEv (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                  a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; k ; S jj | LeAddRaw k (S jj) | Heq];
    let pcell = &m (*a)[k ; 1 ; jj];
    let r = &m (*a)[S k ; ..];
    () };
  () }
example : progOk carveWithEv = true := by native_decide

/-! ## The executing differential

    The seeded run enters the library bodies (`Checked.exec`, docs/20 stage 6):
    `runProgramFrom arrSort caller` walks the caller's fragment with the chain's
    EXECUTING twin as ground, so `QuicksortA` really runs, in place, and what
    comes back is the caller's own bindings. -/

def tarrT (l : List Nat) : Term := .ctorApp "Arr" (l.map Term.nat)

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
    which computes to `Unit` at a concrete length. The callee names stay
    unresolved `.call`s here; the seeded helpers retarget them at the chain. -/
def qsCallerA (l : List Nat) : Term := prog_parse {
  let z = %(tarrT l);
  let b = &m z;
  QuicksortA(%(Term.nat l.length), %(Term.nat l.length), (), b);
  let y = z;
  () }

/-- `splitA` alone, so the divergence can be exhibited one call deep instead of three. -/
def splCaller (l : List Nat) (pvt : Nat) : Term := prog_parse {
  let z = %(tarrT l);
  let b = &m z;
  let r = SplitA(%(Term.nat l.length), %(Term.nat l.length), (), %(Term.nat pvt), b);
  let y = z;
  () }

def runQsA (l : List Nat) : Option (List Nat) :=
  match runProgramFrom arrSort (qsCallerA l) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

def runSplA (l : List Nat) (pvt : Nat) : Option (List Nat) :=
  match runProgramFrom arrSort (splCaller l pvt) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

def sortedRef (l : List Nat) : List Nat := l.mergeSort (fun a b => a <= b)

/-! ### It really sorts, in place, on concrete arrays

    The same declarations elaboration verified symbolically, run on real inputs
    and compared against a trusted sort. Duplicates, already-sorted and
    reverse-sorted included, since the empty-part paths are where a
    partition-based sort breaks. -/

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

/-! ### The full sort, executing, at sizes that do re-enter a carve after a call

    These used to diverge from the checker's verdict: a zero-width carve request must
    not select the leaf it abuts, but the ordinary selection demand-ended the live
    borrow pinned at a leaf's far end anyway. Unreachable symbolically (a residue is
    never known to be zero) and routine concretely, which is why only an executing
    differential could find it. Fixed; these are its regression. -/

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
example : runSplA [3, 1, 4] 2 == some [1, 3, 4] := by native_decide
-- Order WITHIN each part is unspecified; the split point is what is claimed.
example : runSplA [4, 1, 3, 2] 2 == some [2, 1, 4, 3] := by native_decide

/-! ### Cross-differential against the list quicksort

    The list quicksort elsewhere in this suite is a relational take-and-rebuild over a
    LINKED LIST returning two lists by value; `quicksortA` is an in-place scan over an
    ARRAY returning an index. They share no code — not the program, not the
    predicates, not the partition, not the container — and they were written against
    the same postcondition. Comparing them elementwise catches a wrong SHARED reading
    of the spec that neither type checker would see on its own. -/

-- The list side is `S23Direct.qsRun`, run through its own caller, so the sort that
-- runs here is the one checked there, rather than a table of `FnDef`s.
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

/-! ### The checker/machine simulation property, over the array bodies that run

    The seeded analogue of `diffV2`: the concrete final environment (the seeded
    RUN, seed entries dropped) is a σ-instance of some accepted symbolic path's
    (the seeded CHECK, same filter, scopes ended by `programPathsFrom`). -/

def diffFromA (body : Term) : Bool :=
  match runProgramFrom arrSort body with
  | .error _ => false
  | .ok concEnv =>
    let seeded := arrSort.env.env.map (·.1)
    (programPathsFrom arrSort body).any fun r => match r with
      | .ok (_, st) =>
        Dllbc.Tests.S9Diff.instanceOfC
          (canonicalize (st.env.filter (fun kv => !seeded.contains kv.1))) concEnv
      | .error _ => false

def qsCallers : List Term := [qsCallerA [3, 1, 2], qsCallerA [2, 1], qsCallerA [1]]

example : qsCallers.all (fun b => progOkFrom Dllbc.Tests.S25ArrSort.arrSort b)
    = true := by native_decide

example : qsCallers.all diffFromA = true := by native_decide

/-! ## Regression for a carve-after-call bug

    If the node-level collapse is removed from `carveAt`, this goes red, which is
    what makes it a live check on the rule rather than a comment claiming one. -/

/-- Carve inside a borrow AFTER handing it to a call. The
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
                let lo = &m (*tl)[Z ; k3 ; S r2 | LeAddRaw k3 (S r2)
                                      | SInjRaw m (Add k3 (S r2)) Hq];
                let mid = &m (*tl)[k3 ; 1 ; r2];
                let hi = &m (*tl)[S k3 ; r2]; () } } };
  () }
example : progOk c6CarveAfterCall = true := by native_decide

/-! ### Why the scan is not Lomuto

    `(*a)[i | h]` on a symbolic array works; a SECOND index does not, and threading the
    ordering evidence does not rescue it. After the first carve the leaves are
    `[0,i)`, `[i,i+1)`, `[S i, rest)`, and the second request lands in the third — so
    premise (2) is formed LEAF-RELATIVELY against an offset `d` the machine
    minted while solving `j ≡ Add (S i) d`. No program term has type `Le (S d) rest`,
    because `d` has no surface name.

    So `swap(a[i], a[j])` at two runtime cursors is unwritable, and `splitA`'s shape —
    every access at index 0 of a segment the program carved — is forced rather than
    chosen: the right sub-slice must be a segment with its own zero. -/

def twoCursor : Term := prog_parse {
  fn TwoCursor (n : Nat, i : Nat, j : Nat, Pij : Le (S i) j, Pjn : Le (S j) n,
                a : &mut (Array n Nat)) -> Unit {
    let x = (*a)[i | LeTransRaw (S i) j n Pij (LePredLRaw j n Pjn)];
    let y = (*a)[j | Pjn];
    () };
  () }
example : progRejects twoCursor "no leaf" = true := by native_decide

-- Route (a) cannot rescue it either: the second request does not START a segment, so
-- there is no leaf for the supplied residue to decompose.
def twoCursorRes : Term := prog_parse {
  fn TwoCursorRes (n : Nat, i : Nat, j : Nat, r1 : Nat, r2 : Nat,
                   a : &mut (Array n Nat)) -> Unit {
    let x = &m (*a)[i ; 1 ; r1 | LeAddRaw i (S r1)];
    let y = &m (*a)[j ; 1 ; r2 | LeAddRaw j (S r2)];
    () };
  () }
example : progRejects twoCursorRes "no segment starts at" = true := by native_decide

/-! ## Carve obligations may not refine, only cite

    A telescope parameter's σ may not be refined to match a supplied residue; a carve
    may solve along a CITED equation instead. The three probes that boundary asks
    for — MODULE-STATES FORM: the subject is a module block, its callers are
    fragments checked from that seed. The old `withCitedCarve` prefix-template
    (a Lean function splicing `%rest`) retires with the rest of the splices. -/

def citedCarve : Checked := prog () {
  fn CitedCarve (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                 a : &mut (Array n Nat)) -> Unit {
    let l = &m (*a)[Z ; i ; S j | LeAddRaw i (S j) | Heq];
    () };
  () }

/-- (1) A caller whose numbers are CONSISTENT: `n = 3, i = 1, j = 1`, and `Refl`
    inhabits `Id Nat 3 (Add 1 (S 1))` because both sides compute to 3. -/
def citedCallerOk : Term := prog_parse {
  let z = Arr(1, 2, 3); let b = &m z; CitedCarve(3, 1, 1, Refl, b); let y = z; () }
example : progOkFrom citedCarve citedCallerOk = true := by native_decide

/-- (2) …and it RUNS, which is the half that was broken. Before the ruling the checker
    accepted callers the concrete machine got stuck on; now acceptance and execution
    agree on this shape, restoring the checker/machine differential property for it. -/
example : (runProgramFrom citedCarve citedCallerOk).isOk = true := by native_decide

/-- (3) The caller that used to be the counterexample. `n = 2` with `i = j = 5` type-
    checked before the ruling and then got stuck executing; now `Refl` cannot inhabit
    `Id Nat 2 (Add 5 (S 5))` and the CALLER is rejected, at its own boundary, with the
    constraint recorded in the signature it violated. -/
def citedCallerBad : Term := prog_parse {
  let z = Arr(1, 2); let b = &m z; CitedCarve(2, 5, 5, Refl, b); let y = z; () }
example : progOkFrom citedCarve citedCallerBad = false := by native_decide

end Dllbc.Tests.S25ArrSort
end
