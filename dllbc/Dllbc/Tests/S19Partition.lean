import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S17Spec
import Dllbc.Migrate

/-!
# §19 test suite — partition (model + imperative), built on the M18 stack

This milestone assembles the crystallized architecture into its first real
algorithm: an in-place Lomuto partition through a mutable borrow, whose declared
backward spec is the pure `partitionL` model, checked by conversion per path.

It opens with the smallest complete instance of the architecture — a `swapS`
caller that recovers the precise `swapL i j s` (M17) and certifies its count with
`count_swapL'` (M18) — and gates the imperative body on a machine probe: splitting
the driver on a STUCK Bool spine (`leb x pivot`, x symbolic), which the current
substitution-based ⇜ cannot do without generalizing the spine first.
-/

open Dllbc
open Dllbc.StdLemmas (swapL count_swapL' set nth partScanL partScanRangeL partIdxL
  partIdxRangeL partGapRangeL partScanSizeL len_partitionRangeL len_sortRangeL sortRangeL
  partitionRangeL partitionL le_up_r le_add le_add_l le_add_succ le_rw_r le_rw_l le_add_mono_l
  add_succ le_trans le_refl id_sym id_trans id_congr hshift_true hshift_false len_swapL add_zero add_assoc
  count_partitionRangeL count_sortRangeL SortedR sorted_sortRangeL)

namespace Dllbc.Tests.S19Partition

def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def natT : Term := .const "Nat"

/-- Type-check a closed term against a closed type in the pure seed (as in §18). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## M19-A: the `count_swapL'` corollary and its `le_up_r` glue -/

example : chk StdLemmas.le_up_r StdLemmas.le_up_r_ty = true := by native_decide
example : chk StdLemmas.count_swapL' StdLemmas.count_swapL'_ty = true := by native_decide

-- M20-2 length-equation plumbing: the bound-derivation glue.
example : chk StdLemmas.le_add StdLemmas.le_add_ty = true := by native_decide
example : chk StdLemmas.le_add_l StdLemmas.le_add_l_ty = true := by native_decide
example : chk StdLemmas.le_add_succ StdLemmas.le_add_succ_ty = true := by native_decide
example : chk StdLemmas.le_rw_r StdLemmas.le_rw_r_ty = true := by native_decide
example : chk StdLemmas.hshift_true StdLemmas.hshift_true_ty = true := by native_decide
example : chk StdLemmas.hshift_false StdLemmas.hshift_false_ty = true := by native_decide

/-! ## M19-A opener — the architecture's smallest complete instance

    A `swapS` caller over a SYMBOLIC list: it borrows `s`, swaps positions `i`/`j`
    in place (imperative mutation), and its result is the count-preservation
    CERTIFICATE `count_swapL' m i j s pij p2`. After the swap the M17 spec-end
    recovers `s = swapL i j σ` precisely; the certificate — computed over the entry
    snapshot, whose subject `swapL i j s` is definitionally that recovered value —
    proves `count m (swapL i j s) = count m s` in the caller's own environment.
    Imperative mutation + precise recovery (M17) + pure lemma (M18), end to end. -/

-- SUBJECT: raw Term builders (tS/swapLT) feeding the lying specs below — the raw Term is the point.
def tS (t : Term) : Term := .ctorApp "S" [t]
def swapLT (i j l : Term) : Term := .app (.app (.app StdLemmas.swapL i) j) l

-- s=0, m=1, i=2, j=3, pij=4, p2=5; body binders cert=6, b=7.
def certSwapCount : FnDef :=
  decl{ fn certSwapCount (s : List Nat, m : Nat, i : Nat, j : Nat,
        pij : Le (S i) j, p2 : Le (S j) (len s)) -> Id Nat (count m (swapL i j s)) (count m s)
        { let cert = count_swapL' m i j s pij p2;
          let b = &mut s;
          swapS(b, i, j, pij, p2);
          cert } }

def openerTable : List FnDef := [Dllbc.Tests.S17Spec.nthS, Dllbc.Tests.S17Spec.nth2S, Dllbc.Tests.S17Spec.swapSN, certSwapCount]
example : Migrate.progOkOf certSwapCount openerTable = true := by native_decide

-- Negative control: claim the count GREW by one across the swap. The certificate
-- proves equality, so the value-returning audit rejects the lying return type —
-- the opener's acceptance is a real check of a real certificate.
def certSwapCountLie : FnDef :=
  decl{ fn certSwapCountLie (s : List Nat, m : Nat, i : Nat, j : Nat,
        pij : Le (S i) j, p2 : Le (S j) (len s)) -> Id Nat (count m (swapL i j s)) (S (count m s))
        = %certSwapCount.body }
example : Migrate.progRejectsOf certSwapCountLie "does not have return type" [Dllbc.Tests.S17Spec.nthS, Dllbc.Tests.S17Spec.nth2S, Dllbc.Tests.S17Spec.swapSN, certSwapCountLie] = true := by native_decide

/-! ## M20-2 (conformance, base case) — the pivot placement, checked against its spec

    The base of partition's recursion, isolated: place the pivot at the boundary
    `i` with a final swap, declared `back = baseBack` (partScanL's base — cased on
    `i` so the `i = Z` no-op is literally `*v`, not the stuck `swapL Z Z *v`). Cased
    on `i` because swapS cannot self-swap. The bound `pib : Le (S i) (len *v)`
    discharges swapS's `p2` after `i` refines to `S i'` (its `pij` is `Le Z i' = ⊤`,
    `unit`). Per path the declared spec refines with the scrutinee (`*v` on the
    no-op path, `swapL Z (S i') (*v)` on the swap path) and converts with swapS's
    composed backward tree — the §6.2 callee check now firing for a Unit-returning
    in-place body (the M20 auditAction extension). The mechanism partScan builds on. -/

open Dllbc.Tests.S17Spec (nthS nth2S swapSN)

-- The pivot-placement back-spec, CASED on i so the no-op path (i = Z) is literally
-- `*v` (not `swapL Z Z *v`, which is stuck on a symbolic list). Mirrors partScanL's
-- base. v=0, i=1. Used by the pivotPlace scaffolding fns' declared backs.
-- v=0, i=1, pib=2; body binder i2=3.
def pivotPlace : Term := prog{
  fn pivotPlace (v : &mut List Nat, i : Nat, pib : Le (S i) (len *v)) -> Unit
        { match i {
            Z => (),
            S(i2) => { swapS(v, Z, S(i2), (), pib); () }
        } };
  () }
/-- S17's cursor family, which stays a `FnDef` table there (one caller body against
    two callee variants) and so rides in the table here — a program declares the
    SUBJECT and its imported callees are supplied, which is what `progOk`'s `table`
    parameter is for. It used to carry the subject too; neither subject below calls
    the other, so it never needed to. -/
def confTable : List FnDef := [nthS, nth2S, swapSN]
example : progOk pivotPlace (.const "Unit") confTable = true := by native_decide

/-! ## M20-2 (bound derivation) — the base swap's `p2` derived from the length eqn

    Same pivot placement, but the bound is DERIVED from the length equation the
    recursion carries (`hlen : len *v = S (add i g)`, the k=Z instance) rather than
    handed in directly. In the `S i'` branch the equation reduces definitionally to
    `len *v = S (S (add i' g))` (add on a constructor head), so `le_add i' g`
    (whose type is `Le (S (S i')) (S (S (add i' g)))` up to Le reduction) transports
    onto `len *v` via `le_rw_r (id_sym hlen)`. This validates the full
    length-equation → swapS-bound chain the recursive partScan threads. -/


-- v=0, i=1, g=2, hlen=3; body binder i2=4.
def pivotPlaceH : Term := prog{
  fn pivotPlaceH (v : &mut List Nat, i : Nat, g : Nat,
        hlen : Id Nat (len *v) (S (add i g))) -> Unit
        { match i {
            Z => (),
            -- Derive the bound in a `let` FIRST, while `v` is still live (the `len *v`
            -- read is comptime/non-consuming); THEN call swapS (which consumes `v`).
            S(i2) => {
              -- p2 = le_rw_r (S(S i')) (S(S(add i' g))) (len *v) (id_sym hlen) (le_add i' g)
              let p2 = le_rw_r (S (S i2)) (S (S (add i2 g))) (len *v)
                         (id_sym Nat (len *v) (S (S (add i2 g))) hlen)
                         (le_add i2 g);
              swapS(v, Z, S(i2), (), p2);
              ()
            }
        } };
  () }
example : progOk pivotPlaceH (.const "Unit") confTable = true := by native_decide

/-! ## M20-2 (the recursive partScan) — partition's scan loop, checked against partScanL

    The full recursive scan, declared `back = partScanL pivot k i g (*v)`. Telescope
    carries the length equation `hlen : len *v = S (add k (add i g))` (k-first, so the
    step reduces definitionally). Body mirrors the M19 executing partition; the three
    step cases each derive their swapS bound (let-FIRST, per the §5.3 finding) and
    recurse with an UPDATED hlen (an hshift arithmetic transport — definitional total,
    plus a len_swapL bridge in the swap case). resolveTree composes the recursive
    call's back-spec with swapS's, exactly as pivotPlace proved for one swap. -/

-- SUBJECT: raw Term builders. `partScanLT`/`dv` (and `tS`/`zt`/`Refl`/`tlist` below)
-- construct the lying-spec inputs and the executing-differential expected values — the
-- raw Term IS the test subject here, not a surface form under test.
def partScanLT (pivot k i g l : Term) : Term := .app (.app (.app (.app (.app StdLemmas.partScanL pivot) k) i) g) l
def dv : Term := .deref (V 0 "v")

-- v=0, k=1, i=2, g=3, pivot=4, hlen=5; binders k'=6, c/i'=7, g'/hlenX=8, pij=9, p2=10, hlenTSg=11.
/-! ## M21-3 — partScanRange: the subrange scan (partScan shifted by `lo`)

    `partScanRange(v, lo, k, i, g, pivot, hle)` — partScan over the range `[lo, …)`.
    Every position is `add lo`-shifted; the boundary `i` and gap `g` are RELATIVE
    to `lo`. The bound is now an INEQUALITY `hle : Le (add lo (S (add k (add i g))))
    (len *v)` — a sub-range does not span to the end, so the old equation is false;
    the Le is the honest invariant (the top scan/swap position stays < len). The
    M20 Id-toolkit ports through the new `le_rw_l`/`le_add_mono_l`/`add_succ`
    bridges: swap bounds are `le_trans` of a `le_add_mono_l` lifted from the entry
    bound, and each recursion threads `hle` via `le_rw_l` + `id_congr` through
    `λx. add lo (S x)` over the SAME hshift identities partScan uses. -/


/-! ## M21-1 — the partition wrapper (back = partitionL, the partScanL composition)

    partition fixes the public interface: pivot placement + the scan, over a
    segment of length `n` (`hlenW : len *v = n`). Declared `back = partitionL n
    (*v)` — authored (in StdLemmas) as exactly `n = Z ⇒ *v`, `n = S n' ⇒ partScanL
    (nth 0 *v) n' 0 0 *v`, the raw composition of partScan's declared back. The
    scan call's hlen is hlenW transported by add_zero (the wrapper's `i = g = 0`,
    so partScan's `S (add n' (add 0 0))` is `S (add n' Z)`, bridged to `S n'`). -/


-- v=0, n=1, hlenW=2; body binders n'=3, pivot=4, hlen=5.
def partitionLieBack : Term := swapLT (.ctorApp "Z" []) (tS (.ctorApp "Z" [])) dv
def partScanLieBack : Term := partScanLT (V 4 "pivot") (V 1 "k") (V 3 "g") (V 2 "i") dv
/-! ## The lying-back sweep — one lie per CALLEE-CHECKED declared-spec branch

    A negative test per rule branch, not per feature (the M20 lesson). The §6.2
    callee convert-check catches a lie only where the declared back is authored as
    the raw suspension TREE (so tree ≡ back definitionally). Two such branches
    beyond the ones already covered:
    - borrow-returning multi-issued  → nth2Lie   (below)
    - borrow-returning single-issued → throughLie (S17Spec — the M8 arc)
    - Unit-returning recursive        → partScanLie (above; caught where an
      untouched argument-borrow path exposes the swapped spec)

    NOT callee-checked, by design: a back that is a higher-level REFORMULATION of
    the raw tree — swapS's `swapL i j *v` vs its set-based nth2 composition, and
    pivotPlace's swapL-based `baseBack` — never converts and is validated by the
    DIFFERENTIAL (executing recovery = checking recovery), as M17 established. The
    M20 auditAction extension checks in-place backs authored AS the tree (partScan);
    reformulated backs remain the differential's job. -/

def setL (k v l : Term) : Term := .app (.app (.app StdLemmas.set k) v) l

-- Borrow-returning multi-issued: nth2 with i and j swapped in the two sets.
-- SUBJECT: a deliberately-wrong back-spec (raw Term, i/j swapped in the two sets) — the lie is the subject.
-- `nth2Lie` — a LYING backward spec (the two indices swapped), asserting that the
-- §6.2 callee check catches it. Retired with the mechanism in M27-P2: a test of a
-- deleted feature is not coverage. It is also the one back this corpus carried as
-- a RECORD UPDATE rather than as surface syntax, which is why the `back = …` sweep
-- did not reach it — M26-F's `with`-closure lesson, arriving from the other side.

/-! ## M19-B (the gate) — splitting the driver on a STUCK Bool spine

    The imperative partition branches on `if leb x pivot` with `x` symbolic; the
    scrutinee reduces to a stuck spine `leb σ σp`, NOT a bare σ, and the ⇜ split
    (M3) needs a substitutable variable. The machine now GENERALIZES: on an owned
    stuck spine, `generalizeStuck` NF's it and `abstractInto`s it to a fresh
    `σb : Bool` across all σ-bearing state (the M10 invariant's targets), then the
    ordinary owned-sym split refines σb → True/False per branch.

    The probe: a fn whose RETURN TYPE mentions the same `leb n 2` spine, with two
    `boolRec` sides that converge ONLY per branch (`add Z x ≡ x`). Without the
    split the two stuck `boolRec`s differ and neither `Refl` checks; with it, both
    paths reduce and check. Both the spine-in-the-value (the scrutinee) and the
    spine-in-the-type (the pinned return) must refine together — which is exactly
    what generalizing across ALL σ-bearing state delivers. -/

-- SUBJECT: raw Term/Val builders (zt/tnat/lebSp/boolRecNat/Refl) for the stuckProbe
-- lying variants and the pure-model checks — raw Terms are the point here.
def zt : Term := .ctorApp "Z" []
def tnat : Nat → Term | 0 => zt | k + 1 => tS (tnat k)
def lebSp (n : Term) : Term := .app (.app Std.lebFnT n) (tnat 2)
def boolRecNat (t f sp : Term) : Term :=
  .app (.app (.app (.app (.const "boolRec") (.lam (.const "Bool") natT)) t) f) sp
def Refl : Term := .ctorApp "Refl" []

-- n = 0; the `if` binds a fresh scrutinee (id 1).
-- **Written out per twin rather than shared through a skeleton** (M28 ψ). The
-- retSkel form pays when a body is long enough that duplicating it hurts; this body
-- is two lines, so writing each twin in full keeps the honest return type in SURFACE
-- syntax — which for a convergence probe is the whole readable content — at the cost
-- of one repeated `let`. Sharing would have bought nothing and made the honest spec
-- a hand-built `Term`.
def stuckProbe : Term := prog{
  fn stuckProbe (n : Nat) -> Id Nat
        (boolRec (λ (b : Bool). Nat) (S Z) Z (leb n (S (S Z))))
        (boolRec (λ (b : Bool). Nat) (add Z (S Z)) (add Z Z) (leb n (S (S Z))))
        { let c = leb n (S (S Z));
          match c { True => Refl, False => Refl } };
  () }
example : progOk stuckProbe = true := by native_decide

-- Not vacuous (a): the True side does NOT converge (`S Z` vs `S (S Z)`). The
-- generalized σb refines to True in that path and the `boolRec` reduces to two
-- distinct values, so `Refl` fails — proving the per-branch refinement is real.
-- SUBJECT: a deliberately-non-converging return type (raw Term) — the lie is the subject.
def stuckProbeLieRet : Term := .idT natT
  (boolRecNat (tS zt) zt (lebSp (V 0 "n"))) (boolRecNat (tS (tS zt)) zt (lebSp (V 0 "n")))
def stuckProbeLie : Term := prog{
  fn stuckProbeLie (n : Nat) -> %stuckProbeLieRet
        { let c = leb n (S (S Z));
          match c { True => Refl, False => Refl } };
  () }
example : progRejects stuckProbeLie "does not have return type" = true := by native_decide

-- Not vacuous (b): a one-armed match is rejected as non-exhaustive — the
-- generalized σb is genuinely Bool-typed, so exhaustiveness demands True AND False.
-- SUBJECT: a deliberately non-exhaustive body (raw Term, one-armed match) — the defect is the subject.
def stuckProbeNonExhBody : Term := .letIn ⟨1, "c"⟩ (lebSp (V 0 "n")) (.matchE ⟨1, "c"⟩ none [.mk "True" [] Refl])
def stuckProbeNonExh : Term := prog{
  fn stuckProbeNonExh (n : Nat) -> Id Nat
        (boolRec (λ (b : Bool). Nat) (S Z) Z (leb n (S (S Z))))
        (boolRec (λ (b : Bool). Nat) (add Z (S Z)) (add Z Z) (leb n (S (S Z))))
        { %stuckProbeNonExhBody };
  () }
example : progRejects stuckProbeNonExh "non-exhaustive" = true := by native_decide

/-! ## M19-C (model) — `partitionL` computes the Lomuto partition

    Concrete validation of the pure model before wiring the imperative body to it:
    first-element pivot, `≤`-elements moved before it, `>`-elements after, pivot
    landing at the boundary. Covers an already-partitioned input (pivot smallest,
    no swaps), a reverse-sorted input (all `≤`, boundary walks to the end), and a
    mixed input that exercises the `g = S g'` swap branch. -/

-- SUBJECT: raw Val/Term builders (pv/vnat/vlist/tlist) — construct the pure-model expected
-- values and the executing-mode inputs; the raw Val/Term IS the subject under test here.
def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)
def vnat : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnat k]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | x :: xs => .ctor "Cons" [vnat x, vlist xs]
def tlist : List Nat → Term | [] => .ctorApp "Nil" [] | x :: xs => .ctorApp "Cons" [tnat x, tlist xs]
def partLT (n : Nat) (l : List Nat) : Term := .app (.app StdLemmas.partitionL (tnat n)) (tlist l)

example : (pv (partLT 3 [3,1,2]) == vlist [2,1,3]) = true := by native_decide
example : (pv (partLT 3 [1,2,3]) == vlist [1,2,3]) = true := by native_decide          -- already partitioned
example : (pv (partLT 3 [3,2,1]) == vlist [1,2,3]) = true := by native_decide          -- reverse sorted
example : (pv (partLT 5 [3,5,1,2,4]) == vlist [2,1,3,5,4]) = true := by native_decide   -- exercises the swap

/-! ## M21-2 — partIdxL (the boundary index) and sortL (the quicksort model) -/

def idxLT (n : Nat) (l : List Nat) : Term := .app (.app StdLemmas.partIdxL (tnat n)) (tlist l)
def sortLT (fuel n : Nat) (l : List Nat) : Term := .app (.app (.app StdLemmas.sortL (tnat fuel)) (tnat n)) (tlist l)

-- partIdxL = the pivot's final position (matches where the partition run lands it):
example : (pv (idxLT 3 [3,1,2]) == vnat 2) = true := by native_decide    -- pivot 3 → index 2
example : (pv (idxLT 3 [1,2,3]) == vnat 0) = true := by native_decide     -- pivot 1 stays at 0
example : (pv (idxLT 3 [3,2,1]) == vnat 2) = true := by native_decide
example : (pv (idxLT 5 [3,5,1,2,4]) == vnat 2) = true := by native_decide -- [2,1,3,5,4], pivot at 2

-- sortL sorts (fuel = length). Small cases only — sortL's toValPure inlines the
-- whole partition/scan stack, so pv/nfV on it is heavy; the executing quicksort
-- (M21-3) validates it on the larger input classes far more cheaply.
example : (pv (sortLT 2 2 [2,1]) == vlist [1,2]) = true := by native_decide          -- the smallest sort
example : (pv (sortLT 1 1 [7]) == vlist [7]) = true := by native_decide              -- singleton
example : (pv (sortLT 0 0 []) == vlist []) = true := by native_decide                -- empty

/-! ## M21-3 — sortRangeL (the index-bounded quicksort spec, plan of record) -/

def sortRangeLT (fuel lo cnt : Nat) (l : List Nat) : Term :=
  .app (.app (.app (.app StdLemmas.sortRangeL (tnat fuel)) (tnat lo)) (tnat cnt)) (tlist l)

-- Full-range (lo=0, cnt=len): sortRangeL 0 (len l) l is a full sort — the top-
-- level shape the imperative quicksort's back carries.
example : (pv (sortRangeLT 2 0 2 [2,1]) == vlist [1,2]) = true := by native_decide
example : (pv (sortRangeLT 1 0 1 [7]) == vlist [7]) = true := by native_decide
example : (pv (sortRangeLT 0 0 0 []) == vlist []) = true := by native_decide
example : (pv (sortRangeLT 3 0 3 [3,2,1]) == vlist [1,2,3]) = true := by native_decide   -- recursion fires
-- Sub-range (lo>0): sort only [lo, lo+cnt), leaving the rest untouched — the new
-- capability the recursion rides. [5,3,2,9] sorting [3,2] at offset 1 → [5,2,3,9].
example : (pv (sortRangeLT 2 1 2 [5,3,2,9]) == vlist [5,2,3,9]) = true := by native_decide
example : (pv (sortRangeLT 3 1 3 [9,3,1,2,7]) == vlist [9,1,2,3,7]) = true := by native_decide

/-! ## M19-C (imperative, executing mode) — the body computes `partitionL`

    The in-place Lomuto partition through a mutable borrow, mirroring `partitionL`
    exactly. `partScanE` recurses on the scan counter `k`; each step reads the scan
    element with the PURE `nth` on `*v` (a comptime read, the `leb` condition), and
    branches: the `g = S g'` case does an in-place `swapS` then recurses; the base
    places the pivot with a final `swapS` (guarded on `i = S i'` — swapS cannot
    self-swap). Run in executing mode (bounds proofs are placeholders `()`, which
    the run does not type-check) to confirm the imperative algorithm agrees with the
    pure model on concrete inputs — the conformance the checking mode will prove. -/

open Dllbc.Tests.S17Spec (nthS nth2S swapSN)


-- v=0, k=1, i=2, g=3, pivot=4; body binders k2=5, c/i2=6, g2=7.
def partScanE : FnDef :=
  decl{ fn partScanE [k] (v : &mut List Nat, k : Nat, i : Nat, g : Nat, pivot : Nat) -> Unit
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
                  -- `i` and `g2` are read MULTIPLE times here (boundary + scan position
                  -- + the recursion), and §2.1 copy-on-read now makes that natural: a
                  -- `S`-constructor arg reads its var by copy (marker-free Nat), so the
                  -- indices are the plain `S i`, `S (add i (S g2))`, `S g2` — no
                  -- add-spine workaround, and these convert with the model's forms.
                  S(g2) => { swapS(&mut *v, S(i), S(add i (S(g2))), (), ()); partScanE(v, k2, S(i), S(g2), pivot) }
                },
                False => partScanE(v, k2, i, S(g), pivot)
              }
            }
        } } }

-- v=0, n=1; body binders n2=5, pivot=6.
def partitionE : FnDef :=
  decl{ fn partitionE (v : &mut List Nat, n : Nat) -> Unit
        { match n {
            Z => (),
            S(n2) => { let pivot = nth Z (*v); partScanE(v, n2, Z, Z, pivot) }
        } } }

def partTable : List FnDef := [nthS, nth2S, swapSN, partScanE, partitionE]

-- Executing-mode caller: create a concrete list, borrow, partition in place, recover.
def partCaller (lst : List Nat) (n : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlist lst)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.seq (.call "partitionE" [.var ⟨1, "b"⟩, tnat n])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "x"⟩) .unit)))

def runPart (lst : List Nat) (n : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec partTable (partCaller lst n) with
  | .ok env => env.lookup "y" == some (pv (partLT n lst))
  | .error _ => false

-- The executing-mode partition agrees with the pure model on every input class:
-- already-partitioned (no swaps), reverse-sorted (all ≤, boundary walks to the
-- end), and mixed inputs that exercise the interior `g = S g'` swap (the reborrow
-- `&mut *v` path). Getting here surfaced and fixed three machine gaps (see the M19
-- report): shiftVars now shifts runtime vars inside pure spines; readR's var-move
-- ends a suspended reborrow in a borrow's payload; and a reused comptime index is
-- authored as a pure `add` spine so readR delegates to (non-consuming) readC.
example : runPart [3,1,2] 3 = true := by native_decide
example : runPart [1,2,3] 3 = true := by native_decide          -- already partitioned (no swaps)
example : runPart [3,2,1] 3 = true := by native_decide          -- reverse sorted
example : runPart [3,5,1,2,4] 5 = true := by native_decide      -- interior g=S g' swap
example : runPart [5,3,8,1,9,2] 6 = true := by native_decide    -- mixed, multiple interior swaps
example : runPart [2,2,1,3,2] 5 = true := by native_decide      -- duplicates around the pivot

/-! ## M20-3 differential — the CHECKING partScan FnDef, run EXECUTING, = partScanL

    The load-bearing conformance validator (the callee convert-check reaches the
    back only where it's authored as the tree; the swapS leaf's reformulated back
    is the differential's job). We run the SAME partScan FnDef that Migrate.progOkOf
    accepts — bounds, hlen proofs and all — in EXECUTING mode on concrete lists,
    and confirm its recovered list equals `partScanL pivot k 0 0 l`. So the body's
    actual effect matches the declared back on every input class: since Migrate.progOkOf
    accepts `back = partScanL`, executing = partScanL = the recovered value. -/

-- SUBJECT: the executing-mode differential harness (raw Term caller + raw expected-value
-- needle). Generating the caller Term and the `partScanL`-computed needle IS the test here.
/-! ## M21-3 — partitionRange: the subrange partition wrapper (Σ-pinned relative index)

    partitions the range [lo, lo+cnt) in place and returns the pivot's RELATIVE
    offset `i` (absolute = add lo i), Σ-pinned to `partIdxRangeL lo cnt *v`. The
    precondition is the range-fits inequality `hbnd : Le (add lo cnt) (len *v)`;
    the partScanRange call's entry bound (i = g = 0) is hbnd bridged by add_zero
    (`add cnt2 Z = cnt2`), mirroring partition's (M21-1) hlenW-via-add_zero. -/


/-! ## M21-3 — quicksort: the imperative in-place quicksort (back = sortRangeL)

    THE NORTH STAR. `quicksort(v, fuel, lo, cnt, hbnd)` sorts the `cnt` elements at
    offset `lo` in place. Fuel-structural (mirrors sortRangeL): out of fuel / cnt ≤
    1 is a no-op; otherwise pick the pivot, compute the pivot's relative index `i`
    and the right-count `g` from the ENTRY list (before mutating), scan-partition
    the range (partScanRange, whose back IS partitionRangeL lo cnt *v), then recurse
    on [lo, lo+i) and [lo+i+1, …) — sequential reborrows of the one `*v`. Because
    `i`/`g` are the pure `partIdxRangeL`/`partGapRangeL` of the entry list, the
    body's suspension tree (partScanRange's back, then the two quicksort backs
    composed) is DEFINITIONALLY sortRangeL's own unfold — conformance is conversion.

    The two range bounds come from partScanSizeL (i + g + 1 = cnt) and the three
    length-preservation lemmas (the partition and each recursive sort keep len *v,
    so the bounds, stated over the live *v, transport back to len entry = hbnd). -/

/-! ## M22-0 — the conformance baseline's validation suite (quicksort)

    Closing the back-specced (simulation) baseline before the direct-proving
    redirect: the lie is rejected, and the SAME checking-mode FnDef run executing on
    every input class (plus a sub-range) recovers exactly `sortRangeL fuel lo cnt l`
    — so the body's effect is the pure model on concrete data, the conformance the
    §6.2 callee check proves symbolically. -/

-- Not vacuous: identity is the right back only on the no-op paths (fuel Z / cnt ≤ 1);
-- on the sort path the composed suspension tree is sortRangeL, not *v, so it rejects.
-- SUBJECT: a deliberately-wrong back-spec (raw Term, identity) — the lie is the subject.
def quicksortLieBack : Term := dv
def partScanRangeLT (pivot lo k i g l : Term) : Term :=
  .app (.app (.app (.app (.app (.app StdLemmas.partScanRangeL pivot) lo) k) i) g) l
-- SUBJECT: the executing-mode differential harness (raw Term caller).
def psrCaller (lst : List Nat) (lo k pivot : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlist lst)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.seq (.call "partScanRangeE" [.var ⟨1, "b"⟩, tnat lo, tnat k, tnat 0, tnat 0, tnat pivot])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "x"⟩) .unit)))
/-! ## M22 execfix — the executing-mode reborrow-staleness regression + the payoff

    The isolated repro of the pain diary above (`swapS(&mut *b,…)` then a comptime
    deref through a FRESH reborrow), the sequential-swapS positive control (the
    sub-call-read path that always worked, guarding it stays green), and the
    now-unblocked FULL quicksort executing differential. -/

-- The minimal reproducer: after an in-place `swapS(&mut *b,…)` the swapped elements
-- sit in the callee's element-borrows; a probe fn reborrows `&mut *b` and reads
-- `leb (nth Z (*v)) pivot` — the exact comptime-deref-through-a-reborrow that read a
-- stale `loanₘ` (stuck) before the fix. `match c` forces the Bool. Post-fix the
-- reborrow fully re-collapses *v, so `nth Z (*v)` = 1, `leb 1 5` = True, and the
-- owner `x` recovers the swapped [1,2,3].
def lebProbe : FnDef :=
  decl{ fn lebProbe (v : &mut List Nat, pivot : Nat) -> Unit
        { let c = leb (nth Z (*v)) pivot;
          match c { True => (), False => () } } }

-- SUBJECT: raw Term caller for the isolated repro (x=[3,2,1]; b=&mut x; swapS through
-- *b; lebProbe reborrows *b and comptime-reads it; recover y).
def swapLebCaller (lst : List Nat) : Term :=
  .letIn ⟨0,"x"⟩ (tlist lst)
    (.letIn ⟨1,"b"⟩ (.borrow (.var ⟨0,"x"⟩))
      (.seq (.call "swapS" [.borrow (.deref (.var ⟨1,"b"⟩)), tnat 0, tnat 2, .unit, .unit])
        (.seq (.call "lebProbe" [.borrow (.deref (.var ⟨1,"b"⟩)), tnat 5])
          (.letIn ⟨2,"y"⟩ (.var ⟨0,"x"⟩) .unit))))
def runSwapLebProbe (lst : List Nat) (expect : List Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [nthS, nth2S, swapSN, lebProbe] (swapLebCaller lst) with
  | .ok env => env.lookup "y" == some (vlist expect)
  | .error _ => false
-- Before the fix this errored (leb scrutinee stuck on `loanₘ`); now the reborrow
-- probe reads the collapsed list and the owner recovers the swap.
example : runSwapLebProbe [3,2,1] [1,2,3] = true := by native_decide

-- Positive control: two sequential `swapS(&mut *b,…)` of the same positions compose
-- to the identity ([3,2,1] again). This path always worked (swapS reads *v via its
-- OWN nth2 sub-call, a var-read that already cascades) — it guards that the fix does
-- not disturb the sequential-reborrow path.
def swapTwiceCaller (lst : List Nat) : Term :=
  .letIn ⟨0,"x"⟩ (tlist lst)
    (.letIn ⟨1,"b"⟩ (.borrow (.var ⟨0,"x"⟩))
      (.seq (.call "swapS" [.borrow (.deref (.var ⟨1,"b"⟩)), tnat 0, tnat 2, .unit, .unit])
        (.seq (.call "swapS" [.borrow (.deref (.var ⟨1,"b"⟩)), tnat 0, tnat 2, .unit, .unit])
          (.letIn ⟨2,"y"⟩ (.var ⟨0,"x"⟩) .unit))))
def runSwapTwice (lst : List Nat) (expect : List Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [nthS, nth2S, swapSN] (swapTwiceCaller lst) with
  | .ok env => env.lookup "y" == some (vlist expect)
  | .error _ => false
example : runSwapTwice [3,2,1] [3,2,1] = true := by native_decide

-- THE PAYOFF: the FULL quicksort FnDef — bounds, length lemmas and all — run in
-- EXECUTING mode on concrete lists, agreeing with the pure model `sortRangeL`. The
-- body's three sequential `&mut *v` reborrows (partition + two recursive calls) are
-- exactly the reborrow-collapse case the fix unblocks. Full-range callers (lo=0,
-- cnt=len) so `hbnd = le_refl (len x) : Le (add 0 cnt) (len x)`.
/-! ## M22-a — exit-snapshot return types + `old *v` (§5.4, direct-proving enabler)

    A borrow parameter's bare `*v` in the RETURN TYPE reads the EXIT snapshot (the
    collapsed final payload, which the audit already computes); `old *v` names the
    ENTRY snapshot (usable in the type AND the body, a non-consuming reference to
    the entry value). Consumed params stay entry-pinned (M12). These prove the
    reading is genuinely the exit value, not the entry. -/

-- ACCEPTED: after the swap, *v (exit) IS swapL i j (old *v). Refl checks only
-- because bare *v reads the EXIT value; the body's proof cites `old *v` for the entry.
def exitReject : Term := prog{
  fn exitReject (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j, p2 : Le (S j) (len *v))
        -> Id (List Nat) (*v) (old *v)
        { swapS(&mut *v, i, j, pij, p2); Refl };
  () }
example : progRejects exitReject "does not have return type" (.const "Unit") confTable = true := by native_decide

-- OLD/EXIT MIXED: len is preserved across the swap. *v (exit) = swapL i j (old *v),
-- so `len *v = len (old *v)` is exactly len_swapL at the entry snapshot — cited
-- directly with `old *v` in the body (no need to save the list, which would move it).
/-- KEPT AS A DECLARATION: `S27Dispose` §C asserts `S26Fuel.bothWays
    S19Partition.twoRec`, and `bothWays` takes a `FnDef` — it hands the declaration
    to `FnMacro.progOf` itself. That assertion is the disposition record for this
    function's retired `back = *v`, so the subject has to stay the thing the record
    is about. -/
def twoRec : Term := prog{
  fn twoRec [f] (v : &mut List Nat, f : Nat) -> Unit
        { match f {
            Z => (),
            S(f2) => { twoRec(&mut *v, f2); twoRec(&mut *v, f2); () }
        } };
  () }
example : progOk twoRec = true := by native_decide

/-! ## M22-b — swapSE: count-preservation as a PROVEN postcondition (direct proving)

    The first ensures-form rung. NO back: the return type
    `Π n. Id Nat (count n (*v)) (count n (old *v))` is a propositional postcondition
    (swap preserves the multiset), and the body PROVES it from the exit reading —
    the demoted baseline would have declared `back = swapL i j *v` and leaned on the
    conversion check instead. Here the cert is `count_swapL'` (swapL preserves count)
    read directly at the entry snapshot `old *v`.

    WHY DELEGATION, NOT INLINE (the rung's sharpest finding — see the two probes in
    the milestone report). The intended route was to INLINE the swap via `nth2`
    (reborrow `&mut *v`) and ride the §22 bridge, on the expectation that the exit
    reading would be the set/nth form `set i (nth j s) (set j (nth i s) s)`. It is
    NOT. Through inline `nth2`, the audit reconstructs `*v`-exit from nth2's back
    `set i r1 (set j r2 *v)` with r1/r2 the FINAL borrow payloads — and those are
    released as OPAQUE symbols `set i σ8 (set j σ7 s)`. The audit never learns
    `σ8 = nth j s`, `σ7 = nth i s`: the imperative `*ei := *ej; *ej := t` moved
    values through borrows whose provenance the release does not retain. So the
    bridge (about the nth-form) does not even TYPE against the opaque-form exit —
    a DEEPER gap than set-vs-swapL. Routing through `swapS` (swapSN) instead makes
    the exit reading the clean model function `swapL i j (old *v)` (swapSN's back,
    itself a provable postcondition — cf. exitAccept), and `count_swapL'` matches it
    directly with no bridge.

    PAIN DIARY. Three entries.
    • OPAQUE EXIT READINGS — and the THREE-FEATURE ARC (the campaign's principal
      calculus-design finding). A leaf that mutates via pointer writes (`*ei := *ej`)
      leaves an exit whose written values are opaque existentials, so NO value-level
      postcondition (count/sort/perm) is provable about it. Root cause (one level
      deeper, per team-lead): the opacity is NOT intrinsic to inline mutation — it is
      minted at ONE point, buildResult, which creates an issued borrow's payload as a
      FRESH OPAQUE σ because signature-only checking has nothing saying what the
      payload IS at issue time. Everything downstream preserves information (the
      caller's writes are fully watched; the back spec routes surrendered values
      correctly) — only the issue point discards it. So the fix has a precise name:
      ISSUED-PAYLOAD PINNING, the dual of exit-snapshot — a callee declaring what its
      issued borrow's payload is at issue (`nth` pinning `*r = nth i (old *v)`), as
      machinery not a returned proof. The arc: PINNING makes an inline leaf's exit the
      set-form; the §22 BRIDGE (swapL_set) rewrites set-form to the model function;
      the AUDIT-REWRITE-BY-ID feature cites the bridge at the audit — together they
      make inline leaves PROVABLE. Third convergence point for audit-rewrite (after
      M17 callee-side and the exit-reading side).
    • PROOF LINEARITY vs COUNT. Length preservation is FRICTION-FREE (lenPreserve:
      `len_swapL` is unconditional), but count preservation needs the bounds — the
      cert wants `pij`/`p2` (count_swapL' is bounded) AND the swap CONSUMES them.
      Mechanism (per team-lead): proofs MOVE because indexKindV's sctx-type test
      recognizes Nat/Bool/Unit/Id/Π/Type but NOT stuck proposition spines — a σ typed
      `Le (S i) j` whnf's to a stuck natRec application (none of those heads), so it
      fails index-kind and moves. Dodged here by ORDERING alone — the cert is
      let-bound BEFORE the swapS call, reading pij/p2 (non-consuming, ⇝) while live;
      swapS MOVES them after. Fragile: a postcondition citing the proofs AFTER the
      mutation cannot be ordered around. Fix (QUEUED, now RECURRED — the tax was paid
      again at partitionRangeE and quicksortE, the measured-pain threshold): extend
      indexKindTy to erasure-bound stuck types (Le-headed), same §2.1 vacuity
      rationale — proofs-as-copy-on-read. DEFERRED (per team-lead): staging is the
      law of the ladder until a postcondition genuinely can't be staged before its
      mutation, OR the audit-rewrite arc is green-lit. Viability rulings on the fix
      shape: post-readC the Le former has unfolded to an anonymous recursor spine, so
      there is no head to match — a naive "stuck-recursor-to-Type ⇒ copy" is DEAD, not
      just fragile: a σ typed by a stuck `VecF Nat n` is exactly stuck-recursor-to-Type
      yet copying it copies DATA (a vector), the very E0382 class index-kind exists to
      prevent. The sound form is making `Le` a PRIMITIVE former (like Id's `.idT`),
      which also gives audit-rewrite a head to recognize — so it belongs WITH that
      arc, not as a mid-ladder patch.
    • CONVERGENT EVIDENCE. The §22 bridge `swapL_set` (set-form ≡ swapL) is proved
      and kept in StdLemmas as forward infrastructure — the transport the audit-rewrite
      feature cites once pinning lands, generalizing to partition's composed set-forms.
      Separately: count_partitionRangeL / count_sortRangeL are the very pure lemmas the
      PRE-REDIRECT M22 plan wanted — the conformance and direct-proving architectures
      have CONVERGED on the same pure-lemma obligations, differing only in where
      evidence assembly happens. A paper observation. -/
/-! ## M22-b — partitionRangeE: partition's PERMUTATION postcondition (direct proving)

    The partition rung. NO back: the return type `Π n. Id Nat (count n *v)(count n
    (old *v))` says partition permutes the range (preserves the multiset). Same
    delegation discipline as swapSE — the mutation is delegated to `partitionRange`
    (whose back `partitionRangeL lo cnt *v` is a CLOSED function of the input, so the
    exit reading is provable, not opaque), and the cert is the pure permutation
    lemma `count_partitionRangeL` at the entry snapshot. Cert staged before the
    consuming call (reads `hbnd` while live — the proof-linearity dodge again). This
    is the count/Perm half of the eventual `Sorted *v ∧ Perm (old*v) *v` quicksort
    postcondition; sortedness is the other axis, still ahead. -/
/-! ## M22-b — quicksortE: quicksort's PERMUTATION postcondition (direct proving)

    THE NORTH STAR, direct-proving form. NO back: retType `Π n. Id Nat (count n *v)
    (count n (old *v))` says the in-place quicksort PERMUTES its range — a
    propositional postcondition PROVEN in the body (the demoted baseline `quicksort`
    FnDef instead declares `back = sortRangeL fuel lo cnt *v` and checks conformance
    by conversion). Same delegation discipline as the swap and partition rungs: the
    sort is delegated to `quicksort` (back = sortRangeL, a closed function of the
    input, so the exit reading is provable rather than opaque), and the cert is the
    pure permutation lemma count_sortRangeL at the entry snapshot. Cert staged before
    the consuming call (reads hbnd live). This is the Perm half of the full
    `Sorted *v ∧ Perm (old*v) *v`; sortedness (AllLe/AllGe/sorted-glue) is the
    remaining axis. -/
end Dllbc.Tests.S19Partition

