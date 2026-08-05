import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.Tests.S23Direct

/-!
# §27 (probe) — does capital `let` already ARE snapshot naming?

A bounded viability probe, not a milestone. The question: the six filed cases of
"snapshot-naming pain" (`old` generalized to consumed things and superseded
exits) each dodge the same way — build a λ of everything that arrives later,
while the doomed value is still nameable, and apply it after. M26-B shipped
`let X = e`, the comptime binding: `e` read under ⇝, `X` erased, non-consuming,
confined to ⇝-positions. The hypothesis is that this is ALREADY anticipatory
snapshot naming — `let X = ⟨the about-to-die thing⟩` before the statement that
kills it, cite `X` after — so each staged builder collapses to one binding line,
and the residual feature is only (a) retroactivity (`old x` auto-inserting the
binding at `x`'s binding site), (b) the marker-free guard, (c) the one-timepoint
rule.

Every case below is the REAL pain site, copied here and rewritten — not a
sketch. The originals stay untouched in `S23Direct`/`S25ArrSort`/`S26Prog`, so
each pair is a diff against a program that is already known to check.

**Why the mechanism works at all**, stated once so each case can be read against
it. A capital `let` binds a *value* into a slot. Two machine facts then do all
the work:

  * `refineSym` sweeps `env`, so a capital-let binding is refined by every later
    match on a σ it mentions — the binding stays HONEST rather than going stale
    (§F pins this).
  * a *call* does not refine, it re-mints: `buildResult` gives the borrow a
    FRESH σ′ and leaves σ_entry alone. So the binding keeps the pre-call value
    while `*v` moves on. That asymmetry is the whole feature.

And `*v` is a TAKE under ⇒ but a PROJECTION under ⇝ (M26-B §C), which is why the
binding can be of a live borrow's payload without disturbing it.
-/

open Dllbc
open Dllbc.StdLemmas (le_refl le_trans le_up_r append id_congr id_trans id_sym
  set nth swapL len_set swapL_set le_rw_r Ub Lb take leb_true_le leb_false_gt
  le_pred_l count_cons_l count_cons_r len count_append count_cons_congr
  ub_perm lb_perm list_rw sorted_append_pivot count add)

namespace Dllbc.Tests.S27OldProbe

open Dllbc.Tests.S23Direct (partition appendBack setAt swapAt quicksort)

/-! ## §A. Case 1 — `append_back`'s moved data argument (M23-ii, `17f17993`)

    THE PAIN. The congruence must name its right endpoint `append (old *tl) w`,
    but the recursive call has by then MOVED `w`. The original dodges by staging
    the endpoint as a runtime `let` while `w` is live:

        let y = append (*tl) w;
        let h = append_back(&mut *tl, w);
        id_congr … (*tl) y h

    Note what this case is NOT: the staging here is already one line, because the
    doomed thing is a pure spine and a `let` of a spine goes through the pure
    lift. So capital `let` cannot *shorten* it. What it can do is two other
    things, and both are worth pinning separately. -/

/-- A1. The endpoint as a COMPTIME binding: same shape, one character, and the
    line becomes honestly erased instead of a runtime value nothing runs on. -/
def appendBackA1 : Decl :=
  decl{ fn append_back [v] (v : &mut List Nat, w : List Nat)
        -> Id (List Nat) (*v) (append (old *v) w)
        { match v {
            Nil => { *v := w; Refl },
            Cons(hd, tl) => {
              let Y = append (*tl) w;
              let h = append_back(&mut *tl, w);
              id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a) (*tl) Y h
            }
        } } }
example : checkFnOk appendBackA1 = true := by native_decide

/-- A2. THE INTERESTING FORM — name the doomed PARAMETER itself, not the endpoint
    built from it. `let W = w` is anticipatory `old w`: the value `w` had, bound
    before the call that moves it, cited afterwards at its natural use site. This
    is the shape the filing actually asked for, and the endpoint is then written
    where it belongs rather than hoisted. -/
def appendBackA2 : Decl :=
  decl{ fn append_back [v] (v : &mut List Nat, w : List Nat)
        -> Id (List Nat) (*v) (append (old *v) w)
        { match v {
            Nil => { *v := w; Refl },
            Cons(hd, tl) => {
              let W = w;
              let T = *tl;
              let h = append_back(&mut *tl, w);
              id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                (*tl) (append T W) h
            }
        } } }
example : checkFnOk appendBackA2 = true := by native_decide

/-- A3. …and the control that says A2's `let W` is load-bearing rather than
    decorative: drop it, cite `w` after the call, and the read is a
    use-after-move. (`*tl` still needs naming — the call re-mints it — so `T`
    stays; A4 removes that one instead.) -/
def appendBackA3 : Decl :=
  decl{ fn append_back [v] (v : &mut List Nat, w : List Nat)
        -> Id (List Nat) (*v) (append (old *v) w)
        { match v {
            Nil => { *v := w; Refl },
            Cons(hd, tl) => {
              let T = *tl;
              let h = append_back(&mut *tl, w);
              id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                (*tl) (append T w) h
            }
        } } }
example : checkFnOk appendBackA3 = false := by native_decide

/-- A4. The dual control: keep `W`, drop `T`, and write `*tl` at the endpoint —
    which after the call reads the EXIT payload, not the entry one, so the
    congruence's right endpoint is wrong and the audit refuses the body. This is
    the "one timepoint" question made concrete: `T` names entry, `*tl` names now,
    and they are different terms after a call. -/
def appendBackA4 : Decl :=
  decl{ fn append_back [v] (v : &mut List Nat, w : List Nat)
        -> Id (List Nat) (*v) (append (old *v) w)
        { match v {
            Nil => { *v := w; Refl },
            Cons(hd, tl) => {
              let W = w;
              let h = append_back(&mut *tl, w);
              id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                (*tl) (append (*tl) W) h
            }
        } } }
example : checkFnOk appendBackA4 = false := by native_decide

/-! ## §B. Case 2 — the superseded exit (`swap_at`, M23-iii, `73d2fdaf`)

    THE PAIN, and the filing that named the feature: "after the second `set_at`
    the FIRST call's exit σ′ can no longer be NAMED — `*v` reads the newest value,
    and nothing binds an older one. So the entire remaining derivation is staged
    as a FUNCTION OF THE NEXT EXIT while σ′ is still readable, and applied
    afterwards. … The clean fix is a way to bind a snapshot — `let` at comptime,
    naming an exit the way `old` names an entry."

    That sentence is a specification of `let M = *v`, and this is it. The eight
    lines of `finish` become ONE binding plus the derivation written at its own
    use site, in the order it is read. -/

def swapAtB1 : Decl :=
  decl{ fn swap_at (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j,
                    p2 : Le (S j) (len *v), hi : Le (S i) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { let a = nth i (*v);
          let b = nth j (*v);
          let Bridge = swapL_set i j (old *v) pij p2;
          let h1 = set_at(&mut *v, j, a, p2);
          let hlen = id_trans Nat (len *v) (len (set j a (old *v))) (len (old *v))
                       (id_congr (List Nat) Nat len (*v) (set j a (old *v)) h1)
                       (len_set j a (old *v));
          let hi2 = le_rw_r (S i) (len (old *v)) (len *v)
                      (id_sym Nat (len *v) (len (old *v)) hlen) hi;
          -- THE WHOLE FEATURE, in one line: name the mid-state before the write
          -- that supersedes it.
          let M = *v;
          let h2 = set_at(&mut *v, i, b, hi2);
          id_trans (List Nat) (*v) (set i b M) (swapL i j (old *v))
            h2
            (id_trans (List Nat) (set i b M) (set i b (set j a (old *v)))
               (swapL i j (old *v))
               (id_congr (List Nat) (List Nat) (λ (z : List Nat). set i b z)
                 M (set j a (old *v)) h1)
               Bridge) } }
example : checkFnOk swapAtB1 [setAt, swapAtB1] = true := by native_decide

/-- B2. The control: `M` really is the mid-state and not the live payload. Drop
    the binding and write `*v` at the same three places — after the second call
    that reads the FINAL payload, and the chain no longer composes. -/
def swapAtB2 : Decl :=
  decl{ fn swap_at (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j,
                    p2 : Le (S j) (len *v), hi : Le (S i) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { let a = nth i (*v);
          let b = nth j (*v);
          let Bridge = swapL_set i j (old *v) pij p2;
          let h1 = set_at(&mut *v, j, a, p2);
          let hlen = id_trans Nat (len *v) (len (set j a (old *v))) (len (old *v))
                       (id_congr (List Nat) Nat len (*v) (set j a (old *v)) h1)
                       (len_set j a (old *v));
          let hi2 = le_rw_r (S i) (len (old *v)) (len *v)
                      (id_sym Nat (len *v) (len (old *v)) hlen) hi;
          let h2 = set_at(&mut *v, i, b, hi2);
          id_trans (List Nat) (*v) (set i b (*v)) (swapL i j (old *v))
            h2
            (id_trans (List Nat) (set i b (*v)) (set i b (set j a (old *v)))
               (swapL i j (old *v))
               (id_congr (List Nat) (List Nat) (λ (z : List Nat). set i b z)
                 (*v) (set j a (old *v)) h1)
               Bridge) } }
example : checkFnOk swapAtB2 [setAt, swapAtB2] = false := by native_decide

/-! ## §C. Case 6 — the consumed binder (`partition`'s `mkL`/`mkR`, M23-iv, `e0c217e2`)

    THE PAIN. "Both count steps must name `rest` — the tail as it was at ENTRY —
    but `rest` is data and `*v := rest` moves it, so one statement later no term
    in the body denotes it." Dodged by two staged builders, `mkL` and `mkR`.

    The filing also states the sub-question this probe was asked to settle:
    "The lengths need no staged lambda: `len rest` is a NAT, so naming the
    computed value once, while `rest` is live, is enough. (The counts cannot do
    this — `count n rest` is a family over `n`, and it is the LIST the lemma
    needs, not any one of its counts.)"

    **The answer is that naming the LIST is exactly what a capital `let` does.**
    `let R = rest` binds the value, not one of its observations, so every family
    over it — `count n R` at any `n`, and the `count_cons_*` lemmas that take the
    list itself — is available afterwards. Both builders disappear and their two
    call sites become the two lemma applications they always were. -/

def partitionC1 : Decl :=
  decl{ fn partition [v] (v : &mut List Nat, p : Nat)
        -> Σ (hi : List Nat) → Σ (hub : Ub p (*v)) → Σ (hlb : Lb p hi)
             → Σ (hl1 : Le (len *v) (len (old *v))) → Σ (hl2 : Le (len hi) (len (old *v)))
             → Π (n : Nat) → Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))
        { let l = *v;
          match l {
            Nil => { *v := Nil;
                     Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (n : Nat). Refl))))) },
            Cons(x, rest) => {
              -- ONE LINE replaces `mkL` and `mkR` together: the entry tail, named
              -- while it is still live, cited at both use sites below.
              let R = rest;
              let lr = len rest;
              *v := rest;
              let r = partition(&mut *v, p);
              match r { Pair(hi, q1) => match q1 { Pair(hub, q2) => match q2 { Pair(hlb, q3) =>
              match q3 { Pair(hl1, q4) => match q4 { Pair(hl2, hcnt) => {
                if e : leb x p {
                  let lo = *v;
                  let hub2 = Pair(leb_true_le x p e, hub);
                  let hl2b = le_up_r (len hi) lr hl2;
                  let cnt = (λ (n : Nat). count_cons_l n x lo hi R (hcnt n));
                  *v := Cons(x, lo);
                  Pair(hi, Pair(hub2, Pair(hlb, Pair(hl1, Pair(hl2b, cnt)))))
                } else {
                  let hlb2 = Pair(le_pred_l p x (leb_false_gt x p e), hlb);
                  let hl1b = le_up_r (len *v) lr hl1;
                  let cnt = (λ (n : Nat). count_cons_r n x (*v) hi R (hcnt n));
                  Pair(Cons(x, hi), Pair(hub, Pair(hlb2, Pair(hl1b, Pair(hl2, cnt)))))
                }
              } } } } } }
            }
          } } }
example : checkFnOk partitionC1 = true := by native_decide

/-- C2. The control: drop `R` and cite `rest` at the two use sites. `*v := rest`
    moved it, so the reads are use-after-move — which is what says `R` is doing
    the work and not merely renaming something still in scope. -/
def partitionC2 : Decl :=
  decl{ fn partition [v] (v : &mut List Nat, p : Nat)
        -> Σ (hi : List Nat) → Σ (hub : Ub p (*v)) → Σ (hlb : Lb p hi)
             → Σ (hl1 : Le (len *v) (len (old *v))) → Σ (hl2 : Le (len hi) (len (old *v)))
             → Π (n : Nat) → Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))
        { let l = *v;
          match l {
            Nil => { *v := Nil;
                     Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (n : Nat). Refl))))) },
            Cons(x, rest) => {
              let lr = len rest;
              *v := rest;
              let r = partition(&mut *v, p);
              match r { Pair(hi, q1) => match q1 { Pair(hub, q2) => match q2 { Pair(hlb, q3) =>
              match q3 { Pair(hl1, q4) => match q4 { Pair(hl2, hcnt) => {
                if e : leb x p {
                  let lo = *v;
                  let hub2 = Pair(leb_true_le x p e, hub);
                  let hl2b = le_up_r (len hi) lr hl2;
                  let cnt = (λ (n : Nat). count_cons_l n x lo hi rest (hcnt n));
                  *v := Cons(x, lo);
                  Pair(hi, Pair(hub2, Pair(hlb, Pair(hl1, Pair(hl2b, cnt)))))
                } else {
                  let hlb2 = Pair(le_pred_l p x (leb_false_gt x p e), hlb);
                  let hl1b = le_up_r (len *v) lr hl1;
                  let cnt = (λ (n : Nat). count_cons_r n x (*v) hi rest (hcnt n));
                  Pair(Cons(x, hi), Pair(hub, Pair(hlb2, Pair(hl1b, Pair(hl2, cnt)))))
                }
              } } } } } }
            }
          } } }
example : checkFnOk partitionC2 = false := by native_decide

/-! ## §D. Case 3 — the four-builder flagship (`quicksort`; `mkTop`'s shape)

    M25's `mkTop` is the strongest single filing: "the permutation conjunct's far
    endpoint is `countA q n (old *a)`, `id_trans` takes its three points
    EXPLICITLY, and no body term can write `old *a` — so the endpoint has to be
    captured in a closure built before the partition call". Its list twin is
    `quicksort`'s `mkCnt`, and the same body carries `mkUb`/`mkLb` (M25's `mkAD`
    and `mkS`: the pre-sort sub-lists, invalidated as VALUES by the sorts) and
    `fin` (the post-append exit). Four builders, one cause, and the filing is
    explicit that none does mathematical work.

    All four collapse to FIVE capital `let`s — one per timepoint that the body
    needs to talk about:

      `R`   the entry tail, before `*v := rest` consumes it        (`mkCnt`)
      `A`,`B`   the two parts as the partition left them          (`mkUb`, `mkLb`, `mkCnt`)
      `A2`,`B2` the same two after their sorts, before the glue    (`fin`, `mkCnt`)

    and the mathematics is then written once, at the end, in the order it reads —
    no λ-abstraction over "everything that arrives later", no staged application.

    **The family-over-an-index question, settled here.** `mkCnt`'s far endpoint
    is `count n (old *v)` for EVERY `n` — a family, not a value, which is why the
    filing says the `len` trick (name the Nat once) does not transfer. Naming the
    LIST is what transfers: `R` is the list, so `count n (Cons x R)` is available
    at every `n`, and it is written under the returned `λ (n : Nat)` exactly where
    the goal puts it. -/

def quicksortD1 : Decl :=
  decl{ fn quicksort [fuel] (fuel : Nat, v : &mut List Nat, hfuel : Le (len *v) fuel)
        -> Σ (hs : Sorted (*v)) → Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v))
        { let l = *v;
          match l {
            Nil => { *v := Nil; Pair(unit, λ (n : Nat). Refl) },
            Cons(x, rest) => match fuel {
              Z => botElim Unit hfuel,
              S(f2) => {
                let lr = len rest;
                let R = rest;                          -- timepoint 1: the entry tail
                *v := rest;
                let pr = partition(&mut *v, x);
                match pr { Pair(hi, q1) => match q1 { Pair(hub, q2) => match q2 { Pair(hlb, q3) =>
                match q3 { Pair(hl1, q4) => match q4 { Pair(hl2, hpc) => {
                  let A = *v;                          -- timepoint 2: the two parts,
                  let B = hi;                          --   as the partition left them
                  let hf1 = le_trans (len *v) lr f2 hl1 hfuel;
                  let s1 = quicksort(f2, &mut *v, hf1);
                  match s1 { Pair(hs1, hc1) => {
                    let hf2 = le_trans (len hi) lr f2 hl2 hfuel;
                    let s2 = quicksort(f2, &mut hi, hf2);
                    match s2 { Pair(hs2, hc2) => {
                      let A2 = *v;                     -- timepoint 3: the sorted parts,
                      let B2 = hi;                     --   before the glue consumes them
                      let w = Cons(x, hi);
                      let happ = append_back(&mut *v, w);
                      Pair(
                        list_rw (λ (z : List Nat). Sorted z) (append A2 (Cons x B2)) (*v)
                          (id_sym (List Nat) (*v) (append A2 (Cons x B2)) happ)
                          (sorted_append_pivot x A2 B2 hs1
                             (ub_perm x A2 A hc1 hub) hs2 (lb_perm x B2 B hc2 hlb)),
                        λ (n : Nat).
                          id_trans Nat (count n (*v)) (add (count n A2) (count n (Cons x B2)))
                                       (count n (Cons x R))
                            (id_trans Nat (count n (*v)) (count n (append A2 (Cons x B2)))
                                          (add (count n A2) (count n (Cons x B2)))
                               (id_congr (List Nat) Nat (λ (z : List Nat). count n z)
                                  (*v) (append A2 (Cons x B2)) happ)
                               (count_append n A2 (Cons x B2)))
                            (id_trans Nat (add (count n A2) (count n (Cons x B2)))
                                          (add (count n A) (count n (Cons x B)))
                                          (count n (Cons x R))
                               (id_trans Nat (add (count n A2) (count n (Cons x B2)))
                                             (add (count n A) (count n (Cons x B2)))
                                             (add (count n A) (count n (Cons x B)))
                                  (id_congr Nat Nat (λ (r : Nat). add r (count n (Cons x B2)))
                                     (count n A2) (count n A) (hc1 n))
                                  (id_congr Nat Nat (λ (r : Nat). add (count n A) r)
                                     (count n (Cons x B2)) (count n (Cons x B))
                                     (count_cons_congr n x B2 B (hc2 n))))
                               (count_cons_r n x A B R (hpc n))))
                    } }
                  } }
                } } } } } }
              }
            }
          } } }
example : checkFnOk quicksortD1 [partition, appendBack, quicksortD1] = true := by native_decide

/-! ### D2/D3. Not vacuous — the corpus's own two lie twins, against this body

    The rewrite is only interesting if it still refuses what the original refuses.
    Both conjuncts get the corpus's twin: sortedness lied onto the ENTRY, and the
    count equation with its endpoints swapped. Each shares this body verbatim and
    changes only the return type. -/

def qsD1LieSorted : Decl :=
  { quicksortD1 with retType := (decl{ fn t (fuel : Nat, v : &mut List Nat, hfuel : Le (len *v) fuel)
      -> Σ (hs : Sorted (old *v)) → Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v))
      { () } }).retType }
example : checkFnErr qsD1LieSorted "does not have return type"
            [partition, appendBack, qsD1LieSorted] = true := by native_decide

def qsD1LieCount : Decl :=
  { quicksortD1 with retType := (decl{ fn t (fuel : Nat, v : &mut List Nat, hfuel : Le (len *v) fuel)
      -> Σ (hs : Sorted (*v)) → Π (n : Nat) → Id Nat (count n (old *v)) (count n (*v))
      { () } }).retType }
example : checkFnErr qsD1LieCount "does not have return type"
            [partition, appendBack, qsD1LieCount] = true := by native_decide

/-- D4. The control that says the five bindings are naming TIMEPOINTS and not
    just introducing abbreviations: use the live `*v` where `A2` belongs. After
    `append_back` the payload is the glued list, not the sorted left part, so the
    congruence's endpoint is wrong and the audit refuses. -/
def quicksortD4 : Decl :=
  decl{ fn quicksort [fuel] (fuel : Nat, v : &mut List Nat, hfuel : Le (len *v) fuel)
        -> Σ (hs : Sorted (*v)) → Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v))
        { let l = *v;
          match l {
            Nil => { *v := Nil; Pair(unit, λ (n : Nat). Refl) },
            Cons(x, rest) => match fuel {
              Z => botElim Unit hfuel,
              S(f2) => {
                let lr = len rest;
                let R = rest;
                *v := rest;
                let pr = partition(&mut *v, x);
                match pr { Pair(hi, q1) => match q1 { Pair(hub, q2) => match q2 { Pair(hlb, q3) =>
                match q3 { Pair(hl1, q4) => match q4 { Pair(hl2, hpc) => {
                  let A = *v;
                  let B = hi;
                  let hf1 = le_trans (len *v) lr f2 hl1 hfuel;
                  let s1 = quicksort(f2, &mut *v, hf1);
                  match s1 { Pair(hs1, hc1) => {
                    let hf2 = le_trans (len hi) lr f2 hl2 hfuel;
                    let s2 = quicksort(f2, &mut hi, hf2);
                    match s2 { Pair(hs2, hc2) => {
                      let B2 = hi;
                      let w = Cons(x, hi);
                      let happ = append_back(&mut *v, w);
                      Pair(
                        list_rw (λ (z : List Nat). Sorted z) (append (*v) (Cons x B2)) (*v)
                          (id_sym (List Nat) (*v) (append (*v) (Cons x B2)) happ)
                          (sorted_append_pivot x (*v) B2 hs1
                             (ub_perm x (*v) A hc1 hub) hs2 (lb_perm x B2 B hc2 hlb)),
                        λ (n : Nat). Refl)
                    } }
                  } }
                } } } } } }
              }
            }
          } } }
example : checkFnOk quicksortD4 [partition, appendBack, quicksortD4] = false := by native_decide

/-! ## §E. Case 4 — `hfuel` captured before consumption (M25, R16)

    "`hfuel` is a PROOF, so passing it to the partition MOVES it. Both
    sufficiency bounds are therefore staged over it first" — `mkHf`. This case is
    filed under snapshot naming but it is a DIFFERENT problem wearing the same
    dodge: nothing about the proof's value changes, it is merely consumed. So
    there are two candidate fixes and they are worth separating, because only one
    of them is this probe's subject.

    E3 is M26-B's answer (decision 3): the callee declares the parameter capital,
    the argument is ⇝-read, and no naming is needed at all. E2 is the capital-let
    answer, which is what a caller has when it does NOT control the callee. -/

def sink : Decl := decl{ fn sink (a : Nat, b : Nat, h : Le a b) -> Unit { () } }
def sinkC : Decl := decl{ fn sinkC (a : Nat, b : Nat, H : Le a b) -> Unit { () } }

/-- E1. THE PAIN, minimal: the call moves the proof, and the derivation that the
    later call needs cannot be built. -/
def e1 : Decl := decl{ fn caller (n : Nat, f : Nat, hfuel : Le n f) -> Unit
  { sink(n, f, hfuel);
    let hf1 = le_trans n n f (%le_refl n) hfuel;
    sink(n, f, hf1); () } }
example : checkFnOk e1 [sink, e1] = false := by native_decide

/-- E2. The capital-let route: name the proof before the call that consumes it,
    and derive from the name afterwards. Note what is being asked of the fence
    here — `hf1` is a LOWERCASE binding whose right-hand side mentions a capital
    one, and it is then handed to a RUNTIME parameter. -/
def e2 : Decl := decl{ fn caller (n : Nat, f : Nat, hfuel : Le n f) -> Unit
  { let HF = hfuel;
    sink(n, f, hfuel);
    let hf1 = le_trans n n f (%le_refl n) HF;
    sink(n, f, hf1); () } }
example : checkFnOk e2 [sink, e2] = true := by native_decide

/-- E3. M26-B's route, for comparison: the callee's parameter is capital, and the
    pain never arises — no binding, no staging, the proof cited directly. This is
    decision 3, not snapshot naming, and it is the better fix WHEN AVAILABLE. -/
def e3 : Decl := decl{ fn caller (n : Nat, f : Nat, hfuel : Le n f) -> Unit
  { sinkC(n, f, hfuel);
    let hf1 = le_trans n n f (%le_refl n) hfuel;
    sinkC(n, f, hf1); () } }
example : checkFnOk e3 [sinkC, e3] = true := by native_decide

/-- E4. THE FENCE'S EDGE, pinned. A capital binder may be *derived from* into a
    runtime binding (E2), but it may not itself BE the runtime argument: the same
    program with `HF` passed directly is the §6 fence, exactly as `S26Modes` B6
    pins it. So the capital-let route costs one extra `let` whenever the doomed
    proof is wanted verbatim rather than as a premise. -/
def e4 : Decl := decl{ fn caller (n : Nat, f : Nat, hfuel : Le n f) -> Unit
  { let HF = hfuel;
    sink(n, f, hfuel);
    sink(n, f, HF); () } }
example : checkFnErr e4 "cannot be ⇒-moved" [sink, e4] = true := by native_decide

/-! ## §F. Case 5 — the staged `len *v` bound, and the demand-collapse caveat

    M26-E's `append_back` caller: "the fuel that works is `len *v` itself with
    `le_refl` as its bound, STAGED in a `let` before the call, because the borrow
    is taken in between and a comptime argument mentioning `*v` would
    demand-collapse the loan it was just lent."

    This is the one case where the probe expected a caveat and found the caveat
    to be the whole case. -/

def eatFuel : Decl :=
  decl{ fn eatFuel (fuel : Nat, v : &mut List Nat, Hf : Le (len *v) fuel) -> Unit { () } }

/-- F1. The incumbent: a LOWERCASE staged length. Accepted. -/
def f1 : Decl := decl{ fn caller (v : &mut List Nat) -> Unit
  { let lv = len *v; eatFuel(lv, &mut *v, %le_refl lv); () } }
example : checkFnOk f1 [eatFuel, f1] = true := by native_decide

/-- F2. The same staging made COMPTIME. Refused — and not by anything to do with
    snapshots: `fuel` is a runtime parameter, so a capital binding cannot be its
    argument (the §6 fence, `S26Modes` B6 again). The staged length here is a
    genuine runtime value, so this case does not want a comptime binding at all. -/
def f2 : Decl := decl{ fn caller (v : &mut List Nat) -> Unit
  { let LV = len *v; eatFuel(LV, &mut *v, %le_refl LV); () } }
example : checkFnErr f2 "cannot be ⇒-moved" [eatFuel, f2] = true := by native_decide

/-- F3. THE WARNING, probed directly: the un-staged form, with the comptime
    argument written inline after the borrow. Pinned whichever way it goes. -/
def f3 : Decl := decl{ fn caller (v : &mut List Nat) -> Unit
  { eatFuel(len *v, &mut *v, %le_refl (len *v)); () } }
example : checkFnOk f3 [eatFuel, f3] = false := by native_decide

/-! ## §G. Is the binding HONEST? — `refineSym`'s sweep, and the one-timepoint rule

    A snapshot name is only worth having if it stays true. Two properties, and
    they pull in opposite directions, which is why both need pinning:

      * a later MATCH refines the σ the binding holds, and the binding must move
        with it (knowledge, §3.2 — the sweep);
      * a later WRITE or CALL must NOT move it (state, §3.2 — the whole point).

    `refineSym` sweeps `env`, so the first holds by construction. The second holds
    because a call re-mints rather than refines. §G pins both. -/

/-- A comptime probe: a capital-bindered equality, so citing it consumes nothing
    and the two sides are read under ⇝. -/
def idOf : Decl :=
  decl{ fn idOf (A : List Nat, B : List Nat, H : Id (List Nat) A B) -> Unit { () } }

/-- G1. THE SWEEP. `L` is bound to the symbolic payload σ *before* the borrow-mode
    match refines σ to `Cons σ_hd σ_tl`. Afterwards `Refl` inhabits
    `Id L (Cons (*hd) (*tl))` — so the binding was refined with everything else,
    and a capital `let` of a symbolic payload does not go stale under a later
    dependent match. -/
def g1 : Decl := decl{ fn g1 (v : &mut List Nat) -> Unit
  { let L = *v;
    match v { Nil => (), Cons(hd, tl) => { idOf(L, Cons (*hd) (*tl), Refl); () } } } }
example : checkFnOk g1 [idOf, g1] = true := by native_decide

/-- G2. …and the control that says G1 is the sweep and not vacuity: the same
    binding against the WRONG shape is refused, and the rejection prints `L`'s
    refined contents, which is the sweep's own receipt. -/
def g2 : Decl := decl{ fn g2 (v : &mut List Nat) -> Unit
  { let L = *v;
    match v { Nil => (), Cons(hd, tl) => { idOf(L, Nil, Refl); () } } } }
example : checkFnErr g2 "(Id (Cons σ2 σ3) Nil)" [idOf, g2] = true := by native_decide

/-- G3. THE ONE-TIMEPOINT RULE, from the other side: a write does not move the
    binding. `L` is bound, the payload is overwritten with `Nil`, and `L` is still
    σ — which is why claiming `Id L Nil` is refused and the message names σ. -/
def g3 : Decl := decl{ fn g3 (v : &mut List Nat) -> Unit
  { let L = *v; *v := Nil; idOf(L, Nil, Refl); () } }
example : checkFnErr g3 "(Id σ0 Nil)" [idOf, g3] = true := by native_decide

/-! ## §H. Marker-containing values — the guard is NOT there, and here is the shape

    §3.2's knowledge/state invariant: "no substitution for a σ may contain [a hole
    or a loan marker]". It is asserted at `refineSym`, which is the SUBSTITUTION
    site. A capital `let` is a BINDING, not a substitution, so nothing asserts it
    there — and the cases below walk straight in.

    The good news is bounded: nothing unsound follows today, because a marker
    cannot be typed. The bad news is the failure MODE — the binding is admitted
    silently and the refusal arrives later, at a use site, in a message about a
    deferred feature (`λ/neutral typing deferred to M5`) rather than about the
    marker. That is verbatim the class M23-ii and M23-iv each spent a debugging
    cycle on. -/

/-- The comptime slots of every final Ω, and whether any holds a state marker.
    (Env keys are the source names, so the capital ones are the comptime ones.) -/
def comptimeSlotMarker (tbl : List Decl) (d : Decl) : Bool :=
  (runFn tbl d).any (fun r => match r with
    | .ok env => env.any (fun kv =>
        (kv.1.get 0).isUpper && Val.hasStateMarker kv.2)
    | .error _ => false)

-- H1. A capital `let` of a BORROW-typed variable: accepted, and the slot ends up
-- holding `borrowₘ ℓ σ` — a state marker in an erased binding.
def h1 : Decl := decl{ fn h1 (v : &mut List Nat) -> Unit { let X = v; () } }
example : checkFnOk h1 = true := by native_decide
example : comptimeSlotMarker [h1] h1 = true := by native_decide

-- H2. …and with a reborrow outstanding it is a marker containing a marker:
-- `borrowₘ ℓ0 (loanₘ ℓ1)`.
def h2 : Decl := decl{ fn h2 (v : &mut List Nat) -> Unit { let b = &mut *v; let X = v; () } }
example : checkFnOk h2 = true := by native_decide
example : comptimeSlotMarker [h2] h2 = true := by native_decide

-- H3. THE ONE THAT MATTERS FOR THIS FEATURE: a capital `let` of a PAYLOAD while
-- the borrow-mode match's field loans are live. `collapseCDerefs` does not reach
-- them (they are wanted — the match is still open), so the binding is
-- `Cons (loanₘ ℓ1) (loanₘ ℓ2)`. This is the anticipatory-naming idiom writing a
-- marker into a spec binding, and it is accepted today.
def h3 : Decl := decl{ fn h3 (v : &mut List Nat) -> Unit
  { match v { Nil => (), Cons(hd, tl) => { let X = *v; () } } } }
example : checkFnOk h3 = true := by native_decide
example : comptimeSlotMarker [h3] h3 = true := by native_decide

-- H4. What does NOT happen: the marker cannot be laundered through a call, because
-- borrow-typed capital parameters are refused at the call site (`S26Modes` B9).
def eatB : Decl := decl{ fn eatB (B : &mut List Nat) -> Unit { () } }
def h4 : Decl := decl{ fn caller (v : &mut List Nat) -> Unit { let X = v; eatB(X); () } }
example : checkFnErr h4 "borrow-typed binders must be lowercase" [eatB, h4] = true := by
  native_decide

-- H5. …and citing H3's marker-bearing binding in a PROOF is refused — but by
-- `hasType` failing on the marker, which is an accident of a deferred feature
-- rather than a guard. The message is about M5, not about the marker, and that is
-- the diagnostics gap the marker-free guard would close.
def h5 : Decl := decl{ fn h5 (v : &mut List Nat) -> Unit
  { match v { Nil => (), Cons(hd, tl) => { let X = *v; idOf(X, X, Refl); () } } } }
example : checkFnErr h5 "cannot type value loanₘ" [idOf, h5] = true := by native_decide

-- H6. The HOLE half of the same invariant IS guarded, and names itself — which is
-- what makes H1–H3 look like an omission rather than a policy.
def h6 : Decl := decl{ fn h6 (l : List Nat) -> Unit { let y = l; let X = l; () } }
example : checkFnErr h6 "holds ⊥ (use-after-move or uninitialized in a comptime read)" = true := by
  native_decide

/-! ## §I. The ordering caveat, localized

    M26-E's warning — "a comptime argument mentioning `*v` would demand-collapse
    the loan it was just lent" — is real, and this pins exactly how far it
    reaches. It is an ORDERING constraint on anticipatory naming, not a limit on
    what can be named: name the payload BEFORE the borrow, never between the
    borrow and its use. -/

-- I1. THE FAILURE. Reborrow, then name the parent payload: the ⇝-read
-- demand-ends the reborrow, and the write through it hits a vacant slot.
def i1 : Decl := decl{ fn i1 (v : &mut List Nat) -> Unit
  { let b = &mut *v; let X = *v; *b := Nil; () } }
example : checkFnErr i1 "cannot peel a vacant slot" = true := by native_decide

-- I2. THE FIX, and it is free: the same three statements, naming first.
def i2 : Decl := decl{ fn i2 (v : &mut List Nat) -> Unit
  { let X = *v; let b = &mut *v; *b := Nil; () } }
example : checkFnOk i2 = true := by native_decide

-- I3. …and the reborrow's OWN payload may be named at any time, so the constraint
-- is about naming through a different path, not about naming at all.
def i3 : Decl := decl{ fn i3 (v : &mut List Nat) -> Unit
  { let b = &mut *v; let X = *b; *b := Nil; () } }
example : checkFnOk i3 = true := by native_decide

-- I4. Nor does it reach the borrow-mode match: naming the parent payload between
-- the match and a field write costs nothing (the field loans stay parked —
-- which is also why H3's marker gets in).
def i4 : Decl := decl{ fn i4 (v : &mut List Nat) -> Unit
  { match v { Nil => (), Cons(hd, tl) => { let X = *v; *tl := Nil; () } } } }
example : checkFnOk i4 = true := by native_decide

/-! ## §K. The classification — where `*old v` reaches, and where it does not

    ADDENDUM, on a sharpened framing: `old` is properly part of the DEREFERENCE —
    `*old v`, the payload of a borrow as of that borrow's construction — rather
    than a general value-at-binding-site operator, and it is ⇝-ONLY (no efficient
    runtime implementation exists, so the executing machine must never meet it).
    Under that framing the six cases split, and the split is not where the filings
    suggest.

    The machine's own recording is `entrySyms : List (Nat × Nat)`, populated in
    `seedTelescopeV`'s `.borrowT` case — **borrow PARAMETERS only** — and consumed
    in `reflectC` at `.app (.const "old") (.deref (.var v))`, which resolves to
    `.sym σ` and otherwise **falls back to the live deref**. Three consequences
    follow, and each is a test below. -/

-- K1. `old *v` ALREADY reads in a body ⇝-position, so the "extension from return
-- types to body positions" is largely already there for parameters.
def k1 : Decl := decl{ fn k1 (v : &mut List Nat) -> Unit { let X = old *v; () } }
example : checkFnOk k1 = true := by native_decide

-- K2. …and it reads in a ⇒-position too, which the ruling forbids. `old` is
-- `.app (.const "old") (.deref …)` — an ordinary application of a magic const, not
-- its own `Term` constructor — so `readR`'s pure lift sends it to `readC` and it
-- resolves. The slot then holds a runtime COPY of the entry payload while the
-- borrow is untouched: silent aggregate duplication, which §I of `S26Modes` says
-- is coherent only for ERASED binders. The ⇒-absence is NOT by construction
-- today; the seal's pattern (own constructor, no `Val` former, no ⇒ rule
-- writable) is what would make it so.
def k2 : Decl := decl{ fn k2 (v : &mut List Nat) -> Unit { let x = old *v; () } }
example : checkFnOk k2 = true := by native_decide

-- K3. The honest positive: after a mutation `old *v` names the entry, and a
-- capital `let` taken at entry converts with it — two routes to one σ, agreeing.
def k3 : Decl := decl{ fn k3 (v : &mut List Nat) -> Unit
  { let L = *v; *v := Nil; idOf(L, old *v, Refl); () } }
example : checkFnOk k3 [idOf, k3] = true := by native_decide

/-! ### K4. THE DEFECT: the recorded σ does not survive refinement

    The mirror of §G1, and it comes out the other way. `entrySyms` stores the σ's
    INDEX; `refineSym` rewrites OCCURRENCES. So after a match refines the entry
    payload, `reflectC` mints a fresh occurrence of an index nothing else mentions
    any more — the citation is a stale name that has lost the branch's knowledge,
    and the rejection prints exactly that. §G1's capital-let binding in the same
    position is swept and checks. Any work extending the entry-deref to body
    positions has to fix this first, and it is machinery, not syntax. -/
def k4 : Decl := decl{ fn k4 (v : &mut List Nat) -> Unit
  { match v { Nil => (), Cons(hd, tl) => { idOf(old *v, Cons (*hd) (*tl), Refl); () } } } }
example : checkFnErr k4 "(Id σ0 (Cons σ2 σ3))" [idOf, k4] = true := by native_decide

-- K5. The same cause at the projection route: `drop (S Z) (old *v)` is how a
-- whole-payload entry-deref would reach case 6's `rest`, and it sticks as an
-- unreduced `listRec` over the stale σ instead of computing to the tail.
def k5 : Decl := decl{ fn k5 (v : &mut List Nat) -> Unit
  { match v { Nil => (), Cons(hd, tl) => { idOf(drop (S Z) (old *v), *tl, Refl); () } } } }
example : checkFnErr k5 "listRec" [idOf, k5] = true := by native_decide

/-! ### K6. THE REACH: mid-body reborrows are not recorded, and the fallback lies

    `entrySyms` covers telescope borrow parameters. A reborrow created inside the
    body — `&mut *v` handed to a call, `&mut hi` on a local, a match field — has no
    entry recorded, so `old *b` takes `reflectC`'s fallback and silently means
    NOW: after a write through `b`, `old *b` IS the written value. Accepted,
    wrong, no diagnostic. That matters because the mid-body reborrow is where most
    of the borrow class lives — case 2's σ′, case 3's `mkUb`/`mkLb`/`fin`, case
    1's `*tl`. -/
def k6 : Decl := decl{ fn k6 (v : &mut List Nat) -> Unit
  { let b = &mut *v; *b := Nil; idOf(old *b, Nil, Refl); () } }
example : checkFnOk k6 [idOf, k6] = true := by native_decide

-- K7. The parameter's own `old *v` in the same program is correct (σ_entry, not
-- `Nil`) — which is what says K6 is the fallback and not a general breakage.
def k7 : Decl := decl{ fn k7 (v : &mut List Nat) -> Unit
  { let b = &mut *v; *b := Nil; idOf(old *v, Nil, Refl); () } }
example : checkFnErr k7 "(Id σ0 Nil)" [idOf, k7] = true := by native_decide

/-! ### K8. Case 2 is borrow-shaped and OUT OF `*old v`'s REACH

    `swap_at`'s doomed value is σ′ — the payload of the reborrow the SECOND
    `set_at` receives, at that reborrow's construction. `*old v` names the
    parameter's entry, σ_entry, which is a different list. So the case that NAMED
    the feature ("a way to bind a snapshot — `let` at comptime, naming an exit the
    way `old` names an entry") is not served by the entry-deref; §B1's
    `let M = *v` is what serves it. -/
def k8 : Decl :=
  decl{ fn swap_at (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j,
                    p2 : Le (S j) (len *v), hi : Le (S i) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { let a = nth i (*v);
          let b = nth j (*v);
          let Bridge = swapL_set i j (old *v) pij p2;
          let h1 = set_at(&mut *v, j, a, p2);
          let hlen = id_trans Nat (len *v) (len (set j a (old *v))) (len (old *v))
                       (id_congr (List Nat) Nat len (*v) (set j a (old *v)) h1)
                       (len_set j a (old *v));
          let hi2 = le_rw_r (S i) (len (old *v)) (len *v)
                      (id_sym Nat (len *v) (len (old *v)) hlen) hi;
          let h2 = set_at(&mut *v, i, b, hi2);
          id_trans (List Nat) (*v) (set i b (old *v)) (swapL i j (old *v))
            h2
            (id_trans (List Nat) (set i b (old *v)) (set i b (set j a (old *v)))
               (swapL i j (old *v))
               (id_congr (List Nat) (List Nat) (λ (z : List Nat). set i b z)
                 (old *v) (set j a (old *v)) h1)
               Bridge) } }
example : checkFnOk k8 [setAt, k8] = false := by native_decide

/-! ### K9. The classification, and the two answers

    | case | the doomed value | class | reached by `*old v`? |
    |---|---|---|---|
    | 1 | `w`, a consumed data PARAMETER | NON-BORROW | out of scope by the ruling; `let W = w` serves it (§A2) |
    | 1 | `*tl`, a match-field reborrow's entry | BORROW, mid-body | NO — not recorded; `old *tl` means "now" (K6) |
    | 2 | σ′, the payload before the 2nd call | BORROW, mid-body, ANONYMOUS | NO (K8) |
    | 3 `mkCnt` endpoint | the parameter's entry payload | BORROW, PARAMETER | in principle — but stale under refinement (K4) |
    | 3 `mkCnt`'s `rest` | a subterm of that payload | BORROW-derived | NO — projection sticks (K5) |
    | 3 `mkUb`/`mkLb`/`fin` | pre/post-sort `*v` and `hi` | BORROW mid-body + moved data | NO |
    | 4 | `hfuel`, a consumed proof PARAMETER | NON-BORROW | n/a — modes remove the pain entirely (§E3) |
    | 5 | the staged `len *v` | NON-BORROW, and RUNTIME | n/a — not this feature (§F2) |
    | 6 | `rest`, a subterm of the entry payload | BORROW-derived | NO (K5) |

    **(a) Do modes + capital `let` fully cover the NON-BORROW class today? YES.**
    Consumed proofs are covered twice over — by the callee's capital parameter,
    which removes the pain rather than naming around it (§E3), and by
    `let HF = hfuel` where the callee is not yours (§E2). Consumed data binders
    are covered at both granularities the corpus uses: a parameter (§A2's `W`) and
    a match binder (§C1's `R`). Nothing in the non-borrow class waits on new
    machinery.

    **(b) Is the borrow-class residual "the entry-deref citation extended from
    return-type positions to body positions"? NO** — three independent reasons.

    1. *The extension is already there* for the case it covers (K1, K3).
    2. *It is broken in exactly the situation bodies are in.* The recorded σ is an
       INDEX and `refineSym` rewrites OCCURRENCES, so a body citation after any
       match on the payload is stale (K4) — while the capital-let binding in the
       same position is swept and works (§G1). This is the load-bearing gap.
    3. *It does not reach where the pain is.* `entrySyms` records parameters only;
       most of the borrow class is mid-body reborrows, usually anonymous call
       arguments, and `old` on such a borrow silently returns the LIVE payload
       (K6). Capital `let` reaches all of them, because it names a VALUE at a
       chosen moment rather than a borrow at its construction.

    **On ⇝-only by construction: not today** (K2). Making it so the way the seal is
    comptime-free means giving `old` its OWN `Term` constructor with no `Val`
    former and no ⇒ rule — at which point the question is unaskable rather than
    refused. A second reason to want that constructor: `collapseCDerefs` descends
    into the inner deref and demand-ends loans, so even the comptime read has a
    state side effect today (K7 leaves the reborrow at `⊥`). -/

/-! ## §J. The verdict

    **The hypothesis holds.** Capital `let` already IS anticipatory snapshot
    naming. Every staged builder in the corpus is one binding, placed at the
    timepoint the body needs to remember, and the mathematics is then written
    once at its own use site instead of λ-abstracted over "everything that
    arrives later".

    | case | filing | staged builders | after | decl lines |
    |---|---|---|---|---|
    | 1 | `append_back`'s moved `w` (M23-ii) | 0 — it was already a plain `let` | `let W = w` names the PARAMETER (§A2) | 11 → 11 |
    | 2 | `swap_at`'s superseded exit (M23-iii) | 1 (`finish`, 2 binders) | `let M = *v` | 23 → 22 |
    | 3 | `quicksort`/`quicksortA`'s four (M25 `mkTop`) | 4 (15 binders) | 5 `let`s, one per timepoint | 70 → 58 |
    | 4 | `hfuel` before consumption (M25, R16) | 1 (`mkHf`) | `let HF = hfuel` — or nothing at all, M26-B | — |
    | 5 | the `len *v` bound (M26-E) | 0 | NOT this feature: the value is runtime | — |
    | 6 | `partition`'s `mkL`/`mkR` (M23-iv) | 2 (6 binders) | `let R = rest` | 37 → 32 |

    Line counts understate it: the derivations are the same size either way,
    because they are the mathematics. What goes away is 8 builders and 20
    λ-binders across the corpus, and — more than the lines — the ORDER, since a
    body no longer has to be written inside-out.

    **The residual feature is exactly three things, and only one is machinery.**

    1. *Retroactivity is sugar.* `old x` elaborating to a capital `let` at `x`'s
       binding site buys the cases where the author did not know in advance what
       would be needed — §A2 costs two lines where `old w` would cost zero. Pure
       surface: the elaborated form is what §A–§D check today.
    2. *The marker-free guard is real machinery, and it is missing* (§H). A
       capital `let` admits `borrowₘ`/`loanₘ` into an erased slot silently; the
       refusal comes later, at `hasType`, in a message about a deferred feature.
       The hole half of the same invariant IS guarded and names itself (H6), so
       this reads as an omission rather than a policy. It is a diagnostics defect
       today, not a soundness one — nothing can type a marker — but it is the
       exact class that cost M23-ii and M23-iv a debugging cycle each.
    3. *The one-timepoint rule is already the semantics* (§G), not a rule to add:
       `refineSym`'s sweep keeps the binding honest under later matches, and a
       call re-mints rather than refines, so the binding keeps the older value.
       Both directions are pinned, and neither needed a line of new machinery.

    **One ordering constraint comes with the feature** (§I): name a payload
    BEFORE a borrow of it is taken, never between the borrow and its use, because
    the ⇝-read demand-ends the loan. It costs nothing where it applies (I2 is I1
    with two statements swapped) and it does not reach the borrow-mode match.

    **And one case is not this feature at all.** Case 5's staged `len *v` is a
    RUNTIME value — it is the callee's fuel — so it must stay a lowercase `let`
    (F2), and what forces the staging is the demand-collapse (F3), not naming. -/

end Dllbc.Tests.S27OldProbe
