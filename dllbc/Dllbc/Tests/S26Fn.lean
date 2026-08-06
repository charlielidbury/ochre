import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.FnMacro
import Dllbc.Tests.S23Direct
import Dllbc.Tests.S26Seal
import Dllbc.Tests.S26Modes
import Dllbc.Migrate

/-!
# §26 (M26-D) — `fn` is a macro

`combining-fns.md` §7: `fn f (…) -> R { body }` is a binding of `.seal ⟨recursor
term⟩ ⟨the Π⟩`, `[k]` survives only as the macro's hint for which argument becomes
the scrutinee, and the motive is derived from the signature. `Dllbc/FnMacro.lean`
is that elaboration; this file is its evidence.

**Constraint 7 is what makes the whole thing safe to attempt.** Nothing in the
kernel imports `FnMacro`, so macro output is re-checked from scratch at the seal —
where `ih` is a binder and each arm is checked at its own constructor. A bug here
produces a program that fails to check, or one that checks as a different
function; it can never produce an unsound acceptance.

The evidence is therefore **verdicts** — the elaboration checks, or is refused
with a reason. It used to be comparisons as well (against `checkFn`, and against
M26-C's hand elaboration up to α); the first went with `checkFn` in M27-δ and the
second in M28 cluster C, on the same argument constraint 7 makes: what a
comparison could tell you, the kernel already tells you, and only the kernel's
answer is trustworthy about a term neither of us wrote by hand.
-/

open Dllbc
-- (the `S26Seal.ok`/`rejects` open went with those helpers in M28 ν; nothing here
-- used them — every `.ok` below is a pattern match on an `Except`.)
open Dllbc.StdLemmas (le_up_r leb_true_le leb_false_gt le_pred_l
  count_cons_l count_cons_r len Ub Lb)

namespace Dllbc.Tests.S26Fn

/-- The macro's output checks. `table` is what its NON-self calls resolve
    against — self-calls are gone by construction, having become `ih`.

    **This and `ok` are now the same function** (M27-δ), and the collapse is the
    milestone rather than a tidying: "the macro's output checks" and "the
    declaration checks" were two claims while there were two paths, and §7's
    "`fn` IS a macro" is precisely the statement that they are one. The assertions
    below keep their own names because what they are ABOUT still differs — one
    reads as a property of the elaboration, the other of the corpus. -/
def elabOk (d : FnDef) (table : List FnDef := []) : Bool :=
  Migrate.progOkOf d (table ++ [d])

/-- The macro refuses, with `needle` in the message. -/
def elabRejects (d : FnDef) (needle : String) : Bool :=
  match FnMacro.fnElab d with
  | .error e => strContains e needle
  | .ok _ => false

/-! ## §A. The non-recursive case

    A `fn` with no `[k]` is one runtime λ sealed at its signature — the degenerate
    case §4 calls the smell test, now reached from a declaration. It lands first
    because it exercises `telePi` alone: if the Π were built wrongly, everything
    downstream would fail for a reason that had nothing to do with recursors.

    **`roundTrips` went in M28 cluster C.** It asserted `telePi` and `piPeel`
    inverse — build the Π from a telescope, take it apart again, get the telescope
    back — over `pushD`/`splitOff`/`quicksort` and then a five-function battery,
    "asserted directly rather than inferred from the checks passing". Inferring it
    from the checks passing is exactly what the e2e rule asks for, and the
    inference is sound in the direction that matters: `piPeel` is what the KERNEL
    does to a seal, so a `telePi` that were not its inverse would make every
    `elabOk` below fail at the signature. A property whose failure mode is
    "everything reddens" does not need its own assertion. -/

def pushD : FnDef := decl{ fn pushD (e : Nat, v : &mut List Nat) -> Unit
  { let tail = *v; *v := Cons(e, tail); () } }
-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)
example : elabOk pushD = true := by native_decide

/-! ## §B. `split_off` — the macro's output checks

    M26-C hand-wrote `split_off` as a sealed recursor and checked it, before the
    macro existed, by reading §7 rather than by reading the code. This section held
    the macro to that term as an ORACLE: elaborate `splitOff`, wrap both terms as
    `FnDef`s, compare with `FnDef.alphaEq` — up to α, because the macro threads
    binder ids linearly while the hand version got them from the surface
    elaborator — plus a not-vacuous control comparing against the same function's
    base arm, which `alphaEq` said NO to.

    **The oracle comparisons are deleted (M28, cluster C.)** What remains is the
    verdict, which the section's own commentary already named as the claim that
    matters: agreeing with a hand term is worth little if the hand term is wrong,
    and it is the KERNEL that says otherwise. Constraint 7 is the reason —
    nothing in the kernel imports `FnMacro`, so the output is re-checked from
    scratch at the seal, and an elaboration that agreed with my term and failed
    to check would be a bug in both. The hand term has not left the tree:
    `S26Rec` still holds `splitSealed` and still checks it. Only the comparison
    is gone, with `splitElab`/`splitHand`/`asDecl`, which existed for it alone. -/

example : elabOk Tests.S23Direct.splitOff = true := by native_decide
-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)

/-! ### B2. The macro path rejects exactly what the declared path rejects

    `S23Direct` guards `splitOff` with four twins — three spec lies and a body lie
    — precisely so its acceptance is not a coincidence, and notes the division of
    labour: the spec lies are caught on the `i = Z` path, the body lie on the
    recursive one. Running the SAME four through the macro is what turns "the
    elaborated form checks" into "the elaborated form is the same function": it
    accepts what the declaration accepts and refuses what it refuses, twin for
    twin. -/

def splitTwins : List FnDef :=
  [ Tests.S23Direct.splitOffLieTake, Tests.S23Direct.splitOffLieDrop,
    Tests.S23Direct.splitOffLieSwap, Tests.S23Direct.splitOffLieHead ]

-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)
-- …and so does the elaborated one, which is the claim.
example : splitTwins.all (fun d => !(elabOk d)) = true := by native_decide
-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)

/-! ## §C. `quicksort` — the flagship, and the case that fixed the elaboration

    `quicksort`'s `match fuel` is NESTED: inside `match l`'s `Cons` branch, after a
    `let`, and its `Nil` branch never mentions fuel at all. That is what ruled out
    "split the body at its `match k`" and forced the elaboration to be **the whole
    body twice, with `match k` resolved per arm** — which is the ι rule read
    backwards, and is uniform over where the match sits.

    Read the base arm to see it work: it is the entire body with the fuel match
    replaced by its `Z` branch, so the `Nil` case still returns its pair and the
    `Cons` case becomes `botElim Unit hfuel` — the dead path, discharged because
    `hfuel : Le (S (len rest)) Z` IS `Bot`. Nothing about that is special-cased. -/

-- **RETIRED with the J1 bridge** (M27-δ). This elaborated `quicksort` alone and
-- checked it against a TABLE of un-elaborated callees — the half-migrated form
-- §8 kept alive while both paths existed. With one path the whole COHORT must
-- migrate, and `partition`/`append_back` are the `[v]` payload-decrease class,
-- which declines. The carrier is `S26Prog.quicksortP` on the fuel-threaded
-- cohort, asserted there and in `S27Dispose` §B.
-- (`qsTable`, the un-elaborated callee table it was checked against, went with it
-- in M28 cluster C — it had outlived its only reader by a milestone.)
-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)

-- **The `[k]` guard is GONE from the elaborated form, and nothing replaces it.**
-- The macro's output resolves its own recursion through `ih`, so the table it is
-- checked against need not contain it — there is no self-call left to admit at a
-- postcondition, and therefore nothing for a decrease check to police. §7's "the
-- guard evaporates", as the absence of an entry.
--
-- Asserted by `calleeNames` on the elaborated body until M28 cluster C, and now
-- carried by the verdicts instead — which say it more strongly. `elabOk` checks a
-- declaration against `[d]` alone, and every recursive subject in this file passes
-- it: if a self-call survived elaboration it would be an unresolved name in a
-- table that does not contain the function, and §8 rejects a forward reference
-- (`S26Fuel` §D pins exactly that rejection, on a program). The absence of the
-- entry is therefore what makes the presence of the check possible. `elabIn`, the
-- caller-wrapper this probe needed to have a body to inspect, went with it.

/-! ## §D. What the macro refuses, and why each refusal is the honest one -/

-- §12 decision 8. `partition [v]` decreases through a BORROW's payload, which has
-- no recursor form — §9's eliminator is filed, not built. Fuel is something a
-- programmer threads (it changes the signature, and every caller); a macro that
-- invented it would be changing the function's interface behind its author.
example : elabRejects Tests.S23Direct.partition "decision 8" = true := by native_decide

-- §6.2's declared backs are a `FnDef` mechanism with no seal counterpart. M23's
-- corpus declares none, which is why the cohort is unaffected.
-- RETIRED in M27-P2 with the mechanism: there is no `back` field to decline, so
-- the refusal has no subject. `S27Dispose` §C records where §6.2's claims went.

/-! ## §E. `partition`, FUEL-THREADED — §12 decision 8 paid on a real function

    The macro refuses `partition [v]` because payload decrease has no recursor
    form, and refuses it *pointing at decision 8*: fuel-threading is the blessed
    interim, and fuel is a SOURCE change — the signature grows a parameter and a
    bound, and every caller supplies them — not something an elaboration invents
    behind its author. This is that source change, made once so the cost of the
    accepted regression is a measured thing rather than an estimated one.

    Written here rather than in `S23Direct` so the original `[v]` form stays
    exactly as it was (J1: both worlds alive), and so the migration is legible as
    a diff against it: the telescope gains `fuel` and `Hf`, the `Cons` branch
    gains a `match fuel` whose `Z` arm is dead, and the self-call gains two
    arguments. The body is otherwise character-for-character the original.

    **The bound needs no lemma, and that is the interesting part.** At the
    recursive call `Hf : Le (len (Cons x rest)) (S f2)`, which IS
    `Le (len rest) f2` definitionally — the same bounds-cursor descent M14 found
    and M26-C's §I used. Fuel-threading costs a parameter and a dead branch; it
    does not cost a proof.

    **And `Hf` is CAPITAL, which is phase B paying for phase D.** The bound is
    passed to the recursive call and then still needed by the caller; a lowercase
    proof parameter would MOVE it (R16), and the original `partition` never had to
    care because it had no bound to thread. -/

-- Read by `S27Dispose` (§B's paid-twin assertions, its `partFLie` record-update
-- twins and `partitionLosesF`) and by `S26Prog`; cleanup belongs to the finale.
def partitionF : FnDef :=
  decl{ fn partitionF [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (len *v) fuel)
        -> Σ (hi : List Nat) → Σ (hub : Ub p (*v)) → Σ (hlb : Lb p hi)
             → Σ (hl1 : Le (len *v) (len (old *v))) → Σ (hl2 : Le (len hi) (len (old *v)))
             → Π (n : Nat) → Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))
        { let l = *v;
          match l {
            Nil => { *v := Nil;
                     Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (n : Nat). Refl))))) },
            Cons(x, rest) => match fuel {
              -- Out of fuel with a non-empty list: `Hf : Le (S (len rest)) Z` IS
              -- `Bot`, so the path is dead — the same ex-falso `quicksort` already
              -- carried, arriving here as the cost of the guard's removal.
              Z => botElim Unit Hf,
              S(f2) => {
              let mkL = (λ (a : List Nat). λ (b : List Nat).
                          λ (h : Π (n : Nat) → Id Nat (add (count n a) (count n b)) (count n rest)).
                            λ (n : Nat). count_cons_l n x a b rest (h n));
              let mkR = (λ (a : List Nat). λ (b : List Nat).
                          λ (h : Π (n : Nat) → Id Nat (add (count n a) (count n b)) (count n rest)).
                            λ (n : Nat). count_cons_r n x a b rest (h n));
              let lr = len rest;
              *v := rest;
              -- The one changed line: fuel and the bound go with the call, and the
              -- bound is `Hf` UNCHANGED — `Le (len (Cons x rest)) (S f2)` already IS
              -- `Le (len rest) f2`.
              let r = partitionF(f2, &mut *v, p, Hf);
              match r { Pair(hi, q1) => match q1 { Pair(hub, q2) => match q2 { Pair(hlb, q3) =>
              match q3 { Pair(hl1, q4) => match q4 { Pair(hl2, hcnt) => {
                if e : leb x p {
                  let lo = *v;
                  let hub2 = Pair(leb_true_le x p e, hub);
                  let hl2b = le_up_r (len hi) lr hl2;
                  let cnt = mkL lo hi hcnt;
                  *v := Cons(x, lo);
                  Pair(hi, Pair(hub2, Pair(hlb, Pair(hl1, Pair(hl2b, cnt)))))
                } else {
                  let hlb2 = Pair(le_pred_l p x (leb_false_gt x p e), hlb);
                  let hl1b = le_up_r (len *v) lr hl1;
                  let cnt = mkR (*v) hi hcnt;
                  Pair(Cons(x, hi), Pair(hub, Pair(hlb2, Pair(hl1b, Pair(hl2, cnt)))))
                }
              } } } } } }
            } }
          } } }

-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)
-- …and so does its elaboration, which is what decision 8 buys: `partition` is now
-- expressible as a sealed recursor, at the cost of one parameter and one dead
-- branch.
example : elabOk partitionF = true := by native_decide

/-! ### E2. …and the flagship's call site — RETIRED HERE (M28 cluster C)

    "Every caller supplies them" is the other half of decision 8's price, and this
    section paid it: `quicksortF` was `S23Direct.quicksort` with its one `partition`
    call retargeted, built by `toPartitionF`, a term-rewriting pass over the body.
    Its own check had already retired in M27-δ (the table it was checked against
    still held the un-fuel-threaded `append_back`, which declines), leaving one
    `calleeNames` assertion — that the rewritten body names `partitionF` and not
    `partition` — which is a structural probe of a term-rewriter's output, not a
    verdict. It goes, and `quicksortF`/`toPartitionF` go with it, having no other
    reader in the tree.

    **The claim survives with a better carrier**, and it is the one the retired
    assertion already pointed at: `S26Prog.quicksortP` on the fully-migrated cohort
    `[partitionF, appendBackF]`, asserted there and in `S27Dispose` §B. That is a
    call site that supplies the fuel and the bound and CHECKS, which is what "the
    cost is measured" meant — where this section had a caller that was rewritten
    and then inspected rather than run.

    The two facts §E2's prose pinned are unaffected and are properties of that
    cohort: the bound handed over is `hfuel` UNCHANGED (after `*v := rest` the
    callee wants `Le (len rest) f2`, and `hfuel : Le (len (Cons x rest)) (S f2)`
    already IS that, by the same definitional descent the callee's own recursion
    uses), and `hfuel` SURVIVES the call — quicksort needs it twice more — which
    works only because `partitionF`'s bound parameter is CAPITAL and therefore
    ⇝-read. Under phase A that call would have moved it (R16), and the migration
    would have needed staging. -/

end Dllbc.Tests.S26Fn
