import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.FnMacro
import Dllbc.AlphaEq
import Dllbc.Tests.S23Direct
import Dllbc.Tests.S26Seal
import Dllbc.Tests.S26Modes
import Dllbc.Tests.S26Modes
import Dllbc.Tests.S26Rec
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
function; it can never produce an unsound acceptance. That is why the tests below
are allowed to be *comparisons* (does the macro agree with the hand elaboration,
does it agree with `checkFn`) rather than proofs.
-/

open Dllbc
open Dllbc.Tests.S26Seal (ok rejects)
open Dllbc.StdLemmas (le_up_r leb_true_le leb_false_gt le_pred_l
  count_cons_l count_cons_r len Ub Lb)

namespace Dllbc.Tests.S26Fn

/-- Elaborate and bind, which is the `let` §8 says a declaration is. -/
def elabIn (d : FnDef) : Except String FnDef :=
  (FnMacro.fnElab d).map (fun t =>
    { name := "caller", telescope := [], retType := .const "Unit",
      body := .letIn ⟨900, "f"⟩ t .unit })

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

/-! ## §A. The non-recursive case, and the round trip that says the Π is right

    A `fn` with no `[k]` is one runtime λ sealed at its signature — the degenerate
    case §4 calls the smell test, now reached from a declaration. It lands first
    because it exercises `telePi` alone: if the Π were built wrongly, everything
    downstream would fail for a reason that had nothing to do with recursors. -/

def pushD : FnDef := decl{ fn pushD (e : Nat, v : &mut List Nat) -> Unit
  { let tail = *v; *v := Cons(e, tail); () } }
-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)
example : elabOk pushD = true := by native_decide

/-- `telePi` and the kernel's `piPeel` are inverse, which is the property the
    whole elaboration rests on: the macro writes a Π, the kernel takes it apart
    again, and the telescope that comes back is the one that went in. Asserted
    directly rather than inferred from the checks passing. -/
def roundTrips (d : FnDef) : Bool :=
  let tel := FnMacro.teleVars d.telescope
  match piPeel (tel.map (·.1)) (FnMacro.telePi tel d.retType) with
  | .error _ => false
  | .ok (tel', ret') => tel' == tel && ret' == d.retType

example : roundTrips pushD = true := by native_decide
example : roundTrips Tests.S23Direct.splitOff = true := by native_decide
example : roundTrips Tests.S23Direct.quicksort = true := by native_decide
-- …and over a battery, so the round trip is a property and not three points.
example :
  [pushD, Tests.S23Direct.splitOff, Tests.S23Direct.quicksort,
   Tests.S23Direct.partition, Tests.S26Modes.step].all roundTrips = true := by native_decide

/-! ## §B. `split_off` — the macro against the hand elaboration

    M26-C hand-wrote `split_off` as a sealed recursor and checked it. That makes
    it an ORACLE the macro can be held to, and a strong one: it was written before
    the macro existed, by reading §7 rather than by reading the code.

    Compared up to α, not on the nose: the macro threads binder ids linearly while
    the hand version got them from the surface elaborator, so the two agree on
    binding structure and differ on numbering — which is exactly what
    `FnDef.alphaEq` was built for (its own docstring says so). -/

def splitElab : Except String Term := FnMacro.fnElab Tests.S23Direct.splitOff

/-- The hand elaboration from M26-C, extracted from its caller. -/
def splitHand : Term :=
  match Tests.S26Rec.splitSealed.body with
  | .letIn _ t _ => t
  | t => t

/-- Wrap a term as a `FnDef` so `alphaEq` (which is `FnDef`-shaped) can compare two. -/
def asDecl (t : Term) : FnDef :=
  { name := "x", telescope := [], retType := .const "Unit", body := t }

example :
  (match splitElab with
   | .ok t => FnDef.alphaEq (asDecl t) (asDecl splitHand)
   | .error _ => false) = true := by native_decide

-- …and the macro's output checks, which is the claim that matters: agreeing with
-- my hand term would be worth little if my hand term were wrong, and it is the
-- kernel that says otherwise (constraint 7 — the output is re-derived, not
-- trusted).
example : elabOk Tests.S23Direct.splitOff = true := by native_decide
-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)

-- The oracle is not vacuous: α-equality can say NO. Compared against the same
-- function's BASE arm, which is a real term of the same file and shape family.
example :
  (match splitElab with
   | .ok t => FnDef.alphaEq (asDecl t) (asDecl (Tests.S26Rec.splitSealed.body))
   | .error _ => false) = false := by native_decide

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

def qsTable : List FnDef := [Tests.S23Direct.partition, Tests.S23Direct.appendBack]

-- **RETIRED with the J1 bridge** (M27-δ). This elaborated `quicksort` alone and
-- checked it against a TABLE of un-elaborated callees — the half-migrated form
-- §8 kept alive while both paths existed. With one path the whole COHORT must
-- migrate, and `partition`/`append_back` are the `[v]` payload-decrease class,
-- which declines. The carrier is `S26Prog.quicksortP` on the fuel-threaded
-- cohort, asserted there and in `S27Dispose` §B.
-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)

/-- **The `[k]` guard is GONE from the elaborated form, and nothing replaces it.**
    The macro's output resolves its own recursion through `ih`, so the table it is
    checked against need not contain it — there is no self-call left to admit at a
    postcondition, and therefore nothing for a decrease check to police. §7's
    "the guard evaporates", as the absence of an entry. -/
example : (match elabIn Tests.S23Direct.quicksort with
           | .ok c => (calleeNames c.body).contains "quicksort"
           | .error _ => true) = false := by native_decide

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

/-! ### E2. …and the flagship's call site, so the cost is MEASURED

    "Every caller supplies them" is the other half of decision 8's price, and a
    claim about a cost should be paid once rather than estimated. `quicksortF` is
    `S23Direct.quicksort` with exactly one call site retargeted — the same body
    otherwise — and it checks.

    Two things it pins that are not obvious from the signature change alone. The
    bound the caller hands over is `hfuel` UNCHANGED: after `*v := rest` the callee
    wants `Le (len rest) f2`, and `hfuel : Le (len (Cons x rest)) (S f2)` already IS
    that, by the same definitional descent the callee's own recursion uses. And
    `hfuel` survives the call — quicksort needs it twice more, for its own two
    recursive calls — which works only because `partitionF`'s bound parameter is
    CAPITAL and therefore ⇝-read. Under phase A that call would have moved it
    (R16), and the migration would have needed staging. -/

/-- Retarget the one `partition` call — supply the fuel and the bound — and carry
    the function's own new name onto its self-calls. -/
partial def toPartitionF (f2 : Var) : Term → Term
  | .call f as =>
    let as' := as.map (toPartitionF f2)
    if f == "partition" then .call "partitionF" (.var f2 :: as' ++ [.var ⟨2, "hfuel"⟩])
    else if f == "quicksort" then .call "quicksortF" as'
    else .call f as'
  | .letIn x r b => .letIn x (toPartitionF f2 r) (toPartitionF f2 b)
  | .assign a b c => .assign (toPartitionF f2 a) (toPartitionF f2 b) (toPartitionF f2 c)
  | .seq a b => .seq (toPartitionF f2 a) (toPartitionF f2 b)
  | .ctorApp n as => .ctorApp n (as.map (toPartitionF f2))
  | .callV x as => .callV x (as.map (toPartitionF f2))
  | .borrow t => .borrow (toPartitionF f2 t)
  | .deref t => .deref (toPartitionF f2 t)
  | .matchE sc e bs =>
    .matchE sc e (bs.map (fun b => Branch.mk b.ctor b.binders (toPartitionF f2 b.body)))
  | t => t

def quicksortF : FnDef :=
  let q := Tests.S23Direct.quicksort
  let f2 := (FnMacro.succBinder ⟨0, "fuel"⟩ q.body).getD ⟨0, "fuel"⟩
  { q with name := "quicksortF", body := toPartitionF f2 q.body }

-- (the DECLARED twin's check retired with `checkFn`, M27-δ — J1's "both
-- worlds" had two worlds, and there is one now. The `elabOk` assertion beside
-- this one is what the claim became.)
-- …and elaborated through the macro, against a table that no longer contains it.
-- Same disposition: the table here still holds the un-fuel-threaded
-- `append_back`, which declines. `S26Prog.quicksortP [partitionF, appendBackF]`
-- is the fully-migrated cohort and is the carrier.

-- The migration really did change the call: the body names `partitionF` and not
-- `partition`, so the two assertions above are about the new callee.
example : ((calleeNames quicksortF.body).contains "partitionF"
        && !((calleeNames quicksortF.body).contains "partition")) = true := by native_decide

end Dllbc.Tests.S26Fn
