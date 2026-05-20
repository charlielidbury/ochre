# MPSS Redesign: Non-Promotion Tracking

## 1. What the paper's non-promotion tracking means concretely

### 1.1 The statement in Lemma 2 (Diamond Property, p.9:9)

Lemma 2 says:

> Moreover, for any variable x, if in the derivation of
> Gamma_0;s_0 |- t_0 ===> t_1 (resp. t_0 ===> t_2)
> there isn't an application of Rule ME-PRO that makes a promotion
> of variable x, then in the derivation of
> Gamma_2;s_2 |- t_2 ===> t_3 (resp. Gamma_1;s_1 |- t_1 ===> t_3)
> there won't be an application of Rule ME-PRO that makes a promotion
> of variable x.

This is a **second clause** of the diamond property: not only does a
joining term t_3 exist, but the *set of promoted variables* is
preserved across the diamond's edges.  If the left edge doesn't
promote variable x, the top edge won't either; if the bottom edge
doesn't promote x, the right edge won't either.

### 1.2 Where non-promotion tracking is used

**Commutativity (Theorem 1 / Lemma 1, appendix p.9:17--9:20).**

The critical usage is in the **ME-Bet + Ms-App** case (p.9:20).
The setup:

- Bottom edge: Gamma;s |- (lam t.u_0) v_0 ===> u_1[x\v_1]  (ME-BET)
  - Gamma;s_0 |- u_0 ===> u_1       (under Ann.sub context)
  - Gamma;nil |- v_0 ===> v_1
- Left edge:  Gamma;s |- (lam t.u_0) v_0 <==> (lam t.u_2) v_0  (MS-APP)
  - Gamma; v_0::s |- lam t.u_0 <==> lam t.u_2  (MS-FOP)
    - Gamma, x===v_0; s |- u_0 <==> u_2

The proof needs to apply the IH on u_0 in context Gamma, x===v_0; s.
The bottom-edge reduction of u_0 is under a **sub** annotation
(Ann.sub t from ME-BET), but the left-edge reduction is under an
**equiv** annotation (Ann.equiv v_0 from MS-FOP).

The paper resolves this as follows (p.9:20, paragraph starting
"As explained in the introduction paragraph"):

> We know that if the rule ME-PRO appears in the derivation tree
> Gamma;s |- (lam t.u_0) v_0 <==> t_2, then we have in fact
> Gamma;s |- u_0 ===> u_2 (which is because otherwise we'd have
> Gamma, x === v_0; s |- u_0 ===> u_2 and we conclude by Lemma 2).
> We therefore assume that the rule ME-PRO doesn't appear in the
> derivation tree Gamma;s |- t_0 <==> t_2.

The key insight: **if ME-PRO is never used to promote variable x
(the formal parameter) in the subtyping derivation**, then the
derivation under Ann.equiv v_0 is actually just the same derivation
that would work under Ann.sub t --- the annotation at position 0 is
never consulted. The paper then reasons:

1. The subtyping derivation Gamma, x===v_0; s |- u_0 <==> u_2 either
   promotes x or it doesn't.
2. If it doesn't promote x, the derivation works under any annotation
   at position 0 (in particular, Ann.sub t).
3. If it DOES promote x, then ME-PRO fires on x ===alpha in Gamma,
   which means the subtyping step is actually an equivalence step
   (the sub step becomes ===> via MS-EQU). This collapses to
   Gamma;s |- u_0 ===> u_2, and we apply Lemma 2 (diamond) instead.

Then, by Lemma 2's second clause, the diamond's output derivation
*also* doesn't promote x, enabling the substitution lemma (Lemma 30)
to apply.

### 1.3 Where it is used in the diamond proof itself

In the **ME-App + ME-Bet** case of the diamond (p.9:22--9:23):

The derivation Gamma_0, x === v_0; s_0 |- u_0 ===> u_2 is known
not to promote x (because the original derivation goes through
ME-APP which pushes v_0 onto the stack, and ME-FOP pops it into an
equiv annotation --- the body reduction under this equiv annotation
doesn't promote x to v_0 since x was just introduced).

By Lemma 2's second clause, the diamond's output derivation also
doesn't promote x.  This is needed to apply the substitution lemma
(Lemma 32, p.9:44) which requires the derivation to be over an
equiv context.

### 1.4 Concrete example

Consider: Gamma; nil |- (lam Top. x) v  where x is a free variable.

- ME-BET: reduces to v (after substituting x/0 -> v in the body bvar 0)
  - Body reduction under Ann.sub Top: bvar 0 ===> bvar 0 (ME-VAR)
  - ME-PRO cannot fire on bvar 0 because the annotation is Ann.sub, not Ann.equiv
- MS-APP + MS-FOP: promotes the body under Ann.equiv v
  - bvar 0 can now be promoted via ME-PRO to v (since Ann.equiv v is at position 0)
  - This promotion USES ME-PRO on variable 0

The paper's non-promotion tracking says: since the bottom edge
(ME-BET) doesn't promote variable 0 (it can't -- it's under Ann.sub),
the right edge of the diamond also won't promote variable 0.

If ME-PRO IS used on the left edge (promoting bvar 0 to v), then
the whole sub derivation is actually an equiv derivation (via MS-EQU),
and we fall into the diamond case instead of the commutativity case.


## 2. How to encode non-promotion tracking in Lean with de Bruijn

### 2.1 Current problem: `equivRed_change_ann` is FALSE

Our current MPSS.lean (line 397--401) has:

```
def equivRed_change_ann
    (h : MEquivRed (Ann.equiv v :: Gamma) s body body')
    : MEquivRed (Ann.sub dom :: Gamma) s body body' :=
  sorry
```

This is FALSE.  If h uses ME-PRO at bvar 0, it looks up Ann.equiv v
and fires.  Under Ann.sub dom, ME-PRO cannot fire on bvar 0 (it
requires Ann.equiv).  The derivation structure changes.

The paper never needs this lemma because it never changes annotation
types.  Instead, it case-splits on whether ME-PRO fires at bvar 0
and uses the non-promotion tracking guarantee.

### 2.2 Option A: Predicate on derivation trees (RECOMMENDED)

Define a predicate `NoPromoAt (k : Nat)` on derivation trees that
asserts ME-PRO never fires at de Bruijn index k.

```lean
mutual

def MEquivRed.noPromoAt (k : Nat) : MEquivRed Gamma s t t' -> Prop
  | .me_pro (k := j) _ hsub => j != k /\ hsub.noPromoAt k
  | .me_bet hbody harg => hbody.noPromoAt (k+1) /\ harg.noPromoAt k
  | .me_app hu hv => hu.noPromoAt k /\ hv.noPromoAt k
  | .me_fun hdom hbody => hdom.noPromoAt k /\ hbody.noPromoAt (k+1)
  | .me_fop hdom hbody => hdom.noPromoAt k /\ hbody.noPromoAt (k+1)
  | .me_top => True
  | .me_var => True
  | .me_tap => True

def MSubRed.noPromoAt (k : Nat) : MSubRed Gamma s t t' -> Prop
  | .ms_pro (k := j) _ => True  -- ms_pro is on sub annotations, not equiv
  | .ms_equ h => h.noPromoAt k
  | .ms_app h => h.noPromoAt k
  | .ms_fun h => h.noPromoAt (k+1)
  | .ms_fop h => h.noPromoAt (k+1)
  | .ms_top => True

end
```

**Key lemma replacing `equivRed_change_ann`:**

```lean
-- If a derivation under Ann.equiv doesn't promote at index 0,
-- then it works under ANY annotation at index 0.
def equivRed_no_promo_change_ann
    (h : MEquivRed (Ann.equiv v :: Gamma) s body body')
    (hnp : h.noPromoAt 0)
    : MEquivRed (Ann.sub dom :: Gamma) s body body'
```

This is TRUE because:
- ME-PRO at bvar 0 is excluded by `hnp`
- ME-PRO at bvar k (k > 0) looks up Gamma[k-1], unaffected by position 0
- ME-VAR, ME-TOP, ME-TAP don't consult the context
- ME-BET, ME-APP, ME-FUN, ME-FOP recurse (with shifted index for under-binder cases)

**Advantages:**
- Directly matches the paper's reasoning
- No new inductives needed (just a recursive predicate)
- The predicate is Prop, so it doesn't affect computational content
- The key lemma is straightforward structural induction

**Disadvantages:**
- Every invocation of the diamond/commutativity theorem must now
  produce or consume noPromoAt witnesses
- The commutativity proof structure becomes more complex (more outputs)

### 2.3 Option B: Finset of promoted variables as output

Carry a `Finset Nat` of "promoted variables" as output of the
diamond and commutativity theorems.

```lean
def diamond
    (h1 : MEquivRed G0 s0 t0 t1) (h2 : MEquivRed G0 s0 t0 t2)
    (hc1 : CtxRed G0 s0 G1 s1) (hc2 : CtxRed G0 s0 G2 s2)
    : Exists (fun t3 =>
        (MEquivRed G1 s1 t1 t3) ×
        (MEquivRed G2 s2 t2 t3) ×
        -- Promotion tracking: variables NOT promoted in h1 stay
        -- not-promoted in the G2;s2 |- t2 ===> t3 derivation
        (forall k, h1.noPromoAt k -> (proof of G2;s2 output).noPromoAt k) ×
        (forall k, h2.noPromoAt k -> (proof of G1;s1 output).noPromoAt k))
```

This is more explicit but harder to work with in Lean because the
Sigma type must carry the derivation terms for the predicate to apply.

### 2.4 Option C: Refined inductive with split ME-PRO

Split ME-PRO into two constructors:
- `me_pro_fresh`: promotes a variable for the "first time" in this derivation
- `me_pro_repeat`: re-promotes a variable already promoted

This is unworkable because "first time" is a global property of the
derivation tree, not a local one.  It would require threading state
through the inductive, which is essentially Option B with more ceremony.

### 2.5 Recommendation

**Option A (predicate on derivation trees)** is the cleanest encoding.
It directly mirrors the paper's informal "in the derivation... there
isn't an application of ME-PRO that makes a promotion of variable x."


## 3. Which helper lemmas become unnecessary

### 3.1 Eliminated entirely

- **`equivRed_change_ann`** (line 397): FALSE as stated, replaced by
  `equivRed_no_promo_change_ann` which has the noPromoAt precondition.

- **`equivRed_change_ann_rev`** (line 415): This direction (sub -> equiv)
  IS true and was already proved via `equivRed_change_sub_at`.
  However, with the redesign we may not need it either, since the
  paper's proof never changes annotation types.  Instead, the paper
  works entirely in the equiv context (via ME-FOP/MS-FOP) and only
  uses ME-BET which introduces Ann.sub.  The case split on "does the
  derivation promote x?" avoids ever needing to convert.

### 3.2 Simplified

- **`weakening_equivRed_ctx`** (line 233): The current version is a
  full "stability under context reduction" lemma, which is circular.
  With non-promotion tracking, we only need the weaker:
  - `weakening_equivRed_ext`: weakening under context EXTENSION
    (adding a new binding, not reducing an existing one).
  - This is Lemma 19 in the paper, which is straightforward.

- **`subRed_change_sub_at`** (line 352): The k=n sorry (line 363)
  becomes provable if we add a noPromoAt precondition, OR we can
  avoid it entirely by restructuring the proof to not change
  annotation types.

### 3.3 Still needed

- **`substitution_equivRed`** (Lemma 32, line 262): Still needed, but
  the paper's proof of Lemma 32 (p.9:44) does NOT require
  non-promotion tracking.  It is a pure structural induction.

- **`substitution_subRed`** (Lemma 30, line 692): Still needed.  The
  paper's proof (p.9:42) DOES use non-promotion tracking: it has a
  precondition "this derivation is NOT of the form Co[x] <==> Co[t]"
  (i.e., the derivation doesn't promote x through a covariant context).
  In de Bruijn, this becomes a noPromoAt precondition.

- **`ctxRed_unstk`** (line 451): Still needed for the ME-FOP case of
  diamond/commutativity.  The blockers at lines 469/474 are about
  weakening under context extension, which is independent of
  non-promotion tracking and needs to be solved separately (likely
  by storing shifted stack elements or restructuring CtxRed).

- **`weakening_equivRed`** / `weakening_equivRed_ctx`: The paper's
  Lemma 19 (weakening) and Lemma 22 (stability under context
  extension) are still needed.  These are orthogonal to non-promotion
  tracking.


## 4. Concrete plan for redesigned MPSS.lean

### 4.1 Syntax and reduction rules: UNCHANGED

The inductives `Ann`, `MCtx`, `Stack`, `MEquivRed`, `MSubRed`, and
`CtxRed` remain exactly as they are.  Non-promotion tracking is a
PREDICATE on existing derivation trees, not a change to the rules.

### 4.2 New definitions

```lean
-- (1) Predicate: derivation doesn't use ME-PRO at index k
mutual
def MEquivRed.noPromoAt : Nat -> MEquivRed G s t t' -> Prop
def MSubRed.noPromoAt : Nat -> MSubRed G s t t' -> Prop
end

-- (2) Decidability (optional, useful for testing)
mutual
def MEquivRed.decNoPromoAt : (k : Nat) -> (h : MEquivRed G s t t') -> Decidable (h.noPromoAt k)
def MSubRed.decNoPromoAt : (k : Nat) -> (h : MSubRed G s t t') -> Decidable (h.noPromoAt k)
end
```

### 4.3 New helper lemmas

```lean
-- (3) If a derivation doesn't promote at index 0, the annotation
--     at index 0 is irrelevant.
mutual
def equivRed_no_promo_change_ann_at_zero
    (h : MEquivRed (a :: Gamma) s body body')
    (hnp : h.noPromoAt 0)
    (a' : Ann)
    : MEquivRed (a' :: Gamma) s body body'

def subRed_no_promo_change_ann_at_zero
    (h : MSubRed (a :: Gamma) s body body')
    (hnp : h.noPromoAt 0)
    (a' : Ann)
    : MSubRed (a' :: Gamma) s body body'
end
```

### 4.4 Revised diamond property (Lemma 2)

The statement gains a non-promotion tracking output:

```lean
def diamond
    {G0 : MCtx} {s0 : Stack} {t0 t1 t2 : Expr}
    {G1 G2 : MCtx} {s1 s2 : Stack}
    (h1 : MEquivRed G0 s0 t0 t1)
    (h2 : MEquivRed G0 s0 t0 t2)
    (hc1 : CtxRed G0 s0 G1 s1)
    (hc2 : CtxRed G0 s0 G2 s2)
    : Sigma' t3 : Expr,
        (h1r : MEquivRed G1 s1 t1 t3) ×
        (h2r : MEquivRed G2 s2 t2 t3) ×
        -- Non-promotion preservation:
        (forall k, h1.noPromoAt k -> h2r.noPromoAt k) ×
        (forall k, h2.noPromoAt k -> h1r.noPromoAt k)
```

The proof structure follows the paper's appendix (p.9:21--9:25)
exactly, with each case additionally proving the noPromoAt clauses.
Most cases are trivial for the tracking part (reflexive cases don't
promote anything; ME-PRO cases are handled by the IH).

### 4.5 Revised commutativity (Theorem 1)

```lean
def commutativity
    {G : MCtx} {s : Stack} {t0 t1 t2 : Expr}
    {G' : MCtx} {s' : Stack}
    (h_equiv : MEquivRed G s t0 t1)
    (h_sub   : MSubRed G s t0 t2)
    (h_ctx   : CtxRed G s G' s')
    : Sigma' t3 : Expr,
        MEquivRed G s t2 t3 ×
        MSubRed G' s' t1 t3
```

The statement is UNCHANGED from the current one.  The non-promotion
tracking is used INTERNALLY in the proof (specifically in the
ME-BET + MS-APP/MS-FOP case) but does not appear in the statement.

**Proof structure for ME-BET + MS-FOP case (the critical case):**

Given:
- h_equiv: ME-BET gives t1 = body1'[0 |-> v1']
  - h_eq_body : MEquivRed (Ann.sub dom :: G) s body body1' 
  - h_eq_v : MEquivRed G [] v v1'
- h_sub: MS-APP + MS-FOP gives t2 = app (lam dom body2) v
  - h_sub_body : MSubRed (Ann.equiv v :: G) s body body2

Case split on h_sub_body:

**Case A: h_sub_body promotes at index 0 (ME-PRO fires on bvar 0).**

Then h_sub_body is actually an equiv step via MS-EQU wrapping an
ME-PRO.  This means the sub derivation Gamma;(v::s) |- lam dom body
<==> lam dom body2 is actually via MS-EQU (ME-FOP ...).
So h_sub is MS-APP (MS-EQU (ME-APP (ME-FOP ...))).
We can extract the inner MEquivRed and apply diamond (Lemma 2)
directly, falling back to the MS-EQU case of commutativity.

**Case B: h_sub_body does NOT promote at index 0.**

Then by `equivRed_no_promo_change_ann_at_zero`, we can convert
h_sub_body to work under Ann.sub dom:
  h_sub_body_sub : MSubRed (Ann.sub dom :: G) s body body2

Now both h_eq_body and h_sub_body_sub are in the SAME context
(Ann.sub dom :: G), and we can apply the IH directly.

The IH gives body3 with:
  MEquivRed (Ann.sub dom :: G) s body2 body3
  MSubRed (Ann.sub dom' :: G') s' body1' body3

For the top edge (equiv direction), we need:
  MEquivRed G s (app (lam dom body2) v) (body3[0 |-> v1'])
This is ME-BET applied to the body3 derivation and h_eq_v.

For the right edge (sub direction), we need:
  MSubRed G' s' (body1'[0 |-> v1']) (body3[0 |-> v1'])
This is substitution_subRed applied to the body3 derivation.

### 4.6 Revised proof of ME-BET + MS-EQU subcase

When h_sub = MS-EQU h_inner_eq (line 753 in current code), we need
diamond.  The current code calls diamond directly.  With the redesign,
this is the case where the sub step IS an equiv step, and we need
the non-promotion output from diamond to feed into the substitution
lemma.  Specifically:

- diamond gives us t3 and proofs h1r, h2r
- We need substitution_equivRed on h2r
- Lemma 2's tracking clause guarantees h2r.noPromoAt for the
  variables not promoted in h_equiv

This works because substitution_equivRed (Lemma 32) doesn't need
non-promotion tracking as a precondition.

### 4.7 File organization

Keep everything in `PSS/MPSS.lean`.  Estimated section breakdown:

1. **Syntax** (unchanged): ~30 lines
2. **Reduction rules** (unchanged): ~90 lines
3. **noPromoAt predicate** (new): ~40 lines
4. **Reflexivity** (unchanged): ~20 lines
5. **equivRed_no_promo_change_ann_at_zero** (new, replaces equivRed_change_ann): ~60 lines
6. **Diamond with tracking** (revised): ~200 lines
7. **Substitution lemmas** (unchanged statements): ~100 lines
8. **Commutativity** (revised internals): ~150 lines

Total: ~700 lines (current file is ~810 lines).


## 5. Estimate of complexity

### 5.1 New lemmas needed

| Lemma | Difficulty | Lines | Notes |
|-------|-----------|-------|-------|
| `MEquivRed.noPromoAt` | Easy | 20 | Recursive predicate definition |
| `MSubRed.noPromoAt` | Easy | 15 | Mutual with above |
| `equivRed_no_promo_change_ann_at_zero` | Medium | 50 | Structural induction, ME-PRO case excluded by hypothesis |
| `subRed_no_promo_change_ann_at_zero` | Medium | 40 | Mutual with above |
| Diamond tracking clauses | Medium | 80 | Extra output per case, mostly mechanical |
| `noPromoAt_shift` (shifting preserves noPromoAt) | Easy | 20 | Needed if we shift derivation trees |

### 5.2 Cases in commutativity proof

The commutativity proof has the same case structure as the current
one (10 major cases from the product of equiv rules x sub rules).
The change is that the **ME-BET + MS-FOP** case (currently using
the false `equivRed_change_ann`) now case-splits on noPromoAt:

- **Subcase B** (no promotion): uses `equivRed_no_promo_change_ann_at_zero`,
  then proceeds as before.
- **Subcase A** (promotion at 0): extracts the inner ME-PRO, shows the
  sub derivation is actually an equiv derivation, falls to the MS-EQU case.

This adds ~30 lines to this case.  Other cases are unchanged or
have minor additions for propagating noPromoAt.

### 5.3 Cases in diamond proof

The diamond proof has ~15 cases (product of equiv rule x equiv rule,
minus impossible combinations).  Each case needs to additionally
prove two noPromoAt propagation clauses.  Most are trivial:

- ME-TOP/ME-TOP: noPromoAt holds vacuously (True)
- ME-VAR/ME-VAR: same
- ME-VAR/ME-PRO: The output for the left side uses `equivRed_refl`,
  which never promotes.  The output for the right side is weakened
  from the original derivation, preserving noPromoAt.
- ME-PRO/ME-PRO: This is the hardest case (currently sorry'd at line
  523).  The IH on the annotation alpha_0 provides the tracking.
  This case requires mutual diamond for MSubRed or combining the
  two promotions.
- ME-APP/ME-APP: Direct from IH.
- ME-FUN/ME-FUN: Direct from IH.
- ME-FOP/ME-FOP: Direct from IH.
- ME-APP/ME-BET: Uses the non-promotion tracking from the ME-BET
  side to justify that the substitution result preserves tracking.

Estimated additional work per case: 2-5 lines for trivial cases,
15-25 lines for ME-PRO/ME-PRO and ME-APP/ME-BET.

### 5.4 De Bruijn infrastructure still needed (orthogonal)

The following are INDEPENDENT of non-promotion tracking and remain
blockers:

1. **Substitution lemma for equiv reduction** (Lemma 32): ~80 lines.
   Requires shift/subst commutation (already in SyntaxLemmas.lean).

2. **Substitution lemma for sub reduction** (Lemma 30): ~60 lines.
   Now needs a noPromoAt precondition.

3. **Weakening under context extension** (Lemma 19): ~40 lines.
   Needed for `ctxRed_unstk` and `weakening_equivRed_ctx`.

4. **ctxRed_unstk** scoping fix (line 451): The stack elements in
   CtxRed are scoped to the context level where they were reduced.
   Extending the context requires shifting them.  This is a
   structural issue with our CtxRed encoding that needs fixing
   regardless of non-promotion tracking.

### 5.5 Overall effort estimate

- Non-promotion predicate + change_ann lemma: **1-2 days**
- Diamond tracking clauses: **2-3 days**
- Commutativity revision: **1 day** (mostly ME-BET case restructuring)
- Substitution lemmas (independent): **3-5 days**
- Weakening + ctxRed_unstk fix (independent): **2-3 days**

Total: **~10-14 days** to complete commutativity, of which ~4-6 days
are specifically for the non-promotion redesign.


## 6. Summary of the redesign

**What changes:**
1. Add `noPromoAt` predicate on derivation trees (~35 lines)
2. Replace `equivRed_change_ann` (false) with `equivRed_no_promo_change_ann_at_zero` (true, with precondition)
3. Extend diamond's return type with two noPromoAt preservation clauses
4. Restructure the ME-BET + MS-FOP case of commutativity to case-split on noPromoAt

**What doesn't change:**
- All inductive definitions (MEquivRed, MSubRed, CtxRed, Ann, etc.)
- The STATEMENT of commutativity (non-promotion is only used internally)
- The substitution lemmas (they gain a noPromoAt precondition for Lemma 30, but Lemma 32 is unchanged)
- All other helper lemmas (reflexivity, ctxRed_nil, etc.)

**What this unblocks:**
- The ME-BET + MS-APP/MS-FOP case of commutativity, which is currently stuck on the false `equivRed_change_ann`
- The ME-PRO + ME-PRO case of diamond, which needs the tracking clause to apply the IH correctly

**What this does NOT unblock (independent blockers):**
- Substitution lemmas (Lemma 30, 32): de Bruijn shift/subst algebra
- Weakening (Lemma 19): context extension
- ctxRed_unstk scoping: stack element shifting under context extension
