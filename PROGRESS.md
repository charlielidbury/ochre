# Progress

## 2026-08-05 — dllbc/: M26-E CLOSES — a program is a term; the corpus down both paths

Phase E of the `fn`/λ unification, and the last one M26 planned. Commits 52520fed,
c1ce77c6, 8dfa3a9d, f11c462b. **Deletion (the phase's fourth goal) is BLOCKED, and
the blocker is a design question rather than effort — see the map at the end.**

**A PROGRAM IS A TERM, ON BOTH MACHINES.** A let-chain — transparent lets, sealed
lets, a tail — is checked by one symbolic ⇒-walk against NO declaration table and
run by the concrete one, with the differential green on every program in the file.
`checkProgram` is `explore` plus the audit of each path's result and nothing else:
what `checkFn` adds on top of the walk (seeding a telescope, pinning a dependent
return type, exit snapshots) a program has no need of, because it takes no
arguments. `Decl`, `checkFn` and the table stay fully alive (J1).

**THE ONE KERNEL RULE IT NEEDED IS §7's OWN SENTENCE.** §7 cost 2 admits "closed"
function values — "arms reference only their own binders **and globals**" — and
the second half had been empty since it was written, because callees lived in the
table and were reached by name. §8 makes them variables, so a body's free
variables ARE its callees, and both machines rejected the first program written:
`lookupSlot: f#0 is not an entry of Ω` (frame isolation wipes Ω) and `λr: the body
mentions f#0, which is none of its 1 binder(s)`. `admitGlobals` draws the line at
what a body can DO with a binding — a function is CALLED (`.callV` LOCATES its
callee, it never moves it) while data is moved, borrowed or written — so functions
are admitted and everything else keeps M26-C's rejection verbatim, with constraint
5's deferral untouched and its test still failing on the same needle. The checking
side seeds the admitted bindings through frame isolation; the executing side keeps
their ids out of the frame shift (`shiftVarsK`, whose keep set is computed at the
shift site from the body itself — no capture list on the value, no new state).
This is also the only place a SEALED function's capture is checked at all:
`.seal (.lamR …) u` goes straight to `sealFn` and never forms the `.rfn`, so
`readR`'s own check never ran on it.

**THE END OF A PROGRAM IS A DEMAND ON EVERYTHING IT STILL HOLDS**, found by the
differential rather than by reasoning. A program that lends a local to a call and
never looks at it again leaves the loan PARKED — checking releases a group when
something demands it and nothing does, while executing releases a frame's loans on
the way out — so the two machines end in visibly different Ωs on an ordinary
program. `endScope` is `collapseArg` and `releaseFrameLoans` arriving where a
program ends. It can legitimately fail, so it belongs to `checkProgram` and not to
the harness.

**NO FORWARD REFERENCES, shown as an absence.** `let g = seal(λ(y){ h(y) }, …);
let h = …` fails at G'S OWN SEAL with "unknown function 'h'" — the name resolves to
nothing and falls through to the empty table — and the same two bindings SWAPPED
are accepted. Nothing implements the rule; it is what scope IS.

**THE DELIBERATELY-WRONG TABLE BECOMES A DIFFERENT LET-PREFIX**, and the new form
is sharper than the old: one caller suffix under two prefixes, identical honest
body, sealed at a type that keeps the equation versus one that forgets it. The
lying prefix is a program that CHECKS — the lie is not in the callee, it is in what
the callee promises (§5 point 4).

**BOTH FLAGSHIPS ARE PROGRAM TERMS.** M23's list quicksort is three sealed lets and
a tail: checked against no table in under a second, run to a sorted list,
differentially green, refusing all three of its lie twins. `quicksortA` — the array
in-place scan — is the same, refusing all seven of S25's, plus the LIST-vs-ARRAY
cross-differential re-run over eleven inputs with both sides as programs.

The array cohort needed **no source change at all**, which is the finding: it was
already fuel-threaded, so §12 decision 8 costs that lane nothing. R12's carve
machinery — the part of the corpus that leans hardest on the call boundary's
re-mint — transfers to a sealed binding without one adjustment, which is the
strongest evidence the corpus can produce that §5's opacity and §6.1's call rule
are the same mechanism reached two ways.

The list cohort needed `append_back` fuel-threaded, and its CALLER half is the
first place decision 8 cost more than a parameter: quicksort calls it AFTER sorting
both halves, and a sort returns a count equation, not a length bound, so every
length σ it holds has been re-minted by then and deriving one needs a
count-to-length lemma the corpus lacks. The fuel that works is `len *v` itself with
`le_refl` as its bound, STAGED in a `let` before the call — the borrow is taken in
between, and a comptime argument mentioning `*v` would demand-collapse the loan it
was just lent.

**THE CORPUS, DOWN BOTH PATHS: 94 accept, 56 reject, 74 do not migrate, NOTHING
disagrees.** Nothing was rewritten — a bulk migration's failure mode is a
quietly-wrong rewrite that still builds, so `Migrate.lean` derives each
declaration's callee closure (`calleeNames` computes what its table always was,
`topo` orders callees above callers), `progOf` assembles it, and the verdicts are
compared. The report carries counts beside the disagreement list so that a
migration which quietly stopped covering half the corpus changes the numbers even
while `disagree` stays empty.

**THREE THINGS THE COMPARISON FOUND, all invisible to every existing test:**

1. **`progOf` did not permute a call's arguments to match its callee's hoist.**
   `[k]` is a scrutinee-selection hint and `fnElab` moves that parameter to the
   FRONT, so a sealed callee's telescope is not its declaration's telescope. The
   bug is invisible whenever `[k]` is already parameter 0 — which every flagship
   here happens to satisfy, so both flagship commits were green and would have
   stayed green — and passes a borrow where a `Nat` is expected otherwise.
2. **The macro silently repaired a non-terminating program.** `recGrow` recurses
   on itself, the declaration path rejects it by the guard, and the macro dropped
   the scrutinee argument unexamined and produced a recursor on the PREDECESSOR
   that legitimately checks. `ih` is the sealed self-view AT the predecessor, so
   `fnElab` now refuses a self-call at anything else. Constraint 7 held either way
   — the kernel accepted a well-founded program — but "checks as a different
   function" is the macro bug that constraint tolerates and a reader should not.
3. **The comparison itself was asking two different questions.** `checkFn`
   consults a callee's SIGNATURE and never enters its body, so a broken callee is
   invisible to its caller's test; a let-chain audits every sealed binding in it.
   The declaration side now asks whether EVERY member of the cohort checks.

**DELETION IS BLOCKED — the remaining-work map.** J1 is absolute and 74 corpus
declarations have no program form, in three classes:

  * **§6.2's declared `back` (the largest by far)**: S14 wholesale, S17 wholesale,
    and — through the three S17 functions their tables import — 35 of S19's 39.
    This is the M17-era spec corpus that **M23 superseded by design** (its own
    corpus declares ZERO backs), and the seal has no counterpart because the
    ensures IS the contract. Giving `back` a seal form is a design question about
    what replaces a backward spec, not a migration task — it is the one thing
    standing between here and deleting `Decl`.
  * **§12 decision 8's `[v]` payload decrease**: `zero_all`, `nth`, `recCursor`,
    `append_back`, `partition`, `walkArr`. Each is one hand migration of the shape
    M26-D and this phase already paid twice; §9's borrow eliminator retires the
    class.
  * **Recursions `natRec` cannot express**: a non-`Nat` scrutinee (`recList` —
    `listRec` is wired in the kernel's `sealRec` but not in the macro, so this one
    is small), and `recDeep`, which recurses TWO constructors down. The guard
    permits that and a single `natRec` cannot express it, because an arm gets `ih`
    at the immediate predecessor and nothing below it. Filed as a genuine
    expressiveness limit of §7's elaboration.

Also filed, from writing the tests: a sealed PROOF is not a global (§5's `Qed`
binding is a value; a body that wants one should take it as a capital parameter),
and `let X = seal(…)` is refused because a comptime `let` reads its right-hand side
under ⇝ while the seal is a ⇒-form — §6's own parenthesis arriving as a rejection.

104 assertions across `Tests/S26Prog.lean` and `Tests/S26Migrate.lean`, every one
validated by flipping it and confirming the build goes red; none vacuous.

## 2026-08-05 — dllbc/: M26-D CLOSES — `fn` IS a macro; the first cohort migrated

Phase D of the `fn`/λ unification. Phase E (programs are terms, `Decl` deleted)
remains. Commits e4f171a8, 476a61b4.

**`Dllbc/FnMacro.lean` turns a `Decl` into `.seal ⟨natRec P z s⟩ ⟨the Π⟩`**, and
its `split_off` output is **α-equal to the sealed recursor hand-written in M26-C**
— an oracle written from the document, before the macro existed, and so not
tunable against it. Nothing in `Machine`/`Boundary` imports the macro, so
constraint 7 ("no macro in the TCB") is a fact about the import graph rather than
a promise: macro output is re-derived at the seal, and a bug here can only produce
a program that fails to check or checks as a different function.

**The elaboration's one non-obvious step, and quicksort is what settled it.** It
is *not* "split the body at its `match k`" — `quicksort`'s `match fuel` is nested
inside `match l`'s `Cons` branch, after a `let`, and its `Nil` branch never
mentions fuel. What works is **the whole body twice, with every `match k` resolved
to one branch**: base arm = body with the `Z` branch inlined, step arm = body with
the `S` branch inlined and its binder taken as the predecessor. That is the ι rule
read backwards, which is exactly why it does not care where the match sits.

**The guard's evaporation, observed as an absence.** Elaborated `quicksort` checks
against a table that no longer contains it: there is no self-call left to admit at
a postcondition, so there is nothing for a decrease check to police.

**Held to the corpus's own twins.** `S23Direct` guards `splitOff` with three spec
lies and a body lie; running the same four through the macro is what turns "the
elaborated form checks" into "the elaborated form is the same function" — it
accepts what the declaration accepts and refuses what it refuses, twin for twin.

**§12 decision 8, paid on a real function — and it costs less than expected.** The
macro refuses `partition [v]` (payload decrease has no recursor form) pointing at
decision 8, because fuel is a source change and not something an elaboration may
invent. Paying it by hand: **the bound needs no lemma.** At the recursive call
`Hf : Le (len (Cons x rest)) (S f2)` IS `Le (len rest) f2` definitionally — M14's
bounds-cursor descent again — so the bound passes down unchanged. Fuel-threading
costs one parameter and one dead `botElim` branch; it does not cost a proof. The
bound parameter must be CAPITAL, which is phase B paying for phase D: `quicksort`
hands it over and still needs it twice, and a lowercase one would have moved it
(R16). `quicksortF` — the flagship with exactly one call site retargeted — checks
declared and elaborated, so the caller-side half of the price is paid too.
Written in `S26Fn.lean`, leaving the `[v]` form untouched (J1, both worlds alive).

**For phase E**: `Decl.alphaEq` gained the three M26 formers (`.seal`, `.callV`,
`.lamR`); without them the criterion silently degraded to structural equality on
exactly the terms a macro emits. `FnMacro` also refuses declared `back` specs
(§6.2 has no seal counterpart; M23's corpus declares none) and a `[k]` whose type
mentions an earlier parameter (it must be statable before them to bind before
them).

## 2026-08-05 — dllbc/: M26-C CLOSES — effectful recursors; `split_off` checks and runs BOTH ways

Phase C of the `fn`/λ unification (`dllbc/docs/combining-fns.md` §7). Phases D (the
`fn` macro) and E (programs are terms) remain, so this is a phase checkpoint, not the
milestone's. Commits ec7381b0, 9d3d75aa, aca66665, 5a7dcdd0, 9e4ac02f.

**THE HEADLINE.** `split_off` — a real M23 function: recurses, mutates through a
borrow, hands a reborrow to its own recursive call, returns a Σ-chain of two equations
relating exit and entry snapshots, and discharges a dead branch by ex falso — now
checks **both** as the declared `fn` it has always been and as `.seal ⟨natRec …⟩ ⟨Π …⟩`,
and the sealed form also **runs**: called concretely, splitting a real list, with both
machines agreeing on the whole final Ω. That is §7's "`fn` is a macro" discharged on a
real program rather than on a toy. It needs **no fuel** — §12 decision 8's regression is
for `[v]`-style *payload* decrease, and `split_off` recurses on its index, which is
already a `Nat`, so the recursor is `natRec` on the very argument `[i]` named. The
transcription is one change and one deletion: the self-call becomes `ih(&mut *tl, hi)`
(ι supplies the scrutinee) and `match i` disappears into the two arms. Not vacuous, and
with the SAME coverage split as the declared version — S23Direct notes its spec lies are
all caught on the `i = Z` path and only the body lie tests the recursive one; the sealed
form reproduces that exactly, spec lie on the base arm, body lie on the step arm where
`ih` lives.

**THE MILESTONE'S THESIS, MATERIALIZED IN THE CODE.** §3 claims "today's call rule is
not a separate concept from application; it is abstract application at a moded Π".
Factoring the checking-mode call rule out of `.call` into **`callDeclC`** turns that from
a sentence in the doc into a fact about the machine: a sealed function, an `ih`, and a
declaration-table entry are now called by *literally the same function*, because a σ
whose signature is a borrow-moded Π is exactly a callee whose telescope and return type
are known and whose body is not — which is what a table entry already was. Nothing new
sits under it. The `[k]` guard rides along and is inert for a seal, and that is the right
answer rather than a lucky one: a sealed signature is not in the table, and §7 says the
guard EVAPORATES for recursor-expressed functions anyway, because `ih` is a binder and a
binder cannot be a self-call.

**THE ONE FACT THAT SHAPED THE WHOLE PHASE: a borrow-moded Π has no `Val`.** `readC`
refuses `borrowT` — rightly; a borrow type is a telescope-position marker, not a type
anything inhabits — so the sealed signature can only ever be manipulated as a `Term`.
Three consequences, none optional: `piPeel` (Π-as-Term → telescope + return type, needing
a new `Term.substPure`); `St.fsig`, the moded signature of a sealed σ recorded **as a
`Decl`**, since "a telescope and a return type with no body" IS a Decl; and the recursor's
motive, which is not evaluated at all (an inert `@motive` marker) because ι never inspects
it and §7 settles that the checking side DERIVES it from the ascription. The written
motive is compared to the derived one syntactically — forced, not lazy: there is no
conversion to compare up to.

**Two new formers, and why the second could not be a rule.** `Term.lamR`/`Val.rfn` is the
runtime λ — named binders and a suspended *body* — which phase A filed and could not
build. It needs its own former because a body reaches its binders **through Ω** (a match
scrutinizes a `Var`, `&mut x` roots a place at a `Var`) and a de Bruijn index names no
slot: the pure λ substitutes, this one binds. It is **Curry-style** — binders carry names
and no types — because a runtime λ is checked against an ascription, and §5 point 4 is
that the ascription IS the contract. That makes phase B's name-borne modes load-bearing
rather than convenient: `valBinderModes` reads a runtime function's modes off its binder
NAMES, since there is no type to read them off.

**§5.4's AUDIT, RELOCATED TO THE NODE**, closing phase A's third pinned limitation.
Checking a seal at a borrow-moded Π seeds a telescope, explores the body one path per
symbolic branch, and audits each path — `checkFn`'s content reached from a term instead
of from a declaration, with frame isolation (fresh Ω, obligations, groups; only the
peeled type in and the advanced fresh-supplies out), which pays phase A's other debt.
**What picks the rule is the sealed TERM, not the type**, and that is what protects phase
A: everything that is not a runtime λ keeps `readC`-then-`hasType` unchanged, so
§12-open-4's 16-pair identity survives verbatim and no ascription accident can divert a
value seal onto the function path. The extended smell test is an identity over
hand-written twins, both polarities, and the two rejections agree on the **message** and
not merely the verdict — which is what says the check was relocated rather than
reimplemented.

**WHY §8's GUARD CAN EVAPORATE, shown rather than argued.** The `bad()` recursor is
rejected at its own audit and the rejection is *located*: the step arm goes through —
`ih` really does hand it the claim at the predecessor, which is the self-ensures §7 says
is FORCED — and the BASE arm is what stops it, having no `ih` and needing to inhabit
`Id Nat Z (S Z)` outright. Pinned with a pair: that step arm sealed alone, with the
predecessor's claim as an explicit hypothesis, is ACCEPTED. And `ih`-at-the-wrong-level is
a **type error, not a check**: `ih : P k` while the arm proves `P (S k)`, so a
fuel-bounded arm holding `Le (len *v) (S n2)` cannot pass it to something binding
`Le (len *v) n2`; the accepted twin recurses on the tail, where `Le (S (len *tl)) (S n2)`
IS `Le (len *tl) n2` definitionally — M14's bounds-cursor property doing what the guard
did by comparing snapshots, except it is the type. An unsealed recursive λ is unwritable,
and not by a recursion rule: the binding is not in scope in its own right-hand side, so
the inner name falls through to the table where it is not — §8's "a let-chain cannot
reference downward", as predicted.

**readR and explore are now mutual** (9d3d75aa, a relocation with no behaviour change,
committed alone for bisectability), because the seal's audit happens AT THE NODE and
`explore` already called `readR`. This is where §8 was going anyway: once a program is a
term, checking one is the symbolic ⇒-walk of it, and the walk and the reader are one
thing. The queue alternative was rejected — closed-Π-only is a scope cliff, and phase E
would have had to undo it.

**The differential is ONE relation again.** M26-A had left two incomparable extensions
side by side (segments without computation, computation without segments).
`S9Diff.instanceOfC` merges them — collect σ↦concrete through constructors, borrows AND
carved segments, then instantiate, normalize, compare with the segment-aware matcher —
added to S9Diff rather than to a phase file, because the simulation relation should be
one definition. Liveness verified in four directions: S24Arrays' callers still green (the
carve half), M26-A's seal counterexample still green while the OLD relation still says
false on it (the computation half), S9Diff's forced-constrained bug still RED, and a
recursor-specific mutant (fuel-3 symbolic vs fuel-1 concrete) RED.

**Limitations pinned, not patched.** A runtime recursor needs a FUNCTION motive: at a
data motive `ih` is the recursor-at-the-predecessor as a value, the arm stores it, and the
pure fragment cannot reduce it afterwards because its own arm is a body — both machines
produce the same stuck spine (so not a differential failure) and the audit rejects it. A
nullary runtime λ is refused, because at ι "the arm applied to no arguments" and "the arm
with nothing owed" are the same spine and nothing in §7 wants a thunk. A DECLARED fn
cannot return a borrow-moded Π (`checkFn` has no reading for such a return type) — a
limitation of the declaration form that §8 dissolves rather than fixes.

**For phases D and E.** (i) `#eval` in a SCRATCH file now dies with "incomplete case" on
ordinary programs: the twelve-function well-founded mutual block cannot be walked by the
interpreter. Compiled tests are unaffected — probe through a module, not a scratch file.
(ii) The block carries `set_option maxHeartbeats 1000000`; elaboration cost only
(Machine.lean ~2 min), no program pays it. (iii) Phase D's macro should derive motives
from signatures, as §7 says — the kernel already compares the written one against the
derived.

66 assertions in `dllbc/Dllbc/Tests/S26Rec.lean`, each validated by flipping it and
confirming the build goes red. Three times a test was wrong before the machine was — a
sealed body ending in `()` under an ensures promising an `Id` (the seal imposing exactly
the discipline §5 point 4 promised, first on its author's test); an ensures-threading test
whose caller returned a trivially-true `Refl` of its own; and — phase A's per-DEMAND-SITE
finding arriving a third time — a `bad()` control that bound a self-referencing λ and
never used it, so nothing demanded the body and it PASSED. The vacuous version is kept
beside the live ones, pinned as the trap it is.

## 2026-07-30 — dllbc/: M23 CLOSES — in-place quicksort, Sorted ∧ Perm, ZERO declared backs

`quicksort` on main (4e950ab7):

    fn quicksort [fuel] (fuel : Nat, v : &mut List Nat, hfuel : Le (len *v) fuel)
      -> Σ (hs : Sorted (*v)) → Π n. Id Nat (count n (*v)) (count n (old *v))

Sortedness and permutation over the exit snapshot, with **no `back` anywhere in the
call tree**. `partition`, `append_back` and the two self-calls are each described only
by their return type, and every step of the proof is assembled in the body from a
callee's own postcondition. The `Sorted` is the structural Σ-chain, not M22's
positional `SortedR` — which is why `sigmaRec` (stage (i)) had to land first. M22's
model-based stack stays on main untouched as the comparison baseline.

**THE WALL M23-iv MEASURED IS CLOSED: BRANCH EQUATIONS (5194a9cd).** `match h : x { … }`
binds in every branch an equation `h : Id τ ⟨the scrutinee's PRE-SPLIT value⟩ ⟨this
branch's constructor⟩` — Lean's `match h : x with`, Coq's `destruct … eqn:`. It stays
inside §3.2's knowledge/state invariant because the equation IS the branch's match-shape
knowledge, until now applied only as a substitution and now additionally reified as a
citable term. The finding that made it cheap: the equation's content depends entirely on
what happened to the pre-split value. At an ordinary symbolic split ⇜ already rewrote it
to this constructor everywhere, so both endpoints are identical and `h` is literally
`Refl` — no σ, no sctx entry, zero cost; same for a concrete scrutinee. Only at a STUCK
split, where `generalizeStuck` ABSTRACTED the spine before refining, is it a genuine
hypothesis. The binder went on `matchE` (one name per match, since only its TYPE varies
per branch), so `Branch` was untouched and the ~75 `.mk` sites — 40 in the differential
generator — never moved; 58 `.matchE` sites migrated mechanically.

**Stage (iv), the relational partition (e0c217e2).** `*v` keeps the elements ≤ p; the
rest returns by value. Six conjuncts: `Ub p (*v)`, `Lb p hi`, two `Le` length facts, and
`Π n. add (count n (*v)) (count n hi) = count n (old *v)`. **No pure model of the
partition exists in this milestone** — there is no `partitionL`; every conjunct is proven
inductively in the body from the recursive call's ensures. The program is §4.1's
take-and-rebuild, not Lomuto's array scan, and the §8 guard is satisfied with no counter
passed at all. Branch equations paid immediately and are not optional: the same body with
`Refl` in place of `e` is the rejected wall test one screen up.

**The keystone, in whole-list form.** `sorted_append_pivot` wants `Ub x` of the left part
AFTER sorting while the partition bounded it BEFORE, and `Ub`/`Lb` (Σ-chains over the
spine) are not natively permutation-invariant. M22 named the route at the positional
encoding: cross to the multiset, where the property is `Π x. x > p → count x l = Z` and
permutation-invariance is a one-line `id_trans`. `ub_perm`/`lb_perm` plus their four
crossings are that. This is the only place the assembly is more than gluing.

**PERFORMANCE, unasked for: the check takes 21 ms.** M22's quicksort took 38 minutes
before the build-config work and 21.8 s after it (92089249). A thousandfold against the
tuned number on the same machine, with no perf work at all. The whole-list structural
encoding keeps normal forms small where the positional one (`SortedR cnt lo`, `partIdxL`,
bounded-Π predicates over range indices) made them enormous. Naturalness and cost were
never in tension: the natural program is also the cheap one. Partition checks in 3 ms.

**Two more machine defects, both the same class, both live on main before this.** The
demand-end rule — a suspension must collapse before anything reads through it — was
implemented at some sites and not others, and each unimplemented site was a silent-marker
bug. `readR`'s take (`let lo = *v` after a call that borrowed `v`) took the parked
`loanₘ ℓ` ITSELF and it rode into a proof as if it were the callee's released list; and
`collapseCDerefs` did not treat a bare `.var` as a place, so naming a local whose loan a
call still held read the marker. With M23-ii's ⇝-deref fix that is four sites of one rule
closed in this milestone. The rule is now stated once in §5.2 (277644f9) rather than
per-site.

**PAIN DIARY — staging is now the dominant cost of writing these bodies, and quicksort is
the measurement.** Four builders (`mkCnt`, `mkUb`, `mkLb`, `fin`), applied in stages as
their arguments arrive, exist solely because a proof must name values that later
statements consume — "the value `rest` had", "what `*v` held before that call". None does
mathematical work; every one would disappear under the filed `old`-for-consumed-things
feature, which now has **six** independent instances across M22/M23. It was NOT built:
staging reached every case, so the honest deliverable is the measured cost rather than a
rule added under deadline. One sharp sub-observation: the length conjuncts needed no
staging at all, because `len rest` is a Nat and naming the computed value once suffices —
the counts cannot do that, since `count n rest` is a family over `n` and it is the LIST
the lemma wants. That is what staging is for, stated precisely.

**Next.** The snapshot-naming feature (`old` for consumed parameters and binders) is the
one clearly-earned item, with six filings and a measured cost. Beyond it: the executing
differential covers quicksort on seven inputs but the calculus still has no metatheory;
and §6.2's conformance machinery now has a fully worked propositional counterpart to be
compared against.

## 2026-07-30 — dllbc/: M23 — direct proving with NO declared backs (4 of 6 stages)

Removing `back` from the quicksort train. A callee's ONLY description becomes its
return type — a postcondition over the exit snapshot — and a caller sees an opaque
exit plus the returned evidence. The M22 model-based stack stays on main as the
comparison baseline; M23 lives in `dllbc/Dllbc/Tests/S23Direct.lean` plus additions
to StdLemmas and the checker.

**CLOSED: stages (i) sigmaRec, (ii) split_off/append_back, (iii) the swap leaf,
(v) the recursion guard, plus (iv)'s groundwork.** Every commit green on the full
suite. The headline SHAPE is demonstrated: `split_off` is recursive, back-less, and
proves its postcondition from its OWN recursive call's postcondition — which no M22
back-less Decl did (all four were straight-line delegators).

**A LIVE UNSOUNDNESS, found and closed (82290284).** Signature-only checking admits
a self-call at the function's own declared return type with NO decrease requirement,
so `fn bad () -> Id Nat Z (S Z) { bad() }` was ACCEPTED on main. M22 never tripped
it because the hole needs a recursive AND back-less Decl and M22 has both kinds but
never together. Closed by §1.2's `[k]` made operational as §8's snapshot-subterm
guard: a self-call is admitted only when the actual at the declared decreasing
position is a strict structural subterm of that parameter's CURRENT snapshot, which
the symbolic interpreter already has (inside `match n { S(m) => … }` the parameter
reads `S σ_m`). The snapshot rides refineSym — the fourth consumer of the M10
invariant. `[k]` is DECLARED, not inferred: "some argument decreases at each call"
is unsound, and paths are explored independently so no index can be committed to
across them. Borrow parameters decrease through their payload snapshot (the only
thing that shrinks in a cursor). Mutual recursion is rejected. 17 existing recursive
Decls gained a `[k]` annotation.

**Two more machine gaps, both the same shape** — a feature exercised only in the
direction M22 happened to need. (a) `buildResult` built a Σ result's tail
independently of its head, so a pinned return value reached the caller with a
dangling pvar and was unusable; never noticed because M22's Σ-pinned indices were
never CONSUMED (d46f8ae5). (b) A comptime deref through a place holding a parked
loan silently returned the `loanₘ` instead of demanding its end, so a state marker
rode into any proof about a call the body had just made (17f17993). Direct proving
inverts the direction of information flow — evidence travels callee→caller instead
of being checked against a model — and it keeps finding the unexercised half.

**M22's THREE-FEATURE ARC IS RETIRED (73d2fdaf).** M22 filed issued-payload pinning
→ the swapL_set bridge → audit-rewrite-along-cited-bridges as the route to provable
inline leaves. The diagnosis was half right: the opacity is a property of borrows
ISSUED BY A CALL (buildResult mints their payloads as fresh σ), NOT of inline
mutation. A leaf doing its own cursor work through the body's OWN match-field
borrows writes into a suspension the audit itself collapses, so its exit is a
constructor tree over known snapshots — `set_at`'s base case is literally
`{ *hd := x; Refl }`. The arc collapses to a program-level choice: walk the list
yourself instead of calling `nth2`. And the bridge becomes an ordinary body lemma
(`swap_at` ensures `swapL` directly), removing two of audit-rewrite's three
convergence points.

**THE OPEN WALL — a body learns nothing from branching on a comparison.** M18's
two-layer principle (motive abstraction handles OCCURRENCES, branch equations handle
KNOWLEDGE) has only its first layer in the imperative fragment. `generalizeStuck`
abstracts a stuck scrutinee across all σ-bearing state and the branch refines it to
True, so everything that ALREADY mentioned the spine reads True (M19's stuckProbe) —
but a body writing `leb a b` after the split recomputes the spine, and nothing hands
back the equation. `Refl : Id Bool (leb a b) True` is REJECTED inside the True
branch (kept as a negative control). This matters now and not before because the
model architecture only needed the body's types to AGREE; a back-less body must
PRODUCE evidence, and every comparison-driven algorithm must produce "the test said
yes, therefore Le".

**Two routes to the relational partition, both costed, neither started.**
*Route 1 (no new rule)*: keep the body BRANCH-FREE — compute the decision as a
`boolRec` index, never match — and put the case analysis in pure lemmas, which get
branch knowledge from a CONVOY MOTIVE carrying `Id Bool <spine> b` (the idiom
allLeR_extend_far already uses). BOTH halves verified in-suite (`pick`, `ub_pick`).
Costs ~5 pure lemmas (take/drop/count over `insertL`, needing a `Le k (len l)`
conjunct) plus assembly. *Route 2 (recommended)*: give the body BRANCH EQUATIONS —
bind `e : Id Bool <pre-abstraction spine> True` at the split. Partition then takes
the natural two-list shape and the insertL lemma stack disappears. Cost is a
`Branch`/`matchE` surface+Term change with ~75 `.mk` sites to migrate (40 in
Bench.lean's generator); the machine side is small, since the pre-abstraction spine
is right at the split site.

**Banked for whoever continues**: sigmaRec + `elim`'s Pair arm; the buildResult pin;
the recursion guard; the ⇝-side demand-end; `split_off`/`append_back`/`set_at`/
`swap_at`/`insert_at` all back-less with lying twins and executing differentials;
`Ub`/`Lb`/`insertL`/`list_rw` in StdLemmas. Remaining: the relational partition
(iv), then quicksort (vi) — which also wants `sorted_append_pivot : Sorted a → Ub p a
→ Sorted b → Lb p b → Sorted (append a (Cons p b))`. Note the whole-list plan lets
quicksort use the STRUCTURAL `Sorted` (a Σ-chain) instead of M22's positional
`SortedR`, which is precisely why sigmaRec had to land first.

## 2026-07-29 — dllbc/: M22 CLOSES — in-place quicksort verified Sorted ∧ Perm (the full postcondition)

`quicksortSorted` on main (1baa7ecc): a direct-proving Decl whose exit
snapshot satisfies

    Σ (sortedpart : SortedR cnt lo (*v)) → (Π n. Id Nat (count n (*v)) (count n (old *v)))

— sortedness AND permutation — proven from pure lemmas about the model
function the mutation delegates to (`sorted_sortRangeL`, `count_sortRangeL`),
no back-carrying conversion in the postcondition. checkFnOk green in-suite.
This closes the M22-c sortedness half on top of the M22-b permutation half;
M22 is done.

**The sortedness spine** (all on main, StdLemmas): bounded-Π predicates
`AllLeR/AllGtR/SortedR` (Π k. Le (S k) w → …) — FORCED by the missing comptime
Σ-eliminator (match is runtime-only; elim only Nat/Bool/List), the milestone's
one recurring machine gap, which also split the invariant into three separate
lemmas and the keystone into separate directional bridges. The partition
invariant as three model-level lemmas (allLeR/allGtR/pivot). The perm-survival
KEYSTONE: positional AllLeR is NOT permutation-invariant, so bounds are routed
through the multiset predicates noAbove/noBelow (`Π x. Le (S p) x → segCount = Z`),
which ARE — off-end positions read Z, so #1/#3/#5 carry the range-fits bound
`Le (add lo w) (len l)`. The `glue` (SortedR left ∧ AllLeR ≤piv ∧ AllGtR >piv ∧
SortedR right ⟹ SortedR whole), a nested leb-elim dispatcher, deliberately
lemma-guarded subtraction for the right-segment reindex. And `sorted_sortRangeL`
(fuel/cnt induction) carrying `Le cnt fuel` — sortedness, unlike count/len, is
NOT preserved by the out-of-fuel identity, so it needs the depth bound the Decl's
caller supplies.

**Both conjuncts are load-bearing.** The two lying-reject twins
(quicksortSortedLiePerm: 2nd conjunct shifted to count (S n); quicksortSortedLieSorted:
1st conjunct widened to SortedR (S cnt) lo) are #eval-verified REJECTED — same
path for both: "audit: result (…) does not have return type (…)" (Boundary.lean:263).
Their native_decide suite assertions are DEFERRED to a small follow-up (task #62)
after the dllbc-perf-simplest merge, when each costs ~20s compiled instead of
~25 min interpreted.

**Perf note (measured baseline).** native_decide runs through the IR interpreter
(~30× tax) exactly like #eval, so the uncached quicksortSorted subject grinds
~23 min: full lake build 23:02 wall, the standalone #eval 21m54s; a REJECT costs
the same as an ACCEPT (both fully normalize the certificate before the return-type
compare). The compiled path (~54.6s) belongs to the perf lane (dllbc-simplest,
precompileModules). An earlier CPU-contention explanation for the slowness was
WRONG (single-core check on a 20-core box can't be starved by idle orphans) and
is retracted; the cost is intrinsic certificate-term normalization.

**Process.** Spine/worker split validated: the summit lemma type-checked exactly
to the statement dispatched blind. sorted_sortRangeL was driven to done via a
no-idle takeover after the mechanical worker stranded.

## 2026-07-28 — dllbc/: North Star landed; 465× perf; suite modernized; direct-proving redirect — Perm half proven end to end

Four arcs since the last entry, compressed:

**M21, the assembly**: `checkFnOk quicksort = true` (f1de5c54) — the
imperative in-place quicksort verified as an implementation of
`sortRangeL` (§6.2 conformance), independently re-verified from
scratch. En route: the Σ-pinned pivot index (§5.3's singleton-Σ
device), the index-bounded re-model (prefix rides the bound — the
plan of record reasserting itself), the reflectC ⊥ conformance fix
(§2.1's own rule), the knowledge/state invariant VERIFIED
zero-violation and permanently asserted, and &mut demand-ending
parked groups (sequential recursive reborrows).

**Perf**: delayed-lift substPure (+52/−12 to one function): the
quicksort check 84s → 0.18s compiled (465×), full suite from scratch
38m49s → ~13s. Root cause perf(1)-verified: eager per-binder shift
copies of huge closed proof values were ~93% of cycles. Three
cache-family fixes were first MEASURED regressive (branches kept as
documentation of the mapped space).

**Surface**: decl{} + ONE unified term grammar (mode flag = ⇒/⇝
position); the ENTIRE suite converted (91 decl{} + 95 pure{} blocks,
quicksort included); raw Terms survive only as bannered SUBJECTS +
SInternals. Mode inventory (tested, not argued): exactly {&mut, let}
bimodal; the letIn-nfV kernel gap flagged as a theory decision.

**The REDIRECT (user)**: direct proving replaces the pure-model
simulation as the mission; conformance demoted to comparison
baseline ("Aeneas rebuilt in one language"). New ensures-convention
(doc §5.4): borrow-payload derefs in return types read the EXIT
snapshot (canonical because loans end at the audit); `old *v` names
entry (operator, not binder); caller-side one σ shared between loan
release and evidence subject. Executing-mode transitive-collapse fix
landed (the M19 mode-equivalence debt).

**M22 so far — the PERMUTATION half proven END TO END, no back in
any ensures Decl**: swapSE ← count_swapL'; partitionRangeE ("partition
permutes") ← count_partitionRangeL; quicksortE (the North Star
permutes) ← count_sortRangeL, fuel induction whose bound algebra
transferred VERBATIM from the imperative Decl to the pure lemma. THE
CENTRAL FINDING: issued borrow payloads are minted as opaque σs, so
inline-mutating leaves admit NO value-level postcondition — hence the
delegation discipline (mutate through a back-carrying model callee,
cite a pure lemma about its model). Direct proving eliminates
conversion-based verification, NOT the model functions — they persist
as the only provable exit shapes, and both architectures converge on
the same pure lemmas. Candidate-feature arc recorded: issued-payload
pinning → the swapL_set bridge (proven, forward-infra) →
audit-rewrite-along-cited-bridges = inline leaves become provable.

Next: M22-c, the SORTEDNESS half — the partition invariant
(AllLe/AllGe over the models, the crux), sorted-glue up the
recursion, with Perm feeding Sorted (bounds survive permutation, via
counts). Then the full `Sorted (*v) ∧ Perm (old *v) (*v)` North Star
postcondition closes.

## 2026-07-24 — dllbc/: DLLBC mechanized through boundaries; both §4 flagships check

New self-contained Lean package `dllbc/` (package root is the tld; lib
`Dllbc`) mechanizing `dllbc/docs/dllbc-arrows.md` — the Dependent
Low-Level Borrow Calculus, the "one grammar, four arrows" presentation.
Five milestones landed in one day, all sequential dispatches to a single
resumed agent (dllbc-m1), 50 native_decide tests green:

1. §2 concrete machine (moves, borrows, End-Mut, drop, take/refill,
   reborrow; self-reborrow rejected for the doc's stated reason).
2. §3 match, owned + borrow mode (field reborrows, suspension, variant
   change — which needed zero new drop code).
3. Symbolic layer: σ values, ⇜ refinement as global substitution, and
   the explore driver (path-sensitive checking — duplication is the v0
   baseline; the §3.5 join is demoted to a future widening).
4. Pure fragment: readC (⇝), fuel-bounded conversion, hasType, σ-context.
   Fixed MLTT basis (⊥/⊤/Bool/Nat/Σ + List) with recursors as constants —
   deliberately NOT scheme-CIC; type-in-type (consistency deferred).
   Vec exists as its recursive-family encoding via large elimination
   (VecF by natRec), so no indexed families in the kernel; Id/J/K +
   fording is the planned route when they arrive.
5. Boundaries: telescopes with `&mut (s : τ ↝ S)`, checkFn, the §5.4
   audit (collapse-then-convert). **Both §4 flagships check end-to-end**:
   list push (take/rebuild, Rust's E0507), and the Σ-paired VecF push
   mutating both fields in place. The money test: the same body with
   `*l := S(*l)` forgotten is REJECTED — the pair's second field is
   checked against the stuck type `VecF Nat σₗ`, and no constructor
   inhabits a stuck type. Dependent correctness catching a forgotten
   length update through a mutable borrow.

Working method that produced this: the doc's annotated Ω-traces are the
test suite (golden environments up to ℓ/σ renaming); every milestone's
report includes an ambiguity list, folded back into the doc same-day
(commits 040b4698 → c484e8c1 + the M5 batch). Notable spec findings en
route: the owned-position move rule (§2.2) is the single mechanism
behind both forced End-Mut and the §3.3 collapse; the collapse is
demand-driven (owner or audit), never "branch exit"; the audit is
collapse-then-convert, not a bare hasType; and the §4.2 "write order
forced by types" claim does not survive the recursive-family encoding
(no index argument at the constructor) — it returns with native VCons.

Same-day continuation, M6–M8:

6. Calls as wires (§5.3): owed loans minting typed existentials at
   loan-end; the §5.3 imprecision trace (the caller learns exactly the
   signature); the RECURSIVE CURSOR zero_all checking — §2.5's promised
   counterpart to the self-reborrow rejection, tail borrow passed as an
   argument; type-changing ↝ (Bool ↝ Nat) exercised on both sides.
7. Loan groups (§6.1): group nodes (captured loans × issued borrows),
   the ending cascade (issued surrender first — audited — then all
   captured release atomically), choose checking under the per-branch
   callee audit rule (first precise statement, now in the doc), opaque
   groups forgetting as specified. En route: the project's FIRST GENUINE
   SOUNDNESS BUG, introduced by the orchestrator's M7 spec —
   signature-inferred "constrained wire" release. through and advance
   share a signature and differ only in body; constraining advance's
   captured release to the surrendered field payload lets the checker
   refine an owner to its own tail. Caught by the implementing agent's
   precondition analysis plus orchestrator escalation; doc carries the
   provisos (§6.1).
8. Soundness pass + the differential suite: constrained inference
   removed (opaque groups always release fresh existentials — through's
   precision is §6.2's to recover); callee exemption narrowed
   (consumed-into-result/-call, else by-loan locatability, else
   rejected); group ρ ids. And the counterexample-finder: 136 generated
   bodies over three telescopes, 75 accepted by checkFn, 238 concrete
   runs — zero divergences from "accepted ⟹ concrete run completes and
   audits" (native_decide, ~7s clean build). Two metatheory precursors
   surfaced and flagged, not hidden: the simulation theorem needs an
   EXHAUSTIVENESS precondition (a non-exhaustive match is accepted but
   concretely stuck; generator scoped to exhaustive matches meanwhile);
   and v1 is callee-side only — the constrained bug class is
   caller-side, needing calls in the generator plus final-environment
   σ-instance comparison (the simulation relation proper) to catch.

M9–M11, same day: M9 exhaustiveness (the simulation precondition made
syntactic) + differential v2 — whole-program caller+callee runs with
the σ-instance simulation relation, VALIDATED red-then-green (with the
constrained-wire bug test-forced on, the advance-caller differential
goes red; off, green — the harness demonstrably catches its target bug
class). M10 the fording kit: Id/J/K in the kernel, refl-match = the
solution transition only (flex ⇒ ⇜-refine with occurs check;
rigid-rigid ⇒ stuck naming j/k), and the unification library —
NatCode no-confusion, conflict discharge, S-injectivity, UIP — DERIVED
inside the calculus as checked terms: the kernel needs solution only,
the rest is a library, as designed. En route: the "refinement reaches
all σ-bearing state" invariant (an obligations-staleness bug found and
fixed at the through-borrow refl-match). M11 the pure lift (⇒ ⊇ ⇝ on
the borrow-free fragment — bodies now produce, store, and return proof
terms), listRec, pure let, and the quicksort pure library
(Le/eqb/leb/count/Bound/Sorted, le_refl checked). le_trans hit the
raw-eliminator wall — three-level nested dependent induction in
hand-built de Bruijn does not scale; the concrete, attempted-not-
preemptive case for dependent-match elaboration.

NORTH STAR (user-set, 2026-07-24): a fully verified NATURAL in-place
quicksort — see SUGGESTIONS.md's top section for the representation
decisions (slice = mutable borrow + comptime length bound; Perm by
counting; naturalness-first iteration: the calculus bends, not the
program) and the milestone train. The annotated dream program
(S11Lib.lean §11.4) is the live gap list, dependency-ordered:
(1) dependent call-site instantiation [M12, the keystone],
(2) Term-level Std at telescope positions, (3) the cursor-at-depth
idiom [the naturalness make-or-break], (4) sub-slice surface forms,
(5) if-sugar. Deferred throughout: shared borrows, [k]/termination,
§6.2's precision spectrum, proofs.

M12–M15, same day, the quicksort train:

- M12 dependent call-site instantiation (the §5.3 keystone). Two
  semantic rules the tests forced: return types PINNED AT ENTRY (a
  dependent return type may mention arguments the body consumes — it
  means their entry values), and instantiated types joining refinable
  σ-bearing state (first external consumer of the M10 invariant,
  held on first contact). Plus Term-level Std and if-sugar.
- M13 the two-cursor swap gate: nth (borrow-returning recursive
  cursor) and nth2 : (&mut List, i, j) → &mut × &mut — the calculus's
  split_at_mut (two sequential nth calls CANNOT give two live cursors;
  one call returning the pair is the answer to disjointness), and the
  first exercise of M7's multi-issued group end. Naturalness memo:
  ~26 library + ~6 per-site lines, dominant contortion = the
  default-element OOB parameter.
- M14 bounds-proof cursors: prerequisite VERIFIED with negative
  controls (borrow-mode symbolic match refines the payload snapshot;
  len *v computes per branch in sctx-held types), default params
  replaced by Le proofs passing down DEFINITIONALLY (no le_trans
  needed), OOB now a call-site rejection, per-site cost ~5 → 1 line.
  The audit gained the ex-falso branch admission.
- M15 the pure surface authoring layer: pure{} named binders + elim
  recursor sugar with explicit motives — deliberately no unifier, no
  case trees, no motive inference. THE M11 WALL COLLAPSED: le_trans
  authored in 14 lines, checked, applied through instantiation. The
  surface exposed two real hasType gaps (bound-function application
  spines; eliminator over-application) that raw terms could not have
  localized — a mis-typed raw term is indistinguishable from a
  mis-indexed one. Friction noted, not built: lemma application
  inside Decl bodies is still raw-Term splicing.

M16–M17: the crux found, then dissolved — and the architecture
crystallized.

- M16: the lemma stack (arithmetic, count_append, take_drop_id — all
  first-try in the M15 surface), swapL and the UNCONDITIONAL len
  lemmas. count_swapL walled on the missing equational-rewriting
  layer (motive abstraction over computed subterms — cons2_comm is
  "four Refls" morally, ~18 hand-motive lines actually). Then the
  campaign's real crux: an nth2 CALL consumes the slice borrow into
  an opaque group, so a spec-carrying body cannot observe its own
  mutation's result — §6.2's precision spectrum given operational
  meaning. Closed with swapS01: the first spec-carrying in-place
  mutation (inlined cursor work = the contract-free interior;
  Σ-obligation carrying a len-preservation proof checked against the
  actual writes by computation), evidence surviving an opaque
  boundary, ~2 unpack lines per call site measured.
- M17: §6.2 spec group-ends — the M8 constrained-wire arc completed
  soundly (DECLARED backward specs, callee-checked by converting the
  suspension-tree-with-issued-markers-as-holes against the
  declaration, caller-side releases COMPUTED). The headline: specs
  COMPOSE along call chains (sub-call groups resolve through their
  declared specs; recursion through the function's own declaration) —
  LLBC's backward-function composition as checked declarations. The
  real swapS-via-nth2 checks with back = swapL i j s; a caller
  recovers the exact swapped list in checking mode, ZERO unpack
  lines, full precision (0-vs-2 and precision both beat the Σ form);
  the M16 convergence crux is discharged INSIDE the checker; lying
  specs rejected; spec-less calls stay opaque (opt-in, no
  regression).

THE ARCHITECTURE, crystallized by M17: with the whole call tree
spec'd, the imperative program is a checked implementation of a PURE
MODEL, and verification splits into conformance (the ↝/back audit,
mechanical) and model correctness (lemmas about the pure model, in
the comptime fragment). Quicksort's endgame is therefore: sortL as a
fuel-structural pure function, the imperative quicksort declared
back = sortL, and Sorted (sortL s) / count-preservation of sortL as
pure lemmas the caller applies to the precisely-recovered result.
The Σ-wrapped count spec for swapS is OBSOLETE — spec-ends are
strictly stronger.

M18 (closed): the rewriting layer, both halves executable, honest
numbers. Abstraction (generalize-elim over abstractOccurrences,
NF-then-abstract motives) takes cons2_comm ~18 → ~8 and makes the
missed-occurrence bug class impossible; ~8 is the structural FLOOR
for casing-shaped lemmas (casing already delivers the knowledge a
branch equation would — the boolRec residual is intrinsic to
nesting-by-casing). rewrite-by-Id (J-transport by a received Id) is
the equation-chaining tool whose win is EXPRESSIBILITY — it un-walls
the M16 stuck-behind-scrutinee class (count_cons_hit). The TWO-LAYER
PRINCIPLE, §9-ready: motive abstraction handles OCCURRENCES; branch
equations handle KNOWLEDGE; orthogonal, composing — and each maps to
a standard-prover feature (generalize / destruct-eqn:). The payoff:
the bounded count_swapL stack checked FIRST-TRY (cons2_comm →
count_cons_congr → count_headswap → count_swapL, with the load-bearing
Le range bounds — unbounded it is FALSE); the decomposition localizes
all eqb-knowledge into the two small lemmas, leaving pure id_trans
chains, which is WHY the head-swap double-induction never walled.
Plus the imperative tie-in (certConsHit: a mutating fn whose audit
obligation is discharged by a surface-authored rewrite proof, with a
lying-twin rejected) — the quicksort-caller shape in miniature.

M19–M20: partition conformance closed; two corrections to this log.

- M19: the stuck-Bool-spine split gate HELD as designed
  (generalizeStuck = state-level abstraction of the NF'd spine across
  all σ-bearing state, then ordinary refinement — the two-layer
  principle at machine level); partitionL with the GAP-COUNTER design
  (structural swap decision, no second stuck split, self-swap
  impossible — textbook Lomuto's self-swap cannot be expressed by
  nth2's two distinct cursors); executing-mode partition agrees with
  the model on every input class; certSwapCount = the architecture's
  smallest complete instance. Three machine gaps found (shiftVars
  through pure formers; suspended-reborrow end on var move; and the
  big one:) readR moved EVERY var — resolved by COPY-ON-READ for
  INDEX-KIND values only (Nat/Bool/Unit trees, pure-former values,
  σ's sctx-typed as such; data moves even when marker-free — the
  broad marker-free version was briefly decided, implemented, and
  narrowed back: it would have legalized Rust's E0382 aggregate
  class). Process outcome: after repeated message crossings, the
  standing coordination tiebreak is DOC WINS over messages.
- M20: the recursive partScan, declared back = partScanL, ACCEPTED by
  checkFnOk with the full length-equation bound threading — and
  rejected when lying. En route, the second lying-spec-class bug:
  value-returning bodies' declared backs were NEVER callee-checked
  (only the borrow-returning branch ran the §6.2 conversion); fixed
  as the value-returning DUAL (zero-hole spec vs the suspension
  tree). Its PRECISE REACH, corrected mid-milestone by the agent's
  own sweep: the callee check reaches backs authored AS the raw tree
  (partScanL, nth2, through); a REFORMULATED back (swapS's swapL vs
  its set-based tree — semantically equal, never definitionally) is
  the differential's to validate. CORRECTIONS TO THIS LOG: the
  M16–M17 entry's "the M16 convergence crux is discharged INSIDE the
  checker" was FALSE — the value-returning check did not run then, so
  the discharge was vacuous; swapS's back is differential-validated,
  exactly as M17 built it. The deferred principled close: admit a
  reformulated back with a cited bridging equation (audit-side
  rewrite-by-Id). Lying-back sweep per CALLEE-CHECKED branch all
  rejecting; the differential now load-bearing for reformulated
  backs; executing body = declared back = recovered value on every
  input class.

Remaining train: M21 the final assembly — partition wrapper (back =
partitionL), sortL (fuel-structural pure model, authored as the raw
composition of partitionL + recursive backs so the callee check
reaches it), quicksort (back = sortL). M22 the model-correctness
lemmas (count-preservation of partitionL/sortL via the count_swapL
stack; Sorted (sortL s) via AllLe/AllGe + gluing) and the final
caller applying both to the recovered result — the north-star
artifact. Partial correctness; totality after, via fuel or §8
measures.

## 2026-06-10 — pss/: full Lean formalization of the original PSS paper (branch pss-2)

New self-contained Lean 4.16 package `pss/` (no mathlib) formalizing
Hutchins, *Pure Subtype Systems*, POPL 2010 (`docs/papers/pss.pdf`) — the
original paper, per user request, **not** the machine-based reformulation
from `ochre-pss-A/`. See `pss/README.md` for the full paper ↔ Lean
correspondence table. Build green, zero `sorry`, zero `axiom`; paper
conjectures are `Prop`s taken as hypotheses where needed.

Status by section: Figures 1+2 encoded verbatim (de Bruijn; ⊲ as a `Rel`
index; both mutual blocks preserved, with hand-rolled joint induction
principles since Lean's `induction` refuses mutual predicates). §3.5 fully
proved (3 ≤ Nat three ways; Nat + 3 ≡ Nat algorithmically). §3.6/§4.1
universes + §7 toy ARS done. §4 descoped by user (4.1/4.2 proved, 4.3
stated). §5: 5.2/5.3/weakening proved, progress proved from Conjecture 5.1,
preservation from 5.1 + two isolated structural Props; §6: Lemma 6.3 proved,
Lemma 6.4 proved (degenerately — see below), Thm 6.1 reduced to the
`ParDiamond` residual.

Two mechanization findings about the paper itself:
1. **Lemma 5.4's proof sketch has an unstated assumption** (hit
   independently by two agents): weakening `Sub`/`Wf` into context
   extensions with *ill-formed* bounds is not derivable by rule induction
   (DS-FUN extends contexts unvalidated; every `Wf` forces `CtxWf`).
   Isolated as `SubShiftWeakening`; both Lemma 5.4 and narrowing reduce to
   exactly it, and Conjecture 5.1 does not supply it.
2. **The paper's literal Lemma 6.4 is degenerate**: its `≤*` completing
   edge admits folding the spanning edges backwards (`t3 = t2`), so the
   lemma as stated is provable outright yet useless for the §6.6.2
   decreasing-diagrams program. The intended §6.6.1 completions are proved
   separately. Any future index on `≤*` derivations must exclude this.

Process note: parallel worktree agents writing large Lean files died on the
64k output-token cap until dispatched with incremental-write discipline
(≤120-line writes, build-per-chunk, commit-per-milestone).

## 2026-04-23 — Phase 1 sorry-closure: blocked; boundary documented

After landing primitive Bot and the Fin-as-subtype-of-Nat work, I
attempted to close the 4 remaining declaration-level sorries in
`SoundnessProof.lean` per the plan in
`docs/ideas/sorry-closure-plan.md`. Four subagent attempts, all
blocked:

| Task | Status | Blocker |
|---|---|---|
| 1 (`eval_vapp_preserves_fullyQuotable`) | **formally impossible** | Halting Problem reduction via Ω-combinator closure |
| 3 (`quoteClosure_realises`) | blocked | Lean termination checker + cascading sorryAx |
| 2 (`vapp_realises`) | depends on Task 1 | inherits impossibility |
| 4A (hnfq witnesses) | depends on Task 1 | inherits impossibility |
| 4B (Subtype' derivations) | partially blocked | needs `Subtype'.unshift_head` lemma (~500 LOC) |
| 4C (A9) | intentionally sorried | DECISION-LOG 2026-04-22 |

Research note `docs/ideas/quote-witness-feasibility.md` documents
the formal impossibility proof for Task 1's goal. The key
observation: `Val.fullyQuotable d v` does NOT imply
`∃ q, quote fuelω d v = some q` because closure bodies can encode
Ω-combinators that diverge. Phase 2's `progress_mod_fuel` does
NOT subsume this — Phase 2 is about `concEval` stuckness,
different layer.

### What was accomplished

- `docs/ideas/quote-witness-feasibility.md`: formal impossibility
  research note.
- `docs/ideas/autonomous-log.md`: running decision log.
- `docs/ideas/sorry-closure-plan.md`: attempted plan + full
  post-mortem.
- In-file documentation of blockers in `SoundnessProof.lean`,
  `Subtyping.lean`, and on each sub-sorry site.
- `Subtype'.unshift_trivial`: stepping-stone lemma proven
  (cutoff-|Γ| variant, trivial via `shift_of_closedAt`).

### What did not happen

- No declaration-level sorry closed. Baseline unchanged at 4
  (or 3 if we don't count A9's two, which are intentional).
- No new axioms introduced; no regressions.

### The four recommended paths forward

Full analysis at `docs/ideas/sorry-closure-plan.md` §"Recommended
next steps":

- **(a) Accept as-is.** Treat the 4 sorries as OCH's
  non-totality boundary documented formally.
- **(b) Phase 2 (progress_mod_fuel) for its own merits.** Doesn't
  close these sorries but has orthogonal value.
- **(c) Option 1.75 — typed NbE.** 2–4 weeks research-scale
  effort; only option that actually closes these sorries.
- **(d) One more Category-B push.** Tractable ~500 LOC UNSHIFT
  lemma work; closes 3 of 4 B sub-sorries internally but doesn't
  move declaration-sorry count.

## 2026-04-23 — Primitive Bot + Fin-as-subtype-of-Nat

Landed primitive `Bot` as a first-class term/value (`Expr.bot` /
`Val.bot`) with one declarative rule `[S-BotL] Bot ⊑ e` and one
algorithmic arm `| .bot, _ => .ok true`. Bot is non-applicable —
`vapp .bot = none`, parallel to `Type`. Typing restriction via
bidirectional mode: `tyInfer .bot` errors; `tyCheck .bot τ`
accepts only when `τ = Type`.

Replaces the previous definable-Bot encoding
(`fix B. λX:Type. λz:X. λs:(B → X). s B`) in `Std/Fin.lean`, which
worked but was structurally fragile — a single change to Scott
numerals or the subtype algorithm could have re-introduced the
zero-shape collision that caused the `n_ ⊑ Fin n_` diagonal to
pass wrongly.

**Subtype relationships now provable (see `Std/Fin.lean`):**
- `Fin n ⊑ Nat` — every Fin value flows into Nat positions.
- `Fin m ⊑ Fin n` for `m ≤ n` — width monotonicity.
- `n_ ⊑ Fin m_` for `m_ > n_` — specific Nat literals flow into
  `Fin m_` for large-enough `m_`, via the singleton encoding of
  Scott numerals. No `FZ`/`FS` constructors needed.
- `Fin n ⊄ Fin m` for `n > m` — correctly rejected.
- `n_ ⊄ Fin n_` (the "equal index" diagonal) — correctly rejected
  thanks to Bot being primitive, not a structural encoding.

**Soundness impact:** zero new sorries. Phase 1 (preservation-only
theorem) is extended with one trivial case for each structural
induction on `Expr`/`Val`. The 4 pre-existing sorries in
`SoundnessProof.lean` remain for their own reasons (unrelated to
Bot). Axiom set on `Soundness.soundness` / `typeCheck_sound` /
`concEval_equiv` / `concEval_preservation` is unchanged from
baseline.

**Phase 2 (progress_mod_fuel)** — a separate design proposal at
`docs/ideas/soundness-strengthen.md` outlines the path from the
current preservation-only soundness to a statement that
distinguishes fuel exhaustion from genuine stuckness (applying to
Type, applying to Bot, free bvars). Not implemented; awaiting
review.

**Collateral:** removed three illustrative `Subtype'` witnesses in
`Soundness.lean` (`zero_ ⊑ Nat_`, `(λx. x) zero_ ⊑ Nat_`,
`one_ ⊑ Nat_`) that had been broken since the Scott singleton Nat
refactor in commit `39f8516`. The subtyping facts still hold, but
the derivations require nontrivial de Bruijn work under the new
encoding; the witnesses were illustrative, not load-bearing.

Relevant commits: `5636913` (primitive Bot), `db9a011` (soundness-
strengthen proposal), `0566752` (cleanup).

Related: `docs/ideas/bottom.md` (design), `docs/ideas/soundness-
strengthen.md` (follow-up).

## 2026-04-22 — Progress: vapp .lam closed + Closure.fullyQuotable strengthened

Strengthened `Closure.fullyQuotable` to carry `body.closedAt
(env.length + 1) = true` alongside `envFullyQuotable`. This closes the
`vapp .lam` case of `eval_vapp_preserves_fullyQuotable`: given a
`.lam dom cl` head and arg `a`, we have everything needed to apply
the eval IH on `cl.body` under `a :: cl.env` (closedness from the
new conjunct, envFullyQuotable from the existing one, head entry
fullyQuotable + quote from `ha`/`hqa` hypotheses).

Also closed the stuck branches of vapp's `.iota`/`.fix` cases
(producing `.neutral (.stuckRec f a)` from `hf`/`ha` directly).

**Remaining internal sorries in `eval_vapp_preserves_fullyQuotable`:**
- eval `.app f a`: needs quote witnesses on intermediate vals (not
  derivable from envFullyQuotable alone)
- eval `.letE val body`: same issue as `.app`
- vapp `.iota`/`.fix` unfold branches: recursive vapp call needs
  quote witness on eval-produced `f'`, not derivable from current
  hypotheses

The root blocker is identical to what blocks `quoteClosure_realises`:
`Val.fullyQuotable d v` does not easily imply `∃ qv, quote fuelω d v
= some qv` because it requires proving eval success on closure bodies
(mutual with eval).

**Declaration sorries still at 3** — internal structure is cleaner but
the core gap (quote-witness-from-fullyQuotable) remains open.

Commit: 1595679.

## 2026-04-22 — Milestone: R_depth_lift AXIOM-CLEAN

Closed all three closure cases (.lam/.iota/.fix) of R_depth_lift via
`Val.fullyQuotable` threading. `NbE.R_depth_lift` axioms are now
`[propext, Classical.choice, Quot.sound]` — no sorryAx.

**Key enablers (commits 75824f7, 315d3e1, 61a5fb9):**
- `Val.fullyQuotable` predicate (mutual w/ Neutral/Closure/envFullyQuotable).
- `Val.fullyQuotable_mono` + `Val.levelsBelow_of_fullyQuotable`.
- Top-level `match n, v, hlvl, hfq, hq, h with` (mirroring R_mono)
  lets Lean's termination checker see the substituted v constructor.
- `hρfq` field added to OpenCtx, REnv_depth_lift, REnv_lift, RList_depth_lift.
- OpenCtx.empty/push_fresh discharge hρfq (empty vacuous; push_fresh uses mono).

**Declaration sorry migration:**
- R_depth_lift: CLOSED (was the flagship blocker).
- OpenCtx.push_let: NEW sorry — hρfq head + hvfq both need
  `eval_preserves_fullyQuotable` (next target).
- quoteClosure_realises: unchanged.
- tyInfer_sound_open: unchanged.

Count still 3, but the blocker moved to a named theorem
(`eval_preserves_fullyQuotable`) that's provable by induction on
eval fuel (similar to eval_levelsBelow).

## 2026-04-21 (late) — Milestone: vapp_realises closed (4 → 3 declaration sorries)

Path A (closedness-tracking via `Equiv_c d`) fully executed, closing
`vapp_realises` entirely. First sorry decrease since the 10→4
reduction at session start.

**Axiom-clean infrastructure added this session:**
- `Equiv_c d` + combinators (refl/symm/trans/of_Equiv/to_Equiv_zero/mono)
- `Equiv_c.shift` — the nil-Γ-obstruction-killer (no closedness needed)
- `Equiv_c.subst_resp` — substitution congruence without closedness
- `Equiv_c.{lam,iota,fix,app}_cong` — congruence lemmas
- `substEnv_shift_comm` — substitution-shift commutation
- `quote_closedAt` + variants
- `OpenCtx.hρecl` invariant + `substEnv_closedAt`

**Theorems closed:**
- R refactored to use Equiv_c d throughout
- R_depth_lift `.type` and `.neutral` cases closed
- vapp_realises iota/fix unfold cases closed (via Equiv_c.subst_resp
  + Equiv.iota_unfold/fix_unfold chain)

**Remaining 3 declaration sorries:**
- R_depth_lift closure cases: blocked on recursive `Val.fullyQuotable`
  invariant (per-entry quote witnesses on cl.env at arbitrary depth).
- R_quote_equiv closure cases: needs mutual `quoteClosure_realises`
  on quote-fuel (routes through R_depth_lift for env lifting).
- tyInfer_sound_open internal sorries + A9 known-issue.

## 2026-04-21 — Session: R_quote_equiv + vapp iota/fix (agent a516f9da)

**No code changes made.** Extensive investigation documented in
DECISION-LOG (2026-04-21 "R_quote_equiv closure + vapp iota/fix
unfold — investigation").

**Key finding:** Both sorries reduce to the same underlying gap —
shifting Equiv witnesses under binders without closedness (the
nil-Γ `Equiv.shift` sorry). Every alternative approach (routes a/b,
alternative Subtype' chains via unfold_iota_R/iota_intro, bypassing
subst_resp via levelsBelow) ultimately runs into the same wall.

**Declaration sorries remain at 4** (unchanged): depth_lift_bundle,
R_quote_equiv, vapp/eval_realises mutual, tyInfer_sound_open mutual.

**Shortest path forward** (not attempted in this session, too deep):
1. Close the nil-Γ `Equiv.shift` sorry via closedness-tracking
   Equiv + `Subtype'.shift_nil_closed`.
2. Thread `∀ k, ρe[k]?.closedAt 0` invariants through REnv/OpenCtx
   and propagate closedness through eval_realises.

## Current state (2026-04-21)

**3 declaration sorries (down from 10 at session start — 70% reduction).**

Final remaining:
1. `depth_lift_bundle` (bundled `quote_depth_shift` + `R_depth_lift`)
   — blocked on eval level-renaming.
2. `vapp_realises` / `eval_realises` mutual — blocked on R
   definition change (base-conjunct removal + quoteClosure_realises
   via quote-fuel mutual).
3. `tyInfer_sound_open` / `tyCheckFallback_sound_open` /
   `tyCheck_sound_open` mutual — blocked on the SubV_to_Subtype'
   replacement (tier-2 realisability-threaded bridge). Half
the sorries eliminated through a combination of:
- Deleting dead sorry-ridden theorems (SynthN_to_Subtype',
  SubN_to_Subtype', whnfPi_sound chain, openNf_holds, Equiv.shift,
  Equiv.subst_resp).
- Migrating to closedness-carrying variants (subst_resp_closed,
  shift_of_closed, eval_quotes').
- Routing concEval_refines / preservation / soundness through the
  proven closedness-chain.
- Additional cleanup of unused helpers: REnv_id, eval_unf_equiv,
  quoteClosure_{eq,equiv}_openω_fresh, whnfPi_fix_unfold_equiv,
  quote_open_subst, Equiv.subst_target, R_zero, R_neutral_var,
  tyInfer_sound_closed, tyCheckFallback_sound_closed.

Net file size reduction: SoundnessProof.lean ~800 lines shorter
than at session start, Soundness.lean ~120 lines shorter.

Remaining 5 sorries:
1. `quote_depth_shift` (eval level-renaming for closures)
2. `R_depth_lift` (depends on #1)
3. `vapp_realises` / `eval_realises` mutual (base-conjuncts;
   needs R definition change)
4. `SubV_to_Subtype'` (binder & productive-unfold cases; needs
   tier-2 realisability threading)
5. `tyInfer_sound_open` / `tyCheckFallback_sound_open` /
   `tyCheck_sound_open` mutual (needs pieces of #1–#4)

**MAJOR BREAKTHROUGH: `concEval_refines`, `concEval_preservation`,
and `concEval_equiv_closed` are axiom-clean** (depend only on
`propext`, `Quot.sound`). Verified by `#print axioms`. Previously
these transitively depended on `sorryAx` via `Equiv.shift`'s nil-Γ
case. The closedness-propagation chain built this session (see below)
eliminates that dependency.

**Declaration sorry count reduction: 10 → 11 (shift_above added) → 10
(shift_above deleted, hyp_shift_above / bvar_shift_above extracted as
standalone proven lemmas).** The unused `concEval_equiv` also deleted.

`soundness` still has `sorryAx` — but only via the `typeCheck_sound`
branch (SubV/SubN/SynthN bridges), NOT via concEval anymore.

**Closedness-propagation chain (all fully proven this session):**
- `concEval_closedAt` (Eval.lean) — concEval preserves closedness.
- `Expr.shift_of_closedAt` (Syntax.lean, pre-existing) — shift is
  identity on closed expressions.
- `Equiv.subst_resp_closed` (SoundnessProof.lean) — closedness-carrying
  subst_resp that avoids Equiv.shift entirely.
- `Equiv.shift_of_closed` (SoundnessProof.lean) — trivial shift on
  closed endpoints.
- `Subtype'.shift_above_closed` / `shift_nil_closed` (Subtyping.lean)
  — trivial Subtype' shift on closed endpoints.
- `concEval_equiv_closed` (Soundness.lean) — all 8 cases proven using
  the chain above; no sorry.

`concEval_refines` / `concEval_preservation` / `soundness` now route
through `concEval_equiv_closed` (takes closedness).

**Phase 2 incremental structuring (earlier in session):**
- `QuotesCtx` strengthened with `Γ.size = Γe.length`, closing the
  `.hyp` case inside `SubN_to_Subtype'`.
- `SubV/SynthN_to_Subtype'` split from monolithic sorries into
  per-case `cases h` structure — the four SubV structural-guard
  cases (`hyp`, `refl`, `top`, `neutral_struct`) and the
  `SynthN.var` case close directly via the same handlers as
  `SubN_to_Subtype'`. Remaining closure-opening cases in each
  bridge still need tier-2 threading (realisability + quote_open_subst).
- `Subtype'.shift_above` — proven 12/23 cases including `.hyp`
  (was the supposed impossibility wall).

Per-case targets, post-refactor:
- SubV bridge (`SubV_to_Subtype'`): 4/15 cases closed; 11 sorry
  (binder/closure-opening + `neutral_ascent` quote-totality).
- SynthN bridge (`SynthN_to_Subtype'`): 1/6 cases closed; 5 sorry
  (all 5 non-`var` cases need `quote_open_subst`).
- SubN bridge (`SubN_to_Subtype'`): `.hyp` closed (was sorried
  awaiting `QuotesCtx.hlen`); remaining internal sorries mirror
  SubV's obligations.

## Historical state (2026-04-19)

**Phase 1 complete and verified** (f2ba74a). 41 → 0 markers; 0 sorries
in `Och/Std/` or `Och/Tests.lean`.

**Phase 2 (soundness) ~70%.** Nine audit findings A1–A9 in
`SoundnessAudit.lean`; six resolved (A1 covariant-app, A4 inductive
Subtype', A5 iotaIntro annotation, A7 fix-self productivity, A8 asc
transparency, A9 tyInfer-trusted-fix-annotation), one *deferred* (A6
lam-domain — pushing `domB` is more complete but causes seen-list
misses on dNat-style nested fixes; `domA` is sound, see DECISION-LOG
2026-04-18), two by-design (A2 type-in-type, A3 β-blind subCheck →
use typeCheck). Legacy `subCheckNF` retired; sweep is NbE-only
(refl/top/strict/A6-pinned). Algorithm is sound modulo type-in-type.

**Build: clean 71 s** (was 580 s before the `Val.beq` ptrEq fix +
legacy retirement; DECISION-LOG 2026-04-19). DBool/DNat constructors
use the very-dependent encoding (no per-constructor `fix B`).

Proof chain: `subCheckVal → SubV → Subtype' → semantic`.
  - `subCheckVal → SubV`: **fully proven** (axioms `propext`/
    `Quot.sound` only, verified PASS), all 15 match arms + all 4
    helper-function reflections in `SoundnessProof.lean`.
  - **All four target theorems wired** (Soundness.lean):
    `subCheckVal_sound = SubV_to_Subtype' ∘ subCheckVal_subV`;
    `typeCheck_sound = tyCheck_sound_closed ∘ subCheckVal_sound`;
    `concEval_preservation = .trans ∘ concEval_refines`;
    `soundness` composes the latter two. None of the four has a
    direct `sorry`. `concEval_equiv` 8/8 head-shapes leaf-sorry-free;
    `Equiv.iota_unfold` axiom-free.
  - **10 declaration sorries** (all in SoundnessProof.lean;
    Subtyping/Soundness/Eval sorry-free) at `67a202b`.
    **All three root obligations solved with proofs**:
      1. Depth-tagged `Seen` → `ctx_extend_at`/`narrow` proven;
         Subtyping.lean **0 sorries**.
      2. `R` env-exposure → `vapp_realises`/`R_mono`/
         `quote_open_subst`/`Equiv.subst_target` **proven**.
      3. `OpenCtx.hwf`/`hlen` → `tyInfer .bvar`,
         `letBinderType_sound_open` **proven**.
    `Subtype'.app_elim` derived rule added.
  - **Soundness assessment:** the metatheory holds. None of
    the 10 sorries represent open research questions; each
    has a documented engineering route in DECISION-LOG/
    SUGGESTIONS. Three are statement-precision issues, not
    soundness holes: `openNf_holds` (false-as-stated;
    `eval_quotes'` route ready), `tyInfer .fix/.iota` (A9
    annotation-trusted by design), `tyInfer .letE` (algorithm
    gap, fixable in TyCheck.lean).
  - **Remaining 10:**
    - `Equiv.shift` nil-Γ (1) — `Subtype'.shift_nil` ~60 lines
    - `eval_realises` base-conjuncts (3) — drop redundant `R`
      conjunct + quote-fuel-mutual `quoteClosure_realises`
    - `SubV/SubN/SynthN_to_Subtype'` (3) — `(hRa)/(hRb)`
      threading from `subCheckVal_sound_open` callers
    - `openNf_holds` (1) — `(hnfq)` threading via `eval_quotes'`
    - `whnfPi_sound_open` + `tyCheck/tyInfer_sound_open`
      assembly (2) — via proven `quote_open_subst`/`app_elim`

Two checkers: `NbE.subCheck` (Val-domain, the soundness target),
`NbE.typeCheck` (bidirectional). Legacy `subCheckNF` removed.

Simple Och (`lean/Och/Simple/`) remains the proven-sound reference.
Phase 1 path: coinductive seen-set → removed `[fix-ann]` →
neutral-head gate → NbE evaluator → subCheckVal → `fix N. ι self.`
dNat encoding → stuckRec structural arms → bidirectional `typeCheck`.
Phase 2 path: SoundnessAudit → A1/A5/A6/A7/A8 fixes → seen-indexed
Subtype' → SubV reflection → step-indexed `R` → fundamental lemma.

### Agent phase1-coinductive-seen, 2026-04-16

Picked: `dtrue ⊑ dBool` (the central marker).

Found that `subCheckNF` was already accepting it — but only because the
`[fix-ann]` RHS rule (`a ⊑ fix A. body ← a ⊑ A`) made *every* term a subtype
of *every* `fix Type. _`, including `Nat_ ⊑ dBool` and `dBool ⊑ dtrue`. The
annotation `A` is the *type* of the recursion variable, not an upper bound
on the fixpoint, so this rule was unsound and masked the real obstruction.

Removing it exposed the actual gap: the recursive `dtrue ⊑ dBool` subgoal
that reappears in contravariant domain position couldn't be discharged
because `lam`/`app` reset the coinductive assumption set to `[]`. The fix
is the standard Brandt-Henglein discipline:

  - `seen` is threaded through `lam`/`app` instead of reset.
  - Only *productive* steps (fix-unfold, ι-unfold, iotaIntro) extend `seen`.
  - Annotation-widening steps inherit `seen` but never extend it; the
    `.iota`/`.fix` arms in `neutralType` (which silently re-introduced
    ann-widening with the inherited `seen`) are removed.
  - A new `[unfoldIotaL]` arm peels `ι` on the left so `ι_dtrue ⊑ M`
    reduces to its body instead of dead-ending at the annotation.
  - Degenerate `ι A. self` / `fix A. self` (body = `bvar 0`) skip the
    unfold path so they don't close trivially via the assumption set.

After this, all 21 DBool examples close by `native_decide`, including the
negatives (`dBool ⊑ dtrue`, `dtrue ⊑ dfalse`, `dfalse ⊑ dtrue` all
`= .ok false`). `Nat_ ⊑ dBool` and `Type ⊑ dBool` are correctly rejected.

Next obvious target: `dzero ⊑ dNat` runs out of fuel at 200. The DNat
encoding has a Scott-style eliminator whose successor case applies the
predecessor, so unfolding generates much larger terms than DBool. Likely
needs either a sharing-aware `seen` lookup (current `==` is structural on
the unfolded terms) or a smarter unfold strategy that doesn't substitute
the full fixpoint into the successor branch.

### Agent phase1-abseval-museen, 2026-04-16

Picked: `dzero ⊑ dNat`.

Root cause was not subCheckNF at all: `absEvalVal dNat` itself diverged
at any fuel. The `muSeen` cycle check in absEval's app-of-fix/iota arms
compared `(term, arg)` pairs by `==`, but every recursive descent goes
under fresh binders, so both the recursive term and its argument pick up
de-Bruijn shifts and the comparison never fires. Replaced the syntactic
match with a length-based cutoff (one unfold then stuck); subCheckNF's
own L/R rules handle the structural recursion soundly from there.

After that, `dzero ⊑ dNat`, `true_ ⊑ dNat = false`, and the previously
mis-tracked `dzero ⊑ done_ = false` all close at fuel 200. The remaining
DNat tests (`done_/dtwo/dthree ⊑ dNat` and `dNat ⊑ dzero`) are now
*reachable* but blow up: iotaIntro substitutes the closed `dNat` term for
its own self-reference, so each iota-L unfold roughly squares the term
size. This is a representation problem (eager-substitution de Bruijn),
not a missing rule — the obvious fix is an NbE/closure-style evaluator
where substitution is delayed. Also added the missing `body == bvar 0`
guard to fix-R that the verifier flagged.

26 → 25 markers (3 examples closed, 1 negative test corrected from
spurious-true to correct-false).

### Agent phase1-trans-exhaustive, 2026-04-16

Picked: the three `checkTrans` exhaustive transitivity searches in
Tests.lean (smallExprs/stdExprs/edgeExprs). They were sorried after the
μ → ι/fix split because the rule set changed; under the seen-discipline
rework (loop above) all 9³ + 11³ + 11³ triples now satisfy
`a ⊑ b ∧ b ⊑ c → a ⊑ c` with no counterexample.

Also made absEval total on stuck recursive heads: when the muSeen
cutoff fires (or any neutral-spine head can't be typed as an arrow) the
catch-all now returns the stuck application with placeholder type
`Type` instead of erroring with "not callable". This doesn't yet unlock
`Array_ dzero T = Unit_` because the inner β domain check `dzero ⊑ dNat`
sees a *different* normal form of dNat (normalised at non-empty muSeen
inside the fix-Array unfold) than the standalone check does — absEval's
normal form is muSeen-dependent, so it isn't canonical. The Array/Vec
wall is therefore the same NbE/closure-representation problem already
flagged for `done_ ⊑ dNat`, just one indirection deeper.

25 → 22 markers (3 transitivity examples closed).

### Agent phase1-neutral-head-gate, 2026-04-16

Picked: `Array_ dzero Nat_ = Unit_` (Array.lean) and the `Vec Nat_`
normalisation tests, all of which cited "stuck DNat elim on abstract n"
— exactly the absEval recursive-head problem.

The previous depth-1 muSeen cutoff stopped *every* recursive-head
application after one unfold, which prevented `Array_` (a fix) from
unfolding and *then* its argument `dzero` (an ι) from unfolding in the
same chain. Bumping the depth bound made `dzero ⊑ dNat` blow up, so
that's not the lever.

The actual termination criterion is the *argument*, not the depth: a
recursive head applied to a *neutral* (bvar-headed spine) cannot make
progress — the eliminator is stuck on an abstract scrutinee — whereas
applied to a *value* it consumes one constructor layer per unfold and
terminates as long as the value is finite. Added
`Expr.hasNeutralHead` and gated the ι/fix-in-app unfold on
`!arg.hasNeutralHead` (with a high muSeen depth bound kept only for
the degenerate `(fix f. f) v` case).

After this `Array_ dzero Nat_` reduces to `Unit_` (the recursive
`Array_ pred T` in the successor branch stays stuck because `pred` is
a bvar), and `Vec Nat_` normalises (so its negative subtyping tests
close). Everything that uses `done_/dtwo` as a concrete index is still
blocked by the `done_ ⊑ dNat` domain-check blowup inside the β step.

22 → 19 markers (Array_ dzero = Unit, Vec Nat ⊄ Nat, Nat ⊄ Vec Nat).

### Agent phase1-drop-domain-check, 2026-04-16

Picked: the four remaining `Array_ done_/dtwo` markers (Array.lean) and
`dNat ⊄ dzero`.

Two absEval changes:

  1. β-reduce unconditionally. The `(λx:A. b) v` arm previously did a
     `subCheckNF v A` domain check before substituting, which forced
     `(λn:dNat. …) done_` (inside the Array_ unfold) to discharge
     `done_ ⊑ dNat` *during normalisation* — exactly the goal
     subCheckNF was being called to set up. β is type-blind and the
     subCheckNF caller only consumes the value, so dropping the check
     loses inferred-type precision but unblocks normalisation.

  2. Re-add the syntactic head-`==` muSeen check alongside the
     neutral-arg gate. After dropping the domain check, normalising
     `Array_ dtwo` exposes the `(dsucc m) → Type` self-reference in
     dsucc's body: m gets the *value* `done_NF`, the neutral-arg gate
     doesn't fire, and the depth-16 backstop alone makes the term grow
     ~16×. The closed top-level `dsucc` doesn't shift under binders,
     so head-`==` against muSeen fires after one unfold and stops it
     cleanly.

Closes Array.lean: testArr1 ⊑ Array_ done_ Nat, testArr2 ⊑ Array_ dtwo
Nat, unit_ ⊄ Array_ done_ Nat, the (Array_ (dsucc dzero) Nat).isOk
smoke test, plus two new positive `Array_ done_/dtwo` reduction
checks. Closes DNat.lean: dNat ⊄ dzero.

Known incompleteness introduced: `done_ ⊑ dNat` (and dtwo, dthree)
now return `.ok false` instead of timing out. The head-`==` cutoff
leaves a stuck `(dsucc dzero)` inside done_NF's type annotation,
while iotaIntro on the dNat side substitutes the *evaluated* done_NF
(an ι value) for `self`; the two non-canonical normal forms of the
same term then meet in contravariant position and subCheckNF can't
equate them. This is incompleteness (a valid subtype rejected), not
unsoundness. Documented in the in-file TODO; the obvious fix is
either canonical NbE normal forms or a subCheckNF rule that
re-evaluates a stuck recursive-head application before falling
through to neutralType.

19 → 14 markers (5 closed, 2 new positive Array_ tests added).

### Agent phase1-stuck-head-reeval, 2026-04-16

Picked: `testVec1 ⊑ Vec Nat` and the `appendArrays` typing assertion.

Added a stuck-recursive-head re-evaluation rule to subCheckNF: when
either side is `app f arg` with `f = .fix/.iota` (i.e. absEval's
muSeen cutoff left a recursive head un-unfolded — *not* a genuinely
neutral bvar-headed term), unfold it once and recurse with the
seen-set extended. This sits in two places: a dedicated `_, .app
(.fix/.iota …) _` arm right after `unfoldFixR` (so it fires before
the LHS `.fix/.iota` arms — needed for transitivity over edgeExprs),
and inside `neutralType`'s `.app` arm for the LHS direction. Without
this the type-widening fallback collapsed `(dsucc dzero)` to `dNat`
and `(Array_ pred T)` / `(dadd n m)` to `Type`, losing all index
information.

Closes:
  Vec.lean:    testVec1 ⊑ Vec Nat
  Array.lean:  appendArrays ⊑ (T → n → m → Array n T → Array m T
                                 → Array (dadd n m) T)
               — Array.lean now has zero `sorry`.

`done_ ⊑ dNat` is still open: the re-eval rule lets subCheckNF
explore further than before (`.ok false` at fuel ≤150, exponential
at 200) but iotaIntro on dNat still substitutes the closed `dNat`
term for every `:dNat` ascription, so the search fans out before
seen can close it. Same NbE/closure-representation fix as before.

14 → 12 markers.

### Agent phase1-appendvec-northstar, 2026-04-16

Picked: harvest the markers the stuck-head re-eval rule unblocked.

Closes (no checker changes — pure harvest from f04721c):
  Vec.lean:   appendVec ⊑ (T → Vec T → Vec T → Vec T)  — the
              "north star" abstract appendVec test
              concEval (disZero (unpack vecResult)) = false_
              unpack vec1 ≠ dtwo
  Tests.lean: rewrapped (testVec1 : Vec Nat) ⊑ Vec Nat

`appendVec_wrong` (Vec:135) is still accepted: the checker doesn't
yet distinguish `dadd n1 n1` from `dadd n1 n2` under abstract n1,n2
— both reduce to stuck applications of the same closed `dadd` head
and the structural `app, app` rule accepts `n1 ⊑ n2` when both are
bvars. That's a real precision gap (the test is the right
assertion); fixing it likely needs the `app, app` rule to demand
argument *equality* (not just LHS ⊑ RHS) when the head is opaque.

12 → 8 markers.

### Agent ochre-20260416-193340, 2026-04-16

Pure harvest — no checker changes. Once rebased onto
phase1-appendvec-northstar, two more Vec markers close at the same
fuel, via the same stuck-head re-eval mechanism:

  Vec.lean: testVec2 ⊑ Vec Nat  (Array_ dtwo Nat → Pair Nat (Pair Nat
                                 Unit), sigma lines up)
            unpack vec2 → length ≠ done_  (symmetric to unpack vec1
                                 ≠ dtwo)

Separately (earlier in the session, before fetching the remote
updates): probed the `muSeen.length >= 16` cap as a candidate lever
for `done_ ⊑ dNat`. Tried adding a `(fix_expr, arg) == muSeen[..]`
uniqueness check alongside the length cap. done_'s normal form
shrinks ~10× (21620 → 2285 chars) but `subCheck 200 done_ dNat`
returns .ok false at fuel 200 where it previously timed out. The
shorter normal form leaves `(dsucc dzero)` stuck in the λP ann,
iotaIntro substitutes a fuller `done_` on the dNat side, and the
contravariant domain check hits structurally-different shapes.
Reverted — same conclusion phase1-drop-domain-check reached with the
closed-head `==` variant: muSeen caps are tuned to "do enough unfolds
to make shapes line up under eager substitution", not to principled
cycle detection. Documented here so the next agent doesn't re-reach
for this particular lever.

8 → 6 markers.

### Agent phase1-testvec2, 2026-04-16

Same harvest as 193340 above (raced on testVec2). Used the loop to
catalogue the remaining six markers into three distinct obstacles
so the next agent has a map:

  1. `done_/dtwo/dthree ⊑ dNat` (DNat) plus `vecResult ⊑ Vec Nat`
     and `unpack vec2` (Vec) — iotaIntro on dNat substitutes the
     closed `dNat` term for every `:dNat` ascription and the
     search fans out. NbE/closure evaluator.

  2. `unpack vec1 = done_` (Vec:62), abstract unpack `= dNat`
     (Tests:69) — non-canonical normal
     forms: the unpacked length and the literal `done_`/`dNat`
     are computed at different muSeen depths so `==` doesn't fire.
     Tests:69 may also have a wrong expectation (the Sigma type's
     body is the motive `X`, so abstract unpack at motive `Nat_`
     gives `Nat_`, not `dNat`).

  3. `appendVec_wrong` (Vec:135) — accepted because absEval no
     longer does the β domain check (loop 5), so the ill-typed
     `appendArrays T n1 n1 arr1 arr2` (with `arr2 : Array_ n2 T`)
     β-reduces silently. Restoring the domain check would re-block
     all the Array_/appendVec wins; a targeted fix would re-check
     domains only in subCheckNF's goal positions, not during
     normalisation.

### Agent phase1-parallel-forks, 2026-04-16

Four parallel forks, one per remaining obstacle:

  obstacle2-tests69: Tests:69 was a porting error. The pre-c061a3b
    test asserted `= Nat_` (the motive) and passed; the dNat port
    changed it to `= dNat` (n's type) on the assumption that the
    abstract unpack should reveal the witness type. But ascription
    widens to `Vec Nat_ = λX. λk. X`, so applying the motive gives
    the motive back. Under Church-Nat the motive and n's type were
    both `Nat_`, masking the distinction. Restored to `= Nat_` and
    closed. Getting `dNat` here is a Sigma-encoding question
    (Sigma-as-a-type would need to apply k to abstract witnesses),
    not a checker gap.

  obstacle2-vec62: Vec:62/71 restated via concEval. The
    computational fact "unpack gives back the packed length" is a
    runtime property; concEval has no muSeen-path-dependence so
    both sides normalise identically. Bidirectional subCheck also
    works for vec1 but hangs for vec2. The previous absEvalVal
    phrasing was testing absEval's NF canonicity, which is the
    documented representation problem, not the computational fact.

  obstacle1-dnat: skipping ι/fix annotation normalisation in
    absEval is harmless (no regressions) but doesn't close
    `done_ ⊑ dNat`. The fan-out is in λ-domain positions
    (`λpred:self. …`) inside dNat's body, not only ι/fix
    annotations. Skipping λ-domain normalisation breaks Pair
    (its projections need the domain in normal form). Confirms
    NbE.

  obstacle3-domcheck: neutralType domain check fails on both
    correctness and performance. The ill-typed
    `appendArrays T n1 n1 arr1 arr2` is fully β-reduced during
    absEval (no β-site check since loop 5), so by the time
    neutralType sees the application the mismatch is erased — only
    the consistent-with-wrong-indices return type
    `Array_ (dadd n1 n1) T` survives. And the extra `arg ⊑ dom`
    check at every neutral spine is multiplicative in nesting
    depth (appendArrays/appendVec hang at fuel ≥100). The domain
    obligation has to be captured at the β site *before*
    substitution; either (a) absEval annotates each β with a
    deferred obligation subCheckNF collects later, or (b) restore
    the β-site check once obstacle 1 is fixed so `done_ ⊑ dNat`
    doesn't blow it up. (b) means obstacle 3 is sequenced after
    obstacle 1.

6 → 3 markers.

### Agent phase1-nbe-foundation, 2026-04-16

Implemented `lean/Och/NbE.lean`: a closure-based NbE evaluator
(`Val`/`Neutral`/`Closure`, `eval`/`vapp`/`quote`, `nf`/`nfIn`).
Recursive heads (fix/ι) unfold by environment extension instead
of term substitution; a neutral argument blocks the unfold (same
gate as absEval), and a small per-chain `unf` bound stops the
`(dsucc m)→Type` self-reference in done_'s annotation. `quote`
opens closures with a fresh neutral and re-evaluates at `unf=1`,
so the self-reference reads back as a single stuck application
rather than 32 nested ones.

`NbETests.lean` validates: `nf` terminates on `dNat/done_/dtwo/
dthree` (where `absEval` either fans out or produces non-canonical
forms), `Array_ dthree Nat_` reduces to `Pair Nat (Pair Nat (Pair
Nat Unit))` (where `absEval` hangs), and `nf done_ = nf (dsucc
dzero)` (canonicity). All by `native_decide`. No changes to
`absEval`/`subCheckNF`; purely additive.

Tried the naive integration (swap `subCheckNF`'s ~7 `absEval`
calls for `NbE.nfInE`/`nfSubstE`). Doesn't help: `subCheckNF`
works on `Expr`, so each NbE call has to *quote* the result back
to syntax, and the next call re-evaluates that quoted form. The
quote/eval round-trip defeats the sharing — a `Val` closure that
points at `done_val` once becomes an `Expr` with the full
`done_NF` term inlined at every position, and re-evaluating that
re-creates the recursion at a different `unf` depth so `==`
misses. It also makes Vec.lean's existing `native_decide` tests
slower (the quoted forms are larger than absEval's). Reverted.

The *right* integration is `subCheckVal : Val → Val → Bool` —
compare in the semantic domain so closures stay un-quoted.
`iotaIntro` becomes "open the RHS ι closure with the LHS Val in
the env"; `lam-lam` opens both closures with the same fresh
neutral; the seen-set holds `(Val × Val)` pairs (which need
`BEq Val`, derivable once `Closure` compares its `Expr` body and
`Env` structurally). `nfSubstE` is in `NbE.lean` as the entry
point that does env-extension instead of `body.subst 0 a`, ready
for whoever picks this up.

### Agent phase1-subcheckval, 2026-04-17

`done_ ⊑ dNat` is the *encoding*, not the checker. Trace under
subCheckVal (no fan-out, search completes):

  done_'s λs domain  = `λpred:dNat-closed. P (dsucc pred)`
  dNat[done_]'s λs   = `λpred:done_. P (dsucc'[done_] pred)`
                       (dNat's `λpred:bvar0` → `λpred:done_`)

  contra needs `dNat-closed ⊑ done_` — correctly false. And
  semantically: done_ calls `s dzero`, but a dNat[done_]-caller's
  `s` expects `pred:done_`, and `dzero ⊄ done_`. So done_ does
  not satisfy dNat's self-type under this encoding + standard
  function subtyping.

dBool (e08bce9) uses `fix B:Type. ι self:B. …` — B (fix) is the
*type* binder, stable under iotaIntro; self (ι) is the *value*
binder, substituted. dNat conflates them. The fix: wrap dNat in
`fix N:Type. ι self:N. …`, use `N` for all type ascriptions
(`λm:N`, `λpred:N`, `dsucc':(N→N)`), keep `self` only for the
final `P self`. Then iotaIntro substitutes self → done_ but the
λpred annotation stays `:N` (= dNat after fix-unfold), and the
contra `dNat ⊑ dNat` is reflexive.

This is an encoding change, not a checker change. Once dNat
matches dBool's pattern, `done_ ⊑ dNat` should close under the
*existing* subCheckNF (same path as `dtrue ⊑ dBool` in loop 1).
The earlier "NbE root cause" diagnosis below was the fan-out
*symptom*; subCheckVal removed the fan-out and exposed the
underlying encoding mismatch.

**Confirmed**: with `dNat = fix N:Type. ι self:N. …`,
`subCheck 200 done_ dNat = .ok true` under the existing
subCheckNF. All prior tests still pass (build green, no
regressions in DBool/Array/Vec/Tests/NbETests). `dtwo/dthree`
are now *correct* (the contra is reflexive) but subCheckNF
still fans out on them — that's the genuine NbE-integration
work, now decoupled from the encoding question. `vecResult`
(which uses dthree) and `appendVec_wrong` (β-domain-check)
likewise.

### subCheckVal stuckRec-stuckRec arm; dtwo/dthree closed (5862916f)

Probing `NbE.subCheck` on the new encoding revealed a
closure-canonicity gap: the let-bound `dsucc` inside dNat's
body (domain `N` resolved from env) and the top-level `dsucc`
(domain a closed `dNat` Expr) are non-`beq` Vals even though
they denote the same function. When both are stuck on a
neutral (`dsucc pred`), the existing arms re-vapp (no progress,
arg neutral) → `.ok false`.

Fix: a `.neutral (.stuckRec fA aA), .neutral (.stuckRec fB aB)`
arm in subCheckVal that compares structurally — heads via the
`.fix,.fix` η-open arm (which normalises the env difference by
opening both under a shared fresh), args covariantly. With
this, `NbE.subCheck` accepts dzero/done_/dtwo/dthree ⊑ dNat
and rejects dNat⊑dzero, dzero⊑done_.

DNat.lean's dtwo/dthree assertions switched to `NbE.subCheck`
(the Val-domain checker is the better algorithm for these;
subCheckNF still fans out on them and will be retired once
subCheckVal handles the full test surface). Added 4 extra
agreement examples (dzero/done_ positives + 2 negatives under
NbE.subCheck) to lock in semantic agreement with subCheckNF.

**Markers: 3 → 2. Std sorries: 4 → 2.** Remaining: Vec
appendVec_wrong (β-domain-check) and vecResult (dthree
cascade).

### vecResult closed via NbE.subCheck (5862916f)

`NbE.subCheck 400 vecResult (Vec Nat) = .ok true`. Same root
cause as dtwo/dthree (vecResult has length dthree); same fix.
Verified that NbE.subCheck *accepts* appendVec_wrong (it has
no domain check during β), so the last marker genuinely needs
the β-domain-check restored in the typing evaluator.

**Markers: 2 → 1. Std sorries: 2 → 1.** Last marker:
appendVec_wrong.

### TyCheck.lean: bidirectional pass; appendVec_wrong closed (5862916f)

Two separate experiments confirmed the β-domain-check cannot
live inside `absEval`/`subCheckNF`:

  1. **beta-restore worktree**: full-fuel lenient check hangs
     (every β through `Array_` triggers a `done_ ⊑ dNat`
     side-goal, which itself β's through `Array_`, …). At fuel
     ≤64 it returns spurious `.ok false` for legitimate `Array_
     done_` — 7 Array.lean regressions.
  2. **Targeted gate** (only on neutral-headed args): regresses
     `appendArrays` typing because `arr ⊑ Pair Type Type`
     ascends through the muSeen-gated `Array_ (dsucc pred) T`
     to `Type`, losing the `Pair T (Array_ pred T)` reduct.

Both fail for the same architectural reason: the domain check
calls `subCheckNF` which calls `absEval` which calls the domain
check. The standard escape is a *separate* bidirectional pass
that walks the syntactic term, doing one domain check per
`.app`, with NbE supplying conversion as a black box.

`Och/TyCheck.lean` implements this:
  - `tyInfer`/`tyCheck` mutual; `whnfPi` unfolds fix/iota to
    expose Π heads (substituting the inhabitant for ι-self).
  - `.fix`/`.iota` are black boxes of their annotation — the
    pass does not recurse into bodies, so the unprovable
    `Array_ (dsucc pred) T ⊑ Pair Type Type` cast inside
    `appendArrays` never surfaces.
  - β fast-path for `.app (.lam ..) a` and `.app (.letE ..) a`
    avoids the quote-codomain round-trip when the head is an
    inlined helper (`mkVec`, `dpair`).

Fixing this exposed two `subCheckVal` gaps:
  - `synthNeutral .stuckRec f arg` returned `f`'s annotation,
    not `(annotation of f) arg` — wrong arity. Fixed.
  - `subCheckNeutral` had no `.stuckRec, .stuckRec` arm, so
    `Array_ (dadd n1 n2) T` from two paths (appendArrays' return
    annotation vs mkVec's domain via the quote codomain) failed
    even though their `quote`s are *identical Exprs*. Same
    structural fix as the subCheckVal arm.

`typeCheck appendVec τ = .ok true`; `typeCheck appendVec_wrong τ
= .error "arg ⊄ dom at fix·5 (arg=?0)"` — rejected exactly at
the 5th argument of the inner `appendArrays` call.

**Markers: 1 → 0. Std sorries: 1 → 0. PHASE 1 COMPLETE.**

### Phase 2 begins: SoundnessAudit.lean (5862916f)

Three soundness gaps identified and recorded as executable
`native_decide` witnesses in `Och/SoundnessAudit.lean`:

  - **A1**: covariant neutral-app congruence (the `Pair a b ⊑
    Pair A B` mechanism) violates substitution. Witness:
    `Pair zero_ unit_ ⊑ Pair Nat_ Unit_` accepted; eliminating
    with `λn. λu. n→Unit_` gives `zero_→Unit_ ⊄ Nat_→Unit_`.
  - **A2**: type-in-type (`_ ⊑ Type`). Intentional, but admits
    Girard's paradox; the soundness theorem must work modulo
    this.
  - **A3**: subCheck β is type-blind (`(λn:Nat_. n) Bool ⊑
    Bool` accepted). `typeCheck` catches it.

A1 is the actionable one: fixing it requires reverting to
bidirectional neutral-arg comparison and re-encoding `Pair`
(and hence `Array_`) with a separate value constructor. The
DECISION-LOG entry sketches the path. The other arms of
`subCheckVal` (refl, seen, lam-lam, iotaIntro, fix-unfold,
neutralAscent) follow standard sound rules.

### A1 fixed: bidirectional neutral-app + new Pair encoding (5862916f)

`subCheckNeutral`/`subCheckVal`/`subCheckNF`'s neutral-app arms
now require argument *equivalence* (`a ⊑ b ∧ b ⊑ a`). The
closure-canonicity case (DNat dtwo/dthree) and the appendVec
return-type comparison both still pass — they were always
equivalences, not strict subtypes.

`Pair` re-encoded as `λA. λB. λX. λk:(A→B→X). X` (parametric
body); separate `pair_ A B a b = λX. λk. k a b` constructor.
`pair_ … ⊑ Pair A B` via type-ascent through `k` (synth
`k a b : X`). The new Pair is *soundly* covariant in A, B
(contra² on k's domain). All Pair/Array/Vec value-construction
sites updated to `pair_ A B a b`. fst_/snd_ stay monomorphic at
`Pair Type Type` (any Pair coerces via type-in-type).

Build green; markers/Std-sorries stay at 0. SoundnessAudit's
A1 section now records the fix as `a1_ruleFixed` /
`a1_substitutionHolds` / `a1_pairAscent`. Two open items
remain: A2 (type-in-type, accepted as model axiom) and A3
(β-blind subCheck, mitigated by `typeCheck`). The arms-by-arms
soundness proof can now begin.

Verifier (12 checks, 6 adversarial probes): PASS. The old
unsound encoding is rejected even if reverted; equivalent-
but-not-syntactic args still accepted; ~2.15× DNat slowdown
from bidirectional doubling but no fuel exhaustion.

### Subtype' context-indexed; first hand-derivations (5862916f)

`Subtype'` is now `Ctx → Expr → Expr → Prop` with a `.bvar`
rule (`Γ[k] = τ → Γ ⊢ bvar k ⊑ τ.shift (k+1) 0`) realising
type-ascent declaratively. `lam`/`iota_body`/`fix_body` push
the binder's domain onto Γ. `SubtypeCore.toSubtype'` now
quantifies over Γ.

Two hand-built derivations in Soundness.lean confirm the
constructors suffice: `Subtype' [] zero_ Nat_` and
`Subtype' [] unit_ Unit_`, both via three `lam_body` then one
`bvar` (the body `z ⊑ X` is exactly `Γ[1] = bvar 0` shifted).
This is the smallest end-to-end witness that the declarative
relation matches the algorithm.

The remaining gap (β-conversion rule) is documented inline.
Next: prove `subCheckVal_sound` arm-by-arm; the lam-lam,
fix-unfold, and bvar arms now have direct constructors.

### β-conversion + four hand-derivations + non-partial subCheckVal (5862916f)

`Subtype'` gained `beta_L/R`, `letE_L/R`, `asc_L/R`; derived
`app_head`, `beta_head`, `app_ascent`. Hand-derivations for
`(λx.x) zero_ ⊑ Nat_` and `one_ ⊑ Nat_` (via app_ascent).
`subCheckVal` & co. made non-partial (`termination_by fuel`).

### A4/A5 found; A5 fixed; NbE made non-partial (5862916f)

**A4**: inductive `Subtype'` is incomplete for equirecursion.
Tracing `dtrue ⊑ dBool` declaratively: after fix/iota unfolds
the lam-lam contravariant domain needs `dtrue ⊑ dBool` again.
The algorithm closes this via the seen-set; the inductive
relation cannot. Documented with three fix options
(seen-indexed / step-indexed / parameterised coinduction);
seen-indexed is closest to both the algorithm and Simple/'s
proof structure.

**A5**: both checkers' iotaIntro arm skipped the `a ⊑ ann`
premise, accepting `dtrue ⊑ ι self:Nat_. Type` despite
`dtrue ⊄ Nat_`. Fixed: both checkers now require `a ⊑ ann ∧
a ⊑ body[self:=a]`, with seen extended *before* the
annotation check so `fix B. ι self:B. …` closes coinductively.
Verified: constrained-ι rejected; dtrue⊑dBool, done_⊑dNat,
all DBool/DNat/Array/Vec/Tests still pass. The declarative
`Subtype'.iota_intro` already had both premises, so this
brings the algorithm in line with the relation.

**NbE termination**: eval/vapp/quote/quoteClosure/quoteNeutral
all made non-partial (`termination_by fuel`; quoteClosure
gained a fuel match). Full build green. Combined with
non-partial subCheckVal, the entire algorithmic stack now
unfolds in proofs.

**Phase-2 status**: 5 audit findings (A1, A5 fixed; A2 axiom;
A3 mitigated; A4 open). Algorithm sound modulo A2/A4. Declarative
relation has every constructor needed; the one remaining gap
(A4: coinductive encoding) is the last prerequisite for
`subCheckVal_sound`.

### A5 ι-ι gap closed; A4 seen-indexed Subtype' (5862916f)

Verifier FAIL on d1275ab: NbE.subCheck's `.iota,.iota`
structural arm has its own iotaIntro fallback that skipped
the annotation premise, so `(ι:Type.Type) ⊑ (ι:Nat_.Type)`
returned `.ok true` from NbE but `.ok false` from subCheckNF
— the two checkers diverged. Fixed: the ι-ι fallback now
checks `a ⊑ annB` first (same as the `_, .iota` arm).
Regression `a5_iotaIotaPath` locked into SoundnessAudit.

`Subtype'` is now seen-indexed: `Seen → Ctx → Expr → Expr →
Prop` with `.hyp : (a,b) ∈ S → Subtype' S Γ a b`. The four
productive rules (`iota_intro`, three `unfold_*`) extend `S`
before recursing; everything else threads it. `Subtype'.weaken`
proven (seen-monotone). The `dtrue ⊑ dBool` witness in
Soundness.lean has its annotation premise closed via
`.hyp (List.Mem.tail _ (List.Mem.head _))` — the cycle that
previously had no finite derivation now closes in one step.

**All five audit items resolved or accepted.** Algorithm sound
modulo type-in-type. Every arm maps to a declarative
constructor; the seen-set has a declarative counterpart;
the whole stack is non-partial. `subCheckVal_sound` is now a
matter of fuel induction with no architectural blockers.

### `subCheckVal_subV` guard arms proven; supporting lemmas closed (5862916f)

Three parallel worktree forks, all landed:

  1. **`Val.beq` non-partial + `LawfulBEq`** (81d7935): the
     `partial` came from `Closure.beq`'s
     `(e1.zip e2).all (Val.beq …)` hiding the recursion in a
     higher-order arg; replaced with explicit `Env.beq` in
     the same mutual block. `beq_eq`/`beq_refl` proven by
     mutual structural induction; `LawfulBEq Val` instance.

  2. **`eval`/`vapp` fuel monotonicity** (45277e3): combined
     Nat-induction proving both halves; `unf` held fixed
     (only decrements within a vapp chain, never across the
     n→m bridge). `Closure.open_fuel_mono` is a one-liner.

  3. **`dtrue ⊑ dBool` body premise fully closed** (d0b6070):
     the flagship coinductive derivation. `unfold_fix_R` →
     `iota_intro` (annotation via `.hyp`) → `unfold_fix_L` →
     `unfold_iota_L` → `lam`³, with the contravariant
     P-domain closing via `.hyp` at seen[3], the t-domain
     via `app_cong` with `dtrue ≡ ι_dtrue` (each direction
     one fix-unfold), the f-domain via `.top`, and the body
     `t ⊑ P dtrue` via `.bvar`. Every `Subtype'` constructor
     exercised; no sorry.

`SoundnessProof.lean`: the `SubV` Val-level relation +
`subCheckVal_subV` proof. Guard arms (refl via `eq_of_beq`,
hyp via `seen_any_mem`, top) closed by fuel induction at
`maxHeartbeats 4M` (the succ-body is too large for default
unfold; refactoring `subCheckVal` to factor out the match
is the cleaner long-term fix). The match arms remain
sorried (each is `ih` + constructor + `openω_of_open`).

**No axioms** in the proven path: `Val.beq_eq_ax` removed.
Build green; 0 markers, 0 Std/Tests sorries.

### subCheckVal factored; 8 match arms proven; pre-existing sorries swept (5862916f)

Two more parallel-fork landings plus mainline cleanup:

  - **`subCheckVal` refactor** (77ac3da): match arms factored
    into `subCheckValMatch` (lex `(fuel, tag)` termination).
    `subCheckVal_subV` now runs at *default* heartbeats —
    `set_option maxHeartbeats` removed.
  - **8 match arms closed** in `subCheckValMatch_subV`:
    lam-lam, `_,.iota`, `_,.fix`, `.fix,_`, `.iota,_`, plus
    three trivial leaves (`_,.neutral`/`.type,_`/`_,.type`).
    Pattern: `rcases` each sub-result before simping `h`,
    then `ih` + matching `SubV` constructor +
    `Closure.openω_of_open(Fresh)`. Added `hfuel : fuel ≤
    fuelω` premise for the lift.
  - **Pre-existing sorries swept**: `Syntax.lean` 4 → 0
    (the `.letE` cases of the four substitution lemmas; same
    binder pattern as the preceding `.fix` case). `Eval.lean`
    7 → 6 (`concEval_not_letE` added, mirroring
    `concEval_not_asc`).

**Sorry inventory** (excluding `Och/Simple/` and Std/Tests
which are at 0):

| File | Count | On critical path? |
|---|---|---|
| `Syntax.lean` | 0 | — |
| `Eval.lean` | 6 | no (legacy `subCheckNF` fuel-mono) |
| `Subtyping.lean` | 4 | no (legacy `subCheckNF` shape) |
| `SoundnessProof.lean` | 8 | yes (7 match arms + quote bridge) |
| `Soundness.lean` | 3 | yes (target theorems, compose above) |

The 7 remaining match arms are the disjunctive ones (ι-ι and
fix-fix structural-OR-fallback; three stuckRec re-vapp
variants; two neutral struct/ascent). Each maps to existing
`SubV` constructors but needs case-splits on which branch
the algorithm took. The quote bridge (`SubV_to_Subtype'`) is
the substantive remaining work.

### Mutual reflection block; subCheckNeutral/neutralAscent fully proven (5862916f)

`SoundnessProof.lean` restructured into a 5-theorem mutual
block (`subCheckVal_subV`, `subCheckValMatch_subV`,
`subCheckNeutral_subN`, `neutralAscent_subV`,
`synthNeutral_synthN`) with `(fuel, tag)` termination
mirroring the algorithm. Key technique: `split` after a
`do`-block desugars binds positionally NOT in source-pattern
order, so the pattern is `split` (no `next`) → `rename_i` on
bind results → `simp [bind, Except.bind, pure]` → repeat.

  - `subCheckNeutral_subN`: **4/4 arms proven**.
  - `neutralAscent_subV`: **3/3 arms proven** (`.app` via
    `cases` on synthesised type instead of `split` to avoid
    binding-order brittleness).
  - `synthNeutral_synthN`: 2/3 (`.var`, `.app`; `.stuckRec`
    sorried — two-level match on f/ann).
  - `subCheckValMatch_subV`: **12/15 arms proven**. The
    disjunctive `_,.stuckRec`/`.stuckRec,_`/two neutral arms
    closed; ι-ι/fix-fix/stuckRec² (structural-OR-fallback)
    sorried with per-branch decomposition documented.

`SubV` extended with `iota_struct`/`fix_struct`/
`stuckRec_struct`. Legacy `Eval.lean` fuel-mono scaffolded
as a combined 3-conjunct Nat-induction (zero case proven;
succ arms documented but sorried — off critical path).

**Sorry-bearing declarations: 15** (clean build count). On
the soundness critical path: 6 (3 SoundnessProof + 3 target
theorems). Off-path: 9 (5 Eval legacy + 4 Subtyping legacy).
The `subCheckVal → SubV` direction is ~80% done.

### `subCheckVal → SubV` complete (5862916f, ef386b3)

The 3 structural-OR-fallback arms (ι-ι, fix-fix, stuckRec²)
and `synthN.stuckRec` closed. ι-ι/fix-fix: `split` on the
outer `match structural with` exposes `hstruct` via
`rename_i`; structural side → `SubV.iota_struct`/`fix_struct`
via `ih` on annOk + openFresh + body; wildcard side reuses
the proven `_, .iota`/`_, .fix` fallback pattern. stuckRec²:
4 bidirectional checks → `stuckRec_struct`; fallback nests
two `vapp` + beq splits → `revapp_R`/`revapp_L`/`.ok false`-
contradiction. `synthN.stuckRec`: nested split on the
`match f with` or-pattern + `match ann with` → the four
`SynthN.stuckRec*` constructors.

**The mutual reflection block has zero sorry.** Every arm
of `subCheckVal`/`subCheckValMatch`/`subCheckNeutral`/
`neutralAscent`/`synthNeutral` reflects into a `SubV`/`SubN`/
`SynthN` constructor by fuel induction, with no axioms
beyond `propext`/`Quot.sound` (from `LawfulBEq Val`).

**Sorry-bearing declarations: 13.** Critical path: **4**
(`SubV_to_Subtype'` quote bridge + 3 target theorems).
Off-path: 9 (legacy `subCheckNF`).

Verified PASS: all five reflection theorems depend only on
`propext`/`Quot.sound`; no `sorryAx`, no `Classical.choice`,
no `ofReduceBool`. 258 native_decide tests; refactor is
semantics-preserving.

### Quote bridge: 3 non-recursive cases proven; NbE-correctness lemma stated (5862916f)

`SubV_to_Subtype'` is over a mutual inductive (`SubV`/`SubN`/
`SynthN`), so `induction` rejects it (multiple motives). For
now the three non-recursive constructors are dispatched by
`cases`: `.hyp` → `Subtype'.hyp` via `hS` + quote-uniqueness;
`.refl` → `.refl` (quote functional); `.top` → `.top`
(quote .type = .type). The 12 recursive cases each need the
mutual recursor plus two supporting lemmas, both stated:

  - `quote_open_subst` (the NbE correctness theorem):
    `quote (cl.openω v)` is `Subtype'`-β-equivalent to
    `(quoteClosure cl).subst 0 (quote v)`. This is the
    substantive remaining obligation; the standard proof
    is a logical relation between `Val` and `Expr` indexed
    by the eval environment.
  - `Subtype'.narrow` (Γ-monotonicity): `domB ⊑ domA →
    Subtype' S (domA::Γ) x y → Subtype' S (domB::Γ) x y`.
    Bridges the algorithm pushing `domA` vs `Subtype'.lam`
    pushing `domB`.

**Sorry-bearing declarations: 14** (+1 from stating
`quote_open_subst` explicitly). Critical path: **5** (2
SoundnessProof + 3 target theorems).

### A6/A7 + bughunt-lite findings; quote_fuel_mono (5862916f)

Three parallel probes (divergence-sweep, quote-open-attack,
bughunt-lite) ran concurrently and found:

  - **A6** (incomplete): NbE's lam-lam pushed `domA` (source)
    not `domB` (target), rejecting `(λx:Nat_. x) ⊑
    (λx:zero_. zero_)` while subCheckNF accepted. Fixed →
    push domB; both checkers agree. Also brings SubV.lam in
    line with Subtype'.lam (no Γ-narrowing needed for the
    bridge's `.lam` case).
  - **A7** (unsound): NbE's `.fix,_`/`.iota,_` arms accepted
    `(fix self. self) ⊑ X` for any X via the seen-cycle
    (body=bvar0 → open returns `a` → seen' fires).
    Productivity guard `a' == a → false` added; subCheckNF's
    R-side `body == .bvar 0 → false` flipped to `→ true`
    (`X ⊑ ⊤` is true). Both checkers agree on all 8 probes.
  - **Bughunt-lite (3 confirmed at 5-0)**: (1) SubV.revapp_R/L
    lacked `vappω` premise — `b'` could be `.type`, making
    SubV trivially inhabited. Premise added + threaded. (2)
    legacy absEval/neutralType `.fix` arms substituted the
    inhabitant instead of the type. (3) stale comment.

`SubV.unfold_fix_L`/`unfold_iota_L` gained the same
productivity premise as the algorithm (without it, body=
bvar0 + .hyp derived ⊤⊑c via the relation too).

`quote_fuel_mono`/`quoteClosure_fuel_mono`/
`quoteNeutral_fuel_mono` proven (NbE.lean). `eval_unf_equiv`
stated as the precise NbE-correctness obligation;
`quoteClosure_eq_quote_openω_fresh` proven conditional on it.

**SoundnessAudit: 7 findings (A1–A7), 5 resolved.** The
algorithm is sound modulo type-in-type. `subCheckVal → SubV`
remains fully proven (the SubV constructor changes were
absorbed by threading evidence the proof already had).

**Sorry-bearing declarations: 17** (+3 from stating
`narrow`/`shift_preserve`/`eval_unf_equiv` precisely).
Critical path: **6** (3 SoundnessProof + 3 target theorems).

Verified PASS (12 checks incl. β-reducible-self adversarial).
Divergence sweep: **0/576** (locked in as `divergenceSweep_zero`).

### Logical relation R; eval_unf_equiv derived; mutual bridge (5862916f)

Two parallel worktree forks landed and auto-merged:

  - **Step-indexed logical relation `R n d v e`** ("v
    realises e at step n, depth d"). Recurses on `n`; the
    `.lam` clause Kripke-quantifies over `n' ≤ n` (Appel-
    McAllester downward closure). `Equiv` (Subtype'-both-
    directions) defined with refl/symm/trans. `R_quote_equiv`
    *proven*: the base conjunct of `R` at nonzero index gives
    `quote v ≡ e`. **`eval_unf_equiv` is now derived** from
    the (sorried) fundamental lemma `eval_realises` — apply
    at unf₁ and unf₂, both realise the same `e.substEnv ρe`,
    compose via `Equiv.trans ∘ Equiv.symm`. No direct sorry.
  - **3-motive `@SubN.rec`** for the bridge. `SubN.var/app/
    stuckRec` and `SubV.neutral_struct/neutral_ascent` (most
    sub-cases) proven. New helpers: `quoteNeutral_app_shape`,
    `quoteNeutral_var_shape`, `quoteNeutral_stuckRec_shape`.
    The 10 closure-opening cases sorried with IHs visible
    (gated on `quote_open_subst`).

**The entire soundness chain reduces to `eval_realises`**
(the fundamental lemma of `R`). Everything else is either
proven or derived from it. Sorry-bearing declarations: 21
(+4 from stating `R_mono`/`eval_realises`/`REnv_id`/the
3-motive bridge block; `eval_unf_equiv` no longer counts).

### A8; eval_realises .lam/.app/.fix/.iota merged (5862916f)

**A8** (unsound vs concEval): both evaluators returned `τ`
for `.asc t τ`, accepting `Nat_ ⊑ (zero_:Nat_)`. But
`(zero_:Nat_)` computes to `zero_` (concEval, Subtype'.asc_*),
and `Nat_ ⊄ zero_` — subject reduction fails. Found by the
`.asc` case of `eval_realises`. Fix: both evaluators return
`t`. `Std/Id.lean`'s §6.4 "widening via asc" tests updated
(the widening *intent* lives in `typeCheck`'s annotation
handling, not the value evaluator). Divergence corpus
extended to 26×26=676 with `.asc` terms; still zero.

`eval_realises` two-fork merge:
  - **R stabilised**: ∀-form base (`∀ e', quote = e' →
    Equiv e' e`), `d`-depth lam-Kripke, `n'<n` fix/iota-Kripke.
  - **Closed**: `.type`, `.bvar`. `.lam` Kripke mostly closed
    (REnv_take + ihm at n'). `.app` split per fV (`.lam`/
    `.neutral` structured). `.fix`/`.iota` Kripke threaded.
  - **Proven helpers** (cumulative): `R_mono`, `REnv_id`,
    `R_quote_equiv`, `REnv_mono`, `REnv_cons`, `R_resp_Equiv`,
    `REnv_take`, `closedAt_bvarBound`, `Closure.mk'_body_closed`,
    `Equiv.lam`/`.app`/`.beta`, `quote_fuel_mono` family.
  - **Open helpers**: `substEnv_closedAt_irrel`,
    `R_depth_lift`, `REnv_lift`, `eval_env_take`.
  - **5 post-merge re-thread sorries**: cross-fork `ihm`
    signature mismatches (argument-order plumbing).

**8 audit findings (A1–A8), 6 resolved.**

**All three remaining markers reduce to the NbE
root cause:** `done_/dtwo/dthree ⊑ dNat` and `vecResult ⊑ Vec Nat`
are the dNat-self-substitution fan-out directly; `appendVec_wrong`
needs the β-site domain check restored, which is blocked on the
same fan-out. Once an NbE/closure evaluator (or any normaliser
whose NF is canonical and where substitution doesn't copy) lands,
the β-site domain check can come back, and all three should close
together.

### Agent phase1-bounded-domcheck-deadend, 2026-04-16

Tried obstacle (3) with a bounded-fuel domain check: run
`subCheckNF (min fuel 30) a' dom` at every β and reject only on
`.ok false` (`.ok true` and `.error` proceed). The hope was that
the simple `arr2 : Array_ n2 T ⊄ Array_ n1 T` mismatch would be
caught quickly while `done_ ⊑ dNat` would error (out of fuel) and
proceed. It doesn't work: subCheckNF returns `.ok false` for
legitimate deep checks before it errors (the appendArrays body
hits `bvar 0 ⊄ (λpair. pair Type Type)` at fuel 30 because the
type of bvar 0 needs more than 30 fuel to widen to the Pair-
projection shape). So the bounded check rejects valid β.
Documented in the Eval.lean comment so it isn't retried. The
right fix is probably to delay the domain obligation to where
subCheckNF actually *uses* the application's result type (i.e.
inside neutralType's `.app` arm), not at the β site.

### A6 reverted to `domA`; DNat build hang root-caused (5862916f, 2026-04-18)

Verifier FAIL on `cebb1b0`: clean `lake build` hung at
`Och.Std.DNat` (RSS frozen ~708 MB, >25 min). Bisected the
27 commits since the last clean DNat build (`047e59f`,
277 s); the `972db66` PASS verdict had been on cached oleans.
Three-way parallel bisect (`81d7935`/`77ac3da`/`f2684c9`) plus
revert-isolation (`revA6`/`revA7`/`revBoth`) pinned it to
`f2684c9` (A6: `tyCtx.push domA → domB`).

The mechanism: `dNat`'s inner `let dsucc = fix …` evaluates to
a `.fix` whose closure env (after `Closure.mk'`'s `.take`-trim)
is `[dzero, fresh_self@d, vNat]`. The body never references
env[1], but `.take (bvarBound − 1)` keeps it because `N` at
index 2 forces `take 3`. So each structural ι-open at depth
`d` yields a structurally-distinct `dsucc_local`. With `domB`
(taken from `dNat`'s side, hence referencing `dsucc_local`),
neutral-ascent synthesises types containing it; the seen-list
`==` never matches; `dtwo ⊑ dNat` goes exponential. With
`domA` (taken from the input `dtwo`, whose closures contain
no fresh vars) the seen-list works. `#eval NbE.subCheck 170
dtwo dNat`: instant at `domA`, >60 s at `domB`.

A6 was an *incompleteness* fix (`(λx:Nat_. x) ⊑ (λx:zero_.
zero_)`), not a soundness one — so reverting it leaves the
Phase-2 theorem statement unchanged. Reverted `domB → domA`
in `subCheckValMatch`; mirrored in `SubV.lam`; updated
SoundnessAudit A6 to DEFERRED with `a6_dtwoFastWithDomA`
regression; divergence sweep now whitelists the A6 pair and
asserts NbE only ever *under*-accepts. The bridge `SubV.lam →
Subtype'.lam` will need `Subtype'.narrow` (already stated,
sorried). DECISION-LOG entry added.

A worktree fork is implementing the principled fix —
mask unreferenced closure-env entries with a canonical
placeholder so `Val.beq` identifies `dsucc_local` across
fresh-opens — after which `domB` can come back.

### Three forks integrated; subCheckVal_sound wired (5862916f, 2026-04-18)

`70307d5` clean-builds in 580 s (fresh worktree, no oleans);
the DNat hang is gone. Cherry-picked two of the three forks
on top:

- `438931b` → `d45f2d9`: `Subtype'.narrow_at` (position-`k`
  context narrowing) proven for 18/19 constructor cases;
  `narrow` derives from it.
  The one open case is `ctx_extend` — pushing a binder past
  a seen-set entry; the entries' Exprs are closed so this is
  morally the identity, but stating that needs a closedness
  invariant on `S`.
- `fb8164a` → `b668959`: `eval_realises` `.app` head sub-cases
  threaded — `.lam` head closed (was already), `.type`/stuck
  heads closed (new), `.fix`/`.iota` heads down to four named
  obligations: `vapp_open_eq` (vapp of an unfolded fix is
  vapp of body[self↦fix]), `R_resp_iota_unfold`,
  `R_resp_fix_unfold`, and a recursion-shape fix
  (recommendation: ∀-`unf`-quantify `R`'s Kripke clause and
  add `m ≤ fuel` to `eval_realises` so the inner `vapp` call
  is in IH range).
- Closure-mask fork (`6a0d2bf`, tagged
  `a6-closure-mask-experiment`): NOT cherry-picked. Env
  masking makes `dtwo ⊑ dNat` fast under `domB` but not
  `dthree`; the residual mismatch is in closure *bodies*
  (inner-let `dsucc_local` body is `bvar 3`, top-level
  `dsucc` body is the closed `dNat` Expr), so `domB` would
  need quote-based canonicalisation. `domA` stands;
  DECISION-LOG updated.

`subCheckVal_sound` (`Och.Soundness`) is now a direct term:
`SubV_to_Subtype' ∘ subCheckVal_subV` with the empty-context
quote premises discharged vacuously and `quote_fuel_mono`
lifting the user-supplied fuel. Soundness.lean: 3 → 2 direct
sorries (`typeCheck_sound`, `concEval_preservation`).

Sorry-using declarations (clean build at d4b7259): Eval 5,
Subtyping 6, SoundnessProof 9, Soundness 2.

### Eval.lean dead-scaffold removal (5862916f, 2026-04-18)

The legacy-`subCheckNF` fuel-mono scaffold
(`absEval_subCheckNF_neutralType_fuel_mono` from `f82fbfc`)
and four `*_preserves_closedAt`/`*_ctx_irrelevant` lemmas
(`851b67b`) had zero callers and were sorried since
introduction. Removed; doc marker points back to `f82fbfc`.
Eval.lean: 5 → 0 sorries. Total: 22 → 17.

### Six-fork integration; A9 found and fixed (5862916f, 2026-04-18)

Six worktree forks integrated (one parked). Tags pushed at
each fork commit for traceability.

- **R-Kripke restate** (`r-kripke-restate-fork`): `R`'s
  Kripke clauses now ∀-`fuel'`/`unf'`-quantified; 4
  `eval_realises` leaf sorries closed.
- **TyCheck de-partialised** (`tycheck-departialise-fork`):
  `tyInfer`/`tyCheck`/`tyCheckFallback`/`whnfPi` now total
  via `(fuel, tag)` lex; `unfold tyCheck` works.
- **`tyCheck_sound_closed` structured**
  (`tycheck-sound-induct-fork`): mutual `(fuel, tag)`
  induction. `tyCheckFallback_sound_closed` and
  `tyCheck`'s `.asc`/catch-all arms **proven**;
  `quote_total_on_eval`/`whnfPi_sound`/
  `tyInfer_sound_closed` stated. Found A9.
- **`Subtype'` congruence constructors**
  (`subtype-cong-ctors-fork`): `.iota_cong`/`.fix_cong`/
  `.letE_cong` added (vary both ann and body).
  `Equiv.subst_resp` and `R_resp_Equiv` closed (no leaf
  `sorry`; both reduce to the pre-existing `Equiv.shift`);
  `Subtype'.subst_body` removed (subsumed). SoundnessProof
  11 → 8.
- **`ctx_extend_at` deepened** (`ctx-extend-fork`): 16/19
  cases proven; the 3 binder cases need depth-tagged seen
  entries (or `Subtype'`'s `.iota_intro`/`.unfold_*` to
  record closed pairs). 5 shift/subst lemmas added to
  Syntax.lean (all proven).
- **`SubtypeCore` removed**: 4 dead legacy-checker sorries.
  Subtyping 6 → 2.

**A9** (`tyInfer` trusted fix/ι annotation): `typeCheck
(.fix Nat_ unit_) Nat_` was `.ok true`. Fixed by a
`.fix`/`.iota` arm in `tyCheck` that does
`subCheckVal (eval e) expected` directly (bypasses the
annotation-trusting `tyInfer` path; sound via
`subCheckVal_sound`). Two earlier attempts (body-check
inside `tyInfer`; `.ok none` on body-check failure) both
regressed `appendVec` because nested-fix annotations are
opaque neutrals. `tyCheck_sound_closed`'s new arm is
proven; SoundnessAudit gains `a9_fixIotaBodyChecked`.

**Sorry counts at `c5914db`**: Eval 0, Subtyping 2,
SoundnessProof 8, Soundness 5. Total **15** (from 22 at
session start). All four target theorems
(`subCheckVal_sound`/`typeCheck_sound`/
`concEval_preservation`/`soundness`) wired through with no
direct sorry.

### unfold_iota_R; concEval_equiv 8/8; A9 leak paths closed (5862916f, 2026-04-18)

Verifier on `c5914db` found two more A9 leaks: `tyInfer`'s
own `.letE` arm and the `.app (.letE …) a` let-floating
arm both consult `tyInfer val` without verifying. Same fix
as `tyCheck`'s `.letE` (verify via `tyCheck val valTy`,
fall back to singleton). `appendVec` still accepts;
`a9_fixIotaBodyChecked` now five witness conjuncts.

Removed `Subtype'.shift_preserve` (wrongly-stated, subsumed
by `ctx_extend_at`, no callers): Subtyping 2 → 1.

Two more forks integrated:
- **equiv-shift** (`equiv-shift-fork`): `Equiv.shift`'s
  cons-Γ case wired through `Subtype'.ctx_extend [τ]` —
  consolidates `Equiv.shift` and `ctx_extend_at` into the
  same depth-tagged-seen root cause (DECISION-LOG route a).
- **soundness-bundle** (`soundness-bundle-fork`):
  `concEval_equiv` (both directions) proven 7/8 head
  shapes; `concEval_refines` and `quote_total_on_eval`
  derived from it and `eval_quotable` resp. Found: `match`
  on `Equiv`-typed goals eagerly instantiates implicits;
  use `cases` instead.

Added `Subtype'.unfold_iota_R` (symmetric to
`unfold_fix_R`; `iota_intro` is the strictly-stronger
algorithmic form). With it, `Equiv.iota_unfold` is a
one-liner; `concEval_equiv`'s `.app .iota` head closes
(now 8/8). Soundness 5 → 4.

**Sorry counts at `d19f092`**: Eval 0, Subtyping 1,
SoundnessProof 8, Soundness 4. Total **13**. Reduces to
four root obligations: depth-tagged seen-set
(`ctx_extend_at` + `Equiv.shift`); `eval_realises`
recursion-boundary leaves; `eval_quotable` Val-size
measure; open-Γ generalisation of `tyCheck`/`tyInfer`/
`whnfPi_sound`.

### Tech-debt sweep + perf root-cause (5862916f, 2026-04-19)

Six parallel forks. **Clean build: 580 s → 71 s** (8.2×).

- **Perf root-cause** (`perf-rootcause-fork`, +48 to
  SubCheckVal): `Val.beq` walks the value DAG as a *tree*.
  With `unfBound=32`, `dsucc`'s self-applying P-domain
  makes `vthree` a 15.6 M-node tree-walk (the DAG is 63
  nodes; eval is 3 ms). Fix: `unsafe Val.beqFast` with
  `ptrEq ||` prefix, `@[implemented_by]` so the proven
  `Val.beq` is unchanged (`subCheckVal_subV` axioms still
  `[propext, Quot.sound]`). `dthree ⊑ dNat` 322 s →
  0.3 s (1046×); `dfive` (previously untestable) flat
  ~330 ms. PerfProbe.lean carries the regression.
- **Legacy `subCheckNF` retired** (`retire-subchecknf-fork`,
  net −449 lines, Eval.lean 808→339): the Expr-domain
  checker existed for the divergence sweep, which had done
  its job (A1–A8). New SoundnessAudit sweep is NbE-only
  (`sweep_refl`/`top`/`strict`/`a6_pinned`). One test
  weakened: `appendArrays` at its declared type is an
  A6-family NbE incompleteness (legacy accepted via
  `neutralType` Type-widening); pinned in PerfProbe.lean.
- **DBool: very-dependent encoding** (`38d1031`):
  `dtrue`/`dfalse` are now `ι self:Type. λP:(self →
  Type). …` — no per-constructor `fix B` wrapper. The
  `e08bce9` workaround predated A4/A5/A7; the
  very-dependent form now goes through directly. The
  hand-built `dtrue ⊑ dBool` derivation is shorter
  (t-domain is `.refl`).
- **DNat: local-let `dzero` removed**
  (`dnat-simplify-fork`): top-level `dzero` is
  very-dependent, `dNat` references it directly.
  `dsucc_local` stays (genuinely needs `N`). DNat module
  305 s → 256 s pre-ptrEq → ~3 s post.
- **Macro sugar** (`macro-sugar-fork`, `ced372c`):
  `ι x. body`/`fix x. body`/`let x = v in body` desugar to
  the `:Type`-annotated forms (`rfl`-identical Exprs).
- **`letBinderType` helper** (`tycheck-helper-fork`, net
  −5): the three duplicated A9 verification blocks
  factored into one mutual-block function.
- **PropertyTests.lean** (`test-additions-fork`, +240, 33
  tests): open-Γ `subCheckVal` (10), negative subtyping
  (16), `nf` round-trip + refl/top sweeps (7). Two
  *findings* pinned: (a) `nf` is not syntactically
  idempotent (`nf (nf done_) ≠ nf done_` — the
  `eval_unf_equiv` gap; semantic idempotence holds);
  (b) open-Γ neutral-vs-concrete is rejected both ways
  (LHS-only ascent — A6 from a different angle).

13 sorries unchanged.

### Open-Γ generalisation; eval_quotable closed (5862916f, 2026-04-19)

Three soundness-engineering forks on root obligations #3
and #4. Sorry counts after integration: Subtyping 1 +
SoundnessProof 13 + Soundness 3 = **17** (temporarily up
from 13 — the previously-implicit open-Γ obligations are
now named lemmas; dedup of closed/open forms in flight).

- **`eval_quotable`** (`eval-quotable-fork`, root #3): the
  unconditional form is **genuinely false** — `eval 2 _ []
  (.lam .type huge)` succeeds at fuel 2, but `quoteClosure`
  re-evals `huge` (unbounded). Closed via `(nf fuelω
  e).isSome` side-condition; the `nf` witness *is* the
  quote, transported via `eval_fuel_mono`. Axiom-clean
  `[propext, Quot.sound]`. `quote_total_on_eval` and
  `nf_asc_term_isSome` proven; `hnfe`/`hnfτ` threaded
  through `tyCheck_sound_closed` chain. DECISION-LOG
  2026-04-19. Soundness 4→3.

- **Open-Γ skeleton** (`open-gamma-fork`, root #4):
  `OpenCtx Γ ρ Γe` bundles `QuotesCtx` + ρ-quotable +
  eval-quote≡source. `subCheckVal_sound_open`,
  `tyCheckFallback_sound_open`, and `tyCheck_sound_open`'s
  `.asc`/`.fix`/`.iota`/catch-all arms **proven** (`.asc`
  is *shorter* than the closed form — no source-τ
  round-trip). Closed corollary derives at `OpenCtx.empty`
  + `substEnv_nil`. SoundnessProof 8→16 (the +8 are the
  named obligations). **Design finding**: `OpenCtx`'s
  `hρeq` was too strong for let-bound entries.

- **`OpenCtx` ρe-threading** (`openctx-rhoe-fork`):
  `OpenCtx Γ ρ Γe ρe` carries the explicit Expr-level
  substitution. `OpenCtx.push_fresh`/`push_let` **closed**
  (reduce to `eval_realises` + `R_depth_lift` +
  `eval_quotable_open`). `QuotesCtx.push` proven
  axiom-clean. SoundnessProof 16→13.

A dedup fork is replacing the closed `tyCheck_sound_*`
mutual block in Soundness.lean with corollaries of the
open forms; target is Soundness 3→0, SoundnessProof ≤13.

### Soundness.lean sorry-free; root #3 done (5862916f, 2026-04-19)

Dedup landed (`dedup-closed-open-fork`). The closed
`whnfPi_sound`/`tyInfer_sound_closed`/
`tyCheckFallback_sound_closed`/`tyCheck_sound_closed` are
now four short corollaries of `*_open` at `OpenCtx.empty`
+ `substEnv_nil`. The ~225-line mutual block deleted.
`eval_quotable_open` proven axiom-clean (the previous
`hρ`-only statement was also false; the per-call-site
`hnfq` evidence is the new `openNf_holds` — same shape as
the threaded `hnfe`/`hnfτ`).

**`Soundness.lean` is sorry-free.** All four target
theorems plus all closed-context supporting lemmas wired
through. **14 sorries** (Subtyping 1, SoundnessProof 13).
Three root obligations remain (root #3 `eval_quotable` is
done axiom-clean):
  1. Depth-tagged seen → `ctx_extend_at` + `Equiv.shift`
  2. `eval_realises` recursion-boundary → cascades to
     `quote_open_subst` + `SubV_to_Subtype'` chain
  3. Open-Γ residuals: `whnfPi_sound_open`/
     `tyInfer_sound_open`/`tyCheck_sound_open` `.lam`/
     `.letE`/`letBinderType_sound_open`/`openNf_holds`

## Open `TODO[mega-loop]` markers

Agents should run `grep -rn "TODO\[mega-loop\]" lean/` for the current list.
At time of writing there are 11 markers, spanning:

- Dependent-intro tests (`dtrue ⊑ dBool`, `dzero ⊑ dNat`, etc.)
- Negative-check re-verifications
- Array-over-DNat smoke tests
- Transitivity exhaustive checks

## Session log

Agents: append a brief session summary below. What you changed, what you
tried, what blocked you, what the next agent needs to know. Be specific —
file names, markers closed, definitions changed.

---

### phase1-array-dnat-swap (2026-04-14)

**Encoding swap, not a marker close.** Replaced Church-Nat-indexed Array_
with dNat-indexed Array_. The transitional `Array_dnat` is gone; the name
`Array_` now refers to the dNat version. `Vec`, `mkVec`, `appendVec`,
`appendArrays` all moved to dNat indices. `Tests.lean` §6.2 abstract-vec
tests ported. Added `dadd` in Std/Array.lean (was no dNat addition before).

**Test disposition.** Most Vec/Array tests that previously passed via
`native_decide` under Church-Nat are now sorry'd with TODO[mega-loop]
markers. The root obstruction is consistent: the motive
`λn:dNat. λarr:(Array_ n Nat_). _` has a binder whose body
`Array_ n Nat_` evaluates by unfolding Array_'s outer `fix` and then
running DNat's eliminator on the bvar `n`, which is stuck. The old
Church-Nat version did the analogous stuck reduction but absEval silently
admitted it; under the new strict absEval those tests fail honestly.

**Specific flips of intent:**
- `appendArrays` type-check test flipped from `≠ .ok true` to `= .ok true`
  (sorry'd). Under Church-Nat the negative assertion was expressing the
  encoding's limitation; the whole point of dNat indexing is that the
  positive assertion should hold once the mega-loop is closed.
- `appendVec` type-check similarly flipped. `appendVec_wrong` stays as
  `≠ .ok true` — it's a negative assertion that survives the swap.

**Live tests kept:**
- concEval tests on `appendArrays [1,2] [3] = [1,2,3]` in Std/Array.lean.
- isZero-checks, disZero computation tests in Std/DNat.lean (unchanged).
- All non-Vec/Array integration tests in Tests.lean.

**Nothing was trivialised.** No test was swapped from a succ-case to a
zero-case to dodge the reduction (e.g. `Array_ done_ T` stayed as
`Array_ done_ T`, not `Array_ dzero T`).

**Nothing was deleted.** Every Church-Nat test has a dNat analogue at
parity.

**Sorry count added:** ~17 new TODO[mega-loop] markers
(6 in Std/Array.lean, 12 in Std/Vec.lean, 2 in Och/Tests.lean).

**Downstream fallout noticed:** none. `Std/Sigma.lean`, `Std/Pair.lean`
etc. don't reference Array_ or Vec. `Simple/` is untouched (directive).

**Next agent:** the central obstruction is DNat's Scott-style eliminator
on a neutral bvar. If the eliminator were Church-with-ι (per
`docs/research/self-types-for-och.md`), `Array_ n T` would normalize
under an abstract n binder via dependent elimination. That's a
structural DNat redesign — orthogonal to, but unblocking, this swap.
`lake build` passes.
