# Removing substitution: environment-based evaluation for the comptime fragment

**Status: design resolved through discussion (2026-08-07); not yet scheduled.**
All pre-implementation questions are resolved inline (struck-through, with their
resolutions); one item is explicitly deferred (§7) and two are implementation-time
inventories. The document's remaining job is to be attacked by readers and to
brief the eventual implementation milestone (M30 candidate).

## 0. The one-sentence version, and the scope decision

Today the comptime fragment evaluates by *substitution* (copy the argument into the
body, adjusting binder indices) while the runtime evaluates against the environment Ω
(look variables up in a store). The proposal: make the comptime fragment
environment-based too — a λ evaluates to a *closure* (its body plus the environment it
was born in), and application extends that environment instead of substituting. The
technique is standard; it is how Lean's and Agda's own evaluators work, under the name
*normalization by evaluation* (NbE).

**Scope (resolved 2026-08-07): the hot path is the comptime fragment only.** The
runtime store Ω, its `Var` ids, and its flat-arena frame mechanism are untouched by
the first step. The eventual end-state — plain source names as the one variable
representation everywhere — is reached in two steps, and the second (runtime names
via frame pop-with-drop, §7) is explicitly deferred: worth taking if it turns out
easy, natural when compilation work starts, not on the current path.

## 1. Why consider this at all

Stated soberly, because the honest motivation ranking matters:

1. **It deletes a bug class.** Substitution needs index arithmetic (`substPure`,
   `shiftPure`, the delayed-lift machinery). A hand-written index in a motive sat
   wrong for five milestones (M11→M28) without detection, because nothing ever
   consulted it. Environments have no index arithmetic to get wrong.
2. **It closes the last big runtime/comptime implementation gap.** Both fragments
   become environment machines. The difference between them stops being "two
   evaluation styles" and becomes "two disciplines about what the environment may
   contain" — which is the language's actual content (ownership vs knowledge).
3. **It dissolves the λ-merge tension** (task #17). The named-vs-de-Bruijn conflict
   existed because a λ body must survive *inside* stored values, where substitution
   demands indices and Ω demands stable names. A closure sidesteps it: the body is
   stored unevaluated with its environment, and nothing substitutes into it, ever.
4. **Performance is NOT a motivation.** Phase C measured the checker at 1.3% of the
   build, heaviest single check 181 ms. NbE is typically faster than substitution,
   but nothing here is justified by speed, and any speed claim must be measured, not
   assumed. If this change is made, it is made for (1)–(3).

What this change must NOT do: alter the language. Same programs accepted, same
programs rejected, same normal forms compared. It is an evaluator refactor whose
observable behavior is intended to be identical. Every place that intention could
fail is catalogued in §6.

## 2. The theory, minimally

Three ingredients replace substitution:

**Values gain a closure form.** Today a λ's value carries a body that has been
substituted into. Under NbE:

```
Val.closure (env : Env) (body : Term)
```

The body is stored *as written*; `env` is the comptime environment at the point the
λ was evaluated. Application does not substitute:

```
apply (closure env body) arg  =  eval body (env extended with arg)
```

**Unknowns make neutrals.** When evaluation reaches a variable bound to an unknown
(a σ), or an application whose head is one, it stops and records the stuck
application as a *neutral* value — exactly the stuck spines the checker has today.
Nothing new here; DLLBC already has σ's and stuck spines.

**Equality goes through readback.** Two closures cannot be compared structurally
(their environments differ even when they mean the same function). To compare
functions: apply both to a *fresh* σ, evaluate, and compare the results; recursively,
this "reads back" any value into a canonical first-order form, at which point the
current rule — α-equality is literal structural equality — is preserved. Function
equality is rarely asked directly (an `Id` at function type) but is on the path of
nearly every type comparison: the type vocabulary (`Le`, `count`, `Sorted`) is made
of recursor applications whose arguments are λs, so comparing two stuck types means
comparing the λs embedded in their spines. Note the checker *already does the first
half of this*: checking a λ against a Π opens the binder with a fresh σ today.

Fuel: normalization remains fuel-bounded (type-in-type still admits non-termination;
Girard does not care how we evaluate). The fuel moves from the substitution loop to
the eval loop. Nothing improves or worsens here.

## 3. The capture machinery

### 3.1 What is recorded

A closure records `(env, body)`. Two design options for `env`:

- **(a) Capture the whole environment in scope.** O(1) capture (the env is a
  persistent list; capture is a pointer). Simple, standard. Cost: the closure
  retains references to every binding in scope, including ones the body never
  mentions — invisible retention, and "what does this closure depend on" is not
  answerable by looking at the value.
- **(b) Capture only the body's free variables.** Precise and self-describing;
  costs a traversal per λ-evaluation, and the FV computation is one more thing to
  get right.

For the pure fragment the two are *semantically identical* (immutable environments;
retention is unobservable). **Resolved (2026-08-07): (a), full-environment
capture.** Revisit only if runtime capture becomes real, at which point (b)'s
precision is likely load-bearing rather than cosmetic.

### 3.2 Which variables are captured, and the invariant that guards it

Everything the closure's env contains is, by construction, a *comptime* binding:
pure values, σ's, other closures. The language's existing rule — "a mathematical λ
closes over copyable knowledge; an imperative function closes over **nothing**" —
today holds by construction, because the comptime environment simply contains no
state. Under NbE this must be promoted from accident to **asserted invariant**:

> A captured environment contains knowledge only — no hole (⊥), no loan marker, no
> borrow value, no runtime slot reference.

This is the knowledge/state invariant (the one refinement already enforces at its
substitution site) surfacing at a second site: **capture is the act of turning
environment entries into parts of a value**, exactly what refinement's marker-free
condition exists to police. It should be asserted at closure formation the same way
`refineSym` asserts it at substitution, and the whole-corpus instrumentation trick
that validated the first site applies verbatim to this one.

### 3.3 Could this machinery later capture runtime variables/borrows?

Representationally: trivially yes — an env slot can hold any `Val`, including a
borrow. That is precisely why the question needs a fence now.

The hard part was never representation. Substitution genuinely *couldn't* express
captured borrows (there is no place in a copied term for a loan to live), so the old
evaluator enforced "no capture" for free. A closure CAN hold a borrow, so under NbE
"no capture" becomes a rule someone maintains rather than a structural impossibility.
What crossing the bridge would actually require, listed so nobody mistakes the door
being *representable* for the door being *open*:

- A closure holding a borrow becomes a **resource**: non-copyable, affine, with
  ownership semantics on the closure value itself (apply-once? re-lend per call?).
  This is Rust's `Fn`/`FnMut`/`FnOnce` trichotomy arriving in value form.
- Loan bookkeeping searches Ω positions for markers. A borrow inside a captured env
  is a loan half living *inside a value's environment* — every marker search,
  End-Mut plug-back, and audit traversal would need to see through env indirection.
  Today "state lives in Ω" is a locality guarantee; captured borrows end it.
- The audit would need to judge function values that *owe* things.

Draft position: NbE is the right substrate if the language ever wants closures over
runtime state (the door exists), and the assertion of 3.2 is the lock on that door
until an ownership design for closure-resources is written.

## 4. Contracts: store-now, consult-later (resolved to pin/capture)

The checker stores three kinds of contract and consults them later: telescope types
(consulted at every use), borrow obligations, and the pinned return type (both
consulted at the audit). The design question was: when a stored contract is
consulted, *which environment does it see?*

### 4.1 "Up to date" is a phantom requirement

The instinct "the contract must see the live environment" is wrong, and the
design's own invariant says so: *no mutation can make a type stale; snapshots are
copies*. Stored contracts are **supposed to be pinned** to their moment. What looks
like liveness is exactly two sanctioned late-binding events:

1. **Call-site instantiation** — `Fin (len *b)` at a call means the `b` just
   passed. The type is evaluated *at the call event*, in an environment mapping
   parameters to actuals. Not staleness: a fresh evaluation with fresh data.
2. **Exit snapshots at the audit** — a bare `*v` in a return type means the
   collapsed final payload. One deliberate late binding (the `σ_exit` mechanism).

Everything else means *entry* values, forever. This is why the corpus threads
length equations through mutations: a stored `Le (len *v) fuel` does *not* track
the mutated list, by design.

### 4.2 How today's pin works (the mechanism being generalized)

The seal check, in arrows — `Ω ⊢ (λx:τ. M) : (Πx:τ. N)` under ⇒:

```
seed:    Ω₀ = x ↦ borrowₘ ℓ σ₀          σ₀ : τ̂ minted into Γσ
         O += (x, ℓ, Ŝ[s := σ₀])        -- obligation: owed type, ~> binder PINNED
                                        -- at the entry snapshot by substitution
pin:     Ω₀ ⊢ markExit(N) ⇝ N̂          -- return type evaluated ONCE, at entry:
                                        --   old *v → (old stripped) → resolves NOW → σ₀
                                        --   bare *v → rewritten to placeholder σ_exit
body:    Ω₀ ⊢ M ⇒ v ⊣ Ω₁               -- per path; ⇜ refinements sweep N̂ too
audit:   Ω₁ ⟿* collapse x's payload ⇓ p
         N̂[σ_exit := p]                 -- σ_exit is DEFINED, not looked up
         ⊢ v : N̂                        -- value typing + conversion
```

Key observations. The contract is turned into a *value* at entry, embedding σ₀;
after that moment it contains no variable references, so nothing later can shadow
anything in it. Values are immutable trees, so no write can touch the embedded σ₀
("mutation mints new values, never rewrites old ones"). The exit reading *cannot*
be a live read of N (N was consumed at entry) and *cannot* be a re-evaluation at
the audit (consumed parameters are ⊥ by then): it is a **defined placeholder** —
assignment to a promise, the one sanctioned exception to "no substitution carries a
mutation's result". And the audit finds the borrow by loan id ℓ, never by variable
name. Three shadow-immunity mechanisms, stacked: eager evaluation, the σ namespace
(program binders cannot shadow a σ), find-by-ℓ.

(Spelling sidenote, recorded not proposed: today `old` is a *marker* on a deref
position, stripped before the kernel — surface `old *v`. The compositional
spelling `*(old v)`, with `old` an operator on borrows, is the one that would
generalize if `old` ever extends to consumed binders, per the pain diary.)

### 4.3 The two options, and the resolution

**Option A — contracts are closures** (pin by capture). No judgment ever holds two
environments; stored contracts carry their own, comparisons happen on values:

```
SEED-PURE     ρ ⊢ τ ⇓ T      σ fresh,  Γσ += σ:T        continue under ρ[x ↦ σ]

SEED-BORROW   ρ ⊢ τ ⇓ T      σ, ℓ fresh
              O += (x, ℓ, clo(ρ[s ↦ σ], S))     ← ~> pinned by CAPTURE, no substitution
              Ω[x ↦ borrowₘ ℓ σ]

PIN           R := clo(ρ_entry, λ exit₁ … exitₙ. T′)    -- T′ = T with each bare *vᵢ ↦ exitᵢ;
                                                        -- one parameter per borrow param

CALL-INST     ρ_call = actuals θ (+ caller env)
              ρ_call ⊢ τ_param ⇓ T      ⊢ v_arg : T      ← late-binding event 1

AUDIT         collapse vᵢ's payload ⇓ pᵢ
              ρ_entry[exitᵢ ↦ pᵢ] ⊢ T′ ⇓ T_val          ← late binding IS application (event 2)
              obligation closure:  ρ' ⊢ S ⇓ S_val    ⊢ payload : S_val
              ⊢ result : T_val
```

Note what happened to the "σ_exit promise" of the original draft: **it dissolved
into function application.** The pinned return type is a closure awaiting one
argument per borrow parameter; the audit applies it to the collapsed payloads. No
side table, no special substitution, no new theoretical object.

**Option B — contracts are terms, re-evaluated at consultation.** The term's
references must resolve correctly against an environment that has moved on — this
is where globally-unique variables become necessary. But re-evaluation gives the
*wrong answer by default*: at audit time, consumed parameters are ⊥ and payloads
are mutated — the entry values the contract means are gone from the environment.
So B must *rebuild* pinning (substitution at seed, or entry-σ's reachable through
unique names) — which is today's system rearranged, plus a uniqueness obligation.
The shadowing-capture hazard (`fn f (v : &mut …) -> … (*v) … { let v = Nil; … }`
— the audit's `*v` finds the local) is a hazard of **B only**; today's pin and
option A are immune, per 4.2.

| | A (closures) | B (re-evaluate) |
|---|---|---|
| pinning (the actual spec) | structural, free | must be rebuilt |
| unique variables needed | no | **yes** |
| the two live events | evaluated at the event | same |
| refinement sweep | must reach captured envs | as today |
| contracts printable/comparable | via readback only | directly |

**Resolved (2026-08-07): Option A** — pin/capture-style contracts. It is today's
semantics with the mechanism generalized (evaluate-now-and-embed becomes
capture-now-evaluate-at-need), needs no uniqueness discipline anywhere, and keeps
the anti-staleness invariant structural. B's residual virtue (first-order,
printable contracts) is a convenience; readback exists anyway.

## 5. Variable representation (resolved: source names in the comptime fragment)

NbE removes both compensations that motivated the current representations:

- **Indices** compensated for substitution: transplanting a body into a new
  context risks name capture, so names became arithmetic. NbE never transplants a
  body — evaluation carries an environment *to* it. No transplant, no capture, no
  indices. Lexical scoping is structural: each binder extends its closure's env,
  and lookup-nearest-binding is the scope rule. `λ x. λ x. x` just works;
  shadowing is the mechanism, not a hazard.
- **Unique ids** compensated for the *flat* runtime store (frame windows,
  re-consultation stability). The comptime fragment under NbE has no flat store,
  and §4's resolution removes re-consultation. Globally-unique *strings* would be
  today's ids in costume — pointless (agreed 2026-08-07).

So: **plain source names, with shadowing, in the comptime fragment.** Readback
mints fresh names in a reserved namespace (unparseable as source identifiers) so
generated names cannot collide with written ones.

The **runtime** store keeps `Var` ids and the flat arena for now (see §0 scope):
loans end on *demand*, not on scope exit, so the arena's never-pop discipline is
the cheap way to guarantee nothing dangles; §7 records the deferred alternative.

Residue to inventory during implementation: any remaining *term-level* structural
comparison becomes α-sensitive (small post-M28 — the big offenders are deleted);
KernelFloor's hand-built de Bruijn terms get rewritten (a benefit: that is where
the dangling-index bug lived).

## 6. Where the "identical behavior" intention could fail (attack surface)

1. **Values stop being pure trees.** A closure introduces sharing (envs referenced
   by values). In the immutable pure fragment sharing is unobservable — but every
   function that *traverses* values must decide what to do at a closure:
   `hasStateMarker`, `firstLoanMarker`, the ownership-node searches, any residual
   `Val` equality. Policy needed per traversal: descend into envs (3.2 says there
   is nothing to find — assert it), or refuse. An unexamined traversal is a silent
   wrong answer.
2. **Refinement's reach widens.** ⇜ substitutes a σ's solution into every
   σ-bearing component of checker state. σ's now also live inside captured envs,
   so the sweep must map through closure environments. Mechanical, but it must be
   written, and the "zero violations" instrumentation should be re-run after.
3. **Readback must reproduce today's equalities exactly.** The no-η rule, stuck-
   spine identity, `Refl`'s conversion side-condition — all must survive the
   change of equality procedure. KernelFloor is the control group; if it moves,
   the refactor is wrong.
4. ~~The σ_exit "promise"~~ **Resolved (2026-08-07): the promise dissolves into
   application** (§4.3). The pinned return type is a closure awaiting one argument
   per borrow parameter, applied at the audit. The anti-prophecy positioning
   becomes *structural*: before the audit there is no name in any scope for the
   exit value, so nothing can reason about it early — whereas prophecy variables
   exist precisely to be reasoned about early. **Recorded suspicion (user): this
   resolution is suspiciously clean — how does one-parameter-per-borrow-param hold
   up when borrows have differing lifetimes, or are themselves returned?** The
   current boundary that contains the suspicion: borrow-carrying return types are
   never pinned today (they are audited structurally, per issued borrow), so the
   closure-application form covers exactly the value-returning paths. If borrow
   returns ever acquire pinned/postcondition semantics, the parameterization must
   be revisited — that is the named revisit trigger.
5. **Golden traces and the differential.** Checking-mode expected environments
   compare literal contents; if closures appear in any compared position,
   comparisons change meaning. Inventory before, not after.
6. **The exempt raw suite keeps its role.** KernelFloor polices the refactor; its
   rewrite to named form must be verdict-preserving.

## 7. Deferred: runtime names via frame pop-with-drop

*Status: would be nice if it turns out easy; NOT on the current hot path. Natural
adoption point: when compilation work begins, where a stack-and-drop machine is
inevitable anyway.*

The end-state "source names everywhere" needs the runtime side too, and a flat
name-keyed Ω breaks on return (the callee's stale `x` shadows the caller's
forever). The fix is frames with pop-with-drop: on return, deallocate the frame's
cells Rust-style, the drop machinery ending any loans inside.

Soundness is NOT the obstacle — the audit is the proof: an audit-passing function
guarantees at return that caller-reachable data is marker-free (the obligation
check) and no borrow of a local escaped (boundary rejection), so a frame at pop
holds only ⊥'s, plain values, and loan chains endable by the existing drop rules.
Eager ending is admitted by the nondeterministic rule presentation (laziness is a
scheduling, not semantics). The audit already forces the *inward* half (markers in
caller trees collapsed at return); pop-with-drop's increment is ending the frame's
*outward*-held borrows.

What it buys: runtime source names (completing the one-representation end-state);
concrete loan-ending moves toward the checker's atomic-at-boundary semantics
(shrinking the documented simulation-relation divergence); fidelity to compiled
code; bounded Ω. What it costs: frame bookkeeping and a drop sweep on every
return (the arena costs zero); a clean drop-stuckness error story for *unchecked*
programs in the executing machine (a claim over the differential generator's whole
grammar — to be tested, not asserted); golden-trace churn (eager ending is
observable). The honest framing: pop-with-drop is purchased *by* the names goal
plus the metatheory alignment — it is not a free win, and the arena remains
simpler for the current interpreter workload.

## 8. What actually gets deleted, and what appears

Deleted: `substPure`, `shiftPure`, the delayed-lift machinery, every
"substitute then normalize" site in the evaluator, and the `Ŝ[s := σ]`
substitution at seeding (§4: obligations become closures). Appears: `Val.closure`,
`eval` (term × env → val), `apply`, `readback`, the capture assertion (3.2), env
plumbing through the ⇝ rules, the σ_exit promise formalization. The refinement
substitution (σ := shape over checker state) is a different mechanism and
**stays** — it substitutes into values by node identity, not under binders, and
has no index arithmetic.

## 9. Open questions

1. ~~Full-env capture (a) vs free-variable capture (b)~~ **Resolved: (a)**;
   revisit only if runtime capture becomes real.
2. ~~Term representation~~ **Resolved: plain source names with shadowing in the
   comptime fragment (§5); runtime keeps `Var` ids until §7 is taken up.**
3. ~~Do owed types become closures?~~ **Resolved: yes (§4.3, SEED-BORROW).**
4. ~~The σ_exit promise~~ **Resolved: dissolved into closure application** (§4.3,
   attack-surface item 4) — with the recorded suspicion and its revisit trigger
   (borrow-returning / differing-lifetime futures) noted there.
5. ~~Traversal policy~~ **Resolved as policy, executed at implementation**:
   closures are knowledge-opaque by default — the §3.2 invariant is asserted at
   formation, state/marker searches do NOT descend into captured envs (justified
   by the assertion, checked by instrumentation), and equality never traverses a
   closure at all (readback only). Every traversal is enumerated against this
   default during implementation; deviations documented per function.
6. ~~Residual structural comparisons~~ **Resolved as method**: grep-and-fix
   inventory during implementation; expected near-zero post-M28 (the α-sensitive
   offenders — FnStmt's literal `==`, AlphaEq — are already deleted).
7. ~~Fuel parity~~ **Resolved as method**: one fuel discipline threaded through
   eval/apply/readback; the suite passing on *unchanged fuel constants* is the
   parity assertion. Any needed bump is a reported finding, never a silent edit.
8. ~~Migration shape~~ **Resolved**: build the new evaluator ALONGSIDE the old on
   the branch; run an old-vs-new differential over the entire corpus (byte-
   identical verdicts and normal forms — the strongest available net, and the
   M28 playbook applied again); delete the old evaluator BEFORE merge so no
   two-evaluator era reaches main. KernelFloor and the existing checker/machine
   differential ride as additional gates.
9. (Deferred with §7) the drop-stuckness claim over the differential generator's
   grammar.

With 1–8 resolved, this document is second-draft-complete on design: what remains
open is one deferred item (9, tied to §7's deferred pop-with-drop) and the two
implementation-time inventories (5, 6), which produce findings rather than await
decisions. The remaining decision is scheduling.

## 10. Relation to open designs and sequencing

- **Task #17 (λ capability/merge):** parked; if NbE lands, the node merge becomes
  trivial (both λs are "stored body + env discipline") and the capability question
  can be reopened against the closure representation, where a "second signature"
  is just "which env discipline the closure was formed under". The related
  borrow-binder-under-⇝ question (`λ (v : &mut List Nat). len *v` as a
  type-usable function) stays parked with it.
- **Task #15 (paper F1/F3/F6, §2 arrow table):** must WAIT for this change —
  those figures describe exactly the machinery this rewrites; re-extracting them
  twice is the known mistake.
- **δ-constants (parked by measurement):** unaffected.
