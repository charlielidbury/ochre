# M31: Functions are comptime — one λ, heads by ⇝, and the death of `rfn`

**Status: UNDER CONSTRUCTION — design under review with the user; committed early so
Stage 0 (independent of every open design question) could be dispatched. Written to
interrogate the idea, not to glaze it.**

## 0. The model in one sentence

**A function is comptime knowledge: every application `F A` fetches its head by ⇝ and
reads its arguments by their binder modes; no runtime-moded binding ever holds a
function.** The body of an imperative function is still entered by ⇒ — checking enters it
once, at its seal, by audit; execution enters it at every call, in a fresh frame. What
changes is the *mode* of a function binding (comptime — ⇝-read, erased, never consumed —
rather than runtime) and how a callee is *reached* (evaluated as knowledge, not located
as state).

**Terminology.** Ω is the machine's ONE store
(`St.env`), holding both runtime and comptime bindings, differentiated by the binder's
capitalisation — there is no second persistent store, and M31 does not introduce one.
The other environment in the system is **ρ** (`PEnv`, nbe.md's symbol): the transient
evaluation environment the normalizer threads through a single ⇝ evaluation, binding
pure λ/Π binders during β; it exists only for the duration of that evaluation. "Functions
move to comptime" therefore means: function bindings in Ω become comptime-*moded*, not
that they move to a different place.

This is the same push that motivated M30 (nbe.md): bring runtime and comptime semantics in
line for λ. M30 built the substrate — environments, closures, canonical readback — and
deliberately stopped at the boundary (#19(a): closures never leave `Pure.lean`). M31 is
the semantic half: function bindings become comptime-moded, and the values that stand
for functions take the one closure form under one capture rule — knowledge only — with
the confinement boundary restated so it holds without exemption (§2.4).

## 1. What today's system does, for contrast

  * Function bindings are **runtime slots** in Ω: a σ (checking) or a `Val.rfn`
    (executing). `fn` desugars to a runtime `let`.
  * A callee is **located**, not evaluated: `callV` reads a slot by id
    (`Machine.lean:3299`), with a fence refusing ⇒-calls of capital function binders
    (`3306`), a refusal of reading a function out of its slot (`3116–3124`,
    "reached by NAME"), and a `.app` router that picks the applying arrow by inspecting
    the head's *value* (`3412`).
  * Two λ term formers (`.lam` unary/String-bound/pure, `.lamR` n-ary/id-bound/
    imperative), two λ value species (`closure` in Pure.lean, `rfn` in Machine), and a
    seal that dispatches on the sealed **term's shape** (`3270`).
  * Consequences the user has already flagged as debt: `let F = main` is refused by two
    independent mechanisms; "pass a function as an argument" is promised by an error
    message and refused by the code; `G a` is legal in a spec and an error at runtime.

## 2. Target semantics

### 2.1 Binding

**Function names are capitalised, because functions are comptime.** §6's convention —
capital = comptime — stays exactly one rule with no carve-outs: a function is comptime
knowledge, so a binding that holds one must be a capital binding. `fn Quicksort …`
desugars, as today, to a `let` of a λ ascribed its Π, comptime-moded in Ω: ⇝-readable,
never ⇒-consumed, erased. `let Double = λ (n : Nat). add n n` likewise. `let F = Main`
is a ⇝ copy of knowledge: legal, erased, never consumed.

Enforcement is two-sided. The surface refuses a lowercase `fn` name outright. The kernel
backstop is the same rule seen from below — a runtime-moded (lowercase) binding whose
right-hand side produces a function value is refused, with the fix in the message
("functions are comptime; capitalise the binder") — which catches what the surface
cannot see (`let f = add 1`) and is the honest successor of today's function-read
refusal.

This diverges from Rust's snake_case function names deliberately. The divergence tracks
a genuine semantic difference — a Rust function is a runtime item, a DLLBC function is a
comptime value — and the surface should say so rather than hide it.

**Naming style: PascalCase for comptime names, snake_case for runtime names.** The
kernel's mode marker remains the initial letter (what `isUpperInit` reads); PascalCase
vs snake_case is the style convention layered on it, and the one the rename sweep
applies: `SetAt`, `SplitOff`, `QuicksortA`, `Len` for functions and comptime data
(`Hfuel`, `V0`), and `fuel`, `tl`, `hi` for runtime data. A capital-initial name in
snake_case (`Set_at`) is comptime as far as the kernel cares and style-wrong as far as
the corpus cares.

Two consequences. Function-typed *parameters* must be capital too (`Map (G : Π …, v)`),
which under §2.2 is no restriction at all — every function argument is ⇝-read, and
capital is exactly the binder that says so. And the standard vocabulary capitalises with
everything else — `Len`, `Add`, `Count`, `Take` join the already-capital `Le`, `Sorted`
— one rule for every name that denotes a function, library or user's. (Pure λ/Π binders
inside ⇝ terms are untouched: the pure fragment has no mode distinction for the
convention to mark.)

### 2.2 Application: `F A` — head by ⇝, arguments by binder mode

One rule, replacing both the `callV` protocol's location step and the `.app` router:

  1. **Fetch the head by ⇝** — operationally, a `readC` of the head (for a bound name,
     a non-destructive read of its Ω slot). Its value is a closure (body in hand) or a
     neutral/σ (abstract: a sealed function, a spec parameter, `ih`).
  2. **Read the arguments by the binder modes of the head's signature** — unchanged from
     today's `processArgs` discipline: ⇝ for capital binders (non-consuming), loan-seeding
     for `&mut` binders (obligation installed), ⇒ otherwise. Modes must be in hand before
     any argument is read; that ordering constraint survives verbatim.
  3. **Enter or abstract.** Checking mode, abstract head: abstract application at the
     signature (`callDeclC`), result minted from the instantiated codomain — unchanged.
     Executing mode, closure head with imperative body: fresh frame, bind, ⇒-walk, release
     frame loans on exit (today's `applyRFn`, keeping its name or not). Pure body: β in
     the normalizer, as today.

The fence at `3306` is deleted (calling a ⇝-held function is what *every* call now is).
The function-read refusal at `3116` is deleted (Ω holds no functions to mis-read). The
`.app` router is deleted (heads are always ⇝). `G a` means the same thing in a spec and
in a body.

**Saturation survives as a rule about imperative entry, not about syntax** (§12 decision
4): an application whose head has an imperative body must saturate its telescope before
the body is entered; a partial application of an imperative function is a closure holding
arguments — potentially borrows — and is refused with today's message. Partial application
of pure functions (`add 1`) is unchanged and unremarkable.

### 2.3 The seal: one feature, two check engines, honest dispatch

`(t : T)` remains check-then-forget with the shared forget half (`sealMint`). The check
half keeps its two engines — conversion when `t` evaluates to a value, audit
(`checkRFnBody`) when `t` is an imperative body — but the dispatch changes from *term
species* (`.lamR`?) to *body classification*: a λ whose body contains an effectful former
(assign, borrow, `matchE`, an application entering an imperative body) is checked by
audit; anything else by conversion. `sealFn` stops being λ-species vocabulary and becomes
"the audit half of ascription", which `fn` reaches because a definition *is* an
ascription.

### 2.4 One λ, one capture rule

One term former. One value form: **closure = (environment, body)**. And one capture rule
for both fragments, which is nbe.md §3's invariant promoted to the whole language:
**a captured environment contains knowledge only — no ⊥, no loan marker, no borrow
value.** A λ — any λ — may close over the comptime surroundings it was born in: comptime
`let`s, proofs, types, and *other functions*, which are now comptime bindings
themselves. What no λ may capture is runtime state: a lowercase local, a borrow, a hole.

Stated in surface vocabulary: **a λ body may reference its own binders and the
PascalCase bindings in scope — nothing more, nothing less — and this holds for every λ,
pure or imperative, with no clarifications.** A snake_case citation inside any λ body is
refused at formation; the fix is always the same — make it a parameter, or name the
snapshot first (`let V0 = *v`, `let L = len l`) and reference the name. The formation
check is therefore *identical* for both λ species: the node's free runtime variables
must be empty. Nothing expressible is lost: for PascalCase bindings, capture and eager
inlining are indistinguishable (comptime bindings are immutable), so the explicit form
denotes the same stored value the implicit snapshot would have — the knowledge machinery
(refinement, comparison) is untouched; the freeze just becomes visible as a binding.

Snake_case citation remains legal exactly where there is no formation-vs-use **gap**:
in **type positions** (`Le (S i) (len *v)`, return types with `*v`/`old *v`) — a type is
consumed at its own event (seeding, the pin, an ascription), never stored-then-applied
later — and in **ordinary pure computation at statements** (`let n = len *v`), resolved
on the spot. The λ is the one form that is formed now and used later; the gap is where
an implicit snapshot could hide, and the rule closes it. Corpus cost, enumerable: staged
builders and the congruence λs (`append_back`'s `λ (a : List Nat). Cons (*hd) a`
becomes `let H0 = *hd; … λ a. Cons H0 a`) each gain one naming line.

This dissolves today's closedness check rather than relocating it. `rfn` formation
currently refuses every free variable except the global function slots (`admitGlobals` —
"may name a function to call it, captures nothing"); under M31 the exemption *is* the
rule: functions are comptime, so naming one is comptime capture, and the check becomes
simply "free runtime variables are refused". One rule where there were two
(`admitGlobals`' slot exemption, `mkClosure`'s marker scan), and they were always the
same rule seen from two fragments.

`Val.rfn` and `Term.lamR` are deleted; `applyRFn`'s *rule* (frame-bind-and-walk, now
with the closure's knowledge environment in scope for the body's ⇝-reads) survives as
the entry rule for closures with imperative bodies. An imperative λ with no ascribed Π
has nothing to audit its body against and is refused at binding — the seal is the check
event, exactly as `fn` already forces.

#19(a) is **refined, not repealed**: the measured finding (closures with captured
environments break `==`-keyed abstraction — quicksort's count equation failed while
every differential read zero) becomes "**closures live only where nothing converts**".
Concretely: in ρ, transiently, inside the normalizer (as today); and in
*executing-mode* state, which computes and never compares. Checking-mode Ω keeps its
closure-free discipline without any exemption — a pure value is stored in canonical
readback form (its environment discharged by evaluation, as today), and an imperative
function is stored as its σ (the seal forgets the body, environment and all). So the
identity hazard never arises: function occurrences in specs are name-headed neutrals
(`pvar F` applied), which are `==`-stable; closure values are consulted only at β inside
the normalizer or at frame entry inside execution. Every site that compares function
*values* (a Π-typed `hasType`, `piAgree`) goes through canonical readback, which is what
`convert` already is.

## 3. What dies (the deletion inventory)

  * `Term.lamR`, `Val.rfn`, and every case arm matching them (~40 sites).
  * The `callV` fence (`3306`) and the spec-parameter/callable-parameter distinction
    (`map_spec G` vs `map_apply g`) — every function parameter is now both.
  * The function-read refusal (`3116–3124`) and the "functions are reached by NAME"
    model text — succeeded by §2.1's mode backstop, which states the refusal in mode
    vocabulary and names the fix.
  * The `.app` arrow router (`3412`).
  * The term-shape seal dispatch (`3270`) — replaced by body classification.
  * `retarget`'s *resolution* half: a `fn` name is now an ordinary comptime binding, so
    bare `Main` resolves in the surface and `let F = Main` works. (`retarget`'s
    *permutation* half survives: `[k]` hoisting still reorders call arguments — see E8.)
  * Probably `Term.callV` itself, once calls are ordinary app spines (staged last; the
    node can survive stages A–B as "saturated application" sugar).

## 4. What survives unchanged

  * The audit engine: `checkRFnBody`, telescope seeding, obligations, paths, the exit
    audit. This milestone does not touch the borrow checker's logic.
  * `processArgs`' mode discipline and ordering (modes before arguments).
  * Abstract application at a signature (`callDeclC`), `fsig`, σ minting.
  * The recursor elaboration (`fn [k]` → motive + arms + `ih`) — `ih` becomes a comptime
    binding holding a neutral, which is what it always morally was.
  * NbE, canonical readback, the capture guard (knowledge only), no-η.
  * The executing machine's frame/loan discipline.

## 5. Migration stages

Each stage ends with the corpus green and a differential at zero (M30's net pattern:
whole-corpus old-vs-new with a positive control; execution goldens unchanged on
`Traces`).

**Stage 0 — pop-with-drop (independent; can land before everything else).** Ω entries
pop with their lexical scope, ending any loans inside the dropped values (a Rust-style
drop; ending a loan early is sound — the demand machinery already ends loans lazily, so
eager ending only moves the same events earlier). This depends on nothing in M31 and is
expressible entirely on today's id-keyed codebase; E2's newest-wins Ω depends on *it*,
which is why it goes first. Half of it already exists: `releaseFrameLoans` runs at
executing-frame exit, `endScope` at program end — the work extends the same discipline
to sub-frame scopes (match arms, if branches) and to checking mode. The mechanics are a
watermark: `bindSlot` appends and `setSlot` updates in place, so a scope's entries are
exactly the suffix past the Ω-length recorded at entry — no new bookkeeping structure.
Decisions inside the package: drop order (reverse binding order, Rust-style), and the
one semantic edge — a borrow of a scope-local escaping the scope, which is the same
question frame exit answers today, now asked at arm granularity. Its differential
accepts only loan-end *timing* shifts (audits firing earlier, messages moving); zero
acceptance flips expected, and any found are surfaced, not absorbed. Standalone value
even if M31 stalls: deterministic cleanup, nbe.md §7's deferred item closed.

**Stage A — function bindings become comptime-moded (semantics, on today's
representations).** `fn` bindings and λ-valued `let`s stay in Ω but flip mode (value:
today's σ / `rfn` unchanged); call heads fetch by ⇝ (`readC` on the slot); fence and
function-read refusal deleted (backstop installed); `.app` router deleted. **The corpus
rename lands first, as its own mechanical commit** — every `fn` name and stdlib function
name capitalises (§2.1) — so the semantic differential is not buried inside a rename
diff. The remaining *behaviour* deltas are enumerable in advance: `let F = Main` flips
to accepted; spec-vs-call twin tests collapse; lowercase-function-binding tests flip to
the backstop message; everything else must differential to zero. **This stage is the model; it is also the riskiest, so
it goes first** (hardest-first: if functions-in-comptime-scope walls somewhere — E2's id
windows, E7's executing-mode env — we find out before spending on representation work).

**Stage B — one λ.** Merge `.lamR` into the λ former (comma-list as sugar for the
telescope; binder representation per E3); `rfn` becomes a closure under the
knowledge-only capture rule (body payload per E4); `applyRFn` re-keyed, with the
closure's environment in scope for the body's ⇝-reads. Semantics-neutral by construction —
differential must be *exactly* zero, no enumerated flips.

**Stage C — the seal made honest + deletions sweep.** Body-classification dispatch;
`sealFn` renamed/absorbed; `callV` → app spines if E8 resolves cleanly; delete the
inventory in §3; PROGRESS/DECISION-LOG; paper and language.md currency (chapter 12's
deviations block shrinks by one bullet — the call-position containment dies; the
`f(a, b)` spelling remains a surface question, out of scope here).

Stage A before B is a deliberate inversion of "representation first": A is where the
unknowns are, B is mechanical given A, and A's differential is enumerable while B's is
zero. If A walls, nothing was spent on B.

## 6. Sharp edges (the interrogation)

**E1 — mode stays name-directed, enforced both ways.** With capitalised function names
(§2.1) the convention needs no value-directed carve-out: capital = comptime, one rule.
Interrogate the backstop's coverage: a capital binding holding data is legal today and
stays legal (capitals mark all comptime knowledge, not just functions), so the residual
hazard is only a lowercase binding *acquiring* a function value through a path the
kernel misses — every ⇒-read that can produce a closure or a function-σ must end at the
backstop (binding, constructor field, call result, match arm). Enumerate those sites in
Stage A and point the old function-read-refusal tests at the new message. Risk: LOW.

**E2 — binder keying for imperative bodies.** Today imperative bodies reference
parameters as id-keyed `.var`s and Ω frames are id-windows. One λ wants one binder
story. Options: (i) **name-keyed Ω with duplicates, newest entry wins** — recursion's
two-live-frames problem is solved by shadowing, and the capture rule is what makes that
sound: a body may name only its own binders, so newest-wins can never resolve a lookup
to the wrong frame, and everything that genuinely crosses frames (loans, borrows,
obligations, the audit) is ℓ-keyed and shadow-immune by design. Checking mode never has
two live frames at all (calls are abstract; sealed bodies check in fresh Ω), so this is
an executing-machine change. Payoff: retires id minting, frame windows
(`nextFrame + 128`), `shiftVars`/`shiftBindersK`, `progBase` arithmetic, and the
id-range canonicalization filter. **Cost: pop-with-drop becomes mandatory** — under
newest-wins, a stale entry from an ended scope (a match arm's binder, a shadowing `let`)
would wrongly shadow later lookups, so Ω entries must pop with their lexical scope
(nbe.md §7's deferred nice-to-have, promoted to load-bearing and carved out as Stage 0;
brings deterministic loan-ending at scope exit with it). (ii) Fallback: merged λ binds `Var` (id+name), pure
use keys the name, runtime use keys the id — smallest change, keeps the id machinery.
Recommendation: probe (i) first — it is the larger simplification and its preconditions
are all invariants M31 already establishes; fall back to (ii) only if the probe walls on
pop-with-drop. Risk: MEDIUM — this is where Stage B's mechanical-ness lives or dies; the
viability probe (an agent building the merged former + newest-wins Ω against
`checkRFnBody` and the executing differential only) precedes full dispatch.

**E3 — closure body payload.** Pure bodies live in `Val` (the mixed domain embeds pure
syntax); imperative bodies are `Term` (no `Val` embedding for assign/letIn/matchE — and
`rfn` is already the `(∅, Term)` closure in disguise). Options: (i) body := `Val ⊕
Term`; (ii) closures hold `Term` uniformly (textbook NbE: `eval : Env → Term → Val`);
(iii) grow `Val` to embed all of `Term` and **merge the two trees**.

The deciding fact is that the checker structurally TRAVERSES pure λ bodies in place —
`substSym` (σ refinement), `abstractInto` (§19 branch equations; it even sweeps closure
environments), `markExit` (the pin machinery), the loan-marker search, and σ-renumbering
all descend `.lam`/`.pi`/`.sigmaT` bodies as `Val` syntax — while every one of them
treats `rfn` as a LEAF, justified each time by closedness ("no σ inside", "no loans to
find"): the capture rule is what licenses the opacity. So (ii) is not wrong, but it is
priced: stored λ values would carry `Term` bodies inside `Val` state, and each traversal
must either grow a Term twin (a duplicate traversal layer over a second tree — the kind
of duplication this milestone exists to kill) or pay eval/readback at every boundary.
It re-litigates M30's central representation choice (the mixed domain is why 18
substitution sites became 18 one-word edits) at rewrite cost, for payload uniformity.

Recommendation: (i), and not as scaffolding — the `Val ⊕ Term` split materializes the
same semantic line the seal's two check engines draw (§2.3) and the capture/snapshot
distinction draws (§2.4): a pure body is *conversed with* structurally; an imperative
body is *entered* and never traversed. One line, three independent appearances;
representing it as data is principled. (iii) stays the horizon where the question
dissolves by construction; its stated cost is that the union tree admits machine-value
forms (`loanM`, `sym`, `⊥`) everywhere syntax goes — type-enforced invariants become
discipline — and touches every match in `Machine.lean`. Out of M31's scope, direction
left open.

**E4 — borrow-moded λ as a ⇝ value.** A function binding borrows now *exists* as
comptime knowledge (an inert closure: never β-reduced under ⇝, entered only via ⇒).
This is #17's parked question, answered by inertness instead of a second signature.
Interrogate where a *type* could be demanded of it: `hasType v (Π &mut …)` — today a
borrow-moded Π has no `Val` type (M26-C), σ's live in `fsig` alone. The inert closure
inherits the same status: callable, passable, not conversion-typeable; argument-position
checks against borrow-moded Π domains go by `piAgree`-style telescope agreement, not
`hasType`. Risk: MEDIUM — enumerate every `hasType` call site whose expected type could
be borrow-moded and confirm each either cannot arise or has the agreement path.

**E5 — `G a` stuck in a body, then what?** Checking mode, abstract head, *statement*
position: abstract application already answers it. But a stuck application in an
*expression* the ⇒ walk must store — `let x = G a` where `G` is abstract with a pure
signature — produces a neutral in Ω. Neutrals in Ω are already legal (σ's are). Confirm
the differential treats `x`'s subsequent reads as today's σ-reads. Risk: LOW.

**E6 — nullary functions.** `fn main()` exists today (`λR []` under a seal); bare
nullary λs are refused (thunk/ι ambiguity). Under one λ and app spines, `Main()` is a
zero-argument application — the ambiguity returns. Options: (i) `fn F()` desugars to
`λ (u : Unit)`
with call sites passing `unit` — uniform, slightly dishonest; (ii) keep an explicit
saturated-call node (`callV` survives) so "enter with zero arguments" is a form, not a
spine; (iii) refuse nullary `fn`. Recommendation: (ii) for M31 — `callV` was staged to
die *last* precisely because this is the one thing it still says that a spine cannot.
Revisit (i) when the surface call-syntax question (juxtaposition) is decided. Risk: LOW,
contained.

**E7 — the executing machine and comptime-moded slots.** Functions stay in Ω, which
execution already reads, so there is no store-access question here. What must be
confirmed: executing mode today never ⇝-reads (it computes, it does not
convert), and a call head is now a ⇝ fetch — the executing-mode version of that fetch
must be the plain slot read it already does for `rfn`, not a detour through the
normalizer. Also confirm seal transparency (`3251`) composes with the mode flip. Risk:
LOW.

**E8 — `[k]` hoisting and call-site permutation.** The sealed telescope hoists the
decreasing parameter to the front; call sites written in declaration order are permuted
by `retarget` today. Under comptime resolution the *name* resolves without `retarget` —
but the permutation must still happen somewhere. Options: put it in the `fn` sugar's
application sites (surface concern, as today, minus resolution); or stop hoisting and
make the motive peel at position `k` (kernel concern; touches `sealRec`). Recommendation:
keep the surface permutation for M31; hoist-removal is a separate simplification with its
own risk budget. Risk: LOW if kept, MEDIUM if bundled.

**E9 — what the twins/e2e suite must become.** Enumerable flips: `let F = Main`
accepted; spec/apply twins collapse to one function; fence-rejection tests deleted;
"reached by NAME" rejection tests deleted or re-pointed at whatever Stage A's honest
refusals are (e.g. partial imperative application); snake_case citations inside λ
bodies flip to refusals (§2.4), with the staged builders and congruence λs migrated to
the explicit-snapshot form as part of the same commit. Everything else differentials to
zero. The flip list is written down *before* Stage A lands and checked against, not
discovered after (first-readings-err-dramatic).

## 7. What this closes

  * **#17** — the λ-capability/second-signature question, answered by inertness:
    functions are ⇝ values; a borrow-binding λ is knowledge you can hold and pass but
    only ⇒-enter. No second signature, no capability bit.
  * The `let F = main` playground failure, both layers of it.
  * The spec-parameter vs callable-parameter split, the fence, the function-read
    refusal, the `.app` router, `rfn`, `lamR` — the §3 inventory.
  * The "pass it as an argument" promise: passing a function is a ⇝ argument read,
    which is the name-use the current error message describes and the code refuses.

## 8. Non-goals

  * **Capture of runtime state stays shut.** Knowledge capture is open (§2.4's one
    rule); what no λ may close over is a lowercase local, a borrow, or a hole — the
    Fn/FnMut/FnOnce door (nbe.md §3) stays representable-not-open.
  * **Surface call syntax** (juxtaposition vs `f(a, b)`) — orthogonal, already tracked
    in language.md chapter 12's deviations block.
  * **Term/Val unification** (E3 option iii) — named as horizon, not attempted.
  * **Consistency/soundness proofs** — unchanged scope; the checker remains the claim.
