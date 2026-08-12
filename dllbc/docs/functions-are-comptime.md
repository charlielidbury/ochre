# Functions are comptime. M31: heads by ⇝ (semantics). M32: suspensions, one λ, the death of `rfn` (representation)

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

`Val.rfn` and `Term.lamR` are deleted (in M32, with the representation — see §5 Stage
B's extraction); `applyRFn`'s *rule* (frame-bind-and-walk, now
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

> **Implementation addendum (Stage 0, landed on `m31-stage0-popdrop`).** Five things
> the plan above could not have known, recorded where the plan is. Nothing here
> qualifies §2.4's capture rule or E3's recommendation; item 5 is a data point *for*
> the latter, produced by building the former's neighbour.
>
> **1. `pushContinuations` had already answered the arm-scope question, wrongly.** A
> statement-position match is fused with the continuation that followed it — the
> continuation is *duplicated into every arm* so the driver can fork paths — which
> puts it lexically inside the arm and silently extends the arm binders' scope over
> it. "The end of the arm's body" is therefore not a point the normalized term still
> has, and a pop at the `.matchE` node would take the entire tail of the program with
> it. The fix is to make the fusion say where the seam was: `pushContinuations` now
> emits a seam marker there (two, differing by whether the splice binds the arm's
> value — `let y = match x { … }` binds `y` after the arm's own entries and `y`
> belongs to the *enclosing* scope), and wraps the fused arm body so the arm's scope
> knows it owns a seam. That last tag is load-bearing: an arm whose body ends in a
> TAIL-position match has two scopes open at the seam and the seam must take both,
> and nothing in a stack of watermarks can tell which arm a seam belongs to —
> that is a fact about the term.
>
> **2. The rule that fell out, which Stage A/B should hold onto.** *A scope pops when
> control leaves it into an enclosing scope; the outermost one does not.* A
> tail-position arm has no seam and closes with the body containing it; a program's
> own scope never closes, and `endScope` is exactly that case — the drop half without
> the pop. Two harnesses were normalizing differently and now do not: the executing
> machine walked function bodies raw, and agreed with the checking side about arm
> scope only by accident (fusion extended the scope on one side, a leak extended it on
> the other).
>
> **3. The escaping-borrow edge, decided as frame exit already decides it.** Frame
> exit's answer was: skip the loans the result carries out, and the slot holding the
> matching marker survives because the arena never popped anything. Stated rather than
> inherited, that is: **an entry still carrying an ownership node after the drop sweep
> is RETAINED** — a scope-local whose borrow escaped keeps its storage, because that
> storage is where the escaping borrow's payload returns to. This was measured, not
> reasoned: with retention disabled the program still runs *and still checks*, and
> leaves a borrow with no owner anywhere in Ω, `endScope` finding no marker to end. The
> failure mode is a silently dangling borrow, not a stuck `endLoan`. Note also that
> the checker ACCEPTS an arm-local escaping its arm — the audit's boundary rejection
> is about escaping a *function* — so this path is reachable in checked code, not only
> in the differential's unchecked grammar.
>
> **4. What E2 actually gets.** The newest-wins hazard is not the shadowing `let` (two
> lets in one scope are both live, and newest-wins is simply correct) — it is the
> *ended* scope. Two of those exist. A recursive call's second frame must not shadow
> the first after it returns, which is what the frame pop buys and is the load-bearing
> half. And a match arm's binder must not shadow an outer binding of the same name
> after the match (`let h = 5; match x { Cons(h,t) => … }; let y = h` resolves to the
> arm's `h` under name-keying, to the outer one under ids), which is what the seam
> buys. Both are now in place, so E2's precondition is met. The residue Stage B should
> expect: `keep` sets are computed from the escaping value's loans at every pop, and
> the frame's id window (`nextFrame + 128`) is now doing nothing that the watermark
> does not — the `id < 10000` filter every Ω-reading harness carried has already been
> deleted as a consequence. §2.4's strengthening retires the other half of that
> machinery on the same argument: `applyRFn`'s `keep` set is `Term.freeRVars`, the
> globals carried unshifted through `shiftVarsK`, and "the node's free runtime
> variables must be empty" makes that set empty by construction rather than by
> `admitGlobals`' exemption.
>
> **5. E3's traversal argument gained a case, and Stage 0 is a (small) vote for (i).**
> The drop sweep needed a finder E3's enumerated set did not contain —
> `firstHeldBorrow`, "the outermost `borrowM ℓ _` this value HOLDS, skipping `keep`",
> deliberately *not* reaching for the loan markers it carries (their borrows are held
> elsewhere and end on their own owner's drop). Like every traversal on E3's list it is
> opaque at `rfn` and `closure`, licensed by exactly the fact E3 names — the capture
> rule, which is why `Val.loanIds` can say `.rfn _ _ => []  -- closed: no loans to
> find` and mean it. The vote: a `Term`-bodied closure (option ii) would have required
> a Term twin of this finder too, and it was written after M30, i.e. the enumerated set
> is still growing. That is the duplication cost E3 prices, observed once more rather
> than predicted.

**Stage A — function bindings become comptime-moded (semantics, on today's
representations).** `fn` bindings and λ-valued `let`s stay in Ω but flip mode (value:
today's σ / `rfn` unchanged); call heads fetch by ⇝ (`readC` on the slot); fence and
function-read refusal deleted (backstop installed); `.app` router deleted. **Ordering: tolerate → rename → enforce** — the rename cannot
land first as once planned, because capital fn names hit the callV fence under the
unmodified kernel; so commit 1 deletes the fence and tolerates both name-cases, commit
2 is the mechanical rename (every `fn` name and stdlib function name capitalises,
§2.1, zero behaviour delta), commit 3 installs the backstop and removes the tolerance.
The semantic differential still is not buried inside the rename diff — the semantic
commits and the rename commit stay separate. The remaining *behaviour* deltas are enumerable in advance: `let F = Main` flips
to accepted; spec-vs-call twin tests collapse; lowercase-function-binding tests flip to
the backstop message; everything else must differential to zero. **This stage is the model; it is also the riskiest, so
it goes first** (hardest-first: if functions-in-comptime-scope walls somewhere — E2's id
windows, E7's executing-mode env — we find out before spending on representation work).

> **Implementation addendum (Stage A, landed on `m31-stage-a`).** Four commits,
> whole corpus green at each. Recorded where the plan is, in the order the plan
> would be read.
>
> **0. THE ORDER ABOVE IS WRONG, and the corrected one is tolerate → rename →
> enforce.** "The corpus rename lands first, as its own mechanical commit" cannot
> be taken: under the pre-Stage-A kernel, capitalising a `fn` name makes its slot
> a comptime binder, and three rules then refuse it before any call happens — the
> `.letIn` row ⇝-reads a comptime binder's right-hand side and `readC` refuses the
> `.seal` by name, the `callV` fence refuses a capital callee, and the `.app`
> router excludes a capital head before looking anything up. A rename-first commit
> is therefore not "zero behaviour delta"; it is a commit in which every renamed
> function is unusable. The rename can only be green once the kernel tolerates both
> cases. The motive behind the plan's order survives intact — the semantic
> differential is still not buried in a rename diff, it is simply in the commit
> *before* it.
>
> **1. The rule the plan does not state, and Stage A needs first: the seal's arrow
> belongs to the seal.** §2.1 says `fn F …` desugars "as today, to a `let` of a λ
> ascribed its Π, comptime-moded in Ω". Those two halves conflict under the
> existing kernel, because a comptime `let` ⇝-reads its right-hand side and the
> seal is the one form ⇝ refuses *by name* ("minting a fresh σ needs an event and
> ⇝ has none"). The resolution is that the arrow is a property of the RIGHT-HAND
> SIDE: a formation EVENT stays ⇒ whatever the binder's case, and what the capital
> binder changes is the BINDING — erased, ⇝-readable, never ⇒-consumed — not the
> event that produced its value. `Var.comptimeRhs` is that rule, and enforcement
> showed it has two cases, not one: a bare runtime λ is a formation event too
> (`admitGlobals` checks its closedness there), and §2.1's own `let Double = λ …`
> requires it be writable.
>
> Its first consequence is a flip the plan does not list: `let C = (le_refl 3 : Le
> 3 3)` becomes legal. The old refusal said "sealed" and "comptime-bound" are
> mutually exclusive; a function declaration is *precisely* a comptime `let` of a
> sealed λ, so keeping it would refuse every declaration in the language. The `Qed`
> binding and the function declaration are one form.
>
> **2. §2.2's step 3 is not the same claim as "the `.app` router is deleted", and
> the difference is a decision.** What was deleted is the router's MODE
> pre-filter — the capital-head exclusion, which was the fence's shadow and would
> otherwise have filtered out every function there is. What was KEPT is the
> value-directed enter-or-β classification, because that is §2.2 step 3 itself.
> The tempting further step — send every head to `.callV` — would change what a
> stuck spine MEANS in a body: `callVValue` mints a fresh existential at the
> instantiated codomain where `readC` remembers the structured neutral `σ a`. That
> mint-vs-remember split is arrow-keyed (§12 decision 5), not head-keyed, so it is
> not what M31 dissolves, and it was left alone rather than smuggled in.
>
> **3. E4, answered: the wall is not `hasType`, and it is one step earlier.** The
> enumeration is short because it collapses — a borrow-moded Π has no `Val`
> (M26-C), so it cannot be the second argument of `hasType`, which takes `Val`s.
> Every site therefore takes its expected type either from a `Val` (structurally
> safe) or from `readC` of a Term (which refuses `borrowT` by name). Measured, not
> reasoned:
>
>   * declaring a borrow-moded Π parameter — fine (`fsig`, as `ih` already was);
>   * CALLING one from inside a body — fine (`callDeclC`, the `ih` path);
>   * passing a BORROW-FREE function as an argument — **fine, and this is new**:
>     §7's "pass it as an argument" promise is closed for that case;
>   * passing a function whose signature has a `&mut` binder — **refused**, by
>     `processArgs`' `readCWith` of the parameter type: "borrow type `&mut (τ ↝ S)`
>     is only valid at a telescope position".
>
> So E4's predicted `piAgree`-style agreement path does not exist, and nothing
> silently mistypes: the failure is an honest named rejection one step before
> `hasType` is reached. Building that path is Stage B's, and it should be built
> against `piAgree`, which already does telescope agreement on Terms.
>
> A second wall sits in front of it and is the one to fix first: **a `fn` body
> cannot NAME a sibling function as a bare identifier.** Bodies are elaborated in
> `fullRctx` — their own parameters, numbered from 0 — so bare-name resolution
> reaches the program tail only. This is not incidental. If bodies saw sibling
> slots, `fnElab`'s fresh-binder base (`max (maxVarId d.body) … + 1`) would be
> pushed above `progBase` and the synthesized `ih` would collide with a `fn` slot.
> Fixing the scope means fixing that base first.
>
> **4. What the `fn` lowering's refusal sentinel cost, and the general lesson.**
> `fn`'s statement lowering turns a refusal into an unbound `.call` whose NAME
> carries the diagnosis, resting on three properties, the third being "the
> diagnosis survives to the message". It survived because `readR`'s `.call` names
> the function it could not find. A comptime `fn` slot reaches `readC` instead —
> whose `.call` arm did not name it — and ten distinct `fnElab` refusals collapsed
> into one generic sentence about the comptime fragment. A rejection that will not
> say what it refused is worse at every site, so the fix went to the message.
>
> **5. The flip list, as-built against E9.** `let F = Main` accepted (needing a
> surface change too: bare `fn` names had no reading at all, only `f(…)` resolved,
> through `retarget`). Spec/apply twins collapsed. Fence tests deleted. The
> "reached by NAME" tests re-pointed at the backstop — with a wrinkle: `let g = F`
> never reaches the binding, because the ⇒-read of a capital binder hits
> `fenceComptime` first, whose advice ("lower-case it") is exactly what §2.1
> forbids for a function; hence `backstopFnRhs`, the same refusal asked before the
> right-hand side is evaluated, at the one place both names are in view.
> λ-citation refusals added with the migration. **Two flips off the list**, both
> derived rather than chosen: `let C = (proof : T)` (item 1 above), and the
> lowercase λ-valued `let` — `let g = λ(a){…}` — which §2.1 requires be capital and
> which the corpus used 111 times.
>
> **6. Deliberate scope limits, recorded as deferrals rather than found later.**
> The backstop's function test is `.rfn` or an `fsig`-σ — ⇒'s function values,
> exactly what the refusal it succeeds excluded. A pure `.lam` is not one, so
> §2.1's own example `let f = Add 1` is NOT caught; catching it would refuse every
> staged proof-builder in the corpus, which is a second and larger migration.
> Interestingly §2.4 collects part of that debt from the other side: a lowercase
> sealed pure λ is not refused at its binding, but a body that NAMES one is, since
> the binding is lowercase — which is why 94 such declarations capitalised in the
> same stage. And the citation check covers the two positions where a λ becomes a
> value in this corpus (an expression, a `let` right-hand side); a λ passed
> directly as a call argument or stored in a constructor field is unmeasured. One λ
> former makes "value position" one question instead of four, which is Stage B's.
>
> **7. What §2.4 was worth, concretely.** The rule's best moment in the corpus is
> quicksort's staged builders: `mkUb` freezes `*v` BEFORE the two recursive sorts
> and `fin` freezes it AFTER, and they were the same three characters in the
> source. They are now `V0` and `V1` — and the lying twin's lie (pre-sort bounds
> where post-sort ones belong) became the visible difference between `Hub0` and
> `Hub2` rather than something a reader dates by position. The rule's two
> boundaries both needed asserting: a λ's binder DOMAIN is checked (it is stored
> with the λ and read at every application), while a λ inside a type is not (a type
> is consumed at its own event) — without the second, every dependent signature in
> the corpus would have been swallowed.
>
> **8. The rename policy, and the one name where it mattered.** PascalCase =
> capitalise the initial and each letter after an underscore, then drop them.
> Applied to all 215 `fn` names and the `aliasMap` keys (`Len`, `Add`, `Count`, …).
> **Lemma reference names are NOT renamed** — *reversed in Stage C; see its
> addendum below, which is where the collision analysis this item starts now
> lives*: `le_refl`, `nth`, `swapL` are *Lean*
> identifiers reached by the raw fallthrough, with no `Var` for `isUpperInit` to
> read, so no mode marker is being suppressed. That decision was forced by `nth`,
> which is BOTH a `fn` and a `Std` lemma Term in the same block, coexisting at HEAD
> only because the spelling disambiguates (`nth(…)` is a call, `nth Z (*v)` is
> juxtaposition). Capitalise both and one becomes unreachable. The function
> capitalised; the lemma did not; they have different names now.
>
> **9. For Stage B, on the vestigial machinery.** Neither deletion fell out.
> `nextFrame + 128` is untouched by anything here. `applyRFn`'s `keep` set is still
> load-bearing: `admitGlobals` still admits function names as a body's free
> variables, so those ids must still be carried unshifted through `shiftVarsK`.
> §2.4 is what empties that set by construction — the free variables it admits are
> now exactly the comptime ones — so the deletion belongs after E2's newest-wins
> probe, with a differential showing the set empty. **Where that probe should
> start:** comptime-moded slots interact with the Stage 0 watermark discipline in
> one way worth knowing — a `fn` slot is an ordinary Ω entry in the program's
> outermost scope, which never pops, so no function binding is ever dropped by the
> sweep and newest-wins has nothing to resolve about them. The hazard E2 names
> lives entirely in frames and match arms, both of which Stage 0 already closed.

**Stage B — EXTRACTED to M32 (decision: skip the intermediate representation).** The
original Stage B built the merged λ with a `Val ⊕ Term` body payload — a waypoint
representation that M32's suspensions would rewrite again, double-touching the same ~40
`lamR`/`rfn` sites. Skipped: the λ merge, the death of `rfn`/`lamR`, the seal's
body-classification dispatch (vacuous while two formers exist — term-shape dispatch IS
body classification when `.lamR` means imperative), and E2's binder keying all land
ONCE, in M32, directly in the final form. Two scope consequences inside M31: `.lamR`
and `rfn` survive it (their deletion moves to M32), and §2.4's capture generality is
delivered in the restricted form today's representation supports — a fn body may
reference the *functions* above it (today's `admitGlobals` rule, restated in §2.4's
vocabulary); citing enclosing comptime *data* needs a value-carried environment
(escape-via-return dangles under scope-based access) and arrives with M32's
suspensions.


**Stage C — close-out.** Deletions Stage A enables (fence, function-read refusal,
`.app` router — done in A itself; anything residual); PROGRESS/DECISION-LOG; paper and
language.md currency (chapter 12's deviations block shrinks by one bullet — the
call-position containment dies; the `f(a, b)` spelling remains a surface question, out
of scope here). `callV` survives M31 (E6); `sealFn`'s rename waits for M32's dispatch
change.

> **Implementation addendum (Stage C, landed on `m31-stage-c`).** Two commits.
> The first reverses Stage A's addendum item 8; the second deletes what Stage A
> superseded and left standing. Both are recorded here because both found
> something the plan could not have.
>
> **1. Item 8 is reversed: the stdlib lemmas capitalise too (446 names).** Its
> argument — a Lean identifier has no `Var` for `isUpperInit` to read, so
> lowercase suppresses no mode marker — is sound about the KERNEL and silent
> about the READER, who sees one surface vocabulary in which `SwapL` and
> `Quicksort` are both functions and only one of them looks like one. §2.1 says
> "one rule for every name that denotes a function, library or user's"; the
> lemmas are the library half, and leaving them out made the rule a rule about
> `fn` rather than about functions.
>
> **2. The collision surface item 8 identified is real, and has two members, not
> one.** `resolveName` consults `fnSlotId` BEFORE the raw-Lean fallthrough, so a
> capital lemma name is shadowed by a `fn` of the same spelling. Both take the
> `L` suffix on the LEMMA (`swapL`'s L-for-list-spec, generalised — the function
> is the user-facing name and should not move):
>
>   * `nth` → `NthL`, the case item 8 predicted.
>   * `SplitA` → `SplitAL`, which it did not, **because `SplitA` was already
>     PascalCase and so was invisible to a policy stated as a capitalisation
>     rule.** `def SplitA` (the split predicate) and `fn SplitA` (the routine
>     that establishes it) have coexisted on main since ArraySort was written.
>     They are kept apart only by living in different `prog{}` blocks: the spec
>     defs elaborate with an empty `rctx`, so the fallthrough reaches the lemma,
>     while inside the fn's own block the slot would win. Not a bug today. The
>     general lesson for M32's name-keyed store: **a rename policy checks the
>     names it MOVES, and the collisions live among the names it does not.**
>
> The invariant that made `fnSlotId` safe has therefore expired — Stage A could
> say every lemma was lowercase, and that is now false. The replacement is a
> convention, recorded at the definition: a library lemma sharing a spelling with
> a `fn` takes the suffix, checkable in one grep. Making it a real condition
> belongs with M32's keying.
>
> **3. What a mechanical sweep gets wrong in this corpus, measured on a dry run.**
> Two failure modes, neither anticipated. Lean **dot-notation**: `tel.take k`,
> `hoisted.drop 1` are `List.take`/`List.drop`, so the identifier boundary must
> exclude a preceding `.` — which then misses the **qualified** references
> (`Dllbc.StdLemmas.le_refl` across four test modules and Measure's
> `lemmaEntries`), and those are what broke the first build. And **English
> prose**: 16 of the 446 names are all-lowercase single words (`add`, `count`,
> `set`, `sub`, `take`, `drop`, `len`, `append`, `nth`, `pred`, …) and the
> comments contain "a sub-slice", "set closed and small", "would take it". The
> sweep that worked is region-aware (a comment/string/code scanner, not a regex
> over lines): the full map in code spans, and in comment spans the full map only
> inside `backticks`, the unambiguous 430 everywhere.
>
> **4. `globalKind` deleted, and the claim it was propping up corrected.** Found
> by scanning every kernel definition for one with no call site, rather than by
> guessing which helpers Stage A orphaned — five exist, one is M31's.
> `admitGlobals` was its only caller, and §2.4's mode test replaced the call in
> Stage A δ without removing the predicate. `Programs.lean` still said a λ body's
> naming is "decided by `globalKind`, which admits functions and not proofs, so
> `cert` remains un-nameable whether it is bound capital or lowercase". Measured:
> a capital proof cited at a ⇝ position inside a body is **accepted** (the
> predicate would have refused it — a `Le 3 3` σ is not a function value); the
> same binder ⇒-MOVED is refused by `fenceComptime`, which gets there before
> §2.4; lowercase is refused by §2.4. Two tests pin it. **Consequence for M32**:
> "citing enclosing comptime DATA needs a value-carried environment and arrives
> with suspensions" (Stage B's extraction note above) is not true of citation as
> such — a proof at program scope cites fine today. The suspension requirement is
> about the ESCAPING case, and the note should be read that way.
>
> **5. Left undone, deliberately.** `Dllbc.Std`'s Val-level twins (`le_refl`,
> `le_refl_ty`, `le_reflT`) keep their Lean names: they have no surface reading
> at all, and renaming would put `Std.LeRefl` one letter from
> `StdLemmas.LeRefl`, two different objects. Four dead definitions that predate
> M31 (`FnMacro.progOf`, `FnMacro.succBinder`, `Pure.arrRun?`,
> `Value.prettyOmega`) are reported rather than deleted — `progOf` in particular
> is cited in test prose as an equivalence, so removing it costs documentation.

The sequencing rationale, restated for the new shape: M31 is the SEMANTICS milestone
(mode flip, naming, capture/citation rules — enumerable differential), M32 is the
REPRESENTATION milestone (suspensions, one λ, one store keying — zero differential).
Semantics first is still hardest-first: if functions-as-comptime walls anywhere, we
find out before the representation rewrite is funded; and every M31 rule (citation ⇒
σ-free self-contained suspensions; capture ⇒ formation check; Stage 0 ⇒ store hygiene)
shrinks M32.

**M32 scope ledger (rulings from the Stage A review; each item is a debt with a named
owner, not an open question):**

  * **The let-arrow invariant, no exceptions** (user ruling): capital `let` ⇝-reads
    its RHS, lowercase `let` ⇒-reads it — a programmer-statable rule with zero
    carve-outs. `Var.comptimeRhs`'s seal/λ exceptions (Stage A) are transitional debt.
    Deleting them needs the two items below.
  * **Sealing under ⇝.** The check half is already fragment-appropriate (conversion
    for pure, audit for imperative — the audit becomes a judgment invocable from ⇝).
    The genuinely hard part is σ GENERATIVITY: ⇝ evaluation is a function (same term,
    same value — `convert` is `==` on canonical forms), and minting a fresh σ per
    evaluation breaks that. Occurrence-keying ALONE is wrong (user correction): a seal
    site under a binder evaluates at different captured inputs, and those must not
    look equal. Resolution: **the σ is the seal SITE applied to its captured inputs**
    — a structured neutral (`sealσ(site, v₁…vₙ)` over the free variables' values),
    compared structurally like any stuck spine. Deterministic (same site + same
    inputs → same value, so evaluation stays a function; no counter under ⇝) and
    distinguishing (different inputs → different values). `fsig` keys by site. This is
    generativity done the way stuck recursors already do it: nominal head + applied
    arguments.
  * **No runtime λ** (user ruling): λ formation is ⇝-only; the pure lift's λ case and
    `rfn` formation die with `lamR` (already M32's). Consequence: ⇒ can no longer
    construct a function value, so the Stage A backstop becomes DERIVABLE and is
    deleted — the residual enforcement collapses to one rule at one boundary (the
    pure lift's result must be data, not a function), replacing today's scattered
    checks (`backstopFnRhs`/`backstopFnBinding`/species test). The remaining
    lowercase bindings of pure-function values (partial applications, `let f =
    Add 1`) migrate capital in the same commit.
    **REFUTED at M32 R3, measured** (see suspensions.md §2.5's correction and the
    R3 addendum): ⇒ still constructs function values, because a proof of a
    ∀-statement IS a λ and this calculus returns them in Σ tails — the refusal
    rejects quicksort's count equation and `sort2`. The migration is blocked by
    the same fact from the other side: capitalising a proof binding makes it
    unreadable where it is RETURNED. What R3 delivered is three enforcement sites
    becoming one; derivability and the migration move to R3b, behind §2.1.
  * **fn body scope**: bodies elaborate seeing sibling and enclosing bindings (the
    decl{}-era params-only context retires). Gated today on `fnElab`'s fresh-binder
    base colliding with program slots; trivial under M32's name-keying.
  * **The agreement path** for passing borrow-moded-signature functions as arguments
    (`piAgree` at argument positions — E4's measured gap).
  * **Nullary fns desugar to `λ (U : Unit)`** with call sites passing `unit` (user
    decision, overriding E6's keep-callV recommendation) — which removes `callV`'s
    last unique job, so **M32 retires `callV` for app spines**. One preserved
    distinction to carry: the mint-vs-remember split (`callVValue` mints a fresh
    existential at the instantiated codomain; `readC` remembers the structured
    neutral) is arrow-keyed (§12 decision 5), not node-keyed — the spine rule must
    keep it.
    **DONE at M32 R2 (the desugar) and R4 (the retirement), and the warning was
    half right.** The split survived, keyed on the callee's VALUE, and `f(a, b)`
    and `f a b` are now literally the same `Term`. What the warning did not
    anticipate is that `callV` was also carrying THREE rules the arrows were not,
    each of which had to be restated on the value or lost silently: §12 decision
    4's saturation applied to a comptime λ (which the flagship refutes — it
    applies its proof-builders partially), ⇝'s refusal to read a CALL
    (`reflectC` refused the node BY NAME), and §5.2's demand collapse at the
    callee slot. See suspensions.md's R4 addendum.

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
are all invariants M31 establishes; fall back to (ii) only if the probe walls.
**Resolution moved to M32** with the rest of the representation work (Stage B's
extraction): under suspensions the knowledge side is name-keyed anyway, so (i) is the
natural fit and the newest-wins probe becomes part of M32's design phase, not a Stage B
gate. Stage 0's merge already met the precondition (pop-with-drop on main) and narrowed
the hazard (only ended scopes, both now popping).

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

**Resolution: DISSOLVED by skipping the intermediate (user decision).** Option (i) —
the `Val ⊕ Term` payload — is never built: Stage B's extraction to M32 means the λ
merge lands directly in the suspension representation, where the payload question is
unaskable (every body is a Term under an env). The analysis above stands as the reason
(ii) was rejected *as an increment on the mixed domain*, and as background for M32's
design: the traversal set it enumerates is exactly what M32's rewrite must convert, and
the conversed-with/entered line it draws is exactly what normalize-at-splits preserves.

**M32: suspensions everywhere — the classic NbE split.** Term becomes the ONLY syntax; Val shrinks to a semantic domain (constructors,
neutrals, closures, borrow/loan markers, ⊥); Ω stores `(Term, knowledge-env)`
suspensions and normalizes on demand; the mixed domain — Val embedding pure syntax, the
fact that generated this E — dies. This supersedes the earlier union-tree horizon,
which admitted machine forms grammatically everywhere; the suspension endpoint
separates syntax from semantics instead of unioning them. Made viable by this
milestone: §2.4's citation rule is what makes every suspension self-contained (σ-free
Term + small knowledge-only env). The one design obligation has a precise criterion: **a store-wide sweep is safe on
suspensions iff it commutes with evaluation.** Substitution (refinement, σ := v) is
keyed on an atom, which every representation preserves — it commutes, so it propagates
through captured environments and later evaluation gets it right. X-Gen's abstraction
(spine ↦ fresh σb) is keyed on a COMPOUND that evaluation can mint (the env holds the
spine's ingredients, not the spine), so it does not commute — occurrences latent in a
suspension are missed, and later evaluation speaks the pre-abstraction vocabulary:
propositionally still linked by the branch equation, but definitional equality is lost,
which presents as flagship proofs failing (the M30 count-equation mode, measured,
silent). The known answer: **normalize at splits, with write-back** — `refineSym`
already sweeps the whole store at every symbolic split, so evaluating suspensions
during that sweep (and keeping the normalized form — re-deriving later from the
original suspension would replay old vocabulary) materializes every occurrence exactly
where the non-commuting sweep needs it, at the cost the split already pays; between
splits everything stays lazy. Convert-site comparisons are
timing-only (checker is 1.3% of the build — slack exists). Canary: quicksort's count
equation. Cost print: at least M30-sized — every consumer of Val's syntax embedding is
touched.

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
spine; (iii) refuse nullary `fn`. **Decided: (i)** (user ruling at the Stage A review)
— `fn F()` desugars to `λ (U : Unit)`, call sites pass `unit`; `callV` loses its last
unique job and retires in M32 (see the scope ledger's nullary item for the
mint-vs-remember distinction the spine rule must preserve). Risk: LOW, contained.

**E7 — the executing machine and comptime-moded slots.** Functions stay in Ω, which
execution already reads, so there is no store-access question here. What must be
confirmed: executing mode today never ⇝-reads (it computes, it does not
convert), and a call head is now a ⇝ fetch — the executing-mode version of that fetch
must be the plain slot read it already does for `rfn`, not a detour through the
normalizer. Also confirm seal transparency (`3251`) composes with the mode flip. Risk:
LOW.

**E8 — `[k]` hoisting and call-site permutation.** **KEPT, and asserted at M32 R4**
(`S32Spine` §E, directly against `retarget` with the no-hint case as its control).
 The sealed telescope hoists the
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
    refusal, the `.app` router — the §3 inventory's M31 half. (`rfn` and `lamR` close
    in M32, with the representation.)
  * The "pass it as an argument" promise: passing a function is a ⇝ argument read,
    which is the name-use the current error message describes and the code refuses.

## 8. Non-goals

  * **Capture of runtime state stays shut.** Knowledge capture is open (§2.4's one
    rule); what no λ may close over is a lowercase local, a borrow, or a hole — the
    Fn/FnMut/FnOnce door (nbe.md §3) stays representable-not-open.
  * **Surface call syntax** (juxtaposition vs `f(a, b)`) — orthogonal, already tracked
    in language.md chapter 12's deviations block.
  * **M32's representation work** (suspensions, one λ, `rfn`/`lamR` deletion, E2's
    keying, the seal dispatch rename) — planned, specified in E3's M32 section, not
    attempted in M31; M31's capture/citation rules are what make it viable.
  * **Consistency/soundness proofs** — unchanged scope; the checker remains the claim.
