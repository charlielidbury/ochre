# 22 — `prog_parse{ … }`: fragments with free identifiers, bound where they are spliced

Status: design decided by team-lead 2026-08-22 from the raw-term census; built in this lane (`dllbc-prog-parse`). §6 is the as-built record and lists every deviation from the design as briefed.

## 1. The problem, from the census

The census of raw `Term` construction in the test suite (surveyed at `578bb5cc`) found 61 instances, and sorted the structural ones into classes. One class is **open terms**: a fragment that names binders it does not bind, written outside the binder that would bind them — 12 instances. The shapes:

* a spec return type written outside its `fn` header so that several twins can share one body (`Direct.lean:415-420`: "a return type written outside the header — a skeleton, below — has to name them that way");
* branch bodies for a symbolic match, built as Lean values and spliced into the arms (`Programs.lean` §H: the bodies cite `F` and `k` from the enclosing program);
* generator pools for the differential (`Diff.lean:46-56`: "Raw Term construction: the generator needs AST literals, not the `prog{}` macro" — `v` at id 0, match binders at fixed ids 2/3);
* perturbation payloads at a residual telescope's positions (`Functions.lean` §E/§F);
* classifier probes (`Sugar.lean` §D) and a deliberately free `x` (`EagerRec.lean:100`).

Every one of these is raw for the same reason, and `Direct.lean:497-500` states it exactly: *"a `%` splice is a Lean `Term` written outside the macro, which has no way to say 'the `hd` this match will bind'."* The empty-context brace is a decision, not a gap (`ProgMacro.lean:52-65`, M28 η): the three `…With` forms that pre-bound a list of names to ids were deleted because seeding is what `fn` already does. That argument covers programs. It does not cover a fragment, which is not a program and is never checked on its own — it is a piece of one, waiting for the program that will contain it.

## 2. The design

**A fragment's free identifiers stay free, as identifiers, until the fragment is spliced; the splice site binds them against ITS binders.** Capture-on-splice, deliberately unhygienic (§4).

### 2.1 `Term.ident : String → Term` — an unresolved identifier

A new `Term` constructor, **kernel-invisible by construction**. It exists between two events — the parse of a fragment and the splice of that fragment into a block — and at the program boundary it has either been resolved or it is rejected. The precedent is `numberSeals` (and the marker lane's strip, docs/21 §4): `Machine.atBoundary` is the one function every program walk enters through, and a pass there is the place a construct gets to be surface-only.

* **Boundary step.** `atBoundary t = numberSeals (rejectFree t)`. `Term.freeIdents` collects every `.ident` (and every free scrutinee, §2.4) in the term; if any survive, `rejectFree` replaces the program with a term the machine refuses distinctively — the `fnElabOrFail` precedent (`FnMacro.lean:635-651`): an unbound `.call` whose NAME carries the message, prefixed by the needle `§free-identifier`, reached unconditionally because it IS the program. The pinned message is **`free identifier 'v' has no binder at the splice site`**. This is a rejection rather than a strip because an unresolved name is an error in the program, not scaffolding to remove; and it is at the boundary rather than at the first machine rule that meets the node because a free identifier in a branch the walk never takes must still be loud.
* **Composition with the marker lane** (docs/21, off `main` at the time of writing): markers are identity and are stripped first; free identifiers are rejected second; seals are numbered last. `atBoundary = numberSeals ∘ rejectFree ∘ stripMarkers`. The reject pass is structural and will need a marker row when the two merge, written transparent.
* **Machine rows.** Every `match` on `Term` without a catch-all gets an `.ident` row that throws *"unresolved identifier 'v' reached the machine"* — never silent acceptance. These are backstops for entries that bypass `atBoundary` (KernelFloor's direct `readC`/`convert` probes); through the boundary they are unreachable by construction. Traversals that are not the machine (`beq`, `freeRVars`, `substP`, `numberSeals`, `pretty`, …) get structural rows.

**`.var`/`.pvar` stay separate.** The parser classifies every occurrence it can — its own binders, constructors, kernel constants, reified-function aliases, `fn` slots, and Lean-level names — exactly as `prog{}` does, and emits `.ident` ONLY for an occurrence that resolves to nothing. The endpoint this is a step toward is §5.

### 2.2 `prog_parse{ … }` — the existing walker with och's law switched off

ONE walker, one grammar (the M29 γ lesson). The walker's state gains a flag, `SpanAcc.parse`; with it set, the one place och's law is enforced — `resolveName`'s final fallthrough, which emits the Lean identifier of an unresolved name so that Lean reports it — emits instead a term that asks Lean the same question and falls back to `.ident`:

* `Dllbc.Surface.ident_or_free% x` is a term elaborator: if `x` resolves in Lean's scope (a local or a global, `Term.resolveId?`) it elaborates `x` as `prog{}` would have; otherwise it is `Term.ident "x"`. The question is asked at Lean elaboration rather than at macro expansion because a `MacroM` cannot see Lean locals, and a `prog{}` can name one bare (`def f (t : Term) := prog{ … t … }`). This keeps the one property that matters: **every source `prog{}` accepts, `prog_parse{}` accepts, and elaborates to the same `Term`** — parse mode only widens the accepted set, it never re-reads a name.
* Its own binders mint ids as today, from a counter starting at 0. A fragment's `let`/λ/match binders therefore collide with the enclosing block's ids when spliced; that is inert under the name-keyed Ω (M32 R1) and is the same collision the `fn` row already accepts for its telescope (`Uni.lean` `buildTele`'s docstring). The reserved `§pN` pattern slots carry their id in the name, and a fragment's `§p0` cannot collide live with a block's `§p0`: the block's is dead by the time any arm body — where a fragment can be spliced — runs.
* A free **match scrutinee** (`match v { … }` for free `v`) cannot be an `.ident`, because the grammar makes the scrutinee a `Var`. It is emitted as `⟨Dllbc.freeSlot, "v"⟩` — a tag id alongside `noSlot` and `declSlot` — and `bindFree` rewrites it by name like an `.ident`. `Term.freeIdents` reports it; `findSlot?` answers `none` for the tag so that a leaked one is "unbound at runtime", never a silent by-name hit. This is the one place free-ness is carried by a `Var` rather than by the new constructor, and it is forced by the grammar, not chosen.
* The flag is NOT the mode flag M29 γ deleted, and the distinction is the one `SpanAcc.collect`'s docstring already draws: that flag had readers that made the same source elaborate to different `Term`s. This one has exactly one reader, and it turns an error into a term. No accepted program reads differently.

`prog_parse{ }` lives beside `prog{ }` and `prog defer_check { }` in `ElabCheck.lean`. It never checks at elaboration — a fragment is open by construction and has nothing to check.

### 2.3 The splice-site bind

The `%e` row of the walker emits `Dllbc.Term.bindFree ⟨rctx literal⟩ ⟨pctx literal⟩ (e : Dllbc.Term)` instead of the bare value. The contexts are the walker's own at that point — the same `rctx`/`pctx` that `resolveName` would consult for a name written inline there — quoted as list literals. `bindFree` walks the spliced VALUE at Lean runtime (the macro never has the value; a splice is a Lean expression) and resolves every `.ident s`:

* `s` in `pctx` → `.pvar s` (pure binder wins, as `resolveName` has it);
* else `s` in `rctx` → `.var ⟨id, s⟩` (a local or a `fn` slot);
* else it stays `.ident s`, and the boundary rejects it unless an OUTER splice binds it.

That last clause is what makes splicing compose: a fragment spliced into a fragment spliced into a program is bound innermost-first, and a name none of them binds reaches the boundary. It is also why `bindFree` needs no binder-awareness: the fragment's own binders already resolved their occurrences at parse, so an `.ident` is free by construction and a leaf map is the whole pass.

Why at the `%` row and not somewhere with the value in hand: the contexts live in the walker (`elabUTerm rctx pctx next`), and the `%` row is the only place that has both the splice and the contexts. The `fn` row elaborates its return type with `fullRctx ++ rctx` and its body with the same, so `-> %ret` binds `v`, `i` at their positional ids 0, 1 — the `seedTelescope` convention the census's skeletons reproduced by hand. A `%` in the empty context emits `bindFree [] []`, the identity; emitted unconditionally, because a row that special-cases the empty context is a second row.

Cost: one traversal of each spliced value per evaluation of the enclosing definition. The corpus has ~94 `%` sites; a traversal is linear in the spliced term and the terms are small next to the walk that follows. `prog{}`'s elaboration-time check evaluates the assembled `Expr` when it is closed, and `bindFree` of a global fragment is closed, so a program with a spliced fragment is checked at its site like any other.

### 2.4 Where a fragment has no splice site

Two census sites use open terms with NO enclosing block: `Functions.lean` §E/§F compares arm annotations (`Le (Len *v) b` at the residual telescope's `v`) by `Term.beq`, and `EagerRec.lean`'s `openTwo` feeds a term with a free pure `x` straight to the normalizer. For these the bind is written explicitly at the Lean level — `Term.bindFree [("v", 1)] [] prog_parse{ Le (Len *v) %b }` — with a hand context. That is the `…With` shape M28 η deleted, and it is legitimate here for the reason M28 η's argument does not reach: these positions are a DERIVED telescope's (the recursor arm's residual binders, which "no source can write", `Functions.lean:1374-1379`), not a `fn` header's. Anywhere a `fn` header exists, the header is the context and the explicit form is wrong.

## 3. Acceptance

All build-asserted, in `Dllbc/Tests/Parse.lean`:

(a) `prog_parse{ Id (List Nat) (*v) (Take i (old *v)) }` has free `v`, `i` (`Term.freeIdents`), and after `bindFree [("v",0),("i",1)] []` is `Term.beq` to what `prog{}` produces for the same text written INLINE in an `fn` header.
(b) A fragment with free `hd`, spliced into a match arm that binds `hd`, is captured by that arm: the program checks and `beq`s the inline spelling.
(c) A fragment with an internal `let hd` whose inner `hd` is NOT captured by the arm's `hd` — the shadowing pin: the fragment's `hd` is at the fragment's own id, not the arm's.
(d) An unbound free identifier at the boundary is rejected with the pinned message, and a closed `prog{}` still refuses a free name at elaboration (unchanged).
(e) The census's non-twin open-term sites converted (§6 table), each beq-witnessed against its raw form before the raw form was deleted.

## 4. Hygiene ruling

**Parsed fragments are UNHYGIENIC ON PURPOSE.** A fragment's free edge is dynamic: `hd` in a fragment means whatever `hd` the splice site has in scope, which is the whole point — `Direct.lean:497-500`'s "the `hd` this match will bind" is said by writing `hd`. Inside the fragment scoping is lexical as everywhere else: a fragment's own binders shadow the splice site's for their own occurrences (§2.3's leaf-map argument is the mechanism). So a fragment is lexical inside and dynamic at its edge, and a reader of `%frag` at a site knows exactly which names cross: the ones the fragment did not bind.

**Closed programs are unchanged.** `prog{}`, `prog defer_check {}`, `ty{}` still refuse a free name at Lean elaboration (och's law, `Uni.lean:49-55`), and a `prog_parse{}` value that reaches a boundary with a free name is rejected there. There is no path by which a free name is silently accepted.

## 5. The endpoint: one `.ident` for both, resolved by the evaluator

The design as built keeps `.var` and `.pvar` as the parser's classification and adds `.ident` for what the parser could not classify. The stated endpoint is the full merge: one `.ident` replacing both, classified at evaluation by lookup — the same resolution the evaluator already performs by name since M32 R1 (`findSlot?` never reads an id; `Pure.eval` binds by name). That waits for docs/20 (module states), because it needs the SAME resolution path: under module states a block elaborates against a seeded state and names resolve from it, and the classification the surface performs today — pure binder, runtime slot, `fn` slot, constant — becomes a question the environment answers. Doing the merge before that would build a second resolution path to delete later. The `.ident` constructor, the `bindFree` leaf map and the boundary rejection are the pieces that survive the merge unchanged.

## 6. As built

(Filled in by this lane's implementation commits; see the commit messages for each step's rationale.)

### 6.1 Deviations from the design as briefed

* **Free scrutinee tag** (`freeSlot`, §2.2): the brief had every free occurrence as `.ident`; the grammar's `matchE : Var → …` forces a `Var`-level tag for the scrutinee. Reported by `freeIdents`, bound by `bindFree`, `none` from `findSlot?`.
* **Lean-name resolution at elaboration** (`ident_or_free%`, §2.2): the brief said "a name that resolves to nothing"; a `MacroM` cannot decide that for Lean locals, so the decision is deferred to a term elaborator. Without it `prog_parse{}` would have re-read a bare Lean local as `.ident` — a source `prog{}` accepts that `prog_parse{}` would read differently.
* **Explicit `bindFree` at two Lean-level sites** (§2.4): the brief's bind is at the splice site; Functions §E/§F and EagerRec have none.
* **Boundary rejection as a poison term** (§2.1): `atBoundary` stays `Term → Term` (the marker lane composes at the same signature); the rejection rides the `fnElabOrFail` precedent rather than changing the boundary's type at its six entry points.

### 6.2 Conversion table (§3(e))

| site | raw form | converted to | witness |
|---|---|---|---|
| (filled in per commit) | | | |
