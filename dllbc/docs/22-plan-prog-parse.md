# 22 — `prog_parse { … }`: fragments with free identifiers, bound where they are spliced

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

### 2.2 `prog_parse { … }` — the existing walker with och's law switched off

ONE walker, one grammar (the M29 γ lesson). The walker's state gains a flag, `SpanAcc.parse`; with it set, the one place och's law is enforced — `resolveName`'s final fallthrough, which emits the Lean identifier of an unresolved name so that Lean reports it — emits instead a term that asks Lean the same question and falls back to `.ident`:

* `Dllbc.Surface.ident_or_free% x` is a term elaborator: if `x` resolves in Lean's scope (a local or a global, `Term.resolveId?`) it elaborates `x` as `prog{}` would have; otherwise it is `Term.ident "x"`. The question is asked at Lean elaboration rather than at macro expansion because a `MacroM` cannot see Lean locals, and a `prog{}` can name one bare (`def f (t : Term) := prog{ … t … }`). This keeps the one property that matters: **every source `prog{}` accepts, `prog_parse {}` accepts, and elaborates to the same `Term`** — parse mode only widens the accepted set, it never re-reads a name.
* Its own binders mint ids as today, from a counter starting at 0. A fragment's `let`/λ/match binders therefore collide with the enclosing block's ids when spliced; that is inert under the name-keyed Ω (M32 R1) and is the same collision the `fn` row already accepts for its telescope (`Uni.lean` `buildTele`'s docstring). The reserved `§pN` pattern slots carry their id in the name, and a fragment's `§p0` cannot collide live with a block's `§p0`: the block's is dead by the time any arm body — where a fragment can be spliced — runs.
* A free **match scrutinee** (`match v { … }` for free `v`) cannot be an `.ident`, because the grammar makes the scrutinee a `Var`. It is emitted as `⟨Dllbc.freeSlot, "v"⟩` — a tag id alongside `noSlot` and `declSlot` — and `bindFree` rewrites it by name like an `.ident`. `Term.freeIdents` reports it; `findSlot?` answers `none` for the tag so that a leaked one is "unbound at runtime", never a silent by-name hit. This is the one place free-ness is carried by a `Var` rather than by the new constructor, and it is forced by the grammar, not chosen.
* The flag is NOT the mode flag M29 γ deleted, and the distinction is the one `SpanAcc.collect`'s docstring already draws: that flag had readers that made the same source elaborate to different `Term`s. This one has exactly one reader, and it turns an error into a term. No accepted program reads differently.

**`prog_parse { }` IS the parse-stage brace** — the one `7703efee` renamed `prog defer_check` to, by user ruling ("the parsing stage alone: the block elaborates to a `Term` and no judgment runs"), 1,323 sites. This lane was briefed and built against the pre-rename tree, as a fourth brace; on rebase the two are one form, and that is the right reading rather than a convenience: och's law is a property of the CHECKED brace, the parse stage has no judgment to refuse a free name with, and a free name in a parse-stage block that reaches a program boundary unbound is rejected there. The closed braces (`prog{ }`, `ty{ }`) are unchanged and still refuse at Lean elaboration (pinned by `#guard_msgs` in `Tests/Parse.lean`). The flag is set in `prog_parse`'s elaborator rule and nowhere else.

### 2.3 The splice-site bind

The `%e` row of the walker emits `Dllbc.Term.bindFree ⟨rctx literal⟩ ⟨pctx literal⟩ (e : Dllbc.Term)` instead of the bare value. The contexts are the walker's own at that point — the same `rctx`/`pctx` that `resolveName` would consult for a name written inline there — quoted as list literals. `bindFree` walks the spliced VALUE at Lean runtime (the macro never has the value; a splice is a Lean expression) and resolves every `.ident s`:

* `s` in `pctx` → `.pvar s` (pure binder wins, as `resolveName` has it);
* else `s` in `rctx` → `.var ⟨id, s⟩` (a local or a `fn` slot);
* else `s` a kernel constant (`Dllbc.constNames`) → `.const s` — reached only by the lowercase, shadowable ones, which parse mode leaves free (§6.1);
* else it stays `.ident s`, and the boundary rejects it unless an OUTER splice binds it.

That last clause is what makes splicing compose: a fragment spliced into a fragment spliced into a program is bound innermost-first, and a name none of them binds reaches the boundary. It is also why `bindFree` needs no binder-awareness: the fragment's own binders already resolved their occurrences at parse, so an `.ident` is free by construction and a leaf map is the whole pass.

Why at the `%` row and not somewhere with the value in hand: the contexts live in the walker (`elabUTerm rctx pctx next`), and the `%` row is the only place that has both the splice and the contexts. The `fn` row elaborates its return type with `fullRctx ++ rctx` and its body with the same, so `-> %ret` binds `v`, `i` at their positional ids 0, 1 — the `seedTelescope` convention the census's skeletons reproduced by hand. A `%` in the empty context emits `bindFree [] []`, the identity; emitted unconditionally, because a row that special-cases the empty context is a second row.

Cost: one traversal of each spliced value per evaluation of the enclosing definition. The corpus has ~94 `%` sites; a traversal is linear in the spliced term and the terms are small next to the walk that follows. `prog{}`'s elaboration-time check evaluates the assembled `Expr` when it is closed, and `bindFree` of a global fragment is closed, so a program with a spliced fragment is checked at its site like any other.

### 2.4 Where a fragment has no splice site

Two census sites use open terms with NO enclosing block: `Functions.lean` §E/§F compares arm annotations (`Le (Len *v) b` at the residual telescope's `v`) by `Term.beq`, and `EagerRec.lean`'s `openTwo` feeds a term with a free pure `x` straight to the normalizer. For these the bind is written explicitly at the Lean level — `Term.bindFree [("v", 1)] [] prog_parse { Le (Len *v) %b }` — with a hand context. That is the `…With` shape M28 η deleted, and it is legitimate here for the reason M28 η's argument does not reach: these positions are a DERIVED telescope's (the recursor arm's residual binders, which "no source can write", `Functions.lean:1374-1379`), not a `fn` header's. Anywhere a `fn` header exists, the header is the context and the explicit form is wrong.

## 3. Acceptance

All build-asserted, in `Dllbc/Tests/Parse.lean`:

(a) `prog_parse { Id (List Nat) (*v) (Take i (old *v)) }` has free `v`, `i` (`Term.freeIdents`), and after `bindFree [("v",0),("i",1)] []` is `Term.beq` to what `prog{}` produces for the same text written INLINE in an `fn` header.
(b) A fragment with free `hd`, spliced into a match arm that binds `hd`, is captured by that arm: the program checks and `beq`s the inline spelling.
(c) A fragment with an internal `let hd` whose inner `hd` is NOT captured by the arm's `hd` — the shadowing pin: the fragment's `hd` is at the fragment's own id, not the arm's.
(d) An unbound free identifier at the boundary is rejected with the pinned message, and a closed `prog{}` still refuses a free name at elaboration (unchanged).
(e) The census's non-twin open-term sites converted (§6 table), each beq-witnessed against its raw form before the raw form was deleted.

## 4. Hygiene ruling

**Parsed fragments are UNHYGIENIC ON PURPOSE.** A fragment's free edge is dynamic: `hd` in a fragment means whatever `hd` the splice site has in scope, which is the whole point — `Direct.lean:497-500`'s "the `hd` this match will bind" is said by writing `hd`. Inside the fragment scoping is lexical as everywhere else: a fragment's own binders shadow the splice site's for their own occurrences (§2.3's leaf-map argument is the mechanism). So a fragment is lexical inside and dynamic at its edge, and a reader of `%frag` at a site knows exactly which names cross: the ones the fragment did not bind.

**Closed programs are unchanged.** `prog{}`, `prog_parse {}`, `ty{}` still refuse a free name at Lean elaboration (och's law, `Uni.lean:49-55`), and a `prog_parse {}` value that reaches a boundary with a free name is rejected there. There is no path by which a free name is silently accepted.

## 5. The endpoint: one `.ident` for both, resolved by the evaluator

The design as built keeps `.var` and `.pvar` as the parser's classification and adds `.ident` for what the parser could not classify. The stated endpoint is the full merge: one `.ident` replacing both, classified at evaluation by lookup — the same resolution the evaluator already performs by name since M32 R1 (`findSlot?` never reads an id; `Pure.eval` binds by name). That waits for docs/20 (module states), because it needs the SAME resolution path: under module states a block elaborates against a seeded state and names resolve from it, and the classification the surface performs today — pure binder, runtime slot, `fn` slot, constant — becomes a question the environment answers. Doing the merge before that would build a second resolution path to delete later. The `.ident` constructor, the `bindFree` leaf map and the boundary rejection are the pieces that survive the merge unchanged.

## 6. As built

Where things landed: `Term.ident`, `freeSlot`, `constNames`, `Term.freeIdents`, `Term.bindFree`/`bindIdent`, `Term.rejectFree`, `freeIdentNeedle` in `Syntax.lean`; the `.ident` rows in `reflectC` and `readR`, the `freeSlot` guard in `findSlot?`, and `atBoundary = numberSeals ∘ rejectFree` in `Machine.lean`; `SpanAcc.parse`, `ident_or_free%`, the `%` row's `bindFree`, `resolveName`'s parse-mode fallthroughs and `elabScrut`'s free scrutinee in `Uni.lean`; the parse flag set in `prog_parse { }`'s rule in `ElabCheck.lean` (main's parse-stage brace, §2.2); the acceptance battery in `Tests/Parse.lean`.

### 6.1 Deviations from the design as briefed

* **Free scrutinee tag** (`freeSlot`, §2.2): the brief had every free occurrence as `.ident`; the grammar's `matchE : Var → …` forces a `Var`-level tag for the scrutinee. Reported by `freeIdents`, bound by `bindFree`, `none` from `findSlot?`.
* **Lean-name resolution at elaboration** (`ident_or_free%`, §2.2): the brief said "a name that resolves to nothing"; a `MacroM` cannot decide that for Lean locals, so the decision is deferred to a term elaborator. Without it `prog_parse {}` would have re-read a bare Lean local as `.ident` — a source `prog{}` accepts that `prog_parse {}` would read differently.
* **Lowercase kernel constants are decided at the splice, not at parse** (found by the §H conversion, not foreseen). `k` is the `Id` eliminator and the name every `S(k) =>` arm binds; inline the local wins because `resolveName` looks it up first, and a fragment cannot look it up. So a lowercase `constSet` name (`k`, `j`, `natRec`, …) stays `.ident` in parse mode and `bindIdent` asks the splice site's binders first and the table last — the brief's "ctor/const by table" clause, which the first cut had dropped on the argument that the parser classifies constants. It does, except for the shadowable ones. The table moved to the kernel (`Dllbc.constNames`) for `ctorSet`'s reason: two readers, one list. The capitalized constants and all constructors are reserved as binders (`reservedBinder`) and are still classified at parse; the one lowercase constructor, `unit`, is too — nothing in the corpus binds it, and a fragment that needs a splice-site `unit` would be the first.
* **The boundary is the empty-context splice** (§2.1): `rejectFree` runs `bindFree [] []` first, so a bare fragment's `k` is the eliminator at the boundary, and only what survives THAT is rejected. One function for both jobs rather than a second resolution rule at the boundary.
* **`bindFree` rewrites a call whose head the splice site binds as a LOCAL** into the spine `f(a)` would have been inline ("scope beats the table", the call row); a `fn`-slot head stays a `.call` for `retarget`. Needed because a fragment's `F(y)` cannot know what `F` will be; without it a let-bound function at the splice site was "unknown function".
* **Explicit `bindFree` at two Lean-level sites** (§2.4): the brief's bind is at the splice site; Functions §E/§F and EagerRec have none.
* **Boundary rejection as a poison term** (§2.1): `atBoundary` stays `Term → Term` (the marker lane composes at the same signature); the rejection rides the `fnElabOrFail` precedent rather than changing the boundary's type at its six entry points.
* **No fourth brace** (§2.2): the brief's `prog_parse{ }` and main's renamed parse-stage `prog_parse { }` are one form. Consequence worth stating: every one of the 1,323 parse-stage sites now elaborates a free name to `.ident` instead of a Lean error. The suite is green, so none had one; a future typo in a `progRejects` twin's name is reported by the boundary ("free identifier 'x'") instead of by Lean, and the twin's own needle still fails it.
* **`bindFree` and `freeIdents` are structurally recursive** (no `termination_by`), as `numberSeals` is and `beq` is not: the corpus asserts two `rfl` goldens whose sides are a `%vecFT` splice against a bare `vecFT` (`Sugar.lean:222`), and a well-founded `bindFree` is irreducible to `rfl`. Found by the first full build.

### 6.2 What a fragment's ids are

A fragment mints its own binders from 0. The raw pools this replaces chose ids by hand (`Diff.lean`: `hd`/`tl` at 2/3 "fixed"; `Programs.lean` §H: `G` at 3, `y` at 4, `r` at 5), and no fragment reproduces those — so the conversion witnesses below that involve a fragment binder are `Term.beq` MODULO runtime ids (every `Var` id set to 0, names kept), plus the program-level assertions unchanged. The ids are decoration under the name-keyed Ω (M32 R1/R2/R4), and the witnesses also pin that: every verdict, run and count is identical. One id-keyed lookup survives in the kernel — `joinSym`'s per-slot `find?` by id (`Machine.lean`, the arm join) — which a fragment binder at id 0 could in principle collide with against a telescope's `v` at 0; the pinned counts (91/47, 32/15, 13/13) say it did not here. Worth knowing, not this lane's to fix.

### 6.3 Conversion table (§3(e))

| site | raw form | converted to | witness (before deletion) |
|---|---|---|---|
| Diff.lean Df1 `exprs`/`leafBodies`/`matchBodies`/`vNonExhaustive` | `.var ⟨0,"v"⟩`, `.letIn ⟨2,"tail"⟩`, `.matchE ⟨0,"v"⟩ … [⟨2,"hd"⟩, ⟨3,"tl"⟩]` | `prog_parse { … }` pools with `v` free, `match v { … }` a free scrutinee | `beq` after `bindFree [v↦0, x↦2]` on the binder-free pools; modulo ids on the rest; per-body verdicts identical; 91/47 pinned |
| Diff.lean Df1 `nLeaf`/`nBodies` | `.var ⟨0,"n"⟩`, `.var ⟨1,"m"⟩` | fragments with `n`, `m` free | as above with `[n↦0, m↦1]`; 32/15 |
| Diff.lean Df1 `bcLeaf`/`bcBodies` | `.var ⟨0,"b"⟩`, `.matchE ⟨1,"c"⟩` | fragments with `b`, `c` free | as above with `[b↦0, c↦1]`; 13/13 |
| Programs.lean P5 `hSplit` | raw `let`/`let`/`matchE` spine over spliced branch bodies | `prog_parse { let F = …; let n = F(3); match n { Z => %inZ, S(k) => %inS } }` | exact `beq` |
| Programs.lean P5 `hGlobal`/`hCapture`/`hSeal` | raw branch bodies citing `F` (id 0) and `k` (id 2) | `prog_parse { let G = λ(y : Nat){ F(y) }; let r = G(k); … }` etc. | modulo ids; the four verdicts unchanged |
| Programs.lean P5 `hLend` | raw six-`let` spine | one closed `prog{ }` | modulo ids (the census's "ids mint 0..5 in the same order" was wrong: a runtime λ's binders consume the counter) |
| Functions.lean F8 `leLen`, F7 `bndDeclHn` | `%(Std.LeFnT) (%(Std.lenFnT) %(Term.deref (.var ⟨1,"v"⟩))) %b` | `Term.bindFree [("v", 1)] [] prog_parse { Le (Len *v) %b }` (§2.4) | exact `beq` at `Z` and at a `.var` |
| Functions.lean F9 payloads | `.const "Bool"`, `.borrowT "§_" (List Bool) (List Bool)` | `ty{ Bool }`, `ty{ &mut List Bool }` | exact `beq` |
| Sugar.lean S2 classifier probes | `.app (.var g) .unit`, `.app (.const "Len") (.var l)`, `.app (.pvar "Le") (.pvar "a")`, `.var g` | `bindFree [g↦0] [] prog_parse { g () }`, `… prog_parse { natRec l }`, `bindFree [] ["P","a"] prog_parse { P a }`, `… prog_parse { g }` | exact `beq`; the classifier's four answers unchanged. `Len`/`Le` respelled: the surface resolves them to their `…FnT` λ-terms, which is a different head kind; `natRec` and a pure `P` keep the head kind the probe is about |
| EagerRec.lean E2 `openTwo` | `S(S(%(Term.pvar "x")))` | `Term.bindFree [] ["x"] prog_parse { S(S(x)) }` (§2.4) | exact `beq` |

Left alone, as briefed: the twin skeletons (Direct D1/D4, ArraySort A1, HashMap H1, Programs P6's `zapUnder`) — docs/21's marked-twins plan retires them.
