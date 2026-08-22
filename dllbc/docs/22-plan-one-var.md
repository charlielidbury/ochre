# 22 — One `var`: names are the only identity

Status: decided by the user 2026-08-22, overruling the two-stage `Term.ident`/`bindFree` design this lane had built (kept for reference on branch `dllbc-prog-parse-ident` @33ae9b82; nothing of it survives here). This document is the plan, the id-consumer inventory as actually found, the statement-identity decision, and the hygiene ruling. §7 is filled in per commit as built.

## 1. The decision

**One constructor.** `Term.pvar : String → Term` and `Term.var : Var → Term` become a single `Term.var : String → Term`. The `Var` structure loses its `id`. A variable occurrence is a name, and what the name means is decided **structurally, by scope**: an occurrence under an enclosing pure binder (λ/Π/Σ, a borrow type's snapshot binder, a ⇝-`let`) of that name is a pure variable — today's `.pvar` path; otherwise it is an Ω slot — today's `.var` path, and in a ⇒ position it is always Ω. σ's stay the reserved names `§σN` that `symOfName?` recognizes.

This is the rule the surface already applies — `resolveName` consults `pctx` first, then `rctx` — moved from the macro into reflection, where it belongs: a term's meaning should not depend on which binder-list the walker happened to hold when it emitted the node.

**Why the id could go.** The globally-unique runtime id was the identity for Ω lookup in the retired runtime-body grammar. M32 R1 made Ω resolve by NAME, newest wins (`findSlot?` never reads an id); R2 made `freeRVars` ask by name; R4 reduced the ids it still minted to two TAGS (`noSlot`, `declSlot`) and said of distinctness that it "bought nothing". What was left was (a) three consumers that keyed diagnostics by id, (b) the `fn` lowering's fresh-name supply, (c) two snapshot tables, and (d) a handful of tests pinning exact ids. §3 inventories them.

**What it buys.** A fragment written outside its binding context — a spec skeleton, a branch body, a generator pool — is a term with free names, and nothing more: `prog_parse { Take i (old *v) }` is `Take (.var "i") (old (.deref (.var "v")))`, and spliced under a header that binds `v`,`i` it IS the header's own term. No second constructor, no bind pass, no boundary resolution. The census's "open term" class (12 sites) stops being structural.

## 2. The `Var` that remains: a binder, with a kind

Occurrences are strings. **Binders** — `letIn`, `lam`, a match's equation binder, a branch's field binders — stay `Var`, and a `Var` keeps the one thing the name does not say: what KIND of binder it is.

```
inductive BinderKind | pure | slot | decl
structure Var where
  name : String
  kind : BinderKind := .slot
```

The kinds are exactly R4's two tags, named: `pure` is `noSlot` (a comptime λ binder: its argument lands in the comptime environment, not in Ω — `Var.bindsSlot`, which `Term.lamImperative` reads to decide whether applying the λ is ⇒-entry; `fn Identity (n : Nat) -> Nat { n }` is still entered), `decl` is `declSlot` (a `fn` statement's binding, which the harness projections `tailEnvs`/`moduleBinds` drop or select — "is this Ω entry a declaration?" has no other carrier, since `let F = (λ … : Π …)` and `fn F` are the same term by M28 θ), and `slot` is everything else. An enum is not an id: nothing compares, orders, offsets or mints one. `Coe String Var` gives `.pure`, so hand-written pure λs keep their spelling. Match scrutinees are occurrences, so `matchE : String → Option Var → List Branch → Term`.

The brief said to delete the `declSlot` tag; the enum keeps its QUESTION and drops the Nat. Recorded as the one place the design as briefed did not survive the inventory (§3 item 4).

## 3. The id consumers, as found

Found by grep before the compiler and confirmed by it. Per item: what it did, what replaces it.

1. **Statement breadcrumb keys** (`stmtKeyOf`, `noteStmt`, `Diag.stmtKey`, `PointDelta.stmtKey`, `SpanNote.stmtKey`; surface `spanOfLet`/`spanOfFn`/`tagOccsFrom`; `ElabCheck.spanFor`/`keyValues`; `Program.replayTo`/`replayEntry`). A `let`'s key was `.letIn ⟨id,name⟩ .unit`, unique by the id. §4 has the decision.
2. **Hover ledgers keyed `(id, name)`** (`Surface.OccNote.id`, `LetNote.binder`, `ElabCheck.letIndex`, `pointFactFor`, `factsAt`/`factsAtEntry`). The point-hover path replays to a STATEMENT key and then looks the name up in the replayed env newest-wins, so it needs only §4. The binder-granularity fallback (`letIndex`) joined an occurrence to its binder by id; by name alone a `let v` under a parameter `v` would answer with whichever entry came first. Replacement: a `LetNote` records the statement key it was filed under, the surface records on each occurrence the key of the binder it resolved to (the walker knows its scope; the entry is the binder's own statement key for a `let`, the match key for a pattern binder, `none` for a parameter), and `letIndex` keys by `(name, binderKey)`. Shadowing falls through, never guesses.
3. **Snapshot tables by id**: `St.entrySyms : (Nat × Nat)`, `exitSyms`, `borrowVarIds`, `resolveOldEntry`, `markExit`, `processArgs`' `inst`/`exits.lookup x.id`, `joinSym`'s per-slot `env.find? (·.1.id == kv.1.id)`. All by name; telescope names are distinct (asserted where the telescope is seeded, `seedTelescope`, if it is not already); the join's lookup becomes newest-wins like `findSlot?`.
4. **Tags and minting**: `noSlot`, `declSlot` (→ `BinderKind`, §2); `Uni.localId`/`fnSlotId` (→ a kind lookup in one scope list); the `next` counter threaded through the whole walker and every `⟨$(quote next), …⟩` quotation (→ deleted; `rctx`/`pctx` merge into one `List (String × BinderKind × Option key)`, innermost first, which is §1's rule stated as data); `patName next` / `scrutName` / `"__if"` (→ a fresh-name supply in the walker state for the reserved `§pN` pattern slots, since sibling nested patterns must bind DISTINCT names — `patName`'s docstring says why); `St.nextVar` and the seed's `maxNat ids + 1` (→ gone); `FnMacro.paramName x = "§p"++id`, `maxVarId`, `realId`, `base`/`base+1`/`base+2` minting for `hd`/`k'`/`ih` (→ `telePi` binds the parameter's OWN name, which makes `absVar` the identity and prints the Π as the header wrote it — the docstring's own wish; the step arm's minted binders are `hd`, `k'`, `ih`/`Ih` as names, taken from the body's own `match k` branch when it has one, exactly as now, and otherwise minted; `renameVar`, `resolveScrut`, `branchBinders`, `selfScrutArgs`, `hoist` compare names).
5. **Pins of exact ids**: Sugar.lean's goldens (30 `⟨n,"x"⟩` literals), KernelFloor (8 — its control-group role is rawness, not ids; updated mechanically), Functions (9), Direct (8), ArraySort (8), HashMap (5), Programs (3), Traces (2), ProbeModuleStates (1): `⟨i, "x"⟩` → `"x"` at occurrences, `Var.slot "x"`-style at binders. Messages that printed `x#id` print `x`.
6. **Equalities**: `Term.beq`: `.var x, .var y => x == y` (names; the `lam` row already compared names); `Term.alphaEq`: every `.var` goes through the binder stack (`bndPos?`), both free → same name; `convEq` likewise. `freePNames`/`freeRVars`/`symIds`/`substP`/`abstractInto`/`renumberSyms`: one namespace, so `substP x s` stops at ANY binder that rebinds `x` (λ/Π/Σ/borrowT as now, plus a `let`-headed `.seq` and a match's binders), and `freeRVars bound` treats every binder as binding its name — a pure `λ (N : Nat). … N …` no longer reaches an Ω slot named `N` from inside, which is §1's rule and the one observable change.
7. **Reflection and evaluation** — where §1's rule is decided. `reflectC`'s `lets : List Nat` becomes the list of names bound by the binders it has entered (it already walks under `.pi`/`.sigmaT`/`.lam`/`.borrowT` and the ⇝-`let` spine), and `.var x` is `.know (.var x)` when `x` is in it, an Ω read otherwise. `Pure.eval`: `.var x` is `ρ.lookup x`, else a free name means itself (`Sem.pvar`) — an Ω slot never reaches `eval` unresolved, since `reflectC` read it. `letName id` is gone; a ⇝-`let` binds its own name in ρ. `Term.sym σ = .var (symName σ)`; readback mints `.var "§N"`.
8. **`Term.imperative`** named a `.var`-headed spine as ⇒-entry because a `.var` head was an Ω SLOT. A pure-bound head (`λ (P : Π…). P x`) is the same node now, so the classifier carries the pure binders it is under and a spine whose head is pure-bound stays comptime. This is the one traversal that must know binder kinds, and the reason `.pure` is a kind rather than a surface-only fact.
9. **The lowercase constants** (`k`, `j`, `natRec`, …, `Dllbc.constNames`). Inline, a binder named `k` beats the `Id` eliminator because the walker looks the binder up first; a fragment has no binder to find. Rule: in parse mode a lowercase constant name that resolves to nothing is emitted as `.var "k"`, and the three `.var` resolvers — `reflectC`, `readR`, `Pure.eval` — treat an UNBOUND name in `constNames` as the constant. Scope beats the table, decided where the scope is known. Direct-to-normalizer sites (`pv prog_parse { arrCat … }`) are covered by `eval`'s row.

## 4. Statement identity: the term, with the right-hand side, and no guessing

Keys stay TERMS. Every alternative was measured against three constraints the current design meets and the brief asks to preserve: (i) a statement inside a match arm is walked once per path and its key must be the same on every path, (ii) the surface files a key before the program is assembled — a `%` splice inserts statements the surface never numbered — so a key cannot depend on the statement's position in the final term, (iii) docs/20 persists keys across modules (`SpanNote.stmtKey : Term`). A walk ordinal fails (i); a source ordinal fails (ii) the moment a fragment is spliced; a boundary-numbered site in the node (the `seal` precedent) fails (ii) for the surface's half of the join. A term key meets all three by construction — it is what `stmtKeyOf` is.

What the id gave a `let` key was uniqueness. The replacement: **a `let`'s key is its binder AND its right-hand side**, `.letIn x rhs` — the shape `assign`'s key already has (`.assign p rhs`). A `fn` statement's key stays the binder alone (`.letIn ⟨F, .decl⟩ .unit`): the name is what Ω resolves it by, and its right-hand side is the whole lowered body. Two statements with the same key are the same statement written twice, which `spanFor` already reports ("this statement is written more than once") and which `replayTo` must now DECLINE rather than answer with the first: when a key is filed under more than one run on a path, the point is ambiguous and the tooltip falls through to the binder fact or to nothing. That is docs/17's own rule, applied to one more case.

## 5. The surface

`prog{ }` is unchanged in meaning: every name resolves or it is an error at Lean elaboration, at the identifier, with its span — the walker still knows its scope. `prog_parse { }` — main's parse-stage brace since `7703efee` — is the same walker without that assertion: a name that is not a binder in scope, a constructor, a constant, an alias or a Lean-level `Term` is `.var name`, nothing else. The walker keeps ONE scope list instead of `rctx`/`pctx`, and reads a binder's kind only where the emitted term differs by it: `f(a)` on a `slot` head is the app spine, on a `decl` head stays `.call` for `retarget`; `match x` refuses a head that is not a slot; hover occurrences file for slots.

The boundary asserts closedness: `atBoundary` rejects a program with a free name (`Term.freeVars`, minus σ's, minus constants, minus the names a module seed binds) with the unbound-identifier message, by the `fnElabOrFail` precedent — a term the machine refuses distinctively, reached because it is the program. That is what catches a fragment spliced where nothing binds its names, including in a branch the walk never takes.

## 6. Hygiene ruling

**Fragments are unhygienic on purpose.** A name a fragment does not bind means whatever that name means where the fragment lands — which is the whole point: "the `hd` this match will bind" is said by writing `hd`. Inside the fragment, scope is lexical as everywhere else: a fragment's own `let hd` binds its own `hd`, and the splice site's `hd` never sees those occurrences. Lexical inside, dynamic at the edge; and it takes no mechanism at all, because a fragment is a term with free names and the splice is substitution. Closed programs are unchanged.

## 7. As built

(Per commit.)

### 7.1 Conversions (the census's non-twin open-term sites)

| site | raw form | converted to | witness before deletion |
|---|---|---|---|
| (filled in per commit) | | | |
