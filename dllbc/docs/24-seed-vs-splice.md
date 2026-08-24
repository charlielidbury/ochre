# 24 — A seed binding and a spliced constant are not interchangeable

**Status: settled by measurement, 2026-08-24, on branch `retire-aliases`.**

This note exists to stop a specific good idea. The idea is "bind the standard library into `Dllbc.std` and let every consumer resolve its names from the seed, instead of splicing constants at the use site" — which reads like pure tidying, has an obvious readability payoff, and does not work. It was tried, it fails in four independent ways, and the reason is not incidental: **a splice and a seed binding are different judgments**, and the library's existing 26/10 split was already tracking that difference.

## 1. The two mechanisms

A surface name in a `ty{ }` / `prog{ }` block resolves one of two ways.

* **Spliced constant.** The name resolves to a Lean constant holding a `Term` (`Dllbc.Std.Le`, `Dllbc.StdChainRaw.CountAconsCongrRaw`). What lands in the emitted term is the λ itself — a **pure literal, lifted under ⇝**.
* **Seed binding.** The name is bound in the module state the block is seeded from (`let Le = …;` inside `prog (…) { }`), so it resolves to `.var "Le"` against an Ω entry. Using it is **⇒-application of a bound value**.

`Surface.resolveName` consults scope first, so a seed binding shadows everything. That is what makes the swap look free: the same source text, a different rung, apparently the same term.

## 2. What seeding actually buys, exactly

`StdChain.lean`'s header already states it, and the sentence is precise in a way that is easy to read past:

> a seed binding cited in a **type** reduces

Types. Not bodies. The evaluate-by-environment path reduces an Ω-bound former where it appears in a type, which is what a consumer needs to state a spec. It says nothing about applying that former to a symbolic runtime value inside a `fn` body, and that is the case that breaks.

## 3. The four breakages

Measured against `origin/main` f1b8efbc, one variable at a time, full `lake build` each time.

**(a) All ten former aliases bound in `std` — three real rejections.**

```
Tests/Arrays.lean:1309  (sort2)      applyR: natRec is stuck on a symbolic scrutinee (σ₃₃₁₄)
Tests/Direct.lean:445   (splitOffM)  applyR: natRec is stuck on a symbolic scrutinee (σ₃₃₁₂)
Tests/Direct.lean:1109  (qsM)        applyR: natRec is stuck on a symbolic scrutinee (σ₃₃₂₁)
```

The offending expressions are `Leb x y` as an `if` condition, `Take i2 (*tl)`, and `let lr = Len rest;`. Each is the library function applied to a symbolic runtime value inside a body. The full message names the rule:

> Applying a recursor at a symbolic scrutinee is arms-as-bodies CHECKING (§7 cost 1) — reachable through a seal, not through a call.

This is the same argument docs/20 §5 records for the raw proof terms, which is why none of the 110 `XRaw` constants are bound either. It was written about proofs; it is a statement about **any** Ω-bound value that is applied.

**(b) Only the Type-valued three (`Le`, `Bound`, `Sorted`) — still rejects.**

```
Tests/Direct.lean:1261  (qsM)  readC (⇝): a call is not in the comptime fragment
```

at a `Sorted Z0` inside a pure λ (`let Fin = (λ (E : List Nat). … ListRwRaw (λ (Z0 : List Nat). Sorted Z0) …)`). So "predicates are safe because they only appear in types" is false — a type can appear inside a pure λ in a body, and that position reads differently.

**(c) Only `Le` — the suite compiles, and two assertions flip.**

```
Tests/Programs.lean:2380   impLams qsFlagshipT = 22                                   → false
Tests/HashMap.lean:6505    progRejectsFrom hmM (hmGmUnder …) "does not have its …"    → false
```

A structural count over the emitted term, and a pinned rejection message. Both see the difference because there genuinely is one: the splice puts the whole λ into the term and the seed binding puts a `.var` there.

**(d) Binding early in the chain — does not compile at all.**

`Le` alone bound in `std0` rather than the final link:

```
StdChain.lean:1636  (SplitA1Head)  readC (⇝): a runtime λ is not in the comptime fragment
```

So the alternative the header prices in build time is not a build-time trade-off. It is a build failure.

## 4. The line is a USAGE line, not a typing line — which is the trap

The obvious rescue is a rule: "Type-valued formers may be seeded, data-valued ones must be spliced." It does not survive contact with the corpus in either direction.

* `Append`, `Mul`, `Mod`, `Div`, `NthL`, `Set`, `SwapL` are data-valued and **are** seed-bound today, without trouble.
* `Sorted` is Type-valued and breaks (§3b).

The actual predicate is *"is this name ever applied to a symbolic runtime value, or cited inside a pure λ, anywhere in the corpus?"* — a property of the call sites, not of the definition. The 26 formers that are bound are exactly the ones for which the answer is currently no. The ten that were aliases are exactly the ones for which it is yes.

**That is why a mixed regime must not be shipped.** A vocabulary in which `Le` is a seed binding and `Leb` is a spliced constant, both spelled the same way in the same block, contains a landmine: the first program to apply `Le` in a body fails with a message about ι-reduction at a symbolic scrutinee, pointing at a recursor, naming nothing the author did wrong. And the property is not stable — "only cited in types" is true of today's corpus, not of the language, and new programs are being written against this vocabulary now. Uniform splicing is worse in printed goals and better in every other respect.

## 5. What would have to change for seeding to be universal

Not a resolution change — a kernel one. The refusal is `applyR`'s: a recursor stuck on a symbolic scrutinee is refused under ⇒ because arms-as-bodies checking is reachable through a seal and not through a call. To make an Ω-bound library function behave like a spliced one, ⇒-application of a bound *pure literal* would have to be allowed to fall back to the ⇝ reading — i.e. the machine would need to distinguish "an Ω entry whose value is a closed pure term" from "an Ω entry that is a slot or a sealed declaration", and treat the first as a splice. That is a real design question with a real payoff (§6), and it is not a refactor; it belongs in its own lane with its own soundness argument.

## 6. The readability win is real, and it is a printer problem

The motivation was not idle. An alias splices the entire λ body into the printed goal, so a type mentioning `Count`, `Le` and `Sorted` prints as three unfolded recursors; a seed binding would have printed three names. That is a genuine, daily cost.

But it is a cost in the **printer**, not in resolution. The term is the same term either way; what differs is that a `.var` has a name to print and a λ does not. The fix that does not touch the judgment is a print-time abbreviation table: when rendering a `Term`, replace any subterm α-equal to a known library constant with that constant's name. It needs a reverse index built once over `Dllbc.Std` plus `StdChainRaw`, and it changes nothing about what the kernel does. Filed here rather than done, because it is a separate lane.

## 7. What was done instead

`Surface.aliasMap` was deleted and nothing replaced it. The table only ever bridged a NAME to a SPELLING (`Le` ↦ `Dllbc.Std.LeFnT`), so `Dllbc.Std`'s constants were renamed to their surface names — `Le`, `Eqb`, `Leb`, `Len`, `Count`, `Bound`, `Sorted`, `Take`, `Drop`, `Add`, `Append`, one constant each — and exported into `Dllbc`. They now arrive down `resolveName`'s ordinary Lean-identifier fallthrough, like `SwapL` and `Set` always have. Emitted terms are byte-identical, ~1500 use sites needed no edit, and the rule "below `Std` you splice the kernel constants" is now enforced by the import graph rather than by memory.
