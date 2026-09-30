# 07. Editor tooling: checking at elaboration, located errors, hovers

Written 2026-09-30 by team-lead, at the user's request:
> 1. the type checking is done at elaboration time whenever the `ochr` macro is invoked
> 2. errors are localised to the syntax which had the error. e.g. if a function is passed an invalid argument, the argument is underlined with "type error: ..."
> 3. on cursor hover over an identifier, information is shown. the majority of the time this is its value in the abstract environment Ω. this should remove the need for the #guard's since the macro is doing itself.

## Where things stand
- `ochr Name uses … { … }` (`Ochr/Notation.lean`) expands to a `def Name : Block` plus `#ochr_check Name`. That only checks name clashes. The actual checking happens later, in `#eval (run "Name" Name).show` and `#guard (run …).allAsExpected` lines in each examples file, and in `lake exe tests`.
- Surface terms are built by `elabTerm`, which produces Lean syntax for `Term` values, so source positions are thrown away. Errors are strings naming a declaration, not a location.
- `lean_lib Ochr` has no `precompileModules`, so anything the elaborator runs (`#eval`, `evalConst`) runs the checker interpreted.

## What to build, in order (each phase lands on its own)
1. **Check at elaboration.** `#ochr_check` runs the checker on the block, with its `uses` blocks, at elaboration.
   - An accepted `def` is silent.
   - A rejected `def` is an error on that declaration.
   - A `reject def` that is rejected is silent. Hovering it shows the rejection message, so a negative test still shows *why* it is rejected.
   - A `reject def` that is accepted is an error: "expected rejection, but accepted".
   - Make the checker native at elaboration (`precompileModules`, or an equivalent), and measure build time before and after.
2. **Located errors.** Every type or machine error is reported on the smallest piece of source responsible. Examples:
   - an ill-typed argument underlines the argument;
   - a borrow error underlines the access that broke exclusivity;
   - a repack failure underlines the whole-again point;
   - a failed `refl` underlines the `refl`, with the two normal forms that differ.
   This needs source positions carried from the syntax into the checker. Choose the design that keeps the diff small in `Machine.lean`/`Check.lean`, because three other agents are editing those files: examples-tour, rule-audit and dep-fields. For example, a wrapper node or a side table keyed by node, plus an "innermost located term" stack in the evaluator, so error sites need no edits. Write the design down before building it.
3. **Hovers.** Hover over an identifier or place shows its content in Ω *at that program point*. When the point is checked several times, it shows each case, labelled:
   - once per [Split] arm (`x ↦ Z` in one arm, `x ↦ S σ₂` in the other);
   - at the generic call versus an instance.
   It also shows the declared type and, for a borrow, where it points. Hover over a call shows the rule the checker applied, by the paper's name ([Call], [Close] …). Use rule-audit's `Rule` tags (`Ochr/Rules.lean`, `fire`) once they land; this is the "derivation in the paper's names" the user asked for earlier. Hover over a proof term shows the goal it was checked against, as a normal form.
4. **Holes.** A `?` (or `sorry`) term that is reported as a warning showing the expected type (the goal) and the relevant Ω, like Lean's goal view. This is what makes writing a proof in Ochr practical, and the agent-effort benchmark's Ochr condition (docs/05) depends on it.

## What stays
- `lake exe tests`, the ledger and the fuzzer still run blocks programmatically under other configs, so `run` and `Block` stay.
- The per-block `#guard`s go, except one declaration-count check per block (in the registry or the macro). A truncated file compiles green, and the count is what catches it.

## Acceptance
- Every examples and case-study file builds with no `#guard`s beyond the counts.
- A deliberately broken copy of an example shows the error on the right token. Check with the lean-lsp tools: `lean_diagnostic_messages` for errors, `lean_hover_info` for hovers.
- Hovering in `02Borrows.lean` and `17HashMap.lean` shows Ω contents, per-arm values and rule names.
- A `?` hole in a lemma shows its goal.
- The build takes no longer than it does now.
- `notes/lean-checker.md` gains a short "using the checker in the editor" section.
