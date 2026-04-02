# Long-term proof strategy: Och → Ochr → Ochre

Literature review (see `docs/research/`) establishes a clear proof strategy
for the full Ochre roadmap. Key finding: **ownership-disciplined mutation
does not require separation logic.** Every project restricting to safe Rust
(Oxide, Aeneas, Creusot, Patina) avoids it; every project handling unsafe
code (RustBelt, RustHornBelt, RefinedRust) requires it.

## Och (current): pure, no mutation
- **Proof technique:** Fuel-indexed `ValSub` (step-indexed LR)
- **Key challenge:** Equi-recursive mu types + contra-domain subtyping
- **No separation logic needed** — no heap, no mutation

## Ochr (next): ownership + immutable borrowing
- **Proof technique:** Extend `ValSub` with ownership tracking in the
  environment. The heap is a tree of owned values (no aliasing), so no
  separate heap model is needed. Aeneas confirms this works for broad
  safe Rust (ICFP 2022).
- **Key challenge:** Strong mutation — updating a variable's type after
  assignment. This is where dependent types interact with mutation.
  Aeneas's "backward functions" solve this via functional translation;
  Ochre keeps mutation native, so the type system must track it directly.
- **No separation logic needed** — ownership makes the heap tree-shaped.

## Ochre (final): mutable references + concurrency + unsafe
- **Proof technique:** For safe code, same as Ochr. For unsafe primitives
  (`RefCell`, `Mutex`, `Vec` internals), Iris-style separation logic is
  needed — but ONLY for those primitives. User code verified without it.
- **Key challenge:** Bridging the safe/unsafe boundary. RustBelt solved
  this for Rust; Ochre would need an analogous semantic soundness argument.
- **Separation logic needed** — but confined to unsafe primitive impls.

## Why this progression works

The `ValSub` relation from Och extends naturally:
- Och: `ValSub n v τ` — value inhabits type for n steps
- Ochr: `ValSub n env v τ` — value inhabits type given owned environment
- Ochre: `ValSub n world v τ` — value inhabits type in a world (for unsafe)

Each stage adds a parameter but preserves the core framework. The step-index
monotonicity lemmas, compatibility lemmas, and fundamental theorem structure
carry over. This is why step-indexed LR was chosen over checker-based or
coinductive approaches — it's an investment in infrastructure that pays off
across the entire roadmap.

## Research references

- `docs/research/equi-recursive-subtyping-lit-review.md` — 21 papers reviewed
- `docs/research/amin-rompf-deep-dive.md` — Amin-Rompf technique analysis
- `docs/research/aeneas-analysis.md` — Aeneas comparison + ownership vs sep logic
- `docs/research/magmide-analysis.md` — Magmide comparison + lessons learned
