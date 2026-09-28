# Breaker report v1: loans-as-variables, [Def]/[Call-type], P5, non-tail close-off, owner sets, canonicity

## 5-line summary

- **Verdict:** No closed `⊥` and no closed `Id Nat Z (S Z)` against v1. Every round-1 exploit I re-ran is now blocked, and the four meta-model/e346 `⊥`s (C1–C4) stay closed. v1 is the first version I could not break. But two things are *stated* wrongly even though their conclusions hold, and two are *spec gaps* an implementer can get wrong.
- **Most important finding:** D11's `[End]` "no side condition" **invalidates the written proof of canonical observation (T1a)** — that proof relies on "`end ℓ` is enabled only when ℓ's content is loan-free", which v1 deliberately dropped. The *conclusion* (ending is confluent) still holds, but for a different reason (ending is now an acyclic **substitution** system, confluent by hereditary-substitution/Newman, not by the loan-free premise). T1a must be re-proved on that basis, and it is actually *cleaner* under D11, not more fragile.
- **What must change (text, not soundness):** (1) restate T1a for substitution-confluence; (2) §3 "Stuck blocks" close-off lists "borrow variables it uses and places it writes" as borrow arguments but **omits places that appear under `&_`** — the same "appears under `&_`" the footprint §4 already has; add it, and say a place borrowed/written in *any* arm is a borrow argument (value arguments are read-in-all-arms, borrowed/written-in-none); (3) enforce "closures capture no borrows" at Π-type formation, or D13 leaks; (4) note that under D16 `Eq Nat Z (S Z)` is a *stuck* proposition, not `⊥` — still uninhabited and still refutable by large elimination, so the must-fail goals stay must-fail, but the report should say *why* they fail (uninhabited-stuck), not "≡ ⊥".
- **Confidence:** High that the six targeted new mechanisms have no first-order bug in scope (Nat/Unit, tree borrows). Medium on canonicity-with-holes: the pure-end part is solid, the hole part reduces to T5 (naturality) which is unproven; I could not build a differing schedule.
- **What I did not check:** the Lean formalisation; multi-field data and shared borrows (out of scope, D8); decidability/termination of the checker; whether D16's trimmed `Eq` breaks any *wanted* proof (that is the derivers' job, not soundness).

## Attack roster (one line each)

1. (a) Reborrow survives its parent's `[End]` and aliases a new borrow — BLOCKED: substitution relocates a *single* loan; [Access]'s inside-content clause ends any conflict. T1a's stated proof is wrong for v1; conclusion holds.
2. (f) Two loan-ending schedules with different observations — NO BREAK: pure ends confluent by acyclic substitution (3-borrow trace); hole case reduces to T5, unproven, no counterexample.
3. (c) P5: effectful proof `Seven`, and the old C1 `Boom` via `J`/transport — BLOCKED: `Boom` collapses to `⊤ → ⊤`; an effect-asserting proof cannot even be *defined* (snapshot goal); erasure keeps checker = runtime.
4. (b) [Def]/[Call-type] + D13 capture: `Oops2` re-read after mutation — BLOCKED by value-capture; borrow-capturing Π-type `Oops3` — excluded by "closures capture no borrows" **iff enforced at formation** (gap 3).
5. (e) Owner-set footprint D18: `Pick`/`Bad` re-derived under v1 — BLOCKED (both owners observed; `h refl` unprovable). Interacts with D16: the false equation is now *stuck*, not `⊥`, but still unprovable, so the block holds.
6. (d) Non-tail close-off free-place classification — SPEC GAP (gap 2): a place under `&_` in an arm is neither a "borrow variable" nor a "written place"; natural reading (borrow it) is sound, literal reading leaves the sealed program open.
7. (d) Arms borrow different places and return them (`Pick`), then the continuation ends the returned borrow — BLOCKED: single live `borrow_k`; the two `?k` occurrences are owner-side loans, not two writers.
8. (D16) Must-fail `Id Nat Z (S Z)` under trimmed `Eq` — still uninhabited (stuck; only `refl : ⊤`); consistency of this goal survives the trim.
9. Fire triangle re-confirmed under P5 + D16 — still the CBV/restricted-substitution corner; large-elimination refutation of false Nat equations is retained, so no accidental weakening.
