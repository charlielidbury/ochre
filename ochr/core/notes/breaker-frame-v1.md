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

---

## Attack 1 (a) — exclusivity under loans-as-variables, no-side-condition [End]

D11 makes a loan a variable bound by its borrow, and [End ℓ] a plain substitution with **no** side
condition: `borrow_ℓ v ↦ ⊥`, `loan_ℓ ↦ v` everywhere. Aeneas's End-Mut required `v` loan-free (end
inner borrows first). The attack: end a *parent* borrow while a child reborrow is live, hoping the
child survives and comes to alias a fresh borrow (two live writers of one cell).

Chain `c` reborrows `*b` reborrows `a`:
```
a ↦ loan_m        b ↦ borrow_m (loan_n)        c ↦ borrow_n v
```
End the parent `m` first (no side condition lets us, though its content holds `loan_n`):
```
[End m]:  b ↦ ⊥,  substitute (loan_n) for loan_m  ⟹  a ↦ loan_n,  b ↦ ⊥,  c ↦ borrow_n v
```
Now `c` is live and its loan sits at `a`: **c has become a direct borrow of a**. This is correct
reborrow semantics, and crucially `loan_n` occurs in exactly **one** place (`a`), because the
substitution replaced the single `loan_m` occurrence. To "alias something new" I must make a *second*
live borrow reference the same cell. Two routes, both blocked:

- **New borrow of `a`.** `&a` runs [Access] on `a`: "before borrowing `p`, end every borrow whose
  loan occurs inside `content(p)`". `content(a) = loan_n`, so [Access] ends `c` first (`c ↦ ⊥`,
  `a ↦ v`), then `&a` loans a fresh cell. No two live borrows; a later use of `c` reads `⊥` (error).
- **Duplicate the loan.** The only way `loan_n` reaches two owned places is the duplicated-hole case
  (a returned borrow from a multi-borrow call, D18). But that is one hole `?k` for one borrow `k`
  occurring in two *owners* (loan positions), filled together when `k` ends. There is still exactly
  one live `borrow_k` (held by the result). Two owner-side occurrences of `?k` are not two writers;
  they are "two owners whose final content depends on `k`'s final value." No aliasing.

**Outcome: BLOCKED, and D11 is actually more robust than Aeneas here.** Because ending is
substitution, a loan can never split: `[End ℓ]` replaces each `loan_ℓ` occurrence by the one value
`v`, and `[Access]`'s inside-content clause (D19/C5) ends any borrow before a conflicting access.

**But T1a's written proof is invalid for v1.** meta-model T1a argues ends commute because
"`end ℓ` is enabled only when ℓ's content holds no loan/hole, so it does not contain `h_ℓ'`." Under
D11 there is no such enabling condition — I just ended `m` with `loan_n` inside its content. The
right proof: ending is a set of substitutions `loan_ℓ := v_ℓ` on an **acyclic** dependency graph
(I3), and a system of acyclic substitutions is confluent and terminating (hereditary substitution /
Newman). The conclusion `ρ_Ω` well-defined survives; the stated reason does not. This should be fixed
in the metatheory text, and it makes T1 *easier*, not harder.

---

## Attack 2 (f) — two loan-ending schedules, different observations

The flagged top risk. I tried to build a schedule dependence. Pure (non-hole) ends first, three
nested borrows, ending in both orders (continuing Attack 1's chain, now resolving fully):

Schedule A (`m` then `n`): `a ↦ loan_n, c ↦ borrow_n v` → `[End n]` → `a ↦ v`.
Schedule B (`n` then `m`): `[End n]` gives `b ↦ borrow_m v` (n's loan was inside b), then `[End m]`
gives `a ↦ v`. **Same result `a ↦ v`.** In general, one-way dependence (`v_ℓ` mentions `loan_ℓ'`,
not conversely) gives, in either order, `loan_ℓ ↦ v_ℓ[loan_ℓ' := v_ℓ']`; mutual dependence is
forbidden by I3. So pure-end resolution is order-independent by substitution confluence. **No break.**

The hole case is where canonicity is genuinely open. `[End k]` for a returned borrow does *not* just
substitute: it substitutes the written value `w` for `?k` in the sealed programs **and
re-normalises** (re-runs them). So canonicity of two hole-ends `k`, `k'` needs
"substitute-`w`-then-normalise" to commute with "substitute-`w'`-then-normalise". That is exactly
naturality of the normaliser under refinement — meta-model's T5 — which is **unproven**. I attacked
it two ways:

- **Overlapping targets.** For the schedule to matter, re-normalising after filling `?k` must change
  what filling `?k'` produces. That needs the two returned borrows to write cells whose final
  contents interfere. But two *live* mutable borrows into overlapping cells are impossible ([Access]
  exclusivity, Attack 1), so `k` and `k'` write disjoint cells; their sealed programs mention
  disjoint holes; filling one leaves the other inert ([Seal]: "a loan whose borrow is outside the run
  is inert"). Disjoint substitutions on a confluent normaliser commute. No break found.
- **Re-normalisation spawning a new hole.** Filling `?k` with a constructor can make a match inside
  the sealed program fire and [Close] an inner call, minting a fresh hole `?k''`. I could not make
  `?k''`'s owner set depend on the fill order, because the inner call's borrow arguments are
  determined by the (deterministic) sealed run, not by when `k'` ends.

**Outcome: NO BREAK, but not closed.** Canonicity holds for pure ends unconditionally; for holes it
is exactly T5, and T5's own hardest case (returned-borrow [Close] under a completing refinement) is
the one meta-model flags for mechanisation. I still bet the residual risk lives here, but I have no
counterexample, and the structural argument (disjoint holes, deterministic seals) is fairly strong.
Recommend: mechanise `AddM'`/`TailM` resolution first, as both round-1 and the meta-model say.
