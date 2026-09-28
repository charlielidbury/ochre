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

---

## Attack 3 (c) — P5 "proofs are not run"

D14/P5: a call whose result type is a proposition is not run; it returns `⋆` and its borrow arguments
come back unchanged. Three probes.

**(i) The old C1 `Boom` collapses.** With `P₁ x := ⟨⟩`, `P₂ x := (*x := 7; ⟨⟩)`, both
`: Π(x:&Nat). ⊤` (a `Prop` again under P5), and `F h := Id Nat (let a = 0; h &a; a) 0`:
```
F P₁ :  let a = 0; P₁ &a; a       P₁ &a is a proof call ⟹ not run, a unchanged = 0 ⟹ result 0 ⟹ Eq Nat 0 0 ≡ ⊤
F P₂ :  let a = 0; P₂ &a; a       P₂ &a is a proof call ⟹ not run (its *x:=7 erased), a = 0 ⟹ Eq Nat 0 0 ≡ ⊤
```
So `F P₁ ≡ F P₂ ≡ ⊤`, and `J (λg _. F g) ⟨⟩ (refl : Eq _ P₁ P₂)` proves `⊤`, not `⊥`. The v0 bug
needed `P₂ &a` to actually write `a`; P5 stops it. **BLOCKED.**

**(ii) An effect-asserting proof cannot be defined.** To exploit erasure I would want a proof whose
*statement* depends on its own body's write. Try `Bad : Π(x:&Nat). Id Nat (*x) 7`, body
`*x := 7; refl`. [Def] evaluates the goal at the generic call `{c ↦ σ, x ↦ &c}`: `W = {c}`,
`⟦*x⟧ = (σ, σ)`, `⟦7⟧ = (7, σ)`, goal `≡ Eq Nat σ 7 ∧ ⊤ ≡ Eq Nat σ 7` (stuck). The body's `*x := 7`
does not change the *snapshot* goal (D2/P2); `refl : ⊤` cannot inhabit `Eq Nat σ 7`. **REJECTED at
definition.** The variant `Id Nat (*x := 7; *x) 7` is rejected by effect-sensitivity: `⟦*x:=7;*x⟧`
resolves `c = 7` but `⟦7⟧` leaves `c = σ`, so the goal is `Eq Nat 7 σ`, stuck. You cannot write a
proof that certifies its own hidden write.

**(iii) Erasure keeps checker = runtime.** At runtime `Prop` is erased, so a proof call genuinely
does nothing; the checker also treats it as doing nothing (P5). No checker/runtime disagreement — the
v0 adequacy hole (a Prop-valued function whose write happened at runtime but not in the checker, or
vice versa) is closed in both directions. `Twice`/`TwiceMZero` now check by the natural induction
(e346 F8). **Sound.**

One thing to verify in the text: P5 keys on "result type is a proposition." A mixed result like
`Π(x:&Nat). (⊤ × Nat)` is a `Type` (it carries data), so it is **not** erased and its writes *do*
run — correct, but the rule should say "a proposition" means a type in `Prop`, decided by the sort of
`B`, so `⊤ × Nat` (a `Type`) is never mistaken for erasable.

---

## Attack 4 (b) — [Def]/[Call-type] and D13 value-capture

**Oops2 re-read (C4/e346 F5).** `Oops2 x h := (x := S x; h())` with `h : Π(_:Unit). Id Nat x Z`.
D13 makes the Π-type a closure over formation-time values: `h`'s type captures `x`'s value `σ_x` when
`h` is introduced, so `h() : Id Nat σ_x Z`, **not** `Id Nat (S σ_x) Z`. The write `x := S x` cannot
retro-change `h`'s type. `[Call-type]` rebinds only parameters (here the `_ : Unit`), never the
captured `σ_x`. **BLOCKED.**

**Borrow-capturing Π-type (new probe).** Push on the capture: can a Π-type close over an external
*borrow*, so its snapshot desyncs from a live borrow?
```
Oops3 : Π(x : &Nat) (h : Π(_ : Unit). Id Nat (*x) Z). ...
```
Here the inner Π `Π(_:Unit). Id Nat (*x) Z` mentions `x`, a borrow parameter of the outer Π, free in
the inner one. Forming it would capture a borrow. RULES §1 scope says **"closures capture no
borrows"**, and P2 says a Π-type *is* a closure, so `Oops3` must be **rejected at the formation of
the inner Π-type**. That closes the attack — *provided the check is actually performed at
Π-formation*. RULES states the restriction but no rule enforces it; e346/round-1 both assumed it.
**Recommendation (gap 3):** make "a Π-type may not capture a borrow-typed free variable (only its own
borrow parameters)" an explicit formation error. Note this does *not* forbid the good cases: in
`AddMZero : Π(x:&Nat). Id Unit (AddM x 0) ()`, `x` is the Π's *own parameter*, rebound by
[Call-type] at each call — not a captured free variable.

Even under the leaked reading (capture allowed, treated as a value snapshot `borrow_ℓ σ`), the type
is a closed statement about `σ` (D2), so it does not by itself give `⊥`; the danger is purely that
runtime scope (a captured borrow outliving its owner) is violated — an adequacy/memory-safety issue,
not internal inconsistency. Still worth the one-line formation check.

---

## Attack 5 (e) — owner-set footprint (D18), re-derived under v1

The C2 exploit, re-run under v1's rules (`Pick` returns `x1` or `x2` by `n`; `G` refutes
`Id Unit (*z := Z)(*z := S Z)` at entry):
```
Bad n a b := let r = Pick n &a &b; let h = G r; match n { Z => refl | S m => h refl }
```
`[Close]` of `Pick` (result `&Nat`) fills **both** loans with the same hole `?k`:
`a ↦ A(?k) = ⌈…; *r' := ?k; c₁⌉`, `b ↦ B(?k) = ⌈…; *r' := ?k; c₂⌉` (D18/e346 F11). Typing `G r`
before the split: `owners(k) = {a, b}` (D18 owner *set*), so `W' = {a, b}` and
```
h : Π(e : Eq Nat A(Z) A(S Z) ∧ Eq Nat B(Z) B(S Z)). ⊥
```
In the `S σ_m` arm, `Pick (S σ_m)` returns `c₂`, so `A(w) ≡ σ_a` (a untouched) and `B(w) ≡ w`. Thus
```
h : Π(e : Eq Nat σ_a σ_a ∧ Eq Nat Z (S Z)). ⊥  ≡  Π(e : ⊤ ∧ Eq Nat Z (S Z)). ⊥  ≡  Π(e : Eq Nat Z (S Z)). ⊥
```
`h refl` needs `refl : Eq Nat Z (S Z)`; `refl : ⊤` only, and `Eq Nat Z (S Z)` is not reflexive.
**`h refl` REJECTED**, so `Bad`'s `S` arm cannot be completed. **BLOCKED by D18.** Single-owner
(`W' = {a}`) is what let v0 prove `⊥`; observing the set closes it.

**Interaction with D16 (worth noting).** D16 dropped Nat injectivity/disjointness from `Eq`, so
`Eq Nat Z (S Z)` no longer computes to `⊥` — it is a *stuck* proposition. This does **not** reopen
the exploit: `Eq Nat Z (S Z)` is still uninhabited (unprovable), so `h refl` still fails, and the `S`
arm's own goal `Id Nat (S σ_m) Z ≡ Eq Nat (S σ_m) Z` is likewise stuck-unprovable, so `Bad` is
rejected regardless. The report language should be "the needed equation is uninhabited," not
"reduces to `⊥`" — the mechanism is uninhabitation, and it survives the D16 trim.

---

## Attack 6 (d) — non-tail close-off free-place classification (SPEC GAP)

D15 closes a stuck non-tail match as "an anonymous function of its free places: **borrow variables it
uses and places it writes** become borrow arguments, places it only reads become value arguments."
Consider arms that *borrow* an owned place:
```
r = match b { Z => &a1 | S _ => &a2 };  ...        -- a1, a2 owned locals/params
```
`a1`, `a2` appear under `&_`, but they are **owned variables**, not "borrow variables it uses", and
`&a1` is **not** a write. So the literal rule classifies neither `a1` nor `a2` as a borrow
argument — yet the anonymous function must take them as borrow arguments, or the returned borrow
`&a1` references a free variable and the sealed program `[Close]` builds is **not closed** (violating
the invariant that sealed programs are closed). The footprint §4 already gets this right ("every free
place that appears **under `&_`**, on the left of `:=`, or is a borrow-typed variable"); §3's
close-off wording simply omits the `&_` clause.

**Outcome: SPEC GAP, not a `⊥`.** Under the natural reading (a place borrowed in any arm becomes a
borrow argument) the close-off is sound and reproduces `Pick`. Under the literal reading the checker
either rejects a valid program or builds an open sealed program (undefined). Fix: align §3's
free-place rule with §4's footprint — *a place that appears under `&_`, on the left of `:=`, or is a
borrow-typed variable in any arm is a borrow argument; a place read (never borrowed/written) in all
arms is a value argument.* Second half matters too: a place read in one arm and borrowed in another
must be a borrow argument (a per-arm classification would borrow a *copy*, and writes through the
returned borrow would miss the real place — a dangling/adequacy bug).

---

## Attack 7 (d) — arms borrow different places, then the continuation ends the returned borrow

`Pick n &a &b` returns `borrow_k V` with `?k` in both `owners(k) = {a, b}`. Push past typing into the
*continuation*: `let r = Pick n &a &b; *r := S Z` — end/write the returned borrow, and check nothing
aliases.
```
after [Close]:  r ↦ borrow_k V,  a ↦ A(?k),  b ↦ B(?k)              -- one live borrow_k
*r := S Z:  [Access] on *r ends nothing new (V holds no conflicting loan); write ⟹ r's content S Z
end k (drop r):  ?k := S Z into both A, B and re-normalise
  A(S Z) = (Pick n returns c₁ ⟹ c₁ := S Z ⟹ a's final content depends on n)
  B(S Z) = (Pick n returns c₂ ⟹ c₂ := S Z)
```
There is exactly **one** live writer of the returned cell (`r`/`borrow_k`); `a` and `b` hold the
*hole* `?k` (owner-side loans), not a second borrow. When `k` ends, resolution substitutes `S Z` into
both owners' sealed programs and re-normalises; which owner actually receives the write is decided by
`n` inside the sealed run (only one of `c₁ := S Z`, `c₂ := S Z` fires per instantiation). No two-writer
aliasing at any point; [Access] would have ended `k` before any direct access to `a` or `b`.
**BLOCKED / sound.** This is the case D15 newly admits (branch-dependent live borrow), and D18 +
loans-as-variables handle it without a special rule.

---

## Attack 8 — must-fail `Id Nat Z (S Z)` under the trimmed `Eq` (D16)

`Id Nat Z (S Z)` with `W = ∅` computes to `Eq Nat Z (S Z)`. Under D16 (injectivity/disjointness
gone), no conversion rule applies: not reflexive (`Z ≢ S Z`), not a product, not `⊤`. So it is a
**stuck neutral proposition**. Inhabitants: `refl : ⊤` only (does not match), and `J` needs an
existing `Eq` to transport (none). So `Id Nat Z (S Z)` is **uninhabited** — no closed proof.
**Consistency of the must-fail goal survives D16.** (It is also externally refutable by large
elimination: `P := λn. match n {Z ⇒ ⊤ | S _ ⇒ ⊥}`, `transport (symm h) ⟨⟩ : ⊥` from a hypothetical
`h : Eq Nat Z (S Z)` — confirming the equation is genuinely false, not merely unprovable, so nothing
is lost by removing the definitional `⊥` rule.)

---

## Attack 9 — fire triangle re-confirmed under P5 + D16

v1 keeps Ochr in the paper's consistent call-by-value corner: typing is CBV evaluation, [Call-type]
and [Def] bind parameters to argument *values* (never an unevaluated computation into a type), so the
substitution leg is value-restricted. Dependent elimination is [Split] on a variable `σ`. Observable
effects exist only relative to open borrows, which state-passing makes pure (a closed program runs to
a canonical value — meta-model §4, T5b). P5 does not change this; it removes the C1 route where an
effectful *proof* faked an observable boolean. D16 does not weaken it either: false Nat equations
remain refutable by large elimination (Attack 8), so the theory can still prove `S n ≠ Z`, which is
what dependent elimination on `Nat` needs — the trim removes only *definitional* shortcuts, not
provability. **No accidental weakening; no new triangle route.**

---

## Consolidated recommendations (v1)

1. **T1a (canonical observation): re-prove for D11.** Ending is now an acyclic *substitution* system;
   confluence is hereditary-substitution/Newman, not the deleted "content loan-free" premise. The
   conclusion holds and the proof is simpler. (Metatheory text only.)
2. **§3 "Stuck blocks": align the free-place rule with §4's footprint.** Add "appears under `&_`" to
   the borrow-argument clause; classify a place borrowed/written in *any* arm as a borrow argument,
   value arguments being read-in-all-arms-and-never-borrowed. (Correctness of close-off / adequacy.)
3. **Enforce "closures capture no borrows" at Π-type formation** (D13's premise), as an explicit
   formation error; own borrow parameters are exempt (they are rebound, not captured).
4. **Say why the must-fail goals fail under D16:** `Eq Nat Z (S Z)` is *uninhabited-stuck*, not `≡ ⊥`;
   keep the "refutable by large elimination" note so the trim is visibly harmless.
5. **P5: fix the erasure key to "sort of `B` is `Prop`"**, so `⊤ × Nat` (a `Type`) is never erased.

None is a `⊥` against v1. The one genuinely open metatheory risk is unchanged from round 1:
canonical observation *with holes* = T5 naturality, which I could not break but which is unproven;
mechanise the returned-borrow resolution first.
