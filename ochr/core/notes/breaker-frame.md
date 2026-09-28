# Breaker report: frame / [App] / footprint / snapshots

## 5-line summary

- **Verdict:** RULES.md v0 survives every concrete attack I could build: no `⊥`, no closed proof of `Id Nat Z (S Z)`, no accepted-but-false effect equation. But the survival is *conditional* and two things must change in the text for the survival to be real rather than accidental.
- **Most important finding:** [App]'s frame soundness rests *entirely* on mutable-borrow exclusivity, which RULES.md enforces only lazily and implicitly (via [Reorg]+[Ref]). The canonical aliasing counterexample (a commutativity lemma applied to two aliased borrows) is blocked *only* because ending a reborrow silently kills its sibling to `⊥`, which is then caught as a read-of-`⊥`. That is a real defence, but it is doing the whole job and is nowhere stated as an invariant.
- **What must change in RULES.md:** (1) [Assign] must forbid overwriting a place whose content is a loan (Aeneas's "no outer loans"); currently only [Reorg] implies it. (2) The footprint `W` must say what happens to `*r := …` when `r` is a *local* borrow (trace to owner, or declare locals unobservable); as written it is ambiguous and the ambiguity is exactly where an escaping write would hide. (3) The `Id` rule should say both observations run from *independent copies* of Ω (it is defensible as written, but the sequential reading is outright unsound and should be closed off).
- **Confidence:** Medium-high that the in-scope fragment (Nat/Unit, tree-shaped borrows, no borrows-in-data, no shared borrows) has no *first-order* frame bug. Low that the two conjectured obligations (canonical observation; frame lemma proper) actually hold once returned-borrow loan-holes are in play — that is where I would bet a real bug lives.
- **What I did not check:** the Lean formalisation (none yet); the full [Join] anti-unification for >1 outstanding loan; loops/shared borrows/borrows-in-data (all out of scope by D8); adequacy vs a real compiler backend.

## Attack roster (one line each)

1. Alias two `&mut` of one place (`&p`, `&p`) into a commutativity lemma — BLOCKED by [Borrow]+[Reorg] exclusivity, principled.
2. Alias via nested reborrow (`&z`, `&*x`) into the same lemma — BLOCKED, but only because [Reorg] kills the sibling to `⊥` inside the callee; principled yet load-bearing and unstated.
3. Write escaping the footprint via a returned borrow (`TailM`) — BLOCKED, owner-of-free-borrow-var covers it; but the *local* `r` case is under-specified.
4. Post-mutation proof against a frozen goal (`*x:=5; refl`) — BLOCKED by D2 snapshot.
5. Effect-hiding (`Id Nat (*x:=Z; *x) Z`) — BLOCKED by effect-sensitivity (shared `W`).
6. Fire-triangle instantiation (substitution + dependent elim + observable effect) — BLOCKED: Ochr is call-by-value, substitutes only values; sits in the paper's consistent CBV camp. Borrows-as-values loophole examined and closed.
7. `J`/transport across an effectful `Id` — BLOCKED: `Id` reduces to `Eq` on pure observations before any `J` sees it.
8. Non-canonical observation via loan-ending order, esp. returned-borrow loan-holes — OPEN; the most promising place for a real bug.
9. `Id Nat (Add x x) x` well-formed-but-false — confirmed UNPROVABLE (footprint empty, `Eq Nat 2σ σ` stuck).
10. Sequential-vs-copy reading of "both sides run from the same Ω" — a spec hole; the sequential reading is unsound.

---

## Attack 1 & 2 — [App] frame vs aliased borrows (the main target)

The soundness of [App] is the assertion: the codomain `B`, proved by the callee with each borrow
parameter owned by a *fresh isolated ghost*, may be re-evaluated in the caller's environment where
those parameters point at whatever the caller supplies. The frame lemma (§7) says this is fine
*because a call touches only what is reachable from its arguments*. The attack is to make two borrow
parameters, disjoint in the callee, **alias** in the caller, so the callee's proof (which used
disjointness) becomes a proof of a false statement.

### The lemma to weaponise

```
g : Π(x : &Nat) (y : &Nat). Id Nat (*x := Z; *y := S Z; *x) (*x := Z; *y := S Z; Z)
g x y := refl
```

Check `g` with the [Lam] rule. Frame: `x° : Nat ↦ loan_0`, `x ↦ borrow_0 σx`,
`y° : Nat ↦ loan_1`, `y ↦ borrow_1 σy`. `x°` and `y°` are DISTINCT ghosts.

`W(LHS, RHS)`: both sides have `*x :=` and `*y :=`, and `x`, `y` free borrow vars, so
`W = {owner(x), owner(y)} = {x°, y°}` (two places).

- `⟦LHS⟧`: run `*x:=Z` (x°→Z), `*y:=S Z` (y°→S Z), read `*x` = `Z` (copy). Resolve. Tuple
  `(Z, x°=Z, y°=S Z)`.
- `⟦RHS⟧`: run the two writes identically, return `Z`. Tuple `(Z, x°=Z, y°=S Z)`.

`Id … ≡ Eq (Nat × Nat × Nat) (Z,Z,SZ) (Z,Z,SZ) ≡ ⊤ ∧ ⊤ ∧ ⊤ ≡ ⊤`. So `refl` checks. **`g` is
accepted, and its statement is TRUE — for disjoint `x`, `y`.**

### Instantiate with aliased borrows

Now the exploit. Build two live borrows that share an owner and call `g`:

```
attack : Π(z : &Nat). Id Nat (S Z) Z          -- FALSE: would give Eq Nat (S Z) Z ≡ ⊥
attack z :=
    let a = &*z;          -- a : &Nat, reborrow of *z
    g z a                 -- pass z and its own reborrow a
```

If `g z a` type-checks, its result type is `B[x:=z, y:=a]` evaluated at the call site. Here
`owner(z)` and `owner(a)` **coincide** (both resolve to `z°`, because `a` is a reborrow *of* `z`).
With `x`,`y` aliased, `⟦LHS⟧` runs `*x:=Z` then `*y:=S Z` *to the same cell*, so the final read of
`*x` is `S Z`, while `⟦RHS⟧` returns `Z`. The statement becomes `Eq Nat (S Z) Z ≡ ⊥`. A proof of it
plus `Eq Nat Z Z → …` is `⊥`. So **everything hinges on whether `g z a` type-checks.**

### Why it does NOT type-check (the block, traced)

The call `g z a` must produce its result *value* by the machine ([App]: "value comes from the
machine, unfold or [Close]"). `g`'s body is `refl`, but to give `refl` a type the machine must
evaluate the codomain's observations, i.e. run `*x := Z; *y := S Z; *x` in the frame
`[x ↦ (z's borrow), y ↦ (a's borrow)]`. Track the environment at the call:

```
caller:  z° ↦ loan_z | z ↦ borrow_z (content σ)               -- z is the &Nat parameter
let a = &*z:   *z is the content σ inside borrow_z.
               borrow *z:  z ↦ borrow_z (loan_a),  a ↦ borrow_a σ      -- a live, loan_a sits in *z
call g z a:    move z into x_g, move a into y_g:
               frame [ x_g ↦ borrow_z (loan_a),  y_g ↦ borrow_a σ ]
```

Note `x_g`'s content is `borrow_z (loan_a)` — it *contains a loan* (`loan_a`), because `a` borrowed
out of it. Now run `g`'s body:

- `*x_g := Z`: assignment accesses place `*x_g`, whose current content is `loan_a`. By **[Reorg]**
  ("accessing a place whose content … is `loan_ℓ`: end borrow ℓ first"), we must first end
  `borrow_a`. Ending it: `y_g` (`= borrow_a σ`) becomes `⊥`; `loan_a` becomes `σ`. Now
  `x_g ↦ borrow_z σ`, `y_g ↦ ⊥`. Then `*x_g := Z` proceeds: `x_g ↦ borrow_z Z`.
- `*y_g := S Z`: accesses `*y_g`; but `y_g = ⊥`. Reading/writing through `⊥` is **[Ref] / [Read]
  stuck-with-error** ("reading `⊥` is a type error"). **The call is rejected.**

So the aliased call fails, at exactly the step where the second "disjoint" borrow is used, because
creating and passing `a` consumed the exclusivity of `z`, and the lazy [Reorg] cashed that out by
destroying `a` the instant `x` was written. **Blocked, and for the right reason:** `&mut`
exclusivity *is* the frame lemma's hypothesis, and here we watch the machine enforce it.

### What this proves about RULES.md

The block is real but **it is not an invariant anyone stated**; it is an emergent consequence of
three separate rules ([Borrow] loaning the source, [Reorg] ending on access, [Read]/[Ref] trapping
`⊥`). Two concrete fragilities:

1. **[Assign] does not itself forbid overwriting a loan.** In the trace, `*x_g := Z` only worked out
   because [Reorg] fired *before* the write. If an implementer optimises [Assign] to drop-and-write
   without first reorganising (RULES.md's [Assign] literally says "the old content is dropped"), the
   write would silently clobber `loan_a`, `y_g` would keep pointing at freed structure, and the
   aliased call would go through — **unsound**. Aeneas states this explicitly (E-Assign: `v_p` has
   *no outer loans*). RULES.md must copy that premise onto [Assign], not leave it to [Reorg] timing.
2. The defence depends on `⊥`-reads being caught *everywhere* a stuck program might route around
   them. [Close] can bury a read behind a sealed program; see Attack 8.

Also note: RULES.md's move rule ([Read], "if `v` is a borrow: move") is *itself* missing Aeneas's
E-Move premise `{⊥, loan} ∉ v`. In the trace above, `z ↦ borrow_z (loan_a)` is a borrow whose
*content contains a loan*; Aeneas forbids moving such a value outright, which would block `g z a` one
step earlier. RULES.md permits the move and relies on [Reorg] at the later write. Same class of gap.

---

## Attack 3 — a write that escapes the syntactic footprint `W` (target 2)

Goal: a computation `t` whose *persistent* write lands on an owned place **not** in `W(t,u)`, so that
`Id` equates two computations that actually differ in effect. If found, pick the differing value to
get `⊥`.

By P5 (frame) the only owned places `t` can persistently write are: places it borrows/assigns by
name (captured by `W`'s first clause), places reachable through its free borrow variables (captured
by `W`'s second clause, "owner of every borrow-typed free variable"), or places it creates by local
`let` (dropped at the end of `t`, hence not persistent). So the footprint is *complete for the
in-scope fragment* — provided the "owner" map and the drop discipline are exactly right. I probed the
two seams:

**Returned borrow (`TailM`).** Take `t = let r = TailM x; *r := S Z; ()` with `x : &Nat` free.
`TailM x` returns a borrow into the tail of `x`; `*r := S Z` writes that tail; the write persists into
`x`'s owner. Is `owner` captured? `x` is a free borrow variable, so `W ⊇ {owner(x)} = {x°}`, and the
tail of `x` resolves to `x°`. **Captured.** The write is visible in the observation of `x°`. No escape.

**The gap — a write through a *local* borrow.** `W`'s first clause is "the root owned place of every
place appearing under `&_` or on the left of `:=`". In `*r := S Z`, the place is `*r`; its *root* is
`r`, and `r` is a **local, borrow-typed** `let`-binding, not an owned place. RULES.md does not say
whether such an `r` contributes `r` (a non-owned place — meaningless in a footprint of owned places),
or is *traced to its owner* `x°`, or is *dropped* as a local. The intended reading is surely "trace
to the owner", and here the owner `x°` happens to also be caught by the free-variable clause, so no
bug manifests. **But the text as written is ambiguous exactly at the one construct (a returned borrow
stored in a local and written through) where an escaping write would live.** RULES.md must state:
the footprint of `p := …` and `&p` is `owner(root(p))` computed in Ω after ending all borrows — never
the syntactic root when the root is itself a borrow. With that fix the clause becomes complete; as
written it invites an implementer to record `r` (or nothing) and miss the write.

I could not turn this into an accepted false proof, because every route I tried to a *persistent*
out-of-`W` write went through either a syntactic `&`/`:=` on the owner or a free borrow variable, both
in `W`. Verdict: **no bug in scope, but a real specification hole** that would become a bug under
borrows-in-data (D8, out of scope), where a write can reach a place with no name and no free-variable
witness.

---

## Attack 4 — post-mutation proof vs frozen goal (target 3, the D2 snapshot)

The E6 target: `λx:&Nat. (*x := 5; refl) : Π(x:&Nat). Id Nat *x 5`. Trace [Lam]: bind
`x° ↦ loan_0`, `x ↦ borrow_0 σ`. Snapshot the goal *at entry*: `Id Nat *x 5` with `W = {x°}`,
`⟦*x⟧ = (σ, σ)`, `⟦5⟧ = (5, σ)`, so goal `≡ Eq Nat σ 5 ∧ Eq Nat σ σ ≡ Eq Nat σ 5` (stuck,
unprovable). The body runs `*x := 5` (now `x° → 5`) then offers `refl`. `refl : Eq A a a`; to have the
frozen type `Eq Nat σ 5` we would need `σ ≡ 5`. It does not. **Rejected.** The snapshot is doing its
job: the goal is a closed statement about the entry value `σ`, and the mutation cannot retro-fit it.

The stronger variant, where the goal's own observation performs the mutation, is Attack 5.

---

## Attack 5 — effect-hiding inside the observation

Could a computation "launder" a false result by doing the mutation on *both* sides so the effect
cancels? Try `Id Nat (*x := Z; *x) Z`. `W = {x°}`. `⟦*x:=Z; *x⟧ = (Z, x°=Z)`. `⟦Z⟧ = (Z, x°=σ)` —
the RHS `Z` writes nothing, so `x°` resolves to its *entry* value `σ`, not `Z`. Thus
`Id ≡ Eq Nat Z Z ∧ Eq Nat Z σ ≡ Eq Nat Z σ`, **unprovable**. The observation is faithful: because
both sides start from the same Ω and the footprint is shared, any write on one side that the other
lacks shows up as a mismatched place-content. There is no laundering: to make the value equation true
you must give both sides identical effects, and then the statement is genuinely true. **Blocked, by
construction of the observation.** This is the mechanism that makes the whole design honest.

---

## Attack 6 — the Fire Triangle, instantiated in Ochr

The fire triangle (Thm 1): an *observably effectful* theory with *substitution* and *dependent
elimination* is inconsistent. Recipe (paper §2.1): take a closed `t : B` and a context `C` with
`C[true] ≡ true`, `C[false] ≡ true`, `C[t] ≡ false`; dependent elimination gives `x:B ⊢ ⋆ : C[x] =
true`; substitution gives `⊢ ⋆ : C[t] = true`; convert with `C[t] ≡ false` to `false = true`, then
`⊥`. Does Ochr supply all three ingredients simultaneously? I checked each against the actual rules.

**Dependent elimination: YES, unrestricted.** [Split] is exactly Definition 2 for `Nat`: prove the
goal under `σ := Z` and under `σ := S σ'`, conclude it for the variable. Full large elimination.

**Observable effects: YES, that is the point.** `Id` observes; `AddM x 5` is a closed-up-to-`x`
computation not observationally equal to any pure value. Concretely, with `C[·] := ⟦· ; *x⟧` reading
`x` after running the hole, the read distinguishes computations with different writes.

**Substitution (Definition 1, the unrestricted form): NO.** This is where Ochr lives or dies, and it
survives *because it is call-by-value*. The paper's §2.2 is explicit: in CBV, dependent elimination
is always sound and it is *substitution* that must be value-restricted. Every point where Ochr
substitutes a term into a type is guarded by prior evaluation to a value:

- [App] forms `B{x := w}` where `w` is the argument *already reduced to a value* by the CBV machine.
- [Split] substitutes `σ := Z` / `σ := S σ'` — constructors, i.e. values.
- [Let]/[Match] bind `x` to an evaluated value before entering the body.

So Ochr never substitutes an *un-evaluated, effectful* term into a type. It is precisely the paper's
option (2): "effects + dependent elimination + restricted substitution", the consistent PML/Lepigre
corner. The fire-triangle proof stalls at "by substitution, `⊢ ⋆ : C[t] = true`", because `t` (an
effectful computation) is not a value and cannot be substituted into the dependent-elimination
result `C[x] = true`.

**The borrows-as-values loophole (the real worry).** A `borrow_ℓ v` *is* a value, so value
restriction lets it substitute into a type — yet a borrow is an effect *in waiting* (reading it moves
it; writing through it mutates the owner). Is this the fire triangle sneaking back in? I claim no,
and the reason is the synchronization the paper demands. In BTT (paper §2.3) the fix for CBN is to
force the type to *evaluate its argument* via a storage operator, synchronizing effects in term and
type. Ochr gets that synchronization for free: the type `Id A t u` **runs `t` and `u` on the
argument** (the observation *is* the evaluation), on a private copy of the very Ω the term uses. There
is no desync between "effect performed by the term" and "effect the type reasons about", because the
type reasons by performing the same effect on a copy. The dangerous CBN gap — case-analysing a
boolean in the term without reflecting that evaluation in the type — cannot open, because Ochr has no
type former that inspects a computation without running it. **Blocked, and this is the deepest reason
the design is sound: `Id`-computes-by-observation is Ochr's storage operator.**

Residual: this argument is only as strong as "the observation runs *the same* computation the term
runs, from *the same* state." Attack 10 shows the one-line spec ambiguity that, read wrongly, breaks
that identity. And it assumes the private-copy run and the real run agree — the *adequacy* obligation
(§7), unproven.

---

## Attack 7 — `J` / transport across an effectful equation (target 5)

Worry: `Id A t u` between effectful `t, u`, transported by `J`, could move a proof along an
"equation" that only holds up to effects, landing a `P t`-proof at `P u` unsoundly. But `Id` is
*derived* (D5): at any environment it **reduces to `Eq (A × T_W) ⟦t⟧ ⟦u⟧`**, and the two arguments of
that `Eq` are *observations* — tuples of ordinary `Nat`/`Unit`/pair **values**, with every borrow
resolved away. So by the time any `J`/transport looks at the proof, its type is `Eq` between pure
values; `J` never sees a borrow, a loan, or a pending write. The `Eq` conversions (D6) are the
standard injective/disjoint/`⊤`/`∧` rules on `Nat`/`Unit`/pairs, each validated by the proof-irrelevant
set model (they identify propositions of equal truth value). `refl`, `J`, transport then behave
exactly as in CIC on those pure values. **Blocked:** effects are discharged into values by the `Id`
reduction *before* the identity-type machinery engages. (Caveat: this relies on `Id` always getting
its environment to reduce; a raw un-reduced `Id A t u` carried under a binder and transported before
reduction would need the checker to refuse `J` on an unreduced `Id`. Worth a one-line rule: `J`/refl
apply only after `Id` has computed to `Eq`.)

---

## Attack 8 — canonical observation / loan-ending order (target: consistency, §7)

`Id`'s observation "ends every borrow in Ω' and records the resolved content of each `k ∈ W`." §7
*conjectures* this is independent of the order loans are ended in. If it is not, one term `t` has two
normal forms `n₁ ≠ n₂`; then `refl : Id … t t` reduces to `Eq … n₁ n₂` on one ordering and to a
different equation on another, and a term provable under one reduction with a refutation under
another is `⊥`. This is the single most dangerous obligation and it is **open**.

I could not break it *in scope*, and here is why it is plausibly true in scope: with no borrows in
data, no shared borrows and single ownership, live mutable borrows form a **tree** (each loan has a
unique borrow; nested borrows must be ended inside-out because [Reorg]/[Pop] require a borrow's
content to be loan-free before it ends). Sibling (disjoint) borrows commute because each writes only
its own loan's cell. So the ending order is forced up to independent commutations, and the resolved
contents are determined.

**The one place I would keep hunting:** returned borrows with **loan-holes** ([Close], result type
`&T`). There a loan is filled with a sealed program carrying a hole `loan_k`, which resolves only
*after* borrow `k` ends (doc 01 §9 writes this fill as `λfinal. (last_mut♯ σ).back final`). That
imposes a genuine cross-dependency: cell `cᵢ`'s final value depends on when borrow `k` ends. If two
returned borrows could be made mutually dependent (each one's loan-hole naming the other's borrow),
the ending order would matter and canonicity would fail. I argued above that exclusivity keeps the
holes into *disjoint* cells, so the dependency graph is a DAG and a topological order exists and is
unique-up-to-commutation — but I did **not** prove the DAG claim, and doc 01 itself flags the
`last_mut` example as the untested case ("tests whether normal forms with λ-valued loan fills still
let `cong S` go through"). **Recommendation:** make `last_mut`/`AddM'` (E2) the *first* mechanised
example, and state canonicity as a theorem about the loan-hole dependency graph being acyclic, not
just "independent endings commute."

---

## Attack 9 — `Id Nat (Add x x) x` (D3 accepts it as well-formed-but-false)

D3 admits this term; I confirmed it is **unprovable**, i.e. false-but-harmless. `Add a b := AddM &a b;
a`; arguments are `Nat` (owned), and reading an owned `Nat` **copies** (D3). So `Add x x` copies `σ`
twice into two fresh locals, mutates a local, returns `σ + σ = 2σ`. Footprint: `x` appears only as a
by-value read (not under `&`/`:=`, not borrow-typed), so `W = {}` and the observation is just the
value. `⟦Add x x⟧ = (2σ)`, `⟦x⟧ = (σ)`, giving `Eq Nat 2σ σ` — stuck for abstract `σ`, unprovable.
Good: the copy semantics that makes `x + x = 2x` *statable* does not make any false instance
*provable*. No bug.

---

## Attack 10 — "both sides run from the same Ω": copy or sequential?

The `Id` rule reads: `Id A t u ≡ Eq (A × T_W) ⟦t⟧_Ω^W ⟦u⟧_Ω^W`, "both sides run from the same Ω".
Read functionally — each `⟦·⟧_Ω` takes Ω as input and runs from an independent copy — this is correct
and is what P2 ("a private copy of the current environment") demands. But the phrase admits a
**sequential** misreading: thread one Ω through `⟦t⟧` and then `⟦u⟧`. That reading is **unsound**:
`⟦AddM x 0⟧` moves `x`'s borrow out and mutates, so `⟦()⟧` run afterwards would observe the
already-mutated `x°` (and find `x` consumed), collapsing the effect comparison — every
`Id Unit (mutating-t) ()` would look reflexive and prove false effect equalities. **Recommendation:**
state explicitly that `⟦t⟧` and `⟦u⟧` are each computed from an independent copy of Ω (the same
starting Ω, not a shared mutable one). This is a one-line clarification, but it is load-bearing:
Attack 6's fire-triangle argument (the type performs the same effect the term does, on a copy) breaks
if the two observations are not independent.

---

## Correction & consolidated recommendations

**Harm re-classification for Attack 1/2.** On reflection the missing [Assign]/[Read] "no outer loans"
premise does **not** produce an internal `⊥`, because the codomain type is computed by the *same*
machine as the term: if [Assign] clobbered `loan_a`, the type-level observation would clobber it too,
so term and type stay in sync and `g z a` would get type `⊤`, not `⊥`. The real harm is **adequacy /
memory safety**: the *compiled* program would perform a dangling write through `y_g` after `x_g`'s
cell was reassigned — a use-after-free in well-typed code. That is exactly the task's "dangling
borrow" failure mode, just located at the theory↔runtime boundary (the frame/adequacy obligation),
not inside conversion. With the rules as written (i.e. with [Reorg] firing on the access performed by
[Assign]), the symbolic machine *rejects* `g z a` via a read-of-`⊥`, so both consistency and adequacy
hold. The fix is to make the rejection a stated premise rather than an emergent timing property.

**Ranked changes to RULES.md:**

1. **[Assign] and the move case of [Read]: add the "no outer loans" premise** (Aeneas E-Assign /
   E-Move). Overwriting or moving a value whose content contains a `loan` must be rejected outright,
   not left to [Reorg] happening to fire first. Implicates the borrow-checker specification ([Ref]),
   which is currently one sentence and carries the entire frame lemma.
2. **Footprint `W`: define the write/borrow clause via `owner(root(p))` after ending borrows**, so a
   write through a *local* borrow (`let r = TailM x; *r := …`) is traced to its true owner rather
   than to the meaningless local root `r`. Implicates D5.
3. **`Id` rule: say the two observations run from independent copies of Ω** (Attack 10). Implicates
   D5/P2.
4. **`J`/refl apply only after `Id` has computed to `Eq`** (Attack 7 caveat). Implicates D6.
5. **State canonicity as acyclicity of the loan-hole dependency graph** and mechanise the returned-
   borrow example first (Attack 8). Implicates §7 and D4.

None of these is a derivation of `⊥` against v0 as written; all are places where the *text* leaves a
soundness-critical fact implicit, and (1)+(2) are the ones an implementer could get wrong and thereby
ship memory-unsafe well-typed code. The deepest *principled* finding is Attack 6: `Id`-by-observation
is Ochr's storage operator, and it is what buys the fire triangle's "restricted substitution" corner
without the programmer ever writing a value restriction — provided Attack 10's independence holds.
