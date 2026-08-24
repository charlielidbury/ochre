# Diagnosis: why a runtime variable inside a `fn` body hovers as nothing

> **STATUS — one of the three causes is FIXED on this branch (`b924cd51`); the
> other two are diagnosed and not fixed, deliberately.** §5 says what each would
> cost. The full 120-job build is green, `Tests/ShowSpans` (S7) pins the residual
> assertably, and every measurement below is a `textDocument/hover` response
> quoted verbatim rather than a prediction.

**The report.** Hovering `src`, `dst`, `hd`, `tl` inside this program shows
nothing, where the reader wants each one's value — or its symbolic value — *at
that point*:

```lean
def entrypoint : Checked := prog () {
  fn Reverse [src] (src: List Nat, dst: List Nat) -> List Nat {
    match src {
      Nil => dst,
      Cons(hd, tl) => Reverse(tl, Cons(hd, dst))
    }
  };
  ()
}
```

**The answer in one paragraph.** The hover machinery works inside `fn` bodies —
that was checked first and it is not the problem. What this program hits is
**three unrelated breaks wearing one symptom**, and only one of them is a bug in
the hover feature. The first is that `fn F [k] …` is not the program that gets
checked: the `[k]` hint lowers the body to a **recursor** before any checking
happens, which deletes the `match` node the tooltips are keyed by and eliminates
the scrutinee `src` as a binding entirely. The second is a plain omission — a
**bare match arm body filed no occurrence key**, so `Nil => dst` had nothing to
join against; that is fixed here. The third is that a module-level `let` bound by
a **call** is keyed by the pre-retarget term and misses too.

**Of the four names the reporter asked about, one — `src` — has no answer to
give, and that is a fact about the calculus rather than about the tooling.** In
the checked program `src` is not a variable. §4 is about that, because it is the
part a plan could most easily paper over.

---

## 1. What actually happens, measured

Repro file: `Dllbc/Tests/HoverRepro.lean` on this branch (scratch, not in the
default target). Columns are 1-indexed at the start of the identifier. Both
collection options were verified ON — `dllbc.hover` and `dllbc.pointHover` are
`register_option … defValue := true` (`ElabCheck.lean:14`, `:32`) and nothing in
the repro sets them; the positions that DO answer are the proof that collection
ran, so a wrong default is ruled out rather than assumed away.

### 1.1 The reporter's program, position by position

Lines 14–22 of the repro are the program above, verbatim.

| position | what is written there | BEFORE the fix | AFTER the fix |
|---|---|---|---|
| 15:6 | `Reverse`, the declaration | `**Reverse : `(src : List Nat, dst : List Nat) -> List Nat`**` | unchanged |
| 15:15 | `src` inside `[src]` | *(nothing)* | *(nothing)* |
| 15:21 | `src`, the parameter binder | *(nothing)* | *(nothing)* |
| 15:36 | `dst`, the parameter binder | `(σ₄ : List Nat); (σ₀ : List Nat)` | unchanged |
| 16:11 | `src`, the match scrutinee | *(nothing)* | *(nothing)* |
| 17:14 | `dst` in `Nil => dst` | *(nothing)* | **`dst ↦ (σ₀ : List Nat)`** |
| 18:12 | `hd`, the pattern binder | *(nothing)* | *(nothing)* |
| 18:16 | `tl`, the pattern binder | *(nothing)* | *(nothing)* |
| 18:23 | `Reverse`, the self-call | *(nothing)* | *(nothing)* |
| 18:31 | `tl` in the recursive call | *(nothing)* | *(nothing)* |
| 18:40 | `hd` in `Cons(hd, dst)` | *(nothing)* | *(nothing)* |
| 18:44 | `dst` in `Cons(hd, dst)` | *(nothing)* | *(nothing)* |

*(nothing)* is literal: the server answers with the enclosing `prog () { … }`
term and `"info":"Checked"`, which is Lean's ordinary hover for the block. No
DLLBC tooltip is pushed at that span, so the innermost info node containing the
cursor is the whole block.

**Two positions answered from the start, and they are the tell.** `Reverse`
answers because a callee signature is S1 metadata read straight off the source
(`docs/16`). `dst` at 15:36 answers because a parameter binder is an ENTRY
occurrence and the checker's seeds did bind something called `dst` — twice, on
two paths, which is why it renders as two answers separated by `;` with no arm
label. `src` beside it, spelled identically and tagged identically, answers
nothing. **Two parameters of one telescope, one answering and one not, is the
observation the whole diagnosis turns on.**

### 1.2 The variant battery

Nine programs, differing one axis at a time. All measured through
`lean_hover_info`; `✓` means a tooltip, `—` means silence.

| # | program | `src`/scrutinee | param `dst` | pattern `hd`/`tl` | bare arm tail | statement in arm |
|---|---|---|---|---|---|---|
| A | `fn F [src] … { match src { Nil => dst, Cons(hd,tl) => F(…) } }` | — | ✓ (2 paths) | — | — (→ ✓ for `Nil => dst` after fix) | n/a |
| B | same, **no `[k]`** | ✓ | ✓ | ✓ | ✓ | n/a |
| C | no `[k]`, match bound by `let r = match …` | — | ✓ | ✓ | ✓ | ✓ |
| D | `[src]`, body opens `let z = dst;` | — | ✓ (2 paths) | — | binder fallback only | ✓ |
| G | **unsealed** `fn` (no `-> R`), called once | — | — | — | — | — |
| H | no `[k]`, every arm body is a **block** | ✓ | ✓ | ✓ | n/a | ✓ |
| I | `[src]` **and** block arm bodies | — | ✓ | — | n/a | ✓ (per-arm σ, correct) |
| J | no `[k]`, arm tail is a **call** `IdJ(tl)` | ✓ | ✓ | ✓ | ✓ (only via the fallback) | n/a |
| E/F | controls: no `fn` at all | n/a | n/a | n/a | n/a | ✓ |

Four readings worth pulling out of that table:

* **B answers almost everything.** Delete the `[k]` hint and the same body
  hovers: `src ↦ (σ₀ : List Nat)` at the scrutinee, `hd ↦ (σ₂ : Nat)` and
  `tl ↦ (σ₃ : List Nat)` at the pattern binders. So the machinery reaches inside a
  sealed `fn` body perfectly well. **The seal is not the cause** — see §3.
* **I is the sharpest single result.** Keep the `[k]` hint and give each arm a
  statement, and the arms answer *with the right per-arm σ*: `dst ↦ (σ₀ : List
  Nat)` in the `Nil` arm, `dst ↦ (σ₄ : List Nat)` in the `Cons` arm, `hd ↦ (σ₁ :
  Nat)`. The facts are recorded, they are correct, and they are per-branch. What
  fails in A is purely the join.
* **G, the unsealed `fn`, answers WORSE, not differently.** Nothing in the block
  answers except the two S1 signature tooltips. §2.4.
* **C shows the same break outside any `fn`**: `match src` written as `let r =
  match src { … }` loses the scrutinee's tooltip, because the machine's
  breadcrumb at the binding is the `match`, not the `let` the surface keyed by.

---

## 2. Why — the mechanism, named

### 2.0 How a tooltip finds its fact

Three tables meet at `ElabCheck.pushHovers` (`ElabCheck.lean:432`):

1. The walker (`Uni.lean`) files an **occurrence** per identifier —
   `noteOcc` (`:756`) — and later stamps each with the **statement it sits in**,
   `tagOccsFrom` (`:770`), or with the **body/arm it is a telescope position of**,
   `tagOccsEntry` (`:795`).
2. The checker files a **delta** per state change — `notePoint`
   (`Machine.lean:555`) — tagged with the breadcrumb `St.stmtKey` current at
   that moment.
3. The surface joins the two **by term equality on the key**, replaying the
   delta stream up to the key: `replayTo` (`Program.lean:141`) for a statement,
   `replayEntry` (`:197`) for an entry occurrence.

So a tooltip answers exactly when *the term the surface emits as a key* equals
*the term the checker was walking when it filed a delta*. That is true whenever
the elaborated program is structurally the program that was written. All three
breaks below are places where it is not.

Two ways to decline, both silent by design (`docs/16`: "loud where absence
implies a defect, silent where absence is normal"):

* `replayTo` returns `none` when **no run is filed under the key at all**, or
  when more than one is.
* `replayEntry` returns `none` when the keyed run **did not bind the name asked
  about** — the `seeded` guard, which is there to stop a `fn` statement's
  enclosing instance from answering for a parameter.

### 2.1 Break 1 — `[k]` lowers the body to a recursor, and the source shape is gone

`fn F [k] …` does not elaborate to a function with a `match` in it. `FnMacro`
(`FnMacro.lean:340` onward, `docs/06` §7) rewrites the whole body into a
**recursor application**, and it does so at the macro layer, before anything is
checked. Printed from the repro's own probe, the constructor spine of the
reporter's program is:

```
seq
  letIn Reverse
    seal
      app app app app (listRec) (Nat) (lam §src. Π(dst : List Nat). List Nat)
        (lam dst. dst)                                        -- the Nil arm
        (lam hd. lam tl. lam Ih. lam dst. app Ih (Cons hd dst))  -- the Cons arm
  ()
```

against the same program with the hint removed:

```
seq
  letIn HeadB
    seal
      lam src. lam dst. matchE src { Nil => dst, Cons(hd,tl) => tl }
  ()
```

Three things vanished, and each takes a class of tooltip with it:

* **The `matchE` node.** The walker keys pattern binders and bare arm bodies at
  `` `(Dllbc.Term.matchE $scrut none []) `` (`Uni.lean:1451`). In the lowered
  form that term is never walked, so no delta is ever filed under it and
  `replayTo`/`replayEntry` decline for *every* occurrence keyed there. This is
  why `hd` and `tl` at 18:12/18:16 answer nothing in A and answer fine in B.
* **The scrutinee.** `src` becomes the recursor's own argument — the sealed Π's
  first binder — and stops being a runtime binding. The macro says so where it
  refuses a body that still mentions it: *"The scrutinee does not exist inside an
  arm — it is the recursor's argument"* (`FnMacro.lean:507`). The delta dump
  confirms it from the other side; here is the reporter's program's entire
  recorded history:

  ```
  -- path 0 (the enclosing module path)
    key=let Reverse = …  trail=[] :: bound dst/slot := σ₀
    key=let Reverse = …  trail=[] :: bound hd/slot  := σ₁
    key=let Reverse = …  trail=[] :: bound tl/slot  := σ₂
    key=let Reverse = …  trail=[] :: bound Ih/slot  := σ₃
    key=let Reverse = …  trail=[] :: bound dst/slot := σ₄
    key=let Reverse = …  trail=[] :: bound Reverse/decl := σ₆
  -- path 1 (the step branch)
    … the same five seeds …
    key=Ih (Cons hd dst)  trail=[] :: set dst := ⊥
  -- path 2 (the base branch)
    key=let Reverse = …  trail=[] :: bound dst/slot := σ₀
    key=dst              trail=[] :: set dst := ⊥
  ```

  **`src` is never bound.** Not filed late, not filed under another key — never
  bound, on any path. `replayEntry`'s `seeded` guard therefore declines for it on
  every path, which is precisely correct behaviour: there is no fact.

  It also explains the `dst` beside it. `dst` IS bound, twice — σ₀ for the base
  arm and σ₄ for the step arm — so `factsAtEntry` returns two facts and
  `renderPaths` lists both. The arm trails are empty (a recursor's arms are λs,
  not branches), so the two cannot be labelled, and the tooltip reads
  `(σ₄ : List Nat); (σ₀ : List Nat)`. Correct, and less useful than it looks.

* **The self-call.** `selfToIh` (`FnMacro.lean:270`) rewrites `Reverse(tl, …)` to
  `Ih (Cons hd dst)` — a different head, and one argument fewer. So the step
  arm's tail is keyed `Ih (Cons hd dst)` by the machine and
  `Reverse(tl, Cons(hd, dst))` by the surface. Two terms, no join, and this is
  why 18:31/18:40/18:44 still answer nothing even after §2.2's fix, which
  otherwise handles bare arm tails.

**The general statement, because it will recur.** The point-hover join assumes
the elaborated term is the source's shape. `fn`'s `[k]` lowering is the one place
in the surface where a macro *rewrites the program* rather than assembling it, so
it is the one place the assumption fails — and it fails silently, because a
missing key is indistinguishable from a position nothing happened at.

### 2.2 Break 2 — a bare arm body filed no occurrence key (FIXED)

Compare two rows of the walker, one function apart. `elabUBlk`'s final-expression
row (`Uni.lean:2018`+) tags:

```lean
  | `(ublk| $e:uterm) => do
    let occLo ← occMark
    …
    tagOccsFrom occLo e'          -- "This row did NOT tag occurrences until
                                  --  docs/18 §3 … A pre-existing hole in
                                  --  docs/17's surface, fixed here."
```

`elabUArmBody`'s bare row (`Uni.lean:1658`, as it stood) did not:

```lean
  | `(uarmBody| $e:uterm) => do    -- a bare arm body IS the arm's final statement
    let e' ← elabUTerm sc e
    spanOfStmt e' e                -- an error SPAN, and no occurrence key
    return e'
```

The comment on that row already said the right thing — *a bare arm body IS the
arm's final statement* — and the code filed the error span that follows from it
and not the occurrence key that follows from it just as directly.

So every identifier written in a bare arm body fell through to the match row's
`tagOccsEntry`, which routes it to `replayEntry`, which answers **only for names
that arm's own seed bound**. Hence the exact asymmetry the reporter would have
met on any program, hint or no hint:

* `Cons(hd, tl) => tl` — `tl` was bound by this arm's entry, so it answers.
* `Nil => dst` — the base arm binds nothing at all, so nothing in it answers,
  including a parameter that is perfectly live there.

**The fix** gives the row its `occLo`/`tagOccsFrom` pair, so the arm's tail is
keyed as the statement it is. `Nil => dst` now answers `dst ↦ (σ₀ : List Nat)` —
in the reporter's program too, which is the one position of the twelve that this
commit turns from silence into an answer.

**The naive version of that fix regresses, and the regression was measured, not
imagined.** Keying the tail's occurrences at the tail *alone* took an answer
away: in `Cons(hd, tl) => IdJ(tl)` (variant J), `tl` stopped answering, because
`moduleRetarget` rewrites the call and the surface's emitted key is no longer the
term the machine walked — Break 3's mechanism, met from inside an arm. The
occurrence had been answering through the entry route all along.

So the shipped fix keeps **both** keys. `tagOccsEntry` no longer passes over an
occurrence that already has a statement; it records the match key as
`OccNote.entryKey`, and `pointFactFor` tries the finest key first and falls back.
Nothing that answered before answers differently — verified position by position
across all nine programs — and the additions are exactly the positions that
answered with silence. Neither branch guesses: `factsAt` declines on an
unrecognised point, `factsAtEntry` declines on a run that did not seed the name,
and the fallback is a fact about a coarser point rather than an interpolation, so
`docs/16`'s decline-don't-guess survives the second door.

### 2.3 Break 3 — a `let` bound by a call, in a module block

Not part of the reporter's program, found while isolating §2.2, and worth
reporting because it is one line of source away from every real program:

```lean
def use1 : Checked := prog (std) {
  let y = LeRefl(2);
  () }
```

Hovering `y` (`Tests/ModuleStates.lean:34:7`) answers nothing — no point fact and
no binder fallback either, though `St.letTypes` holds an entry for it. The cause
is that `elabModule` (`ElabCheck.lean:702`) evaluates the block and then walks
**`moduleRetarget seedSt v`** (`:744`), not `v`: a `.call` is rewritten to its
resolved spine before the walk. The breadcrumb keys are therefore post-retarget terms and
the surface's emitted keys are pre-retarget ones, and the join misses for exactly
the statements that contain a call. The same mismatch is what made variant J's
arm tail decline.

The shape of the fix is known — the two existing key joins already normalize
through `Term.stripMarkers` for the same class of reason (`docs/21` §5) — but
retarget is not a normalization: it consults the seed's Ω. It would have to be
applied to the surface's keys with the same seed, at `pushHovers`. That is a
contained change and it is not made here, because it belongs with a measurement
of how many keys it moves.

### 2.4 The unsealed `fn` comparison — it answers WORSE, and the reason is structural

Worth doing because it was the sharpest available test of the seal hypothesis,
and its result is the opposite of what that hypothesis predicts. Variant G:

```lean
fn HeadG (src: List Nat, dst: List Nat) {   -- no `-> R`, so no seal
  match src { Nil => dst, Cons(hd, tl) => tl } };
let g = HeadG(Cons(1, Nil), Nil);
```

**Nothing in the block answers** except the two S1 signature tooltips at the
declaration and the call. The delta dump says why:

```
  key=let HeadG = …  :: bound HeadG/decl := λr(src, dst){…}
  key=let g = …      :: bound src/slot := Cons (S Z) Nil
  key=let g = …      :: bound dst/slot := Nil
  key=let g = …  trail=[(src, Cons)] :: set src := ⊥
  key=let g = …  trail=[(src, Cons)] :: bound hd/slot := S Z
  …
```

An unsealed `fn` is not checked at its binding at all — it binds a λ value, and
the body is walked **inlined at the call site**, so every delta it produces is
keyed by the CALLER's statement (`let g = …`). The body's own positions are keyed
by the surface at the fn statement and at the match; neither appears in the
stream. And the parameters, which are entry occurrences of `let HeadG = …`, meet
a run that binds only the declaration slot — `replayEntry`'s `outer` guard —
so they decline too.

**This is the honest generalization: an unsealed `fn` has no single answer to
give.** Its body has one state per call site, so "what is `src` here" is not
well-posed until you say which call. A sealed `fn` has exactly one audit and
therefore exactly one answer, which is why B and H answer and G does not. That is
a design consequence of `docs/06` §7's seal rule rather than a gap, and any
future work here has to decide what a multi-call tooltip even means before it can
build one.

---

## 3. What is NOT the cause — the seal, and why the guess was reasonable

The standing hypothesis before measuring was that a `fn` body is audited under
the SEAL in a fresh Ω (`checkRFnBody`, `Machine.lean:6644`) whose state is
discarded, so positions inside a body never get a breadcrumb the span table can
match. **That is refuted, and it is refuted twice over.**

* Variant B is the same body under the same seal with the `[k]` hint removed, and
  every position in it answers, per-arm, with arm trails attached.
* `Tests/ShowSpans` (S3, S5, S6) has been asserting `show` answers from inside
  sealed `fn` bodies since `docs/18`, and those `#guard_msgs` are green on every
  build.

The guess was reasonable because it names a real door that has been walked into
three times — the breadcrumb, `letTypes`, and the point deltas each had to be
taught to cross `checkRFnBody` separately, which is why `Ledgers` exists as one
record (`Machine.lean:213`+). **But the door has been shut since then, and the
lesson of this investigation is the complementary one:** the seal is now a solved
problem, and the next place a diagnostic channel goes missing is not a state
boundary but a **term rewrite** — a place where the elaborated program stops
being the shape of the source. `[k]` is the first one to bite; `moduleRetarget`
is the second, in §2.3; both are invisible to any amount of care about the seal.

One more thing was ruled out before anything else, because a wrong default would
have been a trivial answer: `dllbc.hover` and `dllbc.pointHover` both default
`true` and were on throughout. The positions that DO answer are the evidence.

---

## 4. The reporter's actual ask: values, not types

They are two different asks with two different feasibilities, and the honest
answer differs per name.

**Where the join works, the value is what you get, and it is the better answer.**
Every tooltip quoted in §1 is a VALUE — `dst ↦ (σ₀ : List Nat)`,
`b ↦ Cons (σ₁ : Nat) (σ₄ : List Nat)`, `x ↦ Cons (S Z) Nil`. The `x : τ` form the
feature is named for survives only as the *inline annotation on a σ*, which is
`docs/16`'s own ruling: a type is what you say when you do not know the value,
and this checker knows the value. A concrete value has no type recorded anywhere
and none is invented (`noteLetType`, `Machine.lean:571`: "the value is stored and
the surface says what it is, which is the honest answer rather than a synthesized
one this bidirectional checker has no function to produce").

**So "show me the value" is already the design, and there is nothing to build for
it.** For a parameter of a sealed `fn`, the value IS a σ with its type — the
function is being checked against arbitrary inputs, so `(σ₀ : List Nat)` is not a
type standing in for a missing value, it is the whole of what is true there.
Variant G's inlined call shows the same machinery printing concrete values
(`src := Cons (S Z) Nil`) when the checker has them.

**`src` is the one name with no answer of either kind, and it is not close.** In
the checked program there is no binding called `src`: the recursor consumed it
(§2.1). So:

* There is no VALUE to show — not a missing record, an absent binding.
* There is no TYPE to show either, except the annotation in the source, and that
  channel was deliberately deleted on 2026-08-21 (`OccNote.entry`'s docstring:
  "under strong updates nothing about a slot is timeless"). Re-introducing it for
  the scrutinee alone would be a carve-out from a ruling, not a fix.
* What COULD be shown is what the arm learned — `src ≡ Nil` in the base branch,
  `src ≡ Cons hd tl` in the step branch. That is a true fact, it is what a reader
  actually wants, and in the un-hinted form the checker literally records it
  (`refine sig0 := Nil` / `refine sig0 := Cons σ₂ σ₃` in variant B's stream). It
  is §5's option 3, and it is the only route that ends with `src` answering.

`Tests/ShowSpans` (S7) pins this as an assertion rather than a claim, since
`show x` prints exactly what hovering `x` there would say:

```
src — no value here (not checked, or not live)
dst ↦ (σ₀ : List Nat)          -- the base arm
src — no value here (not checked, or not live)
hd  ↦ (σ₁ : Nat)               -- the step arm
dst ↦ (σ₄ : List Nat)          -- the step arm, a different σ, correctly
```

---

## 5. Can it be fixed — options and costs

### 5.1 Done

**Bare arm bodies tag their occurrences** (§2.2). Shipped, no regressions, full
build green. It is one position of twelve in the reporter's program and a much
larger fraction in any program without a `[k]` hint — B, C, H and J all gain from
it, and D loses a spurious `(differs per path)` suffix because a point fact now
answers where a binder fact used to.

### 5.2 The `[k]` recursor — three options, in increasing order of honesty and cost

The facts are all recorded and per-arm correct (variant I proves it). What is
missing is a key that the surface and the machine agree on for positions inside
the arms, and an arm trail to label the two answers with.

**Option 1 — retag under `[k]`, cheap and partly dishonest.** Have the `fn` row
tell the match row that a hint is in effect, and entry-tag the arms' occurrences
at the `fn`'s own key instead of the dead `matchE` key. Then `hd` and `tl` answer
(their seeds are in that run), and `dst` answers with the same unlabelled
two-answer blob the parameter already shows. Cost: small, one plumbed flag.
**Why it is not shipped:** the blob shows a reader the *other* arm's value with no
label saying so, in a position where the reader is standing in one specific arm.
That is the failure direction `docs/16` forbids — a confident answer about the
wrong point rather than silence. It would buy two positions and spend the
feature's core property.

**Option 2 — the macro carries provenance, medium cost, general.** `docs/21`
already has `Term.marker` and a `stripMarkers` discipline for exactly the problem
of "the walked term is not the emitted term". `FnMacro` knows which source `match`
it consumed and which λ became which arm; it could wrap each lowered arm in a
marker carrying the source key and the constructor name, and the machine's
breadcrumb would then carry the source's identity through the rewrite. Every
existing surface key works unchanged, `hd`/`tl`/`dst` answer per-arm with real
trails, and — this is the part that makes it worth more than the two positions —
**it generalizes to any future macro-layer rewrite**, which §2.3 says is now the
live class of failure. Cost: a marker discipline through `FnMacro`, and a
decision about whether the markers are stripped before or after the key join
(they are stripped for the existing joins, so this needs its own channel or a
distinguished marker name). Real but contained.

**Option 3 — make the recursor look like the match that was written.** The
strongest version of option 2: file, as plain data on the seal, "arm λ #i is
source arm `C` of the match on `x`", and have the walk push a synthetic
breadcrumb `matchE x` plus trail `(x, C)` when it enters a recursor arm. Then the
surface needs no change at all, arm trails come back, and — uniquely — the
scrutinee becomes answerable: `src ≡ Nil` / `src ≡ Cons hd tl` is exactly what the
arm identity says. Cost: the machine gains a notion of "this λ is an arm", which
is a real concept addition to the walk and wants its own design note.
**Recommendation if this lane continues: option 3, staged behind option 2.**

**What NONE of them do** is make the `[k]` form as good as the un-hinted one for
free. The gap is not an oversight in the hover feature; it is that `fn F [k] …`
is sugar whose desugaring is not a refinement of the source but a rewrite of it,
and diagnostics that follow the SOURCE have to be told about the rewrite.

### 5.3 Break 3, the retargeted call

Apply `moduleRetarget` (with the same seed) to the surface's keys before the join
in `pushHovers`, mirroring the `stripMarkers` normalization already there.
Contained; wants a count of how many keys move before it ships, because it runs
on the success path.

### 5.4 The option NOT recommended

**Making silence loud.** The reporter's symptom is "it shows nothing", and they
cannot tell a position with no fact from a position the tooling never reached. A
tooltip saying `x — no value here` (the string `show` already prints) would
remove that ambiguity at a stroke. It is deliberately not proposed as a fix,
because `docs/16` argues the opposite case at length and the argument is sound:
a missing TYPE is the ordinary case — an unchecked block, a splice, a binder no
path reached — so making it loud sends readers after bugs that are not there. It
is recorded here because it is the obvious idea, it is a user-facing judgment
call rather than a technical one, and someone should decide it deliberately
rather than rediscover it.

---

## 6. Reproducing any of this

`Dllbc/Tests/HoverRepro.lean` holds the nine variants at the line numbers §1
quotes; `Dllbc/Tests/HoverProbe.lean` holds the delta dumps and the constructor
spines. Both are left in the worktree, out of the default target and uncommitted — the
committed record is `Tests/ShowSpans` (S7), which asserts the residual through
`#guard_msgs` rather than through a comment. That follows the corpus's own
ruling: `Tests/HoverSpans.lean` and its 37 pinned positions were deleted in
`d3c5194c` as a non-assertable span file, and `docs/18` exists because `show`
turns the same question into something `lake build` can hold.

To re-measure a position, one `lean_hover_info` call at its line and column. To
see why it answers as it does, `#eval` the delta dump — `modulePathsD { initSt
with hover := true, pointHover := true }` on the `prog_parse` twin — and read the
keys. The keys are the whole story; every break in this document is two terms
that were supposed to be one.
