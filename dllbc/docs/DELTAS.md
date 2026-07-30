# DOC-DELTAS — where the mechanization corrects or refines `design-arrays-slices.md`

Every place M24's implementation departs from the design note, with the reason. The
note gets **one** amendment pass from this ledger at merge review, rather than an
archaeology dig through commit messages.

Each entry says what the note says, what the implementation does, and why. Entries are
grouped by kind: **CORRECTION** (the note is wrong), **REFINEMENT** (the note is right
but under-specified, and the implementation had to choose), **GAP** (the note assumes
something that does not exist), **RESTRICTION** (a real limit the note does not state).

---

## CORRECTIONS

### C1 — `arrCat` and `acons` have no element-type argument (¶1.3)

*Note:* `arrCat : Π (T : Type₀) (m k : Nat) → Array m T → Array k T → Array (add m k) T`.

*Implementation:* `arrCat m k a b`, `acons n x xs`. `aget` and `arrRec` keep their `T`.

*Why:* nothing needs it. An `Array` is never applied, so these two constants' result
types are always **checked** against an expectation and never synthesized — the element
type is recovered from the expected type. Meanwhile the merge normalization and the ⇝
fold would each have had to MANUFACTURE a `T` they cannot read off a value tree, since Ω
records extents, not element types. `aget`'s result type genuinely *is* `T` and must be
synthesized, so it keeps its argument, as does `arrRec`, whose premise types mention `T`.

### C2 — ¶3.3's lifecycle ends the loan one step too eagerly

*Note:* the trace finishes `let x = a[0];` with "the read demands a's node; a loan marker
is in owned position, so §2.2 forces End-Mut ℓ first: the payload plugs into the marker,
m dies".

*Implementation:* the element read succeeds and `m` stays live.

*Why:* §2.2's own wording is "every loan marker in owned position **within the value it
is about to move**", and the value about to move is one element, which carries no marker.
Implementing §2.2 precisely gives strictly more than the trace: an element and a disjoint
range of one array, both live — which is the design's headline arriving one paragraph
before ¶3.4 claims it. Rejoin is unaffected and is demonstrated on the demand that
genuinely wants the whole array.

### C3 — ¶3.5's overlap needs no owned-versus-loaned test

*Note:* "after the first carve the extent map is `[(0,3,loaned ℓ₁), (3,rest,owned)]`, and
no *owned* leaf contains `[2,5)`. Premise (1) fails."

*Implementation:* `[2,5)` is contained in **neither** leaf — it straddles the boundary.
The rejection is "no leaf contains it", full stop.

*Why:* two segments cannot overlap, so a range crossing a segment boundary has no leaf at
all, whatever its status. The rejection is cheaper than the note claims.

### C4 — a request *contained* in a loaned leaf demand-ends rather than rejecting

*Note:* ¶3.5 reads as though any loaned leaf rejects.

*Implementation:* a request contained in a loaned leaf ends that loan and retries
(§5.2's demand-end rule reaching its sixth site); only a straddling request is rejected.

*Why:* this is the calculus's existing character, **probed rather than assumed**:
`let p = &mut x; let q = &mut x;` is accepted on `main` today, leaving
`x ↦ loanₘ ℓ0, p ↦ ⊥, q ↦ borrowₘ ℓ0 3`. It is also what makes ¶3.6's own group trace
work — `let z = a[0]` must end the group to read across it. Two live overlapping mutable
borrows remain unrepresentable; only the *moment* of rejection differs from the note (at
the dead borrow's next use, not at its creation), and both halves are tested.

---

## REFINEMENTS

### R1 — `Le` and `add` live in the kernel

The carve's premises are *stated* against both — premise (2) IS a `Le`, premise (3)
decomposes an extent with `add` — and a kernel rule cannot cite a library it does not
import. Two syntactically different `add`s would never convert, which would break exactly
the conversion the residue-transition decision exists to make definitional (¶3.4's audit).
Both moved to `Pure.lean` with `Std` aliasing them; single-source-of-truth asserted by
test. Recorded as the §9 "`Le` as a primitive former" pressure arriving from a second
independent direction — this strengthens that filing rather than settling it.

### R2 — an uncarved array carries no wrapper (¶1.1)

The note says a single-segment array is "abbreviated to plain σ … since the two are the
same state", and the implementation honours that literally: `§segs` appears only when
carved, and always with ≥ 2 segments. The consequence is that the carve cannot read a
node's total extent off a wrapper. It does not need to — every array-shaped value
determines its own extent (a run knows its length, a segment list sums, an `arrCat` spine
carries both halves) **except** a bare σ, whose extent lives in its `sctx` type. So
`arrExtentPure?` is partial by design. Stamping every array value with its length would
have doubled the representation's one redundancy for nothing.

### R3 — merge is a read-normalization, so ¶3.3's trigger caveat is moot

The note warns that merge "must be robust to being triggered mid-body by a comptime read,
not only by owner demand or the boundary". The way to be robust to a trigger list is to
not have one: every carve merges before it scans, every place operation merges after it
finishes, and **rejoin is merge at `sendPayloadToLoan`** — the moment a payload plugs back
into its marker, which every End-Mut path funnels through (owner demand, the §5.4 audit
collapse, a §6.1 group release). No site can be forgotten because no site is listed.

### R4 — only *runs* merge; two adjacent σ's stay two segments

¶1.1 says two adjacent σ's give `arrCat σ₁ σ₂` as their joint body. The implementation
leaves them apart: the pair already types against `Array (add c₁ c₂) T` by the
extent-consistency check, and ⇝ folds them to that very `arrCat` anyway. Leaving them
keeps merge a pure function of the value tree — no element types, no fuel, no `sctx`.

### R5 — "owned" is MARKER-FREEDOM, not "the body is not itself a marker"

An element cursor parks its marker INSIDE the one-slot run (`§seg [1, Arr [loanₘ ℓ]]`),
because ¶2.1 puts the element and not an `Array 1 T` at an index place. The shallow test
called that body owned, let it merge into its neighbour's run, and would then have handed
the MARKER out as an element on the next read — the silent-marker class §3.2 and §5.2 both
warn about, reached by a new route.

### R6 — a DEGENERATE range request skips the ownership test entirely

Not just the split. Between ¶2.2's take and its refill the segment holds a hole, and the
⇐-fill is its one legal successor; testing ownership first rejected the refill.

### R7 — premise (2) is stated LEAF-RELATIVELY, and the range end is spelled `S^k lo`

Two spelling changes, neither altering what the premise means, both required for it to be
dischargeable at all.

`Le` computes by double `natRec`, so `Le (add b cnt) (add b m)` is stuck on a symbolic `b`
and never converts with the `Le cnt m` a program can supply. Premise (3)'s own logic is
that offsets are leaf-relative; premise (2) now is too.

`add` recurses on its FIRST argument, so `add lo cnt` is stuck whenever `lo` is symbolic —
and at every `a[i]` the count is literally 1, making the obligation read
`Le (add i (S Z)) n`, which no program writes and no library lemma produces. A concrete
count is now unrolled into successors, so `a[i]`'s obligation is `Le (S i) n` — exactly
M13/M14's cursor bound, which is ¶3.5's own claim that range places "take the same terms"
the swap sites have threaded since M13.

### R8 — extent sums are RIGHT-NESTED with no trailing `Z`

`add` recurses left, so `add rest Z` is stuck the moment `rest` is symbolic, and
`Array (add k (add rest Z))` never converts with the owed `Array (add k rest)`. This
looked at first like premise (3) failing and was only the sum being shaped wrong.
Right-nesting also matches the `arrCat` spine the ⇝ fold builds and the
`m ≡ add lo' (add cnt rest)` the transition solves, so all three agree.

### R9 — the simulation relation compares arrays up to ¶1.3's fold

Arrays are the first values in the calculus whose STATE form is coarser than their VALUE.
Merge concatenates runs but must leave a σ body alone, so a checking-mode group release —
a fresh existential at the segment's owed type — blocks exactly the rejoin the concrete
run performs: checking mode ends `Arr⟨1 ▷ [3], 1 ▷ σ₀, 1 ▷ [2]⟩` where executing ends
`[3, 9, 2]`, and both are right. `matchVal` now splits the concrete run by the symbolic
extents and matches segment-wise. ¶3.6 predicts this ("any simulation relation that
reconciled the old case reconciles this one") and is right — but the case is new, and it
silently ASSUMES ¶8.2's obligation 4 (merge is value-preserving), which matters when the
metatheory is written.

---

## GAPS

### G1 — the residue has no surface name, and ¶3.4, ¶5 and ¶6 all assume it does

¶3.4 writes `&mut (*a)[k ; rest]`, ¶5 returns `&mut (Array rest T)`, ¶6 writes
`&mut (*v)[S(i) ; rest]`. In every case `rest` is a σ the CHECKER minted inside premise
(3), with no binder any program can write. ¶5 notices ("more honestly written after the
carve has run") and does not resolve it.

**Partly closed:** `a[lo ; ..]` — "to the end of the segment starting at `lo`". This reads
the residue's extent off the extent map where premise (3) already parked it as a GIVEN, so
it is emphatically not the `sub` ¶2.1 bans: no arithmetic, no new obligation. It makes
¶3.4's second borrow and the exhaustive two-way split writable.

**Still open:** `..` names the residue as a PLACE, not its LENGTH. Any *evidence about*
the residue, and any *call taking* the residue, both need the length as a term. See
§"Open decisions" below.

### G2 — ¶4's Σ-typed slice needs no new type but does need new machinery; BUILT, and it does not solve G1

¶4: "Runtime-length slices … `Σ (c : Nat). &mut (Array c T)` — an ordinary Σ over a
borrow, which §5.2 already declares well-formed. **No new type.**" The TYPE is indeed
well-formed. The MACHINE had never seen a borrow under a type constructor at a telescope
position — §5's own second opacity, never exercised. "No new type" is right; "no new
machinery" would not have been.

**Now built, both sides, green.** `seedTelescope` seeds the parameter as a genuine pair
(a length σ the body can name, plus a borrow carrying an ordinary obligation), and
`processArgs` captures the borrow's loan at a call site while checking the length like any
other argument. A callee destructures it with an ordinary owned match. This is ¶4's
runtime-length slice, delivered.

**And it does not solve G1**, which is what the probe was for: a caller must PRODUCE the
length to construct the pair, so the Σ-slice serves exactly the slices whose length was
already nameable — the case that never needed it. Passing the residue is rejected
(`call: slice payload … does not have its parameter type`), correctly, and no right term
exists to write. A second, independent wall: a RECURSIVE slice-taking callee needs a fuel
bound ABOUT the slice's length, and that length lives inside the Σ where no telescope
entry can mention it; nesting the proof inside too is a second level the machinery does
not have.

---

## RESTRICTIONS

### T1 — recursion cannot decrease through a carved array payload

§8's guard counts only CONSTRUCTOR fields as subterms and deliberately refuses application
spines ("a `Le`-headed neutral has no well-founded subterm order we could appeal to"). A
carve's body split refines the payload σ to an `arrCat` SPINE, so from that moment no
sub-slice is a structural predecessor of its parent. ¶6's quicksort is unaffected (it
decreases on `fuel`, tested green), but "recurse on the sub-slice, no fuel needed" is
closed unless the guard learns that `arrCat`'s array arguments are subterms of their
concatenation — true, and specific to this former. FILED, not built.

### T2 — the residue transition needs the leaf's extent to be a FLEX σ

¶3.2 and ¶8.4 say this for the *signature* case ("rigid length … take the length as a
parameter"). It bites more widely than the note suggests: it applies to every SEGMENT's
extent, not only an array's declared length. A segment whose extent is a constructor tree
(`S i`) or a compound neutral (`add p q`) cannot be sub-carved at a symbolic offset,
because `m ≡ add lo' (add cnt rest)` then equates two rigid terms. A segment whose extent
is a bare σ — a telescope parameter, or a residue a previous carve minted — carves freely.
This is why the three-way split cannot be reached by re-associating the two-way one.

---

## Open decisions (for the merge review)

**The residue's length needs a name.** Three routes, costed:

* **(a) Let the program SUPPLY the residue** — `a[lo ; cnt ; rest | h]`, with premise (3)
  solving `m ≡ add lo' (add cnt rest)` against the supplied term instead of a fresh σ.
  Premise (3) is unchanged (still a solution transition, still no `sub`); it reduces to
  current behaviour when omitted; and it is ¶8.4's own escape hatch, "name the equation and
  carry it, rather than solving it". It has a second payoff: supplying the residue makes
  the *obligation* compute. After `σ_rest := S j` the pivot carve's `Le 1 σ_rest` reduces
  to `Le Z j`, which is ⊤ — so the evidence that could not be written is no longer needed.
  VERIFIED on the arithmetic alone: `Le 1 (S j)` normalizes to `Unit`, `Le 1 rest` with
  `rest` a bare σ does not.
* **(b) Let the carve BIND its residue in the surface** — a real binder form, the most
  honest, the largest.
* **(c) Σ-typed slices** — see G2. **SETTLED NEGATIVE by construction**: the machinery is
  built and green, and the caller must still produce the length to CONSTRUCT the pair.
  Kept anyway, since it is ¶4 delivered and independently useful.

**`arrCat`-aware structural decrease** (T1) — filed, not built.
