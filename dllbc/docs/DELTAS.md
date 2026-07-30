# DOC-DELTAS — where the mechanization corrects or refines `design-arrays-slices.md`

Every place M24's implementation departs from the design note, with the reason. The
note gets **one** amendment pass from this ledger at merge review, rather than an
archaeology dig through commit messages.

**Status:** M24 lane closed at "complete tested array library + carve machinery", branch
`dllbc-arrays-impl`. Eleven commits, full `lake build` green, no regression in any existing
suite. The quicksort LEAF (partition + assembly) is deliberately not started — see the
HANDOFF at the end of this file, which is the brief for that lane.

Each entry says what the note says, what the implementation does, and why., what the implementation does, and why. Entries are
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
M13/M14's cursor bound.

**This is the ledger's best entry.** ¶3.5 claims that `nth2`'s `pij : Le (S i) j` and
`p2 : Le (S j) (len *v)` are "on the nose, the containment obligation the carve rule
demands", and that "range places take the same terms and give them their real job". That
was an argument. It is now literally true: the obligation the carve forms at `a[i]` IS
`Le (S i) n`, character for character the term the swap sites have been threading since
M13 — but only once the spelling is fixed. Written the obvious way it was `Le (add i (S Z)) n`
and the claim would have been false in the one place it was supposed to be exact.

The same spelling is needed for the extent map's RUNNING BASE, found by the three-way
carve: the segment after a width-1 pivot has base `add i 1`, stuck on a symbolic `i` and
never converting with the `S i` a program writes, so `(*a)[S i ; ..]` could not find the
segment it had just created. A concrete count advances the base by successors; a symbolic
one keeps `add`.

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

**FOR WHOEVER WRITES THE METATHEORY, flagged loudly.** ¶3.6 says "any simulation relation
that reconciled the old case reconciles this one". That was rhetorical; it is now an
ASSUMED OBLIGATION WITH A CONCRETE WITNESS. The relation's array case is *defined* by
splitting a concrete run along the symbolic extents, which is sound exactly when merge
preserves values — so obligation 4 is no longer a nice-to-have on ¶8.2's list, it is a
premise of the differential harness's own correctness. If obligation 4 fails, the harness
does not go red; it goes silently green on a mismatch. That inversion is the thing to
know before trusting the differential over array bodies.

### R10 — the library transfer needed three ι-rules to be MECHANICAL

¶1.3 promises the quicksort library "transfers to arrays by replacing `listRec` with
`arrRec` and `Cons` with `acons`. Nothing about the migration requires re-deriving that
mathematics." The mathematics did transfer verbatim — `sorted_append_pivot` and its five
helpers are their list proofs with the container swapped, and they check. What the note
does not mention is that the array constants must COMPUTE the way the list constructors
do, or every step of a transferred proof wants a transport lemma the list proof needs
none of.

Two rules are the obvious ones: `arrCat` computes on an `acons`-headed left argument
(`arrCat (acons x xs) b ⇝ acons x (arrCat xs b)`, which is `append (Cons h t) u ⇝ Cons h
(append t u)`), and `arrRec` fires on the cons view, so a predicate over arrays unfolds on
an `acons` exactly as its counterpart unfolds on a `Cons`. Without them
`SortedA (arrCat (acons h t) …)` does not unfold, and `sorted_append_pivot`'s proof turns
entirely on that unfolding — its own docstring says "Both components are definitional …
which is why no `list_rw` transport appears anywhere in this proof."

The third was invisible until the glue was written, and is the one worth recording: a
nonempty RUN on the left with a non-run on the right peels its head into an `acons`.
`asingle p` COMPUTES to the run `[p]`, so ¶6's own spelling `arrCat (asingle p) r` was
stuck for symbolic `r` — **the doc's chosen notation could not reach the cons view it is
notation FOR**. The rule is the same one read through the other view: a literal is a cons
spine that happens to be written flat.

---

### R11 — ¶1.3's transfer promise is VERIFIED, in full and verbatim

Measured rather than assumed, because it is the claim ¶6's whole cost estimate rests on.
The complete quicksort library now exists over arrays: the predicates (`countA`, `BoundA`,
`SortedA`, `UbA`, `LbA`, `asingle`), the glue stack (`sorted_headA`/`tailA`,
`ub_headA`/`tailA`, `lb_headA`/`tailA`, `lb_boundA`, `bound_arrCat`, `sorted_arrCat`), the
count layer (`count_arrCat`, `count_acons_hit`/`miss`), and M23's permutation keystone
(`noAbove_of_ubA`, `ub_of_noAboveA`, `ub_permA`, and the three `Lb` mirrors).

**Every one is its list counterpart with `listRec ↦ arrRec` and `Cons ↦ acons`, and
nothing else changed.** Twenty-one definitions and proofs; the entire permutation layer and
`count_arrCat` checked first try, and five of the seven glue lemmas did. ¶1.3's "nothing
about the migration requires re-deriving that mathematics" is exactly right, and ¶6's "one
stratum deleted outright (locality), one INHERITED (the pivot glue), none invented" is
exactly what happened. The only thing the note omits is R10's three ι-rules, which are what
make the transfer mechanical rather than merely possible.

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

**Closed, by ROUTE (a):** `a[lo ; cnt ; rest | h]` SUPPLIES the residue's extent. Premise
(3) then solves `m ≡ add lo' (add cnt rest)` against a term the program wrote instead of
minting a σ no binder can name — the same solution transition, still no `sub`, and
reducing to the minting behaviour when the slot is omitted.

**Route (a) is the third instance of a house pattern**, which is a better argument for it
than "smallest": an OPTIONAL surface element that reifies something the checker already
knows, declared rather than inferred, costing nothing when absent. §1.2's `[k]` names the
decreasing position; §3.2's `match h :` names the branch equation; `a[lo ; cnt ; rest]`
names the residue extent. In all three the checker had the fact and the program could not
cite it, and in all three the fix is a binder-free naming rather than new semantics. It is
also the shape chosen for `old *v` over a scope-weird binder — which is precisely why not
route (b), that being the rejected binder pattern.

**The ordering is where the payoff is.** The supplied equation is solved BEFORE premise (2)
is formed, so the obligation is stated over a decomposed extent and often computes away
entirely. ¶6's pivot carve asks `Le 1 rest`, unwritable; with `rest := S j` supplied it
becomes `Le 1 (S j)` ⇝ `Le Z j` ⇝ ⊤, and needs no evidence at all. ¶3.2 says `Le a b` "is
precisely the assertion that `b` decomposes as `a` plus something" — so supplying the
decomposition supplies most of the proof, and route (a) does not merely make the obligation
writable, it deletes it.

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

### G3 — ¶6's honest accounting understates what the partition must return

*Note (¶6, cost 1):* "The partition leaf must now produce its pivot index *together with*
the two carve licenses (`Le i n` and its complement), because the recursive calls carve at
exactly that index."

*Correction:* it must return the licenses AND the RESIDUE EXTENTS. A license alone cannot
be stated, because the thing it would have to be a license *about* — the extent of what is
left after the first carve — is a σ the checker minted and no program can name. With route
(a) the shape is: partition returns the pivot index `i` and the right half's length `j`,
and the body carves `[Z ; i ; S j | le_add i (S j)]`, `[i ; 1 ; j]`, `[S i ; ..]`. The
first license is `le_add`, which the M22 library already had; the second is ⊤.

### G4 — ¶6's partition is a NEW PROGRAM, not a transfer, and the ledger does not say so

¶6's migration ledger is organized as "what disappears / what survives untouched / what
gets built", and its three costs are the partition's extra returns, the both-halves-before-
either-call ordering, and "the pure library gains an array layer … Call it a week of the
kind of work M16–M18 already showed is mechanical".

The array layer IS mechanical, as measured: the predicates, the five glue helpers,
`sorted_arrCat` and `count_arrCat` are their list counterparts with the container swapped,
and they check (R10 records the three ι-rules that make it so). What the ledger does not
say is that **the partition itself does not transfer at all**. M23's partition is a
relational take-and-rebuild over a linked list, returning two lists BY VALUE — §4.1's
idiom, and ¶6's own text endorses it ("The program is §4.1's take-and-rebuild, not
Lomuto's array scan"). The array quicksort ¶6 sketches needs the opposite: an IN-PLACE
scan returning a pivot INDEX, because the recursive calls carve at that index. There is no
list program to port; it is a new one, with its own invariants.

This belongs in ¶6's honest accounting as a fourth cost, and it is the largest of the
four. Everything the note lists under "what disappears" still disappears — the ledger's
accounting of the *predicate* strata is accurate and verified. The gap is only that the
leaf program is counted as surviving when it does not exist yet.

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

---

## Decisions taken (for the merge review)

**The residue's length needs a name — DECIDED: route (a), built, ¶6's three-way carve
green.** The three routes and their fates:

* **(a) Let the program SUPPLY the residue — CHOSEN AND BUILT.** `a[lo ; cnt ; rest | h]`, with premise (3)
  solving `m ≡ add lo' (add cnt rest)` against the supplied term instead of a fresh σ.
  Premise (3) is unchanged (still a solution transition, still no `sub`); it reduces to
  current behaviour when omitted; and it is ¶8.4's own escape hatch, "name the equation and
  carry it, rather than solving it". It has a second payoff: supplying the residue makes
  the *obligation* compute. After `σ_rest := S j` the pivot carve's `Le 1 σ_rest` reduces
  to `Le Z j`, which is ⊤ — so the evidence that could not be written is no longer needed.
  VERIFIED on the arithmetic alone: `Le 1 (S j)` normalizes to `Unit`, `Le 1 rest` with
  `rest` a bare σ does not.
* **(b) Let the carve BIND its residue in the surface** — DECLINED. A real binder form,
  strictly larger, and exactly the scope-weird binder pattern already rejected once when
  `old *v` was chosen over it.
* **(c) Σ-typed slices** — see G2. **SETTLED NEGATIVE by construction**: the machinery is
  built and green, and the caller must still produce the length to CONSTRUCT the pair.
  Kept anyway, since it is ¶4 delivered and independently useful.

**`arrCat`-aware structural decrease** (T1) — filed, not built.

---

# HANDOFF — the quicksort leaf lane

Written for the agent that picks up `dllbc-arrays-impl` and builds the partition and the
quicksort assembly. The carve machinery and the whole pure library are done and tested;
what is left is one genuinely new program plus its assembly. Everything below is either a
pointer to something on the shelf or a constraint the shape has to satisfy.

## 1. Why this is a fresh lane and not a continuation

G4: **¶6's partition does not transfer.** M23's is a relational take-and-rebuild over a
linked list returning two lists BY VALUE — §4.1's idiom, which ¶6's own text endorses
("the program is §4.1's take-and-rebuild, not Lomuto's array scan"). The array version
needs the opposite: an in-place scan returning a pivot INDEX, because the recursive calls
carve at that index. There is no list program to port. It is M23-phase-B-class work with
its own invariants, and it wants fresh context rather than hour-N context.

## 2. The partition's required shape

**Signature.** It must return the pivot index AND the right half's length. G3 records why:
a carve license alone cannot even be STATED about a residue the program cannot name, so
`i` on its own is not enough. The relation `n = add i (S j)` is what makes the caller's
three carves writable.

    fn partition (n : Nat, p : Nat, v : &mut (Array n Nat), …)
      -> Σ (i : Nat) → Σ (j : Nat) → ⟨ensures⟩

**Where the carves happen: in the CALLER, not here.** `partition` mutates `*v` in place
over the whole array and returns indices; `quicksort` then carves. Keeping the carves out
of the leaf is what keeps the leaf's ensures statable over one array rather than over
pieces that do not exist yet.

**What the ensures must carry**, in the shape the assembly consumes:

* the decomposition itself — `Id Nat n (add i (S j))`, or equivalently the exit `*v`
  convertible with `arrCat i (S j) L (arrCat 1 j (asingle p) R)`;
* `UbA p i L` — everything left of the pivot is ≤ p;
* `LbA p j R` — everything right of it is ≥ p;
* count preservation, `Π x. Id Nat (countA x n (*v)) (countA x n (old *v))`.

A design note worth taking seriously: **state the ensures as a decomposition**, because
that is exactly the shape `sorted_arrCat` consumes. The caller's carve then produces
`σ_L : Array i Nat`, `σ_p : Array 1 Nat`, `σ_R : Array j Nat` together with the refinement
`σ_v := arrCat i (S j) σ_L (arrCat 1 j σ_p σ_R)` — definitionally, from premise (3) — so
transporting the ensures onto the pieces costs nothing. If it starts costing a transport
lemma, the ensures are stated in the wrong shape rather than the calculus being awkward.

**The scan.** DLLBC has no loops (§2.5), so the scan is a recursive helper carrying the
scan position and the less-than boundary, swapping through index places. Each swap is two
index-place writes; see `sort2` in `Dllbc/Tests/S24Arrays.lean` for the exact idiom,
including how a symbolic array becomes a run of named elements once its elements are read.

**Branch-equation sites.** The comparison is `if h : leb x p { … } else { … }`, and `h`
is what turns "the test said yes" into `Le`. This is M23's branch-equation feature and it
is not optional — a body that recomputes `leb x p` after the split learns nothing
(§3.2, and M23-iv's wall). `leb_true_le` / `leb_false_gt` / `le_pred_l` are in
`StdLemmas`.

**Recursion.** Fuel-decreasing, `[fuel]`. See §4 below for why nothing else is available
and why nothing else is needed.

## 3. What is on the shelf

**The complete array library** (`Dllbc/StdLemmas.lean`, M24 section at the end), every
member its list counterpart with `listRec ↦ arrRec` and `Cons ↦ acons`:

* predicates — `countA`, `BoundA`, `SortedA`, `UbA`, `LbA`, `asingle`, `anil`;
* glue — `sorted_headA`, `sorted_tailA`, `ub_headA`, `ub_tailA`, `lb_headA`, `lb_tailA`,
  `lb_boundA`, `bound_arrCat`, and **`sorted_arrCat`** (the pivot glue, ¶6's textbook
  statement in textbook shape);
* counts — `count_arrCat`, `count_acons_hit`, `count_acons_miss`, `count_swap2`;
* the permutation keystone — `noAbove_of_ubA`, `ub_of_noAboveA`, **`ub_permA`**, and the
  three `Lb` mirrors. This is the one that cost M22 its hardest result; it transfers
  unchanged, so the "positional bounds are not permutation-invariant" problem has no
  analogue here.

**The carve machinery.** Three-way carving in ¶6's verbatim shape, with route (a)'s
supplied residue:

    let l = &mut (*v)[Z    ; i ; S j | le_add i (S j)];
    let p = &mut (*v)[i    ; 1 ; j];        -- obligation ⊤, no evidence needed
    let r = &mut (*v)[S i  ; ..];           -- degenerate

`threeWay` and `threeWayCall` in `Dllbc/Tests/S24Arrays.lean` are that, checked, including
passing both halves to calls at their program-named lengths. Copy the shape.

**The bounds vocabulary is M13/M14's, unchanged.** `a[i | h]` wants `h : Le (S i) n` —
character for character the cursor bound the swap sites have threaded since M13 (R7).
`le_add`, `le_add_succ`, `le_add_l`, `le_refl`, `le_trans`, `le_pred_l`, `le_rw_l/r` are
all in `StdLemmas` from M22 and apply verbatim.

**The worked miniature.** `sort2` — an in-place two-element sort carrying M23's quicksort
signature at width two, `Σ (hs : SortedA 2 (*a)) → (Π x. Id Nat (countA x 2 (*a)) (countA
x 2 (old *a)))`, zero declared backs, with three lying twins rejected. It is the assembly
in small: read elements, branch on a comparison, mutate through index places, discharge
both conjuncts against the exit snapshot. Start by reading it.

**The differential.** `Dllbc.Tests.S9Diff`'s harness takes array bodies; `matchVal` has the
`§segs`-versus-run case (R9). Three array callers are already through it. The List-vs-Array
quicksort differential the standing brief asks for plugs in here.

## 4. Two filed items this lane must NOT need

Both are real and both are deliberately unbuilt. If the leaf seems to need either, the
program shape is wrong, not the calculus.

* **T1, the `arrCat`-subterm guard extension.** Recursion cannot decrease through a carved
  array payload, because the carve refines the payload σ to an `arrCat` spine and §8's
  guard refuses application spines. **Quicksort recurses on FUEL**, which is M23's shape
  anyway, and `walk` in the suite is that shape tested green. Do not reach for the guard
  extension.
* **G2, Σ-typed slices.** Built and green for length-known slices, and honestly scoped —
  but not needed here, because route (a) means every length a call site passes is
  program-named. If a callee seems to want `Σ (c : Nat). &mut (Array c T)`, the residue
  is unnamed somewhere upstream; supply it at the carve instead.

## 5. Standing constraints from the brief

Fuel-decreasing; whole-value ensures (`Sorted ∧ Π count`-preservation over the exit
snapshot); **zero declared backs**; lying twins per conjunct; and the List-vs-Array
differential on shared inputs (two implementations, one spec — disagreement indicts one of
them). Keep this ledger growing; the design note gets one amendment pass from it at merge
review.

---

## M25 — the partition, the sort, and what running them found

### C5 — the §5.4 exit snapshot was the STATE form, so no carving function could state a postcondition

*Note (¶1.3, ¶3.3):* an array's snapshot is its `arrCat` spine; "a carved-and-rejoined
array has the SAME snapshot as one that was never carved".

*Implementation, before M25:* `readC` (⇝) folds every comptime reading through
`arrFoldDeep`, but `auditAction`'s §5.4 exit-snapshot substitution injected the borrow's
collapsed payload RAW. So after any carve the exit snapshot of `*v` was
`Arr⟨1 ▷ [σx], m ▷ σt⟩` — a `§segs` node — and `countA`/`SortedA`/`UbA` are `arrRec`s
that compute on the cons view and are stuck on one. Every postcondition naming `*v` was
unstateable, with a rejection that reads like the predicate being wrong.

*Why it hid until a real program existed, which is the part worth recording:* merge
concatenates adjacent RUNS and deliberately leaves a σ body alone (R4). A carve at
CONCRETE extents therefore rejoins to a plain run and never needs the fold — that is
every M24 test, `sort2` included. A SYMBOLIC segment cannot merge, and that is what every
program with a runtime-computed split point is made of. R9's "arrays are the first values
whose state form is coarser than their value" had exactly one consumer that had never been
exercised.

*Fixed:* fold before substituting. An unfoldable (still suspended) payload is left alone
and rejected at `hasType`, the documented behaviour, so nothing became more permissive.

### C6 — the carve did not demand-end a SUSPENDED NODE, only a suspended leaf

§5.2 is "any rule that READS a place ends the suspensions parked there before it looks",
and a carve reads the place: it consults the extent map. `carveAt` demand-ended a loaned
LEAF and a marker buried in a one-slot run, but not the case where the WHOLE payload is
out on loan. That case has exactly one producer — a reborrow into a call. `f(&mut *v)`
parks a marker at `*v`, and the group's release plugs the payload back only on demand, so
`arrExtent` had no array value to read and the message ("`loanₘ ℓ3` is not an array value")
reads like a representation bug.

`readR` performs the same collapse at its own reborrow and match sites; this is that rule
reaching the carve. Bisected to five probes: peel+call OK, carve-without-call OK,
swap-writes-without-call OK, self-recursion OK, carve-AFTER-call the only red. So the
missing case is precisely "a recursive array program carves the argument it just handed to
its recursive call", which is every such program and none existed before M25.

### C7 — base alignment does not determine the leaf, and ¶3.2's route-(a) note says it does

*Note (the route-(a) implementation comment):* "The leaf is selected by BASE ALIGNMENT
here rather than by the evidence's type: `a[lo ; cnt ; rest]` says where it starts, so
there is nothing to disambiguate."

*Correction:* a ZERO-EXTENT segment shares its base with the segment after it, so a node
holding one has TWO leaves at that base and the wrong one wins. Zero-extent segments are
unreachable symbolically — a residue σ is never known to be zero — and routine concretely,
since every runtime-computed split has an empty side eventually. The supplied
DECOMPOSITION is what disambiguates, so the selection now prefers the leaf whose extent
already is `add cnt rest`, then any non-empty leaf (an empty leaf cannot contain a request
of positive width).

---

### G7 — route (a) refines a UNIVERSAL, and no caller is ever held to it

**The one soundness finding, and it is decision-relevant for the merge review.**

Premise (3) solves the supplied residue by `reflUnify l.count (add cnt rest)`. When the
leaf's extent is a TELESCOPE PARAMETER's σ — always, in the programs route (a) exists for
— that is a refinement of a UNIVERSALLY quantified length against terms that may be
unrelated existentials, and nothing records the induced constraint in the signature. So
callers are never held to it:

```
fn resCarve (n : Nat, i : Nat, j : Nat, a : &mut (Array n Nat)) -> Unit {
  let l = &mut (*a)[Z ; i ; S j | le_add i (S j)]; () }
```

checks — and so does a caller passing `n = 2, i = 5, j = 5` with a two-element array.
EXECUTING that caller errors: `Refl: both endpoints are rigid (S (S Z) vs S (add 5 (S 5)))`.
So `checkFn` accepts a program the concrete machine gets stuck on, which is M8/M9's
differential property failing rather than over-approximating. The concrete-length case is
safe — `reflUnify` fails honestly there; only the symbolic-parameter case refines.

M25's programs are true and do not rely on the hole, but they cannot PROVE they do not:
`partitionA` and `splitA` therefore return the decomposition as an ordinary Σ-conjunct
(`Id Nat n (add k (S jj))`, `Id Nat m (add k r)`) so the fact is established and
twin-testable, even though the carve does not consume it. In both programs that conjunct
is `Refl` or one `id_congr`, so the honesty is nearly free.

Two ways out at review: premise (3) refuses to refine a σ that is a telescope parameter
(and the program cites an equation instead — which these programs already return), or the
signature records the induced constraint. Filed, not decided.

### G5 — a callee's segment borrows are never released when it returns

**The one M25 did not close, and the reason the executing differential stops at three
elements.** In executing mode a callee's range borrows stay live in the caller's array
after the call, so the caller sees the callee's leftover segmentation rather than one
leaf. `mergeArrays` cannot rejoin it — a loan blocks the merge (R4) — and the caller's
next carve then asks premise (3) to unify the leftover leaf's extent with the
decomposition the program supplied.

Minimal reproducer, one call deep: `splitA [3,1,4]` with `p = 2` fails with
`Refl: both endpoints are rigid (S Z vs S (S Z))`; `splitA [1,3]`, whose caller does not
carve again, runs correctly. So it is not the recursion, the length or the program.

**In CHECKING mode this is invisible, and invisible for a principled reason: §6.2's
opacity re-mints the callee's payload as a fresh σ at the declared type, so the caller
always sees an UNCARVED array.** That re-minting is not merely an over-approximation of
what the concrete machine does — it is a REPAIR of it. §6.1 already flags the family ("a
group releases atomically where the concrete machine ends lazily"); this is the first
instance where the CONCRETE side is the one that is wrong, and it is therefore the first
one that cannot be dismissed as the checker being conservative.

What it needs is a scope-aware release: when a call returns, the loans its body created
must end, exactly as the §5.4 audit collapses them on the checking side. That is not a
carve-rule change and it is filed rather than built.

### G6 — `a[lo ; ..]` is unusable once a residue can be empty

`..` reads the count off the segment STARTING at `lo`, and a zero-extent residue is
dropped by ¶1.1's drop-empty, so at a concrete length there is no segment there at all.
Every residue in M25's programs is therefore named explicitly (`a[S Z ; m2]`,
`a[S k ; jj]`), which routes the request through the carve's obligation machinery instead
of through `restOfLeaf`. G1 records `..` as the partial closure of the residue-naming
problem; this is its limit, and route (a) supersedes it wherever the length is nameable.

---

### R12 — the FUNCTION BOUNDARY is load-bearing, for a reason ¶5 does not give

¶5's advice is "carve inline; reach for the function only when you want the abstraction
boundary". In the array quicksort the boundary is what makes the program possible at all.

A body that peels a head must first match its own length (`match n { S(m2) => … }`),
because only the supplied-residue form `(*a)[Z ; 1 ; m2]` converts against the resulting
rigid extent — the index place `a[i]` has NO residue slot and is rejected outright. But
matching the length is exactly what T2's rigid-extent restriction then punishes: the array
can no longer be carved at a symbolic offset. So one body cannot both select a pivot and
carve at the returned index.

§6.2's opacity is the way out. A call re-mints the caller's payload as a fresh σ at the
declared type, so an array the callee matched, peeled and re-carved comes back UNCARVED
and with a FLEX length — precisely the state the three-way carve needs. `partitionA` is a
separate declaration for that reason and not for modularity.

### R13 — two independent SYMBOLIC indices into one array are unreachable, so Lomuto is not writable

`(*a)[i | h]` on a symbolic array works. A second read at an unrelated `j` cannot: after
the first carve the leaves are `[0,i)`, `[i,i+1)`, `[S i, rest)`, and no evidence a program
can hold selects a leaf for `j`. So `swap(a[i], a[j])` at two runtime indices — Lomuto's
inner loop, and the shape ¶6's own G4 correction calls for ("an IN-PLACE scan") — is not
writable at all.

What is writable is a scan in which every element access is at index 0 of a segment the
program itself carved. ¶6 says "the right sub-slice is a segment with its own zero; there
is no reindexing" as a convenience; it is a HARD CONSTRAINT, and it determines the
algorithm. M25's `splitA` peels the head, splits the tail recursively, and performs at most
ONE swap per level — with the boundary element, reached by a three-way carve, so that both
sides of the exchange are at their own segment's zero.

### R14 — there is NO η at length zero, so a sort's base case is a lemma

`SortedA Z σ` is a stuck `arrRec` — the recursor fires on `Arr`, never on the length index
— so an opaque length-zero payload does not compute to `Unit` and a base case cannot be
discharged by the trivial term. `sortedA_nil` and `splitA_nil` carry `Id Nat n Z` and kill
the cons case with `znots`.

This also determines how the sort tests emptiness. `match n` would refine the length to
`S m2` and block the three-way carve (T2), so `quicksortA` branches on `leb 1 n` and turns
`Le n Z` into `Id Nat n Z` with `le_zero_eq`. Every list program in the corpus matches its
scrutinee; the array sort cannot.

### R15 — ¶6's locality stratum is deleted for the SORT and reappears at the PARTITION's interface

¶6: "one stratum deleted outright (locality), one INHERITED (the pivot glue), none
invented." The first two are verified (R11) and the third is not quite right.

A split point is a statement about two parts of one array, and the honest way to name them
is to carve — which is ¶6's claim, and it holds for the sort, whose sub-slices are its own
carves. It does not hold across a function boundary, for three independent reasons, each
probed: the return type is fixed before the carve that would name the parts exists;
`Array n` and `Array (add k r)` convert only after the CALLER's carve has refined `n`, so
the equation cannot even be STATED in the signature; and the parts cannot be returned by
value either, because reading a segment MOVES it and leaves the borrow holding a hole.

So M25 invents one positional predicate for the scan (`SplitA`) and one for its result
(`PartA`), plus five crossings. The honest claim is **one stratum deleted, one inherited,
one invented at the leaf's interface** — and the invented one is small because `PartA`'s
skip-zero case yields `LbA`, the library predicate, so the bridge to `sorted_arrCat` is a
single lemma with no monotonicity layer. Every crossing is an induction on the left array
and nothing else, the same `arrRec` shape as `bound_arrCat`: the stratum is new, the KIND
of work is not.

### R16 — the staging tax, counted rather than built

Six filings for `old`-on-consumed-things now exist. `quicksortA`'s body carries FOUR staged
builders and `splitA` one; M23's list quicksort carried four. None does mathematical work.

The strongest single case is `mkTop`: the permutation conjunct's far endpoint is
`countA q n (old *a)`, `id_trans` takes its three points EXPLICITLY, and no body term can
write `old *a` — so the endpoint has to be captured in a closure built before the partition
call, while `*a` still IS the entry value. Two further consumption facts cost a debugging
cycle each and belong with it: `match fuel { S(f2) => … }` CONSUMES `fuel`, and passing a
PROOF to a call MOVES it, so `hfuel` must be captured before `partitionA` takes it. M23's
quicksort hit neither, because it never mentions `fuel` after the match and its partition
takes no proof.

### R17 — G4's fourth cost, measured

G4 recorded that the partition is a new program rather than a transfer. Measured: the
partition layer is 21 new pure items (2 predicates, 5 crossings, 8 projections, 4 count
lemmas, 2 nil lemmas) and three declarations. **Every pure item checked first try.** The
programs did not: the failures were all machine gaps (C5, C6, C7) or spelling
(R7's `S k` versus `add k 1`, which is why `splitA_cat_e1` is stated at skip `S k` and
`splitA_cat_i0` at skip exactly `k` — the general `add k t` form is more general and
unusable). Nothing in the mathematics was hard; everything in the plumbing was new.
