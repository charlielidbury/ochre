# Reviewer 9: cold review of `notes/typed-fragment-proof.typ`

Reviewer 9, 2026-09-30. Read: the whole paper (`paper/main.typ` and every section, the appendix included), `RULES.md`, the proof, the plan it carries out (`notes/typed-fragment-plan.md`), the cited `meta-lean` lemmas, and the two cited probes. This review is of the proof as of commit c0e3b665, which records the planned ghost-borrow fix for DropProbe and follows the renumbered claims table; the file has not changed since. Probes of my own: `lean/Scratch/Reviewer9Probe.lean` (38 verdicts in eight blocks, each asserted with `#guard`; run with `lake env lean Scratch/Reviewer9Probe.lean` from `ochr/core/lean`).

## Score: weak reject

(As an appendix proof in a POPL/ICFP submission.)

The proof is organised well. It walks the definition's case tree along one ground instance. It keeps truth of hypotheses as an invariant. It transfers call-site types to the callee's instance through the frame property and injectivity of contexts. And F6 stops a data function's run from depending on its hypotheses. I found no program in F that breaks the theorem, and I think the theorem is probably true of F if naturality holds. But the proof does not yet establish even the conditional statement. Four problems are in the part the proof says is proved, not in the assumption:

- the agreement relation cannot support the steps that read through a borrow, the [Rec] measure among them;
- agreement is undefined at states that accepted F programs reach;
- the assumption's interface does not match how the proof uses it;
- termination does not follow from the lemmas cited for it.

On top of that, Assumption 4 holds almost all of the operational content, and it is known to be false for the full rules. A reader should be told plainly that this is a reduction of soundness for F to a simulation lemma, not a proof of soundness.

No finding is FATAL. I found no counterexample to Theorem 10 or to its corollaries as stated.

The planned ghost-borrow fix that c0e3b665 records does not cover every way the symbolic path ends a borrow early. `Bad4` fails like `Bad2` with only one owner and no `Pick`, and the fix as described does not reach it (finding 7). F5 therefore has to stay until the fix covers that channel too.

## Findings, most severe first

### 1. GAP: agreement does not fix what is behind a borrow, so neither the tail steps nor the [Rec] measure follow "by agreement"

*Location.* Definition (agreement), lines 49–55. Theorem 10's proof: [Tail-match] (line 185: "after [Access], the scrutinee's content has the same constructor on both"), [Tail-split] (line 186: "whose content after [Access] is α(σ) by agreement"), "Callees are safe" (line 174), and the claim's lemma-call bullet on $(j, |beta_j|)$ (line 208). Lemma 9's setup, $beta(sigma_i) = u_i$.

*Claim.* (A1)–(A4) let the proof read, on the ground path, the value seen through a borrow (`match *x`, the content of the decreasing borrow argument) as the symbolic value under α.

*Why it fails.* (A2) compares states only after every borrow is ended. Resolution puts each borrow's content back at its loan and forgets where the borrow pointed. (A3) and (A4) say only which positions hold borrows and which owners they reach. None of the four clauses says what a borrow currently holds. Here is a pair of states that satisfies all four clauses:

- symbolic: `c ↦ loan₁`, `x ↦ borrow₁ (S loan₂)`, `p ↦ borrow₂ σ`, with α(σ) = `Z`;
- ground: `c ↦ loan₁'`, `x ↦ borrow₁' loan₂'`, `p ↦ borrow₂' (S Z)`.

Both resolve to `c ↦ S Z`, with `x` and `p` ⊥. Both paths hold borrows at `x` and `p`. Every owner set is `{c}`. Both states are well formed. But symbolically `p` borrows the predecessor field of `x`'s target, and on the ground it borrows the whole target. So `match *p` takes arm `Z` symbolically (α(σ) = `Z`) and arm `S` on the ground. And if `p` is the decreasing argument of a recursive call, the symbolic argument is a strict subterm of the entry value while the ground argument is the entry value itself. So "the ground run takes arm i", the claim that the recursive call's ground argument is smaller, and the construction of $beta_j$ from the ground arguments do not follow from agreement as defined.

*Missing argument.* Such pairs are presumably unreachable, since both runs create their borrows from the same syntax, and under α a stuck call's sealed programs place the hole where the ground call points (`close_cur`, `close_back`). But that is an invariant, and the relation has to state it and preserve it. For example:

- (A5) at every position that holds $"borrow"_ell w_s$ symbolically and $"borrow"_(ell') w_g$ on the ground, the resolved contents agree under α.

Assumption 4 must then keep (A5) as well, and the tail steps and the measure should cite it. Without (A5), the recursive half of the induction has no justification. That includes termination (finding 4), because every decrease the proof uses is a decrease of a value behind a borrow.

### 2. GAP: agreement is undefined at reachable states of F (a ghost inside a borrow)

*Location.* Definition (agreement) (A2), line 52. The paragraph after it (lines 57–59: "ρ is the resolution of … property 4, which is mechanised"). Lemma 7 (b) ("its resolved content, read through the ghost, is unchanged").

*Claim.* ρ, "which ends every borrow", is defined on the states the walk visits, and it is the order-independent resolution that `end_order_indep` mechanises.

*Why it fails.* [End ℓ] requires the borrow's content to be whole (appendix, after [Assign]). F admits D53's `mem::replace` pattern: it moves out through a borrow and refills before the borrow ends. `Replace(x : &Nat) := let v = *x; *x := S v` is accepted (probe `R9Ghost`). [Tail-let] splits it after `let v = *x`, and the walk needs agreement at that point. There `x`'s content is a ghost, so no sequence of [End]s can end `x`, and ρ does not exist. The checker agrees: `ReplaceObs` forms an `Id` at that point and is rejected with "[D53] a borrow ends while its content is partly moved out". The mechanised `end_order_indep` is for a machine without ghosts, and its first conjunct (the resolved state exists) is false for the current rules at this state. Lemma 7 (b) quietly uses a resolution that "reads through the ghost". Nothing defines it.

*Missing argument.* Define resolution to be ghost-transparent: it ends a borrow whose content holds `ghost(v)` as if the content were `v`. Prove order-independence for that resolution, and use it in (A2) and in Lemma 7. Alternatively, restrict F so that no tail step boundary falls between a move through a borrow and its refill. But `Replace` is in F as written.

### 3. GAP: Assumption 4's interface does not match its uses

*Location.* Assumption 4 (lines 65–71). "Callees are safe" (line 174). Lemma 8 (lines 143–145). The claim's `let` bullet (line 202) and its lemma-call bullet (lines 205–206).

The assumption says: if every data function that `t` calls is safe in the sense of Theorem 10 (i), and the start states agree, then the machine run of `t` succeeds (N1), the end states agree (N2), drops and pops succeed (N3), and resolution commutes with valuation (N4). The proof uses it in four ways that this does not cover.

- (a) *Global callee hypothesis.* "Safe in the sense of (i)" means safe at every ground instance. For $d_k$'s own recursive calls that is the conclusion being proved. The proof only has $d_k$ safe at smaller instances, and to know which instance a ground call hits it needs agreement at the call point (finding 1). The hypothesis has to be per call: "each call that the ground run of `t` makes is safe at its ground arguments". It should come with a statement of how the ground arguments relate to the symbolic ones.
- (b) *Calls at instances that are not ground.* A ground instance puts a numeral behind each borrow parameter. Accepted F programs call functions whose borrow argument holds a ghost: `G(x : &Nat) := let v = *x; W(x)` with `W(y : &Nat) := *y := 0`, and the same with a recursive callee, `GR` calling `WR` (probe `R9Ghost`, all accepted). The induction hypothesis says nothing about such calls, so "callees are safe" is not available for them. On the symbolic path such a call is safe only because [T-Call] runs `W`'s body, or [Close] rejects the non-whole argument. That argument belongs inside the assumption, and termination at these instances is then assumed too, not inherited from the induction.
- (c) *Copying runs.* N1 and N2 are about the runtime machine, in which a read of a `Nat` moves it. The proof applies them to runs that copy. That covers the sides of `Id`, the arguments of `Eq` in Lemma 8, and data steps inside proofs in the claim, all of which run on private copies where every read copies and sees through ghosts. The two runs differ: `Id Nat (let z = a; a) a` is accepted by `refl` (`IdCopies`), while `let z = a; a` as runtime code is rejected (`RunTwice`, probe `R9Copy`). The assumption needs a clause for the erased mode.
- (d) *Intermediate states.* N2 relates the end states of `t`. The measure needs agreement at the call point inside `t`, and Lemma 8 and the claim use agreement for states with a pushed parameter frame ("That state agrees with $Omega_(g 1)";" (overline(x) |-> overline(w)_g)$"). Both have to be stated, either as further clauses or by applying the assumption to the pieces of `t` and to the frame push, with the per-call hypothesis of (a).

### 4. GAP: termination does not follow from the cited lemmas

*Location.* The table row "`exec_total`, `termination_of_calls` … a run terminates if every call it makes does" (line 90). The paragraph "Termination is not a separate assumption" (line 212).

*Claim.* The mechanised structural half says that a run terminates if every call it makes terminates. The induction supplies the calls, so termination comes out of the induction.

*Why it fails.* That is not what the Lean says. `exec_total` (`GuardTerm.lean:212`) assumes `∀ h ∈ t.calls, ∀ ws, CallTerm P h ws`: every function that the term names terminates on every argument list, from every call point. `termination_of_calls` (`GuardTerm.lean:354`) likewise assumes `CallTerm` for every recursive definition at every argument list. For a recursive $d_k$, `t.calls` contains $d_k$, so the hypothesis is the whole termination statement for $d_k$. That is exactly the `sorry` the `GuardTerm.lean` docstring describes. Neither lemma can be applied to a recursive body with the induction hypothesis in place of its premise. What is needed is a trace-indexed form: "a run terminates if each call it actually makes terminates at the arguments it is made with". That is not mechanised. Even with it, knowing which arguments the ground calls get needs finding 1. So termination is part of what N1 assumes. The paper should say so and not claim it for the induction.

### 5. GAP: the transfer from rule set 1.3 cannot be "folded into the assumption"

*Location.* Line 95 ("Transferring these … is part of Assumption 4. So are moves … Everything below Assumption 4 is proved on paper"). Line 22.

The cited lemmas are used outside Assumption 4, in the part the proof calls proved:

- Lemma 7 (b) uses `frame_local` directly;
- Lemma 9 uses `frame_local`, `callRun` and `ctx_inj` directly;
- the definition of agreement relies on `end_order_indep` and `endAll_endSeq` for current-rule states;
- the termination paragraph relies on `exec_total`.

N1–N4 mention none of frames, contexts, or the existence of resolution. So the assumption would have to grow to absorb them, or the proof has to port them. For the existence of resolution the port fails outright (finding 2). Moves are not folded in either: the proof reasons about ghosts itself (Lemma 7 (b)) and gets that part wrong (finding 2).

The cited lemmas themselves, checked with `#print axioms` in `meta-lean`:

- *Sound as cited.* All of them exist and none uses `sorryAx`. `end_order_indep`, `endAll_endSeq`, `frame_local`, `call_effect`, `ctx_inj`, `exec_wf` and `exec_rename` say what the table says, for the v1.3 machine.
- *Hypotheses omitted.* The `close_*` equations hold only if the isolated call run completes, and they have argument hypotheses ("loan-free, not moved, no borrows") that the claims table calls "not yet in Lean". The proof's table leaves these out.
- *Misdescribed.* `exec_total` and `termination_of_calls` (finding 4).
- *Stale docstrings.* The Lean docstring of `end_order_indep` calls it "Property 7"; the paper and the proof number it 4. The `GuardTerm.lean` docstring says `exec_wf` is `sorry` in `WF.lean`; it is not.

### 6. GAP (declared): Assumption 4 is the hard half of the theorem

*Location.* Assumption 4 and lines 73–77.

N1–N4 amount to a complete simulation between the typing judgement (with [Close], [Seal] and eager renormalisation, generalisation records, moves and erased private copies) and the ground machine. Below the assumption, the proof does the case analysis at tail matches, the truth bookkeeping, and three lemmas. The assumption is false for the full rules (DropProbe), and F5 restores it only by an informal argument. The proof is candid about all this, but "Theorem 10" in an appendix will be read as a soundness theorem. Please present it as "soundness of F, conditional on Assumption 4". Name the three risks the proof already lists, and add findings 1–3 here to that list.

### 7. GAP (about the planned fix, not about Theorem 10): the ghost-borrow fix as described misses a second early-end channel, so it cannot lift F5

*Location.* F5 (line 32: "The checker fix for this (ghost borrows) is expected to make F5 unnecessary"). "Naturality fails without F5", the last two bullets (lines 261–262).

*Claim.* The planned fix covers the way the symbolic path ends a borrow earlier than the ground path. When [Access] ends a borrow only because its loan sits in a sealed fill that has other possible owners, the fix releases only the accessed owner and keeps the borrower as a ghost borrow until its binding dies. After that, F5 should be re-checked and lifted.

*Why it fails.* There is a second channel that has one owner, not several. A match on a place whose content is a sealed program ends every loan inside that program (the rule that matches end loans in neutral heads, D29), because the loan's position inside the neutral is unknown. On the ground the loan sits deeper and survives the match. Nothing about this involves other possible owners, so the fix as described does not apply. Probe `R9Bad4`:

```
def Bad4 (x : &Nat) (a : Nat) : Unit := ( x := TailM(&a); match a { Z => (), S _ => () } )
```

- `Bad4` is accepted. At the generic call, `TailM(&a)` closes off, and `a` holds a fill with `x`'s hole inside. The tail match on `a` ends `x`, so `a` is loan-free when it is dropped.
- At `a = 1` it fails with "[Drop] a goes out of scope while it is borrowed" (`RunBad4S`). `TailM` returns a borrow of `a.1`, the match sees the head `S` and ends nothing, and `a` dies while `x` still borrows it.
- At `a = 0` it runs (`RunBad4Z`), because `TailM` returns `&a` itself and the match ends `x` on the ground too.
- `Bad5` is the same with a local borrow declared before the owner, as in `Bad3`.
- All of this holds with and without D53.

`Bad4` and `Bad5` assign a borrow into an older variable, so F5 excludes them, and Theorem 10 for F is not affected. But the line 32 expectation is wrong for this channel. The fix is also not a simple extension here. To keep `x`'s loan in `a`'s fill as a ghost, the checker would have to keep a live loan inside the very neutral that [Tail-gen] is about to generalise away, and generalising a hole away is one of the counterexamples in the paper's table of side conditions ("a hole generalised away").

*Missing argument.* Either the fix handles every end that is uncertain (a different owner, or a different position inside the same owner), or F5 stays.

### 8. MINOR: author's attack point 1 (F5): no counterexample in F, but the written argument has a false step

I looked for a program in F that ends a borrow earlier on the symbolic path and then fails at a ground [Drop] or pop. The symbolic path ends a borrow early in two ways. One is a hole in several fills (probe `E2`: reading the other owner of `Pick`'s hole). The other is a match on a fill, which ends every loan inside the fill even when it has one owner (`E3`). I also tried returning a parameter after an early end (`E4`) and a borrow in flight that outlives a block-local (`E1`). Every candidate either runs at its ground instances or is rejected on the symbolic path too (probe `R9Early`, 9 verdicts).

The argument at lines 32 and 255 says that "a borrower is always declared after every place it borrows". That is false for borrows in flight: a let-block's result, or a call argument, outlives the block's locals (`E1`). The conclusion survives, but by a different route. On the ground, a place can die with a live borrow into it in only two ways:

- If the symbolic counterpart of that borrow is live, (A4) puts the place among its symbolic owners. The symbolic drop then fails too, so this case needs no F5.
- If the symbolic counterpart is ⊥, it cannot be a temporary. A call argument that is ended while in flight is a [Call-err] on the symbolic path. A let-block's result is followed only by drops, and a drop ends only the borrow being dropped, never another one. So it is a binding, and F5's scoping puts it after its target.

Write it that way. It also shows that N3 depends on (A4), which the proof lists only as a risk.

### 9. MINOR: author's attack point 2 (Lemma 7 (a)): true in F, but the case list is wrong and it uses F5

*Location.* Lemma 7 (a), line 130: "An occurrence rooted at a variable holding ⊥ is an error ([Read-err], [Borrow-err], [Assign], [Match-err])."

- *[Assign].* Assigning a whole variable that holds ⊥ is not an error: [Assign] drops the old content, and ⊥ is loan-free. Outside F, `AssignBot` is accepted (probe `R9Clone`). It ends `x` symbolically, then types `Id Unit (x := &c; *x := 5) …`. So the symbolic statement mentions a ⊥ borrow variable, and the ground footprint contains `x`'s ground owner, which the symbolic one lacks. In F this is excluded only because assigning to a borrow variable would assign a borrow, which F5 forbids. Add F5 to Lemma 7 (a) in "Where F's restrictions are used".
- *[Clone].* The appendix's [Clone] has no premise excluding ⊥ (finding 11). By the appendix, `clone(x)` of an ended borrow variable succeeds. The checker rejects it (`CloneBot`). Cite the corrected rule.

### 10. MINOR: author's attack point 3 (Lemma 6 (c)): true in F, and the private-copy half is vacuous; one definitional gap

In F, F3 (no match in a type) and F4 (no non-tail data match) mean that [Split-gen] never runs. [T-Split-goal] is excluded, and the machine closes calls off and never generalises. So the only records are made by [Tail-gen], on the main path of some arm, and the "private copies" clause of (c) never arises. Say so; it is a simpler argument than the one given.

For sibling arms, the argument is right. A text made in one arm can be derived again in another only if the arm-local abstract values it mentions are shared, and they are not. Values common to both arms appear unrefined in the text, and α gives them the same value on both.

The gap is that "extend α … for each record, in the order the records were made" (line 105) includes records whose text mentions abstract values that exist only on another path, or only in an earlier definition's check (Δ and records are global). α does not cover those values, so $"nf"(n alpha)$ is not ground and (a) fails for them. Restrict the extension to records whose text mentions only values that α covers, and show those are the only records the current path can hit. For records made in a sibling, also say why $"nf"(n alpha)$ is defined: it is callee safety through the induction hypothesis, not "because $Omega_s alpha$ is defined".

### 11. MINOR: [Clone] in the appendix breaks the well-formedness that `exec_wf` is cited for

*Location.* Appendix [Clone] (`appendix.typ` line 158) and the note under it (line 161); the proof's table row `exec_wf` (unique borrows).

The appendix rule returns $v^circle$ for whatever `p` holds. For a borrow that gives a second $"borrow"_ell$, against well-formedness condition 1. For ⊥ it gives ⊥.

`RULES.md` §3 [Read] (line 57) takes the other reading. A borrow is moved even inside an erased term: "content a borrow → move" comes before the erased-term clause, and reading ⊥ is an error. `clone(p)` is "a read of `p` inside an erased term", so it follows the same clauses. The checker follows `RULES.md`: it moves a cloned borrow (`CloneB2`: after `clone(x)`, `x` is ⊥) and rejects a clone of ⊥ (`CloneBot`). So the appendix alone is wrong, and it also contradicts its own [Move].

F does not exclude `clone`. Give [Clone] the premises of [Copy], [Move] and [Read-err] (a borrow is moved; ⊥ or undefined content is an error), or restrict it to data.

### 12. MINOR: Corollary 2 (adequacy) is about copying runs

`Id`'s observations run with copying reads, so adequacy says that the erased runs of `t` and `u` agree, not the runtime runs. `IdCopies` (`Id Nat (let z = a; a) a`, by `refl`) is accepted, while `let z = a; a` as code fails ([Read] of a moved `Nat`) (probe `R9Copy`). As stated, "the same result and the same final contents" is true of observations. Say "observations (runs in which reads copy)", so that no reader takes it to be about the moving program.

### 13. MINOR: Corollary 3 is mostly vacuous, and is not a corollary of Theorem 10

At a ground valuation nothing closes off, nothing is stuck and no arm is checked, so items (2)–(4) hold trivially. Item (6) is Lemma 7, which rests on the assumption. The refinements that matter for [Split] are the non-ground ones, such as $sigma := ty("S") sigma'$, and line 240 says they are not proved. Calling the rest "the part of stability that soundness uses" (line 20) overstates it. Soundness uses Theorem 10, not stability. Present these as remarks.

### 14. MINOR: smaller slips in the lemmas and the claim

- *Lemma 8, `Eq` case.* "$T_s alpha = "eq"(D, a_g, b_g) = T_g$" is not a literal equality. The symbolic `eq`/`and` may already have dropped a `True` conjunct, or kept an `And` that valuation does not rebuild. What holds is equal truth, which is all that is needed.
- *(I) and field places.* (I) is about "proof bindings". Inside `match h { Intro(l, k) => … }`, `l` is the field place `h.l`, not a binding, and its type comes from `h`'s type. The claim's "a proof variable has its stored type, true by (I)" needs the one-line extension to field places. So does [Tail-prop] when its scrutinee is a field place.
- *The claim's `let` case vs F6.* F6's grammar of proof terms has no `let` or sequence, but the claim has a case for them (line 202). Either add "a `let` or sequence whose tail is a proof" to F6, or drop the case.
- *[Tail-match] and [Tail-split] skip the effect of [Access].* Access ends more borrows on the symbolic side, including every loan inside a neutral head. Keeping (A2) needs "(A2) survives [End]" on the symbolic side, which needs (N4) together with `endAll_endSeq`. Keeping (A3) and (A4) needs a check. I did it: ending a borrow moves the loans inside it to the position of its own loan, so owner sets do not change. Say so.
- *Unstated restrictions.* No definitions without bodies: an opaque lemma is an axiom, and F2's syntax implies bodies but does not say so. F2 is also used in Lemma 5 (no function values, so conversion on data is syntactic). F3 with F4 is also used in Lemma 6, since records come only from [Tail-gen]. Neither use is in "Where F's restrictions are used".
- *Naming.* "F5" names both the restriction and `lean-meta.md`'s counterexample (line 58, "the form the F5 counterexample of the mechanisation forced"). Rename one.
- *FootprintProbe.* Its verdicts accept or reject whole definitions. They show neither that (a) is strict nor that the extra conjunct becomes ⊤; only its comments say so. `R9Foot` turns the second into a verdict. In arm `Z` a hypothesis formed at an abstract `n` has type `False ∧ ⊤`, and `FPZ` uses its second conjunct as `True`. `FPZshow`'s rejection prints arm `S`'s type as `⊤ ∧ False`. This supports Lemma 7 (b).

### 15. MINOR: where `RULES.md` and the paper differ

- *[Clone].* Finding 11 (the appendix disagrees with `RULES.md` and the checker, which agree with each other).
- *Match on a ghost.* No rule applies in the appendix. [Match] (`appendix.typ` line 248) needs a constructor, [Match-stuck] (line 249) a neutral or an inert loan, and [Match-err] (line 250) lists only "undefined or ⊥". `RULES.md` §3 [Match] (line 64) does not mention ghosts either. Add a ghost to [Match-err]. The checker rejects it: `GhostMatch`, "[Match] on n, which was moved out".
- *Stuck-block captures.* The appendix copies a capture that is only read (mode `cp`) and moves only whole variables. `RULES.md` §3 reads such a capture in place without consuming it, moves parts at sub-place granularity, passes proof places by value, and makes closures formed inside a block capture through its `&` parameters (fuzz-port R2). Not in F, but the two definitions disagree.
- *[Seal]'s final read.* `RULES.md` says the final read `K` of a sealed program copies (it is an observation). The appendix's [Seal] runs `t` with runtime semantics and makes no exception.
- *Stale text in `RULES.md`.*
  - The title says "rule set v2.0", but the body is v2.1.
  - §0 P2 says D59 "will make" the `Unit` rows convertible; D59 is already in.
  - §7's `AddSub` still reads `let old = *x`, which moves `*x` under D53, so the later `&*x` fails. The paper has `clone(*x)`.

## Addendum: D65, `[Drop]` ends the borrows of a dying place (DECISIONS, 37500b5b)

The lead asked whether D65 can be broken. It can, through stuck blocks. I also tested a variant that closes the hole.

### 16. GAP (a soundness witness against D65 as written; outside F): an arm of a stuck block can return an ended borrow, and closing the block off revives it

*Location.* D65's argument ("a later use of an ended borrow errs on the symbolic path whenever it errs on the ground, since the symbolic path ends at least as much"), and its note that returning a borrow of a local is caught by "[Def]'s result check".

*The witness* (probe block `R9D65`; see below for how it was run):

```
def Blk (n : Nat) (b : Nat) : Unit := (
  let r : &Nat = match n { Z => (let q = 0; &q), S _ => &b };
  *r := 5 )
```

- *Under D65, arm `Z` is ⊥.* Arm `Z` returns a borrow of its own local `q`. Before D65, dropping `q` was an error, so `Blk` was rejected. Under D65 the drop ends the borrow, so arm `Z` evaluates to ⊥ at type `&Nat`.
- *[Split] passes it.* [Split] checks the arms and then discards their values; only their types (`&Nat`) have to agree.
- *[Close] revives it.* The match is then closed off as a block. [Close]'s `&T` row gives the block's result a fresh live `borrow_k`, whose hole sits in the fill of `b` (the only place the block borrows).
- *So the symbolic path accepts it.* On the symbolic path `*r := 5` writes through a live borrow, and `Blk` is accepted.
- *And the ground run goes wrong.* At `n = 0` the ground run takes arm `Z` directly, `r` is ⊥, and `*r := 5` fails: "no such place *r: its path does not exist in ⊥".

This is the one direction D65's argument rules out: the ground has ended a borrow that the symbolic path holds live. It happens because [Close]'s `&T` row assumes that the summarised code returns a live borrow into a borrowed argument. For functions, D44 and [Def]'s result check make that true. For a stuck block's arms, nothing checks it once a drop can produce ⊥.

- `G(n, b : &Nat) : &Nat` returns such a block's result. Its generic result is the block's live borrow, so a [Def] check that the result is not ⊥ passes. Yet `G(0, &c)` returns an ended borrow.
- `UseG(n, c) := let r = G(n, &c); *r := 7` is accepted at its generic call, because there `G` closes off to a live borrow. `UseG(0, 1)` then reads an ended borrow.

The fuzzer finds the same shape on its own. On `--drop 100`, seed 1, 20,000 cases, pure D65 has 5 findings of a new kind, `renorm` ("no such place *r: its path does not exist in ⊥"). Case 220 is typical: its statement contains `let a0 = match n0 { Z => …; &n0, S p1 => let a2 = p1; &a2 }`. There, too, one arm returns a borrow of an arm-local. The symbolic statement holds a sealed program that errors when `n0` is refined, while the direct path runs.

*Two smaller points.*

- *The result check is not in the rules yet.* The appendix's [Def] requires only "pop succeeds and $A equiv G'$". Nothing in it rejects a ⊥ result, so D65 must add that premise, and the suite does not test it. The suite's dangling-return tests (`DanglingLocal`, `DanglingReborrow`, `DanglingTail`) have no borrow parameter, so D44 rejects them first. Under scratch D65 without the check, `RetLocal(x : &Nat) : &Nat := let a = 0; &a` is accepted, and no verdict in the suite changes. With D44 switched off, the three dangling returns flip to accepted: the `borrowParam` ledger row gains them.
- *Theorem 10 (i) needs strengthening under D65.* Before D65, "the pop of its frame succeeds" excluded a dangling result. Under D65 the pop never errs, so for borrow-returning data functions (i) must also say that the result is live. Revision 2.1 of the proof (d2bfc99f), which assumes D65 and drops F5, should check this. `Blk` itself is outside F (F4 excludes stuck blocks).

*A fix, tested.* D65 should end the dying place's borrowers only when they are held in bindings: a variable that is not used again, which is the reading of Rust's non-lexical lifetimes. When the borrower is a temporary, the drop should stay an error. A temporary is a value in flight: a let-block's or an arm's result, or a call's result while its frame pops, and it is always used next. With this variant:

- `Blk`, `G`, `UseG` and `RetLocal` are rejected, with no separate result check in [Def] or [Split];
- `Bad2`, `Bad4` and every `DropVariants` run are accepted and run without error, as D65 intends.

Soundness in outline: for a borrower held in a temporary, (A4) puts the dying place among its symbolic owners whenever it is among its ground owners, so if the ground drop errs, the symbolic drop errs too.

*How it was run.* The checker does not implement D65, so the verdicts in `R9D65` are today's (all four rejected by [Drop]). I ran three reflinked copies of the checker at 37a74e89 in a scratch directory; the shared checkout was not modified.

- *Scratch D65.* In `dropTopBind` and `dropValue`, where [Drop] used to err, end the borrower of each live loan in the dying value, repeating until none is left, as [Access] does.
- *The variant.* The same, but if that borrower's position is a temporary, err: `[Drop] q dies while a value in flight borrows it`.
- *The baseline.* The same copy with the change reverted.

| | today's checker | scratch D65 | variant |
|---|---|---|---|
| example and case-study verdicts that change | – | none | none |
| ledger rows that change | – | `accessInside` gains `Naturality.PickEarly`; `borrowParam` gains the three dangling returns | `accessInside` gains `Naturality.PickEarly` |
| `--drop 100`, seed 1, 20,000 cases: `exec` [Drop] findings | 7,228 | 0 | 0 |
| same run: `renorm` findings | 0 | 5 | 0 |
| same run: checked / rejected / invalid | 18,739 / 959 / 302 | 18,744 / 955 / 301 | 18,739 / 959 / 302 |

All three runs also have 551 `adequacy: vacuous` findings, so those are not caused by D65.

## What holds up

- The structure is right. The walk along the case tree with a valuation extended at each split, truth as an invariant, ex falso as unreachability, and [Call-type] handled by the frame property plus injectivity all look correct.
- F6 is the right restriction to decouple (i) from the hypotheses.
- Lemma 9 is right for F. In F, two borrow arguments never share an owner, and at a ground state a loan occurs once, so the context is injective. `ctx_inj` is the right syntactic fact.
- (N4) I could not break. For `Pick`'s fills, valuing first (the hole inert) and ending first give the same state. A fill's run writes its hole and reads $c_i$, but never inspects the hole, and that is the "hole parametricity" lemma the proof should state for the (N4) risk.
- F5 appears to suffice for (N1) and (N3) inside F (finding 8), but see finding 7 for the planned fix.

## The one thing to fix before this goes in the paper

Fix the simulation relation, and restate Assumption 4 against the fixed version. The relation needs three things:

- it must be defined at every state the walk visits, so resolution must see through ghosts (finding 2);
- it must fix what each live borrow holds and where it points, under α, and not only what the states resolve to (finding 1);
- Assumption 4 must hypothesise callee safety per call, at the arguments the ground run actually passes, and must cover copying runs, call points and pushed frames (finding 3).

Then redo the [Rec] measure and the termination step on top of the new relation, without `exec_total`'s "every argument" premise (finding 4). Until then the recursive half of the induction, which is where the paper's earlier false proofs lived, is unargued.

## Re-check of revision 2 (1e9f793b), 2.1 (d2bfc99f) and 2.2 (48f6b5a1)

meta-order asked for a re-check of revision 2.1. Revision 2.2 landed while I was doing it, so this section re-checks 2.2, the current version. Where 2.1 and 2.2 differ, it says so.

*Numbering.* The revision's "Changes from revision 1" list uses this review's first numbering. Here, its (1)–(6) are findings 1–6; its (7)–(14) are findings 8–15; and its (16) is finding 16. Finding 7 (the ghost-borrow plan misses `Bad4`) was inserted later.

*Score for revision 2.2: weak accept, as a conditional reduction.*

- The theorem is now honestly titled as conditional.
- The relation carries what the walk and the measure need.
- Resolution is defined wherever the proof looks.
- Termination is argued call by call.
- The two assumptions are separated and named.

What remains is small and listed at the end. The assumptions still hold almost all of the operational content, and the paper should say so where it cites the theorem. The rule readings also assume two changes that the appendix does not have yet: amended D65, and records that belong to their arm. The paper's appendix and `RULES.md` must be updated to match before the section goes in.

### Verdicts, finding by finding

| # | finding | verdict | where it is answered, and what is left |
|---|---|---|---|
| 1 | agreement fixes only resolutions | closed | (A5) resolves the contents of live borrows. The paragraph after the definition derives "same head constructor after [Access]" and "the ground argument is the symbolic one under α". Both are right: an owned position by (A2), a place through a borrow by (A5). The pair of states I gave in finding 1 violates (A5), as it should. Preserving (A5) is correctly listed as a risk of the assumption. |
| 2 | agreement undefined mid-move | closed | F7 (no runtime read under `*`) and the resolution lemma. I checked every route by which a ghost could reach a borrow's content in F, and found none (below). Replace, G and GR are now outside F. One claim in the lemma is too broad (minor finding R3 below). |
| 3 | interface of Assumption 4 | closed | Per-step (N1)–(N4), the "runs agree" lemma, and the "modes" lemma. meta-order's two doubts are answered below. One use of (T2) is unlisted (minor finding R2 below). |
| 4 | termination | closed | "Runs agree" gives the trace-indexed argument: one pass over the syntax, [End]s bounded by `endBorrow_nb_lt` (which exists in `meta-lean`), and calls justified one by one. `exec_total` is no longer cited. |
| 5 | transfer from 1.3 | closed | (T1)/(T2) are a separate assumption. The table now gives the `close_*` hypotheses. See minor finding R3 for the scope of the order-independence transfer. |
| 6 | the assumption is the hard half | closed | Retitled as conditional, with a paragraph on what is proved and what is assumed. |
| 7 | the ghost-borrow plan misses `Bad4` | closed | The plan was dropped for D65. |
| 8 | the F5 argument | closed, and superseded | F5 is removed. Its job is now done by amended D65 (below). |
| 9 | Lemma 7 (a) | closed | (a) and (b) are symmetric. I checked the new (a) and (b) without F5: a ground-only footprint position is owned only through borrow variables that are ⊥ symbolically. A statement can only assign those as whole variables, and on the ground that assignment ends the old borrow, which changes no resolved content. Any other write to such a position would have to go through a borrow that is live on both paths, and (A4) would then put the position in the symbolic footprint. `AssignBot` and `CloneBot` are cited correctly. |
| 10 | Lemma 6 (c) | closed | Records now belong to their arm (checker 969e3254, stated as a rule reading). In F they come only from [Tail-gen] on the current path, and (A1) at the node that made a record makes it defined. Records from earlier definitions are handled by fresh names. |
| 11 | [Clone] | closed | F8, with the `RULES.md` reading. |
| 12 | adequacy | closed | Stated for observations. The note on `IdCopies` and the "modes" lemma is right. |
| 13 | stability | closed | Given as remarks, not a corollary. |
| 14 | smaller slips | closed | Each sub-point is addressed. |
| 15 | RULES vs paper | closed for F | The readings F depends on are stated. The paper corrections went to rule-audit. |
| 16 | D65 | closed in 2.2; open in 2.1 | See the next paragraph. |

*Finding 16 was also a hole inside F in revision 2.1.* Once F5 is removed, the following function is in F: `FR(n, x : &Nat) : &Nat := match n { Z => (let a = 0; &a), S _ => x }`. Under 2.1's reading of D65 ("never fails"), with no result check in [Def], `FR` is accepted. So is `UseFR(n, c) := let r = FR(n, &c); *r := 1`, because `FR`'s call closes off to a live borrow. `UseFR(0, 1)` then writes through an ended borrow. I confirmed this in the scratch D65 checker. Revision 2.1 appealed to "[Def]'s result check", but that check was in neither its rule readings nor the appendix, so (N2) was false in F. Revision 2.2 adopts the amended D65 (probe block `R9D65`, `FR`). Under it, `FR` is rejected because its result is in flight when `a` dies, so the hole is closed with no separate check. Theorem 10 (i) now states that a borrow result is live, and the new "the result is live" step is right: in F no term of borrow type evaluates to ⊥ on the symbolic path, the pop cannot end the result, and (A3) carries it to the ground.

### meta-order's questions

- *F7 and "modes", and ghosts.* Both are right as far as I can find.
  - *No ghost inside a borrow.* I tried each route by which a ghost could end up inside a borrow's content:
    - pattern variables resolve to places under `*`, so F7 covers them;
    - [Borrow] refuses a place that is not whole;
    - assignments and call arguments carry whole values;
    - a fill's run reads only its own owned cells, and [Seal]'s final read copies (stated as a rule reading);
    - reading a borrow variable moves the whole borrow and leaves ⊥, not a ghost.
  - *"Modes".* In F, the modes differ only at a read of owned non-copy data. Annotations are not run, proofs are skipped, and there are no closures. An erased read of a place whose value holds a ghost sees through it, so the erased run is at least as permissive, and it produces the same values.
- *Erased-mode confinement, which revision 2 leaves to (N3).* (N3) can be proved in F instead of assumed.
  - Type terms in F are match-free (F3), so an erased run of a type former takes the same syntactic steps on both paths, except inside calls.
  - Confinement judges a step by the root of the place it assigns, borrows or moves. The steps inside a call (run on the ground, closed off on the symbolic path) are rooted in the callee's frame and never count.
  - A call's argument steps have the same syntax on both paths.
  - So confinement is decided by the syntax of the type term. Keeping (N3) as an assumption is harmless.
- *Per-step (N2) for calls whose symbolic run completes.* (N2) is enough as an interface, and more than needed.
  - When the symbolic call completes by [App], the callee's body never inspected an abstract value; otherwise it would have been stuck and closed off.
  - Its steps are therefore machine steps between agreeing states: push the frame, run the body, pop the frame, and any inner call is again (N2).
  - So (N2)'s [App] case follows from (N1) by induction on the depth of the ground run's calls, and only the [Close] case needs assuming.
  - Worth saying: it shrinks the assumption to where the risks listed actually are (`close_cur`, `close_back`, hole parametricity).
- *Did anything else use F5?* No. The only remaining use was Lemma 7 (a), and the symmetric (a)/(b) covers it. D65 did remove one implicit protection: the old pop error guaranteed a borrow result was live. Revision 2.2 restores that explicitly, as above.
- *Are "early ends" deep in F?* Yes, but the sentence needs restating.
  - The text says [Access] and [Drop] "keep ending loans until none remains in that place". That holds for [Access] of a read, borrow or write, and for [Drop].
  - It does not hold for the [Access] before a match, which ends only loans on the path and loans inside a neutral at the head.
  - The argument still goes through, because in F an early end comes only from a hole inside a fill, which is a neutral. The ended borrow's content is substituted into that same fill. The fill stays stuck, because its head call never reads the hole (hole parametricity), so the reborrows' loans are again inside the head neutral and the same [Access] ends them.
  - A record cannot swallow those loans: records are made after [Access] has ended every loan in the neutral, and the reborrows' loans are fresh.
  - Say it this way in the text.

### Remaining minor findings on revision 2.2

- *R1. A false sentence in the amended [Drop] argument (harmless).* It says "A new value ended by its own assignment's [Access] is ended on both paths alike, since its loan sits in the assigned place's content on both."
  - In `x := Pick(n, &*x, &b)`, `Pick`'s hole sits in `x`'s content (through the reborrow) and in `b`'s. So the [Access] on `x` ends the new borrow symbolically, while at `n = 1` the ground borrow points into `b` and survives.
  - Probe block `R9AS`: `AS2`, which writes through `x` afterwards, is rejected; `AS2g1`, the same at `n = 1`, runs.
  - The conclusion survives, since the symbolic path ends more and after the assignment the value is a binding. Replace the sentence with that.
- *R2. (T2) is used, unlisted, to turn (i) into the hypothesis of "runs agree".* (i) is about a run from the ground instance $Gamma beta";" phi beta$. "Runs agree" needs the call from the caller's state to complete. Going from one to the other is the frame property. Cite (T2) in "Which calls the walk needs".
- *R3. The resolution lemma claims order-independence at every state of F, symbolic ones included.* The ghost-as-atom argument covers ghosts. It does not cover [End]'s eager re-normalisation of sealed programs on symbolic states, where 1.3's machine is lazy. The proof needs order-independence only at ground states, where [End] is plain substitution (for (A2)), and inside (N4). Restrict the lemma to ground states, or move the symbolic case into (N4).
- *R4.* The resolution discussion cites `Sched.lean` on an unmerged branch (`ochr-core-meta-t1b`). Either merge it or cite it as unmerged in the paper.
