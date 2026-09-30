# Reviewer 9: cold review of `notes/typed-fragment-proof.typ`

Reviewer 9, 2026-09-30. Read: the whole paper (`paper/main.typ` and every section, the appendix included), `RULES.md`, the proof, the plan it carries out (`notes/typed-fragment-plan.md`), the cited `meta-lean` lemmas, and the two cited probes. Probes of my own: `lean/Scratch/Reviewer9Probe.lean` (25 verdicts in five blocks, each asserted with `#guard`; run with `lake env lean Scratch/Reviewer9Probe.lean` from `ochr/core/lean`).

## Score: weak reject

(As an appendix proof in a POPL/ICFP submission.)

The proof is organised well. It walks the definition's case tree along one ground instance. It keeps truth of hypotheses as an invariant. It transfers call-site types to the callee's instance through the frame property and injectivity of contexts. And F6 stops a data function's run from depending on its hypotheses. I found no program in F that breaks the theorem, and I think the theorem is probably true of F if naturality holds. But the proof does not yet establish even the conditional statement. Four problems are in the part the proof says is proved, not in the assumption:

- the agreement relation cannot support the steps that read through a borrow, the [Rec] measure among them;
- agreement is undefined at states that accepted F programs reach;
- the assumption's interface does not match how the proof uses it;
- termination does not follow from the lemmas cited for it.

On top of that, Assumption 4 holds almost all of the operational content, and it is known to be false for the full rules. A reader should be told plainly that this is a reduction of soundness for F to a simulation lemma, not a proof of soundness.

No finding is FATAL. I found no counterexample to Theorem 10 or to its corollaries as stated.

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

### 7. MINOR: author's attack point 1 (F5): no counterexample in F, but the written argument has a false step

I looked for a program in F that ends a borrow earlier on the symbolic path and then fails at a ground [Drop] or pop. The symbolic path ends a borrow early in two ways. One is a hole in several fills (probe `E2`: reading the other owner of `Pick`'s hole). The other is a match on a fill, which ends every loan inside the fill even when it has one owner (`E3`). I also tried returning a parameter after an early end (`E4`) and a borrow in flight that outlives a block-local (`E1`). Every candidate either runs at its ground instances or is rejected on the symbolic path too (probe `R9Early`, 9 verdicts).

The argument at lines 32 and 255 says that "a borrower is always declared after every place it borrows". That is false for borrows in flight: a let-block's result, or a call argument, outlives the block's locals (`E1`). The conclusion survives, but by a different route. On the ground, a place can die with a live borrow into it in only two ways:

- If the symbolic counterpart of that borrow is live, (A4) puts the place among its symbolic owners. The symbolic drop then fails too, so this case needs no F5.
- If the symbolic counterpart is ⊥, it cannot be a temporary. A call argument that is ended while in flight is a [Call-err] on the symbolic path. A let-block's result is followed only by drops, and a drop ends only the borrow being dropped, never another one. So it is a binding, and F5's scoping puts it after its target.

Write it that way. It also shows that N3 depends on (A4), which the proof lists only as a risk.

### 8. MINOR: author's attack point 2 (Lemma 7 (a)): true in F, but the case list is wrong and it uses F5

*Location.* Lemma 7 (a), line 130: "An occurrence rooted at a variable holding ⊥ is an error ([Read-err], [Borrow-err], [Assign], [Match-err])."

- *[Assign].* Assigning a whole variable that holds ⊥ is not an error: [Assign] drops the old content, and ⊥ is loan-free. Outside F, `AssignBot` is accepted (probe `R9Clone`). It ends `x` symbolically, then types `Id Unit (x := &c; *x := 5) …`. So the symbolic statement mentions a ⊥ borrow variable, and the ground footprint contains `x`'s ground owner, which the symbolic one lacks. In F this is excluded only because assigning to a borrow variable would assign a borrow, which F5 forbids. Add F5 to Lemma 7 (a) in "Where F's restrictions are used".
- *[Clone].* The appendix's [Clone] has no premise excluding ⊥ (finding 10). By the appendix, `clone(x)` of an ended borrow variable succeeds. The checker rejects it (`CloneBot`). Cite the corrected rule.

### 9. MINOR: author's attack point 3 (Lemma 6 (c)): true in F, and the private-copy half is vacuous; one definitional gap

In F, F3 (no match in a type) and F4 (no non-tail data match) mean that [Split-gen] never runs. [T-Split-goal] is excluded, and the machine closes calls off and never generalises. So the only records are made by [Tail-gen], on the main path of some arm, and the "private copies" clause of (c) never arises. Say so; it is a simpler argument than the one given.

For sibling arms, the argument is right. A text made in one arm can be derived again in another only if the arm-local abstract values it mentions are shared, and they are not. Values common to both arms appear unrefined in the text, and α gives them the same value on both.

The gap is that "extend α … for each record, in the order the records were made" (line 105) includes records whose text mentions abstract values that exist only on another path, or only in an earlier definition's check (Δ and records are global). α does not cover those values, so $"nf"(n alpha)$ is not ground and (a) fails for them. Restrict the extension to records whose text mentions only values that α covers, and show those are the only records the current path can hit. For records made in a sibling, also say why $"nf"(n alpha)$ is defined: it is callee safety through the induction hypothesis, not "because $Omega_s alpha$ is defined".

### 10. MINOR: [Clone] in the appendix breaks the well-formedness that `exec_wf` is cited for

*Location.* Appendix [Clone]; the proof's table row `exec_wf` (unique borrows).

The appendix rule returns $v^circle$ for whatever `p` holds. For a borrow that gives a second $"borrow"_ell$ (against well-formedness condition 1), and for ⊥ it gives ⊥. `RULES.md` §3 [Read] says `clone(p)` is "a read of `p` inside an erased term", which is [Copy] and excludes both. The checker does a third thing: it moves a cloned borrow (`CloneB2`: after `clone(x)`, `x` is ⊥) and rejects a clone of ⊥ (`CloneBot`). F does not exclude `clone`. Either restrict [Clone] to data (not a borrow, not ⊥) in the appendix, or exclude cloning borrow-typed places from F.

### 11. MINOR: Corollary 2 (adequacy) is about copying runs

`Id`'s observations run with copying reads, so adequacy says that the erased runs of `t` and `u` agree, not the runtime runs. `IdCopies` (`Id Nat (let z = a; a) a`, by `refl`) is accepted, while `let z = a; a` as code fails ([Read] of a moved `Nat`) (probe `R9Copy`). As stated, "the same result and the same final contents" is true of observations. Say "observations (runs in which reads copy)", so that no reader takes it to be about the moving program.

### 12. MINOR: Corollary 3 is mostly vacuous, and is not a corollary of Theorem 10

At a ground valuation nothing closes off, nothing is stuck and no arm is checked, so items (2)–(4) hold trivially. Item (6) is Lemma 7, which rests on the assumption. The refinements that matter for [Split] are the non-ground ones, such as $sigma := ty("S") sigma'$, and line 240 says they are not proved. Calling the rest "the part of stability that soundness uses" (line 20) overstates it. Soundness uses Theorem 10, not stability. Present these as remarks.

### 13. MINOR: smaller slips in the lemmas and the claim

- *Lemma 8, `Eq` case.* "$T_s alpha = "eq"(D, a_g, b_g) = T_g$" is not a literal equality. The symbolic `eq`/`and` may already have dropped a `True` conjunct, or kept an `And` that valuation does not rebuild. What holds is equal truth, which is all that is needed.
- *(I) and field places.* (I) is about "proof bindings". Inside `match h { Intro(l, k) => … }`, `l` is the field place `h.l`, not a binding, and its type comes from `h`'s type. The claim's "a proof variable has its stored type, true by (I)" needs the one-line extension to field places. So does [Tail-prop] when its scrutinee is a field place.
- *The claim's `let` case vs F6.* F6's grammar of proof terms has no `let` or sequence, but the claim has a case for them (line 202). Either add "a `let` or sequence whose tail is a proof" to F6, or drop the case.
- *[Tail-match] and [Tail-split] skip the effect of [Access].* Access ends more borrows on the symbolic side, including every loan inside a neutral head. Keeping (A2) needs "(A2) survives [End]" on the symbolic side, which needs (N4) together with `endAll_endSeq`. Keeping (A3) and (A4) needs a check. I did it: ending a borrow moves the loans inside it to the position of its own loan, so owner sets do not change. Say so.
- *Unstated restrictions.* No definitions without bodies: an opaque lemma is an axiom, and F2's syntax implies bodies but does not say so. F2 is also used in Lemma 5 (no function values, so conversion on data is syntactic). F3 with F4 is also used in Lemma 6, since records come only from [Tail-gen]. Neither use is in "Where F's restrictions are used".
- *Naming.* "F5" names both the restriction and `lean-meta.md`'s counterexample (line 58, "the form the F5 counterexample of the mechanisation forced"). Rename one.
- *FootprintProbe.* Its verdicts accept or reject whole definitions. They show neither that (a) is strict nor that the extra conjunct becomes ⊤; only its comments say so. `R9Foot` turns the second into a verdict. In arm `Z` a hypothesis formed at an abstract `n` has type `False ∧ ⊤`, and `FPZ` uses its second conjunct as `True`. `FPZshow`'s rejection prints arm `S`'s type as `⊤ ∧ False`. This supports Lemma 7 (b).

### 14. MINOR: where `RULES.md` and the paper differ

- *[Clone].* Finding 10.
- *Match on a ghost.* No rule applies in the appendix. [Match] needs a constructor, [Match-stuck] a neutral, and [Match-err] lists only "undefined or ⊥". Add a ghost to [Match-err]. The checker rejects it: `GhostMatch`, "[Match] on n, which was moved out".
- *Stuck-block captures.* The appendix copies a capture that is only read (mode `cp`) and moves only whole variables. `RULES.md` §3 reads such a capture in place without consuming it, moves parts at sub-place granularity, passes proof places by value, and makes closures formed inside a block capture through its `&` parameters (fuzz-port R2). Not in F, but the two definitions disagree.
- *[Seal]'s final read.* `RULES.md` says the final read `K` of a sealed program copies (it is an observation). The appendix's [Seal] runs `t` with runtime semantics and makes no exception.
- *Stale text in `RULES.md`.*
  - The title says "rule set v2.0", but the body is v2.1.
  - §0 P2 says D59 "will make" the `Unit` rows convertible; D59 is already in.
  - §7's `AddSub` still reads `let old = *x`, which moves `*x` under D53, so the later `&*x` fails. The paper has `clone(*x)`.

## What holds up

- The structure is right. The walk along the case tree with a valuation extended at each split, truth as an invariant, ex falso as unreachability, and [Call-type] handled by the frame property plus injectivity all look correct.
- F6 is the right restriction to decouple (i) from the hypotheses.
- Lemma 9 is right for F. In F, two borrow arguments never share an owner, and at a ground state a loan occurs once, so the context is injective. `ctx_inj` is the right syntactic fact.
- (N4) I could not break. For `Pick`'s fills, valuing first (the hole inert) and ending first give the same state. A fill's run writes its hole and reads $c_i$, but never inspects the hole, and that is the "hole parametricity" lemma the proof should state for the (N4) risk.
- F5 appears to suffice for (N1) and (N3) (finding 7).

## The one thing to fix before this goes in the paper

Fix the simulation relation, and restate Assumption 4 against the fixed version. The relation needs three things:

- it must be defined at every state the walk visits, so resolution must see through ghosts (finding 2);
- it must fix what each live borrow holds and where it points, under α, and not only what the states resolve to (finding 1);
- Assumption 4 must hypothesise callee safety per call, at the arguments the ground run actually passes, and must cover copying runs, call points and pushed frames (finding 3).

Then redo the [Rec] measure and the termination step on top of the new relation, without `exec_total`'s "every argument" premise (finding 4). Until then the recursive half of the induction, which is where the paper's earlier false proofs lived, is unargued.
