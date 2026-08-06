#import "../style.typ": *
#import "@preview/curryst:0.5.0": prooftree, rule
== F2: Reorganization (⟿) <fig-reorg>

// Judgment helpers dropj/surrj/ownfree/groupb are pinned in style.typ.
//
// RE-EXTRACTED AT `dc90adce` (this figure's own pin; main.typ's pin declaration
// is a later pass's). Source: Dllbc/Machine.lean — endMut/endLoan/killBorrowInΩ/
// sendPayloadToLoan, drop/firstOwnNode, endIssued/endGroup/releaseCaptured, and
// the Group record. G-EndGroupBack DELETED: `Group.backSpec`, `Decl.back` and
// `resolveTree` no longer exist (M27), so every group end is now the single arm
// below. The `constrained` test-only wire was deleted with its rule-gap in M28.
// `groupb` (the back-carrying group node) survives in style.typ unused; its
// removal belongs to the pass that owns that file.

Reorganization is the judgment that rewrites the borrow bookkeeping: ending loans, vacating displaced values, collapsing the loan groups calls leave behind. No surface syntax elaborates to it — its rules fire _between_ evaluation steps, and they are presented here *nondeterministically*: a rule may fire at any point where its premises hold, and #reorgs($Omega$, $Omega'$) is the reflexive–transitive closure of single steps. The implementation is lazy — it fires a reorganization only when a ⇒/⇐ premise demands one — and carries a fuel bound; both are scheduling, not semantics (the fuel is a totality device for the mechanization, and the demand sites are catalogued before the correspondence table below).

The judgment has two levels. End-Mut and drop touch only the environment and are stated as #reorg($Omega$, $Omega'$) — such a step lifts to the checker state #St($Omega$, $Gamma_sigma$, $O$, $G$, $R$) with the other components fixed. Group ends delete their group node and mint existentials into $Gamma_sigma$, so they are stated over the full state, #reorg($S$, $S'$). Two auxiliary judgments — dropping, #dropj($Omega$, $v$, $Omega'$), and the issued-borrow surrender, #surrj($Omega$, $ell$, $tau$, $v$, $Omega'$) — are not ⟿ steps of their own: they occur only as premises (of ⇐'s overwrite rule in @fig-runtime, and of the group ends here).

*Positions.* $hat(Omega)[dot]$ (and the two-hole $hat(Omega)[dot, dot]$, and its $m$-hole extension) ranges over environment contexts: a marked position is a whole entry of $Omega$ or a position inside an entry's value tree, and $hat(Omega)[v]$ is the environment with $v$ at that position. $hat(v)[dot]$ is the same over a single value. A loan id occurs at most once in each role across the state, so these decompositions are unique. #ownfree($v$) says $v$ contains no #loanm($$) or #borrowm($$, $$) node at any depth.

=== Ending a loan

#v(0.5em)
#align(center, irule("G-EndMut",
  reorg($Omega$, $hat(Omega)[v, vbot]$),
  $Omega = hat(Omega)[loanm(ell), thin borrowm(ell, v)]$,
  $ell in.not "captured"(G)$))
#v(0.5em)

The borrow's current payload is plugged back where the marker sits and the borrow node is killed to $vbot$ — a ⇐-fill aimed at $Omega$'s own bookkeeping, followed by the kill (doc §2.2). Either half may sit at a whole slot or buried inside a value tree: a marker buried in a constructor field (the field loans a borrow-mode match parks, doc §3.3) and a marker directly under a borrow's payload (a suspended reborrow) end by this same rule. The payload $v$ travels as-is — if it is itself suspended, its markers relocate with it, and the chain collapses by further G-EndMut steps; if it is a hole, the plug-back merely leaves the owner's position vacant and fillable, not corrupt (doc §2.4). The side condition routes captured loans to the group rules: ending a loan a call captured is the group's business. (In reachable states the premise is anyway unsatisfiable for a captured $ell$ — its borrow half was consumed into the call and is no longer an $Omega$ position — but the guard is what the implementation checks first, and the rule states it.)

Doc §2.2's "generalized owned-position rule" is a fact about @fig-runtime, not a separate reorganization: a ⇒-move demands that the value it is about to move carry no marker in _owned position_ — on the constructor spine, not under a #borrowm($$, $$) payload, since a carried borrow relocates with its suspensions intact — and G-EndMut, at whatever depth the marker sits, is the reorganization that clears one. Restricting the rule itself to owned position would be wrong: the demand that arrives _through_ a borrow (matching or moving a suspended payload) ends a marker that is not in owned position, by this same rule.

=== Drop

Fill demands a vacant target; when a ⇐ aims at a live value, the value is displaced and must be dropped (doc §2.3). The judgment #dropj($Omega$, $v$, $Omega'$) reads: the displaced value $v$ may be discarded, reorganizing $Omega$ to $Omega'$. Note the form: $v$ is an operand of the judgment, not an entry of $Omega$ — the implementation vacates the slot _before_ dropping, so no stale copy of $v$ is ever visible to the ends' $Omega$-searches.

#v(0.5em)
#align(center, irule("G-DropFree",
  dropj($Omega$, $v$, $Omega$),
  ownfree($v$)))
#v(0.9em)
#align(center, irule("G-DropLoan",
  dropj($Omega$, $v$, $Omega'$),
  $v = hat(v)[loanm(ell)]$,
  $Omega = hat(Omega)[borrowm(ell, p)]$,
  dropj($hat(Omega)[vbot]$, $hat(v)[p]$, $Omega'$)))
#v(0.9em)
#align(center, irule("G-DropBorrow",
  dropj($Omega$, $v$, $Omega'$),
  $v = hat(v)[borrowm(ell, p)]$,
  ownfree($p$),
  $Omega = hat(Omega)[loanm(ell)]$,
  dropj($hat(Omega)[p]$, $hat(v)[vbot]$, $Omega'$)))
#v(0.5em)

Drop is a total procedure, not a choice: end every ownership node the displaced value carries, then discard the remainder. An ownership-free value discards immediately (G-DropFree), so ordinary code pays nothing. A marker in the value ends against its borrow in $Omega$ — the borrow is killed and the payload returns _into the value being dropped_, where the recursive premise continues on it (G-DropLoan: a chain-link value dies with nothing stranded). A borrow node in the value sends its payload home to its marker in $Omega$ and becomes a hole (G-DropBorrow). Doc §2.3's locatability condition is exactly the premises' shape: the half the rule matched is a position within the value being dropped, and the complementary half must be an $Omega$ position.

The #ownfree($p$) premise on G-DropBorrow is doc §2.3's "innermost first" made local, and it is load-bearing. Without it, G-DropBorrow could fire on #borrowm($ell$, $(loanm(ell'))$) by sending the still-suspended payload home — rewiring the owner's loan from $ell$ to $ell'$ and _accepting_ the self-reborrow with no ghost machinery, precisely the "twisted" program this calculus rejects (doc §2.5). With it, a borrow node ends only after its payload is clean, so the buried marker must end first — and if it cannot, no rule applies:

#block(stroke: 0.5pt, inset: 8pt, radius: 4pt, width: 100%)[
  *Non-derivation — the self-reborrow (doc §2.5).* After `let c = &mut *b`, the assignment `b := c` ⇒-consumes `c`, so $Omega = x |-> loanm(ell), thin b |-> borrowm(ell, (loanm(ell')))$ with #borrowm($ell'$, $3$) _in flight_, and the fill must first derive #dropj($Omega$, $borrowm(ell, (loanm(ell')))$, $Omega'$). G-DropLoan on $ell'$ needs #borrowm($ell'$, $p$) as an $Omega$ position — it is the in-flight value, not an entry; G-DropBorrow on $ell$ needs #ownfree($loanm(ell')$) — false; G-DropFree needs an ownership-free value — false. No rule applies; the program is rejected. The stuckness _is_ the rejection: no rule was added to say so.
]

// RULE-GAP: drop does not route through the group machinery. G-DropLoan requires
// the marker's borrow half as an Ω position; the marker of a group-captured loan
// has none (its borrow was consumed into the call), so OVERWRITING a captured
// owner (`a := 5` while a's loan is captured) is stuck/rejected — while a ⇒-READ
// of the same owner demand-ends the group (readR → endLoan → endGroup). The
// read/write asymmetry is the implementation's (drop calls killBorrowInΩ, not
// endLoan); reported to the coordinator, not resolved here.
// STILL OPEN AT `dc90adce`, and re-verified rather than carried over: `drop`
// (Machine.lean) reaches `killBorrowInΩ` on a loan marker, and `readR`'s .var
// case reaches `endLoan`. This is now the ONLY survivor of the three
// audit-strategy holes the paper's §4.5/§6.5 listed — the other two were holes
// in the declared-back machinery and closed when it was deleted.

=== Ending a group

A call mints a loan group #group($rho$, $macron(C)$, $macron(I)$) (@fig-boundaries): the node ties the loans it *captured* (the argument borrows' loans, each annotated with the owed type $S$ from the signature, instantiated at the call) to the borrows it *issued* (the loans of the borrows in its result, owed-typed from the return type). The group's whole content is its ending discipline — issued first, then captured, atomically.

An issued borrow surrenders by the auxiliary judgment: located anywhere in $Omega$, audited against its owed type, killed.

#v(0.5em)
#align(center, irule("G-EndIssued",
  surrj($Omega$, $ell$, $tau$, $p$, $hat(Omega)[vbot]$),
  $Omega = hat(Omega)[borrowm(ell, p)]$,
  $Gamma_sigma tack.r hasT(p, tau)$))
#v(0.5em)

A hole cannot surrender: $vbot$ inhabits no type, so the typing premise already excludes it (the implementation's distinct "nothing surrendered" error is diagnostic, not a separate condition). A payload suspended by a reborrow of the result likewise fails the typing premise; G-EndMut on the parked loan restores it first.

#v(0.5em)
#align(center, prooftree(rule(
  name: smallcaps("G-EndGroupOpaque"),
  reorg(St($Omega_0$, $Gamma_sigma$, $O$, $G$, $R$), St($hat(Omega)[sigma_1, dots, sigma_m]$, $Gamma'_sigma$, $O$, $G without A(rho)$, $R$)),
  stack(spacing: 0.55em,
    align(center, $group(rho, macron(C), macron(I)) in G quad macron(C) = owed(ell_1, tau_1), dots, owed(ell_m, tau_m) quad macron(I) = owed(ell'_1, S_1), dots, owed(ell'_n, S_n)$),
    align(center, $surrj(Omega_(i-1), ell'_i, S_i, v_i, Omega_i) quad (i = 1, dots, n"," "in issued order")$),
    align(center, $sigma_j = cases(sigma'_j & "if" (ell_j |-> sigma'_j) in rho."pin", "fresh at" tau_j & "else") quad Gamma'_sigma = Gamma_sigma, thin overline(sigma_j : tau_j) space #text[(new entries only)]$),
    align(center, $Omega_n = hat(Omega)[loanm(ell_1), dots, loanm(ell_m)]$)))))
#v(0.5em)

Every issued borrow surrenders first; then the group ends _atomically_, every captured loan releasing in the same step. The ordering is the soundness argument made structural (doc §6.1): a captured owner cannot recover while an issued borrow lives, because the release conclusion is unreachable until every surrender premise is derivable — and no other rule can touch a captured loan (G-EndMut's side condition). The end _discards_ the surrendered payloads and releases each captured loan at its owed type — the caller learns exactly what the signature says, and the forgetting is the deliberate precision cost. The atomic captured release over-approximates the concrete demand-driven ending — doc §6.1 records the simulation obligation — and one concrete demand suffices to fire the whole cascade.

*One arm, and which σ it releases.* This is now the _only_ group end. A second arm once applied a declared backward spec to the surrendered values and released the computed result; the whole declared-`back` tier left the language at this pin (@fig-boundaries records what it was), and a third, test-only arm — an identity wire the checker never minted — left with the differential validation that was its only user. What survives of the precision the spec bought is the $rho."pin"$ premise above: @fig-boundaries's #smallcaps[B-Call] mints one σ′ per captured loan _at the call_, typed at its owed type, and pins the release to it, so that the same σ′ is what the callee's return type reads as the exit $ast.op v$. The caller therefore recovers an owner that its returned evidence is _about_. Where a group carries no pin — a hand-built one, or a capture the call did not mint a σ′ for — the release is an ordinary fresh existential and the caller learns only the type, which is the shape doc §5.3's traces show and the reason the rule still reads as the opaque end.

// RULE-GAP: the pinned release makes a caller's recovered owner and its returned
// evidence the same σ′, but nothing in the rules records that σ′ is the CALLEE's
// exit snapshot — that identification is made by the callee's audit substituting
// its own σ_exit (@fig-boundaries, B-Audit-Val) and by the call reflecting the
// return type against the same σ′. The two ends agree by construction in the
// implementation (callDeclC builds both from one list); a rules-level statement
// of the agreement is a metatheory obligation, not a premise. Reported.

The wire (doc §5.3) is the degenerate group, displayed for the shape doc §5.3's traces use — it is an instance, not a separate mechanism:

#v(0.5em)
#align(center, irule([G-EndOwed #h(0.4em) (= G-EndGroupOpaque with $macron(I) = emptyset$)],
  reorg(St($Omega$, $Gamma_sigma$, $O$, $G$, $R$), St($hat(Omega)[sigma]$, $(Gamma_sigma, sigma : tau)$, $O$, $G without A(rho)$, $R$)),
  $group(rho, owed(ell, tau), emptyset) in G$,
  $Omega = hat(Omega)[loanm(ell)]$,
  $sigma "fresh, or" rho."pin"(ell)$))
#v(0.5em)

Ending a call-annotated loan is where the caller learns what the callee did: a fresh value arrives at the owed type — an existential, opened at loan end. Under `&mut List T` the caller learns only that a list came back; under a type-changing ↝ obligation, its precise new index.

#block(fill: luma(245), inset: 10pt, radius: 4pt, width: 100%)[
  *Global side condition: knowledge vs. state (doc §3.2).* Every conclusion in this figure rewrites $Omega$'s value trees _locally_ — a plug-back, a kill, a release lands at a loan's position and nowhere else. No reorganization ever records its effect by substituting for a $sigma$: the $sigma$'s name _knowledge_ (constructor shapes, equation solutions — facts about a value true at entry and forever), while a hole, a marker, or a mutation's result is _state_, a fact about a slot at a moment. The one $Gamma_sigma$-effect a reorganization has runs the other way — group ends *extend* $Gamma_sigma$ with fresh existentials at the owed types; no existing entry is rewritten. Dually, refinement (⇜, @fig-comptime, @fig-match) substitutes into every $sigma$-bearing component of the state — including the owed types stored in $O$ and in the group nodes of $G$, which is why groups live in $S$ — and its replacement must be marker-free. The implementation asserts both directions at the single substitution site (`refineSym`); instrumenting the whole mechanization found zero violations (doc §3.2).
]

*Where the implementation fires these.* The rules above carry no laziness; the checker's demand-driven scheduling (doc §2's standing convention) is one strategy over them, discussed in @sec-empirics. The governing statement is one line — *every demand collapses first* — and the sites are its instances rather than separate rules. A reorganization fires exactly when a ⇒/⇐/⇝ premise needs one: a ⇒-read of an owner whose value carries an owned-position marker ends it (`readR`, variable case); a move of a borrow whose payload is suspended ends the parked reborrow first (`readR`, same case); a ⇒-*take* through a borrow whose payload is a suspension ends it before taking (`readR`, deref case — #smallcaps[R-Take]'s own-free premise, @fig-runtime); `&mut` of a place holding a parked marker demand-ends its loan — a prior call's whole group, in the sequential-reborrow shape (`readR`, borrow case); a match reorganizes its scrutinee the same way (`reorgScrut`); a *comptime* read on the pure lift collapses the places it is about to project through, a bare variable whose own loan a call still holds included (`collapseCDerefs`); a ⇐ onto a live value vacates it by drop (`writeR`); and the return audit collapses argument-borrow payloads with the same ends (`collapseArg`, and `collapseLoanIn` when the borrow is Σ-packaged and so is not the slot's own value), the boundary being the canonical demander (doc §3.3). One site joined the list at this pin without a new rule: the *end of a program* (`endScope`) demands every loan still parked in $Omega$, because a program that lends a local to a call and never looks at it again has no later demand to fire the group, while the concrete machine releases a frame's loans on the way out of it — so without it the two machines would end in visibly different environments over a difference in *when*.

That the list is *closed* is not decoration. Each of the last three entries was
added after a body reached a state the earlier entries did not cover, and in every
case the symptom was identical: the marker itself was read as though it were a
value, and surfaced layers downstream as an untypeable term. The calculus document
now states the rule once with the sites as instances, rather than per-site, for
exactly that reason — an unlisted site is not a missing convenience but a live
silent-marker bug.

// RULE-GAP (scheduling, not rules): the nondeterministic presentation admits
// derivations the implementation's scheduler never finds. Example: demanding a
// captured owner while an ISSUED borrow's payload is suspended by a live
// reborrow — the rules allow G-EndMut on the parked loan first, then the group
// end; the implementation goes endLoan → endGroup → endIssued directly and
// rejects (hasType cannot type a loanₘ payload). Completeness of the strategy
// w.r.t. these rules is a metatheory question; reported, not resolved.

#v(0.5em)

Test anchors name the bucket file and the section namespace within it (the M28 consolidation put 27 era-numbered files into 10 subject buckets, keeping every namespace).

#xref(
  ([#smallcaps[G-EndMut]], [`endLoan` (ungrouped arm): `killBorrowInΩ` then `sendPayloadToLoan`], [`Traces` (`S2` forced End-Mut before a move, doc §2.5 chain collapse; `S3` field-loan collapse on owner read)]),
  ([#smallcaps[G-DropFree] / #smallcaps[G-DropLoan] / #smallcaps[G-DropBorrow]], [`drop`, node selection via `firstOwnNode`], [`Traces` (`S2` overwrite forces drop, doc §2.3; `S3` variant change ends the field loans, doc §3.4)]),
  ([self-reborrow non-derivation], [`killBorrowInΩ`'s in-flight error], [`Traces` (`S2`, `b := c` rejected, "in flight")]),
  ([#smallcaps[G-EndIssued]], [`endIssued`], [`Boundaries` (`S7Group`, holed issued payload: "nothing surrendered")]),
  ([#smallcaps[G-EndGroupOpaque]], [`endGroup` (now its only arm), `releaseCaptured`], [`Boundaries` (`S7Group`: `choose` cascade, fresh $sigma$'s for both owners; `through`, precision deliberately lost)]),
  ([the $rho."pin"$ release], [`Group.exitRelease`, minted in `callDeclC`], [`Programs` (`S27Mixed`: `swapCaller` recovers an owner its returned proof is about)]),
  ([#smallcaps[G-EndOwed]], [`endGroup` with `issued = []`], [`Boundaries` (`S6Call`, the doc §5.3 wire: "the promise is collected")]),
  ([the demand sites], [`readR` (`.var`/`.deref`/`.borrow`), `reorgScrut`, `collapseCDerefs`, `writeR`, `collapseArg`/`collapseLoanIn`, `Program.endScope`], [`Traces` (`S2`, `S3`), `Boundaries` (`S5Bound`), `Programs` (`S26Prog`)]),
)
