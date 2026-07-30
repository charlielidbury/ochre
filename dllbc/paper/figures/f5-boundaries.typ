#import "../style.typ": *
== F5: Boundaries, calls, and the audit <fig-boundaries>

// Extraction agent: paper-f5. Source of truth: Dllbc/Boundary.lean (seedTelescope,
// collapseArg, auditObligation, auditAction, collectResultBorrows, resolveTree,
// reachesLoan, checkFn) and Dllbc/Machine.lean (processArgs, readCWith,
// buildResult, endIssued/endGroup, the Group/Obligation/St state). Doc anchor:
// docs/dllbc-arrows.md §5–§6. Rules are authored here for the first time; where
// the implementation and the doc disagree, the implementation is followed and
// the disagreement is flagged in a // RULE-GAP comment.

Where the Aeneas toolchain @aeneas-2022 _synthesizes_ a backward function per borrow — a
pure function describing what flows back through it — DLLBC moves that
description into the signature and checks it: the $arrow.r.curve$ obligation is
the backward function's _type_ (#smallcaps[B-Seed], #smallcaps[B-Audit]), and,
at the precise end of the doc §6.2 spectrum, a declared `back` is the backward
function _itself_, audited against the body it claims to describe
(#smallcaps[B-Back0]/#smallcaps[B-BackN]) rather than synthesized from it.
This figure is the contract layer: how a signature is entered (seeding), how it
is used (the call), and how it is discharged (the audit at return — the _only_
check in the whole borrow story).

*Reading conventions.* All rules are nondeterministic and fuel-free; the
implementation's fuel bounds its _search_, not the relations. $Phi$ is the
ambient declaration table; $d$ ranges over declarations
$"fn" f(Delta) arrow.r T$ with telescope $Delta = (x_1 : tau_1) dots.h (x_n : tau_n)$
and an optional declared backward spec $d."back" = b$. The checker state is
$cal(S) = St(Omega, Gamma_sigma, O, G, R)$ (environment, $sigma$-context,
obligations, groups, pinned return type); rules display only the components they
touch, the rest ride along unchanged. We write $v in Omega$ (and
$loanm(ell) in p$) for "occurs anywhere inside some slot's value", not merely at
top level. $cal(S)[Omega_1]$ (and likewise for other components) is $cal(S)$
with that component replaced; $cal(S)[Gamma_sigma, sigma : hat(tau)]$ extends a
component in place. Substitution instances are normalized; $"nf"$ is left
implicit except where the normalization _is_ the check. $O$, $R$, and the reflected backward
specs are inside refinement's reach: an F3 $arrow.l.squiggly$ substitutes into
them exactly as into $Omega$ — a `Refl`-match that refines a $sigma$ rewrites
the owed types that mention it, and the audit sees the refined obligation.
Premises draw freely on the other figures: $arrow.r.double$ (F1),
reorganization $arrow.r.long.squiggly$ (F2), $arrow.r.squiggly$ (F3), the
symbolic match fork (F4), and typing $v : tau$ / conversion $equiv$ (F6).

// The auxiliary judgment forms (cS, seedJ, argsJ, resJ, collJ, reachJ, obligJ,
// backJ, resolve, hole) are pinned in style.typ alongside the core judgments.

The auxiliary judgment forms, top-down: #seedJ($cal(S)$, $Delta$, $cal(S)'$)
seeds a telescope at function entry; #argsJ($cal(S)$, $theta$, $overline(a)$, $Delta$, $C$, $cal(S)'$, $theta'$)
checks a call's arguments against a telescope, accumulating the instantiation
$theta$ (parameter variable $arrow.r.bar$ checked actual) and the captured loans
$C$; #resJ($theta$, $T$, $v$, $I$, $cal(S)'$) builds a call's fresh result from
the instantiated return type, collecting the issued loans $I$;
#collJ($T$, $v$, $B$) collects, at return, the result's borrow positions
against the return type; #reachJ($ell$, $ell'$) is transitive reachability
through reborrow chains and group links; #obligJ($cal(S)$, $I$, $"ob"$) audits
one obligation given issued loans $I$; #backJ($cal(S)$, $I$, $d$) checks a
declared backward spec against the body's suspension tree; and the two pinned
forms #audit($cal(S)$, $v$) and #checkFn($d$) close the figure.

=== Seeding the boundary

#align(center)[
#irule("B-Seed-Nil",
  seedJ($cS$, $dot$, $cS$))
#h(2em)
#irule("B-Pin",
  $St(Omega, Gamma_sigma, O, G, dot) tack.r "pin"(T) tack.l St(Omega, Gamma_sigma, O, G, hat(R))$,
  $"no" amp"mut" "type occurs in" T$,
  $overline(sigma_"exit") "fresh, one per borrow param"$,
  evC($Omega$, $"markExit"(T)$, $hat(R)$))
]
#v(0.8em)
#align(center)[
#irule("B-Seed-Pure",
  seedJ($St(Omega, Gamma_sigma, O, G, R)$, $(x : tau), Delta$, $cS'$),
  $tau "not a" amp"mut" "type"$,
  evC($Omega$, $tau$, $hat(tau)$),
  $sigma "fresh"$,
  seedJ($St(Omega[x arrow.r.bar sigma], (Gamma_sigma, sigma : hat(tau)), O, G, R)$, $Delta$, $cS'$))
]
#v(0.8em)
#align(center)[
#irule("B-Seed-Borrow",
  seedJ($St(Omega, Gamma_sigma, O, G, R)$, $(x : borrowT(s, tau, S)), Delta$, $cS'$),
  evC($Omega$, $tau$, $hat(tau)$),
  evC($Omega$, $S$, $hat(S)$),
  $sigma, ell "fresh"$,
  seedJ($St(Omega[x arrow.r.bar borrowm(ell, sigma)], (Gamma_sigma, sigma : hat(tau)), (O, oblig(x, ell, hat(S)[s := sigma])), G, R)$, $Delta$, $cS'$))
]

Seeding is the callee's half of the telescope discipline. A pure parameter
becomes a fresh symbolic value typed in $Gamma_sigma$; a borrow parameter
becomes a fresh argument borrow $borrowm(ell, sigma)$ over a fresh snapshot,
plus an _obligation_ $oblig(x, ell, hat(S)[s := sigma])$ — the owed type with
the $arrow.r.curve$ binder instantiated at the entry snapshot, the one position
that must outlive its moment (doc §5.2). Two deliberate absences. There is _no_
owner entry for $ell$: the caller holds that loan, so nothing in the body can
collapse the argument borrow by owner-demand — only the audit judges it, which
is what makes the audit the single point where judging is possible. And there is
_no cross-parameter substitution_: a later parameter's type mentions an earlier
parameter by its runtime _variable_ ($x$, resolved to the snapshot by
$arrow.r.squiggly$ each time the type is consulted — for a borrow parameter,
$ast.op x$ peels to the payload snapshot). A pure binder substituted at seed
time would sit unsubstituted under whnf, a rigid neutral, and read as rigid at a
refl-match that should have been flex. #smallcaps[B-Pin] fixes the return type
at entry, while the parameters it may mention are still live: a dependent return
type over a consumed parameter means its _entry_ value (re-reading at return
would find $bot$). A return type carrying a borrow anywhere is _not_ pinned
($R = dot$): it is audited structurally at return (#smallcaps[B-Coll-Borrow])
rather than reflected.

The pin is not uniform, and the exception is the propositional architecture's
central move (doc §5.4, @sec-architectures). Before reflecting $T$, the rule mints
one fresh $sigma_"exit"$ per borrow parameter and $"markExit"$ rewrites $T$ so that
a *bare* $ast.op v$ pins to that parameter's $sigma_"exit"$ — the *exit* snapshot —
while `old` $ast.op v$ pins to the entry σ. So a value return type is entry-pinned
in every position except a borrow payload's deref, which reads the end. The exit
σ's live *only* in the pin and in an `exitSyms` side-table — never in
$Gamma_sigma$, never in an obligation — until the audit *defines* them by
substituting each borrow's collapsed final payload, which is why the substitution
is a dedicated audit-local pass and not a ⇜: it carries a mutation's result, and ⇜
is knowledge-only (@fig-comptime). Earlier versions of these rules pinned entry
wholesale and flagged the difference as an unimplemented decision; it is
implemented at this pin.

=== The call: consume and promise

Caller-side telescope discipline, symmetric to seeding: arguments are
$arrow.r.double$-consumed left to right, and each checked actual is bound into
the instantiation $theta$ before the remaining parameter types are consulted —
so at a call site $"Fin"("len" ast.op b)$ means the $b$ just passed. The
$arrow.r.squiggly$ premises below read a declaration type against
$theta, Omega$: the parameter variables resolve through $theta$ (which shadows
any caller slot), everything else through $Omega$ (implementation: `readCWith`).

#align(center)[
#irule("B-Inst-Nil",
  argsJ($cS$, $theta$, $dot$, $dot$, $dot$, $cS$, $theta$))
]
#v(0.8em)
#align(center)[
#irule("B-Inst-Pure",
  argsJ($cS$, $theta$, $a, overline(a)$, $(x : tau), Delta$, $C$, $cS'$, $theta'$),
  evR($Omega$, $a$, $v$, $Omega_1$),
  evC($theta, Omega_1$, $tau$, $hat(tau)$),
  $v : hat(tau)$,
  argsJ($cS[Omega_1]$, $theta[x arrow.r.bar v]$, $overline(a)$, $Delta$, $C$, $cS'$, $theta'$))
]
#v(0.8em)
#align(center)[
#irule("B-Inst-Borrow",
  argsJ($cS$, $theta$, $a, overline(a)$, $(x : borrowT(s, tau, S)), Delta$, $owed(ell, hat(S)[s := w]), C$, $cS'$, $theta'$),
  evR($Omega$, $a$, $borrowm(ell, w)$, $Omega_1$),
  evC($theta, Omega_1$, $tau$, $hat(tau)$),
  $w : hat(tau)$,
  evC($theta, Omega_1$, $S$, $hat(S)$),
  argsJ($cS[Omega_1]$, $theta[x arrow.r.bar borrowm(ell, w)]$, $overline(a)$, $Delta$, $C$, $cS'$, $theta'$))
]

A pure argument is consumed and checked at its (instantiated) parameter type. A
borrow argument must evaluate to a borrow; its payload is checked at $tau$, and
its loan is _captured_, annotated with the owed type instantiated at the
payload snapshot just passed ($hat(S)[s := w]$ — the caller-side mirror of
#smallcaps[B-Seed-Borrow]'s $hat(S)[s := sigma]$). The parameter is bound in
$theta$ to the actual _borrow_, so a later $ast.op x$ in a type peels to the
payload (doc §5.2 at the call site); a bare $x$ of borrow type in an index position
is outside the unrestricted fragment and unspecified. Left-to-right consumption
has a practical corollary (doc §5.3): a later argument expression may not
mention a borrow an earlier argument consumed — a bounds proof about
$ast.op v$ must be `let`-bound _before_ the call that consumes $v$.

#align(center)[
#irule("B-Res-Val",
  resJ($theta$, $T$, $sigma$, $dot$, $cS[Gamma_sigma, sigma : hat(R)]$),
  $T "neither an" amp"mut" "type nor a" Sigma$,
  evC($theta, Omega$, $T$, $hat(R)$),
  $sigma "fresh"$)
]
#v(0.8em)
#align(center)[
#irule("B-Res-Borrow",
  resJ($theta$, $borrowT(s, tau, S)$, $borrowm(ell_r, sigma)$, $owed(ell_r, hat(S)[s := sigma])$, $cS[Gamma_sigma, sigma : hat(tau)]$),
  evC($theta, Omega$, $tau$, $hat(tau)$),
  evC($theta, Omega$, $S$, $hat(S)$),
  $sigma, ell_r "fresh"$)
]
#v(0.8em)
#align(center)[
#irule("B-Res-Pair",
  resJ($theta$, $Sigma(x : A). B$, $"Pair"(v_1, v_2)$, $I_1, I_2$, $cS_2$),
  resJ($theta$, $A$, $v_1$, $I_1$, $cS_1$),
  resJ($theta$, $B[x := v_1]$, $v_2$, $I_2$, $cS_2$))
]

#smallcaps[B-Res-Pair] is *dependent*: the tail is built at $B[x := v_1]$, the
head's freshly-minted component substituted in, one binder at a time from the
outside so that each substitution shifts the remaining binders down as it goes.
Earlier versions of this rule built the two components independently and carried a
rule-gap note saying so — harmless while no caller ever *consumed* a pinned
component, and immediately fatal once a callee's only description is a
$Sigma$-pinned postcondition, since the tail's type reached the caller with a
dangling binder.
#v(0.8em)
#align(center)[
#irule("B-Call",
  $cS tack.r f(overline(a)) arrow.r.double v tack.l cS_2[G, groupb(rho, C, I, hat(b))]$,
  $Phi(f) = "fn" f(Delta) arrow.r T$,
  argsJ($cS$, $dot$, $overline(a)$, $Delta$, $C$, $cS_1$, $theta$),
  resJ($theta$, $T$, $v$, $I$, $cS_2$),
  $rho "fresh"$,
  $(#evC($theta, Omega_2$, $b$, $hat(b)$) space "iff" space Phi(f)."back" = b)$)
]

#v(0.8em)
#align(center)[
#irule("B-Call-Self",
  $cS tack.r f(overline(a)) arrow.r.double v tack.l cS'$,
  $cS."selfRec" = (f, (k, c))$,
  $a_k = "the actual at the declared decreasing position"$,
  $a_k subset.sq c quad #text[(strict structural subterm)]$,
  $cS tack.r f(overline(a)) arrow.r.double v tack.l cS' quad #text[(B-Call)]$)
#h(2em)
#irule("B-Call-Mutual",
  $#text[no rule]$,
  $cS."selfRec" = (g, thin dot) quad g eq.not f$,
  $#reachJ($f$, $g$) #text[ in the call graph of ] Phi$)
]

A call is checked against the signature alone — recursion forces this, and all
calls get it uniformly. That uniformity has one consequence a *self*-call must pay
for. Admitting `f`'s own call at `f`'s declared return type, with nothing else
required, is Hoare's recursion rule without its side condition, and under a return
type that carries real content every false postcondition proves itself
(@sec-lessons). #smallcaps[B-Call-Self] is that side condition. The declaration
names a decreasing position `[k]` (doc §1.2); the checker holds that parameter's
*current snapshot* $c$ — seeded at entry and thereafter carried by ⇜ along with
every other σ-bearing component, so inside `match n { S(m) => … }` it reads
`S` $sym("m")$ — and the call is admitted only if the actual at $k$ is a strict
structural subterm of it. Because the checker is a symbolic interpreter, that test
is ordinary structural comparison; no measure and no termination checker appears
anywhere. A borrow parameter decreases through its *payload* snapshot, which is the
only thing that shrinks in a list cursor. #smallcaps[B-Call-Mutual] is the absence
of a rule: the guard is per-declaration, so `f` $arrow.r$ … $arrow.r$ `f` through
another declaration would let each admit the other's postcondition with nothing
decreasing anywhere, and reachability in the call graph rejects it outright rather
than approximating it. `[k]` is *declared* and not inferred, for two reasons that
are both fatal to inference: "some argument decreases at each call" is unsound,
since two branches can each shrink a different coordinate while growing the other
forever; and paths are explored independently, so no single inferred index could be
committed to across them. #smallcaps[B-Res] builds the fresh result from the
instantiated return type: a non-borrow leaf is a fresh existential at the
return type (the doc §5.3 _wire_); each $amp"mut"$ position mints a fresh _issued_
reborrow over a fresh snapshot, owed-annotated from the return type's own
$arrow.r.curve$; a $Sigma$ of borrows issues one loan per position (`nth2`, the
multi-issued group — this calculus's `split_at_mut`). #smallcaps[B-Call] mints
one loan group $group(rho, C, I)$ tying the captured loans to the issued
ones; when the callee declares a backward spec, the group carries it,
instantiated at the actuals ($hat(b)$). The group's _ending_ discipline belongs
to F2 (@fig-reorg), cited here rather than restated: each issued borrow
surrenders first (#smallcaps[G-EndIssued] — located anywhere in $Omega$,
audited against its owed type, killed), then the group ends atomically.
#smallcaps[G-EndGroupOpaque] releases each captured loan with a fresh
existential at its owed type — "the promise is collected", and how much the
caller learns is exactly how much the signature says; the doc §5.3 wire is its
$I = dot$ instance, #smallcaps[G-EndOwed]. #smallcaps[G-EndGroupBack] consumes
exactly what this figure supplies: the $hat(b)$ minted at #smallcaps[B-Call]
and audited against the callee's body at #smallcaps[B-BackN]/#smallcaps[B-Back0]
below, applied to the surrendered payloads in issued order — the captured loan
releases the _computed_ value, no existential minted. Sound because declared
and checked; the once-tried signature-_inferred_ version was unsound
(`through` and `advance` share a signature) and is gone. Two boundary-relevant
provisos are F2's ledger, not re-derived here: #smallcaps[G-EndGroupBack]
exists only for a single captured loan (a multi-captured declared back
silently degrades to the opaque end), and surrender performs _no_ collapse —
the collapse step lives exclusively in this figure's audit, next.

=== The audit at return

The callee's side, per explored path: the result value $v$ against the return
type, every argument-borrow obligation discharged. The audit is itself a
demand, and it _collapses first_: the #reorgs($cal(S)$, $cal(S)'$) premise in
the two #smallcaps[B-Audit] rules lets F2's reorganizations End-Mut the
payloads' field loans at the boundary — doc §3.3's suspension ending here rather
than at an owner, an argument borrow having none — before conversion judges the
collapsed payloads. Rejection is rule-absence: an orphaned marker (its borrow
missing) can be ended by no G-rule, a hole survives every reorganization and
$vbot$ satisfies no type, and an obligation that is neither locatable nor
continued matches no #smallcaps[B-Oblig]/#smallcaps[B-Exempt] rule — the
implementation errors distinctively in each case ("take without refill", "it
was lost").

First, collecting the result's borrow positions against the return type
($B = dot$ is a value-returning body; a borrow-returning type whose result is
not a borrow admits no rule):

#align(center)[
// RULE-GAP: B-Coll-Borrow reads the return type's owed S at RETURN, in the
// exit state, and instantiates the ↝ binder at the CURRENT payload — unlike
// the value return type, it is not entry-pinned (asymmetry with B-Pin; a
// dependent S over a consumed parameter would misread). No test forces it.
#irule("B-Coll-Borrow",
  collJ($borrowT(s, tau, S)$, $borrowm(ell, p)$, $(ell, p, hat(S)[s := p])$),
  evC($Omega$, $S$, $hat(S)$))
#h(1.5em)
#irule("B-Coll-Val",
  collJ($T$, $v$, $dot$),
  $T "neither an" amp"mut" "type nor a" Sigma$)
]
#v(0.8em)
#align(center)[
#irule("B-Coll-Pair",
  collJ($Sigma(x : A). B$, $"Pair"(v_1, v_2)$, $B_1, B_2$),
  collJ($A$, $v_1$, $B_1$),
  collJ($B$, $v_2$, $B_2$))
]

Reachability — is this loan connected to that one, through reborrow chains
(loan markers parked in a borrow's payload) or through a group (captured in,
issued out)? "Consumed into the result" is _transitive_: a recursive cursor's
outer result is the inner call's issued borrow, reached from the argument
through the group link.

#align(center)[
#irule("B-Reach-Refl",
  reachJ($ell$, $ell$))
#h(1.5em)
#irule("B-Reach-Chain",
  reachJ($ell$, $ell'$),
  $borrowm(ell, p) in Omega$,
  $loanm(ell_c) in p$,
  reachJ($ell_c$, $ell'$))
#h(1.5em)
#irule("B-Reach-Group",
  reachJ($ell$, $ell'$),
  $group(rho, C, I) in G$,
  $ell in C$,
  $ell_i in I$,
  reachJ($ell_i$, $ell'$))
]

One obligation, given the issued loans $I$: exempt if consumed into the result
(directly, or as the captured owner of a field reborrow that became the result
— #smallcaps[B-Reach-Refl] folds the direct case in), exempt if consumed onward
into another call (its story continues through _that_ call's group); otherwise
it must be locatable — as a live borrow _anywhere_ in $Omega$, it may have been
moved into a local value — with a marker-free, hole-free payload of its owed
type.

#align(center)[
#irule("B-Exempt-Result",
  obligJ($cS$, $I$, oblig($x$, $ell$, $S$)),
  reachJ($ell$, $ell'$),
  $ell' in I$)
#h(1.5em)
#irule("B-Exempt-Call",
  obligJ($cS$, $I$, oblig($x$, $ell$, $S$)),
  $group(rho, C, I') in G$,
  $ell in C$)
]
#v(0.8em)
#align(center)[
#irule("B-Oblig-Conv",
  obligJ($cS$, $I$, oblig($x$, $ell$, $S$)),
  $borrowm(ell, p) in Omega$,
  $"no" loanm(dot) "and no" vbot "in" p$,
  $p : S$)
]

The audit rules themselves. A dead branch is admitted first: a result that is
an eliminator applied to a verified inhabitant of $vbot$ is unreachable, and
the audit admits it at _any_ return type — the $vbot$-witness is the only thing
checked, and no obligation is audited (this is how a bounds-proof cursor's
`Nil` branch "returns" a borrow it cannot have: it doesn't, and needn't; the
`botElim` motive need not be the unreflectable borrow return type).

#align(center)[
#irule("B-ExFalso",
  audit($cS$, $v$),
  $v = "botElim" space T' space w$,
  $w : "Bot"$)
]
#v(0.8em)
#align(center)[
// RULE-GAP: if R was never pinned (a borrow occurs somewhere in T yet the
// path's result is value-returning — e.g. a borrow under a Π), the
// implementation falls back to re-reading T at return. Not shown.
#irule("B-Audit-Val",
  audit($cS$, $v$),
  reorgs($cS$, $cS'$),
  collJ($T$, $v$, $dot$),
  $forall "ob" in O' : space obligJ(cS', dot, "ob")$,
  backJ($cS'$, $dot$, $d$),
  $v : hat(R)$)
]
#v(0.8em)
#align(center)[
#irule("B-Audit-Borrow",
  audit($cS$, $v$),
  reorgs($cS$, $cS'$),
  collJ($T$, $v$, $B$),
  $B eq.not dot$,
  $I = "loans"(B)$,
  $forall "ob" in O' : space obligJ(cS', I, "ob")$,
  $forall (ell, p, S) in B : space p : S$,
  backJ($cS'$, $I$, $d$))
]

#smallcaps[B-Audit-Val] is doc §5.4's audit exactly: obligations, then the result
against the entry-pinned return type $hat(R)$. #smallcaps[B-Audit-Borrow] is
its doc §6.1 reshaping for a borrow-returning path: the issued borrows' payloads
are audited against the return type's own owed types, obligations are audited
with the exemptions in force, and no separate result check remains — being
issued _is_ the result's typing, its story continuing caller-side through the
group. The $"back"$ premise is vacuous for a spec-less declaration
(#smallcaps[B-Back-None] below); for a spec-carrying one it is the doc §6.2 callee
check.

=== Declared backward specs: the callee check

The doc §6.2 callee side. A declared back is checked against the _suspension tree_
the body actually built: the captured borrow's payload with the issued loans'
markers read as holes $hole("i")$ (pure de Bruijn, in issued order), resolved
down reborrow chains and _through sub-calls' declared backs_ — the tree _is_
the backward function the body implements, and LLBC's backward functions
compose exactly here. Resolution (first matching clause applies; $hat(f)$ is a
sub-group's instantiated spec):

$ resolve(I, loanm(ell)) & = hole(i) & "if" ell = I_i \
  & = "nf"(hat(f) space resolve(I, loanm(ell'_1)) space dots.h space resolve(I, loanm(ell'_m))) space & "if" ell in C "for some" groupb(rho, C, (ell'_1 dots.h ell'_m), hat(f)) in G \
  & = resolve(I, p) & "if" borrowm(ell, p) in Omega \
  & = loanm(ell) & "otherwise" \
  resolve(I, borrowm(ell, p)) & = hole(i) & "if" ell = I_i \
  & = borrowm(ell, resolve(I, p)) & "otherwise" \
  resolve(I, c(overline(v))) & = c(resolve(I, overline(v))) quad quad resolve(I, v) = v "otherwise" $

The second clause is composition: a loan captured by a sub-call's group
resolves to _that_ call's declared back applied to its (recursively resolved)
issued borrows. Composition is all-or-nothing — a spec-less sub-group falls to
the fourth clause, an unresolvable marker no spec ever converts against, so a
spec-carrying function's whole call tree must be spec'd. Recursion is fine: a
recursive call resolves through the function's own declaration.

#align(center)[
#irule("B-Back-None",
  backJ($cS$, $I$, $d$),
  $d."back" = dot$)
]
#v(0.8em)
#align(center)[
// b̂ throughout: d.back reflected at ENTRY over the telescope snapshots
// (checkFn's selfBack), then ⇜-refined per path like the owed types — not
// re-read at the audit.
#irule("B-BackN",
  backJ($cS$, $I$, $d$),
  $d."back" = b$,
  $oblig(x, ell_c, S) in O$,
  reachJ($ell_c$, $ell'$),
  $ell' in I$,
  $"raw" = cases(p & "if" borrowm(ell_c, p) in Omega, loanm(ell_c) & "else")$,
  $resolve(I, "raw") equiv "nf"(hat(b) space hole(0) space dots.h space hole(k - 1))$)
]
#v(0.8em)
#align(center)[
// The value-returning dual (M20): zero holes, checked directly against the
// argument borrow's resolved suspension tree.
#irule("B-Back0",
  backJ($cS$, $dot$, $d$),
  $d."back" = b$,
  $oblig(x, ell, S) in O$,
  $borrowm(ell, p) in Omega$,
  $resolve(dot, p) equiv "nf"(hat(b))$)
]

#smallcaps[B-BackN] ($k = |I| > 0$) checks a borrow-returning body: the
captured borrow is the obligation consumed into the result (directly — its
loan _is_ a result loan, `through` — or as the owner of a field reborrow that
became the result, `advance`/`nth2`); its payload, or the hole itself if it was
returned directly, resolves to the tree, which must convert with the spec
applied to the holes. #smallcaps[B-Back0] is the value-returning dual: an
in-place mutator issues no borrows, so the spec is applied to _no_ holes and
checked against the argument borrow's resolved tree directly. Until the dual
was implemented a value-returning body's back went unchecked at its own audit
(a lying `partScanL` variant passed; the borrow-returning branch was the only
one that looked) — the lesson generalizes: a negative test per rule _branch_,
not per feature. The dual's reach is precise, and stated as a proviso rather
than a premise: it checks a back authored _as the raw tree_ — `partScanL`,
being literally the composition of its sub-calls' declared backs, converts —
while a back that _reformulates_ the tree (`swapS`'s $"swapL" i j ast.op v$
against the set-based composition it actually implements: semantically equal,
never definitionally so) is outside conversion's reach and is the
differential's to validate. Complementary, not redundant. The principled close,
deferred: admit a reformulated back with a _cited bridging equation_ — the
audit doing rewrite-by-Id along a proved
$"Id"("swapL" i j l, "set" i dots.h ("set" j dots.h l))$ — so reformulation
becomes checked rather than trusted.
// RULE-GAP: two implementation holes the rules do not show. (1) Both back
// checks select the FIRST qualifying obligation (caps.head? / obs.head?) —
// a multi-borrow-argument spec'd fn would have its later captured borrows'
// trees unchecked. (2) Both pass vacuously when no obligation qualifies, and
// B-Back0 also when the argument borrow is not locatable (consumed whole into
// a sub-call) — a declared back can go unaudited on such paths. Neither is
// exercised by a test; both are audit-strategy holes worth closing before any
// soundness statement quantifies over declared specs.

=== The top rule

#align(center)[
#irule("B-CheckFn",
  checkFn($d$),
  $d = "fn" f(Delta) arrow.r T in Phi$,
  seedJ($"init"(Phi)$, $Delta$, $cS_0$),
  $cS_0 tack.r "pin"(T) tack.l cS_1 space ("else" cS_1 = cS_0)$,
  $(#evC($Omega_0$, $b$, $hat(b)$) space "iff" space d."back" = b)$,
  $forall space cS_1 tack.r "body"(d) arrow.r.double v tack.l cS' : quad audit(cS', v)$)
]

Seed the telescope, pin the return type while the parameters are live
(#smallcaps[B-Pin], skipped for a borrow-carrying $T$), reflect the
declaration's own back over the entry snapshots, then _quantify over every
$arrow.r.double$-derivation of the body_ and audit each. The quantification is
where nondeterminism earns its keep: F4's symbolic match makes
$arrow.r.double$ a genuine relation — one derivation per constructor of a
symbolic scrutinee's type, exhaustiveness enforced at the fork — so "explore
all paths, audit each" is a single $forall$ over derivations. Each derivation
carries its own state: the obligations, pinned return type, and reflected back
it audits against are the ones _that path_ refined. Throughout the audit rules,
$T$, $d$, and $O$ are the checked declaration's, ambient; $Phi$ contains $d$
itself, so a recursive call resolves — against the signature, never the body —
without unrolling. The implementation determinizes exactly this figure: a
continuation-pushing pre-pass makes every match terminal, `explore` enumerates
the derivations, and the lazy collapse (`collapseArg`, firing End-Mut
innermost-first when the audit demands a marker-free payload) is one scheduling
of the $arrow.r.long.squiggly^*$ premise.

=== Correspondence

#xref(
  ([#smallcaps[B-Seed-Nil/Pure/Borrow]], [`Boundary.seedTelescope`], [`S5Bound`]),
  ([#smallcaps[B-Pin]], [`Boundary.checkFn` (entry pin), `hasBorrowT`], [`S12Inst`]),
  ([#smallcaps[B-Inst-Nil/Pure/Borrow]], [`Machine.processArgs`, `readCWith`], [`S6Call`, `S12Inst`]),
  ([#smallcaps[B-Res-Val/Borrow/Pair]], [`Machine.buildResult`], [`S7Group` (`nth2`)]),
  ([#smallcaps[B-Call]], [`Machine.readR` (`.call`, checking mode)], [`S6Call`]),
  ([#smallcaps[B-Call-Self]], [`Machine.strictSubterm`, `St.selfRec`], [`S23Direct`]),
  ([#smallcaps[B-Call-Mutual]], [`Machine.reachesFn`], [`S23Direct`]),
  ([#smallcaps[B-Coll-Borrow/Pair/Val]], [`Boundary.collectResultBorrows`], [`S7Group`]),
  ([#smallcaps[B-Reach-Refl/Chain/Group]], [`Boundary.reachesLoan`], [`S14Bounds` (`advance`)]),
  ([#smallcaps[B-Exempt-Result/Call], #smallcaps[B-Oblig-Conv]], [`Boundary.auditObligation`, `collapseArg`], [`S7Group` (`choose`), `S5Bound`]),
  ([#smallcaps[B-ExFalso]], [`Boundary.auditAction` (`botElim` spine)], [`S14Bounds`]),
  ([#smallcaps[B-Audit-Val/Borrow]], [`Boundary.auditAction`], [`S5Bound`, `S7Group`]),
  ([#smallcaps[B-Back-None/Back0]], [`Boundary.auditAction` (value dual)], [`S19Partition` (`partScan`)]),
  ([#smallcaps[B-BackN], $"res"$], [`Boundary.auditAction`, `resolveTree`], [`S17Spec`]),
  ([#smallcaps[B-CheckFn]], [`Boundary.checkFn`, `Machine.explore`], [`S5Bound`, `SDeclUnified`]),
)
