#import "../style.typ": *

// The one auxiliary form new at this pin. Kept LOCAL rather than promoted to
// style.typ, which a concurrent pass owns; promotion (and the removal of the
// now-unused backJ/resolve/hole/checkFn helpers there) is noted in NOTES.md.
#let bodyJ(D, T, b) = $tack.r.double #b space : space #D arrow.r #T$

== F5: Boundaries, calls, and the audit <fig-boundaries>

// Extraction agent: paper-m28. RE-EXTRACTED AT `dc90adce` (the figure's own pin;
// main.typ's pin declaration is a later pass's). Source of truth: Dllbc/Machine.lean
// (sealFn, sealMint, checkRFnBody, seedTelescopeV, markExit, callDeclC, processArgs,
// readCWith, buildResult, collapseArg/collapseLoanIn, reachesLoan, auditObligation,
// collectResultBorrows, auditAction, auditAllPaths, endIssued/endGroup, the
// Group/Obligation/St state), Dllbc/Boundary.lean (auditPaths — all that is left of
// that file), Dllbc/Syntax.lean (hasBorrowT, retMixesBorrow, trivialOwedT),
// Dllbc/Program.lean (checkProgram, endScope) and Dllbc/FnMacro.lean (fnElab).
// Doc anchors: docs/dllbc-arrows.md §5–§6, docs/combining-fns.md §5/§7/§8. Where the
// implementation and the doc disagree, the implementation is followed and the
// disagreement is flagged in a // RULE-GAP comment.
//
// WHAT LEFT THE FIGURE AT THIS PIN, and why it is not a presentational choice:
// B-CheckFn, B-Call-Self, B-Call-Mutual, B-Back-None, B-Back0, B-BackN and the
// suspension-tree resolution `res` all described machinery that no longer exists
// (`checkFn`, `St.selfRec`, `strictSubterm`, `reachesFn`, `Decl.back`,
// `Group.backSpec`, `resolveTree`). See "Declared backward specs, historically"
// below and NOTES.md's `dc90adce` era.

Where the Aeneas toolchain @aeneas-2022 _synthesizes_ a backward function per borrow — a
pure function describing what flows back through it — DLLBC moves that
description into the signature and checks it: the $arrow.r.curve$ obligation is
the backward function's _type_ (#smallcaps[B-Seed-Borrow], #smallcaps[B-Audit]).
At the pin that is the _whole_ of the inversion. The calculus once carried a
second tier — a declared `back`, the backward function itself, audited against
the body claiming to implement it — and it has been removed from the language
rather than deprecated in it; what a caller keeps is what the callee _ascribed_,
and nothing else. This figure is the contract layer that remains: how a function
comes into existence at all (the seal), how its signature is entered (seeding),
how it is used (the call), and how it is discharged (the audit at return — the
_only_ check in the whole borrow story).

*The frame this figure now sits in.* There is no declaration form and no
declaration table. A function is a *sealed runtime λ* — `(λ(x : τ, …){ b } : T)`,
where the ascription is the seal — bound by an ordinary `let`, and a program is
the resulting let-chain (doc combining-fns §8). Three consequences shape every
rule below. Checking a function is an _event_ that fires at its `.seal` node in
program order, not a pass over a table. A callee is reached by *name*: the
binding lexically above the call, so #smallcaps[B-Call] applies a slot's contents
and a forward reference is not a rejected recursion but an unbound variable.
And recursion is not a kernel premise at all — it is handled one layer up, at
elaboration, where a self-call becomes a recursor's `ih` binder or is refused
(see "Recursion, and where it went").

*Reading conventions.* All rules are nondeterministic and fuel-free; the
implementation's fuel bounds its _search_, not the relations. The checker state
is $cal(S) = St(Omega, Gamma_sigma, O, G, R)$ (environment, $sigma$-context,
obligations, groups, pinned return type), and carries two further components the
function model needs: $Phi_sigma$, the *moded-$Pi$ context*, mapping a sealed
function's $sigma$ to the $Pi$ it was sealed at; and $E$, the *exit-snapshot*
side-table of #smallcaps[B-Pin]. Rules display only the components they touch,
the rest ride along unchanged. We write $v in Omega$ (and $loanm(ell) in p$) for
"occurs anywhere inside some slot's value", not merely at top level.
$cal(S)[Omega_1]$ (and likewise for other components) is $cal(S)$ with that
component replaced; $cal(S)[Gamma_sigma, sigma : hat(tau)]$ extends a component
in place. Substitution instances are normalized; $"nf"$ is left implicit except
where the normalization _is_ the check. $O$, $R$ and $G$'s owed types are inside
refinement's reach: an F3 $arrow.l.squiggly$ substitutes into them exactly as
into $Omega$ — a `Refl`-match that refines a $sigma$ rewrites the owed types that
mention it, and the audit sees the refined obligation. Premises draw freely on
the other figures: $arrow.r.double$ (F1), reorganization $arrow.r.long.squiggly$
(F2), $arrow.r.squiggly$ (F3), the symbolic match fork (F4), and typing
$v : tau$ / conversion $equiv$ (F6).

The auxiliary judgment forms, top-down: #bodyJ($Delta$, $T$, $b$) is the sealed
body's check — seed, pin, explore, audit every path — and is what
#smallcaps[B-Seal-Fn] reduces a function to; #seedJ($cal(S)$, $Delta$, $cal(S)'$)
seeds a telescope at entry;
#argsJ($cal(S)$, $theta$, $overline(a)$, $Delta$, $C$, $cal(S)'$, $theta'$)
checks a call's arguments against a telescope, accumulating the instantiation
$theta$ (parameter variable $arrow.r.bar$ checked actual) and the captured loans
$C$; #resJ($theta$, $T$, $v$, $I$, $cal(S)'$) builds a call's fresh result from
the instantiated return type, collecting the issued loans $I$;
#collJ($T$, $v$, $B$) collects, at return, the result's borrow positions against
the return type; #reachJ($ell$, $ell'$) is transitive reachability through
reborrow chains and group links; #obligJ($cal(S)$, $I$, $"ob"$) audits one
obligation given issued loans $I$; and #audit($cal(S)$, $v$) closes the figure.

=== The seal: where a function is checked

Sealing is an F1 $arrow.r.double$-form, and the shape of the sealed _term_ picks
the rule — never the shape of the type. A runtime λ has no value the pure
fragment could type (its body is a body), so "$t$ has type $u$" is not a
#smallcaps[T-…] question at all: it is this figure's audit. Everything that is
not a runtime λ or a recursor spine keeps F6's ordinary rule, which is what makes
sealing a borrow-free term cost precisely `readC`-then-`hasType` as it always
did.

#align(center)[
#irule("B-Seal-Fn",
  $cal(S) tack.r ("seal" space (lambda(overline(x : tau)). b) space u) arrow.r.double sigma tack.l cal(S)[Phi_sigma, sigma : u]$,
  $overline((x : tau)) join u = (Delta space ; space T) quad #text[(the λ's own telescope agrees with the ascription)]$,
  bodyJ($Delta$, $T$, $b$),
  $sigma "fresh" quad (sigma : hat(u)) in Gamma_sigma "iff" "no" amp"mut" "occurs in" u$)
]
#v(0.8em)
#align(center)[
#irule("B-Body",
  bodyJ($Delta$, $T$, $b$),
  $"no" amp"mut" "type occurs in some component of" T "while another carries one"$,
  seedJ($"iso"(Delta, b)$, $Delta$, $cal(S)_0$),
  $cal(S)_0 tack.r "pin"(T) tack.l cal(S)_1 space ("else" cal(S)_1 = cal(S)_0)$,
  $forall space cal(S)_1 tack.r b arrow.r.double v tack.l cal(S)' : quad audit(cal(S)', v)$)
]

#smallcaps[B-Seal-Fn] is two sentences, and they are §5's two. *The check* is one
conversion — the $Pi$ the λ states against the $Pi$ that was ascribed — followed
by the body check on the telescope that agreement yields. The λ _states_ its
telescope rather than receiving it from the ascription, so a mismatch is one
rejection at one place; only the return type comes from $u$, and that is not an
exception to synthesis but the one thing a body cannot synthesize (doc §5 point
4: the ascription is the contract, and a contract is about what comes back).
*The forgetting* mints a fresh $sigma$ carrying that same $Pi$ in $Phi_sigma$,
peeled at _positional_ binders — the convention #smallcaps[B-Inst] and
#smallcaps[B-Res] read a telescope by — so what a caller sees is a callee whose
signature is known and whose body is not. A borrow-moded $Pi$ has no `Val`
(`readC` refuses `borrowT`), so such a $sigma$ lives in $Phi_sigma$ alone and is
callable but not otherwise typeable; a borrow-free one is additionally typed in
$Gamma_sigma$, and the two agree by construction, being read from the same term.

The $"iso"(Delta, b)$ in #smallcaps[B-Body] is *frame isolation*, and it is the
rule's one non-obvious premise. The body is checked in a *fresh* $Omega$, with
fresh obligations and fresh groups, because it is a function being _defined_, not
code running in the caller's world. Exactly two things cross the boundary. In:
the ascribed type, read while the enclosing slots were still live, and the body's
free variables — its *callees*, the bindings lexically above it, resolved and
admitted against the enclosing scope _before_ the wipe (this is also the only
place a sealed function's capture check happens, since a sealed λ never forms a
function value for F1's own closedness check to see). Out: the fresh supplies,
advanced past everything every path minted, so no later mint can collide with a
$sigma$ the check put into a type.

// RULE-GAP: B-Body's first premise is the M27 mixed-return containment
// (`retMixesBorrow`), stated here as a side condition because it is a REFUSAL
// with no rule of its own — see "Three containments" below. It is the reason the
// premise reads "no component may be a value while another is a borrow" rather
// than the more natural "T is a borrow type or it is not".

A recursor sealed at a $Pi$ takes a variant of #smallcaps[B-Seal-Fn] whose
content is the same: the motive is _derived_ from the ascription (the sealed $Pi$
with the scrutinee peeled off) and compared syntactically against the written
one, and then each arm is checked once at its own constructor by
#smallcaps[B-Body], its leading binders being the ones the recursor's premise
gives — the predecessor and `ih`. No path forks: `Z` and `S k` _are_ the split.
`ih` is a telescope entry like any other (#smallcaps[B-Seed-Fn]), typed at the
motive instantiated at the predecessor, and that one fact is the whole recursion
story at kernel level.

=== Seeding the boundary

#align(center)[
#irule("B-Seed-Nil",
  seedJ($cS$, $dot$, $cS$))
#h(2em)
#irule("B-Pin",
  $St(Omega, Gamma_sigma, O, G, dot) tack.r "pin"(T) tack.l St(Omega, Gamma_sigma, O, G, hat(R))$,
  $"no" amp"mut" "type occurs in" T$,
  $overline(sigma_"exit") "fresh, one per borrow param, recorded in" E$,
  evC($Omega$, $"markExit"(T)$, $hat(R)$))
]
#v(0.8em)
#align(center)[
#irule("B-Seed-Pure",
  seedJ($St(Omega, Gamma_sigma, O, G, R)$, $(x : tau), Delta$, $cS'$),
  $tau "not a" amp"mut" "type, not a" Pi "carrying one"$,
  evC($Omega$, $tau$, $hat(tau)$),
  $sigma "fresh"$,
  seedJ($St(Omega[x arrow.r.bar sigma], (Gamma_sigma, sigma : hat(tau)), O, G, R)$, $Delta$, $cS'$))
]
#v(0.8em)
#align(center)[
#irule("B-Seed-Borrow",
  seedJ($St(Omega, Gamma_sigma, O, G, R)$, $(x : borrowT(s, tau, S)), Delta$, $cS'$),
  $x "lowercase (a comptime binder may not be borrow-typed)"$,
  evC($Omega$, $tau$, $hat(tau)$),
  evC($Omega$, $S$, $hat(S)$),
  $sigma, ell "fresh"$,
  seedJ($St(Omega[x arrow.r.bar borrowm(ell, sigma)], (Gamma_sigma, sigma : hat(tau)), (O, oblig(x, ell, hat(S)[s := sigma])), G, R)$, $Delta$, $cS'$))
]
#v(0.8em)
#align(center)[
#irule("B-Seed-Fn",
  seedJ($St(Omega, Gamma_sigma, O, G, R)$, $(x : u), Delta$, $cS'$),
  $u = piT(y, A, B) quad amp"mut" "occurs in" u$,
  $sigma "fresh"$,
  seedJ($St(Omega[x arrow.r.bar sigma], Gamma_sigma, O, G, R)[Phi_sigma, sigma : u]$, $Delta$, $cS'$))
]

Seeding is the callee's half of the telescope discipline. A pure parameter
becomes a fresh symbolic value typed in $Gamma_sigma$; a borrow parameter becomes
a fresh argument borrow $borrowm(ell, sigma)$ over a fresh snapshot, plus an
_obligation_ $oblig(x, ell, hat(S)[s := sigma])$ — the owed type with the
$arrow.r.curve$ binder instantiated at the entry snapshot, the one position that
must outlive its moment (doc §5.2). The entry $sigma$ is _also_ recorded as this
borrow's `old` $ast.op x$ referent, which is what makes the entry payload nameable
in a return type after the body has mutated past it.

#smallcaps[B-Seed-Fn] is the rule that makes recursion cost nothing at kernel
level: a parameter whose type is a borrow-moded $Pi$ — `ih` is the instance that
matters — has no `Val`, so it becomes a $sigma$ with a *signature and no body*,
recorded in $Phi_sigma$ exactly where a sealed function's own $sigma$ goes.
Calling it is therefore the ordinary call rule, and doc combining-fns §7's
convergence argument arrives as a fact about this one branch: the only available
view of the function is the $sigma$-side, so a recursive occurrence is abstract
application at the ascribed $Pi$ — self-ensures _forced_ rather than stipulated.
Nothing in the rule knows it is for a recursor.

Two deliberate absences in #smallcaps[B-Seed-Borrow]. There is _no_ owner entry
for $ell$: the caller holds that loan, so nothing in the body can collapse the
argument borrow by owner-demand — only the audit judges it, which is what makes
the audit the single point where judging is possible. And there is _no
cross-parameter substitution_: a later parameter's type mentions an earlier
parameter by its runtime _variable_ ($x$, resolved to the snapshot by
$arrow.r.squiggly$ each time the type is consulted — for a borrow parameter,
$ast.op x$ peels to the payload snapshot). A pure binder substituted at seed time
would sit unsubstituted under whnf, a rigid neutral, and read as rigid at a
refl-match that should have been flex.

#smallcaps[B-Pin] fixes the return type at entry, while the parameters it may
mention are still live: a dependent return type over a consumed parameter means
its _entry_ value (re-reading at return would find $bot$). A return type carrying
a borrow anywhere is _not_ pinned ($R = dot$): it is audited structurally at
return (#smallcaps[B-Coll-Borrow]) rather than reflected. The pin is not uniform,
and the exception is the propositional architecture's central move (doc §5.4,
@sec-architectures). Before reflecting $T$, the rule mints one fresh
$sigma_"exit"$ per borrow parameter and $"markExit"$ rewrites $T$ so that a
*bare* $ast.op v$ pins to that parameter's $sigma_"exit"$ — the *exit* snapshot —
while `old` $ast.op v$ pins to the entry σ. So a value return type is
entry-pinned in every position except a borrow payload's deref, which reads the
end. The exit σ's live only in the pin and in $E$ — never in $Gamma_sigma$, never
in an obligation — until the audit *defines* them by substituting each borrow's
collapsed final payload, which is why the substitution is a dedicated audit-local
pass and not a ⇜: it carries a mutation's result, and ⇜ is knowledge-only
(@fig-comptime).

A telescope also admits the *runtime-length slice* $Sigma (c : "Nat"). amp"mut" (tau
arrow.r.curve S)$ as a parameter — doc §5's second opacity reaching a telescope
entry. The slot holds a genuine pair, so the length becomes a $sigma$ the body
can name and the borrow carries an ordinary obligation; the rule is
#smallcaps[B-Seed-Borrow] with the payload snapshot substituted under the Σ's own
binder, and it is elided here rather than displayed.

=== The call: consume and promise

Caller-side telescope discipline, symmetric to seeding: arguments are
$arrow.r.double$-consumed left to right, and each checked actual is bound into
the instantiation $theta$ before the remaining parameter types are consulted — so
at a call site $"Fin"("len" ast.op b)$ means the $b$ just passed. The
$arrow.r.squiggly$ premises below read a declaration type against $theta, Omega$:
the parameter variables resolve through $theta$ (which shadows any caller slot),
everything else through $Omega$ (implementation: `readCWith`).

#align(center)[
#irule("B-Inst-Nil",
  argsJ($cS$, $theta$, $dot$, $dot$, $dot$, $cS$, $theta$))
]
#v(0.8em)
#align(center)[
#irule("B-Inst-Pure",
  argsJ($cS$, $theta$, $a, overline(a)$, $(x : tau), Delta$, $C$, $cS'$, $theta'$),
  $x "lowercase"$,
  evR($Omega$, $a$, $v$, $Omega_1$),
  evC($theta, Omega_1$, $tau$, $hat(tau)$),
  $v : hat(tau)$,
  argsJ($cS[Omega_1]$, $theta[x arrow.r.bar v]$, $overline(a)$, $Delta$, $C$, $cS'$, $theta'$))
]
#v(0.8em)
#align(center)[
#irule("B-Inst-Cmp",
  argsJ($cS$, $theta$, $a, overline(a)$, $(X : tau), Delta$, $C$, $cS'$, $theta'$),
  $X "uppercase, " tau "not a" amp"mut" "type"$,
  evC($Omega$, $a$, $v$),
  evC($theta, Omega$, $tau$, $hat(tau)$),
  $v : hat(tau)$,
  argsJ($cS$, $theta[X arrow.r.bar v]$, $overline(a)$, $Delta$, $C$, $cS'$, $theta'$))
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
its loan is _captured_, annotated with the owed type instantiated at the payload
snapshot just passed ($hat(S)[s := w]$ — the caller-side mirror of
#smallcaps[B-Seed-Borrow]'s $hat(S)[s := sigma]$). The parameter is bound in
$theta$ to the actual _borrow_, so a later $ast.op x$ in a type peels to the
payload (doc §5.2 at the call site); a bare $x$ of borrow type in an index
position is outside the unrestricted fragment and unspecified.
#smallcaps[B-Inst-Cmp] is the comptime column: an argument at a *capital*
parameter is read by $arrow.r.squiggly$ — pure and non-consuming — so the caller
keeps it and may cite it after the call, and $Omega$ is unchanged across the
premise. A capital parameter may not be borrow-typed, at the call as at the seed:
a $arrow.r.squiggly$-reading of `&mut` is meaningless. Left-to-right consumption
has a practical corollary (doc §5.3) that the comptime column does _not_ repeal
for runtime arguments: a later runtime argument may not mention a borrow an
earlier one consumed — a bounds proof about $ast.op v$ that is passed at a
lowercase position must be `let`-bound _before_ the call that consumes $v$.

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
Earlier versions of this rule built the two components independently and carried
a rule-gap note saying so — harmless while no caller ever *consumed* a pinned
component, and immediately fatal once a callee's only description is a
$Sigma$-pinned postcondition, since the tail's type reached the caller with a
dangling binder. With declared backs removed, that pin is a caller's _only_ route
to knowing anything about a returned value, so the dependency is now load-bearing
rather than merely correct.

#v(0.8em)
#align(center)[
#irule("B-Call",
  $cS tack.r x(overline(a)) arrow.r.double v tack.l cS_2[G, group(rho, C, I)]$,
  $Omega(x) = sigma quad Phi_sigma (sigma) = u quad "piPeel"(u) = (Delta space ; space T)$,
  $x "lowercase (a capital function-typed binder is a spec parameter)"$,
  argsJ($cS$, $dot$, $overline(a)$, $Delta$, $C$, $cS_1$, $theta$),
  $overline(sigma') "fresh, one per captured loan," space (sigma'_j : tau_j) in Gamma'_sigma$,
  resJ($theta$, $"markExit"_(overline(sigma'))(T)$, $v$, $I$, $cS_2$),
  $rho "fresh"$)
]

A call is checked against the signature alone — recursion forces this, and all
calls get it uniformly. The callee is *located, not consumed*: calling a function
is a place read, so a slot can be called twice, which is what `ih` needs since a
quicksort recurses twice from one arm. What licenses that is the model rather
than F1's copy-on-read — functions are reached by NAME, and calling where bound
is a name-use — and F1's read rule refuses moving a function into a second
binding for the same reason, the two rules being one sentence seen from both
ends.

#smallcaps[B-Res] builds the fresh result from the instantiated return type: a
non-borrow leaf is a fresh existential at the return type (the doc §5.3 _wire_);
each $amp"mut"$ position mints a fresh _issued_ reborrow over a fresh snapshot,
owed-annotated from the return type's own $arrow.r.curve$; a $Sigma$ of borrows
issues one loan per position (`nth2`, the multi-issued group — this calculus's
`split_at_mut`). #smallcaps[B-Call] mints one loan group $group(rho, C, I)$ tying
the captured loans to the issued ones. The group's _ending_ discipline belongs to
F2 (@fig-reorg), cited here rather than restated: each issued borrow surrenders
first (#smallcaps[G-EndIssued] — located anywhere in $Omega$, audited against its
owed type, killed), then the group ends atomically, and
#smallcaps[G-EndGroupOpaque] releases each captured loan with a fresh existential
at its owed type. How much the caller learns is exactly how much the signature
says; the doc §5.3 wire is its $I = dot$ instance, #smallcaps[G-EndOwed].

The $overline(sigma')$ premise is the *exit-snapshot σ-sharing*, and it is what
replaced the declared back as the caller's route to precision. One fresh $sigma'$
is minted per captured borrow, typed at that borrow's owed type; the return type
is `markExit`-rewritten so that a bare $ast.op v$ reflects to $sigma'$, and the
group *pins* that captured loan's release to the same $sigma'$
(#smallcaps[G-EndGroupOpaque]'s pinned case). So the evidence the call returns
and the owner the caller eventually recovers are _the same symbolic value_ — a
returned proof about $ast.op v$ attaches to the value that comes back, instead of
speaking about a σ the group-end then discards. `old` $ast.op v$ clears through to
the actual entry payload instead, unshadowed.

#align(center)[
#irule("B-Call-Unbound",
  $#text[no rule]$,
  $f "names no binding lexically above the call"$)
]

Not a rejected recursion — an *unbound variable*. A `let` is not in scope in its
own right-hand side, so a body's self-call resolves to nothing, and a chain
$f arrow.r g arrow.r f$ through two definitions is a forward reference in the
first of them. Mutual recursion and unguarded self-recursion are therefore ruled
out by *scoping*, with no rule to state and no call-graph analysis to run. This
replaces the pair of rules a declaration table needed (a decreasing-position side
condition on self-calls, and a reachability refusal for mutual ones), and the
replacement is asserted from both sides in the corpus: the witnesses that the
guard used to catch now fail to resolve, and the ones a macro could rewrite are
refused one layer earlier (below).

=== The audit at return

The callee's side, per explored path: the result value $v$ against the return
type, every argument-borrow obligation discharged. The audit is itself a demand,
and it _collapses first_: the #reorgs($cal(S)$, $cal(S)'$) premise in the two
#smallcaps[B-Audit] rules lets F2's reorganizations End-Mut the payloads' field
loans at the boundary — doc §3.3's suspension ending here rather than at an
owner, an argument borrow having none — before conversion judges the collapsed
payloads. Rejection is rule-absence: an orphaned marker (its borrow missing) can
be ended by no G-rule, a hole survives every reorganization and $vbot$ satisfies
no type, and an obligation that is neither locatable nor continued matches no
#smallcaps[B-Oblig]/#smallcaps[B-Exempt] rule — the implementation errors
distinctively in each case ("take without refill", "it was lost").

First, collecting the result's borrow positions against the return type
($B = dot$ is a value-returning body; a borrow-returning type whose result is not
a borrow admits no rule):

#align(center)[
// RULE-GAP: B-Coll-Borrow reads the return type's owed S at RETURN, in the
// exit state, and instantiates the ↝ binder at the CURRENT payload — unlike
// the value return type, it is not entry-pinned (asymmetry with B-Pin; a
// dependent S over a consumed parameter would misread). No test forces it.
// UNCHANGED at this pin; re-verified against collectResultBorrows.
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

Reachability — is this loan connected to that one, through reborrow chains (loan
markers parked in a borrow's payload) or through a group (captured in, issued
out)? "Consumed into the result" is _transitive_: a recursive cursor's outer
result is the inner call's issued borrow, reached from the argument through the
group link.

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
(directly, or as the captured owner of a field reborrow that became the result —
#smallcaps[B-Reach-Refl] folds the direct case in), exempt if consumed onward
into another call (its story continues through _that_ call's group); otherwise it
must be locatable — as a live borrow _anywhere_ in $Omega$, it may have been
moved into a local value — with a marker-free, hole-free payload of its owed
type.

#align(center)[
#irule("B-Exempt-Result",
  obligJ($cS$, $I$, oblig($x$, $ell$, $S$)),
  $S "trivial (as written," amp"mut" tau ")"$,
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

#smallcaps[B-Exempt-Result]'s triviality premise is the second of this pin's
containments and is discussed with the others below; without it the rule is
exactly doc §6.1's "being issued is its exemption", which is correct about the
payload and silently wrong about the owed _type_.

The audit rules themselves. A dead branch is admitted first: a result that is an
eliminator applied to a verified inhabitant of $vbot$ is unreachable, and the
audit admits it at _any_ return type — the $vbot$-witness is the only thing
checked, and no obligation is audited (this is how a bounds-proof cursor's `Nil`
branch "returns" a borrow it cannot have: it doesn't, and needn't; the `botElim`
motive need not be the unreflectable borrow return type).

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
// implementation falls back to re-reading T at return. Not shown. UNCHANGED.
#irule("B-Audit-Val",
  audit($cS$, $v$),
  reorgs($cS$, $cS'$),
  collJ($T$, $v$, $dot$),
  $forall "ob" in O' : space obligJ(cS', dot, "ob")$,
  $hat(R)^E = hat(R)[overline(sigma_"exit" := p_"exit")]$,
  $v : hat(R)^E$)
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
  $forall (ell, p, S) in B : space p : S$)
]

#smallcaps[B-Audit-Val] is doc §5.4's audit exactly: obligations, then the result
against the entry-pinned return type. Its one added premise is #smallcaps[B-Pin]'s
other half arriving — each $sigma_"exit"$ recorded in $E$ is *defined* here as its
borrow's collapsed final payload $p_"exit"$ (folded through
$arrow.r.squiggly$ first, so that a carved-and-rejoined array's exit snapshot is a
value and not a state form on which no predicate computes), and the substitution
is plain, not a ⇜. #smallcaps[B-Audit-Borrow] is doc §6.1's reshaping for a
borrow-returning path: the issued borrows' payloads are audited against the return
type's own owed types, obligations are audited with the exemptions in force, and
no separate result check remains — being issued _is_ the result's typing, its
story continuing caller-side through the group. There is no longer any `back`
premise on either rule.

*The quantification over derivations.* #smallcaps[B-Body]'s last premise —
$forall space cal(S)_1 tack.r b arrow.r.double v tack.l cal(S)' :
space audit(cal(S)', v)$ — is where nondeterminism earns its keep: F4's symbolic match
makes $arrow.r.double$ a genuine relation — one derivation per constructor of a
symbolic scrutinee's type, exhaustiveness enforced at the fork — so "explore all
paths, audit each" is a single $forall$ over derivations. Each derivation carries
its own state: the obligations, pinned return type and exit-snapshot table it
audits against are the ones _that path_ refined. The implementation determinizes
exactly this: a continuation-pushing pre-pass makes every match terminal,
`explore` enumerates the derivations, and the lazy collapse (`collapseArg`, firing
End-Mut innermost-first when the audit demands a marker-free payload) is one
scheduling of the $arrow.r.long.squiggly^*$ premise. The *same* judgment checks a
whole program: `checkProgram` is `explore` plus this $forall$, with no telescope to
seed and no return type to pin, because a program takes no arguments — plus one
extra demand, `endScope`, since a program that lends a local to a call and never
looks at it again would otherwise leave the loan parked forever, and the two
machines would end in visibly different environments over a difference in *when*.

=== Three containments, stated as refusals

Three positions are *unwritable* at this pin, and all three are refusals rather
than rules — the honest move where a check would have nothing to check. Each was
found by an adversarial probe, not by a failing corpus program, which is why they
are stated here rather than left implicit in the rules' shapes.

#block(stroke: 0.5pt, inset: 9pt, radius: 4pt, width: 100%)[
  *(1) A return type may not mix borrow and value components* (#smallcaps[B-Body]'s
  first premise). A borrow-carrying return type is audited _structurally_ and is
  deliberately never pinned, so #smallcaps[B-Audit-Borrow] runs and the value
  check is skipped for the whole type — leaving a non-borrow component of such a
  type judged by nothing at all. That is not vacuous but unsound: the caller's
  #smallcaps[B-Res-Val] mints a σ at the stated leaf type regardless, so the
  caller _receives_ the unearned claim as a proof and may return it at its own
  value return type, where the checking path does run and passes. The witness is
  `fn closedBot () -> Bot` with no hypotheses. Refused rather than repaired,
  because teaching the borrow audit to judge value components would mean checking
  a freshly minted σ against the type it was minted at, which proves nothing.

  *(2) A borrow consumed into the result must owe back what it was lent*
  (#smallcaps[B-Exempt-Result]). The exemption is right about the payload — a
  borrow that left in the result has no payload here to audit — and it takes the
  owed _type_ with it, while the caller's group end mints the release _at_ that
  type. So a non-trivial $arrow.r.curve$ on a consumed parameter is a claim the
  callee is exempted from and the caller receives as fact, checked at neither end.
  A cursor that hands its borrow onward owes back the type it was lent; a richer
  claim belongs on a parameter the body keeps, where the audit runs.

  *(3) A function may not be read into a second binding.* Refused by F1's read
  rule, recorded here because it is the model's own sentence and this figure is
  where the model lives: functions are reached by NAME, and calling where bound
  or passing as an argument are name-uses, while reading one out of its slot is
  the one move that turns a name into a value. It was found as a mechanism bug —
  a σ whose $Pi$ is borrow-moded has no `Val`, so index-kind copying takes the
  move default while the executing machine copies, a simulation break on a
  program *both machines accept* — and it was then generalized past its
  mechanism: the borrow-free case, measured as sound, is refused too, because
  soundness was never what made it wrong.
]

=== Recursion, and where it went

There is no recursion rule in this figure, and the two that used to be here — a
declared decreasing position `[k]` guarding self-calls, and a call-graph
reachability refusal for mutual recursion — are gone with the declaration table
that fed them. What replaced them is not another check. It is *two structural
facts and one macro obligation*:

#block(inset: (left: 1em))[
  #text(size: 9pt)[
  *A recursive occurrence is a binder.* `fn` elaborates a recursing definition to
  a *recursor* whose arms are the body, with each self-call rewritten to an
  application of `ih` — the sealed self-view at the predecessor
  (#smallcaps[B-Seed-Fn]). A binder cannot be a self-call, so there is no premise
  left for a side condition to guard, and the decrease is the recursor's rather
  than the checker's.
  #linebreak()
  *A let-chain cannot reference downward.* A definition that is not a recursion
  gets no `ih`, and its own binding is not in scope in its right-hand side
  (#smallcaps[B-Call-Unbound]) — so `fn bad () -> Id Nat Z (S Z) { bad() }`, the
  witness that made the `[k]` guard necessary, is now unwritable rather than
  rejected. Mutual recursion falls out the same way.
  #linebreak()
  *The macro must not repair a non-terminating source.* `ih` is the self-view at
  the *predecessor*, so rewriting a self-call into one is honest only when that is
  what the call recurses on. `fnElab` checks this before rewriting and refuses
  otherwise — with a distinctive sentinel, `§fn-lowering-refused`, carried as the
  name of a term the kernel then rejects, so that the refusal is observable to a
  test through the ordinary checking path rather than at Lean elaboration time.
  Three source shapes are refused there: a self-call at an argument that is not
  the predecessor, a self-call in the base branch, and a decrease through a
  borrow's *payload*, which has no recursor form at all (fuel-threading is the
  blessed interim, and it is a source change rather than an elaboration).
  ]
]

This is the one place where a soundness-relevant obligation moved _out_ of the
kernel, and it is worth being explicit about the trade. The elaborated term is
well-founded by construction and the kernel re-derives everything about it, so
`fnElab` is not in the trusted base for *soundness*; what it is trusted for is
*faithfulness* — that the function checked is the function written. A macro that
silently rewrote a non-terminating source into a terminating recursor would
produce a term that checks and a claim that is about a different function, which
is precisely the failure the three refusals above exist to prevent.

=== Declared backward specs, historically

Between the second and third pins this figure carried a fourth subsection: rules
#smallcaps[B-Back-None], #smallcaps[B-Back0] and #smallcaps[B-BackN], and a
resolution function taking a body's *suspension tree* — the captured borrow's
payload with the issued loans' markers read as holes — against a declared `back`,
so that a caller's group end could _compute_ each release rather than mint an
existential (@fig-reorg's since-deleted #smallcaps[G-EndGroupBack]). The whole
tier — surface `back = …`, `Decl.back`, `Group.backSpec`, `resolveTree`, both
callee-side checks and the caller-side end — was removed from the language at
this pin. The claim it supported is now made by the $arrow.r.curve$ obligation
and by #smallcaps[B-Call]'s exit-snapshot σ-sharing: *what a caller keeps is what
the callee ascribed.* The rules as they stood, and the three audit-strategy holes
they carried, are recoverable from the paper's history at pin `9d92a894`; two of
those three holes are closed by this deletion rather than by a fix, which
@sec-boundaries and NOTES.md both record as such.

=== Correspondence

Test anchors name the bucket file and the section namespace within it (the M28
consolidation put 27 era-numbered files into 10 subject buckets, keeping every
namespace).

#xref(
  ([#smallcaps[B-Seal-Fn], #smallcaps[B-Body]], [`Machine.sealFn`, `sealMint`, `checkRFnBody`, `piAgree`], [`Functions` (`S26Seal`, `FnStmt`)]),
  ([the recursor variant], [`Machine.sealRec`, `checkArm`, `recLayout`], [`Functions` (`S26Rec`)]),
  ([frame isolation, globals], [`Machine.admitGlobals`, `checkRFnBody` (the wipe)], [`Functions` (`S27Lam`)]),
  ([#smallcaps[B-Seed-Nil/Pure/Borrow/Fn]], [`Machine.seedTelescopeV`], [`Boundaries` (`S5Bound`)]),
  ([#smallcaps[B-Pin]], [`checkRFnBody` (entry pin), `markExit`, `hasBorrowT`], [`Boundaries` (`S12Inst`)]),
  ([#smallcaps[B-Inst-Nil/Pure/Cmp/Borrow]], [`Machine.processArgs`, `readCWith`, `readComptimeArg`], [`Boundaries` (`S6Call`, `S12Inst`), `Programs` (`S26Modes`)]),
  ([#smallcaps[B-Res-Val/Borrow/Pair]], [`Machine.buildResult`], [`Boundaries` (`S7Group`, `nth2`)]),
  ([#smallcaps[B-Call]], [`Machine.callDeclC`, `readR` (`.callV` on an `fsig` σ)], [`Boundaries` (`S6Call`), `Functions` (`FnStmt`)]),
  ([#smallcaps[B-Call]'s exit σ-sharing], [`callDeclC` (`exitRelease`), `Group.exitRelease`], [`Programs` (`S27Mixed`, `swapCaller`)]),
  ([#smallcaps[B-Call-Unbound]], [`readR` (`.call` — "unknown function"), `Program.checkProgram`], [`Programs` (`S26Prog`), `Direct` (`S23Direct`)]),
  ([#smallcaps[B-Coll-Borrow/Pair/Val]], [`Machine.collectResultBorrows`], [`Boundaries` (`S7Group`)]),
  ([#smallcaps[B-Reach-Refl/Chain/Group]], [`Machine.reachesLoan`], [`Boundaries` (`S14Bounds`, `advance`)]),
  ([#smallcaps[B-Exempt-Result/Call], #smallcaps[B-Oblig-Conv]], [`Machine.auditObligation`, `collapseArg`, `collapseLoanIn`], [`Boundaries` (`S7Group` `choose`, `S5Bound`)]),
  ([#smallcaps[B-ExFalso]], [`Machine.auditAction` (`botElim` spine)], [`Boundaries` (`S14Bounds`)]),
  ([#smallcaps[B-Audit-Val/Borrow]], [`Machine.auditAction`], [`Boundaries` (`S5Bound`, `S7Group`)]),
  ([#smallcaps[B-Audit-Paths]], [`Machine.auditAllPaths`, `Boundary.auditPaths`, `Program.checkProgram`, `endScope`], [`Programs` (`S26Prog`), `Direct` (`S23Direct`)]),
  ([containment (1)], [`Syntax.retMixesBorrow`, `retComponents`], [`Programs` (`S27Mixed` §A–§D)]),
  ([containment (2)], [`Syntax.trivialOwedT`, `Obligation.trivialOwed`], [`Programs` (`S27Mixed` §E)]),
  ([containment (3)], [`readR` (`.var`, the `fsig` test)], [`Programs` (`S27Mixed` §F)]),
  ([recursion at elaboration], [`FnMacro.fnElab`, `selfScrutArgs`, `selfToIh`, `hoist`, `fnRefusedNeedle`], [`Direct` (`S23Direct`), `Functions` (`FnStmt`)]),
)
