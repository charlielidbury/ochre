#import "../style.typ": *

== F4: Match <fig-match>

// Match is the calculus's ONLY eliminator (§3): no field projection, no tag
// test, no destructor. Its symbolic rule is the founding identification —
// entering a branch on a symbolic scrutinee IS dependent pattern matching in
// the Agda style, refinement by unification and substitution (⇜), not by
// threading equality proofs. This figure owns the M- prefix (style.typ §55).

Match is the only eliminator, and its symbolic rule is the calculus's founding
identification: *entering a branch on a symbolic scrutinee is dependent pattern
matching* in the Agda style — refinement by unification and substitution (the
⇜ of @fig-comptime), never by threading equality proofs. The concrete modes are
the two ways a branch's binders meet the scrutinee — an owned value is
*destructured* (§3.1), a mutable borrow is matched *through* (§3.3) —
and the symbolic split (§3.2) is where type-checking becomes case analysis.

The scrutinee is a *variable* (a substitutable identity is what refinement
needs), and branch patterns bind constructor fields one level deep;
`overline(x)` denotes the field-binder vector, `overline("br")` the branch
list, `Δ_C` the field telescope of constructor `C`, and `"ctors"(T)` the
constructor set of type `T`. Inside a `match` term a branch is written
`C(overline(x)) => t`.

// ---- local match-specific term notation (the pinned ⇒/⇜ arrows and the
// checker state S = ⟨Ω;Γσ;O;G;R⟩ come from style.typ; only term-level syntax
// is introduced here, per style's "no local *judgment* syntax" rule). ----
#let mtch(s) = $"match" #s space { overline("br") }$
#let arm(c, xs, t) = $#c (#xs) => #t$
#let susp(l, c, ls) = $#borrowm(l, $#c ( #ls )$)$
#let setres(v, om) = ${ (#v, #om) }$

=== Scrutinee reorganization (a shared premise)

Every rule below assumes the scrutinee slot has first been *reorganized*, lazily
and innermost-first, until it exposes a constructor or a symbolic value
(`reorgScrut`). Three reorganizations can fire, each owned by another figure and
cited, not restated: End-Mut on a *suspended owner* or a *reborrowed payload*
(@fig-reorg); and, when the scrutinee whnf-reduces to a *stuck spine* — a
neutral `Bool` like $"leb" thin sigma thin sigma'$, not a bare σ — its
generalization to a fresh $sigma_b : "Bool"$ across the whole state
(@fig-comptime, `X-Gen`), after which it dispatches as an owned-symbolic
scrutinee. The outcome is one of four dispatches: owned or borrow mode, concrete
or symbolic.

=== Concrete modes

#irule("M-Owned",
  evR($Omega$, mtch($x$), $v$, $Omega'$),
  $Omega(x) = #ctorv($C$, $overline(v)$)$,
  $#arm($C$, $overline(x)$, $t$) in overline("br")$,
  evR($Omega[x |-> #vbot, thin overline(x) |-> overline(v)]$, $t$, $v$, $Omega'$),
)

Owned destructuring (§3.1): the scrutinee is ⇒-consumed (its slot ← ⊥), its
fields move into the binders, and the selected branch body is evaluated. On
concrete values this is ι-reduction wearing binder syntax.

#irule("M-Borrow",
  evR($Omega$, mtch($x$), $v$, $Omega''$),
  $Omega(x) = #borrowm($ell$, $#ctorv($C$, $overline(v)$)$)$,
  $#arm($C$, $overline(x)$, $t$) in overline("br") quad overline(ell') "fresh"$,
  $Omega' = Omega[x |-> #susp($ell$, $C$, $overline(#loanm($ell'$))$), thin overline(x)_i |-> #borrowm($ell'_i$, $v_i$)]$,
  evR($Omega'$, $t$, $v$, $Omega''$),
)

Matching *through* a mutable borrow (§3.3): each field binder becomes a
whole-value *reborrow* of its component (fresh loan $ell'_i$), and the parent's
payload becomes a `C` of loan markers — the parent is *suspended*, since no
rule reads through a loan, so the children's intermediate states are
unobservable through `x`. The field writes inside the branch are *contract-free
strong updates*. The field loans do *not* end at branch exit; they collapse
only when a demand arrives through the parent chain — the owner is read
(End-Mut, @fig-reorg) or the boundary audit fires (@fig-boundaries) — §3.3's
precision on the collapse trigger. The nullary case (`Nil()`) is degenerate:
no binders, no loans issued, the refinement alone updates the payload.

=== Symbolic modes: the split

Inside a body, arguments are symbolic. A match on a symbolic scrutinee does not
reduce to one successor — it *forks*, and the judgment is *set-valued*:
$
  Omega tack.r #mtch($x$) arrow.r.double #setres($v_i$, $Omega_i$)_i
$
— one $(#text[result], #text[state])$ pair per branch, checked independently.
Duplication, not a join, is the baseline (§3.5): the continuation is re-checked
under each branch (see the elaboration note below), so there is no merge step
and each path carries its own refined state. The runs are up to renaming of loan
and symbolic ids, which branches mint independently. Nondeterministic, no fuel
in the judgment (the implementation bounds spine depth only).

#irule("M-Exhaust",
  $"exhaustive"(sigma, overline(C))$,
  $#sctx($sigma$, $T$) in Gamma_sigma$,
  $"ctors"(T) subset.eq { overline(C) }$,
)

A side-condition on both symbolic rules: the branch heads $overline(C)$ must
cover the scrutinee type's constructor set (`checkExhaustive`). A missing branch
is an accepted-but-concretely-stuck program, so exhaustiveness is the simulation
theorem's precondition made syntactic. `Bot`'s constructor set is empty, so the
empty match on a `Bot` scrutinee is vacuously exhaustive.

#irule("M-OwnedSym",
  $Omega tack.r #mtch($x$) arrow.r.double #setres($v_i$, $Omega'_i$)_i$,
  $Omega(x) = #sym($$) quad #sctx($sigma$, $T$) in Gamma_sigma quad "exhaustive"(sigma, overline(C))$,
  $#text[for each ] #arm($C_i$, $overline(x)_i$, $t_i$) in overline("br") : quad overline(sigma)_i : Delta_(C_i) #text[ fresh]$,
  $S tack.r x arrow.l.squiggly #ctorv($C_i$, $overline(#sym($$))_i$) tack.l S_i quad #text[(X-Shape)]$,
  evR($Omega_i [x |-> #vbot, thin overline(x)_i |-> overline(#sym($$))_i]$, $t_i$, $v_i$, $Omega'_i$),
)

The symbolic owned split (§3.2) — *the founding identification made a rule*.
Branch entry is a ⇜ refinement (`X-Shape`, @fig-comptime): the constructor shape
$C_i(overline(sigma)_i)$ is substituted for σ *everywhere* in the whole checker
state $S$ (Ω, the σ-context, obligations, groups, the pinned return type — not Ω
alone), and only then are the field σ's minted, *typed by the instantiated field
telescope* $Delta_(C_i)$ (dependent positions instantiated at the earlier fresh
σ's — `typeFieldSyms`), the scrutinee consumed, and the branch body checked.
$Omega_i$ is the Ω-projection of the refined state $S_i$.

#irule("M-BorrowSym",
  $Omega tack.r #mtch($x$) arrow.r.double #setres($v_i$, $Omega''_i$)_i$,
  $Omega(x) = #borrowm($ell$, $#sym($$)$) quad #sctx($sigma$, $T$) in Gamma_sigma quad "exhaustive"(sigma, overline(C))$,
  $#text[for each ] #arm($C_i$, $overline(x)_i$, $t_i$) in overline("br") : quad overline(sigma)_i : Delta_(C_i) #text[ fresh] quad overline(ell')_i #text[ fresh]$,
  $S tack.r ast.op x arrow.l.squiggly #ctorv($C_i$, $overline(#sym($$))_i$) tack.l S_i quad #text[(X-Shape, at the payload)]$,
  $Omega'_i = Omega_i [x |-> #susp($ell$, $C_i$, $overline(#loanm($ell'$))_i$), thin overline(x)_(i,j) |-> #borrowm($ell'_(i,j)$, $#sym($$)_(i,j)$)]$,
  evR($Omega'_i$, $t_i$, $v_i$, $Omega''_i$),
)

Borrow mode on a symbolic payload (§3.3): refine *at the payload* (⇜ at `*x`,
substituting σ everywhere) *then* reborrow the fields, suspending the parent —
the same field-loan / suspension structure as `M-Borrow`, entered per path.

#irule("M-Refl-Flex",
  $Omega tack.r "match" x { "Refl" => t } arrow.r.double #setres($v$, $Omega'$)$,
  $Omega(x) = #sym($$) quad #sctx($sigma$, $"Id" A thin a thin b$) in Gamma_sigma$,
  $a arrow.b.double a' quad b arrow.b.double b' quad a' = #sym($f$) quad #sym($f$) in.not "syms"(b')$,
  $S tack.r #sym($f$) arrow.l.squiggly b' tack.l S_1 quad #text[(X-Sol)]$,
  $S_1 tack.r x arrow.l.squiggly "Refl" tack.l S_2$,
  evR($Omega_2 [x |-> #vbot]$, $t$, $v$, $Omega'$),
)

The refl-match — the *solution* transition (`reflUnify`, via `mintFieldSyms`).
Matching `Refl` at an identity type whnf-unifies the endpoints: a *flex*
endpoint (a substitutable σ not occurring on the other side — the occurs check
is real) is solved to the other by `X-Sol` (@fig-comptime), symmetrically in
$a$/$b$; the scrutinee's own σ is then refined to `Refl` (a second ⇜), and the
`Refl` branch, being field-free, consumes and continues. The borrow case is
identical at `*x`.

// RULE-GAP: rigid–rigid Refl is STUCK — no rule. The kernel does no
// injectivity / conflict / cycle reasoning; those are the fording library's job
// via the j/k eliminators (@fig-comptime). `reflUnify` throws ("both endpoints
// rigid … use j/k"); there is deliberately no M-rule for it.
When both endpoints whnf to rigid heads, the match is *stuck* — there is no
rule. The kernel performs no injectivity, conflict, or cycle reasoning; such
identities are eliminated by the `j`/`k` fording eliminators (@fig-comptime),
not by a match rule.

=== The σ-typing obligation

The premise $overline(sigma)_i : Delta_(C_i)$ hides an obligation: the branch
constructors must be constructors *of the scrutinee's type* — $C_i$ must belong
to $"ctors"(T)$, and $Delta_(C_i)$ is read from the signature table with its
dependent positions instantiated (`mintFieldSyms` / `typeFieldSyms`). The
symbolic machinery cannot see this alone; it is discharged by the σ-context
$Gamma_sigma$ of the comptime fragment (§9). A stray constructor is rejected
("does not belong"), distinct from the exhaustiveness rejection above.

=== Elaboration note (not a rule)

`match` is a statement-position form. A syntactic pre-pass pushes each match's
continuation into every branch (`let y = match … ; k` and `match … ; k` become
*terminal* matches, duplicating `k`), so every match splits in tail position and
the continuation is re-checked once per branch (`pushContinuations`, then
`explore`). This is the §3.5 *duplication baseline*: maximally precise, no
generalization step, worst-case exponential in match-nesting depth. A *symbolic*
match left in *expression* position (a constructor argument) cannot split and
is rejected ("expression position"); a concrete expression-position match is
fine.

// RULE-GAP: the §3.5 JOIN (reorganize branches to a common shape, then
// generalize differing pure values — ⇜ run backwards) is a documented FUTURE
// widening to control the duplication cost. It is NOT implemented — there is no
// M-Join rule, and nothing downstream depends on it (doc's own v0 note).
// RULE-GAP: comptime ι-reduction of `match` on the pure fragment (§3.1, the ⇝
// column) is UNIMPLEMENTED — `reflectC` errors on `.matchE` ("match not
// implemented in the comptime fragment this milestone"). No ⇝-match rule;
// deferred to §9's substitution discipline for binders.

#v(0.5em)
The §3.5 *join* (reorganize branches to a common shape, then generalize the
values that still differ — the ⇜ of refinement run backwards) is a documented
future *widening* of this duplication; it is not implemented, and no rule
depends on it. Comptime match (the ⇝ column, §3.1) is likewise deferred.

=== Correspondence

#xref(
  ([M-Owned],     [`ownedSelect`, `readR`/`exploreMatch`], [`S3` §3.1]),
  ([M-Borrow],    [`borrowSelect`],                        [`S3` §3.3–3.4]),
  ([M-OwnedSym],  [`symOwnedSetup`, `exploreSymBranches`], [`S3Sym`, `S5Bound`]),
  ([M-BorrowSym], [`symBorrowSetup`],                      [`S3Sym`, `S5Bound`]),
  ([M-Refl-Flex], [`reflUnify` (via `mintFieldSyms`)],     [`S10Ford`]),
  ([M-Exhaust],   [`checkExhaustive`],                     [`S5Bound`]),
  ([σ-typing],    [`typeFieldSyms`, `mintFieldSyms`],      [`S5Bound`]),
  ([X-Gen (cited)], [`generalizeStuck`, `reorgScrut`],     [`S19Partition`]),
)
