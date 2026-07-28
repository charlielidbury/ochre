#import "../style.typ": *
== F3: The comptime arrows (⇝/⇜) <fig-comptime>

// Authored from the implementation as source of truth: `Dllbc/Pure.lean`
// (whnfV/nfV — β and the six ι-rules) and `Dllbc/Machine.lean` (reflectC/readC
// — the Ω-facing ⇝ rules; refineSym/reflUnify/generalizeStuck — the ⇜ rules).
// Presented NONDETERMINISTICALLY and fuel-free: the ⇝ premises recurse big-step
// (the implementation's fuel is one terminating schedule of a confluent system),
// and every "stuck" case below is the *absence* of a rule, never a side effect.

The comptime pair is the runtime pair (@fig-runtime) restricted to the
borrow-free, assignment-free fragment: ⇝ is the ⇒ column minus the borrowing
rows, minus `:=`, and minus consumption (doc §1.3). Two shape facts encode that
restriction and are worth stating before the rules. First, *⇝ carries no output
environment* — the judgment is $evC(Omega, t, v)$, with no $Omega'$. That shape
*is* the effect-freedom claim: a comptime read cannot move, mint, or assign, so
it has nothing to hand back (the sole footprint any ⇝-evaluation leaves is the
fresh pure entries its `let`s bind, and those are confined to the premise that
uses them — rule #smallcaps[C-Let]). Second, ⇜ is the checker's *refinement*
judgment $refi(S, x, t, S')$: it has no surface syntax (no program text
elaborates to ⇜), fires only at match-branch entry, and rewrites the whole
checker state by substitution. Throughout this figure the state abbreviates
$S = St(Omega, Gamma_sigma, O, G, R)$ — the environment, the σ-context, the
boundary obligations (@fig-boundaries), the loan groups (@fig-boundaries), and
the pinned return type.

=== The ⇝ arrow: reduction (β and ι)

`readC` is reflect-then-normalize: `reflectC` maps a term into a value
(resolving Ω snapshot reads, below) and `nfV` normalizes it by β and ι. The
reduction rules read directly off `whnfV`.

#align(center)[#stack(dir: ttb, spacing: 1.2em,
  irule(
    "C-Beta",
    $evC(Omega, (lambda (x : tau). t) space u, v)$,
    $evC(Omega, t[x := u], v)$,
  ),
  grid(columns: 2, column-gutter: 2.4em, row-gutter: 1.2em,
    irule(
      "C-IotaNatZ",
      $evC(Omega, "natRec" space P space z space s space n, v)$,
      $evC(Omega, n, ctorv("Z", ""))$,
      $evC(Omega, z, v)$,
    ),
    irule(
      "C-IotaNatS",
      $evC(Omega, "natRec" space P space z space s space n, v)$,
      $evC(Omega, n, ctorv("S", m))$,
      $evC(Omega, s space m space ("natRec" space P space z space s space m), v)$,
    ),
  ),
  grid(columns: 2, column-gutter: 2.4em, row-gutter: 1.2em,
    irule(
      "C-IotaJ",
      $evC(Omega, "j" space A space a space P space d space b space p, v)$,
      $evC(Omega, p, ctorv("Refl", ""))$,
      $evC(Omega, d, v)$,
    ),
    irule(
      "C-IotaK",
      $evC(Omega, "k" space A space a space P space d space p, v)$,
      $evC(Omega, p, ctorv("Refl", ""))$,
      $evC(Omega, d, v)$,
    ),
  ),
)]

*Gloss.* #smallcaps[C-Beta] is ordinary β: a `lam`-headed spine substitutes its
argument (`substPure 0 u b` in the implementation — the delayed-lift substitution
of the perf note). #smallcaps[C-IotaNatZ]/#smallcaps[C-IotaNatS] are the two
`natRec` ι-rules: reduce the target, and fire on its constructor — `Z` selects
the base, `S m` unfolds one step and recurs. *`boolRec` and `listRec` follow the
identical scheme* (reduce the scrutinee; one rule per constructor —
`True`/`False` for `boolRec`, `Nil`/`Cons h t` for `listRec`, the `Cons` case
recurring on the tail exactly as `S m` recurs on the predecessor); they are
elided here for space. #smallcaps[C-IotaJ] and #smallcaps[C-IotaK] are the
fording kit's eliminators (doc §10) and get explicit rules: Paulin-Mohring `j`
and Streicher `k` both fire *only* on `Refl`, collapsing to the `Refl`-case
witness `d`. `botElim` has no ι-rule at all — ⊥ has no constructors, so a
`botElim` spine is always a stuck value.

=== The ⇝ arrow: reflection (the Ω-facing rules)

These three are `reflectC`: how a comptime read consults Ω. Each is
non-destructive — Ω is read, never written.

#align(center)[#stack(dir: ttb, spacing: 1.2em,
  grid(columns: 2, column-gutter: 2.4em, row-gutter: 1.2em, align: bottom,
    irule(
      "C-Snap",
      $evC(Omega, x, v)$,
      $Omega(x) = v$,
      $v eq.not vbot$,
    ),
    irule(
      "C-Deref",
      $evC(Omega, *t, v)$,
      $evC(Omega, t, borrowm(ell, v))$,
      $v "proper"$,
    ),
  ),
  irule(
    "C-Let",
    $evC(Omega, ("let" x = "rhs" \; "rest"), w)$,
    $evC(Omega, "rhs", v)$,
    $evC(Omega\, x arrow.r.bar v, "rest", w)$,
  ),
)]

*Gloss.* #smallcaps[C-Snap] is the snapshot read: a variable resolves to the
value its slot *currently* holds, and — crucially — does not consume it (no
$Omega'$; the owner keeps the value). The side-condition $v eq.not vbot$ is the
`reflectC` guard (doc §2.1): every read-shaped rule excludes the vacant slot, so
a comptime read of a moved or uninitialized variable is *stuck*, not a silent ⊥.
#smallcaps[C-Deref] is the comptime deref (doc §5.2): $*(borrowm(ell, v))$
projects the payload snapshot $v$ — a pure projection, never a store lookup, so a
type mentioning `*b` is never stale. The proviso "$v$ proper" is load-bearing: a
*suspended* borrow whose payload carries loan markers (mid-match, @fig-match) has
no meaningful snapshot, and comptime deref is undefined on it until the reborrows
end. #smallcaps[C-Let] is the pure `let`: reflect the right-hand side, bind it as
a *fresh* Ω entry, and read the body under the extension. The extension
$Omega, x arrow.r.bar v$ appears only in the premise — it is the one sanctioned
footprint of a comptime read (doc §1.3), scoped to the body's evaluation and
invisible in the conclusion's no-$Omega'$ shape.

#block(inset: (left: 1em))[
  #text(size: 8.5pt)[
  *Footnote (kernel gap, doc'd in the milestones record).* #smallcaps[C-Let]
  presents what ⇝ does *today*: `reflectC` eliminates the `let` at reflection
  time by binding a fresh Ω entry. The value-level normalizer `nfV` has *no*
  `letIn` rule — `Val` has no `let` former at all — so `let` reduces only along
  the reflection pass, never during pure normalization or conversion. `let` is
  thus one of the two bimodal surface forms (with `&mut`); a single kernel `nfV`
  `letIn`/β rule would make it mode-free. Whether to add it (kernel simplicity)
  or keep the surface split is an open decision, deliberately left to the user.
  ]
]

=== Stuckness is the absence of a rule

One prose note covers every ⇝ dead-end, since none is a side effect. A recursor
whose target reduces to a *neutral* (a bare $sym("")$, or a stuck spine) matches
no ι-rule and is returned as a stuck value — this is exactly the "type computes
under a stuck index" property the `Vec` encoding relies on
($"VecF" space "Nat" space ctorv("S", sym("l"))$ unfolds while $sym("l")$ is
unknown; doc §4.2).
`botElim` never fires. A comptime read of ⊥ is stuck (#smallcaps[C-Snap]'s
side-condition). And the refl-match below is stuck when neither endpoint is a
flexible σ. In each case there is simply no rule, and the value stands as a legal
stuck neutral.

=== The ⇜ arrow: refinement

Refinement fires at branch entry, once the scrutinee has been read (⇝) to expose
what it holds. It substitutes globally, subject to a single deep invariant:

#block(fill: luma(236), inset: 10pt, radius: 3pt, width: 100%, stroke: 0.5pt + luma(170))[
  #set text(size: 9pt)
  *Global knowledge/state constraint on every X-rule (doc §3.2 — the calculus's
  deepest invariant).* Write $S[sigma := t]$ for substituting $t$ for $sym("")$
  in *every* σ-bearing component of the checker state:
  #h(0.4em) $Omega$, the σ-context $Gamma_sigma$, the boundary obligations $O$,
  every loan group in $G$ (its captured and issued owed types, and its backward
  spec), the pinned return type $R$, and the self-back spec.
  #linebreak()
  #v(0.35em)
  This has a *dual* that bounds what a refinement may carry. ⇜ propagates
  *knowledge* — a constructor shape true of the value timelessly, or an equation
  solution — and never *state*. The replacement $t$ must be marker-free: no hole
  $vbot$, no $loanm(ell)$, no $borrowm(ell, "")$ (enforced at `refineSym` by
  `hasStateMarker`). Consequently the *only* σ-substitutions in the entire
  calculus are match-shape refinement (#smallcaps[X-Shape]) and equation
  solutions (#smallcaps[X-Sol]) — *never* a mutation's result. Substituting a
  take, a fill, or an End-Mut plug-back for a σ would make the snapshot track the
  present, which is the staleness doc §0 promises snapshots can never have. (Audited
  across the whole mechanization: zero violations.)
]

#v(0.6em)

#align(center)[#stack(dir: ttb, spacing: 1.2em,
  irule(
    "X-Shape",
    $refi(S, p, ctorv(C, overline(sigma)), S[sym("") := ctorv(C, overline(sigma))])$,
    $evC(Omega, p, sym(""))$,
    $Gamma_sigma (sym("")) = tau$,
    $C in "ctors"(tau)$,
    $overline(sigma) "fresh, typed by" C"'s telescope"$,
  ),
  grid(columns: 2, column-gutter: 1.8em, row-gutter: 1.2em, align: bottom,
    irule(
      "X-Sol",
      $refi(S, p, ctorv("Refl", ""), S[sym("") := b'])$,
      $hasT(p, borrowT(A, a, b) #h(-1em))$,
      $evC(Omega, a, sym(""))$,
      $evC(Omega, b, b')$,
      $sym("") in.not b'$,
    ),
    irule(
      "X-SolRefl",
      $refi(S, p, ctorv("Refl", ""), S)$,
      $hasT(p, borrowT(A, a, b) #h(-1em))$,
      $evC(Omega, a, a')$,
      $evC(Omega, b, b')$,
      $conv(a', b')$,
    ),
  ),
  irule(
    "X-Gen",
    $refi(S, x, sym("b"), S[e := sym("b")])$,
    $evC(Omega, x, e)$,
    $e "a stuck spine" (e eq.not sym(""))$,
    $hasT(sym("b"), "Bool") "fresh"$,
  ),
)]

*Gloss.* #smallcaps[X-Shape] is the branch-entry refinement of doc §3.2/doc §3.3.
Once the scrutinee place $p$ reads to a symbolic $sym("")$ (owned mode: $p = x$;
borrow mode: $p = *x$, the deref cell of the ⇜ column), the branch for
constructor $C$ mints fresh field σ's — typed by $C$'s field telescope in
$Gamma_sigma$, which is what discharges the obligation that $C$ actually inhabits
$sym("")$'s type — and substitutes $ctorv(C, overline(sigma))$ for $sym("")$
*everywhere*. In owned mode the scrutinee slot then goes to ⊥ and the binders
take the fresh σ's; in borrow mode the payload becomes $ctorv(C, ...)$ over fresh
loan markers (a suspended parent) and the binders become reborrows — but the
*refinement* is this one rule either way, run first.

#smallcaps[X-Sol] and #smallcaps[X-SolRefl] are the refl-match *solution
transition* (doc §10, `reflUnify`): matching a symbolic $p : borrowT(A, a, b)$
against `Refl` unifies the endpoints. Whnf both; if one side is a flexible
$sym("")$ not occurring in the other (#smallcaps[X-Sol]; the occurs-check
side-condition $sym("") in.not b'$ is mandatory), refine it to the other side
everywhere; if the endpoints already convert (#smallcaps[X-SolRefl]), the
refinement is the identity on state. This is *solution only* — no injectivity,
conflict, or cycle: when *both* endpoints are rigid the match is stuck (no rule),
naming `j`/`k` as the elimination route the library must take.

#smallcaps[X-Gen] is the stuck-spine split (doc §19, `generalizeStuck`), the
machine-level inverse of substitution. When a `match`/`if` scrutinee reads to a
stuck neutral spine $e$ (e.g. `leb` $sym("")$ $sym("p")$ — an application, *not* a
bare σ), no #smallcaps[X-Shape] can fire, since refinement needs a substitutable
σ. So normalize $e$, mint a fresh $sym("b") : "Bool"$, and abstract every
occurrence of $e$ to $sym("b")$ across the same all-of-state targets $[sigma :=
t]$ reaches. The ordinary #smallcaps[X-Shape] on $sym("b")$ (`True`/`False`) then
refines the spine per branch, in values *and* types alike.

#block(inset: (left: 1em))[
  #text(size: 8.5pt)[
  *#smallcaps[Rule-gap] notes (implementation vs. this figure / doc).*
  #linebreak()
  #box(width: 1.2em)[•] *C-Deref proviso.* `reflectC`'s deref case projects a
  `borrowM`'s payload *unconditionally* — it does not test the payload for loan
  markers. The "$v$ proper" side-condition of #smallcaps[C-Deref] is the doc's
  intent (doc §5.2: comptime deref is stuck on a suspended payload); today
  stuckness surfaces one layer downstream instead (`nfV` treats a marker as a
  leaf; a later `hasType` rejects it), rather than at the peel. Reported, not
  resolved.
  #linebreak()
  #box(width: 1.2em)[•] *Comptime `match` deferred.* `reflectC` errors on a
  surface `.matchE` ("not implemented in the comptime fragment"). ι-reduction of
  case analysis is therefore reached *only* through the recursor constants
  (#smallcaps[C-IotaNat…] etc.), never a `match` form — the doc's §3.1 note that
  the v0 mechanization "defers comptime match entirely." So the doc's arrow table
  entry marking `match` as ⇝-defined is aspirational at the surface; it holds
  today only via the recursors it elaborates to (doc §9).
  #linebreak()
  #box(width: 1.2em)[•] *#smallcaps[X-Gen] is Bool-only.* `generalizeStuck` mints
  a $sym("b") : "Bool"$ specifically; generalizing a stuck spine of another type
  is not implemented (nothing needs it yet — the only stuck-scrutinee split in
  the corpus is `leb`/`if`).
  ]
]

=== Rule ↔ implementation ↔ test

#xref(
  ([#smallcaps[C-Beta]],          [`Pure.whnfV` (β case)],                    [`S4Pure`]),
  ([#smallcaps[C-IotaNatZ/S]],    [`Pure.whnfV` (`natRec`)],                  [`S4Pure`]),
  ([#smallcaps[C-IotaBool/List]], [`Pure.whnfV` (`boolRec`/`listRec`)],       [`S4Pure`, `S11Lib`]),
  ([#smallcaps[C-IotaJ/K]],       [`Pure.whnfV` (`j`/`k`)],                    [`S10Ford`]),
  ([#smallcaps[C-Snap]],          [`Machine.reflectC` (`.var`)],              [`S4Pure`, `S3Sym`]),
  ([#smallcaps[C-Deref]],         [`Machine.reflectC` (`.deref`)],            [`S5Bound`]),
  ([#smallcaps[C-Let]],           [`Machine.reflectC` (`.letIn`)],            [`S4Pure`]),
  ([#smallcaps[X-Shape]],         [`Machine.refineSym` via `symOwnedSetup`/`symBorrowSetup`], [`S3Sym`]),
  ([#smallcaps[X-Sol/Refl]],      [`Machine.reflUnify` → `refineSym`],        [`S10Ford`]),
  ([#smallcaps[X-Gen]],           [`Machine.generalizeStuck` (`abstractInto`)], [`S19Partition` (`stuckProbe`)]),
)
