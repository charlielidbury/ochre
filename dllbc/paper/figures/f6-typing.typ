#import "../style.typ": *
== F6: Value typing and conversion <fig-typing>

// SOURCE OF TRUTH: dllbc/Dllbc/Machine.lean (`hasType`, `synthSpine`,
// `checkFields`) and dllbc/Dllbc/Pure.lean (`convert`, `nfV`, `whnfV`,
// `ctorSig`). These rules are AUTHORED from the implementation — the doc had no
// prior figure. Prefix T- for typing, C≡- for conversion (style.typ pin).

The comptime fragment (@fig-comptime) is a small dependent type theory, and this
figure is its judgment of *inhabitation*: when does a value $v$ inhabit a type
$tau$, written $#hasT($v$, $tau$)$? The check is the mechanism behind the money test of §4.2 —
inhabitation is tested against a type that must first *compute* to canonical
form, and a stuck type (an index that never reduced, say #box[$"Vec" T space
sigma_l$] with $sigma_l$ unknown) exposes no constructor, so conversion has
nothing to say yes to and the audit rejects. Two judgments do the work: value
typing $#hasT($v$, $tau$)$ (`hasType`) and definitional conversion $#conv($tau$,
$tau'$)$ (`convert`). They are mutually entangled — every typing leaf ends in a
conversion, and `Refl` is well-typed only up to one.

*Global conventions.* (i) The subject is *weak-head normalized before any rule
fires* (`hasType` calls `whnfV` on $v$ first): a $beta$-redex or a stuck
recursor spine reduces to its weak head, so the rules below read on canonical
subjects. (ii) The rules are stated *nondeterministically and fuel-free*;
conversion is factored out into a single coercion rule #smallcaps[T-Conv], and
the implementation's fusion of a convert-check into each synthesis leaf is one
deterministic reading of it. (iii) There is *no context turnstile* in the
judgment: the σ-context $Gamma_sigma$ (each symbolic value's type, `St.sctx`) is
ambient checker state, consulted where a rule names it.

#block(inset: (left: 1em), stroke: (left: 0.6pt + gray), width: 100%)[
  *Algorithm note (stated once).* `convert` decides $#conv($tau$, $tau'$)$ by
  normalizing both sides to normal form (β and ι, de Bruijn, *no η*) under an
  explicit fuel and comparing syntactically ($#conv($tau$, $tau'$) := "nfV"(tau) =
  "nfV"(tau')$). Because v0 collapses the universe hierarchy to type-in-type
  (§1.1), strong normalization fails (Girard's paradox lives there), so
  conversion — and hence typing — is a *fuel-bounded partial decision
  procedure*, correct on the normalizing fragment where all v0 programs live.
  The fuel is the algorithm's, not the relation's; the rules carry none.
]

=== The conversion judgment $#conv($tau$, $tau'$)$

Definitional equality is the least congruence containing $beta$ and $iota$,
closed under the equivalence laws. Presented as axioms (the normal-form equality
`convert` computes is exactly this relation for a confluent, normalizing
fragment):

#grid(columns: (1fr, 1fr, 1fr), gutter: 1em, align: center + horizon,
  irule("C≡-Refl", conv($tau$, $tau$)),
  irule("C≡-Sym", conv($tau'$, $tau$), conv($tau$, $tau'$)),
  irule("C≡-Trans", conv($tau$, $tau''$), conv($tau$, $tau'$), conv($tau'$, $tau''$)),
)

#v(0.4em)
#align(center, irule("C≡-Cong",
  conv($F(dot.c dot.c dot.c tau_i dot.c dot.c dot.c)$, $F(dot.c dot.c dot.c tau'_i dot.c dot.c dot.c)$),
  conv($tau_i$, $tau'_i$)))

#smallcaps[C≡-Cong] closes conversion under every term former $F ∈ {"app",
"ctor", Pi, Sigma, lambda, "Id"}$, componentwise — normal-form equality is a
congruence by construction.

The computation rules, $beta$ and the $iota$-rules for the recursor basis
(`whnfV` in `Pure.lean`), as directed equations read as conversions:

#block(inset: (left: 1em))[
$
"(C≡-Beta)" & quad (lambda (x : tau). t) space u equiv t[x := u] \
"(C≡-IotaNat)" & quad "natRec" P space z space s space "Z" equiv z
  quad quad "natRec" P space z space s space ("S" space m) equiv s space m space ("natRec" P space z space s space m) \
"(C≡-IotaBool)" & quad "boolRec" P space t space f space "True" equiv t
  quad quad "boolRec" P space t space f space "False" equiv f \
"(C≡-IotaList)" & quad "listRec" A P space p_n space p_c space "Nil" equiv p_n
  quad quad "listRec" A P space p_n space p_c space ("Cons" space h space t) equiv p_c space h space t space ("listRec" A P space p_n space p_c space t) \
"(C≡-IotaJ)" & quad "j" A space a space P space d space b space "Refl" equiv d
  quad quad "(C≡-IotaK)" quad "k" A space a space P space d space "Refl" equiv d \
$
]

A recursor whose target normalizes to a *neutral* (a `sym` or a bound variable,
never a constructor) does not reduce: the spine is a stuck value and convertible
only to itself and its congruent variants — this is what makes `add σ 1` and
`add σ 2` inconvertible (S4Pure). `botElim` has *no* ι-rule: ⊥ has no
constructor, so `botElim T x` is always stuck.

*Deliberately absent: η.* There is no rule $lambda (x : tau). f space x equiv f$.
Two λ's with the same domain differing only in their bodies are *not* convertible
(S4Pure: $lambda (u : "Nat"). u space.quad equiv.not space.quad lambda (u :
"Nat"). "Z"$ is `false`). `convert` compares normal forms structurally; η would
require comparing under an applied/abstracted context, which it does not do.

// RULE-GAP: convert is nf-equality, so it silently includes the FULL congruence
// and equivalence closure — there is no separately-named C≡-App/C≡-Ctor in the
// code, only `nfV a == nfV b`. The C≡-Cong/Refl/Sym/Trans rules above are the
// declarative content of that single equation, not distinct code paths.

=== The value-typing judgment $#hasT($v$, $tau$)$

// T-Type: hasType's .type/.pi/.sigmaT/.idT cases — a former inhabits Type.
==== Universe and type formers

#grid(columns: (1fr, 1fr), gutter: 1em, align: center + horizon,
  irule("T-Type", hasT($"Type"$, $tau$), conv($tau$, $"Type"$)),
  irule("T-Former", hasT($F$, $tau$), $F ∈ {Pi (x:A) arrow.r B, space Sigma (x:A). B, space "Id" A space a space b}$, conv($tau$, $"Type"$)),
)

Type-in-type: $"Type" : "Type"$, and every type former inhabits $"Type"$ (§1.1;
the hierarchy returns with §9). Both are checking rules — the target $tau$ need
only *convert* to $"Type"$, which is where #smallcaps[T-Conv] is folded in.

// T-Sym: hasType's `.sym σ` (non-applied) case — sctx lookup + convert.
==== Symbolic values

#align(center, irule("T-Sym", hasT($sigma$, $tau_sigma$), $Gamma_sigma (sigma) = tau_sigma$))

A symbolic value synthesizes the type the σ-context records for it; other types
follow by #smallcaps[T-Conv]. (In code, the two are fused: the `.sym` case
returns $#conv($tau_sigma$, $tau$)$ directly.) A σ absent from $Gamma_sigma$ is a
checker-internal error, not a `false`.

// T-Ctor: hasType's `.ctor` case + ctorSig table + checkFields dependent thread.
==== Constructors

#align(center, irule("T-Ctor",
  hasT($c(v_1, ..., v_n)$, $tau$),
  $"ctorSig"(c, space "whnf" tau) = [tau_1, ..., tau_n]$,
  $#hasT($v_1$, $tau_1$) quad #hasT($v_2$, $tau_2[x_1 := v_1]$) quad ... quad #hasT($v_n$, $tau_n[x_1 := v_1, ..., x_(n-1) := v_(n-1)]$)$))

The expected type is *whnf'd first*, then matched against the signature table
below to recover the constructor's field-type telescope; a table miss (the
constructor does not inhabit this type former, or the type is stuck) yields
`false`, not an error — this *is* the money-test rejection. Fields are checked
left to right, each subsequent field type instantiated at the *values* of the
earlier fields (`checkFields` threads `substPure 0 vᵢ`): this is exactly how
`Pair`'s second field is typed against the first field's value — dependent Σ.

#align(center, table(columns: (auto, auto, auto), align: (left, left, left), inset: 6pt,
  table.header([*constructor*], [*expected type (whnf)*], [*field telescope*]),
  [`unit`], [$"Unit"$], [$[]$],
  [`True` / `False`], [$"Bool"$], [$[]$],
  [`Z`], [$"Nat"$], [$[]$],
  [`S`], [$"Nat"$], [$["Nat"]$],
  [`Nil`], [$"List" T$], [$[]$],
  [`Cons`], [$"List" T$], [$[T, space "List" T]$],
  [`Pair`], [$Sigma (x:A). B$], [$[A, space B]$ (2nd dependent on 1st)],
  [`Refl`], [$"Id" A space a space b$], [$[]$ if $#conv($a$, $b$)$, else miss],
))

`Refl` is the one signature entry carrying a *side condition*: it inhabits $"Id"
A space a space b$ only when the endpoints convert ($#conv($a$, $b$)$), which is how
`Id`'s reflexive constructor witnesses definitional equality. The table has no
`inductive`-declaration machinery behind it — it is a fixed basis (Unit, Bool,
Nat, List, Σ, Id), the v0 kernel's constructor set (§7.1).

// T-Lam: hasType's `.lam` case — domains convert, body under a fresh σ witness.
==== Functions against a Π

#align(center, irule("T-Lam",
  hasT($lambda (x:A). b$, $tau$),
  $"whnf" tau = Pi (x:A'). C$,
  conv($A$, $A'$),
  $Gamma_sigma, space sigma : A' space ⊢ space #hasT($b[x := sigma]$, $C[x := sigma]$)$))

A λ is checked against a Π: the declared domain must *convert* to the Π's domain,
then the body is checked under a *fresh symbolic witness* $sigma : A'$ added to
$Gamma_sigma$ — the binder opened with a hypothesis of the Π's domain type. This
is what types a Π-typed lemma (`id_sym`, S16Spec) and the recursors' λ-shaped
step arguments (`s`, `pc`). It is the elaboration of dependent elimination
(§9/§10), with no arrow of its own.

// T-ElimSynth: hasType's `.app` neutral case — eliminator-const synthesis + finish/synthSpine.
==== Eliminator-neutral synthesis

A neutral application spine `head args` synthesizes a type only when `head` is
one of the eliminator constants. The fixed prefix is typed to a *base result* —
the motive $P$ applied to the target(s) — its premises checked; any *extra*
arguments (an over-applied eliminator, `natRec … n` at a function motive then
given its argument) are then absorbed by #smallcaps[T-Spine]'s spine synthesis.
One schema, instantiated per eliminator by the table:

#align(center, irule("T-ElimSynth",
  hasT($e space macron(p) space macron(m) space macron(t) space macron("rest")$, $tau'$),
  $"premises"(e, macron(m), macron(t))$,
  $"base" = P(macron(t)) quad "per the table"$,
  $"synthSpine"("base", macron("rest")) = tau''$,
  conv($tau'$, $tau''$)))

#align(center, table(columns: (auto, auto, auto), align: (left, left, left), inset: 6pt,
  table.header([*applied form*], [*premises*], [*base result*]),
  [$"natRec" P space z space s space n$],
    [$#hasT($z$, $P space "Z"$)$; #h(0.3em) $#hasT($s$, $Pi (m:"Nat") arrow.r P space m arrow.r P("S" m)$)$; #h(0.3em) $#hasT($n$, $"Nat"$)$],
    [$P space n$],
  [$"boolRec" P space t space f space b$],
    [$#hasT($t$, $P space "True"$)$; #h(0.3em) $#hasT($f$, $P space "False"$)$; #h(0.3em) $#hasT($b$, $"Bool"$)$],
    [$P space b$],
  [$"listRec" A space P space p_n space p_c space l$],
    [$#hasT($p_n$, $P space "Nil"$)$; #h(0.3em) $#hasT($p_c$, $Pi (h:A) arrow.r Pi (t:"List" A) arrow.r P space t arrow.r P("Cons" h space t)$)$; #h(0.3em) $#hasT($l$, $"List" A$)$],
    [$P space l$],
  [$"botElim" T space x$], [$#hasT($x$, $"Bot"$)$], [$T$],
))

The two `Id`-eliminators, written explicitly (Paulin-Mohring J and Streicher K,
§10):

#grid(columns: (1fr, 1fr), gutter: 1em, align: center + horizon,
  irule("T-Elim-J",
    hasT($"j" A space a space P space d space b space p$, $P space b space p$),
    hasT($d$, $P space a space "Refl"$),
    hasT($p$, $"Id" A space a space b$)),
  irule("T-Elim-K",
    hasT($"k" A space a space P space d space p$, $P space p$),
    hasT($d$, $P space "Refl"$),
    hasT($p$, $"Id" A space a space a$)),
)

These are what let *library* fording terms type-check as ordinary values —
`natNoConf` (a `j`-spine landing in a reducing `NatCode`, hence in ⊥),
constructor injectivity (`injProof` via `j`), UIP (`uipProof` via `k`) — with no
machine rule beyond the eliminators' own typing (S10Ford).

// T-Spine: hasType's `.sym σ` applied case + synthSpine Π-instantiation.
==== Application spines for bound function variables

When the neutral head is a σ (a bound function variable applied — `ih b c hab
hbc`), its type is looked up and the spine is synthesized by iterated
Π-instantiation:

#grid(columns: (1.15fr, 1fr), gutter: 1em, align: center + horizon,
  irule("T-Spine",
    hasT($sigma space a_1 space ... space a_n$, $tau_"res"$),
    $Gamma_sigma (sigma) = tau_sigma$,
    $"synthSpine"(tau_sigma, [a_1, ..., a_n]) = tau_"res"$),
  irule("Spine-Π",
    $"synthSpine"(tau, a :: macron(a)) = tau_"res"$,
    $"whnf" tau = Pi (x:A). B$,
    hasT($a$, $A$),
    $"synthSpine"(B[x := a], macron(a)) = tau_"res"$),
)

`synthSpine` on the empty argument list is the identity ($"synthSpine"(tau, []) =
tau$); each argument checks against the current domain and instantiates the
codomain at the argument's *value*. It is shared with #smallcaps[T-ElimSynth]
(the over-application tail), so ordinary application typing and eliminator
over-application are one mechanism.

// T-Conv: the coercion folded into every leaf `Val.convert fuel _ ty`.
==== Conversion coercion

#align(center, irule("T-Conv", hasT($v$, $tau'$), hasT($v$, $tau$), conv($tau$, $tau'$)))

The single coercion rule: a value keeps its type up to definitional equality.
Nondeterministic here; in code it is *not* a standalone rule but is fused into
every synthesis leaf (`.sym`, `.type`, formers, and each `finish`/`synthSpine`
result all end in `Val.convert fuel _ ty`). There is *no subsumption and no
subtyping* — the calculus has conversion only, never a $tau <= tau'$.

=== What no rule does

*No rule types a hole.* There is no $#hasT($bot$, $tau$)$: ⊥ is the absence of a
value, inhabiting nothing (§2.1). `hasType` never receives a ⊥ that a rule
accepts, and the comptime read that would produce one is rejected upstream
(`reflectC` on a moved slot). This is the same fact the boundary audit leans on
— a function cannot return a hole.

*Ex-falso admission lives in F5, not here.* #smallcaps[T-Elim] above types
`botElim T x` *when `x` is a genuine ⊥-inhabitant* — an ordinary eliminator
application. The *audit-level* rule that admits a dead branch at *any* return
type on the strength of a ⊥-witness (a cursor's `Nil` branch "returning" a borrow
it cannot have) is a boundary rule, `B-ExFalso` in @fig-boundaries — excluded
from this figure by design. The distinction: here the ⊥-witness types a *term*;
there it discharges a *return obligation*.

// ---------- Rule ↔ implementation ↔ test ----------
#v(0.4em)
#xref(
  ([#smallcaps[T-Ctor]], [`hasType` `.ctor`, `checkFields`, `ctorSig`], [S4Pure (dependent `Pair`), S5Bound `vecPush`]),
  ([#smallcaps[T-Sym]], [`hasType` `.sym`, `St.sctx`], [S10Ford `learn`]),
  ([#smallcaps[T-Lam]], [`hasType` `.lam` (fresh-σ body)], [S16Spec `id_sym`]),
  ([#smallcaps[T-ElimSynth]], [`hasType` `.app`, `finish`, `synthSpine`], [S10Ford `j`/`k`/`botElim`/`natNoConf`]),
  ([#smallcaps[T-Spine]], [`hasType` `.sym`-applied, `synthSpine`], [S10Ford `injProof`/`uipProof`; S16Spec]),
  ([#smallcaps[T-Type] / T-Former], [`hasType` `.type`/`.pi`/`.sigmaT`/`.idT`], [S4Pure]),
  ([#smallcaps[T-Conv]], [`Val.convert` at each leaf], [S5Bound money test; S4Pure `VecF`]),
  ([#smallcaps[C≡-Beta] / -Iota], [`convert`, `nfV`, `whnfV`], [S4Pure (stuck neutrals, `VecF`); S10Ford `natCode`]),
  ([#smallcaps[C≡] (no η)], [`convert` = nf-equality], [S4Pure (two λ's)]),
)
