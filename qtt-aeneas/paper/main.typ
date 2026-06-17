// ============================================================
//  Fusing Quantitative Type Theory and Aeneas
//  A single calculus for dependently-typed in-place mutation
// ============================================================

#set document(title: "Fusing Quantitative Type Theory and Aeneas")
#set page(
  paper: "a4",
  margin: (x: 2.4cm, top: 2.4cm, bottom: 2.6cm),
  numbering: "1",
  number-align: center,
)
#set text(font: "New Computer Modern", size: 10.5pt, lang: "en")
#set par(justify: true, leading: 0.62em, spacing: 0.9em)
#show heading: set text(weight: "bold")
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => block(above: 1.3em, below: 0.7em, it)
#show heading.where(level: 2): it => block(above: 1.0em, below: 0.5em, it)

// ---- math / symbol conventions ----
#show math.equation: set text(font: "New Computer Modern Math")

// ---- raw code styling ----
#show raw: set text(font: ("DejaVu Sans Mono", "New Computer Modern Math", "Libertinus Serif"))
#show raw.where(block: false): set text(size: 9.2pt)
#show raw.where(block: true): it => block(
  fill: luma(248),
  inset: 8pt,
  radius: 3pt,
  width: 100%,
  stroke: 0.4pt + luma(220),
  text(size: 8pt, it),
)

// ---- figure helpers (uniform supplements) ----
#let fig(body, cap) = figure(body, caption: cap, kind: image, supplement: [Figure])
#let lst(body, cap) = figure(body, caption: cap, kind: raw, supplement: [Listing])
#show figure.caption: set text(size: 9pt)
#set figure(gap: 0.7em)

// ---- inference-rule macro ----
#let rname(n) = text(size: 0.8em)[#smallcaps(n)]
#let rule(name, prem, conc) = box(grid(
  columns: (auto, auto),
  column-gutter: 0.7em,
  align: horizon,
  box(stack(dir: ttb, spacing: 5pt, align(center, prem), line(length: 100%, stroke: 0.55pt), align(center, conc))),
  rname(name),
))

// ---- diagram primitives ----
#let dblue = rgb("#2F6Fb0")
#let dcoral = rgb("#cf5a33")
#let dgray = rgb("#6b7280")
#let dink = rgb("#1f2937")
#let dnode(dx, dy, w, h, sc, fc, title, sub) = place(top + left, dx: dx, dy: dy, box(
  width: w,
  height: h,
  radius: 4pt,
  fill: fc,
  stroke: 0.9pt + sc,
  inset: 4pt,
  align(center + horizon, stack(dir: ttb, spacing: 2.5pt, text(9pt, fill: dink, weight: "medium", title), text(
    8.5pt,
    fill: sc.darken(8%),
    sub,
  ))),
))
#let dshaft(x1, y1, x2, y2, c) = place(top + left, dx: 0pt, dy: 0pt, line(
  start: (x1, y1),
  end: (x2, y2),
  stroke: 1pt + c,
))
#let dhead(x, y, c) = place(top + left, dx: x - 3.5pt, dy: y - 6pt, polygon(
  fill: c,
  (0pt, 0pt),
  (7pt, 0pt),
  (3.5pt, 6pt),
))

// ============================================================
//  TITLE BLOCK
// ============================================================
#align(center)[
  #block(text(size: 17pt, weight: "bold")[
    Fusing Quantitative Type Theory and Aeneas:\
    A Single Calculus for Dependently-Typed In-Place Mutation
  ])
  #v(2pt)
  #text(size: 11pt)[Charlie Lidbury]
  #v(-2pt)
  #text(size: 9.5pt, style: "italic")[Department of Computing, Imperial College London]
  #v(2pt)
  #text(size: 9pt)[Working note --- design and proof sketch]
]

#v(2pt)
#block(inset: (x: 1.2cm), text(size: 9.7pt)[
  *Abstract.* Quantitative Type Theory (QTT) supports dependent types together with a principled,
  semiring-graded account of erasure; Aeneas reasons about Rust-style mutable borrowing in a
  purely value-based way, translating borrow-manipulating code into pure functional programs without
  any model of memory. We show that the two can be combined into a single language with one syntax and
  one set of typing rules, yielding dependent types over in-place mutation. The key is to recognise that
  the two systems police *orthogonal* axes --- QTT a *multiplicity* (relevance/erasure) axis, Aeneas an
  *ownership* (aliasing) axis --- and to carry, in the type of a mutable borrow, a multiplicity-zero
  *prophecy*: the value the borrow will hold when it ends. Erasure sends the multiplicity-one fragment to
  Aeneas's Low-Level Borrow Calculus and the multiplicity-zero fragment to the pure functional model the
  proof is stated about, so one derivation reads simultaneously as runnable pointer code, a pure model,
  and a machine-checked proof. We illustrate the calculus by sketching a correctness proof of an in-place
  quicksort, and we identify the one genuinely new metatheoretic obligation the fusion introduces ---
  a prophecy-aware substitution principle --- together with the open problems that remain.
])

// ============================================================
= Introduction
// ============================================================

Two recent lines of work each solve half of a problem we should like to solve whole. Quantitative Type
Theory @atkey2018qtt, building on McBride's resource-aware reframing of linear logic @mcbride2016plenty,
equips a dependent type theory with a usage *semiring* $R$ so that every variable carries a multiplicity:
the multiplicity $0$ marks data that may appear in types but must be erased before runtime, giving
dependent types "for free" with respect to compilation. Aeneas @ho2022aeneas takes a different problem ---
verifying imperative, borrow-manipulating Rust --- and dispatches it without ever modelling memory: it gives
a *value-based* semantics in which a mutable borrow is reasoned about through a pair of a *forward* and a
*backward* function, and translates low-level code into pure functional code suitable for an off-the-shelf
proof assistant.

What neither provides is the combination: a *quantitative dependent type theory whose erasure target is a
value-based borrow calculus*, so that one can state and prove dependent functional specifications of code
that mutates in place, and have the proof, the pure model, and the executable pointer program all fall out
of a single typing derivation. Closing that gap is the goal of the Ochre language @lidbury2024ochre, and
this note works out the core of the fusion.

#heading(level: 2, numbering: none, outlined: false)[Contributions]
We (i) isolate the conceptual move that makes a single calculus possible --- separating QTT's multiplicity
axis from Aeneas's ownership axis, and bridging them with a prophecy carried at multiplicity zero
(#ref(<sec:idea>)); (ii) give a combined syntax (#ref(<sec:syntax>)) and the load-bearing typing rules
(#ref(<sec:rules>)), including the borrow-splitting rule where the two systems fuse most visibly;
(iii) explain how the three layers --- runtime data, borrows, and proofs --- coexist and what survives
erasure, and conjecture a denotational model based on lenses (#ref(<sec:erase>)); (iv) sketch a correctness
proof of in-place quicksort, in which the dependent type of a tail-recursive helper *is* the loop invariant
(#ref(<sec:quicksort>)); and (v) identify the single new admissibility obligation the fusion creates and
survey the open problems (#ref(<sec:meta>)).

// ============================================================
= The idea that makes a single calculus possible <sec:idea>
// ============================================================

The temptation, when combining a linear or quantitative discipline with borrowing, is to make "mutable
borrow" *be* the semiring's $1$. It is not, and conflating the two leads to a system that fights its own
rules. The resolution is to stop treating "linearity" as one thing. QTT and Aeneas each police a different
axis, and once separated they compose almost without friction.

- *Multiplicity* (QTT's semiring $R$, with $\{0,1,omega\}$ the running instance) controls
  _relevance_: how many runtime copies a variable contributes, with $0$ meaning "erased but usable in
  types". This is the erasure axis.

- *Ownership mode* (Aeneas) controls _aliasing_: owned versus unique-view ($#"&mut"$) versus shared-view
  ($#"&"$), forbidding two live $#"&mut"$ to the same place. This is the aliasing axis.

These are orthogonal. QTT multiplicity counts *syntactic occurrences*: a borrow read five times and
written three times "occurs eight times". Uniqueness of a mutable borrow, by contrast, is a non-aliasing
property with nothing to do with occurrence count. The two coincide only under a *value-threading*
presentation --- exactly the one Aeneas already uses, where the environment is rebound, $Omega[x ↦ v']$,
on every mutation. If each mutation _consumes the borrow handle and produces a fresh one_, the handle
genuinely occurs once between mutations, hence is multiplicity-$1$; and the "no second $#"&mut"$" invariant
is enforced *separately* by the borrow-introduction rule (Aeneas's prohibition on borrowing an
already-loaned place), not by the semiring. Keep the two axes apart and the system stays sound; merge them
and it does not.

The second ingredient is a *bridge term*. To state a dependent post-condition about an in-place mutation
one must be able to *name the value the borrow will hold when it ends*. That object already has three names
in the literature, and they denote the same device: RustHorn's *prophecy variable*, representing a pointer
as the pair of its current target value and its target value at the end of the borrow @matsushita2020rusthorn;
Aeneas's *backward-function input* @ho2022aeneas; and RefinedRust's *borrow names*, where a mutable
reference carries both its current value and a name communicating its final value @gaeher2024refinedrust.
The fused mutable-borrow type therefore carries *two* type-level (multiplicity-$0$) terms: the current
contents and the prophesied final contents. QTT supplies the erasure that makes both cost nothing at
runtime; Aeneas supplies the operational meaning of "resolve the prophecy" (run the backward function); the
dependent layer states the relation between them.

A word on novelty, to frame the contribution honestly. Prophecy-in-the-borrow-type is *established*:
RustHorn, RefinedRust, and most recently Thrust --- a dependent refinement type system that incorporates
prophecy and obtains strong updates through Rust's "aliasing XOR mutability" guarantee
@ogawa2025thrust --- all do it. What has *not* been done is folding it into a full *quantitative dependent
type theory* (universes, $Pi$/$Sigma$, erasure-as-quantity in the QTT/GrTT sense @moon2021grtt) whose
operational and erasure target is Aeneas's value-based Low-Level Borrow Calculus (LLBC). RefinedRust and
Thrust are refinement layers over base types, backed respectively by the Iris separation logic and by
Constrained Horn Clause solving; here we want the borrows *and* the proofs to live in one core whose erasure
*is* the Aeneas functional translation. That gap is what the calculus below targets.

// ============================================================
= Combined syntax <sec:syntax>
// ============================================================

We resolve the notation clash up front. Multiplicities are $rho, pi in R$, a positive semiring with the
zero-product property; output usage is $sigma in \{0,1\}$ (Atkey's restriction, retained --- see
#ref(<sec:meta>)); regions/lifetimes are $alpha, beta, gamma$. We write the prophecy pairing as
$⟨a ⇝ a'⟩$, read "current $a$, prophesied-final $a'$". #ref(<fig:syntax>) gives the grammar.

#let ann(t) = text(8.5pt, fill: rgb("#5b6470"))[#t]
#fig(
  grid(
    columns: (auto, auto, auto, 1fr),
    column-gutter: (0.45em, 0.7em, 1.4em),
    row-gutter: 0.5em,
    align: (right + horizon, center + horizon, left + horizon, left + horizon),

    $A, B$, $::=$, $(x :^(rho sigma) A) -> B$, ann[dependent function; $rho$ = arg. multiplicity],
    [], $|$, $(x :^(rho sigma) A) ⊗ B$, ann[dependent tensor --- the thing that splits borrows],
    [], $|$, $"Set" mid(|) "El" med M mid(|) a =_A b$, ann[universe, decoding, identity (proofs live here)],
    [], $|$, $"Nat" mid(|) "Bool" mid(|) "Fin" med M mid(|) "Array" med M med A$, [],
    [], $|$, $#"&"^m ⟨alpha⟩ A ⟨a ⇝ a'⟩$, ann[mutable borrow in region $alpha$; current $a$, prophecy $a'$],
    [], $|$, $#"&"^s ⟨alpha⟩ A ⟨a⟩$, ann[shared borrow; current $a$ (final $equiv$ current)],
    [],
    $|$,
    $"Perm" med dot.c med dot.c mid(|) "Sorted" med dot.c mid(|) dots.h$,
    ann[spec predicates (ordinary inductive types)],

    grid.cell(colspan: 4, v(3pt)),

    $M, N$,
    $::=$,
    $x mid(|) lambda mid(|) "App" mid(|) (M,N) mid(|) "let" mid(|) "elim"_(B,N,F) mid(|) "code"_("Set")$,
    ann[QTT core],
    [], $|$, $#"&mut" med p mid(|) #"&shr" med p$, ann[take a borrow of a place $p$],
    [],
    $|$,
    $"idx" med i med s mid(|) "set" med i med a med s mid(|) "swap" med a med b med s mid(|) "split" med k med s$,
    ann[borrow / array operations],
    [], $|$, $f med ⟨alpha⟩ med M dots.h$, ann[call with regions instantiated],

    grid.cell(colspan: 4, v(3pt)),

    $Gamma$,
    $::=$,
    $⋄ mid(|) Gamma, x :^(rho sigma) A mid(|) Gamma, alpha$,
    ann[variables with multiplicity; region binders],
  ),
  [Combined syntax. The annotation $:^(rho sigma)$ records argument multiplicity $rho$ and output usage $sigma$; the two borrow types are the only addition to a QTT core.],
) <fig:syntax>

Two structural points carry over from QTT untouched. First, types are still formed in a *zeroed* context
$0 Gamma$, so the terms $a, a'$ appearing inside a borrow type are contemplative, multiplicity-$0$
occurrences --- exactly QTT's "variables in types for free". Second, context scaling $pi Gamma$ and
addition $Gamma_1 + Gamma_2$ behave as in Atkey. Crucially, one does *not* need a separate stateful context
for the borrow's current value: mutation rebinds the handle linearly, so the "state" lives in the handle's
type index and is threaded purely.

// ============================================================
= Combined typing rules <sec:rules>
// ============================================================

The judgement form is $Gamma tack.r M :^(rho sigma) A$ as in QTT. We give only the load-bearing rules; the
QTT core (variable, conversion, $Pi$, $lambda$, application, $⊗$, $"Bool"$, $"Set"$) is inherited verbatim,
with application generalised below for the borrow case.

*Taking a mutable borrow* consumes an owned place at multiplicity $1$ and mints a fresh region together with
a fresh prophecy at multiplicity $0$:

#v(2pt)
#align(center, rule(
  "Mut-Borrow",
  $Gamma tack.r p :^1 A wide alpha "fresh" wide a' :^0 A "fresh prophecy"$,
  $Gamma ∖ p, alpha tack.r #"&mut" med p :^1 #"&"^m ⟨alpha⟩ A ⟨floor(p) ⇝ a'⟩ quad "and" p "is loaned-in-"alpha$,
))
#v(2pt)

The side-condition "$p$ loaned-in-$alpha$" (i.e. $p$ is inaccessible until $alpha$ closes) is precisely
Aeneas's mutable-borrow precondition; that is where uniqueness is enforced, *not* in the semiring.

*An in-place write* consumes the handle and produces a fresh one whose *current* index is updated; the
prophecy is untouched, since it is the value at end-of-borrow, not now:

#v(2pt)
#align(center, rule(
  "Set",
  $Gamma tack.r s :^1 #"&"^m ⟨alpha⟩ ("Array" med n med A) ⟨v ⇝ f⟩ wide i :^0 "Fin" med n wide Gamma' tack.r a :^(rho sigma) A$,
  $Gamma + Gamma' tack.r "set" med i med a med s :^1 #"&"^m ⟨alpha⟩ ("Array" med n med A) ⟨ v[i ↦ a] ⇝ f ⟩$,
))
#v(2pt)

This linear consume-and-rebind is exactly Aeneas's value update $Omega[x ↦ v']$, and it is why the handle is
occurrence-$1$ even though the borrow is written many times. The swap $"swap" med a med b med s$ is
derivable; and reading, $"idx" med i med s : (A ⊗ #"&"^m ⟨alpha⟩ dots.h ⟨v ⇝ f⟩)$, returns the element *and
gives the handle back*, modelling the instantaneous shared reborrow $#"&" * s$, copy out, drop (free for a
machine integer).

*Splitting a borrow* is the crux of in-place divide-and-conquer, and the point at which the two systems fuse
most visibly:

#v(2pt)
#align(center, text(9.4pt, rule(
  "Split",
  $Gamma tack.r s :^1 #"&"^m ⟨alpha⟩ ("Array" med n med A) ⟨v ⇝ f⟩ wide k :^0 "Fin"(n+1) wide f_l, f_r "fresh"$,
  $Gamma tack.r "split" med k med s :^1 (s_l : #"&"^m ⟨alpha⟩ ("Array" med k med A) ⟨"take" med k med v ⇝ f_l⟩) ⊗ \ (s_r : #"&"^m ⟨alpha⟩ ("Array"(n-k) med A) ⟨"drop" med k med v ⇝ f_r⟩)$,
)))
#v(2pt)
#align(center, text(9.5pt)[with the multiplicity-$0$ prophecy law $quad f equiv "append" med f_l med f_r$.])
#v(2pt)

That law $f equiv "append" med f_l med f_r$ is the type-level image of Aeneas's region projection together
with *backward-function composition*: the whole's final value is the append of the parts' finals. Both
sub-borrows live in the *same* region $alpha$, and the index arithmetic $n = k + (n - k)$ is plain
type-level $"Nat"$ at multiplicity $0$ --- QTT's contribution, and what makes length preservation fall out
for free, the prophecies $f_l, f_r$ carrying the indices $k$ and $n - k$. The $⊗$ is genuine: eliminating the
pair forces *both* halves to be used linearly, which is exactly what forces both halves to be processed and
recombined.

*Closing a region* resolves the prophecy and returns ownership:

#v(2pt)
#align(center, rule(
  "End-Mut",
  $Gamma tack.r s :^1 #"&"^m ⟨alpha⟩ A ⟨v ⇝ f⟩ wide alpha "closing, no other live borrows in" alpha$,
  $f := v quad "(prophecy resolves definitionally)" semi quad "place restored with value" v semi quad s ↦ bot$,
))
#v(2pt)

This is Aeneas's region-end and RustHorn's resolution $a^circle.small = a$ at once: at the instant the
borrow ends, "final $equiv$ current" becomes true. Operationally it *is* running the backward function with
the now-known final value.

*Calling an opaque function* with a mutable-borrow argument is where modularity lives. Let
$f : dots.h → (s :^1 #"&"^m ⟨alpha⟩ A ⟨a ⇝ a'⟩) → (r :^1 R) ⊗^0 "Post"(a, a', r)$ be its signature.

#v(2pt)
#align(center, text(9.4pt, rule(
  "App-Mut",
  $f : dots.h → (s :^1 #"&"^m ⟨alpha⟩ A ⟨a ⇝ a'⟩) → (r :^1 R) ⊗^0 "Post"(a,a',r) wide Gamma tack.r s :^1 #"&"^m ⟨alpha⟩ A ⟨v ⇝ f_0⟩$,
  $Gamma tack.r f ⟨alpha⟩ dots.h med s :^1 (r : R) ⊗^0 "Post"(v, a', r) wide [ med s ↦ ⟨a' ⇝ f_0⟩ med ]$,
)))
#v(2pt)

The caller never sees $f$'s body, only that $f$'s prophecy $a'$ --- the borrow's value once $f$'s reborrow
ends, i.e. immediately after the call, since $r$ is not a borrow --- satisfies $"Post"$. In
functional-translation terms $r = f_"fwd" dots.h$ and $a' = f_("back",alpha) dots.h$, with $"Post"$ the
spec lemma about $f_("back",alpha)$. Dually, a *leaf* function that fully determines its mutations does not
invoke this opacity on its own body: it pins its prophecy at #rname("End-Mut")/return and proves $"Post"$
about the concrete final value.

// ============================================================
= Erasure and the coexistence of three layers <sec:erase>
// ============================================================

QTT's restriction $sigma in \{0,1\}$ splits every judgement into a *present* half and an *erased* half.
We place the entire proof apparatus --- $"Perm"$, $"Sorted"$, the prophecy terms $a'$, the index $n$, the
bound lemmas --- in $sigma = 0$. After erasure $abs(dot.c)$, what remains in $sigma = 1$ is this: a mutable
borrow $#"&"^m ⟨alpha⟩ A$ becomes, in a forward function, just $A$ (the current value); region-close becomes
a backward function $A → A$ (Aeneas). Indices and proofs vanish; handle-threading becomes value-passing. So
a well-typed term erases to (a) a memory-safe LLBC program --- Aeneas guarantees the swaps do not alias ---
and (b) its pure functional model in the prover. The punchline is that *the backward function of an in-place
sort is literally the functional sort* $"list" med "i32" → "list" med "i32"$, and the correctness theorem is
a statement about that function. One derivation, three readings: runnable pointer code (QTT erasure), pure
model (Aeneas translation), and machine-checked proof (the $sigma = 0$ layer).

There is a clean semantic story waiting here too, though it is a conjecture rather than a theorem. Atkey
realises QTT terms with realisers over an $R$-linear combinatory algebra and explicitly flags a connection
to Geometry-of-Interaction and *reversible* computation; Aeneas independently observes that its backward
functions are "akin to lenses". A *lens* between sets $S$ and $A$ is simply a pair of functions --- a getter
$"get" : S → A$ and a setter $"put" : S → A → S$ --- satisfying three equations,
$"get"("put" med s med a) = a$, $"put" med s med ("get" med s) = s$, and
$"put"("put" med s med a) med a' = "put" med s med a'$; informally, "the current value, plus how an updated
view flows back". (No category theory is needed to *use* a lens; lens *composition* is just how nested or
split borrows stack.) That is exactly the content of a mutable borrow: $"get"$ reads the current value,
$"put"$ is the backward function. The natural model is therefore a quantitative category-with-families in
which $#"&"^m ⟨alpha⟩ A$ is interpreted by a lens, #rname("Split") by lens composition together with the
$"append"$ law, and #rname("End-Mut") by applying $"put"$ --- with the $"put"$ direction being the reverse
wiring Atkey's realisers already carry. The two papers' loose ends --- his reversibility remark, their lens
remark --- meet at "a quantitative category-with-families of lenses".

// ============================================================
= Case study: proving in-place quicksort <sec:quicksort>
// ============================================================

The specification vocabulary is ordinary $sigma = 0$ inductive data:

#lst(
  ```
  idx    : Array n A → Fin n → A
  Perm   : Array n A → Array n A → Set      -- multiset equality (bijection on Fin n)
  Sorted : Array n A → Set
  Below  : A → Array m A → Set              -- pivot ≥ every element
  Above  : A → Array m A → Set              -- pivot ≤ every element
  ```,
  [Specification predicates. All live at multiplicity $0$ and erase completely.],
)

and two standard lemmas do all the gluing, both erased:

#lst(
  ```
  sortedConcat        : Sorted l → Sorted r → Below piv l → Above piv r
                        → Sorted (l ++ [piv] ++ r)
  permPreservesBelow  : Perm u w → Below piv u → Below piv w     -- (+ the Above twin)
  ```,
  [The two gluing lemmas.],
)

The external view of $"partition"$ exposes only the pivot index $p$ on the result side; everything else is
erased proof:

#lst(
  ```
  partition :
    (n   :⁰ Nat) → (pos :⁰ n ≥ 1) →
    (s   :¹ &ᵐ⟨α⟩ (Array n I32) ⟨xs ⇝ xs'⟩) →
    (p   :¹ Fin n) ⊗⁰
      ( Perm xs xs'
      × Below (idx xs' p) (take (toNat p) xs')
      × Above (idx xs' p) (drop (suc (toNat p)) xs') )
  ```,
  [Signature of $"partition"$. Only $p : "Fin" med n$ survives erasure on the result side.],
)

The body must be *recursive, not a loop* --- and this is a real constraint inherited from Aeneas, not a
stylistic choice: its concrete semantics supports loops, but the *symbolic* semantics that generates the
translation does not, only recursion. The Lomuto loop becomes a tail-recursive helper *whose dependent type
is the loop invariant*. This is the clean dependent-types account of "loop invariant", and it is worth
stating explicitly:

#lst(
  ```
  partGo :
    (n   :⁰ Nat) → (piv :¹ I32) → (i :¹ Fin (suc n)) → (j :¹ Fin (suc n)) →
    (s   :¹ &ᵐ⟨α⟩ (Array n I32) ⟨ys ⇝ ys'⟩) →
    -- Inv ys i j  ≜   Perm xs₀ ys                          (xs₀ = contents at entry)
    --              ∧ (∀ k. k < i        → idx ys k ≤ piv)
    --              ∧ (∀ k. i ≤ k < j    → idx ys k > piv)
    --              ∧ j ≤ n−1            (last slot holds pivot until final swap)
    (p   :¹ Fin n) ⊗⁰ Post(…)
  ```,
  [The Lomuto helper. Its dependent type is exactly the loop invariant.],
)

Each step is a linear $"swap"$/$"set"$ that updates $"ys"$ (current) and re-establishes $"Inv"$: if
$"idx" med j med s ≤ "piv"$, perform $"swap" med i med j med s$ and bump $i$ (the "$≤ "piv"$" prefix grows);
if $> "piv"$, leave $s$ and bump $j$; when $j$ reaches $n - 1$, $"swap" med i med (n-1) med s$ places the
pivot and the helper returns $p := i$. At that return the prophecy $"ys"'$ is *pinned* --- $"partGo"$ fully
determines its final array --- so $"Post"$ is provable about a concrete value. Termination: $n - 1 - j$
strictly decreases; it is $sigma = 0$, erased, and Aeneas emits a `decreases` clause.

The whole-slice prophecy decomposes into the two sub-slice prophecies plus the fixed pivot, and that
decomposition *is* the backward-function composition (#ref(<fig:rec>)).

#fig(
  box(width: 360pt, height: 250pt, {
    dshaft(190pt, 40pt, 190pt, 57pt, dblue)
    dshaft(190pt, 92pt, 190pt, 104pt, dblue)
    dshaft(80pt, 104pt, 300pt, 104pt, dblue)
    dshaft(80pt, 104pt, 80pt, 119pt, dblue)
    dshaft(190pt, 104pt, 190pt, 119pt, dblue)
    dshaft(300pt, 104pt, 300pt, 119pt, dblue)
    dhead(190pt, 57pt, dblue)
    dhead(80pt, 119pt, dblue)
    dhead(190pt, 119pt, dblue)
    dhead(300pt, 119pt, dblue)
    dshaft(80pt, 154pt, 80pt, 170pt, dcoral)
    dshaft(300pt, 154pt, 300pt, 170pt, dcoral)
    dshaft(190pt, 154pt, 190pt, 170pt, dcoral)
    dshaft(80pt, 170pt, 300pt, 170pt, dcoral)
    dshaft(190pt, 170pt, 190pt, 184pt, dcoral)
    dhead(190pt, 184pt, dcoral)
    dnode(120pt, 6pt, 140pt, 34pt, dblue, dblue.lighten(88%), [quicksort #raw("s")], [#raw("⟨xs ⇝ xs'⟩")])
    dnode(70pt, 58pt, 240pt, 34pt, dgray, dgray.lighten(90%), [partition in place], [returns pivot index #raw("p")])
    dnode(20pt, 120pt, 120pt, 34pt, dblue, dblue.lighten(88%), [quicksort #raw("left")], [#raw("⟨l ⇝ l'⟩")])
    dnode(150pt, 120pt, 80pt, 34pt, dgray, dgray.lighten(90%), [pivot], [fixed])
    dnode(240pt, 120pt, 120pt, 34pt, dblue, dblue.lighten(88%), [quicksort #raw("right")], [#raw("⟨r ⇝ r'⟩")])
    dnode(70pt, 184pt, 240pt, 38pt, dcoral, dcoral.lighten(90%), [on return (split law)], [#raw(
      "xs' = l' ++ [piv] ++ r'",
    )])
    place(top + left, dx: 40pt, dy: 232pt, line(start: (0pt, 0pt), end: (16pt, 0pt), stroke: 1pt + dblue))
    place(top + left, dx: 60pt, dy: 226pt, text(8pt, fill: dink)[forward: recurse])
    place(top + left, dx: 175pt, dy: 232pt, line(start: (0pt, 0pt), end: (16pt, 0pt), stroke: 1pt + dcoral))
    place(top + left, dx: 195pt, dy: 226pt, text(8pt, fill: dink)[backward: prophecy resolves])
  }),
  [Quicksort recursion. Forward calls (blue) descend: `quicksort` calls `partition`, then splits the slice into a left flank, a fixed pivot, and a right flank, and recurses on the flanks. Backward prophecy composition (coral) reassembles the final slice as `l' ++ [piv] ++ r'` via the #smallcaps("Split") laws.],
) <fig:rec>

The term realising this picture threads one mutable borrow through $"partition"$, peels the pivot with two
$"split"$s, and recurses on the two flanks. Every line is an instance of one of the rules of
#ref(<sec:rules>).

#lst(
  ```
  quicksort :
    (n :⁰ Nat) →
    (s :¹ &ᵐ⟨α⟩ (Array n I32) ⟨xs ⇝ xs_f⟩) →
    (⋆ :¹ I) ⊗⁰ (Perm xs xs_f × Sorted xs_f)

  quicksort n s = case n of
    0     → (⋆, (Perm-refl, Sorted-nil))      -- End-Mut later pins  xs_f := xs
    suc 0 → (⋆, (Perm-refl, Sorted-single))   -- already sorted; no write happens
    _     →                                   -- n ≥ 2
      -- App-Mut advances s to ⟨m ⇝ xs_f⟩;   piv ≜ idx m p
      let (p, (πpart, blo, abv)) = partition n (≥1 n) s
          (sl,   s≥)       = split (toNat p) s    -- law:  xs_f ≡ append fl f≥
          (spiv, sr)       = split 1 s≥           -- law:  f≥ ≡ append fpiv fr
          (⋆, (πl, sortl)) = quicksort (toNat p)        sl    -- advances sl  ⟨_ ⇝ fl⟩
          (⋆, (πr, sortr)) = quicksort (n − toNat p − 1) sr   -- advances sr  ⟨_ ⇝ fr⟩
      in (⋆, (perm, sorted))
    where
      -- when α closes:  fpiv := [piv]  (length-1, never written), hence
      --     xs_f  ≡  fl ++ [piv] ++ fr
      blo'   : Below piv fl = permPreservesBelow πl blo    -- piv ≥ all of fl
      abv'   : Above piv fr = permPreservesAbove πr abv    -- piv ≤ all of fr
      sorted : Sorted xs_f  = sortedConcat sortl sortr blo' abv'
      perm   : Perm xs xs_f = Perm-trans πpart (Perm-cong-around piv πl πr)
               --  Perm xs m  from partition, then  Perm m xs_f  since
               --     m ≡ take p m ++ [piv] ++ drop (p+1) m   and the flanks permute
  ```,
  [In-place quicksort. The runtime content is `partition` plus two recursive calls on disjoint sub-slices; the prophecy terms and all five proofs erase.],
) <lst:quicksort>

#v(-2pt)
The detailed gluing facts named in the `where` block above are exactly the two lemmas of #ref(<sec:quicksort>):
$"sortedConcat"$ builds $"Sorted" med "xs"_f$ from the two sorted flanks and the pivot bounds, while
$"permPreservesBelow"$/$"permPreservesAbove"$ transport the partition's bounds across each recursive
permutation.

Three features of this body are worth saying out loud, because they are where the fusion does real work
rather than merely type-checking.

*The entire correctness proof is built against the prophecy variable $"xs"_f$, before $"xs"_f$ has a value.*
Nothing in the `where` block knows the final array; it knows only relational $sigma = 0$ facts about it ---
$"xs"_f equiv f_l #raw("++") [#raw("piv")] #raw("++") f_r$ from the two #rname("Split") laws, $"Sorted" med f_l$ and
$"Sorted" med f_r$ from the recursive calls, and the $"Below"$/$"Above"$ bounds from $"partition"$
transported across the recursion by $"permPreservesBelow"$. $"sortedConcat"$ assembles $"Sorted" med "xs"_f$
out of those. The concrete value of $"xs"_f$ only materialises later, at the outermost #rname("End-Mut"),
when region $alpha$ closes; at that instant every fact pinned during the recursion becomes a fact about the
now-known array, and reasoning ahead of time was sound precisely because prophecy resolution is consistent.
This is the RustHorn move, but here it happens *inside* a dependent proof rather than inside an SMT encoding:
the prophecy is a $sigma = 0$ term and the facts about it are $sigma = 0$ proofs.

*Both `partition` and the recursive `quicksort` calls are opaque*, via #rname("App-Mut"). The caller of
$"partition"$ never sees its body; it sees only that the borrow's current value advanced from $"xs"$ to the
prophecy $m$ and that the post-condition holds. The recursive calls advance $"sl"$ and $"sr"$ from their
current values to $f_l$ and $f_r$ the same way. The proof is thus genuinely modular: $"partition"$'s
in-place Lomuto loop is verified once, through $"partGo"$, and consumed only through its signature.

*Length preservation is free.* The indices $n = "toNat" med p + 1 + (n - "toNat" med p - 1)$ are type-level
$"Nat"$ at multiplicity $0$, so $"sl" : "Array"("toNat" med p)$ and
$"sr" : "Array"(n - "toNat" med p - 1)$ are forced by typing; the prophecies $f_l, f_r$ inherit exactly
those lengths, and $"xs"_f$'s length is fixed before any value is. This is the QTT contribution: the same
erased-index machinery that makes the array/$"Fin" med n$ example efficient makes "the sort returns an array
of the same length" a typing fact rather than a lemma.

// ============================================================
= Metatheory and open problems <sec:meta>
// ============================================================

Most of the metatheory is inherited. The fusion introduces *exactly one* genuinely new admissibility
obligation, and then a cluster of limitations that are real and should be stated plainly rather than papered
over.

*The one new obligation: prophecy-aware substitution.* QTT's reason for restricting the output usage to
$sigma in \{0,1\}$ is that substitution is otherwise inadmissible --- one cannot in general split an
$O^(rho_1 + rho_2)$ back into $O^(rho_1)$ and $O^(rho_2)$ at an application. The combined system has a
structurally identical hazard, but the dangerous object is the prophecy rather than the multiplicity. A
prophecy $a'$ is a $sigma = 0$ term naming a value that does not exist yet; the fact $f := v$ produced by
#rname("End-Mut") is only sound *at the region boundary*. If substitution could move a prophecy resolution
across an open region's boundary, one would be asserting a $sigma = 0$ equation about a final value in a
context where that value is not yet pinned --- the same flavour of unsoundness in a new guise. The
discipline that rescues it is the obvious one once seen: prophecies are born exactly at #rname("Mut-Borrow"),
resolved exactly at #rname("End-Mut"), and regions are well-nested (a stack). The metatheorem to prove is
then "substitution is admissible provided no substituted prophecy crosses an open region boundary" --- one
may freely substitute *current* values, never *across* a live region. This is the structural twin of Atkey's
$\{0,1\}$ restriction, and it is no coincidence that it coincides with what RustHornBelt must establish in
its soundness proof: the existence of an acyclic relation among borrows summarising their dependencies
@matsushita2022rusthornbelt. Well-nesting of regions *is* that acyclicity, surfaced as a syntactic
discipline.

*Erasure soundness.* There are two erasures and they must commute: $abs(dot.c)$ to the $sigma = 1$ fragment
lands in LLBC (Aeneas's source), and Aeneas's functional translation then produces the pure model. The
theorem to want is that a well-typed combined term erases to a well-typed LLBC program whose Aeneas
backward-function translation *equals* the $sigma = 0$ functional model the proof talks about. One would not
reprove memory safety --- the $sigma = 1$ image is already an Aeneas-checked program --- but rather that the
$sigma = 0$ prophecy layer is a sound refinement of LLBC's backward functions. The strategy is RustHornBelt's:
it is the first machine-checked soundness proof for RustHorn-style prophecy verification, achieved through a
separation-logic mechanism it calls parametric prophecies @matsushita2022rusthornbelt, and that soundness
statement --- prophecy resolution is sound against a memory semantics, under the acyclicity condition --- is
exactly what licenses our $f := v$ against Aeneas's value-based region-end.

*The realisability model is a target, not a result.* The "quantitative category-with-families of lenses"
story of #ref(<sec:erase>) is a conjecture. The honest obstruction is one Atkey flags himself: the
Boolean/coproduct structure breaks the reversibility of his realisers. #rname("Split") and region-merge are
coproduct-flavoured operations, so the lens model must absorb exactly the non-reversible part, which is
where the hard semantic work concentrates.

*Loops, and the join problem.* One inherits Aeneas's restriction directly: its concrete semantics has loops,
but the symbolic semantics that drives the translation supports only recursion. The dependent-types payoff
is real --- the loop invariant *is* the dependent type of the tail-recursive helper, as in $"partGo"$ ---
but admitting *surface* loops means solving Aeneas's deferred difficulty, the join/merge problem (it
currently forces every disjunction into terminal position by duplicating continuations). In the dependent
setting the join is strictly harder, because the merge point must unify *prophecy terms and indices*, not
just borrow shapes. The encouraging counterpoint is Thrust: its CHC-based inference synthesises inductive
invariants for loops and recursive functions @ogawa2025thrust, suggesting the loop-invariant synthesis is
automatable for the refinement fragment even where it is not for the full dependent fragment.

*Inherited LLBC signature restrictions.* Because the erasure target is LLBC, four restrictions carry over
verbatim: no nested borrows in signatures, no borrows in type declarations, terminal-position disjunctions
only, and no instantiating a polymorphic function at a borrow-containing type. The second --- no borrows in
type declarations --- bites Ochre's ambitions hardest, because it directly bounds how far the dependent layer
may index types by *borrowed* data. This is a genuine design tension, not merely an engineering gap.

*A decidability fork worth designing around.* The $sigma = 0$ layer here is full dependent type theory, so
$"Perm"$/$"Sorted"$ proofs are ordinary dependent proofs --- undecidable in general, which is fine for a
proof-assistant-backed language where one discharges them interactively, exactly as Aeneas does its proofs
extrinsically in F#super[$star$] or Coq. But Thrust marks the other end of the axis: by folding prophecy into
a refinement type system, strong updates ride on Rust's "aliasing XOR mutability" guarantee, update
information is propagated back to the owner when a mutable borrow is released, and the obligations are emitted
as CHC constraints in SMT-LIB format @ogawa2025thrust. That is a push-button, invariant-inferring discipline
bought at the cost of expressiveness (one cannot state $"Sorted"$ as a rich inductive; it must be encoded as
refinements). The clean design for Ochre is to make this a *mode* rather than a fork: one multiplicity-$0$
fragment with a dependent mode (expressive, interactive) and a refinement mode (restricted, automated,
CHC-shaped) --- the Thrust-versus-Aeneas axis, unified under the single $sigma = 0$ layer.

*The concrete payoff that pays for all of this: bounds-check erasure.* Because indices live at multiplicity
$0$ and $"Fin" med n$ carries its bound as an erased proof, a $"set" med i med a med s$ with
$i : "Fin" med n$ discharges its bounds obligation at type-checking time and erases to an *unchecked* store.
This is the in-place-mutation generalisation of the very example that motivates QTT in the first place, and
it is the same thing RefinedRust achieves by linking the value of a mutable reference to the value of its
owner through borrow names, verifying unsafe pointer-manipulating code foundationally in Coq
@gaeher2024refinedrust. One obtains proof-carrying elimination of runtime checks, now extended past reads to
in-place writes --- the feature that justifies carrying the dependent layer at all.

// ============================================================
= Related work <sec:related>
// ============================================================

The prophecy device originates with RustHorn @matsushita2020rusthorn, which encodes a mutable borrow as a
pair of its current value and a prophesied final value to obtain CHC-based functional verification of safe
Rust; RustHornBelt @matsushita2022rusthornbelt gives the first machine-checked soundness proof for that
style, extending RustBelt @jung2018rustbelt with parametric prophecies in Iris. RefinedRust
@gaeher2024refinedrust and RefinedC @sammler2021refinedc are foundational refinement-and-ownership type
systems in Coq/Iris; RefinedRust's "borrow names" are the prophecy under another name. Thrust
@ogawa2025thrust is the closest prior art on the type-theoretic side: a *dependent refinement* type system
for Rust that incorporates prophecy and obtains strong updates from aliasing-XOR-mutability, with CHC-based
inference. Our calculus differs from all of these in target and ambition: rather than a refinement layer over
base types backed by a separate logic or solver, it is a *quantitative dependent* core in the QTT
@atkey2018qtt / graded-modal @moon2021grtt / McBride @mcbride2016plenty lineage, whose borrows and proofs
share one language and whose erasure *is* the Aeneas @ho2022aeneas value-based functional translation.

// ============================================================
= Conclusion
// ============================================================

Separating QTT's multiplicity axis from Aeneas's ownership axis, and bridging them with a multiplicity-zero
prophecy carried in the borrow type, yields a single calculus in which dependent specifications of in-place
mutation can be stated and proved, with the proof, the pure model, and the executable program all extracted
from one derivation. The quicksort case study shows the mechanism end to end, including the reading of a loop
invariant as the dependent type of a tail-recursive helper. The fusion is not free of obligations --- it
demands a prophecy-aware substitution principle, and it inherits Aeneas's loop and signature restrictions ---
but the obligations are circumscribed and, in the substitution case, structurally familiar from QTT itself.

This calculus fuses *two* of Ochre's three axes: QTT's multiplicity/erasure and Aeneas's ownership. The
third, structural subtyping, is untouched here, and is the natural next fusion. It will interact with
#rname("Split")/region-projection specifically --- subtyping on the *parts* of a split borrow, and how a
subtype coercion commutes with the $"append"$ prophecy law --- which is where we would look first when
folding the subtyping half back in.

#v(1em)
#bibliography("refs.bib", title: [References], style: "association-for-computing-machinery")
