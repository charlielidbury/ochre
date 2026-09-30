#import "../style.typ": *

// Numbered statements, as in the paper's §7.
#let thm(kind, name, body) = figure(kind: "ochr-thm", supplement: kind, numbering: "1", caption: name, body)
#show figure.where(kind: "ochr-thm"): it => block(width: 100%, above: 0.9em, below: 0.9em, breakable: true, align(left)[
  *#it.supplement #context it.counter.display(it.numbering) (#it.caption.body).* #it.body
])
#let proof(body) = block(width: 100%, above: 0.6em, below: 0.9em, [_Proof._ #body #h(1fr) $square$])
#let ev = math.scripts(sym.arrow.b.double)
#let agr(a) = $attach(approx, br: #a)$
#let res = $rho$
#let ok(x) = $tack.double #x$

== Soundness of a typed fragment, conditional on naturality and transfer <sec-tf>

This section reduces soundness of a fragment F to an assumption that the two evaluation paths simulate each other. F has natural numbers, `Unit`, the propositions `True`, `False` and `And`, `Eq` and `Id`, first-order top-level functions with borrow parameters (some of which return a borrow), [Close], and [Split] with refinement and generalisation. For F we prove that, if the assumption holds, two things are true of every accepted program:
- every data function runs without error at every concrete input;
- every lemma is true at every concrete input at which its hypotheses are true.

Consistency of F and adequacy of `Id` follow (@tf-cor-cons, @tf-cor-adeq).

The assumption, naturality (@tf-ass-n), says one step at a time that a symbolic run and the ground run agree once every borrow is ended. It carries most of the operational content. It holds only because of the [Drop] rule's treatment of lent places (@tf-drop). A second assumption (@tf-ass-t) transfers two mechanised lemmas from the earlier rule set to the current rules. Everything else is proved here, and each mechanised lemma is named where it is used (@tf-anchors).

=== The fragment F <tf-frag>

F is the calculus of the appendix restricted as follows. Each restriction says why; @tf-remains lists where each is used.

+ *Data.* The only inductive declarations are the library's `Nat`, `Unit`, `False`, `True` and `And`. Data types are `Nat` and `Unit`; borrow types are `&Nat` and `&Unit`. There are no pairs and no user inductives. _Why:_ ground values are then numerals and `()`.
+ *First order, with bodies.*
  - Programs are sequences of top-level definitions with bodies, $kw("def") f (x_1 : A_1 dots x_n : A_n) : B space [kw("by") x_j] := b$, where $n >= 0$ and $n = 0$ is a constant. There are no opaque definitions, since an opaque lemma is an axiom.
  - Each $A_i$ is a data type, a borrow type or a proposition. `B` is a data type, a borrow type (and then some $A_i$ is one) or a proposition.
  - There are no `fix` or `λ` inside bodies, no Π-types as values, no function parameters (so no abstract functions), no universes other than as the sorts of these types, no parameters of sort `Prop`, no type families and no Prop-valued functions.
  - A definition mentions itself only as the head of a call in its body, never in a type: not in its parameter types or codomain, and not in an annotation, `Eq` or `Id` inside its body.
  - A definition is a _data function_ if `B` is data or a borrow type, and a _lemma_ if `B` is a proposition.

  _Why:_ conversion on data is then syntactic (@tf-lem-conv), the type of every sealed program is a closed data type (@tf-gen), and every call inside a type is to an earlier definition.
+ *Propositions.* $P ::= ty("True") | ty("False") | P and Q | ty("Eq") D thin a thin b | ty("Id") D thin t thin u$, with $D in {ty("Nat"), ty("Unit")}$. The terms `a`, `b`, `t`, `u` inside a type contain no `match`. _Why:_ a match inside a type that gets stuck is closed off as a stuck block, which F leaves out. It also means the typed run of a statement reaches every place occurrence in it (@tf-lem-w).
+ *No stuck blocks.* A `match` on data occurs only in tail position in a definition's body: the body itself, an arm of a match in tail position, or the tail of a `let` or sequence in tail position. It never occurs on the right of a `let`. So [Split] is only [Tail-split] and [Tail-gen]. No stuck block is ever formed, and [Split-gen] and [T-Split-goal] never run.
+ *Proof forms.* Proof terms are:
  - `refl`, $chevron.l h, k chevron.r$, proof variables and their field places, and lemma calls;
  - a `let` or sequence whose tail is a proof;
  - a match on a proof of `And` or `True` (one arm);
  - `match h {}` on a proof of `False`, which occurs only in lemma bodies.

  There is no `J`, `rewrite` or `split`. _Why:_ a data function's run then never depends on the truth of its hypotheses (@tf-thm, part (i)).
+ *No move out through a borrow.* In code that runs, a read of a place under `*` (such as `*x`, or `(*x).1` of a number) is written `clone(…)`. Reading a borrow variable itself, which moves the borrow, is allowed. Reads in types and proofs copy anyway. _Why:_ no borrow ever holds a ghost (@tf-lem-res). Resolution is then defined at every ground state the proof visits, and every call's borrow arguments are whole. It excludes the `mem::replace` pattern `let v = *x; *x := S v`, which must be written with `clone(*x)`.

Moves are otherwise as in the rules (D53): `Nat` is not a copy type, so a runtime read of an owned `Nat` place moves it and leaves a ghost.

The proof uses three properties of the rules, all stated in the appendix:
- *[Drop] of a lent place* (@app-aux). When a dying owned value holds a live loan, a borrower _held in a binding_ (a variable, or a place inside one) is ended, as a write through [Access] would end it. A borrower that is a _value in flight_ (a call argument, the value being assigned, a let-block's or arm's result, or a call's result while its frame pops) makes the drop an error. So a local may die while a variable that borrowed it is never used again, but a block or a function may not return a borrow of its own local.
- *Moved-out places* (@app-machine). A match on a place that holds a ghost is an error at runtime ([Match-err]).
- *[Seal]'s final read* (@app-seal). The final read of a sealed program copies, so a sealed program never moves out through a borrow.

=== Ground instances, truth, resolution and agreement <tf-defs>

#thm([Definition], [ground, valuation], [
  A value is _ground_ if it contains no abstract value, no sealed program and no inert loan; a ground value of type `Nat` is a numeral and one of type `Unit` is `()`. A state is ground if its values are; it may hold live borrows and loans. A _valuation_ α assigns to each abstract value σ in its domain a ground value of type Δ(σ). For a state Ω whose abstract values α covers, $Omega alpha$ is $Omega[alpha(sigma) slash sigma]^+$, substitution followed by normalisation; it is _defined_ when every normalisation it triggers ends without error. α _respects_ the records of the state if $alpha(sigma) = r alpha$ for every refinement $sigma := r$ and $alpha(sigma) = "nf"(n alpha)$ for every generalisation record $n := sigma$.
]) <tf-def-ground>

The _generic state_ of a definition `d` is $Gamma";" phi$, its generic call's environment. Borrow parameters are bound to $"borrow"_(ell_i) sigma_i$, with owned cells $c_i |-> "loan"_(ell_i)$. Data parameters are bound to fresh $sigma_i$, and proof parameters to ⋆ with their types stored.
- A _ground instance_ of `d` is a valuation β of $sigma_1, dots, sigma_n$; its state is $Gamma beta";" phi beta$.
- Its _hypotheses_ are the proof parameters' types, evaluated at the ground instance left to right.
- Its _goal_ is `B` evaluated there, which is the [Call-type] of the call $d(overline(a) beta)$ from a caller whose frame holds the cells.
- A call made at a ground state is _at_ the ground instance whose values are its arguments: a data argument's numeral, and the content of a borrow argument, which is a numeral by @tf-lem-res.

A run is in _runtime mode_ when its reads of non-copy data move, and in _erased mode_ when every read copies (types, proofs, and the sides of `Id`, all on private copies).

#thm([Definition], [truth], [
  At a ground state, `eq` on two numerals computes to `True`, `False` or an `And` of such, and `eq` on `Unit` to `True`. So a proposition value computed at a ground state is built from `True`, `False` and `And` alone. _Truth_ ⊨ is defined on these by $ok(ty("True"))$, $not ok(ty("False"))$, and $ok(P and Q)$ iff $ok(P)$ and $ok(Q)$.
]) <tf-def-truth>

*Resolution.* For a well-formed state Ω, $res(Omega)$ ends every borrow, and $res_Omega (w)$ is the value `w` with each live loan replaced by the resolved content of its borrow, which is well defined by acyclicity.

#thm([Lemma], [resolution], [
  In F no borrow ever holds a ghost. At every well-formed ground state of F, ρ is defined, and it does not depend on the order in which borrows are ended. Ending some borrows first does not change it.
]) <tf-lem-res>
#proof[
  - *No borrow holds a ghost.* A ghost is created only by a runtime read of non-copy data, which leaves `ghost(v)` in the place read. By F6 no such read is under `*`, and a sealed program's final read copies. So a ghost appears only at an owned position or inside one. [Borrow] refuses a place that holds a ghost. So a borrow's content never holds one, and [End]'s wholeness premise always holds.
  - *Order independence.* A ghost holds a loan-free value, because [Access] ends every loan inside a place before it is read. So substitution passes a ghost by, as it passes an abstract value. With each ghost read as an opaque atom, a ground state of F is a state of the mechanised machine. There, order-independence (property 4 of @fig-claims) is mechanised: `end_order_indep` (resolution exists in a well-formed state, and every order of the held borrows reaches it) and `endAll_endSeq` (ending some borrows first does not change it).
  - *What this needs.* Well-formedness of F's states is @tf-ass-t (T1).
  - *Why only ground states.* At a symbolic state, ending a borrow re-normalises the sealed programs it substitutes into, which reading ghosts as atoms does not cover. Every use of ρ at a symbolic state goes through (N3) of @tf-ass-n.
]

#thm([Definition], [agreement], [
  Let $Omega_s$ be a state on the symbolic path, α a valuation that covers and respects it, and $Omega_g$ a ground state with the same frames, bindings and temporaries. $Omega_s agr(alpha) Omega_g$ holds when:
  (A1) $Omega_s alpha$ is defined;
  (A2) $res(Omega_s alpha) = res(Omega_g)$ up to a renaming of loans;
  (A3) every position that holds a borrow in $Omega_s$ holds a borrow in $Omega_g$;
  (A4) at every position that holds $"borrow"_ell$ in $Omega_s$ and $"borrow"_(ell')$ in $Omega_g$, $"owners"_(Omega_g)(ell') subset.eq "owners"_(Omega_s)(ell)$;
  (A5) at every position that holds $"borrow"_ell w_s$ in $Omega_s$ and $"borrow"_(ell') w_g$ in $Omega_g$, $res_(Omega_s alpha)(w_s alpha) = res_(Omega_g)(w_g)$: each live borrow holds the same value once the loans inside it are resolved.
]) <tf-def-agr>

The clauses do the following:
- (A2) is equivalent to "some sequences of [End]s take $Omega_s alpha$ and $Omega_g$ to one state" (@tf-lem-res). The stronger form, equality before resolution, fails: while the mechanisation was built, a counterexample showed that ending a borrow early changes which borrows a later assignment ends, although both states agree after resolution. (A2) survives an [End] on either side, which is how the symbolic path may end a borrow earlier than the ground path (the `Pick` example of @conj-nat).
- (A3) says the symbolic path has ended at least the borrows the ground path has.
- (A4) says its owners over-approximate: a returned borrow's hole sits in the fill of every place it may point into.
- (A5) fixes what each live borrow holds. Without it the relation would admit pairs that resolve alike but in which a borrow points at different parts of its target. For example, symbolically `p` borrows the predecessor field of `x`'s target, and on the ground it borrows the whole target. `match *p` would then take different arms, and a decreasing argument behind `p` would have different sizes.

The consequence the proof uses is this. At agreeing states, a place that is readable on both paths has the same resolved content: by (A2) at an owned position, and by (A5) through a borrow. In particular, after [Access], a scrutinee has the same head constructor on both paths. A loan-free value in flight, such as a call's data argument, is the symbolic value under α. And the content of a borrow argument, which is loan-free (well-formedness condition 5) and whole (@tf-lem-res), is the symbolic content under α.

=== What the proof assumes, and what it cites <tf-anchors>

#thm([Assumption], [naturality, step by step], [
  Let $Omega_s agr(alpha) Omega_g$, and consider one step of a rule of F, in runtime mode or in erased mode, that succeeds from $Omega_s$ on the symbolic path (the typing judgement, in which stuck calls close off).
  (N1) _Primitive steps._ For [Access] ($"acc"^R$ and $"acc"^M$), [Read], [Copy], [Move], [Borrow], [Assign], [Clone], [Ctor], binding a `let` and dropping its binding, dropping a discarded value, pushing a frame of agreeing values, and popping a frame: the same step succeeds from $Omega_g$ in the same mode, and the resulting states, with the step's value as a temporary, agree.
  (N2) _Calls that close off._ At agreeing call points, whose arguments are temporaries of both states, suppose the symbolic call closes off by [Close] and the ground call runs to completion without error. Then the resulting states and results agree.
  (N3) _Resolution commutes with valuation._ $res(Omega_s) alpha = res(Omega_s alpha)$ up to a renaming of loans, including through [Seal]'s re-normalisation of a fill whose hole is inert.
]) <tf-ass-n>

This is naturality in relational form. It is stated per step, so that the proof can use agreement at every call point and every pushed frame.
- A call whose symbolic run returns by [App] ran its body without inspecting an abstract value, so its steps are (N1) steps in the callee's frame. Only a call that closes off needs (N2).
- (N2) assumes only that the ground call it relates is safe. The proof supplies that call by call (@tf-lem-runs), at the arguments the ground run actually passes. By F6 every such call is at a ground instance.
- (N1) and (N2) cover erased mode as well as runtime mode.

The risks we know of are:
- agreement after a [Drop], and the preservation of (A3): early ends are deep, so no reborrow outlives its early-ended borrow on the symbolic path (@tf-drop);
- the preservation of (A5) by [Close]. Under α, a closed-off call's fills place the hole where the ground call's returned borrow points: `close_cur`, `close_back`;
- (N3) through [Seal] with inert loans. The lemma behind it is _hole parametricity_: a fill's run writes its hole and reads its cells, but never inspects the hole.

A proof of @tf-ass-n would go rule by rule and use the mechanised lemmas below.

#thm([Assumption], [transfer from the earlier rule set], [
  (T1) The current rules, restricted to F, preserve well-formedness conditions 1–5, as `exec_wf` proves for the earlier rule set.
  (T2) The frame property holds for F, as `frame_local` and `call_effect` prove for the earlier rule set: a run changes the environment below its own frame only through the loans held by that frame's borrows, and a call's effect is its isolated run, plugged back into the caller.
]) <tf-ass-t>

The mechanised machine has no ghosts, reads by copying, normalises sealed programs only when states are compared, and has a `Unit` row in [Close]. (T1) and (T2) are the two facts about it that this section uses outside @tf-ass-n. Two other mechanised facts are about values, not runs, and they carry over by the argument of @tf-lem-res: a ghost holds no loan, so it is an atom for substitution. These are order-independence (@tf-lem-res) and the injectivity of contexts (`ctx_inj`, @tf-lem-call).

#table(columns: (30%, 1fr, 24%), stroke: none, inset: (x: 4pt, y: 3pt), align: left,
  table.hline(stroke: 0.5pt),
  [*Lean*], [*Statement, for the earlier rule set*], [*Used for*],
  table.hline(stroke: 0.4pt),
  [`end_order_indep`, `endAll_endSeq`], [in a well-formed state resolution exists, every order of the held borrows reaches it, and ending some borrows first does not change it], [@tf-lem-res],
  [`frame_local`, `call_effect`], [the frame property], [@tf-ass-t (T2); @tf-lem-w; @tf-lem-call; the calls of @tf-thm],
  [`ctx_inj`], [a context holding a loan is injective in the loan's final value], [@tf-lem-call],
  [`exec_wf`], [runs of terms that do not name the machine's temporaries preserve well-formedness], [@tf-ass-t (T1)],
  [`endBorrow_nb_lt`], [each [End] removes a borrow, so [Access] and [Drop] end], [@tf-lem-runs (termination)],
  [`close_res`, `close_fin`, `close_cur`, `close_back`], [if a call's isolated run completes, the sealed programs of [Close] normalise to its result, the final contents of its borrowed places, its current content and its backward function. They also need hypotheses on the arguments (loan-free, not moved out, no borrows inside) and on the results (no loans or borrows in the data rows), which follow from well-formedness but are not yet discharged in Lean], [a proof of @tf-ass-n: (A1), (A5) and (N3) at [Close]],
  [`exec_rename`], [the machine commutes with renaming loans], [a proof of @tf-ass-n: (A2)'s renaming],
  table.hline(stroke: 0.5pt),
)

=== Lemmas <tf-lemmas>

#thm([Lemma], [confinement is decided by syntax], [
  For a type term of F evaluated at agreeing states $Omega_s agr(alpha) Omega_g$, its erased-mode run is confined on the symbolic path iff it is confined on the ground path.
]) <tf-lem-conf>
#proof[
  - Confinement judges each step by the root of the place it assigns, borrows or moves: whether that root is a position of the environment the erased term started from.
  - Type terms of F are match-free (F3), so both runs perform the same steps of the term's syntax, on the same places.
  - Steps inside a callee's run are rooted in the callee's own frame, and so are never judged against the outer environment.
  - So the decision is a function of the syntax and of which positions exist, and agreement relates positions of the same binding.
]

#thm([Lemma], [truth and conversion], [
  (a) If $P equiv Q$ are proposition values at a ground state, then $ok(P)$ iff $ok(Q)$. (b) In F, if $v equiv w$ then $v alpha equiv w alpha$ for every valuation α for which both are defined.
]) <tf-lem-conv>
#proof[
  - *Which rules apply.* In F the conversion rules that apply are [Conv-refl], [Conv-cong] and [Conv-unit]. F has no function values and no Π-closures (F2), and its only η is `eq`'s for `Unit`. On data values, [Conv-cong] compares sealed programs by their programs, component by component. So on data, ≡ is equality up to the names of bound variables.
  - *(a).* At a ground state a proposition is built from `True`, `False` and `And` (@tf-def-truth). [Conv-cong] relates `And` to `And` componentwise, and [Conv-unit] removes `True` conjuncts. Both preserve truth, by induction on the derivation of ≡.
  - *(b).* A valuation substitutes and then normalises, rebuilding every `Eq` type with `eq`. It sends equal values to equal values, and the unit laws commute with substitution.
]

#thm([Lemma], [generalisation], [
  Let a node of a [Def] case tree have state $Omega_s$. Let α cover and respect every abstract value of $Omega_s$ except those introduced by the generalisation records made on the path to that node, and let $Omega_s alpha$ be defined once α is extended. Extend α by $alpha(sigma) := "nf"(n alpha)$ for each such record $n := sigma$, in the order the records were made. Then:
  (a) the records visible at the node are exactly those made by [Tail-gen] on the path from the root to it;
  (b) $alpha(sigma)$ is a ground value of type Δ(σ);
  (c) $(Omega_s [sigma slash n]^+) alpha = Omega_s alpha$, so generalising is invisible under α.
]) <tf-gen>
#proof[
  - *(a).* In F, [Split-gen] and [T-Split-goal] never run (F3, F4), so records come only from [Tail-gen], in tail position of the body being checked, and never on a private copy. A record belongs to the [Split] arm that made it and is dropped when the arm ends. A record made while checking an earlier definition is keyed by a text that mentions that check's abstract values or loan labels, and fresh names are never reused, so no state of this check can derive that text again. What remains is exactly the records made on this path.
  - *(b).* Take a record $n := sigma$ made at a node on the path. `n` occurs in that node's state, so its normal form under α exists by (A1) at that node, which the walk of @tf-thm maintains. In F, `n` has one of the two row shapes of [Close], with a head call of a data function (F2, F4). Its normal form under α is a value of that function's declared codomain, or of the declared type of the cell a fill row reads. [Tail-gen] gives σ the type of the matched place, which in F is the same closed data type (F1, F2).
  - *(c).* Every occurrence of `n` becomes σ, and every later re-derivation of `n` on the path normalises to $rho^*(sigma)$ ([Seal-stuck]). Under α both become $"nf"(n alpha)$, which is what `n` itself becomes, since normalisation is deterministic.

  No record crosses a sibling arm, so there is no cross-arm consistency to show. The closed proof of `False` of @sec-typing-types needed exactly such a crossing, through a type family.
]

#thm([Lemma], [footprints], [
  Let $Omega_s agr(alpha) Omega_g$, and let `t` and `u` be statement terms of F whose typed runs from $Omega_s$ succeed. Let $W_s$ and $W_g$ be the footprints $W(t, u)$ at $Omega_s$ and at $Omega_g$, as sets of positions. Then:
  (a) every $pi in W_g without W_s$ is owned only through borrow variables that hold ⊥ at $Omega_s$, and `t` and `u` only assign those variables, as whole variables;
  (b) for each π in $W_s without W_g$ or in $W_g without W_s$, the erased-mode ground runs of `t` and of `u` from $Omega_g$ leave the resolved content of π unchanged;
  (c) each observed place has the same type on both paths.
]) <tf-lem-w>
#proof[
  *The frame fact.* By @tf-ass-t (T2), a run changes the environment below its own frame only through the loans held by that frame's borrows, and in its own frame only the places it writes or borrows. In erased mode reads copy, so no read changes a place. Ending a borrow, including the old borrow that an assignment to a borrow variable drops, does not change any resolved content. So the resolved content of a position π can change only if `t` writes π or writes through a live borrow that π owns. Both are the owners of the places `t` writes or borrows and of the borrow variables it names, which is $W_g (t)$ by the definition of the footprint.

  *(a).* Let $pi in W_g$ be owned by the root of an occurrence `p` in `t` or `u`.
  - If `p` is rooted at an owned variable, it contributes that variable on both paths.
  - If `p` is rooted at a borrow variable `x`, then `x` holds a borrow at $Omega_g$, since a variable holding ⊥ contributes nothing. At $Omega_s$ it holds a borrow or ⊥; it never holds a loan, since `&&D` is not a type. If it holds a borrow, (A4) gives $"own"_(Omega_g)(x) subset.eq "own"_(Omega_s)(x)$, so $pi in W_s$.
  - Suppose it holds ⊥. The statement terms are match-free (F3), so the typed run of `t` reaches every occurrence in `t`, including those in erased positions, which the typing judgement runs on private copies ([T-Erase]).
    - Every occurrence rooted at a variable holding ⊥ is an error except an assignment to the whole variable. A read of `x` or of a place under it is [Read-err]. A borrow is [Borrow-err]. A match is [Match-err]. A `clone` is excluded by [Clone]'s premise. An assignment through `x` fails because its content is undefined.
    - `x := t'` drops ⊥, which is loan-free, and binds a new borrow. After it, `x` holds that same new borrow on both paths.
    - So `t` and `u` use `x` only by assigning it as a whole. The test `AssignBot` (the artifact's `Drops` block) is such a statement.

  *(b).* A position outside $W_g$ is left unchanged by both ground runs, by the frame fact. That covers $W_s without W_g$.
  - Let $pi in W_g without W_s$. By (a), π is owned only through borrow variables that hold ⊥ at $Omega_s$, which `t` and `u` only assign.
  - On the ground, such an assignment drops the variable's old borrow, which ends it and changes no resolved content.
  - If `t` wrote π through any other place `q`, the root of `q` would hold a live borrow at $Omega_s$, or be π itself. By (A4), π would then be in $W_s$.
  - So neither run changes π.

  *(c).* Observed places have type `Nat` or `Unit`. A place's type is read from its stored type; a temporary's is read from its value's type, which is a numeral's, Δ(σ)'s or a sealed program's declared codomain. Agreement relates positions of the same binding, and in F no refinement changes these types (F1, F2).
]

The symbolic side's extra positions do occur, and their conjuncts do become `True`: a hypothesis formed at an abstract `n` through `Pick(n, &a, &b)` has type `False ∧ ⊤` in arm `Z`, and a proof can use its second conjunct as `True`.

#thm([Lemma], [types agree], [
  Let $Omega_s agr(alpha) Omega_g$ and let `A` be a proposition of F. Suppose every call made in erased mode by the ground evaluation of `A` runs to completion without error. If `A` evaluates to $T_s$ at $Omega_s$ (in a type position, on a private copy), then it evaluates to some $T_g$ at $Omega_g$, and $ok(T_s alpha)$ iff $ok(T_g)$.
]) <tf-lem-types>
#proof[By induction on `A`. The runs involved are in erased mode, and by @tf-lem-conf the type former is confined on both paths or on neither.
  - *`True`, `False`.* $T_s = T_g$.
  - *`P ∧ Q`.* [T-Ind] keeps the head `And`, and its parts are evaluated one after the other on one private copy. By @tf-lem-runs agreement holds between them. Use the induction hypothesis.
  - *`Eq D a b`.* By @tf-lem-runs the ground runs of `a` and `b` succeed and their values agree. Values in flight are loan-free (T1), so $a_s alpha = a_g$ and $b_s alpha = b_g$. $T_s = "eq"(D, a_s, b_s)$, and valuation rebuilds `Eq` types with `eq`. `eq` may already have dropped a `True` conjunct symbolically that valuation does not restore, so $T_s alpha$ and $"eq"(D, a_g, b_g) = T_g$ need not be equal as values. But they have the same truth, which is what the lemma claims.
  - *`Id D t u`.* By @tf-lem-runs the ground runs of `t` and `u` succeed in agreement with the symbolic ones. The observation then ends every borrow. By (N3) and (A2), each symbolic observation under α equals the ground one after resolution, position by position: $r_s alpha = r_g$, and $w_s (pi) alpha = w_g (pi)$ for every position π; the same holds for `u`. So:
    - $T_s alpha$ has the truth of the conjunction of $"eq"(D, r_g, r'_g)$ and of $"eq"(T_pi, w_g (pi), w'_g (pi))$ over $pi in W_s$;
    - $T_g$ is the same conjunction over $pi in W_g$;
    - by @tf-lem-w (b), each conjunct over a position in only one of $W_s$ and $W_g$ compares equal values, so it is `True`; by (c) the conjuncts' types agree;
    - the truth of a conjunction does not depend on the order of its conjuncts.
]

#thm([Lemma], [call types], [
  Let `L` be a lemma of F with parameters $overline(x) : overline(A)$ and codomain `B`, called at a ground call point $Omega_g$ with arguments $overline(w)$. Let β be the ground instance the call is at. Then each parameter type, and `B`, are true at the call site ([Call-type]) iff they are true at the ground instance.
]) <tf-lem-call>
#proof[
  - *Setup.* At the call site the types are evaluated in $Omega_g";" (overline(x) |-> overline(w))$, and at the instance in $Gamma beta";" phi beta$. The two states differ only below the parameter frame. At the instance the borrow parameters' loans sit in the cells $c_i$; at the call site they sit in the caller's places.
  - *Runs.* Apply (T2) with the parameter frame as the core; its ports are exactly the cells. Each run made while evaluating a type at the call site is then the run at the instance, with the ports' final values substituted into the caller's frames. So results, and the final contents of the parameter frame's own positions, coincide.
  - *Borrow parameters.* An `Id` conjunct over a borrow parameter's owner compares, at the instance, the final contents of $c_i$. At the call site it compares the final contents of the owners of $ell_i$.
  - *One owner.* At a ground state a loan occurs at most once: only sealed programs may hold a loan twice (well-formedness condition 2, by T1), and a ground state has none. So $ell_i$ has one owner, reached through a chain of borrow contents, and its final content is $K[v]$ for the borrow's final value `v` and a context `K` that holds the hole once.
  - *Injectivity.* By `ctx_inj`, `K` is injective, so $"eq"(K[v], K[v'])$ is true iff $"eq"(v, v')$ is.
]

#thm([Lemma], [runs agree], [
  Let $Omega_s agr(alpha) Omega_g$. Let `t` be a term of F that is not a match on data, and suppose $Omega_s tack.r t ev v_s : A tack.l Omega'_s$ on the symbolic path, in runtime or erased mode. Suppose also that every call that the ground run of `t` makes at a call site of `t` runs to completion without error, in that mode, at the ground instance it is at. Then:
  - the ground run of `t` in that mode terminates without error, as $cfg(Omega_g, t) ev cfg(Omega'_g, v_g)$;
  - the states agree at every call point of `t`, and there each ground argument is the symbolic argument under α (for a borrow argument, its content);
  - the final states, with the values as temporaries, agree.
]) <tf-lem-runs>
#proof[By induction on `t`, one step at a time.
  - *Steps.* Each primitive step is (N1).
  - *Calls.* At a call, the arguments are evaluated into temporaries by the induction hypothesis. The consequence of agreement stated after @tf-def-agr then gives the ground arguments. Loan-free data arguments equal the symbolic ones under α, and borrow arguments' contents are whole and equal the symbolic contents under α, so the ground call is at the ground instance the lemma names.
    - The ground call runs to completion by hypothesis.
    - If the symbolic call closes off, (N2) gives agreement after it.
    - If it returns by [App], its body's steps are (N1) steps in the callee's frame. The calls they make are parts of the ground call's run, which completes, so the same argument applies to them, by induction on the depth of the run. Agreement after the call follows.
  - *Termination.* F has no loops, a match on data is never part of `t` (F4), and a match on a proof takes its one arm or is never run. So the ground run of `t` visits each subterm of `t` at most once. In addition it performs finitely many [End]s at each [Access] and [Drop], since each removes a borrow (`endBorrow_nb_lt`), and it makes the calls, which end by hypothesis. So it terminates.

  What is assumed about a call is its safety at the arguments it actually receives. That is weaker than safety of every call at every argument list, which is the premise of the mechanised `exec_total`.
]

#thm([Lemma], [modes], [
  If a data function's runtime-mode run from a ground instance completes without error, so does its erased-mode run, with the same result.
]) <tf-lem-modes>
#proof[
  - *Where the modes differ.* They differ only at [Read] of owned non-copy data. Runtime mode leaves `ghost(v)` behind, and erased mode leaves `v`. By F6 no such read is under `*`, and a ground instance holds no ghost.
  - *The erased state has fewer ghosts.* Run both from the instance. At each step the erased state is the runtime state with the ghosts that runtime-mode reads created replaced by their values.
  - *Premises.* Ghosts only ever make a premise fail: [Read-err], [Borrow-err], [Match-err], and [End]'s wholeness. So every premise that holds on the runtime state holds on the erased state.
  - *Results.* The values the steps produce are the same.
]

=== The theorem <tf-thm-sec>

#thm([Theorem], [soundness of F, conditional on @tf-ass-n and @tf-ass-t], [
  Let $cal(P) = d_1 dots d_m$ be a program of F whose definitions are accepted in order by [Def] and [Const]. Then for every $d_k$ and every ground instance β of $d_k$:
  (i) if $d_k$ is a data function, its body runs from the ground instance to completion without error, in runtime mode and in erased mode, and the pop of its frame succeeds; if $d_k$ returns a borrow, the result is a live borrow, not ⊥;
  (ii) if $d_k$ is a lemma, or a constant of proposition type, and its hypotheses at β are true, then its goal at β is true.
]) <tf-thm>

#proof[
  *The induction.* By induction on the pairs $(k, |beta(sigma_j)|)$, ordered lexicographically. $|v|$ is the size of the numeral that is $d_k$'s decreasing argument, read through the borrow for `&Nat`; it is 0 without `by`. Fix `k` and β, and assume (i) and (ii) for every smaller pair.
  - A constant ($n = 0$) is checked by [Const] from the empty environment, without a case tree. A data constant's value is computed once, at checking time. For a proof constant, (ii) is the claim below with $alpha = emptyset$, as in @tf-cor-cons.
  - For (i), erased mode follows from runtime mode by @tf-lem-modes. The rest of the proof is about runtime mode and about definitions with parameters, checked by [Def].

  *Which calls the walk needs, and why each is safe.* @tf-lem-runs needs every call that the ground run makes at a call site of the body to run to completion at the ground instance it is at. There are three kinds.
  - A call of $d_j$ with $j < k$, since a definition is checked against the ones before it: safe by the induction hypothesis (i), in either mode.
  - A recursive call of $d_k$ at a call site on the walk's path. The symbolic check applied [Rec] there ([T-Call]'s premise), so the symbolic decreasing argument, or its content, is a strict subterm of $rho^*(sigma_j)$. By @tf-lem-runs the ground argument at that call point is the symbolic one under α. α respects ρ, so it is a strict subterm of $alpha(sigma_j) = beta(sigma_j)$, and the pair is smaller.
  - A call made while evaluating a type. By F2 it is to an earlier definition, and it is in erased mode; safe by the induction hypothesis (i) and @tf-lem-modes.

  Proof calls are never run at ground ([Erase-proof]); only their types are evaluated, which is the third kind. The induction hypothesis (i) is about a run from the callee instance's own state. A call at a ground call point completes because, by @tf-ass-t (T2), its run is that isolated run, plugged back into the caller.

  *The walk.* We follow $d_k$'s case tree $cal(L)$, from [Def], along β. Throughout we keep five things:
  - a node of the tree with its symbolic state $Omega_s$;
  - a valuation $alpha supset.eq beta$ that covers and respects $Omega_s$;
  - the ground state $Omega_g$ that the ground run of the body has reached;
  - agreement, $Omega_s agr(alpha) Omega_g$;
  - when $d_k$ is a lemma, the invariant (I): every proof place of $Omega_s$ (a binding declared a proof, or a field place of one) has a type $T$ with $ok(T alpha)$.

  At the root, $Omega_s = Gamma";" phi^+$, $Omega_g = Gamma beta";" phi^+ beta$ and $alpha = beta$. Agreement is immediate, since $Omega_s beta = Omega_g$. (I) holds by @tf-lem-types, applied to each hypothesis in turn: its type at the generic state is true under β iff it is true at the ground instance, where it is true by assumption. The tail rules move down the tree:
  - *[Tail-let], [Tail-seq].* `t` is not a match on data (F4). By @tf-lem-runs its ground run succeeds and agreement is kept; (N1) covers the drop. (I) is kept: a proof bound by the `let` has a true type by the claim below.
  - *[Tail-match].* [Access] is (N1). By the consequence of agreement stated after @tf-def-agr, the scrutinee then has the same head constructor on both paths, so both take the same arm.
  - *[Tail-split] on σ.* After [Access], by the same consequence, the ground scrutinee's head is that of α(σ), say $ty("C")_i$, so the ground run takes arm `i`. We move to the tree's arm `i` and extend α to the arm's fresh field values by the fields of α(σ). α respects $sigma := r_i$ and $(Omega_s [sigma := r_i]) alpha = Omega_s alpha$, so agreement and (I) carry over.
  - *[Tail-gen] on a sealed program `n`.* Extend α by @tf-gen and continue as for [Tail-split].
  - *[Tail-prop] (lemma bodies).*
    - With one arm (`And`, `True`), move to it. Its field places have the field types, which are true, since $ok((P and Q) alpha)$ gives $ok(P alpha)$ and $ok(Q alpha)$; (I) is extended to them.
    - With no arms, the scrutinee's type is `False`, and (I) would give $ok(ty("False"))$. So no ground instance reaches this node, and there is nothing to prove. This is where ex falso is sound.
  - *[Tail-end] `t`.*
    - This is a leaf $(Omega'_s, v, A)$. [Def] gives $"pop"(Omega'_s, v)$ succeeding and $A equiv G'$, the goal refined along the path.
    - By @tf-lem-runs the ground run of `t` succeeds, and by (N1) so does the ground pop. The ground run of the body follows the walk's path one tail rule at a time. The path is finite, and each segment terminates (@tf-lem-runs). So the body runs to completion without error.
    - *The result is live.* In F a term of borrow type never evaluates to ⊥ on the symbolic path. Reading ⊥ is [Read-err]. [Borrow] makes a live borrow. A call's result is live by [Close]'s borrow row, or, for a call that runs, by the same argument for the callee's tail term. There are no stuck blocks (F4), and a stuck block is the one way an arm could return a borrow ended by a drop and have [Close] revive it.
    - The pop does not end the result either. A dying local lent to the result, which is a value in flight during the pop, makes the pop an error rather than an end ([Drop] of a lent place). So the symbolic result is a live borrow, held as a temporary after the pop. By (A3) the ground result, at the same position, is a borrow too. This is (i).
    - For (ii), `v` is a proof, and the claim below gives $ok(A alpha)$. By @tf-lem-conv (b), $A alpha equiv G' alpha$.
    - $G' alpha = G beta$, because α respects the path's refinements and records (@tf-gen (c)) and `G` mentions only generic values. By @tf-lem-conv (a), $ok(G beta)$.
    - By @tf-lem-types at the root, the goal at the ground instance is true. The calls made in evaluating it are to earlier definitions (F2).

  *Claim (proof terms have true types).* Let $Omega_s agr(alpha) Omega_g$ with (I), and $Omega_s tack.r t ev star : A tack.l Omega'_s$ for a proof term `t` of F. Then $ok(A alpha)$. By induction on the derivation:
  - `refl` has type `True`.
  - $chevron.l h, k chevron.r$: [T-Ctor] types `h : P'` and `k : Q'` with $P' equiv P$ and $Q' equiv Q$. Use the induction hypothesis and @tf-lem-conv.
  - A proof place has its type, true by (I). A proof constant `c` has its declared type ([T-Const]), which is true by the theorem's induction hypothesis (ii), since `c` is earlier in the program.
  - *A `let` or sequence whose tail is a proof* (F5). The proof runs on a private copy, in erased mode, and the machine never runs it. By @tf-lem-runs, in erased mode with the calls justified above, the same steps run from $Omega_g$ succeed and keep agreement. So there are ground states in agreement at every intermediate state, and the induction hypothesis applies to the proof subterms there.
  - A match on a proof: as for [Tail-prop]. With no arms (under an annotation, [T-Match-erased]), the premise gives `h : False`, against (I), so the case is vacuous.
  - *A lemma call $L_j (overline(u))$ ([T-Call-proof]).*
    - The arguments evaluate at $Omega_s$ to $overline(w)_s$, ending at $Omega_(s 1)$. By @tf-lem-runs the ground evaluation gives $overline(w)_g$ at $Omega_(g 1)$, in agreement, with each ground argument the symbolic one under α.
    - The parameter types $T_i$ and the call's type `B'` are evaluated after pushing the parameter frame, which is (N1). By @tf-lem-types each has the truth of the corresponding type at the ground call site; the calls in them are to definitions before $L_j$ (F2).
    - A proof argument $u_i$ has type $A'_i equiv T_i$, which is true under α by the induction hypothesis and @tf-lem-conv. So the ground call site's hypotheses are true, and by @tf-lem-call so are those of the ground instance $beta_j$ of $L_j$ the call is at.
    - The pair $(j, |beta_j|)$ is smaller than the current one: $j < k$, or $j = k$ and [Rec] ([T-Call-proof]'s premise) made the decreasing argument a strict subterm, as for data calls. So the theorem's induction hypothesis (ii) makes $L_j$'s goal at $beta_j$ true.
    - By @tf-lem-call, `B'` at the ground call site is true, and by @tf-lem-types, $ok(B' alpha)$.
]

This theorem reduces soundness of F to @tf-ass-n and @tf-ass-t; it is not a proof of soundness outright.
- *What is proved.* The case analysis at tail matches and [Rec]'s decrease under α. Termination at the level of calls. The truth bookkeeping, footprints, call types, confinement and generalisation.
- *What is assumed.* That each step of a symbolic run and the corresponding ground step agree, with agreement including what each live borrow holds (A5). And that the earlier rule set's well-formedness and frame property hold for F.

=== Corollaries <tf-cors>

#thm([Corollary], [consistency of F, conditional], [
  Under @tf-ass-n and @tf-ass-t, no closed term of F has type `False`. More generally:
  - if a closed proof term `t` of F is typed from the empty environment, $epsilon tack.r t ev star : A tack.l Omega'$, after the definitions of an accepted program, then $ok(A)$;
  - every accepted constant of proposition type is true.

  In particular no closed term has type `Eq Nat Z (S Z)`, which computes to `False`.
]) <tf-cor-cons>
#proof[The empty state is ground, and $epsilon agr(emptyset) epsilon$ holds with (I) vacuous. The claim in the proof of @tf-thm, with $alpha = emptyset$ and @tf-thm itself supplying the lemma calls and the calls in types, gives $ok(A)$. `False` is not true, and truth is invariant under conversion (@tf-lem-conv (a)), so $A equiv.not ty("False")$.]

#thm([Corollary], [adequacy of `Id`, conditional], [
  Under @tf-ass-n and @tf-ass-t, suppose a lemma $L : Pi(overline(x) : overline(A)). ty("Id") D thin t thin u$ of F is accepted. Then at every ground instance whose hypotheses are true, the _observations_ of `t` and `u` are equal: their runs on private copies, in erased mode, give the same result and the same final contents of every place either run changes.
]) <tf-cor-adeq>
#proof[By @tf-thm (ii), $"and"("eq"(D, r, r'), "eq"(T_pi, w_pi, w'_pi), dots)$ is true. At a ground state, `eq` on two numerals is `True` iff they are equal, and `Unit` has one value. By @tf-lem-w (b), every place that `t` or `u` changes is observed.]

The corollary is about observations, which read by copying. It says nothing directly about `t` and `u` as runtime code, whose reads of an owned `Nat` move. For example, `Id Nat (let z = a; a) a` is proved by `refl`, while `let z = a; a` is rejected as code. By @tf-lem-modes, an accepted data function's runtime and erased runs from a ground instance agree, so for calls of accepted functions the distinction does not matter.

*Remarks on stability.* For a term of F at agreeing states, the decisions of @lem-stable are:
- (1) and (4), erasure, matches decided by a proof's type, and each call's class and [Close] row, are read from declared types, constructor names and declared codomains. F never changes those.
- (2): F forms no stuck blocks.
- (3): at a ground instance every match takes its arm, so no arm is checked.
- (5): the same types for observed places (@tf-lem-w (c)).
- (6): footprints may differ in both directions, but every position in only one of them contributes a conjunct that is `True` (@tf-lem-w). The symbolic side's extras are the common case, from over-approximate owners. The ground side's extras come only from borrow variables that the symbolic path has already ended and that a statement reassigns (`AssignBot`).

These are remarks, not a corollary. At ground valuations most items hold trivially. The refinements that matter for [Split], such as $sigma := ty("S") sigma'$, are not ground, and this section says nothing about them. Soundness uses @tf-thm, not stability.

=== [Drop] after an early end <tf-drop>

The symbolic path can end a borrow earlier than the ground path, which (A2) allows. The [Drop] rule for a lent place is what keeps that from mattering. If a drop failed whenever the dying value held a live loan, this program would be accepted and go wrong:
```
Bad2(n : Nat, b : Nat, x : &Nat) : Unit := let a = 0; x := Pick(n, &a, &b); let z = b; ()
```
- *Symbolic path.* At the abstract `n`, `Pick` closes off, and its hole $"loan"_k$ sits in the fills of both `a` and `b`. Reading `b` ends `k`, because [Access] ends every loan inside the content, sealed programs included. So `x` holds ⊥, and `a` holds data when it goes out of scope. The [Drop] succeeds.
- *Ground path, `Bad2(0, 5, &y)`.* `Pick` returns a borrow of `a`, and `b` holds no loan. Reading `b` ends nothing, and `a` goes out of scope while `x` still borrows it. Under that rule, the drop would fail.

A match on a fill with a single owner does the same: the match ends every loan inside the fill, while on the ground the loan sits deeper and survives the match. The test `Bad4` of the `Drops` block has this shape.

*The rule.* When a dying owned value holds a live loan, [Drop] ends the borrower if the borrower is held in a binding, and fails if the borrower is a value in flight (@tf-frag). `Bad2` and `Bad4` are then accepted and run without error. Returning a borrow of a local (`let a = 0; &a`, the test `RetLocal`) is still rejected, with no separate check: the result is a value in flight when the local is dropped.

Ending every borrower, including those in flight, would be unsound. A stuck block's arm could return a borrow of an arm-local, which the drop turns into ⊥. [Split] discards the arm's value, and [Close]'s borrow row then gives the block a fresh live borrow. So the ground run would meet ⊥ where the symbolic run holds a live borrow.

*Why the [Drop] clause of (N1) holds.* The argument is part of @tf-ass-n. A ground drop fails only if the dying place is lent to a value in flight. Take that temporary's symbolic counterpart, at the same position.
- If it is live, (A4) puts the dying place among its symbolic owners, so the symbolic drop fails too.
- If it is ⊥, the symbolic path ended it early while it was in flight. In F, a borrow is in flight during a call's argument evaluation, during an assignment's [Access], during a let-block's final drops, during a pop, and, as the discarded value of `t; u`, during its own drop. Constructor fields are data. Type formers and observations run on private copies, a callee's parameters are bindings once its frame is pushed, and [Close] consumes its borrow arguments, so none of these adds a case.
  - A call argument ended in flight is [Call-err] on the symbolic path.
  - During drops and pops, only borrowers held in bindings are ended, so a temporary is never ended there.
  - An assignment's new value is never ended by the assignment's own [Access], on either path, so `x := Pick(n, &*x, &b); *x := 5` is accepted. That [Access] ends only the loans in the part of the place's content that the place owns. A place that receives a borrow has borrow type, and what it owns is its old borrow, not the data behind it. A place of data type receives loan-free data. While the new value is in flight, the only drop is of the old content, a borrow, so the drop ends it and never fails. After the assignment the value is a binding.
  - A discarded value of `t; u` that is a borrow is ended by its own drop, which never fails.

So when the symbolic drop succeeds, the ground drop succeeds. The borrowers the ground drop ends are those held in bindings whose owners include the dying place. By (A4) their symbolic counterparts are ended by the symbolic drop too, or were already ⊥. So (A3) is kept, and (A2), (A4) and (A5) are unaffected, since ending borrows does not change the resolution.

*Early ends are deep.* An early symbolic end does not leave a reborrow alive that the ground path later ends. In F, an early end comes from a hole inside a fill: [Access] or [Drop] meets the loan inside a sealed program.
- The ended borrow's content, reborrows included, is substituted into that same fill.
- Hole parametricity keeps the fill stuck: its run never inspects the hole. So those loans are still inside a neutral at the head of the place being accessed.
- The same [Access] or [Drop] keeps ending loans until none remains there, so it ends the reborrows too.

A [Match]'s [Access] ends only loans on the path and loans inside a neutral at the head, not loans deeper in a value. An assignment's [Access] ends only the loans in the part of the place's content that the place owns, including loans inside neutrals in that part ($L^A$, @app-aux). A loan behind a borrow the place holds, even one inside a neutral, is left alone on both paths, and the drop of that borrow carries it back to its owner. In each case, an early end that the [Access] makes is made inside a neutral, so the argument goes through the fill staying stuck. So a program that reborrows through `Pick`'s result and then assigns `x := &c` is accepted: the reborrow's loan sits behind the borrow `x` held, and that borrow's drop carries it back.

Pairs would break the argument: a shallow read of one field would leave a reborrow in the other field alive. F has none (F1). The argument is part of @tf-ass-n, as the preservation of (A3).

The reborrow-and-replace idiom is in F, and it is accepted. `Trav(x : &Nat) : Unit := match *x { Z => (), S p => (x := &p; *x := 0) }`, the test `Trav` of the artifact's `Reborrows` block, satisfies F1–F6. The new borrow's loan sits behind the borrow that `x` held, which the assignment's [Access] leaves alone. The drop of the old borrow carries the loan back to its owner, where it stays live. So @tf-thm covers it.

=== What would remove the assumptions <tf-remains>

+ *Prove @tf-ass-n for F.* This is a simulation, rule by rule, between the typing judgement's symbolic run and the ground machine, with agreement (A1)–(A5) as the relation. It uses order-independence at every [End], the `close_*` equations at every [Close], and the frame property at every call. The risks are:
  - the preservation of (A3) (early ends are deep), (A4) and (A5);
  - agreement after a drop;
  - (N3) through [Seal] with inert loans.

  We estimate it at 3–5k lines of Lean.
+ *Prove @tf-ass-t,* by porting `exec_wf` and the frame lemma to ghosts and to the current [Close].
+ *Widen F.* Each addition brings back a decision of @lem-stable:
  - moves through borrows (F6): ghost-transparent resolution;
  - stuck blocks (F4): captures and modes;
  - closures and Π-values: class, captured types, [Conv-fun];
  - user inductives and pairs: disjointness and injectivity in `eq`;
  - type families: the types of generalised values;
  - `J` and `rewrite`: transport and stuck casts.

*Where F's restrictions are used.*
- F1: ground values (@tf-def-truth); @tf-gen (b); @tf-lem-w (c); early ends are deep (@tf-drop).
- F2: @tf-lem-conv (conversion on data is syntactic); @tf-gen (b); @tf-lem-w (c); calls in types are to earlier definitions (@tf-thm).
- F3: @tf-lem-conf; @tf-lem-w (a) (every occurrence in a statement is reached); with F4, @tf-gen (a) (records come only from [Tail-gen]).
- F4: the walk forms no stuck blocks; @tf-lem-runs; the live result of @tf-thm (i).
- F5: @tf-thm (i) (a data function's run never depends on the truth of a hypothesis); the claim's `let` case.
- F6: @tf-lem-res; the whole borrow arguments of @tf-lem-runs; @tf-lem-modes.
- The [Drop] rule for lent places: the [Drop] clause of (N1), and the live result of @tf-thm (i) (@tf-drop).
