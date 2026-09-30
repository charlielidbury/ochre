#import "../paper/style.typ": *
// Standalone compile, from ochr/core: typst compile --root . notes/typed-fragment-proof.typ. Drop the next line when included in the paper, which numbers headings itself.
#set heading(numbering: "1.1")

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

= A theorem for a typed fragment <sec-tf>

_Draft for an appendix section. Notes file: `ochr/core/notes/typed-fragment-proof.typ` (2026-09-30). The plan it carries out is `notes/typed-fragment-plan.md`. References to "the appendix" are to the paper's appendix, whose rules this section uses by name._

This section proves a theorem about the typed calculus for a fragment F. F has natural numbers, `Unit`, the propositions `True`, `False` and `And`, `Eq` and `Id`, first-order top-level functions with borrow parameters (some of which return a borrow), [Close], and [Split] with refinement and generalisation. The theorem says two things. Every accepted data function runs without error at every concrete input. Every accepted lemma is true at every concrete input at which its hypotheses are true. Consistency of F and adequacy of `Id` follow (@tf-cor-cons, @tf-cor-adeq), and so does the part of stability that soundness uses (@tf-cor-stab).

The proof is by induction on the program and on the [Rec] measure, and it has one step that is not proved here. We state that step as an assumption, naturality (@tf-ass-n). It says that a run on abstract inputs and the run on concrete inputs agree once every borrow is ended. Everything else is either proved below or cites a lemma mechanised in `ochr/core/meta-lean` (@tf-anchors). The assumption is where the risk is. A probe written for this proof found that it is false for the full rules (`DropProbe`, @tf-drop), and F excludes the programs involved (restriction F5).

== The fragment F <tf-frag>

F is the calculus of the appendix restricted as follows. Each restriction says why.

+ *Data.* The only inductive declarations are the library's `Nat`, `Unit`, `False`, `True` and `And`. Data types are `Nat` and `Unit`; borrow types are `&Nat` and `&Unit`. There are no pairs and no user inductives. _Why:_ it keeps ground values to numerals and `()`.
+ *First order.* Programs are sequences of top-level definitions $kw("def") f (x_1 : A_1 dots x_n : A_n) : B space [kw("by") x_j] := b$ ($n >= 0$; $n = 0$ is a constant). Each $A_i$ is a data type, a borrow type or a proposition, and `B` is a data type, a borrow type (and then some $A_i$ is one, D44) or a proposition. There are no `fix` or `λ` inside bodies, no Π-types as values, no function parameters (so no abstract functions), no universes other than as the sorts of these types, no parameters of sort `Prop`, no type families and no Prop-valued functions. A definition is a _data function_ if `B` is data or a borrow type, and a _lemma_ if `B` is a proposition. _Why:_ this makes the type of every sealed program a closed data type (@tf-gen), which is what reviewer 6's closed proof of `False` (A1) lacked.
+ *Propositions.* $P ::= ty("True") | ty("False") | P and Q | ty("Eq") D thin a thin b | ty("Id") D thin t thin u$, with $D in {ty("Nat"), ty("Unit")}$. The terms `a`, `b`, `t`, `u` inside a type contain no `match`. _Why:_ a match inside a type that gets stuck is closed off as a stuck block, which F leaves out. It also makes every place occurrence in a statement reached by the statement's run (@tf-lem-w).
+ *No stuck blocks.* A `match` on data occurs only in tail position in a definition's body: the body itself, an arm of a match in tail position, or the tail of a `let` or sequence in tail position. It never occurs on the right of a `let`. So [Split] is only [Tail-split] and [Tail-gen], and no stuck block is ever formed.
+ *No borrow is assigned into an existing place.* In `p := t`, `t` does not have a borrow type. Borrows are bound by `let`, passed as arguments, or returned. _Why:_ @tf-drop. With the assignment `x := Pick(n, &a, &b)` the symbolic path accepts a function that fails at a concrete instance. Without it, a borrower is declared after every place it borrows, so it is dropped before them on both paths.
+ *Proof forms.* Proof terms are `refl`, $chevron.l h, k chevron.r$, proof variables, lemma calls, a match on a proof of `And` or `True` (one arm), and `match h {}` on a proof of `False`. `match h {}` occurs only in lemma bodies. There is no `J`, `rewrite` or `split`. _Why:_ a data function's run then never depends on the truth of its hypotheses (@tf-thm, part (i)).

Moves (D53) are as in the rules: `Nat` is not a copy type, so a runtime read of a `Nat` place moves it.

== Ground instances, truth and agreement <tf-defs>

#thm([Definition], [ground], [
  A value is _ground_ if it contains no abstract value, no sealed program and no inert loan; a ground value of type `Nat` is a numeral and one of type `Unit` is `()`. A state is ground if its values are; it may hold live borrows and loans. A _valuation_ α assigns to each abstract value σ in its domain a ground value of type Δ(σ). For a state Ω whose abstract values α covers, $Omega alpha$ is $Omega[alpha(sigma) slash sigma]^+$, substitution followed by normalisation (appendix, item 6 of the auxiliary definitions); it is _defined_ when every normalisation it triggers ends without error. α _respects_ the records of the state if $alpha(sigma) = r alpha$ for every refinement $sigma := r$ and $alpha(sigma) = "nf"(n alpha)$ for every generalisation record $n := sigma$.
]) <tf-def-ground>

The _generic state_ of a definition `d` is $Gamma";" phi$, its generic call's environment (appendix, item 10): borrow parameters are bound to $"borrow"_(ell_i) sigma_i$ with owned cells $c_i |-> "loan"_(ell_i)$, data parameters to fresh $sigma_i$, and proof parameters to ⋆ with their types stored. A _ground instance_ of `d` is a valuation β of $sigma_1, dots, sigma_n$; its state is $Gamma beta";" phi beta$. Its _hypotheses_ are the proof parameters' types evaluated at the ground instance, left to right. The goal at the ground instance is `B` evaluated there, which is the [Call-type] of the call $d(overline(a) beta)$ from a caller whose frame holds the cells.

#thm([Definition], [truth], [
  At a ground state, `eq` on two numerals computes to `True`, `False` or an `And` of such, and `eq` on `Unit` to `True`, so a proposition value computed at a ground state is built from `True`, `False` and `And` alone. _Truth_ ⊨ is defined on these by $ok(ty("True"))$, $not ok(ty("False"))$, and $ok(P and Q)$ iff $ok(P)$ and $ok(Q)$.
]) <tf-def-truth>

#thm([Definition], [agreement], [
  Let $Omega_s$ be a state on the symbolic path, α a valuation that covers and respects it, and $Omega_g$ a ground state with the same frames, bindings and temporaries. $Omega_s agr(alpha) Omega_g$ holds when:
  (A1) $Omega_s alpha$ is defined;
  (A2) $res(Omega_s alpha) = res(Omega_g)$ up to a renaming of loans, where ρ ends every borrow;
  (A3) every position that holds a borrow in $Omega_s$ holds a borrow in $Omega_g$;
  (A4) at every position that holds $"borrow"_ell$ in $Omega_s$ and $"borrow"_(ell')$ in $Omega_g$, $"owners"_(Omega_g)(ell') subset.eq "owners"_(Omega_s)(ell)$.
]) <tf-def-agr>

Both $Omega_s alpha$ and $Omega_g$ are ground, and at a ground state [End] is plain substitution, because there are no sealed programs to re-normalise. So ρ is the resolution of property 7, which is mechanised: the result does not depend on the order in which borrows are ended (`end_order_indep`). Moreover, a state reached by any successful sequence of [End]s resolves to the same state (`endAll_endSeq`). Two consequences are used throughout:
- (A2) is equivalent to "some sequences of [End]s take $Omega_s alpha$ and $Omega_g$ to one state", which is the form the F5 counterexample of the mechanisation forced (`notes/lean-meta.md`);
- (A2) survives an [End] on either side, which is how the symbolic path may end a borrow earlier than the ground path (property 9's `Pick` example) without breaking agreement.

(A3) says that the symbolic path has ended at least the borrows the ground path has. (A4) says that its owners over-approximate: a returned borrow's hole sits in the fill of every place it may point into.

== What the proof assumes, and what it cites <tf-anchors>

#thm([Assumption], [naturality], [
  Let every data function that a term `t` of F calls be safe, in the sense of @tf-thm (i). Let $Omega_s agr(alpha) Omega_g$, and let `t` not be a match on data. If $Omega_s tack.r t ev v_s : A tack.l Omega'_s$ on the symbolic path, then:
  (N1) the machine run $cfg(Omega_g, t) ev cfg(Omega'_g, v_g)$ ends without error;
  (N2) $Omega'_s dot v_s agr(alpha) Omega'_g dot v_g$;
  (N3) if $"drop"(Omega'_s, v_s)$, or the pop of a frame, succeeds on the symbolic path, it succeeds on the ground path, and agreement is kept;
  (N4) resolution commutes with valuation: $res(Omega_s) alpha = res(Omega_s alpha)$ up to a renaming of loans.
]) <tf-ass-n>

This is the relational form of property 9. The symbolic run includes the runs of callee bodies in the machine ([T-Call]), where calls stuck on an abstract value close off. On the ground path those calls run.

*It is false without restriction F5.* The probe `ochr/core/lean/Scratch/DropProbe.lean` (@tf-drop) is an accepted data function whose ground run fails at a [Drop], against (N1) and (N3). We believe F5 restores (N1) and (N3), by the argument given in F5, but we have not proved it. The other risks in @tf-ass-n are:
- (N4), for [Seal] with inert loans. A fill ⌈`L; let r = C; *r := loan_k; c`⌉ is normalised with `loan_k` inert, and ending `k` later substitutes into it and re-normalises;
- the preservation of (A4) by every rule.

Its proof would go by induction on the machine's rules. It would use these mechanised facts, which are stated for `meta-lean`'s machine (rule set 1.3: copy reads, lazy normalisation, and a `Unit` row in [Close]):

#table(columns: (30%, 1fr, 24%), stroke: none, inset: (x: 4pt, y: 3pt), align: left,
  table.hline(stroke: 0.5pt),
  [*Lean*], [*Statement*], [*Used for*],
  table.hline(stroke: 0.4pt),
  [`end_order_indep`, `endAll_endSeq`], [resolution exists in a well-formed state, does not depend on the order of [End]s, and is not changed by ending some borrows first], [@tf-def-agr],
  [`frame_local`, `call_effect`], [a run changes the environment below its frame only through the loans of its own borrows; a call's effect is its isolated run, plugged back], [@tf-lem-w, @tf-lem-call; (N1)–(N2) at calls],
  [`close_res`, `close_fin`, `close_cur`, `close_back`], [the sealed programs of [Close] normalise to the call's result, the final contents of its borrowed places, its current content and its backward function], [(N2) and (N4) at [Close]],
  [`ctx_inj`], [a context holding a loan is injective in the loan's final value], [@tf-lem-call],
  [`exec_wf`], [runs preserve well-formedness: unique borrows, bound and acyclic loans, loan-free values in flight], [owners are defined; @tf-lem-call],
  [`exec_total`, `termination_of_calls`], [a run terminates if every call it makes does], [(N1): the ground run ends],
  [`exec_rename`], [the machine commutes with renaming loans], [(A2)'s renaming],
  table.hline(stroke: 0.5pt),
)

Transferring these from rule set 1.3 to the current rules is part of @tf-ass-n. So are moves, which the mechanised machine does not have. Everything below @tf-ass-n is proved on paper in this section.

== Lemmas <tf-lemmas>

#thm([Lemma], [truth and conversion], [
  (a) If $P equiv Q$ are proposition values at a ground state, then $ok(P)$ iff $ok(Q)$. (b) In F, if $v equiv w$ then $v alpha equiv w alpha$ for every valuation α for which both are defined.
]) <tf-lem-conv>
#proof[In F the conversion rules that apply are [Conv-refl], [Conv-cong] and [Conv-unit]: F has no function values and no Π-closures, and its only η is `eq`'s for `Unit`. On data values, [Conv-cong] compares sealed programs by their programs, component by component, so on data ≡ is equality up to the names of bound variables. (a) At a ground state a proposition is built from `True`, `False` and `And` (@tf-def-truth). [Conv-cong] relates `And` to `And` componentwise, and [Conv-unit] removes `True` conjuncts. Both preserve truth, by induction on the derivation of ≡. (b) A valuation substitutes and then normalises, rebuilding every `Eq` type with `eq`. So it sends equal values to equal values, and the unit laws commute with substitution.]

#thm([Lemma], [generalisation], [
  Let α cover and respect $Omega_s$, except for the abstract values that generalisation records introduce, and let $Omega_s alpha$ be defined. Extend α by $alpha(sigma) := "nf"(n alpha)$ for each record $n := sigma$, in the order the records were made. Then:
  (a) $alpha(sigma)$ is a ground value of type Δ(σ);
  (b) $(Omega_s [sigma slash n]^+) alpha = Omega_s alpha$, so generalising is invisible under α;
  (c) the extension does not depend on which path of the case tree, or which private copy, made the record.
]) <tf-gen>
#proof[
  - *Shape.* In F every sealed program has one of the two row shapes of [Close], with a head call $C = f(overline(a))^h$ of a data function `f`. There are no neutral heads, closures or stuck blocks (F2, F4).
  - *(a).* $n alpha$ is a closed program with ground embedded values. Its normal form exists because $Omega_s alpha$ is defined. It is a value of `f`'s declared codomain for ⌈`L; C`⌉ and ⌈`L; let r = C; *r`⌉, and of the cell's declared type for the fill rows. [Tail-gen] gives σ the type of the matched place. In F the type of a place is a closed data type that no refinement changes (F1, F2), and it is the type just named.
  - *(b).* Every occurrence of `n` becomes σ, and every later re-derivation of `n` normalises to $rho^*(sigma)$ ([Seal-stuck]). Under α both become $"nf"(n alpha)$, which is what `n` itself becomes, since normalisation is deterministic.
  - *(c).* The record is global and keyed by the text of `n` (D37: it survives private copies and is seen by sibling arms). The text fixes the value of `n` under any valuation of the abstract values it mentions. Fresh names are never reused, so those values mean the same on every path where they exist. So on any path that sees the record, $alpha(sigma) = "nf"(n alpha)$ is forced.
  - *Where A1 fits.* What differed between arms in reviewer 6's A1 was Δ(σ), through an abstract function whose result type depended on a refinement. F excludes both.
]

#thm([Lemma], [footprints], [
  Let $Omega_s agr(alpha) Omega_g$, and let `t` and `u` be statement terms of F whose typed runs from $Omega_s$ succeed. Let $W_s$ and $W_g$ be the footprints $W(t, u)$ at $Omega_s$ and at $Omega_g$, as sets of positions. Then:
  (a) $W_g subset.eq W_s$;
  (b) for each $pi in W_s without W_g$, the ground runs of `t` and of `u` from $Omega_g$ leave the resolved content of π unchanged;
  (c) each observed place has the same type on both paths.
]) <tf-lem-w>
#proof[
  *(b).* By `frame_local`, a run changes the environment below its own frame only through the loans held by that frame's borrows. In its own frame it changes only the places it writes, borrows or moves. A place that is moved out holds a ghost, and its resolved content, read through the ghost, is unchanged. So the positions whose resolved content a run of `t` can change are the owners of the places `t` writes or borrows and of the borrow variables it names: $W_g (t)$, by the definition of the footprint. A position outside $W_g = W_g (t) union W_g (u)$ is left unchanged by both runs.

  *(a).* Let $pi in W_g$, owned by the root of an occurrence `p` in `t` or `u`.
  - If `p` is rooted at an owned variable, it contributes that variable on both paths.
  - If `p` is rooted at a borrow variable `x`, then `x` holds a borrow at $Omega_g$, and at $Omega_s$ it holds a borrow or ⊥. It never holds a loan, since `&&D` is not a type.
  - It cannot hold ⊥. The statement terms are match-free (F3), so the typed run of `t` reaches every occurrence in `t`. That includes those in erased positions, which the typing judgement runs on private copies ([T-Erase]). An occurrence rooted at a variable holding ⊥ is an error ([Read-err], [Borrow-err], [Assign], [Match-err]), and the run succeeded.
  - So `x` holds a borrow at $Omega_s$, and (A4) gives $"own"_(Omega_g)(x) subset.eq "own"_(Omega_s)(x)$. Hence $pi in W_s$.

  *(c).* Observed places have type `Nat` or `Unit`. A place's type is read from its stored type; a temporary's is read from its value's type, which is a numeral's, Δ(σ)'s or a sealed program's declared codomain. Agreement relates positions of the same binding, and in F no refinement changes these types (F1, F2).
]

The probe `ochr/core/lean/Scratch/FootprintProbe.lean` shows (a) is strict. With `r = Pick(n, &a, &b)`, an `Id` about writes through `r` has conjuncts over `a` and `b` at an abstract `n`, and over `a` alone at `n = 0`. Formed at the abstract `n` and then refined, its `b` conjunct becomes `True`, as (b) predicts.

#thm([Lemma], [types agree], [
  Let $Omega_s agr(alpha) Omega_g$ and let `A` be a proposition of F. If `A` evaluates to $T_s$ at $Omega_s$ (in a type position, on a private copy), then it evaluates to some $T_g$ at $Omega_g$, and $ok(T_s alpha)$ iff $ok(T_g)$.
]) <tf-lem-types>
#proof[Induction on `A`.
  - *`True`, `False`.* $T_s = T_g$.
  - *`P ∧ Q`.* [T-Ind] keeps the head `And`. Its parts are evaluated one after the other on one private copy, and by (N2) agreement holds between them. Use the induction hypothesis.
  - *`Eq D a b`.* By (N1)–(N2) the ground runs of `a` and `b` succeed and their values agree. Values in flight are loan-free (`exec_wf`), so agreement of values is equality after valuation: $a_s alpha = a_g$ and $b_s alpha = b_g$. $T_s = "eq"(D, a_s, b_s)$, and valuation rebuilds `Eq` types with `eq`, so $T_s alpha = "eq"(D, a_g, b_g) = T_g$.
  - *`Id D t u`.* By (N1)–(N2) the ground runs of `t` and `u` succeed in agreement with the symbolic ones. The observation then ends every borrow. By (N4) and (A2), each symbolic observation under α equals the ground one after resolution, position by position: $r_s alpha = r_g$, and $w_s (pi) alpha = w_g (pi)$ for every position π; the same holds for `u`. So:
    - $T_s alpha$ is `and` of $"eq"(D, r_g, r'_g)$ and of $"eq"(T_pi, w_g (pi), w'_g (pi))$ over $pi in W_s$;
    - $T_g$ is the same over $pi in W_g$;
    - by @tf-lem-w (a) $W_g subset.eq W_s$; by (b) each conjunct over $W_s without W_g$ compares equal values, so it is `True`; by (c) the conjuncts' types agree;
    - `and` drops `True` conjuncts, and the truth of a conjunction does not depend on the order of its conjuncts.
]

#thm([Lemma], [call types], [
  Let `L` be a lemma of F with parameters $overline(x) : overline(A)$ and codomain `B`, called at a ground call point $Omega_g$ with arguments $overline(w)$. Let β be the ground instance with $beta(sigma_i) = w_i$ for a data parameter, and $beta(sigma_i) = u_i$ for a borrow parameter with $w_i = "borrow"_(ell_i) u_i$. Then each parameter type, and `B`, are true at the call site ([Call-type]) iff they are true at the ground instance.
]) <tf-lem-call>
#proof[
  - *Setup.* At the call site the types are evaluated in $Omega_g";" (overline(x) |-> overline(w))$, and at the instance in $Gamma beta";" phi beta$. The two states differ only below the parameter frame. At the instance the borrow parameters' loans sit in the cells $c_i$; at the call site they sit in the caller's places.
  - *Runs.* Apply `frame_local` with the parameter frame as the core. Its ports are exactly the cells: "`callRun` *is* the meta-model's CallRun" (`notes/lean-meta.md`). Each run made while evaluating a type at the call site is then the run at the instance, with the ports' final values substituted into the caller's frames. So results, and the final contents of the parameter frame's own positions, coincide.
  - *Borrow parameters.* An `Id` conjunct over a borrow parameter's owner compares, at the instance, the final contents of $c_i$. At the call site it compares the final contents of the owners of $ell_i$.
  - *One owner.* At a ground state a loan occurs at most once: only sealed programs may hold a loan twice (well-formedness condition 2, preserved by `exec_wf`), and a ground state has none. So $ell_i$ has one owner, reached through a chain of borrow contents, and its final content is $K[v]$ for the borrow's final value `v` and a context `K` that holds the hole once.
  - *Injectivity.* By `ctx_inj`, `K` is injective, so $"eq"(K[v], K[v'])$ is true iff $"eq"(v, v')$ is.
]

== The theorem <tf-thm-sec>

#thm([Theorem], [accepted programs of F are sound at every ground instance], [
  Let $cal(P) = d_1 dots d_m$ be a program of F whose definitions are accepted in order by [Def] and [Const]. Then for every $d_k$ and every ground instance β of $d_k$:
  (i) if $d_k$ is a data function, its body runs from its ground instance to completion without error, and the pop of its frame succeeds;
  (ii) if $d_k$ is a lemma, or a constant of proposition type, and its hypotheses at β are true, then its goal at β is true.
]) <tf-thm>

#proof[
  *The induction.* By induction on the pairs $(k, |beta(sigma_j)|)$, ordered lexicographically. $|v|$ is the size of the numeral that is $d_k$'s decreasing argument, read through the borrow for `&Nat`; it is 0 without `by`. Fix `k` and β, and assume (i) and (ii) for every smaller pair. A constant ($n = 0$) is checked by [Const] from the empty environment, without a case tree. A data constant's value is computed once, at checking time, and (ii) for a proof constant is the claim below with $alpha = emptyset$, as in @tf-cor-cons. The rest of the proof is about definitions with parameters, checked by [Def].

  *Callees are safe.* A data function called directly by the body of $d_k$ on its symbolic path is some $d_j$ with $j < k$, since a definition is checked against the ones before it, or it is $d_k$ itself. A call of $d_k$ in its own body passes, in position `j`, a strict subterm of $rho^*(sigma_j)$ ([Rec]). Under any α that respects the path, that is a numeral smaller than $beta(sigma_j)$. So the induction hypothesis makes every direct callee safe, as @tf-ass-n requires. Calls made inside a callee's run are that callee's business, covered by the induction hypothesis at its own instance. The same bound gives (ii) for recursive lemma calls.

  *The walk.* We follow $d_k$'s case tree $cal(L)$, from [Def], along β. Throughout we keep five things:
  - a node of the tree with its symbolic state $Omega_s$;
  - a valuation $alpha supset.eq beta$ that covers and respects $Omega_s$;
  - the ground state $Omega_g$ that the ground run of the body has reached;
  - agreement, $Omega_s agr(alpha) Omega_g$;
  - when $d_k$ is a lemma, the invariant (I): every proof binding $x : T$ of $Omega_s$ has $ok(T alpha)$.

  At the root, $Omega_s = Gamma";" phi^+$, $Omega_g = Gamma beta";" phi^+ beta$ and $alpha = beta$. Agreement is immediate, since $Omega_s beta = Omega_g$. (I) holds by @tf-lem-types, applied to each hypothesis in turn: its type at the generic state is true under β iff it is true at the ground instance, where it is true by assumption. The tail rules move down the tree:
  - *[Tail-let], [Tail-seq].* `t` is not a match on data (F4). By @tf-ass-n its ground run succeeds, agreement is kept, and (N3) covers the drop. (I) is kept: a proof bound by the `let` has a true type by the claim below.
  - *[Tail-match].* Both paths take the same arm: after [Access], the scrutinee's content has the same constructor on both.
  - *[Tail-split] on σ.* The ground run matches on the same place, whose content after [Access] is α(σ) by agreement. If $alpha(sigma) = ty("C")_i (overline(v))$, the ground run takes arm `i`, and we move to the tree's arm `i`, extending α by $alpha(sigma_(i j)) := v_j$. α respects $sigma := r_i$ and $(Omega_s [sigma := r_i]) alpha = Omega_s alpha$, so agreement and (I) carry over.
  - *[Tail-gen] on a sealed program `n`.* Extend α by @tf-gen and continue as for [Tail-split].
  - *[Tail-prop] (lemma bodies).*
    - With one arm (`And`, `True`), move to it. Its fields hold ⋆ at the field types, which are true, since $ok((P and Q) alpha)$ gives $ok(P alpha)$ and $ok(Q alpha)$.
    - With no arms the scrutinee's type is `False`, and (I) would give $ok(ty("False"))$. So no ground instance reaches this node, and there is nothing to prove. This is where ex falso is sound.
  - *[Tail-end] `t`.*
    - This is a leaf $(Omega'_s, v, A)$. [Def] gives $"pop"(Omega'_s, v)$ succeeding and $A equiv G'$, the goal refined along the path.
    - By (N1)–(N3) the ground run of `t` and the ground pop succeed. With the steps before, the ground run of the body has run to completion without error, since it follows the path of the walk one tail rule at a time; each segment ends by (N1). This is (i).
    - For (ii), `v` is a proof and the claim below gives $ok(A alpha)$. By @tf-lem-conv (b), $A alpha equiv G' alpha$.
    - $G' alpha = G beta$, because α respects the path's refinements and records (@tf-gen (b)) and `G` mentions only generic values. By @tf-lem-conv (a), $ok(G beta)$.
    - By @tf-lem-types at the root, the goal at the ground instance is true.

  *Claim (proof terms have true types).* Let $Omega_s agr(alpha) Omega_g$ with (I), and $Omega_s tack.r t ev star : A tack.l Omega'_s$ for a proof term `t` of F. Then $ok(A alpha)$. By induction on the derivation:
  - `refl` has type `True`.
  - $chevron.l h, k chevron.r$: [T-Ctor] types `h : P'` and `k : Q'` with $P' equiv P$ and $Q' equiv Q$. Use the induction hypothesis and @tf-lem-conv.
  - A proof variable has its stored type, true by (I). A proof constant `c` has its declared type ([T-Const]), true by the induction hypothesis (ii) for `c`, which comes earlier in the program.
  - *`let` and sequence inside a proof.* The proof runs on a private copy, and the machine never runs it. By @tf-ass-n, the same data steps run from $Omega_g$ succeed and keep agreement, so there are ground states in agreement at every intermediate state, and the induction hypothesis applies to the proof subterms there.
  - A match on a proof: as for [Tail-prop]. With no arms (under an annotation, [T-Match-erased]), the premise gives `h : False`, against (I), so the case is vacuous.
  - *A lemma call $L_j (overline(u))$ ([T-Call-proof]).*
    - The arguments evaluate at $Omega_s$ to $overline(w)_s$, ending at $Omega_(s 1)$. By @tf-ass-n the ground evaluation gives $overline(w)_g$ at $Omega_(g 1)$, in agreement.
    - The parameter types $T_i$ and the call's type `B'` are evaluated at $Omega_(s 1)";" (overline(x) |-> overline(w)_s)$. That state agrees with $Omega_(g 1)";" (overline(x) |-> overline(w)_g)$, so by @tf-lem-types each has the truth of the corresponding type at the ground call site.
    - A proof argument $u_i$ has type $A'_i equiv T_i$, which is true under α by the induction hypothesis and @tf-lem-conv. So the ground call site's hypotheses are true, and by @tf-lem-call so are those of the ground instance $beta_j$ of $L_j$, with $beta_j (sigma_i) = w_(g, i)$.
    - The pair $(j, |beta_j|)$ is smaller than the current one: $j < k$, or $j = k$ and [Rec] made the decreasing argument a strict subterm. So the theorem's induction hypothesis (ii) makes $L_j$'s goal at $beta_j$ true.
    - By @tf-lem-call, `B'` at the ground call site is true, and by @tf-lem-types, $ok(B' alpha)$.
]

Termination is not a separate assumption. The ground run's segments end by (N1). (N1) rests on the mechanised structural half (`exec_total`, `termination_of_calls`: a run terminates if every call it makes does), and the induction supplies the calls. This is the recursive half that the general termination statement in `GuardTerm.lean` lacks, obtained here from [Rec] under α. Its cost is that it is only as strong as @tf-ass-n.

== Corollaries <tf-cors>

#thm([Corollary], [consistency of F], [
  No closed term of F has type `False`. More generally:
  - if a closed proof term `t` of F is typed from the empty environment, $epsilon tack.r t ev star : A tack.l Omega'$, after the definitions of an accepted program, then $ok(A)$;
  - every accepted constant of proposition type is true.

  In particular no closed term has type `Eq Nat Z (S Z)`, which computes to `False`.
]) <tf-cor-cons>
#proof[The empty state is ground, and $epsilon agr(emptyset) epsilon$ holds with (I) vacuous. The claim in the proof of @tf-thm, with $alpha = emptyset$ and @tf-thm itself supplying the lemma calls, gives $ok(A)$. `False` is not true, and truth is invariant under conversion (@tf-lem-conv (a)), so $A equiv.not ty("False")$.]

#thm([Corollary], [adequacy of `Id`], [
  If a lemma $L : Pi(overline(x) : overline(A)). ty("Id") D thin t thin u$ of F is accepted, then at every ground instance whose hypotheses are true, `t` and `u` have equal observations: the same result and the same final contents of every place either of them changes.
]) <tf-cor-adeq>
#proof[By @tf-thm (ii), $"and"("eq"(D, r, r'), "eq"(T_pi, w_pi, w'_pi), dots)$ is true. At a ground state, `eq` on two numerals is `True` iff they are equal, and `Unit` has one value. By @tf-lem-w (b), every place that `t` or `u` changes is observed.]

#thm([Corollary], [stability for F, at ground valuations], [
  For a term of F run at $Omega_s$ and at $Omega_g$ with $Omega_s agr(alpha) Omega_g$, the decisions of Conjecture 3 (stability, §7) are:
  (1) the same erasures and the same matches decided by the type of a proof, read from declared types and constructor names, which F never changes;
  (2) no stuck blocks on either path;
  (3) no arm is checked at a ground instance, where every match takes its arm; what soundness needs of item (3) is @tf-thm;
  (4) the same class and [Close] row for each call, read from the callee's declared codomain;
  (5) the same type for each observed place (@tf-lem-w (c));
  (6) $W_g subset.eq W_s$, and each conjunct over $W_s without W_g$ becomes `True` under α (@tf-lem-w, and the proof of @tf-lem-types).
]) <tf-cor-stab>

Conjecture 3 at refinements that are not ground, such as $sigma := ty("S") sigma'$, is not proved here. Soundness only needs its instances at ground valuations.

== Naturality fails without F5 <tf-drop>

The probe `ochr/core/lean/Scratch/DropProbe.lean` (5 of 5 verdicts as described, with and without D53) contains
```
def Bad2 (n : Nat) (b : Nat) (x : &Nat) : Unit := ( let a = 0; x := Pick(n, &a, &b); let z = b; () )
```
- *Symbolic path.* It is accepted at its generic call. At the abstract `n`, `Pick` closes off, and its hole $"loan"_k$ sits in the fills of both `a` and `b`. Reading `b` ends `k`, because [Access] ends every loan inside the content, sealed programs included. So `x` holds ⊥ and `a` holds data when `a` goes out of scope, and the [Drop] succeeds.
- *Ground path, `Bad2(0, 5, &y)`.* `Pick` returns a borrow of `a`, and `b` holds no loan. Reading `b` ends nothing, and `a` goes out of scope while `x` still borrows it: "[Drop] a goes out of scope while it is borrowed".
- *At `n = 1`* it runs.
- *The same with a local `let x = &c` declared before `a`* (`Bad3`).

The symbolic path ended a borrow earlier than the ground path, which (A2) allows. An earlier end is exactly what lets a later [Drop] succeed, so (N1) and (N3) fail.

*Why F5 excludes it.* Without assignments of borrows, a borrow value is created by `&p`, which needs `p` to exist, and is then bound by `let`, moved into another `let`, passed to a call, or returned. A borrower is therefore always declared after every place it borrows, and is dropped before them on both paths. A borrow passed to a call is dropped when the callee's frame pops, which happens before the caller's locals are dropped. So when the ground path drops a place, no live borrow into it remains, and the symbolic path has ended at least as much (A3). This is an argument, not a proof, and it is part of @tf-ass-n.

*Consequences for the paper.*
- The clause "if the run of tα ends, it ends without error" of the naturality conjecture is false for the full rules.
- So is "accepted programs do not go wrong when run", beyond the fuzzer's generator, which does not assign returned borrows into variables declared earlier.
- We see no route from this to a closed proof of `False`. The model reads a run through its resolution, and resolution does not see a [Drop] error. But the rules should change, or state the restriction. The options are in the team notes: keep other owners lent after an over-approximate end, as lexical lifetimes do; let a ground [Drop] end a live borrower, as non-lexical lifetimes do; or adopt F5.

== What would remove the assumption <tf-remains>

+ *Prove @tf-ass-n for F.* This is item M4 of `notes/typed-fragment-plan.md`: a simulation, rule by rule, between the typing judgement's symbolic run and the ground machine, with agreement as the relation. It uses property 7 at every [End], `close_*` at every [Close], and the frame lemma at every call. Its three risks are:
  - F5's sufficiency for (N1) and (N3);
  - (N4) through [Seal] with inert loans;
  - the preservation of (A4).
+ *Lift the mechanised lemmas to the current rules.* Moves (ghosts); [Close] without the `Unit` row; normalisation at every refinement and [End] rather than when states are compared.
+ *Widen F.* Each addition brings back a decision of Conjecture 3:
  - stuck blocks: their captures and modes;
  - closures and Π-values: class, captured types, [Conv-fun];
  - user inductives and pairs: disjointness and injectivity in `eq`, and matches on several-constructor proofs;
  - type families: generalisation types, where A1 lives;
  - `J` and `rewrite`: transport, and the stuck casts of D56.

*Where F's restrictions are used.*
- F1 and F2: @tf-gen (a) and (c) (the closed type of a sealed program); @tf-lem-w (c).
- F3: @tf-lem-w (a) (every occurrence in a statement is reached).
- F4: the walk has no stuck blocks, and every non-tail term is typed without [Split].
- F5: @tf-ass-n's (N1) and (N3), through @tf-drop.
- F6: @tf-thm (i), since a data function's run never depends on the truth of a hypothesis.
