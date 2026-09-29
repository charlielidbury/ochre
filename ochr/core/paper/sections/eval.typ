#import "../style.typ": *

Definitional equality in Ochr is normalisation by one deterministic machine. With effects, rewriting-anywhere is not confluent: evaluating `(λy. (x := 2; y))(x := 1)` argument-first and substituting-first leave `x` holding different numbers. A fixed call-by-value order restores uniqueness, and the machine then plays the role that normalisation by evaluation plays for pure type theories @nbe: two terms are definitionally equal when the machine sends them to the same normal form. On concrete inputs it is an ordinary interpreter. On abstract inputs it runs until it has to inspect an abstract value, and the question the rest of this section answers is what it returns then.

The judgement is big-step: `⟨Ω, t⟩ ⇓ ⟨Ω', v⟩` runs `t` from environment `Ω` to value `v` and environment `Ω'`, and a run may instead be _stuck_ (it needs to inspect a neutral) or fail with a borrow error.

== Borrows

#figure(kind: image, supplement: [Figure],
  block[
    #rules(
      infer(name: "End", $"borrow"_ell v "in" Omega$, $Omega arrow.squiggly Omega["borrow"_ell v := bot][v slash "loan"_ell]$),
      infer(name: "Borrow", $v = "content"(Omega, p)$, $cfg(Omega, \&p) arrow.b.double cfg(Omega[p |-> "loan"_ell], "borrow"_ell v)$),
    )
    #rules(
      infer(name: "Read", $v = "content"(Omega, p) "borrow-free"$, $cfg(Omega, p) arrow.b.double cfg(Omega, v)$),
      infer(name: "Move", $"content"(Omega, p) = "borrow"_ell v$, $cfg(Omega, p) arrow.b.double cfg(Omega[p |-> bot], "borrow"_ell v)$),
      infer(name: "Assign", $cfg(Omega, t) arrow.b.double cfg(Omega_1, v)$, $Omega_2 = "drop"(Omega_1, "content"(Omega_1, p))$, $cfg(Omega, p := t) arrow.b.double cfg(Omega_2[p |-> v], ())$),
    )
  ],
  caption: [Borrows. Every rule that accesses a place `p` is preceded by [Access]: end every borrow whose loan lies on the path to `p` or inside its content (for a match, which inspects only the head: on the path, at the head, or anywhere inside a neutral head). `drop` ends the borrows inside a dropped value and fails on a live loan in a dropped owned value.],
) <fig-borrows>

@fig-borrows gives the rules for borrows. They are Aeneas's, simplified by treating loans as variables.

*Ending* a borrow [End] replaces it by `⊥` and substitutes its content for its loan. There is no side condition: if the content itself contains loans (because something has reborrowed part of it), they travel with it, and the reborrows remain valid. Ending is allowed at any time; the machine does it lazily, when a place is accessed. [Access] makes every access exclusive: before a place is read, borrowed, assigned or matched on, every borrow whose loan lies on the path to it or inside its content is ended. A borrower that has been ended holds `⊥`, and any later use of it is an error. This is the whole of the borrow checker: exclusivity of mutable borrows is not a separate analysis but a consequence of running the program.

*Reading* a place copies its content if the content is borrow-free [Read] and moves it out otherwise [Move]. Data is therefore copied, and borrows, which must stay unique, are moved; reborrowing is explicit (`&*x`). A compiled program should implement a last-use copy as a move, so that `AddM` performs no allocation; an affine usage discipline outside the core would license this, but we have not defined it, nor proved that the compiled program agrees with the machine (@sec-discussion). Inside types copying is essential: `Id Nat (Add(x, x)) x` must at least be a well-formed statement, and so must `x + x = 2 · x`.

== Calls and matches

A call evaluates its arguments left to right, each into a temporary of the current frame, so that [Access] can see and end them: `f(&x, &x)` ends the first borrow when the second is taken, and the call then fails reading `⊥`. It then pushes a frame binding the parameters, runs the body, and pops the frame, dropping its bindings. Popping a frame that still lends out one of its owned places is an error: something would outlive the place it borrows.

Types and proofs are erased at runtime, and the machine treats them accordingly: an erased term is evaluated on a _private copy_ of the environment, argument evaluation included, and the copy is then discarded. Which terms are erased is read from syntax and declarations, never from a normal form (@sec-typing): a call is erased when its callee's codomain _term_ is a sort or has declared sort `Prop`, and any other term when it stands in a type position or its declared type has sort `Prop`. A proof may use mutation freely on its copy, but it cannot affect the real environment, so running a proof and skipping it are indistinguishable and the machine skips it, returning `⋆`. A call whose head is itself a neutral (an abstract function, or a sealed program) is stuck at once.

`match p { Z => t, S y => u }` inspects the head of `p`'s content. `Z` selects the first arm, and `S v` selects the second with `y` standing for the sub-place `p.1`. Through a borrow, `match *x` leaves the successor in the borrowed content, so `&y` then reborrows the predecessor field in place: `x ↦ borrow₀ (S loan₁)` and the new borrow is `borrow₁ v`. If the head is a neutral, the run is stuck. A match on a proof never inspects it, since every proof is `⋆`: whether a match is on a proof is read from the declarations of the constructors its arms name, and such a match is decided by the proof's type (@sec-typing-prop).

== Functions and closures <sec-eval-closures>

A `fix` evaluates to a _closure_ $chevron.l overline(kappa) tack.r kw("fix") f (overline(x) : overline(A)) : B dots := t chevron.r$: its code with the current values $overline(kappa)$ of its free variables, in binding order, each with its binding's declared type and proof flag. A Π-type is formed the same way, and a top-level function is just its name. Capturing is reading: a borrow that lends a captured variable out is ended first, and the closure keeps a copy. So what can be captured is what can be copied (data, proofs, types, closures, abstract values and sealed programs), while capturing a borrow or a moved-out place is an error; a `λ` inside a function that takes `x : &Nat` copies the number first, as in `let n = *x; let f = (λ(y : Nat) : Nat => n)`, and may still take borrows as parameters, as `λ(z : &Nat) : Unit => AddM(z, 0)` does.

Captures are therefore snapshots, by the mechanism that forms a type once (@sec-typing): there is no capture by reference and no closure that mutates its environment. A closure holds no borrow, so it is copied like data, but it cannot be an inductive field or be borrowed; a borrow inside a closure would be a borrow stored inside a value (@sec-discussion). Calling a closure pushes one frame holding its captured values, itself if it is recursive, and the parameters. Two function values are convertible when their Π-types are, their captured values are pairwise, and their generic calls have the same observation (@app-conv). The only capture of places, as in Rust's closures, is by a closed-off stuck match (@sec-eval-seal), and it makes them the arguments of a call.

== Closing off

When the body of a call is stuck, the call itself is stuck, and so is everything waiting for it. A pure type theory would return the stuck call as a neutral term. An effectful call cannot simply be returned: part of what it produces is the final content of the places it borrowed, and the caller's environment needs those contents before it can continue. We _close off_ the call instead.

#figure(kind: image, supplement: [Figure],
  block[
    $ "the body of" f(w_1, ..., w_n) "is stuck," quad w_i = "borrow"_(ell_i) u_i " for " i in I, quad u_i "loan-free" $
    $ L := "let" c_i = u_i quad (i in I) quad quad C := f(a_1, ..., a_n), quad a_i = cases(\&c_i & "if " i in I, w_i & "otherwise") $
    #table(
      columns: 3, stroke: none, align: left, inset: 4pt,
      table.hline(stroke: 0.5pt),
      [result type], [result], [each $"loan"_(ell_i)$ becomes],
      table.hline(stroke: 0.4pt),
      [`Unit`], [`()`], [$seal("L; C; " c_i)$],
      [borrow-free $D$], [$seal("L; C")$], [$seal("L; C; " c_i)$],
      [$\&T$], [$"borrow"_k seal("L; let r = C; *r")$], [$seal("L; let r = C; *r := " "loan"_k "; " c_i)$],
      table.hline(stroke: 0.5pt),
    )
  ],
  caption: [[Close]. The partial run of the body is discarded; the borrows `borrow_ℓᵢ` are consumed; `k` is fresh.],
) <fig-close>

@fig-close gives the rule. Take the call at the point where its arguments have been evaluated. For each borrow argument `borrow_ℓᵢ uᵢ`, the canonical program `L; C` recreates the situation the call was in, but with the borrowed contents owned by fresh local places `cᵢ`: it moves each `uᵢ` into `cᵢ` and calls `f` on `&cᵢ`. This program is closed. Running it and reading `cᵢ` afterwards computes exactly what the call would have left behind the borrow, so each loan is filled with the sealed program #seal(`L; C; cᵢ`). The call returns the sealed program #seal(`L; C`), or `()` if its result type is `Unit`.

Sealed programs compute what Aeneas's backward functions compute, in the source language. For `AddM(borrow₀ σ, y)`, the loan receives #seal(`let c = σ; AddM(&c, y); c`), which is the body of `Add(σ, y)`, where Aeneas's translation would emit `add_m_back σ y`. This correspondence is proved for the first-order fragment of @sec-meta-mech (property 5), and it is narrower than Aeneas. A sealed program belongs to one call, not to a region of the callee's signature, so a borrow-returning call's hole goes into every borrowed argument (@sec-intro-scope). It is computed by unfolding the callee, where Aeneas reads the signature. And it has no counterpart for loops or for borrows stored in data. Nothing about the call is lost: when `σ` is later refined, the sealed program runs again.

*Returning a borrow.* If `f` returns a borrow, the contents of the places it borrowed are not determined when the call returns: they depend on what the caller will write through the returned borrow before it ends. The rule therefore returns a borrow of a fresh `k`, whose content is the sealed program for the returned borrow's initial content, and fills each `loan_ℓᵢ` with a sealed program that has a _hole_: it writes `loan_k` through the returned borrow before reading `cᵢ`. Because loans are variables, the hole is filled by the ordinary [End] rule: when the caller drops the returned borrow with final content `w`, `w` is substituted for `loan_k`. This records only the _final_ value written through the returned borrow, which is all that Aeneas's backward function takes as input, and the hole plays the role of Aeneas's region abstraction for this call. If `f` has several borrow arguments, the hole occurs in each of their sealed programs, and one [End] fills them all.

The precondition that each `uᵢ` is loan-free is guaranteed by [Access], which ended those loans when the argument was read or borrowed. Without it, a live loan would be copied into a sealed program and survive the borrow that binds it.

== Sealed programs and refinement <sec-eval-seal>

Values are kept in normal form. The normal form of a sealed program #seal(`L; C; K`) is obtained by running it from the empty environment, with one restriction: its _head call_ `C` may not itself be closed off (calls made inside `C`'s body may). This is the analogue of the guard on fixpoint unfolding in the calculus of inductive constructions. Without it, a sealed program would re-close into itself forever; with it, a sealed program either runs to a value or stays exactly as it is. A loan whose borrow lives outside the run (a hole whose returned borrow is still live) is _inert_: the run treats it like an abstract value. A borrow error during normalisation is a type error at the point that triggered it. When a case split has generalised a sealed program to an abstract value (@sec-typing), every later derivation of the same closed program normalises to that value.

A _refinement_ substitutes a constructor pattern for an abstract value, `σ := Z` or `σ := S σ'`, when a case split learns it (@sec-typing). Substitution into a sealed program is followed by normalisation, which runs the sealed program again. For `N(σ) = ⌈let c = σ; AddM(&c, 0); c⌉` and `σ := S σ'`, the head call `AddM` now unfolds, matches the successor, reborrows the predecessor, and makes the inner recursive call, which is stuck on `σ'` and is closed off; so `N(S σ') = S N(σ')`. Normal forms of this shape are what makes the induction of @sec-overview go through. The key property, a conjecture of @sec-meta, is that refinement commutes with closing off: refining the arguments of a closed-off call and re-normalising gives the same normal form as closing off the call on the refined arguments.

*Stuck blocks.* A stuck `match` that is not the body of a call is closed off in the same way, as the body of a call to an anonymous function of its free places. Pattern variables are first resolved to the sub-places they denote, and the function takes the resulting maximal places the way Rust infers closure captures: a place the match moves out of, in any arm, is moved in; a place it writes or borrows is passed by borrow; a place it only reads is copied. The function's result type is the match's type, which must agree across the arms or be annotated (`let x : A = match …`). Only a match whose arms have been type-checked is closed off, including a match inside a type, and a stuck block is erased exactly when each of its arms is a declared proof. This covers stuck matches inside types and, during checking, a stuck match that is followed by more code (@sec-typing).
