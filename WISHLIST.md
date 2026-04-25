# Wishlist

Things Ochre's type system *should* support but doesn't (yet). Each entry: what we want, why it matters, what's blocking it today.

This file is aspirational. Not a roadmap — items here may take years, may need fundamentally new machinery, or may turn out to require trade-offs that make them undesirable in their stated form. Use it to remember the direction of travel.

---

## 1. `Fin n ⊑ Nat_` at the type level

**What:** Every value of type `Fin n` should also be a value of type `Nat_`. Today, value-level subsumption gives us `n_ ⊑ Fin m_` for specific naturals (a Nat literal can be passed where a Fin is expected). The reverse — passing a `Fin n` value where a `Nat_` is expected — is rejected.

**Why it matters:** Ergonomics. Fin's whole purpose is "Nat with an upper bound", so a Fin-indexed value should be usable anywhere a Nat is expected without coercion. Today users have to thread value-level subsumption manually. See `lean/Och/Std/DFin.lean:113-116` for the explicit "Option F tradeoff" comment.

**Blocker:** The current encoding (Option F) makes Fin's structural shape distinct from Nat_'s. Algorithmic subsumption is purely structural, so they don't relate. Adding `Fin n ⊑ Nat_` would require either:
- A different encoding that puts Fin structurally below Nat_ (would likely break the constants ⊑ both story).
- A non-structural subsumption rule (see #3 below).

---

## 2. Parametric width-monotonicity: `λn:Nat_. Fin n ⊑ λn:Nat_. Fin (succ_ n)`

**What:** Fin's width-monotonicity (`Fin a ⊑ Fin b` when `a ≤ b`) should hold *parametrically*, under a fresh n bound by an enclosing λ — not just at concrete numerals.

**Why it matters:** Without this, generic functions over Fin can't grow their bound. Every dependent operation that needs to widen a Fin index has to be specialised at concrete sizes. Breaks compositionality of Fin/Vec/Array machinery.

**Blocker:** When n is a neutral, `Fin n` reduces to a stuck eliminator (`n.elim(zero→Bot; succ→sCase n)`) that can't fire. The structural subtype check has no path through stuck eliminators against a non-stuck RHS. Needs the rule in #3.

---

## 3. Subsumption through stuck eliminators

**What:** Today, when one or both sides of a subtype check is an elimination of an inductive type whose subject is a neutral, the eliminator can't fire and the algorithm has no path forward. We want the algorithm to recognise that such a stuck elim is still *semantically* the union of its branches, and close the subsumption when the inhabitation-equivalent claim holds.

Concretely: judgments like `Fin n ⊑ Fin (succ_ n)` under fresh `n:Nat_` are sound (inhabitation-true) but currently rejected because `Fin n` is stuck while `Fin (succ_ n)` reduces.

**Why it matters:** Unblocks #2, and the analogous parametric reasoning for Vec, List, and every other index-recursive type. Closes a real gap between the algorithmic checker and the declarative subtype relation it's meant to implement.

**Blocker:** Open design problem. The challenge is recovering structural information from a stuck elim without sacrificing decidability or termination, and doing so uniformly across inductive types rather than per-type. Solutions exist in adjacent settings (bisimulation up-to-context, coverage checking, η-rules for inductives) but no off-the-shelf adaptation that fits Och's structural-with-recursion ⊑ cleanly.

---

## 4. Inhabitation-as-subsumption: `(∀x. x:A → x:B) ⟹ A ⊑ B`

**What:** The general law that A is a subtype of B iff every inhabitant of A is also an inhabitant of B. Today's ⊑ is sound w.r.t. inhabitation but incomplete — A might semantically subset B without the structural check noticing.

**Why it matters:** This is the *meaning* of subtyping that all the other rules are trying to approximate. Getting it as a derivable property would mean Och's algorithmic ⊑ matches the natural mathematical reading. #1, #2, and many other gaps would dissolve as instances.

**Blocker:** Undecidable in general — "every inhabitant" is universal quantification over a possibly-infinite type. Realistic paths to *partial* satisfaction:

- **Decidable approximations** via structured rules. #3 is one such approximation for inductive types. More rules of similar character (functional types, Σ-types, μ-types) would extend coverage.
- **Elaboration-time lemmas.** A separate proof language where users discharge `Fin n ⊑ Nat_`-style obligations once, register them, and the checker trusts them at use sites.
- **Coercion system.** Subsumption is implicit only at coercion sites where a registered coercion function exists. Doesn't give silent subsumption but recovers the practical effect.

Full equivalence (∀-inhabitation ⟺ ⊑) probably requires leaving decidable type-checking — observational equality, quotients, or theorem-prover-style obligations. Treat as a north star, not a deliverable.
