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

## 3. Subsumption rule for stuck eliminators

**What:** When both sides of a subtype check are eliminations of the same inductive type and the subject is neutral, instead of treating the elim as opaque, virtually case-split on the subject's possible constructor shapes and check the subsumption in each branch.

```
n : Nat_ neutral
LHS = Fin n               = stuck(n; zero→Bot; succ→sCase n)
RHS = Fin (succ_ n)       = sCase n                          -- already reduced

Split on n:
  case n = zero_  : LHS = Bot,           RHS = Fin one_       → Bot ⊑ Fin one_  ✓ (S-BotL)
  case n = succ_ k: LHS = Fin (succ_ k), RHS = Fin (succ_ succ_ k) → recurse / coinductive close
```

**Why it matters:** Unblocks #2 (and the analogous parametric reasoning for Vec, List, every other index-recursive type). Closes a real gap between the structural algorithm and what the declarative subtype relation already endorses.

**Blocker:** Implementation work. Needs a constructor-signature dispatcher per inductive type, careful coinductive closure to avoid infinite split, and integration with the seen-set. Cousins: bisimulation up-to-context (Brandt-Henglein style, which Och already does for `fix`), dependent-pattern-match coverage checking. Doable.

---

## 4. Inhabitation-as-subsumption: `(∀x. x:A → x:B) ⟹ A ⊑ B`

**What:** The general law that A is a subtype of B iff every inhabitant of A is also an inhabitant of B. Today's ⊑ is sound w.r.t. inhabitation but incomplete — A might semantically subset B without the structural check noticing.

**Why it matters:** This is the *meaning* of subtyping that all the other rules are trying to approximate. Getting it as a derivable property would mean Och's algorithmic ⊑ matches the natural mathematical reading. #1, #2, and many other gaps would dissolve as instances.

**Blocker:** Undecidable in general — "every inhabitant" is universal quantification over a possibly-infinite type. Realistic paths to *partial* satisfaction:

- **Decidable approximations** via structured rules. #3 is one such approximation for inductive types. More rules of similar character (functional types, Σ-types, μ-types) would extend coverage.
- **Elaboration-time lemmas.** A separate proof language where users discharge `Fin n ⊑ Nat_`-style obligations once, register them, and the checker trusts them at use sites.
- **Coercion system.** Subsumption is implicit only at coercion sites where a registered coercion function exists. Doesn't give silent subsumption but recovers the practical effect.

Full equivalence (∀-inhabitation ⟺ ⊑) probably requires leaving decidable type-checking — observational equality, quotients, or theorem-prover-style obligations. Treat as a north star, not a deliverable.
