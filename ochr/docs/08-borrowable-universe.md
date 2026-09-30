# 08. `Type₀` holds only runtime types; borrow anything in it

Written 2026-09-30 by team-lead. The user's decision, after asking why the hashmap cannot be generic in its value type: "go with moving Prop up and allowing function borrows", with a note that moving `Prop` up can be undone later if a reason is found. Recorded as D66.

## The problem
A generic `get_mut(m, k) : &V` needs `&V` for a type parameter `V : Type₀`. Today borrows are allowed only of data types (a rule written after reviewer-3 found Hurkens' paradox through `&Type₀`). That ban caught three different things at once:
- types: the real danger;
- functions: never designed;
- proofs: harmless, but swept along.
A parameter `V : Type₀` could be instantiated with any of them. It could even be `Prop`, since `Prop : Type₀`.

## The decision
1. **`Prop : Type₁`**, beside `Type₀` rather than inside it. This is Coq's arrangement: `Set` for computational types and `Prop`, both in `Type₁`. `Type₀` plays `Set`'s role. Universes stay non-cumulative, and `Prop` stays impredicative (a Π into `Prop` is in `Prop`).
2. **The borrow rule becomes one universe check: `&A` is well formed iff `A : Type₀`** (plus the existing `unsized` rule for views). With (1), everything in `Type₀` exists at runtime:
   - data types;
   - function types whose codomain is data or a function, since a Π into `Prop` lands in `Prop` and a Π into a universe lands above `Type₀`;
   - borrow types, which are handled by the existing rule that `&` appears only at the top of a declared type.
   So:
   - `&(Π(n : Nat). Nat)` is allowed;
   - `&V` for a type parameter `V : Type₀` is allowed;
   - `&P` for a proposition `P` is rejected automatically (`P : Prop`, not `Type₀`);
   - `&Prop` and `&Type₀` are rejected automatically.
   There is no separate "is this data?" test.
3. **Machine: nothing new.** A function value is a closure, and a place can hold one. [Access], [Borrow], [End] and [Assign] don't care what kind of value sits in the place. Calling through a borrow reads the place, and a call does not consume its function (D53). If a function with a function-typed borrow parameter gets stuck, [Close] makes the final content of that place a sealed program of function type. Calling that later is a call with an unknown head, which already closes off (D26).
4. **Equality of functions stays as it is.** It is by conversion (generic-call observation, D30), with no function extensionality. So `Id` over a borrowed function is provable only when both sides compute to the same function: weak, but not unsound.

## What changes for users
- Code generic over `A : Type₀` can no longer be applied to `Prop`. It would say `A : Type₁`, and a list of propositions needs its own declaration at `Type₁`. `Box(Prop)` becomes an ordinary universe error. The fuzzer's `--rules` family found that this was already against the rules and accepted anyway.
- Storing a function in data through a type parameter (`Box(Π(n : Nat). Nat)`, paper §4.3) stays allowed.

## Revisit if
A real use of `Prop` at `Type₀` appears. The fallback is Lean's arrangement (`Prop : Type₀`) plus a side condition: a type parameter the code borrows may not be instantiated with `Prop` or a universe, checked at instantiation like Rust's implicit `Sized`.

## Acceptance
- **Checked:**
  - borrow a closure, write a different closure through the borrow, and call through it, including a closure that captures;
  - a function with a function-typed borrow parameter that gets stuck and closes off;
  - a generic `Swap(V : Type₀)(a b : &V)`;
  - a generic bucket `GetMut(V : Type₀)(b : &Bucket(V), k, h) : &V`.
- **Rejected:** `&h` for a proof; `&P` for `P : Prop`; `&A` for `A : Type₁`; `Box(Prop)`; `PropInType : Type := Prop` (it becomes `: Type₁`).
- **Ledger rows,** each flipping a named witness:
  - `propUp`: `Prop : Type₀` restored brings back the `&V`-at-`Prop` witness;
  - `borrowUniverse`: the old data-only test restored flips the function-borrow witnesses to rejected, class completeness.
- **Fuzzer:** `--rules` expectations updated (function borrows and function-typed inductive parameters are now allowed), and the exec oracle covers function-typed borrow parameters.
- **In step:** RULES and DECISIONS (lead), and the paper (§3 borrow well-formedness, the universe line, §4.3), change together with the checker.
