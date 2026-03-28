# Problem

Layer 1: Subtyping
Task 1.1: Define the subtyping relation ⊑ on terms. Given two terms τ₁ and τ₂, define when τ₁ ⊑ τ₂ holds. Must handle: reflexivity, transitivity, pointwise function subtyping (contravariant input, covariant output), and Type. Verification: the relation must satisfy true ⊑ Bool, false ⊑ Bool, 3 ⊑ Nat, true ⋢ Nat, succ 2 ⋢ 2, unit ⊑ Unit, and Pair Nat Bool ⋢ Pair Bool Nat (these are directly from the test case §6.3). Write out the derivation tree for each.
Task 1.2: Verify subtyping for compound types. Using the relation from 1.1, derive: emptyArray Nat ⊑ Array 0 Nat, consArray Nat 0 10 (emptyArray Nat) ⊑ Array 1 Nat, emptyArray Nat ⋢ Array 1 Nat, and consArray Nat 0 10 (emptyArray Nat) ⋢ Array 2 Nat. These require β-reduction of Array followed by subtyping. Verification: produce derivation trees. This task depends on 1.1.
Task 1.3: Verify subtyping for dependent types. Derive: dpair Nat (λ(n: Nat). Array n Nat) 2 arr ⊑ Vec Nat for a concrete arr : Array 2 Nat. This exercises dependent pair subtyping where the second component's type depends on the first. Verification: produce the derivation tree. Depends on 1.1 and 1.2.

# Solution
// put your answer here
