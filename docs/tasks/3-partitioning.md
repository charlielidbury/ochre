# Problem

Layer 3: Abstract Inputs and Partitioning
Task 3.1: Define the partitioning mechanism. Formalize how the abstract interpreter handles application of an abstract Church-encoded value to branch arguments. Specifically: when n : Nat (abstract) is applied as n Bool true (λ_. false), define how the interpreter partitions into the true and false branches with narrowed environments. Verification: show that the partition of Nat via isZero produces exactly {0} and {succ k | k : Nat}, and that these are exhaustive.
Task 3.2: Verify typing of abstract test cases. Using the rules from 2.1 and the partitioning from 3.1, derive the judgments for §6.2 (ascribed inputs). Key case: v1 Nat (λ(n: Nat). λ(arr: Array n Nat). n) ⇝ Nat where v1 : Vec Nat is abstract. Verification: derivation trees. Depends on 2.1, 3.1.

# Solution
// put your answer here