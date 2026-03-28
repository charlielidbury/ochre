# Problem

Layer 2: Typing Rules
Task 2.1: Define the abstract evaluation judgment Γ ⊢ e ⇝ τ. Write natural deduction rules for: variable, lambda, application, ascription, Type. Verification: the rules must be deterministic — given Γ and e, there is exactly one τ (the most precise type). State and verify this uniqueness property for each rule.
Task 2.2: Verify typing of concrete test cases. Using the rules from 2.1, derive the judgments for every line in §6.1 (concrete instantiation). Each EXPECT annotation becomes a specific judgment to derive. Verification: produce the derivation tree for each. This depends on 2.1 and 1.1.
Task 2.3: Verify typing of transparency tests. Derive the judgments for §6.4: id Nat 3 ⇝ 3 (not Nat), id_ascribed Nat 3 ⇝ Nat (not 3), double 3 ⇝ 6. These specifically test that transparency propagates precision and ascription blocks it. Verification: derivation trees showing the precise type in each case. Depends on 2.1.
Task 2.4: Verify rejection of failing tests. Show that each test in §6.3 cannot be given a type / results in a type error. For each BAD case, show where the derivation gets stuck or produces a contradiction. Verification: for each case, identify the exact rule that fails and why. Depends on 2.1 and 1.1.

# Solution
// put your answer here