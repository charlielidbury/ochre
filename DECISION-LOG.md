# Decision Log

Record significant design decisions here. Each entry should explain WHAT was
decided, WHY, and what alternatives were considered.

Format:
```
## [Date] [Agent-ID] Short title

**Decision:** What was decided.

**Why:** The reasoning.

**Alternatives considered:** What else was on the table.

**Implications:** What this constrains or enables going forward.
```

---

## 2026-03-31 och-md-20260331-123613 Monotonicity fails for dependent domains

**Decision:** Monotonicity of abstract evaluation does NOT hold in general
for the current Och rules. This is not a proof gap — it is a genuine
semantic failure demonstrated by counterexample.

**Counterexample:**
```
f = λ(A:Type). λ(x:A). x

Under A:Type:  f A  ⇝  λ(x:Type).x    -- narrower set (works on everything)
Under A:Nat:   f A  ⇝  λ(x:Nat).x     -- wider set (only needs to work on Nat)
```
`λ(x:Nat).x ⋢ λ(x:Type).x` because S-Lam contra requires `Type ⊑ Nat`.

This is the Prop 5.2.9 phenomenon in pure Och: narrowing the context variable
A from Type to Nat WIDENS the resulting function type, because:
- Narrowing A narrows the lambda's domain (covariant in context)
- Narrower domain → wider function set (contravariant in subtyping)

**Why this matters:** Monotonicity is what makes Ochre's strong mutation
sound. Without it, narrowing a variable's type after mutation could
invalidate previously-checked typing judgments.

**Alternatives considered:**
1. Restrict variables from lambda domains — kills dependent types
2. Pointwise function subtyping (no direct domain comparison) — promising
3. Accept failure and restrict monotonicity to ground/fully-applied types —
   most practical, matches actual usage patterns
4. Modify the App eval rule to wrap results preserving monotonicity
5. Keep current rules and prove soundness without monotonicity (via
   closed-term simulation lemma)

**Implications:**
- The current subtyping rules (Task 1) are correct for the derivations in
  Tasks 1-3, but the S-Lam rule's contravariant domain causes problems for
  monotonicity when combined with dependent domain instantiation
- Soundness proof (Task 4.1) is blocked at the App case, which requires
  monotonicity to bridge concrete and abstract substitutions
- Any fix must preserve: `true ⊑ Bool`, `3 ⊑ Nat`, `succ ⊑ λ(_:Nat).Nat`,
  and all other derivations from Tasks 1-3
- Fixes #2 and #3 should be explored next
