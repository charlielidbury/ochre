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

## 2026-03-31 och-md-20260331-123613 Two sources of anti-monotonicity

**Decision:** There are TWO separate sources of anti-monotonicity, not one.

1. **Domain anti-monotonicity**: dependent domains + contra subtyping.
   Counterexample: `λ(A:Type).λ(x:A).x` under A narrowing.
2. **Body anti-monotonicity**: anti-monotone functions (e.g., Not) used in
   ascription. Counterexample: `(Not B : B)` under B:Bool→B:true.
   This IS Prop 5.2.9 — a body-level phenomenon, not domain-level.

**Why:** Earlier analysis conflated these. Separating them reveals that
domain erasure fixes #1 but not #2. #2 is more fundamental.

**Implications:** Any fix strategy must address both independently.

## 2026-03-31 och-md-20260331-123613 true = 0 at runtime

**Decision:** Domain annotations are erased at runtime (§4.1), so
`true = λ_.λa.λ_.a = 0` as runtime values. The spec's `true ⋢ Nat` is a
design choice about type identity, not a soundness requirement.

**Why:** Both `true` and `0` select their second argument. Domain annotations
(`f:X` vs `s:X→X`) are the only distinction, and these are erased.

**Alternatives considered:**
- Accept `true ⊑ Nat` (matches runtime, breaks user expectations)
- Two-level subtyping: strict (⊑ₛ) for users, relaxed (⊑ᵣ) for metatheory
- Add explicit tags to Church encodings to recover disjointness

**Implications:**
- For Ochre with algebraic data types, this issue vanishes (constructors
  are genuinely distinct, not Church-encoded)
- For Och specifically, the overlap is an artifact of Church encoding
- Two-level subtyping is the most promising approach: prove metatheory
  with ⊑ᵣ (monotone), present to users with ⊑ₛ (stricter)
- Runtime subtyping (⊑ᵣ) IS monotone — domain erasure eliminates the
  contravariance that causes domain anti-monotonicity
