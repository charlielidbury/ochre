# Lemma: Values Have Erased Domains

## Statement

If `M ⟶ V` (under the rules with deep domain erasure in E-Fun), then
all domain annotations in V are ⊤. Formally: `erase(V) = V`.

## Proof

By induction on the derivation of `M ⟶ V`.

**Case E-Top:** V = ⊤. erase(⊤) = ⊤ = V. ∎

**Case E-Fun:** V = (x: ⊤) → erase(M).
erase(V) = erase((x: ⊤) → erase(M)) = (x: ⊤) → erase(erase(M)).
Since erase is idempotent (erase(erase(M)) = erase(M)):
erase(V) = (x: ⊤) → erase(M) = V. ∎

(Idempotence of erase: by structural induction on M. erase replaces all
domains with ⊤; applying erase again finds all domains already ⊤.)

**Case E-App:** M ⟶ (x: ⊤) → B', N ⟶ N_v, B'[x ≔ N_v] ⟶ V.

By IH on M: erase((x: ⊤) → B') = (x: ⊤) → B'. So B' = erase(B')
(the body of the function value is already erased).

By IH on N: erase(N_v) = N_v (the argument value is already erased).

Now B'[x ≔ N_v]: B' has all domains ⊤ (erased). Where does x appear
in B'? Since B' = erase(B_raw) for some original body B_raw, and erase
replaces all domains with ⊤, x does NOT appear in any domain position
of B'. x only appears in body (non-domain) positions.

Substituting N_v for x: N_v has all domains ⊤ (by IH). Placing N_v in
body positions of B' (which already has all ⊤ domains) gives a term with
all ⊤ domains.

Then B'[x ≔ N_v] ⟶ V, and by IH on this sub-derivation, erase(V) = V. ∎

**Case E-Asc:** M ⟶ V. By IH, erase(V) = V. ∎

## Corollary

For any value V produced by ⟶, all function subterms in V have the form
`(x: ⊤) → N` where N also has all ⊤ domains. This means:

1. The S-Fun contravariant domain check when comparing V ⊑ R is always
   `domain(R) ⊑ ⊤`, which is S-Top. Contravariance is trivially satisfied.

2. The only non-trivial comparisons are covariant body comparisons,
   where the more-precise concrete value helps rather than hurts.

∎
