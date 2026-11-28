import Ochr.Meaning.Lemmas

/-!
# Replacing an unknown by what it means: the substitution lemma for unknowns (docs/31 D77)

The counterpart, for unknowns, of `meanV_substLoan` / `run_substLoan` (`Lemmas.lean`, beside the
congruence lemmas `meanV_congr` / `run_congr`): under an assignment at which `ρ σ = ⟦r⟧`
(`Steps.RefineOk`), substituting `r` for `σ` in a value, a type or a program's text keeps the meaning
and the run. It is what `Steps.substEnv_abs_step_stmt` (a refinement's substitution over the whole
state) owes underneath: every position, stored type and record means the same, and a sealed program
whose text changed means the same before its re-run (whose meaning is [Seal]'s, `nfSealed_step`).

**Which proofs it reuses.** For a loan, `meanV_substLoan` is the congruence lemma (move to the
future fixed at `ℓ`) followed by `meanV_substSame` / `runT_substSame` (`RunSubst.lean`: at a future
where `loan ℓ` already means the filler, substituting it changes nothing, clause by clause). For an
unknown no congruence step is needed: the assignment already gives `σ` the refinement's meaning, so
the lemma IS the same-meaning substitution, with the atom `.abs σ` in place of `.loan ℓ`. That
induction does not look at which atom it replaces except in its base case, so the proof is
`RunSubst.lean`'s induction with the atom renamed, not a fifth induction, provided its base case
holds, the hypothesis `AbsFillOK` below. **Proved** (`RunSubstAbs.lean`: `meanV_substAbs`,
`run_substAbs`, standard axioms).

**The base case failed at the type the run gave an embedded value** (`absFill_shape_false`, until
the data-layer port): `run`'s `.val` clause typed `.abs σ` at `Δ σ` and every other data value at the
HINT, so `.val (.abs σ)` and `.val Z` meant the same where `ρ σ = 0` and were typed `Nat` and `err`;
the run-level lemma with whole results was false at the text `.val σ` itself. Way out 1 below is
taken: the run types an embedded value by what it is, and the base case now holds wherever
`DeltaOk` does (`absFill_shape`, kernel-checked). Where the
type is not read again, nothing changes: on the `SplitSubst` runs the meanings and even the whole
runs agree (`pred2_instance`), since a call reads its arguments' meanings only. The two ways out
that were open:
1. (taken) the run's `.val` clause types a number at `Nat` and a constructor value at the type its
   record names (for one that records its parameters, its own type `D(ps̄)`), as the checker types
   them. Then `AbsFillOK.shape` holds wherever `DeltaOk` does (a refinement of `σ` is a value of
   `σ`'s stored type, which is what `Δ σ` is the code of), and the lemma is the generalised
   `runT_substSame`.
2. state it up to types (result types and the types bindings store): then it is a new induction (a
   simulation between states whose binding types differ but whose meanings agree).
-/

namespace Ochr

mutual
/-- Replace every unknown `σ` by `r` in a value, inside sealed programs, closures and types too
(the pure half of the checker's `substV (.abs σ) r`; re-normalisation is a separate step). -/
def Value.substAbs (σ : Nat) (r : Value) : Value → Value
  | .abs σ' => if σ' = σ then r else .abs σ'
  | .succ v => .succ (Value.substAbs σ r v)
  | .tRef v => .tRef (Value.substAbs σ r v)
  | .borrow m v => .borrow m (Value.substAbs σ r v)
  | .gloan m v => .gloan m (Value.substAbs σ r v)
  | .tEq A a b => .tEq (Value.substAbs σ r A) (Value.substAbs σ r a) (Value.substAbs σ r b)
  | .clo cs t rd => .clo (Value.substAbsList σ r cs) (Term.substAbs σ r t) (Value.substAbsRd σ r rd)
  | .tPi cs t rd => .tPi (Value.substAbsList σ r cs) (Term.substAbs σ r t) (Value.substAbsRd σ r rd)
  | .sealed t => .sealed (Term.substAbs σ r t)
  | .ind ty c h ps fs => .ind ty c h (Value.substAbsList σ r ps) (Value.substAbsList σ r fs)
  | .tInd n as => .tInd n (Value.substAbsList σ r as)
  | v => v
termination_by structural v => v

def Value.substAbsList (σ : Nat) (r : Value) : List Value → List Value
  | [] => []
  | v :: vs => Value.substAbs σ r v :: Value.substAbsList σ r vs
termination_by structural vs => vs

def Value.substAbsRd (σ : Nat) (r : Value) : List (DeclInfo × Value) → List (DeclInfo × Value)
  | [] => []
  | (d, v) :: vs => (d, Value.substAbs σ r v) :: Value.substAbsRd σ r vs
termination_by structural vs => vs

def Term.substAbs (σ : Nat) (r : Value) : Term → Term
  | .val v => .val (Value.substAbs σ r v)
  | .assign p t => .assign p (Term.substAbs σ r t)
  | .letIn h t u => .letIn h (Term.substAbs σ r t) (Term.substAbs σ r u)
  | .seq t u => .seq (Term.substAbs σ r t) (Term.substAbs σ r u)
  | .matchNat p z s => .matchNat p (Term.substAbs σ r z) (Term.substAbs σ r s)
  | .pi hs ds c => .pi hs (Term.substAbsList σ r ds) (Term.substAbs σ r c)
  | .fix f hs ds c d b => .fix f hs (Term.substAbsList σ r ds) (Term.substAbs σ r c) d (Term.substAbs σ r b)
  | .call f as h => .call (Term.substAbs σ r f) (Term.substAbsList σ r as) h
  | .succ t => .succ (Term.substAbs σ r t)
  | .eq A a b => .eq (Term.substAbs σ r A) (Term.substAbs σ r a) (Term.substAbs σ r b)
  | .cong f h => .cong (Term.substAbs σ r f) (Term.substAbs σ r h)
  | .ref A => .ref (Term.substAbs σ r A)
  | .id A a b => .id (Term.substAbs σ r A) (Term.substAbs σ r a) (Term.substAbs σ r b)
  | .ascribe t A => .ascribe (Term.substAbs σ r t) (Term.substAbs σ r A)
  | .prim n as => .prim n (Term.substAbsList σ r as)
  | .tind n as => .tind n (Term.substAbsList σ r as)
  | .ctor ty c h ps as => .ctor ty c h (Term.substAbsList σ r ps) (Term.substAbsList σ r as)
  | .matchInd p ty arms => .matchInd p ty (Term.substAbsArms σ r arms)
  -- exp-block-text: a sealed block's cells, their declared types, its type and its match (`Machine.substT`'s `.block`)
  | .block cs rd pf B m => .block (Term.substAbsArms σ r cs) (Value.substAbsRd σ r rd) pf (Value.substAbs σ r B) (Term.substAbs σ r m)
  | t => t
termination_by structural t => t

def Term.substAbsList (σ : Nat) (r : Value) : List Term → List Term
  | [] => []
  | t :: ts => Term.substAbs σ r t :: Term.substAbsList σ r ts
termination_by structural ts => ts

def Term.substAbsArms (σ : Nat) (r : Value) : List (Hint × Term) → List (Hint × Term)
  | [] => []
  | (h, t) :: ts => (h, Term.substAbs σ r t) :: Term.substAbsArms σ r ts
termination_by structural ts => ts
end

end Ochr

namespace Ochr.Meaning
open Classical

section
variable (K : RunCtx) (ρ : Assignment)

/-- The decisions do not see the substitution of `r` for `σ` (`DecInvariant`'s counterpart; for a
data unknown and a constructor refinement the real `Decide` reads both `.other`: `valueDecl`'s
frozen reading of a data unknown is `valTypeDecl` of its type, `.other`, and a constructor value's
is `.other`). -/
def DecInvariantAbs (D : Decisions) (σ : Nat) (r : Value) : Prop :=
  (∀ sc t, D.flags sc (Term.substAbs σ r t) = D.flags sc t) ∧
  (∀ sc t, D.declOf sc (Term.substAbs σ r t) = D.declOf sc t) ∧
  (∀ sc t, D.piSort sc (Term.substAbs σ r t) = D.piSort sc t) ∧
  (∀ sc e t, D.joinMoves sc e (Term.substAbs σ r t) = D.joinMoves sc e t) ∧
  (∀ sc t, D.rePointed sc (Term.substAbs σ r t) = D.rePointed sc t) ∧
  (∀ sc t, D.typeDecl sc (Term.substAbs σ r t) = D.typeDecl sc t) ∧
  (∀ sc e t, D.blockCaps sc e (Term.substAbs σ r t) = D.blockCaps sc e t)

/-- What the substitution of `r` for `σ` needs (`FillOK`'s counterpart; no future is fixed, the
assignment already gives `σ` its value): `r` means `ρ σ` at every hint, the run types the embedded
`r` as it types the embedded `σ` (the base case of the induction), and the decisions do not see the
substitution. -/
structure AbsFillOK (ψ : Future) (σ : Nat) (r : Value) : Prop where
  mean : ∀ hint, meanV K ρ ψ hint r = ρ σ
  shape : ∀ hint s, (run K ρ ψ hint (.val r) s).map (·.1.2) = (run K ρ ψ hint (.val (.abs σ)) s).map (·.1.2)
  dec : DecInvariantAbs K.D σ r

/-- **The base case holds wherever `DeltaOk` does** (kernel-checked; since the run's `.val` clause
types an embedded value by what it is, as the checker does). Where `Δ σ` is `σ`'s stored type read
as `DeltaOk` reads it (`deltaOf`), a refinement of `σ`, a number where the stored type is `Nat`, a
constructor value recording the stored type's parameters where it is `D(ps̄)`, is typed by the run
exactly as `.val σ` is. (Before, the run typed every data value but an unknown at the hint, and this
was false at the text `.val σ` itself: `.val Z` at `err`, `.val σ` at `Nat`.) -/
theorem absFill_shape (hK : ∀ n, (K.C.global n).2.label = none) (st : MState) (σ : Nat)
    (hΔ : K.Δ σ = deltaOf K ρ st σ) (ψ : Future) (r : Value)
    (hr : (st.absTy[σ]? = some .tNat ∧ (r = .zero ∨ ∃ v, r = .succ v)) ∨
      ∃ (ty : String) (c : Nat) (h : Hint) (ps fs : List Value) (d : IndDecl),
        st.absTy[σ]? = some (.tInd ty ps) ∧ r = .ind ty c h ps fs ∧
        K.Γ.find? (·.name == ty) = some d ∧ (ps.isEmpty && !d.params.isEmpty) = false ∧
        ∀ l, Value.anyAtomList (· == .loan l) ps = false)
    -- the strict `.val` clause tests an embedded constructor value against its type: the filler
    -- means a member of `σ`'s type (what an assignment typing its unknowns gives, `ρ σ ∈ Δ σ`)
    (hmem : ∀ hint, meanV K ρ ψ hint r ∈ₛ[K.dm.read] (K.Δ σ).m) :
    ∀ hint s, (run K ρ ψ hint (.val r) s).map (·.1.2) = (run K ρ ψ hint (.val (.abs σ)) s).map (·.1.2) := by
  intro hint s
  rw [run_val_def, run_val_def]
  simp only [Option.map_some, Option.some.injEq]
  have hvσ : valT K ρ ψ hint (.abs σ) = deltaOf K ρ st σ := hΔ
  rw [hvσ]
  rcases hr with ⟨hT, hn⟩ | ⟨ty, c, h, ps, fs, d, hT, rfl, hd, hps, hl⟩
  · have hv : valT K ρ ψ hint r = .plain TyM.nat := by
      rcases hn with rfl | ⟨v, rfl⟩ <;> rfl
    rw [hv]
    simp only [deltaOf, hT]
    rcases hn with rfl | ⟨v, rfl⟩ <;> rfl
  · have hP : meanParams K ρ ψ d 0 [] ps = meanParams K ρ (fun _ => .err) d 0 [] ps :=
      meanParams_congrE K ρ ψ (fun _ => .err) hK d ps 0 [] (fun l h => by rw [hl l] at h; cases h)
    have hv : valT K ρ ψ hint (.ind ty c h ps fs) = .plain (K.dm.tyM d (meanParams K ρ (fun _ => .err) d 0 [] ps)) := by
      simp only [valT, hd, hps, Bool.false_eq_true, if_false, hP]
      rfl
    have hm := hmem hint
    rw [hΔ] at hm
    rw [hv]
    simp only [deltaOf, hT, Ochr.Value.tyS, Value.mean, hd, meanParams_eq_mean] at hm ⊢
    -- `σ`'s type is strict (`paramsOk`): the filler is a member of it, so it is not `err`
    by_cases hpo : paramsOk K.dm d (meanParams K ρ (fun _ => .err) d 0 [] ps)
    rotate_left
    · rw [if_neg hpo] at hm; obtain ⟨a, _⟩ := hm; exact a.elim
    rw [if_pos hpo] at hm ⊢
    -- a constructor value of a declared type at a known record means a tree, not `err`
    have hne : meanV K ρ ψ hint (.ind ty c h ps fs) ≠ .err := by
      simp only [meanV, Value.mean, hd, hps, Bool.false_eq_true, if_false]
      split <;> simp [DataModel.ctorR]
    simp only [strictVal, SM.strictS, pure]
    rw [if_neg hne, if_pos (by exact hm)]
    rfl

end

end Ochr.Meaning
