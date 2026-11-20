import Ochr.Meaning.Regress.DepSites
import Ochr.Meaning.Regress.StaticLend

/-!
# Dependence within sites on two more states (docs/31 D67; kernel-checked)

Under the erased comparison (`pathKey`), beside `Regress/DepSites.lean`'s six:
* **a reborrow of a reborrow** (`let r = &a; let s = &*r; let t = &*s`), and after the middle
  borrow's end, whose re-rooting the checker's `endBorrow` agrees with (`rr_end`): holds
  (`dws_RR`, `dws_RR'`);
* **a field borrowed through a returned borrow of a pair** (`let r = IdP(&x); let s = &(*r).0`),
  the first site BELOW a root by field (`(r, [*, .0])`): holds (`dws_Pair`) when the pair's second
  field's type reads no earlier field (`hty`, as the library data model's `fieldTy` does). For a
  dependent pair it fails in the reading's TYPE (`dws_Pair_dependent_fails`): the type field `1` is
  read at reads field `0`, which is lent; the meaning read does not.
The checker's states are read at holes of its real runs (`atHole`, the editor's Ω), and the
reference's sites are the checker's (identity renaming), kernel-checked.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr DepSitesAt uses Nats {
  def IdP (p : &(Nat × Nat)) : &(Nat × Nat) := &*p
  def RRAt (a : Nat) : Unit := (let r = &a; let s = &*r; let t = &*s; ?)
  def PairAt (a : Nat) (b : Nat) : Unit := (let x = (a, b); let r = IdP(&x); let s = &(*r).0; ?)
}

namespace Ochr.Meaning.Regress.DepSitesMore
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CallInPlace Ochr.Meaning.Regress

def atHole (name : String) : List Value :=
  let r := Ochr.Test.runWith (some Prelude) "DepSitesAt" DepSitesAt (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2)) | _ => none).headD []
  | none => []

/-! ## A reborrow of a reborrow

`let r = &a; let s = &*r; let t = &*s`. At the hole the checker holds `a ↦ loan_0`,
`r ↦ borrow_0 loan_1`, `s ↦ borrow_1 loan_2`, `t ↦ borrow_2 σ0` (frame `1`: the function, `a`, `r`,
`s`, `t`). The reference (identity renaming, the checker's sites): `a` reads `0`'s final content,
`r` reads `1`'s, `s` reads `2`'s, `t` holds `σ0`. Then [End 1] at `s` (`s`'s borrow ends while
`t` lives): `r` reads `2`'s final content (`1` fixed to what `s` holds), `s` is forgotten, and
`t`'s site `(s, [*])` is re-rooted through `1`'s site `(r, [*])` to `(r, [*])` (the reborrow's `*`
replaces the ended borrow's, `inContent`), as the checker's `endBorrow` does (`rr_end`). No site
path holds two `*`s. -/

def vRR : List Value := [.loan 0, .borrow 0 (.loan 1), .borrow 1 (.loan 2), .borrow 2 (.abs 0)]
#guard atHole "RRAt" == vRR
def stRR : MState := StaticLend.stateAt "RRAt" vRR 3 1

/-- The checker's sites: `0` at `a`, `1` at `(r, [*])`, `2` at `(s, [*])`; after its [End 1] at `s`,
every label is lent where the reference's `relend` lends it, `2` at `(r, [*])`. -/
theorem rr_sites : StaticLend.sameSites (Env.sitesOf stRR.env 0) [⟨.bind 1 1, [], false⟩] = true ∧
    StaticLend.sameSites (Env.sitesOf stRR.env 1) [⟨.bind 1 2, [.deref], false⟩] = true ∧
    StaticLend.sameSites (Env.sitesOf stRR.env 2) [⟨.bind 1 3, [.deref], false⟩] = true := by
  decide +kernel
theorem rr_end : StaticLend.endAgrees stRR 1 (.bind 1 3) 50 = true ∧
    StaticLend.sameSites ((StaticLend.refOf stRR.env).relend 1 (.bind 1 3) 2) [⟨.bind 1 2, [.deref], false⟩] = true := by
  decide +kernel

def SRR (S A R T U : SBinding) (vs vt : Sem) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { A with val := fun ψ => ψ 0 },
      { R with val := fun ψ => ψ 1 }, { T with val := fun ψ => ψ 2 }, { U with val := fun _ => vt }] []],
    shape := fun p => if p = .bind 1 2 then some 0 else if p = .bind 1 3 then some 1 else if p = .bind 1 4 then some 2 else none,
    nextLoan := 3, lent := Env.sitesOf stRR.env }

def SRR' (S A R T U : SBinding) (vs vt : Sem) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { A with val := fun ψ => ψ 0 },
      { R with val := fun ψ => ψ 2 }, { T with val := fun _ => .moved }, { U with val := fun _ => vt }] []],
    shape := fun p => if p = .bind 1 2 then some 0 else if p = .bind 1 4 then some 2 else none,
    nextLoan := 3, lent := (StaticLend.refOf stRR.env).relend 1 (.bind 1 3) }

theorem rs_RR (l i : Nat) (h : (l = 0 ∧ i = 1) ∨ (l = 1 ∧ i = 2) ∨ (l = 2 ∧ i = 3)) :
    (Env.sitesOf stRR.env l).any (fun x => decide (x.pos = .bind 1 i) && (pathKey x.path).isEmpty) = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel

theorem rs_RR' (l i : Nat) (h : (l = 0 ∧ i = 1) ∨ (l = 2 ∧ i = 2)) :
    ((StaticLend.refOf stRR.env).relend 1 (.bind 1 3) l).any
      (fun x => decide (x.pos = .bind 1 i) && (pathKey x.path).isEmpty) = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel

variable (dm : DataModel) (Γ : List IndDecl)

/-- **A reborrow of a reborrow.** -/
theorem dws_RR (S A R T U : SBinding) (vs vt : Sem) : DepWithinSites dm Γ (SRR S A R T U vs vt) := by
  apply DepSites.dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SRR]
    · rcases i with _ | _ | _ | _ | _ | i
      · simp [SState.valAt, SRR]
      · simp [SState.valAt, SRR, DepSites.agree_of_rootSited h (l := 0) (rs_RR 0 1 (.inl ⟨rfl, rfl⟩))]
      · simp [SState.valAt, SRR, DepSites.agree_of_rootSited h (l := 1) (rs_RR 1 2 (.inr (.inl ⟨rfl, rfl⟩)))]
      · simp [SState.valAt, SRR, DepSites.agree_of_rootSited h (l := 2) (rs_RR 2 3 (.inr (.inr ⟨rfl, rfl⟩)))]
      all_goals simp [SState.valAt, SRR]
    · simp [SState.valAt, SRR]
  · rcases f with _ | _ | f <;> simp [SState.valAt, SRR]

/-- **The same after the middle borrow's end.** -/
theorem dws_RR' (S A R T U : SBinding) (vs vt : Sem) : DepWithinSites dm Γ (SRR' S A R T U vs vt) := by
  apply DepSites.dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SRR']
    · rcases i with _ | _ | _ | _ | _ | i
      · simp [SState.valAt, SRR']
      · simp [SState.valAt, SRR', DepSites.agree_of_rootSited h (l := 0) (rs_RR' 0 1 (.inl ⟨rfl, rfl⟩))]
      · simp [SState.valAt, SRR', DepSites.agree_of_rootSited h (l := 2) (rs_RR' 2 2 (.inr ⟨rfl, rfl⟩))]
      all_goals simp [SState.valAt, SRR']
    · simp [SState.valAt, SRR']
  · rcases f with _ | _ | f <;> simp [SState.valAt, SRR']


/-! ## A field borrowed through a returned borrow of a pair

`IdP (p : &(Nat × Nat)) : &(Nat × Nat) := &*p`, then `let x = (a, b); let r = IdP(&x); let s = &(*r).0`.
At the hole the checker holds `a ↦ ⊥`, `b ↦ ⊥`, `x ↦ lent_2 loan_2` (a fill over `2`, the call run
in place), `r ↦ borrow_2 (loan_3, σ1)`, `s ↦ borrow_3 σ0` (frame `1`: the function, `a`, `b`, `x`,
`r`, `s`). The reference (identity renaming, the checker's sites): `x` reads a function of `2`'s
final content (`callOf`'s `.ref` row), `r` reads the pair whose field `0` is `3`'s final content
and whose field `1` is `σ1`'s meaning (`ctorM`: a constructor value describes itself, its element
whatever the fields give), `s` holds `σ0`. `3` is lent at `(r, [*, .0])`, BELOW the root: a read of
`r` at a path whose first field is `.1` is incomparable with it, and reads field `1` whatever `3`'s
final content is, at a type that does not read field `0` when the pair is not dependent
(`hty`; the library data model's `fieldTy` ignores the earlier fields, `Data.lean`). -/

def vP : List Value := [.bot, .bot, .gloan 2 (.loan 2),
  .borrow 2 (.ind "Pair" 0 ⟨"Mk"⟩ [.tNat, .tNat] [.loan 3, .abs 1]), .borrow 3 (.abs 0)]
#guard atHole "PairAt" == vP
def stP : MState := StaticLend.stateAt "PairAt" vP 4 2

/-- The checker's sites: `2` fills `x`; `3` is lent at `(r, [*, .0])`. -/
theorem pair_sites : StaticLend.sameSites (Env.sitesOf stP.env 2) [⟨.bind 1 3, [], true⟩] = true ∧
    StaticLend.sameSites (Env.sitesOf stP.env 3) [⟨.bind 1 4, [.deref, .field ⟨"Pair", 0, 0, ""⟩], false⟩] = true := by
  decide +kernel

noncomputable def SPr (S A B X R T : SBinding) (fx : Sem → Sem) (ps : List Sem) (v1 vs vt : Sem)
    (e : Sem → Option (Σ A : Type, A)) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { A with val := fun _ => .moved },
      { B with val := fun _ => .moved }, { X with val := fun ψ => fx (ψ 2) },
      { R with val := fun ψ => .dat "Pair" ps 0 [ψ 3, v1] (e (ψ 3)) }, { T with val := fun _ => vt }] []],
    shape := fun p => if p = .bind 1 4 then some 2 else if p = .bind 1 5 then some 3 else none,
    nextLoan := 4, lent := Env.sitesOf stP.env }

/-- Off field `0`, a pair's reading does not read field `0` (its type at field `1` by `hty`). -/
theorem follow_pair_off (ps : List Sem) (v1 : Sem)
    (hty : ∀ x y : Sem, contentTyS dm Γ "Pair" ps 0 1 [x] v1 = contentTyS dm Γ "Pair" ps 0 1 [y] v1)
    (a a' : Sem) (e e' : Option (Σ A : Type, A)) :
    ∀ (steps : List Step) (T : TyS), (pathKey steps).head? ≠ none → (pathKey steps).head? ≠ some (0, 0) →
      Sem.follow dm Γ T (.dat "Pair" ps 0 [a, v1] e) steps = Sem.follow dm Γ T (.dat "Pair" ps 0 [a', v1] e') steps
  | [], _, h, _ => absurd rfl h
  | .deref :: ss, T, h1, h2 => by
    simp only [Sem.follow, Sem.step, Option.bind_some]
    exact follow_pair_off ps v1 hty a a' e e' ss T h1 h2
  | .proj i :: ss, T, h1, h2 => by
    cases i with
    | zero => exact absurd rfl h2
    | succ i =>
      cases i with
      | zero => simp [Sem.follow, Sem.step, Sem.stepField, hty a a']
      | succ i => simp [Sem.follow, Sem.step, Sem.stepField]
  | .field g :: ss, T, h1, h2 => by
    simp only [Sem.follow, Sem.step, Sem.stepField]
    by_cases hc : 0 = g.ctor
    · have hi : g.idx ≠ 0 := fun hi => h2 (by simp [pathKey, Step.key, ← hc, hi])
      rcases g with ⟨gt, gc, gi, gn⟩
      simp only at hc hi
      subst hc
      rcases gi with _ | _ | gi
      · exact absurd rfl hi
      · simp [hty a a']
      · simp
    · simp [hc]

theorem rs_P (l i : Nat) (h : l = 2 ∧ i = 3) :
    (Env.sitesOf stP.env l).any (fun x => decide (x.pos = .bind 1 i) && (pathKey x.path).isEmpty) = true := by
  obtain ⟨rfl, rfl⟩ := h; decide +kernel

theorem siteP3 : (Env.sitesOf stP.env 3).any
    (fun x => decide (x.pos = .bind 1 4) && pathKey x.path == [(0, 0)]) = true := by
  decide +kernel

/-- **A field borrowed through a returned borrow of a pair**: the site below the root. -/
theorem dws_Pair (S A B X R T : SBinding) (fx : Sem → Sem) (ps : List Sem) (v1 vs vt : Sem)
    (e : Sem → Option (Σ A : Type, A))
    (hty : ∀ x y : Sem, contentTyS dm Γ "Pair" ps 0 1 [x] v1 = contentTyS dm Γ "Pair" ps 0 1 [y] v1) :
    DepWithinSites dm Γ (SPr S A B X R T fx ps v1 vs vt e) := by
  intro p steps ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SPr]
    · rcases i with _ | _ | _ | _ | _ | _ | i
      · simp [SState.valAt, SPr]
      · simp [SState.valAt, SPr]
      · simp [SState.valAt, SPr]
      · have h2 : ψ 2 = ψ' 2 := Classical.byContradiction fun hne => by
          have := (h 2 hne).2
          rw [DepSites.reached_of_rootSited (s := SPr S A B X R T fx ps v1 vs vt e) (p := .bind 1 3) (l := 2)
            (rs_P 2 3 ⟨rfl, rfl⟩) steps] at this; cases this
        simp [SState.valAt, SPr, h2]
      · by_cases h3 : ψ 3 = ψ' 3
        · simp [SState.valAt, SPr, h3]
        · have hr := (h 3 h3).2
          obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp siteP3
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxp
          have hd : dataHit steps x.path = false := by
            simp only [SState.reached, SPr, List.any_eq_false] at hr
            have := hr x hx
            simp only [hxp.1, Bool.and_eq_true, decide_eq_true_eq, true_and, Bool.not_eq_true] at this
            exact this
          simp only [dataHit, hxp.2, Bool.or_eq_false_iff] at hd
          simp only [SState.valAt, SPr, SState.tyAt]
          refine follow_pair_off dm Γ ps v1 hty _ _ _ _ steps _ ?_ ?_
          · intro hn
            have : pathKey steps = [] := by
              cases hk : pathKey steps with
              | nil => rfl
              | cons _ _ => rw [hk] at hn; cases hn
            rw [this] at hd; simp at hd
          · intro hn
            cases hk : pathKey steps with
            | nil => rw [hk] at hn; cases hn
            | cons k0 rest =>
              rw [hk] at hn hd
              simp only [List.head?_cons, Option.some.injEq] at hn
              subst hn
              simp [List.isPrefixOf] at hd
      · simp [SState.valAt, SPr]
      · simp [SState.valAt, SPr]
    · simp [SState.valAt, SPr]
  · rcases f with _ | _ | f <;> simp [SState.valAt, SPr]

theorem sitesP3_all : (Env.sitesOf stP.env 3).all
    (fun x => !decide (x.pos = .bind 1 4) || pathKey x.path == [(0, 0)]) = true := by
  decide +kernel

/-- **For a dependent pair the reading's TYPE reads the lent field**: where the type field `1` is read
at depends on field `0` (`fieldTy` reading the earlier fields, as a dependent declaration's does),
two typed futures differing only at `3` (lent at `(r, [*, .0])`, incomparable with `[*, .1]`) read
field `1` at different types. The meaning read is the same (`follow_pair_off`'s first component). -/
theorem dws_Pair_dependent_fails (S A B X R T : SBinding) (fx : Sem → Sem) (ps : List Sem) (v1 vs vt : Sem)
    (e : Sem → Option (Σ A : Type, A)) (x y : Sem)
    (hdep : contentTyS dm Γ "Pair" ps 0 1 [x] v1 ≠ contentTyS dm Γ "Pair" ps 0 1 [y] v1) :
    ¬ DepWithinSites dm Γ (SPr S A B X R T fx ps v1 vs vt e) := by
  intro h
  have := h (.bind 1 4) [.deref, .field ⟨"Pair", 0, 1, ""⟩] (fun l => if l = 3 then x else .err)
    (fun l => if l = 3 then y else .err) (fun l hl => ?_)
  · simp [SState.valAt, SPr, Sem.follow, Sem.step, Sem.stepField] at this
    exact hdep this
  · by_cases hl3 : l = 3
    · subst hl3
      refine ⟨?_, ?_⟩
      · rw [SState.live_iff]
        exact ⟨.bind 1 5, by simp [SPr, SState.positions, List.range'], by simp [SPr]⟩
      · simp only [SState.reached, SPr, List.any_eq_false]
        intro z hz hzr
        have hall := List.all_eq_true.mp sitesP3_all z hz
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hzr
        simp only [hzr.1, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hall
        have h2 := hzr.2
        have hk : pathKey [Step.deref, .field ⟨"Pair", 0, 1, ""⟩] = [(0, 1)] := rfl
        rw [dataHit, hall, hk] at h2
        revert h2; decide
    · simp [hl3] at hl

end Ochr.Meaning.Regress.DepSitesMore
