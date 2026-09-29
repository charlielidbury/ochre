import OchrMeta.Machine

/-! # Algebra for the frame lemma

The frame lemma compares a run from `Ω₁ ++ Ω₂` with a run from `Ω₁ ++ [ports]`, where the
*ports* frame has one binding `port ℓ ↦ loan_ℓ` per borrow of `Ω₁`: the run sees only `Ω₁`,
and each port records what the run substituted for `loan_ℓ` (the paper's θ).  The full state
is recovered by `frameMap Ω₂`, which substitutes the ports' final values into `Ω₂`. -/

namespace OchrMeta

/-- The value recorded for loan `l` by a ports frame `P` whose `i`-th port stands for loan `K[i]`.
Ports are keyed by position (not by loan name), so that renaming loans commutes with forming
the ports frame. -/
def portSub (K : List Nat) (P : Frame) (l : Nat) : Option Val :=
  (K.idxOf? l).bind fun i => P.lookup (.port i)

def Env.substPorts (K : List Nat) (P : Frame) (Ω : Env) : Env := Ω.mapVals (Val.substSim (portSub K P))

/-- The loans the ports of `Ω` stand for: its borrow names (in a well-formed environment each
occurs once; a repeated name gets a second, unused port). -/
def Env.portKeys (Ω : Env) : List Nat := Ω.borrows

/-- One port per borrow name of `Ω`, initially holding its own loan. -/
def Env.portsOf (Ω : Env) : Frame := Ω.portKeys.zipIdx.map fun p => (Var.port p.2, Val.loan p.1)

/-- Recover the full state from a port-side state `A ++ [P]`. -/
def frameMap (K : List Nat) (Ω₂ : Env) (s : St) : St :=
  ⟨s.env.dropLast ++ Ω₂.substPorts K (s.env.getLastD []), s.next⟩

/-! ## Values -/

theorem Val.substSim_substLoan (σ : Nat → Option Val) (l : Nat) (w : Val) :
    ∀ v : Val, (∀ m ∈ v.loans, σ m = none → m ≠ l) →
      Val.substLoan l w (v.substSim σ) = v.substSim (fun m => (σ m).map (Val.substLoan l w)) := by
  intro v
  induction v with
  | loan m =>
    intro h
    simp only [Val.substSim, Val.loans, List.mem_singleton, forall_eq] at h ⊢
    cases hσ : σ m with
    | none =>
      have := h hσ
      simp [Val.substLoan, this]
    | some u => simp
  | succ v ih => intro h; simp only [Val.substSim, Val.substLoan]; rw [ih (by simpa [Val.loans] using h)]
  | borrow m v ih =>
    intro h; simp only [Val.substSim, Val.substLoan]; rw [ih (by simpa [Val.loans] using h)]
  | pair a b iha ihb =>
    intro h
    simp only [Val.loans, List.mem_append] at h
    simp only [Val.substSim, Val.substLoan]
    rw [iha (fun m hm => h m (Or.inl hm)), ihb (fun m hm => h m (Or.inr hm))]
  | sealed f a k x iha ihx =>
    intro h
    simp only [Val.loans, List.mem_append] at h
    simp only [Val.substSim, Val.substLoan]
    rw [iha (fun m hm => h m (Or.inl hm)), ihx (fun m hm => h m (Or.inr hm))]
  | _ => intro _; rfl

theorem Val.substSim_id (σ : Nat → Option Val) (hσ : ∀ l, σ l = none ∨ σ l = some (.loan l)) :
    ∀ v : Val, v.substSim σ = v := by
  intro v
  induction v with
  | loan m => rcases hσ m with h | h <;> simp [Val.substSim, h]
  | _ => simp_all [Val.substSim]

theorem Frame.lookup_mapVals (g : Val → Val) (P : Frame) (x : Var) :
    (Frame.mapVals g P).lookup x = (P.lookup x).map g := by
  induction P with
  | nil => rfl
  | cons b P ih =>
    obtain ⟨y, v⟩ := b
    simp only [Frame.mapVals, List.map_cons, List.lookup_cons] at ih ⊢
    split <;> simp_all

theorem portSub_mapVals (K : List Nat) (g : Val → Val) (P : Frame) (l : Nat) :
    portSub K (Frame.mapVals g P) l = (portSub K P l).map g := by
  simp only [portSub, Frame.lookup_mapVals]
  cases K.idxOf? l <;> simp

theorem Frame.mapVals_mapVals (g h : Val → Val) (F : Frame) :
    Frame.mapVals g (Frame.mapVals h F) = Frame.mapVals (g ∘ h) F := by
  simp [Frame.mapVals]

theorem Env.mapVals_mapVals (g h : Val → Val) (Ω : Env) :
    Env.mapVals g (Env.mapVals h Ω) = Env.mapVals (g ∘ h) Ω := by
  simp [Env.mapVals, Frame.mapVals, Function.comp_def]

theorem Env.mapVals_append (g : Val → Val) (A B : Env) :
    Env.mapVals g (A ++ B) = Env.mapVals g A ++ Env.mapVals g B := by
  simp [Env.mapVals]

theorem Frame.mapVals_congr (g h : Val → Val) (F : Frame) (hgh : ∀ b ∈ F, g b.2 = h b.2) :
    Frame.mapVals g F = Frame.mapVals h F := by
  simp only [Frame.mapVals]
  apply List.map_congr_left
  intro b hb
  rw [hgh b hb]

theorem Env.mapVals_congr (g h : Val → Val) (Ω : Env) (hgh : ∀ F ∈ Ω, ∀ b ∈ F, g b.2 = h b.2) :
    Env.mapVals g Ω = Env.mapVals h Ω := by
  simp only [Env.mapVals]
  apply List.map_congr_left
  intro F hF
  exact Frame.mapVals_congr g h F (hgh F hF)

/-! ## Operations on the top frame commute with appending frames below -/

namespace St

/-- `s` with the frames `X` appended below. -/
def app (s : St) (X : Env) : St := ⟨s.env ++ X, s.next⟩

@[simp] theorem app_env (s : St) (X : Env) : (s.app X).env = s.env ++ X := rfl
@[simp] theorem app_next (s : St) (X : Env) : (s.app X).next = s.next := rfl

theorem frameMap_app (K : List Nat) (Ω₂ : Env) (c : St) (P : Frame) :
    frameMap K Ω₂ (c.app [P]) = c.app (Ω₂.substPorts K P) := by
  simp [frameMap, app]

theorem lookup_app {s : St} (X : Env) (hs : s.env ≠ []) (x : Var) : (s.app X).lookup x = s.lookup x := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => exact absurd rfl hs
  | cons F Ω => rfl

theorem modTop_app {s : St} (X : Env) (hs : s.env ≠ []) (g : Frame → Frame) :
    (s.app X).modTop g = (s.modTop g).app X := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => exact absurd rfl hs
  | cons F Ω => rfl

theorem setVar_app {s : St} (X : Env) (hs : s.env ≠ []) (x : Var) (v : Val) :
    (s.app X).setVar x v = (s.setVar x v).app X := modTop_app X hs _

theorem bind_app {s : St} (X : Env) (hs : s.env ≠ []) (x : Var) (v : Val) :
    (s.app X).bind x v = (s.bind x v).app X := modTop_app X hs _

theorem push_app (s : St) (X : Env) (F : Frame) : (s.app X).push F = (s.push F).app X := rfl

theorem unbind_app {s : St} (X : Env) (hs : s.env ≠ []) (x : Var) :
    (s.app X).unbind x = (s.unbind x).map fun (p : Val × St) => (p.1, p.2.app X) := by
  obtain ⟨Ω, n⟩ := s
  cases Ω with
  | nil => exact absurd rfl hs
  | cons F Ω =>
    simp only [unbind, app, List.cons_append, Option.map_map]
    cases F.remove x <;> rfl

theorem setPlace_app {s : St} (X : Env) (hs : s.env ≠ []) (x : Var) (π : List Proj) (v : Val) :
    (s.app X).setPlace x π v = (s.setPlace x π v).map (·.app X) := by
  simp only [setPlace, lookup_app X hs]
  cases s.lookup x with
  | none => rfl
  | some c =>
    simp only [Option.bind_some]
    cases c.set π v with
    | none => rfl
    | some c' => simp [setVar_app X hs]

end St

end OchrMeta
