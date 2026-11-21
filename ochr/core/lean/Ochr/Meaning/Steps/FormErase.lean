import Ochr.Meaning.Steps.Form
import Ochr.Meaning.PosLib

/-!
# Nothing the simulation reads reads a temporary's stored type (lead7)

Main's D104 gave every temporary a stored type (`Frame.tempTys`), which the checker writes and never
reads. Nor does anything here: the positions, the values, the meanings, the holders, the live loans
and their sites, and the checker's state read as a reference state all read a frame's bindings and
temporaries only. So two environments that differ only in the temporaries' types are the same to
`Rel` (`Rel.erase`). `Env.erase` forgets them.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

@[simp] theorem Frame.erase_binds (fr : Frame) : fr.erase.binds = fr.binds := rfl
@[simp] theorem Frame.erase_temps (fr : Frame) : fr.erase.temps = fr.temps := rfl
@[simp] theorem Env.erase_size (env : Env) : env.erase.size = env.size := Array.size_map ..
theorem Env.erase_get? (env : Env) (f : Nat) : env.erase[f]? = env[f]?.map Frame.erase := Array.getElem?_map ..

theorem Env.erase_getD (env : Env) (f : Nat) : (env.erase[f]?.getD default) = (env[f]?.getD default).erase := by
  rw [Env.erase_get?]; cases env[f]? <;> rfl

theorem allPos_erase (env : Env) : allPos env.erase = allPos env := by
  rw [allPos_eq, allPos_eq, Env.erase_size]
  congr 1; funext f
  rw [Env.erase_get?]; cases env[f]? <;> rfl

theorem valAt_erase (env : Env) (p : Pos) : valAt env.erase p = valAt env p := by
  cases p with
  | bind f i => rw [valAt_bind_eq, valAt_bind_eq, Env.erase_getD]; rfl
  | temp f i => rw [valAt_temp_eq, valAt_temp_eq, Env.erase_getD]; rfl

theorem shape_erase (env : Env) : Env.shape env.erase = Env.shape env := by
  funext p; simp only [Env.shape, valAt_erase]

theorem values_erase (env : Env) : Env.values env.erase = Env.values env := by
  simp only [Env.values, allPos_erase]
  congr 1; funext p; exact valAt_erase env p

theorem findBorrow_erase (env : Env) (l : Nat) : findBorrow env.erase l = findBorrow env l := by
  simp only [findBorrow, allPos_erase, valAt_erase]

theorem liveLoan_erase (env : Env) : liveLoan env.erase = liveLoan env := by
  funext l; simp only [liveLoan, findBorrow_erase]

theorem sitesOf_erase (env : Env) : Env.sitesOf env.erase = Env.sitesOf env := by
  funext l; simp only [Env.sitesOf, allPos_erase, valAt_erase]

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

theorem hintAt_erase (env : Env) (p : Pos) : Env.hintAt dm C Γ ρ env.erase p = Env.hintAt dm C Γ ρ env p := by
  cases p with
  | temp => rfl
  | bind f i => simp only [Env.hintAt, Env.erase_get?]; cases env[f]? <;> rfl

theorem mean_erase (φ : Future) (env : Env) (p : Pos) : Env.mean dm C Γ ρ φ env.erase p = Env.mean dm C Γ ρ φ env p := by
  cases p with
  | bind f i => simp only [Env.mean, hintAt_erase, Env.erase_get?]; cases env[f]? <;> rfl
  | temp f i => simp only [Env.mean, hintAt_erase, Env.erase_get?]; cases env[f]? <;> rfl

theorem sstate_erase (st : MState) :
    MState.sstate dm C Γ ρ { st with env := st.env.erase } = MState.sstate dm C Γ ρ st := by
  simp only [MState.sstate, Env.erase, Array.toList_map, List.zipIdx_map, List.map_map]
  congr 1
  · congr 1; funext ⟨fr, f⟩
    simp only [Function.comp, Frame.erase_binds, Frame.erase_temps]
    congr 2
    · funext ⟨b, i⟩; congr 1
      · exact hintAt_erase dm C Γ ρ st.env _
      · funext φ; exact mean_erase dm C Γ ρ φ st.env _
    · funext ⟨_, i⟩; funext φ; exact mean_erase dm C Γ ρ φ st.env _
  · exact shape_erase st.env
  · exact sitesOf_erase st.env

end

theorem occurs_erase (st : MState) (l : Nat) : MState.Occurs { st with env := st.env.erase } l ↔ st.Occurs l := by
  unfold MState.Occurs; rw [values_erase]

/-- **`Rel` does not read the temporaries' stored types.** -/
theorem rel_erase {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState} :
    Rel K ρ φ π { st with env := st.env.erase } s ↔ Rel K ρ φ π st s := by
  have e1 : SM' K ρ { st with env := st.env.erase } = SM' K ρ st := sstate_erase K.dm K.M K.Γ ρ st
  have e2 : MState.mean K.dm K.M K.Γ ρ { st with env := st.env.erase } = MState.mean K.dm K.M K.Γ ρ st := by
    simp only [MState.mean, allPos_erase, shape_erase]
    congr 1; funext φ p; exact mean_erase K.dm K.M K.Γ ρ φ st.env p
  constructor
  · intro hr
    refine ⟨?_, ?_, ?_, ?_, ?_, hr.holders, hr.records⟩
    · rw [← e1]; exact hr.skel
    · intro l hl ho; exact hr.fresh l hl ((occurs_erase st l).mpr ho)
    · rw [← e2]; exact hr.sim
    · have := hr.inj; simp only [liveLoan_erase] at this; exact this
    · have := hr.sites; simp only [liveLoan_erase, sitesOf_erase] at this; exact this
  · intro hr
    refine ⟨?_, ?_, ?_, ?_, ?_, hr.holders, hr.records⟩
    · rw [e1]; exact hr.skel
    · intro l hl ho; exact hr.fresh l hl ((occurs_erase st l).mp ho)
    · rw [e2]; exact hr.sim
    · show ∀ l l', liveLoan st.env.erase l = true → _; simp only [liveLoan_erase]; exact hr.inj
    · show ∀ l, liveLoan st.env.erase l = true → _; simp only [liveLoan_erase, sitesOf_erase]; exact hr.sites

/-- Pushing a temporary commutes with forgetting the temporaries' types. -/
theorem erase_pushTemp (env : Env) (v : Value) (T? : Option Value) :
    Env.erase (env.modify (env.size - 1) fun fr => { fr with temps := fr.temps.push v, tempTys := fr.tempTys.push T? }) =
      (Env.erase env).modify (env.erase.size - 1) fun fr => { fr with temps := fr.temps.push v } := by
  apply Array.ext_getElem?
  intro f
  simp only [Env.erase_get?, Array.getElem?_modify, Env.erase_size]
  split <;> cases env[f]? <;> rfl

/-- The environment of `withTempT`, its temporaries' types forgotten. -/
theorem erase_withTempT (st : MState) (v : Value) (T? : Option Value) :
    (st.withTempT v T?).env.erase = (Env.erase st.env).modify (st.env.erase.size - 1) fun fr => { fr with temps := fr.temps.push v } :=
  erase_pushTemp st.env v T?

theorem binds_erase (env : Env) (f : Nat) : (env.erase[f]!).binds = (env[f]!).binds := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Env.erase_get?]
  cases env[f]? <;> rfl

theorem temps_erase (env : Env) (f : Nat) : (env.erase[f]!).temps = (env[f]!).temps := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Env.erase_get?]
  cases env[f]? <;> rfl

end Ochr.Meaning.Steps.Form
