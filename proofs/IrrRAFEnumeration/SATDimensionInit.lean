module

public import proofs.IrrRAFEnumeration.SATDimensionParsing
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion Complexity Complexity.TM

theorem rewindParsedInput_correct {k : Nat} (bits : List Bool) (d : Nat)
    (work : Fin k → Tape) (ys : List Bool) (hw : ∀ i, Parked (work i)) :
    (rewindInputTM (n := k)).HoareTime
      (EmitPred (advanceInput (parkedInput bits) d) work ys)
      (EmitPred (parkedInput bits) work ys) (d+3) := by
  let P : TM.TapePred k := fun inp w out =>
    inp.cells = (parkedInput bits).cells ∧ w = work ∧ OutAcc ys out
  have h := rewindInputTM_hoareTime_frame (n := k) (d+1) (P := P) (by
    intro inp w out inp' w' out' hP hc _ hwork hout
    exact ⟨hc.trans hP.1, hwork.trans hP.2.1, by rw [hout]; exact hP.2.2⟩)
  apply h.consequence
  · rintro inp w out ⟨rfl,rfl,hout⟩
    refine ⟨rfl, (parkedInput_parked bits).2, ?_, hout.parked.read_ne_start,
      hout.parked.1, fun i => ⟨(hw i).read_ne_start,(hw i).1⟩, rfl,rfl,hout⟩
    simp [advanceInput, parkedInput, Nat.add_comm]
  · rintro inp w out ⟨hh,hc,hw',hout⟩
    exact ⟨Tape.ext hh hc,hw',hout⟩
  · omega

def dimensionInitTM {k : Nat} (rn rm : Fin k) : TM k :=
  seqTM bumpTM (seqTM (dimensionRegsTM rn rm) rewindInputTM)

/-- Actual dimension initialization from standard input and blank tapes;
the input head is restored for the subsequent addressed clause probes. -/
theorem dimensionInitTM_correct {n m k : Nat} (Φ : Fin m → Finset (Choice n))
    (rn rm : Fin k) (hne : rm ≠ rn) :
    (dimensionInitTM rn rm).HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update (Function.update (fun _ : Fin k => regTape 0) rn (regTape n))
          rm (regTape m)) [])
      (3*n+3*m+13) := by
  let W₀ : Fin k → Tape := fun _ => regTape 0
  let W := Function.update (Function.update W₀ rn (regTape n)) rm (regTape m)
  have hw : ∀ i, Parked (W i) :=
    updateReg_parked _ (updateReg_parked _ (fun _ => parked_regTape _) _ _) _ _
  have h₁ : (bumpTM (n := k)).HoareTime _
      (EmitPred (parkedInput (cnfBits Φ)) W₀ []) 1 :=
    (bumpTM_hoareTime (cnfBits Φ)).strengthen_post (by
      rintro inp work out ⟨hi,hw,hout⟩
      exact ⟨hi,funext (fun i => (hw i).eq_regT),hout⟩)
  have h₂ := dimensionRegsTM_correct Φ rn rm hne W₀ []
    (fun _ => parked_regTape _) rfl rfl
  have h₃ := rewindParsedInput_correct (cnfBits Φ) (n+m+2) W [] hw
  have h₂₃ := seqTM_hoareTime _ _ h₂
    (emitPred_transition (advanceInput_parked _ _ (parkedInput_parked _)) hw []) h₃
  have hall := seqTM_hoareTime _ _ h₁
    (emitPred_transition (parkedInput_parked _) (fun _ => parked_regTape _) []) h₂₃
  apply hall.mono_bound
  omega

end IrrRAFEnumeration.SATSource
