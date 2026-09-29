module

public import proofs.IrrRAFEnumeration.CompletionBaseRegisters

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def baseBankValues (d r : Nat) : Fin 23 → Nat :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,d,r,d+r,d*d,r+d*d+d,r+d*d,
    d+r+3,2*d+r+3,3*d+r+3,4*d+r+3,3*d]

set_option maxHeartbeats 800000 in
theorem baseBankStage_final (d r : Nat) : baseBankStage d r 19 = baseBankValues d r := by
  funext i
  fin_cases i <;> simp [baseBankStage,baseBankOps,BaseRegOp.eval,baseBankInitial,baseBankValues] <;> omega

def basePreparationTM : TM 23 := seqTM (dimensionInitTM 12 13) baseBankTM

def basePreparationTime (N : Nat) := 6*N+15+19*(opBudget (10*(N+1)^2)+1)

/-- Complete blank-tape initialization of every shared base-emitter address. -/
theorem basePreparationTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] :
    basePreparationTM.HoareTime
      (fun inp work out =>
        inp = Tape.init ((inputBits Q C (Equiv.refl _) (Equiv.refl _)).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseBankValues d r)) [])
      (basePreparationTime (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length) := by
  let z := inputBits Q C (Equiv.refl _) (Equiv.refl _)
  have h₁ := originalDimensionInit_correct (decC := decC) Q C (12 : Fin 23) 13 (by decide)
  have he : Function.update (Function.update (fun _ : Fin 23 => regTape 0) 12 (regTape d))
      13 (regTape r) = baseRegWork (baseBankInitial d r) := by
    simp only [baseBankInitial,baseRegWork_update]
    rfl
  rw [he] at h₁
  have h₂ := baseBankTM_correct d r (parkedInput z) [] (parkedInput_parked z)
  rw [baseBankStage_final] at h₂
  have h := seqTM_hoareTime _ _ h₁
    (emitPred_transition (parkedInput_parked z) (fun _ => parked_regTape _) []) h₂
  apply h.mono_bound
  have hd : d ≤ z.length := by
    dsimp only [z]
    unfold inputBits
    repeat rw [List.length_append]
    repeat rw [List.length_replicate]
    omega
  have hr : r ≤ z.length := by
    dsimp only [z]
    unfold inputBits
    repeat rw [List.length_append]
    repeat rw [List.length_replicate]
    omega
  have hs := Nat.mul_le_mul hd hd
  have hc : baseBankCap d r ≤ 10*(z.length+1)^2 := by
    unfold baseBankCap
    nlinarith
  have hb : opBudget (baseBankCap d r) ≤ opBudget (10*(z.length+1)^2) := by
    unfold opBudget
    gcongr
  change (3*d+3*r+13)+1+(19*(opBudget (baseBankCap d r)+1)+1) ≤ basePreparationTime z.length
  unfold basePreparationTime
  omega

end IrrRAFEnumeration.CompletionQuery
