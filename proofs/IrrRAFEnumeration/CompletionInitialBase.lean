module

public import proofs.IrrRAFEnumeration.CompletionQueryClock

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

/-- Reuse the existing emitter after one shared whole-machine entry bump. -/
def parkedBaseCompilerTM : TM 23 :=
  seqTM (seqTM (dimensionRegsTM 12 13) rewindInputTM)
    (seqTM baseBankTM baseEmitTM)

theorem existingBaseEmit_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] :
    baseEmitTM.HoareTime
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseBankValues d r)) [])
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseRunState d r 6))
        (SAT.CNF.encode (assembledBase (decC := decC) Q C)))
      (6*(baseRunPhaseTime
        (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).length+1)+1) := by
  let z := inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)
  let Y : Nat → List Bool := @baseRunOutput d r Q C decC
  let A : List Bool := SAT.CNF.encode (assembledBase (decC := decC) Q C)
  have h := bigSeqTM_hoareTime ((List.finRange 6).map baseRunPhaseTM)
    (parkedInput z) (fun k => baseRegWork (baseRunState d r k)) Y
    (baseRunPhaseTime z.length) (parkedInput_parked z) (fun _ _ => parked_regTape _) (by
      intro k hk
      have hk6 : k < 6 := by simpa using hk
      have hh := baseRunPhaseTM_correct (decC := decC) Q C ⟨k,hk6⟩ (Y k)
      have hy := baseRunOutput_succ (decC := decC) Q C ⟨k,hk6⟩
      change Y k ++ SAT.CNF.encode (basePhaseClauses (decC := decC) Q C ⟨k,hk6⟩) =
        Y (k+1) at hy
      rw [hy] at hh
      have hfin : (List.finRange 6)[k]'(List.length_map baseRunPhaseTM ▸ hk) =
          (⟨k,hk6⟩ : Fin 6) := by
        apply Fin.ext
        interval_cases k <;> rfl
      have hm : ((List.finRange 6).map baseRunPhaseTM)[k]'hk =
          baseRunPhaseTM ⟨k,hk6⟩ := by
        rw [List.getElem_map]
        exact congrArg baseRunPhaseTM hfin
      rw [hm]
      exact hh)
  have hfull : Y 6 = A := by
    let f : Fin 6 → SAT.CNF := @basePhaseClauses d r Q C decC
    change SAT.CNF.encode (((List.finRange 6).take 6).flatMap f) =
      SAT.CNF.encode
        ([PositiveCompletionCNF.positive ((List.finRange r).map PositiveCompletionCNF.selectVar)] ++
          initialFoodClauses Q ++
          (List.finRange d).flatMap (firingLayerClauses Q) ++
          (List.finRange d).flatMap (supportLayerClauses Q) ++
          (List.finRange r).flatMap (reactantClauses Q) ++
          (List.finRange r).map (@catalystClause d r C decC))
    rw [show List.finRange 6 = [0,1,2,3,4,5] by decide]
    rw [show List.take 6 ([0,1,2,3,4,5] : List (Fin 6)) = [0,1,2,3,4,5] by rfl]
    have hflat : List.flatMap f ([0,1,2,3,4,5] : List (Fin 6)) =
        f 0 ++ (f 1 ++ (f 2 ++ (f 3 ++ (f 4 ++ (f 5 ++ []))))) := by
      simp only [List.flatMap_cons,List.flatMap_nil]
    have h0 : f 0 =
        [PositiveCompletionCNF.positive ((List.finRange r).map PositiveCompletionCNF.selectVar)] := rfl
    have h1 : f 1 = initialFoodClauses Q := rfl
    have h2 : f 2 = (List.finRange d).flatMap (firingLayerClauses Q) := rfl
    have h3 : f 3 = (List.finRange d).flatMap (supportLayerClauses Q) := rfl
    have h4 : f 4 = (List.finRange r).flatMap (reactantClauses Q) := rfl
    have h5 : f 5 = (List.finRange r).map (@catalystClause d r C decC) := rfl
    have hassoc (a b c d e g : SAT.CNF) :
        a ++ (b ++ (c ++ (d ++ (e ++ g)))) = ((((a ++ b) ++ c) ++ d) ++ e) ++ g := by
      simp only [List.append_assoc]
    rw [hflat,h0,h1,h2,h3,h4,h5,List.append_nil]
    exact congrArg SAT.CNF.encode (hassoc _ _ _ _ _ _)
  have hz : Y 0 = [] := by
    unfold Y baseRunOutput
    rfl
  simp only [List.length_map,List.length_finRange,hfull,hz] at h
  exact h

theorem parkedBaseCompiler_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] :
    parkedBaseCompilerTM.HoareTime
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (fun _ => regTape 0) [])
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseRunState d r 6))
        (SAT.CNF.encode (assembledBase (decC := decC) Q C)))
      (baseCompilerTime
        (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).length) := by
  let z := inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)
  let W := Function.update (Function.update (fun _ : Fin 23 => regTape 0) 12 (regTape d))
    13 (regTape r)
  have hw : ∀ i, Parked (W i) :=
    updateReg_parked _ (updateReg_parked _ (fun _ => parked_regTape _) _ _) _ _
  have hdim := seqTM_hoareTime _ _
    (originalDimensionRegs_correct (decC := decC) Q C (12 : Fin 23) 13 (by decide)
      (fun _ => regTape 0) [] (fun _ => parked_regTape _) rfl rfl)
    (emitPred_transition (advanceInput_parked _ _ (parkedInput_parked z)) hw [])
    (rewindParsedInput_correct z (d+r+2) W [] hw)
  have he : W = baseRegWork (baseBankInitial d r) := by
    simp only [baseBankInitial,baseRegWork_update]
    rfl
  rw [he] at hdim
  have hbank := baseBankTM_correct d r (parkedInput z) [] (parkedInput_parked z)
  rw [baseBankStage_final] at hbank
  have htail := seqTM_hoareTime _ _ hbank
    (emitPred_transition (parkedInput_parked z) (fun _ => parked_regTape _) [])
    (existingBaseEmit_correct (decC := decC) Q C)
  have h := seqTM_hoareTime _ _ hdim
    (emitPred_transition (parkedInput_parked z) (fun _ => parked_regTape _) []) htail
  apply h.mono_bound
  have hd : d ≤ z.length := by
    dsimp [z]
    unfold inputBits
    repeat rw [List.length_append]
    repeat rw [List.length_replicate]
    omega
  have hr : r ≤ z.length := by
    dsimp [z]
    unfold inputBits
    repeat rw [List.length_append]
    repeat rw [List.length_replicate]
    omega
  have hc : baseBankCap d r ≤ 10*(z.length+1)^2 := by
    have hdd := Nat.mul_le_mul hd hd
    unfold baseBankCap
    nlinarith
  have hb : opBudget (baseBankCap d r) ≤ opBudget (10*(z.length+1)^2) := by
    unfold opBudget
    gcongr
  change (2*d+2*r+5)+1+(d+r+2+3)+1+
    ((19*(opBudget (baseBankCap d r)+1)+1)+1+
      (6*(baseRunPhaseTime z.length+1)+1)) ≤ baseCompilerTime z.length
  unfold baseCompilerTime basePreparationTime
  omega

/-- Base bytes are stored in a fixed extra bank, preserving the original CRS input. -/
theorem placedParkedBase_correct {d r : Nat} (n : Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r))
    [decC : DecidableRel C] :
    (placeWorkTM n 0 parkedBaseCompilerTM.retargetOutput).HoareTime
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (placedClockWork n 0 (fun _ => regTape 0)
          (frameWork (m := 1) (fun _ : Fin 23 => regTape 0)
            (fun _ => accumulatorTape []))) [])
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (placedClockWork n 0 (fun _ => regTape 0)
          (frameWork (m := 1) (baseRegWork (baseRunState d r 6))
            (fun _ => accumulatorTape
              (SAT.CNF.encode (assembledBase (decC := decC) Q C))))) [])
      (baseCompilerTime
        (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).length) := by
  exact placeEmitter_correct _ n 0 (fun _ => regTape 0) (fun _ _ => parked_regTape _)
    _ _ _ _ _ _ _ (redirectEmitter_correct _ _ _ _ _ _ _ _
      (parkedBaseCompiler_correct (decC := decC) Q C))

end IrrRAFEnumeration.CompletionQuery
