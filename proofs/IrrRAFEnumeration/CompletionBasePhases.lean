module

public import proofs.IrrRAFEnumeration.CompletionBaseLoad

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def basePhasePre (d r : Nat) (p : Fin 6) : Fin 23 → Nat :=
  baseLoadStage (baseBankValues d r) (baseLoadSources p) 12

def basePhaseScratch (d r : Nat) (p : Fin 6) : Fin 12 → Nat :=
  match p.val with
  | 0 => ![r,r,0,0,0,0,0,0,0,0,0,0]
  | 1 => ![d,2*d+r+3,r+d,0,0,0,0,0,0,0,0,0]
  | 2 => ![d,2*d+r+3,r+d*d,0,firingBase d r d,r,r+d*d,0,2*d+r+3,d,0,0]
  | 3 => ![r,3*d+r+3,firingBase d r d,0,3*d,r+(d+1)*d,r+d*d,d,
            3*d+r+3,firingBase d r d,3*d+r+3,d]
  | 4 => ![d,2*d+r+3+3*d*r,r+d*d,0,r,r,r+d*d,0,0,0,0,0]
  | _ => ![d,4*d+r+3+3*d*r,r+d*d,0,r,r,r+d*d,0,0,0,0,0]

def basePhasePost (d r : Nat) (p : Fin 6) (q : Fin 23) : Nat :=
  if h : q.val < 12 then basePhaseScratch d r p ⟨q.val,h⟩ else baseBankValues d r q

def basePhaseClauses {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (p : Fin 6) : SAT.CNF :=
  match p.val with
  | 0 => [PositiveCompletionCNF.positive ((List.finRange r).map PositiveCompletionCNF.selectVar)]
  | 1 => initialFoodClauses Q
  | 2 => (List.finRange d).flatMap (firingLayerClauses Q)
  | 3 => (List.finRange d).flatMap (supportLayerClauses Q)
  | 4 => (List.finRange r).flatMap (reactantClauses Q)
  | _ => (List.finRange r).map (@catalystClause d r C decC)

def basePhaseTM (p : Fin 6) : TM 23 :=
  match p.val with
  | 0 => rangeClauseTM true 0 1
  | 1 => maskScanTM.liftTM 19
  | 2 => firingFamilyTM.liftTM 13
  | 3 => supportFamilyTM.liftTM 11
  | 4 => reactantFamilyTM.liftTM 16
  | _ => catalystFamilyTM.liftTM 16

def basePhaseTime (d r : Nat) (p : Fin 6) : Nat :=
  match p.val with
  | 0 => r*(5*r+16)+r+5
  | 1 => d*(5*(d+r+3)+5*r+10*d+53)+d+2
  | 2 => d*(firingFamilyStepBudget d r+2)+d+2
  | 3 => d*(supportFamilyStepBudget d r+2)+d+2
  | 4 => r*(reactantStepBudget d r+2)+r+2
  | _ => r*(catalystStepBudget d r+2)+r+2

set_option maxHeartbeats 1000000 in
theorem basePhaseTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (p : Fin 6) (ys : List Bool) :
    (basePhaseTM p).HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (basePhasePre d r p)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (basePhasePost d r p)) (ys++SAT.CNF.encode (basePhaseClauses Q C p)))
      (basePhaseTime d r p) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let bank := baseRegWork (baseBankValues d r)
  change (basePhaseTM p).HoareTime
    (EmitPred inp (baseRegWork (basePhasePre d r p)) ys)
    (EmitPred inp (baseRegWork (basePhasePost d r p))
      (ys++SAT.CNF.encode (basePhaseClauses (decC := decC) Q C p)))
    (basePhaseTime d r p)
  have hp : Parked inp := parkedInput_parked _
  have he : ∀ i, Parked (bank i) := fun _ => parked_regTape _
  fin_cases p
  · have h := rangeClauseTM_correct true (0 : Fin 23) 1 (by decide) 0 r inp
      (baseRegWork (basePhasePre d r 0)) ys hp (fun _ => parked_regTape _) rfl rfl
    have hw : Function.update (baseRegWork (basePhasePre d r 0)) 1 (regTape (0+r)) =
        baseRegWork (basePhasePost d r 0) := by
      funext i
      fin_cases i <;> first | rfl | exact congrArg regTape (Nat.zero_add r)
    rw [hw,rangeLiterals_selection] at h
    unfold basePhaseTM basePhaseClauses
    convert h using 1 <;> simp [basePhaseTime]
  · have h0 := maskScanTM_correct inp (d+r+3) r d ys hp rfl rfl
    rw [original_food_maskClauses (decC := decC) Q C] at h0
    have h := liftTM_frame_correct maskScanTM 19 bank (fun i _ => he i)
      inp inp (maskWork (regTape d) (d+r+3) r 0) (maskWork (regTape d) (d+r+3+d) (r+d) 0) _ _ _ h0
    have hi : frameWork (m := 19) (maskWork (regTape d) (d+r+3) r 0) bank = baseRegWork (basePhasePre d r 1) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePre,baseLoadStage,baseLoadValue,
          baseLoadSources,bankSource,baseBankValues,maskWork]
      all_goals congr 1
    have ho : frameWork (m := 19) (maskWork (regTape d) (d+r+3+d) (r+d) 0) bank = baseRegWork (basePhasePost d r 1) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePost,basePhaseScratch,baseBankValues,maskWork]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    rw [hi,ho] at h
    exact h
  · have h0 := firingFamilyTM_correct (decC := decC) Q C ys
    have h := liftTM_frame_correct firingFamilyTM 13 bank (fun i _ => he i)
      inp inp (firingOuterWork d (reactantStart d r 0) r r (firingBase d r 0) 0 r (reactantStart d r 0) (regTape d)) (firingOuterWork d (reactantStart d r 0) (r+d*d) (r+d*d) (firingBase d r d) 0 r (reactantStart d r 0) (regTape d)) _ _ _ h0
    have hi : frameWork (m := 13) (firingOuterWork d (reactantStart d r 0) r r (firingBase d r 0) 0 r (reactantStart d r 0) (regTape d)) bank = baseRegWork (basePhasePre d r 2) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePre,baseLoadStage,baseLoadValue,
          baseLoadSources,bankSource,baseBankValues,firingOuterWork,firingWork,catalystFamilyWork,reactantStart,firingBase]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    have ho : frameWork (m := 13) (firingOuterWork d (reactantStart d r 0) (r+d*d) (r+d*d) (firingBase d r d) 0 r (reactantStart d r 0) (regTape d)) bank = baseRegWork (basePhasePost d r 2) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePost,basePhaseScratch,baseBankValues,firingOuterWork,firingWork,catalystFamilyWork,reactantStart,firingBase]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    rw [hi,ho] at h
    exact h
  · have h0 := supportFamilyTM_correct (decC := decC) Q C ys
    have h := liftTM_frame_correct supportFamilyTM 11 bank (fun i _ => he i)
      inp inp (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r 0) (r+d) r (outputStart d r 0) (firingBase d r 0) d (outputStart d r 0) (regTape d)) (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r d) (r+(d+1)*d) (r+d*d) (outputStart d r 0) (firingBase d r d) d (outputStart d r 0) (regTape d)) _ _ _ h0
    have hi : frameWork (m := 11) (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r 0) (r+d) r (outputStart d r 0) (firingBase d r 0) d (outputStart d r 0) (regTape d)) bank = baseRegWork (basePhasePre d r 3) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePre,baseLoadStage,baseLoadValue,
          baseLoadSources,bankSource,baseBankValues,supportOuterWork,supportLayerWork,supportWork,strideWork,outputStart,firingBase]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    have ho : frameWork (m := 11) (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r d) (r+(d+1)*d) (r+d*d) (outputStart d r 0) (firingBase d r d) d (outputStart d r 0) (regTape d)) bank = baseRegWork (basePhasePost d r 3) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePost,basePhaseScratch,baseBankValues,supportOuterWork,supportLayerWork,supportWork,strideWork,outputStart,firingBase]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    rw [hi,ho] at h
    exact h
  · have h0 := reactantFamilyTM_correct Q C ys
    have h := liftTM_frame_correct reactantFamilyTM 16 bank (fun i _ => he i)
      inp inp (catalystFamilyWork d (reactantStart d r 0) (r+d*d) (r+d*d) 0 (regTape r)) (catalystFamilyWork d (reactantStart d r r) (r+d*d) (r+d*d) r (regTape r)) _ _ _ h0
    have hi : frameWork (m := 16) (catalystFamilyWork d (reactantStart d r 0) (r+d*d) (r+d*d) 0 (regTape r)) bank = baseRegWork (basePhasePre d r 4) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePre,baseLoadStage,baseLoadValue,
          baseLoadSources,bankSource,baseBankValues,catalystFamilyWork,reactantStart]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    have ho : frameWork (m := 16) (catalystFamilyWork d (reactantStart d r r) (r+d*d) (r+d*d) r (regTape r)) bank = baseRegWork (basePhasePost d r 4) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePost,basePhaseScratch,baseBankValues,catalystFamilyWork,reactantStart]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    rw [hi,ho] at h
    exact h
  · have h0 := catalystFamilyTM_correct Q C ys
    have h := liftTM_frame_correct catalystFamilyTM 16 bank (fun i _ => he i)
      inp inp (catalystFamilyWork d (catalystStart d r 0) (r+d*d) (r+d*d) 0 (regTape r)) (catalystFamilyWork d (catalystStart d r r) (r+d*d) (r+d*d) r (regTape r)) _ _ _ h0
    have hi : frameWork (m := 16) (catalystFamilyWork d (catalystStart d r 0) (r+d*d) (r+d*d) 0 (regTape r)) bank = baseRegWork (basePhasePre d r 5) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePre,baseLoadStage,baseLoadValue,
          baseLoadSources,bankSource,baseBankValues,catalystFamilyWork,catalystStart]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    have ho : frameWork (m := 16) (catalystFamilyWork d (catalystStart d r r) (r+d*d) (r+d*d) r (regTape r)) bank = baseRegWork (basePhasePost d r 5) := by
      funext i
      fin_cases i <;>
        dsimp [frameWork,bank,baseRegWork,basePhasePost,basePhaseScratch,baseBankValues,catalystFamilyWork,catalystStart]
      all_goals congr 1 <;> norm_num [baseLoadSources,baseLoadStage,baseLoadValue,
        baseBankValues,bankSource,basePhaseScratch] <;> ring
    rw [hi,ho] at h
    exact h

end IrrRAFEnumeration.CompletionQuery
