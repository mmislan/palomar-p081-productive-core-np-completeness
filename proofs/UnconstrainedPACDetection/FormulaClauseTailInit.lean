module

public import proofs.UnconstrainedPACDetection.FormulaClauseTailStageFinish

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseTailInit
open Complexity Complexity.TM
open FormulaWiring (levels varCount)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

def core : TM 21 := seqTM (placeWorkTM 0 4 FormulaVariableFinalBridge.core)
  (seqTM (placeWorkTM 0 1 FormulaFinalVariablePrepare.base) FormulaClauseTailStageFinish.machine)

theorem core_hoare (φ : SAT.CNF) (r f : Nat) (ys : List Bool) (hf : f ≤ cap φ) :
    core.HoareTime
      (EmitPred (word φ.encode) (FormulaAllRailTails.frame (varCount φ) r
        (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (FormulaClauseTailHeads.frame 0 0 r (FormulaClauseCursor.base φ) 0
        (levels φ) (varCount φ) φ.length (regTape (levels φ))) ys) (48*(opBudget (cap φ)+1)) := by
  obtain ⟨hL,hV,hC⟩ := FormulaEnumeration.parameter_bounds φ
  have hLc : levels φ ≤ cap φ := by unfold cap; nlinarith
  have hVc : varCount φ ≤ cap φ := by unfold cap; nlinarith
  have hCc : φ.length ≤ cap φ := by unfold cap; nlinarith
  have hB : FormulaClauseCursor.base φ ≤ cap φ := by
    have he := congrArg List.length (FormulaClauseCursor.labels φ)
    simp only [List.length_append,FormulaClauseCursor.initialVertices_length,List.length_map,List.length_finRange] at he
    have hn := FormulaIndexedGraph.labels_bound φ
    have hb : FormulaClauseCursor.base φ ≤ (FormulaIndexedGraph.labels φ).length := by omega
    apply hb.trans (hn.trans _)
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have hs := FormulaVariableFinalBridge.core_hoare 0 r 0 (levels φ) (varCount φ) (cap φ)
    (word φ.encode) (word_parked _) ys hLc
  have h0 : (placeWorkTM 0 4 FormulaVariableFinalBridge.core).HoareTime
      (EmitPred (word φ.encode) (FormulaAllRailTails.frame (varCount φ) r (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (FormulaClauseTailStageFinish.frame r 0 0 (levels φ) (varCount φ) φ.length (levels φ) f) ys)
      (4*opBudget (cap φ)+3) := by
    apply FormulaChangingFrame.hoare _ 0 4 _ _ _ _ _ _ _ _
      (FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _)) _ _ _ hs
    · intro t; fin_cases t <;> rfl
    · intro t; fin_cases t <;> first | rfl | exact (FormulaEndpointRegisters.unary_word 0).symm
    · intro t ht
      fin_cases t <;> simp_all [placeWorkInMiddle,FormulaAllRailTails.frame,FormulaClauseTailStageFinish.frame,
        FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
        FormulaRailTailReentrant.frame,FormulaRailHeadVariables.extend,FormulaFinalVariableClauseLoop.bank]
  have hb := FormulaFinalVariablePrepare.base_hoare 0 0 r 0 0 (levels φ) (varCount φ) φ.length (cap φ)
    (regTape (levels φ)) (parked_regTape _) (word φ.encode) (word_parked _) ys hLc hVc (Nat.zero_le _) hB
  have h1 := FormulaChangingFrame.append_hoare _ _ _ _ (regTape f) _ _ _
    (FormulaFinalVariableClauseLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _) hb
  have h2 := FormulaClauseTailStageFinish.hoare r (FormulaClauseCursor.base φ) (levels φ) (varCount φ)
    φ.length f (cap φ) (word φ.encode) (word_parked _) ys hB hLc hCc hf
  have h12 := seqTM_hoareTime _ _ h1
    (emitPred_transition (word_parked _) (FormulaClauseTailStageFinish.parked _ _ _ _ _ _ _ _) _) h2
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (FormulaClauseTailStageFinish.parked _ _ _ _ _ _ _ _) _) h12
  have he : FormulaClauseTailStageFinish.frame r (FormulaClauseCursor.base φ) 0
      (levels φ) (varCount φ) φ.length φ.length (levels φ) =
      FormulaClauseTailHeads.frame 0 0 r (FormulaClauseCursor.base φ) 0
        (levels φ) (varCount φ) φ.length (regTape (levels φ)) := by
    funext t; fin_cases t <;> rfl
  rw [he] at h
  exact h.mono_bound (by omega)

def frame (r L V C f g : Nat) : Fin 22 → Tape :=
  FormulaChangingFrame.extend (FormulaAllRailTails.frame V r L V C (regTape f)) (regTape g)

theorem parked (r L V C f g : Nat) : ∀ t, Parked (frame r L V C f g t) :=
  FormulaChangingFrame.parked _ _ (FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _)

def machine : TM 22 := seqTM (placeWorkTM 0 1 core) (copyIntoTM 18 21)

theorem hoare (φ : SAT.CNF) (r f g : Nat) (ys : List Bool) (hf : f ≤ cap φ) (hg : g ≤ cap φ) :
    machine.HoareTime (EmitPred (word φ.encode) (frame r (levels φ) (varCount φ) φ.length f g) ys)
      (EmitPred (word φ.encode) (FormulaClauseTailLoop.frame 0 r (FormulaClauseCursor.base φ)
        (levels φ) (varCount φ) φ.length (regTape φ.length)) ys) (49*(opBudget (cap φ)+1)) := by
  have h0 := core_hoare φ r f ys hf
  have h0' := FormulaChangingFrame.append_hoare _ _ _ _ (regTape g) _ _ _
    (FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _) h0
  have hC : φ.length ≤ cap φ := by
    have h := (FormulaEnumeration.parameter_bounds φ).2.2
    unfold cap; nlinarith
  have h1 := (copyIntoTM_hoareTime (18 : Fin 22) 21 (by decide) φ.length g (word φ.encode)
    (FormulaClauseTailLoop.frame 0 r (FormulaClauseCursor.base φ) (levels φ) (varCount φ) φ.length (regTape g))
    ys (word_parked _) (fun t _ => FormulaClauseTailLoop.parked _ _ _ _ _ _ _ (parked_regTape _) t) rfl rfl).mono_bound
      (copyIntoTM_le_opBudget hC hg)
  have he : Function.update (FormulaClauseTailLoop.frame 0 r (FormulaClauseCursor.base φ)
      (levels φ) (varCount φ) φ.length (regTape g)) 21 (regTape φ.length) =
      FormulaClauseTailLoop.frame 0 r (FormulaClauseCursor.base φ) (levels φ) (varCount φ) φ.length (regTape φ.length) := by
    funext t; fin_cases t <;> simp [FormulaClauseTailLoop.frame,FormulaChangingFrame.extend]
  rw [he] at h1
  exact (seqTM_hoareTime _ _ h0'
    (emitPred_transition (word_parked _) (FormulaClauseTailLoop.parked _ _ _ _ _ _ _ (parked_regTape _)) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaClauseTailInit
