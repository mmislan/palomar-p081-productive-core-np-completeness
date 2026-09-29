module

public import proofs.UnconstrainedPACDetection.FormulaClauseTailInit

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseTailReturn
open Complexity Complexity.TM
open FormulaWiring (levels varCount)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

theorem head_frame (i c r a b L V C : Nat) (fuel : Tape) :
    FormulaClauseTailHeads.frame i c r a b L V C fuel = FormulaChangingFrame.extend
      (FormulaFinalVariableClauseLoop.bank i c r a b L V C (regTape C)) fuel := by
  funext t; fin_cases t <;> rfl

def core : TM 21 := seqTM (placeWorkTM 0 1 FormulaClauseFrameReturn.machine) (copyIntoTM 16 20)

theorem core_hoare (φ : SAT.CNF) (r : Nat) (ys : List Bool) :
    core.HoareTime
      (EmitPred (word φ.encode) (FormulaClauseTailHeads.frame 0 φ.length r
        (FormulaClauseCursor.base φ+φ.length) 0 (levels φ) (varCount φ) φ.length (regTape (levels φ))) ys)
      (EmitPred (word φ.encode) (FormulaAllRailTails.frame (varCount φ) r
        (levels φ) (varCount φ) φ.length (regTape (varCount φ))) ys) (8*opBudget (cap φ)+7) := by
  obtain ⟨hL,hV,hC⟩ := FormulaEnumeration.parameter_bounds φ
  have hLc : levels φ+1 ≤ cap φ := by unfold cap; nlinarith
  have hVc : varCount φ ≤ cap φ := by unfold cap; nlinarith
  have hCc : φ.length ≤ cap φ := by unfold cap; nlinarith
  have hA : FormulaClauseCursor.base φ+φ.length ≤ cap φ := by
    have he := congrArg List.length (FormulaClauseCursor.labels φ)
    simp only [List.length_append,FormulaClauseCursor.initialVertices_length,List.length_map,List.length_finRange] at he
    have hn := FormulaIndexedGraph.labels_bound φ
    have hb : FormulaClauseCursor.base φ+φ.length ≤ (FormulaIndexedGraph.labels φ).length := by omega
    apply hb.trans (hn.trans _)
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have h0 := FormulaClauseFrameReturn.hoare 0 φ.length r (FormulaClauseCursor.base φ+φ.length) 0
    (levels φ) (varCount φ) φ.length φ.length (cap φ) (word φ.encode) (word_parked _) ys
    (Nat.zero_le _) hCc hA (Nat.zero_le _) hLc hCc
  have h0' := FormulaChangingFrame.append_hoare _ _ _ _ (regTape (levels φ)) _ _ _
    (FormulaFinalVariableClauseLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _) h0
  rw [← head_frame] at h0'
  have h1 := (copyIntoTM_hoareTime (16 : Fin 21) 20 (by decide) (varCount φ) (levels φ)
    (word φ.encode) (FormulaAllRailTails.frame (varCount φ) r (levels φ) (varCount φ) φ.length (regTape (levels φ)))
    ys (word_parked _) (fun t _ => FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _) t) rfl rfl).mono_bound
      (copyIntoTM_le_opBudget hVc (by omega : levels φ ≤ cap φ))
  have he : Function.update (FormulaAllRailTails.frame (varCount φ) r (levels φ) (varCount φ) φ.length (regTape (levels φ)))
      20 (regTape (varCount φ)) = FormulaAllRailTails.frame (varCount φ) r
        (levels φ) (varCount φ) φ.length (regTape (varCount φ)) := by
    funext t; fin_cases t <;> simp [FormulaAllRailTails.frame,FormulaChangingFrame.extend]
  rw [he] at h1
  exact (seqTM_hoareTime _ _ h0'
    (emitPred_transition (word_parked _) (FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _)) _) h1).mono_bound (by omega)

def machine : TM 22 := placeWorkTM 0 1 core

theorem hoare (φ : SAT.CNF) (r : Nat) (ys : List Bool) : machine.HoareTime
    (EmitPred (word φ.encode) (FormulaClauseTailLoop.frame φ.length r (FormulaClauseCursor.base φ)
      (levels φ) (varCount φ) φ.length (regTape φ.length)) ys)
    (EmitPred (word φ.encode) (FormulaClauseTailInit.frame r (levels φ) (varCount φ) φ.length
      (varCount φ) φ.length) ys) (8*opBudget (cap φ)+7) := by
  exact FormulaChangingFrame.append_hoare _ _ _ _ (regTape φ.length) _ _ _
    (FormulaClauseTailHeads.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _)
    (core_hoare φ r ys)

end UnconstrainedPACDetection.FormulaClauseTailReturn
