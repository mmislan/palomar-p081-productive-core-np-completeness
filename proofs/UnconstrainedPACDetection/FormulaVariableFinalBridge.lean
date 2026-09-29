module

public import proofs.UnconstrainedPACDetection.FormulaVariableTailInit

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableFinalBridge
open Complexity Complexity.TM
open FormulaWiring (levels varCount)
open FormulaRailHeadPrepare (bank parked)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

def core : TM 17 := seqTM (copyIntoTM 15 6)
  (seqTM (incRegTM 6) (seqTM (copyIntoTM 15 14) (incRegTM 14)))

theorem core_hoare (i r a L V M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hL : L ≤ M) : core.HoareTime (EmitPred inp (bank i V 0 r a 0 0 L V) ys)
      (EmitPred inp (bank i V (L+1) r a 0 (L+1) L V) ys) (4*opBudget M+3) := by
  have h0 := (copyIntoTM_hoareTime (15 : Fin 17) 6 (by decide) L 0 inp (bank i V 0 r a 0 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hL (Nat.zero_le _))
  have he0 : Function.update (bank i V 0 r a 0 0 L V) 6 (regTape L) = bank i V L r a 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  have h1 := (incRegTM_hoareTime (6 : Fin 17) L inp (bank i V L r a 0 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (incRegTM_le_opBudget hL)
  have he1 : Function.update (bank i V L r a 0 0 L V) 6 (regTape (L+1)) = bank i V (L+1) r a 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := (copyIntoTM_hoareTime (15 : Fin 17) 14 (by decide) L 0 inp (bank i V (L+1) r a 0 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hL (Nat.zero_le _))
  have he2 : Function.update (bank i V (L+1) r a 0 0 L V) 14 (regTape L) = bank i V (L+1) r a 0 L L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  have h3 := (incRegTM_hoareTime (14 : Fin 17) L inp (bank i V (L+1) r a 0 L L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (incRegTM_le_opBudget hL)
  have he3 : Function.update (bank i V (L+1) r a 0 L L V) 14 (regTape (L+1)) = bank i V (L+1) r a 0 (L+1) L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he3] at h3
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h3
  have h123 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h23
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h123).mono_bound (by omega)

def machine : TM 21 := placeWorkTM 0 4 core

theorem hoare (φ : SAT.CNF) (r : Nat) (ys : List Bool) : machine.HoareTime
    (EmitPred (word φ.encode) (FormulaVariableTailLoop.frame (varCount φ) r
      (levels φ) (varCount φ) φ.length (regTape (varCount φ))) ys)
    (EmitPred (word φ.encode) (FormulaChangingFrame.extend
      (FormulaFinalVariableClauseLoop.bank (varCount φ) 0 r (20*levels φ+varCount φ) 0
        (levels φ) (varCount φ) φ.length (regTape (levels φ))) (regTape (varCount φ))) ys)
    (4*opBudget (cap φ)+3) := by
  have hL : levels φ ≤ cap φ := by
    have h := (FormulaEnumeration.parameter_bounds φ).1
    unfold cap; nlinarith
  have h := core_hoare (varCount φ) r (20*levels φ+varCount φ) (levels φ) (varCount φ) (cap φ)
    (word φ.encode) (word_parked _) ys hL
  apply FormulaChangingFrame.hoare _ 0 4 _ _ _ _ _ _ _ _
    (FormulaVariableTailLoop.parked _ _ _ _ _ _ (parked_regTape _)) _ _ _ h
  · intro t; fin_cases t <;> rfl
  · intro t; fin_cases t <;> first | rfl | exact (FormulaEndpointRegisters.unary_word 0).symm
  · intro t ht
    fin_cases t <;> simp_all [placeWorkInMiddle,FormulaVariableTailLoop.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaRailHeadVariables.extend,
      FormulaFinalVariableClauseLoop.bank]

end UnconstrainedPACDetection.FormulaVariableFinalBridge
