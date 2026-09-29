module

public import proofs.UnconstrainedPACDetection.FormulaVariableFinalBridge

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseFrameReturn
open Complexity Complexity.TM
open FormulaFinalVariableClauseLoop (bank parked)

def common (r L V C : Nat) : Fin 20 → Tape := FormulaSwitchVariableHeads.bank 0 V 0 r 0 0 0 L V L C

def machine : TM 20 := seqTM (clearRegTM 3)
  (seqTM (placeWorkTM 0 3 FormulaRailTailReset.machine) (copyIntoTM 15 17))

theorem hoare (i c r a b L V C g M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hiM : i ≤ M) (hc : c ≤ M) (ha : a ≤ M) (hb : b ≤ M) (hL : L+1 ≤ M) (hg : g ≤ M) :
    machine.HoareTime (EmitPred inp (bank i c r a b L V C (regTape g)) ys)
      (EmitPred inp (common r L V C) ys) (7*opBudget M+6) := by
  have h0 := (clearRegTM_hoareTime (3 : Fin 20) c inp (bank i c r a b L V C (regTape g)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl).mono_bound (clearRegTM_le_opBudget hc)
  have he0 : Function.update (bank i c r a b L V C (regTape g)) 3 (regTape 0) =
      bank i 0 r a b L V C (regTape g) := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  let mid := FormulaSwitchVariableHeads.bank 0 V 0 r 0 0 0 L V g C
  have hs := FormulaRailTailReset.hoare i V (L+1) r a b (L+1) L V M inp hi ys hiM hL ha hb hL
  have h1 : (placeWorkTM 0 3 FormulaRailTailReset.machine).HoareTime
      (EmitPred inp (bank i 0 r a b L V C (regTape g)) ys) (EmitPred inp mid ys) (5*opBudget M+4) := by
    apply FormulaChangingFrame.hoare _ 0 3 _ _ _ _ _ _ _ _
      (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _ _ _ hs
    · intro t; fin_cases t <;> first | rfl | exact (FormulaEndpointRegisters.unary_word 0).symm
    · intro t; fin_cases t <;> rfl
    · intro t ht
      fin_cases t <;> simp_all [placeWorkInMiddle,bank,mid,FormulaSwitchVariableHeads.bank,
        FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
        FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  have h2 := (copyIntoTM_hoareTime (15 : Fin 20) 17 (by decide) L g inp mid ys hi
    (fun t _ => FormulaSwitchVariableHeads.parked _ _ _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound
      (copyIntoTM_le_opBudget (by omega) hg)
  have he2 : Function.update mid 17 (regTape L) = common r L V C := by
    funext t; fin_cases t <;> simp [mid,common,FormulaSwitchVariableHeads.bank,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he2] at h2
  have h12 := seqTM_hoareTime _ _ h1
    (emitPred_transition hi (FormulaSwitchVariableHeads.parked _ _ _ _ _ _ _ _ _ _ _) _) h2
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h12).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaClauseFrameReturn
