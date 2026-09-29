module

public import proofs.UnconstrainedPACDetection.FormulaExternalTailPhase

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailReset
open Complexity Complexity.TM
open FormulaSwitchTailHeads (frame frame_parked)

def machine : TM 21 := seqTM (clearRegTM 5) (seqTM (clearRegTM 6)
  (seqTM (clearRegTM 11) (seqTM (clearRegTM 14) (seqTM (copyIntoTM 15 17) (copyIntoTM 16 20)))))

theorem hoare (i v j r a b f L V g C h M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hv : v ≤ M) (hj : j ≤ M) (hb : b ≤ M) (hf : f ≤ M) (hg : g ≤ M) (hh : h ≤ M)
    (hL : L ≤ M) (hV : V ≤ M) :
    machine.HoareTime (EmitPred inp (frame i v j r a b f L V g C h) ys)
      (EmitPred inp (frame i 0 0 r a 0 0 L V L C V) ys) (6*opBudget M+5) := by
  have h0 := (clearRegTM_hoareTime (5 : Fin 21) v inp (frame i v j r a b f L V g C h) ys hi
    (fun t _ => frame_parked _ _ _ _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hv)
  have he0 : Function.update (frame i v j r a b f L V g C h) 5 (regTape 0) = frame i 0 j r a b f L V g C h := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.bank,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he0] at h0
  have h1 := (clearRegTM_hoareTime (6 : Fin 21) j inp (frame i 0 j r a b f L V g C h) ys hi
    (fun t _ => frame_parked _ _ _ _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hj)
  have he1 : Function.update (frame i 0 j r a b f L V g C h) 6 (regTape 0) = frame i 0 0 r a b f L V g C h := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.bank,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he1] at h1
  have h2 := (clearRegTM_hoareTime (11 : Fin 21) b inp (frame i 0 0 r a b f L V g C h) ys hi
    (fun t _ => frame_parked _ _ _ _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hb)
  have he2 : Function.update (frame i 0 0 r a b f L V g C h) 11 (regTape 0) = frame i 0 0 r a 0 f L V g C h := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.bank,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he2] at h2
  have h3 := (clearRegTM_hoareTime (14 : Fin 21) f inp (frame i 0 0 r a 0 f L V g C h) ys hi
    (fun t _ => frame_parked _ _ _ _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hf)
  have he3 : Function.update (frame i 0 0 r a 0 f L V g C h) 14 (regTape 0) = frame i 0 0 r a 0 0 L V g C h := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.bank,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he3] at h3
  have h4 := (copyIntoTM_hoareTime (15 : Fin 21) 17 (by decide) L g inp (frame i 0 0 r a 0 0 L V g C h) ys hi
    (fun t _ => frame_parked _ _ _ _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hL hg)
  have he4 : Function.update (frame i 0 0 r a 0 0 L V g C h) 17 (regTape L) = frame i 0 0 r a 0 0 L V L C h := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.bank,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he4] at h4
  have h5 := (copyIntoTM_hoareTime (16 : Fin 21) 20 (by decide) V h inp (frame i 0 0 r a 0 0 L V L C h) ys hi
    (fun t _ => frame_parked _ _ _ _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hV hh)
  have he5 : Function.update (frame i 0 0 r a 0 0 L V L C h) 20 (regTape V) = frame i 0 0 r a 0 0 L V L C V := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend]
  rw [he5] at h5
  have h45 := seqTM_hoareTime _ _ h4 (emitPred_transition hi (frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h5
  have h345 := seqTM_hoareTime _ _ h3 (emitPred_transition hi (frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h45
  have h2345 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h345
  have h12345 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h2345
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h12345).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaSwitchTailReset
