module

public import proofs.UnconstrainedPACDetection.FormulaClauseTailLoop

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseTailStageFinish
open Complexity Complexity.TM

def frame (r a b L V C g h : Nat) : Fin 21 → Tape := FormulaChangingFrame.extend
  (FormulaFinalVariableClauseLoop.bank 0 0 r a b L V C (regTape g)) (regTape h)

theorem parked (r a b L V C g h : Nat) : ∀ t, Parked (frame r a b L V C g h t) :=
  FormulaChangingFrame.parked _ _ (FormulaFinalVariableClauseLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _)

def machine : TM 21 := seqTM (copyIntoTM 11 10)
  (seqTM (clearRegTM 11) (seqTM (copyIntoTM 18 17) (copyIntoTM 15 20)))

theorem hoare (r B L V C f M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hB : B ≤ M) (hL : L ≤ M) (hC : C ≤ M) (hf : f ≤ M) :
    machine.HoareTime (EmitPred inp (frame r 0 B L V C L f) ys)
      (EmitPred inp (frame r B 0 L V C C L) ys) (4*opBudget M+3) := by
  have h0 := (copyIntoTM_hoareTime (11 : Fin 21) 10 (by decide) B 0 inp (frame r 0 B L V C L f) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hB (Nat.zero_le _))
  have he0 : Function.update (frame r 0 B L V C L f) 10 (regTape B) = frame r B B L V C L f := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaFinalVariableClauseLoop.bank]
  rw [he0] at h0
  have h1 := (clearRegTM_hoareTime (11 : Fin 21) B inp (frame r B B L V C L f) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hB)
  have he1 : Function.update (frame r B B L V C L f) 11 (regTape 0) = frame r B 0 L V C L f := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaFinalVariableClauseLoop.bank]
  rw [he1] at h1
  have h2 := (copyIntoTM_hoareTime (18 : Fin 21) 17 (by decide) C L inp (frame r B 0 L V C L f) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hC hL)
  have he2 : Function.update (frame r B 0 L V C L f) 17 (regTape C) = frame r B 0 L V C C f := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaFinalVariableClauseLoop.bank]
  rw [he2] at h2
  have h3 := (copyIntoTM_hoareTime (15 : Fin 21) 20 (by decide) L f inp (frame r B 0 L V C C f) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hL hf)
  have he3 : Function.update (frame r B 0 L V C C f) 20 (regTape L) = frame r B 0 L V C C L := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend]
  rw [he3] at h3
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (parked _ _ _ _ _ _ _ _) _) h3
  have h123 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _) _) h23
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _) _) h123).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaClauseTailStageFinish
