module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailPort
public import proofs.UnconstrainedPACDetection.FormulaRoutedFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailBoundary
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)
open FormulaSwitchTailReentrant (frame parked)

def route (last : Bool) : Equiv.Perm (Fin 21) :=
  (Equiv.swap 3 8).trans (if last then Equiv.swap 1 15 else Equiv.refl _)

def query (last : Bool) : TM 21 :=
  VerifierWorkPermutation.machine (placeWorkTM 0 17 (FormulaEqualityPair.query last)) (route last)

theorem query_hoare (last : Bool) (i r a L V C : Nat) (inp : Tape) (hi : Parked inp)
    (ys : List Bool) : (query last).HoareTime
      (EmitPred inp (frame i r a L V C) ys)
      (EmitPred inp (frame i r a L V C)
        (ys ++ [decide (i+(if last then 1 else 0)=(if last then L else 0))]))
      (4*i+3*max (i+1) (if last then L else 0)+32) := by
  apply FormulaRoutedFrame.hoare _ 0 17 (route last) inp
    (FormulaEqualityPair.small i (if last then L else 0)) (frame i r a L V C)
    _ _ _ (parked _ _ _ _ _ _) _ (FormulaEqualityPair.query_hoare last i _ ys inp hi)
  intro t
  cases last <;> fin_cases t <;>
    simp [route,Equiv.swap_apply_def,placeWorkIdx,frame,FormulaSwitchTailHeads.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.bank,FormulaSwitchVariableHeads.extend,
      FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,
      FormulaRailHeadPrepare.bank,FormulaEqualityPair.small,FormulaClauseCompare.bank]
  exact FormulaEndpointRegisters.unary_word 0

end UnconstrainedPACDetection.FormulaSwitchTailBoundary
