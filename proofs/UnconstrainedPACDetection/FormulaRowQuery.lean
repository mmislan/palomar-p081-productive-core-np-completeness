module

public import proofs.UnconstrainedPACDetection.FormulaRowBoundary
public import proofs.UnconstrainedPACDetection.FormulaNegativeChain

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRowQuery
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def frame (r L V C S P N : Nat) (fuel : Tape) (t : Fin 28) : Tape :=
  if h : t.val<22 then FormulaAllTails.frame r L V C ⟨t.val,h⟩ else
  if t.val=22 then regTape 1 else if t.val=23 then regTape 4 else
  if t.val=24 then regTape S else if t.val=25 then regTape P else
  if t.val=26 then regTape N else fuel

theorem parked (r L V C S P N : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (frame r L V C S P N fuel t) := by
  intro t; unfold frame; split
  · exact FormulaAllTails.parked _ _ _ _ _
  · split
    · exact parked_regTape _
    · split
      · exact parked_regTape _
      · split
        · exact parked_regTape _
        · split
          · exact parked_regTape _
          · split
            · exact parked_regTape _
            · exact hf

def value (S P : Nat) (q : Fin 4) : Nat := ![1,4,S,P] q

def slot (q : Fin 4) : Fin 28 := ⟨22+q.val,by omega⟩

def route (q : Fin 4) : Equiv.Perm (Fin 28) :=
  ((Equiv.swap 0 9).trans (Equiv.swap 1 (slot q))).trans (Equiv.swap 3 8)

def query (q : Fin 4) : TM 28 :=
  VerifierWorkPermutation.machine (placeWorkTM 0 24 (FormulaEqualityPair.query false)) (route q)

theorem hoare (q : Fin 4) (r L V C S P N : Nat) (fuel : Tape) (hf : Parked fuel)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) : (query q).HoareTime
      (EmitPred inp (frame r L V C S P N fuel) ys)
      (EmitPred inp (frame r L V C S P N fuel) (ys ++ [decide (r=value S P q)]))
      (4*r+3*max (r+1) (value S P q)+32) := by
  have h := FormulaEqualityPair.query_hoare false r (value S P q) ys inp hi
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at h
  apply FormulaRoutedFrame.hoare _ 0 24 (route q) inp (FormulaEqualityPair.small r (value S P q))
    (frame r L V C S P N fuel) _ _ _ (parked _ _ _ _ _ _ _ _ hf) _ h
  intro t
  fin_cases q <;> fin_cases t <;>
    simp [route,slot,Equiv.swap_apply_def,placeWorkIdx,frame,value,FormulaAllTails.frame,
      FormulaExternalTailPhase.frame,FormulaAllRailTails.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaRailTailReentrant.frame,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank,FormulaEqualityPair.small,FormulaClauseCompare.bank]

end UnconstrainedPACDetection.FormulaRowQuery
