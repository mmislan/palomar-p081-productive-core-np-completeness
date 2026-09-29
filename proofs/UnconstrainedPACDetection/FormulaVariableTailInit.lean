module

public import proofs.UnconstrainedPACDetection.FormulaVariableTailLoop

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableTailInit
open Complexity Complexity.TM
open FormulaWiring (levels varCount)
open FormulaRailHeadPrepare (bank parked)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

def core : TM 17 := seqTM (copyIntoTM 16 5)
  (seqTM (setConstTM 6 20) (seqTM (mulAddIntoTM 15 6 10) (clearRegTM 6)))

theorem core_hoare (v r L V M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hv : v ≤ M) (hL : L ≤ M) (hV : V ≤ M) (h20 : 20 ≤ M) (hbase : 20*L ≤ M) :
    core.HoareTime (EmitPred inp (bank 0 v 0 r 0 0 0 L V) ys)
      (EmitPred inp (bank 0 V 0 r (20*L) 0 0 L V) ys) (4*opBudget M+3) := by
  have h0 := (copyIntoTM_hoareTime (16 : Fin 17) 5 (by decide) V v inp (bank 0 v 0 r 0 0 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl).mono_bound (copyIntoTM_le_opBudget hV hv)
  have he0 : Function.update (bank 0 v 0 r 0 0 0 L V) 5 (regTape V) = bank 0 V 0 r 0 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  have h1 := (setConstTM_hoareTime (6 : Fin 17) 20 0 inp (bank 0 V 0 r 0 0 0 L V) ys hi
    (parked _ _ _ _ _ _ _ _ _) rfl).mono_bound (setConstTM_le_opBudget h20 (Nat.zero_le _))
  have he1 : Function.update (bank 0 V 0 r 0 0 0 L V) 6 (regTape 20) = bank 0 V 20 r 0 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := (mulAddIntoTM_hoareTime (15 : Fin 17) 6 10 (by decide) (by decide) (by decide)
    L 20 0 inp (bank 0 V 20 r 0 0 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl rfl).mono_bound
      (mulAddIntoTM_le_opBudget hL h20 (by omega : 0+L*20 ≤ M))
  have he2 : Function.update (bank 0 V 20 r 0 0 0 L V) 10 (regTape (0+L*20)) =
      bank 0 V 20 r (20*L) 0 0 L V := by
    have he : 0+L*20 = 20*L := by omega
    rw [he]; funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  have h3 := (clearRegTM_hoareTime (6 : Fin 17) 20 inp (bank 0 V 20 r (20*L) 0 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget h20)
  have he3 : Function.update (bank 0 V 20 r (20*L) 0 0 L V) 6 (regTape 0) = bank 0 V 0 r (20*L) 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he3] at h3
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h3
  have h123 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h23
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h123).mono_bound (by omega)

def machine : TM 21 := seqTM (placeWorkTM 0 4 core) (copyIntoTM 16 20)

theorem hoare (φ : SAT.CNF) (v r f : Nat) (ys : List Bool) (hv : v ≤ cap φ) (hf : f ≤ cap φ) :
    machine.HoareTime
      (EmitPred (word φ.encode) (FormulaAllRailTails.frame v r (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (FormulaVariableTailLoop.frame 0 r (levels φ) (varCount φ) φ.length (regTape (varCount φ))) ys)
      (5*opBudget (cap φ)+4) := by
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hLc : levels φ ≤ cap φ := by unfold cap; nlinarith
  have hVc : varCount φ ≤ cap φ := by unfold cap; nlinarith
  have h0 := core_hoare v r (levels φ) (varCount φ) (cap φ) (word φ.encode) (word_parked _) ys
    hv hLc hVc (by unfold cap; nlinarith only [Nat.zero_le φ.encode.length]) (by unfold cap; nlinarith)
  have h0' : (placeWorkTM 0 4 core).HoareTime
      (EmitPred (word φ.encode) (FormulaAllRailTails.frame v r (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (FormulaVariableTailLoop.frame 0 r (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (4*opBudget (cap φ)+3) := by
    apply FormulaChangingFrame.hoare _ 0 4 _ _ _ _ _ _ _ _
      (FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _)) _ _ _ h0
    · intro t; fin_cases t <;> rfl
    · intro t; fin_cases t <;> simp [FormulaVariableTailLoop.frame,FormulaChangingFrame.extend,
        FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaRailHeadVariables.extend,bank,placeWorkIdx]
    · intro t ht
      fin_cases t <;> simp_all [placeWorkInMiddle,FormulaAllRailTails.frame,FormulaVariableTailLoop.frame,
        FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
        FormulaRailHeadVariables.extend,FormulaRailTailReentrant.frame,bank]
  have h1 := (copyIntoTM_hoareTime (16 : Fin 21) 20 (by decide) (varCount φ) f (word φ.encode)
    (FormulaVariableTailLoop.frame 0 r (levels φ) (varCount φ) φ.length (regTape f)) ys (word_parked _)
    (fun t _ => FormulaVariableTailLoop.parked _ _ _ _ _ _ (parked_regTape _) t) rfl rfl).mono_bound
      (copyIntoTM_le_opBudget hVc hf)
  have he : Function.update (FormulaVariableTailLoop.frame 0 r (levels φ) (varCount φ) φ.length (regTape f)) 20
      (regTape (varCount φ)) = FormulaVariableTailLoop.frame 0 r (levels φ) (varCount φ) φ.length (regTape (varCount φ)) := by
    funext t; fin_cases t <;> simp [FormulaVariableTailLoop.frame,FormulaChangingFrame.extend]
  rw [he] at h1
  exact (seqTM_hoareTime _ _ h0'
    (emitPred_transition (word_parked _) (FormulaVariableTailLoop.parked _ _ _ _ _ _ (parked_regTape _)) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaVariableTailInit
