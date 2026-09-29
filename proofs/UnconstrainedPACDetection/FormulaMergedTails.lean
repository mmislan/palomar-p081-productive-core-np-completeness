module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailPhase

@[expose] public section

namespace UnconstrainedPACDetection.FormulaMergedTails
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)
open FormulaSwitchTailReentrant (frame parked)

def prepare : TM 21 := seqTM (copyIntoTM 15 0) (decRegTM 0)

theorem prepare_hoare (r L V C : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    prepare.HoareTime (EmitPred inp (frame 0 r 0 L V C) ys)
      (EmitPred inp (frame (L-1) r 0 L V C) ys) (2*L^2+9*L+12) := by
  have h0 := copyIntoTM_hoareTime (15 : Fin 21) 0 (by decide) L 0 inp (frame 0 r 0 L V C) ys hi
    (fun t _ => parked _ _ _ _ _ _ t) rfl rfl
  have he0 : Function.update (frame 0 r 0 L V C) 0 (regTape L) = frame L r 0 L V C := by
    funext t; fin_cases t <;> simp [frame,FormulaSwitchTailHeads.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.bank,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
      FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he0] at h0
  have h1 := decRegTM_hoareTime (0 : Fin 21) L inp (frame L r 0 L V C) ys hi
    (fun t _ => parked _ _ _ _ _ _ t) rfl
  have he1 : Function.update (frame L r 0 L V C) 0 (regTape (L-1)) = frame (L-1) r 0 L V C := by
    funext t; fin_cases t <;> simp [frame,FormulaSwitchTailHeads.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.bank,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
      FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he1] at h1
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _) _) h1).mono_bound (by nlinarith)

theorem finish_hoare (r L V C : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (clearRegTM (0 : Fin 21)).HoareTime (EmitPred inp (frame (L-1) r 0 L V C) ys)
      (EmitPred inp (frame 0 r 0 L V C) ys) (2*L+4) := by
  have h := clearRegTM_hoareTime (0 : Fin 21) (L-1) inp (frame (L-1) r 0 L V C) ys hi
    (fun t _ => parked _ _ _ _ _ _ t) rfl
  have he : Function.update (frame (L-1) r 0 L V C) 0 (regTape 0) = frame 0 r 0 L V C := by
    funext t; fin_cases t <;> simp [frame,FormulaSwitchTailHeads.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.bank,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
      FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he] at h
  exact h.mono_bound (by omega)

def machine (right : Bool) (rt : Option Bool) : TM 21 :=
  seqTM (FormulaSwitchTailReentrant.machine 1 right rt (some false))
    (seqTM prepare (seqTM (FormulaSwitchTailReentrant.machine 0 right rt (some true)) (clearRegTM 0)))

def budget (φ : SAT.CNF) : Nat := 2*FormulaSwitchTailReentrant.budget φ+2*(levels φ)^2+11*levels φ+19

theorem hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (tag r)).HoareTime
      (EmitPred (word φ.encode) (frame 0 (index r) 0 (levels φ) (varCount φ) φ.length) ys)
      (EmitPred (word φ.encode) (frame 0 (index r) 0 (levels φ) (varCount φ) φ.length)
        (ys ++ FormulaVertexTailFields.port φ right r (.inl false) ++ FormulaVertexTailFields.port φ right r (.inl true)))
      (budget φ) := by
  let first : Fin (levels φ) := ⟨0,FormulaWiring.levels_pos φ⟩
  let last : Fin (levels φ) := ⟨levels φ-1,by have h := FormulaWiring.levels_pos φ; omega⟩
  have hp : FormulaPairExecution.tailMeaning φ (.inl false) = SwitchStack.sw first 1 := by
    simp [FormulaPairExecution.tailMeaning,tailVertex,MarkedGraph.decode,FormulaIndexedGraph.terminals,
      PACFormulaReduction.terminals,PACFormulaReduction.terminal,FormulaWiring.sourceP,first]
  have hq : FormulaPairExecution.tailMeaning φ (.inl true) = SwitchStack.sw last 0 := by
    simp [FormulaPairExecution.tailMeaning,tailVertex,MarkedGraph.decode,FormulaIndexedGraph.terminals,
      PACFormulaReduction.terminals,PACFormulaReduction.terminal,FormulaWiring.sourceQ,last]
  have h0 := FormulaSwitchTailReentrant.hoare φ first 1 right r (.inl false) hp ys
  have h1 := prepare_hoare (index r) (levels φ) (varCount φ) φ.length (word φ.encode) (word_parked _)
    (ys ++ FormulaVertexTailFields.port φ right r (.inl false))
  have h2 := FormulaSwitchTailReentrant.hoare φ last 0 right r (.inl true) hq
    (ys ++ FormulaVertexTailFields.port φ right r (.inl false))
  have h3 := finish_hoare (index r) (levels φ) (varCount φ) φ.length (word φ.encode) (word_parked _)
    ((ys ++ FormulaVertexTailFields.port φ right r (.inl false)) ++ FormulaVertexTailFields.port φ right r (.inl true))
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _) _) h3
  have h123 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _) _) h23
  have h := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _) _) h123
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaMergedTails
