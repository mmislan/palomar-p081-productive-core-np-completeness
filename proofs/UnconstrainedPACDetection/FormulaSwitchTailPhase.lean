module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailLevels
public import proofs.UnconstrainedPACDetection.FormulaExternalTailPhase

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailPhase
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)
open FormulaChangingFrame (extend)

def frame (i r a L V C g : Nat) : Fin 22 → Tape :=
  extend (FormulaSwitchTailReentrant.frame i r a L V C) (regTape g)

theorem parked (i r a L V C g : Nat) : ∀ t, Parked (frame i r a L V C g t) :=
  FormulaChangingFrame.parked _ _ (FormulaSwitchTailReentrant.parked _ _ _ _ _ _) (parked_regTape _)

theorem prepare_hoare (r L V C : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (copyIntoTM (15 : Fin 22) 21).HoareTime
      (EmitPred inp (frame 0 r 0 L V C C) ys) (EmitPred inp (frame 0 r 0 L V C L) ys)
      (2*C+2*L^2+7*L+7) := by
  have h := copyIntoTM_hoareTime (15 : Fin 22) 21 (by decide) L C inp (frame 0 r 0 L V C C) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ t) rfl rfl
  have he : Function.update (frame 0 r 0 L V C C) 21 (regTape L) = frame 0 r 0 L V C L := by
    funext t; fin_cases t <;> simp [frame,extend]
  rw [he] at h
  exact h.mono_bound (by nlinarith)

def finish : TM 22 := seqTM (clearRegTM 0) (seqTM (clearRegTM 10) (copyIntoTM 18 21))

theorem finish_hoare (r L V C : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    finish.HoareTime (EmitPred inp (frame L r (20*L) L V C L) ys)
      (EmitPred inp (frame 0 r 0 L V C C) ys) (44*L+2*C^2+7*C+17) := by
  have h0 := clearRegTM_hoareTime (0 : Fin 22) L inp (frame L r (20*L) L V C L) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ t) rfl
  have he0 : Function.update (frame L r (20*L) L V C L) 0 (regTape 0) = frame 0 r (20*L) L V C L := by
    funext t; fin_cases t <;> simp [frame,extend,FormulaSwitchTailReentrant.frame,FormulaSwitchTailHeads.frame,
      FormulaSwitchVariableHeads.bank,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
      FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he0] at h0
  have h1 := clearRegTM_hoareTime (10 : Fin 22) (20*L) inp (frame 0 r (20*L) L V C L) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ t) rfl
  have he1 : Function.update (frame 0 r (20*L) L V C L) 10 (regTape 0) = frame 0 r 0 L V C L := by
    funext t; fin_cases t <;> simp [frame,extend,FormulaSwitchTailReentrant.frame,FormulaSwitchTailHeads.frame,
      FormulaSwitchVariableHeads.bank,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
      FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he1] at h1
  have h2 := copyIntoTM_hoareTime (18 : Fin 22) 21 (by decide) C L inp (frame 0 r 0 L V C L) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ t) rfl rfl
  have he2 : Function.update (frame 0 r 0 L V C L) 21 (regTape C) = frame 0 r 0 L V C C := by
    funext t; fin_cases t <;> simp [frame,extend]
  rw [he2] at h2
  have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _) _) h2
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _) _) h12).mono_bound (by nlinarith)

def machine (right : Bool) (rt : Option Bool) : TM 22 :=
  seqTM (copyIntoTM 15 21) (seqTM (FormulaSwitchTailLevels.machine right rt) finish)

def budget (φ : SAT.CNF) : Nat :=
  2*(levels φ)^2+51*levels φ+2*φ.length^2+9*φ.length+26+
    (levels φ*(FormulaSwitchTailLevels.bodyBudget φ+2)+(levels φ+2))

theorem bits_eq (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    FormulaSwitchTailLevels.bits φ right r (levels φ) =
      ((List.finRange (levels φ)).flatMap (fun i => (List.finRange 20).map (SwitchStack.sw i))).flatMap
        (FormulaVertexTailFields.vertex φ right r) := by
  have hl := FormulaHeadFieldOrder.range_fields (levels φ)
    (fun i => FormulaSwitchTailPorts.bits φ i right r 20)
  change FormulaSwitchTailLevels.bits φ right r (levels φ) = _ at hl
  rw [hl,List.flatMap_assoc]
  apply congrArg (fun f => (List.finRange (levels φ)).flatMap f)
  funext i
  have hp := FormulaHeadFieldOrder.range_fields 20
    (fun p => FormulaVertexTailFields.vertex φ right r (SwitchStack.sw i p))
  unfold FormulaSwitchTailPorts.bits FormulaSwitchTailPorts.field
  simpa only [List.flatMap_map] using hp

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (tag r)).HoareTime
      (EmitPred (word φ.encode) (frame 0 (index r) 0 (levels φ) (varCount φ) φ.length φ.length) ys)
      (EmitPred (word φ.encode) (frame 0 (index r) 0 (levels φ) (varCount φ) φ.length φ.length)
        (ys ++ ((List.finRange (levels φ)).flatMap (fun i => (List.finRange 20).map (SwitchStack.sw i))).flatMap
          (FormulaVertexTailFields.vertex φ right r))) (budget φ) := by
  have h0 := prepare_hoare (index r) (levels φ) (varCount φ) φ.length (word φ.encode) (word_parked _) ys
  have h1 := FormulaSwitchTailLevels.hoare φ right r ys
  have h2 := finish_hoare (index r) (levels φ) (varCount φ) φ.length (word φ.encode) (word_parked _)
    (ys ++ FormulaSwitchTailLevels.bits φ right r (levels φ))
  have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _) _) h2
  have h := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _) _) h12
  rw [bits_eq] at h
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaSwitchTailPhase
