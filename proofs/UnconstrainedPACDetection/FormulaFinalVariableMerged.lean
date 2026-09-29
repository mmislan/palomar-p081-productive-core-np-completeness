module

public import proofs.UnconstrainedPACDetection.FormulaFinalVariableClauseLoop

@[expose] public section

namespace UnconstrainedPACDetection.FormulaFinalVariableMerged
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaFinalVariableClauseLoop (bank parked round)
open VerifierPairRestore (word word_parked)

theorem round_hoare (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var (Fin.last (varCount φ)))) (fuel : Tape)
    (hf : Parked fuel) (ys : List Bool) :
    (round right (choose right (tag r) (tag a) (some false))).HoareTime
      (EmitPred (word φ.encode) (bank (varCount φ) φ.length (index r) (index a) 0
        (levels φ) (varCount φ) φ.length fuel) ys)
      (EmitPred (word φ.encode) (bank (varCount φ) φ.length (index r) (index a) 0
        (levels φ) (varCount φ) φ.length fuel)
        (ys ++ FormulaHeadFieldOrder.field φ right r a (.inl false)))
      (7*varCount φ+7*φ.length+3*(FormulaIndexedGraph.labels φ).length+103) := by
  have hb : FormulaPairExecution.headMeaning φ (.inl false) =
      .inr (.clause (Fin.last φ.length)) := by
    rw [FormulaMergedHeads.merged_meaning]
    rfl
  have h := FormulaVariablePair.clause_entry φ (Fin.last (varCount φ)) (Fin.last φ.length)
    right r a (.inl false) ha hb ys
  have h' := FormulaRoutedFrame.hoare _ 0 7 FormulaFinalVariableClauseLoop.route _ _
    (bank (varCount φ) φ.length (index r) (index a) 0 (levels φ) (varCount φ) φ.length fuel)
    _ _ _ (parked _ _ _ _ _ _ _ _ _ hf) (by
      intro t; fin_cases t <;> first | rfl | exact FormulaEndpointRegisters.unary_word 0) h
  apply h'.mono_bound
  have hr := FormulaCoefficientRound.index_bound r
  have hat := FormulaCoefficientRound.index_bound a
  dsimp only [index] at hr hat
  cases right <;> simp only [Fin.val_last,index,Bool.false_eq_true,ite_false,ite_true] <;> omega

def prepare : TM 20 := seqTM (copyIntoTM 18 3) (clearRegTM 11)

theorem prepare_hoare (i c r a b L V C : Nat) (fuel : Tape) (hf : Parked fuel)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    prepare.HoareTime (EmitPred inp (bank i c r a b L V C fuel) ys)
      (EmitPred inp (bank i C r a 0 L V C fuel) ys) (2*c+2*b+2*C^2+7*C+12) := by
  have h0 := copyIntoTM_hoareTime (18 : Fin 20) 3 (by decide) C c inp
    (bank i c r a b L V C fuel) ys hi (fun t _ => parked _ _ _ _ _ _ _ _ _ hf t) rfl rfl
  have he0 : Function.update (bank i c r a b L V C fuel) 3 (regTape C) = bank i C r a b L V C fuel := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  have h1 := clearRegTM_hoareTime (11 : Fin 20) b inp (bank i C r a b L V C fuel) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ hf t) rfl
  have he1 : Function.update (bank i C r a b L V C fuel) 11 (regTape 0) = bank i C r a 0 L V C fuel := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ hf) _) h1).mono_bound (by nlinarith)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  seqTM prepare (round right plan)

theorem hoare (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var (Fin.last (varCount φ)))) (c b : Nat)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    (machine right (choose right (tag r) (tag a) (some false))).HoareTime
      (EmitPred (word φ.encode) (bank (varCount φ) c (index r) (index a) b
        (levels φ) (varCount φ) φ.length fuel) ys)
      (EmitPred (word φ.encode) (bank (varCount φ) φ.length (index r) (index a) 0
        (levels φ) (varCount φ) φ.length fuel)
        (ys ++ FormulaHeadFieldOrder.field φ right r a (.inl false)))
      (2*c+2*b+2*φ.length^2+14*φ.length+7*varCount φ+3*(FormulaIndexedGraph.labels φ).length+116) := by
  have h0 := prepare_hoare (varCount φ) c (index r) (index a) b (levels φ) (varCount φ)
    φ.length fuel hf (word φ.encode) (word_parked _) ys
  have h1 := round_hoare φ right r a ha fuel hf ys
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ hf) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaFinalVariableMerged
