module

public import proofs.UnconstrainedPACDetection.FormulaClauseTailHeads

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseTailPrepare
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaClauseTailHeads (frame parked)

def prepare : TM 21 := seqTM (clearRegTM 0) (seqTM (setConstTM 11 2) (copyIntoTM 15 20))

theorem prepare_hoare (i c r a b L V C f : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    prepare.HoareTime (EmitPred inp (frame i c r a b L V C (regTape f)) ys)
      (EmitPred inp (frame 0 c r a 2 L V C (regTape L)) ys)
      (2*i+2*b+2*f+2*L^2+7*L+37) := by
  have h0 := clearRegTM_hoareTime (0 : Fin 21) i inp (frame i c r a b L V C (regTape f)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl
  have he0 : Function.update (frame i c r a b L V C (regTape f)) 0 (regTape 0) =
      frame 0 c r a b L V C (regTape f) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.extend,FormulaClauseHeadLoop.bank]
  rw [he0] at h0
  have h1 := setConstTM_hoareTime (11 : Fin 21) 2 b inp (frame 0 c r a b L V C (regTape f)) ys hi
    (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) rfl
  have he1 : Function.update (frame 0 c r a b L V C (regTape f)) 11 (regTape 2) =
      frame 0 c r a 2 L V C (regTape f) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.extend,FormulaClauseHeadLoop.bank]
  rw [he1] at h1
  have h2 := copyIntoTM_hoareTime (15 : Fin 21) 20 (by decide) L f inp (frame 0 c r a 2 L V C (regTape f)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl rfl
  have he2 : Function.update (frame 0 c r a 2 L V C (regTape f)) 20 (regTape L) =
      frame 0 c r a 2 L V C (regTape L) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend]
  rw [he2] at h2
  have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h2
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h12).mono_bound (by nlinarith)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 :=
  seqTM prepare (FormulaClauseTailHeads.loop right plan)

theorem hoare (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.clause c.castSucc)) (i b f : Nat) (ys : List Bool) :
    (machine right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (frame i c.val (index r) (index a) b (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (frame (levels φ) c.val (index r) (index a) (20*levels φ+2)
        (levels φ) (varCount φ) φ.length (regTape (levels φ))) (ys ++ FormulaClauseTailHeads.bits φ right r a (levels φ)))
      (2*i+2*b+2*f+2*(levels φ)^2+7*levels φ+38+FormulaClauseTailHeads.loopBudget φ) := by
  have hp := prepare_hoare i c.val (index r) (index a) b (levels φ) (varCount φ) φ.length f
    (word φ.encode) (word_parked _) ys
  have hl := FormulaClauseTailHeads.loop_hoare φ c right r a ha ys
  exact (seqTM_hoareTime _ _ hp (emitPred_transition (word_parked _)
    (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) hl).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaClauseTailPrepare
