module

public import proofs.UnconstrainedPACDetection.FormulaAllRailTails

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableTailBody
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open VerifierPairRestore (word word_parked)
open FormulaRailHeadPrepare (bank parked)
open FormulaVariableTailBound (cap)

def advance : TM 17 := seqTM (clearRegTM 11) (seqTM (incRegTM 0) (incRegTM 10))

theorem advance_hoare (k V r A b L M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hk : k ≤ M) (hA : A ≤ M) (hb : b ≤ M) :
    advance.HoareTime (EmitPred inp (bank k V 0 r A b 0 L V) ys)
      (EmitPred inp (bank (k+1) V 0 r (A+1) 0 0 L V) ys) (3*opBudget M+2) := by
  have h0 := (clearRegTM_hoareTime (11 : Fin 17) b inp (bank k V 0 r A b 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (clearRegTM_le_opBudget hb)
  have he0 : Function.update (bank k V 0 r A b 0 L V) 11 (regTape 0) = bank k V 0 r A 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  have h1 := (incRegTM_hoareTime (0 : Fin 17) k inp (bank k V 0 r A 0 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (incRegTM_le_opBudget hk)
  have he1 : Function.update (bank k V 0 r A 0 0 L V) 0 (regTape (k+1)) = bank (k+1) V 0 r A 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := (incRegTM_hoareTime (10 : Fin 17) A inp (bank (k+1) V 0 r A 0 0 L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl).mono_bound (incRegTM_le_opBudget hA)
  have he2 : Function.update (bank (k+1) V 0 r A 0 0 L V) 10 (regTape (A+1)) = bank (k+1) V 0 r (A+1) 0 0 L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h2
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h12).mono_bound (by omega)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  seqTM (FormulaVariableTailCaller.machine right plan) advance

def budget (φ : SAT.CNF) : Nat :=
  83*opBudget (cap φ)+6*(FormulaIndexedGraph.labels φ).length+4*(varCount φ)^2+18*varCount φ+156

theorem hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (bank v.val (varCount φ) 0 (index r) (20*levels φ+v.val) 0 0 (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank (v.val+1) (varCount φ) 0 (index r) (20*levels φ+(v.val+1)) 0 0 (levels φ) (varCount φ))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
          (FormulaHeadFieldOrder.field φ right r (FormulaVariableCursor.port φ v.castSucc)))) (budget φ) := by
  let a := FormulaVariableCursor.port φ v.castSucc
  have ha : tailMeaning φ a = .inr (.var v.castSucc) := by
    simp [a,tailMeaning,FormulaVariableCursor.port,tailVertex,MarkedGraph.decode]
  have ht : tag a = none := rfl
  have hai : index a = 20*levels φ+v.val := FormulaVariableCursor.port_index φ v.castSucc
  have h0 := FormulaVariableTailCaller.canonical_hoare φ v right r a ha 0 0 0 ys (Nat.zero_le _)
  rw [ht,hai] at h0
  have hN : (FormulaIndexedGraph.labels φ).length ≤ cap φ := by
    apply (FormulaIndexedGraph.labels_bound φ).trans
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have hA : 20*levels φ+v.val ≤ cap φ := by
    rw [← hai]; exact (FormulaCoefficientRound.index_bound a).trans hN
  have hv : v.val ≤ cap φ := by omega
  have h1 := advance_hoare v.val (varCount φ) (index r) (20*levels φ+v.val)
    (FormulaRailBase.value (levels φ) (varCount φ) v.val true) (levels φ) (cap φ)
    (word φ.encode) (word_parked _)
    (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r a)) hv hA (FormulaVariableTailBound.base_bound φ v true)
  have he : 20*levels φ+v.val+1 = 20*levels φ+(v.val+1) := by omega
  rw [he] at h1
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h1).mono_bound
    (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaVariableTailBody
