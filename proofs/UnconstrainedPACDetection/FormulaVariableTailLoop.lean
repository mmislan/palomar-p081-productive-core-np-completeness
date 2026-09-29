module

public import proofs.UnconstrainedPACDetection.FormulaVariableTailBody

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableTailLoop
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open VerifierPairRestore (word word_parked)

def frame (k r L V C : Nat) (fuel : Tape) : Fin 21 → Tape :=
  FormulaChangingFrame.extend (FormulaSwitchVariableHeads.extend (FormulaRailClauseHeads.extend
    (FormulaRailHeadVariables.extend (FormulaRailHeadPrepare.bank k V 0 r (20*L+k) 0 0 L V) (regTape L)) C)) fuel

theorem parked (k r L V C : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (frame k r L V C fuel t) :=
  FormulaChangingFrame.parked _ _ (FormulaSwitchVariableHeads.extend_parked _
    (FormulaRailClauseHeads.extend_parked _ _ (FormulaRailHeadVariables.extend_parked _ _
      (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) (parked_regTape _)))) hf

def body (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 :=
  placeWorkTM 0 4 (FormulaVariableTailBody.machine right plan)

theorem body_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    (body right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame v.val (index r) (levels φ) (varCount φ) φ.length fuel) ys)
      (EmitPred (word φ.encode) (frame (v.val+1) (index r) (levels φ) (varCount φ) φ.length fuel)
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
          (FormulaHeadFieldOrder.field φ right r (FormulaVariableCursor.port φ v.castSucc))))
      (FormulaVariableTailBody.budget φ) := by
  have h := FormulaVariableTailBody.hoare φ v right r ys
  apply FormulaChangingFrame.hoare _ 0 4 _ _ _ _ _ _ _ _
    (parked _ _ _ _ _ _ hf) _ _ _ h
  · intro t; fin_cases t <;> rfl
  · intro t; fin_cases t <;> rfl
  · intro t ht
    fin_cases t <;> simp_all [placeWorkInMiddle,frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaRailHeadVariables.extend,
      FormulaRailHeadPrepare.bank]

def fields (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  if hk : k < varCount φ then
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaVariableCursor.port φ ⟨k,by omega⟩))
  else []

def bits (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (fields φ right r)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 := forRegTM (body right plan) 20

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame 0 (index r) (levels φ) (varCount φ) φ.length (regTape (varCount φ))) ys)
      (EmitPred (word φ.encode) (frame (varCount φ) (index r) (levels φ) (varCount φ) φ.length (regTape (varCount φ)))
        (ys ++ bits φ right r (varCount φ)))
      (varCount φ*(FormulaVariableTailBody.budget φ+2)+(varCount φ+2)) := by
  let V := varCount φ
  let w := fun k => frame k (index r) (levels φ) V φ.length (regTape V)
  let zs := fun k => ys ++ bits φ right r k
  have h := forRegTM_hoareTime (body right (choose right (tag r) none none)) (20 : Fin 21) V
    (word φ.encode) w zs (FormulaVariableTailBody.budget φ) (word_parked _)
    (by intro k; rfl) (by intro k t _; exact parked _ _ _ _ _ _ (parked_regTape _) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells V⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 20 fuel = frame z (index r) (levels φ) V φ.length fuel := by
        funext t; fin_cases t <;> simp [w,frame,FormulaChangingFrame.extend]
      have hb := body_hoare φ ⟨k,hk⟩ right r fuel hf (zs k)
      have heq : fields φ right r k =
          (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
            (FormulaHeadFieldOrder.field φ right r (FormulaVariableCursor.port φ ⟨k,by omega⟩)) := by
        unfold fields; rw [dite_eq_left hk]
      have hy : zs (k+1) = zs k ++ fields φ right r k := by
        simp [zs,bits,List.range_succ,List.flatMap_append,List.append_assoc]
      rw [he,he,hy,heq]
      exact hb)
  simpa only [machine,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,V,Nat.add_assoc] using h

end UnconstrainedPACDetection.FormulaVariableTailLoop
