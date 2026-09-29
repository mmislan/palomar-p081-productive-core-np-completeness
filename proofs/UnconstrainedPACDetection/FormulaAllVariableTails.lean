module

public import proofs.UnconstrainedPACDetection.FormulaClauseFrameReturn

@[expose] public section

namespace UnconstrainedPACDetection.FormulaAllVariableTails
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

def bits (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  (List.finRange (varCount φ+1)).flatMap (fun v =>
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaVariableCursor.port φ v)))

theorem bits_eq (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    FormulaVariableTailLoop.bits φ right r (varCount φ) ++
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
        (FormulaHeadFieldOrder.field φ right r (FormulaVariableCursor.port φ (Fin.last (varCount φ)))) =
      bits φ right r := by
  have hr := FormulaHeadFieldOrder.range_fields (varCount φ) (fun v =>
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaVariableCursor.port φ v.castSucc)))
  change FormulaVariableTailLoop.bits φ right r (varCount φ) = _ at hr
  unfold bits
  rw [hr,List.finRange_succ_last]
  simp only [List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,List.append_nil]

def finishBudget (φ : SAT.CNF) : Nat :=
  40*(opBudget (cap φ)+1)+2*levels φ+4*φ.length^2+23*φ.length+
    7*varCount φ+3*(FormulaIndexedGraph.labels φ).length+131+
    φ.length*(10*varCount φ+10*φ.length+10*(FormulaIndexedGraph.labels φ).length+202)+(φ.length+2)

def budget (φ : SAT.CNF) : Nat := 16*opBudget (cap φ)+
  varCount φ*(FormulaVariableTailBody.budget φ+2)+(varCount φ+2)+finishBudget φ+17

def machine (right : Bool) (ordinary merged : FormulaCoefficientPlan.Plan) : TM 21 :=
  seqTM FormulaVariableTailInit.machine (seqTM (FormulaVariableTailLoop.machine right ordinary)
    (seqTM FormulaVariableFinalBridge.machine
      (seqTM (placeWorkTM 0 1 (FormulaFinalVariableCanonical.machine right merged ordinary))
        (placeWorkTM 0 1 FormulaClauseFrameReturn.machine))))

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (v f : Nat) (ys : List Bool)
    (hv : v ≤ cap φ) (hf : f ≤ cap φ) :
    (machine right (choose right (tag r) none none) (choose right (tag r) none (some false))).HoareTime
      (EmitPred (word φ.encode) (FormulaAllRailTails.frame v (index r) (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (FormulaAllRailTails.frame (varCount φ) (index r)
        (levels φ) (varCount φ) φ.length (regTape (varCount φ))) (ys ++ bits φ right r)) (budget φ) := by
  let a := FormulaVariableCursor.port φ (Fin.last (varCount φ))
  let zs := ys ++ FormulaVariableTailLoop.bits φ right r (varCount φ)
  let lastFields := (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
    (FormulaHeadFieldOrder.field φ right r a)
  have ha : tailMeaning φ a = .inr (.var (Fin.last (varCount φ))) := by
    simp [a,tailMeaning,FormulaVariableCursor.port,tailVertex,MarkedGraph.decode]
  have ht : tag a = none := rfl
  have hai : index a = 20*levels φ+varCount φ := FormulaVariableCursor.port_index φ (Fin.last (varCount φ))
  obtain ⟨hL,hV,hC⟩ := FormulaEnumeration.parameter_bounds φ
  have hLc : levels φ+1 ≤ cap φ := by unfold cap; nlinarith
  have hVc : varCount φ ≤ cap φ := by unfold cap; nlinarith
  have hCc : φ.length ≤ cap φ := by unfold cap; nlinarith
  have hN : (FormulaIndexedGraph.labels φ).length ≤ cap φ := by
    apply (FormulaIndexedGraph.labels_bound φ).trans
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have hA : 20*levels φ+varCount φ ≤ cap φ := by
    rw [← hai]; exact (FormulaCoefficientRound.index_bound a).trans hN
  have hB : FormulaClauseCursor.base φ+φ.length ≤ cap φ := by
    have he := congrArg List.length (FormulaClauseCursor.labels φ)
    simp only [List.length_append,FormulaClauseCursor.initialVertices_length,List.length_map,List.length_finRange] at he
    have hb : FormulaClauseCursor.base φ+φ.length ≤ (FormulaIndexedGraph.labels φ).length := by omega
    exact hb.trans hN
  have h0 := FormulaVariableTailInit.hoare φ v (index r) f ys hv hf
  have h1 := FormulaVariableTailLoop.canonical_hoare φ right r ys
  have h2 := FormulaVariableFinalBridge.hoare φ (index r) zs
  have h3 := (FormulaFinalVariableCanonical.canonical_hoare φ right r a ha 0 0 (levels φ) zs).mono_bound
    (show _ ≤ finishBudget φ by unfold finishBudget; omega)
  rw [ht,hai] at h3
  have h3' := FormulaChangingFrame.append_hoare _ _ _ _ (regTape (varCount φ)) _ _ _
    (FormulaFinalVariableClauseLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _) h3
  have h4 := FormulaClauseFrameReturn.hoare (varCount φ) φ.length (index r) (20*levels φ+varCount φ)
    (FormulaClauseCursor.base φ+φ.length) (levels φ) (varCount φ) φ.length φ.length (cap φ)
    (word φ.encode) (word_parked _) (zs ++ lastFields) hVc hCc hA hB hLc hCc
  have h4' := FormulaChangingFrame.append_hoare _ _ _ _ (regTape (varCount φ)) _ _ _
    (FormulaFinalVariableClauseLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _) h4
  have h34 := seqTM_hoareTime _ _ h3'
    (emitPred_transition (word_parked _) (FormulaChangingFrame.parked _ _
      (FormulaFinalVariableClauseLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _)) _) h4'
  have h234 := seqTM_hoareTime _ _ h2
    (emitPred_transition (word_parked _) (FormulaChangingFrame.parked _ _
      (FormulaFinalVariableClauseLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _)) _) h34
  have h1234 := seqTM_hoareTime _ _ h1
    (emitPred_transition (word_parked _) (FormulaVariableTailLoop.parked _ _ _ _ _ _ (parked_regTape _)) _) h234
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (FormulaVariableTailLoop.parked _ _ _ _ _ _ (parked_regTape _)) _) h1234
  have he : zs ++ lastFields = ys ++ bits φ right r := by
    unfold zs lastFields a
    rw [List.append_assoc,bits_eq]
  rw [he] at h
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaAllVariableTails
