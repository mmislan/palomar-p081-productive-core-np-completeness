module

public import proofs.UnconstrainedPACDetection.FormulaClauseCursor
public import proofs.UnconstrainedPACDetection.FormulaVariablePair

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableCursor
open Complexity.SAT FormulaWiring DirectedLinkageSource
open FormulaCoefficientPlan (index tag)
open FormulaPairExecution (headMeaning tailMeaning)

def port (φ : CNF) (v : Fin (varCount φ+1)) :
    Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ) :=
  .inr ⟨(FormulaIndexedGraph.vertexEquiv φ).symm (.inr (.var v)), by
    rintro ⟨t,ht⟩
    have h := congrArg (FormulaIndexedGraph.vertexEquiv φ) ht
    cases t with
    | inl t => cases t <;> simp [FormulaIndexedGraph.terminals,
        PACFormulaReduction.terminals,PACFormulaReduction.terminal,sourceP,sourceQ,SwitchStack.sw] at h
    | inr t => cases t <;> simp [FormulaIndexedGraph.terminals,
        PACFormulaReduction.terminals,PACFormulaReduction.terminal,sinkP,sinkQ,SwitchStack.sw] at h⟩

theorem port_meaning (φ : CNF) (v : Fin (varCount φ+1)) :
    headMeaning φ (port φ v) = .inr (.var v) := by
  simp [headMeaning,port,headVertex,MarkedGraph.decode]

theorem port_index (φ : CNF) (v : Fin (varCount φ+1)) : index (port φ v) = 20*levels φ+v.val := by
  let sws := (List.finRange (levels φ)).flatMap (fun i => (List.finRange 20).map (SwitchStack.sw (X := External φ) i))
  have hl : sws.length = 20*levels φ := by simp [sws,List.length_flatMap]; omega
  have hb : sws.length+v.val < (FormulaIndexedGraph.labels φ).length := by
    rw [FormulaOrderedEnumeration.labels_eq_vertices,FormulaEnumeration.vertices_length]
    have := v.isLt
    omega
  have he : FormulaIndexedGraph.vertexEquiv φ ⟨sws.length+v.val,hb⟩ = .inr (.var v) := by
    change (FormulaIndexedGraph.labels φ)[sws.length+v.val] = _
    simp only [FormulaOrderedEnumeration.labels_eq_vertices,FormulaEnumeration.vertices,List.append_assoc]
    rw [List.getElem_append_right (by change sws.length ≤ _; omega)]
    rw [List.getElem_append_left (by
      simp only [List.length_map,List.length_finRange]
      change sws.length+v.val-sws.length < varCount φ+1
      have := v.isLt
      omega)]
    simp
    apply Fin.ext
    change sws.length+v.val-levels φ*20 = v.val
    omega
  simpa only [FormulaCoefficientPlan.index, port, hl] using
    congrArg Fin.val ((FormulaIndexedGraph.vertexEquiv φ).symm_apply_eq.mpr he.symm)

/-- Every nonzero variable head is impossible after a switch tail. -/
theorem nonzero_rejected (φ : CNF) (i : Fin (levels φ)) (p : ControlSwitch.V)
    (a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v : Fin (varCount φ+1)) (hv : v.val ≠ 0) :
    ¬FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,port φ v) := by
  intro h
  have h' := h.1
  change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ (port φ v)) at h'
  rw [ha,port_meaning] at h'
  simp [FormulaWiring.adjacency,SwitchStack.Edge,SwitchStack.sw,DataWire,hv] at h'

end UnconstrainedPACDetection.FormulaVariableCursor
