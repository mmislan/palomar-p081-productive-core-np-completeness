module

public import proofs.UnconstrainedPACDetection.FormulaOtherHeadOrder

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailCanonical
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)
open FormulaPairExecution (tailMeaning)
open FormulaVertexHeadFields (vertex)

theorem bits_eq (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) :
    FormulaSwitchTailHeads.bits φ i p right r a =
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (FormulaHeadFieldOrder.field φ right r a) := by
  have hv : (FormulaIndexedGraph.labels φ).flatMap (vertex φ right r a) =
      (List.finRange (levels φ)).flatMap (fun j => (List.finRange 20).flatMap
        (fun q => vertex φ right r a (SwitchStack.sw j q))) ++
      (FormulaOtherHeadOrder.variableHeads φ).flatMap (vertex φ right r a) ++
      (FormulaOtherHeadOrder.rails φ).flatMap (vertex φ right r a) ++
      (FormulaOtherHeadOrder.clauses φ).flatMap (vertex φ right r a) := by
    have h := congrArg (fun xs => xs.flatMap (vertex φ right r a)) (FormulaOrderedEnumeration.labels_eq_vertices φ)
    simpa only [FormulaEnumeration.vertices,FormulaOtherHeadOrder.variableHeads,FormulaOtherHeadOrder.rails,
      FormulaOtherHeadOrder.clauses,List.flatMap_append,List.flatMap_assoc,List.flatMap_map] using h
  rw [← FormulaSwitchHeadOrder.all_levels φ i p right r a ha,
    FormulaOtherHeadOrder.variable_fields φ i p right r a ha,
    FormulaOtherHeadOrder.all_rails,FormulaOtherHeadOrder.clause_fields] at hv
  have h := FormulaVertexHeadFields.head_scan φ right r a
  rw [hv] at h
  simpa only [FormulaSwitchTailHeads.bits,List.append_assoc] using h.symm

/-- Exact canonical head scan, with all counters physically initialized and returned. -/
theorem canonical_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v j b f g h : Nat) (ys : List Bool)
    (hf : f ≤ 100*(φ.encode.length+2)^2) (hg : g ≤ 100*(φ.encode.length+2)^2) :
    (FormulaSwitchTailHeads.machine p right (tag r) (tag a)).HoareTime
      (EmitPred (word φ.encode)
        (FormulaSwitchTailHeads.frame i.val v j (index r) (index a) b f (levels φ) (varCount φ) g φ.length h) ys)
      (EmitPred (word φ.encode)
        (FormulaSwitchTailHeads.frame i.val (varCount φ) (levels φ+1) (index r) (index a)
          (FormulaClauseCursor.base φ+φ.length) (levels φ+1) (levels φ) (varCount φ) φ.length φ.length (levels φ-1))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
          (FormulaHeadFieldOrder.field φ right r a)))
      (FormulaSwitchTailHeads.budget φ i.val v j b h) := by
  rw [← bits_eq φ i p right r a ha]
  exact FormulaSwitchTailHeads.hoare φ i p right r a ha v j b f g h ys hf hg

end UnconstrainedPACDetection.FormulaSwitchTailCanonical
