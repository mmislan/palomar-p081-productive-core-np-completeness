module

public import proofs.UnconstrainedPACDetection.FormulaRailBase
public import proofs.UnconstrainedPACDetection.FormulaClausePair

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseCursor
open Complexity.SAT FormulaWiring DirectedLinkageSource
open FormulaCoefficientPlan (index tag)
open FormulaPairExecution (headMeaning)

def base (φ : CNF) : Nat := FormulaRailBase.value (levels φ) (varCount φ) (varCount φ) false

def initialVertices (φ : CNF) : List (Vertex φ) :=
  (List.finRange (levels φ)).flatMap (fun i => (List.finRange 20).map (SwitchStack.sw i)) ++
  (List.finRange (varCount φ+1)).map (fun v => .inr (.var v)) ++
  (List.finRange (varCount φ)).flatMap (fun v =>
    [false,true].flatMap (fun s => (List.finRange (levels φ+1)).map
      (fun j => .inr (.rail v s j))))

theorem labels (φ : CNF) : FormulaIndexedGraph.labels φ = initialVertices φ ++
    (List.finRange (φ.length+1)).map (fun c => .inr (.clause c)) := by
  rw [FormulaOrderedEnumeration.labels_eq_vertices]
  rfl

theorem initialVertices_length (φ : CNF) : (initialVertices φ).length = base φ := by
  simp [initialVertices,base,FormulaRailBase.value,List.length_flatMap]
  ring

/-- Only c<C is internal; c=C is the first merged head port. -/
def port (φ : CNF) (c : Fin φ.length) :
    Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ) :=
  .inr ⟨(FormulaIndexedGraph.vertexEquiv φ).symm (.inr (.clause ⟨c.val,by omega⟩)), by
    rintro ⟨t,ht⟩
    have h := congrArg (FormulaIndexedGraph.vertexEquiv φ) ht
    cases t with
    | inl t => cases t <;> simp [FormulaIndexedGraph.terminals,
        PACFormulaReduction.terminals,PACFormulaReduction.terminal,sourceP,sourceQ,SwitchStack.sw] at h
    | inr t => cases t <;> simp [FormulaIndexedGraph.terminals,
        PACFormulaReduction.terminals,PACFormulaReduction.terminal,sinkP,sinkQ,SwitchStack.sw] at h
              ; omega⟩

theorem port_meaning (φ : CNF) (c : Fin φ.length) :
    headMeaning φ (port φ c) = .inr (.clause ⟨c.val,by omega⟩) := by
  simp [headMeaning,port,headVertex,MarkedGraph.decode]

theorem port_index (φ : CNF) (c : Fin φ.length) : index (port φ c) = base φ+c.val := by
  have hb : base φ+c.val < (FormulaIndexedGraph.labels φ).length := by
    rw [labels,List.length_append,initialVertices_length]
    simp only [List.length_map,List.length_finRange]
    omega
  have he : FormulaIndexedGraph.vertexEquiv φ ⟨base φ+c.val,hb⟩ =
      .inr (.clause ⟨c.val,by omega⟩) := by
    change (FormulaIndexedGraph.labels φ)[base φ+c.val] = _
    simp only [labels]
    rw [List.getElem_append_right (by rw [initialVertices_length]; omega)]
    simp [initialVertices_length]
  exact congrArg Fin.val ((FormulaIndexedGraph.vertexEquiv φ).symm_apply_eq.mpr he.symm)

end UnconstrainedPACDetection.FormulaClauseCursor
