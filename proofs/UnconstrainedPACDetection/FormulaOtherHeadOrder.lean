module

public import proofs.UnconstrainedPACDetection.FormulaSwitchHeadOrder

@[expose] public section

namespace UnconstrainedPACDetection.FormulaOtherHeadOrder
open Complexity.SAT DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaPairExecution (tailMeaning)
open FormulaVertexHeadFields (vertex)

def variableHeads (φ : CNF) : List (FormulaWiring.Vertex φ) :=
  (List.finRange (varCount φ+1)).map (fun v => .inr (.var v))
def rails (φ : CNF) : List (FormulaWiring.Vertex φ) :=
  (List.finRange (varCount φ)).flatMap (fun v => [false,true].flatMap
    (fun s => (List.finRange (levels φ+1)).map (fun j => .inr (.rail v s j))))
def clauses (φ : CNF) : List (FormulaWiring.Vertex φ) :=
  (List.finRange (φ.length+1)).map (fun c => .inr (.clause c))

theorem variable_field (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (v : Fin (varCount φ+1)) :
    vertex φ right r a (.inr (.var v)) = FormulaSwitchVariableHeads.field φ right r a v := by
  have h := FormulaVertexHeadFields.of_internal φ right r a (FormulaVariableCursor.port φ v) rfl
  rw [FormulaVariableCursor.port_meaning] at h
  exact h

theorem variable_fields (φ : CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) :
    (variableHeads φ).flatMap (vertex φ right r a) = FormulaSwitchVariableHeads.field φ right r a 0 := by
  unfold variableHeads
  simp only [List.flatMap_map,variable_field]
  exact FormulaSwitchVariableHeads.all_variable_fields φ i p right r a ha

theorem rail_fields (φ : CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    (FormulaRailCursor.block φ v s).flatMap (vertex φ right r a) =
      FormulaRailHeadLoop.bits φ v s right r a (levels φ+1) := by
  have hr := FormulaHeadFieldOrder.range_fields (levels φ+1)
    (fun j => FormulaHeadFieldOrder.field φ right r a (FormulaRailCursor.port φ v s j))
  change FormulaRailHeadLoop.bits φ v s right r a (levels φ+1) = _ at hr
  rw [hr]
  unfold FormulaRailCursor.block
  rw [List.flatMap_map]
  apply congrArg (fun f => (List.finRange (levels φ+1)).flatMap f)
  funext j
  have h := FormulaVertexHeadFields.of_internal φ right r a (FormulaRailCursor.port φ v s j) rfl
  rw [FormulaRailCursor.port_meaning] at h
  exact h

theorem all_rails (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    (rails φ).flatMap (vertex φ right r a) =
      FormulaRailHeadVariables.bits φ right r a (varCount φ) := by
  have hr := FormulaHeadFieldOrder.range_fields (varCount φ)
    (fun v => FormulaRailHeadSigns.bits φ v right r a)
  change FormulaRailHeadVariables.bits φ right r a (varCount φ) = _ at hr
  rw [hr]
  unfold rails
  rw [List.flatMap_assoc]
  apply congrArg (fun f => (List.finRange (varCount φ)).flatMap f)
  funext v
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change (FormulaRailCursor.block φ v false ++ FormulaRailCursor.block φ v true).flatMap (vertex φ right r a) = _
  rw [List.flatMap_append,rail_fields,rail_fields]
  rfl

theorem clause_field (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (c : Fin φ.length) :
    vertex φ right r a (.inr (.clause c.castSucc)) =
      FormulaHeadFieldOrder.field φ right r a (FormulaClauseCursor.port φ c) := by
  have h := FormulaVertexHeadFields.of_internal φ right r a (FormulaClauseCursor.port φ c) rfl
  rw [FormulaClauseCursor.port_meaning] at h
  exact h

theorem final_clause (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    vertex φ right r a (.inr (.clause (Fin.last φ.length))) = [] :=
  FormulaVertexHeadFields.terminal φ right r a (.inr false)

theorem clause_fields (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    (clauses φ).flatMap (vertex φ right r a) = FormulaClauseHeadLoop.bits φ right r a φ.length := by
  have hr := FormulaHeadFieldOrder.range_fields φ.length
    (fun c => FormulaHeadFieldOrder.field φ right r a (FormulaClauseCursor.port φ c))
  change FormulaClauseHeadLoop.bits φ right r a φ.length = _ at hr
  rw [hr]
  unfold clauses
  rw [List.finRange_succ_last]
  simp only [List.map_append,List.map_map,List.flatMap_append,List.flatMap_map,
    List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,final_clause,List.append_nil,
    Function.comp_def,clause_field]

end UnconstrainedPACDetection.FormulaOtherHeadOrder
