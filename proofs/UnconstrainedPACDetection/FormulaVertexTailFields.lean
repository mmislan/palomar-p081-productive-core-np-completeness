module

public import proofs.UnconstrainedPACDetection.FormulaAllClauseTails

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVertexTailFields
open Complexity.SAT DirectedLinkageSource
open FormulaPairExecution (tailMeaning)
open FormulaCoefficientPlan (tag)

def port (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (FormulaHeadFieldOrder.field φ right r a)

def indexed (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (k : Fin (FormulaIndexedGraph.labels φ).length) : List Bool :=
  if hk : k ∉ Set.range (FormulaIndexedGraph.terminals φ) then port φ right r (.inr ⟨k,hk⟩) else []

def vertex (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (y : FormulaWiring.Vertex φ) : List Bool :=
  indexed φ right r ((FormulaIndexedGraph.vertexEquiv φ).symm y)

theorem of_internal (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ha : tag a = none) :
    vertex φ right r (tailMeaning φ a) = port φ right r a := by
  cases a with
  | inl a => simp [tag] at ha
  | inr a =>
    simp [vertex,indexed,tailMeaning,tailVertex,MarkedGraph.decode,a.property]
    apply congrArg (fun z => port φ right r (.inr z))
    exact Subtype.ext rfl

theorem tail_scan (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (port φ right r) =
      port φ right r (.inl false) ++ port φ right r (.inl true) ++
      (FormulaIndexedGraph.labels φ).flatMap (vertex φ right r) := by
  have hs := FormulaHeadFieldOrder.selected_fields (List.finRange (FormulaIndexedGraph.labels φ).length)
    (fun k => k ∉ Set.range (FormulaIndexedGraph.terminals φ)) (List.nodup_finRange _)
    (fun k => port φ right r (.inr k)) (indexed φ right r)
    (by intro k; simp [indexed,k.property]) (by intro k hk; unfold indexed; exact dite_eq_right hk)
  change (FiniteMarkedSource.internals (FormulaIndexedGraph.terminals φ)).flatMap
    (fun k => port φ right r (.inr k)) = _ at hs
  have hv : (FormulaIndexedGraph.labels φ).flatMap (vertex φ right r) =
      (List.finRange (FormulaIndexedGraph.labels φ).length).flatMap (indexed φ right r) := by
    have he := congrArg (fun xs => xs.flatMap (vertex φ right r)) (FormulaHeadFieldOrder.indexed_vertices φ)
    simpa only [List.flatMap_map,vertex,Equiv.symm_apply_apply] using he.symm
  rw [← hv] at hs
  simpa only [FormulaOrderedTable.rows,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.flatMap_map,List.append_assoc] using
      congrArg (fun z => port φ right r (.inl false) ++ port φ right r (.inl true) ++ z) hs

theorem terminal (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (t : Bool ⊕ Bool) :
    vertex φ right r (PACFormulaReduction.terminals φ t) = [] := by
  have ht : (FormulaIndexedGraph.vertexEquiv φ).symm (PACFormulaReduction.terminals φ t) ∈
      Set.range (FormulaIndexedGraph.terminals φ) := ⟨t,rfl⟩
  simp [vertex,indexed,ht]

theorem variable_field (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (v : Fin (FormulaWiring.varCount φ+1)) :
    vertex φ right r (.inr (.var v)) = port φ right r (FormulaVariableCursor.port φ v) := by
  have h := of_internal φ right r (FormulaVariableCursor.port φ v) rfl
  simpa [tailMeaning,FormulaVariableCursor.port,tailVertex,MarkedGraph.decode] using h

theorem rail_field (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (v : Fin (FormulaWiring.varCount φ)) (s : Bool) (j : Fin (FormulaWiring.levels φ+1)) :
    vertex φ right r (.inr (.rail v s j)) = port φ right r (FormulaRailCursor.port φ v s j) := by
  have h := of_internal φ right r (FormulaRailCursor.port φ v s j) rfl
  simpa [tailMeaning,FormulaRailCursor.port,tailVertex,MarkedGraph.decode] using h

theorem clause_field (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (c : Fin φ.length) :
    vertex φ right r (.inr (.clause c.castSucc)) = port φ right r (FormulaClauseCursor.port φ c) := by
  have h := of_internal φ right r (FormulaClauseCursor.port φ c) rfl
  have hm : tailMeaning φ (FormulaClauseCursor.port φ c) = .inr (.clause c.castSucc) := by
    simp [tailMeaning,FormulaClauseCursor.port,tailVertex,MarkedGraph.decode]
    rfl
  rw [hm] at h
  exact h

theorem variable_fields (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    (FormulaOtherHeadOrder.variableHeads φ).flatMap (vertex φ right r) = FormulaAllVariableTails.bits φ right r := by
  unfold FormulaOtherHeadOrder.variableHeads FormulaAllVariableTails.bits
  simp only [List.flatMap_map,variable_field,port]

theorem rail_fields (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    (FormulaOtherHeadOrder.rails φ).flatMap (vertex φ right r) =
      FormulaAllRailTails.bits φ right r (FormulaWiring.varCount φ) := by
  have hr := FormulaHeadFieldOrder.range_fields (FormulaWiring.varCount φ)
    (fun v => FormulaRailTailReentrant.bits φ v right r)
  change FormulaAllRailTails.bits φ right r (FormulaWiring.varCount φ) = _ at hr
  rw [hr]
  unfold FormulaOtherHeadOrder.rails
  rw [List.flatMap_assoc]
  apply congrArg (fun f => (List.finRange (FormulaWiring.varCount φ)).flatMap f)
  funext v
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.flatMap_append,List.flatMap_map,rail_field]
  rfl

theorem clause_fields (φ : CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    (FormulaOtherHeadOrder.clauses φ).flatMap (vertex φ right r) = FormulaAllClauseTails.bits φ right r := by
  have ht : vertex φ right r (.inr (.clause (Fin.last φ.length))) = [] := terminal φ right r (.inr false)
  unfold FormulaOtherHeadOrder.clauses FormulaAllClauseTails.bits
  rw [List.finRange_succ_last]
  simp only [List.map_append,List.map_map,List.flatMap_append,List.flatMap_map,
    List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,ht,List.append_nil,
    Function.comp_def,clause_field,port]

end UnconstrainedPACDetection.FormulaVertexTailFields
