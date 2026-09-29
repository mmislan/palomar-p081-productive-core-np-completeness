module

public import proofs.UnconstrainedPACDetection.FormulaHeadFieldOrder
public import proofs.UnconstrainedPACDetection.FormulaSwitchCursor

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVertexHeadFields
open Complexity.SAT DirectedLinkageSource
open FormulaPairExecution (tailMeaning headMeaning)
open FormulaCoefficientPlan (choose tag index)
open FormulaHeadFieldOrder (field)

def indexed (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (k : Fin (FormulaIndexedGraph.labels φ).length) : List Bool :=
  if hk : k ∉ Set.range (FormulaIndexedGraph.terminals φ) then field φ right r a (.inr ⟨k,hk⟩) else []

def vertex (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (y : FormulaWiring.Vertex φ) : List Bool :=
  indexed φ right r a ((FormulaIndexedGraph.vertexEquiv φ).symm y)

theorem of_internal (φ : CNF) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (hb : tag b = none) :
    vertex φ right r a (headMeaning φ b) = field φ right r a b := by
  cases b with
  | inl b => simp [tag] at hb
  | inr b =>
    simp [vertex,indexed,headMeaning,headVertex,MarkedGraph.decode,b.property]
    apply congrArg (fun z => field φ right r a (.inr z))
    exact Subtype.ext rfl

theorem head_scan (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a) =
      FormulaMergedHeads.field φ right r a false ++ FormulaMergedHeads.field φ right r a true ++
      (FormulaIndexedGraph.labels φ).flatMap (vertex φ right r a) := by
  have hs := FormulaHeadFieldOrder.selected_fields (List.finRange (FormulaIndexedGraph.labels φ).length)
    (fun k => k ∉ Set.range (FormulaIndexedGraph.terminals φ)) (List.nodup_finRange _)
    (fun k => field φ right r a (.inr k)) (indexed φ right r a)
    (by intro k; simp [indexed,k.property]) (by intro k hk; unfold indexed; exact dite_eq_right hk)
  change (FiniteMarkedSource.internals (FormulaIndexedGraph.terminals φ)).flatMap
    (fun k => field φ right r a (.inr k)) = _ at hs
  have hv : (FormulaIndexedGraph.labels φ).flatMap (vertex φ right r a) =
      (List.finRange (FormulaIndexedGraph.labels φ).length).flatMap (indexed φ right r a) := by
    have he := congrArg (fun xs => xs.flatMap (vertex φ right r a)) (FormulaHeadFieldOrder.indexed_vertices φ)
    simpa only [List.flatMap_map,vertex,Equiv.symm_apply_apply] using he.symm
  rw [← hv] at hs
  have hf (s : Bool) : field φ right r a (.inl s) = FormulaMergedHeads.field φ right r a s := rfl
  simpa only [FormulaOrderedTable.rows,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.flatMap_map,List.append_assoc,hf] using
      congrArg (fun z => field φ right r a (.inl false) ++ field φ right r a (.inl true) ++ z) hs

def raw (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (y : FormulaWiring.Vertex φ) : List Bool :=
  if FormulaWiring.adjacency φ (tailMeaning φ a) y then BinaryFields.encodeField
    (FormulaCoefficientPlan.value (choose right (tag r) (tag a) none) (index r)
      (if right then ((FormulaIndexedGraph.vertexEquiv φ).symm y).val else index a)).bits else []

theorem nonterminal (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (y : FormulaWiring.Vertex φ)
    (hy : (FormulaIndexedGraph.vertexEquiv φ).symm y ∉ Set.range (FormulaIndexedGraph.terminals φ)) :
    vertex φ right r a y = raw φ right r a y := by
  let b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ) := .inr ⟨(FormulaIndexedGraph.vertexEquiv φ).symm y,hy⟩
  have hm : headMeaning φ b = y := by simp [b,headMeaning,headVertex,MarkedGraph.decode]
  have he := FormulaHeadFieldOrder.arc_meaning φ a b
  rw [hm] at he
  have hv := (FormulaVariablePair.field_eq (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) right r a b).symm
  simpa only [vertex,indexed,dite_eq_left hy,field,raw,he,b,tag,index] using hv

theorem terminal (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (t : Bool ⊕ Bool) :
    vertex φ right r a (PACFormulaReduction.terminals φ t) = [] := by
  have ht : (FormulaIndexedGraph.vertexEquiv φ).symm (PACFormulaReduction.terminals φ t) ∈
      Set.range (FormulaIndexedGraph.terminals φ) := ⟨t,rfl⟩
  simp [vertex,indexed,ht]

theorem internal_iff (φ : CNF) (y : FormulaWiring.Vertex φ) :
    (FormulaIndexedGraph.vertexEquiv φ).symm y ∉ Set.range (FormulaIndexedGraph.terminals φ) ↔
      y ∉ Set.range (PACFormulaReduction.terminals φ) := by
  constructor
  · intro h ⟨t,ht⟩
    apply h
    refine ⟨t,?_⟩
    simp [FormulaIndexedGraph.terminals,ht]
  · intro h ⟨t,ht⟩
    apply h
    refine ⟨t,?_⟩
    have he := congrArg (FormulaIndexedGraph.vertexEquiv φ) ht
    simpa [FormulaIndexedGraph.terminals] using he

end UnconstrainedPACDetection.FormulaVertexHeadFields
