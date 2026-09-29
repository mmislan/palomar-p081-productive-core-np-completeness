module

public import proofs.UnconstrainedPACDetection.FormulaSwitchRailPair
public import Mathlib.Data.List.Infix

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailCursor
open Complexity.SAT FormulaWiring DirectedLinkageSource
open FormulaCoefficientPlan (index tag)
open FormulaPairExecution (headMeaning)

def block (φ : CNF) (v : Fin (varCount φ)) (s : Bool) : List (Vertex φ) :=
  (List.finRange (levels φ+1)).map (fun j => .inr (.rail v s j))

/-- A rail cursor is always an internal canonical port, including both endpoints. -/
def port (φ : CNF) (v : Fin (varCount φ)) (s : Bool) (j : Fin (levels φ+1)) :
    Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ) :=
  .inr ⟨(FormulaIndexedGraph.vertexEquiv φ).symm (.inr (.rail v s j)), by
    rintro ⟨t,ht⟩
    have h := congrArg (FormulaIndexedGraph.vertexEquiv φ) ht
    cases t with
    | inl t => cases t <;> simp [FormulaIndexedGraph.terminals,
        PACFormulaReduction.terminals,PACFormulaReduction.terminal,sourceP,sourceQ,SwitchStack.sw] at h
    | inr t => cases t <;> simp [FormulaIndexedGraph.terminals,
        PACFormulaReduction.terminals,PACFormulaReduction.terminal,sinkP,sinkQ,SwitchStack.sw] at h⟩

theorem port_meaning (φ : CNF) (v : Fin (varCount φ)) (s : Bool) (j : Fin (levels φ+1)) :
    headMeaning φ (port φ v s j) = .inr (.rail v s j) := by
  simp [headMeaning,port,headVertex,MarkedGraph.decode]

theorem port_tag (φ : CNF) (v : Fin (varCount φ)) (s : Bool) (j : Fin (levels φ+1)) :
    tag (port φ v s j) = none := rfl

/-- The whole cursor interval is contiguous in the existing ordered vertex list. -/
theorem block_infix (φ : CNF) (v : Fin (varCount φ)) (s : Bool) :
    block φ v s <:+: FormulaIndexedGraph.labels φ := by
  rw [FormulaOrderedEnumeration.labels_eq_vertices]
  obtain ⟨pre,post,hv⟩ := List.mem_iff_append.mp (List.mem_finRange v)
  let switches : List (Vertex φ) := (List.finRange (levels φ)).flatMap (fun i =>
    (List.finRange 20).map (SwitchStack.sw i))
  let vars := (List.finRange (varCount φ+1)).map (fun w => (Sum.inr (.var w) : Vertex φ))
  let rails := fun w : Fin (varCount φ) => block φ w false ++ block φ w true
  let clauses := (List.finRange (φ.length+1)).map (fun c => (Sum.inr (.clause c) : Vertex φ))
  have he : FormulaEnumeration.vertices φ = switches ++ vars ++
      pre.flatMap rails ++ (block φ v false ++ block φ v true) ++
      post.flatMap rails ++ clauses := by
    simp only [FormulaEnumeration.vertices,hv,List.flatMap_append,List.flatMap_cons]
    simp [switches,vars,rails,clauses,block,List.append_assoc]
  rw [he]
  cases s with
  | false =>
    refine ⟨switches ++ vars ++ pre.flatMap rails,
      block φ v true ++ post.flatMap rails ++ clauses,?_⟩
    simp [List.append_assoc]
  | true =>
    refine ⟨switches ++ vars ++ pre.flatMap rails ++ block φ v false,
      post.flatMap rails ++ clauses,?_⟩
    simp [List.append_assoc]

/-- A single starting index and physical increment suffice for the complete block. -/
theorem port_index (φ : CNF) (v : Fin (varCount φ)) (s : Bool)
    (pre post : List (Vertex φ))
    (h : pre ++ block φ v s ++ post = FormulaIndexedGraph.labels φ)
    (j : Fin (levels φ+1)) : index (port φ v s j) = pre.length+j.val := by
  have hj : j.val < (block φ v s).length := by simpa [block] using j.isLt
  have hb : pre.length+j.val < (FormulaIndexedGraph.labels φ).length := by
    rw [← h,List.length_append,List.length_append]; omega
  have he : FormulaIndexedGraph.vertexEquiv φ ⟨pre.length+j.val,hb⟩ =
      .inr (.rail v s j) := by
    change (FormulaIndexedGraph.labels φ)[pre.length+j.val] = _
    simp only [← h,List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left hj]
    simp [block]
  have hi := (FormulaIndexedGraph.vertexEquiv φ).symm_apply_eq.mpr he.symm
  exact congrArg Fin.val hi

end UnconstrainedPACDetection.FormulaRailCursor
