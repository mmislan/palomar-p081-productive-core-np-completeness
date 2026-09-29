module

public import proofs.UnconstrainedPACDetection.FormulaVariableCursor

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchCursor
open Complexity.SAT FormulaWiring

def block (φ : CNF) (i : Fin (levels φ)) : List (Vertex φ) :=
  (List.finRange 20).map (SwitchStack.sw i)

theorem factor (φ : CNF) (i : Fin (levels φ)) :
    ∃ pre post : List (Vertex φ), pre ++ block φ i ++ post = FormulaIndexedGraph.labels φ ∧
      pre.length = 20*i.val := by
  let ip := (List.finRange (levels φ)).take i.val
  let is := (List.finRange (levels φ)).drop (i.val+1)
  have hi : i.val < (List.finRange (levels φ)).length := by simp
  have hs : List.finRange (levels φ) = ip ++ i :: is := by
    have h := List.take_append_drop i.val (List.finRange (levels φ))
    rw [← List.getElem_cons_drop hi] at h
    simpa [ip,is] using h.symm
  have hp : ip.length = i.val := by simp [ip]
  let vars := (List.finRange (varCount φ+1)).map (fun v => (Sum.inr (.var v) : Vertex φ))
  let rails := (List.finRange (varCount φ)).flatMap (fun v => [false,true].flatMap
    (fun s => (List.finRange (levels φ+1)).map (fun j => (Sum.inr (.rail v s j) : Vertex φ))))
  let clauses := (List.finRange (φ.length+1)).map (fun c => (Sum.inr (.clause c) : Vertex φ))
  refine ⟨ip.flatMap (block φ),is.flatMap (block φ) ++ vars ++ rails ++ clauses,?_,?_⟩
  · rw [FormulaOrderedEnumeration.labels_eq_vertices]
    simp only [FormulaEnumeration.vertices,hs,List.flatMap_append,List.flatMap_cons]
    simp [block,vars,rails,clauses,List.append_assoc]
    rfl
  · simp [block,List.length_flatMap,hp]
    omega

theorem index (φ : CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) :
    ((FormulaIndexedGraph.vertexEquiv φ).symm (SwitchStack.sw i p)).val = 20*i.val+p.val := by
  obtain ⟨pre,post,hblock,hpre⟩ := factor φ i
  have hp : p.val < (block φ i).length := by simp [block]
  have hb : pre.length+p.val < (FormulaIndexedGraph.labels φ).length := by
    rw [← hblock,List.length_append,List.length_append]
    omega
  have he : FormulaIndexedGraph.vertexEquiv φ ⟨pre.length+p.val,hb⟩ = SwitchStack.sw i p := by
    change (FormulaIndexedGraph.labels φ)[pre.length+p.val] = _
    simp only [← hblock,List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left hp]
    simp [block]
  simpa only [hpre] using congrArg Fin.val ((FormulaIndexedGraph.vertexEquiv φ).symm_apply_eq.mpr he.symm)

end UnconstrainedPACDetection.FormulaSwitchCursor
