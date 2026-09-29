module

public import proofs.UnconstrainedPACDetection.FormulaRailHeadLoop

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailBase
open Complexity.SAT FormulaWiring
open FormulaRailCursor (block)

def value (L V v : Nat) (s : Bool) : Nat :=
  20*L+(V+1)+(2*v+(if s then 1 else 0))*(L+1)

/-- The physical starting index is an explicit polynomial in live dimensions. -/
theorem factor (φ : CNF) (v : Fin (varCount φ)) (s : Bool) :
    ∃ pre post : List (Vertex φ),
      pre ++ block φ v s ++ post = FormulaIndexedGraph.labels φ ∧
      pre.length = value (levels φ) (varCount φ) v.val s := by
  let vp := (List.finRange (varCount φ)).take v.val
  let vs := (List.finRange (varCount φ)).drop (v.val+1)
  have hi : v.val < (List.finRange (varCount φ)).length := by simp
  have hv : List.finRange (varCount φ) = vp ++ v :: vs := by
    have h := List.take_append_drop v.val (List.finRange (varCount φ))
    rw [← List.getElem_cons_drop hi] at h
    simpa [vp,vs] using h.symm
  have hp : vp.length = v.val := by simp [vp]
  let switches : List (Vertex φ) := (List.finRange (levels φ)).flatMap (fun i =>
    (List.finRange 20).map (SwitchStack.sw i))
  let vars := (List.finRange (varCount φ+1)).map (fun w => (Sum.inr (.var w) : Vertex φ))
  let rails := fun w : Fin (varCount φ) => block φ w false ++ block φ w true
  let clauses := (List.finRange (φ.length+1)).map (fun c => (Sum.inr (.clause c) : Vertex φ))
  have he : FormulaIndexedGraph.labels φ = switches ++ vars ++
      vp.flatMap rails ++ (block φ v false ++ block φ v true) ++
      vs.flatMap rails ++ clauses := by
    rw [FormulaOrderedEnumeration.labels_eq_vertices]
    simp only [FormulaEnumeration.vertices,hv,List.flatMap_append,List.flatMap_cons]
    simp [switches,vars,rails,clauses,block,List.append_assoc]
  have hl : (vp.flatMap rails).length = v.val*(2*(levels φ+1)) := by
    simp [rails,block,List.length_flatMap,hp,two_mul]
  cases s with
  | false =>
    refine ⟨switches ++ vars ++ vp.flatMap rails,
      block φ v true ++ vs.flatMap rails ++ clauses,?_,?_⟩
    · rw [he]; simp [List.append_assoc]
    · simp [List.length_append,hl,switches,vars,List.length_flatMap,value]
      ring
  | true =>
    refine ⟨switches ++ vars ++ vp.flatMap rails ++ block φ v false,
      vs.flatMap rails ++ clauses,?_,?_⟩
    · rw [he]; simp [List.append_assoc]
    · simp [List.length_append,hl,switches,vars,List.length_flatMap,block,value]
      ring

end UnconstrainedPACDetection.FormulaRailBase
