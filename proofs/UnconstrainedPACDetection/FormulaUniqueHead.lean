module

public import proofs.UnconstrainedPACDetection.FormulaRailTailMiddle
public import proofs.UnconstrainedPACDetection.FormulaOutdegree

@[expose] public section

namespace UnconstrainedPACDetection.FormulaUniqueHead
open Complexity Complexity.TM DirectedLinkageSource
open FormulaPairExecution (tailMeaning headMeaning)
open FormulaHeadFieldOrder (field)

theorem head_injective (φ : SAT.CNF) : Function.Injective (headMeaning φ) := by
  intro x y h
  exact headVertex_injective (MarkedGraph.decode_injective _ ((FormulaIndexedGraph.vertexEquiv φ).injective h))

theorem canonical (φ : SAT.CNF) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (hnext : ∀ y, FormulaWiring.adjacency φ (tailMeaning φ a) y ↔ y=headMeaning φ b) :
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a) =
      field φ right r a b := by
  have he (q : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
      field φ right r a q = if q=b then field φ right r a q else [] := by
    by_cases hq : q=b
    · simp only [ite_eq_left hq]
    · rw [ite_eq_right hq]
      unfold field
      apply ite_eq_right
      rw [FormulaHeadFieldOrder.arc_meaning,hnext]
      exact fun h => hq (head_injective φ h)
  have hn : (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).Nodup := by
    unfold FormulaOrderedTable.rows
    rw [← FormulaOrderedEnumeration.ports_eq]
    exact List.nodup_dedup _
  have hm : b ∈ FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ) := by
    unfold FormulaOrderedTable.rows
    rw [← FormulaOrderedEnumeration.ports_eq]
    exact FiniteMarkedSource.mem_ports _ b
  have hx := FormulaVariableTailCanonical.isolated _ hn b hm (field φ right r a)
  have hf : (fun q => field φ right r a q) = (fun q => if q=b then field φ right r a q else []) := funext he
  exact (congrArg (fun g => (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap g) hf).trans hx

theorem middle_bits (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s i.castSucc)) :
    field φ right r a (FormulaRailTailCandidates.switchPort φ i) ++
      field φ right r a (FormulaRailCursor.port φ v s i.succ) =
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a) := by
  cases hb : FormulaWiring.blocked φ i v s with
  | false =>
    have hn (y : FormulaWiring.Vertex φ) : FormulaWiring.adjacency φ (tailMeaning φ a) y ↔
        y=headMeaning φ (FormulaRailCursor.port φ v s i.succ) := by
      rw [ha,FormulaOutdegree.rail_iff,FormulaRailCursor.port_meaning]
      simp [FormulaOutdegree.railNext,i.isLt,hb]
      rfl
    have hz : field φ right r a (FormulaRailTailCandidates.switchPort φ i) = [] := by
      unfold field
      apply ite_eq_right
      rw [FormulaHeadFieldOrder.arc_meaning,hn,FormulaRailTailCandidates.switch_meaning,
        FormulaRailCursor.port_meaning]
      simp [SwitchStack.sw]
    rw [hz,List.nil_append,canonical φ right r a _ hn]
  | true =>
    have hn (y : FormulaWiring.Vertex φ) : FormulaWiring.adjacency φ (tailMeaning φ a) y ↔
        y=headMeaning φ (FormulaRailTailCandidates.switchPort φ i) := by
      rw [ha,FormulaOutdegree.rail_iff,FormulaRailTailCandidates.switch_meaning]
      simp [FormulaOutdegree.railNext,i.isLt,hb]
    have hz : field φ right r a (FormulaRailCursor.port φ v s i.succ) = [] := by
      unfold field
      apply ite_eq_right
      rw [FormulaHeadFieldOrder.arc_meaning,hn,FormulaRailTailCandidates.switch_meaning,
        FormulaRailCursor.port_meaning]
      simp [SwitchStack.sw]
    rw [hz,List.append_nil,canonical φ right r a _ hn]

end UnconstrainedPACDetection.FormulaUniqueHead
