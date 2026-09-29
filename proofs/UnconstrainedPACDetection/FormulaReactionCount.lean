module

public import proofs.UnconstrainedPACDetection.FormulaDegreeSum

@[expose] public section

namespace UnconstrainedPACDetection.FormulaReactionCount
open Complexity.SAT FormulaWiring DirectedLinkageSource

def physicalEquiv (V : Type*) : PhysicalVertex V ≃ Bool ⊕ (Bool ⊕ V) where
  toFun
    | .source b => .inl b
    | .sink b => .inr (.inl b)
    | .internal v => .inr (.inr v)
  invFun
    | .inl b => .source b
    | .inr (.inl b) => .sink b
    | .inr (.inr v) => .internal v
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with b | b | v <;> rfl

theorem ports_count {n : Nat} (T : (Bool ⊕ Bool) ↪ Fin n) :
    (FiniteMarkedSource.ports T).length+2 = n := by
  classical
  have hr := Fintype.card_congr (FiniteMarkedSource.rowEquiv T)
  have hv := Fintype.card_congr (MarkedGraph.vertexEquiv T)
  have hp := Fintype.card_congr (physicalEquiv (MarkedGraph.Internal T))
  simp only [Fintype.card_fin,Fintype.card_sum,Fintype.card_bool] at hr hv hp
  omega

theorem vertex_count (φ : CNF) :
    Fintype.card (Vertex φ) =
      20*levels φ+2*varCount φ*(levels φ+1)+varCount φ+φ.length+2 := by
  have he := Fintype.card_congr (FormulaDegreeSum.externalEquiv φ)
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at he
  have hc : Fintype.card (Vertex φ) =
      Fintype.card (Fin (levels φ) × Fin 20) + Fintype.card (External φ) :=
    Fintype.card_sum
  rw [hc]
  simp only [Fintype.card_prod,Fintype.card_fin,he]
  ring

theorem table_reactions (φ : CNF) :
    (FormulaPACEncoding.table φ).reactions =
      20*levels φ+2*varCount φ*(levels φ+1)+varCount φ+φ.length := by
  have projection {m n : Nat} (s : ReversibleSource (Fin m) (Fin n)) :
      (GraphSourceTable.dense s).reactions = n := rfl
  have hr := ports_count (FormulaIndexedGraph.terminals φ)
  have hv := Fintype.card_congr (FormulaIndexedGraph.vertexEquiv φ)
  rw [Fintype.card_fin,vertex_count] at hv
  unfold FormulaPACEncoding.table FiniteMarkedSource.dense
  rw [projection]
  omega

/-- Exact second source header, retaining the existing merged-terminal enumeration. -/
theorem table_reactions_from_counts (φ : CNF) :
    (FormulaPACEncoding.table φ).reactions =
      20+20*(occurrences φ).length+5*varCount φ+
        2*(occurrences φ).length*varCount φ+φ.length := by
  rw [table_reactions]
  unfold levels
  ring

end UnconstrainedPACDetection.FormulaReactionCount
