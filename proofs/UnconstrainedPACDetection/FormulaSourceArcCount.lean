module

public import proofs.UnconstrainedPACDetection.FormulaNormalization
public import proofs.UnconstrainedPACDetection.FormulaPACEncoding

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSourceArcCount
open Complexity.SAT FormulaWiring DirectedLinkageSource

private noncomputable def physicalArcEquiv {X : Type*}
    (A : PhysicalVertex X → PhysicalVertex X → Prop) :
    FromAdjacency.Arcs A ≃ {e : PhysicalVertex X × PhysicalVertex X //
      DirectedPathNormalization.pruned A (.source false) (.source true)
        (.sink false) (.sink true) e.1 e.2} :=
  Equiv.ofBijective
    (fun e => ⟨(tailVertex e.val.1,headVertex e.val.2), e.property.1,e.property.2,
      tailVertex_ne_sink _ _,tailVertex_ne_sink _ _,
      headVertex_ne_source _ _,headVertex_ne_source _ _⟩)
    (by
      constructor
      · intro e f h
        have he := congrArg Subtype.val h
        apply Subtype.ext
        exact Prod.ext (tailVertex_injective (congrArg Prod.fst he))
          (headVertex_injective (congrArg Prod.snd he))
      · rintro ⟨⟨u,v⟩,ha,hne,ht0,ht1,hs0,hs1⟩
        cases u with
        | source b =>
          cases v with
          | source c => cases c <;> contradiction
          | sink c => exact ⟨⟨(.inl b,.inl c),ha,hne⟩,rfl⟩
          | internal z => exact ⟨⟨(.inl b,.inr z),ha,hne⟩,rfl⟩
        | sink b => cases b <;> contradiction
        | internal z =>
          cases v with
          | source c => cases c <;> contradiction
          | sink c => exact ⟨⟨(.inr z,.inl c),ha,hne⟩,rfl⟩
          | internal w => exact ⟨⟨(.inr z,.inr w),ha,hne⟩,rfl⟩)

private noncomputable def decoded (φ : CNF) :
    PhysicalVertex (MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) ≃ Vertex φ :=
  (MarkedGraph.vertexEquiv (FormulaIndexedGraph.terminals φ)).trans
    (FormulaIndexedGraph.vertexEquiv φ)

private theorem decoded_source (φ : CNF) (b : Bool) :
    decoded φ (.source b) = if b then sourceQ φ else sourceP φ := by
  change FormulaIndexedGraph.vertexEquiv φ ((FormulaIndexedGraph.vertexEquiv φ).symm
    (PACFormulaReduction.terminal φ (.inl b))) = _
  rw [Equiv.apply_symm_apply]
  cases b <;> rfl

private theorem decoded_sink (φ : CNF) (b : Bool) :
    decoded φ (.sink b) = if b then sinkQ φ else sinkP φ := by
  change FormulaIndexedGraph.vertexEquiv φ ((FormulaIndexedGraph.vertexEquiv φ).symm
    (PACFormulaReduction.terminal φ (.inr b))) = _
  rw [Equiv.apply_symm_apply]
  cases b <;> rfl

private theorem decoded_pruned (φ : CNF)
    (u v : PhysicalVertex (MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))) :
    DirectedPathNormalization.pruned
      (MarkedGraph.pulled (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ))
      (.source false) (.source true) (.sink false) (.sink true) u v ↔
      adjacency φ (decoded φ u) (decoded φ v) := by
  have hp := congrFun (congrFun (FormulaNormalization.pruned_eq φ) (decoded φ u)) (decoded φ v)
  rw [← hp]
  simp only [DirectedPathNormalization.pruned]
  have he : MarkedGraph.pulled (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) u v = adjacency φ (decoded φ u) (decoded φ v) := rfl
  rw [he]
  have hi := (decoded φ).injective
  have hn (a b) : decoded φ a ≠ decoded φ b ↔ a ≠ b :=
    not_congr (hi.eq_iff)
  have ht0 : decoded φ (.sink false) = sinkP φ := decoded_sink φ false
  have ht1 : decoded φ (.sink true) = sinkQ φ := decoded_sink φ true
  have hs0 : decoded φ (.source false) = sourceP φ := decoded_source φ false
  have hs1 : decoded φ (.source true) = sourceQ φ := decoded_source φ true
  rw [← ht0,← ht1,← hs0,← hs1]
  simp only [hn]

/-- The actual source entities correspond bijectively to the formula's directed arcs. -/
noncomputable def entityArcEquiv (φ : CNF) :
    Fin (FiniteMarkedSource.arcList (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ)).length ≃
      {e : Vertex φ × Vertex φ // adjacency φ e.1 e.2} :=
  (FiniteMarkedSource.entityEquiv (FormulaIndexedGraph.edge φ)
    (FormulaIndexedGraph.terminals φ)).trans
      ((physicalArcEquiv _).trans
        (Equiv.subtypeEquiv (Equiv.prodCongr (decoded φ) (decoded φ))
          (fun e => decoded_pruned φ e.1 e.2)))

/-- Exact header count transport; this does not change the source's entity order. -/
theorem entity_count (φ : CNF) :
    (FiniteMarkedSource.arcList (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ)).length =
      Fintype.card {e : Vertex φ × Vertex φ // adjacency φ e.1 e.2} := by
  simpa using Fintype.card_congr (entityArcEquiv φ)

/-- The first serialized source header is the number of formula adjacency pairs. -/
theorem table_entities (φ : CNF) :
    (FormulaPACEncoding.table φ).entities =
      Fintype.card {e : Vertex φ × Vertex φ // adjacency φ e.1 e.2} := by
  have projection {m n : Nat} (s : ReversibleSource (Fin m) (Fin n)) :
      (GraphSourceTable.dense s).entities = m := rfl
  unfold FormulaPACEncoding.table FiniteMarkedSource.dense
  rw [projection]
  exact entity_count φ

end UnconstrainedPACDetection.FormulaSourceArcCount
