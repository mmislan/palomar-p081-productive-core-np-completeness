module

public import proofs.UnconstrainedPACDetection.FormulaEnumeration
public import proofs.UnconstrainedPACDetection.PACFormulaReduction
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

namespace UnconstrainedPACDetection.FormulaIndexedGraph
open Complexity.SAT FormulaWiring DirectedPathNormalization

/-- Dedup makes the indexing contract independent of enumeration repetitions. -/
def labels (φ : CNF) : List (Vertex φ) := (FormulaEnumeration.vertices φ).dedup

theorem labels_nodup (φ : CNF) : (labels φ).Nodup := List.nodup_dedup _
theorem mem_labels (φ : CNF) (x : Vertex φ) : x ∈ labels φ := by
  simp [labels,FormulaEnumeration.mem_vertices]

/-- Both directions are executable: list lookup and first-occurrence index. -/
def vertexEquiv (φ : CNF) : Fin (labels φ).length ≃ Vertex φ :=
  List.Nodup.getEquivOfForallMemList (labels φ) (labels_nodup φ) (mem_labels φ)

def edge (φ : CNF) (i j : Fin (labels φ).length) : Prop :=
  adjacency φ (vertexEquiv φ i) (vertexEquiv φ j)

instance edgeDecidable (φ : CNF) : DecidableRel (edge φ) := fun _ _ =>
  inferInstanceAs (Decidable (adjacency φ _ _))

def terminals (φ : CNF) : (Bool ⊕ Bool) ↪ Fin (labels φ).length :=
  (PACFormulaReduction.terminals φ).trans (vertexEquiv φ).symm.toEmbedding

def arcs (φ : CNF) : List (Fin (labels φ).length × Fin (labels φ).length) :=
  (FormulaEnumeration.arcs φ).map
    (fun e => ((vertexEquiv φ).symm e.1,(vertexEquiv φ).symm e.2))

theorem mem_arcs (φ : CNF) (i j : Fin (labels φ).length) :
    (i,j) ∈ arcs φ ↔ edge φ i j := by
  constructor
  · intro h
    obtain ⟨⟨x,y⟩,hm,he⟩ := List.mem_map.mp h
    have he' := Prod.mk.inj he
    obtain ⟨rfl,rfl⟩ := he'
    simpa [edge] using (FormulaEnumeration.mem_arcs φ x y).mp hm
  · intro h
    refine List.mem_map.mpr ⟨(vertexEquiv φ i,vertexEquiv φ j),?_,by simp⟩
    exact (FormulaEnumeration.mem_arcs φ _ _).mpr h

theorem labels_bound (φ : CNF) : (labels φ).length ≤ 30*(φ.encode.length+1)^2 :=
  (List.dedup_sublist _).length_le.trans (FormulaEnumeration.vertices_polynomial φ)

theorem arcs_bound (φ : CNF) : (arcs φ).length ≤ 900*(φ.encode.length+1)^4 := by
  simpa [arcs] using FormulaEnumeration.arcs_polynomial φ

theorem linkage_iff_sat (φ : CNF) :
    Linkage (edge φ) (terminals φ (.inl false)) (terminals φ (.inl true))
      (terminals φ (.inr false)) (terminals φ (.inr true)) ↔ φ.Satisfiable := by
  unfold edge
  rw [linkage_pull_iff]
  simp only [terminals,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply]
  change Linkage (adjacency φ) (sourceP φ) (sourceQ φ) (sinkP φ) (sinkQ φ) ↔ _
  rw [← PACFormulaReduction.accepted_iff_linkage,FormulaLinkage.formula_paths_iff_sat]

end UnconstrainedPACDetection.FormulaIndexedGraph
