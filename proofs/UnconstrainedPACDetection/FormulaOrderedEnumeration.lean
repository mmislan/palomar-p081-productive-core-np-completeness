module

public import proofs.UnconstrainedPACDetection.FormulaReactionCount

@[expose] public section

namespace UnconstrainedPACDetection.FormulaOrderedEnumeration
open Complexity.SAT FormulaWiring DirectedLinkageSource

/-- The canonical vertex indices already enumerate each vertex once. -/
theorem labels_eq_vertices (φ : CNF) :
    FormulaIndexedGraph.labels φ = FormulaEnumeration.vertices φ := by
  have h := Fintype.card_congr (FormulaIndexedGraph.vertexEquiv φ)
  rw [Fintype.card_fin,FormulaReactionCount.vertex_count] at h
  apply (List.dedup_sublist (FormulaEnumeration.vertices φ)).eq_of_length
  exact h.trans (FormulaEnumeration.vertices_length φ).symm

theorem vertices_nodup (φ : CNF) : (FormulaEnumeration.vertices φ).Nodup := by
  rw [← labels_eq_vertices]
  exact FormulaIndexedGraph.labels_nodup φ

/-- Erasing proofs after ordered selection is ordinary filtering, without a reorder. -/
theorem selected_values {X : Type*} [DecidableEq X] (l : List X)
    (P : X → Prop) [DecidablePred P] (hn : l.Nodup) :
    (FiniteSubtypeEnumeration.selected l P).map Subtype.val = l.filter (fun x => decide (P x)) := by
  have hf : (l.filterMap (fun x => if h : P x then some (⟨x,h⟩ : {x // P x})
      else none)).map Subtype.val = l.filter (fun x => decide (P x)) := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      have ht := ih hn.of_cons
      by_cases hx : P x <;> simpa [hx] using ht
  unfold FiniteSubtypeEnumeration.selected
  rw [← List.dedup_map_of_injective Subtype.val_injective,hf]
  exact (hn.filter _).dedup

theorem internals_values {n : Nat} (T : (Bool ⊕ Bool) ↪ Fin n) :
    (FiniteMarkedSource.internals T).map Subtype.val =
      (List.finRange n).filter (fun x => decide (x ∉ Set.range T)) := by
  exact selected_values _ _ (List.nodup_finRange n)

theorem ports_nodup {n : Nat} (T : (Bool ⊕ Bool) ↪ Fin n) :
    ([Sum.inl false,Sum.inl true] ++
      (FiniteMarkedSource.internals T).map Sum.inr).Nodup := by
  have hi := FiniteSubtypeEnumeration.nodup_selected (List.finRange n)
    (fun x => x ∉ Set.range T)
  change (Sum.inl false :: Sum.inl true ::
    (FiniteMarkedSource.internals T).map Sum.inr).Nodup
  simp only [List.nodup_cons,List.mem_cons,List.mem_map,not_or]
  refine ⟨⟨(by intro h; cases h),?_⟩,⟨?_,?_⟩⟩
  · rintro ⟨x,_,h⟩; cases h
  · rintro ⟨x,_,h⟩; cases h
  · exact hi.map Sum.inr_injective

theorem ports_eq {n : Nat} (T : (Bool ⊕ Bool) ↪ Fin n) :
    FiniteMarkedSource.ports T = [Sum.inl false,Sum.inl true] ++
      (FiniteMarkedSource.internals T).map Sum.inr :=
  (ports_nodup T).dedup

/-- The entity order is the ordered port product filtered by adjacency. -/
theorem arc_values {n : Nat} (A : Fin n → Fin n → Prop) [DecidableRel A]
    (T : (Bool ⊕ Bool) ↪ Fin n) :
    (FiniteMarkedSource.arcList A T).map Subtype.val =
      ((FiniteMarkedSource.ports T).product (FiniteMarkedSource.ports T)).filter
        (fun e => decide (FiniteMarkedSource.arcPredicate A T e)) := by
  apply selected_values
  exact (List.nodup_dedup _).product (List.nodup_dedup _)

end UnconstrainedPACDetection.FormulaOrderedEnumeration
