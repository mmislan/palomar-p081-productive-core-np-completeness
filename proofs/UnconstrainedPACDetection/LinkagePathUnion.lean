module

public import proofs.UnconstrainedPACDetection.ArcPathIncidences

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource.PathUnion

variable {V E : Type*} [DecidableEq E] [DecidableEq V] {D : Network V E}
variable (P : ArcPath D false false) (R : ArcPath D true true)

def entities : Finset E := Finset.univ.image P.arcs ∪ Finset.univ.image R.arcs
def rows : Finset (Bool ⊕ V) := (entities P R).image D.tail

omit [DecidableEq V] in
theorem mem_entities (e : E) : e ∈ entities P R ↔
    (∃ i, P.arcs i = e) ∨ ∃ j, R.arcs j = e := by simp [entities]

omit [DecidableEq V] in
theorem arcP_mem (i : Fin P.length) : P.arcs i ∈ entities P R :=
  (mem_entities P R _).mpr (Or.inl ⟨i, rfl⟩)
omit [DecidableEq V] in
theorem arcR_mem (i : Fin R.length) : R.arcs i ∈ entities P R :=
  (mem_entities P R _).mpr (Or.inr ⟨i, rfl⟩)

theorem tail_mem {e : E} (he : e ∈ entities P R) : D.tail e ∈ rows P R :=
  Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem source_mem : Sum.inl false ∈ rows P R := by
  rw [← P.start]
  exact tail_mem P R (arcP_mem P R _)
theorem sink_mem : Sum.inl true ∈ rows P R := by
  rw [← R.start]
  exact tail_mem P R (arcR_mem P R _)

theorem head_mem {e : E} (he : e ∈ entities P R) : D.head e ∈ rows P R := by
  rcases (mem_entities P R e).mp he with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · by_cases hi : i.1 + 1 < P.length
    · rw [P.head_before_last i hi]
      exact tail_mem P R (arcP_mem P R _)
    · rw [P.head_last i hi]
      exact source_mem P R
  · by_cases hi : i.1 + 1 < R.length
    · rw [R.head_before_last i hi]
      exact tail_mem P R (arcR_mem P R _)
    · rw [R.head_last i hi]
      exact sink_mem P R

theorem endpoint_rows_mem {e : E} (he : e ∈ entities P R) :
    tailRow (D.tail e) ∈ rows P R ∧ headRow (D.head e) ∈ rows P R := by
  constructor
  · cases ht : D.tail e with
    | inl b => exact source_mem P R
    | inr v => simpa [ht, tailRow] using tail_mem P R he
  · cases hh : D.head e with
    | inl b => exact sink_mem P R
    | inr v => simpa [hh, headRow] using head_mem P R he

omit [DecidableEq V] in
theorem tail_injOn (hdis : Disjoint P.vertices R.vertices) :
    Set.InjOn D.tail (entities P R : Set E) := by
  intro e he f hf h
  rcases (mem_entities P R e).mp he with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases (mem_entities P R f).mp hf with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact congrArg P.arcs (P.tail_injective h)
  · exact False.elim (P.tail_disjoint R hdis i j h)
  · exact False.elim (P.tail_disjoint R hdis j i h.symm)
  · exact congrArg R.arcs (R.tail_injective h)

theorem card_eq (hdis : Disjoint P.vertices R.vertices) :
    (entities P R).card = (rows P R).card :=
  (Finset.card_image_iff.mpr (tail_injOn P R hdis)).symm

theorem mixed : ∀ r ∈ rows P R,
    (∃ e ∈ entities P R, matrix D r e < 0) ∧
      ∃ e ∈ entities P R, 0 < matrix D r e := by
  intro r hr
  cases r with
  | inl b =>
    cases b
    · exact ⟨⟨P.arcs ⟨0, P.positive⟩, arcP_mem P R _,
        (terminal_signs D _).1.1.mpr P.start⟩,
        ⟨R.arcs ⟨0, R.positive⟩, arcR_mem P R _,
        (terminal_signs D _).1.2.mpr R.start⟩⟩
    · exact ⟨⟨P.arcs ⟨P.length - 1, by have := P.positive; omega⟩, arcP_mem P R _,
        (terminal_signs D _).2.1.mpr P.finish⟩,
        ⟨R.arcs ⟨R.length - 1, by have := R.positive; omega⟩, arcR_mem P R _,
        (terminal_signs D _).2.2.mpr R.finish⟩⟩
  | inr v =>
    obtain ⟨e, he, hv⟩ := Finset.mem_image.mp hr
    refine ⟨⟨e, he, (local_signs D e v).1.1.mpr hv⟩, ?_⟩
    rcases (mem_entities P R e).mp he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨j, hj⟩ := P.tail_internal_predecessor i v hv
      exact ⟨P.arcs j, arcP_mem P R j, (local_signs D _ v).1.2.mpr hj⟩
    · obtain ⟨j, hj⟩ := R.tail_internal_predecessor i v hv
      exact ⟨R.arcs j, arcR_mem P R j, (local_signs D _ v).1.2.mpr hj⟩

end UnconstrainedPACDetection.DirectedLinkageSource.PathUnion
