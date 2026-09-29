module

public import proofs.UnconstrainedPACDetection.LinkagePhysicalPaths

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource.ArcPath

variable {V E : Type*} {D : Network V E} {s t u v : Bool}

theorem tail_disjoint (P : ArcPath D s t) (R : ArcPath D u v)
    (h : Disjoint P.vertices R.vertices) (i : Fin P.length) (j : Fin R.length) :
    D.tail (P.arcs i) ≠ D.tail (R.arcs j) := by
  intro he
  apply Set.disjoint_left.mp h
    (show tailVertex (D.tail (P.arcs i)) ∈ P.vertices from Or.inl ⟨i, rfl⟩)
  exact Or.inl ⟨j, congrArg tailVertex he.symm⟩

theorem head_before_last (P : ArcPath D s t) (i : Fin P.length)
    (hi : i.1 + 1 < P.length) :
    D.head (P.arcs i) = D.tail (P.arcs ⟨i.1 + 1, hi⟩) := P.consecutive i.1 hi

theorem head_last (P : ArcPath D s t) (i : Fin P.length)
    (hi : ¬ i.1 + 1 < P.length) : D.head (P.arcs i) = Sum.inl t := by
  have he : i = ⟨P.length - 1, by have := P.positive; omega⟩ := by
    apply Fin.ext
    change i.1 = P.length - 1
    omega
  rw [he]
  exact P.finish

theorem tail_internal_predecessor (P : ArcPath D s t) (i : Fin P.length)
    (z : V) (hz : D.tail (P.arcs i) = Sum.inr z) :
    ∃ j : Fin P.length, D.head (P.arcs j) = Sum.inr z := by
  have hip : 0 < i.1 := by
    by_contra h
    have he : i = ⟨0, P.positive⟩ := Fin.ext (by change i.1 = 0; omega)
    have hh := P.start
    rw [← he, hz] at hh
    cases hh
  refine ⟨⟨i.1 - 1, by omega⟩, ?_⟩
  have hs : i.1 - 1 + 1 < P.length := by omega
  rw [P.consecutive (i.1 - 1) hs]
  have he : (⟨i.1 - 1 + 1, hs⟩ : Fin P.length) = i :=
    Fin.ext (by change i.1 - 1 + 1 = i.1; omega)
  rw [he]
  exact hz

/-- Transport an endpoint potential along the original arc sequence directly. -/
theorem transport (P : ArcPath D s t) (U W : Bool ⊕ V → ℝ)
    (hedge : ∀ i, W (D.head (P.arcs i)) = U (D.tail (P.arcs i)))
    (hinternal : ∀ z, U (Sum.inr z) = W (Sum.inr z)) :
    W (Sum.inl t) = U (Sum.inl s) ∧
      ∀ i, U (D.tail (P.arcs i)) = U (Sum.inl s) := by
  have ht : ∀ k (hk : k < P.length),
      U (D.tail (P.arcs ⟨k, hk⟩)) = U (Sum.inl s) := by
    intro k
    induction k with
    | zero => intro hk; rw [P.start]
    | succ k ih =>
      intro hk
      obtain ⟨z, hz⟩ := P.internal ⟨k + 1, hk⟩ (by change 0 < k + 1; omega)
      rw [hz, hinternal, ← hz, ← P.consecutive k hk, hedge]
      exact ih (by omega)
  constructor
  · rw [← P.finish, hedge]
    exact ht _ _
  · intro i
    exact ht i.1 i.2

end UnconstrainedPACDetection.DirectedLinkageSource.ArcPath
