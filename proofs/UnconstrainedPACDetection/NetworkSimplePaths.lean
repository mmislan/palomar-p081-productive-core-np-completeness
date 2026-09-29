module

public import proofs.UnconstrainedPACDetection.ArcPathIncidences
public import proofs.UnconstrainedPACDetection.DirectedPathNormalization

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

def adjacency {V E : Type*} (D : Network V E) (u v : PhysicalVertex V) : Prop :=
  ∃ e, tailVertex (D.tail e) = u ∧ headVertex (D.head e) = v

namespace ArcPath

variable {V E : Type*} {D : Network V E} {s t : Bool}

def vertexSequence (P : ArcPath D s t) : Fin (P.length + 1) → PhysicalVertex V :=
  Fin.lastCases (PhysicalVertex.sink t) (fun i => tailVertex (D.tail (P.arcs i)))

theorem vertexSequence_castSucc (P : ArcPath D s t) (i : Fin P.length) :
    P.vertexSequence i.castSucc = tailVertex (D.tail (P.arcs i)) := by simp [vertexSequence]

theorem vertexSequence_last (P : ArcPath D s t) :
    P.vertexSequence (Fin.last P.length) = PhysicalVertex.sink t := by simp [vertexSequence]

theorem vertexSequence_succ (P : ArcPath D s t) (i : Fin P.length) :
    P.vertexSequence i.succ = headVertex (D.head (P.arcs i)) := by
  by_cases hi : i.1 + 1 < P.length
  · have he : i.succ = (⟨i.1 + 1, hi⟩ : Fin P.length).castSucc := Fin.ext rfl
    rw [he, vertexSequence_castSucc]
    exact (P.physical_consecutive i.1 hi).symm
  · have he : i.succ = Fin.last P.length := Fin.ext (by change i.1 + 1 = P.length; omega)
    rw [he, vertexSequence_last, P.head_last i hi]
    rfl

theorem vertexSequence_injective (P : ArcPath D s t) : Function.Injective P.vertexSequence := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro h
      rw [vertexSequence_last, vertexSequence_castSucc] at h
      exact False.elim (tailVertex_ne_sink _ _ h.symm)
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h
      rw [vertexSequence_last, vertexSequence_castSucc] at h
      exact False.elim (tailVertex_ne_sink _ _ h)
    · intro h
      rw [vertexSequence_castSucc, vertexSequence_castSucc] at h
      exact congrArg Fin.castSucc (P.tail_injective (tailVertex_injective h))

@[reducible] def toSimplePath (P : ArcPath D s t) :
    DirectedPathNormalization.SimplePath (adjacency D) (.source s) (.sink t) where
  length := P.length
  positive := P.positive
  vertex := P.vertexSequence
  injective := P.vertexSequence_injective
  start := by
    change P.vertexSequence (⟨0, P.positive⟩ : Fin P.length).castSucc = _
    rw [vertexSequence_castSucc, P.start]
    rfl
  finish := P.vertexSequence_last
  edge i := by
    rw [vertexSequence_castSucc, vertexSequence_succ]
    exact ⟨P.arcs i, rfl, rfl⟩

theorem toSimplePath_vertices (P : ArcPath D s t) : P.toSimplePath.vertices = P.vertices := by
  ext x
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hi
      simp only [toSimplePath, vertexSequence, Fin.lastCases_last] at hi
      exact Or.inr hi.symm
    · intro hi
      change P.vertexSequence i.castSucc = x at hi
      rw [vertexSequence_castSucc] at hi
      exact Or.inl ⟨i, hi⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, (vertexSequence_castSucc P i).trans hi⟩
    · exact ⟨Fin.last P.length, (vertexSequence_last P).trans hi.symm⟩

end ArcPath
end UnconstrainedPACDetection.DirectedLinkageSource
