module

public import proofs.UnconstrainedPACDetection.NetworkSimplePaths
public import proofs.UnconstrainedPACDetection.LinkagePACForward

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

theorem headVertex_injective {V : Type*} : Function.Injective (@headVertex V) := by
  intro x y h
  cases x <;> cases y <;> simp_all [headVertex]

theorem headVertex_ne_source {V : Type*} (x : Bool ⊕ V) (b : Bool) :
    headVertex x ≠ PhysicalVertex.source b := by cases x <;> simp [headVertex]

theorem head_tail_labels_equal {V : Type*} (x y : Bool ⊕ V)
    (h : headVertex x = tailVertex y) : x = y := by
  cases x <;> cases y <;> simp_all [headVertex, tailVertex]

namespace VertexPath

variable {V E : Type*} {D : Network V E} {s t : Bool}
variable (P : DirectedPathNormalization.SimplePath (adjacency D)
  (PhysicalVertex.source s) (PhysicalVertex.sink t))

noncomputable def arc (i : Fin P.length) : E := Classical.choose (P.edge i)

theorem arc_tail (i : Fin P.length) :
    tailVertex (D.tail (arc P i)) = P.vertex i.castSucc := (Classical.choose_spec (P.edge i)).1
theorem arc_head (i : Fin P.length) :
    headVertex (D.head (arc P i)) = P.vertex i.succ := (Classical.choose_spec (P.edge i)).2

noncomputable def toArcPath : ArcPath D s t := by
  refine ⟨P.length, P.positive, arc P, ?_, ?_, ?_, ?_, ?_⟩
  · apply tailVertex_injective
    exact (arc_tail P _).trans P.start
  · apply headVertex_injective
    have he : (⟨P.length - 1, by have := P.positive; omega⟩ : Fin P.length).succ =
        Fin.last P.length := Fin.ext (by change P.length - 1 + 1 = P.length; have := P.positive; omega)
    exact (arc_head P _).trans (congrArg P.vertex he |>.trans P.finish)
  · intro i hi
    apply head_tail_labels_equal
    exact (arc_head P ⟨i, by omega⟩).trans (arc_tail P ⟨i + 1, hi⟩).symm
  · intro i hi
    cases he : D.tail (arc P i) with
    | inr z => exact ⟨z, rfl⟩
    | inl b =>
      let j : Fin P.length := ⟨i.1 - 1, by omega⟩
      have hj : j.succ = i.castSucc := Fin.ext (by change i.1 - 1 + 1 = i.1; omega)
      have h := (arc_head P j).trans ((congrArg P.vertex hj).trans (arc_tail P i).symm)
      rw [he] at h
      exact False.elim (headVertex_ne_source _ _ h)
  · intro i j h
    have hv := (arc_tail P i).symm.trans ((congrArg tailVertex h).trans (arc_tail P j))
    have hi := congrArg (fun k : Fin (P.length + 1) => k.1) (P.injective hv)
    exact Fin.ext hi

theorem vertices_subset : (toArcPath P).vertices ⊆ P.vertices := by
  intro x hx
  rcases hx with ⟨i, hi⟩ | hi
  · exact ⟨i.castSucc, (arc_tail P i).symm.trans hi⟩
  · exact ⟨Fin.last P.length, P.finish.trans hi.symm⟩

end VertexPath

theorem arc_linkage_iff_simple {V E : Type*} (D : Network V E) :
    (∃ (P : ArcPath D false false) (R : ArcPath D true true),
      Disjoint P.vertices R.vertices) ↔
    DirectedPathNormalization.Linkage (adjacency D)
      (.source false) (.source true) (.sink false) (.sink true) := by
  constructor
  · rintro ⟨P, R, h⟩
    refine ⟨P.toSimplePath, R.toSimplePath, ?_⟩
    simpa only [ArcPath.toSimplePath_vertices] using h
  · rintro ⟨P, R, h⟩
    exact ⟨VertexPath.toArcPath P, VertexPath.toArcPath R,
      h.mono (VertexPath.vertices_subset P) (VertexPath.vertices_subset R)⟩

theorem pac_iff_simple_linkage {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (D : Network V E) :
    (∃ candidate, (source D).PAC candidate) ↔
      DirectedPathNormalization.Linkage (adjacency D)
        (.source false) (.source true) (.sink false) (.sink true) :=
  (pac_iff_linkage D).trans (arc_linkage_iff_simple D)

end UnconstrainedPACDetection.DirectedLinkageSource
