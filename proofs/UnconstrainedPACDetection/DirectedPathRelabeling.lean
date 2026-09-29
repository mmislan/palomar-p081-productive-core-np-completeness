module

public import proofs.UnconstrainedPACDetection.DirectedPathNormalization

@[expose] public section

namespace UnconstrainedPACDetection.DirectedPathNormalization

def SimplePath.map {X Y : Type*} {A : X → X → Prop} {B : Y → Y → Prop}
    {s t : X} (P : SimplePath A s t) (f : X → Y) (hf : Function.Injective f)
    (hedge : ∀ x y, A x y → B (f x) (f y)) : SimplePath B (f s) (f t) where
  length := P.length
  positive := P.positive
  vertex i := f (P.vertex i)
  injective := hf.comp P.injective
  start := congrArg f P.start
  finish := congrArg f P.finish
  edge i := hedge _ _ (P.edge i)

theorem Linkage.map {X Y : Type*} {A : X → X → Prop} {B : Y → Y → Prop}
    {s1 s2 t1 t2 : X} (h : Linkage A s1 s2 t1 t2)
    (f : X → Y) (hf : Function.Injective f)
    (hedge : ∀ x y, A x y → B (f x) (f y)) :
    Linkage B (f s1) (f s2) (f t1) (f t2) := by
  obtain ⟨P, Q, hd⟩ := h
  refine ⟨P.map f hf hedge, Q.map f hf hedge, ?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨i, hi⟩ ⟨j, hj⟩
  have he : P.vertex i = Q.vertex j := hf (hi.trans hj.symm)
  exact Set.disjoint_left.mp hd (show P.vertex i ∈ P.vertices from ⟨i, rfl⟩)
    ⟨j, he.symm⟩

theorem linkage_pull_iff {X Y : Type*} (e : X ≃ Y) (A : Y → Y → Prop)
    (s1 s2 t1 t2 : X) :
    Linkage (fun x y => A (e x) (e y)) s1 s2 t1 t2 ↔
      Linkage A (e s1) (e s2) (e t1) (e t2) := by
  constructor
  · intro h
    exact h.map e e.injective (fun _ _ h => h)
  · intro h
    have hr := h.map e.symm e.symm.injective
      (B := fun x y => A (e x) (e y)) (fun x y h => by simpa using h)
    simpa only [Equiv.symm_apply_apply] using hr

end UnconstrainedPACDetection.DirectedPathNormalization
