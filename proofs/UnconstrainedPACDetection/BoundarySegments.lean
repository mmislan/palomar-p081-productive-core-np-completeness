module

public import proofs.UnconstrainedPACDetection.BoundaryFirstReturn

@[expose] public section

namespace UnconstrainedPACDetection.BoundaryFirstReturn

variable {X : Type*} [Fintype X] (p : Equiv.Perm X) (S : Set X)

def segment (a : S) : Set X :=
  {x | ∃ i : Fin (length p S a), (p : X → X)^[i.1] a.1 = x}

theorem start_mem_segment (a : S) : a.1 ∈ segment p S a :=
  ⟨⟨0, (length_spec p S a).1⟩, rfl⟩

theorem segments_disjoint (a b : S) (hab : a ≠ b) :
    Disjoint (segment p S a) (segment p S b) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, hi⟩ ⟨j, hj⟩
  exact prefixes_disjoint p S a b hab i.2 j.2 (hi.trans hj.symm)

/-- Crossing an edge whose head is internal preserves membership of each
boundary segment. Thus unvisited internal cycles cannot leak into a path. -/
theorem segment_step_iff (a : S) (x : X) (hx : p x ∉ S) :
    p x ∈ segment p S a ↔ x ∈ segment p S a := by
  constructor
  · rintro ⟨i, hi⟩
    have hiz : i.1 ≠ 0 := by
      intro hz
      have he : a.1 = p x := by simpa [hz] using hi
      exact hx (he ▸ a.2)
    refine ⟨⟨i.1 - 1, by omega⟩, ?_⟩
    apply p.injective
    rw [← Function.iterate_succ_apply' (f := (p : X → X)) (i.1 - 1) a.1]
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ i.1)] using hi
  · rintro ⟨i, hi⟩
    have hlt : i.1 + 1 < length p S a := by
      by_contra h
      have he : i.1 + 1 = length p S a := by omega
      have hp : p x = (p : X → X)^[length p S a] a.1 := by
        rw [← he, Function.iterate_succ_apply', hi]
      exact hx (hp.symm ▸ (length_spec p S a).2)
    refine ⟨⟨i.1 + 1, hlt⟩, ?_⟩
    rw [Function.iterate_succ_apply', hi]

/-- The unique predecessor of a return destination is the last prefix point. -/
theorem predecessor_mem_segment (a : S) (x : X)
    (hx : p x = (p : X → X)^[length p S a] a.1) :
    x ∈ segment p S a := by
  have hn := (length_spec p S a).1
  refine ⟨⟨length p S a - 1, by omega⟩, ?_⟩
  apply p.injective
  rw [← Function.iterate_succ_apply' (f := (p : X → X)) (length p S a - 1) a.1]
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ length p S a)] using hx.symm

end UnconstrainedPACDetection.BoundaryFirstReturn
