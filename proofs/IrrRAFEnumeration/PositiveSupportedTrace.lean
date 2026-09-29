module

public import proofs.IrrRAFEnumeration.PositiveRAFTrace

@[expose] public section

namespace IrrRAFEnumeration.PositiveSupportedTrace
open RAF PositiveRAFTrace

variable {M R : Type*} [DecidableEq M] [DecidableEq R] [Fintype M]

abbrev Fires (M R : Type*) [Fintype M] := Fin (Fintype.card M) → Finset R

/-- One-way support clauses: no equality with the whole closure is required.
The intended caller is a completion-to-SAT compiler using row and firing bits. -/
def SupportCheck (Q : CRS M R) (S : Finset R) (D : Rows M) (F : Fires M R) : Prop :=
  D ⟨0, by omega⟩ ⊆ Q.food ∧ ∀ i : Fin (Fintype.card M),
    F i ⊆ S ∧ (∀ r ∈ F i, Q.inputs r ⊆ D ⟨i.val, by omega⟩) ∧
    D ⟨i.val+1, by omega⟩ ⊆ D ⟨i.val, by omega⟩ ∪ (F i).biUnion Q.outputs

omit [DecidableEq R] in
theorem support_rows_sound (Q : CRS M R) (S : Finset R)
    (D : Rows M) (F : Fires M R) (h : SupportCheck Q S D F)
    (i : Fin (Fintype.card M+1)) : D i ⊆ closureAt Q S i.val := by
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero => exact h.1
  | succ k ih =>
    have hk' : k < Fintype.card M := by omega
    have hp := ih (by omega)
    obtain ⟨hFS,hinputs,hnext⟩ := h.2 ⟨k,hk'⟩
    intro x hx
    rcases Finset.mem_union.mp (hnext hx) with hx | hx
    · exact Finset.mem_union_left _ (hp hx)
    · obtain ⟨r,hr,hxr⟩ := Finset.mem_biUnion.mp hx
      have hen : Enabled Q (closureAt Q S k) r := (hinputs r hr).trans hp
      simp only [closureAt,closureStep,Finset.mem_union,Finset.mem_biUnion]
      exact Or.inr ⟨r,hFS hr,by simpa only [ite_eq_left hen] using hxr⟩

omit [DecidableEq R] in
theorem canonical_support (Q : CRS M R) (S : Finset R) :
    SupportCheck Q S (fun i => closureAt Q S i.val)
      (fun i => S.filter (fun r => Enabled Q (closureAt Q S i.val) r)) := by
  refine ⟨Finset.Subset.rfl,?_⟩
  intro i
  refine ⟨Finset.filter_subset _ _,?_,?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x hx
    simp only [closureAt,closureStep,Finset.mem_union,Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r,hr,hxr⟩
    · exact Finset.mem_union_left _ hx
    · by_cases he : Enabled Q (closureAt Q S i.val) r
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨r,Finset.mem_filter.mpr ⟨hr,he⟩,by simpa only [ite_eq_left he] using hxr⟩
      · simp only [ite_eq_right he,Finset.notMem_empty] at hxr

/-- Sound and complete certificates using only implication constraints. -/
theorem isRAF_iff_supported (Q : CRS M R) (C : Catalysis M R) (S : Finset R) :
    IsRAF Q C S ↔ ∃ (D : Rows M) (F : Fires M R),
      SupportCheck Q S D F ∧ EndCheck Q C S (D ⟨Fintype.card M, by omega⟩) := by
  constructor
  · intro h
    exact ⟨fun i => closureAt Q S i.val,_,canonical_support Q S,
      (isRAF_iff_bounded Q C S).mp h⟩
  · rintro ⟨D,F,h,hend⟩
    apply (isRAF_iff_bounded Q C S).mpr
    have hs := support_rows_sound Q S D F h ⟨Fintype.card M,by omega⟩
    refine ⟨hend.1,?_⟩
    intro r hr
    obtain ⟨hi,x,hx,hc⟩ := hend.2 r hr
    exact ⟨hi.trans hs,x,hs hx,hc⟩

theorem available_iff_supported (Q : CRS M R) (C : Catalysis M R)
    (G : Finset (Finset R)) (U : Finset R) :
    PositiveCompletion.Available (IsRAF Q C) G U ↔
      ∃ (S : Finset R) (D : Rows M) (F : Fires M R),
        S ⊆ U ∧ SupportCheck Q S D F ∧
        EndCheck Q C S (D ⟨Fintype.card M,by omega⟩) ∧ ∀ I ∈ G, ¬ I ⊆ S := by
  constructor
  · rintro ⟨S,hSU,hS,hG⟩
    obtain ⟨D,F,hs,he⟩ := (isRAF_iff_supported Q C S).mp hS
    exact ⟨S,D,F,hSU,hs,he,hG⟩
  · rintro ⟨S,D,F,hSU,hs,he,hG⟩
    exact ⟨S,hSU,(isRAF_iff_supported Q C S).mpr ⟨D,F,hs,he⟩,hG⟩

end IrrRAFEnumeration.PositiveSupportedTrace
