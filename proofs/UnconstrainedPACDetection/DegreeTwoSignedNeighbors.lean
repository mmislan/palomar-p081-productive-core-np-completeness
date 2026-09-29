module

public import proofs.UnconstrainedPACDetection.DegreeTwoSaturation

@[expose] public section

namespace UnconstrainedPACDetection.DegreeTwoSignedNeighbors

theorem unique_signs {E : Type*} [Fintype E] (f : E → ℤ)
    (hdegree : (Finset.univ.filter (fun e => f e ≠ 0)).card ≤ 2)
    (hmixed : (∃ e, f e < 0) ∧ ∃ e, 0 < f e) :
    (∃! e, f e < 0) ∧ ∃! e, 0 < f e := by
  classical
  obtain ⟨⟨a, ha⟩, b, hb⟩ := hmixed
  have hab : a ≠ b := by intro h; subst b; omega
  have hsub : ({a, b} : Finset E) ⊆ Finset.univ.filter (fun e => f e ≠ 0) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_lt ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_gt hb⟩
  have heq : Finset.univ.filter (fun e => f e ≠ 0) = {a, b} :=
    (Finset.eq_of_subset_of_card_le hsub (by simpa [hab] using hdegree)).symm
  have hcases : ∀ e, f e ≠ 0 → e = a ∨ e = b := by
    intro e he
    have hm : e ∈ Finset.univ.filter (fun e => f e ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩
    rw [heq] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  constructor
  · refine ⟨a, ha, ?_⟩
    intro e he
    rcases hcases e (ne_of_lt he) with h | h
    · exact h
    · subst e; omega
  · refine ⟨b, hb, ?_⟩
    intro e he
    rcases hcases e (ne_of_gt he) with h | h
    · subst e; omega
    · exact h

end UnconstrainedPACDetection.DegreeTwoSignedNeighbors
