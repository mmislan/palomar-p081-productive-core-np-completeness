module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic

@[expose] public section

namespace UnconstrainedPACDetection.DegreeTwoSaturation

/-- In a square incidence relation, row degree at least two and column degree
at most two force equality at every vertex. No rank hypothesis is needed. -/
theorem all_degrees_two {R C : Type*} [Fintype R] [Fintype C]
    (inc : R → C → Prop) [DecidableRel inc]
    (hcard : Fintype.card R = Fintype.card C)
    (hrows : ∀ r, 2 ≤ (Finset.univ.filter (inc r)).card)
    (hcols : ∀ c, (Finset.univ.filter (fun r => inc r c)).card ≤ 2) :
    (∀ r, (Finset.univ.filter (inc r)).card = 2) ∧
      (∀ c, (Finset.univ.filter (fun r => inc r c)).card = 2) := by
  have hdouble : (∑ r, (Finset.univ.filter (inc r)).card) =
      ∑ c, (Finset.univ.filter (fun r => inc r c)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow inc
  have hlo : (∑ _r : R, (2 : ℕ)) ≤ ∑ r, (Finset.univ.filter (inc r)).card :=
    Finset.sum_le_sum (fun r _ => hrows r)
  have hhi : (∑ c, (Finset.univ.filter (fun r => inc r c)).card) ≤
      ∑ _c : C, (2 : ℕ) := Finset.sum_le_sum (fun c _ => hcols c)
  have hconst : (∑ _r : R, (2 : ℕ)) = ∑ _c : C, (2 : ℕ) := by simp [hcard]
  have hrEq : (∑ _r : R, (2 : ℕ)) = ∑ r, (Finset.univ.filter (inc r)).card := by omega
  have hcEq : (∑ c, (Finset.univ.filter (fun r => inc r c)).card) =
      ∑ _c : C, (2 : ℕ) := by omega
  constructor
  · intro r
    exact ((Finset.sum_eq_sum_iff_of_le (fun r _ => hrows r)).mp hrEq r (Finset.mem_univ r)).symm
  · intro c
    exact (Finset.sum_eq_sum_iff_of_le (fun c _ => hcols c)).mp hcEq c (Finset.mem_univ c)

/-- The lower degree bound comes from the actual mixed-sign matrix condition. -/
theorem mixed_square_degrees_two {R C : Type*} [Fintype R] [Fintype C]
    (A : R → C → ℝ) (hcard : Fintype.card R = Fintype.card C)
    (hmixed : ∀ r, (∃ c, A r c < 0) ∧ ∃ c, 0 < A r c)
    (hcols : ∀ c, (Finset.univ.filter (fun r => A r c ≠ 0)).card ≤ 2) :
    (∀ r, (Finset.univ.filter (fun c => A r c ≠ 0)).card = 2) ∧
      (∀ c, (Finset.univ.filter (fun r => A r c ≠ 0)).card = 2) := by
  classical
  apply all_degrees_two (fun r c => A r c ≠ 0) hcard _ hcols
  intro r
  obtain ⟨⟨c, hc⟩, d, hd⟩ := hmixed r
  have hcd : c ≠ d := by
    intro h
    subst d
    linarith
  have hsub : ({c, d} : Finset C) ⊆ Finset.univ.filter (fun e => A r e ≠ 0) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_lt hc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_gt hd⟩
  simpa [hcd] using Finset.card_le_card hsub

/-- Once two incidences are retained, the global degree bound excludes an
unselected incidence. This is the projection-fidelity step. -/
theorem no_incidence_outside {R : Type*} [Fintype R] [DecidableEq R]
    (s : Finset R) (inc : R → Prop) [DecidablePred inc]
    (hglobal : (Finset.univ.filter inc).card ≤ 2)
    (hlocal : (s.filter inc).card = 2) : ∀ r, inc r → r ∈ s := by
  have hsub : s.filter inc ⊆ Finset.univ.filter inc :=
    Finset.filter_subset_filter _ (Finset.subset_univ s)
  have heq : s.filter inc = Finset.univ.filter inc :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro r hr
  have hm : r ∈ s.filter inc := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
  exact (Finset.mem_filter.mp hm).1

end UnconstrainedPACDetection.DegreeTwoSaturation
