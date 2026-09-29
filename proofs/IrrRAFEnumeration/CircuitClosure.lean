module

public import proofs.IrrRAFEnumeration.CircuitSource

@[expose] public section

namespace IrrRAFEnumeration.CircuitSource

open RAF RAF.Frankl

def reset {n q : Nat} : Reaction n q := Sum.inr (Fin.last q)

theorem reset_inputs {n w q : Nat} (D : Rules n w q) :
    (crs D).inputs (reset : Reaction n q) = {Molecule.wire D.output} := by
  simp [crs, reset]

theorem wire_mem_reset_outputs {n w q : Nat} (D : Rules n w q) (v : Fin w) :
    Molecule.wire v ∈ (crs D).outputs (reset : Reaction n q) := by
  simp [crs, reset]

/-- If the reset's prerequisite can be generated, the reset makes every
signal-rule input available. This uses no acyclicity assumption. -/
theorem foodGenerated_of_output_reached {n w q : Nat} (D : Rules n w q)
    {S : Finset (Reaction n q)} (hreset : reset ∈ S)
    (hout : ∃ k, Molecule.wire D.output ∈ closureAt (crs D) S k) :
    FoodGenerated (crs D) S := by
  obtain ⟨k, hk⟩ := hout
  have hen : Enabled (crs D) (closureAt (crs D) S k) reset := by
    rw [Enabled, reset_inputs]
    exact Finset.singleton_subset_iff.mpr hk
  have hw : ∀ v, Molecule.wire v ∈ closureAt (crs D) S (k + 1) := by
    intro v
    simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inr ⟨reset, hreset, by
      simpa [hen] using wire_mem_reset_outputs D v⟩
  intro r _
  cases r with
  | inl i => exact ⟨0, by simp [crs, closureAt]⟩
  | inr j =>
      refine ⟨k + 1, ?_⟩
      intro x hx
      by_cases hlt : j.val < q
      · simp only [crs, hlt, dite_true, Finset.mem_image] at hx
        obtain ⟨v, _, rfl⟩ := hx
        exact hw v
      · simp only [crs, hlt, dite_false, Finset.mem_singleton] at hx
        rw [hx]
        exact hw D.output

/-- First-enablement reasoning prevents the reset from manufacturing its own
prerequisite: every RAF derives the output even with the reset removed. -/
theorem raf_output_reached_without_reset {n w q : Nat} (D : Rules n w q)
    {S : Finset (Reaction n q)} (hS : IsRAF (crs D) catalysis S) :
    ∃ k, Molecule.wire D.output ∈ closureAt (crs D) (S.erase reset) k := by
  have hr : reset ∈ S := raf_contains_all_aux D hS (Fin.last q)
  have hex : ∃ k, Enabled (crs D) (closureAt (crs D) S k) reset := hS.2.1 _ hr
  let K := Nat.find hex
  have hnot : ∀ j < K, ¬ Enabled (crs D) (closureAt (crs D) S j) reset := by
    intro j hj
    exact Nat.find_min hex hj
  have heq := closureAt_erase_eq_of_not_enabled_before (crs D) S reset K hnot K le_rfl
  refine ⟨K, ?_⟩
  rw [heq]
  have hen := Nat.find_spec hex
  rw [Enabled, reset_inputs] at hen
  exact hen (by simp)

/-- Exact ordinary-RAF normal form for any finite rule system with the reset
and mandatory catalytic cycle. The RHS is reset-free signal reachability. -/
theorem isRAF_iff_all_aux_and_output {n w q : Nat} (D : Rules n w q)
    (S : Finset (Reaction n q)) :
    IsRAF (crs D) catalysis S ↔
      (∀ j : Fin (q + 1), Sum.inr j ∈ S) ∧
      ∃ k, Molecule.wire D.output ∈ closureAt (crs D) (S.erase reset) k := by
  constructor
  · intro hS
    exact ⟨raf_contains_all_aux D hS, raf_output_reached_without_reset D hS⟩
  · rintro ⟨haux, k, hk⟩
    have hr : reset ∈ S := haux (Fin.last q)
    have hfg : FoodGenerated (crs D) S := foodGenerated_of_output_reached D hr
      ⟨k, closureAt_mono_reactions (crs D) (Finset.erase_subset _ _) k hk⟩
    refine ⟨⟨reset, hr⟩, hfg, ?_⟩
    intro r _
    have hp : Molecule.marker (catalystIndex r) ∈
        (crs D).outputs (Sum.inr (catalystIndex r)) := by simp [crs]
    obtain ⟨j, hj⟩ := output_mem_some_closureAt_of_foodGenerated
      (crs D) hfg (haux (catalystIndex r)) hp
    exact ⟨_, j, hj, rfl⟩

end IrrRAFEnumeration.CircuitSource
