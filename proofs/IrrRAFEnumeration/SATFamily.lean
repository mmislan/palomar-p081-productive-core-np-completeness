module

public import proofs.IrrRAFEnumeration.SATReduction
public import proofs.IrrRAFEnumeration.RAFCompletion

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open RAF SATCompletion CircuitSource

theorem sourceSet_card {n m : Nat} (T : Finset (Choice n)) :
    (sourceSet (m := m) T).card = Fintype.card (Step n m) + 1 + T.card := by
  have hdis : Disjoint
      ((encodeInputs T).image (Sum.inl : Fin (Fintype.card (Choice n)) →
        Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))))
      (Finset.univ.image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro r hr hl
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hl
    have heq := hi.trans hj.symm
    cases heq
  unfold sourceSet canonical
  rw [Finset.card_union_of_disjoint hdis]
  rw [Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]
  rw [encodeInputs, Finset.card_image_of_injective _ (inputCode n).injective]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

def baseline (n m : Nat) :=
  (Finset.univ : Finset (Fin n)).image (fun i => sourceSet (m := m) (pair i))

theorem pair_injective {n : Nat} : Function.Injective (pair : Fin n → Finset (Choice n)) := by
  intro i j h
  have hi : (i,false) ∈ pair j := by rw [← h]; simp [pair]
  simpa [pair] using hi

theorem baseline_card (n m : Nat) : (baseline n m).card = n := by
  unfold baseline
  calc
    _ = (Finset.univ : Finset (Fin n)).card :=
      Finset.card_image_of_injective _ (fun _ _ h => pair_injective (sourceSet_injective h))
    _ = n := by simp

theorem baseline_member_card {n m : Nat} {S : Finset
    (Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))}
    (hS : S ∈ baseline n m) : S.card = Fintype.card (Step n m) + 3 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
  rw [sourceSet_card]
  simp [pair, Nat.add_assoc]

theorem baseline_subset_irrRAFFamily {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) :
    baseline n m ⊆ irrRAFFamily (crs (rules Φ)) catalysis := by
  intro S hS
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
  rw [mem_irrRAFFamily, sourceSet_irreducible_iff]
  exact pair_minimal hn (family Φ) i

theorem irrRAFFamily_eq_baseline_iff_unsat {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) :
    irrRAFFamily (crs (rules Φ)) catalysis = baseline n m ↔
      ¬ ∃ T, ¬ conflict T ∧ covers T ∧ hits (family Φ) T := by
  rw [← literal_baseline_complete_iff_unsat hn Φ, Finset.ext_iff]
  simp [baseline, eq_comm]

/-- The complete baseline's total reaction-list length is polynomial in the
constructor parameters and is known before solving the SAT instance. -/
theorem baseline_output_incidence (n m : Nat) :
    ∑ S ∈ baseline n m, S.card = n * (Fintype.card (Step n m) + 3) := by
  calc
    ∑ S ∈ baseline n m, S.card =
        ∑ _S ∈ baseline n m, (Fintype.card (Step n m) + 3) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact baseline_member_card hS
    _ = n * (Fintype.card (Step n m) + 3) := by simp [baseline_card]

end IrrRAFEnumeration.SATSource
