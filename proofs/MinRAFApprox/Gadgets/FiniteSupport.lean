module

public import proofs.MinRAFApprox.Gadgets.SetCoverBijection

@[expose] public section

namespace MinRAFApprox.SetCoverSource

open RAF MinRAFApprox.Reaction

variable {m n M : Nat}

/-- A genuinely finite carrier for every molecule that can occur in the
amplified source: food, one gate product per universe element, and one product
per block coordinate. -/
abbrev ActiveMolecule (m n M : Nat) :=
  Unit ⊕ (Fin m ⊕ (Fin n × Fin M))

/-- Embed the finite active carrier into the ambient molecule syntax used by
the reduction. -/
def embedActive : ActiveMolecule m n M → MinRAFApprox.Molecule n M
  | Sum.inl _ => MinRAFApprox.Molecule.food
  | Sum.inr (Sum.inl i) => MinRAFApprox.Molecule.y i.val
  | Sum.inr (Sum.inr (j, k)) => MinRAFApprox.Molecule.z j k

theorem embedActive_injective :
    Function.Injective (embedActive (m := m) (n := n) (M := M)) := by
  intro a b hab
  rcases a with _ | (i | jk) <;> rcases b with _ | (i' | jk') <;>
    simp [embedActive] at hab ⊢
  · exact Fin.ext hab
  · exact Prod.ext hab.1 hab.2

/-- The finite set of all molecules mentioned by the source construction. -/
def activeMolecules (m n M : Nat) : Finset (MinRAFApprox.Molecule n M) :=
  Finset.univ.image (embedActive (m := m) (n := n) (M := M))

@[simp] theorem food_mem_activeMolecules :
    MinRAFApprox.Molecule.food ∈ activeMolecules m n M := by
  simp [activeMolecules, embedActive]

@[simp] theorem y_mem_activeMolecules (i : Fin m) :
    MinRAFApprox.Molecule.y i.val ∈ activeMolecules m n M := by
  apply Finset.mem_image.mpr
  exact ⟨Sum.inr (Sum.inl i), Finset.mem_univ _, rfl⟩

@[simp] theorem z_mem_activeMolecules (j : Fin n) (k : Fin M) :
    MinRAFApprox.Molecule.z j k ∈ activeMolecules m n M := by
  apply Finset.mem_image.mpr
  exact ⟨Sum.inr (Sum.inr (j, k)), Finset.mem_univ _, rfl⟩

/-- The active molecular carrier has exactly `1 + m + nM` elements. -/
theorem activeMolecules_card :
    (activeMolecules m n M).card = 1 + m + n * M := by
  classical
  rw [activeMolecules, Finset.card_image_of_injective _ embedActive_injective]
  simp [ActiveMolecule, Nat.add_assoc]

theorem food_subset_activeMolecules :
    (crs m n M).food ⊆ activeMolecules m n M := by
  simp [crs]

theorem outputs_subset_activeMolecules
    (r : MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)) :
    (crs m n M).outputs r ⊆ activeMolecules m n M := by
  cases r <;> simp [crs]

theorem inputs_subset_activeMolecules
    (hm : 0 < m)
    (r : MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)) :
    (crs m n M).inputs r ⊆ activeMolecules m n M := by
  cases r with
  | gate i =>
      by_cases hi : i.val = 0
      · simp [crs, hi]
      · have hpred : i.val - 1 < m := by omega
        have hy := y_mem_activeMolecules (m := m) (n := n) (M := M)
          (⟨i.val - 1, hpred⟩ : Fin m)
        intro x hx
        simp only [crs, hi, ite_false, Finset.mem_insert,
          Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact food_mem_activeMolecules
        · exact hy
  | block j k =>
      by_cases hk : k.val = 0
      · have hy := y_mem_activeMolecules (m := m) (n := n) (M := M)
          (lastFin m hm)
        intro x hx
        simp only [crs, hk, ite_true, Finset.mem_insert,
          Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact food_mem_activeMolecules
        · simpa [lastFin] using hy
      · intro x hx
        simp only [crs, hk, ite_false, Finset.mem_insert,
          Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact food_mem_activeMolecules
        · exact z_mem_activeMolecules j (predFin k)

/-- Every closure stage lies in the explicit finite active carrier.  This is
independent of the chosen reaction subset. -/
theorem closureAt_subset_activeMolecules
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M))) (stage : Nat) :
    closureAt (crs m n M) S stage ⊆ activeMolecules m n M := by
  induction stage with
  | zero => exact food_subset_activeMolecules
  | succ stage ih =>
      intro x hx
      rw [closureAt, closureStep] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ih hx
      · obtain ⟨r, _hrS, hxout⟩ := Finset.mem_biUnion.mp hx
        by_cases henabled : Enabled (crs m n M) (closureAt (crs m n M) S stage) r
        · simp only [henabled, ite_true] at hxout
          exact outputs_subset_activeMolecules r hxout
        · simp [henabled] at hxout

/-- Finite-support form of the RAF predicate.  It is logically equivalent to
the original definition, and explicitly certifies that every catalytic
witness belongs to the finite active carrier. -/
theorem isRAF_iff_finite_active_support
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n))
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M))) :
    IsRAF (crs m n M) (catalysis I) S ↔
      S.Nonempty ∧ FoodGenerated (crs m n M) S ∧
        ∀ r ∈ S, ∃ x ∈ activeMolecules m n M, ∃ stage,
          x ∈ closureAt (crs m n M) S stage ∧ catalysis I x r := by
  constructor
  · rintro ⟨hne, hfg, hcat⟩
    refine ⟨hne, hfg, ?_⟩
    intro r hr
    obtain ⟨x, stage, hx, hxr⟩ := hcat r hr
    exact ⟨x, closureAt_subset_activeMolecules S stage hx, stage, hx, hxr⟩
  · rintro ⟨hne, hfg, hcat⟩
    refine ⟨hne, hfg, ?_⟩
    intro r hr
    obtain ⟨x, _hxActive, stage, hx, hxr⟩ := hcat r hr
    exact ⟨x, stage, hx, hxr⟩

end MinRAFApprox.SetCoverSource
