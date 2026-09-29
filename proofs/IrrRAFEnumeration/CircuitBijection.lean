module

public import proofs.IrrRAFEnumeration.CircuitClosure
public import proofs.IrrRAFEnumeration.Irreducibility

@[expose] public section

namespace IrrRAFEnumeration.CircuitSource

open RAF

def canonical {n q : Nat} (T : Finset (Fin n)) : Finset (Reaction n q) :=
  T.image Sum.inl ∪ Finset.univ.image Sum.inr

@[simp] theorem inl_mem_canonical {n q : Nat} (T : Finset (Fin n)) (i : Fin n) :
    (Sum.inl i : Reaction n q) ∈ canonical T ↔ i ∈ T := by
  simp [canonical]

@[simp] theorem inr_mem_canonical {n q : Nat} (T : Finset (Fin n))
    (j : Fin (q + 1)) : (Sum.inr j : Reaction n q) ∈ canonical T := by
  simp [canonical]

def selectedInputs {n q : Nat} (S : Finset (Reaction n q)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Sum.inl i ∈ S)

theorem eq_canonical_of_all_aux {n q : Nat} (S : Finset (Reaction n q))
    (haux : ∀ j, Sum.inr j ∈ S) : S = canonical (selectedInputs S) := by
  ext r
  cases r with
  | inl i => simp [selectedInputs]
  | inr j => simp [haux j]

@[simp] theorem canonical_subset_iff {n q : Nat} (T U : Finset (Fin n)) :
    (canonical T : Finset (Reaction n q)) ⊆ canonical U ↔ T ⊆ U := by
  constructor
  · intro h i hi
    exact (inl_mem_canonical U i).mp (h ((inl_mem_canonical T i).mpr hi))
  · intro h r hr
    cases r with
    | inl i => exact (inl_mem_canonical U i).mpr (h ((inl_mem_canonical T i).mp hr))
    | inr j => exact inr_mem_canonical U j

theorem canonical_injective {n q : Nat} :
    Function.Injective (canonical : Finset (Fin n) → Finset (Reaction n q)) := by
  intro T U h
  apply Finset.Subset.antisymm
  · exact (canonical_subset_iff T U).mp (by rw [h])
  · exact (canonical_subset_iff U T).mp (by rw [h])

/-- The accepted input sets are defined by literal reset-free food closure;
the circuit/SAT compiler must identify this predicate with its own evaluation. -/
def Accepts {n w q : Nat} (D : Rules n w q) (T : Finset (Fin n)) : Prop :=
  ∃ k, Molecule.wire D.output ∈ closureAt (crs D) ((canonical T).erase reset) k

theorem canonical_isRAF_iff {n w q : Nat} (D : Rules n w q)
    (T : Finset (Fin n)) : IsRAF (crs D) catalysis (canonical T) ↔ Accepts D T := by
  rw [isRAF_iff_all_aux_and_output]
  exact and_iff_right (fun j => inr_mem_canonical T j)

/-- Whole-family, rather than merely existence-preserving, source normal form. -/
theorem isRAF_iff_exists_canonical {n w q : Nat} (D : Rules n w q)
    (S : Finset (Reaction n q)) :
    IsRAF (crs D) catalysis S ↔ ∃ T, Accepts D T ∧ S = canonical T := by
  constructor
  · intro hS
    have heq := eq_canonical_of_all_aux S (raf_contains_all_aux D hS)
    refine ⟨selectedInputs S, ?_, heq⟩
    apply (canonical_isRAF_iff D _).mp
    rw [← heq]
    exact hS
  · rintro ⟨T, hT, rfl⟩
    exact (canonical_isRAF_iff D T).mpr hT

/-- Exact minimal-input/irrRAF correspondence. No enumeration complexity
conclusion is asserted until Accepts is docked to an explicit SAT source. -/
theorem canonical_irreducible_iff {n w q : Nat} (D : Rules n w q)
    (T : Finset (Fin n)) :
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF (crs D) catalysis (canonical T) ↔
      Minimal (Accepts D) T := by
  constructor
  · intro h
    refine ⟨(canonical_isRAF_iff D T).mp h.1, ?_⟩
    intro U hU hUT
    exact (canonical_subset_iff T U).mp
      (h.2 (canonical U) ((canonical_isRAF_iff D U).mpr hU)
        ((canonical_subset_iff U T).mpr hUT))
  · intro h
    refine ⟨(canonical_isRAF_iff D T).mpr h.1, ?_⟩
    intro S hS hST
    obtain ⟨U, hU, rfl⟩ := (isRAF_iff_exists_canonical D S).mp hS
    exact (canonical_subset_iff T U).mpr
      (h.2 hU ((canonical_subset_iff U T).mp hST))

end IrrRAFEnumeration.CircuitSource
