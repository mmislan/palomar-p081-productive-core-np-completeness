module

public import proofs.MinRAFApprox.Irreducible

@[expose] public section

namespace IrrRAFEnumeration

open RAF

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- The monotone predicate that a reaction set contains at least one RAF. -/
def HasRAFWithin (Q : CRS M R) (C : Catalysis M R) (S : Finset R) : Prop :=
  ∃ A : Finset R, IsRAF Q C A ∧ A ⊆ S

omit [DecidableEq R] in
theorem hasRAFWithin_mono (Q : CRS M R) (C : Catalysis M R)
    {S T : Finset R} (hST : S ⊆ T) :
    HasRAFWithin Q C S → HasRAFWithin Q C T := by
  rintro ⟨A, hA, hAS⟩
  exact ⟨A, hA, hAS.trans hST⟩

/-- Irreducibility can be certified by checking every one-reaction deletion.
This is the finite logical core of the polynomial verifier: the semantic
`HasRAFWithin` test can later be implemented by maxRAF. -/
theorem irreducibleRAF_iff_oneDeletion
    (Q : CRS M R) (C : Catalysis M R) (A : Finset R) :
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF Q C A ↔
      IsRAF Q C A ∧
        ∀ r ∈ A, ¬ HasRAFWithin Q C (A.erase r) := by
  constructor
  · intro hirr
    refine ⟨hirr.1, ?_⟩
    intro r hrA hwithin
    obtain ⟨B, hBraf, hBerase⟩ := hwithin
    have hAB : A ⊆ B :=
      hirr.2 B hBraf (hBerase.trans (A.erase_subset r))
    have hrB : r ∈ B := hAB hrA
    have : r ∈ A.erase r := hBerase hrB
    simp at this
  · rintro ⟨hAraf, hdeletion⟩
    refine ⟨hAraf, ?_⟩
    intro B hBraf hBA
    by_contra hAB
    rw [Finset.not_subset] at hAB
    obtain ⟨r, hrA, hrB⟩ := hAB
    have hBerase : B ⊆ A.erase r := by
      intro x hxB
      exact Finset.mem_erase.mpr ⟨by
        intro hxr
        apply hrB
        simpa [hxr] using hxB, hBA hxB⟩
    exact hdeletion r hrA ⟨B, hBraf, hBerase⟩

/-- An irrRAF is exactly an inclusion-minimal true set of the monotone
predicate `HasRAFWithin`. -/
theorem irreducibleRAF_iff_minimal_hasRAFWithin
    (Q : CRS M R) (C : Catalysis M R) (A : Finset R) :
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF Q C A ↔
      Minimal (HasRAFWithin Q C) A := by
  constructor
  · intro hirr
    refine ⟨⟨A, hirr.1, Finset.Subset.rfl⟩, ?_⟩
    intro B hBwithin hBA
    obtain ⟨I, hIraf, hIB⟩ := hBwithin
    exact (hirr.2 I hIraf (hIB.trans hBA)).trans hIB
  · intro hmin
    obtain ⟨I, hIraf, hIA⟩ := hmin.1
    have hAI : A ⊆ I := hmin.2 ⟨I, hIraf, Finset.Subset.rfl⟩ hIA
    have hEq : I = A := Finset.Subset.antisymm hIA hAI
    subst I
    refine ⟨hIraf, ?_⟩
    intro B hBraf hBA
    exact hmin.2 ⟨B, hBraf, Finset.Subset.rfl⟩ hBA

end IrrRAFEnumeration
