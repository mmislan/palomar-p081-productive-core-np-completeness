module

public import proofs.IrrRAFEnumeration.FiniteDuality

@[expose] public section

namespace IrrRAFEnumeration

open RAF

variable {M R : Type*} [Fintype R] [DecidableEq M] [DecidableEq R]

/-- The complete finite antichain of irreducible RAFs of a literal CRS. -/
noncomputable def irrRAFFamily (Q : CRS M R) (C : Catalysis M R) :
    Finset (Finset R) := by
  classical
  exact Finset.univ.powerset.filter
    (MinRAFApprox.SetCoverSource.IsIrreducibleRAF Q C)

@[simp] theorem mem_irrRAFFamily
    (Q : CRS M R) (C : Catalysis M R) (A : Finset R) :
    A ∈ irrRAFFamily Q C ↔
      MinRAFApprox.SetCoverSource.IsIrreducibleRAF Q C A := by
  classical
  simp [irrRAFFamily]

/-- Every RAF-containing set contains an irrRAF, and conversely. -/
theorem hasRAFWithin_iff_contains_irrRAF
    (Q : CRS M R) (C : Catalysis M R) (S : Finset R) :
    HasRAFWithin Q C S ↔ ContainsMember (irrRAFFamily Q C) S := by
  classical
  constructor
  · rintro ⟨A, hAraf, hAS⟩
    obtain ⟨I, hIA, hImin⟩ :=
      exists_minimal_subset (fun T => IsRAF Q C T) hAraf
    have hIirr : MinRAFApprox.SetCoverSource.IsIrreducibleRAF Q C I :=
      hImin
    exact ⟨I, (mem_irrRAFFamily Q C I).mpr hIirr, hIA.trans hAS⟩
  · rintro ⟨I, hIfamily, hIS⟩
    exact ⟨I, (mem_irrRAFFamily Q C I).mp hIfamily |>.1, hIS⟩

theorem irrRAFFamily_isClutter (Q : CRS M R) (C : Catalysis M R) :
    IsClutter (irrRAFFamily Q C) := by
  intro A hA B hB hAB
  have hAirr := (mem_irrRAFFamily Q C A).mp hA
  have hBirr := (mem_irrRAFFamily Q C B).mp hB
  exact hBirr.2 A hAirr.1 hAB

/-- irrRAFs and minimal RAF-destroying deletion sets are exact finite blocker
duals. -/
theorem irrRAF_blocker_involution (Q : CRS M R) (C : Catalysis M R) :
    blocker (blocker (irrRAFFamily Q C)) = irrRAFFamily Q C :=
  blocker_blocker _ (irrRAFFamily_isClutter Q C)

/-- Exact known-family completion theorem in literal RAF semantics.  A known
subfamily is complete iff deleting every minimal hitting set of that subfamily
leaves no RAF. -/
theorem knownIrrRAFs_complete_iff
    (Q : CRS M R) (C : Catalysis M R) (G : Finset (Finset R))
    (hG : G ⊆ irrRAFFamily Q C) :
    G = irrRAFFamily Q C ↔
      ∀ H, Minimal (Hits G) H →
        ¬ HasRAFWithin Q C (Finset.univ \ H) := by
  rw [knownFamily_complete_iff (irrRAFFamily Q C) G
    (irrRAFFamily_isClutter Q C) hG]
  simp only [hasRAFWithin_iff_contains_irrRAF]

end IrrRAFEnumeration
