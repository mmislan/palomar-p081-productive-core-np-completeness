module

public import proofs.UnconstrainedPACDetection.IntegerFlowChecker
public import proofs.UnconstrainedPACDetection.AdjugateFlowBits

@[expose] public section

namespace UnconstrainedPACDetection

open ScaledInverseCertificate
variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]

def ReversibleSource.sideBitBound (s : ReversibleSource Entity Reaction) : ℕ :=
  Finset.univ.sup fun r => Finset.univ.sup fun x =>
    max (s.left r x).size (s.right r x).size

omit [DecidableEq Entity] [DecidableEq Reaction] in
theorem netInt_le_sideBitBound (s : ReversibleSource Entity Reaction) (r : Reaction) (x : Entity) :
    |s.netInt r x| ≤ (2 : ℤ) ^ s.sideBitBound := by
  have hpair : max (s.left r x).size (s.right r x).size ≤ s.sideBitBound :=
    Finset.le_sup_of_le (Finset.mem_univ r)
      (Finset.le_sup_of_le (Finset.mem_univ x) le_rfl)
  have hl := Nat.size_le.mp ((le_max_left _ _).trans hpair)
  have hr := Nat.size_le.mp ((le_max_right _ _).trans hpair)
  have hl' : (s.left r x : ℤ) < (2 : ℤ) ^ s.sideBitBound := by exact_mod_cast hl
  have hr' : (s.right r x : ℤ) < (2 : ℤ) ^ s.sideBitBound := by exact_mod_cast hr
  unfold ReversibleSource.netInt
  exact abs_le.mpr ⟨by omega, by omega⟩

def ReversibleSource.checkBoundedFlow (s : ReversibleSource Entity Reaction)
    (X : Finset Entity) (w : Reaction → ℤ) : Bool :=
  s.checkIntegerFlow X w && decide (∀ r,
    (w r).natAbs.size ≤ flowBitBound (Fintype.card Reaction) s.sideBitBound)

theorem exists_pac_iff_checkBoundedFlow (s : ReversibleSource Entity Reaction) :
    (∃ c, s.PAC c) ↔ ∃ X w, s.checkBoundedFlow X w = true := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := (exists_pac_iff_exists_squareMinor s).1 hp
    obtain ⟨e⟩ : Nonempty (↥c.2 ≃ ↥c.1) := Fintype.card_eq.mp (by simpa using hc.2.2.2.1.symm)
    refine ⟨c.1, s.minorFlow c e, ?_⟩
    have hcheck := (checkIntegerFlow_iff s c.1 (s.minorFlow c e)).2 (minorFlow_checks s c e hc)
    have hq : Fintype.card ↥c.2 ≤ Fintype.card Reaction := by simpa using Finset.card_le_univ c.2
    have hbits : ∀ r, (s.minorFlow c e r).natAbs.size ≤
        flowBitBound (Fintype.card Reaction) s.sideBitBound := by
      intro r
      by_cases hr : r ∈ c.2
      · have hlocal := adjugateFlow_bits (s.certificateMatrix c e) s.sideBitBound
          (fun i j => netInt_le_sideBitBound s i.1 (e j).1) (⟨r, hr⟩ : ↥c.2)
        simpa [ReversibleSource.minorFlow, hr] using
          hlocal.trans (flowBitBound_mono hq s.sideBitBound)
      · simp [ReversibleSource.minorFlow, hr]
    simp [ReversibleSource.checkBoundedFlow, hcheck, hbits]
  · rintro ⟨X, w, hw⟩
    have hh : s.checkIntegerFlow X w = true ∧
        ∀ r, (w r).natAbs.size ≤ flowBitBound (Fintype.card Reaction) s.sideBitBound := by
      simpa [ReversibleSource.checkBoundedFlow] using hw
    have h := hh.1
    exact (exists_pac_iff_checkIntegerFlow s).2 ⟨X, w, h⟩

end UnconstrainedPACDetection
