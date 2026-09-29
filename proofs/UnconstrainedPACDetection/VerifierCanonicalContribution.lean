module

public import proofs.UnconstrainedPACDetection.VerifierCanonicalCoordinates
public import proofs.UnconstrainedPACDetection.VerifierCoefficientIteration

@[expose] public section

/-! The actual coefficient machine instantiated at a common canonical coordinate. -/
namespace UnconstrainedPACDetection.VerifierCanonicalContribution
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierCanonicalCoordinates
open VerifierSignedContribution (newPos newNeg)

def flow (w : BinaryWitnessData.Witness) (r : ℕ) := w.flow.getD r 0
def sign (w : BinaryWitnessData.Witness) (r : ℕ) := decide (flow w r < 0)
def magnitude (w : BinaryWitnessData.Witness) (r : ℕ) := (flow w r).natAbs.bits
def product (s : BinarySourceData.DenseSource) (b : Bool) (r : Fin s.reactions) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) :=
  VerifierBinaryProduct.multiply (coefficient s b r x).bits (magnitude w r.val)

theorem canonical_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (b : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (pos neg : List Bool) (out₀ : Tape)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    s.encode = BinaryFields.encode (sourcePrefix s b r x) ++
      (BinaryFields.encodeField (coefficient s b r x).bits ++ sourceSuffix s b r x) ∧
    (VerifierCoefficientIteration.machine b).HoareTime
      (VerifierCoefficientIteration.pred [] (1+r.val) (wordTape w.encode) pos neg
        (BinaryFields.encodeField (coefficient s b r x).bits ++ sourceSuffix s b r x) out₀)
      (VerifierCoefficientIteration.pred [] (1+r.val) (wordTape w.encode)
        (newPos (xor b (sign w r.val)) (product s b r x w) pos)
        (newNeg (xor b (sign w r.val)) (product s b r x w) neg) (sourceSuffix s b r x) out₀)
      (2*VerifierContributionIteration.contributionBound (witnessPrefix w r.val)
        (coefficient s b r x).bits (magnitude w r.val) pos neg+
        5*(coefficient s b r x).bits.length+2*(magnitude w r.val).length+
        2*(product s b r x w).length+r.val+41) := by
  refine ⟨source_split s hs b r x,?_⟩
  have hr : r.val < w.flow.length := by rw [hw]; exact r.isLt
  have hi : (wordTape w.encode).HasBinarySuffix
      (BinaryFields.encode (witnessPrefix w r.val) ++
        (BinaryFields.encodeField (sign w r.val :: magnitude w r.val) ++ witnessSuffix w r.val)) := by
    unfold VerifierBufferedProduct.wordTape
    change ((Tape.init (w.encode.map Γ.ofBool)).move .right).HasBinarySuffix
      (BinaryFields.encode (witnessPrefix w r.val) ++
        (BinaryFields.encodeField (BinaryFields.writeInt (w.flow.getD r.val 0)) ++
          witnessSuffix w r.val))
    rw [← witness_split w r.val hr]
    exact (Tape.init_move_right_hasBinaryString w.encode).hasBinarySuffix
  have h := VerifierCoefficientIteration.coefficient_iteration_hoare b (witnessPrefix w r.val)
    (coefficient s b r x).bits (sign w r.val) (magnitude w r.val) pos neg
    (sourceSuffix s b r x) (witnessSuffix w r.val) (wordTape w.encode) out₀ hi
    ((Tape.StartInvariant.init_ofBool w.encode).move .right) rfl ho hoh
  have hk := witnessPrefix_length w r.val hr
  rw [hk] at h
  exact h.mono_bound (by dsimp [product]; omega)

theorem sign_magnitude (z : ℤ) : (if decide (z < 0) then (-1 : ℤ) else 1) * z.natAbs = z := by
  by_cases hz : z < 0
  · simp [hz,abs_of_neg hz]
  · simp [hz,abs_of_nonneg (le_of_not_gt hz)]

/-- The machine's updated total difference is precisely the selected canonical
coefficient multiplied by the signed flow of the same reaction. -/
theorem canonical_value (s : BinarySourceData.DenseSource) (b : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness) (pos neg : List Bool) :
    (BinaryFields.readNat (newPos (xor b (sign w r.val)) (product s b r x w) pos) : ℤ) -
      BinaryFields.readNat (newNeg (xor b (sign w r.val)) (product s b r x w) neg) =
    (BinaryFields.readNat pos : ℤ)-BinaryFields.readNat neg+
      (if b then (1 : ℤ) else -1)*coefficient s b r x*flow w r.val := by
  have h := VerifierSignedContribution.contribution_value b (sign w r.val)
    (coefficient s b r x).bits (magnitude w r.val) pos neg
  simp only [magnitude,BinaryFields.readNat_bits] at h
  change (BinaryFields.readNat (newPos (xor b (sign w r.val)) (product s b r x w) pos) : ℤ) -
    BinaryFields.readNat (newNeg (xor b (sign w r.val)) (product s b r x w) neg) = _ at h
  rw [h]
  have hz := sign_magnitude (flow w r.val)
  change (if sign w r.val then (-1 : ℤ) else 1) * (flow w r.val).natAbs = flow w r.val at hz
  calc
    _ = (BinaryFields.readNat pos : ℤ)-BinaryFields.readNat neg+
      (if b then (1 : ℤ) else -1)*coefficient s b r x*
        ((if sign w r.val then (-1 : ℤ) else 1)*(flow w r.val).natAbs) := by ring
    _ = _ := by rw [hz]

end UnconstrainedPACDetection.VerifierCanonicalContribution
