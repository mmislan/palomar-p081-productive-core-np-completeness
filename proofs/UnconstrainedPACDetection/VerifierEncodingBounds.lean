module

public import proofs.UnconstrainedPACDetection.VerifierRunningTotals

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEncodingBounds
open VerifierCanonicalCoordinates

theorem split_length (fs : List (List Bool)) (k : ℕ) :
    (BinaryFields.encode (fs.take k)).length+(BinaryFields.encode (fs.drop k)).length =
      (BinaryFields.encode fs).length := by
  have h := congrArg (fun xs => (BinaryFields.encode xs).length) (List.take_append_drop k fs)
  simpa only [BinaryFields.encode,List.flatMap_append,List.length_append] using h

theorem take_le (fs : List (List Bool)) (k : ℕ) :
    (BinaryFields.encode (fs.take k)).length ≤ (BinaryFields.encode fs).length := by
  have h := split_length fs k
  omega

theorem drop_le (fs : List (List Bool)) (k : ℕ) :
    (BinaryFields.encode (fs.drop k)).length ≤ (BinaryFields.encode fs).length := by
  have h := split_length fs k
  omega

theorem count_le (fs : List (List Bool)) : fs.length ≤ (BinaryFields.encode fs).length := by
  induction fs with
  | nil => simp [BinaryFields.encode]
  | cons f fs ih =>
    simp only [BinaryFields.encode,List.flatMap_cons,List.length_append,
      BinaryFields.encodeField_length,List.length_cons] at *
    omega

theorem coefficient_le (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (b : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) :
    (coefficient s b r x).bits.length ≤ s.encode.length := by
  have h := congrArg List.length (source_split s hs b r x)
  simp only [List.length_append,BinaryFields.encodeField_length] at h
  omega

theorem source_values_le (s : BinarySourceData.DenseSource) :
    (BinaryFields.encode (s.values.map Nat.bits)).length ≤ s.encode.length := by
  simp only [BinarySourceData.DenseSource.encode,BinaryFields.encode,List.flatMap_cons,
    List.length_append]
  omega

theorem skipped_le (s : BinarySourceData.DenseSource) (b : Bool)
    (r : Fin s.reactions) (x : Fin s.entities) :
    (BinaryFields.encode (VerifierStrideCoordinates.skipped s b r x)).length ≤ s.encode.length := by
  have h1 := take_le ((s.values.map Nat.bits).drop (valueIndex s b r x+1)) (s.entities-1)
  have h2 := drop_le (s.values.map Nat.bits) (valueIndex s b r x+1)
  have h3 := source_values_le s
  simpa only [VerifierStrideCoordinates.skipped,List.map_take,List.map_drop] using h1.trans (h2.trans h3)

theorem witness_bounds (w : BinaryWitnessData.Witness) (r : ℕ) (hr : r < w.flow.length) :
    (BinaryFields.encode (witnessPrefix w r)).length ≤ w.encode.length ∧
    (VerifierCanonicalContribution.magnitude w r).length ≤ w.encode.length := by
  have h := congrArg List.length (witness_split w r hr)
  simp only [List.length_append,BinaryFields.encodeField_length,BinaryFields.writeInt,
    List.length_cons] at h
  change (BinaryFields.encode (witnessPrefix w r)).length ≤ w.encode.length ∧
    (w.flow.getD r 0).natAbs.bits.length ≤ w.encode.length
  omega

theorem reaction_count (w : BinaryWitnessData.Witness) : w.flow.length ≤ w.encode.length := by
  have h := count_le (w.mask :: w.flow.map BinaryFields.writeInt)
  simp only [List.length_cons,List.length_map] at h
  exact (Nat.le_succ w.flow.length).trans h

end UnconstrainedPACDetection.VerifierEncodingBounds
