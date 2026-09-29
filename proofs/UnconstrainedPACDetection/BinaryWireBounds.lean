module

public import proofs.UnconstrainedPACDetection.BinarySourceData
public import proofs.UnconstrainedPACDetection.BinaryWitnessData
public import proofs.UnconstrainedPACDetection.BoundedFlowChecker

@[expose] public section

namespace UnconstrainedPACDetection.BinaryWireBounds

theorem field_count_le (fs : List (List Bool)) : fs.length ≤ (BinaryFields.encode fs).length := by
  induction fs with
  | nil => simp [BinaryFields.encode]
  | cons f fs ih =>
    simp only [BinaryFields.encode, List.flatMap_cons, List.length_append,
      BinaryFields.encodeField_length, List.length_cons] at *
    omega

theorem payload_length_le (fs : List (List Bool)) :
    (fs.map List.length).sum ≤ (BinaryFields.encode fs).length := by
  induction fs with
  | nil => simp [BinaryFields.encode]
  | cons f fs ih =>
    simp only [BinaryFields.encode, List.flatMap_cons, List.length_append,
      BinaryFields.encodeField_length, List.map_cons, List.sum_cons] at *
    omega

theorem source_counts_le (s : BinarySourceData.DenseSource) (h : s.WellFormed)
    (hm : 0 < s.entities) (hn : 0 < s.reactions) :
    s.entities ≤ s.encode.length ∧ s.reactions ≤ s.encode.length := by
  have hf := field_count_le (s.entities.bits :: s.reactions.bits :: s.values.map Nat.bits)
  have he : s.values.length = 2 * (s.entities * s.reactions) := h
  simp only [List.length_cons, List.length_map] at hf
  change s.values.length + 1 + 1 ≤ s.encode.length at hf
  have hmp := Nat.mul_le_mul_left s.entities (show 1 ≤ s.reactions by omega)
  have hnp := Nat.mul_le_mul_right s.reactions (show 1 ≤ s.entities by omega)
  constructor <;> nlinarith

theorem source_value_bits_le (s : BinarySourceData.DenseSource) :
    (s.values.map Nat.size).sum ≤ s.encode.length := by
  have h := payload_length_le (s.entities.bits :: s.reactions.bits :: s.values.map Nat.bits)
  simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
    Nat.size_eq_bits_len] at h
  change s.entities.size + (s.reactions.size + (s.values.map Nat.size).sum) ≤ s.encode.length at h
  omega

theorem getD_size_le (xs : List ℕ) (i : ℕ) : (xs.getD i 0).size ≤ (xs.map Nat.size).sum := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have h := ih i
      simpa using h.trans (Nat.le_add_left _ x.size)

theorem source_side_bits_le (s : BinarySourceData.DenseSource) :
    s.toSource.sideBitBound ≤ s.encode.length := by
  apply Finset.sup_le
  intro r _
  apply Finset.sup_le
  intro x _
  apply max_le
  · exact (getD_size_le s.values _).trans (source_value_bits_le s)
  · exact (getD_size_le s.values _).trans (source_value_bits_le s)

theorem witness_length (w : BinaryWitnessData.Witness) :
    w.encode.length = 2 * w.mask.length + 1 +
      (w.flow.map (fun z => 2 * z.natAbs.size + 3)).sum := by
  have he : ∀ z : ℤ, 2 * (BinaryFields.writeInt z).length + 1 = 2 * z.natAbs.size + 3 := by
    intro z
    simp [BinaryFields.writeInt, Nat.size_eq_bits_len]
    omega
  simp [BinaryWitnessData.Witness.encode, BinaryFields.encode_length,
    List.map_map, Function.comp_def, he]

theorem flow_sum_bound (zs : List ℤ) (B : ℕ) :
    (∀ z ∈ zs, z.natAbs.size ≤ B) →
      (zs.map (fun z => 2 * z.natAbs.size + 3)).sum ≤ zs.length * (2 * B + 3) := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    intro h
    have hz := h z (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem witness_length_bound (w : BinaryWitnessData.Witness) (B : ℕ)
    (h : ∀ z ∈ w.flow, z.natAbs.size ≤ B) :
    w.encode.length ≤ 2 * w.mask.length + 1 + w.flow.length * (2 * B + 3) := by
  rw [witness_length]
  exact Nat.add_le_add_left (flow_sum_bound w.flow B h) _

end UnconstrainedPACDetection.BinaryWireBounds
