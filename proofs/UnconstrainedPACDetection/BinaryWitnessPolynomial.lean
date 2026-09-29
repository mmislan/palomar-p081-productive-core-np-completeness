module

public import proofs.UnconstrainedPACDetection.BinaryPACVerifier
public import proofs.UnconstrainedPACDetection.BinaryWireBounds

@[expose] public section

namespace UnconstrainedPACDetection.BinaryPACVerifier

open BinaryWireBounds ScaledInverseCertificate

theorem cubic_bound (m n b L : ℕ) (hm : m ≤ L) (hn : n ≤ L) (hb : b ≤ L) :
    2 * m + 1 + n * (2 * flowBitBound n b + 3) ≤ 16 * (L + 1) ^ 3 := by
  have hnn := Nat.mul_le_mul hn hn
  have hbn := Nat.mul_le_mul hb hn
  have hB : flowBitBound n b ≤ L + 4 * L ^ 2 + 1 := by
    unfold flowBitBound
    nlinarith
  have hprod := Nat.mul_le_mul hn (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hB) 3)
  nlinarith

/-- A concrete polynomial bound on an actual accepted binary witness.
This theorem does not assert polynomial machine execution of the verifier. -/
theorem exists_short_witness {input : List Bool} (h : input ∈ language) :
    ∃ witness, witness.length ≤ 16 * (input.length + 1) ^ 3 ∧ verify input witness = true := by
  obtain ⟨s, hs, hp⟩ := h
  have hm : 0 < s.entities := by
    obtain ⟨c, hc⟩ := hp
    obtain ⟨x, _⟩ := hc.1.1
    exact lt_of_le_of_lt (Nat.zero_le x.val) x.isLt
  have hn : 0 < s.reactions := by
    obtain ⟨c, hc⟩ := hp
    obtain ⟨r, _⟩ := hc.1.2.1
    exact lt_of_le_of_lt (Nat.zero_le r.val) r.isLt
  have henc := BinarySourceData.decode_reencode hs
  have hcounts := source_counts_le s (BinarySourceData.decode_wellFormed hs) hm hn
  have hb := source_side_bits_le s
  rw [henc] at hcounts hb
  obtain ⟨X, flow, hcheck⟩ := (exists_pac_iff_checkBoundedFlow s.toSource).1 hp
  have hbits : ∀ r, (flow r).natAbs.size ≤ flowBitBound s.reactions s.toSource.sideBitBound := by
    have hh : s.toSource.checkIntegerFlow X flow = true ∧
        ∀ r, (flow r).natAbs.size ≤ flowBitBound s.reactions s.toSource.sideBitBound := by
      simpa [ReversibleSource.checkBoundedFlow] using hcheck
    exact hh.2
  let w := BinaryWitnessData.fromCandidate X flow
  have hwbits : ∀ z ∈ w.flow, z.natAbs.size ≤ flowBitBound s.reactions s.toSource.sideBitBound := by
    simpa [w, BinaryWitnessData.fromCandidate] using hbits
  have hlen := witness_length_bound w _ hwbits
  simp only [w, BinaryWitnessData.fromCandidate_mask_length,
    BinaryWitnessData.fromCandidate_flow_length] at hlen
  refine ⟨w.encode, hlen.trans (cubic_bound _ _ _ _ hcounts.1 hcounts.2 hb), ?_⟩
  have hm0 : s.entities ≠ 0 := by omega
  have hn0 : s.reactions ≠ 0 := by omega
  simpa [verify, hs, hm0, hn0, w] using hcheck

theorem language_iff_short_verified (input : List Bool) :
    input ∈ language ↔ ∃ witness, witness.length ≤ 16 * (input.length + 1) ^ 3 ∧
      verify input witness = true :=
  ⟨exists_short_witness, fun ⟨_, _, h⟩ => verify_sound h⟩

end UnconstrainedPACDetection.BinaryPACVerifier
