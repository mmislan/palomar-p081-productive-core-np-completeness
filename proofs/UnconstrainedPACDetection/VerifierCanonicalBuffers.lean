module

public import proofs.UnconstrainedPACDetection.VerifierEncodingBounds

@[expose] public section

namespace UnconstrainedPACDetection.VerifierCanonicalBuffers
open VerifierCanonicalCoordinates
open VerifierCanonicalContribution (sign magnitude product)
open VerifierCanonicalLoop (reaction)

def running (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions) (b : Bool)
    (x : Fin s.entities) (w : BinaryWitnessData.Witness) (p₀ n₀ : List Bool) :=
  VerifierRunningTotals.totals (fun i => xor b (sign w i))
    (fun i => product s b (reaction s hn i) x w) p₀ n₀

def envelope (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (p₀ n₀ : List Bool) := s.encode.length+3*w.encode.length+p₀.length+n₀.length+1

theorem product_bound (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (b : Bool) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (hw : w.flow.length = s.reactions) (i : ℕ) :
    (product s b (reaction s hn i) x w).length ≤ s.encode.length+2*w.encode.length := by
  have hc := VerifierEncodingBounds.coefficient_le s hs b (reaction s hn i) x
  have hm := (VerifierEncodingBounds.witness_bounds w (reaction s hn i).val
    (by rw [hw]; exact (reaction s hn i).isLt)).2
  have hp := VerifierBinaryProduct.multiply_length
    (coefficient s b (reaction s hn i) x).bits (magnitude w (reaction s hn i).val)
  change (product s b (reaction s hn i) x w).length ≤ _ at hp
  omega

theorem buffer_bounds (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (b : Bool) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (hw : w.flow.length = s.reactions)
    (p₀ n₀ : List Bool) (i : ℕ) (hi : i ≤ s.reactions) :
    (running s hn b x w p₀ n₀ i).1.length ≤ envelope s w p₀ n₀ ∧
    (running s hn b x w p₀ n₀ i).2.length ≤ envelope s w p₀ n₀ := by
  have h := VerifierRunningTotals.lengths (fun j => xor b (sign w j))
    (fun j => product s b (reaction s hn j) x w) p₀ n₀
    (s.encode.length+2*w.encode.length) i (fun j _ => product_bound s hs hn b x w hw j)
  have hc := VerifierEncodingBounds.reaction_count w
  rw [hw] at hc
  change (running s hn b x w p₀ n₀ i).1.length ≤ _ ∧
    (running s hn b x w p₀ n₀ i).2.length ≤ _ at h
  dsimp [envelope]
  omega

theorem body_budget (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (b : Bool) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (hw : w.flow.length = s.reactions)
    (p₀ n₀ : List Bool) (i : ℕ) (hi : i < s.reactions) :
    VerifierReactionLoop.bodyBound (witnessPrefix w i)
      (VerifierStrideCoordinates.skipped s b (reaction s hn i) x)
      (coefficient s b (reaction s hn i) x).bits (magnitude w i)
      (running s hn b x w p₀ n₀ i).1 (running s hn b x w p₀ n₀ i).2 ≤
      120*(envelope s w p₀ n₀+1)^2 := by
  have hwit := VerifierEncodingBounds.witness_bounds w i (by rw [hw]; exact hi)
  have hfc := VerifierEncodingBounds.count_le (witnessPrefix w i)
  have hskip := VerifierEncodingBounds.skipped_le s b (reaction s hn i) x
  have hsc := VerifierEncodingBounds.count_le (VerifierStrideCoordinates.skipped s b (reaction s hn i) x)
  have hc := VerifierEncodingBounds.coefficient_le s hs b (reaction s hn i) x
  have hb := buffer_bounds s hs hn b x w hw p₀ n₀ i (by omega)
  apply VerifierReactionBudget.body_bound
  all_goals dsimp [envelope] at *; omega

end UnconstrainedPACDetection.VerifierCanonicalBuffers
