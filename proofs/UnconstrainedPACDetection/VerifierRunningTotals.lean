module

public import proofs.UnconstrainedPACDetection.VerifierCanonicalPhase

@[expose] public section

namespace UnconstrainedPACDetection.VerifierRunningTotals
open VerifierSignedContribution (newPos newNeg)

def totals (choose : ℕ → Bool) (term : ℕ → List Bool) (p₀ n₀ : List Bool) :
    ℕ → List Bool × List Bool
  | 0 => (p₀,n₀)
  | i+1 => (newPos (choose i) (term i) (totals choose term p₀ n₀ i).1,
      newNeg (choose i) (term i) (totals choose term p₀ n₀ i).2)

theorem pos_length (b : Bool) (term pos : List Bool) :
    (newPos b term pos).length ≤ max term.length pos.length+1 := by
  cases b
  · simp only [newPos,Bool.false_eq_true,↓reduceIte]
    omega
  · exact VerifierBinaryAdd.add_length false term pos

theorem neg_length (b : Bool) (term neg : List Bool) :
    (newNeg b term neg).length ≤ max term.length neg.length+1 := by
  cases b
  · exact VerifierBinaryAdd.add_length false term neg
  · simp only [newNeg,↓reduceIte]
    omega

/-- Even non-normalized binary accumulators grow at most one bit per update
beyond the maximum term and initial-buffer length. -/
theorem lengths (choose : ℕ → Bool) (term : ℕ → List Bool) (p₀ n₀ : List Bool)
    (M i : ℕ) (ht : ∀ j, j < i → (term j).length ≤ M) :
    (totals choose term p₀ n₀ i).1.length ≤ max M (max p₀.length n₀.length)+i ∧
    (totals choose term p₀ n₀ i).2.length ≤ max M (max p₀.length n₀.length)+i := by
  induction i with
  | zero => simp only [totals,Nat.add_zero]; omega
  | succ i ih =>
    have h := ih (fun j hj => ht j (by omega))
    have hp := pos_length (choose i) (term i) (totals choose term p₀ n₀ i).1
    have hn := neg_length (choose i) (term i) (totals choose term p₀ n₀ i).2
    have hm := ht i (by omega)
    simp only [totals]
    omega

theorem update_value (b : Bool) (term pos neg : List Bool) :
    (BinaryFields.readNat (newPos b term pos) : ℤ)-BinaryFields.readNat (newNeg b term neg) =
      (BinaryFields.readNat pos : ℤ)-BinaryFields.readNat neg+
        (if b then (1 : ℤ) else -1)*BinaryFields.readNat term := by
  cases b <;> simp [newPos,newNeg,VerifierBinaryAdd.add_value] <;> ring

theorem value (choose : ℕ → Bool) (term : ℕ → List Bool) (p₀ n₀ : List Bool) (i : ℕ) :
    (BinaryFields.readNat (totals choose term p₀ n₀ i).1 : ℤ)-
      BinaryFields.readNat (totals choose term p₀ n₀ i).2 =
    (BinaryFields.readNat p₀ : ℤ)-BinaryFields.readNat n₀+
      ∑ j ∈ Finset.range i, (if choose j then (1 : ℤ) else -1)*BinaryFields.readNat (term j) := by
  induction i with
  | zero => simp [totals]
  | succ i ih =>
    simp only [totals,update_value,Finset.sum_range_succ] at *
    rw [ih]
    ring

end UnconstrainedPACDetection.VerifierRunningTotals
