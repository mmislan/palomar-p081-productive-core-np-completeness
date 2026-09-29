module

public import proofs.UnconstrainedPACDetection.VerifierReactionLoop

@[expose] public section

namespace UnconstrainedPACDetection.VerifierReactionBudget

/-- One common length envelope absorbs every local arithmetic and traversal cost.
The relation of N to the original input size is a separate obligation. -/
theorem body_bound (N : ℕ) (fields skipped : List (List Bool)) (xs mag pos neg : List Bool)
    (hf : (BinaryFields.encode fields).length ≤ N) (hfc : fields.length ≤ N)
    (hs : (BinaryFields.encode skipped).length ≤ N) (hsc : skipped.length ≤ N)
    (hx : xs.length ≤ N) (hm : mag.length ≤ N) (hp : pos.length ≤ N) (hn : neg.length ≤ N) :
    VerifierReactionLoop.bodyBound fields skipped xs mag pos neg ≤ 120*(N+1)^2 := by
  have hprod := VerifierBinaryProduct.multiply_length xs mag
  have hprodN : (VerifierBinaryProduct.multiply xs mag).length ≤ 3*N := by omega
  have hmax : max (VerifierBinaryProduct.multiply xs mag).length (max pos.length neg.length) ≤ 3*N :=
    max_le hprodN (max_le (by omega) (by omega))
  have hadd : VerifierSignedContribution.addBound (VerifierBinaryProduct.multiply xs mag) pos neg ≤ 9*N+8 := by
    dsimp [VerifierSignedContribution.addBound]
    omega
  have hmul : mag.length*(10*xs.length+20*mag.length+30) ≤ N*(30*N+30) :=
    Nat.mul_le_mul hm (by omega)
  have hc : VerifierContributionIteration.contributionBound fields xs mag pos neg ≤
      30*N^2+45*N+22 := by
    dsimp [VerifierContributionIteration.contributionBound]
    nlinarith
  dsimp [VerifierReactionLoop.bodyBound]
  nlinarith

theorem loop_bound (v N : ℕ) (hv : v ≤ N) :
    v*(120*(N+1)^2+2)+(v+2) ≤ 124*(N+1)^3 := by
  have hm := Nat.mul_le_mul_right (120*(N+1)^2+2) hv
  nlinarith [sq_nonneg (N : ℤ)]

end UnconstrainedPACDetection.VerifierReactionBudget
