module

public import proofs.UnconstrainedPACDetection.ScaledInverseBounds
public import proofs.UnconstrainedPACDetection.CertificateBitBounds

@[expose] public section

/-! Compress the scaled inverse to one integer flow; no determinant need be
computed by the eventual verifier. -/

namespace UnconstrainedPACDetection.ScaledInverseCertificate

open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def adjugateFlow (A : Matrix n n ℤ) : n → ℤ :=
  A.det • ((fun _ => (1 : ℤ)) ᵥ* A.adjugate)

theorem adjugateFlow_balance (A : Matrix n n ℤ) (j : n) :
    ∑ i, A i j * adjugateFlow A i = A.det * A.det := by
  have h : adjugateFlow A ᵥ* A = fun _ => A.det * A.det := by
    rw [adjugateFlow, Matrix.smul_vecMul, Matrix.vecMul_vecMul,
      Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
    ext i
    simp
  have hj := congrFun h j
  simpa [Matrix.vecMul, dotProduct, mul_comm] using hj

theorem adjugateFlow_height (A : Matrix n n ℤ) (H : ℤ) (hH : 1 ≤ H)
    (hA : ∀ i j, |A i j| ≤ H) (i : n) :
    |adjugateFlow A i| ≤ (Fintype.card n : ℤ) * heightBound (n := n) H ^ 2 := by
  have hC : 0 ≤ heightBound (n := n) H := by
    unfold heightBound
    positivity
  have hs : |∑ j, A.adjugate j i| ≤ (Fintype.card n : ℤ) * heightBound (n := n) H := by
    calc
      |∑ j, A.adjugate j i| ≤ ∑ j, |A.adjugate j i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : n, heightBound (n := n) H := Finset.sum_le_sum fun j _ =>
        adjugate_height_bound A H hH hA j i
      _ = _ := by simp
  calc
    |adjugateFlow A i| = |A.det| * |∑ j, A.adjugate j i| := by
      simp [adjugateFlow, Matrix.vecMul, dotProduct, abs_mul]
    _ ≤ heightBound (n := n) H * ((Fintype.card n : ℤ) * heightBound (n := n) H) :=
      mul_le_mul (det_height_bound A H hA) hs (abs_nonneg _) hC
    _ = _ := by ring

end UnconstrainedPACDetection.ScaledInverseCertificate
