module

public import proofs.UnconstrainedPACDetection.AdjugateFlow

@[expose] public section

namespace UnconstrainedPACDetection.ScaledInverseCertificate

def flowBitBound (q b : ℕ) : ℕ := q + 2 * (q * q + b * q) + 1

theorem flowBitBound_mono {q N : ℕ} (h : q ≤ N) (b : ℕ) :
    flowBitBound q b ≤ flowBitBound N b := by
  unfold flowBitBound
  have hq := Nat.mul_le_mul h h
  have hb := Nat.mul_le_mul_left b h
  omega

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem adjugateFlow_bits (A : Matrix n n ℤ) (b : ℕ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ) ^ b) (i : n) :
    (adjugateFlow A i).natAbs.size ≤ flowBitBound (Fintype.card n) b := by
  let q := Fintype.card n
  let C := heightBound (n := n) ((2 : ℤ) ^ b)
  have hH : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hC : 0 ≤ C := by unfold C heightBound; positivity
  have hc : C ≤ (2 : ℤ) ^ (q * q + b * q) :=
    heightBound_le_two_pow (n := n) (2 ^ b) b (by positivity) le_rfl
  have hq : (q : ℤ) ≤ (2 : ℤ) ^ q := by exact_mod_cast (Nat.le_of_lt q.lt_two_pow_self)
  have hz : |adjugateFlow A i| ≤ (2 : ℤ) ^ (q + 2 * (q * q + b * q)) := by
    calc
      |adjugateFlow A i| ≤ (q : ℤ) * C ^ 2 := adjugateFlow_height A (2 ^ b) hH hA i
      _ ≤ (2 : ℤ) ^ q * ((2 : ℤ) ^ (q * q + b * q)) ^ 2 :=
        mul_le_mul hq (pow_le_pow_left₀ hC hc 2) (sq_nonneg C) (by positivity)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [← Int.natCast_natAbs] at hz
  have hn : (adjugateFlow A i).natAbs ≤ 2 ^ (q + 2 * (q * q + b * q)) := by
    exact_mod_cast hz
  simpa [flowBitBound, q, Nat.size_pow] using Nat.size_le_size hn

end UnconstrainedPACDetection.ScaledInverseCertificate
