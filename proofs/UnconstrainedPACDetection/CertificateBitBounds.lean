module

public import proofs.UnconstrainedPACDetection.ScaledInverseBounds
public import Mathlib.Data.Nat.Size

@[expose] public section

/-! Explicit polynomial magnitude-bit bounds. A sign bit and index encoding
are additional data in the eventual total binary verifier. -/

namespace UnconstrainedPACDetection.ScaledInverseCertificate

theorem factorial_le_two_pow_sq (q : ℕ) : q.factorial ≤ 2 ^ (q * q) := by
  calc
    q.factorial ≤ q ^ q := Nat.factorial_le_pow q
    _ ≤ (2 ^ q) ^ q := Nat.pow_le_pow_left (Nat.le_of_lt q.lt_two_pow_self) q
    _ = 2 ^ (q * q) := (pow_mul 2 q q).symm

variable {n : Type*} [Fintype n]

theorem heightBound_le_two_pow (H : ℤ) (b : ℕ) (hH : 0 ≤ H)
    (hb : H ≤ (2 : ℤ) ^ b) :
    heightBound (n := n) H ≤
      (2 : ℤ) ^ (Fintype.card n * Fintype.card n + b * Fintype.card n) := by
  let q := Fintype.card n
  have hf : (q.factorial : ℤ) ≤ (2 : ℤ) ^ (q * q) := by
    exact_mod_cast factorial_le_two_pow_sq q
  calc
    heightBound (n := n) H = (q.factorial : ℤ) * H ^ q := rfl
    _ ≤ (2 : ℤ) ^ (q * q) * ((2 : ℤ) ^ b) ^ q :=
      mul_le_mul hf (pow_le_pow_left₀ hH hb q) (pow_nonneg hH q) (by positivity)
    _ = (2 : ℤ) ^ (q * q + b * q) := by rw [← pow_mul, ← pow_add]

theorem magnitude_bits_le (z H : ℤ) (b : ℕ) (hH : 0 ≤ H)
    (hb : H ≤ (2 : ℤ) ^ b) (hz : |z| ≤ heightBound (n := n) H) :
    z.natAbs.size ≤ Fintype.card n * Fintype.card n + b * Fintype.card n + 1 := by
  have h := hz.trans (heightBound_le_two_pow (n := n) H b hH hb)
  rw [← Int.natCast_natAbs] at h
  have hn : z.natAbs ≤ 2 ^ (Fintype.card n * Fintype.card n + b * Fintype.card n) := by
    exact_mod_cast h
  have hs := Nat.size_le_size hn
  simpa only [Nat.size_pow] using hs

end UnconstrainedPACDetection.ScaledInverseCertificate
