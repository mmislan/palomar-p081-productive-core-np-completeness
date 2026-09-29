module

public import proofs.UnconstrainedPACDetection.ScaledInverseCertificate
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

@[expose] public section

/-! A uniform height bound for integer scaled-inverse certificates. Using the
row-replacement formula for adjugate avoids a separate order-zero cofactor case. -/

namespace UnconstrainedPACDetection.ScaledInverseCertificate

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

def heightBound (H : ℤ) : ℤ :=
  (Nat.factorial (Fintype.card n) : ℤ) * H ^ Fintype.card n

theorem det_height_bound (A : Matrix n n ℤ) (H : ℤ)
    (hA : ∀ i j, |A i j| ≤ H) : |A.det| ≤ heightBound (n := n) H := by
  simpa [heightBound, nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) hA)

theorem adjugate_height_bound (A : Matrix n n ℤ) (H : ℤ)
    (hH : 1 ≤ H) (hA : ∀ i j, |A i j| ≤ H) (i j : n) :
    |A.adjugate i j| ≤ heightBound (n := n) H := by
  rw [Matrix.adjugate_apply]
  apply det_height_bound
  intro r c
  by_cases hr : r = j
  · subst r
    by_cases hc : c = i
    · subst c
      simpa using hH
    · simpa [Matrix.updateRow, Function.update, Pi.single_apply, hc] using
        (show (0 : ℤ) ≤ H by omega)
  · simpa [Matrix.updateRow, Function.update, hr] using hA r c

theorem exists_bounded_certificate_iff (A : Matrix n n ℤ) (H : ℤ)
    (hH : 1 ≤ H) (hA : ∀ i j, |A i j| ≤ H) :
    (∃ d B, Accepts A d B ∧ |d| ≤ heightBound (n := n) H ∧
      ∀ i j, |B i j| ≤ heightBound (n := n) H) ↔
      LinearIndependent ℝ (fun i j => (A i j : ℝ)) := by
  constructor
  · rintro ⟨d, B, h, _, _⟩
    exact (real_rows_iff_certificate A).2 ⟨d, B, h⟩
  · intro h
    have hd := (exists_certificate_iff A).1 ((real_rows_iff_certificate A).1 h)
    exact ⟨A.det, A.adjugate, ⟨hd, Matrix.mul_adjugate A⟩,
      det_height_bound A H hA, adjugate_height_bound A H hH hA⟩

end UnconstrainedPACDetection.ScaledInverseCertificate
